//! Passive conditional-source row records. Every restored input is reconstructed
//! by original-template admission and every instance is checked again in Core.

use super::source_resource_image::PlainPairRecord;
use super::{
    Decoder, Encoder, ImageFailure, Slice, SpanRecord, StructuralInput, Wire, WireOutput,
    WireReader, WireWriter, append, charge, get, index, push,
};
use crate::{
    core::{
        HandlerId, NodeId,
        capture::{ActualCaptureInputs, ActualCaptureWitness, ActualValuePathStep},
        provider::{
            CaptureInputId, HandlerPendingRows, PendingRowEquality, PendingRowEquation,
            PendingRowRecomputation, PendingRowRecord, ResolvedProviderHandlerRows,
        },
        source_resource::{CheckedSourceResourceTemplate, SourceHandlerRowInputs},
    },
    resolved::{ProviderTemplateId, ResumeId},
    types::{EffectRow, InferenceVariableId},
};
use std::collections::{HashMap, HashSet};

#[derive(Clone, Copy)]
struct PendingRecord {
    identity: u32,
    tag: u8,
    left: u32,
    right: u32,
    missing: bool,
    source: SpanRecord,
}
#[derive(Clone, Copy)]
struct EqualityRecord {
    left: u32,
    right: u32,
    source: SpanRecord,
}
#[derive(Clone, Copy)]
struct RecomputeRecord {
    nodes: Slice,
    output: u32,
    handler: u32,
    resume: u32,
}
#[derive(Clone, Copy)]
struct PathRecord {
    tag: u8,
    first: SpanRecord,
    second: Option<SpanRecord>,
    ordinal: u32,
}
#[derive(Clone, Copy)]
struct WitnessRecord {
    input: u32,
    request: SpanRecord,
    path: Slice,
    row: u32,
}
wire_struct!(PendingRecord, identity, tag, left, right, missing, source);
wire_struct!(EqualityRecord, left, right, source);
wire_struct!(RecomputeRecord, nodes, output, handler, resume);
wire_struct!(PathRecord, tag, first, second, ordinal);
wire_struct!(WitnessRecord, input, request, path, row);

pub(super) struct SourceInputsRecord {
    direct: u32,
    equations: Vec<PendingRecord>,
    equalities: Vec<EqualityRecord>,
    recomputations: Vec<RecomputeRecord>,
}
impl SourceInputsRecord {
    pub(super) fn identities(&self) -> impl Iterator<Item = InferenceVariableId> + '_ {
        self.equations
            .iter()
            .map(|record| InferenceVariableId::new(record.identity))
    }
}

fn original_node(mapping: &[Option<u32>], id: NodeId) -> Result<u32, ImageFailure> {
    mapping
        .get(id.value() as usize)
        .copied()
        .flatten()
        .ok_or(ImageFailure::InvalidRecord)
}

impl Encoder<'_> {
    pub(super) fn encode_source_row_inputs(
        &mut self,
        inputs: &SourceHandlerRowInputs,
        mapping: &[Option<u32>],
    ) -> Result<Slice, ImageFailure> {
        let direct = self.encode_structural(StructuralInput::Row(&inputs.direct))?;
        let mut equations = Vec::new();
        for record in &inputs.pending.equations {
            let (tag, left, right, missing) = match &record.equation {
                PendingRowEquation::Discard(node) => (0, original_node(mapping, *node)?, 0, false),
                PendingRowEquation::Union(left, right) => (
                    1,
                    self.encode_structural(StructuralInput::Row(left))?,
                    self.encode_structural(StructuralInput::Row(right))?,
                    false,
                ),
                PendingRowEquation::Remove(row, effect, missing) => (
                    2,
                    self.encode_structural(StructuralInput::Row(row))?,
                    self.encode_structural(StructuralInput::Instance(effect))?,
                    *missing,
                ),
            };
            let source = self.span(record.source)?;
            push(
                &mut equations,
                PendingRecord {
                    identity: record.identity.value(),
                    tag,
                    left,
                    right,
                    missing,
                    source,
                },
                self.work,
            )?;
        }
        let mut equalities = Vec::new();
        for equality in &inputs.pending.equalities {
            let left = self.encode_structural(StructuralInput::Row(&equality.left))?;
            let right = self.encode_structural(StructuralInput::Row(&equality.right))?;
            let source = self.span(equality.source)?;
            push(
                &mut equalities,
                EqualityRecord {
                    left,
                    right,
                    source,
                },
                self.work,
            )?;
        }
        let mut recomputations = Vec::new();
        for recompute in &inputs.pending.recomputations {
            let start = self.image.node_children.len();
            for node in &recompute.nodes {
                push(
                    &mut self.image.node_children,
                    original_node(mapping, *node)?,
                    self.work,
                )?;
            }
            let nodes = Slice::of(&self.image.node_children, start)?;
            let output = self.encode_structural(StructuralInput::Row(&recompute.output))?;
            push(
                &mut recomputations,
                RecomputeRecord {
                    nodes,
                    output,
                    handler: recompute.handler.value(),
                    resume: recompute.resume.value(),
                },
                self.work,
            )?;
        }
        let mut writer = WireWriter {
            output: WireOutput::Encoded(Vec::new()),
            work: self.work,
        };
        direct.write(&mut writer)?;
        writer.table(&equations)?;
        writer.table(&equalities)?;
        writer.table(&recomputations)?;
        let WireOutput::Encoded(bytes) = writer.output else {
            return Err(ImageFailure::InvalidRecord);
        };
        append(&mut self.image.bytes, &bytes, self.work)
    }

    pub(super) fn encode_source_row_pairs<K: Copy + Eq + std::hash::Hash>(
        &mut self,
        rows: &HashMap<K, EffectRow>,
        mut key: impl FnMut(K) -> Result<u32, ImageFailure>,
    ) -> Result<Slice, ImageFailure> {
        let mut ordered = Vec::new();
        for (id, row) in rows {
            push(&mut ordered, (key(*id)?, row), self.work)?;
        }
        // Sort coordinates before structural interning, so hash iteration cannot
        // choose the first representation slot or change canonical wire order.
        for at in 0..ordered.len() {
            let mut selected = at;
            for next in at + 1..ordered.len() {
                charge(self.work, 1)?;
                if ordered[next].0 < ordered[selected].0 {
                    selected = next;
                }
            }
            charge(self.work, 1)?;
            ordered.swap(at, selected);
        }
        let mut records = Vec::new();
        for (original, row) in ordered {
            let copied = self.encode_structural(StructuralInput::Row(row))?;
            push(
                &mut records,
                PlainPairRecord { original, copied },
                self.work,
            )?;
        }
        append(&mut self.image.source_plain_pairs, &records, self.work)
    }

    pub(super) fn encode_source_row_claim(
        &mut self,
        claim: &ResolvedProviderHandlerRows,
        mapping: &[Option<u32>],
    ) -> Result<Slice, ImageFailure> {
        let mut rows = [0; 4];
        for (slot, row) in rows.iter_mut().zip(claim.source_rows()) {
            *slot = self.encode_structural(StructuralInput::Row(row))?;
        }
        let pending = self.encode_source_row_pairs(claim.pending(), |id| Ok(id.value()))?;
        let nodes =
            self.encode_source_row_pairs(claim.node_rows(), |id| original_node(mapping, id))?;
        let handlers =
            self.encode_source_row_pairs(claim.handler_outputs(), |id| Ok(id.value()))?;
        let captures = claim.capture_inputs();
        let capture_rows = self.encode_source_row_pairs(&captures.rows, |id| index(id.value()))?;
        let mut paths = Vec::new();
        let mut witnesses = Vec::new();
        for witness in &captures.witnesses {
            let start = paths.len();
            for step in &witness.path {
                let (tag, first, second, ordinal) = match *step {
                    ActualValuePathStep::Root(span) => (0, self.span(span)?, None, 0),
                    ActualValuePathStep::Call(span) => (1, self.span(span)?, None, 0),
                    ActualValuePathStep::Invoke(first, second) => {
                        (2, self.span(first)?, Some(self.span(second)?), 0)
                    }
                    ActualValuePathStep::Dispatch(first, second, ordinal) => (
                        3,
                        self.span(first)?,
                        Some(self.span(second)?),
                        index(ordinal)?,
                    ),
                };
                push(
                    &mut paths,
                    PathRecord {
                        tag,
                        first,
                        second,
                        ordinal,
                    },
                    self.work,
                )?;
            }
            let path = Slice::of(&paths, start)?;
            let request = self.span(witness.request)?;
            let row = self.encode_structural(StructuralInput::Row(&witness.row))?;
            push(
                &mut witnesses,
                WitnessRecord {
                    input: index(witness.input.value())?,
                    request,
                    path,
                    row,
                },
                self.work,
            )?;
        }
        let mut writer = WireWriter {
            output: WireOutput::Encoded(Vec::new()),
            work: self.work,
        };
        for row in rows {
            row.write(&mut writer)?;
        }
        pending.write(&mut writer)?;
        nodes.write(&mut writer)?;
        handlers.write(&mut writer)?;
        capture_rows.write(&mut writer)?;
        writer.table(&paths)?;
        writer.table(&witnesses)?;
        let WireOutput::Encoded(bytes) = writer.output else {
            return Err(ImageFailure::InvalidRecord);
        };
        append(&mut self.image.bytes, &bytes, self.work)
    }
}

impl Decoder<'_> {
    pub(super) fn source_row_inputs_record(
        &mut self,
        blob: Slice,
    ) -> Result<SourceInputsRecord, ImageFailure> {
        let bytes = blob.get(&self.image.bytes)?;
        let mut reader = WireReader {
            bytes,
            offset: 0,
            work: self.work,
        };
        let direct = u32::read(&mut reader)?;
        let equations = reader.table::<PendingRecord>()?;
        let equalities = reader.table::<EqualityRecord>()?;
        let recomputations = reader.table::<RecomputeRecord>()?;
        if reader.offset != bytes.len() {
            return Err(ImageFailure::InvalidRecord);
        }
        Ok(SourceInputsRecord {
            direct,
            equations,
            equalities,
            recomputations,
        })
    }

    pub(super) fn source_row_inputs(
        &mut self,
        record: SourceInputsRecord,
        nodes: &[NodeId],
    ) -> Result<SourceHandlerRowInputs, ImageFailure> {
        let direct = self.structural(record.direct)?.row()?;
        let mut pending = HandlerPendingRows::default();
        for record in record.equations {
            let equation = match record.tag {
                0 if record.right == 0 && !record.missing => {
                    PendingRowEquation::Discard(*get(nodes, record.left)?)
                }
                1 if !record.missing => PendingRowEquation::Union(
                    self.structural(record.left)?.row()?,
                    self.structural(record.right)?.row()?,
                ),
                2 => PendingRowEquation::Remove(
                    self.structural(record.left)?.row()?,
                    self.structural(record.right)?.instance()?,
                    record.missing,
                ),
                _ => return Err(ImageFailure::InvalidRecord),
            };
            let source = self.span(record.source)?;
            push(
                &mut pending.equations,
                PendingRowRecord {
                    identity: InferenceVariableId::new(record.identity),
                    equation,
                    source,
                },
                self.work,
            )?;
        }
        for record in record.equalities {
            let left = self.structural(record.left)?.row()?;
            let right = self.structural(record.right)?.row()?;
            let source = self.span(record.source)?;
            push(
                &mut pending.equalities,
                PendingRowEquality {
                    left,
                    right,
                    source,
                },
                self.work,
            )?;
        }
        for record in record.recomputations {
            let mut roots = Vec::new();
            for node in record.nodes.get(&self.image.node_children)? {
                push(&mut roots, *get(nodes, *node)?, self.work)?;
            }
            let output = self.structural(record.output)?.row()?;
            push(
                &mut pending.recomputations,
                PendingRowRecomputation {
                    nodes: roots,
                    output,
                    handler: HandlerId::new(record.handler),
                    resume: ResumeId::new(record.resume),
                },
                self.work,
            )?;
        }
        Ok(SourceHandlerRowInputs { direct, pending })
    }

    pub(super) fn install_source_pending(
        &mut self,
        identities: impl Iterator<Item = InferenceVariableId>,
    ) -> Result<HashSet<InferenceVariableId>, ImageFailure> {
        let mut current = HashSet::new();
        for id in identities {
            charge(self.work, 1)?;
            current.try_reserve(1).map_err(|_| ImageFailure::Resource)?;
            if !current.insert(id) {
                return Err(ImageFailure::InvalidRecord);
            }
        }
        Ok(std::mem::replace(&mut self.source_pending_rows, current))
    }

    pub(super) fn source_row_pairs<K: Eq + std::hash::Hash>(
        &mut self,
        rows: Slice,
        mut key: impl FnMut(u32) -> Result<K, ImageFailure>,
    ) -> Result<HashMap<K, EffectRow>, ImageFailure> {
        let records = rows.get(&self.image.source_plain_pairs)?;
        charge(self.work, records.len())?;
        let mut result = HashMap::new();
        result
            .try_reserve(records.len())
            .map_err(|_| ImageFailure::Resource)?;
        let mut previous = None;
        for record in records {
            if previous.is_some_and(|id| id >= record.original) {
                return Err(ImageFailure::InvalidRecord);
            }
            previous = Some(record.original);
            let id = key(record.original)?;
            let row = self.structural(record.copied)?.row()?;
            if result.insert(id, row).is_some() {
                return Err(ImageFailure::InvalidRecord);
            }
        }
        Ok(result)
    }

    pub(super) fn source_row_claim(
        &mut self,
        blob: Slice,
        template: &CheckedSourceResourceTemplate,
        original_nodes: &[NodeId],
    ) -> Result<ResolvedProviderHandlerRows, ImageFailure> {
        let bytes = blob.get(&self.image.bytes)?;
        let mut reader = WireReader {
            bytes,
            offset: 0,
            work: self.work,
        };
        let roots = [
            u32::read(&mut reader)?,
            u32::read(&mut reader)?,
            u32::read(&mut reader)?,
            u32::read(&mut reader)?,
        ];
        let pending = Slice::read(&mut reader)?;
        let node_rows = Slice::read(&mut reader)?;
        let handlers = Slice::read(&mut reader)?;
        let capture_rows = Slice::read(&mut reader)?;
        let paths = reader.table::<PathRecord>()?;
        let records = reader.table::<WitnessRecord>()?;
        if reader.offset != bytes.len() {
            return Err(ImageFailure::InvalidRecord);
        }
        let [direct, epsilon, output, residual] = roots;
        let rows = [
            self.structural(direct)?.row()?,
            self.structural(epsilon)?.row()?,
            self.structural(output)?.row()?,
            self.structural(residual)?.row()?,
        ];
        let pending = self.source_row_pairs(pending, |id| Ok(InferenceVariableId::new(id)))?;
        let node_rows = self.source_row_pairs(node_rows, |id| Ok(*get(original_nodes, id)?))?;
        let handlers = self.source_row_pairs(handlers, |id| Ok(HandlerId::new(id)))?;
        let capture_rows = self.source_row_pairs(capture_rows, |id| {
            Ok(CaptureInputId::from_image_claim(id as usize))
        })?;
        let mut witnesses = Vec::new();
        let mut used_paths = 0usize;
        for record in records {
            if record.path.start as usize != used_paths {
                return Err(ImageFailure::InvalidRecord);
            }
            let mut path = Vec::new();
            for step in record.path.get(&paths)? {
                let first = self.span(step.first)?;
                let step = match (step.tag, step.second, step.ordinal) {
                    (0, None, 0) => ActualValuePathStep::Root(first),
                    (1, None, 0) => ActualValuePathStep::Call(first),
                    (2, Some(second), 0) => ActualValuePathStep::Invoke(first, self.span(second)?),
                    (3, Some(second), ordinal) => {
                        ActualValuePathStep::Dispatch(first, self.span(second)?, ordinal as usize)
                    }
                    _ => return Err(ImageFailure::InvalidRecord),
                };
                push(&mut path, step, self.work)?;
            }
            used_paths = used_paths
                .checked_add(record.path.len as usize)
                .ok_or(ImageFailure::Resource)?;
            let input = CaptureInputId::from_image_claim(record.input as usize);
            if !capture_rows.contains_key(&input) {
                return Err(ImageFailure::InvalidRecord);
            }
            let request = self.span(record.request)?;
            let row = self.structural(record.row)?.row()?;
            push(
                &mut witnesses,
                ActualCaptureWitness {
                    input,
                    request,
                    path,
                    row,
                },
                self.work,
            )?;
        }
        if used_paths != paths.len() {
            return Err(ImageFailure::InvalidRecord);
        }
        let captures = ActualCaptureInputs {
            template: ProviderTemplateId::new(template.header().original.id, 2),
            rows: capture_rows,
            witnesses,
        };
        template
            .restore_row_claim(rows, pending, node_rows, handlers, captures, self.work)
            .map_err(ImageFailure::Validation)
    }
}

#[cfg(test)]
pub(super) fn mutate_claim_for_test(
    image: &mut super::PureImage,
    blob: Slice,
    mutation: u8,
) -> Slice {
    let mut work = crate::types::TypeWorkBudget::default();
    let mut reader = WireReader {
        bytes: blob.get(&image.bytes).unwrap(),
        offset: 0,
        work: &mut work,
    };
    let mut roots = [
        u32::read(&mut reader).unwrap(),
        u32::read(&mut reader).unwrap(),
        u32::read(&mut reader).unwrap(),
        u32::read(&mut reader).unwrap(),
    ];
    let pending = Slice::read(&mut reader).unwrap();
    let nodes = Slice::read(&mut reader).unwrap();
    let handlers = Slice::read(&mut reader).unwrap();
    let captures = Slice::read(&mut reader).unwrap();
    let paths = reader.table::<PathRecord>().unwrap();
    let mut witnesses = reader.table::<WitnessRecord>().unwrap();
    assert_eq!(reader.offset, reader.bytes.len());
    match mutation {
        0 => {
            let empty = witnesses
                .iter()
                .position(|record| record.row == roots[1])
                .expect("empty request");
            assert_ne!(roots[0], roots[1]);
            witnesses[empty].row = roots[0];
        }
        1 => {
            for record in captures.get(&image.source_plain_pairs).unwrap().iter() {
                assert_eq!(record.original, 0);
            }
            let begin = captures.start as usize;
            for record in &mut image.source_plain_pairs[begin..begin + captures.len as usize] {
                record.original += 1;
            }
            for witness in &mut witnesses {
                witness.input += 1;
            }
        }
        2 => {
            roots[1] = roots[0];
            roots[3] = roots[0];
        }
        _ => panic!("unknown claim mutation"),
    }
    let mut writer = WireWriter {
        output: WireOutput::Encoded(Vec::new()),
        work: &mut work,
    };
    for root in roots {
        root.write(&mut writer).unwrap();
    }
    pending.write(&mut writer).unwrap();
    nodes.write(&mut writer).unwrap();
    handlers.write(&mut writer).unwrap();
    captures.write(&mut writer).unwrap();
    writer.table(&paths).unwrap();
    writer.table(&witnesses).unwrap();
    let WireOutput::Encoded(bytes) = writer.output else {
        unreachable!()
    };
    append(&mut image.bytes, &bytes, &mut work).unwrap()
}

#[cfg(test)]
pub(super) fn replace_discard_node_for_test(
    image: &mut super::PureImage,
    blob: Slice,
    node: u32,
) -> Slice {
    let mut work = crate::types::TypeWorkBudget::default();
    let mut reader = WireReader {
        bytes: blob.get(&image.bytes).unwrap(),
        offset: 0,
        work: &mut work,
    };
    let direct = u32::read(&mut reader).unwrap();
    let mut equations = reader.table::<PendingRecord>().unwrap();
    let equalities = reader.table::<EqualityRecord>().unwrap();
    let recomputations = reader.table::<RecomputeRecord>().unwrap();
    assert_eq!(reader.offset, reader.bytes.len());
    let discard = equations.iter_mut().find(|record| record.tag == 0).unwrap();
    assert_ne!(discard.left, node);
    discard.left = node;
    let mut writer = WireWriter {
        output: WireOutput::Encoded(Vec::new()),
        work: &mut work,
    };
    direct.write(&mut writer).unwrap();
    writer.table(&equations).unwrap();
    writer.table(&equalities).unwrap();
    writer.table(&recomputations).unwrap();
    let WireOutput::Encoded(bytes) = writer.output else {
        unreachable!()
    };
    append(&mut image.bytes, &bytes, &mut work).unwrap()
}
