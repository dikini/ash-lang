//! Private primitive serialization for the bounded arena experiment.
//!
//! Native tags describe physical layouts only. They grant no Ash Layout or Ref
//! authority. Preparation owns scratch bytes before the arena reserves storage;
//! decoding produces independent copied data and retains no native pointer.
//! Aggregate descriptors and constructor identities must come from a bridge
//! that authenticates the complete type dictionary. Local consistency checks
//! cannot detect a forged sole-constructor subset or grant Ash Layout evidence.
//! Aggregate preparation supports only acyclic by-value data and duplicates
//! shared inline fields. The production scalar entry points require authenticated
//! dictionaries from the caller and an evaluator work debit. Reference payloads
//! and source callbacks remain unsupported.

use crate::arena::{AllocationError, LayoutTag, PayloadLayout};
use ash::foreign::runtime::{ForeignData, ForeignDataNode, ForeignExecutionError};
use ash::{
    integer::Integer,
    types::{ConstructorId, TYPE_WORK_LIMIT},
};
use std::{collections::HashSet, sync::Arc};

/// Recoverable payload refusal remains distinct from terminal host exhaustion.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum PreparationError {
    Refused(AllocationError),
    Internal(ForeignExecutionError),
}

impl From<AllocationError> for PreparationError {
    fn from(error: AllocationError) -> Self {
        Self::Refused(error)
    }
}

fn check_work(contents: usize) -> Result<(), ForeignExecutionError> {
    contents
        .checked_add(1)
        .filter(|work| *work <= TYPE_WORK_LIMIT)
        .ok_or(ForeignExecutionError::WORK_EXHAUSTED)?;
    Ok(())
}

fn scratch(size: usize) -> Result<Vec<u8>, ForeignExecutionError> {
    let mut bytes = Vec::new();
    bytes
        .try_reserve_exact(size)
        .map_err(|_| ForeignExecutionError::STORAGE_REFUSED)?;
    Ok(bytes)
}

#[derive(Clone, Copy, Debug)]
pub(super) enum ScalarKind {
    Unit,
    Boolean,
    Integer,
    Bytes,
    String,
}

/// Finite, flat descriptors supplied by a future authenticated bridge. Slots
/// identify graph edges; IDs identify supplied layout facts, never value names.
/// No graph here establishes source layout authority or owner dependencies.
#[derive(Debug)]
pub(super) struct LayoutDescriptor {
    pub(super) id: u64,
    pub(super) shape: LayoutShape,
}

#[derive(Debug)]
pub(super) enum LayoutShape {
    Scalar(ScalarKind),
    Tuple(Box<[usize]>),
    /// The bridge supplies all constructors in defining order.
    Nominal(Box<[ConstructorLayout]>),
    /// Reference authentication and relational dependencies remain unavailable.
    UnsupportedReference,
}

#[derive(Clone, Copy, Debug)]
pub(super) struct ConstructorLayout {
    pub(super) constructor: ConstructorId,
    /// Foreign constructor payloads have one child; multiple source fields use
    /// a tuple descriptor here, preserving the admitted ForeignData shape.
    pub(super) payload: Option<usize>,
}

#[derive(Clone, Copy, Debug)]
pub(super) struct LayoutGraph<'a> {
    pub(super) descriptors: &'a [LayoutDescriptor],
    pub(super) root: usize,
}

#[derive(Default)]
struct Work {
    used: usize,
}

impl Work {
    fn charge(&mut self, amount: usize) -> Result<(), ForeignExecutionError> {
        self.used = self
            .used
            .checked_add(amount)
            .filter(|used| *used <= TYPE_WORK_LIMIT)
            .ok_or(ForeignExecutionError::WORK_EXHAUSTED)?;
        Ok(())
    }
}

fn reserve<T>(values: &mut Vec<T>, extra: usize) -> Result<(), ForeignExecutionError> {
    values
        .try_reserve(extra)
        .map_err(|_| ForeignExecutionError::STORAGE_REFUSED)
}

fn aligned(cursor: usize, alignment: usize) -> Option<usize> {
    cursor
        .checked_add(alignment.checked_sub(1)?)
        .map(|value| value & !(alignment - 1))
}

fn append(
    bytes: &mut Vec<u8>,
    contents: &[u8],
    work: &mut Work,
) -> Result<(), ForeignExecutionError> {
    work.charge(contents.len())?;
    reserve(bytes, contents.len())?;
    bytes.extend_from_slice(contents);
    Ok(())
}

fn scalar_matches(kind: ScalarKind, node: &ForeignDataNode) -> bool {
    matches!(
        (kind, node),
        (ScalarKind::Unit, ForeignDataNode::Unit)
            | (ScalarKind::Boolean, ForeignDataNode::Boolean(_))
            | (ScalarKind::Integer, ForeignDataNode::Integer(_))
            | (ScalarKind::Bytes, ForeignDataNode::Bytes(_))
            | (ScalarKind::String, ForeignDataNode::String(_))
    )
}

fn charge_scalar(work: &mut Work, node: &ForeignDataNode) -> Result<(), ForeignExecutionError> {
    let contents = match node {
        // ForeignData validation counts both the copied integer and its root
        // exposure. Charging each expanded occurrence preserves that bound.
        ForeignDataNode::Integer(value) => usize::try_from(value.magnitude_byte_length())
            .ok()
            .and_then(|size| size.max(1).checked_mul(2))
            .ok_or(ForeignExecutionError::WORK_EXHAUSTED)?,
        ForeignDataNode::Bytes(bytes) => bytes.len(),
        ForeignDataNode::String(text) => text.len(),
        _ => 0,
    };
    work.charge(contents)
}

enum DecodeTask {
    Value(usize),
    Tuple(usize),
    Constructor(ConstructorId, bool),
}

impl LayoutShape {
    fn edge_count(&self) -> usize {
        match self {
            Self::Tuple(fields) => fields.len(),
            Self::Nominal(constructors) => constructors.len(),
            _ => 0,
        }
    }

    fn edge(&self, index: usize) -> Option<usize> {
        match self {
            Self::Tuple(fields) => fields.get(index).copied(),
            Self::Nominal(constructors) => constructors.get(index)?.payload,
            _ => None,
        }
    }
}

impl LayoutGraph<'_> {
    /// Reject every by-value cycle, including an unselected constructor branch,
    /// before traversing values. Flat storage also avoids recursive destruction.
    fn validate(&self, work: &mut Work) -> Result<Vec<usize>, PreparationError> {
        let invalid = PreparationError::Refused(AllocationError::InvalidPayload);
        if self.root >= self.descriptors.len() {
            return Err(invalid);
        }
        work.charge(self.descriptors.len())
            .map_err(PreparationError::Internal)?;
        let mut ids = HashSet::new();
        ids.try_reserve(self.descriptors.len())
            .map_err(|_| PreparationError::Internal(ForeignExecutionError::STORAGE_REFUSED))?;
        for descriptor in self.descriptors {
            if !ids.insert(descriptor.id) {
                return Err(invalid);
            }
            if matches!(descriptor.shape, LayoutShape::UnsupportedReference) {
                return Err(invalid);
            }
            if let LayoutShape::Nominal(constructors) = &descriptor.shape {
                if constructors.is_empty() || u32::try_from(constructors.len() - 1).is_err() {
                    return Err(invalid);
                }
                work.charge(constructors.len())
                    .map_err(PreparationError::Internal)?;
                let mut constructors_seen = HashSet::new();
                constructors_seen
                    .try_reserve(constructors.len())
                    .map_err(|_| {
                        PreparationError::Internal(ForeignExecutionError::STORAGE_REFUSED)
                    })?;
                let owner = constructors[0].constructor.owner();
                for (ordinal, constructor) in constructors.iter().enumerate() {
                    if constructor.constructor.owner() != owner
                        || u32::try_from(ordinal).ok()
                            != Some(constructor.constructor.constructor())
                        || !constructors_seen.insert(constructor.constructor)
                    {
                        return Err(invalid);
                    }
                }
            }
        }
        let mut states = Vec::new();
        reserve(&mut states, self.descriptors.len()).map_err(PreparationError::Internal)?;
        states.resize(self.descriptors.len(), 0_u8);
        let mut alignments = Vec::new();
        reserve(&mut alignments, self.descriptors.len()).map_err(PreparationError::Internal)?;
        alignments.resize(self.descriptors.len(), 1_usize);
        let mut stack = Vec::new();
        for start in 0..self.descriptors.len() {
            if states[start] != 0 {
                continue;
            }
            reserve(&mut stack, 1).map_err(PreparationError::Internal)?;
            stack.push((start, 0_usize));
            states[start] = 1;
            while let Some((index, next)) = stack.last_mut() {
                work.charge(1).map_err(PreparationError::Internal)?;
                let descriptor = &self.descriptors[*index];
                if *next < descriptor.shape.edge_count() {
                    let child = descriptor.shape.edge(*next);
                    *next += 1;
                    if let Some(child) = child {
                        let state = *states.get(child).ok_or(invalid)?;
                        if state == 1 {
                            return Err(invalid);
                        }
                        if state == 0 {
                            states[child] = 1;
                            reserve(&mut stack, 1).map_err(PreparationError::Internal)?;
                            stack.push((child, 0));
                        }
                    }
                    continue;
                }
                let index = *index;
                let mut alignment = match &descriptor.shape {
                    LayoutShape::Scalar(ScalarKind::Unit | ScalarKind::Boolean) => 1,
                    LayoutShape::Scalar(_) => 8,
                    LayoutShape::Nominal(constructors) if constructors.len() > 1 => 4,
                    _ => 1,
                };
                for edge in 0..descriptor.shape.edge_count() {
                    work.charge(1).map_err(PreparationError::Internal)?;
                    if let Some(child) = descriptor.shape.edge(edge) {
                        alignment = alignment.max(alignments[child]);
                    }
                }
                alignments[index] = alignment;
                states[index] = 2;
                stack.pop();
            }
        }
        Ok(alignments)
    }
}

#[derive(Debug)]
pub(super) struct PreparedPayload {
    layout: PayloadLayout,
    bytes: Vec<u8>,
}

impl PreparedPayload {
    /// Expands admitted inline sharing without recursion before arena mutation.
    pub(super) fn value(
        tag: LayoutTag,
        graph: LayoutGraph<'_>,
        value: &ForeignData,
    ) -> Result<Self, PreparationError> {
        let invalid = PreparationError::Refused(AllocationError::InvalidPayload);
        let mut work = Work::default();
        let alignments = graph.validate(&mut work)?;
        let mut stack = Vec::new();
        reserve(&mut stack, 1).map_err(PreparationError::Internal)?;
        stack.push((graph.root, value.root()));
        let mut bytes = Vec::new();
        while let Some((descriptor, node)) = stack.pop() {
            work.charge(1).map_err(PreparationError::Internal)?;
            let node = value.node(node).ok_or(invalid)?;
            let start = aligned(bytes.len(), alignments[descriptor]).ok_or(invalid)?;
            let padding = start.checked_sub(bytes.len()).ok_or(invalid)?;
            work.charge(padding).map_err(PreparationError::Internal)?;
            reserve(&mut bytes, padding).map_err(PreparationError::Internal)?;
            bytes.resize(start, 0);
            match (&graph.descriptors[descriptor].shape, node) {
                (LayoutShape::Scalar(kind), node) if scalar_matches(*kind, node) => {
                    charge_scalar(&mut work, node).map_err(PreparationError::Internal)?;
                    let scalar = Self::scalar(tag, node)?;
                    append(&mut bytes, scalar.bytes(), &mut work)
                        .map_err(PreparationError::Internal)?;
                }
                (LayoutShape::Tuple(fields), ForeignDataNode::Tuple(children)) => {
                    if fields.len() != children.len() {
                        return Err(invalid);
                    }
                    work.charge(fields.len())
                        .map_err(PreparationError::Internal)?;
                    reserve(&mut stack, fields.len()).map_err(PreparationError::Internal)?;
                    stack.extend(fields.iter().copied().zip(children.iter().copied()).rev());
                }
                (LayoutShape::Nominal(constructors), ForeignDataNode::Constructor(id, child)) => {
                    let ordinal = usize::try_from(id.constructor()).map_err(|_| invalid)?;
                    let constructor = constructors.get(ordinal).ok_or(invalid)?;
                    if constructor.constructor != *id
                        || constructor.payload.is_some() != child.is_some()
                    {
                        return Err(invalid);
                    }
                    if constructors.len() > 1 {
                        append(&mut bytes, &id.constructor().to_le_bytes(), &mut work)
                            .map_err(PreparationError::Internal)?;
                    }
                    if let (Some(descriptor), Some(child)) = (constructor.payload, child) {
                        reserve(&mut stack, 1).map_err(PreparationError::Internal)?;
                        stack.push((descriptor, *child));
                    }
                }
                _ => return Err(invalid),
            }
        }
        let layout = PayloadLayout::new(tag, bytes.len(), alignments[graph.root])?;
        Ok(Self { layout, bytes })
    }

    /// Preflights the selected native primitive encoding before arena reservation.
    /// Unsupported shapes and integer narrowing refuse; host work and scratch
    /// exhaustion remain terminal. Tags never authenticate source layout facts.
    pub(super) fn scalar(
        tag: LayoutTag,
        value: &ForeignDataNode,
    ) -> Result<Self, PreparationError> {
        // Determine the complete encoding and all bounded arithmetic before
        // reserving scratch. No caller callback or arena mutation occurs here.
        let mut fixed = [0_u8; 8];
        let (contents, header, alignment): (&[u8], Option<[u8; 8]>, usize) = match value {
            ForeignDataNode::Unit => (&[], None, 1),
            ForeignDataNode::Boolean(value) => {
                fixed[0] = u8::from(*value);
                (&fixed[..1], None, 1)
            }
            ForeignDataNode::Integer(value) => {
                let integer = value
                    .to_i64()
                    .ok_or(PreparationError::Refused(AllocationError::InvalidPayload))?;
                fixed = integer.to_le_bytes();
                (&fixed, None, 8)
            }
            ForeignDataNode::Bytes(bytes) => {
                let count = u64::try_from(bytes.len())
                    .map_err(|_| PreparationError::Refused(AllocationError::InvalidPayload))?;
                (bytes, Some(count.to_le_bytes()), 8)
            }
            ForeignDataNode::String(text) => {
                let count = u64::try_from(text.len())
                    .map_err(|_| PreparationError::Refused(AllocationError::InvalidPayload))?;
                (text.as_bytes(), Some(count.to_le_bytes()), 8)
            }
            _ => return Err(PreparationError::Refused(AllocationError::InvalidPayload)),
        };
        check_work(contents.len()).map_err(PreparationError::Internal)?;
        let size = contents
            .len()
            .checked_add(if header.is_some() { 8 } else { 0 })
            .ok_or(PreparationError::Refused(AllocationError::InvalidPayload))?;
        let layout = PayloadLayout::new(tag, size, alignment)?;
        let mut bytes = scratch(size).map_err(PreparationError::Internal)?;
        if let Some(header) = header {
            bytes.extend_from_slice(&header);
        }
        bytes.extend_from_slice(contents);
        Ok(Self { layout, bytes })
    }

    pub(super) fn layout(&self) -> PayloadLayout {
        self.layout
    }

    pub(super) fn bytes(&self) -> &[u8] {
        &self.bytes
    }
}

pub(super) fn decode_value(
    graph: LayoutGraph<'_>,
    bytes: &[u8],
) -> Result<ForeignData, ForeignExecutionError> {
    let mismatch = ForeignExecutionError("arena aggregate encoding mismatch");
    let mut work = Work::default();
    let alignments = graph.validate(&mut work).map_err(|error| match error {
        PreparationError::Refused(_) => {
            ForeignExecutionError("arena aggregate descriptor mismatch")
        }
        PreparationError::Internal(error) => error,
    })?;
    // Bound hostile extents before traversal scratch or any copied packed data.
    work.charge(bytes.len())?;
    let mut tasks = Vec::new();
    reserve(&mut tasks, 1)?;
    tasks.push(DecodeTask::Value(graph.root));
    let mut nodes = Vec::new();
    let mut roots = Vec::new();
    let mut cursor = 0_usize;
    while let Some(task) = tasks.pop() {
        work.charge(1)?;
        match task {
            DecodeTask::Value(descriptor) => {
                let start = aligned(cursor, alignments[descriptor]).ok_or(mismatch)?;
                let padding = bytes.get(cursor..start).ok_or(mismatch)?;
                if padding.iter().any(|byte| *byte != 0) {
                    return Err(mismatch);
                }
                cursor = start;
                match &graph.descriptors[descriptor].shape {
                    LayoutShape::Scalar(kind) => {
                        let extent = match kind {
                            ScalarKind::Unit => 0,
                            ScalarKind::Boolean => 1,
                            ScalarKind::Integer => 8,
                            ScalarKind::Bytes | ScalarKind::String => {
                                let header_end = cursor.checked_add(8).ok_or(mismatch)?;
                                let header: [u8; 8] = bytes
                                    .get(cursor..header_end)
                                    .ok_or(mismatch)?
                                    .try_into()
                                    .map_err(|_| mismatch)?;
                                let count = usize::try_from(u64::from_le_bytes(header))
                                    .map_err(|_| mismatch)?;
                                count.checked_add(8).ok_or(mismatch)?
                            }
                        };
                        let end = cursor.checked_add(extent).ok_or(mismatch)?;
                        let contents = bytes.get(cursor..end).ok_or(mismatch)?;
                        if matches!(kind, ScalarKind::Bytes | ScalarKind::String) {
                            // Reject malformed extents before classifying work,
                            // and charge admitted contents before copying them.
                            work.charge(extent - 8)?;
                        }
                        if matches!(kind, ScalarKind::Integer) {
                            work.charge(16)?;
                        }
                        let node = decode_scalar_node(*kind, contents)?;
                        reserve(&mut roots, 1)?;
                        reserve(&mut nodes, 1)?;
                        roots.push(nodes.len());
                        nodes.push(node);
                        cursor = end;
                    }
                    LayoutShape::Tuple(fields) => {
                        work.charge(fields.len())?;
                        reserve(&mut tasks, fields.len().checked_add(1).ok_or(mismatch)?)?;
                        tasks.push(DecodeTask::Tuple(fields.len()));
                        tasks.extend(fields.iter().rev().copied().map(DecodeTask::Value));
                    }
                    LayoutShape::Nominal(constructors) => {
                        let ordinal = if constructors.len() > 1 {
                            let end = cursor.checked_add(4).ok_or(mismatch)?;
                            let encoded: [u8; 4] = bytes
                                .get(cursor..end)
                                .ok_or(mismatch)?
                                .try_into()
                                .map_err(|_| mismatch)?;
                            cursor = end;
                            usize::try_from(u32::from_le_bytes(encoded)).map_err(|_| mismatch)?
                        } else {
                            0
                        };
                        let constructor = constructors.get(ordinal).ok_or(mismatch)?;
                        reserve(&mut tasks, 2)?;
                        tasks.push(DecodeTask::Constructor(
                            constructor.constructor,
                            constructor.payload.is_some(),
                        ));
                        if let Some(child) = constructor.payload {
                            tasks.push(DecodeTask::Value(child));
                        }
                    }
                    LayoutShape::UnsupportedReference => return Err(mismatch),
                }
            }
            DecodeTask::Tuple(count) => {
                let start = roots.len().checked_sub(count).ok_or(mismatch)?;
                let mut fields = Vec::new();
                reserve(&mut fields, count)?;
                fields.extend_from_slice(&roots[start..]);
                roots.truncate(start);
                reserve(&mut nodes, 1)?;
                reserve(&mut roots, 1)?;
                roots.push(nodes.len());
                nodes.push(ForeignDataNode::Tuple(fields.into_boxed_slice()));
            }
            DecodeTask::Constructor(id, has_payload) => {
                let child = if has_payload {
                    Some(roots.pop().ok_or(mismatch)?)
                } else {
                    None
                };
                reserve(&mut nodes, 1)?;
                reserve(&mut roots, 1)?;
                roots.push(nodes.len());
                nodes.push(ForeignDataNode::Constructor(id, child));
            }
        }
    }
    if cursor != bytes.len() || roots.len() != 1 {
        return Err(mismatch);
    }
    ForeignData::new(nodes, roots[0])
}

pub(super) fn decode_scalar(
    kind: ScalarKind,
    bytes: &[u8],
) -> Result<ForeignData, ForeignExecutionError> {
    let node = decode_scalar_node(kind, bytes)?;
    let mut nodes = Vec::new();
    nodes
        .try_reserve_exact(1)
        .map_err(|_| ForeignExecutionError::STORAGE_REFUSED)?;
    nodes.push(node);
    ForeignData::new(nodes, 0)
}

fn decode_scalar_node(
    kind: ScalarKind,
    bytes: &[u8],
) -> Result<ForeignDataNode, ForeignExecutionError> {
    let mismatch = ForeignExecutionError("arena primitive encoding mismatch");
    let node = match kind {
        ScalarKind::Unit if bytes.is_empty() => ForeignDataNode::Unit,
        ScalarKind::Boolean => match bytes {
            [0] => ForeignDataNode::Boolean(false),
            [1] => ForeignDataNode::Boolean(true),
            _ => return Err(mismatch),
        },
        ScalarKind::Integer => {
            let encoded: [u8; 8] = bytes.try_into().map_err(|_| mismatch)?;
            ForeignDataNode::Integer(Integer::from_i64(i64::from_le_bytes(encoded)))
        }
        ScalarKind::Bytes | ScalarKind::String => {
            let header: [u8; 8] = bytes
                .get(..8)
                .ok_or(mismatch)?
                .try_into()
                .map_err(|_| mismatch)?;
            let count = usize::try_from(u64::from_le_bytes(header)).map_err(|_| mismatch)?;
            let extent = count.checked_add(8).ok_or(mismatch)?;
            if extent != bytes.len() {
                return Err(mismatch);
            }
            check_work(count)?;
            let contents = &bytes[8..];
            if matches!(kind, ScalarKind::String) {
                std::str::from_utf8(contents).map_err(|_| mismatch)?;
            }
            let mut copy = scratch(count)?;
            copy.extend_from_slice(contents);
            match kind {
                ScalarKind::Bytes => ForeignDataNode::Bytes(Arc::from(copy)),
                ScalarKind::String => ForeignDataNode::String(Arc::from(
                    String::from_utf8(copy).map_err(|_| mismatch)?,
                )),
                _ => return Err(mismatch),
            }
        }
        _ => return Err(mismatch),
    };
    Ok(node)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::arena::{AllocationFailure, Arena};
    use ash::foreign::runtime::ForeignExecutionReason;
    use ash::{integer::Integer, types::TYPE_WORK_LIMIT};
    use std::sync::Arc;

    fn aggregate_fixture() -> (
        Vec<LayoutDescriptor>,
        ForeignData,
        ConstructorId,
        ConstructorId,
    ) {
        use ash::types::NominalTypeId;
        let source = ash::source::SourceFile::new("arena-codec-fixture", "")
            .unwrap()
            .id();
        let sole = ConstructorId::new(NominalTypeId::new(source, 0), 0);
        let selected = ConstructorId::new(NominalTypeId::new(source, 1), 1);
        let descriptors = vec![
            LayoutDescriptor {
                id: 0,
                shape: LayoutShape::Scalar(ScalarKind::Boolean),
            },
            LayoutDescriptor {
                id: 1,
                shape: LayoutShape::Scalar(ScalarKind::Integer),
            },
            LayoutDescriptor {
                id: 2,
                shape: LayoutShape::Scalar(ScalarKind::String),
            },
            LayoutDescriptor {
                id: 3,
                shape: LayoutShape::Tuple(Box::new([0, 1, 0])),
            },
            LayoutDescriptor {
                id: 4,
                shape: LayoutShape::Nominal(Box::new([ConstructorLayout {
                    constructor: sole,
                    payload: Some(3),
                }])),
            },
            LayoutDescriptor {
                id: 5,
                shape: LayoutShape::Nominal(Box::new([
                    ConstructorLayout {
                        constructor: ConstructorId::new(selected.owner(), 0),
                        payload: None,
                    },
                    ConstructorLayout {
                        constructor: selected,
                        payload: Some(3),
                    },
                ])),
            },
            LayoutDescriptor {
                id: 6,
                shape: LayoutShape::Tuple(Box::new([4, 5, 2])),
            },
        ];
        let data = ForeignData::new(
            vec![
                ForeignDataNode::Boolean(true),
                ForeignDataNode::Integer(Integer::from_i64(41)),
                ForeignDataNode::Boolean(false),
                ForeignDataNode::Tuple(Box::new([0, 1, 2])),
                ForeignDataNode::Constructor(sole, Some(3)),
                ForeignDataNode::Constructor(selected, Some(3)),
                ForeignDataNode::String(Arc::from("λ\0🙂")),
                ForeignDataNode::Tuple(Box::new([4, 5, 6])),
            ],
            7,
        )
        .unwrap();
        (descriptors, data, sole, selected)
    }

    #[test]
    fn nested_tuples_and_nominal_payloads_roundtrip_through_native_storage() {
        let (descriptors, data, sole, selected) = aggregate_fixture();
        let graph = LayoutGraph {
            descriptors: &descriptors,
            root: 6,
        };
        let tag = LayoutTag::new(100);
        let payload = PreparedPayload::value(tag, graph, &data).unwrap();
        assert_eq!(payload.layout().natural_alignment(), 8);
        assert_eq!(payload.layout().size(), 71);
        assert_eq!(&payload.bytes()[24..28], &1_u32.to_le_bytes());
        assert_eq!(&payload.bytes()[17..24], &[0; 7]);
        assert_eq!(&payload.bytes()[28..32], &[0; 4]);
        let mut arena = Arena::new(payload.layout().size(), 1).unwrap();
        let key = publish(&mut arena, &payload);
        let copy = decode_value(graph, arena.read(key, tag).unwrap()).unwrap();
        drop(arena);
        let Some(ForeignDataNode::Tuple(fields)) = copy.node(copy.root()) else {
            panic!("missing copied tuple")
        };
        assert_eq!(fields.len(), 3);
        for (field, constructor) in [(fields[0], sole), (fields[1], selected)] {
            let Some(ForeignDataNode::Constructor(actual, Some(child))) = copy.node(field) else {
                panic!("missing copied constructor")
            };
            assert_eq!(*actual, constructor);
            let Some(ForeignDataNode::Tuple(values)) = copy.node(*child) else {
                panic!("missing copied constructor payload")
            };
            assert!(matches!(
                copy.node(values[0]),
                Some(ForeignDataNode::Boolean(true))
            ));
            assert!(
                matches!(copy.node(values[1]), Some(ForeignDataNode::Integer(value)) if value.to_i64() == Some(41))
            );
            assert!(matches!(
                copy.node(values[2]),
                Some(ForeignDataNode::Boolean(false))
            ));
        }
        assert!(
            matches!(copy.node(fields[2]), Some(ForeignDataNode::String(value)) if value.as_ref() == "λ\0🙂")
        );
        // Natural alignment belongs to the complete nominal layout, even when
        // the selected constructor has no child and occupies only its tag.
        let empty_id = ConstructorId::new(selected.owner(), 0);
        let empty =
            ForeignData::new(vec![ForeignDataNode::Constructor(empty_id, None)], 0).unwrap();
        let nominal_graph = LayoutGraph {
            descriptors: &descriptors,
            root: 5,
        };
        let payload = PreparedPayload::value(tag, nominal_graph, &empty).unwrap();
        assert_eq!(payload.layout().size(), 4);
        assert_eq!(payload.layout().natural_alignment(), 8);
        let mut arena = Arena::new(4, 1).unwrap();
        let key = publish(&mut arena, &payload);
        let copied = decode_value(nominal_graph, arena.read(key, tag).unwrap()).unwrap();
        assert!(
            matches!(copied.node(copied.root()), Some(ForeignDataNode::Constructor(id, None)) if *id == empty_id)
        );
    }

    #[test]
    fn aggregate_corruption_cycles_and_expanded_sharing_refuse_without_publication() {
        let (descriptors, data, _, _) = aggregate_fixture();
        let graph = LayoutGraph {
            descriptors: &descriptors,
            root: 6,
        };
        let tag = LayoutTag::new(101);
        let payload = PreparedPayload::value(tag, graph, &data).unwrap();
        let mut arena = Arena::new(80, 2).unwrap();
        let key = publish(&mut arena, &payload);
        let before = arena.usage();
        for position in [0, 17, 28] {
            let mut corrupt = arena.read(key, tag).unwrap().to_vec();
            corrupt[position] = 2;
            assert!(decode_value(graph, &corrupt).is_err());
        }
        let mut corrupt = arena.read(key, tag).unwrap().to_vec();
        corrupt[24..28].copy_from_slice(&2_u32.to_le_bytes());
        assert!(decode_value(graph, &corrupt).is_err());
        for shape in [
            LayoutShape::Tuple(Box::new([0])),
            LayoutShape::UnsupportedReference,
        ] {
            let invalid = [LayoutDescriptor { id: 0, shape }];
            assert!(matches!(
                PreparedPayload::value(
                    tag,
                    LayoutGraph {
                        descriptors: &invalid,
                        root: 0
                    },
                    &data
                ),
                Err(PreparationError::Refused(AllocationError::InvalidPayload))
            ));
        }
        let (mut shuffled, _, _, _) = aggregate_fixture();
        let LayoutShape::Nominal(constructors) = &mut shuffled[5].shape else {
            unreachable!()
        };
        constructors.swap(0, 1);
        assert!(matches!(
            PreparedPayload::value(
                tag,
                LayoutGraph {
                    descriptors: &shuffled,
                    root: 6
                },
                &data
            ),
            Err(PreparationError::Refused(AllocationError::InvalidPayload))
        ));
        // A compact backward-referencing input may expand to a much larger
        // inline tree. Charge repeated visits, even for zero-byte Unit leaves.
        let mut shared_descriptors = vec![LayoutDescriptor {
            id: 0,
            shape: LayoutShape::Scalar(ScalarKind::Unit),
        }];
        let mut nodes = vec![ForeignDataNode::Unit];
        for level in 1..20 {
            shared_descriptors.push(LayoutDescriptor {
                id: level as u64,
                shape: LayoutShape::Tuple(Box::new([level - 1, level - 1])),
            });
            nodes.push(ForeignDataNode::Tuple(Box::new([level - 1, level - 1])));
        }
        let shared = ForeignData::new(nodes, 19).unwrap();
        let shared_graph = LayoutGraph {
            descriptors: &shared_descriptors,
            root: 19,
        };
        assert!(matches!(
            PreparedPayload::value(tag, shared_graph, &shared),
            Err(PreparationError::Internal(error))
                if error.reason() == ForeignExecutionReason::WorkExhausted
        ));
        assert!(decode_value(shared_graph, &[]).is_err());
        assert_eq!(arena.usage(), before);
        assert_eq!(arena.read(key, tag).unwrap(), payload.bytes());
    }

    fn publish(arena: &mut Arena, payload: &PreparedPayload) -> crate::arena::AllocationKey {
        arena
            .allocate(payload.layout(), 0, |bytes| {
                bytes.copy_from_slice(payload.bytes());
                Ok::<_, ()>(())
            })
            .unwrap()
    }

    #[test]
    fn primitive_values_roundtrip_through_native_storage_and_survive_owner_completion() {
        let mut arena = Arena::new(96, 9).unwrap();
        let values = [
            (ScalarKind::Unit, ForeignDataNode::Unit, 0, 1),
            (ScalarKind::Boolean, ForeignDataNode::Boolean(true), 1, 1),
            (
                ScalarKind::Integer,
                ForeignDataNode::Integer(Integer::from_i64(i64::MIN)),
                8,
                8,
            ),
            (
                ScalarKind::Integer,
                ForeignDataNode::Integer(Integer::from_i64(i64::MAX)),
                8,
                8,
            ),
            (
                ScalarKind::Bytes,
                ForeignDataNode::Bytes(Arc::from([0, 255, 128])),
                11,
                8,
            ),
            (
                ScalarKind::String,
                ForeignDataNode::String(Arc::from("λ\0🙂")),
                15,
                8,
            ),
            (
                ScalarKind::Bytes,
                ForeignDataNode::Bytes(Arc::from([])),
                8,
                8,
            ),
            (
                ScalarKind::String,
                ForeignDataNode::String(Arc::from("")),
                8,
                8,
            ),
            (ScalarKind::Unit, ForeignDataNode::Unit, 0, 1),
        ];
        let mut copies = Vec::new();
        for (index, (kind, value, size, alignment)) in values.into_iter().enumerate() {
            let tag = LayoutTag::new(index as u64);
            let payload = PreparedPayload::scalar(tag, &value).unwrap();
            assert_eq!(payload.layout().size(), size);
            assert_eq!(payload.layout().natural_alignment(), alignment);
            let key = publish(&mut arena, &payload);
            let stored = arena.read(key, tag).unwrap();
            if !stored.is_empty() {
                assert_eq!(stored.as_ptr() as usize % alignment, 0);
            }
            let copy = decode_scalar(kind, stored).unwrap();
            copies.push((value, copy));
        }
        assert_eq!(arena.usage().object_count, 9);
        drop(arena);
        for (original, copy) in copies {
            // ForeignData deliberately has no structural equality: compare the
            // admitted scalar roots after their native owner has completed.
            assert_eq!(
                format!("{original:?}"),
                format!("{:?}", copy.node(copy.root()).unwrap())
            );
        }
    }

    #[test]
    fn refused_preparation_and_publication_preserve_an_earlier_native_object() {
        let mut arena = Arena::new(16, 2).unwrap();
        let tag = LayoutTag::new(42);
        let first = PreparedPayload::scalar(tag, &ForeignDataNode::Boolean(false)).unwrap();
        let key = publish(&mut arena, &first);
        let before = arena.usage();
        assert!(matches!(
            PreparedPayload::scalar(
                tag,
                &ForeignDataNode::Bytes(Arc::from(vec![0; TYPE_WORK_LIMIT]))
            ),
            Err(PreparationError::Internal(error))
                if error.reason() == ForeignExecutionReason::WorkExhausted
        ));
        for value in [
            ForeignDataNode::Integer(Integer::parse_decimal("9223372036854775808").unwrap()),
            ForeignDataNode::Integer(&Integer::from_i64(i64::MIN) + &Integer::from_i64(-1)),
            ForeignDataNode::State(0),
            ForeignDataNode::Tuple(Box::new([])),
        ] {
            assert!(matches!(
                PreparedPayload::scalar(tag, &value),
                Err(PreparationError::Refused(AllocationError::InvalidPayload))
            ));
            assert_eq!(arena.usage(), before);
            assert_eq!(arena.read(key, tag).unwrap(), &[0]);
        }
        let large = PreparedPayload::scalar(tag, &ForeignDataNode::Bytes(Arc::from([1]))).unwrap();
        assert_eq!(
            arena.allocate(large.layout(), 0, |_| Ok::<_, ()>(())),
            Err(AllocationFailure::Refused(AllocationError::OutOfPayload))
        );
        let integer =
            PreparedPayload::scalar(tag, &ForeignDataNode::Integer(Integer::from_i64(41))).unwrap();
        assert_eq!(
            arena.allocate(integer.layout(), 0, |bytes| {
                bytes.copy_from_slice(integer.bytes());
                Err("result admission refused")
            }),
            Err(AllocationFailure::Initialization(
                "result admission refused"
            ))
        );
        assert_eq!(arena.usage(), before);
        assert_eq!(arena.read(key, tag).unwrap(), &[0]);
        let integer_key = publish(&mut arena, &integer);
        assert_eq!(arena.usage().used_payload_bytes, 16);
        assert_eq!(arena.read(integer_key, tag).unwrap(), &41_i64.to_le_bytes());
        let unit = PreparedPayload::scalar(tag, &ForeignDataNode::Unit).unwrap();
        assert_eq!(
            arena.allocate(unit.layout(), 0, |_| Ok::<_, ()>(())),
            Err(AllocationFailure::Refused(AllocationError::OutOfObjects))
        );
        assert_eq!(arena.read(key, tag).unwrap(), &[0]);
    }

    #[test]
    fn malformed_dynamic_headers_remain_binding_failures_before_work_charges() {
        for kind in [ScalarKind::Bytes, ScalarKind::String] {
            let descriptors = [LayoutDescriptor {
                id: 0,
                shape: LayoutShape::Scalar(kind),
            }];
            let graph = LayoutGraph {
                descriptors: &descriptors,
                root: 0,
            };
            for count in [u64::try_from(TYPE_WORK_LIMIT).unwrap() + 1, u64::MAX] {
                let bytes = count.to_le_bytes();
                assert_eq!(
                    decode_scalar(kind, &bytes).unwrap_err().reason(),
                    ForeignExecutionReason::Binding
                );
                assert_eq!(
                    decode_value(graph, &bytes).unwrap_err().reason(),
                    ForeignExecutionReason::Binding
                );
            }
        }
    }

    #[test]
    fn malformed_native_contents_are_rejected_without_a_copied_result() {
        for (kind, bytes) in [
            (ScalarKind::Unit, vec![0]),
            (ScalarKind::Boolean, vec![2]),
            (ScalarKind::Integer, vec![0; 7]),
            (ScalarKind::Bytes, vec![0; 7]),
            (
                ScalarKind::Bytes,
                [2_u64.to_le_bytes().as_slice(), &[1]].concat(),
            ),
            (
                ScalarKind::Bytes,
                [0_u64.to_le_bytes().as_slice(), &[1]].concat(),
            ),
            (ScalarKind::Bytes, u64::MAX.to_le_bytes().to_vec()),
            (
                ScalarKind::String,
                [1_u64.to_le_bytes().as_slice(), &[255]].concat(),
            ),
        ] {
            assert!(decode_scalar(kind, &bytes).is_err());
        }
    }
}


/// Production scalar entry: the authenticated caller supplies the full
/// dictionary and pays conversion plus the eventual native byte copy first.
pub(super) fn prepare_scalar_with_work(
    tag: LayoutTag,
    value: &ForeignDataNode,
    work: &mut ash::foreign::runtime::ForeignInvocationWork<'_>,
) -> Result<PreparedPayload, PreparationError> {
    let (conversion, extent) = match value {
        ForeignDataNode::Unit => (1, 0),
        ForeignDataNode::Boolean(_) => (1, 1),
        ForeignDataNode::Integer(integer) => (
            usize::try_from(integer.magnitude_byte_length()).map_err(|_| PreparationError::Internal(ForeignExecutionError::WORK_EXHAUSTED))?.max(1),
            8,
        ),
        _ => return Err(PreparationError::Internal(ForeignExecutionError("unsupported arena scalar"))),
    };
    let units = conversion.checked_add(extent).and_then(|units| units.checked_add(extent))
        .ok_or(PreparationError::Internal(ForeignExecutionError::WORK_EXHAUSTED))?;
    work.charge(units).map_err(PreparationError::Internal)?;
    PreparedPayload::scalar(tag, value)
}

pub(super) fn decode_scalar_with_work(
    kind: ScalarKind,
    bytes: &[u8],
    work: &mut ash::foreign::runtime::ForeignInvocationWork<'_>,
) -> Result<ForeignData, ForeignExecutionError> {
    work.charge(bytes.len().checked_add(1).ok_or(ForeignExecutionError::WORK_EXHAUSTED)?)?;
    decode_scalar(kind, bytes)
}
