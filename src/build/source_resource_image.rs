//! Passive product source-resource construction records. Defining forests are
//! restored unchecked, checked as lifecycle templates, then compared with each
//! specialized scope by the ordinary final Core validator.

use super::{
    ArmRecord, BinderIdentity, Decoder, EffectIdentity, Encoder, ImageFailure,
    NativeInterpretationRecord, NodeRecord, NominalId, OperationIdentity, ParameterBuffer,
    QuantifierRecord, ResolvedTypeRecord, Slice, SpanRecord, StructuralInput, TypeVariableIdentity,
    Unsupported, Wire, WireReader, WireWriter, append, charge, get, index, push,
};
use crate::{
    core::source_resource::{
        CheckedSourceResourceHeader, CheckedSourceResourceTemplate, SourceResourceCopyClaim,
        SourceResourceLifecycleEntry, SourceResourceScopeNode,
    },
    core::{EffectOperationFamily, NodeId, UnvalidatedEffectProgram},
    resolved::{
        ResolvedEffectInstance, ResolvedInterfaceApplication, ResolvedInterfaceOccurrence,
        ResolvedOwnerArgument, ResolvedRegistry, ResolvedType, SourceResourceTypeFact,
    },
    types::{
        EffectInstance, EffectRow, Kind, ResourceDefinitionId, Type, TypeVariableId, TypeWorkBudget,
    },
};
use std::{collections::HashMap, sync::Arc};

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub(super) struct ResourceIdentity {
    pub(super) module: u32,
    pub(super) local: u32,
}
#[derive(Clone, Copy, Debug)]
pub(super) struct InterfaceIdentity {
    module: u32,
    local: u32,
}
#[derive(Clone, Copy, Debug)]
pub(super) struct InterfaceOwnerRecord {
    id: InterfaceIdentity,
    parameters: Slice,
}
#[derive(Clone, Copy, Debug)]
pub(super) struct ResourceArgumentRecord {
    argument: u32,
    provenance: u32,
    origin: u32,
    span: SpanRecord,
}
#[derive(Clone, Copy, Debug)]
pub(super) struct ResourceEffectRecord {
    effect: u32,
    arguments: Slice,
    origin: u32,
    span: SpanRecord,
}
#[derive(Clone, Copy, Debug)]
pub(super) struct ResourceHeaderRecord {
    id: ResourceIdentity,
    family: NominalId,
    public: bool,
    spelling: Slice,
    parameters: Slice,
    owned_position: u32,
    owned_origin: u32,
    input: ResolvedTypeRecord,
    state: ResolvedTypeRecord,
    data: ResolvedTypeRecord,
    acquisition: ResolvedTypeRecord,
    completion: ResolvedTypeRecord,
    result: ResolvedTypeRecord,
    answer: u32,
    codec_scope: bool,
    codec_span: SpanRecord,
    provider: InterfaceIdentity,
    provider_spelling: Slice,
    provider_origin: u32,
    provider_arguments: Slice,
    provider_span: SpanRecord,
    provided: ResourceEffectRecord,
    interpreted: Slice,
    origin: u32,
}
#[derive(Clone, Copy, Debug)]
pub(super) struct HandlerRecord {
    id: u32,
    body: u32,
    effect: u32,
    clauses: Slice,
}
#[derive(Clone, Copy, Debug)]
pub(super) struct ClauseRecord {
    operation: OperationIdentity,
    resume: u32,
    arm: ArmRecord,
}
#[derive(Clone, Copy, Debug)]
pub(super) struct TemplateGraphRecord {
    nodes: Slice,
    root: u32,
    catalog: u32,
}
#[derive(Clone, Copy, Debug)]
pub(super) struct SourceTemplateRecord {
    header: u32,
    acquire: u32,
    finish: u32,
    handler: u32,
}
#[derive(Clone, Copy, Debug)]
pub(super) struct NodePairRecord {
    original: u32,
    copied: u32,
}
#[derive(Clone, Copy, Debug)]
pub(super) struct BinderPairRecord {
    original: BinderIdentity,
    copied: BinderIdentity,
}
#[derive(Clone, Copy, Debug)]
pub(super) struct FreshTypeRecord {
    original: TypeVariableIdentity,
    copied: TypeVariableIdentity,
    kind: u32,
}
#[derive(Clone, Copy, Debug)]
pub(super) struct PlainPairRecord {
    original: u32,
    copied: u32,
}
#[derive(Clone, Copy, Debug)]
pub(super) struct SourceSubstitutionRecord {
    original: TypeVariableIdentity,
    value: u32,
}
#[derive(Clone, Copy, Debug)]
pub(super) struct SourceCopyRecord {
    nodes: Slice,
    binders: Slice,
    variables: Slice,
    handlers: Slice,
    resumes: Slice,
    types: Slice,
    rows: Slice,
}
#[derive(Clone, Copy, Debug)]
pub(super) struct SourceScopeRecord {
    template: u32,
    arguments: Slice,
    pub(super) identity: TypeVariableIdentity,
    initializer: u32,
    acquire_parameter: u32,
    acquire_body: u32,
    finish_parameter: u32,
    finish_body: u32,
    handler_state: u32,
    handler_pattern: u32,
    handle: u32,
    handler: u32,
    output_value: u32,
    output_effects: u32,
    acquire_copy: u32,
    finish_copy: u32,
    handler_copy: u32,
    pub(super) interpretations: Slice,
}

wire_struct!(ResourceIdentity, 8, module, local);
wire_struct!(InterfaceIdentity, 8, module, local);
wire_struct!(InterfaceOwnerRecord, 16, id, parameters);
wire_struct!(
    ResourceArgumentRecord,
    24,
    argument,
    provenance,
    origin,
    span
);
wire_struct!(ResourceEffectRecord, 28, effect, arguments, origin, span);
wire_struct!(
    ResourceHeaderRecord,
    282,
    id,
    family,
    public,
    spelling,
    parameters,
    owned_position,
    owned_origin,
    input,
    state,
    data,
    acquisition,
    completion,
    result,
    answer,
    codec_scope,
    codec_span,
    provider,
    provider_spelling,
    provider_origin,
    provider_arguments,
    provider_span,
    provided,
    interpreted,
    origin
);
wire_struct!(HandlerRecord, 20, id, body, effect, clauses);
wire_struct!(ClauseRecord, 28, operation, resume, arm);
wire_struct!(TemplateGraphRecord, 16, nodes, root, catalog);
wire_struct!(SourceTemplateRecord, 16, header, acquire, finish, handler);
wire_struct!(NodePairRecord, 8, original, copied);
wire_struct!(BinderPairRecord, 10, original, copied);
wire_struct!(FreshTypeRecord, 14, original, copied, kind);
wire_struct!(PlainPairRecord, 8, original, copied);
wire_struct!(SourceSubstitutionRecord, 9, original, value);
wire_struct!(
    SourceCopyRecord,
    56,
    nodes,
    binders,
    variables,
    handlers,
    resumes,
    types,
    rows
);
wire_struct!(
    SourceScopeRecord,
    81,
    template,
    arguments,
    identity,
    initializer,
    acquire_parameter,
    acquire_body,
    finish_parameter,
    finish_body,
    handler_state,
    handler_pattern,
    handle,
    handler,
    output_value,
    output_effects,
    acquire_copy,
    finish_copy,
    handler_copy,
    interpretations
);

#[derive(Clone, Copy, Debug)]
pub(super) struct MethodCatalogRecord {
    methods: Slice,
}
#[derive(Clone, Copy, Debug)]
pub(super) struct MethodRecord {
    interface: InterfaceIdentity,
    local: u32,
    interface_parameters: Slice,
    inherited_parameters: Slice,
    parameters: Slice,
    value_type: u32,
}
#[derive(Clone, Copy, Debug)]
pub(super) enum OwnerIdentity {
    Effect(EffectIdentity),
    Interface(InterfaceIdentity),
    Resource(ResourceIdentity),
}
#[derive(Clone, Copy, Debug)]
pub(super) struct InheritedParameterRecord {
    owner: OwnerIdentity,
    slot: u32,
    binder: TypeVariableIdentity,
}
wire_struct!(MethodCatalogRecord, 8, methods);
wire_struct!(
    MethodRecord,
    40,
    interface,
    local,
    interface_parameters,
    inherited_parameters,
    parameters,
    value_type
);
wire_struct!(InheritedParameterRecord, 18, owner, slot, binder);
impl Wire for OwnerIdentity {
    const MINIMUM: usize = 9;
    fn write(&self, writer: &mut WireWriter<'_>) -> Result<(), ImageFailure> {
        match self {
            Self::Effect(id) => {
                0u8.write(writer)?;
                id.write(writer)
            }
            Self::Interface(id) => {
                1u8.write(writer)?;
                id.write(writer)
            }
            Self::Resource(id) => {
                2u8.write(writer)?;
                id.write(writer)
            }
        }
    }
    fn read(reader: &mut WireReader<'_>) -> Result<Self, ImageFailure> {
        Ok(match u8::read(reader)? {
            0 => Self::Effect(Wire::read(reader)?),
            1 => Self::Interface(Wire::read(reader)?),
            2 => Self::Resource(Wire::read(reader)?),
            _ => return Err(ImageFailure::InvalidEncoding),
        })
    }
}

pub(super) struct EncodedSourceTemplate {
    slot: u32,
    mappings: [Vec<Option<u32>>; 3],
}
pub(super) struct RestoredSourceTemplate {
    template: Arc<CheckedSourceResourceTemplate>,
    nodes: [Vec<NodeId>; 3],
}

impl InterfaceOwnerRecord {
    pub(super) fn parameters(&self) -> Slice {
        self.parameters
    }
}

impl Encoder<'_> {
    pub(super) fn resource_identity(
        &mut self,
        id: ResourceDefinitionId,
    ) -> Result<ResourceIdentity, ImageFailure> {
        Ok(ResourceIdentity {
            module: self.module(id.module())?,
            local: id.ordinal(),
        })
    }
    fn interface_identity(
        &mut self,
        id: crate::interface::InterfaceId,
    ) -> Result<InterfaceIdentity, ImageFailure> {
        Ok(InterfaceIdentity {
            module: self.module(id.module())?,
            local: id.declaration(),
        })
    }
    fn resolved_type_record(
        &mut self,
        original: &ResolvedType,
    ) -> Result<ResolvedTypeRecord, ImageFailure> {
        Ok(ResolvedTypeRecord {
            ty: self.encode_type(&original.ty)?,
            provenance: self.encode_provenance(&original.provenance)?,
            origin: self.encode_origin(&original.origin)?,
            span: self.span(original.span)?,
        })
    }
    fn resource_effect(
        &mut self,
        original: &ResolvedEffectInstance,
    ) -> Result<ResourceEffectRecord, ImageFailure> {
        let effect = self.encode_structural(StructuralInput::Instance(&original.instance))?;
        let start = self.image.resource_provenance.len();
        for original in &original.argument_provenance {
            let root = self.encode_provenance(original)?;
            push(&mut self.image.resource_provenance, root, self.work)?;
        }
        Ok(ResourceEffectRecord {
            effect,
            arguments: Slice::of(&self.image.resource_provenance, start)?,
            origin: self.encode_origin(&original.origin)?,
            span: self.span(original.span)?,
        })
    }
    pub(super) fn encode_source_headers(
        &mut self,
        registry: &ResolvedRegistry,
    ) -> Result<(), ImageFailure> {
        for (id, parameters) in registry.image_interface_owner_definitions() {
            let id = self.interface_identity(id)?;
            let start = self.image.parameters.len();
            for parameter in parameters {
                self.encode_parameter(parameter)?;
            }
            push(
                &mut self.image.interface_owners,
                InterfaceOwnerRecord {
                    id,
                    parameters: Slice::of(&self.image.parameters, start)?,
                },
                self.work,
            )?;
        }
        for header in registry.source_resource_facts() {
            self.encode_source_header(header)?;
        }
        let mut selected = HashMap::new();
        charge(self.work, registry.type_variable_count())?;
        selected
            .try_reserve(registry.type_variable_count())
            .map_err(|_| ImageFailure::Resource)?;
        for (_, parameters) in registry.nominal_parameter_entries() {
            for parameter in parameters {
                selected.insert(parameter.id, ());
            }
        }
        for effect in registry.effects() {
            for parameter in &effect.parameters {
                selected.insert(parameter.id, ());
            }
        }
        for row in registry.global_parameter_rows() {
            for id in row.parameters() {
                selected.insert(*id, ());
            }
        }
        for (_, parameters) in registry.image_interface_owner_definitions() {
            for parameter in parameters {
                selected.insert(parameter.id, ());
            }
        }
        for header in registry.source_resource_facts() {
            for parameter in &header.parameters {
                selected.insert(parameter.id, ());
            }
            selected.insert(header.answer.id, ());
        }
        // The admission inventory permits only actual scope Fresh identities here.
        for parameter in registry.type_variables() {
            if !selected.contains_key(&parameter.id) {
                let slot = self.encode_parameter(parameter)?;
                push(&mut self.image.source_parameters, slot, self.work)?;
            }
        }
        Ok(())
    }
    fn encode_source_header(
        &mut self,
        header: &Arc<SourceResourceTypeFact>,
    ) -> Result<u32, ImageFailure> {
        charge(self.work, 1)?;
        if let Some((pointer, slot)) = self.source_headers.get(&header.id) {
            return if *pointer == Arc::as_ptr(header) {
                Ok(*slot)
            } else {
                Err(ImageFailure::InvalidRecord)
            };
        }
        self.source_headers
            .try_reserve(1)
            .map_err(|_| ImageFailure::Resource)?;
        let id = self.resource_identity(header.id)?;
        let family = self.nominal(header.family)?;
        let spelling = append(&mut self.image.bytes, header.spelling.as_bytes(), self.work)?;
        let start = self.image.parameters.len();
        for parameter in &header.parameters {
            self.encode_parameter(parameter)?;
        }
        let parameters = Slice::of(&self.image.parameters, start)?;
        let answer = self.encode_parameter(&header.answer)?;
        for slot in parameters.start
            ..parameters
                .start
                .checked_add(parameters.len)
                .ok_or(ImageFailure::Resource)?
        {
            push(&mut self.image.source_parameters, slot, self.work)?;
        }
        push(&mut self.image.source_parameters, answer, self.work)?;
        let start = self.image.resource_arguments.len();
        for argument in &header.provider.arguments {
            let record = ResourceArgumentRecord {
                argument: self.encode_structural(StructuralInput::Argument(&argument.ty))?,
                provenance: self.encode_provenance(&argument.provenance)?,
                origin: self.encode_origin(&argument.origin)?,
                span: self.span(argument.span)?,
            };
            push(&mut self.image.resource_arguments, record, self.work)?;
        }
        let provider_arguments = Slice::of(&self.image.resource_arguments, start)?;
        let start = self.image.resource_effects.len();
        for effect in &header.interpreted {
            let effect = self.resource_effect(effect)?;
            push(&mut self.image.resource_effects, effect, self.work)?;
        }
        let interpreted = Slice::of(&self.image.resource_effects, start)?;
        let record = ResourceHeaderRecord {
            id,
            family,
            public: header.public,
            spelling,
            parameters,
            owned_position: index(header.owned_position)?,
            owned_origin: self.encode_origin(&header.owned_origin)?,
            input: self.resolved_type_record(&header.input)?,
            state: self.resolved_type_record(&header.state)?,
            data: self.resolved_type_record(&header.data)?,
            acquisition: self.resolved_type_record(&header.acquisition)?,
            completion: self.resolved_type_record(&header.completion)?,
            result: self.resolved_type_record(&header.result)?,
            answer,
            codec_scope: header.codec.kind == crate::surface::SurfaceResourceReportCodecKind::Scope,
            codec_span: self.span(header.codec.span)?,
            provider: self.interface_identity(header.provider.interface.id)?,
            provider_spelling: append(
                &mut self.image.bytes,
                header.provider.interface.spelling.as_bytes(),
                self.work,
            )?,
            provider_origin: self.encode_origin(&header.provider.interface.origin)?,
            provider_arguments,
            provider_span: self.span(header.provider.span)?,
            provided: self.resource_effect(&header.provided)?,
            interpreted,
            origin: self.encode_origin(&header.origin)?,
        };
        let slot = push(&mut self.image.resource_headers, record, self.work)?;
        self.source_headers
            .insert(header.id, (Arc::as_ptr(header), slot));
        Ok(slot)
    }
    pub(super) fn encode_handler(
        &mut self,
        handler: &crate::core::HandlerNode,
    ) -> Result<u32, ImageFailure> {
        if handler.has_hook_contracts() {
            return Err(ImageFailure::Unsupported(Unsupported::EffectOperation));
        }
        let start = self.image.source_clauses.len();
        for clause in handler.clauses() {
            let record = ClauseRecord {
                operation: self.operation_identity(clause.operation())?,
                resume: clause.resume().value(),
                arm: ArmRecord {
                    pattern: self.encode_pattern(clause.pattern())?,
                    body: self.node(clause.body())?,
                    origin: self.encode_origin(clause.origin())?,
                },
            };
            push(&mut self.image.source_clauses, record, self.work)?;
        }
        let record = HandlerRecord {
            id: handler.id().value(),
            body: self.node(handler.body())?,
            effect: self.encode_structural(StructuralInput::Instance(handler.effect()))?,
            clauses: Slice::of(&self.image.source_clauses, start)?,
        };
        push(&mut self.image.source_handlers, record, self.work)
    }

    /// Temporarily uses the same node encoder with a separate flat arena. No
    /// checked program or second normalized source contract is constructed.
    fn encode_template_graph(
        &mut self,
        original: &UnvalidatedEffectProgram,
    ) -> Result<(u32, Vec<Option<u32>>), ImageFailure> {
        let main_nodes = std::mem::take(&mut self.image.nodes);
        let main_mapping = std::mem::take(&mut self.remapped);
        // Generated binder identities belong to their defining arena. Different
        // original forests may reuse one identity with different typed records.
        // Keep the wire records append-only, but intern within this forest only.
        let main_binders = std::mem::take(&mut self.binders);
        let result = (|| {
            let count = original.image_node_count();
            charge(self.work, count)?;
            self.remapped
                .try_reserve_exact(count)
                .map_err(|_| ImageFailure::Resource)?;
            self.remapped.resize(count, None);
            let mut pending = Vec::new();
            push(&mut pending, (original.image_root(), false), self.work)?;
            while let Some((id, finish)) = pending.pop() {
                charge(self.work, 1)?;
                let node_index = original
                    .image_node_index(id)
                    .ok_or(ImageFailure::InvalidRecord)?;
                if self.node(id).is_ok() {
                    continue;
                }
                let (expression_ty, expression_effects, expression_origin, expression_kind) =
                    original
                        .image_node(node_index)
                        .ok_or(ImageFailure::InvalidRecord)?;
                if finish {
                    let ty = self.encode_type(expression_ty)?;
                    let origin = self.encode_origin(
                        expression_origin
                            .as_ref()
                            .ok_or(ImageFailure::InvalidRecord)?,
                    )?;
                    let tag = self.encode_effect_node(expression_kind)?;
                    let effects =
                        Some(self.encode_structural(StructuralInput::Row(expression_effects))?);
                    let slot = push(
                        &mut self.image.nodes,
                        NodeRecord {
                            effects,
                            tag,
                            ty,
                            origin,
                        },
                        self.work,
                    )?;
                    *self
                        .remapped
                        .get_mut(node_index)
                        .ok_or(ImageFailure::InvalidRecord)? = Some(slot);
                } else {
                    push(&mut pending, (id, true), self.work)?;
                    let count = <EffectOperationFamily as crate::core::dialect::CoreOperationFamily>::child_count(expression_kind);
                    charge(self.work, count)?;
                    for child in (0..count).rev() {
                        let child = <EffectOperationFamily as crate::core::dialect::CoreOperationFamily>::child_at(expression_kind, child)
                            .ok_or(ImageFailure::InvalidRecord)?;
                        push(&mut pending, (child, false), self.work)?;
                    }
                }
            }
            if self.image.nodes.len() != count {
                return Err(ImageFailure::InvalidRecord);
            }
            let root = self.node(original.image_root())?;
            let nodes = append(&mut self.image.template_nodes, &self.image.nodes, self.work)?;
            let catalog = self.encode_method_catalog(original.method_evidence())?;
            let graph = push(
                &mut self.image.source_graphs,
                TemplateGraphRecord {
                    nodes,
                    root,
                    catalog,
                },
                self.work,
            )?;
            Ok((graph, std::mem::take(&mut self.remapped)))
        })();
        self.image.nodes = main_nodes;
        self.remapped = main_mapping;
        self.binders = main_binders;
        result
    }
    fn encode_source_template(
        &mut self,
        original: &Arc<CheckedSourceResourceTemplate>,
    ) -> Result<u32, ImageFailure> {
        charge(self.work, 1)?;
        let key = Arc::as_ptr(original);
        if let Some(template) = self.source_templates.get(&key) {
            return Ok(template.slot);
        }
        self.source_templates
            .try_reserve(1)
            .map_err(|_| ImageFailure::Resource)?;
        let header = self.encode_source_header(&original.header().original)?;
        let (acquire, acquire_mapping) = self.encode_template_graph(original.original_acquire())?;
        let (finish, finish_mapping) = self.encode_template_graph(original.original_finish())?;
        let (handler, handler_mapping) = self.encode_template_graph(original.original_handler())?;
        let slot = push(
            &mut self.image.source_templates,
            SourceTemplateRecord {
                header,
                acquire,
                finish,
                handler,
            },
            self.work,
        )?;
        self.source_templates.insert(
            key,
            EncodedSourceTemplate {
                slot,
                mappings: [acquire_mapping, finish_mapping, handler_mapping],
            },
        );
        Ok(slot)
    }

    pub(super) fn encode_source_scope(
        &mut self,
        scope: &SourceResourceScopeNode,
    ) -> Result<u32, ImageFailure> {
        let template = self.encode_source_template(scope.original())?;
        // Maps are moved out temporarily so each copy can use the common paid
        // encoder without cloning the defining graph's node coordinates.
        let key = Arc::as_ptr(scope.original());
        let retained = self
            .source_templates
            .remove(&key)
            .ok_or(ImageFailure::InvalidRecord)?;
        let claims = scope.copy_claims();
        let result = (|| {
            let mut copies = [0u32; 3];
            for (position, claim) in claims.into_iter().enumerate() {
                copies[position] = self.encode_source_copy(claim, &retained.mappings[position])?;
            }
            let start = self.image.source_arguments.len();
            for argument in scope.arguments() {
                let argument = self.encode_structural(StructuralInput::Argument(argument))?;
                push(&mut self.image.source_arguments, argument, self.work)?;
            }
            let arguments = Slice::of(&self.image.source_arguments, start)?;
            let start = self.image.interpretations.len();
            for interpretation in scope.native_interpretations() {
                let effect =
                    self.encode_structural(StructuralInput::Instance(interpretation.effect()))?;
                let symbol = self.encode_native_symbol(interpretation.symbol())?;
                push(
                    &mut self.image.interpretations,
                    NativeInterpretationRecord { effect, symbol },
                    self.work,
                )?;
            }
            let interpretations = Slice::of(&self.image.interpretations, start)?;
            let record = SourceScopeRecord {
                template,
                arguments,
                identity: self.type_variable(scope.identity())?,
                initializer: self.node(scope.initializer)?,
                acquire_parameter: self.encode_binder(&scope.acquire.parameter)?,
                acquire_body: self.node(scope.acquire.body)?,
                finish_parameter: self.encode_binder(&scope.finish.parameter)?,
                finish_body: self.node(scope.finish.body)?,
                handler_state: self.encode_binder(&scope.handler_state)?,
                handler_pattern: self.encode_pattern(&scope.handler_pattern)?,
                handle: self.encode_binder(&scope.handle)?,
                handler: self.encode_handler(&scope.handler)?,
                output_value: self.encode_type(scope.handler_output.value())?,
                output_effects: self
                    .encode_structural(StructuralInput::Row(scope.handler_output.effects()))?,
                acquire_copy: copies[0],
                finish_copy: copies[1],
                handler_copy: copies[2],
                interpretations,
            };
            push(&mut self.image.source_scopes, record, self.work)
        })();
        self.source_templates.insert(key, retained);
        result
    }
    fn encode_source_copy(
        &mut self,
        claim: SourceResourceCopyClaim<'_>,
        original: &[Option<u32>],
    ) -> Result<u32, ImageFailure> {
        if !claim.freshening.nominals.is_empty()
            || !claim.freshening.lexicals.is_empty()
            || !claim.substitution.pending.is_empty()
        {
            return Err(ImageFailure::Unsupported(Unsupported::RegistryMetadata));
        }
        let start = self.image.source_node_pairs.len();
        for (source, target) in claim.nodes {
            let source = original
                .get(usize::try_from(source.value()).map_err(|_| ImageFailure::InvalidRecord)?)
                .copied()
                .flatten()
                .ok_or(ImageFailure::InvalidRecord)?;
            let copied = self.node(*target)?;
            push(
                &mut self.image.source_node_pairs,
                NodePairRecord {
                    original: source,
                    copied,
                },
                self.work,
            )?;
        }
        let nodes = Slice::of(&self.image.source_node_pairs, start)?;
        let start = self.image.source_binder_pairs.len();
        for (source, target) in claim.freshening.binders {
            let record = BinderPairRecord {
                original: self.binder_id(*source)?,
                copied: self.binder_id(*target)?,
            };
            push(&mut self.image.source_binder_pairs, record, self.work)?;
        }
        let binders = Slice::of(&self.image.source_binder_pairs, start)?;
        let start = self.image.source_fresh_types.len();
        for (source, target, kind) in claim.freshening.types {
            let record = FreshTypeRecord {
                original: self.type_variable(*source)?,
                copied: self.type_variable(*target)?,
                kind: self.encode_kind(kind)?,
            };
            push(&mut self.image.source_fresh_types, record, self.work)?;
        }
        let variables = Slice::of(&self.image.source_fresh_types, start)?;
        let start = self.image.source_plain_pairs.len();
        for (source, target) in claim.freshening.handlers {
            push(
                &mut self.image.source_plain_pairs,
                PlainPairRecord {
                    original: source.value(),
                    copied: target.value(),
                },
                self.work,
            )?;
        }
        let handlers = Slice::of(&self.image.source_plain_pairs, start)?;
        let start = self.image.source_plain_pairs.len();
        for (source, target) in claim.freshening.resumes {
            push(
                &mut self.image.source_plain_pairs,
                PlainPairRecord {
                    original: source.value(),
                    copied: target.value(),
                },
                self.work,
            )?;
        }
        let resumes = Slice::of(&self.image.source_plain_pairs, start)?;
        let start = self.image.source_substitutions.len();
        for (source, ty) in claim.substitution.types {
            let record = SourceSubstitutionRecord {
                original: self.type_variable(*source)?,
                value: self.encode_type(ty)?,
            };
            push(&mut self.image.source_substitutions, record, self.work)?;
        }
        let types = Slice::of(&self.image.source_substitutions, start)?;
        let start = self.image.source_substitutions.len();
        for (source, row) in claim.substitution.rows {
            let record = SourceSubstitutionRecord {
                original: self.type_variable(*source)?,
                value: self.encode_structural(StructuralInput::Row(row))?,
            };
            push(&mut self.image.source_substitutions, record, self.work)?;
        }
        let rows = Slice::of(&self.image.source_substitutions, start)?;
        push(
            &mut self.image.source_copies,
            SourceCopyRecord {
                nodes,
                binders,
                variables,
                handlers,
                resumes,
                types,
                rows,
            },
            self.work,
        )
    }
}

impl Decoder<'_> {
    pub(super) fn resource_identity(
        &mut self,
        id: ResourceIdentity,
    ) -> Result<ResourceDefinitionId, ImageFailure> {
        charge(self.work, 1)?;
        Ok(ResourceDefinitionId::new(
            *get(&self.modules, id.module)?,
            id.local,
        ))
    }
    fn interface_identity(
        &mut self,
        id: InterfaceIdentity,
    ) -> Result<crate::interface::InterfaceId, ImageFailure> {
        charge(self.work, 1)?;
        Ok(crate::interface::InterfaceId::new(
            *get(&self.modules, id.module)?,
            id.local,
        ))
    }
    fn provenance_view(
        &mut self,
        arena: Option<&crate::resolved::ResolvedTypeProvenance>,
        root: u32,
    ) -> Result<crate::resolved::ResolvedTypeProvenance, ImageFailure> {
        let root = usize::try_from(root).map_err(|_| ImageFailure::InvalidRecord)?;
        if root >= self.image.provenance.len() {
            return Err(ImageFailure::InvalidRecord);
        }
        arena
            .ok_or(ImageFailure::InvalidRecord)?
            .image_view(root, self.work)
            .map_err(|_| ImageFailure::Resource)
    }
    fn resolved_annotation(
        &mut self,
        record: ResolvedTypeRecord,
        arena: Option<&crate::resolved::ResolvedTypeProvenance>,
    ) -> Result<ResolvedAnnotationOwner, ImageFailure> {
        let ty = self.ty(record.ty)?;
        let provenance = self.provenance_view(arena, record.provenance)?;
        let origin = self.origin(record.origin)?;
        let span = self.span(record.span)?;
        Ok(ResolvedAnnotationOwner(Some(ResolvedType {
            ty: ty.into_inner(),
            provenance,
            origin: origin.take(),
            span,
        })))
    }
    fn resource_effect(
        &mut self,
        record: ResourceEffectRecord,
        arena: Option<&crate::resolved::ResolvedTypeProvenance>,
    ) -> Result<ResolvedEffectOwner, ImageFailure> {
        let instance = self.structural(record.effect)?.instance()?;
        let mut provenance = Vec::new();
        for root in record.arguments.get(&self.image.resource_provenance)? {
            let view = self.provenance_view(arena, *root)?;
            push(&mut provenance, view, self.work)?;
        }
        if provenance.len() != instance.arguments().len() {
            return Err(ImageFailure::InvalidRecord);
        }
        let origin = self.origin(record.origin)?;
        let span = self.span(record.span)?;
        Ok(ResolvedEffectOwner(Some(ResolvedEffectInstance {
            instance,
            argument_provenance: provenance.into_boxed_slice(),
            origin: origin.take(),
            span,
        })))
    }
    pub(super) fn source_registry(
        &mut self,
        mut registry: ResolvedRegistry,
        arena: Option<&crate::resolved::ResolvedTypeProvenance>,
    ) -> Result<ResolvedRegistry, ImageFailure> {
        let mut source_parameters = ParameterBuffer(Vec::new());
        charge(self.work, self.image.source_parameters.len())?;
        source_parameters
            .0
            .try_reserve_exact(self.image.source_parameters.len())
            .map_err(|_| ImageFailure::Resource)?;
        for slot in &self.image.source_parameters {
            source_parameters
                .0
                .push(self.parameter(*get(&self.image.parameters, *slot)?)?);
        }
        // Interface slots belong exclusively to their owner records in the
        // wire coverage proof. Install their canonical binders before the
        // original owner definition authenticates its independently decoded row.
        for record in &self.image.interface_owners {
            let parameters = self.parameters(record.parameters)?;
            charge(self.work, parameters.0.len())?;
            source_parameters
                .0
                .try_reserve(parameters.0.len())
                .map_err(|_| ImageFailure::Resource)?;
            source_parameters.0.extend(parameters.into_vec());
        }
        registry = registry
            .with_image_source_parameters(source_parameters.into_vec(), self.work)
            .map_err(|_| ImageFailure::RegistryAdmission)?;
        let mut interfaces = Vec::new();
        for record in &self.image.interface_owners {
            let id = self.interface_identity(record.id)?;
            let parameters = self.parameters(record.parameters)?;
            push(&mut interfaces, (id, parameters.into_vec()), self.work)?;
        }
        registry = registry
            .with_image_interface_owner_definitions(interfaces, self.work)
            .map_err(|_| ImageFailure::RegistryAdmission)?;
        let mut facts = Vec::new();
        for record in &self.image.resource_headers {
            let fact = self.source_header(*record, arena)?;
            charge(self.work, 1)?;
            push(&mut facts, Arc::new(fact), self.work)?;
        }
        registry
            .with_image_source_resource_facts(facts, self.work)
            .map_err(|_| ImageFailure::RegistryAdmission)
    }
    fn source_header(
        &mut self,
        record: ResourceHeaderRecord,
        arena: Option<&crate::resolved::ResolvedTypeProvenance>,
    ) -> Result<SourceResourceTypeFact, ImageFailure> {
        let id = self.resource_identity(record.id)?;
        let family = self.nominal(record.family)?;
        let spelling = self.text(record.spelling)?;
        let parameters = self.parameters(record.parameters)?;
        let answer = self.parameter(*get(&self.image.parameters, record.answer)?)?;
        let owned_origin = self.origin(record.owned_origin)?;
        let origin = self.origin(record.origin)?;
        let input = self.resolved_annotation(record.input, arena)?;
        let state = self.resolved_annotation(record.state, arena)?;
        let data = self.resolved_annotation(record.data, arena)?;
        let acquisition = self.resolved_annotation(record.acquisition, arena)?;
        let completion = self.resolved_annotation(record.completion, arena)?;
        let result = self.resolved_annotation(record.result, arena)?;
        let provider_id = self.interface_identity(record.provider)?;
        let provider_spelling = self.text(record.provider_spelling)?;
        let provider_origin = self.origin(record.provider_origin)?;
        let mut provider_arguments = OwnerArgumentBuffer(Vec::new());
        for argument in record
            .provider_arguments
            .get(&self.image.resource_arguments)?
        {
            let ty = self.structural(argument.argument)?.argument()?;
            let provenance = self.provenance_view(arena, argument.provenance)?;
            let origin = self.origin(argument.origin)?;
            let span = self.span(argument.span)?;
            charge(self.work, 1)?;
            provider_arguments
                .0
                .try_reserve(1)
                .map_err(|_| ImageFailure::Resource)?;
            provider_arguments.0.push(ResolvedOwnerArgument {
                ty: ty.into_inner(),
                provenance,
                origin: origin.take(),
                span,
            });
        }
        let provider_span = self.span(record.provider_span)?;
        let codec_span = self.span(record.codec_span)?;
        let provided = self.resource_effect(record.provided, arena)?;
        let mut interpreted = ResolvedEffectBuffer(Vec::new());
        for effect in record.interpreted.get(&self.image.resource_effects)? {
            let effect = self.resource_effect(*effect, arena)?;
            charge(self.work, 1)?;
            interpreted
                .0
                .try_reserve(1)
                .map_err(|_| ImageFailure::Resource)?;
            interpreted.0.push(effect.take());
        }
        let owned_position =
            usize::try_from(record.owned_position).map_err(|_| ImageFailure::InvalidRecord)?;
        Ok(SourceResourceTypeFact {
            id,
            family,
            public: record.public,
            spelling,
            parameters: parameters.into_boxed_slice(),
            owned_position,
            owned_origin: owned_origin.take(),
            input: input.take(),
            state: state.take(),
            data: data.take(),
            acquisition: acquisition.take(),
            completion: completion.take(),
            result: result.take(),
            answer,
            codec: crate::surface::SurfaceResourceReportCodec {
                kind: if record.codec_scope {
                    crate::surface::SurfaceResourceReportCodecKind::Scope
                } else {
                    crate::surface::SurfaceResourceReportCodecKind::AcquiredOnly
                },
                span: codec_span,
            },
            provider: ResolvedInterfaceApplication {
                interface: ResolvedInterfaceOccurrence {
                    id: provider_id,
                    spelling: provider_spelling,
                    origin: provider_origin.take(),
                },
                arguments: provider_arguments.take(),
                span: provider_span,
            },
            provided: provided.take(),
            interpreted: interpreted.take(),
            origin: origin.take(),
        })
    }
    pub(super) fn source_handler_parts(
        &mut self,
        builder: &mut crate::core::EffectCoreBuilder,
        nodes: &[NodeId],
        slot: u32,
    ) -> Result<
        (
            crate::core::HandlerId,
            NodeId,
            EffectInstance,
            Vec<crate::core::EffectClause>,
        ),
        ImageFailure,
    > {
        let record = *get(&self.image.source_handlers, slot)?;
        let effect = self.structural(record.effect)?.instance()?;
        let body = *get(nodes, record.body)?;
        let mut clauses = Vec::new();
        for record in record.clauses.get(&self.image.source_clauses)? {
            let operation = self.operation_identity(record.operation)?;
            let pattern = self.pattern(builder, record.arm.pattern)?;
            let body = *get(nodes, record.arm.body)?;
            let origin = self.origin(record.arm.origin)?;
            let clause = crate::core::EffectClause::new(
                operation,
                crate::resolved::ResumeId::new(record.resume),
                crate::core::CoreMatchArm::new(pattern.take(), body, origin.take()),
            );
            push(&mut clauses, clause, self.work)?;
        }
        Ok((
            crate::core::HandlerId::new(record.id),
            body,
            effect,
            clauses,
        ))
    }
    pub(super) fn source_handler(
        &mut self,
        builder: &mut crate::core::EffectCoreBuilder,
        nodes: &[NodeId],
        slot: u32,
    ) -> Result<crate::core::HandlerNode, ImageFailure> {
        let (id, body, effect, clauses) = self.source_handler_parts(builder, nodes, slot)?;
        Ok(crate::core::HandlerNode::new(id, body, effect, clauses))
    }
    pub(super) fn source_binder_reservations(
        &mut self,
    ) -> Result<Vec<crate::resolved::BinderId>, ImageFailure> {
        // Original forests and the main arena may repeat generated identities.
        // Reservation tracks names only; materialization and Core admission
        // still authenticate each arena's complete typed binder records.
        charge(self.work, self.image.binders.len())?;
        let mut seen = std::collections::HashSet::new();
        seen.try_reserve(self.image.binders.len())
            .map_err(|_| ImageFailure::Resource)?;
        let mut binders = Vec::new();
        for record in &self.image.binders {
            let id = self.binder_id(record.id)?;
            charge(self.work, 1)?;
            if seen.insert(id) {
                push(&mut binders, id, self.work)?;
            }
        }
        Ok(binders)
    }
    fn source_graph(
        &mut self,
        registry: &Arc<ResolvedRegistry>,
        symbols: &[Arc<crate::foreign::checked_source::CheckedForeignSymbol>],
        binders: &[crate::resolved::BinderId],
        slot: u32,
    ) -> Result<(UnvalidatedEffectProgram, Vec<NodeId>), ImageFailure> {
        let graph = *get(&self.image.source_graphs, slot)?;
        let records = graph.nodes.get(&self.image.template_nodes)?;
        let catalog = self.method_catalog(graph.catalog)?;
        let mut builder = crate::core::EffectCoreBuilder::with_registry_and_method_evidence(
            Arc::clone(registry),
            catalog,
        )?;
        builder.reserve_image_reconstruction_storage(
            records.len(),
            self.image.binders.len(),
            self.work,
        )?;
        builder.reserve_provider_draft_binders(binders, self.work)?;
        let mut nodes = Vec::new();
        for record in records {
            let ty = self.ty(record.ty)?;
            let origin = self.origin(record.origin)?;
            let effects = self
                .structural(record.effects.ok_or(ImageFailure::InvalidRecord)?)?
                .row()?;
            let node = self.effect_node(
                &mut builder,
                &nodes,
                symbols,
                &[],
                record.tag,
                ty,
                effects,
                origin,
            )?;
            push(&mut nodes, node, self.work)?;
        }
        let program = builder.finish_provider_draft(*get(&nodes, graph.root)?, self.work)?;
        Ok((program, nodes))
    }
    pub(super) fn source_templates(
        &mut self,
        registry: &Arc<ResolvedRegistry>,
        symbols: &[Arc<crate::foreign::checked_source::CheckedForeignSymbol>],
        binders: &[crate::resolved::BinderId],
    ) -> Result<Vec<RestoredSourceTemplate>, ImageFailure> {
        let mut templates = Vec::new();
        for record in &self.image.source_templates {
            let header_record = *get(&self.image.resource_headers, record.header)?;
            let id = self.resource_identity(header_record.id)?;
            let original = registry
                .source_resource_fact(id)
                .ok_or(ImageFailure::InvalidRecord)?;
            let header = CheckedSourceResourceHeader::admit(original, registry, self.work)
                .map_err(ImageFailure::Validation)?;
            let (acquire, acquire_nodes) =
                self.source_graph(registry, symbols, binders, record.acquire)?;
            let (finish, finish_nodes) =
                self.source_graph(registry, symbols, binders, record.finish)?;
            let (handler, handler_nodes) =
                self.source_graph(registry, symbols, binders, record.handler)?;
            let mut sources = Vec::new();
            let mut module_sources = Vec::new();
            for (module, source) in self.modules.iter().zip(self.sources.iter()) {
                push(&mut sources, source, self.work)?;
                push(&mut module_sources, (*module, source.id()), self.work)?;
            }
            let template = CheckedSourceResourceTemplate::admit(
                Arc::new(header),
                acquire,
                finish,
                handler,
                &sources,
                &module_sources,
                self.work,
            )
            .map_err(ImageFailure::Validation)?;
            let record = RestoredSourceTemplate {
                template: Arc::new(template),
                nodes: [acquire_nodes, finish_nodes, handler_nodes],
            };
            push(&mut templates, record, self.work)?;
        }
        Ok(templates)
    }
    fn source_copy(
        &mut self,
        slot: u32,
        original: &[NodeId],
        copied: &[NodeId],
    ) -> Result<RestoredSourceCopy, ImageFailure> {
        let record = *get(&self.image.source_copies, slot)?;
        let mut copy = RestoredSourceCopy::default();
        for record in record.nodes.get(&self.image.source_node_pairs)? {
            let pair = (
                *get(original, record.original)?,
                *get(copied, record.copied)?,
            );
            push(&mut copy.nodes, pair, self.work)?;
        }
        for record in record.binders.get(&self.image.source_binder_pairs)? {
            let pair = (
                self.binder_id(record.original)?,
                self.binder_id(record.copied)?,
            );
            push(&mut copy.binders, pair, self.work)?;
        }
        for record in record.variables.get(&self.image.source_fresh_types)? {
            let value = (
                self.type_variable(record.original)?,
                self.type_variable(record.copied)?,
                self.kind(record.kind)?,
            );
            push(&mut copy.variables, value, self.work)?;
        }
        for record in record.handlers.get(&self.image.source_plain_pairs)? {
            push(
                &mut copy.handlers,
                (
                    crate::core::HandlerId::new(record.original),
                    crate::core::HandlerId::new(record.copied),
                ),
                self.work,
            )?;
        }
        for record in record.resumes.get(&self.image.source_plain_pairs)? {
            push(
                &mut copy.resumes,
                (
                    crate::resolved::ResumeId::new(record.original),
                    crate::resolved::ResumeId::new(record.copied),
                ),
                self.work,
            )?;
        }
        charge(
            self.work,
            record.types.len as usize + record.rows.len as usize,
        )?;
        copy.types
            .try_reserve(record.types.len as usize)
            .map_err(|_| ImageFailure::Resource)?;
        copy.rows
            .try_reserve(record.rows.len as usize)
            .map_err(|_| ImageFailure::Resource)?;
        for record in record.types.get(&self.image.source_substitutions)? {
            let id = self.type_variable(record.original)?;
            let ty = self.ty(record.value)?;
            if let Some(displaced) = copy.types.insert(id, ty.into_inner()) {
                crate::types::discard_type_iteratively(displaced);
                return Err(ImageFailure::InvalidRecord);
            }
        }
        for record in record.rows.get(&self.image.source_substitutions)? {
            let id = self.type_variable(record.original)?;
            let row = self.structural(record.value)?.row()?;
            if copy.rows.insert(id, row).is_some() {
                return Err(ImageFailure::InvalidRecord);
            }
        }
        Ok(copy)
    }
    pub(super) fn source_scope(
        &mut self,
        builder: &mut crate::core::EffectCoreBuilder,
        nodes: &[NodeId],
        symbols: &[Arc<crate::foreign::checked_source::CheckedForeignSymbol>],
        templates: &[RestoredSourceTemplate],
        slot: u32,
    ) -> Result<SourceResourceScopeNode, ImageFailure> {
        let record = *get(&self.image.source_scopes, slot)?;
        let template = get(templates, record.template)?;
        let mut guarded_arguments = Vec::new();
        for argument in record.arguments.get(&self.image.source_arguments)? {
            let argument = self.structural(*argument)?.argument()?;
            push(&mut guarded_arguments, argument, self.work)?;
        }
        let mut arguments = Vec::new();
        charge(self.work, guarded_arguments.len())?;
        arguments
            .try_reserve_exact(guarded_arguments.len())
            .map_err(|_| ImageFailure::Resource)?;
        let identity = self.type_variable(record.identity)?;
        let initializer = *get(nodes, record.initializer)?;
        let acquire = SourceResourceLifecycleEntry {
            parameter: self.binder(builder, record.acquire_parameter)?,
            body: *get(nodes, record.acquire_body)?,
        };
        let finish = SourceResourceLifecycleEntry {
            parameter: self.binder(builder, record.finish_parameter)?,
            body: *get(nodes, record.finish_body)?,
        };
        let handler_state = self.binder(builder, record.handler_state)?;
        let handler_pattern = self.pattern(builder, record.handler_pattern)?;
        let handle = self.binder(builder, record.handle)?;
        let handler = self.source_handler(builder, nodes, record.handler)?;
        let output_value = self.ty(record.output_value)?;
        let output_effects = self.structural(record.output_effects)?.row()?;
        let acquire_copy = self.source_copy(record.acquire_copy, &template.nodes[0], nodes)?;
        let finish_copy = self.source_copy(record.finish_copy, &template.nodes[1], nodes)?;
        let handler_copy = self.source_copy(record.handler_copy, &template.nodes[2], nodes)?;
        for argument in guarded_arguments {
            arguments.push(argument.into_inner());
        }
        let scope = SourceResourceScopeNode::new(
            Arc::clone(&template.template),
            arguments.into_boxed_slice(),
            identity,
            initializer,
            acquire,
            finish,
            handler_state,
            handler_pattern.take(),
            handle,
            handler,
            crate::types::ComputationType::new(output_value.into_inner(), output_effects),
            [
                acquire_copy.claim(),
                finish_copy.claim(),
                handler_copy.claim(),
            ],
            self.work,
        )
        .map_err(ImageFailure::Validation)?;
        let expected = record.interpretations.get(&self.image.interpretations)?;
        if expected.len() != scope.native_interpretations().len() {
            return Err(ImageFailure::InvalidRecord);
        }
        for (expected, actual) in expected.iter().zip(scope.native_interpretations()) {
            let symbol = get(symbols, expected.symbol)?;
            let effect = self.structural(expected.effect)?.instance()?;
            if !Arc::ptr_eq(symbol, actual.symbol())
                || !same_instance(&effect, actual.effect(), self.work)?
            {
                return Err(ImageFailure::InvalidRecord);
            }
        }
        Ok(scope)
    }
}

struct ResolvedEffectOwner(Option<ResolvedEffectInstance>);
impl ResolvedEffectOwner {
    fn take(mut self) -> ResolvedEffectInstance {
        self.0.take().expect("live source effect occurrence")
    }
}
impl Drop for ResolvedEffectOwner {
    fn drop(&mut self) {
        if let Some(effect) = self.0.take() {
            crate::source::discard_origin_iteratively(effect.origin);
        }
    }
}
struct ResolvedEffectBuffer(Vec<ResolvedEffectInstance>);
impl ResolvedEffectBuffer {
    fn take(mut self) -> Box<[ResolvedEffectInstance]> {
        std::mem::take(&mut self.0).into_boxed_slice()
    }
}
impl Drop for ResolvedEffectBuffer {
    fn drop(&mut self) {
        for effect in self.0.drain(..) {
            crate::source::discard_origin_iteratively(effect.origin);
        }
    }
}

struct ResolvedAnnotationOwner(Option<ResolvedType>);
impl ResolvedAnnotationOwner {
    fn take(mut self) -> ResolvedType {
        self.0.take().expect("live resolved annotation")
    }
}
impl Drop for ResolvedAnnotationOwner {
    fn drop(&mut self) {
        if let Some(value) = self.0.take() {
            crate::types::discard_type_iteratively(value.ty);
            crate::source::discard_origin_iteratively(value.origin);
        }
    }
}
struct OwnerArgumentBuffer(Vec<ResolvedOwnerArgument>);
impl OwnerArgumentBuffer {
    fn take(mut self) -> Box<[ResolvedOwnerArgument]> {
        std::mem::take(&mut self.0).into_boxed_slice()
    }
}
impl Drop for OwnerArgumentBuffer {
    fn drop(&mut self) {
        for value in self.0.drain(..) {
            crate::types::discard_kinded_argument_iteratively(value.ty);
            crate::source::discard_origin_iteratively(value.origin);
        }
    }
}
#[derive(Default)]
struct RestoredSourceCopy {
    nodes: Vec<(NodeId, NodeId)>,
    binders: Vec<(crate::resolved::BinderId, crate::resolved::BinderId)>,
    variables: Vec<(TypeVariableId, TypeVariableId, Kind)>,
    handlers: Vec<(crate::core::HandlerId, crate::core::HandlerId)>,
    resumes: Vec<(crate::resolved::ResumeId, crate::resolved::ResumeId)>,
    types: HashMap<TypeVariableId, Type>,
    rows: HashMap<TypeVariableId, EffectRow>,
    pending: HashMap<crate::types::InferenceVariableId, EffectRow>,
}
impl RestoredSourceCopy {
    fn claim(&self) -> SourceResourceCopyClaim<'_> {
        SourceResourceCopyClaim {
            nodes: &self.nodes,
            freshening: crate::core::provider::ProviderFreshening {
                binders: &self.binders,
                types: &self.variables,
                handlers: &self.handlers,
                resumes: &self.resumes,
                nominals: &[],
                lexicals: &[],
            },
            substitution: crate::core::provider::ProviderTemplateSubstitution {
                types: &self.types,
                rows: &self.rows,
                pending: &self.pending,
            },
        }
    }
}
impl Drop for RestoredSourceCopy {
    fn drop(&mut self) {
        for (_, ty) in self.types.drain() {
            crate::types::discard_type_iteratively(ty);
        }
    }
}

fn same_instance(
    left: &EffectInstance,
    right: &EffectInstance,
    work: &mut TypeWorkBudget,
) -> Result<bool, ImageFailure> {
    charge(work, 1)?;
    if left.effect() != right.effect() || left.arguments().len() != right.arguments().len() {
        return Ok(false);
    }
    for (left, right) in left.arguments().iter().zip(right.arguments()) {
        if !crate::types::same_kinded_argument_with_budget(left, right, work)
            .map_err(|_| ImageFailure::Resource)?
        {
            return Ok(false);
        }
    }
    Ok(true)
}

fn methods_only(catalog: &crate::core::dialect::MethodEvidenceCatalog) -> bool {
    catalog.lexical_owners().is_empty()
        && catalog.implementation_owners().is_empty()
        && catalog.domains().is_empty()
        && catalog.occurrences().is_empty()
        && catalog.final_occurrence_owners().is_empty()
        && catalog.adapters().is_empty()
        && catalog.concrete_sources().is_empty()
        && catalog.expectations().is_empty()
}
impl Encoder<'_> {
    pub(super) fn encode_method_catalog(
        &mut self,
        catalog: &Arc<crate::core::dialect::MethodEvidenceCatalog>,
    ) -> Result<u32, ImageFailure> {
        if !methods_only(catalog) {
            return Err(ImageFailure::Unsupported(Unsupported::MethodEvidence));
        }
        let start = self.image.source_methods.len();
        for method in catalog.methods() {
            let interface = self.interface_identity(method.id.interface())?;
            let variable_start = self.image.method_variables.len();
            for id in &method.interface_parameters {
                let id = self.type_variable(*id)?;
                push(&mut self.image.method_variables, id, self.work)?;
            }
            let interface_parameters = Slice::of(&self.image.method_variables, variable_start)?;
            let inherited_start = self.image.inherited_parameters.len();
            for parameter in &method.inherited_parameters {
                let owner = match parameter.owner {
                    crate::resolved::OwnerId::Effect(id) => {
                        OwnerIdentity::Effect(self.effect_identity(id)?)
                    }
                    crate::resolved::OwnerId::Interface(id) => {
                        OwnerIdentity::Interface(self.interface_identity(id)?)
                    }
                    crate::resolved::OwnerId::Resource(id) => {
                        OwnerIdentity::Resource(self.resource_identity(id)?)
                    }
                };
                let binder = self.type_variable(parameter.binder)?;
                push(
                    &mut self.image.inherited_parameters,
                    InheritedParameterRecord {
                        owner,
                        slot: parameter.slot,
                        binder,
                    },
                    self.work,
                )?;
            }
            let inherited_parameters =
                Slice::of(&self.image.inherited_parameters, inherited_start)?;
            let quantifier_start = self.image.quantifiers.len();
            for (id, kind) in &method.parameters {
                let id = self.type_variable(*id)?;
                let kind = self.encode_kind(kind)?;
                push(
                    &mut self.image.quantifiers,
                    QuantifierRecord { id, kind },
                    self.work,
                )?;
            }
            let parameters = Slice::of(&self.image.quantifiers, quantifier_start)?;
            let value_type = self.encode_type(&method.value_type)?;
            push(
                &mut self.image.source_methods,
                MethodRecord {
                    interface,
                    local: method.id.declaration(),
                    interface_parameters,
                    inherited_parameters,
                    parameters,
                    value_type,
                },
                self.work,
            )?;
        }
        push(
            &mut self.image.method_catalogs,
            MethodCatalogRecord {
                methods: Slice::of(&self.image.source_methods, start)?,
            },
            self.work,
        )
    }
}
impl Decoder<'_> {
    pub(super) fn method_catalog(
        &mut self,
        slot: u32,
    ) -> Result<Arc<crate::core::dialect::MethodEvidenceCatalog>, ImageFailure> {
        let catalog = *get(&self.image.method_catalogs, slot)?;
        let mut methods = Vec::new();
        for record in catalog.methods.get(&self.image.source_methods)? {
            let id = crate::interface::MethodId::new(
                self.interface_identity(record.interface)?,
                record.local,
            );
            let mut interface_parameters = Vec::new();
            for id in record
                .interface_parameters
                .get(&self.image.method_variables)?
            {
                let id = self.type_variable(*id)?;
                push(&mut interface_parameters, id, self.work)?;
            }
            let mut inherited_parameters = Vec::new();
            for parameter in record
                .inherited_parameters
                .get(&self.image.inherited_parameters)?
            {
                let owner = match parameter.owner {
                    OwnerIdentity::Effect(id) => {
                        crate::resolved::OwnerId::Effect(self.effect_identity(id)?)
                    }
                    OwnerIdentity::Interface(id) => {
                        crate::resolved::OwnerId::Interface(self.interface_identity(id)?)
                    }
                    OwnerIdentity::Resource(id) => {
                        crate::resolved::OwnerId::Resource(self.resource_identity(id)?)
                    }
                };
                let binder = self.type_variable(parameter.binder)?;
                push(
                    &mut inherited_parameters,
                    crate::resolved::InheritedOwnerParameter {
                        owner,
                        slot: parameter.slot,
                        binder,
                    },
                    self.work,
                )?;
            }
            let mut parameters = Vec::new();
            for parameter in record.parameters.get(&self.image.quantifiers)? {
                let id = self.type_variable(parameter.id)?;
                let kind = self.kind(parameter.kind)?;
                push(&mut parameters, (id, kind), self.work)?;
            }
            let value_type = self.ty(record.value_type)?;
            let method = crate::core::dialect::MethodEvidenceMethod {
                id,
                interface_parameters: interface_parameters.into_boxed_slice(),
                inherited_parameters: inherited_parameters.into_boxed_slice(),
                parameters: parameters.into_boxed_slice(),
                value_type: value_type.into_inner(),
            };
            push(&mut methods, method, self.work)?;
        }
        charge(self.work, 1)?;
        Ok(Arc::new(crate::core::dialect::MethodEvidenceCatalog::new(
            methods,
            Vec::new(),
            Vec::new(),
            Vec::new(),
            Vec::new(),
            Vec::new(),
            Vec::new(),
        )))
    }
}

#[cfg(test)]
mod tests {
    use super::super::{PureImage, get};
    use crate::types::TypeWorkBudget;
    use std::sync::Arc;
    use std::{
        fs,
        path::PathBuf,
        sync::atomic::{AtomicU64, Ordering},
    };
    struct Fixture(PathBuf);
    impl Drop for Fixture {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.0);
        }
    }
    #[test]
    fn arena_image_reconstruction_keeps_one_cumulative_allowance() {
        let root = std::env::temp_dir().join(format!("ash-arena-cost-{}", std::process::id()));
        fs::create_dir(&root).unwrap();
        let fixture = Fixture(root);
        fs::write(
            fixture.0.join("arena.ash"),
            include_str!("../../libraries/arena.ash"),
        )
        .unwrap();
        fs::write(
            fixture.0.join("entry.ash"),
            include_str!("../../tests/fixtures/source-arena/entry.ash"),
        )
        .unwrap();
        let compiled = crate::driver::compile_path(crate::driver::RunConfiguration {
            entry: fixture.0.join("entry.ash"),
            roots: crate::module::ModuleRoots::empty(),
        })
        .unwrap();
        let (program, provenance) = compiled.effect_build_input().unwrap();
        let image = super::super::encode_effect_for_build(
            program,
            provenance,
            super::super::super::NATIVE_TARGET,
            &mut TypeWorkBudget::default(),
        )
        .unwrap()
        .image;
        let bytes = image.encode_bytes(&mut TypeWorkBudget::default()).unwrap();
        let expected = image
            .encode_native_expectations(&mut TypeWorkBudget::default())
            .unwrap();
        drop(compiled);
        fs::remove_file(fixture.0.join("arena.ash")).unwrap();
        fs::remove_file(fixture.0.join("entry.ash")).unwrap();
        let restore = |work: &mut TypeWorkBudget| {
            let decoded = PureImage::decode_bytes(&bytes, work)?;
            decoded.admit_expected_native_facts(&expected, work)?;
            decoded.restore_effect(work)
        };
        let mut measured = TypeWorkBudget::default();
        drop(restore(&mut measured).expect("complete arena fits the unchanged startup allowance"));
        let cost = measured.used();
        assert!(cost < measured.limit());
        for prefix in [0, 17] {
            let mut exact = TypeWorkBudget::with_limit(cost + prefix);
            exact.charge(prefix).unwrap();
            drop(restore(&mut exact).expect("exact cumulative allowance succeeds"));
            assert_eq!(exact.used(), cost + prefix);
            let mut short = TypeWorkBudget::with_limit(cost + prefix - 1);
            short.charge(prefix).unwrap();
            assert!(
                restore(&mut short).is_err(),
                "one-short allowance refuses reconstruction"
            );
            assert!(
                short.used() > prefix,
                "completed work is retained on refusal"
            );
        }
        drop(restore(&mut TypeWorkBudget::default()).expect("fresh retry remains independent"));
    }
    fn scope_image() -> PureImage {
        static IDS: AtomicU64 = AtomicU64::new(0);
        let root = std::env::temp_dir().join(format!(
            "ash-source-scope-image-{}-{}",
            std::process::id(),
            IDS.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&root).unwrap();
        let fixture = Fixture(root);
        fs::write(
            fixture.0.join("owner.ash"),
            include_str!("../../tests/fixtures/source-owner/owner.ash"),
        )
        .unwrap();
        fs::write(
            fixture.0.join("entry.ash"),
            include_str!("../../tests/fixtures/source-owner/entry.ash"),
        )
        .unwrap();
        let compiled = crate::driver::compile_path(crate::driver::RunConfiguration {
            entry: fixture.0.join("entry.ash"),
            roots: crate::module::ModuleRoots::empty(),
        })
        .unwrap();
        let (program, provenance) = compiled.effect_build_input().unwrap();
        let build = super::super::encode_effect_for_build(
            program,
            provenance,
            super::super::super::NATIVE_TARGET,
            &mut TypeWorkBudget::default(),
        )
        .unwrap();
        assert_eq!(
            build.bridges.len(),
            2,
            "native acquire and unconditional void teardown; ordinary Ash provider reads private data"
        );
        assert_eq!(
            build.image.source_templates.len(),
            1,
            "one original template shared by all scopes"
        );
        assert_eq!(build.image.source_graphs.len(), 3, "three defining forests");
        assert_eq!(
            build.image.source_scopes.len(),
            3,
            "helper plus nested outer and inner scope"
        );
        build.image
    }
    #[test]
    fn source_scope_image_checks_original_forests_and_exact_copies_without_sources() {
        let image = scope_image();
        let bytes = image.encode_bytes(&mut TypeWorkBudget::default()).unwrap();
        let expected = image
            .encode_native_expectations(&mut TypeWorkBudget::default())
            .unwrap();
        // Generated startup shares one structural allowance across decoding,
        // expectation correspondence, restoration, and library admission.
        let mut work = TypeWorkBudget::default();
        let decoded = PureImage::decode_bytes(&bytes, &mut work).unwrap();
        let facts = decoded
            .admit_expected_native_facts(&expected, &mut work)
            .unwrap();
        let restored = decoded.restore_effect(&mut work).unwrap();
        for (slot, record) in decoded.prepared_libraries.iter().enumerate() {
            let slot = u32::try_from(slot).unwrap();
            let expected = facts.library(slot, &restored, &mut work).unwrap();
            let ordinal = decoded
                .native_symbols
                .iter()
                .find(|symbol| symbol.prepared_library == slot)
                .unwrap()
                .library_ordinal;
            let identity = restored
                .relocate_library(record.module, ordinal, &mut work)
                .unwrap();
            crate::foreign::checked_source::check_executable_foreign_library_in_program(
                identity,
                Arc::clone(&restored.prepared[slot as usize]),
                &expected,
                super::super::super::NATIVE_TARGET,
                &restored.program,
                &mut work,
            )
            .unwrap();
        }
        let scopes = restored
            .program
            .nodes()
            .iter()
            .filter_map(|node| match &node.kind {
                crate::core::EffectExprKind::Operation(
                    crate::core::EffectOperation::SourceResourceScope(scope),
                ) => Some(scope),
                _ => None,
            })
            .collect::<Vec<_>>();
        assert_eq!(scopes.len(), 3);
        for scope in &scopes[1..] {
            assert!(Arc::ptr_eq(scopes[0].original(), scope.original()));
        }
        assert!(
            scopes
                .iter()
                .all(|scope| scope.native_interpretations().len() == 2)
        );
        drop(restored);
        let mut corrupted =
            PureImage::decode_bytes(&bytes, &mut TypeWorkBudget::default()).unwrap();
        let prefixes = corrupted.native_fact_prefixes.as_mut().unwrap();
        assert!(prefixes.types > 0);
        prefixes.types -= 1;
        assert!(
            corrupted
                .admit_expected_native_facts(&expected, &mut TypeWorkBudget::default())
                .is_err(),
            "independent expectations authenticate declaration table boundaries"
        );
        let mut corrupted =
            PureImage::decode_bytes(&bytes, &mut TypeWorkBudget::default()).unwrap();
        let claim = *get(
            &corrupted.source_copies,
            corrupted.source_scopes[0].acquire_copy,
        )
        .unwrap();
        let pairs = claim.nodes.get(&corrupted.source_node_pairs).unwrap();
        assert!(pairs.len() > 1);
        let start = claim.nodes.start as usize;
        corrupted.source_node_pairs[start].copied = corrupted.source_node_pairs[start + 1].copied;
        assert!(
            corrupted
                .restore_effect(&mut TypeWorkBudget::default())
                .is_err(),
            "copied map corruption must fail independent Core admission"
        );
        let mut corrupted =
            PureImage::decode_bytes(&bytes, &mut TypeWorkBudget::default()).unwrap();
        let interpretation = corrupted.source_scopes[0].interpretations.start as usize;
        corrupted
            .interpretations
            .swap(interpretation, interpretation + 1);
        assert!(
            corrupted
                .restore_effect(&mut TypeWorkBudget::default())
                .is_err(),
            "scope request interpretations retain exact ordered original symbols"
        );
    }
}
