//! Matching-compiler storage for source lexical forwarding and ordinary helper evidence.
//! Restored records remain claims until ordinary Core and source-scope admission.
//! This carrier preserves global/resource-family requirements and lexical/abstract
//! helper selections. Concrete implementations, adapters and captured or ordinary
//! non-resource lexical dictionaries remain explicitly unsupported.
use super::{
    ArgumentOwner, BinderIdentity, Decoder, Encoder, ImageFailure, InterfaceIdentity,
    ResourceIdentity, Slice, StructuralInput, TypeBuffer, Unsupported, Wire, WireOutput,
    WireReader, WireWriter, append, charge, get, index, push,
};
use crate::core::dialect::{
    MethodEvidenceAnchorRole, MethodEvidenceCatalog, MethodEvidenceExpectedRole,
    MethodEvidenceOwner, MethodEvidenceProducer,
};
use crate::interface::{
    EvidenceNode, EvidenceNodeId, InterfaceApplication, LexicalEvidenceId, MethodId, RequirementId,
    RequirementOwner,
};
use crate::{core::NodeId, types::TypeWorkBudget};
use std::sync::Arc;

#[derive(Clone, Copy)]
struct LexicalIdentity {
    module: u32,
    local: u32,
}
#[derive(Clone, Copy)]
struct MethodIdentity {
    interface: InterfaceIdentity,
    local: u32,
}
wire_struct!(LexicalIdentity, module, local);
wire_struct!(MethodIdentity, interface, local);

// Implementation-owned evidence remains outside this bounded carrier. Both
// source global and resource-family identities are retained without name lookup.
#[derive(Clone, Copy)]
struct MethodOwnerRecord {
    global: Option<BinderIdentity>,
    resource: Option<ResourceIdentity>,
}
#[derive(Clone, Copy)]
struct RequirementRecord {
    owner: MethodOwnerRecord,
    local: u32,
}
wire_struct!(MethodOwnerRecord, global, resource);
wire_struct!(RequirementRecord, owner, local);

fn put<T: Wire>(
    data: &mut Vec<u8>,
    value: T,
    work: &mut TypeWorkBudget,
) -> Result<(), ImageFailure> {
    let mut writer = WireWriter {
        output: WireOutput::Encoded(std::mem::take(data)),
        work,
    };
    let result = value.write(&mut writer);
    let WireOutput::Encoded(bytes) = writer.output else {
        unreachable!()
    };
    *data = bytes;
    result
}
fn take<T: Wire>(
    data: &[u8],
    offset: &mut usize,
    work: &mut TypeWorkBudget,
) -> Result<T, ImageFailure> {
    let mut reader = WireReader {
        bytes: data,
        offset: *offset,
        work,
    };
    let value = T::read(&mut reader)?;
    *offset = reader.offset;
    Ok(value)
}

impl Encoder<'_> {
    fn lexical_identity(&mut self, id: LexicalEvidenceId) -> Result<LexicalIdentity, ImageFailure> {
        Ok(LexicalIdentity {
            module: self.module(id.module())?,
            local: id.declaration(),
        })
    }
    fn method_identity(&mut self, id: MethodId) -> Result<MethodIdentity, ImageFailure> {
        Ok(MethodIdentity {
            interface: self.interface_identity(id.interface())?,
            local: id.declaration(),
        })
    }
    fn method_application(
        &mut self,
        application: &InterfaceApplication,
    ) -> Result<(InterfaceIdentity, Slice), ImageFailure> {
        let interface = self.interface_identity(application.interface())?;
        let start = self.image.source_arguments.len();
        for argument in application.arguments() {
            let argument = self.encode_structural(StructuralInput::Argument(argument))?;
            push(&mut self.image.source_arguments, argument, self.work)?;
        }
        Ok((interface, Slice::of(&self.image.source_arguments, start)?))
    }
    fn method_owner(
        &mut self,
        owner: Option<MethodEvidenceOwner>,
    ) -> Result<Option<MethodOwnerRecord>, ImageFailure> {
        owner
            .map(|owner| match owner {
                MethodEvidenceOwner::Global(binder) => Ok(MethodOwnerRecord {
                    global: Some(self.binder_id(binder)?),
                    resource: None,
                }),
                MethodEvidenceOwner::ResourceFamily(resource) => Ok(MethodOwnerRecord {
                    global: None,
                    resource: Some(self.resource_identity(resource)?),
                }),
                MethodEvidenceOwner::Implementation(_) => {
                    Err(ImageFailure::Unsupported(Unsupported::MethodEvidence))
                }
            })
            .transpose()
    }
    fn method_requirement(
        &mut self,
        requirement: RequirementId,
    ) -> Result<RequirementRecord, ImageFailure> {
        let owner = match requirement.owner() {
            RequirementOwner::Global(binder) => MethodEvidenceOwner::Global(binder),
            RequirementOwner::ResourceFamily(resource) => {
                MethodEvidenceOwner::ResourceFamily(resource)
            }
            RequirementOwner::Impl(_) => {
                return Err(ImageFailure::Unsupported(Unsupported::MethodEvidence));
            }
        };
        Ok(RequirementRecord {
            owner: self
                .method_owner(Some(owner))?
                .ok_or(ImageFailure::InvalidRecord)?,
            local: requirement.declaration(),
        })
    }
    fn put_method_producer(
        &mut self,
        data: &mut Vec<u8>,
        producer: MethodEvidenceProducer,
    ) -> Result<(), ImageFailure> {
        match producer {
            MethodEvidenceProducer::Lexical { source } => {
                let source = self.lexical_identity(source)?;
                put(data, 0u8, self.work)?;
                put(data, source, self.work)
            }
            MethodEvidenceProducer::Abstract { requirement } => {
                let requirement = self.method_requirement(requirement)?;
                put(data, 1u8, self.work)?;
                put(data, requirement, self.work)
            }
            _ => Err(ImageFailure::Unsupported(Unsupported::MethodEvidence)),
        }
    }
    fn put_method_selection(
        &mut self,
        data: &mut Vec<u8>,
        selection: &crate::interface::EvidenceSelection,
    ) -> Result<(), ImageFailure> {
        let interface = self.interface_identity(selection.interface())?;
        let start = self.image.source_arguments.len();
        for argument in selection.arguments() {
            let argument = self.encode_structural(StructuralInput::Argument(argument))?;
            push(&mut self.image.source_arguments, argument, self.work)?;
        }
        let arguments = Slice::of(&self.image.source_arguments, start)?;
        put(data, interface, self.work)?;
        put(data, arguments, self.work)?;
        put(data, index(selection.node_count())?, self.work)?;
        put(data, index(selection.root().index())?, self.work)?;
        for slot in 0..selection.node_count() {
            charge(self.work, 1)?;
            let methods = match selection.node(EvidenceNodeId::new(slot)) {
                Some(EvidenceNode::Lexical { source, methods }) => {
                    let source = self.lexical_identity(source)?;
                    put(data, 0u8, self.work)?;
                    put(data, source, self.work)?;
                    methods
                }
                Some(EvidenceNode::Abstract {
                    requirement,
                    methods,
                }) => {
                    let requirement = self.method_requirement(requirement)?;
                    put(data, 1u8, self.work)?;
                    put(data, requirement, self.work)?;
                    methods
                }
                _ => return Err(ImageFailure::Unsupported(Unsupported::MethodEvidence)),
            };
            put(data, index(methods.len())?, self.work)?;
            for method in methods {
                let method = self.method_identity(*method)?;
                put(data, method, self.work)?;
            }
        }
        Ok(())
    }
    fn method_occurrence(
        &mut self,
        catalog: &MethodEvidenceCatalog,
        slot: Option<usize>,
    ) -> Result<Option<u32>, ImageFailure> {
        charge(self.work, catalog.occurrences().len())?;
        slot.map(|slot| {
            catalog
                .occurrences()
                .iter()
                .position(|row| row.slot == slot)
                .ok_or(ImageFailure::InvalidRecord)
                .and_then(index)
        })
        .transpose()
    }
    pub(super) fn encode_source_forwardings(
        &mut self,
        lexical: LexicalEvidenceId,
        forwardings: &[crate::core::provider::ProviderForwardingMethod],
    ) -> Result<Slice, ImageFailure> {
        let mut data = Vec::new();
        let lexical = self.lexical_identity(lexical)?;
        put(&mut data, lexical, self.work)?;
        put(&mut data, index(forwardings.len())?, self.work)?;
        for forwarding in forwardings {
            let method = self.method_identity(forwarding.method)?;
            let binder = self.binder_id(forwarding.binder)?;
            put(&mut data, method, self.work)?;
            put(&mut data, binder, self.work)?;
        }
        append(&mut self.image.source_method_evidence, &data, self.work)
    }
    pub(super) fn encode_source_method_evidence(
        &mut self,
        catalog: &MethodEvidenceCatalog,
    ) -> Result<Slice, ImageFailure> {
        if !catalog.implementation_owners().is_empty()
            || !catalog.adapters().is_empty()
            || !catalog.concrete_sources().is_empty()
        {
            return Err(ImageFailure::Unsupported(Unsupported::MethodEvidence));
        }
        let mut data = Vec::new();
        put(&mut data, index(catalog.lexical_owners().len())?, self.work)?;
        for owner in catalog.lexical_owners() {
            if !owner.source_parameters.is_empty() || !owner.captures.is_empty() {
                return Err(ImageFailure::Unsupported(Unsupported::MethodEvidence));
            }
            let source = self.lexical_identity(owner.source)?;
            let method = self.method_identity(owner.method)?;
            let binder = self.binder_id(owner.binder)?;
            let (interface, application) = self.method_application(&owner.application)?;
            put(&mut data, source, self.work)?;
            put(&mut data, method, self.work)?;
            put(&mut data, binder, self.work)?;
            match &owner.resource {
                Some(crate::core::dialect::MethodEvidenceResourceOwner::Provider(resource)) => {
                    put(&mut data, 0u8, self.work)?;
                    let definition = self.resource_identity(resource.definition)?;
                    let family = self.nominal(resource.family)?;
                    let identity = self.type_variable(resource.identity)?;
                    let start = self.image.source_arguments.len();
                    for argument in &resource.arguments {
                        let argument =
                            self.encode_structural(StructuralInput::Argument(argument))?;
                        push(&mut self.image.source_arguments, argument, self.work)?;
                    }
                    let arguments = Slice::of(&self.image.source_arguments, start)?;
                    put(&mut data, definition, self.work)?;
                    put(&mut data, family, self.work)?;
                    put(&mut data, identity, self.work)?;
                    put(&mut data, arguments, self.work)?;
                }
                Some(crate::core::dialect::MethodEvidenceResourceOwner::Builtin(acquisition)) => {
                    put(&mut data, 1u8, self.work)?;
                    let acquisition = self.encode_cell_acquisition(*acquisition)?;
                    put(&mut data, acquisition, self.work)?;
                }
                None => return Err(ImageFailure::Unsupported(Unsupported::MethodEvidence)),
            }
            put(&mut data, interface, self.work)?;
            put(&mut data, application, self.work)?;
        }
        put(&mut data, index(catalog.domains().len())?, self.work)?;
        for domain in catalog.domains() {
            let owner = self
                .method_owner(Some(domain.owner))?
                .ok_or(ImageFailure::InvalidRecord)?;
            let requirement = self.method_requirement(domain.requirement)?;
            let method = self.method_identity(domain.method)?;
            let (interface, arguments) = self.method_application(&domain.application)?;
            put(&mut data, index(domain.source_parameters.len())?, self.work)?;
            for (id, kind) in &domain.source_parameters {
                let id = self.type_variable(*id)?;
                let kind = self.encode_kind(kind)?;
                put(&mut data, id, self.work)?;
                put(&mut data, kind, self.work)?;
            }
            put(&mut data, owner, self.work)?;
            put(&mut data, requirement, self.work)?;
            put(&mut data, domain.requirement_position, self.work)?;
            put(&mut data, method, self.work)?;
            put(&mut data, domain.method_position, self.work)?;
            put(&mut data, interface, self.work)?;
            put(&mut data, arguments, self.work)?;
        }
        put(&mut data, index(catalog.occurrences().len())?, self.work)?;
        for occurrence in catalog.occurrences() {
            let owner = self.method_owner(occurrence.scope)?;
            let binder = occurrence
                .scope_binder
                .map(|binder| self.binder_id(binder))
                .transpose()?;
            let target_owner = self.method_owner(occurrence.target_owner)?;
            let target_requirement = occurrence
                .target_requirement
                .map(|id| self.method_requirement(id))
                .transpose()?;
            let method = occurrence
                .checked_method
                .map(|method| self.method_identity(method))
                .transpose()?;
            let (interface, application) =
                self.method_application(&occurrence.checked_application)?;
            let value = occurrence
                .checked_value_type
                .as_ref()
                .map(|ty| self.encode_type(ty))
                .transpose()?;
            put(&mut data, owner, self.work)?;
            put(&mut data, binder, self.work)?;
            put(&mut data, target_owner, self.work)?;
            put(&mut data, target_requirement, self.work)?;
            put(&mut data, method, self.work)?;
            put(&mut data, interface, self.work)?;
            put(&mut data, application, self.work)?;
            put(&mut data, value, self.work)?;
            put(
                &mut data,
                index(occurrence.method_arguments.len())?,
                self.work,
            )?;
            for argument in &occurrence.method_arguments {
                let argument = self.encode_type(argument)?;
                put(&mut data, argument, self.work)?;
            }
            self.put_method_selection(&mut data, &occurrence.selection)?;
        }
        put(&mut data, index(catalog.expectations().len())?, self.work)?;
        for expectation in catalog.expectations() {
            let occurrence = self.method_occurrence(catalog, expectation.occurrence)?;
            let method = self.method_identity(expectation.method)?;
            put(&mut data, occurrence, self.work)?;
            put(&mut data, method, self.work)?;
            match expectation.role {
                MethodEvidenceExpectedRole::LexicalOwner { owner } => {
                    put(&mut data, 0u8, self.work)?;
                    put(&mut data, index(owner)?, self.work)?;
                }
                MethodEvidenceExpectedRole::LexicalUse {
                    owner,
                    selection_node,
                } => {
                    put(&mut data, 1u8, self.work)?;
                    put(&mut data, index(owner)?, self.work)?;
                    put(&mut data, index(selection_node.index())?, self.work)?;
                }
                MethodEvidenceExpectedRole::Domain { domain } => {
                    put(&mut data, 2u8, self.work)?;
                    put(&mut data, index(domain)?, self.work)?;
                }
                MethodEvidenceExpectedRole::Application { domain, producer } => {
                    put(&mut data, 3u8, self.work)?;
                    put(&mut data, index(domain)?, self.work)?;
                    put(&mut data, index(producer)?, self.work)?;
                }
                MethodEvidenceExpectedRole::Instantiation { producer } => {
                    put(&mut data, 4u8, self.work)?;
                    put(&mut data, index(producer)?, self.work)?;
                }
                _ => return Err(ImageFailure::Unsupported(Unsupported::MethodEvidence)),
            }
        }
        append(&mut self.image.source_method_evidence, &data, self.work)
    }
    pub(super) fn encode_source_method_anchors(
        &mut self,
        catalog: &MethodEvidenceCatalog,
        anchors: &[crate::core::dialect::MethodEvidenceAnchor],
    ) -> Result<Slice, ImageFailure> {
        let mut data = Vec::new();
        put(&mut data, index(anchors.len())?, self.work)?;
        for anchor in anchors {
            let node = self.node(anchor.node)?;
            let owner = self.method_owner(anchor.owner)?;
            let requirement = anchor
                .requirement
                .map(|id| self.method_requirement(id))
                .transpose()?;
            let method = self.method_identity(anchor.method)?;
            let (interface, application) = self.method_application(&anchor.application)?;
            let occurrence = self.method_occurrence(catalog, anchor.occurrence)?;
            put(&mut data, node, self.work)?;
            put(&mut data, owner, self.work)?;
            put(&mut data, requirement, self.work)?;
            put(&mut data, method, self.work)?;
            put(&mut data, interface, self.work)?;
            put(&mut data, application, self.work)?;
            match anchor.role {
                MethodEvidenceAnchorRole::LexicalOwner { source, binder } => {
                    let source = self.lexical_identity(source)?;
                    let binder = self.binder_id(binder)?;
                    put(&mut data, 0u8, self.work)?;
                    put(&mut data, source, self.work)?;
                    put(&mut data, binder, self.work)?;
                }
                MethodEvidenceAnchorRole::LexicalUse {
                    source,
                    binder,
                    selection_node,
                } => {
                    let source = self.lexical_identity(source)?;
                    let binder = self.binder_id(binder)?;
                    put(&mut data, 1u8, self.work)?;
                    put(&mut data, source, self.work)?;
                    put(&mut data, binder, self.work)?;
                    put(&mut data, index(selection_node.index())?, self.work)?;
                }
                MethodEvidenceAnchorRole::Domain { binder } => {
                    let binder = self.binder_id(binder)?;
                    put(&mut data, 2u8, self.work)?;
                    put(&mut data, binder, self.work)?;
                }
                MethodEvidenceAnchorRole::Application { producer } => {
                    put(&mut data, 3u8, self.work)?;
                    self.put_method_producer(&mut data, producer)?;
                }
                MethodEvidenceAnchorRole::Instantiation { binder } => {
                    let binder = binder.map(|id| self.binder_id(id)).transpose()?;
                    put(&mut data, 4u8, self.work)?;
                    put(&mut data, binder, self.work)?;
                }
                _ => return Err(ImageFailure::Unsupported(Unsupported::MethodEvidence)),
            }
            put(&mut data, occurrence, self.work)?;
            put(&mut data, index(anchor.expectation)?, self.work)?;
        }
        append(&mut self.image.source_method_evidence, &data, self.work)
    }
}

impl Decoder<'_> {
    fn lexical_identity(&mut self, id: LexicalIdentity) -> Result<LexicalEvidenceId, ImageFailure> {
        charge(self.work, 1)?;
        Ok(LexicalEvidenceId::new(
            *get(&self.modules, id.module)?,
            id.local,
        ))
    }
    fn method_identity(&mut self, id: MethodIdentity) -> Result<MethodId, ImageFailure> {
        Ok(MethodId::new(
            self.interface_identity(id.interface)?,
            id.local,
        ))
    }
    fn method_arguments(
        &mut self,
        arguments: Slice,
    ) -> Result<Box<[crate::types::KindedArgument]>, ImageFailure> {
        let mut guarded = Vec::new();
        for argument in arguments.get(&self.image.source_arguments)? {
            let argument = self.structural(*argument)?.argument()?;
            push(&mut guarded, argument, self.work)?;
        }
        let mut retained = Vec::new();
        charge(self.work, guarded.len())?;
        retained
            .try_reserve_exact(guarded.len())
            .map_err(|_| ImageFailure::Resource)?;
        retained.extend(guarded.into_iter().map(ArgumentOwner::into_inner));
        Ok(retained.into_boxed_slice())
    }
    fn method_application(
        &mut self,
        interface: InterfaceIdentity,
        arguments: Slice,
    ) -> Result<InterfaceApplication, ImageFailure> {
        Ok(InterfaceApplication::new_kinded(
            self.interface_identity(interface)?,
            self.method_arguments(arguments)?,
        ))
    }
    fn method_owner(
        &mut self,
        owner: Option<MethodOwnerRecord>,
    ) -> Result<Option<MethodEvidenceOwner>, ImageFailure> {
        owner
            .map(|owner| {
                charge(self.work, 1)?;
                match (owner.global, owner.resource) {
                    (Some(binder), None) => {
                        Ok(MethodEvidenceOwner::Global(self.binder_id(binder)?))
                    }
                    (None, Some(resource)) => Ok(MethodEvidenceOwner::ResourceFamily(
                        self.resource_identity(resource)?,
                    )),
                    _ => Err(ImageFailure::InvalidRecord),
                }
            })
            .transpose()
    }
    fn method_requirement(
        &mut self,
        requirement: RequirementRecord,
    ) -> Result<RequirementId, ImageFailure> {
        let owner = match self
            .method_owner(Some(requirement.owner))?
            .ok_or(ImageFailure::InvalidRecord)?
        {
            MethodEvidenceOwner::Global(binder) => RequirementOwner::Global(binder),
            MethodEvidenceOwner::ResourceFamily(resource) => {
                RequirementOwner::ResourceFamily(resource)
            }
            MethodEvidenceOwner::Implementation(_) => return Err(ImageFailure::InvalidRecord),
        };
        Ok(RequirementId::new(owner, requirement.local))
    }
    fn take_method_producer(
        &mut self,
        bytes: &[u8],
        offset: &mut usize,
    ) -> Result<MethodEvidenceProducer, ImageFailure> {
        match take::<u8>(bytes, offset, self.work)? {
            0 => {
                let source = take(bytes, offset, self.work)?;
                Ok(MethodEvidenceProducer::Lexical {
                    source: self.lexical_identity(source)?,
                })
            }
            1 => {
                let requirement = take(bytes, offset, self.work)?;
                Ok(MethodEvidenceProducer::Abstract {
                    requirement: self.method_requirement(requirement)?,
                })
            }
            _ => Err(ImageFailure::InvalidRecord),
        }
    }
    fn take_method_selection(
        &mut self,
        bytes: &[u8],
        offset: &mut usize,
    ) -> Result<crate::interface::EvidenceSelection, ImageFailure> {
        let interface = take(bytes, offset, self.work)?;
        let arguments = take(bytes, offset, self.work)?;
        let application = self.method_application(interface, arguments)?;
        let count: u32 = take(bytes, offset, self.work)?;
        let root: u32 = take(bytes, offset, self.work)?;
        let root = usize::try_from(root).map_err(|_| ImageFailure::InvalidRecord)?;
        if root >= usize::try_from(count).map_err(|_| ImageFailure::InvalidRecord)? {
            return Err(ImageFailure::InvalidRecord);
        }
        let mut selection = crate::interface::EvidenceSelectionBuilder::new();
        for slot in 0..count {
            let tag: u8 = take(bytes, offset, self.work)?;
            let source = match tag {
                0 => Some(take::<LexicalIdentity>(bytes, offset, self.work)?),
                1 => None,
                _ => return Err(ImageFailure::InvalidRecord),
            };
            let requirement = if tag == 1 {
                Some(take::<RequirementRecord>(bytes, offset, self.work)?)
            } else {
                None
            };
            let count: u32 = take(bytes, offset, self.work)?;
            let mut methods = Vec::new();
            for _ in 0..count {
                let method = take(bytes, offset, self.work)?;
                let method = self.method_identity(method)?;
                push(&mut methods, method, self.work)?;
            }
            // Transfer every builder charge, including failed-operation work,
            // into the same cumulative reconstruction allowance.
            let source = source
                .map(|source| self.lexical_identity(source))
                .transpose()?;
            let requirement = requirement
                .map(|id| self.method_requirement(id))
                .transpose()?;
            let mut constraints =
                crate::interface::InterfaceConstraintBudget::with_limit(self.work.remaining());
            let prepared = match (source, requirement) {
                (Some(source), None) => selection.push_lexical(source, &methods, &mut constraints),
                (None, Some(requirement)) => {
                    selection.push_abstract(requirement, &methods, &mut constraints)
                }
                _ => return Err(ImageFailure::InvalidRecord),
            };
            charge(self.work, constraints.used())?;
            let id = prepared.map_err(|_| ImageFailure::Resource)?;
            if id.index() != usize::try_from(slot).map_err(|_| ImageFailure::InvalidRecord)? {
                return Err(ImageFailure::InvalidRecord);
            }
        }
        charge(self.work, 2)?;
        selection
            .finish(EvidenceNodeId::new(root), application)
            .map_err(|_| ImageFailure::InvalidRecord)
    }
    fn method_occurrence_key(
        &mut self,
        catalog: &MethodEvidenceCatalog,
        wire: Option<u32>,
    ) -> Result<Option<usize>, ImageFailure> {
        wire.map(|wire| {
            charge(
                self.work,
                catalog
                    .occurrences()
                    .len()
                    .checked_add(1)
                    .ok_or(ImageFailure::Resource)?,
            )?;
            // Pins remain in occurrence WIRE order. Slot-sorted rows are used
            // only for catalog lookup, never as the wire ordinal translation.
            let key = get(catalog.final_occurrence_owners(), wire)?.storage_id();
            if catalog.occurrence(key).is_none() {
                return Err(ImageFailure::InvalidRecord);
            }
            Ok(key)
        })
        .transpose()
    }
    pub(super) fn source_forwardings(
        &mut self,
        record: Slice,
    ) -> Result<
        (
            LexicalEvidenceId,
            Box<[crate::core::provider::ProviderForwardingMethod]>,
        ),
        ImageFailure,
    > {
        let bytes = record.get(&self.image.source_method_evidence)?;
        let mut offset = 0;
        let id = take(bytes, &mut offset, self.work)?;
        let lexical = self.lexical_identity(id)?;
        let count: u32 = take(bytes, &mut offset, self.work)?;
        let mut forwardings = Vec::new();
        for _ in 0..count {
            let method = take(bytes, &mut offset, self.work)?;
            let binder = take(bytes, &mut offset, self.work)?;
            let forwarding = crate::core::provider::ProviderForwardingMethod {
                method: self.method_identity(method)?,
                binder: self.binder_id(binder)?,
            };
            push(&mut forwardings, forwarding, self.work)?;
        }
        if offset != bytes.len() {
            return Err(ImageFailure::InvalidRecord);
        }
        Ok((lexical, forwardings.into_boxed_slice()))
    }
    pub(super) fn source_method_evidence(
        &mut self,
        record: Slice,
        mut methods: Vec<crate::core::dialect::MethodEvidenceMethod>,
    ) -> Result<Arc<MethodEvidenceCatalog>, ImageFailure> {
        // Restored ordinary modules use DirectCoreSource identities, whereas
        // the sealed cell retains its builtin namespace. Relocation can reverse
        // their original ordering. Rebuild the identity-keyed lookup order with
        // paid comparisons, retaining all original IDs, types and duplicates
        // for the ordinary independent authentication below.
        charge(self.work, methods.len().saturating_sub(1))?;
        if methods.windows(2).any(|pair| pair[0].id >= pair[1].id) {
            for index in 1..methods.len() {
                let mut cursor = index;
                while cursor > 0 {
                    charge(self.work, 1)?;
                    if methods[cursor - 1].id <= methods[cursor].id {
                        break;
                    }
                    methods.swap(cursor - 1, cursor);
                    cursor -= 1;
                }
            }
            charge(self.work, methods.len().saturating_sub(1))?;
            if methods.windows(2).any(|pair| pair[0].id >= pair[1].id) {
                return Err(ImageFailure::InvalidRecord);
            }
        }
        let bytes = record.get(&self.image.source_method_evidence)?;
        let mut offset = 0;
        let count: u32 = take(bytes, &mut offset, self.work)?;
        let mut owners = Vec::new();
        for _ in 0..count {
            let source = take(bytes, &mut offset, self.work)?;
            let method = take(bytes, &mut offset, self.work)?;
            let binder = take(bytes, &mut offset, self.work)?;
            let resource = match take::<u8>(bytes, &mut offset, self.work)? {
                0 => {
                    let definition = take(bytes, &mut offset, self.work)?;
                    let family = take(bytes, &mut offset, self.work)?;
                    let identity = take(bytes, &mut offset, self.work)?;
                    let arguments = take(bytes, &mut offset, self.work)?;
                    crate::core::dialect::MethodEvidenceResourceOwner::Provider(
                        crate::core::dialect::ProviderEvidenceOwner {
                            definition: self.resource_identity(definition)?,
                            family: self.nominal(family)?,
                            identity: self.type_variable(identity)?,
                            arguments: self.method_arguments(arguments)?,
                        },
                    )
                }
                1 => {
                    let acquisition = take(bytes, &mut offset, self.work)?;
                    crate::core::dialect::MethodEvidenceResourceOwner::Builtin(
                        self.cell_acquisition(acquisition)?,
                    )
                }
                _ => return Err(ImageFailure::InvalidRecord),
            };
            let interface = take(bytes, &mut offset, self.work)?;
            let application = take(bytes, &mut offset, self.work)?;
            let owner = crate::core::dialect::MethodEvidenceLexicalOwner {
                resource: Some(resource),
                source_parameters: Box::new([]),
                source: self.lexical_identity(source)?,
                method: self.method_identity(method)?,
                binder: self.binder_id(binder)?,
                application: self.method_application(interface, application)?,
                captures: Box::new([]),
            };
            push(&mut owners, owner, self.work)?;
        }
        let count: u32 = take(bytes, &mut offset, self.work)?;
        let mut domains = Vec::new();
        for _ in 0..count {
            let count: u32 = take(bytes, &mut offset, self.work)?;
            let mut parameters = Vec::new();
            for _ in 0..count {
                let id = take(bytes, &mut offset, self.work)?;
                let kind = take(bytes, &mut offset, self.work)?;
                let id = self.type_variable(id)?;
                let kind = self.kind(kind)?;
                push(&mut parameters, (id, kind), self.work)?;
            }
            let owner = take(bytes, &mut offset, self.work)?;
            let requirement = take(bytes, &mut offset, self.work)?;
            let requirement_position = take(bytes, &mut offset, self.work)?;
            let method = take(bytes, &mut offset, self.work)?;
            let method_position = take(bytes, &mut offset, self.work)?;
            let interface = take(bytes, &mut offset, self.work)?;
            let arguments = take(bytes, &mut offset, self.work)?;
            let domain = crate::core::dialect::MethodEvidenceDomain {
                source_parameters: parameters.into_boxed_slice(),
                owner: self
                    .method_owner(Some(owner))?
                    .ok_or(ImageFailure::InvalidRecord)?,
                requirement: self.method_requirement(requirement)?,
                requirement_position,
                method: self.method_identity(method)?,
                method_position,
                application: self.method_application(interface, arguments)?,
            };
            push(&mut domains, domain, self.work)?;
        }
        let count: u32 = take(bytes, &mut offset, self.work)?;
        let mut occurrences = Vec::new();
        let mut pins = Vec::new();
        let mut keys = Vec::new();
        for _ in 0..count {
            let scope = take(bytes, &mut offset, self.work)?;
            let scope_binder: Option<BinderIdentity> = take(bytes, &mut offset, self.work)?;
            let target_owner = take(bytes, &mut offset, self.work)?;
            let target_requirement: Option<RequirementRecord> =
                take(bytes, &mut offset, self.work)?;
            let method: Option<MethodIdentity> = take(bytes, &mut offset, self.work)?;
            let interface = take(bytes, &mut offset, self.work)?;
            let arguments = take(bytes, &mut offset, self.work)?;
            let value: Option<u32> = take(bytes, &mut offset, self.work)?;
            let count: u32 = take(bytes, &mut offset, self.work)?;
            let mut method_arguments = TypeBuffer(Vec::new());
            for _ in 0..count {
                let argument = take(bytes, &mut offset, self.work)?;
                let argument = self.ty(argument)?;
                charge(self.work, 1)?;
                method_arguments
                    .0
                    .try_reserve(1)
                    .map_err(|_| ImageFailure::Resource)?;
                method_arguments.0.push(argument.into_inner());
            }
            let selection = self.take_method_selection(bytes, &mut offset)?;
            let application = self.method_application(interface, arguments)?;
            let checked_value_type = value.map(|value| self.ty(value)).transpose()?;
            let scope = self.method_owner(scope)?;
            let scope_binder = scope_binder.map(|id| self.binder_id(id)).transpose()?;
            let target_owner = self.method_owner(target_owner)?;
            let target_requirement = target_requirement
                .map(|id| self.method_requirement(id))
                .transpose()?;
            let checked_method = method
                .map(|method| self.method_identity(method))
                .transpose()?;
            let pin = crate::interface::FinalOccurrenceOwner::new_with_budget(self.work)
                .map_err(|_| ImageFailure::Resource)?;
            let slot = pin.storage_id();
            let occurrence = crate::core::dialect::MethodEvidenceOccurrence {
                slot,
                scope,
                scope_binder,
                target_owner,
                target_requirement,
                checked_method,
                checked_application: application,
                method_arguments: method_arguments.into_vec().into_boxed_slice(),
                checked_value_type: checked_value_type
                    .map(crate::types::IterativeTypeOwner::into_inner),
                selection,
            };
            push(&mut pins, pin, self.work)?;
            push(&mut keys, slot, self.work)?;
            push(&mut occurrences, occurrence, self.work)?;
        }
        let count: u32 = take(bytes, &mut offset, self.work)?;
        let mut expectations = Vec::new();
        for _ in 0..count {
            let occurrence: Option<u32> = take(bytes, &mut offset, self.work)?;
            let method = take(bytes, &mut offset, self.work)?;
            let tag: u8 = take(bytes, &mut offset, self.work)?;
            let first: u32 = take(bytes, &mut offset, self.work)?;
            let first = usize::try_from(first).map_err(|_| ImageFailure::InvalidRecord)?;
            let role = match tag {
                0 => MethodEvidenceExpectedRole::LexicalOwner { owner: first },
                1 => {
                    let node: u32 = take(bytes, &mut offset, self.work)?;
                    MethodEvidenceExpectedRole::LexicalUse {
                        owner: first,
                        selection_node: EvidenceNodeId::new(
                            usize::try_from(node).map_err(|_| ImageFailure::InvalidRecord)?,
                        ),
                    }
                }
                2 => MethodEvidenceExpectedRole::Domain { domain: first },
                3 => {
                    let producer: u32 = take(bytes, &mut offset, self.work)?;
                    MethodEvidenceExpectedRole::Application {
                        domain: first,
                        producer: usize::try_from(producer)
                            .map_err(|_| ImageFailure::InvalidRecord)?,
                    }
                }
                4 => MethodEvidenceExpectedRole::Instantiation { producer: first },
                _ => return Err(ImageFailure::InvalidRecord),
            };
            let occurrence = occurrence.map(|id| get(&keys, id).copied()).transpose()?;
            let expected = crate::core::dialect::MethodEvidenceExpectation {
                occurrence,
                method: self.method_identity(method)?,
                role,
            };
            push(&mut expectations, expected, self.work)?;
        }
        if offset != bytes.len() {
            return Err(ImageFailure::InvalidRecord);
        }
        // Fresh allocation keys never enter the wire. Keep pins and keys in
        // decoded wire order even when arbitrary allocation order sorts rows.
        charge(
            self.work,
            occurrences
                .len()
                .checked_mul(occurrences.len())
                .ok_or(ImageFailure::Resource)?,
        )?;
        occurrences.sort_unstable_by_key(|row| row.slot);
        let mut catalog = MethodEvidenceCatalog::new(
            methods,
            Vec::new(),
            domains,
            occurrences,
            Vec::new(),
            Vec::new(),
            expectations,
        );
        catalog.set_lexical_owners(owners);
        catalog
            .attach_final_occurrence_owners(pins, &keys, self.work)
            .map_err(ImageFailure::Validation)?;
        charge(self.work, 1)?;
        Ok(Arc::new(catalog))
    }
    pub(super) fn source_method_anchors(
        &mut self,
        builder: &mut crate::core::EffectCoreBuilder,
        nodes: &[NodeId],
        catalog: &MethodEvidenceCatalog,
        record: Slice,
    ) -> Result<(), ImageFailure> {
        let bytes = record.get(&self.image.source_method_evidence)?;
        let mut offset = 0;
        let count: u32 = take(bytes, &mut offset, self.work)?;
        for _ in 0..count {
            let node = take(bytes, &mut offset, self.work)?;
            let owner = take(bytes, &mut offset, self.work)?;
            let requirement: Option<RequirementRecord> = take(bytes, &mut offset, self.work)?;
            let method = take(bytes, &mut offset, self.work)?;
            let interface = take(bytes, &mut offset, self.work)?;
            let application = take(bytes, &mut offset, self.work)?;
            let role = match take::<u8>(bytes, &mut offset, self.work)? {
                0 => {
                    let source = take(bytes, &mut offset, self.work)?;
                    let binder = take(bytes, &mut offset, self.work)?;
                    MethodEvidenceAnchorRole::LexicalOwner {
                        source: self.lexical_identity(source)?,
                        binder: self.binder_id(binder)?,
                    }
                }
                1 => {
                    let source = take(bytes, &mut offset, self.work)?;
                    let binder = take(bytes, &mut offset, self.work)?;
                    let selection_node: u32 = take(bytes, &mut offset, self.work)?;
                    MethodEvidenceAnchorRole::LexicalUse {
                        source: self.lexical_identity(source)?,
                        binder: self.binder_id(binder)?,
                        selection_node: EvidenceNodeId::new(
                            usize::try_from(selection_node)
                                .map_err(|_| ImageFailure::InvalidRecord)?,
                        ),
                    }
                }
                2 => {
                    let binder = take(bytes, &mut offset, self.work)?;
                    MethodEvidenceAnchorRole::Domain {
                        binder: self.binder_id(binder)?,
                    }
                }
                3 => MethodEvidenceAnchorRole::Application {
                    producer: self.take_method_producer(bytes, &mut offset)?,
                },
                4 => {
                    let binder: Option<BinderIdentity> = take(bytes, &mut offset, self.work)?;
                    MethodEvidenceAnchorRole::Instantiation {
                        binder: binder.map(|binder| self.binder_id(binder)).transpose()?,
                    }
                }
                _ => return Err(ImageFailure::InvalidRecord),
            };
            let occurrence: Option<u32> = take(bytes, &mut offset, self.work)?;
            let expectation: u32 = take(bytes, &mut offset, self.work)?;
            let expectation =
                usize::try_from(expectation).map_err(|_| ImageFailure::InvalidRecord)?;
            let occurrence = self.method_occurrence_key(catalog, occurrence)?;
            let application = self.method_application(interface, application)?;
            let owner = self.method_owner(owner)?;
            let requirement = requirement
                .map(|id| self.method_requirement(id))
                .transpose()?;
            let method = self.method_identity(method)?;
            let node = *get(nodes, node)?;
            charge(self.work, 8)?;
            builder.with_caller_type_work(self.work, |builder| {
                builder.authenticate_method_evidence(
                    node,
                    owner,
                    requirement,
                    method,
                    application,
                    role,
                    occurrence,
                )
            })?;
            // Authentication may normalize the occurrence's owner. The wire
            // must already claim that exact owner; do not silently repair it.
            let anchor = builder
                .method_evidence_anchors()
                .last()
                .ok_or(ImageFailure::InvalidRecord)?;
            if anchor.node != node
                || anchor.owner != owner
                || anchor.requirement != requirement
                || anchor.method != method
                || anchor.role != role
                || anchor.occurrence != occurrence
                || anchor.expectation != expectation
            {
                return Err(ImageFailure::InvalidRecord);
            }
        }
        if offset != bytes.len() {
            return Err(ImageFailure::InvalidRecord);
        }
        Ok(())
    }
}
