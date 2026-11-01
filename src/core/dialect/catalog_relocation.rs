//! Structural assembly of completed, compiler-owned module evidence.

use std::{collections::HashMap, sync::Arc};

use super::{
    BuildError, IterativeArgumentBuffer, MethodEvidenceAdapter, MethodEvidenceAdapterEdge,
    MethodEvidenceAnchor, MethodEvidenceAnchorRole, MethodEvidenceCatalog,
    MethodEvidenceConcreteSource, MethodEvidenceDomain, MethodEvidenceExpectation,
    MethodEvidenceExpectedProducer, MethodEvidenceExpectedRole, MethodEvidenceImplementationOwner,
    MethodEvidenceLexicalOwner, MethodEvidenceMethod, MethodEvidenceOccurrence,
    MethodEvidenceOwner, MethodEvidenceResourceOwner, NodeId,
};
use crate::{
    core::transform::FragmentIdentities,
    interface::{ImplMethodId, InterfaceApplication, MethodId, RequirementId},
    module::ModuleId,
    resolved::BinderId,
    types::{
        Type, TypeVariableId, TypeWorkBudget, clone_kinded_type_parameters_with_budget,
        clone_type_with_budget, discard_type_iteratively,
    },
};

#[derive(Clone, Copy, Debug)]
pub(crate) struct CompletedCatalogOffsets {
    pub(crate) lexical: usize,
    pub(crate) expectations: usize,
}

fn resource() -> BuildError {
    BuildError::TypeWorkExceeded
}

fn binder(id: BinderId, identities: &FragmentIdentities) -> Result<BinderId, BuildError> {
    match id {
        BinderId::Resolved { .. } => Ok(id),
        BinderId::Generated(_) => identities
            .binders
            .get(&id)
            .copied()
            .ok_or(BuildError::InvalidPayload),
    }
}

fn variable(
    id: TypeVariableId,
    identities: &FragmentIdentities,
) -> Result<TypeVariableId, BuildError> {
    match id {
        TypeVariableId::Resolved { .. } => Ok(id),
        TypeVariableId::Generated(_) => identities
            .variables
            .get(&id)
            .copied()
            .ok_or(BuildError::InvalidPayload),
    }
}

fn owner(
    value: MethodEvidenceOwner,
    identities: &FragmentIdentities,
) -> Result<MethodEvidenceOwner, BuildError> {
    match value {
        MethodEvidenceOwner::Global(id) => Ok(MethodEvidenceOwner::Global(binder(id, identities)?)),
        other => Ok(other),
    }
}

fn owner_module(owner: MethodEvidenceOwner) -> Option<ModuleId> {
    match owner {
        MethodEvidenceOwner::Global(id) => id.module(),
        MethodEvidenceOwner::Implementation(id) => Some(id.implementation().module()),
        MethodEvidenceOwner::ResourceFamily(id) => Some(id.module()),
    }
}

fn ty(
    value: &Type,
    identities: &FragmentIdentities,
    work: &mut TypeWorkBudget,
) -> Result<Type, BuildError> {
    crate::types::rename_fragment_type_with(
        value,
        &identities.variables,
        None,
        |units| work.charge(units),
        || (),
    )
    .map_err(|()| resource())?
    .map_err(|_| BuildError::InvalidPayload)
}

fn application(
    value: &InterfaceApplication,
    identities: &FragmentIdentities,
    work: &mut TypeWorkBudget,
) -> Result<InterfaceApplication, BuildError> {
    work.charge(value.arguments().len())
        .map_err(|()| resource())?;
    let mut arguments = IterativeArgumentBuffer(Vec::new());
    arguments
        .0
        .try_reserve_exact(value.arguments().len())
        .map_err(|_| resource())?;
    for argument in value.arguments() {
        arguments.0.push(
            crate::types::rename_fragment_argument_with(
                argument,
                &identities.variables,
                None,
                |units| work.charge(units),
                || (),
            )
            .map_err(|()| resource())?
            .map_err(|_| BuildError::InvalidPayload)?,
        );
    }
    Ok(InterfaceApplication::new_kinded(
        value.interface(),
        arguments.into_boxed_slice(),
    ))
}

fn slice<T: Copy>(value: &[T], work: &mut TypeWorkBudget) -> Result<Box<[T]>, BuildError> {
    work.charge(value.len()).map_err(|()| resource())?;
    let mut copied = Vec::new();
    copied
        .try_reserve_exact(value.len())
        .map_err(|_| resource())?;
    copied.extend_from_slice(value);
    Ok(copied.into_boxed_slice())
}

struct TypeBuffer(Vec<Type>);

impl TypeBuffer {
    fn into_boxed_slice(mut self) -> Box<[Type]> {
        std::mem::take(&mut self.0).into_boxed_slice()
    }
}

impl Drop for TypeBuffer {
    fn drop(&mut self) {
        for value in self.0.drain(..) {
            discard_type_iteratively(value);
        }
    }
}

fn types(
    values: &[Type],
    identities: &FragmentIdentities,
    work: &mut TypeWorkBudget,
) -> Result<Box<[Type]>, BuildError> {
    work.charge(values.len()).map_err(|()| resource())?;
    let mut copied = TypeBuffer(Vec::new());
    copied
        .0
        .try_reserve_exact(values.len())
        .map_err(|_| resource())?;
    for value in values {
        copied.0.push(ty(value, identities, work)?);
    }
    Ok(copied.into_boxed_slice())
}

struct AdapterEdges(Vec<MethodEvidenceAdapterEdge>);

impl AdapterEdges {
    fn into_boxed_slice(mut self) -> Box<[MethodEvidenceAdapterEdge]> {
        std::mem::take(&mut self.0).into_boxed_slice()
    }
}

impl Drop for AdapterEdges {
    fn drop(&mut self) {
        for mut edge in self.0.drain(..) {
            discard_type_iteratively(std::mem::replace(&mut edge.value_type, Type::Unit));
        }
    }
}

fn expected_producer(
    value: MethodEvidenceExpectedProducer,
    expectation_offset: usize,
) -> Result<MethodEvidenceExpectedProducer, BuildError> {
    match value {
        MethodEvidenceExpectedProducer::Authenticated(index) => {
            Ok(MethodEvidenceExpectedProducer::Authenticated(
                index.checked_add(expectation_offset).ok_or_else(resource)?,
            ))
        }
        other => Ok(other),
    }
}

fn expected_role(
    role: MethodEvidenceExpectedRole,
    catalog: &MethodEvidenceCatalog,
    lexical_offset: usize,
    adapter_offset: usize,
    expectation_offset: usize,
    owner_positions: &HashMap<ImplMethodId, usize>,
    domain_positions: &HashMap<(MethodEvidenceOwner, RequirementId, MethodId), usize>,
) -> Result<MethodEvidenceExpectedRole, BuildError> {
    let lexical = |index: usize| {
        catalog
            .lexical_owners
            .get(index)
            .ok_or(BuildError::InvalidPayload)?;
        index.checked_add(lexical_offset).ok_or_else(resource)
    };
    let adapter = |index: usize| {
        catalog
            .adapters
            .get(index)
            .ok_or(BuildError::InvalidPayload)?;
        index.checked_add(adapter_offset).ok_or_else(resource)
    };
    let expectation = |index: usize| {
        catalog
            .expectations
            .get(index)
            .ok_or(BuildError::InvalidPayload)?;
        index.checked_add(expectation_offset).ok_or_else(resource)
    };
    let domain = |index: usize| {
        let value = catalog
            .domains
            .get(index)
            .ok_or(BuildError::InvalidPayload)?;
        domain_positions
            .get(&(value.owner, value.requirement, value.method))
            .copied()
            .ok_or(BuildError::InvalidPayload)
    };
    Ok(match role {
        MethodEvidenceExpectedRole::LexicalCaptureUse { owner, ordinal } => {
            MethodEvidenceExpectedRole::LexicalCaptureUse {
                owner: lexical(owner)?,
                ordinal,
            }
        }
        MethodEvidenceExpectedRole::LexicalOwner { owner } => {
            MethodEvidenceExpectedRole::LexicalOwner {
                owner: lexical(owner)?,
            }
        }
        MethodEvidenceExpectedRole::LexicalUse {
            owner,
            selection_node,
        } => MethodEvidenceExpectedRole::LexicalUse {
            owner: lexical(owner)?,
            selection_node,
        },
        MethodEvidenceExpectedRole::ImplementationOwner { owner } => {
            let value = catalog
                .implementation_owners
                .get(owner)
                .ok_or(BuildError::InvalidPayload)?;
            MethodEvidenceExpectedRole::ImplementationOwner {
                owner: *owner_positions
                    .get(&value.implementation)
                    .ok_or(BuildError::InvalidPayload)?,
            }
        }
        MethodEvidenceExpectedRole::Domain { domain: index } => {
            MethodEvidenceExpectedRole::Domain {
                domain: domain(index)?,
            }
        }
        MethodEvidenceExpectedRole::Application {
            domain: index,
            producer,
        } => MethodEvidenceExpectedRole::Application {
            domain: domain(index)?,
            producer: expectation(producer)?,
        },
        MethodEvidenceExpectedRole::Instantiation { producer } => {
            MethodEvidenceExpectedRole::Instantiation {
                producer: expectation(producer)?,
            }
        }
        MethodEvidenceExpectedRole::Adapter { adapter: index } => {
            MethodEvidenceExpectedRole::Adapter {
                adapter: adapter(index)?,
            }
        }
        MethodEvidenceExpectedRole::AdapterEdge {
            adapter: index,
            ordinal,
        } => MethodEvidenceExpectedRole::AdapterEdge {
            adapter: adapter(index)?,
            ordinal,
        },
    })
}

fn acquisition(
    mut value: crate::resolved::ResourceAcquisition,
    identities: &FragmentIdentities,
) -> Result<crate::resolved::ResourceAcquisition, BuildError> {
    value.identity = variable(value.identity, identities)?;
    value.handle = binder(value.handle, identities)?;
    let crate::resolved::ResourceMethods::Cell([first, second]) = value.methods;
    value.methods = crate::resolved::ResourceMethods::Cell([
        binder(first, identities)?,
        binder(second, identities)?,
    ]);
    Ok(value)
}

pub(crate) fn relocate_completed_anchor(
    anchor: &MethodEvidenceAnchor,
    identities: &FragmentIdentities,
    offsets: CompletedCatalogOffsets,
    mut node: impl FnMut(NodeId) -> Result<NodeId, BuildError>,
    work: &mut TypeWorkBudget,
) -> Result<MethodEvidenceAnchor, BuildError> {
    work.charge(1).map_err(|()| resource())?;
    let role = match anchor.role {
        MethodEvidenceAnchorRole::LexicalCaptureUse { owner, ordinal } => {
            MethodEvidenceAnchorRole::LexicalCaptureUse {
                owner: owner.checked_add(offsets.lexical).ok_or_else(resource)?,
                ordinal,
            }
        }
        MethodEvidenceAnchorRole::LexicalOwner {
            source,
            binder: value,
        } => MethodEvidenceAnchorRole::LexicalOwner {
            source,
            binder: binder(value, identities)?,
        },
        MethodEvidenceAnchorRole::LexicalUse {
            source,
            binder: value,
            selection_node,
        } => MethodEvidenceAnchorRole::LexicalUse {
            source,
            binder: binder(value, identities)?,
            selection_node,
        },
        MethodEvidenceAnchorRole::ImplementationOwner {
            implementation,
            binder: value,
        } => MethodEvidenceAnchorRole::ImplementationOwner {
            implementation,
            binder: binder(value, identities)?,
        },
        MethodEvidenceAnchorRole::Domain { binder: value } => MethodEvidenceAnchorRole::Domain {
            binder: binder(value, identities)?,
        },
        MethodEvidenceAnchorRole::Application { producer } => {
            MethodEvidenceAnchorRole::Application { producer }
        }
        MethodEvidenceAnchorRole::Instantiation { binder: value } => {
            MethodEvidenceAnchorRole::Instantiation {
                binder: value.map(|value| binder(value, identities)).transpose()?,
            }
        }
        MethodEvidenceAnchorRole::Adapter {
            implementation,
            selection_node,
        } => MethodEvidenceAnchorRole::Adapter {
            implementation,
            selection_node,
        },
        MethodEvidenceAnchorRole::AdapterEdge {
            adapter,
            adapter_selection_node,
            ordinal,
            producer_node,
            producer_selection_node,
            producer_binder,
            producer,
        } => MethodEvidenceAnchorRole::AdapterEdge {
            adapter,
            adapter_selection_node,
            ordinal,
            producer_node: node(producer_node)?,
            producer_selection_node,
            producer_binder: producer_binder
                .map(|value| binder(value, identities))
                .transpose()?,
            producer,
        },
    };
    Ok(MethodEvidenceAnchor {
        node: node(anchor.node)?,
        owner: anchor
            .owner
            .map(|value| owner(value, identities))
            .transpose()?,
        requirement: anchor.requirement,
        method: anchor.method,
        application: application(&anchor.application, identities, work)?,
        role,
        occurrence: anchor.occurrence,
        expectation: anchor
            .expectation
            .checked_add(offsets.expectations)
            .ok_or_else(resource)?,
    })
}

fn sort_occurrences(
    occurrences: Vec<MethodEvidenceOccurrence>,
    work: &mut TypeWorkBudget,
) -> Result<Vec<MethodEvidenceOccurrence>, BuildError> {
    let count = occurrences.len();
    work.charge(count.checked_mul(5).ok_or_else(resource)?)
        .map_err(|()| resource())?;
    let mut order = Vec::new();
    let mut scratch = Vec::new();
    order.try_reserve_exact(count).map_err(|_| resource())?;
    scratch.try_reserve_exact(count).map_err(|_| resource())?;
    order.extend(0..count);
    scratch.resize(count, 0);
    let mut width = 1usize;
    while width < count {
        let mut start = 0usize;
        while start < count {
            let middle = start.saturating_add(width).min(count);
            let end = middle.saturating_add(width).min(count);
            let (mut left, mut right) = (start, middle);
            for output in &mut scratch[start..end] {
                work.charge(1).map_err(|()| resource())?;
                if right == end
                    || (left < middle
                        && occurrences[order[left]].slot <= occurrences[order[right]].slot)
                {
                    *output = order[left];
                    left += 1;
                } else {
                    *output = order[right];
                    right += 1;
                }
            }
            start = end;
        }
        std::mem::swap(&mut order, &mut scratch);
        width = width.checked_mul(2).ok_or_else(resource)?;
    }
    let mut owned = Vec::new();
    owned.try_reserve_exact(count).map_err(|_| resource())?;
    owned.extend(occurrences.into_iter().map(Some));
    let mut result = Vec::new();
    result.try_reserve_exact(count).map_err(|_| resource())?;
    for index in order {
        let occurrence = owned[index].take().ok_or(BuildError::InvalidPayload)?;
        if result
            .last()
            .is_some_and(|previous: &MethodEvidenceOccurrence| previous.slot == occurrence.slot)
        {
            return Err(BuildError::InvalidPayload);
        }
        result.push(occurrence);
    }
    Ok(result)
}

/// Joins each defining catalogue exactly once after the destination's
/// fragment identities are known. Imported declaration rows are lookup
/// inputs of a producer, so only the defining module contributes them here.
pub(crate) fn compose_completed_catalogs(
    catalogs: Vec<(ModuleId, Arc<MethodEvidenceCatalog>)>,
    identities: &HashMap<ModuleId, FragmentIdentities>,
    work: &mut TypeWorkBudget,
) -> Result<
    (
        MethodEvidenceCatalog,
        HashMap<ModuleId, CompletedCatalogOffsets>,
    ),
    BuildError,
> {
    work.charge(catalogs.len().checked_mul(3).ok_or_else(resource)?)
        .map_err(|()| resource())?;
    let mut methods = Vec::new();
    let mut owners = Vec::new();
    let mut domains = Vec::new();
    for (module, catalog) in &catalogs {
        work.charge(catalog.lookup_work().ok_or_else(resource)?)
            .map_err(|()| resource())?;
        for method in catalog
            .methods
            .iter()
            .filter(|row| row.id.interface().module() == *module)
        {
            methods.try_reserve(1).map_err(|_| resource())?;
            let spelling = {
                work.charge(method.spelling.len())
                    .map_err(|()| resource())?;
                let mut spelling = String::new();
                spelling
                    .try_reserve_exact(method.spelling.len())
                    .map_err(|_| resource())?;
                spelling.push_str(&method.spelling);
                spelling.into_boxed_str()
            };
            methods.push(MethodEvidenceMethod {
                id: method.id,
                spelling,
                interface_parameters: slice(&method.interface_parameters, work)?,
                inherited_parameters: slice(&method.inherited_parameters, work)?,
                parameters: clone_kinded_type_parameters_with_budget(&method.parameters, work)
                    .map_err(|()| resource())?
                    .into_boxed_slice(),
                value_type: clone_type_with_budget(&method.value_type, work)
                    .map_err(|()| resource())?,
            });
        }
        for value in catalog
            .implementation_owners
            .iter()
            .filter(|row| row.implementation.implementation().module() == *module)
        {
            owners.try_reserve(1).map_err(|_| resource())?;
            owners.push(MethodEvidenceImplementationOwner {
                implementation: value.implementation,
                binder: value.binder,
                head_type_parameter_count: value.head_type_parameter_count,
                source_parameters: clone_kinded_type_parameters_with_budget(
                    &value.source_parameters,
                    work,
                )
                .map_err(|()| resource())?
                .into_boxed_slice(),
                application: value
                    .application
                    .clone_with_budget(work)
                    .map_err(|()| resource())?,
            });
        }
        for value in catalog
            .domains
            .iter()
            .filter(|row| owner_module(row.owner) == Some(*module))
        {
            domains.try_reserve(1).map_err(|_| resource())?;
            domains.push(MethodEvidenceDomain {
                source_parameters: clone_kinded_type_parameters_with_budget(
                    &value.source_parameters,
                    work,
                )
                .map_err(|()| resource())?
                .into_boxed_slice(),
                owner: value.owner,
                requirement: value.requirement,
                requirement_position: value.requirement_position,
                method: value.method,
                method_position: value.method_position,
                application: value
                    .application
                    .clone_with_budget(work)
                    .map_err(|()| resource())?,
            });
        }
    }
    for index in 1..methods.len() {
        let mut cursor = index;
        while cursor > 0 {
            work.charge(1).map_err(|()| resource())?;
            if methods[cursor - 1].id < methods[cursor].id {
                break;
            }
            if methods[cursor - 1].id == methods[cursor].id {
                return Err(BuildError::InvalidPayload);
            }
            methods.swap(cursor - 1, cursor);
            cursor -= 1;
        }
    }
    for index in 1..owners.len() {
        let mut cursor = index;
        while cursor > 0 {
            work.charge(1).map_err(|()| resource())?;
            if owners[cursor - 1].implementation < owners[cursor].implementation {
                break;
            }
            if owners[cursor - 1].implementation == owners[cursor].implementation {
                return Err(BuildError::InvalidPayload);
            }
            owners.swap(cursor - 1, cursor);
            cursor -= 1;
        }
    }
    work.charge(
        owners
            .len()
            .checked_add(domains.len())
            .and_then(|count| count.checked_mul(2))
            .ok_or_else(resource)?,
    )
    .map_err(|()| resource())?;
    let mut owner_positions = HashMap::new();
    owner_positions
        .try_reserve(owners.len())
        .map_err(|_| resource())?;
    for (index, row) in owners.iter().enumerate() {
        if owner_positions.insert(row.implementation, index).is_some() {
            return Err(BuildError::InvalidPayload);
        }
    }
    let mut domain_positions = HashMap::new();
    domain_positions
        .try_reserve(domains.len())
        .map_err(|_| resource())?;
    for (index, row) in domains.iter().enumerate() {
        if domain_positions
            .insert((row.owner, row.requirement, row.method), index)
            .is_some()
        {
            return Err(BuildError::InvalidPayload);
        }
    }

    let mut lexical_owners = Vec::new();
    let mut occurrences = Vec::new();
    let mut adapters = Vec::new();
    let mut concrete_sources = Vec::new();
    let mut expectations = Vec::new();
    let mut offsets = HashMap::new();
    offsets
        .try_reserve(catalogs.len())
        .map_err(|_| resource())?;
    let mut defining = Vec::new();
    defining
        .try_reserve_exact(catalogs.len())
        .map_err(|_| resource())?;
    for (module, catalog) in catalogs {
        let identities = identities.get(&module).ok_or(BuildError::InvalidPayload)?;
        work.charge(catalog.lookup_work().ok_or_else(resource)?)
            .map_err(|()| resource())?;
        lexical_owners
            .try_reserve(catalog.lexical_owners.len())
            .map_err(|_| resource())?;
        occurrences
            .try_reserve(catalog.occurrences.len())
            .map_err(|_| resource())?;
        adapters
            .try_reserve(catalog.adapters.len())
            .map_err(|_| resource())?;
        concrete_sources
            .try_reserve(catalog.concrete_sources.len())
            .map_err(|_| resource())?;
        expectations
            .try_reserve(catalog.expectations.len())
            .map_err(|_| resource())?;
        let lexical_offset = lexical_owners.len();
        let adapter_offset = adapters.len();
        let expectation_offset = expectations.len();
        if offsets
            .insert(
                module,
                CompletedCatalogOffsets {
                    lexical: lexical_offset,
                    expectations: expectation_offset,
                },
            )
            .is_some()
        {
            return Err(BuildError::InvalidPayload);
        }
        for value in &catalog.lexical_owners {
            work.charge(value.captures.len()).map_err(|()| resource())?;
            let mut captures = Vec::new();
            captures
                .try_reserve_exact(value.captures.len())
                .map_err(|_| resource())?;
            for capture in value.captures.iter() {
                captures.push(binder(*capture, identities)?);
            }
            let resource_owner = match &value.resource {
                Some(MethodEvidenceResourceOwner::Builtin(value)) => Some(
                    MethodEvidenceResourceOwner::Builtin(acquisition(*value, identities)?),
                ),
                None => None,
            };
            lexical_owners.push(MethodEvidenceLexicalOwner {
                resource: resource_owner,
                source_parameters: slice(&value.source_parameters, work)?,
                source: value.source,
                method: value.method,
                binder: binder(value.binder, identities)?,
                application: application(&value.application, identities, work)?,
                captures: captures.into_boxed_slice(),
            });
        }
        let mut plans = crate::interface::EvidencePlanRelocations::default();
        for value in &catalog.occurrences {
            occurrences.push(MethodEvidenceOccurrence {
                slot: value.slot,
                scope: value
                    .scope
                    .map(|value| owner(value, identities))
                    .transpose()?,
                scope_binder: value
                    .scope_binder
                    .map(|value| binder(value, identities))
                    .transpose()?,
                target_owner: value
                    .target_owner
                    .map(|value| owner(value, identities))
                    .transpose()?,
                target_requirement: value.target_requirement,
                checked_method: value.checked_method,
                checked_application: application(&value.checked_application, identities, work)?,
                method_arguments: types(&value.method_arguments, identities, work)?,
                checked_value_type: value
                    .checked_value_type
                    .as_ref()
                    .map(|value| ty(value, identities, work))
                    .transpose()?,
                selection: plans
                    .relocate(&value.selection, &identities.variables, work)
                    .map_err(|()| resource())?,
            });
        }
        for value in &catalog.adapters {
            work.charge(value.prerequisites.len())
                .map_err(|()| resource())?;
            let mut prerequisites = AdapterEdges(Vec::new());
            prerequisites
                .0
                .try_reserve_exact(value.prerequisites.len())
                .map_err(|_| resource())?;
            for edge in value.prerequisites.iter() {
                prerequisites.0.push(MethodEvidenceAdapterEdge {
                    owner: owner(edge.owner, identities)?,
                    requirement: edge.requirement,
                    method: edge.method,
                    application: application(&edge.application, identities, work)?,
                    interface_parameters: slice(&edge.interface_parameters, work)?,
                    method_parameters: clone_kinded_type_parameters_with_budget(
                        &edge.method_parameters,
                        work,
                    )
                    .map_err(|()| resource())?
                    .into_boxed_slice(),
                    value_type: ty(&edge.value_type, identities, work)?,
                    producer: expected_producer(edge.producer, expectation_offset)?,
                });
            }
            adapters.push(MethodEvidenceAdapter {
                selection_node: value.selection_node,
                implementation: value.implementation,
                binder: binder(value.binder, identities)?,
                source_parameters: slice(&value.source_parameters, work)?,
                head_arguments: types(&value.head_arguments, identities, work)?,
                prerequisites: prerequisites.into_boxed_slice(),
            });
        }
        for value in &catalog.concrete_sources {
            concrete_sources.push(MethodEvidenceConcreteSource {
                occurrence: value.occurrence,
                selection_node: value.selection_node,
                implementation: value.implementation,
                binder: binder(value.binder, identities)?,
                head_arguments: types(&value.head_arguments, identities, work)?,
                prerequisites: slice(&value.prerequisites, work)?,
            });
        }
        for value in &catalog.expectations {
            expectations.push(MethodEvidenceExpectation {
                occurrence: value.occurrence,
                method: value.method,
                role: expected_role(
                    value.role,
                    &catalog,
                    lexical_offset,
                    adapter_offset,
                    expectation_offset,
                    &owner_positions,
                    &domain_positions,
                )?,
            });
        }
        defining.push(catalog);
    }
    let occurrences = sort_occurrences(occurrences, work)?;
    let mut result = MethodEvidenceCatalog::new(
        methods,
        owners,
        domains,
        occurrences,
        adapters,
        concrete_sources,
        expectations,
    );
    result.set_lexical_owners(lexical_owners);
    result.retain_defining_catalogs(defining);
    Ok((result, offsets))
}
