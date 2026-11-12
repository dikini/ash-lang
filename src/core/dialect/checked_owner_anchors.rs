//! Original checked owner coordinates used by independent Core validation.

use crate::{
    evidence_validation::ValidatedInterfaceProgram,
    interface::{InterfaceId, MethodId},
    module::ModuleId,
    resolved::{BinderId, ResolvedRegistry},
    source::{Origin, SourceFile, SourceId, Span},
    types::{TypeVariableId, TypeWorkBudget},
};

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(crate) enum OriginalOwner {
    Interface(InterfaceId),
    Method(MethodId),
    Global(BinderId),
}

#[derive(Clone, Copy, Debug)]
pub(crate) struct OriginalParameter {
    pub(crate) parameter: TypeVariableId,
    pub(crate) expansion_primary: Option<Span>,
}

#[derive(Debug)]
pub(crate) struct OriginalOwnerRow {
    pub(crate) owner: OriginalOwner,
    pub(crate) parameters: Box<[OriginalParameter]>,
}

#[derive(Clone, Copy, Debug)]
pub(crate) struct OriginalDeclaringSlot {
    pub(crate) parameter: TypeVariableId,
    pub(crate) row: u32,
    pub(crate) slot: u32,
}

#[derive(Debug)]
pub(crate) struct OriginalModuleOwners {
    pub(crate) module: ModuleId,
    pub(crate) source: SourceId,
    pub(crate) rows: Box<[OriginalOwnerRow]>,
    pub(crate) slots: Box<[OriginalDeclaringSlot]>,
}

#[derive(Debug, Default)]
pub(crate) struct CheckedOwnerOrders {
    modules: Box<[OriginalModuleOwners]>,
}

#[derive(Clone, Copy, Debug)]
pub(crate) enum PreparationError {
    Invalid,
    Resource,
}

fn charge(work: &mut TypeWorkBudget, amount: usize) -> Result<(), PreparationError> {
    work.charge(amount).map_err(|()| PreparationError::Resource)
}

fn add(count: usize, amount: usize) -> Result<usize, PreparationError> {
    count.checked_add(amount).ok_or(PreparationError::Resource)
}

fn primary_span(origin: &Origin, work: &mut TypeWorkBudget) -> Result<Span, PreparationError> {
    let mut current = origin;
    loop {
        charge(work, 1)?;
        match current {
            Origin::Source(span) => return Ok(*span),
            Origin::Expansion { invocation, .. } => return Ok(*invocation),
            Origin::Generated { cause, .. } => current = cause,
            Origin::Related { primary, .. } => current = primary,
        }
    }
}

fn row(
    owner: OriginalOwner,
    ids: impl ExactSizeIterator<Item = TypeVariableId>,
    module: ModuleId,
    source: SourceId,
    registry: &ResolvedRegistry,
    work: &mut TypeWorkBudget,
) -> Result<OriginalOwnerRow, PreparationError> {
    charge(work, ids.len())?;
    let mut parameters = Vec::new();
    parameters
        .try_reserve_exact(ids.len())
        .map_err(|_| PreparationError::Resource)?;
    for id in ids {
        charge(work, 1)?;
        let canonical = registry
            .type_variable(id)
            .ok_or(PreparationError::Invalid)?;
        if id.module() != Some(module)
            || canonical.id != id
            || primary_span(&canonical.origin, work)?.source() != source
        {
            return Err(PreparationError::Invalid);
        }
        let expansion_primary = match &canonical.origin {
            Origin::Expansion { invocation, .. } => Some(*invocation),
            _ => None,
        };
        parameters.push(OriginalParameter {
            parameter: id,
            expansion_primary,
        });
    }
    Ok(OriginalOwnerRow {
        owner,
        parameters: parameters.into_boxed_slice(),
    })
}

// Sort a finite index with paid merge passes, then move the owned rows once.
fn sorted_unique<T, K: Copy + Ord>(
    items: Vec<T>,
    key: impl Fn(&T) -> K,
    work: &mut TypeWorkBudget,
) -> Result<Vec<T>, PreparationError> {
    let count = items.len();
    if count < 2 {
        charge(work, count)?;
        return Ok(items);
    }
    charge(
        work,
        count.checked_mul(4).ok_or(PreparationError::Resource)?,
    )?;
    let mut order = Vec::new();
    let mut scratch = Vec::new();
    order
        .try_reserve_exact(count)
        .map_err(|_| PreparationError::Resource)?;
    scratch
        .try_reserve_exact(count)
        .map_err(|_| PreparationError::Resource)?;
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
                charge(work, 1)?;
                if right == end
                    || (left < middle && key(&items[order[left]]) <= key(&items[order[right]]))
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
        width = width.checked_mul(2).ok_or(PreparationError::Resource)?;
    }
    let mut owned = Vec::new();
    let mut sorted = Vec::new();
    owned
        .try_reserve_exact(count)
        .map_err(|_| PreparationError::Resource)?;
    sorted
        .try_reserve_exact(count)
        .map_err(|_| PreparationError::Resource)?;
    owned.extend(items.into_iter().map(Some));
    let mut previous = None;
    for index in order {
        charge(work, 1)?;
        let item = owned[index].take().ok_or(PreparationError::Invalid)?;
        let current = key(&item);
        if previous == Some(current) {
            return Err(PreparationError::Invalid);
        }
        previous = Some(current);
        sorted.push(item);
    }
    Ok(sorted)
}

impl CheckedOwnerOrders {
    pub(super) fn prepare(
        linked: &ValidatedInterfaceProgram,
        sources: &[&SourceFile],
        module_sources: &[(ModuleId, SourceId)],
        work: &mut TypeWorkBudget,
    ) -> Result<Self, PreparationError> {
        charge(work, linked.groups().len())?;
        let mut modules: Vec<OriginalModuleOwners> = Vec::new();
        modules
            .try_reserve_exact(linked.groups().len())
            .map_err(|_| PreparationError::Resource)?;
        for group in linked.groups() {
            charge(work, 1)?;
            let module = group.module();
            if !module.is_admitted_source() {
                continue;
            }
            let source = group.span().source();
            let relation_probes = module_sources
                .len()
                .checked_mul(3)
                .ok_or(PreparationError::Resource)?;
            charge(work, add(sources.len(), relation_probes)?)?;
            if sources.iter().filter(|file| file.id() == source).count() != 1
                || module_sources
                    .iter()
                    .filter(|(candidate, mapped)| *candidate == module && *mapped == source)
                    .count()
                    != 1
                || module_sources
                    .iter()
                    .filter(|(candidate, _)| *candidate == module)
                    .count()
                    != 1
                || module_sources
                    .iter()
                    .filter(|(_, mapped)| *mapped == source)
                    .count()
                    != 1
            {
                return Err(PreparationError::Invalid);
            }

            let mut row_count = group.schemes().len();
            let mut slot_count = 0;
            charge(
                work,
                add(group.schemes().len(), group.interface_facts().len())?,
            )?;
            for scheme in group.schemes() {
                slot_count = add(slot_count, scheme.scheme.type_parameters.len())?;
            }
            for interface in group.interface_facts() {
                row_count = add(row_count, add(1, interface.methods.len())?)?;
                slot_count = add(slot_count, interface.parameters.len())?;
                charge(work, interface.methods.len())?;
                for method in &interface.methods {
                    slot_count = add(slot_count, method.authoritative_type_parameters().len())?;
                }
            }
            charge(work, add(row_count, slot_count)?)?;
            let mut rows = Vec::new();
            rows.try_reserve_exact(row_count)
                .map_err(|_| PreparationError::Resource)?;
            let registry = linked.registry();
            for interface in group.interface_facts() {
                charge(work, 1)?;
                if interface.id.module() != module {
                    return Err(PreparationError::Invalid);
                }
                rows.push(row(
                    OriginalOwner::Interface(interface.id),
                    interface.parameters.iter().map(|parameter| parameter.id),
                    module,
                    source,
                    registry,
                    work,
                )?);
                for method in &interface.methods {
                    charge(work, 1)?;
                    if method.id.interface() != interface.id {
                        return Err(PreparationError::Invalid);
                    }
                    rows.push(row(
                        OriginalOwner::Method(method.id),
                        method
                            .authoritative_type_parameters()
                            .iter()
                            .map(|parameter| parameter.id),
                        module,
                        source,
                        registry,
                        work,
                    )?);
                }
            }
            for scheme in group.schemes() {
                charge(work, 1)?;
                if scheme.binder.module() != Some(module) {
                    return Err(PreparationError::Invalid);
                }
                rows.push(row(
                    OriginalOwner::Global(scheme.binder),
                    scheme
                        .scheme
                        .type_parameters
                        .iter()
                        .map(|(parameter, _)| *parameter),
                    module,
                    source,
                    registry,
                    work,
                )?);
            }
            let rows = sorted_unique(rows, |entry| entry.owner, work)?;

            let mut slots = Vec::new();
            slots
                .try_reserve_exact(slot_count)
                .map_err(|_| PreparationError::Resource)?;
            for (row_index, owner) in rows.iter().enumerate() {
                for (slot_index, parameter) in owner.parameters.iter().enumerate() {
                    charge(work, 1)?;
                    slots.push(OriginalDeclaringSlot {
                        parameter: parameter.parameter,
                        row: u32::try_from(row_index).map_err(|_| PreparationError::Resource)?,
                        slot: u32::try_from(slot_index).map_err(|_| PreparationError::Resource)?,
                    });
                }
            }
            let slots = sorted_unique(slots, |entry| entry.parameter, work)?;
            modules.push(OriginalModuleOwners {
                module,
                source,
                rows: rows.into_boxed_slice(),
                slots: slots.into_boxed_slice(),
            });
        }
        let modules = sorted_unique(modules, |entry| entry.module, work)?;
        Ok(Self {
            modules: modules.into_boxed_slice(),
        })
    }

    pub(crate) fn modules(&self) -> &[OriginalModuleOwners] {
        &self.modules
    }
}
