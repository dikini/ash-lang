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

// Charge each comparison and move before inserting into already-reserved storage.
fn insert_row(
    rows: &mut Vec<OriginalOwnerRow>,
    row: OriginalOwnerRow,
    work: &mut TypeWorkBudget,
) -> Result<(), PreparationError> {
    let mut position = rows.len();
    for (index, previous) in rows.iter().enumerate() {
        charge(work, 1)?;
        if previous.owner == row.owner {
            return Err(PreparationError::Invalid);
        }
        if previous.owner > row.owner {
            position = index;
            break;
        }
    }
    charge(work, rows.len() - position)?;
    rows.insert(position, row);
    Ok(())
}

fn insert_slot(
    slots: &mut Vec<OriginalDeclaringSlot>,
    slot: OriginalDeclaringSlot,
    work: &mut TypeWorkBudget,
) -> Result<(), PreparationError> {
    let mut position = slots.len();
    for (index, previous) in slots.iter().enumerate() {
        charge(work, 1)?;
        if previous.parameter == slot.parameter {
            return Err(PreparationError::Invalid);
        }
        if previous.parameter > slot.parameter {
            position = index;
            break;
        }
    }
    charge(work, slots.len() - position)?;
    slots.insert(position, slot);
    Ok(())
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
                if interface.id.module() != module {
                    return Err(PreparationError::Invalid);
                }
                insert_row(
                    &mut rows,
                    row(
                        OriginalOwner::Interface(interface.id),
                        interface.parameters.iter().map(|parameter| parameter.id),
                        module,
                        source,
                        registry,
                        work,
                    )?,
                    work,
                )?;
                for method in &interface.methods {
                    if method.id.interface() != interface.id {
                        return Err(PreparationError::Invalid);
                    }
                    insert_row(
                        &mut rows,
                        row(
                            OriginalOwner::Method(method.id),
                            method
                                .authoritative_type_parameters()
                                .iter()
                                .map(|parameter| parameter.id),
                            module,
                            source,
                            registry,
                            work,
                        )?,
                        work,
                    )?;
                }
            }
            for scheme in group.schemes() {
                if scheme.binder.module() != Some(module) {
                    return Err(PreparationError::Invalid);
                }
                insert_row(
                    &mut rows,
                    row(
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
                    )?,
                    work,
                )?;
            }

            let mut slots = Vec::new();
            slots
                .try_reserve_exact(slot_count)
                .map_err(|_| PreparationError::Resource)?;
            for (row_index, owner) in rows.iter().enumerate() {
                for (slot_index, parameter) in owner.parameters.iter().enumerate() {
                    charge(work, 1)?;
                    insert_slot(
                        &mut slots,
                        OriginalDeclaringSlot {
                            parameter: parameter.parameter,
                            row: u32::try_from(row_index)
                                .map_err(|_| PreparationError::Resource)?,
                            slot: u32::try_from(slot_index)
                                .map_err(|_| PreparationError::Resource)?,
                        },
                        work,
                    )?;
                }
            }
            let mut position = modules.len();
            for (index, previous) in modules.iter().enumerate() {
                charge(work, 1)?;
                if previous.module == module {
                    return Err(PreparationError::Invalid);
                }
                if previous.module > module {
                    position = index;
                    break;
                }
            }
            charge(work, modules.len() - position)?;
            modules.insert(
                position,
                OriginalModuleOwners {
                    module,
                    source,
                    rows: rows.into_boxed_slice(),
                    slots: slots.into_boxed_slice(),
                },
            );
        }
        Ok(Self {
            modules: modules.into_boxed_slice(),
        })
    }

    pub(crate) fn modules(&self) -> &[OriginalModuleOwners] {
        &self.modules
    }
}
