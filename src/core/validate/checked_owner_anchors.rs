//! Authenticate active Core owners against the original checked coordinates.

use super::{CoreOperationFamily, ScopeFamily, ValidationError, ValidationReason, Validator};
use crate::{
    core::dialect::checked_owner_anchors::{
        CheckedOwnerOrders, OriginalModuleOwners, OriginalOwner, OriginalOwnerRow,
        OriginalParameter,
    },
    interface::MethodId,
    module::ModuleId,
    resolved::{OwnerId, ResolvedTypeVariable},
    source::{Origin, Span},
    types::TypeVariableId,
};

fn invalid() -> ValidationError {
    ValidationError::new(ValidationReason::Registry, None)
}

impl<'program, 'source, F: CoreOperationFamily + ScopeFamily> Validator<'program, 'source, F> {
    fn checked_originals(&self) -> &CheckedOwnerOrders {
        self.prepared_owner_anchors
            .unwrap_or(self.program.generated_parameter_anchors.as_ref())
            .checked_owners()
    }

    fn original_module(
        &self,
        id: ModuleId,
    ) -> Result<Option<&OriginalModuleOwners>, ValidationError> {
        let modules = self.checked_originals().modules();
        let (mut low, mut high) = (0, modules.len());
        while low < high {
            self.charge_type_work(1)?;
            let middle = low + (high - low) / 2;
            match modules[middle].module.cmp(&id) {
                std::cmp::Ordering::Less => low = middle + 1,
                std::cmp::Ordering::Greater => high = middle,
                std::cmp::Ordering::Equal => return Ok(Some(&modules[middle])),
            }
        }
        Ok(None)
    }

    fn original_row(
        &self,
        owner: OriginalOwner,
    ) -> Result<Option<&OriginalOwnerRow>, ValidationError> {
        let module = match owner {
            OriginalOwner::Interface(id) => Some(id.module()),
            OriginalOwner::Method(id) => Some(id.interface().module()),
            OriginalOwner::Global(id) => id.module(),
        };
        let Some(module) = module else {
            return Ok(None);
        };
        let Some(module) = self.original_module(module)? else {
            return Ok(None);
        };
        let (mut low, mut high) = (0, module.rows.len());
        while low < high {
            self.charge_type_work(1)?;
            let middle = low + (high - low) / 2;
            match module.rows[middle].owner.cmp(&owner) {
                std::cmp::Ordering::Less => low = middle + 1,
                std::cmp::Ordering::Greater => high = middle,
                std::cmp::Ordering::Equal => return Ok(Some(&module.rows[middle])),
            }
        }
        Ok(None)
    }

    fn same_original_parameters(
        &self,
        expected: &[OriginalParameter],
        actual: impl ExactSizeIterator<Item = TypeVariableId>,
    ) -> Result<bool, ValidationError> {
        self.charge_type_work(expected.len().saturating_add(1))?;
        Ok(expected.len() == actual.len()
            && expected
                .iter()
                .map(|parameter| parameter.parameter)
                .eq(actual))
    }

    fn active_method(
        &self,
        id: MethodId,
    ) -> Result<Option<&crate::core::dialect::MethodEvidenceMethod>, ValidationError> {
        let methods = self.program.method_evidence.methods();
        let (mut low, mut high) = (0, methods.len());
        while low < high {
            self.charge_type_work(1)?;
            let middle = low + (high - low) / 2;
            match methods[middle].id.cmp(&id) {
                std::cmp::Ordering::Less => low = middle + 1,
                std::cmp::Ordering::Greater => high = middle,
                std::cmp::Ordering::Equal => return Ok(Some(&methods[middle])),
            }
        }
        Ok(None)
    }

    pub(super) fn authenticate_checked_originals(&self) -> Result<(), ValidationError> {
        if self.checked_owner_anchors_authenticated.get() {
            return Ok(());
        }
        let registry = &self.program.registry;
        let catalog = &self.program.method_evidence;
        let modules = self.checked_originals().modules();
        if modules.is_empty() {
            return Err(invalid());
        }
        let mut previous_module = None;
        for module in modules {
            self.charge_type_work(1)?;
            if !module.module.is_admitted_source()
                || previous_module.is_some_and(|previous| previous >= module.module)
                || !self.sources.contains_key(&module.source)
                || self.module_sources.as_ref().is_some_and(|relation| {
                    relation.get(&module.module).copied() != Some(module.source)
                })
            {
                return Err(invalid());
            }
            previous_module = Some(module.module);
            let mut previous_owner = None;
            let mut count = 0usize;
            for row in &module.rows {
                self.charge_type_work(1)?;
                if previous_owner.is_some_and(|previous| previous >= row.owner) {
                    return Err(invalid());
                }
                previous_owner = Some(row.owner);
                count = count
                    .checked_add(row.parameters.len())
                    .ok_or_else(|| ValidationError::new(ValidationReason::Resource, None))?;
                for parameter in &row.parameters {
                    self.charge_type_work(1)?;
                    if parameter.parameter.module() != Some(module.module)
                        || parameter
                            .expansion_primary
                            .is_some_and(|span| span.source() != module.source)
                    {
                        return Err(invalid());
                    }
                }
                match row.owner {
                    OriginalOwner::Interface(interface) => {
                        let owner = OwnerId::Interface(interface);
                        let definition = registry
                            .defining_owner_parameters(owner)
                            .ok_or_else(invalid)?;
                        let signature = registry.owner_signature(owner).ok_or_else(invalid)?;
                        if interface.module() != module.module
                            || !self.same_original_parameters(
                                &row.parameters,
                                definition.iter().map(|parameter| parameter.id),
                            )?
                            || !self.same_original_parameters(
                                &row.parameters,
                                signature.parameters.iter().copied(),
                            )?
                        {
                            return Err(invalid());
                        }
                    }
                    OriginalOwner::Method(method) => {
                        let active = self.active_method(method)?.ok_or_else(invalid)?;
                        let interface = self
                            .original_row(OriginalOwner::Interface(method.interface()))?
                            .ok_or_else(invalid)?;
                        let owner = OwnerId::Interface(method.interface());
                        if method.interface().module() != module.module
                            || !self.same_original_parameters(
                                &row.parameters,
                                active.parameters.iter().map(|(id, _)| *id),
                            )?
                            || !self.same_original_parameters(
                                &interface.parameters,
                                active.interface_parameters.iter().copied(),
                            )?
                            || active.inherited_parameters.len() != interface.parameters.len()
                        {
                            return Err(invalid());
                        }
                        self.charge_type_work(active.inherited_parameters.len())?;
                        if active
                            .inherited_parameters
                            .iter()
                            .zip(&interface.parameters)
                            .enumerate()
                            .any(|(slot, (role, parameter))| {
                                role.owner != owner
                                    || usize::try_from(role.slot) != Ok(slot)
                                    || role.binder != parameter.parameter
                            })
                        {
                            return Err(invalid());
                        }
                    }
                    OriginalOwner::Global(binder) => {
                        let actual = registry.global_parameter_row(binder);
                        if binder.module() != Some(module.module)
                            || match actual {
                                Some(actual) => !self.same_original_parameters(
                                    &row.parameters,
                                    actual.parameters().iter().copied(),
                                )?,
                                None => !row.parameters.is_empty(),
                            }
                        {
                            return Err(invalid());
                        }
                    }
                }
            }
            if count != module.slots.len() {
                return Err(invalid());
            }
            let mut previous_slot = None;
            for slot in &module.slots {
                self.charge_type_work(1)?;
                let original = usize::try_from(slot.row)
                    .ok()
                    .and_then(|row| module.rows.get(row))
                    .and_then(|row| {
                        usize::try_from(slot.slot)
                            .ok()
                            .and_then(|index| row.parameters.get(index))
                    })
                    .ok_or_else(invalid)?;
                if previous_slot.is_some_and(|previous| previous >= slot.parameter)
                    || original.parameter != slot.parameter
                {
                    return Err(invalid());
                }
                previous_slot = Some(slot.parameter);
            }
        }

        // The reverse direction refuses active source owners absent from the originals.
        for (id, _) in registry.image_interface_owner_definitions() {
            self.charge_type_work(1)?;
            if id.module().is_admitted_source()
                && self.original_row(OriginalOwner::Interface(id))?.is_none()
            {
                return Err(invalid());
            }
        }
        for method in catalog.methods() {
            self.charge_type_work(1)?;
            if method.id.interface().module().is_admitted_source()
                && self
                    .original_row(OriginalOwner::Method(method.id))?
                    .is_none()
            {
                return Err(invalid());
            }
        }
        for row in registry.global_parameter_rows() {
            self.charge_type_work(1)?;
            if row
                .owner()
                .module()
                .is_some_and(ModuleId::is_admitted_source)
                && self
                    .original_row(OriginalOwner::Global(row.owner()))?
                    .is_none()
            {
                return Err(invalid());
            }
        }
        self.checked_owner_anchors_authenticated.set(true);
        Ok(())
    }

    fn original_slot_matches(
        &self,
        id: TypeVariableId,
        span: Span,
    ) -> Result<bool, ValidationError> {
        let Some(module) = id.module() else {
            return Ok(false);
        };
        let Some(module) = self.original_module(module)? else {
            return Ok(false);
        };
        let (mut low, mut high) = (0, module.slots.len());
        while low < high {
            self.charge_type_work(1)?;
            let middle = low + (high - low) / 2;
            let slot = &module.slots[middle];
            match slot.parameter.cmp(&id) {
                std::cmp::Ordering::Less => low = middle + 1,
                std::cmp::Ordering::Greater => high = middle,
                std::cmp::Ordering::Equal => {
                    let original = usize::try_from(slot.row)
                        .ok()
                        .and_then(|row| module.rows.get(row))
                        .and_then(|row| {
                            usize::try_from(slot.slot)
                                .ok()
                                .and_then(|index| row.parameters.get(index))
                        })
                        .ok_or_else(invalid)?;
                    return Ok(original.parameter == id && original.expansion_primary == Some(span));
                }
            }
        }
        Ok(false)
    }

    pub(super) fn allows_original_expansion_tie(
        &self,
        previous: &ResolvedTypeVariable,
        current: &ResolvedTypeVariable,
    ) -> Result<bool, ValidationError> {
        let (
            Origin::Expansion {
                invocation: previous_span,
                ..
            },
            Origin::Expansion {
                invocation: current_span,
                ..
            },
        ) = (&previous.origin, &current.origin)
        else {
            return Ok(false);
        };
        if previous_span != current_span || previous.id.module() != current.id.module() {
            return Ok(false);
        }
        if self.checked_originals().modules().is_empty() {
            return Ok(false);
        }
        self.authenticate_checked_originals()?;
        Ok(self.original_slot_matches(previous.id, *previous_span)?
            && self.original_slot_matches(current.id, *current_span)?)
    }
}
