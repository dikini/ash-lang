//! Bounded comparison of contextual provider registry metadata.

use super::*;

fn charge_provenance(
    provenance: &ResolvedTypeProvenance,
    work: &mut TypeWorkBudget,
) -> Result<(), ()> {
    work.charge(provenance.nodes.len())?;
    for node in provenance.nodes.iter() {
        match node {
            ResolvedTypeProvenanceNode::Tuple { elements, .. } => work.charge(elements.len())?,
            ResolvedTypeProvenanceNode::Resource { arguments, .. } => {
                work.charge(arguments.len())?
            }
            ResolvedTypeProvenanceNode::Row { argument_roots, .. } => {
                work.charge(argument_roots.len())?
            }
            ResolvedTypeProvenanceNode::Function {
                effect_arguments, ..
            } => work.charge(effect_arguments.len())?,
            _ => {}
        }
    }
    Ok(())
}

fn same_optional_type(
    left: Option<&Type>,
    right: Option<&Type>,
    work: &mut TypeWorkBudget,
) -> Result<bool, ()> {
    match (left, right) {
        (None, None) => Ok(true),
        (Some(left), Some(right)) => crate::types::same_type_with_budget(left, right, work),
        _ => Ok(false),
    }
}

fn same_nominal(
    left: &ResolvedNominalType,
    right: &ResolvedNominalType,
    work: &mut TypeWorkBudget,
) -> Result<bool, ()> {
    work.charge(1usize.checked_add(left.constructors.len()).ok_or(())?)?;
    if left.id != right.id
        || left.declaration_kind != right.declaration_kind
        || left.spelling != right.spelling
        || left.constructors != right.constructors
        || !same_origin_with_budget(&left.origin, &right.origin, work)?
        || !same_optional_type(
            left.representation.as_ref(),
            right.representation.as_ref(),
            work,
        )?
    {
        return Ok(false);
    }
    match (
        &left.representation_provenance,
        &right.representation_provenance,
    ) {
        (None, None) => Ok(true),
        (Some(left), Some(right)) => {
            for provenance in [left, right] {
                charge_provenance(provenance, work)?;
            }
            Ok(left == right)
        }
        _ => Ok(false),
    }
}

impl ResolvedRegistry {
    #[cfg(test)]
    pub(crate) fn mutate_provider_effect_identity_for_test(&mut self, module: ModuleId) {
        let position = self
            .effects
            .iter()
            .position(|effect| effect.id.module() == module)
            .unwrap();
        let effect = &mut self.effects[position];
        let old = effect.id;
        let replacement = EffectId::new(module, u32::MAX);
        effect.id = replacement;
        for operation in &mut effect.operations {
            operation.id = OperationId::new(replacement, operation.id.operation());
        }
        self.effect_positions.remove(&old);
        self.effect_positions.insert(replacement, position);
    }

    #[cfg(test)]
    pub(crate) fn mutate_provider_annotation_origin_for_test(&mut self, origin: Origin) {
        self.effects[0].operations[0].annotation.origin = origin;
    }

    #[cfg(test)]
    pub(crate) fn mutate_provider_state_kind_for_test(&mut self, remove: bool) {
        let id = self
            .foreign_modules
            .values()
            .flat_map(|fact| &fact.states)
            .map(|state| state.id)
            .find(|id| self.abstract_nominal_kinds.contains_key(id))
            .unwrap();
        if remove {
            self.abstract_nominal_kinds.remove(&id);
        } else {
            self.abstract_nominal_kinds.get_mut(&id).unwrap().kind =
                NonMaterializedNominalKind::Ordinary(Kind::Type);
        }
    }

    #[cfg(test)]
    pub(crate) fn remove_provider_admission_for_test(&mut self) {
        self.foreign_modules.clear();
    }

    /// Retains canonical imported effect binders for contextual Core checking.
    /// Ordinary module checker views need only their effect declaration rows;
    /// Core kind validation additionally resolves each defining binder by ID.
    pub(crate) fn provider_template_view(
        &self,
        imported: &ImportedFacts,
        work: &mut TypeWorkBudget,
    ) -> Result<Self, ResolvedBuildFailure> {
        let mut registry = self.checker_view(imported, work)?;
        let mut parameters = ResolvedTypeVariableBuffer(Vec::new());
        let mut pending_ids = HashSet::new();
        for effect in registry.effects() {
            work.charge(effect.parameters.len())
                .map_err(|()| ResolvedBuildFailure::TypeResource)?;
            for parameter in &effect.parameters {
                if let Some(existing) = registry.type_variable(parameter.id) {
                    if !same_checker_type_variable_with_budget(existing, parameter, work)
                        .map_err(|()| ResolvedBuildFailure::TypeResource)?
                    {
                        return Err(ResolvedBuildFailure::InvalidState);
                    }
                } else {
                    pending_ids
                        .try_reserve(1)
                        .map_err(|_| ResolvedBuildFailure::TypeResource)?;
                    if !pending_ids.insert(parameter.id) {
                        return Err(ResolvedBuildFailure::InvalidState);
                    }
                    parameters
                        .0
                        .try_reserve(1)
                        .map_err(|_| ResolvedBuildFailure::TypeResource)?;
                    parameters.0.push(
                        clone_resolved_type_variable_with_budget(parameter, work)
                            .map_err(|()| ResolvedBuildFailure::TypeResource)?,
                    );
                }
            }
        }
        registry
            .type_variables
            .try_reserve(parameters.0.len())
            .map_err(|_| ResolvedBuildFailure::TypeResource)?;
        for parameter in parameters.into_vec() {
            // Every absent identity was checked for uniqueness before moving
            // recursive origins out of the iterative-drop buffer.
            registry
                .type_variables
                .insert(parameter.id, parameter.into());
        }
        Ok(registry)
    }

    /// Compares a draft's metadata with independently retained canonical facts.
    /// Equality is iterative for recursive type, kind and provenance payloads.
    /// This comparison grants no native phase or template-publication authority.
    pub(crate) fn same_provider_metadata(
        &self,
        canonical: &Self,
        work: &mut TypeWorkBudget,
    ) -> Result<bool, ()> {
        self.same_provider_metadata_with_native_memo(
            canonical,
            &mut crate::foreign::NativeAuthenticationMemo::default(),
            work,
        )
    }

    /// Reuses only native self-proof within the caller's exact admission.
    /// Actual registry metadata and its canonical correspondence are always checked.
    pub(crate) fn same_provider_metadata_with_native_memo(
        &self,
        canonical: &Self,
        native_authentication: &mut crate::foreign::NativeAuthenticationMemo,
        work: &mut TypeWorkBudget,
    ) -> Result<bool, ()> {
        let widths = [
            self.nominals.len(),
            self.constructors.len(),
            self.lexical_nominals.len(),
            self.lexical_constructors.len(),
            self.effects.len(),
            self.owner_definitions.len(),
            self.owner_definition_positions.len(),
            self.owner_signatures.effects.len(),
            self.owner_signatures.interfaces.len(),
            self.owner_signatures.resources.len(),
            self.nominal_parameters.len(),
            self.type_variables.len(),
            self.global_parameter_rows.len(),
            self.abstract_nominal_kinds.len(),
            self.foreign_modules.len(),
        ];
        let expected = [
            canonical.nominals.len(),
            canonical.constructors.len(),
            canonical.lexical_nominals.len(),
            canonical.lexical_constructors.len(),
            canonical.effects.len(),
            canonical.owner_definitions.len(),
            canonical.owner_definition_positions.len(),
            canonical.owner_signatures.effects.len(),
            canonical.owner_signatures.interfaces.len(),
            canonical.owner_signatures.resources.len(),
            canonical.nominal_parameters.len(),
            canonical.type_variables.len(),
            canonical.global_parameter_rows.len(),
            canonical.abstract_nominal_kinds.len(),
            canonical.foreign_modules.len(),
        ];
        work.charge(
            widths
                .iter()
                .try_fold(1usize, |sum, width| sum.checked_add(*width).ok_or(()))?,
        )?;
        if widths != expected
            || self.nominal_positions != canonical.nominal_positions
            || self.constructor_positions != canonical.constructor_positions
            || self.lexical_nominal_positions != canonical.lexical_nominal_positions
            || self.lexical_constructor_positions != canonical.lexical_constructor_positions
            || self.effect_positions != canonical.effect_positions
            || self.owner_definition_positions != canonical.owner_definition_positions
            || self.owner_signatures.effect_positions != canonical.owner_signatures.effect_positions
            || self.owner_signatures.interface_positions
                != canonical.owner_signatures.interface_positions
            || self.owner_signatures.resource_positions
                != canonical.owner_signatures.resource_positions
            || self.global_parameter_positions != canonical.global_parameter_positions
            || self.abstract_nominal_names != canonical.abstract_nominal_names
        {
            return Ok(false);
        }
        for (left, right) in self
            .owner_definitions
            .iter()
            .zip(&canonical.owner_definitions)
        {
            work.charge(left.parameters.len().checked_add(1).ok_or(())?)?;
            if left.owner != right.owner
                || left.family != right.family
                || left.parameters.len() != right.parameters.len()
            {
                return Ok(false);
            }
            for (left, right) in left.parameters.iter().zip(&right.parameters) {
                if !same_checker_type_variable_with_budget(left, right, work)? {
                    return Ok(false);
                }
            }
        }
        for (left, right) in self
            .owner_signatures
            .effects
            .iter()
            .chain(self.owner_signatures.interfaces.iter())
            .zip(
                canonical
                    .owner_signatures
                    .effects
                    .iter()
                    .chain(canonical.owner_signatures.interfaces.iter()),
            )
        {
            work.charge(left.parameters.len().checked_add(1).ok_or(())?)?;
            if left.owner != right.owner || left.parameters != right.parameters {
                return Ok(false);
            }
        }
        for ((left_family, left), (right_family, right)) in self
            .owner_signatures
            .resources
            .iter()
            .zip(canonical.owner_signatures.resources.iter())
        {
            work.charge(left.parameters.len().checked_add(1).ok_or(())?)?;
            if left_family != right_family
                || left.owner != right.owner
                || left.parameters != right.parameters
            {
                return Ok(false);
            }
        }
        for (left, right) in self
            .nominals
            .iter()
            .chain(&self.lexical_nominals)
            .zip(canonical.nominals.iter().chain(&canonical.lexical_nominals))
        {
            if !same_nominal(left, right, work)? {
                return Ok(false);
            }
        }
        for (left, right) in self
            .constructors
            .iter()
            .chain(&self.lexical_constructors)
            .zip(
                canonical
                    .constructors
                    .iter()
                    .chain(&canonical.lexical_constructors),
            )
        {
            work.charge(1)?;
            if left.id != right.id
                || left.owner != right.owner
                || left.spelling != right.spelling
                || !same_origin_with_budget(&left.origin, &right.origin, work)?
                || !same_optional_type(left.payload.as_ref(), right.payload.as_ref(), work)?
            {
                return Ok(false);
            }
        }
        for (owner, left) in &self.nominal_parameters {
            let Some(right) = canonical.nominal_parameters.get(owner) else {
                return Ok(false);
            };
            work.charge(left.len())?;
            if left.len() != right.len() {
                return Ok(false);
            }
            for (left, right) in left.iter().zip(right.iter()) {
                if !same_checker_type_variable_with_budget(left, right, work)? {
                    return Ok(false);
                }
            }
        }
        for (id, left) in &self.type_variables {
            let Some(right) = canonical.type_variables.get(id) else {
                return Ok(false);
            };
            if !same_checker_type_variable_with_budget(left, right, work)? {
                return Ok(false);
            }
        }
        for (id, left) in &self.abstract_nominal_kinds {
            let Some(right) = canonical.abstract_nominal_kinds.get(id) else {
                return Ok(false);
            };
            if left.origin != right.origin || !left.kind.same_with_budget(&right.kind, work)? {
                return Ok(false);
            }
        }
        for (left, right) in self
            .global_parameter_rows
            .iter()
            .zip(&canonical.global_parameter_rows)
        {
            work.charge(left.parameters().len())?;
            if left != right {
                return Ok(false);
            }
        }
        for (left, right) in self.effects.iter().zip(&canonical.effects) {
            work.charge(
                left.parameters
                    .len()
                    .checked_add(left.operations.len())
                    .ok_or(())?,
            )?;
            if left.id != right.id
                || left.public != right.public
                || left.spelling != right.spelling
                || left.span != right.span
                || left.parameters.len() != right.parameters.len()
                || left.operations.len() != right.operations.len()
                || !same_origin_with_budget(&left.origin, &right.origin, work)?
            {
                return Ok(false);
            }
            for (left, right) in left.parameters.iter().zip(&right.parameters) {
                if !same_checker_type_variable_with_budget(left, right, work)? {
                    return Ok(false);
                }
            }
            for (left, right) in left.operations.iter().zip(&right.operations) {
                if left.id != right.id
                    || left.spelling != right.spelling
                    || left.span != right.span
                    || left.annotation.span != right.annotation.span
                    || !same_origin_with_budget(&left.origin, &right.origin, work)?
                    || !same_origin_with_budget(
                        &left.annotation.origin,
                        &right.annotation.origin,
                        work,
                    )?
                    || !crate::types::same_type_with_budget(
                        &left.annotation.ty,
                        &right.annotation.ty,
                        work,
                    )?
                {
                    return Ok(false);
                }
                charge_provenance(&left.annotation.provenance, work)?;
                charge_provenance(&right.annotation.provenance, work)?;
                if left.annotation.provenance != right.annotation.provenance {
                    return Ok(false);
                }
            }
        }
        for (id, fact) in &self.foreign_modules {
            let Some(expected) = canonical.foreign_modules.get(id) else {
                return Ok(false);
            };
            for fact in [fact, expected] {
                match native_authentication.authenticate(fact, work) {
                    Ok(()) => {}
                    Err(error) if error.is_resource_exhaustion() => return Err(()),
                    Err(_) => return Ok(false),
                }
            }
            if fact != expected {
                return Ok(false);
            }
            for state in &fact.states {
                work.charge(1)?;
                let Some(actual) = self.nominal_kind(state.id) else {
                    continue;
                };
                let Some(parameters) = fact.canonical_registry().nominal_parameters(state.id)
                else {
                    return Ok(false);
                };
                let expected_kind = crate::types::clone_arrows_with_budget(
                    parameters.iter().map(|parameter| &parameter.kind),
                    Kind::Type,
                    work,
                )?;
                let actual_kind = match actual {
                    CanonicalNominalKind::RowBearingResource { .. } => return Ok(false),
                    CanonicalNominalKind::Frozen { kind, origin } => {
                        if origin != state.origin.primary_span() {
                            return Ok(false);
                        }
                        crate::types::clone_kind_with_budget(kind, work)?
                    }
                    CanonicalNominalKind::Parameters { parameters, origin } => {
                        if origin != state.origin.primary_span() {
                            return Ok(false);
                        }
                        crate::types::clone_arrows_with_budget(
                            parameters.iter().map(|parameter| &parameter.kind),
                            Kind::Type,
                            work,
                        )?
                    }
                };
                if !crate::types::same_kind_with_budget(&actual_kind, &expected_kind, work)? {
                    return Ok(false);
                }
            }
        }
        Ok(true)
    }
}
