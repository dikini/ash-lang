//! Exact passive selections from one independently restored registry. These
//! records describe visibility; they do not carry registry checking authority.

use super::{
    Arc, BinderId, CanonicalNominalKind, ConstructorId, EffectId, HashMap, InterfaceId, Kind,
    NominalTypeId, NonMaterializedNominalKind, NonMaterializedNominalKindFact, OperationId,
    OwnerId, ResolvedBuildFailure, ResolvedConstructor, ResolvedConstructorBuffer,
    ResolvedEffectBuffer, ResolvedGlobalParameterVecBuffer, ResolvedNominalBuffer,
    ResolvedNominalDeclarationKind, ResolvedNominalParameterVecBuffer, ResolvedNominalType,
    ResolvedRegistry, ResolvedTypeVariable, ResolvedTypeVariableBuffer,
    SourceForeignNominalCandidate, TypeVariableId, TypeWorkBudget, clone_arrows_with_budget,
    clone_constructor_ids_for_combined_registry, clone_effect_origin_with_budget,
    clone_kind_with_budget, clone_resolved_effect_with_budget,
    clone_resolved_type_variable_with_budget, clone_resolved_type_variables_with_budget,
    clone_type_with_budget, discard_resolved_type_variable, same_checker_type_variable_with_budget,
    same_kind_with_charge, same_origin_with_budget, same_resolved_type_provenance_with_budget,
    try_clone_string,
};

#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub(crate) enum ImageRegistryItem {
    Nominal(NominalTypeId),
    Constructor(ConstructorId),
    Effect(EffectId),
    Variable(TypeVariableId),
    Global(BinderId),
    Abstract(NominalTypeId),
    Interface(InterfaceId),
    Resource(crate::types::ResourceDefinitionId),
    Foreign(NominalTypeId),
    Native(OperationId),
    Preflight(BinderId),
}

fn paid<T>(result: Result<T, ()>) -> Result<T, ResolvedBuildFailure> {
    result.map_err(|()| ResolvedBuildFailure::TypeResource)
}
fn push<T>(
    values: &mut Vec<T>,
    value: T,
    work: &mut TypeWorkBudget,
) -> Result<(), ResolvedBuildFailure> {
    paid(work.charge(1))?;
    values
        .try_reserve(1)
        .map_err(|_| ResolvedBuildFailure::TypeResource)?;
    values.push(value);
    Ok(())
}

/// Fixed paid merge passes keep canonical ordering independent of hash order
/// without a quadratic comparison bill. Scratch storage contains identities only.
pub(crate) fn sort_image_registry_items(
    items: &mut [ImageRegistryItem],
    work: &mut TypeWorkBudget,
) -> Result<(), ()> {
    let count = items.len();
    work.charge(count)?;
    if count < 2 {
        return Ok(());
    }
    let mut scratch = Vec::new();
    scratch.try_reserve_exact(count).map_err(|_| ())?;
    scratch.resize(count, items[0]);
    let mut width = 1;
    while width < count {
        // At most count comparisons, count output writes and count copy-backs.
        work.charge(count.checked_mul(3).ok_or(())?)?;
        let mut start = 0;
        while start < count {
            let middle = start.saturating_add(width).min(count);
            let end = middle.saturating_add(width).min(count);
            let (mut left, mut right) = (start, middle);
            for output in &mut scratch[start..end] {
                if left < middle && (right == end || items[left] <= items[right]) {
                    *output = items[left];
                    left += 1;
                } else {
                    *output = items[right];
                    right += 1;
                }
            }
            start = end;
        }
        items.copy_from_slice(&scratch);
        width = width.checked_mul(2).unwrap_or(count);
    }
    Ok(())
}

struct InterfaceRows(Vec<(InterfaceId, Vec<ResolvedTypeVariable>)>);
impl InterfaceRows {
    fn into_vec(mut self) -> Vec<(InterfaceId, Vec<ResolvedTypeVariable>)> {
        std::mem::take(&mut self.0)
    }
}
impl Drop for InterfaceRows {
    fn drop(&mut self) {
        for (_, row) in self.0.drain(..) {
            for parameter in row {
                discard_resolved_type_variable(parameter);
            }
        }
    }
}

impl ResolvedRegistry {
    pub(crate) fn image_registry_abstract_names(
        &self,
        work: &mut TypeWorkBudget,
    ) -> Result<Vec<(NominalTypeId, &str)>, ResolvedBuildFailure> {
        let mut names = Vec::new();
        for (id, name) in &self.abstract_nominal_names {
            push(&mut names, (*id, name.as_str()), work)?;
        }
        Ok(names)
    }
    pub(crate) fn image_registry_items(
        &self,
        work: &mut TypeWorkBudget,
    ) -> Result<Vec<ImageRegistryItem>, ResolvedBuildFailure> {
        use ImageRegistryItem::*;
        if !self.lexical_nominals.is_empty()
            || !self.lexical_constructors.is_empty()
            || !self.provider_contracts.is_empty()
            || !self.foreign_modules.is_empty()
        {
            return Err(ResolvedBuildFailure::InvalidState);
        }
        let mut items = Vec::new();
        for value in &self.nominals {
            push(&mut items, Nominal(value.id), work)?;
        }
        for value in &self.constructors {
            push(&mut items, Constructor(value.id), work)?;
        }
        for value in &self.effects {
            push(&mut items, Effect(value.id), work)?;
        }
        for id in self.type_variables.keys() {
            push(&mut items, Variable(*id), work)?;
        }
        for row in &self.global_parameter_rows {
            push(&mut items, Global(row.owner), work)?;
        }
        for id in self.abstract_nominal_kinds.keys() {
            push(&mut items, Abstract(*id), work)?;
        }
        for definition in &self.owner_definitions {
            if let OwnerId::Interface(id) = definition.owner {
                push(&mut items, Interface(id), work)?;
            }
        }
        for id in self.source_resource_facts.keys() {
            push(&mut items, Resource(*id), work)?;
        }
        for value in &self.source_foreign_nominals {
            push(&mut items, Foreign(value.nominal), work)?;
        }
        for id in self.native_symbols.keys() {
            push(&mut items, Native(*id), work)?;
        }
        for id in self.scalar_preflights.keys() {
            push(&mut items, Preflight(*id), work)?;
        }
        paid(sort_image_registry_items(&mut items, work))?;
        if items.windows(2).any(|pair| pair[0] == pair[1]) {
            return Err(ResolvedBuildFailure::InvalidState);
        }
        Ok(items)
    }

    /// Selects exact canonical records, retaining original foreign allocations.
    /// Every reconstructed registry still returns through the ordinary validator.
    pub(crate) fn select_image_registry(
        &self,
        items: &[ImageRegistryItem],
        abstract_names: &[(NominalTypeId, &str)],
        work: &mut TypeWorkBudget,
    ) -> Result<Self, ResolvedBuildFailure> {
        use ImageRegistryItem::*;
        let invalid = || ResolvedBuildFailure::InvalidState;
        paid(work.charge(items.len()))?;
        if items.windows(2).any(|pair| pair[0] >= pair[1]) {
            return Err(invalid());
        }
        let mut nominals = ResolvedNominalBuffer(Vec::new());
        let mut constructors = ResolvedConstructorBuffer(Vec::new());
        let mut parameters = ResolvedNominalParameterVecBuffer(Vec::new());
        let mut effects = ResolvedEffectBuffer(Vec::new());
        let mut globals = ResolvedGlobalParameterVecBuffer(Vec::new());
        let mut variables = ResolvedTypeVariableBuffer(Vec::new());
        let mut interfaces = InterfaceRows(Vec::new());
        let mut resources = Vec::new();
        let mut names = HashMap::new();
        paid(work.charge(abstract_names.len()))?;
        names
            .try_reserve(abstract_names.len())
            .map_err(|_| ResolvedBuildFailure::TypeResource)?;
        for (id, name) in abstract_names {
            paid(work.charge(1))?;
            if names.insert(*id, *name).is_some() {
                return Err(invalid());
            }
        }
        for item in items {
            paid(work.charge(1))?;
            match *item {
                Nominal(id) => {
                    let value = self.nominal(id).ok_or_else(invalid)?;
                    if value.declaration_kind != ResolvedNominalDeclarationKind::Data
                        || value.representation.is_some()
                        || value.representation_provenance.is_some()
                    {
                        return Err(invalid());
                    }
                    paid(
                        work.charge(
                            value
                                .spelling
                                .len()
                                .checked_add(value.constructors.len())
                                .ok_or(ResolvedBuildFailure::TypeResource)?,
                        ),
                    )?;
                    paid(work.charge(1))?;
                    nominals
                        .0
                        .try_reserve(1)
                        .map_err(|_| ResolvedBuildFailure::TypeResource)?;
                    let spelling = try_clone_string(&value.spelling)?;
                    let constructors =
                        clone_constructor_ids_for_combined_registry(&value.constructors)?;
                    let origin = paid(clone_effect_origin_with_budget(&value.origin, work))?;
                    let value = ResolvedNominalType {
                        id,
                        declaration_kind: value.declaration_kind,
                        spelling,
                        constructors,
                        representation: None,
                        representation_provenance: None,
                        origin,
                    };
                    nominals.0.push(value);
                    let row = self.nominal_parameters(id).ok_or_else(invalid)?;
                    paid(work.charge(1))?;
                    parameters
                        .0
                        .try_reserve(1)
                        .map_err(|_| ResolvedBuildFailure::TypeResource)?;
                    let row = paid(clone_resolved_type_variables_with_budget(row, work))?;
                    parameters.0.push((id, row));
                }
                Constructor(id) => {
                    let value = self.constructor(id).ok_or_else(invalid)?;
                    paid(work.charge(value.spelling.len()))?;
                    paid(work.charge(1))?;
                    constructors
                        .0
                        .try_reserve(1)
                        .map_err(|_| ResolvedBuildFailure::TypeResource)?;
                    let spelling = try_clone_string(&value.spelling)?;
                    let origin = paid(clone_effect_origin_with_budget(&value.origin, work))?;
                    // Stage the origin before the fallible payload clone.
                    constructors.0.push(ResolvedConstructor {
                        id,
                        owner: value.owner,
                        spelling,
                        payload: None,
                        origin,
                    });
                    constructors.0.last_mut().ok_or_else(invalid)?.payload = value
                        .payload
                        .as_ref()
                        .map(|ty| paid(clone_type_with_budget(ty, work)))
                        .transpose()?;
                }
                Effect(id) => {
                    paid(work.charge(1))?;
                    effects
                        .0
                        .try_reserve(1)
                        .map_err(|_| ResolvedBuildFailure::TypeResource)?;
                    let value = paid(clone_resolved_effect_with_budget(
                        self.effect(id).ok_or_else(invalid)?,
                        work,
                    ))?;
                    effects.0.push(value);
                }
                Variable(id) => {
                    paid(work.charge(1))?;
                    variables
                        .0
                        .try_reserve(1)
                        .map_err(|_| ResolvedBuildFailure::TypeResource)?;
                    let value = paid(clone_resolved_type_variable_with_budget(
                        self.type_variable(id).ok_or_else(invalid)?,
                        work,
                    ))?;
                    variables.0.push(value);
                }
                Global(id) => {
                    paid(work.charge(1))?;
                    globals
                        .0
                        .try_reserve(1)
                        .map_err(|_| ResolvedBuildFailure::TypeResource)?;
                    let row = self.global_parameter_row(id).ok_or_else(invalid)?;
                    let mut cloned = ResolvedTypeVariableBuffer(Vec::new());
                    for id in row.parameters() {
                        paid(work.charge(1))?;
                        cloned
                            .0
                            .try_reserve(1)
                            .map_err(|_| ResolvedBuildFailure::TypeResource)?;
                        let value = paid(clone_resolved_type_variable_with_budget(
                            self.type_variable(*id).ok_or_else(invalid)?,
                            work,
                        ))?;
                        cloned.0.push(value);
                    }
                    globals.0.push((id, cloned.into_vec()));
                }
                Interface(id) => {
                    paid(work.charge(1))?;
                    interfaces
                        .0
                        .try_reserve(1)
                        .map_err(|_| ResolvedBuildFailure::TypeResource)?;
                    let value = self
                        .owner_definitions
                        .get(
                            *self
                                .owner_definition_positions
                                .get(&OwnerId::Interface(id))
                                .ok_or_else(invalid)?,
                        )
                        .ok_or_else(invalid)?;
                    let row = paid(clone_resolved_type_variables_with_budget(
                        &value.parameters,
                        work,
                    ))?;
                    interfaces.0.push((id, row));
                }
                Resource(id) => push(
                    &mut resources,
                    Arc::clone(self.source_resource_fact(id).ok_or_else(invalid)?),
                    work,
                )?,
                Abstract(_) | Foreign(_) | Native(_) | Preflight(_) => {}
            }
        }
        let selected = Self::new_with_budget(nominals.into_vec(), constructors.into_vec(), work)?;
        let mut selected =
            paid(selected.with_type_parameters_with_budget(parameters.into_vec(), work))?
                .with_effects_with_budget(effects.into_vec(), work)?
                .with_image_global_parameters(std::mem::take(&mut globals.0), work)?
                .with_image_source_parameters(variables.into_vec(), work)?
                .with_image_interface_owner_definitions(interfaces.into_vec(), work)?
                .with_image_source_resource_facts(resources, work)?;
        // The selected abstract category can differ from visible constructors;
        // never infer one category from a module's presence in the main view.
        selected.abstract_nominal_names.clear();
        selected.abstract_nominal_kinds.clear();
        for item in items {
            paid(work.charge(1))?;
            match *item {
                Abstract(id) => {
                    let name = names.remove(&id).ok_or_else(invalid)?;
                    paid(
                        work.charge(
                            name.len()
                                .checked_add(2)
                                .ok_or(ResolvedBuildFailure::TypeResource)?,
                        ),
                    )?;
                    // Opaque imports can hide a declaration which the combined
                    // main registry materializes. Select only its canonical
                    // kind and defining origin; never copy its constructors.
                    let (kind, origin) = match self.nominal_kind(id).ok_or_else(invalid)? {
                        CanonicalNominalKind::Parameters { parameters, origin } => (
                            NonMaterializedNominalKind::Ordinary(paid(clone_arrows_with_budget(
                                parameters.iter().map(|parameter| &parameter.kind),
                                Kind::Type,
                                work,
                            ))?),
                            origin,
                        ),
                        CanonicalNominalKind::Frozen { kind, origin } => (
                            NonMaterializedNominalKind::Ordinary(paid(clone_kind_with_budget(
                                kind, work,
                            ))?),
                            origin,
                        ),
                        CanonicalNominalKind::RowBearingResource { resource, origin } => (
                            NonMaterializedNominalKind::RowBearingResource(resource),
                            origin,
                        ),
                    };
                    selected
                        .abstract_nominal_names
                        .try_reserve(1)
                        .map_err(|_| ResolvedBuildFailure::TypeResource)?;
                    selected
                        .abstract_nominal_kinds
                        .try_reserve(1)
                        .map_err(|_| ResolvedBuildFailure::TypeResource)?;
                    selected
                        .abstract_nominal_names
                        .insert(id, try_clone_string(name)?);
                    selected
                        .abstract_nominal_kinds
                        .insert(id, NonMaterializedNominalKindFact { kind, origin });
                }
                Foreign(id) => {
                    paid(work.charge(self.source_foreign_nominals.len()))?;
                    let value = self
                        .source_foreign_nominals
                        .iter()
                        .find(|value| value.nominal == id)
                        .ok_or_else(invalid)?;
                    let value = SourceForeignNominalCandidate {
                        prepared: Arc::clone(&value.prepared),
                        role: value.role,
                        nominal: id,
                        parameters: value.parameters.clone_with_budget(work)?,
                        access: value.access.as_ref().map(Arc::clone),
                    };
                    push(&mut selected.source_foreign_nominals, value, work)?;
                }
                Native(id) => selected.retain_native_symbol(
                    Arc::clone(self.native_symbols.get(&id).ok_or_else(invalid)?),
                    work,
                )?,
                Preflight(id) => selected.retain_scalar_preflight(
                    Arc::clone(self.scalar_preflights.get(&id).ok_or_else(invalid)?),
                    work,
                )?,
                _ => {}
            }
        }
        if !names.is_empty() {
            return Err(invalid());
        }
        // Declaration attachment may not silently add unselected facts.
        let retained_items = selected.image_registry_items(work)?;
        paid(work.charge(items.len()))?;
        if retained_items != items {
            return Err(invalid());
        }
        Ok(selected)
    }

    /// Encoder-side exact correspondence, before any graph admission. Missing
    /// or differently exposed facts are an unsupported representation, never
    /// permission to widen the original checker view.
    #[cfg(test)]
    pub(crate) fn same_image_registry(
        &self,
        other: &Self,
        work: &mut TypeWorkBudget,
    ) -> Result<bool, ResolvedBuildFailure> {
        let items = self.image_registry_items(work)?;
        let other_items = other.image_registry_items(work)?;
        paid(work.charge(items.len()))?;
        if items != other_items {
            return Ok(false);
        }
        for item in &items {
            if let ImageRegistryItem::Abstract(id) = item {
                let name = self
                    .abstract_nominal_names
                    .get(id)
                    .ok_or(ResolvedBuildFailure::InvalidState)?;
                paid(work.charge(name.len()))?;
                if other.abstract_nominal_names.get(id) != Some(name) {
                    return Ok(false);
                }
            }
        }
        self.same_selected_image_facts(other, &items, work)
    }

    /// The source template already owns its independently checked view. The
    /// encoder compares every selected canonical fact directly instead of
    /// allocating another registry merely to compare and discard it. Opaque
    /// exposure names come from that original view and are encoded separately.
    pub(crate) fn matches_image_registry_projection(
        &self,
        canonical: &Self,
        work: &mut TypeWorkBudget,
    ) -> Result<bool, ResolvedBuildFailure> {
        let items = self.image_registry_items(work)?;
        self.same_selected_image_facts(canonical, &items, work)
    }

    fn same_selected_image_facts(
        &self,
        other: &Self,
        items: &[ImageRegistryItem],
        work: &mut TypeWorkBudget,
    ) -> Result<bool, ResolvedBuildFailure> {
        use ImageRegistryItem::*;
        let same_parameters = |a: &[ResolvedTypeVariable],
                               b: &[ResolvedTypeVariable],
                               work: &mut TypeWorkBudget|
         -> Result<bool, ResolvedBuildFailure> {
            paid(work.charge(1))?;
            if a.len() != b.len() {
                return Ok(false);
            }
            for (a, b) in a.iter().zip(b) {
                if !paid(same_checker_type_variable_with_budget(a, b, work))? {
                    return Ok(false);
                }
            }
            Ok(true)
        };
        for item in items.iter().copied() {
            paid(work.charge(1))?;
            let equal = match item {
                Nominal(id) => {
                    let a = self.nominal(id).ok_or(ResolvedBuildFailure::InvalidState)?;
                    let b = other
                        .nominal(id)
                        .ok_or(ResolvedBuildFailure::InvalidState)?;
                    paid(
                        work.charge(
                            a.spelling
                                .len()
                                .checked_add(a.constructors.len())
                                .ok_or(ResolvedBuildFailure::TypeResource)?,
                        ),
                    )?;
                    a.id == b.id
                        && a.declaration_kind == b.declaration_kind
                        && a.spelling == b.spelling
                        && a.constructors == b.constructors
                        && a.representation.is_none()
                        && b.representation.is_none()
                        && a.representation_provenance.is_none()
                        && b.representation_provenance.is_none()
                        && paid(same_origin_with_budget(&a.origin, &b.origin, work))?
                        && same_parameters(
                            self.nominal_parameters(id)
                                .ok_or(ResolvedBuildFailure::InvalidState)?,
                            other
                                .nominal_parameters(id)
                                .ok_or(ResolvedBuildFailure::InvalidState)?,
                            work,
                        )?
                }
                Constructor(id) => {
                    let a = self
                        .constructor(id)
                        .ok_or(ResolvedBuildFailure::InvalidState)?;
                    let b = other
                        .constructor(id)
                        .ok_or(ResolvedBuildFailure::InvalidState)?;
                    paid(work.charge(a.spelling.len()))?;
                    a.id == b.id
                        && a.owner == b.owner
                        && a.spelling == b.spelling
                        && paid(same_origin_with_budget(&a.origin, &b.origin, work))?
                        && match (&a.payload, &b.payload) {
                            (None, None) => true,
                            (Some(a), Some(b)) => {
                                paid(crate::types::same_type_with_budget(a, b, work))?
                            }
                            _ => false,
                        }
                }
                Effect(id) => {
                    let a = self.effect(id).ok_or(ResolvedBuildFailure::InvalidState)?;
                    let b = other.effect(id).ok_or(ResolvedBuildFailure::InvalidState)?;
                    paid(
                        work.charge(
                            a.spelling
                                .len()
                                .checked_add(a.operations.len())
                                .ok_or(ResolvedBuildFailure::TypeResource)?,
                        ),
                    )?;
                    let mut same = a.id == b.id
                        && a.public == b.public
                        && a.spelling == b.spelling
                        && a.span == b.span
                        && a.operations.len() == b.operations.len()
                        && match (&a.native_contract, &b.native_contract) {
                            (None, None) => true,
                            (Some(a), Some(b)) => Arc::ptr_eq(a, b),
                            _ => false,
                        }
                        && same_parameters(&a.parameters, &b.parameters, work)?
                        && paid(same_origin_with_budget(&a.origin, &b.origin, work))?;
                    for (a, b) in a.operations.iter().zip(&b.operations) {
                        paid(work.charge(a.spelling.len()))?;
                        same &= a.id == b.id
                            && a.spelling == b.spelling
                            && a.span == b.span
                            && a.annotation.span == b.annotation.span
                            && paid(crate::types::same_type_with_budget(
                                &a.annotation.ty,
                                &b.annotation.ty,
                                work,
                            ))?
                            && paid(same_resolved_type_provenance_with_budget(
                                &a.annotation.provenance,
                                &b.annotation.provenance,
                                work,
                            ))?
                            && paid(same_origin_with_budget(&a.origin, &b.origin, work))?
                            && paid(same_origin_with_budget(
                                &a.annotation.origin,
                                &b.annotation.origin,
                                work,
                            ))?;
                    }
                    same
                }
                Variable(id) => paid(same_checker_type_variable_with_budget(
                    self.type_variable(id)
                        .ok_or(ResolvedBuildFailure::InvalidState)?,
                    other
                        .type_variable(id)
                        .ok_or(ResolvedBuildFailure::InvalidState)?,
                    work,
                ))?,
                Global(id) => {
                    let a = self
                        .global_parameter_row(id)
                        .ok_or(ResolvedBuildFailure::InvalidState)?;
                    let b = other
                        .global_parameter_row(id)
                        .ok_or(ResolvedBuildFailure::InvalidState)?;
                    paid(work.charge(a.parameters().len()))?;
                    a.parameters() == b.parameters()
                }
                Abstract(id) => {
                    let a = self
                        .abstract_nominal_kinds
                        .get(&id)
                        .ok_or(ResolvedBuildFailure::InvalidState)?;
                    match other
                        .nominal_kind(id)
                        .ok_or(ResolvedBuildFailure::InvalidState)?
                    {
                        CanonicalNominalKind::Parameters { parameters, origin } => {
                            if a.origin != origin {
                                false
                            } else if let NonMaterializedNominalKind::Ordinary(kind) = &a.kind {
                                let mut rest = kind;
                                let mut equal = true;
                                for parameter in parameters {
                                    paid(work.charge(1))?;
                                    let Kind::Arrow(domain, codomain) = rest else {
                                        equal = false;
                                        break;
                                    };
                                    if !paid(same_kind_with_charge(
                                        domain,
                                        &parameter.kind,
                                        || work.charge(1),
                                    ))? {
                                        equal = false;
                                        break;
                                    }
                                    rest = codomain;
                                }
                                paid(work.charge(1))?;
                                equal && matches!(rest, Kind::Type)
                            } else {
                                false
                            }
                        }
                        CanonicalNominalKind::Frozen { kind, origin } => {
                            a.origin == origin
                                && match &a.kind {
                                    NonMaterializedNominalKind::Ordinary(original) => {
                                        paid(same_kind_with_charge(original, kind, || {
                                            work.charge(1)
                                        }))?
                                    }
                                    _ => false,
                                }
                        }
                        CanonicalNominalKind::RowBearingResource { resource, origin } => {
                            a.origin == origin
                                && matches!(a.kind, NonMaterializedNominalKind::RowBearingResource(original) if original==resource)
                        }
                    }
                }
                Interface(id) => {
                    let a = self
                        .owner_definitions
                        .get(
                            *self
                                .owner_definition_positions
                                .get(&OwnerId::Interface(id))
                                .ok_or(ResolvedBuildFailure::InvalidState)?,
                        )
                        .ok_or(ResolvedBuildFailure::InvalidState)?;
                    let b = other
                        .owner_definitions
                        .get(
                            *other
                                .owner_definition_positions
                                .get(&OwnerId::Interface(id))
                                .ok_or(ResolvedBuildFailure::InvalidState)?,
                        )
                        .ok_or(ResolvedBuildFailure::InvalidState)?;
                    a.family == b.family && same_parameters(&a.parameters, &b.parameters, work)?
                }
                Resource(id) => Arc::ptr_eq(
                    self.source_resource_fact(id)
                        .ok_or(ResolvedBuildFailure::InvalidState)?,
                    other
                        .source_resource_fact(id)
                        .ok_or(ResolvedBuildFailure::InvalidState)?,
                ),
                Foreign(id) => {
                    paid(
                        work.charge(
                            self.source_foreign_nominals
                                .len()
                                .checked_add(other.source_foreign_nominals.len())
                                .ok_or(ResolvedBuildFailure::TypeResource)?,
                        ),
                    )?;
                    let a = self
                        .source_foreign_nominals
                        .iter()
                        .find(|value| value.nominal == id)
                        .ok_or(ResolvedBuildFailure::InvalidState)?;
                    let b = other
                        .source_foreign_nominals
                        .iter()
                        .find(|value| value.nominal == id)
                        .ok_or(ResolvedBuildFailure::InvalidState)?;
                    Arc::ptr_eq(&a.prepared, &b.prepared)
                        && a.role == b.role
                        && same_parameters(&a.parameters, &b.parameters, work)?
                        && match (&a.access, &b.access) {
                            (None, None) => true,
                            (Some(a), Some(b)) => Arc::ptr_eq(a, b),
                            _ => false,
                        }
                }
                Native(id) => Arc::ptr_eq(
                    self.native_symbols
                        .get(&id)
                        .ok_or(ResolvedBuildFailure::InvalidState)?,
                    other
                        .native_symbols
                        .get(&id)
                        .ok_or(ResolvedBuildFailure::InvalidState)?,
                ),
                Preflight(id) => Arc::ptr_eq(
                    self.scalar_preflights
                        .get(&id)
                        .ok_or(ResolvedBuildFailure::InvalidState)?,
                    other
                        .scalar_preflights
                        .get(&id)
                        .ok_or(ResolvedBuildFailure::InvalidState)?,
                ),
            };
            if !equal {
                return Ok(false);
            }
        }
        Ok(true)
    }
}
