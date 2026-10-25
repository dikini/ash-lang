//! Defining constructor meanings borrowed from an existing checked registry.
//!
//! This reference supplies no projected kind, source access or native authority.
//! Only completed local checking may create it; imports retain the same reference.

use super::{
    ResolvedBuildFailure, ResolvedNominalDeclarationKind, ResolvedRegistry, ResolvedTypeVariable,
    same_origin_with_constraint_budget,
    same_summary_resolved_type_variables_with_constraint_budget,
};
#[cfg(test)]
use crate::types::discard_type_iteratively;
use crate::{
    interface::same_type_with_constraint_budget,
    source::Origin,
    types::{ConstructorId, Type, TypeWorkBudget},
};
use std::{fmt, sync::Arc};

/// The existing defining registry, rather than a copied constructor fact.
pub(crate) struct ConstructorOriginal(Arc<ResolvedRegistry>);

impl PartialEq for ConstructorOriginal {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0)
    }
}

impl Eq for ConstructorOriginal {}

impl fmt::Debug for ConstructorOriginal {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        // Never recursively compare or print the complete defining registry.
        formatter
            .debug_struct("ConstructorOriginal")
            .finish_non_exhaustive()
    }
}

impl ConstructorOriginal {
    /// Caller is the completed local-check publication path, never an import.
    pub(super) fn from_checked(
        registry: &Arc<ResolvedRegistry>,
        work: &mut TypeWorkBudget,
    ) -> Result<Self, ResolvedBuildFailure> {
        work.charge(1)
            .map_err(|()| ResolvedBuildFailure::TypeResource)?;
        Ok(Self(Arc::clone(registry)))
    }

    /// Forward the original reference without replacing its defining registry.
    pub(crate) fn retain(&self, work: &mut TypeWorkBudget) -> Result<Self, ResolvedBuildFailure> {
        Self::from_checked(&self.0, work)
    }

    #[cfg(test)]
    pub(super) fn reminted_for_test(&self) -> Self {
        Self(Arc::new((*self.0).clone()))
    }

    #[cfg(test)]
    pub(super) fn stale_payload_for_test(&self, id: ConstructorId, payload: Type) -> Self {
        let mut registry = (*self.0).clone();
        let position = registry.constructor_positions[&id];
        if let Some(previous) = registry.constructors[position].payload.replace(payload) {
            discard_type_iteratively(previous);
        }
        Self(Arc::new(registry))
    }

    /// Compare just this constructor meaning and its ordered owner formals.
    /// Parent scheme, kind, publication and access checks remain independent.
    #[expect(
        clippy::too_many_arguments,
        reason = "compare one existing constructor against its defining registry without an auxiliary fact carrier"
    )]
    pub(super) fn authenticate(
        &self,
        id: ConstructorId,
        declaration_kind: ResolvedNominalDeclarationKind,
        spelling: &str,
        payload: Option<&Type>,
        origin: &Origin,
        parameters: &[ResolvedTypeVariable],
        work: &mut TypeWorkBudget,
        constraints: &mut crate::interface::InterfaceConstraintBudget,
    ) -> Result<(), ResolvedBuildFailure> {
        work.charge(4)
            .map_err(|()| ResolvedBuildFailure::TypeResource)?;
        let invalid = || ResolvedBuildFailure::InvalidState;
        let constructor = self.0.constructor(id).ok_or_else(invalid)?;
        let owner = self.0.nominal(id.owner()).ok_or_else(invalid)?;
        let original_parameters = self.0.nominal_parameters(owner.id).ok_or_else(invalid)?;
        let ordinal = usize::try_from(id.constructor()).map_err(|_| invalid())?;
        if constructor.id != id
            || constructor.owner != id.owner()
            || owner.id != id.owner()
            || owner.declaration_kind != declaration_kind
            || owner.constructors.get(ordinal) != Some(&id)
        {
            return Err(invalid());
        }
        let spelling_work = spelling
            .len()
            .checked_add(constructor.spelling.len())
            .ok_or(ResolvedBuildFailure::TypeResource)?;
        work.charge(spelling_work)
            .map_err(|()| ResolvedBuildFailure::TypeResource)?;
        if spelling != constructor.spelling || parameters.len() != original_parameters.len() {
            return Err(invalid());
        }
        // The shared comparator pays each parameter/kind/origin step. Prepay
        // spelling byte comparisons separately before it examines those names.
        for (parameter, original) in parameters.iter().zip(original_parameters) {
            let bytes = parameter
                .spelling
                .len()
                .checked_add(original.spelling.len())
                .ok_or(ResolvedBuildFailure::TypeResource)?;
            work.charge(bytes)
                .map_err(|()| ResolvedBuildFailure::TypeResource)?;
        }
        if !same_summary_resolved_type_variables_with_constraint_budget(
            parameters,
            original_parameters,
            constraints,
        )? || !same_origin_with_constraint_budget(origin, &constructor.origin, constraints)?
        {
            return Err(invalid());
        }
        let expected_payload = match owner.declaration_kind {
            ResolvedNominalDeclarationKind::Data => constructor.payload.as_ref(),
            ResolvedNominalDeclarationKind::Newtype => {
                Some(owner.representation.as_ref().ok_or_else(invalid)?)
            }
        };
        let same_payload = match (payload, expected_payload) {
            (None, None) => true,
            (Some(actual), Some(expected)) => {
                same_type_with_constraint_budget(actual, expected, constraints)
                    .map_err(|()| ResolvedBuildFailure::ConstraintResource)?
            }
            _ => false,
        };
        if !same_payload {
            return Err(invalid());
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        module::ModuleId,
        resolved::{ResolvedConstructor, ResolvedNominalType},
        types::NominalTypeId,
    };

    #[test]
    fn constructor_original_last_owner_refusal_and_replacement_drop_iteratively() {
        std::thread::Builder::new()
            .stack_size(256 * 1024)
            .spawn(|| {
                let source =
                    crate::source::SourceFile::new("constructor-original-drop", "C").unwrap();
                let span = source
                    .span(crate::source::ByteRange::new(0, 1).unwrap())
                    .unwrap();
                let id = NominalTypeId::new(ModuleId::new(10998), 0);
                let fact = || {
                    let mut origin = Origin::Source(span);
                    let mut payload = Type::Int;
                    for _ in 0..32768 {
                        origin = Origin::Generated {
                            cause: Box::new(origin),
                            reason: crate::source::GeneratedReason::TypeChecking,
                        };
                        payload = Type::Function(Box::new(Type::Int), Box::new(payload));
                    }
                    let constructor = ConstructorId::new(id, 0);
                    let mut registry = ResolvedRegistry::new(
                        vec![ResolvedNominalType {
                            id,
                            declaration_kind: ResolvedNominalDeclarationKind::Data,
                            spelling: "C".to_owned(),
                            constructors: Box::new([constructor]),
                            representation: None,
                            representation_provenance: None,
                            origin: Origin::Source(span),
                        }],
                        vec![ResolvedConstructor {
                            id: constructor,
                            owner: id,
                            spelling: "C".to_owned(),
                            payload: Some(payload),
                            origin,
                        }],
                    );
                    registry.nominal_parameters.insert(id, Box::new([]));
                    ConstructorOriginal::from_checked(
                        &Arc::new(registry),
                        &mut TypeWorkBudget::with_limit(1),
                    )
                    .unwrap()
                };
                let original = fact();
                assert!(original.retain(&mut TypeWorkBudget::with_limit(0)).is_err());
                assert_eq!(Arc::strong_count(&original.0), 1);
                let retained = original.retain(&mut TypeWorkBudget::with_limit(1)).unwrap();
                assert_eq!(original, retained);
                drop(original);
                drop(retained);
                let mut slot = Some(fact());
                let previous = slot.replace(fact());
                drop(previous);
                drop(slot);
            })
            .unwrap()
            .join()
            .unwrap();
    }
}
