//! Defining constructor meanings borrowed from an existing checked registry.
//!
//! This reference supplies no projected kind, source access or native authority.
//! Only completed local checking may create it; imports retain the same reference.

use super::*;
use std::fmt;

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
