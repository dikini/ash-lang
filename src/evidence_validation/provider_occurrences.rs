//! Compiler-only copies of original provider evidence occurrences.
//!
//! Fresh allocation pins and rewritten selections are preparation claims. The
//! scope factory independently reconstructs their complete original relation.

use super::{
    EvidenceValidationFailure, LinkedInterfaceRegistry, MethodEvidenceInputs,
    build_method_evidence_catalog_from_inputs, invalid_root, resource, same_argument_charged,
    type_resource,
};
use crate::{
    core::dialect::{MethodEvidenceCatalog, MethodEvidenceOccurrence, MethodEvidenceOwner},
    interface::{InterfaceApplication, InterfaceConstraintBudget},
    resolved::ResolvedModuleProgram,
    source::Span,
    types::{TypeWorkBudget, clone_type_with_budget},
};
use std::{collections::HashSet, fmt, sync::Arc};
use {
    crate::interface::FinalOccurrenceOwner, crate::types::IterativeArgumentOwner,
    crate::types::IterativeTypeOwner,
};

impl fmt::Debug for CopiedProviderOccurrenceCatalog {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("CopiedProviderOccurrenceCatalog")
            .field("occurrences", &self.occurrences.len())
            .field("owners", &self.owners.len())
            .field("relocations", &self.relocations.len())
            .finish()
    }
}

fn copy_application(
    source: &InterfaceApplication,
    context: &ProviderCopyContext<'_>,
    span: Span,
    types: &mut TypeWorkBudget,
) -> Result<InterfaceApplication, EvidenceValidationFailure> {
    let count = source.arguments().len();
    types
        .charge(count.checked_mul(2).ok_or_else(|| type_resource(span))?)
        .map_err(|()| type_resource(span))?;
    let mut staged = Vec::new();
    staged
        .try_reserve_exact(count)
        .map_err(|_| type_resource(span))?;
    let mut arguments = Vec::new();
    arguments
        .try_reserve_exact(count)
        .map_err(|_| type_resource(span))?;
    for argument in source.arguments() {
        staged.push(IterativeArgumentOwner::new(
            context
                .argument(argument, types)
                .map_err(|failure| mapping_failure(failure, span))?,
        ));
    }
    arguments.extend(staged.into_iter().map(IterativeArgumentOwner::into_inner));
    Ok(InterfaceApplication::new_kinded(
        source.interface(),
        arguments.into_boxed_slice(),
    ))
}

fn copy_owner(
    owner: Option<MethodEvidenceOwner>,
    original: ProviderOriginalTemplate<'_>,
    context: &ProviderCopyContext<'_>,
    span: Span,
    types: &mut TypeWorkBudget,
) -> Result<Option<MethodEvidenceOwner>, EvidenceValidationFailure> {
    Ok(match owner {
        Some(MethodEvidenceOwner::Global(binder)) => Some(MethodEvidenceOwner::Global(
            context
                .binder(binder, types)
                .map_err(|failure| mapping_failure(failure, span))?,
        )),
        Some(MethodEvidenceOwner::ResourceFamily(definition)) => {
            types.charge(1).map_err(|()| type_resource(span))?;
            let ProviderOriginalTemplate::Handler(handler) = original else {
                return Err(invalid_root(span));
            };
            let template = handler.original_template();
            if template.definition() != definition || template.ordinal() != 3 {
                return Err(invalid_root(span));
            }
            Some(MethodEvidenceOwner::ResourceFamily(definition))
        }
        Some(MethodEvidenceOwner::Implementation(method)) => {
            Some(MethodEvidenceOwner::Implementation(method))
        }
        None => None,
    })
}

fn mapping_failure(failure: crate::core::BuildError, span: Span) -> EvidenceValidationFailure {
    match failure {
        crate::core::BuildError::TypeWorkExceeded => type_resource(span),
        _ => invalid_root(span),
    }
}

fn retain_occurrence(
    source: &MethodEvidenceOccurrence,
    span: Span,
    types: &mut TypeWorkBudget,
) -> Result<MethodEvidenceOccurrence, EvidenceValidationFailure> {
    let application = source
        .checked_application
        .clone_with_budget(types)
        .map_err(|()| type_resource(span))?;
    let count = source.method_arguments.len();
    types
        .charge(count.checked_mul(2).ok_or_else(|| type_resource(span))?)
        .map_err(|()| type_resource(span))?;
    let mut staged = Vec::new();
    staged
        .try_reserve_exact(count)
        .map_err(|_| type_resource(span))?;
    let mut arguments = Vec::new();
    arguments
        .try_reserve_exact(count)
        .map_err(|_| type_resource(span))?;
    for argument in &source.method_arguments {
        staged.push(IterativeTypeOwner::new(
            clone_type_with_budget(argument, types).map_err(|()| type_resource(span))?,
        ));
    }
    let value_type = source
        .checked_value_type
        .as_ref()
        .map(|ty| {
            clone_type_with_budget(ty, types)
                .map(IterativeTypeOwner::new)
                .map_err(|()| type_resource(span))
        })
        .transpose()?;
    arguments.extend(staged.into_iter().map(IterativeTypeOwner::into_inner));
    Ok(MethodEvidenceOccurrence {
        slot: source.slot,
        scope: source.scope,
        scope_binder: source.scope_binder,
        target_owner: source.target_owner,
        target_requirement: source.target_requirement,
        checked_method: source.checked_method,
        checked_application: application,
        method_arguments: arguments.into_boxed_slice(),
        checked_value_type: value_type.map(IterativeTypeOwner::into_inner),
        selection: source.selection.clone(),
    })
}
