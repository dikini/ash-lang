//! Compiler-only copies of original provider evidence occurrences.
//!
//! Fresh allocation pins and rewritten selections are preparation claims. The
//! scope factory independently reconstructs their complete original relation.

use super::{
    EvidenceValidationFailure, MethodEvidenceInputs, build_method_evidence_catalog_from_inputs,
    invalid_root, resource, same_argument_charged, type_resource,
};
use crate::{
    core::dialect::{MethodEvidenceCatalog, MethodEvidenceOccurrence, MethodEvidenceOwner},
    interface::{InterfaceApplication, InterfaceConstraintBudget},
    resolved::ResolvedModuleProgram,
    source::Span,
    types::{TypeWorkBudget, clone_type_with_budget},
};
use crate::{
    core::provider::{ProviderCopyContext, ProviderOccurrenceRelocation, ProviderOriginalTemplate},
    interface::FinalOccurrenceOwner,
    types::{IterativeArgumentOwner, IterativeTypeOwner},
};
use std::{collections::HashSet, fmt, sync::Arc};

/// A complete copied occurrence set for one immutable original template.
/// Original code remains outside executable Core; this catalog contains only
/// checked types, selected plans and their original allocation identities.
pub(crate) struct CopiedProviderOccurrenceCatalog {
    pub(crate) original_catalog: Arc<MethodEvidenceCatalog>,
    pub(crate) occurrences: Vec<MethodEvidenceOccurrence>,
    pub(crate) owners: Vec<FinalOccurrenceOwner>,
    pub(crate) relocations: Vec<ProviderOccurrenceRelocation>,
}

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

pub(crate) fn copy_provider_occurrences(
    original: ProviderOriginalTemplate<'_>,
    context: &ProviderCopyContext<'_>,
    span: Span,
    constraints: &mut InterfaceConstraintBudget,
    types: &mut TypeWorkBudget,
) -> Result<CopiedProviderOccurrenceCatalog, EvidenceValidationFailure> {
    let source = match original {
        ProviderOriginalTemplate::Lifecycle(authority, program) => {
            authority
                .authenticate_source(program, types)
                .map_err(|failure| {
                    if failure.reason() == crate::core::ValidationReason::Resource {
                        type_resource(span)
                    } else {
                        invalid_root(span)
                    }
                })?;
            program
        }
        ProviderOriginalTemplate::Handler(authority) => {
            authority.authenticate_source(types).map_err(|failure| {
                if failure.reason() == crate::core::ValidationReason::Resource {
                    type_resource(span)
                } else {
                    invalid_root(span)
                }
            })?;
            authority.original_program()
        }
    };
    let catalog = source.method_evidence();
    let count = catalog.occurrences().len();
    types
        .charge(
            count
                .checked_mul(4)
                .and_then(|n| n.checked_add(1))
                .ok_or_else(|| type_resource(span))?,
        )
        .map_err(|()| type_resource(span))?;
    let mut output = CopiedProviderOccurrenceCatalog {
        original_catalog: Arc::clone(catalog),
        occurrences: Vec::new(),
        owners: Vec::new(),
        relocations: Vec::new(),
    };
    output
        .occurrences
        .try_reserve_exact(count)
        .map_err(|_| type_resource(span))?;
    output
        .owners
        .try_reserve_exact(count)
        .map_err(|_| type_resource(span))?;
    output
        .relocations
        .try_reserve_exact(count)
        .map_err(|_| type_resource(span))?;
    let mut originals = HashSet::new();
    originals
        .try_reserve(count)
        .map_err(|_| type_resource(span))?;
    for occurrence in catalog.occurrences() {
        if !originals.insert(occurrence.slot) {
            return Err(invalid_root(span));
        }
        let owner =
            FinalOccurrenceOwner::new_with_budget(types).map_err(|()| type_resource(span))?;
        let slot = owner.storage_id();
        let application = copy_application(&occurrence.checked_application, context, span, types)?;
        let selection = occurrence.selection.specialize_with(
            types,
            constraints,
            |ty, work| {
                context
                    .ty(ty, work)
                    .map_err(|failure| mapping_failure(failure, span))
            },
            |argument, work| {
                context
                    .argument(argument, work)
                    .map_err(|failure| mapping_failure(failure, span))
            },
            |lexical, work| {
                context
                    .lexical(lexical, work)
                    .map_err(|failure| mapping_failure(failure, span))
            },
            || type_resource(span),
            || resource(span),
            || invalid_root(span),
        )?;
        if selection.interface() != application.interface()
            || selection.arguments().len() != application.arguments().len()
            || !selection.same_original_owner(&occurrence.selection)
        {
            return Err(invalid_root(span));
        }
        for (actual, expected) in selection.arguments().iter().zip(application.arguments()) {
            if !same_argument_charged(actual, expected, constraints, span)? {
                return Err(invalid_root(span));
            }
        }
        let count = occurrence.method_arguments.len();
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
        for argument in &occurrence.method_arguments {
            staged.push(IterativeTypeOwner::new(
                context
                    .ty(argument, types)
                    .map_err(|failure| mapping_failure(failure, span))?,
            ));
        }
        let value_type = occurrence
            .checked_value_type
            .as_ref()
            .map(|ty| {
                context
                    .ty(ty, types)
                    .map(IterativeTypeOwner::new)
                    .map_err(|failure| mapping_failure(failure, span))
            })
            .transpose()?;
        let scope = copy_owner(occurrence.scope, context, span, types)?;
        let scope_binder = occurrence
            .scope_binder
            .map(|binder| {
                context
                    .binder(binder, types)
                    .map_err(|failure| mapping_failure(failure, span))
            })
            .transpose()?;
        let target_owner = copy_owner(occurrence.target_owner, context, span, types)?;
        // No fallible work remains after releasing the iterative Type guards.
        arguments.extend(staged.into_iter().map(IterativeTypeOwner::into_inner));
        output.occurrences.push(MethodEvidenceOccurrence {
            slot,
            scope,
            scope_binder,
            target_owner,
            target_requirement: occurrence.target_requirement,
            checked_method: occurrence.checked_method,
            checked_application: application,
            method_arguments: arguments.into_boxed_slice(),
            checked_value_type: value_type.map(IterativeTypeOwner::into_inner),
            selection,
        });
        output.relocations.push(ProviderOccurrenceRelocation {
            original: occurrence.slot,
            copied: slot,
        });
        output.owners.push(owner);
    }
    Ok(output)
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
        other => other,
    })
}

fn mapping_failure(failure: crate::core::BuildError, span: Span) -> EvidenceValidationFailure {
    match failure {
        crate::core::BuildError::TypeWorkExceeded => type_resource(span),
        _ => invalid_root(span),
    }
}

/// Builds all auxiliary evidence rows after copied occurrences have joined the
/// linked source occurrences. Prepared copies remain immutable in source plans;
/// final catalog shares their exact allocation pins and selected plan views.
pub(crate) fn build_catalog_with_provider_copies<'a>(
    program: &ResolvedModuleProgram,
    copies: impl Iterator<Item = &'a CopiedProviderOccurrenceCatalog>,
    constraints: &mut InterfaceConstraintBudget,
    types: &mut TypeWorkBudget,
) -> Result<MethodEvidenceCatalog, EvidenceValidationFailure> {
    let span = program.result().span;
    let mut occurrences = Vec::new();
    let mut owners = Vec::new();
    let mut keys = Vec::new();
    for copy in copies {
        let count = copy.occurrences.len();
        if copy.owners.len() != count
            || copy.relocations.len() != count
            || copy.original_catalog.occurrences().len() != count
        {
            return Err(invalid_root(span));
        }
        // Three retained vectors and two Arc cells per specialized selection.
        types
            .charge(count.checked_mul(5).ok_or_else(|| type_resource(span))?)
            .map_err(|()| type_resource(span))?;
        occurrences
            .try_reserve(count)
            .map_err(|_| type_resource(span))?;
        owners.try_reserve(count).map_err(|_| type_resource(span))?;
        keys.try_reserve(count).map_err(|_| type_resource(span))?;
        for (((occurrence, owner), relocation), original) in copy
            .occurrences
            .iter()
            .zip(&copy.owners)
            .zip(&copy.relocations)
            .zip(copy.original_catalog.occurrences())
        {
            if occurrence.slot != owner.storage_id()
                || relocation.copied != occurrence.slot
                || relocation.original != original.slot
                || !occurrence
                    .selection
                    .same_original_owner(&original.selection)
            {
                return Err(invalid_root(span));
            }
            occurrences.push(retain_occurrence(occurrence, span, types)?);
            owners.push(
                owner
                    .clone_with_budget(types)
                    .map_err(|()| type_resource(span))?,
            );
            keys.push(occurrence.slot);
        }
    }
    let mut catalog = build_method_evidence_catalog_from_inputs(
        MethodEvidenceInputs::Linked(program),
        occurrences,
        constraints,
        types,
    )?;
    catalog
        .attach_final_occurrence_owners(owners, &keys, types)
        .map_err(|failure| {
            if failure.reason() == crate::core::ValidationReason::Resource {
                type_resource(span)
            } else {
                invalid_root(span)
            }
        })?;
    Ok(catalog)
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
