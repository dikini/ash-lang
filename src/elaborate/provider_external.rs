//! Contextual checking of unpublished lifecycle helper occurrences.

use super::{
    Arc, CoreBuilder, CoreElaborator, CorePattern, EffectOperationFamily, HashSet,
    IterativeTypeOwner, LifecycleDraftCheckError, LifecycleTemplateDraft, OwnedTypeBuffer,
    PendingEvidencePublication, Phase, ResolvedExpr, ResolvedExprKind, ResolvedResourceDefinition,
    TypeError, TypeWorkBudget, TypedNodeOwner, clone_effect_row_with_budget, constraint_resource,
    discard_type_iteratively, invalid_state, provider, selection_failure, type_resource,
};
use crate::core::{NodeId, TypedBinder};
use crate::elaborate::CorePatternBuffer;

impl LifecycleTemplateDraft {
    pub(super) fn admit_from_defining_module(
        self,
        module: &crate::resolved::ResolvedModule,
        work: &mut TypeWorkBudget,
    ) -> Result<provider::CheckedLifecycleTemplate, LifecycleDraftCheckError> {
        self.admit_from_defining_module_with_native_memo(module, None, work)
    }

    pub(super) fn admit_from_defining_module_with_native_memo(
        self,
        module: &crate::resolved::ResolvedModule,
        native_authentication: Option<&crate::foreign::NativeAuthenticationSession>,
        work: &mut TypeWorkBudget,
    ) -> Result<provider::CheckedLifecycleTemplate, LifecycleDraftCheckError> {
        let retained = module.defining_sources();
        work.charge(
            retained
                .len()
                .checked_mul(2)
                .ok_or(LifecycleDraftCheckError::Resource)?,
        )
        .map_err(|()| LifecycleDraftCheckError::Resource)?;
        let mut sources = Vec::new();
        let mut module_sources = Vec::new();
        sources
            .try_reserve_exact(retained.len())
            .map_err(|_| LifecycleDraftCheckError::Resource)?;
        module_sources
            .try_reserve_exact(retained.len())
            .map_err(|_| LifecycleDraftCheckError::Resource)?;
        for (id, source) in retained {
            sources.push(&**source);
            module_sources.push((*id, source.id()));
        }
        self.admit_with_native_memo(
            module,
            &sources,
            &module_sources,
            native_authentication,
            work,
        )
    }

    pub(super) fn check_staged_externals(
        &self,
        definition: &ResolvedResourceDefinition,
        imported: &crate::resolved::ImportedFacts,
        sources: &[&crate::source::SourceFile],
        module_sources: &[(crate::module::ModuleId, crate::source::SourceId)],
        canonical: &crate::resolved::ResolvedRegistry,
        work: &mut TypeWorkBudget,
    ) -> Result<(), LifecycleDraftCheckError> {
        self.check_staged_externals_with_associations(
            definition,
            imported,
            sources,
            module_sources,
            canonical,
            &[],
            work,
        )
    }

    #[expect(
        clippy::too_many_arguments,
        reason = "the private draft entry retains independently supplied source, canonical, and association proof inputs"
    )]
    pub(super) fn check_staged_externals_with_associations(
        &self,
        definition: &ResolvedResourceDefinition,
        imported: &crate::resolved::ImportedFacts,
        sources: &[&crate::source::SourceFile],
        module_sources: &[(crate::module::ModuleId, crate::source::SourceId)],
        canonical: &crate::resolved::ResolvedRegistry,
        associations: &[crate::core::provider::DraftStateAssociation<'_>],
        work: &mut TypeWorkBudget,
    ) -> Result<(), LifecycleDraftCheckError> {
        self.reconstruct_staged_externals(
            definition,
            imported,
            sources,
            module_sources,
            canonical,
            associations,
            true,
            None,
            work,
        )
        .map(drop)
    }

    pub(super) fn admit(
        self,
        module: &crate::resolved::ResolvedModule,
        sources: &[&crate::source::SourceFile],
        module_sources: &[(crate::module::ModuleId, crate::source::SourceId)],
        work: &mut TypeWorkBudget,
    ) -> Result<provider::CheckedLifecycleTemplate, LifecycleDraftCheckError> {
        self.admit_with_native_memo(module, sources, module_sources, None, work)
    }

    pub(super) fn admit_with_native_memo(
        self,
        module: &crate::resolved::ResolvedModule,
        sources: &[&crate::source::SourceFile],
        module_sources: &[(crate::module::ModuleId, crate::source::SourceId)],
        native_authentication: Option<&crate::foreign::NativeAuthenticationSession>,
        work: &mut TypeWorkBudget,
    ) -> Result<provider::CheckedLifecycleTemplate, LifecycleDraftCheckError> {
        work.charge(module.resources().len())
            .map_err(|()| LifecycleDraftCheckError::Resource)?;
        let definition = module
            .resources()
            .iter()
            .find(|definition| definition.id == self.id.definition())
            .ok_or(LifecycleDraftCheckError::InvalidEntry)?;
        let canonical = Arc::new(
            module
                .registry()
                .provider_template_view(module.imported_facts(), work)
                .map_err(|failure| match failure {
                    crate::resolved::ResolvedBuildFailure::TypeResource
                    | crate::resolved::ResolvedBuildFailure::ConstraintResource => {
                        LifecycleDraftCheckError::Resource
                    }
                    _ => LifecycleDraftCheckError::InvalidEntry,
                })?,
        );
        work.charge(module.resources().len())
            .map_err(|()| LifecycleDraftCheckError::Resource)?;
        let mut associations = Vec::new();
        associations
            .try_reserve_exact(module.resources().len())
            .map_err(|_| LifecycleDraftCheckError::Resource)?;
        for source in module.resources() {
            work.charge(source.parameters.len())
                .map_err(|()| LifecycleDraftCheckError::Resource)?;
            let mut parameters = Vec::new();
            parameters
                .try_reserve_exact(source.parameters.len())
                .map_err(|_| LifecycleDraftCheckError::Resource)?;
            parameters.extend(source.parameters.iter().map(|parameter| parameter.id));
            associations.push(provider::HeaderStateAssociation {
                definition: source.id,
                family: source.family,
                parameters: parameters.into_boxed_slice(),
                state: IterativeTypeOwner::new(
                    crate::types::clone_type_with_budget(&source.state.ty, work)
                        .map_err(|()| LifecycleDraftCheckError::Resource)?,
                ),
            });
        }
        work.charge(associations.len())
            .map_err(|()| LifecycleDraftCheckError::Resource)?;
        let mut borrowed = Vec::new();
        borrowed
            .try_reserve_exact(associations.len())
            .map_err(|_| LifecycleDraftCheckError::Resource)?;
        for association in &associations {
            borrowed.push(crate::core::provider::DraftStateAssociation {
                definition: association.definition,
                family: association.family,
                parameters: &association.parameters,
                state: &association.state,
            });
        }
        let authenticated = self.reconstruct_staged_externals(
            definition,
            module.imported_facts(),
            sources,
            module_sources,
            &canonical,
            &borrowed,
            false,
            native_authentication,
            work,
        )?;

        let occurrences = &self
            .staged_externals
            .as_ref()
            .ok_or(LifecycleDraftCheckError::InvalidEntry)?
            .occurrences;
        work.charge(occurrences.len())
            .map_err(|()| LifecycleDraftCheckError::Resource)?;
        let mut originals = std::collections::HashMap::new();
        originals
            .try_reserve(occurrences.len())
            .map_err(|_| LifecycleDraftCheckError::Resource)?;
        for occurrence in occurrences {
            let root = occurrence
                .node
                .ok_or(LifecycleDraftCheckError::InvalidEntry)?;
            if originals.insert(root, &occurrence.occurrence).is_some() {
                return Err(LifecycleDraftCheckError::InvalidEntry);
            }
        }
        let phase = match self.phase {
            Phase::Acquire => crate::core::provider::LifecyclePhase::Acquire,
            Phase::Finish => crate::core::provider::LifecyclePhase::Finish,
            _ => return Err(LifecycleDraftCheckError::InvalidEntry),
        };
        let original = crate::core::provider::admit_lifecycle_original(
            &self.core,
            &crate::core::provider::LifecycleEntryContext {
                definition: crate::core::provider::LifecycleDefinitionView::source(
                    definition, phase,
                ),
                template: self.id,
                phase,
                body: self.body,
                parameter: self.parameter,
                hidden_answer: self.hidden_answer,
                hidden_row: self.hidden_row,
                formal_parameters: &self.formal_parameters,
            },
            &authenticated,
            &borrowed,
            work,
        )
        .map_err(LifecycleDraftCheckError::Core)?;
        let externals = authenticated
            .retain_lifecycle(&self.core, &originals, work)
            .map_err(LifecycleDraftCheckError::Core)?;

        drop(originals);
        drop(borrowed);
        let parameter = match self.phase {
            Phase::Acquire => &definition.acquire_binder,
            Phase::Finish => &definition.finish_binder,
            _ => return Err(LifecycleDraftCheckError::InvalidEntry),
        };
        let parameter_origin =
            crate::core::provider::RetainedHandlerOrigin::copy(&parameter.origin, work)
                .map_err(LifecycleDraftCheckError::Core)?;
        Ok(provider::CheckedLifecycleTemplate {
            original,
            parameter_origin: Arc::new(parameter_origin),
            draft: self,
            canonical,
            externals: Arc::new(externals),
            associations,
        })
    }

    #[expect(
        clippy::too_many_arguments,
        reason = "source, canonical, association, and work authorities remain explicit during owned admission"
    )]
    fn reconstruct_staged_externals<'a>(
        &'a self,
        definition: &ResolvedResourceDefinition,
        imported: &'a crate::resolved::ImportedFacts,
        sources: &[&crate::source::SourceFile],
        module_sources: &[(crate::module::ModuleId, crate::source::SourceId)],
        canonical: &crate::resolved::ResolvedRegistry,
        associations: &[crate::core::provider::DraftStateAssociation<'_>],
        check_flow: bool,
        native_authentication: Option<&crate::foreign::NativeAuthenticationSession>,
        work: &mut TypeWorkBudget,
    ) -> Result<crate::core::provider::AuthenticatedProviderExternals<'a>, LifecycleDraftCheckError>
    {
        let staged = self
            .staged_externals
            .as_ref()
            .ok_or(LifecycleDraftCheckError::InvalidEntry)?;
        let source = match self.phase {
            Phase::Acquire => &definition.acquire,
            Phase::Finish => &definition.finish,
            _ => return Err(LifecycleDraftCheckError::InvalidEntry),
        };
        let checked = provider_source_occurrences_with_facts(
            source,
            crate::resolved::ProviderExternalFacts {
                imported,
                defining: self.defining_facts.as_deref(),
            },
            work,
        )?;
        if checked.len() != staged.occurrences.len() {
            return Err(LifecycleDraftCheckError::InvalidEntry);
        }
        let mut occurrences = Vec::new();
        work.charge(checked.len())
            .map_err(|()| LifecycleDraftCheckError::Resource)?;
        occurrences
            .try_reserve_exact(checked.len())
            .map_err(|_| LifecycleDraftCheckError::Resource)?;
        let mut used = HashSet::new();
        for source in checked {
            work.charge(staged.occurrences.len())
                .map_err(|()| LifecycleDraftCheckError::Resource)?;
            let retained = staged
                .occurrences
                .iter()
                .find(|candidate| {
                    candidate.occurrence.term == source.term
                        && candidate.occurrence.origin.primary_span()
                            == source.origin.primary_span()
                })
                .ok_or(LifecycleDraftCheckError::InvalidEntry)?;
            work.charge(source.spelling.len() + source.evidence.len() + 1)
                .map_err(|()| LifecycleDraftCheckError::Resource)?;
            if retained.occurrence.spelling != source.spelling
                || retained.occurrence.import_span() != source.import_span()
                || retained.occurrence.evidence.len() != source.evidence.len()
                || !crate::resolved::same_origin_with_budget(
                    &retained.occurrence.origin,
                    &source.origin,
                    work,
                )
                .map_err(|()| LifecycleDraftCheckError::Resource)?
                || retained
                    .occurrence
                    .evidence
                    .iter()
                    .zip(&source.evidence)
                    .any(|(a, b)| {
                        a.storage_id() != b.storage_id()
                            || a.selection().is_some()
                            || b.selection().is_some()
                    })
            {
                return Err(LifecycleDraftCheckError::InvalidEntry);
            }
            let root = retained
                .node
                .ok_or(LifecycleDraftCheckError::InvalidEntry)?;
            work.charge(1)
                .map_err(|()| LifecycleDraftCheckError::Resource)?;
            used.try_reserve(1)
                .map_err(|_| LifecycleDraftCheckError::Resource)?;
            if !used.insert(root) {
                return Err(LifecycleDraftCheckError::InvalidEntry);
            }
            occurrences.push(crate::core::provider::ProviderExternalOccurrence {
                root,
                source,
                arguments: &retained.arguments,
                row_arguments: &retained.row_arguments,
            });
        }
        let externals = crate::core::provider::authenticate_staged_externals_with_defining(
            &self.core,
            imported,
            self.defining_facts.as_deref(),
            &staged.publication,
            &occurrences,
            sources,
            module_sources,
            canonical,
            associations,
            definition.id.module(),
            native_authentication,
            work,
        )
        .map_err(LifecycleDraftCheckError::Core)?;

        if check_flow {
            self.check_flow_with_external_context(
                definition,
                associations,
                Some(&externals),
                work,
            )?;
        }

        Ok(externals)
    }

    pub(super) fn check_plain_externals(
        &self,
        definition: &ResolvedResourceDefinition,
        imported: &crate::resolved::ImportedFacts,
        sources: &[&crate::source::SourceFile],
        module_sources: &[(crate::module::ModuleId, crate::source::SourceId)],
        canonical: &crate::resolved::ResolvedRegistry,
        work: &mut TypeWorkBudget,
    ) -> Result<(), LifecycleDraftCheckError> {
        self.check_plain_externals_with_associations(
            definition,
            imported,
            sources,
            module_sources,
            canonical,
            &[],
            work,
        )
    }

    #[expect(
        clippy::too_many_arguments,
        reason = "the private draft entry retains independently supplied source, canonical, and association proof inputs"
    )]
    pub(super) fn check_plain_externals_with_associations(
        &self,
        definition: &ResolvedResourceDefinition,
        imported: &crate::resolved::ImportedFacts,
        sources: &[&crate::source::SourceFile],
        module_sources: &[(crate::module::ModuleId, crate::source::SourceId)],
        canonical: &crate::resolved::ResolvedRegistry,
        associations: &[crate::core::provider::DraftStateAssociation<'_>],
        work: &mut TypeWorkBudget,
    ) -> Result<(), LifecycleDraftCheckError> {
        let externals = crate::core::provider::authenticate_plain_externals_with_defining(
            &self.core,
            imported,
            self.defining_facts.as_deref(),
            sources,
            module_sources,
            canonical,
            associations,
            work,
        )
        .map_err(LifecycleDraftCheckError::Core)?;
        self.check_flow_with_external_context(definition, associations, Some(&externals), work)
    }
}

impl provider::CompiledHandlerDraft {
    pub(super) fn check(
        &self,
        module: &crate::resolved::ResolvedModule,
        sources: &[&crate::source::SourceFile],
        module_sources: &[(crate::module::ModuleId, crate::source::SourceId)],
        work: &mut TypeWorkBudget,
    ) -> Result<(), provider::LifecycleDraftCheckError> {
        let staged = self
            .staged_externals
            .as_ref()
            .ok_or(provider::LifecycleDraftCheckError::InvalidEntry)?;
        work.charge(staged.occurrences.len())
            .map_err(|()| provider::LifecycleDraftCheckError::Resource)?;
        let mut occurrences = Vec::new();
        occurrences
            .try_reserve_exact(staged.occurrences.len())
            .map_err(|_| provider::LifecycleDraftCheckError::Resource)?;
        for retained in &staged.occurrences {
            occurrences.push(crate::core::provider::ProviderExternalOccurrence {
                root: retained
                    .node
                    .ok_or(provider::LifecycleDraftCheckError::InvalidEntry)?,
                source: &retained.occurrence,
                arguments: &retained.arguments,
                row_arguments: &retained.row_arguments,
            });
        }
        crate::core::validate::check_provider_handler_staged_structure(
            &self.fragment,
            module,
            sources,
            module_sources,
            &staged.publication,
            &occurrences,
            work,
        )
        .map_err(provider::LifecycleDraftCheckError::Core)
    }

    pub(super) fn admit(
        self,
        module: &crate::resolved::ResolvedModule,
        sources: &[&crate::source::SourceFile],
        module_sources: &[(crate::module::ModuleId, crate::source::SourceId)],
        work: &mut TypeWorkBudget,
    ) -> Result<provider::CheckedConditionalHandler, provider::LifecycleDraftCheckError> {
        self.admit_with_native_memo(module, sources, module_sources, None, work)
    }

    pub(super) fn admit_with_native_memo(
        self,
        module: &crate::resolved::ResolvedModule,
        sources: &[&crate::source::SourceFile],
        module_sources: &[(crate::module::ModuleId, crate::source::SourceId)],
        native_authentication: Option<&crate::foreign::NativeAuthenticationSession>,
        work: &mut TypeWorkBudget,
    ) -> Result<provider::CheckedConditionalHandler, provider::LifecycleDraftCheckError> {
        let staged = self
            .staged_externals
            .ok_or(provider::LifecycleDraftCheckError::InvalidEntry)?;
        work.charge(staged.occurrences.len())
            .map_err(|()| provider::LifecycleDraftCheckError::Resource)?;
        let mut occurrences = Vec::new();
        occurrences
            .try_reserve_exact(staged.occurrences.len())
            .map_err(|_| provider::LifecycleDraftCheckError::Resource)?;
        for retained in &staged.occurrences {
            occurrences.push(crate::core::provider::ProviderExternalOccurrence {
                root: retained
                    .node
                    .ok_or(provider::LifecycleDraftCheckError::InvalidEntry)?,
                source: &retained.occurrence,
                arguments: &retained.arguments,
                row_arguments: &retained.row_arguments,
            });
        }
        let template = crate::core::validate::admit_provider_handler_template(
            self.fragment,
            module,
            sources,
            module_sources,
            Some((&staged.publication, &occurrences)),
            native_authentication,
            work,
        )
        .map_err(provider::LifecycleDraftCheckError::Core)?;
        drop(occurrences);
        Ok(provider::CheckedConditionalHandler {
            template,
            staged_externals: staged,
        })
    }
}

#[derive(Debug)]
pub(super) struct StagedProviderExternals {
    pub(super) publication: PendingEvidencePublication,
    pub(super) occurrences: Vec<provider::CheckedGlobalOccurrence>,
}

pub(super) struct LoweredProviderForest {
    pub(super) core: crate::core::UnvalidatedEffectProgram,
    pub(super) staged: Option<StagedProviderExternals>,
    pub(super) roots: Vec<NodeId>,
    pub(super) correspondence: Vec<Option<NodeId>>,
    pub(super) states: Vec<TypedBinder>,
    pub(super) patterns: CorePatternBuffer,
    pub(super) pending_rows: crate::core::provider::HandlerPendingRows,
}

impl CoreElaborator<EffectOperationFamily> {
    pub(super) fn lower_provider_source_draft(
        &mut self,
        root: NodeId,
        body: &mut NodeId,
        imported: &crate::resolved::ImportedFacts,
        publication: PendingEvidencePublication,
        substitutions: &super::super::OwnerReplacementBuffer,
    ) -> Result<
        (
            crate::core::UnvalidatedEffectProgram,
            Option<StagedProviderExternals>,
        ),
        TypeError,
    > {
        let lowered = self.lower_provider_source_forest(
            &[root],
            imported,
            publication,
            substitutions,
            &[],
            &[],
        )?;
        *body = lowered
            .correspondence
            .get(body.value() as usize)
            .copied()
            .flatten()
            .ok_or_else(invalid_state)?;
        Ok((lowered.core, lowered.staged))
    }

    pub(super) fn lower_provider_source_forest(
        &mut self,
        roots: &[NodeId],
        imported: &crate::resolved::ImportedFacts,
        publication: PendingEvidencePublication,
        substitutions: &super::super::OwnerReplacementBuffer,
        states: &[&TypedBinder],
        patterns: &[&CorePattern],
    ) -> Result<LoweredProviderForest, TypeError> {
        self.lower_provider_source_forest_with_pending(
            roots,
            imported,
            publication,
            substitutions,
            states,
            patterns,
            crate::core::provider::HandlerPendingRows::default(),
        )
    }

    #[expect(
        clippy::too_many_arguments,
        reason = "conditional forest owns pending source equations separately from ABI evidence and binder relocation"
    )]
    pub(super) fn lower_provider_source_forest_with_pending(
        &mut self,
        roots: &[NodeId],
        imported: &crate::resolved::ImportedFacts,
        mut publication: PendingEvidencePublication,
        substitutions: &super::super::OwnerReplacementBuffer,
        states: &[&TypedBinder],
        patterns: &[&CorePattern],
        pending_rows: crate::core::provider::HandlerPendingRows,
    ) -> Result<LoweredProviderForest, TypeError> {
        let root = *roots.first().ok_or_else(invalid_state)?;
        publication
            .relocate_types_and_rows(
                |ty, work| {
                    substitutions
                        .substitute(ty, work)
                        .map_err(|_| crate::evidence::SelectionFailure::TypeResource)
                },
                |row, work| {
                    substitutions
                        .substitute_row(row, work)
                        .map_err(|_| crate::evidence::SelectionFailure::TypeResource)
                },
                &mut self.constraint_work,
                &mut self.type_work,
            )
            .map_err(|failure| selection_failure(failure, None))?;
        let mut occurrences = std::mem::take(&mut self.provider_global_occurrences);
        let mut replacements = HashSet::new();
        self.type_work
            .charge(occurrences.len())
            .map_err(|()| type_resource())?;
        replacements
            .try_reserve(occurrences.len())
            .map_err(|_| type_resource())?;
        for occurrence in &mut occurrences {
            let binder = occurrence
                .occurrence
                .global_binder()
                .ok_or_else(invalid_state)?;
            if imported.global(binder).is_none()
                && self
                    .provider_defining_facts
                    .as_ref()
                    .and_then(|facts| facts.global(binder))
                    .is_none()
            {
                return Err(invalid_state());
            }
            if !replacements.insert(occurrence.node.ok_or_else(invalid_state)?) {
                return Err(invalid_state());
            }
            let zonked = IterativeTypeOwner::new(self.zonk(&occurrence.value_type)?);
            occurrence.value_type =
                IterativeTypeOwner::new(substitutions.substitute(&zonked, &mut self.type_work)?);
            for argument in occurrence.arguments.0.iter_mut() {
                let zonked = IterativeTypeOwner::new(self.zonk(argument)?);
                let rewritten = substitutions.substitute(&zonked, &mut self.type_work)?;
                discard_type_iteratively(std::mem::replace(argument, rewritten));
            }
            for row in &mut occurrence.row_arguments {
                let zonked = self.zonk_effect_row(row)?;
                *row = substitutions.substitute_row(&zonked, &mut self.type_work)?;
            }
        }
        let placeholder = CoreBuilder::<EffectOperationFamily>::with_registry_for_family(
            Arc::clone(&self.registry),
        );
        let (source, pending_rows) = std::mem::replace(&mut self.builder, placeholder)
            .finish_provider_conditional_draft(root, pending_rows, &mut self.type_work)?;
        // Validate the full source graph's arena and acyclicity before omitting
        // obsolete children during the final ABI traversal.
        let full_order = crate::core::transform::provider_fragment_order(
            &source,
            roots,
            &HashSet::new(),
            &mut self.type_work,
        )
        .map_err(provider_transform_failure)?;
        let catalog = crate::evidence_validation::build_provider_method_evidence_catalog(
            crate::resolved::ProviderExternalFacts {
                imported,
                defining: self.provider_defining_facts.as_deref(),
            },
            &self.registry,
            crate::core::transform::provider_draft_span(&source, root)
                .map_err(provider_transform_failure)?,
            occurrences.iter().map(|o| &o.occurrence),
            &publication,
            &mut self.constraint_work,
            &mut self.type_work,
        )
        .map_err(|failure| match failure.reason() {
            crate::evidence_validation::EvidenceValidationReason::TypeResourceExhausted => {
                type_resource()
            }
            crate::evidence_validation::EvidenceValidationReason::ConstraintResourceExhausted => {
                constraint_resource()
            }
            _ => invalid_state(),
        })?;
        self.builder = crate::core::transform::prepare_provider_fragment_builder_with_catalog(
            &source,
            &full_order,
            Arc::new(catalog),
            states,
            patterns,
            &mut self.type_work,
        )
        .map_err(provider_transform_failure)?;
        let order = crate::core::transform::provider_fragment_order(
            &source,
            roots,
            &replacements,
            &mut self.type_work,
        )
        .map_err(provider_transform_failure)?;
        pending_rows.seed_builder(&mut self.builder, &mut self.type_work)?;
        let mut lowering = self.prepare_provider_import_lowering(imported)?;
        self.type_work
            .charge(full_order.len())
            .map_err(|()| type_resource())?;
        let count = self.builder.node_checkpoint();
        debug_assert_eq!(count, 0);
        let mut remapped = Vec::new();
        remapped
            .try_reserve_exact(full_order.len())
            .map_err(|_| type_resource())?;
        // IDs can be sparse because obsolete nodes are pruned only in the output.
        let max = full_order
            .iter()
            .map(|id| id.value() as usize)
            .max()
            .ok_or_else(invalid_state)?
            + 1;
        self.type_work.charge(max).map_err(|()| type_resource())?;
        remapped
            .try_reserve_exact(max)
            .map_err(|_| type_resource())?;
        remapped.resize(max, None);
        for original in order {
            self.type_work
                .charge(occurrences.len() + 1)
                .map_err(|()| type_resource())?;
            crate::core::transform::begin_provider_draft_work(
                &mut self.builder,
                self.type_work.remaining(),
            );
            let result = (|| {
                let rewritten = if let Some(occurrence) = occurrences
                    .iter_mut()
                    .find(|occurrence| occurrence.source_node == Some(original))
                {
                    let expected = crate::core::transform::provider_draft_type(&source, original)
                        .map_err(provider_transform_failure)?;
                    let provenance = self.at_span_provenance(
                        expected,
                        occurrence.occurrence.origin.primary_span(),
                    )?;
                    let mut arguments = OwnedTypeBuffer(Vec::new());
                    self.type_work
                        .charge(occurrence.arguments.len())
                        .map_err(|()| type_resource())?;
                    arguments
                        .try_reserve(occurrence.arguments.len())
                        .map_err(|_| type_resource())?;
                    for argument in occurrence.arguments.iter() {
                        arguments.push(self.clone_type(argument)?);
                    }
                    let mut rows = Vec::new();
                    self.type_work
                        .charge(occurrence.row_arguments.len())
                        .map_err(|()| type_resource())?;
                    rows.try_reserve(occurrence.row_arguments.len())
                        .map_err(|_| type_resource())?;
                    for row in &occurrence.row_arguments {
                        rows.push(
                            clone_effect_row_with_budget(row, &mut self.type_work)
                                .map_err(|()| type_resource())?,
                        );
                    }
                    let typed = TypedNodeOwner::new(
                        self.lower_checked_global_occurrence(
                            occurrence
                                .occurrence
                                .global_binder()
                                .ok_or_else(invalid_state)?,
                            &occurrence.occurrence,
                            arguments,
                            rows,
                            expected,
                            provenance,
                            &mut lowering,
                            Some(&publication),
                        )?,
                    );
                    occurrence.node = Some(typed.node);
                    typed.node
                } else {
                    crate::core::transform::rebuild_provider_draft_node(
                        &mut self.builder,
                        &source,
                        &remapped,
                        original,
                    )
                    .map_err(provider_transform_failure)?
                };
                Ok::<_, TypeError>(rewritten)
            })();
            crate::core::transform::discharge_provider_draft_work(
                &self.builder,
                &mut self.type_work,
            )?;
            let rewritten = result?;
            remapped[original.value() as usize] = Some(rewritten);
        }
        self.type_work
            .charge(
                roots
                    .len()
                    .checked_add(states.len())
                    .and_then(|count| count.checked_add(patterns.len()))
                    .ok_or_else(type_resource)?,
            )
            .map_err(|()| type_resource())?;
        let mut mapped_roots = Vec::new();
        mapped_roots
            .try_reserve_exact(roots.len())
            .map_err(|_| type_resource())?;
        for root in roots {
            mapped_roots.push(
                remapped
                    .get(root.value() as usize)
                    .copied()
                    .flatten()
                    .ok_or_else(invalid_state)?,
            );
        }
        let mut mapped_states = Vec::new();
        mapped_states
            .try_reserve_exact(states.len())
            .map_err(|_| type_resource())?;
        for state in states {
            crate::core::transform::begin_provider_draft_work(
                &mut self.builder,
                self.type_work.remaining(),
            );
            let result =
                crate::core::transform::rebuild_provider_fragment_binder(&mut self.builder, state)
                    .map_err(provider_transform_failure);
            crate::core::transform::discharge_provider_draft_work(
                &self.builder,
                &mut self.type_work,
            )?;
            mapped_states.push(result?);
        }
        let mut mapped_patterns = CorePatternBuffer(Vec::new());
        mapped_patterns
            .try_reserve(patterns.len())
            .map_err(|_| type_resource())?;
        for pattern in patterns {
            crate::core::transform::begin_provider_draft_work(
                &mut self.builder,
                self.type_work.remaining(),
            );
            let result = crate::core::transform::rebuild_provider_fragment_pattern(
                &mut self.builder,
                pattern,
            )
            .map_err(provider_transform_failure);
            crate::core::transform::discharge_provider_draft_work(
                &self.builder,
                &mut self.type_work,
            )?;
            mapped_patterns.push(result?);
        }
        let placeholder = CoreBuilder::<EffectOperationFamily>::with_registry_for_family(
            Arc::clone(&self.registry),
        );
        let pending_rows =
            pending_rows.relocate(root, &remapped, mapped_roots[0], &mut self.type_work)?;
        let (core, pending_rows) = std::mem::replace(&mut self.builder, placeholder)
            .finish_provider_conditional_draft(
                mapped_roots[0],
                pending_rows,
                &mut self.type_work,
            )?;
        Ok(LoweredProviderForest {
            core,
            staged: Some(StagedProviderExternals {
                publication,
                occurrences,
            }),
            roots: mapped_roots,
            correspondence: remapped,
            states: mapped_states,
            patterns: mapped_patterns,
            pending_rows,
        })
    }
}

fn provider_transform_failure(failure: crate::core::transform::TransformError) -> TypeError {
    match failure {
        crate::core::transform::TransformError::Build(error) => error.into(),
        crate::core::transform::TransformError::InvalidValidatedInput => invalid_state(),
    }
}

#[cfg(test)]
pub(super) fn provider_source_occurrences<'a>(
    root: &'a ResolvedExpr,
    imported: &crate::resolved::ImportedFacts,
    work: &mut TypeWorkBudget,
) -> Result<Vec<&'a crate::resolved::ResolvedOccurrence>, LifecycleDraftCheckError> {
    provider_source_occurrences_with_facts(
        root,
        crate::resolved::ProviderExternalFacts {
            imported,
            defining: None,
        },
        work,
    )
}

pub(super) fn provider_source_occurrences_with_facts<'a>(
    root: &'a ResolvedExpr,
    facts: crate::resolved::ProviderExternalFacts<'_>,
    work: &mut TypeWorkBudget,
) -> Result<Vec<&'a crate::resolved::ResolvedOccurrence>, LifecycleDraftCheckError> {
    walk_provider_source_occurrences(
        root,
        |occurrence| {
            occurrence
                .global_binder()
                .is_some_and(|binder| facts.global(binder).is_some())
        },
        false,
        work,
    )
}

#[cfg(test)]
pub(super) fn all_provider_expression_occurrences<'a>(
    root: &'a ResolvedExpr,
    work: &mut TypeWorkBudget,
) -> Result<Vec<&'a crate::resolved::ResolvedOccurrence>, LifecycleDraftCheckError> {
    walk_provider_source_occurrences(root, |_| true, true, work)
}

fn walk_provider_source_occurrences<'a>(
    root: &'a ResolvedExpr,
    mut include: impl FnMut(&crate::resolved::ResolvedOccurrence) -> bool,
    allow_control: bool,
    work: &mut TypeWorkBudget,
) -> Result<Vec<&'a crate::resolved::ResolvedOccurrence>, LifecycleDraftCheckError> {
    let mut found = Vec::new();
    enum Item<'a> {
        Expression(&'a ResolvedExpr),
        Block(&'a crate::resolved::ResolvedBlock),
        Declaration(&'a crate::resolved::ResolvedLocalDeclaration),
    }
    let mut pending = Vec::new();
    pending
        .try_reserve(1)
        .map_err(|_| LifecycleDraftCheckError::Resource)?;
    pending.push(Item::Expression(root));
    while let Some(item) = pending.pop() {
        work.charge(1)
            .map_err(|()| LifecycleDraftCheckError::Resource)?;
        pending
            .try_reserve(3)
            .map_err(|_| LifecycleDraftCheckError::Resource)?;
        match item {
            Item::Block(block) => {
                work.charge(block.declarations.len())
                    .map_err(|()| LifecycleDraftCheckError::Resource)?;
                pending
                    .try_reserve(block.declarations.len().saturating_add(1))
                    .map_err(|_| LifecycleDraftCheckError::Resource)?;
                pending.push(Item::Expression(&block.result));
                pending.extend(block.declarations.iter().map(Item::Declaration));
            }
            Item::Declaration(crate::resolved::ResolvedLocalDeclaration::Binding(binding)) => {
                pending.push(Item::Expression(&binding.initializer))
            }
            Item::Declaration(crate::resolved::ResolvedLocalDeclaration::Recursive(group)) => {
                work.charge(group.members.len())
                    .map_err(|()| LifecycleDraftCheckError::Resource)?;
                pending
                    .try_reserve(group.members.len())
                    .map_err(|_| LifecycleDraftCheckError::Resource)?;
                pending.extend(
                    group
                        .members
                        .iter()
                        .map(|member| Item::Expression(&member.initializer)),
                );
            }
            Item::Declaration(crate::resolved::ResolvedLocalDeclaration::Evidence(source)) => {
                work.charge(source.method_groups.len())
                    .map_err(|()| LifecycleDraftCheckError::Resource)?;
                for group in &source.method_groups {
                    work.charge(group.equations.len())
                        .map_err(|()| LifecycleDraftCheckError::Resource)?;
                    pending
                        .try_reserve(group.equations.len())
                        .map_err(|_| LifecycleDraftCheckError::Resource)?;
                    pending.extend(
                        group
                            .equations
                            .iter()
                            .map(|equation| Item::Expression(&equation.body)),
                    );
                }
            }
            Item::Declaration(crate::resolved::ResolvedLocalDeclaration::Newtype(_)) => {}
            Item::Expression(expression) => match &expression.kind {
                // Only the test occurrence inventory permits clause control;
                // defining lifecycle checks always pass false.
                ResolvedExprKind::Resume(resume) if allow_control => {
                    pending.push(Item::Expression(&resume.value))
                }
                ResolvedExprKind::Discard(_) if allow_control => {}
                ResolvedExprKind::Cleanup(cleanup) if allow_control => {
                    pending.push(Item::Expression(&cleanup.body));
                    pending.push(Item::Expression(&cleanup.action));
                }
                ResolvedExprKind::Handle(handler) if allow_control => {
                    work.charge(handler.clauses.len())
                        .map_err(|()| LifecycleDraftCheckError::Resource)?;
                    pending
                        .try_reserve(handler.clauses.len().saturating_add(1))
                        .map_err(|_| LifecycleDraftCheckError::Resource)?;
                    pending.push(Item::Expression(&handler.body));
                    pending.extend(
                        handler
                            .clauses
                            .iter()
                            .map(|clause| Item::Expression(&clause.body)),
                    );
                }
                ResolvedExprKind::Handle(_)
                | ResolvedExprKind::Resume(_)
                | ResolvedExprKind::Discard(_)
                | ResolvedExprKind::Cleanup(_)
                | ResolvedExprKind::Resource(_)
                | ResolvedExprKind::ProviderResource(_) => {
                    return Err(LifecycleDraftCheckError::InvalidEntry);
                }
                ResolvedExprKind::Block(block) => pending.push(Item::Block(block)),
                ResolvedExprKind::Function(function) => pending.push(Item::Block(&function.body)),
                ResolvedExprKind::Apply(application) => {
                    pending.push(Item::Expression(&application.argument));
                    pending.push(Item::Expression(&application.function));
                }
                ResolvedExprKind::Add(binary)
                | ResolvedExprKind::Multiply(binary)
                | ResolvedExprKind::Equal(binary) => {
                    pending.push(Item::Expression(&binary.left));
                    pending.push(Item::Expression(&binary.right));
                }
                ResolvedExprKind::Tuple(elements) => {
                    work.charge(elements.len())
                        .map_err(|()| LifecycleDraftCheckError::Resource)?;
                    pending
                        .try_reserve(elements.len())
                        .map_err(|_| LifecycleDraftCheckError::Resource)?;
                    pending.extend(elements.iter().map(Item::Expression));
                }
                ResolvedExprKind::Match(matched) => {
                    work.charge(matched.arms.len())
                        .map_err(|()| LifecycleDraftCheckError::Resource)?;
                    pending
                        .try_reserve(matched.arms.len().saturating_add(1))
                        .map_err(|_| LifecycleDraftCheckError::Resource)?;
                    pending.push(Item::Expression(&matched.scrutinee));
                    pending.extend(matched.arms.iter().map(|arm| Item::Expression(&arm.body)));
                }
                ResolvedExprKind::Perform(request) => {
                    pending.push(Item::Expression(&request.operand))
                }
                ResolvedExprKind::Integer(_)
                | ResolvedExprKind::Boolean(_)
                | ResolvedExprKind::Unit
                | ResolvedExprKind::Constructor(_) => {}
                ResolvedExprKind::Occurrence(occurrence) => {
                    if include(occurrence) {
                        work.charge(1)
                            .map_err(|()| LifecycleDraftCheckError::Resource)?;
                        found
                            .try_reserve(1)
                            .map_err(|_| LifecycleDraftCheckError::Resource)?;
                        found.push(occurrence);
                    }
                }
            },
        }
    }
    Ok(found)
}
