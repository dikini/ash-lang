//! Immutable allocation and evidence-copy claims for final provider synthesis.
//! No executable Core or implementation selection is produced in this prepass.
use super::PreparedScopeCopyPlan;
use crate::core::provider::ProviderOriginalTemplate;
use crate::elaborate::{
    CoreElaborator, CoreLoweringFamily, EffectElaborator, ElaborationFailure,
    GeneratedTypeVariableRegistry, GeneratedTypeVariableRegistryFailure, TypeError,
    constraint_resource, invalid_state, type_resource,
};
use crate::evidence_validation::{
    CopiedProviderOccurrenceCatalog, SourceProviderOccurrence, copy_provider_occurrences,
};
use crate::interface::LexicalEvidenceId;
use crate::{
    core::NodeId,
    interface::InterfaceConstraintBudget,
    resolved::ResolvedRegistry,
    types::{TypeVariableId, TypeWorkBudget},
};
use std::primitive::u32;
use std::{
    collections::{HashMap, HashSet},
    sync::Arc,
};

pub(crate) struct FinalProviderInstancePlan {
    pub(in crate::elaborate) copyplan: PreparedScopeCopyPlan,
    pub(crate) copies: [CopiedProviderOccurrenceCatalog; 3],
}
pub(crate) struct FinalProviderPreparation {
    registry: Arc<ResolvedRegistry>,
    plans: HashMap<LexicalEvidenceId, Arc<FinalProviderInstancePlan>>,
    binder_cursor_end: u32,
    next_type: u32,
    next_handler: u32,
    next_resume: u32,
    next_lexical: u32,
    generated: GeneratedTypeVariableRegistry,
}
impl std::fmt::Debug for FinalProviderPreparation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("FinalProviderPreparation")
            .field("plans", &self.plans.len())
            .field("generated_slots", &self.generated.len())
            .field("binder_cursor_end", &self.binder_cursor_end)
            .finish()
    }
}
impl FinalProviderPreparation {
    pub(crate) fn plans(&self) -> &HashMap<LexicalEvidenceId, Arc<FinalProviderInstancePlan>> {
        &self.plans
    }
    pub(crate) fn plan(&self, id: LexicalEvidenceId) -> Option<&Arc<FinalProviderInstancePlan>> {
        self.plans.get(&id)
    }
    pub(crate) fn registry(&self) -> &Arc<ResolvedRegistry> {
        &self.registry
    }
    pub(crate) fn apply_to<F: CoreLoweringFamily>(
        self: &Arc<Self>,
        compiler: &mut CoreElaborator<F>,
    ) -> Result<(), ElaborationFailure> {
        if !Arc::ptr_eq(&self.registry, &compiler.registry)
            || compiler.final_provider_preparation.is_some()
            || !compiler.generated_type_variables.0.is_empty()
            || compiler.next_generated_type_variable != u32::MAX
            || compiler.next_handler != 0
            || compiler.next_provider_resume != u32::MAX
            || compiler.next_provider_lexical != u32::MAX
        {
            return Err(ElaborationFailure::InvalidState);
        }
        if F::effect_builder(&mut compiler.builder).is_none() {
            return Err(ElaborationFailure::EffectCoreUnavailable);
        }
        for (index, fact) in self.generated.0.iter().enumerate() {
            let index = u32::try_from(index).map_err(|_| ElaborationFailure::InvalidState)?;
            let id = TypeVariableId::generated(
                u32::MAX
                    .checked_sub(index)
                    .ok_or(ElaborationFailure::InvalidState)?,
            );
            match fact {
                Some(fact) => compiler.generated_type_variables.insert(
                    id,
                    &fact.kind,
                    fact.origin,
                    &mut compiler.type_work,
                ),
                None => compiler
                    .generated_type_variables
                    .skip_reserved(id, &mut compiler.type_work),
            }
            .map_err(|failure| match failure {
                GeneratedTypeVariableRegistryFailure::Resource => {
                    ElaborationFailure::TypeResourceExhausted
                }
                _ => ElaborationFailure::InvalidState,
            })?;
        }
        let builder = F::effect_builder(&mut compiler.builder)
            .ok_or(ElaborationFailure::EffectCoreUnavailable)?;
        crate::core::transform::begin_provider_draft_work(builder, compiler.type_work.remaining());
        let seeded = builder.seed_provider_copy_binder_cursor(self.binder_cursor_end);
        crate::core::transform::discharge_provider_draft_work(builder, &mut compiler.type_work)
            .map_err(ElaborationFailure::from)?;
        seeded.map_err(ElaborationFailure::Core)?;
        compiler.next_generated_type_variable = self.next_type;
        compiler.next_handler = self.next_handler;
        compiler.next_provider_resume = self.next_resume;
        compiler.next_provider_lexical = self.next_lexical;
        compiler
            .type_work
            .charge(1)
            .map_err(|()| ElaborationFailure::TypeResourceExhausted)?;
        compiler.final_provider_preparation = Some(Arc::clone(self));
        Ok(())
    }
}
fn evidence_failure(failure: crate::evidence_validation::EvidenceValidationFailure) -> TypeError {
    match failure.reason() {
        crate::evidence_validation::EvidenceValidationReason::TypeResourceExhausted => {
            type_resource()
        }
        crate::evidence_validation::EvidenceValidationReason::ConstraintResourceExhausted => {
            constraint_resource()
        }
        _ => invalid_state(),
    }
}
pub(crate) fn prepare_final_provider_program(
    program: &crate::resolved::ResolvedModuleProgram,
    basecatalog: Arc<crate::core::dialect::MethodEvidenceCatalog>,
    inventory: &[SourceProviderOccurrence<'_>],
    typework: &mut TypeWorkBudget,
    constraintwork: &mut InterfaceConstraintBudget,
) -> Result<Option<Arc<FinalProviderPreparation>>, TypeError> {
    if inventory.is_empty() {
        return Ok(None);
    }
    let mut compiler = EffectElaborator::for_module_program_inputs(
        program.registry(),
        program.groups(),
        program.result(),
        basecatalog,
    )
    .map_err(TypeError::Internal)?;
    std::mem::swap(&mut compiler.type_work, typework);
    std::mem::swap(&mut compiler.constraint_work, constraintwork);
    let result = (|| {
        compiler
            .type_work
            .charge(inventory.len())
            .map_err(|()| type_resource())?;
        let mut plans = HashMap::new();
        plans
            .try_reserve(inventory.len())
            .map_err(|_| type_resource())?;
        for occurrence in inventory {
            let prepared = occurrence
                .resource
                .prepared
                .get()
                .ok_or_else(invalid_state)?;
            if prepared.provider() != occurrence.resource.provider
                || plans.contains_key(&prepared.provider())
            {
                return Err(invalid_state());
            }
            let source = prepared.code.template_source(
                prepared.definition.id,
                prepared.definition.family,
                program.registry(),
                &mut compiler.type_work,
            )?;
            let copyplan = compiler.prepare_scope_copy_plan(
                &source,
                &prepared.actuals,
                &prepared.body,
                &prepared.handler_rows,
                prepared.provider().module(),
                occurrence.span,
            )?;
            let originals = [
                ProviderOriginalTemplate::Lifecycle(
                    source.acquire.original,
                    source.acquire.program,
                ),
                ProviderOriginalTemplate::Lifecycle(source.finish.original, source.finish.program),
                ProviderOriginalTemplate::Handler(source.handler),
            ];
            let acquire = copy_provider_occurrences(
                originals[0],
                &copyplan.phases[0].context(),
                occurrence.span,
                &mut compiler.constraint_work,
                &mut compiler.type_work,
            )
            .map_err(evidence_failure)?;
            let finish = copy_provider_occurrences(
                originals[1],
                &copyplan.phases[1].context(),
                occurrence.span,
                &mut compiler.constraint_work,
                &mut compiler.type_work,
            )
            .map_err(evidence_failure)?;
            let handler = copy_provider_occurrences(
                originals[2],
                &copyplan.phases[2].context(),
                occurrence.span,
                &mut compiler.constraint_work,
                &mut compiler.type_work,
            )
            .map_err(evidence_failure)?;
            compiler.type_work.charge(1).map_err(|()| type_resource())?;
            plans.insert(
                prepared.provider(),
                Arc::new(FinalProviderInstancePlan {
                    copyplan,
                    copies: [acquire, finish, handler],
                }),
            );
        }
        compiler.type_work.charge(1).map_err(|()| type_resource())?;
        let preparation = FinalProviderPreparation {
            registry: Arc::clone(program.registry()),
            plans,
            binder_cursor_end: compiler.builder.provider_copy_binder_cursor(),
            next_type: compiler.next_generated_type_variable,
            next_handler: compiler.next_handler,
            next_resume: compiler.next_provider_resume,
            next_lexical: compiler.next_provider_lexical,
            generated: std::mem::take(&mut compiler.generated_type_variables),
        };
        Ok(Some(Arc::new(preparation)))
    })();
    std::mem::swap(&mut compiler.type_work, typework);
    std::mem::swap(&mut compiler.constraint_work, constraintwork);
    result
}

/// Derives final scalar catalogue addresses from the frozen copied occurrence
/// keys. Adapter producer nodes remain original addresses until the shared
/// forest copier resolves its complete source-to-target node relation.
pub(crate) fn final_provider_catalog_relocations(
    original: &crate::core::UnvalidatedEffectProgram,
    roots: &[NodeId],
    phase: &super::copy::PreparedPhaseCopy,
    copied: &CopiedProviderOccurrenceCatalog,
    target: &crate::core::dialect::MethodEvidenceCatalog,
    work: &mut TypeWorkBudget,
) -> Result<Vec<crate::core::provider::ProviderCatalogRelocation>, TypeError> {
    use crate::core::dialect::{
        MethodEvidenceAnchorRole as Role, MethodEvidenceOwner as Owner,
        MethodEvidenceProducer as Producer,
    };
    let context = phase.context();
    if !Arc::ptr_eq(original.method_evidence(), &copied.original_catalog) {
        return Err(invalid_state());
    }
    let order =
        crate::core::transform::provider_entry_forest_order(original, roots, &HashSet::new(), work)
            .map_err(|failure| match failure {
                crate::core::transform::TransformError::Build(error) => {
                    TypeError::Internal(error.into())
                }
                _ => invalid_state(),
            })?;
    work.charge(order.len()).map_err(|()| type_resource())?;
    let mut reachable = HashSet::new();
    reachable
        .try_reserve(order.len())
        .map_err(|_| type_resource())?;
    reachable.extend(order);
    fn owner(
        owner: Option<Owner>,
        context: &crate::core::provider::ProviderCopyContext<'_>,
        work: &mut TypeWorkBudget,
    ) -> Result<Option<Owner>, TypeError> {
        owner
            .map(|owner| {
                Ok(match owner {
                    Owner::Global(binder) => Owner::Global(context.binder(binder, work)?),
                    other => other,
                })
            })
            .transpose()
    }
    fn producer(
        producer: Producer,
        context: &crate::core::provider::ProviderCopyContext<'_>,
        work: &mut TypeWorkBudget,
    ) -> Result<Producer, TypeError> {
        Ok(match producer {
            Producer::Lexical { source } => Producer::Lexical {
                source: context.lexical(source, work)?,
            },
            other => other,
        })
    }
    work.charge(original.method_evidence_anchors().len())
        .map_err(|()| type_resource())?;
    let mut output = Vec::new();
    output
        .try_reserve_exact(original.method_evidence_anchors().len())
        .map_err(|_| type_resource())?;
    for (original_anchor, anchor) in original.method_evidence_anchors().iter().enumerate() {
        if !reachable.contains(&anchor.node) {
            continue;
        }
        let occurrence = anchor
            .occurrence
            .map(|old| {
                work.charge(copied.relocations.len())
                    .map_err(|()| type_resource())?;
                let mut matches = copied
                    .relocations
                    .iter()
                    .filter(|relation| relation.original == old);
                let fresh = matches.next().ok_or_else(invalid_state)?.copied;
                if matches.next().is_some() {
                    return Err(invalid_state());
                }
                work.charge(copied.occurrences.len())
                    .map_err(|()| type_resource())?;
                let copied_occurrence = copied
                    .occurrences
                    .iter()
                    .find(|occurrence| occurrence.slot == fresh)
                    .ok_or_else(invalid_state)?;
                let actual = target.occurrence(fresh).ok_or_else(invalid_state)?;
                if !actual
                    .selection
                    .same_original_owner(&copied_occurrence.selection)
                    || actual.scope != copied_occurrence.scope
                    || actual.scope_binder != copied_occurrence.scope_binder
                    || actual.target_owner != copied_occurrence.target_owner
                    || actual.target_requirement != copied_occurrence.target_requirement
                    || actual.checked_method != copied_occurrence.checked_method
                    || actual.checked_application.interface()
                        != copied_occurrence.checked_application.interface()
                    || actual.checked_application.arguments().len()
                        != copied_occurrence.checked_application.arguments().len()
                    || actual.method_arguments.len() != copied_occurrence.method_arguments.len()
                {
                    return Err(invalid_state());
                }
                for (actual, expected) in actual
                    .checked_application
                    .arguments()
                    .iter()
                    .zip(copied_occurrence.checked_application.arguments())
                {
                    if !crate::types::same_kinded_argument_with_budget(actual, expected, work)
                        .map_err(|()| type_resource())?
                    {
                        return Err(invalid_state());
                    }
                }
                match (
                    &actual.checked_value_type,
                    &copied_occurrence.checked_value_type,
                ) {
                    (Some(actual), Some(expected)) => {
                        if !crate::types::same_type_with_budget(actual, expected, work)
                            .map_err(|()| type_resource())?
                        {
                            return Err(invalid_state());
                        }
                    }
                    (None, None) => {}
                    _ => return Err(invalid_state()),
                }
                if actual.selection.interface() != copied_occurrence.selection.interface()
                    || actual.selection.arguments().len()
                        != copied_occurrence.selection.arguments().len()
                {
                    return Err(invalid_state());
                }
                for (actual, expected) in actual
                    .selection
                    .arguments()
                    .iter()
                    .zip(copied_occurrence.selection.arguments())
                {
                    if !crate::types::same_kinded_argument_with_budget(actual, expected, work)
                        .map_err(|()| type_resource())?
                    {
                        return Err(invalid_state());
                    }
                }
                for (actual, expected) in actual
                    .method_arguments
                    .iter()
                    .zip(copied_occurrence.method_arguments.iter())
                {
                    if !crate::types::same_type_with_budget(actual, expected, work)
                        .map_err(|()| type_resource())?
                    {
                        return Err(invalid_state());
                    }
                }
                Ok(fresh)
            })
            .transpose()?;
        let role = match anchor.role {
            Role::LexicalCaptureUse { owner, ordinal } => {
                let original_owner = original
                    .method_evidence()
                    .lexical_owners()
                    .get(owner)
                    .ok_or_else(invalid_state)?;
                let source = context.lexical(original_owner.source, work)?;
                let binder = context.binder(original_owner.binder, work)?;
                work.charge(target.lexical_owners().len())
                    .map_err(|()| type_resource())?;
                let mut owners = target
                    .lexical_owners()
                    .iter()
                    .enumerate()
                    .filter(|(_, owner)| {
                        owner.source == source
                            && owner.method == original_owner.method
                            && owner.binder == binder
                    });
                let (owner, actual) = owners.next().ok_or_else(invalid_state)?;
                if owners.next().is_some() || ordinal >= actual.captures.len() {
                    return Err(invalid_state());
                }
                let original_capture = *original_owner
                    .captures
                    .get(ordinal)
                    .ok_or_else(invalid_state)?;
                if actual.captures[ordinal] != context.binder(original_capture, work)? {
                    return Err(invalid_state());
                }
                Role::LexicalCaptureUse { owner, ordinal }
            }
            Role::LexicalOwner { source, binder } => Role::LexicalOwner {
                source: context.lexical(source, work)?,
                binder: context.binder(binder, work)?,
            },
            Role::LexicalUse {
                source,
                binder,
                selection_node,
            } => Role::LexicalUse {
                source: context.lexical(source, work)?,
                binder: context.binder(binder, work)?,
                selection_node,
            },
            Role::ImplementationOwner {
                implementation,
                binder,
            } => Role::ImplementationOwner {
                implementation,
                binder: context.binder(binder, work)?,
            },
            Role::Domain { binder } => Role::Domain {
                binder: context.binder(binder, work)?,
            },
            Role::Application { producer: original } => Role::Application {
                producer: producer(original, &context, work)?,
            },
            Role::Instantiation { binder } => Role::Instantiation {
                binder: binder.map(|id| context.binder(id, work)).transpose()?,
            },
            Role::AdapterEdge {
                adapter,
                adapter_selection_node,
                ordinal,
                producer_node,
                producer_selection_node,
                producer_binder,
                producer: original,
            } => {
                if !reachable.contains(&producer_node) {
                    return Err(invalid_state());
                }
                Role::AdapterEdge {
                    adapter,
                    adapter_selection_node,
                    ordinal,
                    producer_node,
                    producer_selection_node,
                    producer_binder: producer_binder
                        .map(|id| context.binder(id, work))
                        .transpose()?,
                    producer: producer(original, &context, work)?,
                }
            }
            other => other,
        };
        output.push(crate::core::provider::ProviderCatalogRelocation {
            original_anchor,
            owner: owner(anchor.owner, &context, work)?,
            requirement: anchor.requirement,
            occurrence,
            role,
        });
    }
    Ok(output)
}
