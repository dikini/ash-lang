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
    pub(crate) family_copies: Box<[CopiedProviderOccurrenceCatalog]>,
    pub(crate) family_members: Box<[Arc<super::PreparedProviderFamilyInstance>]>,
    family_relocations: Box<[FinalFamilyForwardingRelocation]>,
}
// A private original-to-final member relation, minted only while allocating
// final forwardings. The original payload is retained once; the final payload
// remains owned by the plan's existing family_members vector.
struct FinalFamilyForwardingRelocation {
    original: Arc<super::PreparedProviderFamilyInstance>,
    member: usize,
}

fn same_family_application(
    left: &crate::interface::InterfaceApplication,
    right: &crate::interface::InterfaceApplication,
    work: &mut TypeWorkBudget,
) -> Result<bool, TypeError> {
    if left.interface() != right.interface() || left.arguments().len() != right.arguments().len() {
        return Ok(false);
    }
    work.charge(left.arguments().len())
        .map_err(|()| type_resource())?;
    for (left, right) in left.arguments().iter().zip(right.arguments()) {
        if !crate::types::same_kinded_argument_with_budget(left, right, work)
            .map_err(|()| type_resource())?
        {
            return Ok(false);
        }
    }
    Ok(true)
}

fn authenticate_family_forwarding_pair(
    original: &super::PreparedProviderFamilyInstance,
    final_member: &super::PreparedProviderFamilyInstance,
    work: &mut TypeWorkBudget,
) -> Result<(), TypeError> {
    use crate::{resolved::BinderId, source::Origin};
    if original.source != final_member.source
        || original.identity != final_member.identity
        || original.forwardings.is_empty()
        || original.selections.is_empty()
        || original.forwardings.len() != final_member.forwardings.len()
        || original.requirements.len() != final_member.requirements.len()
        || original.selections.len() != final_member.selections.len()
        || !matches!(
            &*original.payload,
            crate::types::Type::Unit | crate::types::Type::Bool | crate::types::Type::Int
        )
        || !same_family_application(&original.application, &final_member.application, work)?
        || !crate::types::same_type_with_budget(&original.payload, &final_member.payload, work)
            .map_err(|()| type_resource())?
        || crate::types::compare_effect_instances_with_budget(
            &original.provided,
            &final_member.provided,
            work,
        )
        .map_err(|()| type_resource())?
            != std::cmp::Ordering::Equal
        || crate::types::compare_effect_instances_with_budget(
            &original.native,
            &final_member.native,
            work,
        )
        .map_err(|()| type_resource())?
            != std::cmp::Ordering::Equal
    {
        return Err(invalid_state());
    }
    work.charge(
        original
            .requirements
            .len()
            .checked_add(original.selections.len())
            .and_then(|count| count.checked_add(original.forwardings.len()))
            .ok_or_else(type_resource)?,
    )
    .map_err(|()| type_resource())?;
    for ((left, left_node), (right, right_node)) in original
        .requirements
        .iter()
        .zip(&final_member.requirements)
        .chain(original.selections.iter().zip(&final_member.selections))
    {
        if left_node != right_node || left.root() != right.root() || !left.shares_plan_with(right) {
            return Err(invalid_state());
        }
    }
    for (index, ((method, operation, binder), (final_method, final_operation, final_binder))) in
        original
            .forwardings
            .iter()
            .zip(&final_member.forwardings)
            .enumerate()
    {
        work.charge(index.checked_mul(2).ok_or_else(type_resource)?)
            .map_err(|()| type_resource())?;
        if method != final_method
            || operation != final_operation
            || method.interface() != original.application.interface()
            || !matches!(binder.id(), BinderId::Generated(_))
            || !matches!(final_binder.id(), BinderId::Generated(_))
            || original.forwardings[..index]
                .iter()
                .any(|(previous, _, previous_binder)| {
                    previous == method || previous_binder.id() == binder.id()
                })
            || final_member.forwardings[..index]
                .iter()
                .any(|(_, _, previous)| previous.id() == final_binder.id())
            || !matches!((binder.origin(), final_binder.origin()),
                (Origin::Source(left), Origin::Source(right)) if left == right)
            || !crate::types::same_type_with_budget(binder.ty(), final_binder.ty(), work)
                .map_err(|()| type_resource())?
        {
            return Err(invalid_state());
        }
    }
    for (index, (selection, node)) in original.selections.iter().enumerate() {
        work.charge(index).map_err(|()| type_resource())?;
        if original.selections[..index]
            .iter()
            .any(|(previous, previous_node)| {
                previous_node == node
                    && previous.root() == selection.root()
                    && previous.shares_plan_with(selection)
            })
        {
            return Err(invalid_state());
        }
        // Every retained occurrence must describe the whole canonical method
        // vector, even when a caller later requests only one forwarding.
        authenticate_family_forwarding_claim(
            original,
            selection,
            *node,
            original.forwardings[0].0,
            work,
        )?;
    }
    Ok(())
}

fn authenticate_family_forwarding_claim(
    original: &super::PreparedProviderFamilyInstance,
    selection: &crate::interface::EvidenceSelection,
    node: crate::interface::EvidenceNodeId,
    method: crate::interface::MethodId,
    work: &mut TypeWorkBudget,
) -> Result<usize, TypeError> {
    use crate::interface::EvidenceNode;
    let Some(EvidenceNode::ProviderFamily {
        source,
        definition,
        parameter,
        application,
        prerequisites,
        methods,
    }) = selection.node(node)
    else {
        return Err(invalid_state());
    };
    if source != original.source
        || definition != original.identity.definition
        || parameter != original.identity.parameter
        || !same_family_application(application, &original.application, work)?
        || methods.len() != original.forwardings.len()
        || prerequisites.len() != original.requirements.len()
    {
        return Err(invalid_state());
    }
    work.charge(
        original
            .selections
            .len()
            .checked_add(methods.len())
            .and_then(|count| count.checked_add(prerequisites.len()))
            .ok_or_else(type_resource)?,
    )
    .map_err(|()| type_resource())?;
    let mut recorded = false;
    for (retained, retained_node) in &original.selections {
        if *retained_node == node
            && retained.root() == selection.root()
            && retained.shares_plan_with(selection)
        {
            if recorded {
                return Err(invalid_state());
            }
            recorded = true;
        }
    }
    if !recorded {
        return Err(invalid_state());
    }
    let mut selected = None;
    for (index, (selected_method, (forwarded_method, _, _))) in
        methods.iter().zip(&original.forwardings).enumerate()
    {
        if selected_method != forwarded_method {
            return Err(invalid_state());
        }
        if *selected_method == method && selected.replace(index).is_some() {
            return Err(invalid_state());
        }
    }
    let (first, first_node) = original.selections.first().ok_or_else(invalid_state)?;
    let Some(EvidenceNode::ProviderFamily {
        prerequisites: first_prerequisites,
        ..
    }) = first.node(*first_node)
    else {
        return Err(invalid_state());
    };
    if first_prerequisites.len() != original.requirements.len() {
        return Err(invalid_state());
    }
    for (((retained, retained_node), actual), first_prerequisite) in original
        .requirements
        .iter()
        .zip(prerequisites)
        .zip(first_prerequisites)
    {
        if retained_node != first_prerequisite
            || retained_node.index() >= first_node.index()
            || actual.index() >= node.index()
            || retained.root() != first.root()
            || !retained.shares_plan_with(first)
        {
            return Err(invalid_state());
        }
        let Some(EvidenceNode::NativeLayout { producer: expected }) = retained.node(*retained_node)
        else {
            return Err(invalid_state());
        };
        let Some(EvidenceNode::NativeLayout { producer: actual }) = selection.node(*actual) else {
            return Err(invalid_state());
        };
        if expected != actual {
            return Err(invalid_state());
        }
    }
    selected.ok_or_else(invalid_state)
}

fn retain_family_forwarding_relocations(
    primary: LexicalEvidenceId,
    source: Option<LexicalEvidenceId>,
    identity: Option<crate::core::provider::ProviderFamilyIdentity>,
    methods: Option<&[(crate::interface::MethodId, crate::types::OperationId)]>,
    originals: &[Arc<super::PreparedProviderFamilyInstance>],
    finals: &[Arc<super::PreparedProviderFamilyInstance>],
    work: &mut TypeWorkBudget,
) -> Result<Box<[FinalFamilyForwardingRelocation]>, TypeError> {
    if originals.is_empty() && finals.is_empty() {
        return Ok(Box::new([]));
    }
    if originals.len() != finals.len() {
        return Err(invalid_state());
    }
    let source = source.ok_or_else(invalid_state)?;
    let identity = identity.ok_or_else(invalid_state)?;
    let methods = methods.ok_or_else(invalid_state)?;
    if methods.is_empty() {
        return Err(invalid_state());
    }
    if primary == source || primary.module() != source.module() {
        return Err(invalid_state());
    }
    work.charge(originals.len()).map_err(|()| type_resource())?;
    let mut relations = Vec::new();
    relations
        .try_reserve_exact(originals.len())
        .map_err(|_| type_resource())?;
    for (member, (original, final_member)) in originals.iter().zip(finals).enumerate() {
        if original.source != source
            || original.identity != identity
            || original.forwardings.len() != methods.len()
        {
            return Err(invalid_state());
        }
        work.charge(methods.len()).map_err(|()| type_resource())?;
        for ((method, operation, _), (canonical_method, canonical_operation)) in
            original.forwardings.iter().zip(methods)
        {
            if method != canonical_method || operation != canonical_operation {
                return Err(invalid_state());
            }
        }
        work.charge(member).map_err(|()| type_resource())?;
        for previous in &originals[..member] {
            if Arc::ptr_eq(previous, original)
                || same_family_application(&previous.application, &original.application, work)?
            {
                return Err(invalid_state());
            }
        }
        authenticate_family_forwarding_pair(original, final_member, work)?;
        relations.push(FinalFamilyForwardingRelocation {
            original: Arc::clone(original),
            member,
        });
    }
    Ok(relations.into_boxed_slice())
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
    /// Authenticates an original frozen family claim before returning its
    /// genuinely allocated final forwarding identity. Claims never supply a map.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn relocate_family_forwarding(
        &self,
        selection: &crate::interface::EvidenceSelection,
        node: crate::interface::EvidenceNodeId,
        method: crate::interface::MethodId,
        source: LexicalEvidenceId,
        member: usize,
        original_binder: crate::resolved::BinderId,
        work: &mut TypeWorkBudget,
    ) -> Result<crate::resolved::BinderId, TypeError> {
        work.charge(self.plans.len())
            .map_err(|()| type_resource())?;
        let mut selected = None;
        for (primary, plan) in &self.plans {
            work.charge(plan.family_relocations.len())
                .map_err(|()| type_resource())?;
            if plan.family_relocations.len() != plan.family_members.len() {
                return Err(invalid_state());
            }
            for relation in &plan.family_relocations {
                if relation.original.source != source || relation.member != member {
                    continue;
                }
                if *primary == source || primary.module() != source.module() {
                    return Err(invalid_state());
                }
                let final_member = plan.family_members.get(member).ok_or_else(invalid_state)?;
                // The complete pair was authenticated at private construction.
                // Both member Arcs are immutable; readers check the current
                // occurrence claim without walking every retained receipt again.
                let method_index = authenticate_family_forwarding_claim(
                    &relation.original,
                    selection,
                    node,
                    method,
                    work,
                )?;
                if relation.original.forwardings[method_index].2.id() != original_binder
                    || selected
                        .replace(final_member.forwardings[method_index].2.id())
                        .is_some()
                {
                    return Err(invalid_state());
                }
            }
        }
        selected.ok_or_else(invalid_state)
    }
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
        TypeWorkBudget::default(),
    )
    .map_err(TypeError::Internal)?;
    std::mem::swap(&mut compiler.type_work, typework);
    std::mem::swap(&mut compiler.constraint_work, constraintwork);
    let result = (|| {
        compiler
            .type_work
            .charge(inventory.len())
            .map_err(|()| type_resource())?;
        let mut plans = HashMap::<LexicalEvidenceId, Arc<FinalProviderInstancePlan>>::new();
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
            let copyplan = if prepared.family_members.is_empty() {
                if !prepared.family_rows.is_empty() {
                    return Err(invalid_state());
                }
                compiler.prepare_scope_copy_plan(
                    &source,
                    &prepared.actuals,
                    &prepared.body,
                    &prepared.handler_rows,
                    prepared.provider().module(),
                    occurrence.span,
                )?
            } else {
                compiler.prepare_scope_copy_plan_with_family_rows(
                    &source,
                    &prepared.actuals,
                    &prepared.body,
                    &prepared.handler_rows,
                    &prepared.family_members,
                    &prepared.family_rows,
                    prepared.provider().module(),
                    occurrence.span,
                )?
            };
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
            let family_copies: Box<[CopiedProviderOccurrenceCatalog]> =
                if copyplan.family_phases.is_empty() {
                    Box::new([])
                } else {
                    let family = source.family.as_ref().ok_or_else(invalid_state)?;
                    if copyplan.family_phases.len() != prepared.family_members.len() {
                        return Err(invalid_state());
                    }
                    compiler
                        .type_work
                        .charge(copyplan.family_phases.len())
                        .map_err(|()| type_resource())?;
                    let mut copies = Vec::new();
                    copies
                        .try_reserve_exact(copyplan.family_phases.len())
                        .map_err(|_| type_resource())?;
                    for phase in &copyplan.family_phases {
                        copies.push(
                            copy_provider_occurrences(
                                ProviderOriginalTemplate::Handler(family.handler),
                                &phase.context(),
                                occurrence.span,
                                &mut compiler.constraint_work,
                                &mut compiler.type_work,
                            )
                            .map_err(evidence_failure)?,
                        );
                    }
                    copies.into_boxed_slice()
                };
            let family_members = compiler.prepare_final_family_members(&prepared.family_members)?;
            let family_relocations = retain_family_forwarding_relocations(
                prepared.provider(),
                occurrence.resource.family_provider,
                source.family.as_ref().map(|family| family.identity),
                source.family.as_ref().map(|family| family.methods),
                &prepared.family_members,
                &family_members,
                &mut compiler.type_work,
            )?;
            if let Some(first) = family_relocations.first() {
                // A family lexical source belongs to exactly one prepared scope.
                compiler
                    .type_work
                    .charge(plans.len())
                    .map_err(|()| type_resource())?;
                for existing in plans.values() {
                    compiler
                        .type_work
                        .charge(existing.family_relocations.len())
                        .map_err(|()| type_resource())?;
                    if existing
                        .family_relocations
                        .iter()
                        .any(|relation| relation.original.source == first.original.source)
                    {
                        return Err(invalid_state());
                    }
                }
            }
            compiler.type_work.charge(1).map_err(|()| type_resource())?;
            plans.insert(
                prepared.provider(),
                Arc::new(FinalProviderInstancePlan {
                    copyplan,
                    copies: [acquire, finish, handler],
                    family_copies,
                    family_members,
                    family_relocations,
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
            Producer::ProviderFamily {
                source,
                member,
                binder,
            } => Producer::ProviderFamily {
                source: context.lexical(source, work)?,
                member,
                binder: context.binder(binder, work)?,
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
            Role::ProviderFamilyUse {
                source,
                member,
                selection_node,
                binder,
            } => Role::ProviderFamilyUse {
                source: context.lexical(source, work)?,
                member,
                selection_node,
                binder: context.binder(binder, work)?,
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
