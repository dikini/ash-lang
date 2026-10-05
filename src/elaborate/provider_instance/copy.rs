//! One frozen occurrence plan for genuine source and final template copies.
//! Plans are compiler claims; only independent final Core admission supplies
//! execution authority. Source capture uses the same copied typed forests.

use super::{
    CoreElaborator, CoreLoweringFamily, OwnerReplacementBuffer, ResourceActuals, TypeError,
    invalid_state, type_resource,
};
use crate::core::provider::{
    ProviderCatalogRelocation, ProviderCopiedForest, ProviderCopyContext, ProviderFreshening,
    ProviderLifecycleEntry, ProviderOriginalTemplate, ProviderTemplateSubstitution,
};
use crate::core::{EffectClause, HandlerId};
use crate::elaborate::generated_type_variable_registry_error;
use crate::interface::LexicalEvidenceId;
use crate::resolved::ResumeId;
use crate::types::{InferenceVariableId, NominalTypeId};
use crate::{
    core::{NodeId, TypedBinder},
    resolved::BinderId,
    source::Span,
    types::{
        ComputationType, EffectRow, EffectRowVariable, Kind, Type, TypeStructureNode,
        TypeVariableId, TypeWorkBudget, clone_effect_row_with_budget,
    },
};
use std::collections::{HashMap, HashSet};

pub(in crate::elaborate) struct PreparedPhaseCopy {
    pub(in crate::elaborate) sigma: OwnerReplacementBuffer,
    pub(in crate::elaborate) pending: HashMap<InferenceVariableId, EffectRow>,
    node_rows: HashMap<NodeId, EffectRow>,
    binders: HashMap<BinderId, BinderId>,
    variables: HashMap<TypeVariableId, TypeVariableId>,
    handlers: HashMap<HandlerId, HandlerId>,
    resumes: HashMap<ResumeId, ResumeId>,
    nominals: HashMap<NominalTypeId, NominalTypeId>,
    lexicals: HashMap<LexicalEvidenceId, LexicalEvidenceId>,
    binder_pairs: Vec<(BinderId, BinderId)>,
    type_pairs: Vec<(TypeVariableId, TypeVariableId, Kind)>,
    handler_pairs: Vec<(HandlerId, HandlerId)>,
    resume_pairs: Vec<(ResumeId, ResumeId)>,
    nominal_pairs: Vec<(NominalTypeId, NominalTypeId)>,
    lexical_pairs: Vec<(LexicalEvidenceId, LexicalEvidenceId)>,
}
impl PreparedPhaseCopy {
    fn empty() -> Self {
        Self {
            sigma: OwnerReplacementBuffer::new(),
            pending: HashMap::new(),
            node_rows: HashMap::new(),
            binders: HashMap::new(),
            variables: HashMap::new(),
            handlers: HashMap::new(),
            resumes: HashMap::new(),
            nominals: HashMap::new(),
            lexicals: HashMap::new(),
            binder_pairs: Vec::new(),
            type_pairs: Vec::new(),
            handler_pairs: Vec::new(),
            resume_pairs: Vec::new(),
            nominal_pairs: Vec::new(),
            lexical_pairs: Vec::new(),
        }
    }
    pub(in crate::elaborate) fn substitution(&self) -> ProviderTemplateSubstitution<'_> {
        ProviderTemplateSubstitution {
            types: self.sigma.types.as_map(),
            rows: &self.sigma.rows,
            pending: &self.pending,
        }
    }
    pub(in crate::elaborate) fn node_rows(&self) -> &HashMap<NodeId, EffectRow> {
        &self.node_rows
    }
    pub(in crate::elaborate) fn freshening(&self) -> ProviderFreshening<'_> {
        ProviderFreshening {
            binders: &self.binder_pairs,
            types: &self.type_pairs,
            handlers: &self.handler_pairs,
            resumes: &self.resume_pairs,
            nominals: &self.nominal_pairs,
            lexicals: &self.lexical_pairs,
        }
    }
    pub(in crate::elaborate) fn context(&self) -> ProviderCopyContext<'_> {
        ProviderCopyContext {
            types: self.sigma.types.as_map(),
            rows: &self.sigma.rows,
            pending: &self.pending,
            node_rows: &self.node_rows,
            binders: &self.binders,
            variables: &self.variables,
            handlers: &self.handlers,
            resumes: &self.resumes,
            nominals: &self.nominals,
            lexicals: &self.lexicals,
        }
    }
}
pub(in crate::elaborate) struct PreparedScopeCopyPlan {
    pub(in crate::elaborate) phases: [PreparedPhaseCopy; 3],
}
pub(in crate::elaborate) struct ScopeCopiedEntries {
    pub(in crate::elaborate) acquire: ProviderLifecycleEntry,
    pub(in crate::elaborate) finish: ProviderLifecycleEntry,
    pub(in crate::elaborate) state: TypedBinder,
    pub(in crate::elaborate) handler: HandlerId,
    pub(in crate::elaborate) clauses: Vec<EffectClause>,
    pub(in crate::elaborate) forests: [ProviderCopiedForest; 3],
}

fn reserve_pair<K: Eq + std::hash::Hash + Copy>(
    map: &mut HashMap<K, K>,
    pairs: &mut Vec<(K, K)>,
    count: usize,
    work: &mut TypeWorkBudget,
) -> Result<(), TypeError> {
    work.charge(count.checked_mul(2).ok_or_else(type_resource)?)
        .map_err(|()| type_resource())?;
    map.try_reserve(count).map_err(|_| type_resource())?;
    pairs
        .try_reserve_exact(count)
        .map_err(|_| type_resource())?;
    Ok(())
}
fn insert_pair<K: Eq + std::hash::Hash + Copy>(
    map: &mut HashMap<K, K>,
    pairs: &mut Vec<(K, K)>,
    old: K,
    new: K,
) -> Result<(), TypeError> {
    if old == new || map.insert(old, new).is_some() {
        return Err(invalid_state());
    }
    pairs.push((old, new));
    Ok(())
}
fn validation(error: crate::core::ValidationError) -> TypeError {
    if error.reason() == crate::core::ValidationReason::Resource {
        type_resource()
    } else {
        invalid_state()
    }
}

fn retain_payload_variable(
    id: TypeVariableId,
    forbidden: &mut HashSet<TypeVariableId>,
    work: &mut TypeWorkBudget,
) -> Result<(), ()> {
    work.charge(1)?;
    if !forbidden.contains(&id) {
        forbidden.try_reserve(1).map_err(|_| ())?;
        forbidden.insert(id);
    }
    Ok(())
}
fn inspect_payload_variable(
    node: TypeStructureNode<'_>,
    forbidden: &mut HashSet<TypeVariableId>,
    work: &mut TypeWorkBudget,
) -> Result<bool, ()> {
    match node {
        TypeStructureNode::Type(Type::Variable(id)) => {
            retain_payload_variable(*id, forbidden, work)?
        }
        TypeStructureNode::Type(Type::Forall(parameters, _)) => {
            for (parameter, _) in parameters {
                retain_payload_variable(*parameter, forbidden, work)?;
            }
        }
        TypeStructureNode::Tail(tail) => {
            if let EffectRowVariable::Rigid(id) = tail.variable() {
                retain_payload_variable(id, forbidden, work)?;
            }
        }
        _ => {}
    }
    Ok(false)
}
fn retain_type_payload_variables(
    root: &Type,
    forbidden: &mut HashSet<TypeVariableId>,
    work: &mut TypeWorkBudget,
) -> Result<(), TypeError> {
    crate::types::visit_type_structure_with_budget(root, work, |node, work| {
        inspect_payload_variable(node, forbidden, work)
    })
    .map_err(|()| type_resource())?;
    Ok(())
}
fn retain_row_payload_variables(
    row: &EffectRow,
    forbidden: &mut HashSet<TypeVariableId>,
    work: &mut TypeWorkBudget,
) -> Result<(), TypeError> {
    let members = row
        .known()
        .len()
        .checked_add(row.tail().map_or(0, |tail| tail.lacks().len()))
        .and_then(|n| n.checked_add(1))
        .ok_or_else(type_resource)?;
    work.charge(members).map_err(|()| type_resource())?;
    if let Some(tail) = row.tail() {
        work.charge(1).map_err(|()| type_resource())?;
        if let EffectRowVariable::Rigid(id) = tail.variable() {
            retain_payload_variable(id, forbidden, work).map_err(|()| type_resource())?;
        }
    }
    for instance in row
        .known()
        .iter()
        .chain(row.tail().into_iter().flat_map(|tail| tail.lacks()))
    {
        for argument in instance.arguments() {
            crate::types::visit_argument_structure_with_budget(argument, work, |node, work| {
                inspect_payload_variable(node, forbidden, work)
            })
            .map_err(|()| type_resource())?;
        }
    }
    Ok(())
}

impl<F: CoreLoweringFamily> CoreElaborator<F> {
    pub(in crate::elaborate) fn prepare_scope_copy_plan(
        &mut self,
        source: &super::super::provider::ProviderTemplateSource<'_>,
        actuals: &ResourceActuals,
        body: &ComputationType,
        rows: &crate::core::provider::ResolvedProviderHandlerRows,
        module: crate::module::ModuleId,
        origin: Span,
    ) -> Result<PreparedScopeCopyPlan, TypeError> {
        if actuals.arguments().len() != source.fact.parameters.len() {
            return Err(invalid_state());
        }
        let originals = [
            ProviderOriginalTemplate::Lifecycle(source.acquire.original, source.acquire.program),
            ProviderOriginalTemplate::Lifecycle(source.finish.original, source.finish.program),
            ProviderOriginalTemplate::Handler(source.handler),
        ];
        let mut phases = [
            PreparedPhaseCopy::empty(),
            PreparedPhaseCopy::empty(),
            PreparedPhaseCopy::empty(),
        ];
        for (index, phase) in phases.iter_mut().enumerate() {
            match originals[index] {
                ProviderOriginalTemplate::Lifecycle(original, _) => {
                    if original.formals().len() != actuals.arguments().len() {
                        return Err(invalid_state());
                    }
                    for ((_, generated, _), actual) in
                        original.formals().iter().zip(actuals.arguments())
                    {
                        phase
                            .sigma
                            .insert_cloned(*generated, actual, &mut self.type_work)?;
                    }
                }
                ProviderOriginalTemplate::Handler(_) => {
                    for (formal, actual) in source.fact.parameters.iter().zip(actuals.arguments()) {
                        phase
                            .sigma
                            .insert_cloned(formal.id, actual, &mut self.type_work)?;
                    }
                }
            }
            let hidden = match originals[index] {
                ProviderOriginalTemplate::Lifecycle(original, _) => original.hidden(),
                ProviderOriginalTemplate::Handler(original) => original.original_hidden(),
            };
            if hidden[0].1 != Kind::Type || hidden[1].1 != Kind::EffectRow {
                return Err(invalid_state());
            }
            let value = crate::types::IterativeArgumentOwner::new(
                crate::types::KindedArgument::TypeArg(self.clone_type(body.value())?),
            );
            phase
                .sigma
                .insert_cloned(hidden[0].0, &value, &mut self.type_work)?;
            let row =
                crate::types::IterativeArgumentOwner::new(crate::types::KindedArgument::RowArg(
                    clone_effect_row_with_budget(rows.residual(), &mut self.type_work)
                        .map_err(|()| type_resource())?,
                ));
            phase
                .sigma
                .insert_cloned(hidden[1].0, &row, &mut self.type_work)?;
            if index == 2 {
                self.type_work
                    .charge(rows.pending().len())
                    .map_err(|()| type_resource())?;
                phase
                    .pending
                    .try_reserve(rows.pending().len())
                    .map_err(|_| type_resource())?;
                for (id, row) in rows.pending() {
                    phase.pending.insert(
                        *id,
                        clone_effect_row_with_budget(row, &mut self.type_work)
                            .map_err(|()| type_resource())?,
                    );
                }
                self.type_work
                    .charge(rows.node_rows().len())
                    .map_err(|()| type_resource())?;
                phase
                    .node_rows
                    .try_reserve(rows.node_rows().len())
                    .map_err(|_| type_resource())?;
                for (node, row) in rows.node_rows() {
                    phase.node_rows.insert(
                        *node,
                        clone_effect_row_with_budget(row, &mut self.type_work)
                            .map_err(|()| type_resource())?,
                    );
                }
            }
        }
        let mut inventories = Vec::new();
        self.type_work.charge(3).map_err(|()| type_resource())?;
        inventories
            .try_reserve_exact(3)
            .map_err(|_| type_resource())?;
        for (original, phase) in originals.iter().zip(&phases) {
            inventories.push(
                original
                    .local_identities(&phase.substitution(), &mut self.type_work)
                    .map_err(validation)?,
            );
        }
        // All originals are known before allocating targets, so one phase can
        // never accidentally choose a local identity from another phase.
        let mut forbidden_binders = HashSet::new();
        let mut forbidden_types = HashSet::new();
        let mut forbidden_handlers = HashSet::new();
        let mut forbidden_resumes = HashSet::new();
        let mut forbidden_lexicals = HashSet::new();
        for inventory in &inventories {
            if !inventory.nominals.is_empty() {
                return Err(invalid_state());
            } // target registry proof remains a later obligation
            for (count, reserve) in [
                (inventory.binders.len(), 0),
                (inventory.types.len(), 1),
                (inventory.handlers.len(), 2),
                (inventory.resumes.len(), 3),
                (inventory.lexicals.len(), 4),
            ] {
                self.type_work.charge(count).map_err(|()| type_resource())?;
                match reserve {
                    0 => forbidden_binders.try_reserve(count),
                    1 => forbidden_types.try_reserve(count),
                    2 => forbidden_handlers.try_reserve(count),
                    3 => forbidden_resumes.try_reserve(count),
                    _ => forbidden_lexicals.try_reserve(count),
                }
                .map_err(|_| type_resource())?;
            }
            forbidden_binders.extend(inventory.binders.iter().copied());
            forbidden_types.extend(inventory.types.iter().map(|(id, _)| *id));
            forbidden_handlers.extend(inventory.handlers.iter().copied());
            forbidden_resumes.extend(inventory.resumes.iter().copied());
            forbidden_lexicals.extend(inventory.lexicals.iter().copied());
        }
        // Actual replacements are immutable caller payloads. Fresh local
        // binders must not capture any free or forall-bound identity inside
        // them, including nested row members/lacks and pending row solutions.
        for phase in &phases {
            for payload in phase.sigma.types.as_map().values() {
                retain_type_payload_variables(payload, &mut forbidden_types, &mut self.type_work)?;
            }
            for payload in phase.sigma.rows.values().chain(phase.pending.values()) {
                retain_row_payload_variables(payload, &mut forbidden_types, &mut self.type_work)?;
            }
        }
        retain_type_payload_variables(body.value(), &mut forbidden_types, &mut self.type_work)?;
        retain_row_payload_variables(body.effects(), &mut forbidden_types, &mut self.type_work)?;
        for (phase, inventory) in phases.iter_mut().zip(inventories) {
            reserve_pair(
                &mut phase.binders,
                &mut phase.binder_pairs,
                inventory.binders.len(),
                &mut self.type_work,
            )?;
            for old in inventory.binders.iter() {
                let fresh = loop {
                    let builder = F::effect_builder(&mut self.builder).ok_or_else(invalid_state)?;
                    crate::core::transform::begin_provider_draft_work(
                        builder,
                        self.type_work.remaining(),
                    );
                    let allocated = builder.allocate_provider_copy_binders(1);
                    crate::core::transform::discharge_provider_draft_work(
                        builder,
                        &mut self.type_work,
                    )?;
                    let allocated = allocated?;
                    let fresh = *allocated.first().ok_or_else(invalid_state)?;
                    self.type_work.charge(1).map_err(|()| type_resource())?;
                    if !forbidden_binders.contains(&fresh) {
                        break fresh;
                    }
                };
                insert_pair(&mut phase.binders, &mut phase.binder_pairs, *old, fresh)?;
            }
            self.type_work
                .charge(
                    inventory
                        .types
                        .len()
                        .checked_mul(2)
                        .ok_or_else(type_resource)?,
                )
                .map_err(|()| type_resource())?;
            phase
                .variables
                .try_reserve(inventory.types.len())
                .map_err(|_| type_resource())?;
            phase
                .type_pairs
                .try_reserve_exact(inventory.types.len())
                .map_err(|_| type_resource())?;
            for (old, kind) in inventory.types.into_vec() {
                while forbidden_types.contains(&TypeVariableId::generated(
                    self.next_generated_type_variable,
                )) {
                    self.generated_type_variables
                        .skip_reserved(
                            TypeVariableId::generated(self.next_generated_type_variable),
                            &mut self.type_work,
                        )
                        .map_err(generated_type_variable_registry_error)?;
                    self.next_generated_type_variable = self
                        .next_generated_type_variable
                        .checked_sub(1)
                        .ok_or_else(invalid_state)?;
                }
                let fresh = self.fresh_type_variable(&kind, origin)?;
                if phase.variables.insert(old, fresh).is_some() {
                    return Err(invalid_state());
                }
                phase.type_pairs.push((old, fresh, kind));
            }
            reserve_pair(
                &mut phase.handlers,
                &mut phase.handler_pairs,
                inventory.handlers.len(),
                &mut self.type_work,
            )?;
            for old in inventory.handlers.iter() {
                let fresh = loop {
                    self.type_work.charge(1).map_err(|()| type_resource())?;
                    let fresh = HandlerId::new(self.next_handler);
                    self.next_handler =
                        self.next_handler.checked_add(1).ok_or_else(invalid_state)?;
                    if !forbidden_handlers.contains(&fresh) {
                        break fresh;
                    }
                };
                insert_pair(&mut phase.handlers, &mut phase.handler_pairs, *old, fresh)?;
            }
            reserve_pair(
                &mut phase.resumes,
                &mut phase.resume_pairs,
                inventory.resumes.len(),
                &mut self.type_work,
            )?;
            for old in inventory.resumes.iter() {
                let fresh = loop {
                    self.type_work.charge(1).map_err(|()| type_resource())?;
                    let fresh = ResumeId::new(self.next_provider_resume);
                    self.next_provider_resume = self
                        .next_provider_resume
                        .checked_sub(1)
                        .ok_or_else(invalid_state)?;
                    if !forbidden_resumes.contains(&fresh) {
                        break fresh;
                    }
                };
                insert_pair(&mut phase.resumes, &mut phase.resume_pairs, *old, fresh)?;
            }
            reserve_pair(
                &mut phase.lexicals,
                &mut phase.lexical_pairs,
                inventory.lexicals.len(),
                &mut self.type_work,
            )?;
            for old in inventory.lexicals.iter() {
                let fresh = loop {
                    self.type_work.charge(1).map_err(|()| type_resource())?;
                    let fresh = LexicalEvidenceId::new(module, self.next_provider_lexical);
                    self.next_provider_lexical = self
                        .next_provider_lexical
                        .checked_sub(1)
                        .ok_or_else(invalid_state)?;
                    if !forbidden_lexicals.contains(&fresh) {
                        break fresh;
                    }
                };
                insert_pair(&mut phase.lexicals, &mut phase.lexical_pairs, *old, fresh)?;
            }
        }
        Ok(PreparedScopeCopyPlan { phases })
    }
}

pub(in crate::elaborate) fn lower_prepared_scope_copies(
    builder: &mut crate::core::EffectCoreBuilder,
    source: &super::super::provider::ProviderTemplateSource<'_>,
    plan: &PreparedScopeCopyPlan,
    work: &mut TypeWorkBudget,
) -> Result<ScopeCopiedEntries, TypeError> {
    lower_scope_copies(builder, source, plan, None, work)
}
pub(in crate::elaborate) fn lower_final_scope_copies(
    builder: &mut crate::core::EffectCoreBuilder,
    source: &super::super::provider::ProviderTemplateSource<'_>,
    plan: &PreparedScopeCopyPlan,
    catalog: [&[ProviderCatalogRelocation]; 3],
    work: &mut TypeWorkBudget,
) -> Result<ScopeCopiedEntries, TypeError> {
    lower_scope_copies(builder, source, plan, Some(catalog), work)
}
fn lower_scope_copies(
    builder: &mut crate::core::EffectCoreBuilder,
    source: &super::super::provider::ProviderTemplateSource<'_>,
    plan: &PreparedScopeCopyPlan,
    catalog: Option<[&[ProviderCatalogRelocation]; 3]>,
    work: &mut TypeWorkBudget,
) -> Result<ScopeCopiedEntries, TypeError> {
    use crate::core::{
        provider::{copy_prepared_provider_forest, copy_provider_forest},
        transform,
    };
    fn failure(error: transform::TransformError) -> TypeError {
        match error {
            transform::TransformError::Build(error) => error.into(),
            _ => invalid_state(),
        }
    }
    fn forest(
        builder: &mut crate::core::EffectCoreBuilder,
        program: &crate::core::UnvalidatedEffectProgram,
        roots: &[NodeId],
        phase: &PreparedPhaseCopy,
        catalog: Option<&[ProviderCatalogRelocation]>,
    ) -> Result<ProviderCopiedForest, TypeError> {
        let replacements = HashMap::new();
        let context = phase.context();
        match catalog {
            Some(catalog) => {
                copy_provider_forest(builder, program, roots, &replacements, &context, catalog)
            }
            None => copy_prepared_provider_forest(builder, program, roots, &replacements, &context),
        }
        .map_err(failure)
    }
    transform::begin_provider_draft_work(builder, work.remaining());
    let result = (|| {
        let acquire_forest = forest(
            builder,
            source.acquire.program,
            &[source.acquire.body],
            &plan.phases[0],
            catalog.map(|catalog| catalog[0]),
        )?;
        let original_acquire = source
            .acquire
            .original
            .parameter_binder(source.acquire.program, work)
            .map_err(validation)?;
        let acquire_parameter = transform::rebuild_provider_fragment_binder_with_context(
            builder,
            original_acquire,
            &plan.phases[0].context(),
        )
        .map_err(failure)?;
        let acquire = ProviderLifecycleEntry {
            parameter: acquire_parameter,
            body: *acquire_forest.roots.first().ok_or_else(invalid_state)?,
        };
        let finish_forest = forest(
            builder,
            source.finish.program,
            &[source.finish.body],
            &plan.phases[1],
            catalog.map(|catalog| catalog[1]),
        )?;
        let original_finish = source
            .finish
            .original
            .parameter_binder(source.finish.program, work)
            .map_err(validation)?;
        let finish_parameter = transform::rebuild_provider_fragment_binder_with_context(
            builder,
            original_finish,
            &plan.phases[1].context(),
        )
        .map_err(failure)?;
        let finish = ProviderLifecycleEntry {
            parameter: finish_parameter,
            body: *finish_forest.roots.first().ok_or_else(invalid_state)?,
        };
        work.charge(source.handler.original_clauses().len())
            .map_err(|()| type_resource())?;
        let mut roots = Vec::new();
        roots
            .try_reserve_exact(source.handler.original_clauses().len())
            .map_err(|_| type_resource())?;
        roots.extend(
            source
                .handler
                .original_clauses()
                .iter()
                .map(EffectClause::body),
        );
        let handler_forest = forest(
            builder,
            source.handler.original_program(),
            &roots,
            &plan.phases[2],
            catalog.map(|catalog| catalog[2]),
        )?;
        let context = plan.phases[2].context();
        let state = transform::rebuild_provider_fragment_binder_with_context(
            builder,
            source.handler.original_state(),
            &context,
        )
        .map_err(failure)?;
        let handler = *plan.phases[2]
            .handlers
            .get(&source.handler.original_handler())
            .ok_or_else(invalid_state)?;
        work.charge(source.handler.original_clauses().len())
            .map_err(|()| type_resource())?;
        let mut clauses = Vec::new();
        clauses
            .try_reserve_exact(source.handler.original_clauses().len())
            .map_err(|_| type_resource())?;
        for (original, body) in source
            .handler
            .original_clauses()
            .iter()
            .zip(handler_forest.roots.iter())
        {
            let resume = context.resume(original.resume(), work)?;
            let origin = transform::rebuild_provider_fragment_origin(builder, original.origin())
                .map_err(failure)?;
            let pattern = transform::rebuild_provider_fragment_pattern_with_context(
                builder,
                original.pattern(),
                &context,
            )
            .map_err(failure)?;
            clauses.push(EffectClause::new(
                original.operation(),
                resume,
                crate::core::CoreMatchArm::new(pattern, *body, origin),
            ));
        }
        Ok(ScopeCopiedEntries {
            acquire,
            finish,
            state,
            handler,
            clauses,
            forests: [acquire_forest, finish_forest, handler_forest],
        })
    })();
    transform::discharge_provider_draft_work(builder, work)?;
    result
}
