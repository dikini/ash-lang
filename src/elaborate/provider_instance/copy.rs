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
// Preparation retains genuine inventories before any target allocation.
// These are compiler claims; final validation still checks the complete union.
struct PreparedPhaseAllocation {
    phase: PreparedPhaseCopy,
    binders: Box<[BinderId]>,
    types: Box<[(TypeVariableId, Kind)]>,
    handlers: Box<[HandlerId]>,
    resumes: Box<[ResumeId]>,
    nominals: Box<[NominalTypeId]>,
    lexicals: Box<[LexicalEvidenceId]>,
}
#[derive(Default)]
struct ScopeCopyForbidden {
    binders: HashSet<BinderId>,
    types: HashSet<TypeVariableId>,
    handlers: HashSet<HandlerId>,
    resumes: HashSet<ResumeId>,
    nominals: HashSet<NominalTypeId>,
    lexicals: HashSet<LexicalEvidenceId>,
}
impl ScopeCopyForbidden {
    fn retain(
        &mut self,
        allocation: &PreparedPhaseAllocation,
        work: &mut TypeWorkBudget,
    ) -> Result<(), TypeError> {
        if !allocation.nominals.is_empty() {
            return Err(invalid_state());
        } // target registry proof remains a later obligation
        for (count, reserve) in [
            (allocation.binders.len(), 0),
            (allocation.types.len(), 1),
            (allocation.handlers.len(), 2),
            (allocation.resumes.len(), 3),
            (allocation.lexicals.len(), 4),
        ] {
            work.charge(count).map_err(|()| type_resource())?;
            match reserve {
                0 => self.binders.try_reserve(count),
                1 => self.types.try_reserve(count),
                2 => self.handlers.try_reserve(count),
                3 => self.resumes.try_reserve(count),
                _ => self.lexicals.try_reserve(count),
            }
            .map_err(|_| type_resource())?;
        }
        self.binders.extend(allocation.binders.iter().copied());
        self.types
            .extend(allocation.types.iter().map(|(id, _)| *id));
        self.handlers.extend(allocation.handlers.iter().copied());
        self.resumes.extend(allocation.resumes.iter().copied());
        self.lexicals.extend(allocation.lexicals.iter().copied());
        // Local nominal copies remain unsupported until target registry proof
        // exists. This empty set records the complete guarded namespace.
        self.nominals.extend(allocation.nominals.iter().copied());
        Ok(())
    }
    fn retain_payloads(
        &mut self,
        phase: &PreparedPhaseCopy,
        work: &mut TypeWorkBudget,
    ) -> Result<(), TypeError> {
        let count = phase
            .sigma
            .types
            .as_map()
            .len()
            .checked_add(phase.sigma.rows.len())
            .and_then(|count| count.checked_add(phase.pending.len()))
            .and_then(|count| count.checked_add(phase.node_rows.len()))
            .ok_or_else(type_resource)?;
        work.charge(count).map_err(|()| type_resource())?;
        for ty in phase.sigma.types.as_map().values() {
            retain_type_payload_variables(ty, &mut self.types, work)?;
        }
        for row in phase
            .sigma
            .rows
            .values()
            .chain(phase.pending.values())
            .chain(phase.node_rows.values())
        {
            retain_row_payload_variables(row, &mut self.types, work)?;
        }
        Ok(())
    }
}

pub(in crate::elaborate) struct PreparedScopeCopyPlan {
    pub(in crate::elaborate) phases: [PreparedPhaseCopy; 3],
    pub(in crate::elaborate) family_phases: Box<[PreparedPhaseCopy]>,
}
pub(in crate::elaborate) struct ScopeCopiedEntries {
    pub(in crate::elaborate) acquire: ProviderLifecycleEntry,
    pub(in crate::elaborate) finish: ProviderLifecycleEntry,
    pub(in crate::elaborate) state: TypedBinder,
    pub(in crate::elaborate) handler: HandlerId,
    pub(in crate::elaborate) clauses: Vec<EffectClause>,
    pub(in crate::elaborate) forests: [ProviderCopiedForest; 3],
}

pub(in crate::elaborate) struct FamilyCopiedEntries {
    pub(in crate::elaborate) state: TypedBinder,
    pub(in crate::elaborate) handler: HandlerId,
    pub(in crate::elaborate) clauses: Vec<EffectClause>,
    pub(in crate::elaborate) dictionaries: Vec<TypedBinder>,
    pub(in crate::elaborate) forest: ProviderCopiedForest,
}

pub(in crate::elaborate) fn lower_family_scope_copies(
    builder: &mut crate::core::EffectCoreBuilder,
    source: &super::super::provider::ProviderTemplateSource<'_>,
    plan: &PreparedScopeCopyPlan,
    catalogs: Option<&[Vec<ProviderCatalogRelocation>]>,
    work: &mut TypeWorkBudget,
) -> Result<Vec<FamilyCopiedEntries>, TypeError> {
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
    if catalogs.is_some_and(|catalogs| catalogs.len() != plan.family_phases.len()) {
        return Err(invalid_state());
    }
    if plan.family_phases.is_empty() {
        return Ok(Vec::new());
    }
    let original = source.family.ok_or_else(invalid_state)?.handler;
    work.charge(plan.family_phases.len())
        .map_err(|()| type_resource())?;
    let mut copied = Vec::new();
    copied
        .try_reserve_exact(plan.family_phases.len())
        .map_err(|_| type_resource())?;
    transform::begin_provider_draft_work(builder, work.remaining());
    let result = (|| {
        for (index, phase) in plan.family_phases.iter().enumerate() {
            work.charge(
                original
                    .original_clauses()
                    .len()
                    .checked_add(original.original_dictionary_parameters().len())
                    .ok_or_else(type_resource)?,
            )
            .map_err(|()| type_resource())?;
            let mut roots = Vec::new();
            roots
                .try_reserve_exact(original.original_clauses().len())
                .map_err(|_| type_resource())?;
            roots.extend(original.original_clauses().iter().map(EffectClause::body));
            let context = phase.context();
            let replacements = HashMap::new();
            let forest = match catalogs {
                Some(catalogs) => copy_provider_forest(
                    builder,
                    original.original_program(),
                    &roots,
                    &replacements,
                    &context,
                    &catalogs[index],
                ),
                None => copy_prepared_provider_forest(
                    builder,
                    original.original_program(),
                    &roots,
                    &replacements,
                    &context,
                ),
            }
            .map_err(failure)?;
            if forest.roots.len() != original.original_clauses().len() {
                return Err(invalid_state());
            }
            let state = transform::rebuild_provider_fragment_binder_with_context(
                builder,
                original.original_state(),
                &context,
            )
            .map_err(failure)?;
            let handler = *phase
                .handlers
                .get(&original.original_handler())
                .ok_or_else(invalid_state)?;
            let mut dictionaries = Vec::new();
            dictionaries
                .try_reserve_exact(original.original_dictionary_parameters().len())
                .map_err(|_| type_resource())?;
            for binder in original.original_dictionary_parameters() {
                dictionaries.push(
                    transform::rebuild_provider_fragment_binder_with_context(
                        builder, binder, &context,
                    )
                    .map_err(failure)?,
                );
            }
            let mut clauses = Vec::new();
            clauses
                .try_reserve_exact(original.original_clauses().len())
                .map_err(|_| type_resource())?;
            for (clause, body) in original.original_clauses().iter().zip(&forest.roots) {
                let resume = context.resume(clause.resume(), work)?;
                let origin = transform::rebuild_provider_fragment_origin(builder, clause.origin())
                    .map_err(failure)?;
                let pattern = transform::rebuild_provider_fragment_pattern_with_context(
                    builder,
                    clause.pattern(),
                    &context,
                )
                .map_err(failure)?;
                clauses.push(EffectClause::new(
                    clause.operation(),
                    resume,
                    crate::core::CoreMatchArm::new(pattern, *body, origin),
                ));
            }
            copied.push(FamilyCopiedEntries {
                state,
                handler,
                clauses,
                dictionaries,
                forest,
            });
        }
        Ok(())
    })();
    transform::discharge_provider_draft_work(builder, work)?;
    result?;
    Ok(copied)
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

fn retain_original_copy_payload_variables(
    arguments: &[crate::types::KindedArgument],
    body: &ComputationType,
    residual: &EffectRow,
    pending: &HashMap<InferenceVariableId, EffectRow>,
    forbidden: &mut HashSet<TypeVariableId>,
    work: &mut TypeWorkBudget,
) -> Result<(), TypeError> {
    // The caller has completed all three unique sigma insertions. Their cloned
    // payloads preserve these original identities; collect the union once.
    work.charge(arguments.len()).map_err(|()| type_resource())?;
    for argument in arguments {
        match argument {
            crate::types::KindedArgument::TypeArg(ty) => {
                retain_type_payload_variables(ty, forbidden, work)?;
            }
            crate::types::KindedArgument::RowArg(row) => {
                retain_row_payload_variables(row, forbidden, work)?;
            }
        }
    }
    retain_type_payload_variables(body.value(), forbidden, work)?;
    retain_row_payload_variables(residual, forbidden, work)?;
    // Read the final map after all original inserts, preserving winning values.
    for row in pending.values() {
        retain_row_payload_variables(row, forbidden, work)?;
    }
    retain_row_payload_variables(body.effects(), forbidden, work)
}

/// Source-only row positions may remain ordinary registered inferences.
/// Copying these coordinates claims no completed row receipt or Core authority.
pub(in crate::elaborate) struct ProviderScopeCopyRows<'a> {
    pub(in crate::elaborate) residual: &'a EffectRow,
    pub(in crate::elaborate) pending: &'a HashMap<InferenceVariableId, EffectRow>,
    pub(in crate::elaborate) nodes: &'a HashMap<NodeId, EffectRow>,
}

impl<F: CoreLoweringFamily> CoreElaborator<F> {
    /// Allocates source-resource copies from their original programs and full
    /// Type/Row vectors, without experimental provider declaration authority.
    pub(in crate::elaborate) fn prepare_source_resource_copies(
        &mut self,
        template: &crate::core::source_resource::CheckedSourceResourceTemplate,
        arguments: &[crate::types::KindedArgument],
        body: &ComputationType,
        module: crate::module::ModuleId,
        origin: Span,
    ) -> Result<[PreparedPhaseCopy; 3], TypeError> {
        let header = &template.header().original;
        if header.parameters.len() != arguments.len() {
            return Err(invalid_state());
        }
        let mut inputs = Vec::new();
        self.type_work.charge(3).map_err(|_| type_resource())?;
        inputs.try_reserve_exact(3).map_err(|_| type_resource())?;
        for index in 0..3 {
            let mut phase = PreparedPhaseCopy::empty();
            for (formal, argument) in header.parameters.iter().zip(arguments) {
                phase
                    .sigma
                    .insert_cloned(formal.id, argument, &mut self.type_work)?;
            }
            if index == 2 {
                phase.sigma.insert_borrowed(
                    header.answer.id,
                    crate::elaborate::BorrowedOwnerArgument::TypeArg(body.value()),
                    &mut self.type_work,
                )?;
                let original_direct = template
                    .handler_direct_row(&mut self.type_work)
                    .map_err(validation)?;
                let direct = phase
                    .sigma
                    .substitute_row(&original_direct, &mut self.type_work)?;
                let mut residual =
                    clone_effect_row_with_budget(body.effects(), &mut self.type_work)
                        .map_err(|_| type_resource())?;
                for effect in direct.known() {
                    residual = residual
                        .remove_exact_with_budget(effect, &mut self.type_work)
                        .map_err(|_| type_resource())?
                        .map_err(|_| invalid_state())?;
                }
                phase.sigma.insert_borrowed(
                    template.handler_continuation(),
                    crate::elaborate::BorrowedOwnerArgument::RowArg(&residual),
                    &mut self.type_work,
                )?;
            }
            let original_handler = template.original_handler_node();
            let mut roots = Vec::new();
            self.type_work
                .charge(if index == 2 {
                    original_handler.clauses().len()
                } else {
                    1
                })
                .map_err(|_| type_resource())?;
            roots
                .try_reserve_exact(if index == 2 {
                    original_handler.clauses().len()
                } else {
                    1
                })
                .map_err(|_| type_resource())?;
            let (program, parameter) = match index {
                0 => {
                    roots.push(template.acquire_entry().1);
                    (template.original_acquire(), template.acquire_entry().0)
                }
                1 => {
                    roots.push(template.finish_entry().1);
                    (template.original_finish(), template.finish_entry().0)
                }
                _ => {
                    roots.extend(original_handler.clauses().iter().map(EffectClause::body));
                    (template.original_handler(), template.handler_entry().0)
                }
            };
            let patterns: &[&crate::core::CorePattern] = if index == 2 {
                &[template.handler_pattern()]
            } else {
                &[]
            };
            let inventory = crate::core::provider::source_resource_local_identities(
                program,
                &roots,
                &[parameter],
                patterns,
                (index == 2).then_some(original_handler),
                &phase.substitution(),
                &mut self.type_work,
            )
            .map_err(validation)?;
            inputs.push(PreparedPhaseAllocation {
                phase,
                binders: inventory.binders,
                types: inventory.types,
                handlers: inventory.handlers,
                resumes: inventory.resumes,
                nominals: inventory.nominals,
                lexicals: inventory.lexicals,
            });
        }
        let mut forbidden = ScopeCopyForbidden::default();
        for input in &inputs {
            forbidden.retain(input, &mut self.type_work)?;
        }
        retain_original_copy_payload_variables(
            arguments,
            body,
            body.effects(),
            &HashMap::new(),
            &mut forbidden.types,
            &mut self.type_work,
        )?;
        self.allocate_primary_copy_phases(inputs, &forbidden, module, origin)
    }

    pub(in crate::elaborate) fn prepare_scope_copy_plan(
        &mut self,
        source: &super::super::provider::ProviderTemplateSource<'_>,
        actuals: &ResourceActuals,
        body: &ComputationType,
        rows: &crate::core::provider::ResolvedProviderHandlerRows,
        module: crate::module::ModuleId,
        origin: Span,
    ) -> Result<PreparedScopeCopyPlan, TypeError> {
        self.prepare_scope_copy_plan_with_rows(
            source,
            actuals,
            body,
            ProviderScopeCopyRows {
                residual: rows.residual(),
                pending: rows.pending(),
                nodes: rows.node_rows(),
            },
            module,
            origin,
        )
    }

    #[allow(clippy::too_many_arguments)]
    pub(in crate::elaborate) fn prepare_scope_copy_plan_with_family_rows(
        &mut self,
        source: &super::super::provider::ProviderTemplateSource<'_>,
        actuals: &ResourceActuals,
        body: &ComputationType,
        primary: &crate::core::provider::ResolvedProviderHandlerRows,
        members: &[std::sync::Arc<super::PreparedProviderFamilyInstance>],
        rows: &[crate::core::provider::ResolvedProviderHandlerRows],
        module: crate::module::ModuleId,
        origin: Span,
    ) -> Result<PreparedScopeCopyPlan, TypeError> {
        if members.len() != rows.len() {
            return Err(invalid_state());
        }
        if members.is_empty() {
            return self.prepare_scope_copy_plan(source, actuals, body, primary, module, origin);
        }
        let family = source.family.as_ref().ok_or_else(invalid_state)?;
        let primary_rows = ProviderScopeCopyRows {
            residual: primary.residual(),
            pending: primary.pending(),
            nodes: primary.node_rows(),
        };
        let primary_inputs =
            self.prepare_scope_copy_phase_inputs(source, actuals, body, &primary_rows, None)?;
        self.type_work
            .charge(members.len())
            .map_err(|()| type_resource())?;
        let mut family_inputs = Vec::new();
        family_inputs
            .try_reserve_exact(members.len())
            .map_err(|_| type_resource())?;
        for (member, rows) in members.iter().zip(rows) {
            if member.identity() != family.identity {
                return Err(invalid_state());
            }
            let rows = ProviderScopeCopyRows {
                residual: rows.residual(),
                pending: rows.pending(),
                nodes: rows.node_rows(),
            };
            let original = ProviderOriginalTemplate::Handler(family.handler);
            let phase = self.prepare_copy_phase_sigma(
                original,
                source,
                actuals,
                body,
                &rows,
                Some((family.identity.parameter, &member.payload)),
            )?;
            family_inputs.push(self.prepare_copy_phase_inventory(original, phase)?);
        }
        // The immutable group covers primary and every actual family handler.
        // No target allocator has run while either original namespace was absent.
        let mut forbidden = ScopeCopyForbidden::default();
        for allocation in primary_inputs.iter().chain(&family_inputs) {
            forbidden.retain(allocation, &mut self.type_work)?;
            forbidden.retain_payloads(&allocation.phase, &mut self.type_work)?;
        }
        retain_row_payload_variables(body.effects(), &mut forbidden.types, &mut self.type_work)?;
        let phases =
            self.allocate_primary_copy_phases(primary_inputs, &forbidden, module, origin)?;
        self.type_work
            .charge(members.len())
            .map_err(|()| type_resource())?;
        let mut family_phases = Vec::new();
        family_phases
            .try_reserve_exact(members.len())
            .map_err(|_| type_resource())?;
        for allocation in family_inputs {
            family_phases.push(self.allocate_copy_phase(allocation, &forbidden, module, origin)?);
        }
        Ok(PreparedScopeCopyPlan {
            phases,
            family_phases: family_phases.into_boxed_slice(),
        })
    }

    pub(in crate::elaborate) fn prepare_scope_copy_plan_with_rows(
        &mut self,
        source: &super::super::provider::ProviderTemplateSource<'_>,
        actuals: &ResourceActuals,
        body: &ComputationType,
        rows: ProviderScopeCopyRows<'_>,
        module: crate::module::ModuleId,
        origin: Span,
    ) -> Result<PreparedScopeCopyPlan, TypeError> {
        self.prepare_scope_copy_plan_with_payload(source, actuals, body, rows, module, origin, None)
    }

    #[allow(clippy::too_many_arguments)]
    fn prepare_scope_copy_plan_with_payload(
        &mut self,
        source: &super::super::provider::ProviderTemplateSource<'_>,
        actuals: &ResourceActuals,
        body: &ComputationType,
        rows: ProviderScopeCopyRows<'_>,
        module: crate::module::ModuleId,
        origin: Span,
        payload: Option<(TypeVariableId, &Type)>,
    ) -> Result<PreparedScopeCopyPlan, TypeError> {
        let inputs = self.prepare_scope_copy_phase_inputs(source, actuals, body, &rows, payload)?;
        let mut forbidden = ScopeCopyForbidden::default();
        for allocation in &inputs {
            forbidden.retain(allocation, &mut self.type_work)?;
        }
        // Preserve the legacy caller-payload traversal and debit exactly.
        retain_original_copy_payload_variables(
            actuals.arguments(),
            body,
            rows.residual,
            &inputs[2].phase.pending,
            &mut forbidden.types,
            &mut self.type_work,
        )?;
        let phases = self.allocate_primary_copy_phases(inputs, &forbidden, module, origin)?;
        Ok(PreparedScopeCopyPlan {
            phases,
            family_phases: Box::new([]),
        })
    }

    fn prepare_scope_copy_phase_inputs(
        &mut self,
        source: &super::super::provider::ProviderTemplateSource<'_>,
        actuals: &ResourceActuals,
        body: &ComputationType,
        rows: &ProviderScopeCopyRows<'_>,
        payload: Option<(TypeVariableId, &Type)>,
    ) -> Result<Vec<PreparedPhaseAllocation>, TypeError> {
        if actuals.arguments().len() != source.fact.parameters.len() {
            return Err(invalid_state());
        }
        let originals = [
            ProviderOriginalTemplate::Lifecycle(source.acquire.original, source.acquire.program),
            ProviderOriginalTemplate::Lifecycle(source.finish.original, source.finish.program),
            ProviderOriginalTemplate::Handler(source.handler),
        ];
        // Keep all sigma construction before inventories, as in the legacy path.
        let phases = [
            self.prepare_copy_phase_sigma(originals[0], source, actuals, body, rows, None)?,
            self.prepare_copy_phase_sigma(originals[1], source, actuals, body, rows, None)?,
            self.prepare_copy_phase_sigma(originals[2], source, actuals, body, rows, payload)?,
        ];
        self.type_work.charge(3).map_err(|()| type_resource())?;
        let mut inputs = Vec::new();
        inputs.try_reserve_exact(3).map_err(|_| type_resource())?;
        for (original, phase) in originals.into_iter().zip(phases) {
            inputs.push(self.prepare_copy_phase_inventory(original, phase)?);
        }
        Ok(inputs)
    }

    fn prepare_copy_phase_inventory(
        &mut self,
        original: ProviderOriginalTemplate<'_>,
        phase: PreparedPhaseCopy,
    ) -> Result<PreparedPhaseAllocation, TypeError> {
        let inventory = original
            .local_identities(&phase.substitution(), &mut self.type_work)
            .map_err(validation)?;
        Ok(PreparedPhaseAllocation {
            phase,
            binders: inventory.binders,
            types: inventory.types,
            handlers: inventory.handlers,
            resumes: inventory.resumes,
            nominals: inventory.nominals,
            lexicals: inventory.lexicals,
        })
    }

    #[allow(clippy::too_many_arguments)]
    fn prepare_copy_phase_sigma(
        &mut self,
        original: ProviderOriginalTemplate<'_>,
        source: &super::super::provider::ProviderTemplateSource<'_>,
        actuals: &ResourceActuals,
        body: &ComputationType,
        rows: &ProviderScopeCopyRows<'_>,
        payload: Option<(TypeVariableId, &Type)>,
    ) -> Result<PreparedPhaseCopy, TypeError> {
        let is_handler = matches!(original, ProviderOriginalTemplate::Handler(_));
        let mut phase = PreparedPhaseCopy::empty();
        match original {
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
        if is_handler && let Some((parameter, payload)) = payload {
            phase.sigma.insert_borrowed(
                parameter,
                crate::elaborate::BorrowedOwnerArgument::TypeArg(payload),
                &mut self.type_work,
            )?;
        }
        let hidden = match original {
            ProviderOriginalTemplate::Lifecycle(original, _) => original.hidden(),
            ProviderOriginalTemplate::Handler(original) => original.original_hidden(),
        };
        if hidden[0].1 != Kind::Type || hidden[1].1 != Kind::EffectRow {
            return Err(invalid_state());
        }
        phase.sigma.insert_borrowed(
            hidden[0].0,
            crate::elaborate::BorrowedOwnerArgument::TypeArg(body.value()),
            &mut self.type_work,
        )?;
        phase.sigma.insert_borrowed(
            hidden[1].0,
            crate::elaborate::BorrowedOwnerArgument::RowArg(rows.residual),
            &mut self.type_work,
        )?;
        if is_handler {
            self.type_work
                .charge(rows.pending.len())
                .map_err(|()| type_resource())?;
            phase
                .pending
                .try_reserve(rows.pending.len())
                .map_err(|_| type_resource())?;
            for (id, row) in rows.pending {
                phase.pending.insert(
                    *id,
                    clone_effect_row_with_budget(row, &mut self.type_work)
                        .map_err(|()| type_resource())?,
                );
            }
            self.type_work
                .charge(rows.nodes.len())
                .map_err(|()| type_resource())?;
            phase
                .node_rows
                .try_reserve(rows.nodes.len())
                .map_err(|_| type_resource())?;
            for (node, row) in rows.nodes {
                phase.node_rows.insert(
                    *node,
                    clone_effect_row_with_budget(row, &mut self.type_work)
                        .map_err(|()| type_resource())?,
                );
            }
        }
        Ok(phase)
    }

    fn allocate_primary_copy_phases(
        &mut self,
        inputs: Vec<PreparedPhaseAllocation>,
        forbidden: &ScopeCopyForbidden,
        module: crate::module::ModuleId,
        origin: Span,
    ) -> Result<[PreparedPhaseCopy; 3], TypeError> {
        if inputs.len() != 3 {
            return Err(invalid_state());
        }
        let mut inputs = inputs.into_iter();
        Ok([
            self.allocate_copy_phase(
                inputs.next().ok_or_else(invalid_state)?,
                forbidden,
                module,
                origin,
            )?,
            self.allocate_copy_phase(
                inputs.next().ok_or_else(invalid_state)?,
                forbidden,
                module,
                origin,
            )?,
            self.allocate_copy_phase(
                inputs.next().ok_or_else(invalid_state)?,
                forbidden,
                module,
                origin,
            )?,
        ])
    }

    fn allocate_copy_phase(
        &mut self,
        allocation: PreparedPhaseAllocation,
        forbidden: &ScopeCopyForbidden,
        module: crate::module::ModuleId,
        origin: Span,
    ) -> Result<PreparedPhaseCopy, TypeError> {
        let PreparedPhaseAllocation {
            mut phase,
            binders,
            types,
            handlers,
            resumes,
            nominals,
            lexicals,
        } = allocation;
        if !nominals.is_empty() || !forbidden.nominals.is_empty() {
            return Err(invalid_state());
        }
        reserve_pair(
            &mut phase.binders,
            &mut phase.binder_pairs,
            binders.len(),
            &mut self.type_work,
        )?;
        for old in binders.iter() {
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
                if !forbidden.binders.contains(&fresh) {
                    break fresh;
                }
            };
            insert_pair(&mut phase.binders, &mut phase.binder_pairs, *old, fresh)?;
        }
        self.type_work
            .charge(types.len().checked_mul(2).ok_or_else(type_resource)?)
            .map_err(|()| type_resource())?;
        phase
            .variables
            .try_reserve(types.len())
            .map_err(|_| type_resource())?;
        phase
            .type_pairs
            .try_reserve_exact(types.len())
            .map_err(|_| type_resource())?;
        for (old, kind) in types.into_vec() {
            while forbidden.types.contains(&TypeVariableId::generated(
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
            handlers.len(),
            &mut self.type_work,
        )?;
        for old in handlers.iter() {
            let fresh = loop {
                self.type_work.charge(1).map_err(|()| type_resource())?;
                let fresh = HandlerId::new(self.next_handler);
                self.next_handler = self.next_handler.checked_add(1).ok_or_else(invalid_state)?;
                if !forbidden.handlers.contains(&fresh) {
                    break fresh;
                }
            };
            insert_pair(&mut phase.handlers, &mut phase.handler_pairs, *old, fresh)?;
        }
        reserve_pair(
            &mut phase.resumes,
            &mut phase.resume_pairs,
            resumes.len(),
            &mut self.type_work,
        )?;
        for old in resumes.iter() {
            let fresh = loop {
                self.type_work.charge(1).map_err(|()| type_resource())?;
                let fresh = ResumeId::new(self.next_provider_resume);
                self.next_provider_resume = self
                    .next_provider_resume
                    .checked_sub(1)
                    .ok_or_else(invalid_state)?;
                if !forbidden.resumes.contains(&fresh) {
                    break fresh;
                }
            };
            insert_pair(&mut phase.resumes, &mut phase.resume_pairs, *old, fresh)?;
        }
        reserve_pair(
            &mut phase.lexicals,
            &mut phase.lexical_pairs,
            lexicals.len(),
            &mut self.type_work,
        )?;
        for old in lexicals.iter() {
            let fresh = loop {
                self.type_work.charge(1).map_err(|()| type_resource())?;
                let fresh = LexicalEvidenceId::new(module, self.next_provider_lexical);
                self.next_provider_lexical = self
                    .next_provider_lexical
                    .checked_sub(1)
                    .ok_or_else(invalid_state)?;
                if !forbidden.lexicals.contains(&fresh) {
                    break fresh;
                }
            };
            insert_pair(&mut phase.lexicals, &mut phase.lexical_pairs, *old, fresh)?;
        }
        Ok(phase)
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

#[cfg(test)]
mod payload_collection_tests {
    use super::*;
    use crate::module::ModuleId;
    use crate::types::{EffectId, EffectInstance, KindedArgument, ResourceDefinitionId};

    fn variable(id: u32) -> TypeVariableId {
        TypeVariableId::generated(id)
    }

    fn row(seed: u32) -> EffectRow {
        let module = ModuleId::new(31);
        EffectRow::with_tail(
            Box::new([EffectInstance::new_kinded(
                EffectId::new(module, seed),
                Box::new([
                    KindedArgument::TypeArg(Type::Variable(variable(seed))),
                    KindedArgument::RowArg(EffectRow::open(
                        EffectRowVariable::rigid(variable(seed + 1)),
                        Box::new([EffectInstance::new(
                            EffectId::new(module, seed + 1),
                            Box::new([Type::Variable(variable(seed + 2))]),
                        )]),
                    )),
                ]),
            )]),
            EffectRowVariable::rigid(variable(seed + 3)),
            Box::new([EffectInstance::new(
                EffectId::new(module, seed + 2),
                Box::new([Type::Forall(
                    Box::new([(
                        variable(seed + 4),
                        Kind::Arrow(Box::new(Kind::Type), Box::new(Kind::EffectRow)),
                    )]),
                    Box::new(Type::Variable(variable(seed + 5))),
                )]),
            )]),
        )
    }

    fn fixture() -> (Vec<KindedArgument>, ComputationType, EffectRow) {
        let ty = Type::Forall(
            Box::new([(variable(1), Kind::Type), (variable(2), Kind::EffectRow)]),
            Box::new(Type::ResourceApply(
                ResourceDefinitionId::new(ModuleId::new(31), 0),
                Box::new([
                    KindedArgument::TypeArg(Type::Function(
                        Box::new(Type::Application(
                            Box::new(Type::Variable(variable(3))),
                            Box::new(Type::Variable(variable(4))),
                        )),
                        Box::new(Type::EffectfulFunction(
                            Box::new(Type::Variable(variable(5))),
                            Box::new(ComputationType::new(
                                Type::Tuple(Box::new([Type::Variable(variable(6)), Type::Unit])),
                                row(20),
                            )),
                        )),
                    )),
                    KindedArgument::RowArg(row(30)),
                ]),
            )),
        );
        (
            vec![KindedArgument::TypeArg(ty), KindedArgument::RowArg(row(40))],
            ComputationType::new(
                Type::Forall(
                    Box::new([(variable(7), Kind::Type)]),
                    Box::new(Type::Variable(variable(8))),
                ),
                row(50),
            ),
            row(60),
        )
    }

    fn phases(
        arguments: &[KindedArgument],
        body: &ComputationType,
        residual: &EffectRow,
    ) -> [PreparedPhaseCopy; 3] {
        let mut phases = [
            PreparedPhaseCopy::empty(),
            PreparedPhaseCopy::empty(),
            PreparedPhaseCopy::empty(),
        ];
        let mut work = TypeWorkBudget::unbounded();
        for (index, phase) in phases.iter_mut().enumerate() {
            for (ordinal, argument) in arguments.iter().enumerate() {
                phase
                    .sigma
                    .insert_cloned(
                        variable(1000 + index as u32 * 100 + ordinal as u32),
                        argument,
                        &mut work,
                    )
                    .unwrap();
            }
            let value = KindedArgument::TypeArg(
                crate::types::clone_type_with_budget(body.value(), &mut work).unwrap(),
            );
            phase
                .sigma
                .insert_cloned(variable(2000 + index as u32), &value, &mut work)
                .unwrap();
            let row =
                KindedArgument::RowArg(clone_effect_row_with_budget(residual, &mut work).unwrap());
            phase
                .sigma
                .insert_cloned(variable(3000 + index as u32), &row, &mut work)
                .unwrap();
        }
        phases
    }

    // The exact old collection order, retained only as the set-law oracle.
    fn original_collection(
        phases: &[PreparedPhaseCopy; 3],
        body: &ComputationType,
        forbidden: &mut HashSet<TypeVariableId>,
        work: &mut TypeWorkBudget,
    ) {
        for phase in phases {
            for payload in phase.sigma.types.as_map().values() {
                retain_type_payload_variables(payload, forbidden, work).unwrap();
            }
            for payload in phase.sigma.rows.values().chain(phase.pending.values()) {
                retain_row_payload_variables(payload, forbidden, work).unwrap();
            }
        }
        retain_type_payload_variables(body.value(), forbidden, work).unwrap();
        retain_row_payload_variables(body.effects(), forbidden, work).unwrap();
    }

    #[test]
    fn original_copy_inputs_preserve_complete_forbidden_identity_union() {
        let (arguments, body, residual) = fixture();
        let mut phases = phases(&arguments, &body, &residual);
        phases[2]
            .pending
            .insert(InferenceVariableId::new(0), row(70));
        let seeded = HashSet::from([variable(900), variable(1), variable(70)]);
        let mut original = seeded.clone();
        let mut original_work = TypeWorkBudget::unbounded();
        original_collection(&phases, &body, &mut original, &mut original_work);
        let mut direct = seeded;
        let mut direct_work = TypeWorkBudget::unbounded();
        retain_original_copy_payload_variables(
            &arguments,
            &body,
            &residual,
            &phases[2].pending,
            &mut direct,
            &mut direct_work,
        )
        .unwrap();
        assert_eq!(direct, original);
        for id in [
            1, 2, 3, 4, 5, 6, 7, 8, 20, 21, 22, 23, 24, 25, 30, 40, 50, 60, 70, 74, 75, 900,
        ] {
            assert!(
                direct.contains(&variable(id)),
                "missing original identity {id}"
            );
        }
        assert!(direct_work.used() < original_work.used());
        // Membership is the sole input to original fresh-Type collision checks.
        assert_eq!(
            (0..1000)
                .filter(|id| !direct.contains(&variable(*id)))
                .collect::<Vec<_>>(),
            (0..1000)
                .filter(|id| !original.contains(&variable(*id)))
                .collect::<Vec<_>>()
        );
    }

    #[test]
    fn original_copy_inputs_use_final_pending_winner_and_keep_unique_sigma_guard() {
        let body = ComputationType::new(Type::Unit, EffectRow::empty());
        let residual = EffectRow::empty();
        let mut phases = phases(&[], &body, &residual);
        let key = InferenceVariableId::new(0);
        phases[2].pending.insert(
            key,
            EffectRow::open(EffectRowVariable::rigid(variable(101)), Box::new([])),
        );
        phases[2].pending.insert(
            key,
            EffectRow::open(EffectRowVariable::rigid(variable(102)), Box::new([])),
        );
        let mut original = HashSet::new();
        original_collection(
            &phases,
            &body,
            &mut original,
            &mut TypeWorkBudget::unbounded(),
        );
        let mut direct = HashSet::new();
        retain_original_copy_payload_variables(
            &[],
            &body,
            &residual,
            &phases[2].pending,
            &mut direct,
            &mut TypeWorkBudget::unbounded(),
        )
        .unwrap();
        assert_eq!(direct, original);
        assert!(!direct.contains(&variable(101)));
        assert!(direct.contains(&variable(102)));
        assert!(
            phases[0]
                .sigma
                .insert_cloned(
                    variable(2000),
                    &KindedArgument::TypeArg(Type::Variable(variable(103))),
                    &mut TypeWorkBudget::unbounded()
                )
                .is_err()
        );
    }

    #[test]
    fn original_copy_input_collection_refusal_is_local_and_retry_preserves_union() {
        let (arguments, body, residual) = fixture();
        let phases = phases(&arguments, &body, &residual);
        let mut expected = HashSet::from([variable(900)]);
        let mut measured = TypeWorkBudget::unbounded();
        retain_original_copy_payload_variables(
            &arguments,
            &body,
            &residual,
            &phases[2].pending,
            &mut expected,
            &mut measured,
        )
        .unwrap();
        for limit in 0..measured.used() {
            let mut scratch = HashSet::from([variable(900)]);
            let mut short = TypeWorkBudget::with_limit(limit);
            assert!(
                retain_original_copy_payload_variables(
                    &arguments,
                    &body,
                    &residual,
                    &phases[2].pending,
                    &mut scratch,
                    &mut short
                )
                .is_err()
            );
            assert!(scratch.is_subset(&expected));
            retain_original_copy_payload_variables(
                &arguments,
                &body,
                &residual,
                &phases[2].pending,
                &mut scratch,
                &mut TypeWorkBudget::unbounded(),
            )
            .unwrap();
            assert_eq!(scratch, expected);
        }
    }
}
