//! Pure virtual Evidence equations. No original context, slot, Head, root feed
//! or activation is published here. The owner admits the complete family and
//! actual context, interns one scope for PlanId, and drives all local requests
//! before publishing any part of the batch. This module grants no admission.

use std::collections::{HashMap, HashSet};
use std::hash::{DefaultHasher, Hash, Hasher};

use super::{AdmittedFrame, Expr, Failure, Graph, TypeWorkBudget, charge, copy_slice};
use super::deferred_frame::{Arena as Routes, CompletedFrame, ProjectionClass, RouteId};
use super::producer::{ClosureAlternative, ScopeId, Value};
use super::typed_environment::{Arena as Types, TypeOrigin};

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(super) struct PlanId(usize);

#[derive(Clone, Copy)]
pub(super) struct Mark {
    plans: usize,
    bindings: usize,
    completions: usize,
}

// Original ordered coordinates, extracted by the owner using its existing
// evidence indices. Distinct evidence ordinals/duplicate binding occurrences
// remain distinct even when they have identical keys, arguments or routes.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(super) struct DictionaryFeed {
    pub(super) binding_ordinal: usize,
    pub(super) evidence_ordinal: usize,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(super) struct VisitInput {
    pub(super) expression: usize,
    pub(super) lexical: bool,
    pub(super) binding_start: usize,
    pub(super) binding_end: usize,
}

// The owner supplies the EXACT original CaptureTopology first-visit order,
// before any dynamic writes. It also supplies matched evidence ordinals that
// CaptureTopology's compact binding-ordinal vector itself does not retain.
pub(super) struct TopologyInput<'a> {
    pub(super) visits: &'a [VisitInput],
    pub(super) bindings: &'a [DictionaryFeed],
    pub(super) residuals: &'a [DictionaryFeed],
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(super) struct CreationRequest {
    pub(super) scope: ScopeId,
    pub(super) expression: usize,
}

struct Plan<'g> {
    digest: u64,
    graph: &'g Graph,
    evidence: usize,
    function: usize,
    declared: &'g [usize],
    alternatives: Vec<ClosureAlternative>,
    bindings: Vec<Value>,
    visits: Vec<VisitInput>,
    binding_feeds: Vec<DictionaryFeed>,
    residuals: Vec<DictionaryFeed>,
    classes: Vec<(usize, ProjectionClass)>,
    creation_requests: Vec<CreationRequest>,
    local_requests: Vec<usize>,
    scope: Option<ScopeId>,
    completed: Option<Completed>,
}

struct Completed {
    value: Value,
    complete_routes: Vec<RouteId>,
    frame: CompletedFrame,
    origin: TypeOrigin,
    any_ready: RouteId,
}

pub(super) struct Arena<'g> {
    graph: &'g Graph,
    plans: Vec<Plan<'g>>,
    by_digest: HashMap<u64, Vec<PlanId>>,
    scope_bindings: Vec<PlanId>,
    completions: Vec<PlanId>,
}

// Opaque complete incoming environment, not a local-only answer. One row per
// E expression retains feeds in original per-alternative [visits; residuals]
// insertion order. The local recipe must still be evaluated in this SAME E.
pub(super) struct IncomingEnvironment {
    plan: PlanId,
    rows: Vec<IncomingRow>,
}

struct IncomingRow {
    expression: usize,
    class: ProjectionClass,
    feeds: Vec<Value>,
}

pub(super) struct Completion {
    pub(super) value: Value,
    pub(super) frame: CompletedFrame,
    pub(super) origin: TypeOrigin,
    // The owner stages this condition onto its interned E scope activation.
    // Evidence specialization itself adds NO Function K/root capture feeds.
    pub(super) activation_condition: RouteId,
}

fn compatible(upper: ProjectionClass, source: ProjectionClass) -> bool {
    source == ProjectionClass::Empty || source == upper
}

fn hash_alternative(alternative: &ClosureAlternative, hash: &mut impl Hasher) {
    alternative.function.hash(hash);
    alternative.frame.hash(hash);
    alternative.creation.hash(hash);
    alternative.origin.hash(hash);
    alternative.gate.hash(hash);
}

fn same_alternative(left: &ClosureAlternative, right: &ClosureAlternative) -> bool {
    left.function == right.function && left.frame == right.frame
        && left.creation == right.creation && left.origin == right.origin && left.gate == right.gate
}

fn same_value(left: &Value, right: &Value, budget: &mut TypeWorkBudget) -> Result<bool, Failure> {
    charge(budget, left.alternatives.len().checked_add(right.alternatives.len())
        .and_then(|n| n.checked_add(2)).ok_or(Failure::Resource)?)?;
    Ok(left.route == right.route && left.class == right.class
        && left.alternatives.len() == right.alternatives.len()
        && left.alternatives.iter().zip(&right.alternatives).all(|(l, r)| same_alternative(l, r)))
}

fn class_for(classes: &[(usize, ProjectionClass)], expression: usize,
    budget: &mut TypeWorkBudget) -> Result<Option<ProjectionClass>, Failure>
{
    charge(budget, classes.len())?;
    Ok(classes.iter().find(|(e, _)| *e == expression).map(|(_, c)| *c))
}

fn copy_values(values: &[Value], budget: &mut TypeWorkBudget) -> Result<Vec<Value>, Failure> {
    charge(budget, values.len())?;
    let mut result = Vec::new();
    result.try_reserve_exact(values.len()).map_err(|_| Failure::Resource)?;
    for value in values { result.push(value.copy(budget)?); }
    Ok(result)
}

impl<'g> Arena<'g> {
    pub(super) fn new(graph: &'g Graph) -> Self {
        Self { graph, plans: Vec::new(), by_digest: HashMap::new(),
            scope_bindings: Vec::new(), completions: Vec::new() }
    }

    pub(super) fn mark(&self, budget: &mut TypeWorkBudget) -> Result<Mark, Failure> {
        charge(budget, 1)?;
        Ok(Mark { plans: self.plans.len(), bindings: self.scope_bindings.len(),
            completions: self.completions.len() })
    }

    // Call before Registry recycles its appended ScopeId suffix. All handles
    // from the aborted attempt must be discarded. Routes/Types/frame IDs are
    // append-only and are NOT recycled here. Insertion prepays this flat
    // cleanup, so a depleted work budget cannot prevent rollback.
    pub(super) fn abort(&mut self, mark: Mark) -> Result<(), Failure> {
        if mark.plans > self.plans.len() || mark.bindings > self.scope_bindings.len()
            || mark.completions > self.completions.len() { return Err(Failure::Invalid); }
        while self.completions.len() > mark.completions {
            let id = self.completions.pop().ok_or(Failure::Invalid)?;
            self.plans.get_mut(id.0).ok_or(Failure::Invalid)?.completed = None;
        }
        while self.scope_bindings.len() > mark.bindings {
            let id = self.scope_bindings.pop().ok_or(Failure::Invalid)?;
            self.plans.get_mut(id.0).ok_or(Failure::Invalid)?.scope = None;
        }
        while self.plans.len() > mark.plans {
            let id = PlanId(self.plans.len() - 1);
            let digest = self.plan(id)?.digest;
            let bucket = self.by_digest.get_mut(&digest).ok_or(Failure::Invalid)?;
            if bucket.last() != Some(&id) { return Err(Failure::Invalid); }
            bucket.pop().ok_or(Failure::Invalid)?;
            if bucket.is_empty() { self.by_digest.remove(&digest).ok_or(Failure::Invalid)?; }
            self.plans.pop().ok_or(Failure::Invalid)?;
        }
        Ok(())
    }

    pub(super) fn scope(&self, id: PlanId) -> Result<Option<ScopeId>, Failure> {
        Ok(self.plan(id)?.scope)
    }

    // Root associates its freshly registered canonical E scope BEFORE any
    // local child expansion. This module never invents an occurrence/context.
    pub(super) fn bind_scope(&mut self, id: PlanId, scope: ScopeId,
        budget: &mut TypeWorkBudget) -> Result<(), Failure> {
        charge(budget, 3)?; // lookup, publication and eventual rollback
        if let Some(old) = self.plan(id)?.scope {
            return if old == scope { Ok(()) } else { Err(Failure::Invalid) };
        }
        self.scope_bindings.try_reserve(1).map_err(|_| Failure::Resource)?;
        self.plans.get_mut(id.0).ok_or(Failure::Invalid)?.scope = Some(scope);
        self.scope_bindings.push(id);
        Ok(())
    }

    fn plan(&self, id: PlanId) -> Result<&Plan<'g>, Failure> {
        self.plans.get(id.0).ok_or(Failure::Invalid)
    }

    // Whole-plan semantic preflight precedes even inert route allocation.
    // Classes must be owner-proved COMPLETE E upper classes, including all
    // local and incoming writers. Raw-I Slot baselines are NOT that authority.
    // Eligibility, the exact original topology and the pure local dependency
    // DAG remain owner obligations. No current atom/readiness answer is used.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn prepare(&mut self, evidence: usize, function: usize,
        topology: TopologyInput<'_>, input: &Value, bindings: &[Value],
        classes: &[(usize, ProjectionClass)], budget: &mut TypeWorkBudget,
    ) -> Result<Option<(PlanId, bool)>, Failure> {
        charge(budget, 2)?;
        let Some(Expr::Evidence { bindings: source_bindings, .. }) = self.graph.expressions.get(evidence)
            else { return Ok(None); };
        let Some(Expr::Function { captures: declared, .. }) = self.graph.expressions.get(function)
            else { return Ok(None); };
        if input.class != ProjectionClass::Callable(function) || input.alternatives.is_empty()
            || bindings.len() != source_bindings.len() { return Ok(None); }
        charge(budget, input.alternatives.len())?;
        if input.alternatives.iter().any(|a| a.function != function) { return Ok(None); }
        let mut class_seen = HashSet::new();
        charge(budget, classes.len())?;
        class_seen.try_reserve(classes.len()).map_err(|_| Failure::Resource)?;
        for &(expression, class) in classes {
            charge(budget, 1)?;
            if self.graph.expressions.get(expression).is_none() || !class_seen.insert(expression) {
                return Ok(None);
            }
            if let ProjectionClass::Callable(code) = class {
                if !matches!(self.graph.expressions.get(code), Some(Expr::Function { .. })) { return Ok(None); }
            }
        }
        let mut local_requests = Vec::new();
        let mut requested = HashSet::new();
        let mut add_local = |expression, budget: &mut TypeWorkBudget| -> Result<bool, Failure> {
            if class_for(classes, expression, budget)?.is_none() { return Ok(false); }
            charge(budget, 1)?;
            if !requested.contains(&expression) {
                requested.try_reserve(1).map_err(|_| Failure::Resource)?;
                local_requests.try_reserve(1).map_err(|_| Failure::Resource)?;
                requested.insert(expression);
                local_requests.push(expression);
            }
            Ok(true)
        };
        charge(budget, declared.len())?;
        for &capture in declared { if !add_local(capture, budget)? { return Ok(None); } }
        let mut visit_seen = HashSet::new();
        let mut covered = HashSet::new();
        charge(budget, topology.visits.len())?;
        visit_seen.try_reserve(topology.visits.len()).map_err(|_| Failure::Resource)?;
        covered.try_reserve(topology.visits.len()).map_err(|_| Failure::Resource)?;
        let mut expected_start = 0;
        for visit in topology.visits {
            charge(budget, 2)?;
            if !visit_seen.insert(visit.expression) || visit.binding_start != expected_start
                || visit.binding_start > visit.binding_end || visit.binding_end > topology.bindings.len()
                || !add_local(visit.expression, budget)? { return Ok(None); }
            expected_start = visit.binding_end;
            if visit.binding_start != visit.binding_end {
                if visit.lexical { return Ok(None); }
                covered.insert(visit.expression);
            }
            // The admitted family has Slot lexical terminals. Function/other
            // deep terminal materialization needs another source proof.
            if visit.lexical && !matches!(self.graph.expressions.get(visit.expression), Some(Expr::Slot)) {
                return Ok(None);
            }
            let class = class_for(classes, visit.expression, budget)?.ok_or(Failure::Invalid)?;
            for feed in &topology.bindings[visit.binding_start..visit.binding_end] {
                if !validate_feed(self.graph, source_bindings, bindings, *feed, visit.expression, class, budget)? {
                    return Ok(None);
                }
            }
        }
        if expected_start != topology.bindings.len() { return Ok(None); }
        charge(budget, topology.residuals.len())?;
        for feed in topology.residuals {
            let (_, expression) = self.graph.evidence.get(feed.evidence_ordinal).ok_or(Failure::Invalid)?;
            charge(budget, 1)?;
            if covered.contains(expression) || !add_local(*expression, budget)? { return Ok(None); }
            let class = class_for(classes, *expression, budget)?.ok_or(Failure::Invalid)?;
            if !validate_feed(self.graph, source_bindings, bindings, *feed, *expression, class, budget)? {
                return Ok(None);
            }
        }
        // Root extracts the complete residual vector. Do not infer a missing
        // binding/key match to mean it has no obligation.
        let mut creation_requests = Vec::new();
        let mut creation_seen = HashSet::new();
        let request_bound = input.alternatives.len().checked_mul(topology.visits.len()).ok_or(Failure::Resource)?;
        charge(budget, request_bound)?;
        creation_requests.try_reserve(request_bound).map_err(|_| Failure::Resource)?;
        creation_seen.try_reserve(request_bound).map_err(|_| Failure::Resource)?;
        for alternative in &input.alternatives {
            for visit in topology.visits {
                if visit.lexical {
                    let request = CreationRequest { scope: alternative.creation, expression: visit.expression };
                    if creation_seen.insert(request) { creation_requests.push(request); }
                }
            }
        }
        // Full immutable equality, not atom-set equality. Neither the parent
        // occurrence ScopeId nor an original ancestry prefix enters this key.
        let mut hash = DefaultHasher::new();
        evidence.hash(&mut hash); function.hash(&mut hash);
        charge(budget, input.alternatives.len())?;
        input.alternatives.len().hash(&mut hash);
        for alternative in &input.alternatives { hash_alternative(alternative, &mut hash); }
        charge(budget, bindings.len())?;
        bindings.len().hash(&mut hash);
        for binding in bindings {
            binding.route.hash(&mut hash); binding.class.hash(&mut hash);
            charge(budget, binding.alternatives.len())?;
            binding.alternatives.len().hash(&mut hash);
            for alternative in &binding.alternatives { hash_alternative(alternative, &mut hash); }
        }
        charge(budget, topology.visits.len().checked_add(topology.bindings.len())
            .and_then(|n| n.checked_add(topology.residuals.len()))
            .and_then(|n| n.checked_add(classes.len())).ok_or(Failure::Resource)?)?;
        topology.visits.hash(&mut hash); topology.bindings.hash(&mut hash);
        topology.residuals.hash(&mut hash); classes.hash(&mut hash);
        let digest = hash.finish();
        charge(budget, 1)?;
        if let Some(candidates) = self.by_digest.get(&digest) {
            charge(budget, candidates.len())?;
            for &id in candidates {
                let old = self.plan(id)?;
                charge(budget, old.alternatives.len().checked_add(input.alternatives.len())
                    .and_then(|n| n.checked_add(topology.visits.len()))
                    .and_then(|n| n.checked_add(topology.bindings.len()))
                    .and_then(|n| n.checked_add(topology.residuals.len()))
                    .and_then(|n| n.checked_add(classes.len())).ok_or(Failure::Resource)?)?;
                if old.evidence != evidence || old.function != function
                    || old.visits != topology.visits || old.binding_feeds != topology.bindings
                    || old.residuals != topology.residuals || old.classes != classes
                    || old.alternatives.len() != input.alternatives.len()
                    || !old.alternatives.iter().zip(&input.alternatives).all(|(l, r)| same_alternative(l, r))
                    || old.bindings.len() != bindings.len() { continue; }
                let mut same = true;
                for (old, new) in old.bindings.iter().zip(bindings) { same &= same_value(old, new, budget)?; }
                if same { return Ok(Some((id, false))); }
            }
        }
        let plan = Plan { digest, graph: self.graph, evidence, function, declared,
            alternatives: copy_slice(&input.alternatives, budget)?, bindings: copy_values(bindings, budget)?,
            visits: copy_slice(topology.visits, budget)?, binding_feeds: copy_slice(topology.bindings, budget)?,
            residuals: copy_slice(topology.residuals, budget)?, classes: copy_slice(classes, budget)?,
            creation_requests, local_requests, scope: None, completed: None };
        // Flat owned vectors and their eventual failed-attempt cleanup.
        let cleanup = plan.alternatives.len().checked_add(plan.bindings.len())
            .and_then(|n| n.checked_add(plan.visits.len()))
            .and_then(|n| n.checked_add(plan.binding_feeds.len()))
            .and_then(|n| n.checked_add(plan.residuals.len()))
            .and_then(|n| n.checked_add(plan.classes.len()))
            .and_then(|n| n.checked_add(plan.creation_requests.len()))
            .and_then(|n| n.checked_add(plan.local_requests.len())).ok_or(Failure::Resource)?;
        charge(budget, cleanup.checked_add(3).ok_or(Failure::Resource)?)?;
        for binding in &plan.bindings { charge(budget, binding.alternatives.len())?; }
        self.plans.try_reserve(1).map_err(|_| Failure::Resource)?;
        self.by_digest.try_reserve(1).map_err(|_| Failure::Resource)?;
        let id = PlanId(self.plans.len());
        match self.by_digest.entry(digest) {
            std::collections::hash_map::Entry::Occupied(mut entry) => {
                entry.get_mut().try_reserve(1).map_err(|_| Failure::Resource)?;
                self.plans.push(plan); entry.get_mut().push(id);
            }
            std::collections::hash_map::Entry::Vacant(entry) => {
                let mut ids = Vec::new();
                ids.try_reserve(1).map_err(|_| Failure::Resource)?;
                self.plans.push(plan); ids.push(id); entry.insert(ids);
            }
        }
        Ok(Some((id, true)))
    }

    pub(super) fn creation_requests(&self, id: PlanId) -> Result<&[CreationRequest], Failure> {
        Ok(&self.plan(id)?.creation_requests)
    }

    pub(super) fn local_requests(&self, id: PlanId) -> Result<&[usize], Failure> {
        Ok(&self.plan(id)?.local_requests)
    }

    // The owner resolves creation_requests in exactly this order. ALL checks
    // precede route allocation. A missing request/value is never Empty.
    pub(super) fn incoming(&self, id: PlanId, creations: &[Value], routes: &mut Routes,
        budget: &mut TypeWorkBudget) -> Result<Option<IncomingEnvironment>, Failure>
    {
        let plan = self.plan(id)?;
        if creations.len() != plan.creation_requests.len() { return Ok(None); }
        charge(budget, creations.len())?;
        for (request, value) in plan.creation_requests.iter().zip(creations) {
            let class = class_for(&plan.classes, request.expression, budget)?.ok_or(Failure::Invalid)?;
            if !compatible(class, value.class) { return Ok(None); }
        }
        let mut rows = Vec::new();
        charge(budget, plan.local_requests.len())?;
        rows.try_reserve_exact(plan.local_requests.len()).map_err(|_| Failure::Resource)?;
        for &expression in &plan.local_requests {
            rows.push(IncomingRow { expression,
                class: class_for(&plan.classes, expression, budget)?.ok_or(Failure::Invalid)?, feeds: Vec::new() });
        }
        for alternative in &plan.alternatives {
            charge(budget, plan.visits.len())?;
            for visit in &plan.visits {
                for feed in &plan.binding_feeds[visit.binding_start..visit.binding_end] {
                    let value = plan.bindings.get(feed.binding_ordinal).ok_or(Failure::Invalid)?;
                    append_feed(&mut rows, visit.expression, value, alternative.gate, routes, budget)?;
                }
                if visit.lexical {
                    charge(budget, plan.creation_requests.len())?;
                    let position = plan.creation_requests.iter().position(|request|
                        request.scope == alternative.creation && request.expression == visit.expression)
                        .ok_or(Failure::Invalid)?;
                    append_feed(&mut rows, visit.expression, &creations[position], alternative.gate, routes, budget)?;
                }
            }
            // Residuals belong after THIS alternative's full visit vector.
            charge(budget, plan.residuals.len())?;
            for feed in &plan.residuals {
                let expression = plan.graph.evidence.get(feed.evidence_ordinal).ok_or(Failure::Invalid)?.1;
                let value = plan.bindings.get(feed.binding_ordinal).ok_or(Failure::Invalid)?;
                append_feed(&mut rows, expression, value, alternative.gate, routes, budget)?;
            }
        }
        Ok(Some(IncomingEnvironment { plan: id, rows }))
    }

    // CompleteE(x) = LOCAL_E(x) plus every incoming original writer in order.
    // Nonleaf captures MUST reach this API after actual local evaluation in E;
    // they cannot be replaced by a raw-creation capture route.
    pub(super) fn finish_expression(&self, incoming: &IncomingEnvironment, expression: usize,
        local: &Value, routes: &mut Routes, budget: &mut TypeWorkBudget,
    ) -> Result<Option<Value>, Failure> {
        self.plan(incoming.plan)?;
        charge(budget, incoming.rows.len())?;
        let row = incoming.rows.iter().find(|row| row.expression == expression).ok_or(Failure::Invalid)?;
        if !compatible(row.class, local.class) { return Ok(None); }
        let mut values = Vec::new();
        charge(budget, row.feeds.len().checked_add(1).ok_or(Failure::Resource)?)?;
        values.try_reserve_exact(row.feeds.len().checked_add(1).ok_or(Failure::Resource)?)
            .map_err(|_| Failure::Resource)?;
        values.push(local);
        values.extend(row.feeds.iter());
        join_values(row.class, &values, routes, budget).map(Some)
    }

    // One frame for the complete shared E, never one frame per incoming
    // creation. Provider conjunction consequently sees the SAME completed
    // capture environment for every specialized G alternative.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn complete(&mut self, id: PlanId, scope: ScopeId, complete_values: &[Value],
        parent_activation: RouteId, admitted: &AdmittedFrame, types: &mut Types,
        routes: &mut Routes, budget: &mut TypeWorkBudget,
    ) -> Result<Option<Completion>, Failure> {
        let plan = self.plan(id)?;
        if admitted.function != plan.function || plan.scope != Some(scope)
            || complete_values.len() != plan.local_requests.len() {
            return Ok(None);
        }
        if let Some(completed) = &plan.completed {
            charge(budget, complete_values.len())?;
            if completed.complete_routes.len() != complete_values.len()
                || !completed.complete_routes.iter().zip(complete_values).all(|(route, value)| *route == value.route)
            { return Err(Failure::Invalid); }
            return completion(completed, parent_activation, routes, budget).map(Some);
        }
        charge(budget, complete_values.len())?;
        for (&expression, value) in plan.local_requests.iter().zip(complete_values) {
            let class = class_for(&plan.classes, expression, budget)?.ok_or(Failure::Invalid)?;
            if !compatible(class, value.class) { return Ok(None); }
        }
        let mut captures = Vec::new();
        let mut classes = Vec::new();
        let mut supports = Vec::new();
        let mut origins = Vec::new();
        charge(budget, plan.declared.len().checked_add(plan.local_requests.len())
            .and_then(|n| n.checked_add(plan.alternatives.len())).ok_or(Failure::Resource)?)?;
        captures.try_reserve_exact(plan.declared.len()).map_err(|_| Failure::Resource)?;
        classes.try_reserve_exact(plan.declared.len()).map_err(|_| Failure::Resource)?;
        supports.try_reserve_exact(plan.local_requests.len()).map_err(|_| Failure::Resource)?;
        origins.try_reserve_exact(plan.alternatives.len()).map_err(|_| Failure::Resource)?;
        for &expression in plan.declared {
            charge(budget, plan.local_requests.len())?;
            let position = plan.local_requests.iter().position(|e| *e == expression).ok_or(Failure::Invalid)?;
            captures.push((expression, complete_values[position].route));
            classes.push(class_for(&plan.classes, expression, budget)?.ok_or(Failure::Invalid)?);
        }
        for (&expression, value) in plan.local_requests.iter().zip(complete_values) {
            charge(budget, plan.declared.len())?;
            if matches!(plan.graph.expressions.get(expression), Some(Expr::Slot)) && !plan.declared.contains(&expression) {
                supports.push((expression, value.route));
            }
        }
        for alternative in &plan.alternatives { origins.push((alternative.origin, alternative.gate)); }
        let origin = TypeOrigin::Conditional(types.conditional(&origins, budget)?);
        let pending = routes.bindings_with_support(plan.function, plan.declared, &captures, &classes,
            origin, &supports, budget)?;
        let frame = routes.complete_under(pending, admitted)?;
        let construct = routes.equation_construct(plan.function, frame, budget)?;
        let free = routes.free(budget)?;
        let mut ready = Vec::new();
        charge(budget, plan.alternatives.len())?;
        ready.try_reserve_exact(plan.alternatives.len()).map_err(|_| Failure::Resource)?;
        for alternative in &plan.alternatives {
            let count = plan.bindings.len().checked_add(1).ok_or(Failure::Resource)?;
            charge(budget, count)?;
            let mut inputs = Vec::new();
            inputs.try_reserve_exact(count).map_err(|_| Failure::Resource)?;
            inputs.push(alternative.gate);
            inputs.extend(plan.bindings.iter().map(|binding| binding.route));
            ready.push(routes.equation_ready(&inputs, free, budget)?);
        }
        // OR of boolean readiness routes. This is not a union of independently
        // specialized capture environments and never selects the first origin.
        let any_ready = match ready.as_slice() {
            [one] => *one,
            _ => routes.equation_join(ProjectionClass::Metadata, &ready, budget)?,
        };
        let route = routes.equation_ready(&[any_ready], construct, budget)?;
        charge(budget, 1)?;
        let mut alternatives = Vec::new();
        alternatives.try_reserve_exact(1).map_err(|_| Failure::Resource)?;
        alternatives.push(ClosureAlternative { function: plan.function, frame, creation: scope, origin, gate: route });
        charge(budget, complete_values.len().checked_mul(2).ok_or(Failure::Resource)?)?;
        let mut complete_routes = Vec::new();
        complete_routes.try_reserve_exact(complete_values.len()).map_err(|_| Failure::Resource)?;
        complete_routes.extend(complete_values.iter().map(|value| value.route));
        let completed = Completed { value: Value { route, class: ProjectionClass::Callable(plan.function), alternatives },
            complete_routes, frame, origin, any_ready };
        let result = completion(&completed, parent_activation, routes, budget)?;
        // Cache and rollback journal publish together; replay does not mint
        // another frame. Different actual parents still stage their OWN demand.
        charge(budget, 3)?;
        self.completions.try_reserve(1).map_err(|_| Failure::Resource)?;
        self.plans.get_mut(id.0).ok_or(Failure::Invalid)?.completed = Some(completed);
        self.completions.push(id);
        Ok(Some(result))
    }
}

fn completion(completed: &Completed, parent_activation: RouteId, routes: &mut Routes,
    budget: &mut TypeWorkBudget) -> Result<Completion, Failure> {
    let free = routes.free(budget)?;
    let activation_condition = routes.equation_ready(&[parent_activation, completed.any_ready], free, budget)?;
    Ok(Completion { value: completed.value.copy(budget)?, frame: completed.frame,
        origin: completed.origin, activation_condition })
}

fn validate_feed(graph: &Graph,
    tuples: &[(crate::interface::RequirementId, crate::interface::MethodId, usize)],
    values: &[Value], feed: DictionaryFeed, target: usize, class: ProjectionClass,
    budget: &mut TypeWorkBudget,
) -> Result<bool, Failure> {
    charge(budget, 3)?;
    let &(key, expression) = graph.evidence.get(feed.evidence_ordinal).ok_or(Failure::Invalid)?;
    let tuple = tuples.get(feed.binding_ordinal).ok_or(Failure::Invalid)?;
    let value = values.get(feed.binding_ordinal).ok_or(Failure::Invalid)?;
    Ok(expression == target && key == (tuple.0, tuple.1) && graph.expressions.get(tuple.2).is_some()
        && compatible(class, value.class))
}

fn append_feed(rows: &mut [IncomingRow], expression: usize, source: &Value, gate: RouteId,
    routes: &mut Routes, budget: &mut TypeWorkBudget,
) -> Result<(), Failure> {
    charge(budget, rows.len())?;
    let row = rows.iter_mut().find(|row| row.expression == expression).ok_or(Failure::Invalid)?;
    let route = routes.equation_ready(&[gate], source.route, budget)?;
    charge(budget, source.alternatives.len().checked_add(1).ok_or(Failure::Resource)?)?;
    let mut alternatives = Vec::new();
    alternatives.try_reserve_exact(source.alternatives.len()).map_err(|_| Failure::Resource)?;
    for alternative in &source.alternatives {
        let alternative_gate = routes.equation_ready(&[gate], alternative.gate, budget)?;
        alternatives.push(ClosureAlternative { gate: alternative_gate, ..*alternative });
    }
    row.feeds.try_reserve(1).map_err(|_| Failure::Resource)?;
    row.feeds.push(Value { route, class: source.class, alternatives });
    Ok(())
}

fn join_values(class: ProjectionClass, values: &[&Value], routes: &mut Routes,
    budget: &mut TypeWorkBudget,
) -> Result<Value, Failure> {
    charge(budget, values.len())?;
    let mut inputs = Vec::new();
    let mut alternatives = Vec::new();
    inputs.try_reserve_exact(values.len()).map_err(|_| Failure::Resource)?;
    for value in values {
        inputs.push(value.route);
        charge(budget, value.alternatives.len())?;
        alternatives.try_reserve(value.alternatives.len()).map_err(|_| Failure::Resource)?;
        alternatives.extend_from_slice(&value.alternatives);
    }
    let route = match inputs.as_slice() {
        [] => routes.empty(budget)?,
        [one] => *one,
        _ => routes.equation_join(class, &inputs, budget)?,
    };
    Ok(Value { route, class, alternatives })
}
