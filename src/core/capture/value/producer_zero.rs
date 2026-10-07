//! Exact saved-zero heads plus static closure sidecars for the shared iterative
//! producer driver. No observed answer is cached, and no original context,
//! slot, head, demand activation or root feed is installed by this helper.

use std::collections::HashMap;

use super::{AdmittedFrame, Expr, Failure, Graph, TypeWorkBudget, charge, copy_slice};
use super::deferred_frame::{Arena as Routes, OriginalPort, ProjectionClass, RouteId};
use super::local_recipe::{Compiler, SlotRole};
use super::producer::{ClosureAlternative, Registry, ScopeKind,
    TypedBranch, TypedStage, Value};
use super::support_plan::SupportKind;
use super::typed_environment::{self, Arena as Types, TypeOrigin};

// Owner-supplied proof data, not a shape-derived admission token. The owner has
// checked no incoming Invoke/Root recurrence reaches context zero and has
// inventoried all zero writers for EACH listed original Slot. Dictionary
// initialization at Call contexts and metadata initialization at Root/Invoke
// contexts do not by themselves prove this. The helper rechecks static roles.
pub(super) struct ZeroCertificate<'g, 'a> {
    pub(super) graph: &'g Graph,
    pub(super) empty_slots: &'a [usize],
}

// Created only by the original context owner after proving context=Call(0,e).
// The owner may intern that canonical coordinate as paid monotone bookkeeping
// before acceptance. Descriptor preparation must not acquire its slots, heads,
// activation or publication authority; the coordinate alone proves no value.
pub(super) struct ExactEvidenceZero {
    pub(super) expression: usize,
    pub(super) context: usize,
}

#[derive(Clone, Copy, Debug)]
pub(super) enum Decline {
    WrongGraph,
    Unsupported,
    Class,
    MissingZeroWriter,
    MissingCanonical,
    TypedWitness,
    EvidencePayload,
}

// These are original coordinates. The root driver schedules dependencies
// before their finish job; no helper recursively walks expressions/factories.
pub(super) enum Request {
    Slot { expression: usize, role: SlotRole, class: ProjectionClass, empty: bool },
    Alias { expression: usize, child: usize, class: ProjectionClass },
    Merge { expression: usize, inputs: Vec<usize> },
    TypedCall { expression: usize, function: usize, arguments: Vec<usize>,
        factory: usize, returned: usize },
    Evidence { expression: usize, payload: usize, factory: usize, returned: usize },
}

// Only pure canonical metadata EQUATIONS live here. Saved Value.route remains
// the exact original head (or a certified empty Slot); these are never atom
// answers or substitutes for real q@0 readiness. Pair with the same arenas.
pub(super) struct ZeroState {
    pub(super) canonical_metadata: HashMap<usize, RouteId>,
}

impl ZeroState {
    pub(super) fn new() -> Self { Self { canonical_metadata: HashMap::new() } }

    pub(super) fn canonical(&self, expression: usize, budget: &mut TypeWorkBudget)
        -> Result<Option<RouteId>, Failure>
    {
        charge(budget, 1)?;
        Ok(self.canonical_metadata.get(&expression).copied())
    }

    fn retain(&mut self, expression: usize, route: RouteId,
        budget: &mut TypeWorkBudget) -> Result<(), Failure>
    {
        charge(budget, 1)?;
        if let Some(old) = self.canonical_metadata.get(&expression) {
            return if *old == route { Ok(()) } else { Err(Failure::Invalid) };
        }
        self.canonical_metadata.try_reserve(1).map_err(|_| Failure::Resource)?;
        self.canonical_metadata.insert(expression, route);
        Ok(())
    }
}

pub(super) fn request(registry: &Registry<'_>, compiler: &mut Compiler<'_>,
    expression: usize, certificate: &ZeroCertificate<'_, '_>, budget: &mut TypeWorkBudget,
) -> Result<Result<Request, Decline>, Failure> {
    if !std::ptr::eq(registry.graph, certificate.graph) { return Ok(Err(Decline::WrongGraph)); }
    let Some(source) = registry.graph.expressions.get(expression) else { return Err(Failure::Invalid); };
    let Some(class) = compiler.prove_source_class(expression, budget)? else {
        return Ok(Err(Decline::Class));
    };
    let prepared = compiler.prepared(expression).ok_or(Failure::Invalid)?;
    if !std::ptr::eq(prepared.source, source) { return Ok(Err(Decline::WrongGraph)); }
    Ok(Ok(match source {
        Expr::Slot => {
            let Some(role) = compiler.source_slot_role(expression, budget)? else {
                return Ok(Err(Decline::Unsupported));
            };
            let empty = match role {
                SlotRole::Global { .. } | SlotRole::Lexical { .. }
                    if matches!(class, ProjectionClass::Callable(_)) => false,
                SlotRole::Resource if class == ProjectionClass::Metadata => false,
                SlotRole::Metadata | SlotRole::Dictionary { .. } | SlotRole::Unbound => {
                    charge(budget, certificate.empty_slots.len())?;
                    if !certificate.empty_slots.contains(&expression) {
                        return Ok(Err(Decline::MissingZeroWriter));
                    }
                    // Also reject assignment/resource/provider/ambiguous roles;
                    // this static check is necessary, never the zero proof.
                    if compiler.fresh_raw_slot_role(expression, budget)?.is_none() {
                        return Ok(Err(Decline::Unsupported));
                    }
                    true
                }
                _ => return Ok(Err(Decline::Unsupported)),
            };
            Request::Slot { expression, role, class, empty }
        }
        Expr::Alias(child) => {
            if !compiler.raw_local_recipe(expression, budget)? {
                return Ok(Err(Decline::Unsupported));
            }
            Request::Alias { expression, child: *child, class }
        }
        Expr::Merge(inputs) => {
            if class != ProjectionClass::Metadata || !compiler.raw_local_recipe(expression, budget)? {
                return Ok(Err(Decline::Class));
            }
            Request::Merge { expression, inputs: copy_slice(inputs, budget)? }
        }
        Expr::Call { function, arguments, type_application: true, .. } => {
            if !compiler.raw_local_recipe(expression, budget)? {
                return Ok(Err(Decline::Unsupported));
            }
            let relation = registry.relation(expression)?;
            if class != ProjectionClass::Callable(relation.body) {
                return Ok(Err(Decline::Class));
            }
            Request::TypedCall { expression, function: *function,
                arguments: copy_slice(arguments, budget)?, factory: relation.factory,
                returned: relation.body }
        }
        Expr::Evidence { .. } => {
            let Some(payload) = compiler.direct_evidence_payload(expression, budget)? else {
                return Ok(Err(Decline::EvidencePayload));
            };
            if class != ProjectionClass::Callable(payload.body) {
                return Ok(Err(Decline::Class));
            }
            Request::Evidence { expression, payload: payload.payload,
                factory: payload.factory, returned: payload.body }
        }
        _ => return Ok(Err(Decline::Unsupported)),
    }))
}

pub(super) fn finish_slot(state: &mut ZeroState, expression: usize, role: SlotRole,
    class: ProjectionClass, empty: bool, routes: &mut Routes, budget: &mut TypeWorkBudget,
) -> Result<Value, Failure> {
    // `empty` comes only from the successful Request::Slot above. Globals and
    // lexical methods remain opaque. Resource metadata is also exact opaque
    // input, never a canonical Empty/Free or permission for raw support.
    if empty {
        if !matches!(role, SlotRole::Metadata | SlotRole::Dictionary { .. } | SlotRole::Unbound) {
            return Err(Failure::Invalid);
        }
        let route = routes.empty(budget)?;
        if matches!(class, ProjectionClass::Empty | ProjectionClass::Metadata) {
            state.retain(expression, route, budget)?;
        }
        return Ok(Value::opaque(route, ProjectionClass::Empty));
    }
    if !matches!((role, class),
        (SlotRole::Global { .. } | SlotRole::Lexical { .. }, ProjectionClass::Callable(_))
        | (SlotRole::Resource, ProjectionClass::Metadata)) {
        return Err(Failure::Invalid);
    }
    Ok(Value::opaque(head(expression, 0, routes, budget)?, class))
}

pub(super) fn finish_alias(state: &mut ZeroState, expression: usize, child: usize,
    class: ProjectionClass, value: &Value, routes: &mut Routes, budget: &mut TypeWorkBudget,
) -> Result<Result<Value, Decline>, Failure> {
    if value.class != ProjectionClass::Empty && value.class != class {
        return Ok(Err(Decline::Class));
    }
    if matches!(class, ProjectionClass::Metadata | ProjectionClass::Empty) {
        let Some(route) = state.canonical(child, budget)? else {
            return Ok(Err(Decline::MissingCanonical));
        };
        state.retain(expression, route, budget)?;
    }
    let mut result = saved_head(expression, value, routes, budget)?;
    result.class = class;
    Ok(Ok(result))
}

pub(super) fn finish_merge(state: &mut ZeroState, expression: usize, inputs: &[usize],
    routes: &mut Routes, budget: &mut TypeWorkBudget,
) -> Result<Result<Value, Decline>, Failure> {
    charge(budget, inputs.len())?;
    let mut children = Vec::new();
    children.try_reserve_exact(inputs.len()).map_err(|_| Failure::Resource)?;
    for input in inputs {
        let Some(route) = state.canonical(*input, budget)? else {
            return Ok(Err(Decline::MissingCanonical));
        };
        children.push(route);
    }
    let canonical = match children.as_slice() {
        [] => routes.free(budget)?,
        [one] => routes.metadata_view(*one, budget)?,
        _ => {
            charge(budget, children.len().checked_add(1).ok_or(Failure::Resource)?)?;
            children.try_reserve(1).map_err(|_| Failure::Resource)?;
            children.insert(0, routes.free(budget)?);
            routes.equation_join(ProjectionClass::Metadata, &children, budget)?
        }
    };
    state.retain(expression, canonical, budget)?;
    Ok(Ok(Value::opaque(head(expression, 0, routes, budget)?, ProjectionClass::Metadata)))
}

// Normalize with canonical pure zero metadata, while retaining EXACT original
// callee/actual heads for real local readiness. Real q@0 uses the same canonical
// normalization inputs at its authenticated boundary; otherwise keys differ.
// No activation edge is needed from the inert Zero scope.
pub(super) fn begin_typed(registry: &mut Registry<'_>, state: &ZeroState,
    expression: usize, types: &mut Types, routes: &mut Routes, budget: &mut TypeWorkBudget,
) -> Result<Result<TypedStage, Decline>, Failure> {
    let relation = registry.relation(expression)?;
    let Some(Expr::Call { function, arguments, type_application: true, .. }) =
        registry.graph.expressions.get(expression) else { return Err(Failure::Invalid); };
    let Some(checked) = typed_environment::check_global_factory_shape(registry.graph, expression, budget)?
        else { return Ok(Err(Decline::TypedWitness)); };
    if checked.factory() != relation.factory { return Ok(Err(Decline::TypedWitness)); }
    charge(budget, arguments.len().checked_add(1).ok_or(Failure::Resource)?)?;
    let mut canonical = Vec::new();
    let mut inputs = Vec::new();
    canonical.try_reserve_exact(arguments.len()).map_err(|_| Failure::Resource)?;
    inputs.try_reserve_exact(arguments.len().checked_add(1).ok_or(Failure::Resource)?)
        .map_err(|_| Failure::Resource)?;
    inputs.push(head(*function, 0, routes, budget)?);
    for argument in arguments {
        let Some(route) = state.canonical(*argument, budget)? else {
            return Ok(Err(Decline::MissingCanonical));
        };
        canonical.push(route);
        inputs.push(head(*argument, 0, routes, budget)?);
    }
    let Some(normalized) = types.normalize_closed_symbolic(&checked, &canonical, budget)? else {
        return Ok(Err(Decline::TypedWitness));
    };
    // This identity is retained before the caller requests even one capture.
    let (scope, _) = registry.intern_raw(relation.factory, normalized, &canonical, types, routes, budget)?;
    charge(budget, 1)?;
    let mut branches = Vec::new();
    branches.try_reserve_exact(1).map_err(|_| Failure::Resource)?;
    branches.push(TypedBranch { scope, origin_gate: routes.free(budget)? });
    Ok(Ok(TypedStage { parent: registry.zero(), expression, returned: relation.body, inputs, branches }))
}

pub(super) fn finish_typed(registry: &Registry<'_>, stage: &TypedStage,
    routes: &mut Routes, budget: &mut TypeWorkBudget) -> Result<Value, Failure>
{
    if stage.parent != registry.zero() { return Err(Failure::Invalid); }
    let predicted = registry.finish_typed(stage, routes, budget)?;
    saved_head(stage.expression, &predicted, routes, budget)
}

// One actual E0 environment, retaining all direct payload type origins. Unlike
// virtual Evidence, these coordinates are original Head(x,E0) projections;
// no lexical/dictionary unions are predicted and no E0 slots are installed.
pub(super) fn finish_evidence(registry: &mut Registry<'_>, compiler: &mut Compiler<'_>,
    exact: &ExactEvidenceZero, payload: &Value, admitted: &AdmittedFrame,
    types: &mut Types, routes: &mut Routes, budget: &mut TypeWorkBudget,
) -> Result<Result<Value, Decline>, Failure> {
    let expression = exact.expression;
    if exact.context == 0 { return Err(Failure::Invalid); }
    let Some(direct) = compiler.direct_evidence_payload(expression, budget)? else {
        return Ok(Err(Decline::EvidencePayload));
    };
    let original_payload = registry.graph.expressions.get(direct.payload).ok_or(Failure::Invalid)?;
    let prepared = compiler.prepared(direct.payload).ok_or(Failure::Invalid)?;
    if !std::ptr::eq(prepared.source, original_payload) { return Ok(Err(Decline::WrongGraph)); }
    if payload.class != ProjectionClass::Callable(direct.body) || payload.alternatives.is_empty()
        || admitted.function != direct.body { return Ok(Err(Decline::EvidencePayload)); }
    let qualified = registry.factory(direct.factory)?;
    if qualified.returned() != direct.body { return Err(Failure::Invalid); }
    let captures = qualified.returned_support().captures();
    let visits = qualified.returned_support().visits();
    charge(budget, captures.len().checked_add(visits.len()).and_then(|n|
        n.checked_add(payload.alternatives.len())).ok_or(Failure::Resource)?)?;
    let saved = head(expression, 0, routes, budget)?;
    let mut origins = Vec::new();
    origins.try_reserve_exact(payload.alternatives.len()).map_err(|_| Failure::Resource)?;
    for alternative in &payload.alternatives {
        if alternative.function != direct.body || routes.function(alternative.frame)? != direct.body {
            return Ok(Err(Decline::EvidencePayload));
        }
        let free = routes.free(budget)?;
        let gate = routes.equation_ready(&[saved, alternative.gate], free, budget)?;
        origins.push((alternative.origin, gate));
    }
    let origin = TypeOrigin::Conditional(types.conditional(&origins, budget)?);
    let mut bindings = Vec::new();
    let mut classes = Vec::new();
    let mut supports = Vec::new();
    bindings.try_reserve_exact(captures.len()).map_err(|_| Failure::Resource)?;
    classes.try_reserve_exact(captures.len()).map_err(|_| Failure::Resource)?;
    supports.try_reserve_exact(visits.len()).map_err(|_| Failure::Resource)?;
    for capture in captures {
        let Some(class) = compiler.prove_source_class(*capture, budget)? else {
            return Ok(Err(Decline::Class));
        };
        bindings.push((*capture, head(*capture, exact.context, routes, budget)?));
        classes.push(class);
    }
    for visit in visits {
        if !matches!(visit.kind, SupportKind::Terminal(_)) { continue; }
        charge(budget, captures.len())?;
        if captures.contains(&visit.expression) { continue; }
        if compiler.prove_source_class(visit.expression, budget)?.is_none() {
            return Ok(Err(Decline::Class));
        }
        supports.push((visit.expression, head(visit.expression, exact.context, routes, budget)?));
    }
    // This is a staging sidecar only. It never enters the canonical original
    // constructor cache, even with zero deep supports. Actual material e0 owns
    // Closure(G,E0) and its live type provenance. The sidecar frame keeps exact
    // original context provenance; only its Value carries conditional types.
    let pending = routes.bindings_with_support(direct.body, captures, &bindings, &classes,
        TypeOrigin::OriginalContext(exact.context), &supports, budget)?;
    let frame = routes.complete_under(pending, admitted)?;
    let scope = registry.append_scope(ScopeKind::SavedEvidence { expression }, origin, routes, budget)?;
    registry.complete_external_scope(scope, origin, frame, routes, budget)?;
    charge(budget, 1)?;
    let mut alternatives = Vec::new();
    alternatives.try_reserve_exact(1).map_err(|_| Failure::Resource)?;
    alternatives.push(ClosureAlternative { function: direct.body, frame,
        creation: scope, origin, gate: saved });
    Ok(Ok(Value { route: saved, class: ProjectionClass::Callable(direct.body), alternatives }))
}

fn head(expression: usize, context: usize, routes: &mut Routes,
    budget: &mut TypeWorkBudget) -> Result<RouteId, Failure>
{
    routes.head(OriginalPort { expression, context }, budget)
}

fn saved_head(expression: usize, predicted: &Value, routes: &mut Routes,
    budget: &mut TypeWorkBudget) -> Result<Value, Failure>
{
    let route = head(expression, 0, routes, budget)?;
    let mut alternatives = copy_slice(&predicted.alternatives, budget)?;
    charge(budget, alternatives.len())?;
    for alternative in &mut alternatives { alternative.gate = route; }
    Ok(Value { route, class: predicted.class, alternatives })
}
