//! Private source staging. No original slot, head, root feed or activation is
//! published here. The owner supplies whole-family/actual-context admission,
//! drives the explicit requests, and publishes only after the batch is complete.

use std::collections::{HashMap, HashSet};

use super::{AdmittedFrame, Expr, Failure, Graph, TypeWorkBudget, charge, copy_slice};
use super::deferred_frame::{ActivationId, Arena as Routes, CompletedFrame,
    ProjectionClass, RouteId};
use super::support_plan::{QualifiedFamily, QualifiedFactory, TypedCallRelation};
use super::typed_environment::{self, Arena as Types, NormalizedEnvironmentId, TypeOrigin};

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(super) struct ScopeId(pub(super) usize);

#[derive(Clone, Copy)]
pub(super) struct ClosureAlternative {
    pub(super) function: usize,
    pub(super) frame: CompletedFrame,
    pub(super) creation: ScopeId,
    pub(super) origin: TypeOrigin,
    pub(super) gate: RouteId,
}

pub(super) struct Value {
    pub(super) route: RouteId,
    pub(super) class: ProjectionClass,
    pub(super) alternatives: Vec<ClosureAlternative>,
}

impl Value {
    pub(super) fn copy(&self, budget: &mut TypeWorkBudget) -> Result<Self, Failure> {
        Ok(Self { route: self.route, class: self.class,
            alternatives: copy_slice(&self.alternatives, budget)? })
    }
    pub(super) fn opaque(route: RouteId, class: ProjectionClass) -> Self {
        Self { route, class, alternatives: Vec::new() }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum ScopeKind {
    Zero,
    Raw { factory: usize, normalized: NormalizedEnvironmentId },
    Evidence { expression: usize },
    SavedEvidence { expression: usize },
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum ScopeState { Prepared, Complete }

pub(super) struct Scope {
    pub(super) kind: ScopeKind,
    pub(super) origin: TypeOrigin,
    pub(super) activation: ActivationId,
    pub(super) activation_route: RouteId,
    pub(super) state: ScopeState,
    pub(super) actuals: Vec<RouteId>,
    pub(super) frame: Option<CompletedFrame>,
}

#[derive(Clone, Copy)]
pub(super) struct TypedBranch {
    pub(super) scope: ScopeId,
    pub(super) origin_gate: RouteId,
}

pub(super) struct TypedStage {
    pub(super) parent: ScopeId,
    pub(super) expression: usize,
    pub(super) returned: usize,
    // Exact local callee, followed by every ordered metadata actual. The
    // saved complete q output is deliberately absent from readiness.
    pub(super) inputs: Vec<RouteId>,
    pub(super) branches: Vec<TypedBranch>,
}

#[derive(Clone, Copy)]
pub(super) struct RootFeed {
    pub(super) factory: usize,
    pub(super) returned: usize,
    pub(super) capture: usize,
    pub(super) route: RouteId,
}

#[derive(Clone, Copy, Eq, PartialEq)]
enum ExtensionPhase { Preparing, Publishing }

// One exclusive source-owner attempt. Undo work is prepaid with each staged
// mutation, so abort remains available after work or allocation refusal.
struct Extension {
    phase: ExtensionPhase,
    scope_start: usize,
    activation_start: usize,
    root_feed_start: usize,
    memo_keys: Vec<(ScopeId, usize)>,
    local_memo_keys: Vec<(ScopeId, usize)>,
    raw_keys: Vec<NormalizedEnvironmentId>,
}

pub(super) struct Registry<'g> {
    pub(super) graph: &'g Graph,
    pub(super) scopes: Vec<Scope>,
    pub(super) memo: HashMap<(ScopeId, usize), Value>,
    pub(super) local_memo: HashMap<(ScopeId, usize), Value>,
    families: Vec<QualifiedFamily<'g>>,
    factories: HashMap<usize, (usize, usize)>,
    relations: HashMap<usize, TypedCallRelation>,
    raw_scopes: HashMap<NormalizedEnvironmentId, ScopeId>,
    // Dedup equations, never original ancestry paths or observed atom answers.
    activation_edges: HashSet<(ActivationId, RouteId)>,
    pub(super) staged_activation_edges: Vec<(ActivationId, RouteId)>,
    pub(super) staged_root_feeds: Vec<RootFeed>,
    extension: Option<Extension>,
}

impl<'g> Registry<'g> {
    pub(super) fn new(graph: &'g Graph, routes: &mut Routes,
        budget: &mut TypeWorkBudget) -> Result<Self, Failure>
    {
        let (activation, activation_route) = routes.activation(budget)?;
        charge(budget, 1)?;
        let mut scopes = Vec::new();
        scopes.try_reserve_exact(1).map_err(|_| Failure::Resource)?;
        // This demand remains inert. Predicting q@0 descriptors cannot feed K.
        scopes.push(Scope { kind: ScopeKind::Zero, origin: TypeOrigin::OriginalContext(0),
            activation, activation_route, state: ScopeState::Complete,
            actuals: Vec::new(), frame: None });
        Ok(Self { graph, scopes, memo: HashMap::new(), local_memo: HashMap::new(),
            families: Vec::new(), factories: HashMap::new(), relations: HashMap::new(),
            raw_scopes: HashMap::new(), activation_edges: HashSet::new(),
            staged_activation_edges: Vec::new(), staged_root_feeds: Vec::new(), extension: None })
    }

    // Begin only at a committed boundary. The owner retains the exclusive
    // Registry loan until commit/abort and must not publish during preparation.
    pub(super) fn begin_extension(&mut self, budget: &mut TypeWorkBudget) -> Result<(), Failure> {
        charge(budget, self.scopes.len().checked_add(3).ok_or(Failure::Resource)?)?;
        if self.extension.is_some() || !self.staged_activation_edges.is_empty()
            || !self.staged_root_feeds.is_empty()
            || self.scopes.iter().any(|scope| scope.state != ScopeState::Complete)
        { return Err(Failure::Invalid); }
        self.extension = Some(Extension { phase: ExtensionPhase::Preparing,
            scope_start: self.scopes.len(), activation_start: self.staged_activation_edges.len(),
            root_feed_start: self.staged_root_feeds.len(), memo_keys: Vec::new(),
            local_memo_keys: Vec::new(), raw_keys: Vec::new() });
        Ok(())
    }

    fn preparing(&self) -> Result<&Extension, Failure> {
        let extension = self.extension.as_ref().ok_or(Failure::Invalid)?;
        if extension.phase != ExtensionPhase::Preparing { return Err(Failure::Invalid); }
        Ok(extension)
    }

    // Consume/drop every attempted Work, TypedStage, Prepared, Evidence and
    // Zero helper handle before this call. ScopeId suffixes may be reused; no
    // route, activation, type, frame or original Analysis identity is recycled.
    pub(super) fn abort_extension(&mut self) -> Result<(), Failure> {
        self.preparing()?;
        let extension = self.extension.take().ok_or(Failure::Invalid)?;
        for edge in self.staged_activation_edges[extension.activation_start..].iter().rev() {
            self.activation_edges.remove(edge);
        }
        self.staged_activation_edges.truncate(extension.activation_start);
        self.staged_root_feeds.truncate(extension.root_feed_start);
        for key in extension.memo_keys.iter().rev() { self.memo.remove(key); }
        for key in extension.local_memo_keys.iter().rev() { self.local_memo.remove(key); }
        for key in extension.raw_keys.iter().rev() { self.raw_scopes.remove(key); }
        self.scopes.truncate(extension.scope_start);
        Ok(())
    }

    // Every semantic check and driver request must finish before sealing.
    // After this boundary abort/fallback is forbidden: a Resource refusal in
    // live publication is terminal for the source owner, not a semantic decline.
    pub(super) fn seal_extension(&mut self, budget: &mut TypeWorkBudget) -> Result<(), Failure> {
        let extension = self.preparing()?;
        let cleanup = extension.memo_keys.len().checked_add(extension.local_memo_keys.len())
            .and_then(|n| n.checked_add(extension.raw_keys.len()))
            .and_then(|n| n.checked_add(self.staged_activation_edges.len()))
            .and_then(|n| n.checked_add(self.staged_root_feeds.len()))
            .and_then(|n| n.checked_add(self.scopes.len()))
            .and_then(|n| n.checked_add(3)).ok_or(Failure::Resource)?;
        charge(budget, cleanup)?;
        if self.scopes.iter().any(|scope| scope.state != ScopeState::Complete) {
            return Err(Failure::Invalid);
        }
        self.extension.as_mut().ok_or(Failure::Invalid)?.phase = ExtensionPhase::Publishing;
        Ok(())
    }

    // Called only after successful original publication. Clearing the consumed
    // buffers retains committed dedup and all completed descriptor scopes.
    pub(super) fn commit_extension(&mut self) -> Result<(), Failure> {
        let extension = self.extension.as_ref().ok_or(Failure::Invalid)?;
        if extension.phase != ExtensionPhase::Publishing { return Err(Failure::Invalid); }
        let extension = self.extension.take().ok_or(Failure::Invalid)?;
        self.staged_activation_edges.truncate(extension.activation_start);
        self.staged_root_feeds.truncate(extension.root_feed_start);
        Ok(())
    }

    pub(super) fn zero(&self) -> ScopeId { ScopeId(0) }

    pub(super) fn scope(&self, id: ScopeId) -> Result<&Scope, Failure> {
        self.scopes.get(id.0).ok_or(Failure::Invalid)
    }

    pub(super) fn add_family(&mut self, family: QualifiedFamily<'g>,
        budget: &mut TypeWorkBudget) -> Result<(), Failure>
    {
        charge(budget, family.factories().len().checked_add(family.relations().len())
            .ok_or(Failure::Resource)?)?;
        for qualified in family.factories() {
            if !std::ptr::eq(qualified.factory_support().graph(), self.graph) {
                return Err(Failure::Invalid);
            }
            if let Some((f, n)) = self.factories.get(&qualified.factory()) {
                if self.families[*f].factories()[*n].returned() != qualified.returned() {
                    return Err(Failure::Invalid);
                }
            }
        }
        for relation in family.relations() {
            if let Some(old) = self.relations.get(&relation.expression) {
                if old.factory != relation.factory || old.body != relation.body {
                    return Err(Failure::Invalid);
                }
            }
        }
        self.families.try_reserve(1).map_err(|_| Failure::Resource)?;
        self.factories.try_reserve(family.factories().len()).map_err(|_| Failure::Resource)?;
        self.relations.try_reserve(family.relations().len()).map_err(|_| Failure::Resource)?;
        let index = self.families.len();
        for (node, qualified) in family.factories().iter().enumerate() {
            self.factories.entry(qualified.factory()).or_insert((index, node));
        }
        for relation in family.relations() { self.relations.insert(relation.expression, *relation); }
        self.families.push(family);
        Ok(())
    }

    pub(super) fn factory(&self, function: usize) -> Result<&QualifiedFactory<'g>, Failure> {
        let &(family, node) = self.factories.get(&function).ok_or(Failure::Invalid)?;
        self.families.get(family).and_then(|f| f.factories().get(node)).ok_or(Failure::Invalid)
    }

    pub(super) fn relation(&self, expression: usize) -> Result<TypedCallRelation, Failure> {
        self.relations.get(&expression).copied().ok_or(Failure::Invalid)
    }

    pub(super) fn append_scope(&mut self, kind: ScopeKind, origin: TypeOrigin,
        routes: &mut Routes, budget: &mut TypeWorkBudget) -> Result<ScopeId, Failure>
    {
        self.preparing()?;
        if matches!(kind, ScopeKind::Zero | ScopeKind::Raw { .. }) { return Err(Failure::Invalid); }
        charge(budget, 2)?; // append and prepaid scope-suffix disposal
        self.scopes.try_reserve(1).map_err(|_| Failure::Resource)?;
        let (activation, activation_route) = routes.activation(budget)?;
        let id = ScopeId(self.scopes.len());
        self.scopes.push(Scope { kind, origin, activation, activation_route,
            state: ScopeState::Prepared, actuals: Vec::new(), frame: None });
        Ok(id)
    }

    pub(super) fn append_external_scope(&mut self, expression: usize, origin: TypeOrigin,
        routes: &mut Routes, budget: &mut TypeWorkBudget) -> Result<ScopeId, Failure>
    {
        self.append_scope(ScopeKind::Evidence { expression }, origin, routes, budget)
    }

    // The source owner supplies an already authenticated completed frame and
    // its exact origin. Completion changes only this attempt's new scope; it
    // publishes no original capture feed, context binding, head or atom.
    pub(super) fn complete_external_scope(
        &mut self, scope: ScopeId, origin: TypeOrigin, frame: CompletedFrame,
        routes: &Routes, budget: &mut TypeWorkBudget,
    ) -> Result<(), Failure> {
        let start = self.preparing()?.scope_start;
        charge(budget, 3)?;
        if scope.0 < start { return Err(Failure::Invalid); }
        let record = self.scope(scope)?;
        if record.state != ScopeState::Prepared || record.frame.is_some()
            || record.origin != origin
            || !matches!(record.kind, ScopeKind::Evidence { .. }
                | ScopeKind::SavedEvidence { .. })
        { return Err(Failure::Invalid); }
        let function = routes.function(frame)?;
        if !matches!(self.graph.expressions.get(function), Some(Expr::Function { .. })) {
            return Err(Failure::Invalid);
        }
        let record = self.scopes.get_mut(scope.0).ok_or(Failure::Invalid)?;
        record.frame = Some(frame);
        record.state = ScopeState::Complete;
        Ok(())
    }

    pub(super) fn memo(&self, scope: ScopeId, expression: usize,
        budget: &mut TypeWorkBudget) -> Result<Option<&Value>, Failure>
    {
        self.scope(scope)?;
        charge(budget, 1)?;
        Ok(self.memo.get(&(scope, expression)))
    }

    // A completed immutable equation cannot be overwritten by a partial answer.
    pub(super) fn put(&mut self, scope: ScopeId, expression: usize, value: Value,
        budget: &mut TypeWorkBudget) -> Result<(), Failure>
    {
        self.preparing()?;
        self.scope(scope)?;
        if self.graph.expressions.get(expression).is_none() { return Err(Failure::Invalid); }
        charge(budget, 3)?; // lookup, journal append and prepaid map removal
        if self.memo.contains_key(&(scope, expression)) { return Err(Failure::Invalid); }
        self.memo.try_reserve(1).map_err(|_| Failure::Resource)?;
        let extension = self.extension.as_mut().ok_or(Failure::Invalid)?;
        extension.memo_keys.try_reserve(1).map_err(|_| Failure::Resource)?;
        extension.memo_keys.push((scope, expression));
        self.memo.insert((scope, expression), value);
        Ok(())
    }

    fn raw_factory(&self, scope: ScopeId) -> Result<&QualifiedFactory<'g>, Failure> {
        let ScopeKind::Raw { factory, .. } = self.scope(scope)?.kind else { return Err(Failure::Invalid); };
        self.factory(factory)
    }

    pub(super) fn expression_class(&self, scope: ScopeId, expression: usize,
        budget: &mut TypeWorkBudget) -> Result<ProjectionClass, Failure>
    {
        let factory = self.raw_factory(scope)?;
        charge(budget, factory.support_classes().len())?;
        factory.support_classes().iter().find(|c| c.expression == expression)
            .map(|c| c.class).ok_or(Failure::Invalid)
    }

    pub(super) fn saved_count(&self, scope: ScopeId, expression: usize,
        budget: &mut TypeWorkBudget) -> Result<usize, Failure>
    {
        let factory = self.raw_factory(scope)?;
        charge(budget, factory.capture_seeds().len())?;
        Ok(factory.capture_seeds().iter().filter(|&&capture| capture == expression).count())
    }

    // The normalized full kinded input key exists BEFORE any F/G capture child
    // is requested. Equal input scopes share expansion but keep occurrence
    // activation edges and exact outer saved/head feeds separate.
    pub(super) fn intern_raw(&mut self, factory: usize, normalized: NormalizedEnvironmentId,
        actuals: &[RouteId], types: &Types, routes: &mut Routes,
        budget: &mut TypeWorkBudget) -> Result<(ScopeId, bool), Failure>
    {
        self.preparing()?;
        self.factory(factory)?;
        let environment = types.normalized(normalized)?;
        charge(budget, actuals.len().checked_add(1).ok_or(Failure::Resource)?)?;
        if environment.factory() != factory || environment.bindings().len() != actuals.len()
            || environment.bindings().iter().zip(actuals).any(|(b, r)| b.route() != *r)
        { return Err(Failure::Invalid); }
        if let Some(id) = self.raw_scopes.get(&normalized) { return Ok((*id, false)); }
        let actuals = copy_slice(actuals, budget)?;
        charge(budget, 5)?; // both inserts, undo journal and prepaid removals
        self.scopes.try_reserve(1).map_err(|_| Failure::Resource)?;
        self.raw_scopes.try_reserve(1).map_err(|_| Failure::Resource)?;
        self.extension.as_mut().ok_or(Failure::Invalid)?.raw_keys
            .try_reserve(1).map_err(|_| Failure::Resource)?;
        let (activation, activation_route) = routes.activation(budget)?;
        let extension = self.extension.as_mut().ok_or(Failure::Invalid)?;
        let id = ScopeId(self.scopes.len());
        extension.raw_keys.push(normalized);
        self.scopes.push(Scope { kind: ScopeKind::Raw { factory, normalized },
            origin: TypeOrigin::Normalized(normalized), activation, activation_route,
            state: ScopeState::Prepared, actuals, frame: None });
        self.raw_scopes.insert(normalized, id);
        Ok((id, true))
    }

    pub(super) fn raw_dependencies(&self, scope: ScopeId,
        budget: &mut TypeWorkBudget) -> Result<Vec<(ScopeId, usize)>, Failure>
    {
        let factory = self.raw_factory(scope)?;
        let count = factory.capture_seeds().len()
            .checked_add(factory.returned_support().captures().len())
            .and_then(|n| n.checked_add(factory.slot_baselines().len())).ok_or(Failure::Resource)?;
        charge(budget, count)?;
        let mut result = Vec::new();
        result.try_reserve_exact(count).map_err(|_| Failure::Resource)?;
        // Retain all ordered F capture installation inputs, even those absent
        // from G's declared captures. Separate deep Slot support follows.
        for &capture in factory.capture_seeds() { result.push((scope, capture)); }
        for capture in factory.returned_support().captures() { result.push((scope, *capture)); }
        for slot in factory.slot_baselines() { result.push((scope, slot.expression)); }
        Ok(result)
    }

    pub(super) fn raw_slot(&self, scope: ScopeId, expression: usize, saved: Option<&Value>,
        routes: &mut Routes, budget: &mut TypeWorkBudget) -> Result<Value, Failure>
    {
        let factory = self.raw_factory(scope)?;
        charge(budget, factory.slot_baselines().len())?;
        let slot = factory.slot_baselines().iter().find(|s| s.expression == expression)
            .ok_or(Failure::Invalid)?;
        let mut inputs = Vec::new();
        inputs.try_reserve_exact(1).map_err(|_| Failure::Resource)?;
        let mut alternatives = Vec::new();
        if let Some(ordinal) = slot.formal_ordinal {
            inputs.push(*self.scope(scope)?.actuals.get(ordinal).ok_or(Failure::Invalid)?);
        }
        let count = self.saved_count(scope, expression, budget)?;
        if (count != 0) != saved.is_some() { return Err(Failure::Invalid); }
        if let Some(saved) = saved {
            compatible(slot.class, saved.class)?;
            charge(budget, count)?;
            inputs.try_reserve(count).map_err(|_| Failure::Resource)?;
            for _ in 0..count {
                inputs.push(saved.route);
                append_alternatives(&mut alternatives, &saved.alternatives, budget)?;
            }
        }
        let route = match inputs.as_slice() {
            [] => routes.empty(budget)?,
            [one] => *one,
            _ => routes.equation_join(slot.class, &inputs, budget)?,
        };
        Ok(Value { route, class: slot.class, alternatives })
    }

    pub(super) fn finish_alias(&self, child: &Value,
        budget: &mut TypeWorkBudget) -> Result<Value, Failure> { child.copy(budget) }

    pub(super) fn finish_merge(&self, children: &[Value], routes: &mut Routes,
        budget: &mut TypeWorkBudget) -> Result<Value, Failure>
    {
        charge(budget, children.len())?;
        if children.iter().any(|v| !matches!(v.class, ProjectionClass::Empty | ProjectionClass::Metadata)
            || !v.alternatives.is_empty()) { return Err(Failure::Invalid); }
        charge(budget, children.len())?;
        let route = match children {
            [] => routes.free(budget)?,
            [one] => routes.metadata_view(one.route, budget)?,
            _ => {
                let count = children.len().checked_add(1).ok_or(Failure::Resource)?;
                let mut inputs = Vec::new();
                inputs.try_reserve_exact(count).map_err(|_| Failure::Resource)?;
                inputs.push(routes.free(budget)?);
                inputs.extend(children.iter().map(|v| v.route));
                routes.equation_join(ProjectionClass::Metadata, &inputs, budget)?
            }
        };
        Ok(Value::opaque(route, ProjectionClass::Metadata))
    }

    // Store LOCAL separately, then complete it with each independent ordered
    // original F capture seed. A saved callable cannot activate the local q.
    pub(super) fn finish_expression(&mut self, scope: ScopeId, expression: usize,
        local: Value, saved: Option<&Value>, routes: &mut Routes,
        budget: &mut TypeWorkBudget) -> Result<(), Failure>
    {
        self.preparing()?;
        let class = self.expression_class(scope, expression, budget)?;
        compatible(class, local.class)?;
        let count = self.saved_count(scope, expression, budget)?;
        if (count != 0) != saved.is_some() { return Err(Failure::Invalid); }
        let mut complete = local.copy(budget)?;
        complete.class = class;
        if let Some(saved) = saved {
            compatible(class, saved.class)?;
            let size = count.checked_add(1).ok_or(Failure::Resource)?;
            charge(budget, size)?;
            let mut inputs = Vec::new();
            inputs.try_reserve_exact(size).map_err(|_| Failure::Resource)?;
            inputs.push(local.route);
            for _ in 0..count {
                inputs.push(saved.route);
                append_alternatives(&mut complete.alternatives, &saved.alternatives, budget)?;
            }
            complete.route = routes.equation_join(class, &inputs, budget)?;
        }
        charge(budget, 6)?; // both lookups/journals and prepaid map removals
        if self.local_memo.contains_key(&(scope, expression)) || self.memo.contains_key(&(scope, expression)) {
            return Err(Failure::Invalid);
        }
        self.local_memo.try_reserve(1).map_err(|_| Failure::Resource)?;
        self.memo.try_reserve(1).map_err(|_| Failure::Resource)?;
        let extension = self.extension.as_mut().ok_or(Failure::Invalid)?;
        extension.local_memo_keys.try_reserve(1).map_err(|_| Failure::Resource)?;
        extension.memo_keys.try_reserve(1).map_err(|_| Failure::Resource)?;
        extension.local_memo_keys.push((scope, expression));
        extension.memo_keys.push((scope, expression));
        self.local_memo.insert((scope, expression), local);
        self.memo.insert((scope, expression), complete);
        Ok(())
    }

    pub(super) fn stage_activation(&mut self, activation: ActivationId, condition: RouteId,
        budget: &mut TypeWorkBudget) -> Result<(), Failure>
    {
        self.preparing()?;
        charge(budget, 1)?;
        if self.activation_edges.contains(&(activation, condition)) { return Ok(()); }
        charge(budget, 2)?; // staged suffix journal and prepaid dedup removal
        self.activation_edges.try_reserve(1).map_err(|_| Failure::Resource)?;
        self.staged_activation_edges.try_reserve(1).map_err(|_| Failure::Resource)?;
        self.activation_edges.insert((activation, condition));
        self.staged_activation_edges.push((activation, condition));
        Ok(())
    }

    // Conditional origins must be flattened explicitly by the owner into all
    // coherent origin/gate pairs. An unresolved ordinary context declines;
    // only the certified Zero scope permits identity symbolic substitution.
    pub(super) fn begin_typed(&mut self, parent: ScopeId, expression: usize,
        callee: &Value, actuals: &[Value], origins: &[(TypeOrigin, RouteId)],
        types: &mut Types, routes: &mut Routes, budget: &mut TypeWorkBudget,
    ) -> Result<Option<TypedStage>, Failure> {
        self.preparing()?;
        charge(budget, actuals.len().checked_add(1).ok_or(Failure::Resource)?)?;
        let relation = self.relation(expression)?;
        if callee.class != ProjectionClass::Callable(relation.factory)
            || actuals.iter().any(|a| !matches!(a.class, ProjectionClass::Empty | ProjectionClass::Metadata)
                || !a.alternatives.is_empty()) || origins.is_empty()
        { return Ok(None); }
        let Some(checked) = typed_environment::check_global_factory_shape(self.graph, expression, budget)?
            else { return Ok(None); };
        if checked.factory() != relation.factory { return Ok(None); }
        let actual_routes: Vec<RouteId> = {
            charge(budget, actuals.len())?;
            let mut result = Vec::new();
            result.try_reserve_exact(actuals.len()).map_err(|_| Failure::Resource)?;
            result.extend(actuals.iter().map(|a| a.route));
            result
        };
        // Normalize the complete branch set before retaining any raw scope.
        let mut normalized = Vec::new();
        charge(budget, origins.len())?;
        normalized.try_reserve_exact(origins.len()).map_err(|_| Failure::Resource)?;
        for &(origin, gate) in origins {
            let id = match origin {
                TypeOrigin::OriginalContext(0) if self.scope(parent)?.kind == ScopeKind::Zero =>
                    types.normalize_closed_symbolic(&checked, &actual_routes, budget)?,
                TypeOrigin::OriginalContext(_) | TypeOrigin::Conditional(_) => return Ok(None),
                _ => types.normalize(&checked, origin, &actual_routes, budget)?,
            };
            let Some(id) = id else { return Ok(None); };
            normalized.push((id, gate));
        }
        let count = actuals.len().checked_add(1).ok_or(Failure::Resource)?;
        charge(budget, count)?;
        let mut inputs = Vec::new();
        inputs.try_reserve_exact(count).map_err(|_| Failure::Resource)?;
        inputs.push(callee.route);
        inputs.extend_from_slice(&actual_routes);
        let mut branches = Vec::new();
        branches.try_reserve_exact(normalized.len()).map_err(|_| Failure::Resource)?;
        for (id, origin_gate) in normalized {
            let (scope, _) = self.intern_raw(relation.factory, id, &actual_routes, types, routes, budget)?;
            let mut ready_inputs = copy_slice(&inputs, budget)?;
            charge(budget, ready_inputs.len().checked_add(2).ok_or(Failure::Resource)?)?;
            ready_inputs.try_reserve(2).map_err(|_| Failure::Resource)?;
            ready_inputs.insert(0, self.scope(parent)?.activation_route);
            ready_inputs.push(origin_gate);
            let free = routes.free(budget)?;
            let condition = routes.equation_ready(&ready_inputs, free, budget)?;
            let activation = self.scope(scope)?.activation;
            self.stage_activation(activation, condition, budget)?;
            branches.push(TypedBranch { scope, origin_gate });
        }
        Ok(Some(TypedStage { parent, expression, returned: relation.body, inputs, branches }))
    }

    pub(super) fn complete_raw(&mut self, scope: ScopeId, admitted: &AdmittedFrame,
        routes: &mut Routes, budget: &mut TypeWorkBudget) -> Result<CompletedFrame, Failure>
    {
        let factory = self.raw_factory(scope)?;
        let function = factory.returned();
        if admitted.function != function { return Err(Failure::Invalid); }
        if let Some(frame) = self.scope(scope)?.frame {
            if self.scope(scope)?.state != ScopeState::Complete { return Err(Failure::Invalid); }
            return Ok(frame);
        }
        let start = self.preparing()?.scope_start;
        if scope.0 < start || self.scope(scope)?.state != ScopeState::Prepared {
            return Err(Failure::Invalid);
        }
        let captures = factory.returned_support().captures();
        charge(budget, captures.len().checked_add(factory.slot_baselines().len())
            .and_then(|n| n.checked_add(factory.capture_seeds().len())).ok_or(Failure::Resource)?)?;
        // Every F capture must have been evaluated, even if G never declares it.
        for &capture in factory.capture_seeds() {
            if !self.memo.contains_key(&(scope, capture)) { return Err(Failure::Invalid); }
        }
        let mut bindings = Vec::new();
        let mut classes = Vec::new();
        let mut supports = Vec::new();
        let mut feeds = Vec::new();
        bindings.try_reserve_exact(captures.len()).map_err(|_| Failure::Resource)?;
        classes.try_reserve_exact(captures.len()).map_err(|_| Failure::Resource)?;
        feeds.try_reserve_exact(captures.len()).map_err(|_| Failure::Resource)?;
        supports.try_reserve_exact(factory.slot_baselines().len()).map_err(|_| Failure::Resource)?;
        let activation = self.scope(scope)?.activation_route;
        for (&capture, certificate) in captures.iter().zip(factory.declared_capture_classes()) {
            if capture != certificate.expression { return Err(Failure::Invalid); }
            let value = self.memo.get(&(scope, capture)).ok_or(Failure::Invalid)?;
            compatible(certificate.class, value.class)?;
            bindings.push((capture, value.route));
            classes.push(certificate.class);
            let route = routes.equation_ready(&[activation], value.route, budget)?;
            feeds.push(RootFeed { factory: factory.factory(), returned: function, capture, route });
        }
        for slot in factory.slot_baselines() {
            let value = self.memo.get(&(scope, slot.expression)).ok_or(Failure::Invalid)?;
            compatible(slot.class, value.class)?;
            charge(budget, captures.len())?;
            if !captures.contains(&slot.expression) { supports.push((slot.expression, value.route)); }
        }
        let pending = routes.bindings_with_support(function, captures, &bindings, &classes,
            self.scope(scope)?.origin, &supports, budget)?;
        let frame = routes.complete_under(pending, admitted)?;
        charge(budget, feeds.len().checked_add(1).ok_or(Failure::Resource)?)?;
        self.staged_root_feeds.try_reserve(feeds.len()).map_err(|_| Failure::Resource)?;
        // Scope disposal was prepaid by intern_raw; each feed also prepays
        // removal from this attempt's root-feed suffix on semantic abort.
        let record = self.scopes.get_mut(scope.0).ok_or(Failure::Invalid)?;
        self.staged_root_feeds.extend(feeds);
        record.frame = Some(frame);
        record.state = ScopeState::Complete;
        Ok(frame)
    }

    // LOCAL TypeCall descriptor. The driver must subsequently add independent
    // saved q@0 through finish_expression, never into these readiness inputs.
    pub(super) fn finish_typed(&self, stage: &TypedStage, routes: &mut Routes,
        budget: &mut TypeWorkBudget) -> Result<Value, Failure>
    {
        let mut outputs = Vec::new();
        let mut alternatives = Vec::new();
        charge(budget, stage.branches.len())?;
        outputs.try_reserve_exact(stage.branches.len()).map_err(|_| Failure::Resource)?;
        alternatives.try_reserve_exact(stage.branches.len()).map_err(|_| Failure::Resource)?;
        for branch in &stage.branches {
            let scope = self.scope(branch.scope)?;
            let frame = scope.frame.ok_or(Failure::Invalid)?;
            let construct = routes.equation_construct(stage.returned, frame, budget)?;
            let mut inputs = copy_slice(&stage.inputs, budget)?;
            inputs.try_reserve(1).map_err(|_| Failure::Resource)?;
            inputs.push(branch.origin_gate);
            let route = routes.equation_ready(&inputs, construct, budget)?;
            outputs.push(route);
            alternatives.push(ClosureAlternative { function: stage.returned, frame,
                creation: branch.scope, origin: scope.origin, gate: route });
        }
        let class = ProjectionClass::Callable(stage.returned);
        let route = match outputs.as_slice() {
            [] => return Err(Failure::Invalid),
            [one] => *one,
            _ => routes.equation_join(class, &outputs, budget)?,
        };
        Ok(Value { route, class, alternatives })
    }
}

fn compatible(upper: ProjectionClass, source: ProjectionClass) -> Result<(), Failure> {
    if source == ProjectionClass::Empty || source == upper { Ok(()) }
    else { Err(Failure::Invalid) }
}

fn append_alternatives(target: &mut Vec<ClosureAlternative>, source: &[ClosureAlternative],
    budget: &mut TypeWorkBudget) -> Result<(), Failure>
{
    charge(budget, source.len())?;
    target.try_reserve(source.len()).map_err(|_| Failure::Resource)?;
    target.extend_from_slice(source);
    Ok(())
}
