//! Connected, iterative, prepublication producer staging. Actual entry is
//! restricted to context zero; Raw/Evidence children carry complete normalized
//! origins. The Host supplies proofs and coordinates, never live mutations.

use std::collections::{HashMap, HashSet};

use super::{AdmittedFrame, Expr, Failure, Graph, TypeWorkBudget, charge, copy_slice};
use super::deferred_frame::{Arena as Routes, OriginalPort, ProjectionClass, RouteId};
use super::local_recipe::Compiler;
use super::producer::{Registry, ScopeId, ScopeKind, ScopeState, TypedStage, Value};
use super::producer_evidence::{self as evidence, IncomingEnvironment, PlanId, TopologyInput};
use super::producer_zero::{self as zero, ExactEvidenceZero, ZeroCertificate, ZeroState};
use super::typed_environment::{Arena as Types, TypeOrigin};

pub(super) struct EvidenceInputs<'a> {
    pub(super) topology: TopologyInput<'a>,
    // Complete E upper classes, including pure children below dictionary cuts.
    pub(super) classes: &'a [(usize, ProjectionClass)],
}

// Implementations are prepared from the exact immutable Graph and the owner's
// all-writer/no-I0-ingress/actual-family guards. No method acquires a context,
// reads current atoms, installs original slots or publishes a head/root feed.
pub(super) trait Host {
    fn zero_empty_slot(&self, expression: usize) -> bool;
    fn evidence(&self, expression: usize, function: usize) -> Option<EvidenceInputs<'_>>;
    fn class(&self, expression: usize) -> Option<ProjectionClass>;
    fn exact_evidence_zero(&self, expression: usize) -> Option<ExactEvidenceZero>;
    fn admitted(&self, function: usize) -> Option<&AdmittedFrame>;
}

#[derive(Debug)]
pub(super) enum Decline {
    EntryContext,
    Unsupported,
    MissingHost,
    Class,
    Cycle,
    Origin,
    TypedCall,
    Evidence,
    ZeroWrongGraph,
    ZeroUnsupported,
    ZeroClass,
    ZeroMissingZeroWriter,
    ZeroMissingCanonical,
    ZeroTypedWitness,
    ZeroEvidencePayload,
}

impl From<zero::Decline> for Decline {
    fn from(reason: zero::Decline) -> Self {
        match reason {
            zero::Decline::WrongGraph => Self::ZeroWrongGraph,
            zero::Decline::Unsupported => Self::ZeroUnsupported,
            zero::Decline::Class => Self::ZeroClass,
            zero::Decline::MissingZeroWriter => Self::ZeroMissingZeroWriter,
            zero::Decline::MissingCanonical => Self::ZeroMissingCanonical,
            zero::Decline::TypedWitness => Self::ZeroTypedWitness,
            zero::Decline::EvidencePayload => Self::ZeroEvidencePayload,
        }
    }
}

enum Stop { Resource(Failure), Decline(Decline) }
impl From<Failure> for Stop { fn from(value: Failure) -> Self { Self::Resource(value) } }

#[derive(Clone, Copy, Eq, PartialEq)]
enum Phase { Preparing, Ready, Sealed }

enum Local {
    Slot,
    Alias(usize),
    Merge(Vec<usize>),
    Typed { function: usize, arguments: Vec<usize> },
}

enum Job {
    Entry(usize),
    BuildEntry(usize),
    FinishEntry(TypedStage),
    Evaluate(ScopeId, usize),
    FinishLocal { scope: ScopeId, expression: usize, local: Local },
    FinishTyped { stage: TypedStage, saved_zero: bool },
    FinishZero(zero::Request),
    EnsureRaw(ScopeId),
    CompleteRaw(ScopeId),
    PrepareEvidence { parent: ScopeId, expression: usize, payload: usize,
        function: usize, bindings: Vec<usize> },
    EnsureEvidence(ScopeId),
    BuildIncoming(ScopeId),
    CompleteEvidence(ScopeId),
    FinishEvidenceUse { parent: ScopeId, expression: usize, scope: ScopeId },
}

struct Environment {
    plan: PlanId,
    function: usize,
    classes: Vec<(usize, ProjectionClass)>,
    rows: Vec<usize>,
    incoming: Option<IncomingEnvironment>,
}

struct Attempt {
    phase: Phase,
    expression: usize,
    evidence_mark: evidence::Mark,
    jobs: Vec<Job>,
    visiting: HashSet<(ScopeId, usize)>,
    scopes_visiting: HashSet<ScopeId>,
    // Journals prepay removal BEFORE any helper can publish an attempted key.
    zero_candidates: Vec<usize>,
    environments: Vec<ScopeId>,
    saved_scopes: Vec<ScopeId>,
    output: Option<Value>,
}

pub(super) struct Sealed {
    pub(super) expression: usize,
    pub(super) local: Value,
}

pub(super) struct DriverState<'g> {
    pub(super) registry: Registry<'g>,
    pub(super) zero: ZeroState,
    pub(super) evidence: evidence::Arena<'g>,
    environments: HashMap<ScopeId, Environment>,
    saved_contexts: HashMap<ScopeId, usize>,
    attempt: Option<Attempt>,
}

impl<'g> DriverState<'g> {
    pub(super) fn new(graph: &'g Graph, routes: &mut Routes,
        budget: &mut TypeWorkBudget) -> Result<Self, Failure>
    {
        Ok(Self { registry: Registry::new(graph, routes, budget)?, zero: ZeroState::new(),
            evidence: evidence::Arena::new(graph), environments: HashMap::new(),
            saved_contexts: HashMap::new(), attempt: None })
    }

    pub(super) fn begin(&mut self, expression: usize, context: usize,
        budget: &mut TypeWorkBudget) -> Result<Result<(), Decline>, Failure>
    {
        if self.attempt.is_some() { return Err(Failure::Invalid); }
        if context != 0 { return Ok(Err(Decline::EntryContext)); }
        if !matches!(self.registry.graph.expressions.get(expression),
            Some(Expr::Call { type_application: true, .. })) {
            return Ok(Err(Decline::TypedCall));
        }
        self.registry.relation(expression)?;
        charge(budget, 2)?;
        let mut jobs = Vec::new();
        jobs.try_reserve_exact(1).map_err(|_| Failure::Resource)?;
        jobs.push(Job::Entry(expression));
        let evidence_mark = self.evidence.mark(budget)?;
        self.registry.begin_extension(budget)?;
        self.attempt = Some(Attempt { phase: Phase::Preparing, expression, evidence_mark,
            jobs, visiting: HashSet::new(), scopes_visiting: HashSet::new(),
            zero_candidates: Vec::new(), environments: Vec::new(), saved_scopes: Vec::new(), output: None });
        Ok(Ok(()))
    }

    fn preparing(&self) -> Result<&Attempt, Failure> {
        let attempt = self.attempt.as_ref().ok_or(Failure::Invalid)?;
        if attempt.phase != Phase::Preparing { return Err(Failure::Invalid); }
        Ok(attempt)
    }

    fn push(&mut self, job: Job, budget: &mut TypeWorkBudget) -> Result<(), Failure> {
        self.preparing()?;
        charge(budget, 2)?; // append and prepaid failed-attempt job disposal
        let jobs = &mut self.attempt.as_mut().ok_or(Failure::Invalid)?.jobs;
        jobs.try_reserve(1).map_err(|_| Failure::Resource)?;
        jobs.push(job);
        Ok(())
    }

    // Reverse pushes preserve the requested dependency evaluation order.
    fn evaluate_many(&mut self, inputs: &[(ScopeId, usize)],
        budget: &mut TypeWorkBudget) -> Result<(), Failure>
    {
        charge(budget, inputs.len())?;
        for &(scope, expression) in inputs.iter().rev() {
            self.push(Job::Evaluate(scope, expression), budget)?;
        }
        Ok(())
    }

    fn values(&self, inputs: &[(ScopeId, usize)],
        budget: &mut TypeWorkBudget) -> Result<Vec<Value>, Failure>
    {
        charge(budget, inputs.len())?;
        let mut values = Vec::new();
        values.try_reserve_exact(inputs.len()).map_err(|_| Failure::Resource)?;
        for &(scope, expression) in inputs { values.push(self.value(scope, expression, budget)?); }
        Ok(values)
    }

    fn value(&self, scope: ScopeId, expression: usize,
        budget: &mut TypeWorkBudget) -> Result<Value, Failure>
    {
        self.registry.memo(scope, expression, budget)?.ok_or(Failure::Invalid)?.copy(budget)
    }

    fn done(&mut self, scope: ScopeId, expression: usize,
        budget: &mut TypeWorkBudget) -> Result<(), Failure>
    {
        charge(budget, 1)?;
        if !self.attempt.as_mut().ok_or(Failure::Invalid)?.visiting.remove(&(scope, expression)) {
            return Err(Failure::Invalid);
        }
        Ok(())
    }

    // Run preparation only. Every failure aborts helper caches before ScopeId
    // recycling. No semantic decline is returned after seal/publication starts.
    pub(super) fn run(&mut self, host: &impl Host, compiler: &mut Compiler<'g>,
        types: &mut Types, routes: &mut Routes, budget: &mut TypeWorkBudget,
    ) -> Result<Result<(), Decline>, Failure> {
        self.preparing()?;
        loop {
            let job = self.attempt.as_mut().ok_or(Failure::Invalid)?.jobs.pop();
            let Some(job) = job else { break; };
            if let Err(stop) = self.step(job, host, compiler, types, routes, budget) {
                self.abort()?;
                return match stop { Stop::Resource(failure) => Err(failure),
                    Stop::Decline(reason) => Ok(Err(reason)) };
            }
        }
        let attempt = self.attempt.as_mut().ok_or(Failure::Invalid)?;
        if attempt.output.is_none() || !attempt.visiting.is_empty() || !attempt.scopes_visiting.is_empty() {
            self.abort()?;
            return Err(Failure::Invalid);
        }
        attempt.phase = Phase::Ready;
        Ok(Ok(()))
    }

    pub(super) fn seal(&mut self, budget: &mut TypeWorkBudget) -> Result<Sealed, Failure> {
        let attempt = self.attempt.as_ref().ok_or(Failure::Invalid)?;
        if attempt.phase != Phase::Ready || attempt.output.is_none() { return Err(Failure::Invalid); }
        self.registry.seal_extension(budget)?;
        let attempt = self.attempt.as_mut().ok_or(Failure::Invalid)?;
        attempt.phase = Phase::Sealed;
        Ok(Sealed { expression: attempt.expression, local: attempt.output.take().ok_or(Failure::Invalid)? })
    }

    pub(super) fn commit(&mut self) -> Result<(), Failure> {
        if self.attempt.as_ref().ok_or(Failure::Invalid)?.phase != Phase::Sealed {
            return Err(Failure::Invalid);
        }
        self.registry.commit_extension()?;
        self.attempt.take().ok_or(Failure::Invalid)?;
        Ok(())
    }

    pub(super) fn abort(&mut self) -> Result<(), Failure> {
        if self.attempt.as_ref().ok_or(Failure::Invalid)?.phase == Phase::Sealed {
            return Err(Failure::Invalid);
        }
        let mut attempt = self.attempt.take().ok_or(Failure::Invalid)?;
        // Drop every job/sidecar/creation association before a ScopeId suffix
        // is recycled. Cleanup is prepaid at each insertion and takes no budget.
        attempt.jobs.clear();
        attempt.output.take();
        attempt.visiting.clear();
        attempt.scopes_visiting.clear();
        for scope in attempt.environments.drain(..).rev() { self.environments.remove(&scope); }
        for scope in attempt.saved_scopes.drain(..).rev() { self.saved_contexts.remove(&scope); }
        for expression in attempt.zero_candidates.drain(..).rev() {
            self.zero.canonical_metadata.remove(&expression);
        }
        self.evidence.abort(attempt.evidence_mark)?;
        self.registry.abort_extension()
    }

    fn journal_zero(&mut self, expression: usize,
        budget: &mut TypeWorkBudget) -> Result<(), Failure>
    {
        charge(budget, 1)?;
        if self.zero.canonical_metadata.contains_key(&expression) { return Ok(()); }
        charge(budget, 2)?; // journal append and prepaid candidate removal
        let journal = &mut self.attempt.as_mut().ok_or(Failure::Invalid)?.zero_candidates;
        journal.try_reserve(1).map_err(|_| Failure::Resource)?;
        journal.push(expression);
        Ok(())
    }

    fn local_class(&self, scope: ScopeId, expression: usize,
        budget: &mut TypeWorkBudget) -> Result<ProjectionClass, Stop>
    {
        let environment = self.environments.get(&scope).ok_or(Failure::Invalid)?;
        charge(budget, environment.classes.len())?;
        environment.classes.iter().find(|(e, _)| *e == expression).map(|(_, c)| *c)
            .ok_or(Stop::Decline(Decline::Class))
    }

    fn finish(&mut self, scope: ScopeId, expression: usize, local: Value,
        routes: &mut Routes, budget: &mut TypeWorkBudget) -> Result<(), Stop>
    {
        match self.registry.scope(scope)?.kind {
            ScopeKind::Raw { .. } => {
                let saved = if self.registry.saved_count(scope, expression, budget)? != 0 {
                    Some(self.value(self.registry.zero(), expression, budget)?)
                } else { None };
                self.registry.finish_expression(scope, expression, local, saved.as_ref(), routes, budget)?;
            }
            ScopeKind::Evidence { .. } => {
                let class = self.local_class(scope, expression, budget)?;
                if local.class != ProjectionClass::Empty && local.class != class {
                    return Err(Stop::Decline(Decline::Class));
                }
                let environment = self.environments.get(&scope).ok_or(Failure::Invalid)?;
                charge(budget, environment.rows.len())?;
                let complete = if environment.rows.contains(&expression) {
                    self.evidence.finish_expression(environment.incoming.as_ref().ok_or(Failure::Invalid)?,
                        expression, &local, routes, budget)?
                        .ok_or(Stop::Decline(Decline::Class))?
                } else {
                    // The exact full topology/residual table covers every E
                    // incoming writer. Below a dictionary cut this child has
                    // no incoming E row; its independently proved class still
                    // comes from the Host's complete local dependency table.
                    Value { class, ..local }
                };
                self.registry.put(scope, expression, complete, budget)?;
            }
            _ => return Err(Failure::Invalid.into()),
        }
        self.done(scope, expression, budget)?;
        Ok(())
    }

    fn step(&mut self, job: Job, host: &impl Host, compiler: &mut Compiler<'g>,
        types: &mut Types, routes: &mut Routes, budget: &mut TypeWorkBudget,
    ) -> Result<(), Stop> {
        charge(budget, 1)?;
        match job {
            Job::Entry(expression) => {
                let (function, arguments) = call_inputs(self.registry.graph, expression, budget)?;
                let zero = self.registry.zero();
                self.push(Job::BuildEntry(expression), budget)?;
                let mut inputs = Vec::new();
                charge(budget, arguments.len().checked_add(1).ok_or(Failure::Resource)?)?;
                inputs.try_reserve_exact(arguments.len().checked_add(1).ok_or(Failure::Resource)?)
                    .map_err(|_| Failure::Resource)?;
                inputs.push((zero, function));
                inputs.extend(arguments.into_iter().map(|argument| (zero, argument)));
                self.evaluate_many(&inputs, budget)?;
            }
            Job::BuildEntry(expression) => {
                let stage = zero::begin_typed(&mut self.registry, &self.zero, expression, types, routes, budget)?
                    .map_err(|reason| Stop::Decline(reason.into()))?;
                let free = routes.free(budget)?;
                let condition = routes.equation_ready(&stage.inputs, free, budget)?;
                for branch in &stage.branches {
                    let activation = self.registry.scope(branch.scope)?.activation;
                    self.registry.stage_activation(activation, condition, budget)?;
                }
                let scopes = branch_scopes(&stage, budget)?;
                self.push(Job::FinishEntry(stage), budget)?;
                for scope in scopes.into_iter().rev() { self.push(Job::EnsureRaw(scope), budget)?; }
            }
            Job::FinishEntry(stage) => {
                let value = self.registry.finish_typed(&stage, routes, budget)?;
                let attempt = self.attempt.as_mut().ok_or(Failure::Invalid)?;
                if attempt.output.is_some() { return Err(Failure::Invalid.into()); }
                attempt.output = Some(value);
            }
            Job::Evaluate(scope, expression) => {
                if self.registry.memo(scope, expression, budget)?.is_some() { return Ok(()); }
                charge(budget, 3)?; // lookup/insert and prepaid visiting disposal
                let visiting = &mut self.attempt.as_mut().ok_or(Failure::Invalid)?.visiting;
                visiting.try_reserve(1).map_err(|_| Failure::Resource)?;
                if !visiting.insert((scope, expression)) {
                    return Err(Stop::Decline(Decline::Cycle));
                }
                match self.registry.scope(scope)?.kind {
                    ScopeKind::Zero => self.schedule_zero(expression, host, compiler, budget)?,
                    ScopeKind::SavedEvidence { .. } => {
                        if !matches!(self.registry.graph.expressions.get(expression), Some(Expr::Slot)) {
                            return Err(Stop::Decline(Decline::Unsupported));
                        }
                        charge(budget, 2)?;
                        let context = *self.saved_contexts.get(&scope).ok_or(Failure::Invalid)?;
                        let class = host.class(expression).ok_or(Stop::Decline(Decline::MissingHost))?;
                        let route = routes.head(OriginalPort { expression, context }, budget)?;
                        self.registry.put(scope, expression, Value::opaque(route, class), budget)?;
                        self.done(scope, expression, budget)?;
                    }
                    ScopeKind::Raw { .. } | ScopeKind::Evidence { .. } =>
                        self.schedule_local(scope, expression, compiler, budget)?,
                }
            }
            Job::FinishLocal { scope, expression, local } => match local {
                Local::Slot => {
                    if matches!(self.registry.scope(scope)?.kind, ScopeKind::Raw { .. }) {
                        let saved = if self.registry.saved_count(scope, expression, budget)? != 0 {
                            Some(self.value(self.registry.zero(), expression, budget)?)
                        } else { None };
                        let value = self.registry.raw_slot(scope, expression, saved.as_ref(), routes, budget)?;
                        self.registry.put(scope, expression, value, budget)?;
                        self.done(scope, expression, budget)?;
                    } else {
                        let local = Value::opaque(routes.empty(budget)?, ProjectionClass::Empty);
                        self.finish(scope, expression, local, routes, budget)?;
                    }
                }
                Local::Alias(child) => {
                    let child = self.value(scope, child, budget)?;
                    let local = self.registry.finish_alias(&child, budget)?;
                    self.finish(scope, expression, local, routes, budget)?;
                }
                Local::Merge(inputs) => {
                    let requests = same_scope(scope, &inputs, budget)?;
                    let children = self.values(&requests, budget)?;
                    let local = self.registry.finish_merge(&children, routes, budget)?;
                    self.finish(scope, expression, local, routes, budget)?;
                }
                Local::Typed { function, arguments } => {
                    let callee = self.value(scope, function, budget)?;
                    let requests = same_scope(scope, &arguments, budget)?;
                    let actuals = self.values(&requests, budget)?;
                    let origin = self.registry.scope(scope)?.origin;
                    let origins = flatten_origins(origin, types, routes, budget)?;
                    let stage = self.registry.begin_typed(scope, expression, &callee, &actuals, &origins,
                        types, routes, budget)?.ok_or(Stop::Decline(Decline::TypedCall))?;
                    let scopes = branch_scopes(&stage, budget)?;
                    self.push(Job::FinishTyped { stage, saved_zero: false }, budget)?;
                    for scope in scopes.into_iter().rev() { self.push(Job::EnsureRaw(scope), budget)?; }
                }
            },
            Job::FinishTyped { stage, saved_zero } => {
                if saved_zero {
                    let value = zero::finish_typed(&self.registry, &stage, routes, budget)?;
                    self.registry.put(self.registry.zero(), stage.expression, value, budget)?;
                    self.done(self.registry.zero(), stage.expression, budget)?;
                } else {
                    let local = self.registry.finish_typed(&stage, routes, budget)?;
                    self.finish(stage.parent, stage.expression, local, routes, budget)?;
                }
            }
            Job::FinishZero(request) => self.finish_zero(request, host, compiler, types, routes, budget)?,
            Job::EnsureRaw(scope) => {
                if self.registry.scope(scope)?.state == ScopeState::Complete { return Ok(()); }
                self.enter_scope(scope, budget)?;
                let inputs = self.registry.raw_dependencies(scope, budget)?;
                self.push(Job::CompleteRaw(scope), budget)?;
                self.evaluate_many(&inputs, budget)?;
            }
            Job::CompleteRaw(scope) => {
                let ScopeKind::Raw { factory, .. } = self.registry.scope(scope)?.kind else {
                    return Err(Failure::Invalid.into());
                };
                let function = self.registry.factory(factory)?.returned();
                charge(budget, 1)?;
                let admitted = host.admitted(function).ok_or(Stop::Decline(Decline::MissingHost))?;
                self.registry.complete_raw(scope, admitted, routes, budget)?;
                self.leave_scope(scope, budget)?;
            }
            Job::PrepareEvidence { parent, expression, payload, function, bindings } => {
                let input = self.value(parent, payload, budget)?;
                let requests = same_scope(parent, &bindings, budget)?;
                let bindings = self.values(&requests, budget)?;
                charge(budget, 1)?;
                let supplied = host.evidence(expression, function)
                    .ok_or(Stop::Decline(Decline::MissingHost))?;
                let Some((plan, _)) = self.evidence.prepare(expression, function, supplied.topology,
                    &input, &bindings, supplied.classes, budget)? else {
                    return Err(Stop::Decline(Decline::Evidence));
                };
                let scope = if let Some(scope) = self.evidence.scope(plan)? { scope } else {
                    let origin = conditional_origin(&input, types, budget)?;
                    let scope = self.registry.append_external_scope(expression, origin, routes, budget)?;
                    self.evidence.bind_scope(plan, scope, budget)?;
                    let rows = copy_slice(self.evidence.local_requests(plan)?, budget)?;
                    let classes = copy_slice(supplied.classes, budget)?;
                    charge(budget, 4)?; // map/journal publication and prepaid removal
                    self.environments.try_reserve(1).map_err(|_| Failure::Resource)?;
                    let attempt = self.attempt.as_mut().ok_or(Failure::Invalid)?;
                    attempt.environments.try_reserve(1).map_err(|_| Failure::Resource)?;
                    attempt.environments.push(scope);
                    self.environments.insert(scope, Environment { plan, function, classes, rows, incoming: None });
                    scope
                };
                self.push(Job::FinishEvidenceUse { parent, expression, scope }, budget)?;
                self.push(Job::EnsureEvidence(scope), budget)?;
            }
            Job::EnsureEvidence(scope) => {
                if self.registry.scope(scope)?.state == ScopeState::Complete { return Ok(()); }
                self.enter_scope(scope, budget)?;
                let plan = self.environments.get(&scope).ok_or(Failure::Invalid)?.plan;
                let creations = copy_slice(self.evidence.creation_requests(plan)?, budget)?;
                self.push(Job::BuildIncoming(scope), budget)?;
                for request in creations.into_iter().rev() {
                    self.push(Job::Evaluate(request.scope, request.expression), budget)?;
                }
            }
            Job::BuildIncoming(scope) => {
                let plan = self.environments.get(&scope).ok_or(Failure::Invalid)?.plan;
                let requests = self.evidence.creation_requests(plan)?;
                let mut creations = Vec::new();
                charge(budget, requests.len())?;
                creations.try_reserve_exact(requests.len()).map_err(|_| Failure::Resource)?;
                for request in requests { creations.push(self.value(request.scope, request.expression, budget)?); }
                let incoming = self.evidence.incoming(plan, &creations, routes, budget)?
                    .ok_or(Stop::Decline(Decline::Evidence))?;
                let record = self.environments.get_mut(&scope).ok_or(Failure::Invalid)?;
                if record.incoming.is_some() { return Err(Failure::Invalid.into()); }
                record.incoming = Some(incoming);
                let inputs = same_scope(scope, self.evidence.local_requests(plan)?, budget)?;
                self.push(Job::CompleteEvidence(scope), budget)?;
                self.evaluate_many(&inputs, budget)?;
            }
            Job::CompleteEvidence(scope) => {
                let completion = self.evidence_completion(scope, routes.free(budget)?, host, types, routes, budget)?;
                self.registry.complete_external_scope(scope, completion.origin, completion.frame, routes, budget)?;
                self.leave_scope(scope, budget)?;
            }
            Job::FinishEvidenceUse { parent, expression, scope } => {
                let activation = self.registry.scope(parent)?.activation_route;
                let completion = self.evidence_completion(scope, activation, host, types, routes, budget)?;
                let target = self.registry.scope(scope)?.activation;
                self.registry.stage_activation(target, completion.activation_condition, budget)?;
                self.finish(parent, expression, completion.value, routes, budget)?;
            }
        }
        Ok(())
    }

    fn enter_scope(&mut self, scope: ScopeId, budget: &mut TypeWorkBudget) -> Result<(), Stop> {
        charge(budget, 3)?;
        let visiting = &mut self.attempt.as_mut().ok_or(Failure::Invalid)?.scopes_visiting;
        visiting.try_reserve(1).map_err(|_| Failure::Resource)?;
        if !visiting.insert(scope) {
            return Err(Stop::Decline(Decline::Cycle));
        }
        Ok(())
    }

    fn leave_scope(&mut self, scope: ScopeId, budget: &mut TypeWorkBudget) -> Result<(), Failure> {
        charge(budget, 1)?;
        if !self.attempt.as_mut().ok_or(Failure::Invalid)?.scopes_visiting.remove(&scope) {
            return Err(Failure::Invalid);
        }
        Ok(())
    }

    fn schedule_local(&mut self, scope: ScopeId, expression: usize,
        compiler: &mut Compiler<'g>, budget: &mut TypeWorkBudget) -> Result<(), Stop>
    {
        let source = self.registry.graph.expressions.get(expression).ok_or(Failure::Invalid)?;
        if matches!(self.registry.scope(scope)?.kind, ScopeKind::Evidence { .. }) {
            self.local_class(scope, expression, budget)?;
        }
        let mut inputs = Vec::new();
        let local = match source {
            Expr::Slot => Local::Slot,
            Expr::Alias(child) => {
                charge(budget, 1)?;
                inputs.try_reserve(1).map_err(|_| Failure::Resource)?;
                inputs.push((scope, *child));
                Local::Alias(*child)
            }
            Expr::Merge(children) => {
                inputs = same_scope(scope, children, budget)?;
                Local::Merge(copy_slice(children, budget)?)
            }
            Expr::Call { function, arguments, type_application: true, .. } => {
                charge(budget, arguments.len().checked_add(1).ok_or(Failure::Resource)?)?;
                inputs.try_reserve_exact(arguments.len().checked_add(1).ok_or(Failure::Resource)?)
                    .map_err(|_| Failure::Resource)?;
                inputs.push((scope, *function));
                inputs.extend(arguments.iter().map(|argument| (scope, *argument)));
                Local::Typed { function: *function, arguments: copy_slice(arguments, budget)? }
            }
            Expr::Evidence { bindings, .. } => {
                let direct = compiler.direct_evidence_payload(expression, budget)?
                    .ok_or(Stop::Decline(Decline::Evidence))?;
                charge(budget, bindings.len().checked_add(1).ok_or(Failure::Resource)?)?;
                inputs.try_reserve_exact(bindings.len().checked_add(1).ok_or(Failure::Resource)?)
                    .map_err(|_| Failure::Resource)?;
                inputs.push((scope, direct.payload));
                let mut arguments = Vec::new();
                arguments.try_reserve_exact(bindings.len()).map_err(|_| Failure::Resource)?;
                for binding in bindings { inputs.push((scope, binding.2)); arguments.push(binding.2); }
                if matches!(self.registry.scope(scope)?.kind, ScopeKind::Raw { .. })
                    && self.registry.saved_count(scope, expression, budget)? != 0 {
                    inputs.try_reserve(1).map_err(|_| Failure::Resource)?;
                    inputs.push((self.registry.zero(), expression));
                }
                self.push(Job::PrepareEvidence { parent: scope, expression, payload: direct.payload,
                    function: direct.body, bindings: arguments }, budget)?;
                self.evaluate_many(&inputs, budget)?;
                return Ok(());
            }
            _ => return Err(Stop::Decline(Decline::Unsupported)),
        };
        if matches!(self.registry.scope(scope)?.kind, ScopeKind::Raw { .. })
            && self.registry.saved_count(scope, expression, budget)? != 0 {
            inputs.try_reserve(1).map_err(|_| Failure::Resource)?;
            inputs.push((self.registry.zero(), expression));
        }
        self.push(Job::FinishLocal { scope, expression, local }, budget)?;
        self.evaluate_many(&inputs, budget)?;
        Ok(())
    }

    fn schedule_zero(&mut self, expression: usize, host: &impl Host,
        compiler: &mut Compiler<'g>, budget: &mut TypeWorkBudget) -> Result<(), Stop>
    {
        charge(budget, 1)?;
        let singleton = [expression];
        let empty_slots = if host.zero_empty_slot(expression) { &singleton[..] } else { &[] };
        let certificate = ZeroCertificate { graph: self.registry.graph, empty_slots };
        let request = zero::request(&self.registry, compiler, expression, &certificate, budget)?
            .map_err(|reason| Stop::Decline(reason.into()))?;
        let zero = self.registry.zero();
        let inputs = match &request {
            zero::Request::Slot { .. } => Vec::new(),
            zero::Request::Alias { child, .. } => same_scope(zero, &[*child], budget)?,
            zero::Request::Merge { inputs, .. } => same_scope(zero, inputs, budget)?,
            zero::Request::TypedCall { function, arguments, .. } => {
                let mut result = same_scope(zero, arguments, budget)?;
                charge(budget, result.len().checked_add(1).ok_or(Failure::Resource)?)?;
                result.try_reserve(1).map_err(|_| Failure::Resource)?;
                result.insert(0, (zero, *function));
                result
            }
            zero::Request::Evidence { payload, .. } => same_scope(zero, &[*payload], budget)?,
        };
        self.push(Job::FinishZero(request), budget)?;
        self.evaluate_many(&inputs, budget)?;
        Ok(())
    }

    fn finish_zero(&mut self, request: zero::Request, host: &impl Host,
        compiler: &mut Compiler<'g>, types: &mut Types, routes: &mut Routes,
        budget: &mut TypeWorkBudget) -> Result<(), Stop>
    {
        let zero = self.registry.zero();
        let (expression, value) = match request {
            zero::Request::Slot { expression, role, class, empty } => {
                if empty && matches!(class, ProjectionClass::Empty | ProjectionClass::Metadata) {
                    self.journal_zero(expression, budget)?;
                }
                (expression, zero::finish_slot(&mut self.zero, expression, role, class, empty, routes, budget)?)
            }
            zero::Request::Alias { expression, child, class } => {
                let value = self.value(zero, child, budget)?;
                if matches!(class, ProjectionClass::Empty | ProjectionClass::Metadata) {
                    self.journal_zero(expression, budget)?;
                }
                let value = zero::finish_alias(&mut self.zero, expression, child, class, &value, routes, budget)?
                    .map_err(|reason| Stop::Decline(reason.into()))?;
                (expression, value)
            }
            zero::Request::Merge { expression, inputs } => {
                self.journal_zero(expression, budget)?;
                let value = zero::finish_merge(&mut self.zero, expression, &inputs, routes, budget)?
                    .map_err(|reason| Stop::Decline(reason.into()))?;
                (expression, value)
            }
            zero::Request::TypedCall { expression, .. } => {
                let stage = zero::begin_typed(&mut self.registry, &self.zero, expression, types, routes, budget)?
                    .map_err(|reason| Stop::Decline(reason.into()))?;
                let scopes = branch_scopes(&stage, budget)?;
                self.push(Job::FinishTyped { stage, saved_zero: true }, budget)?;
                for scope in scopes.into_iter().rev() { self.push(Job::EnsureRaw(scope), budget)?; }
                return Ok(());
            }
            zero::Request::Evidence { expression, payload, returned, .. } => {
                let payload = self.value(zero, payload, budget)?;
                charge(budget, 2)?;
                let exact = host.exact_evidence_zero(expression)
                    .ok_or(Stop::Decline(Decline::MissingHost))?;
                if exact.expression != expression { return Err(Failure::Invalid.into()); }
                let admitted = host.admitted(returned)
                    .ok_or(Stop::Decline(Decline::MissingHost))?;
                let value = zero::finish_evidence(&mut self.registry, compiler, &exact, &payload,
                    admitted, types, routes, budget)?
                    .map_err(|reason| Stop::Decline(reason.into()))?;
                charge(budget, value.alternatives.len())?;
                for alternative in &value.alternatives {
                    charge(budget, 4)?;
                    if self.saved_contexts.contains_key(&alternative.creation) { return Err(Failure::Invalid.into()); }
                    self.saved_contexts.try_reserve(1).map_err(|_| Failure::Resource)?;
                    let journal = &mut self.attempt.as_mut().ok_or(Failure::Invalid)?.saved_scopes;
                    journal.try_reserve(1).map_err(|_| Failure::Resource)?;
                    journal.push(alternative.creation);
                    self.saved_contexts.insert(alternative.creation, exact.context);
                }
                (expression, value)
            }
        };
        self.registry.put(zero, expression, value, budget)?;
        self.done(zero, expression, budget)?;
        Ok(())
    }

    fn evidence_completion(&mut self, scope: ScopeId, parent_activation: RouteId,
        host: &impl Host, types: &mut Types, routes: &mut Routes, budget: &mut TypeWorkBudget,
    ) -> Result<evidence::Completion, Stop> {
        let environment = self.environments.get(&scope).ok_or(Failure::Invalid)?;
        let plan = environment.plan;
        let function = environment.function;
        let inputs = same_scope(scope, self.evidence.local_requests(plan)?, budget)?;
        let complete = self.values(&inputs, budget)?;
        charge(budget, 1)?;
        let admitted = host.admitted(function)
            .ok_or(Stop::Decline(Decline::MissingHost))?;
        self.evidence.complete(plan, scope, &complete, parent_activation, admitted, types, routes, budget)?
            .ok_or(Stop::Decline(Decline::Evidence))
    }
}

fn same_scope(scope: ScopeId, expressions: &[usize], budget: &mut TypeWorkBudget)
    -> Result<Vec<(ScopeId, usize)>, Failure>
{
    charge(budget, expressions.len())?;
    let mut result = Vec::new();
    result.try_reserve_exact(expressions.len()).map_err(|_| Failure::Resource)?;
    result.extend(expressions.iter().map(|expression| (scope, *expression)));
    Ok(result)
}

fn call_inputs(graph: &Graph, expression: usize, budget: &mut TypeWorkBudget)
    -> Result<(usize, Vec<usize>), Failure>
{
    let Some(Expr::Call { function, arguments, type_application: true, .. }) = graph.expressions.get(expression)
        else { return Err(Failure::Invalid); };
    Ok((*function, copy_slice(arguments, budget)?))
}

fn branch_scopes(stage: &TypedStage, budget: &mut TypeWorkBudget) -> Result<Vec<ScopeId>, Failure> {
    charge(budget, stage.branches.len())?;
    let mut scopes = Vec::new();
    scopes.try_reserve_exact(stage.branches.len()).map_err(|_| Failure::Resource)?;
    scopes.extend(stage.branches.iter().map(|branch| branch.scope));
    Ok(scopes)
}

fn conditional_origin(input: &Value, types: &mut Types,
    budget: &mut TypeWorkBudget) -> Result<TypeOrigin, Failure>
{
    charge(budget, input.alternatives.len())?;
    let mut origins = Vec::new();
    origins.try_reserve_exact(input.alternatives.len()).map_err(|_| Failure::Resource)?;
    origins.extend(input.alternatives.iter().map(|alternative| (alternative.origin, alternative.gate)));
    Ok(TypeOrigin::Conditional(types.conditional(&origins, budget)?))
}

// Explicit flat traversal keeps all coherent conditional origin/gate pairs.
// OriginalContext is never guessed symbolic outside the separate Zero helper.
fn flatten_origins(origin: TypeOrigin, types: &Types, routes: &mut Routes,
    budget: &mut TypeWorkBudget) -> Result<Vec<(TypeOrigin, RouteId)>, Stop>
{
    let free = routes.free(budget)?;
    let mut work = Vec::new();
    let mut result = Vec::new();
    charge(budget, 1)?;
    work.try_reserve(1).map_err(|_| Failure::Resource)?;
    work.push((origin, free));
    while let Some((origin, gate)) = work.pop() {
        charge(budget, 1)?;
        match origin {
            TypeOrigin::Conditional(id) => {
                let alternatives = types.conditional_origins(id)?;
                charge(budget, alternatives.len())?;
                work.try_reserve(alternatives.len()).map_err(|_| Failure::Resource)?;
                for &(origin, next_gate) in alternatives.iter().rev() {
                    let gate = routes.equation_ready(&[gate, next_gate], free, budget)?;
                    work.push((origin, gate));
                }
            }
            TypeOrigin::Normalized(_) => {
                result.try_reserve(1).map_err(|_| Failure::Resource)?;
                result.push((origin, gate));
            }
            TypeOrigin::OriginalContext(_) => return Err(Stop::Decline(Decline::Origin)),
        }
    }
    Ok(result)
}
