//! Private source fragment: child of capture::value, alongside deferred_frame.
//! Input preservation and substitution only. No source/frame admission token.
//! One arena belongs to one immutable Graph and one paired deferred_frame::Arena.

use std::collections::{HashMap, HashSet};
use std::hash::{DefaultHasher, Hash, Hasher};

use super::{Expr, Failure, Graph, ProducerWitness, TypeWorkBudget, charge};
use super::deferred_frame::RouteId;
use crate::types::{self, EffectRow, IterativeArgumentOwner, Kind, KindedArgument, Type,
    TypeVariableId};

// Pure normalized input equations, never an original context or occurrence ID.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(super) struct NormalizedEnvironmentId(usize);

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(super) struct ConditionalOriginId(usize);

// OriginalContext is unresolved provenance, never permission to guess a type
// environment from the current owner atoms or from equal static Types.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(super) enum TypeOrigin {
    Normalized(NormalizedEnvironmentId),
    Conditional(ConditionalOriginId),
    OriginalContext(usize),
}

pub(super) struct NormalizedBinding {
    definition_binder: TypeVariableId,
    use_binder: TypeVariableId,
    formal: usize,
    actual: usize,
    route: RouteId,
    normalized: IterativeArgumentOwner,
}

impl NormalizedBinding {
    pub(super) fn route(&self) -> RouteId { self.route }
    pub(super) fn argument(&self) -> &KindedArgument { self.normalized.as_ref() }
}

// Original definition/use witnesses remain addressed by factory/application
// graph coordinates. Headers are retained in full for canonical comparison.
// Bindings describe the CLOSED global factory's definition scope only; they
// do not import a dynamic caller's unrelated binders into that factory.
pub(super) struct NormalizedEnvironment {
    application: usize,
    factory: usize,
    definition_header: Vec<(TypeVariableId, Kind)>,
    use_header: Vec<(TypeVariableId, Kind)>,
    bindings: Vec<NormalizedBinding>,
}

impl NormalizedEnvironment {
    pub(super) fn factory(&self) -> usize { self.factory }
    pub(super) fn bindings(&self) -> &[NormalizedBinding] { &self.bindings }
}

// Private fields prevent callers forging positional alpha pairing from kinds
// alone. The token borrows the exact immutable graph/witness records checked
// below. It is NOT a lifetime callee-stream or source-admission certificate.
pub(super) struct CheckedFactoryUse<'g> {
    graph: &'g Graph,
    application: usize,
    factory: usize,
    use_header: &'g [(TypeVariableId, Kind)],
    definition_header: &'g [(TypeVariableId, Kind)],
    formals: &'g [usize],
    arguments: &'g [super::ProducerArgument],
}

impl CheckedFactoryUse<'_> {
    pub(super) fn factory(&self) -> usize { self.factory }
}

fn producer(graph: &Graph, expression: usize) -> Option<&ProducerWitness> {
    match graph.producers.as_slice() {
        [table] => table.entries.get(&expression),
        _ => None,
    }
}

// Complete Kind equality with paid, fallible, iterative traversal storage.
fn same_kind(left: &Kind, right: &Kind, budget: &mut TypeWorkBudget) -> Result<bool, Failure> {
    charge(budget, 1)?;
    let mut pending = Vec::new();
    pending.try_reserve(1).map_err(|_| Failure::Resource)?;
    pending.push((left, right));
    while let Some((left, right)) = pending.pop() {
        charge(budget, 1)?;
        match (left, right) {
            (Kind::Type, Kind::Type) | (Kind::EffectRow, Kind::EffectRow) => {}
            (Kind::Arrow(ld, lc), Kind::Arrow(rd, rc)) => {
                charge(budget, 2)?;
                pending.try_reserve(2).map_err(|_| Failure::Resource)?;
                pending.push((lc.as_ref(), rc.as_ref()));
                pending.push((ld.as_ref(), rd.as_ref()));
            }
            _ => return Ok(false),
        }
    }
    Ok(true)
}

// Immutable witness/shape relation only. This does not establish a current or
// lifetime callee stream, closed lexical scope, activation, or source admission.
pub(super) fn check_global_factory_shape<'g>(
    graph: &'g Graph, application: usize, budget: &mut TypeWorkBudget,
) -> Result<Option<CheckedFactoryUse<'g>>, Failure> {
    charge(budget, 1)?;
    let Some(ProducerWitness::Application { function, binders: use_header, arguments }) =
        producer(graph, application) else { return Ok(None); };
    let Some(Expr::Call { function: original_function, arguments: original_arguments,
        type_application: true, .. }) = graph.expressions.get(application)
        else { return Ok(None); };
    charge(budget, arguments.len())?;
    if function != original_function || original_arguments.len() != arguments.len()
        || original_arguments.iter().zip(arguments).any(|(a, b)| *a != b.port)
    { return Ok(None); }
    let Some(Expr::Alias(global)) = graph.expressions.get(*function) else { return Ok(None); };
    charge(budget, graph.globals.len())?;
    let mut sources = graph.globals.iter().filter(|(slot, _)| slot == global);
    let Some(&(_, factory)) = sources.next() else { return Ok(None); };
    if sources.next().is_some() { return Ok(None); }
    let Some(ProducerWitness::Abstraction { binders: definition_header, formals }) =
        producer(graph, factory) else { return Ok(None); };
    let Some(Expr::Function { parameters, body, .. }) = graph.expressions.get(factory)
        else { return Ok(None); };
    charge(budget, parameters.len())?;
    if parameters != formals || formals.is_empty() || formals.len() != definition_header.len()
        || use_header.len() != definition_header.len() || arguments.len() != formals.len()
    { return Ok(None); }
    // Retain this first slice's original TypeAbs -> ordinary Function role.
    let Some(Expr::Function { parameters: inner, captures, .. }) = graph.expressions.get(*body)
        else { return Ok(None); };
    if inner.len() != 1 || captures.is_empty() || graph.metadata.contains_key(&inner[0])
        || !graph.targets.contains_key(body)
    { return Ok(None); }
    charge(budget, formals.len().checked_mul(3).ok_or(Failure::Resource)?)?;
    let mut definitions = HashSet::new();
    let mut uses = HashSet::new();
    let mut slots = HashSet::new();
    definitions.try_reserve(formals.len()).map_err(|_| Failure::Resource)?;
    uses.try_reserve(formals.len()).map_err(|_| Failure::Resource)?;
    slots.try_reserve(formals.len()).map_err(|_| Failure::Resource)?;
    for (((definition, dk), (use_binder, uk)), (formal, argument)) in definition_header.iter()
        .zip(use_header).zip(formals.iter().zip(arguments))
    {
        charge(budget, 1)?;
        if !definitions.insert(*definition) || !uses.insert(*use_binder) || !slots.insert(*formal)
            || graph.metadata.get(formal) != Some(definition)
            || !matches!(graph.expressions.get(*formal), Some(Expr::Slot))
            || !same_kind(dk, uk, budget)?
        { return Ok(None); }
        match (dk, argument.value.as_ref()) {
            (Kind::EffectRow, KindedArgument::RowArg(_)) => {}
            (Kind::Type | Kind::Arrow(_, _), KindedArgument::TypeArg(_)) => {}
            _ => return Ok(None),
        }
        let Some(Expr::Merge(inputs)) = graph.expressions.get(argument.port) else { return Ok(None); };
        charge(budget, inputs.len())?;
        if inputs.iter().any(|input| !graph.metadata.contains_key(input)
            || !matches!(graph.expressions.get(*input), Some(Expr::Slot)))
        { return Ok(None); }
    }
    Ok(Some(CheckedFactoryUse { graph, application, factory,
        use_header, definition_header, formals, arguments }))
}

// Full Type hashing is the shared paid/fallible iterative operation. The row
// root traversal below likewise retains only borrowed flat work; it includes
// exact known instances, nested kinded arguments, tail identity and lacks.
fn hash_argument(argument: &KindedArgument, state: &mut impl Hasher,
    budget: &mut TypeWorkBudget) -> Result<(), Failure>
{
    enum Work<'a> {
        Argument(&'a KindedArgument),
        Row(&'a EffectRow),
        Arguments(std::slice::Iter<'a, KindedArgument>),
        Instances(std::slice::Iter<'a, types::EffectInstance>),
    }
    let mut pending = Vec::new();
    macro_rules! push {
        ($work:expr) => {{
            charge(budget, 1)?;
            pending.try_reserve(1).map_err(|_| Failure::Resource)?;
            pending.push($work);
        }};
    }
    push!(Work::Argument(argument));
    while let Some(work) = pending.pop() {
        match work {
            Work::Argument(KindedArgument::TypeArg(ty)) => {
                0_u8.hash(state);
                types::hash_type_with_budget(ty, state, budget).map_err(|()| Failure::Resource)?;
            }
            Work::Argument(KindedArgument::RowArg(row)) => {
                1_u8.hash(state);
                push!(Work::Row(row));
            }
            Work::Arguments(mut arguments) => {
                if let Some(argument) = arguments.next() {
                    push!(Work::Arguments(arguments));
                    push!(Work::Argument(argument));
                }
            }
            Work::Instances(mut instances) => {
                if let Some(instance) = instances.next() {
                    instance.effect().hash(state);
                    instance.arguments().len().hash(state);
                    push!(Work::Instances(instances));
                    push!(Work::Arguments(instance.arguments().iter()));
                }
            }
            Work::Row(row) => {
                10_u8.hash(state);
                row.known().len().hash(state);
                match row.tail() {
                    None => 0_u8.hash(state),
                    Some(tail) => {
                        1_u8.hash(state);
                        tail.variable().hash(state);
                        tail.lacks().len().hash(state);
                        push!(Work::Instances(tail.lacks().iter()));
                    }
                }
                push!(Work::Instances(row.known().iter()));
            }
        }
    }
    Ok(())
}

fn hash_header(header: &[(TypeVariableId, Kind)], state: &mut impl Hasher,
    budget: &mut TypeWorkBudget) -> Result<(), Failure>
{
    charge(budget, header.len().checked_add(1).ok_or(Failure::Resource)?)?;
    header.len().hash(state);
    for (binder, kind) in header {
        binder.hash(state);
        types::hash_kind_with_budget(kind, state, budget).map_err(|()| Failure::Resource)?;
    }
    Ok(())
}

impl NormalizedEnvironment {
    fn key_hash(&self, budget: &mut TypeWorkBudget) -> Result<u64, Failure> {
        let mut state = DefaultHasher::new();
        charge(budget, self.bindings.len().checked_add(3).ok_or(Failure::Resource)?)?;
        self.application.hash(&mut state);
        self.factory.hash(&mut state);
        hash_header(&self.definition_header, &mut state, budget)?;
        hash_header(&self.use_header, &mut state, budget)?;
        self.bindings.len().hash(&mut state);
        for binding in &self.bindings {
            binding.definition_binder.hash(&mut state);
            binding.use_binder.hash(&mut state);
            binding.formal.hash(&mut state);
            binding.actual.hash(&mut state);
            binding.route.hash(&mut state);
            hash_argument(binding.argument(), &mut state, budget)?;
        }
        Ok(state.finish())
    }

    fn same_key(&self, other: &Self, budget: &mut TypeWorkBudget) -> Result<bool, Failure> {
        charge(budget, 3)?;
        if self.application != other.application || self.factory != other.factory
            || self.bindings.len() != other.bindings.len()
        { return Ok(false); }
        for (left, right) in [(&self.definition_header, &other.definition_header),
            (&self.use_header, &other.use_header)]
        {
            charge(budget, left.len().checked_add(1).ok_or(Failure::Resource)?)?;
            if left.len() != right.len() { return Ok(false); }
            for ((lb, lk), (rb, rk)) in left.iter().zip(right) {
                if lb != rb || !same_kind(lk, rk, budget)? { return Ok(false); }
            }
        }
        charge(budget, self.bindings.len())?;
        for (left, right) in self.bindings.iter().zip(&other.bindings) {
            if left.definition_binder != right.definition_binder || left.use_binder != right.use_binder
                || left.formal != right.formal || left.actual != right.actual || left.route != right.route
                || !types::same_kinded_argument_with_budget(left.argument(), right.argument(), budget)
                    .map_err(|()| Failure::Resource)?
            { return Ok(false); }
        }
        Ok(true)
    }

    fn copy(&self, budget: &mut TypeWorkBudget) -> Result<Self, Failure> {
        let definition_header = types::clone_kinded_type_parameters_fallibly_with_budget(
            &self.definition_header, budget).map_err(|()| Failure::Resource)?;
        let use_header = types::clone_kinded_type_parameters_fallibly_with_budget(
            &self.use_header, budget).map_err(|()| Failure::Resource)?;
        charge(budget, self.bindings.len())?;
        let mut bindings = Vec::new();
        bindings.try_reserve_exact(self.bindings.len()).map_err(|_| Failure::Resource)?;
        for binding in &self.bindings {
            let normalized = IterativeArgumentOwner::new(
                types::clone_kinded_argument_with_budget(binding.argument(), budget)
                    .map_err(|()| Failure::Resource)?);
            bindings.push(NormalizedBinding { definition_binder: binding.definition_binder,
                use_binder: binding.use_binder, formal: binding.formal, actual: binding.actual,
                route: binding.route, normalized });
        }
        Ok(Self { application: self.application, factory: self.factory,
            definition_header, use_header, bindings })
    }
}

pub(super) struct Arena {
    normalized: Vec<NormalizedEnvironment>,
    normalized_by_hash: HashMap<u64, Vec<NormalizedEnvironmentId>>,
    normalized_graph: Option<usize>,
    conditional: Vec<Vec<(TypeOrigin, RouteId)>>,
    conditional_by_hash: HashMap<u64, Vec<ConditionalOriginId>>,
}

impl Arena {
    pub(super) fn new() -> Self {
        Self { normalized: Vec::new(), normalized_by_hash: HashMap::new(), normalized_graph: None,
            conditional: Vec::new(), conditional_by_hash: HashMap::new() }
    }

    pub(super) fn normalized(&self, id: NormalizedEnvironmentId)
        -> Result<&NormalizedEnvironment, Failure>
    {
        self.normalized.get(id.0).ok_or(Failure::Invalid)
    }

    pub(super) fn conditional_origins(&self, id: ConditionalOriginId)
        -> Result<&[(TypeOrigin, RouteId)], Failure>
    {
        self.conditional.get(id.0).map(Vec::as_slice).ok_or(Failure::Invalid)
    }

    // Preserve every ordered origin/gate pair, including repeated alternatives.
    // Gates are exact equations in the paired route arena, never observed here.
    // A conditional may refer only to already published origin records; owned
    // storage is flat and no recursive origin/drop ownership can arise.
    pub(super) fn conditional(&mut self, origins: &[(TypeOrigin, RouteId)],
        budget: &mut TypeWorkBudget) -> Result<ConditionalOriginId, Failure>
    {
        charge(budget, origins.len().checked_add(1).ok_or(Failure::Resource)?)?;
        let mut state = DefaultHasher::new();
        origins.len().hash(&mut state);
        for (origin, gate) in origins {
            match origin {
                TypeOrigin::Normalized(id) => { self.normalized(*id)?; }
                TypeOrigin::Conditional(id) => { self.conditional_origins(*id)?; }
                TypeOrigin::OriginalContext(_) => {}
            }
            origin.hash(&mut state);
            gate.hash(&mut state);
        }
        let hash = state.finish();
        charge(budget, 1)?;
        if let Some(ids) = self.conditional_by_hash.get(&hash) {
            charge(budget, ids.len())?;
            for id in ids {
                let existing = self.conditional_origins(*id)?;
                charge(budget, origins.len().checked_add(1).ok_or(Failure::Resource)?)?;
                if existing == origins { return Ok(*id); }
            }
        }
        let origins = super::copy_slice(origins, budget)?;
        charge(budget, 3)?;
        self.conditional.try_reserve(1).map_err(|_| Failure::Resource)?;
        self.conditional_by_hash.try_reserve(1).map_err(|_| Failure::Resource)?;
        let id = ConditionalOriginId(self.conditional.len());
        if let Some(ids) = self.conditional_by_hash.get_mut(&hash) {
            ids.try_reserve(1).map_err(|_| Failure::Resource)?;
            self.conditional.push(origins);
            ids.push(id);
        } else {
            let mut ids = Vec::new();
            ids.try_reserve_exact(1).map_err(|_| Failure::Resource)?;
            ids.push(id);
            self.conditional.push(origins);
            self.conditional_by_hash.insert(hash, ids);
        }
        Ok(id)
    }

    // This operation is input normalization only. Before using its result as
    // a virtual factory scope, the source owner must prove closed-global free
    // binder coverage, original lexical provenance (including imports), and
    // the exact metadata-route equations in the paired route arena. The shape
    // token and Type equality cannot supply those proofs. Symbolic free Types
    // and row tails remain exact terms; they are not guessed to be closed.
    // Child substitution scope retains ONLY this factory's definition bindings.
    pub(super) fn normalize(
        &mut self, relation: &CheckedFactoryUse<'_>, parent: TypeOrigin,
        actual_routes: &[RouteId], budget: &mut TypeWorkBudget,
    ) -> Result<Option<NormalizedEnvironmentId>, Failure> {
        charge(budget, 1)?;
        let candidate = {
            let (replacements, rows) = match parent {
                TypeOrigin::OriginalContext(_) | TypeOrigin::Conditional(_) => return Ok(None),
                TypeOrigin::Normalized(id) => {
                    let environment = self.normalized(id)?;
                    let mut replacements = HashMap::new();
                    let mut rows = HashMap::new();
                    charge(budget, environment.bindings.len().checked_mul(2).ok_or(Failure::Resource)?)?;
                    for binding in &environment.bindings {
                        match binding.argument() {
                            KindedArgument::TypeArg(ty) => {
                                replacements.try_reserve(1).map_err(|_| Failure::Resource)?;
                                replacements.insert(binding.definition_binder, ty);
                            }
                            KindedArgument::RowArg(row) => {
                                let row = types::clone_effect_row_with_budget(row, budget)
                                    .map_err(|()| Failure::Resource)?;
                                rows.try_reserve(1).map_err(|_| Failure::Resource)?;
                                rows.insert(binding.definition_binder, row);
                            }
                        }
                    }
                    (replacements, rows)
                }
            };
            Self::normalize_candidate(relation, actual_routes, &replacements, &rows, budget)?
        };
        let Some(candidate) = candidate else { return Ok(None); };
        self.intern_normalized(relation.graph, candidate, budget).map(Some)
    }

    // Explicit ORIGINAL symbolic seed, with identity substitution. The caller
    // must separately authenticate context 0 or its exact canonical Root(owner)
    // seed, unique original body/root and closed-global scope. This is not a
    // recovery path for an unresolved ordinary Invoke/OriginalContext origin.
    pub(super) fn normalize_closed_symbolic(
        &mut self, relation: &CheckedFactoryUse<'_>, actual_routes: &[RouteId],
        budget: &mut TypeWorkBudget,
    ) -> Result<Option<NormalizedEnvironmentId>, Failure> {
        charge(budget, 1)?;
        let Some(candidate) = Self::normalize_candidate(relation, actual_routes,
            &HashMap::new(), &HashMap::new(), budget)? else { return Ok(None); };
        self.intern_normalized(relation.graph, candidate, budget).map(Some)
    }

    fn normalize_candidate(
        relation: &CheckedFactoryUse<'_>, actual_routes: &[RouteId],
        replacements: &HashMap<TypeVariableId, &Type>, rows: &HashMap<TypeVariableId, EffectRow>,
        budget: &mut TypeWorkBudget,
    ) -> Result<Option<NormalizedEnvironment>, Failure> {
        charge(budget, relation.arguments.len().checked_add(1).ok_or(Failure::Resource)?)?;
        if actual_routes.len() != relation.arguments.len() { return Err(Failure::Invalid); }
        let definition_header = types::clone_kinded_type_parameters_fallibly_with_budget(
            relation.definition_header, budget).map_err(|()| Failure::Resource)?;
        let use_header = types::clone_kinded_type_parameters_fallibly_with_budget(
            relation.use_header, budget).map_err(|()| Failure::Resource)?;
        let mut bindings = Vec::new();
        bindings.try_reserve_exact(relation.arguments.len()).map_err(|_| Failure::Resource)?;
        for ((((definition, _), (use_binder, _)), (formal, argument)), route) in relation.definition_header
            .iter().zip(relation.use_header).zip(relation.formals.iter().zip(relation.arguments))
            .zip(actual_routes)
        {
            // One simultaneous substitution; shared traversal shields nested
            // Forall binders and validates complete row/lacks constraints.
            let normalized = match types::substitute_kinded_argument_borrowed_with(
                argument.value.as_ref(), replacements, rows, |cells| budget.charge(cells),
            ).map_err(|()| Failure::Resource)? {
                Ok(value) => IterativeArgumentOwner::new(value),
                Err(_) => return Ok(None),
            };
            bindings.push(NormalizedBinding { definition_binder: *definition,
                use_binder: *use_binder, formal: *formal, actual: argument.port,
                route: *route, normalized });
        }
        Ok(Some(NormalizedEnvironment { application: relation.application,
            factory: relation.factory, definition_header, use_header, bindings }))
    }

    fn intern_normalized(&mut self, graph: &Graph, candidate: NormalizedEnvironment,
        budget: &mut TypeWorkBudget) -> Result<NormalizedEnvironmentId, Failure>
    {
        // Exact immutable Graph namespace, not a Type or activation identity.
        // No raw pointer is retained or dereferenced; the existing graph loan
        // owns the arena for this whole analysis and each independent snapshot.
        let graph_identity = std::ptr::from_ref(graph) as usize;
        charge(budget, 1)?;
        if self.normalized_graph.is_some_and(|original| original != graph_identity) {
            return Err(Failure::Invalid);
        }
        let hash = candidate.key_hash(budget)?;
        charge(budget, 1)?;
        if let Some(ids) = self.normalized_by_hash.get(&hash) {
            charge(budget, ids.len())?;
            for id in ids {
                if self.normalized(*id)?.same_key(&candidate, budget)? { return Ok(*id); }
            }
        }
        // Reserve every retained record/index entry before either is published.
        charge(budget, 3)?;
        self.normalized.try_reserve(1).map_err(|_| Failure::Resource)?;
        self.normalized_by_hash.try_reserve(1).map_err(|_| Failure::Resource)?;
        let mut new_ids = None;
        if let Some(ids) = self.normalized_by_hash.get_mut(&hash) {
            ids.try_reserve(1).map_err(|_| Failure::Resource)?;
        } else {
            let mut ids = Vec::new();
            ids.try_reserve_exact(1).map_err(|_| Failure::Resource)?;
            new_ids = Some(ids);
        }
        let id = NormalizedEnvironmentId(self.normalized.len());
        if let Some(mut ids) = new_ids {
            ids.push(id);
            self.normalized.push(candidate);
            self.normalized_by_hash.insert(hash, ids);
        } else {
            let ids = self.normalized_by_hash.get_mut(&hash).ok_or(Failure::Invalid)?;
            self.normalized.push(candidate);
            ids.push(id);
        }
        self.normalized_graph = Some(graph_identity);
        Ok(id)
    }

    // Preserve normalized/conditional IDs and RouteIds exactly. Pair this
    // independent query copy with the SAME frame arena's terminal snapshot.
    // Query-local normalized additions never mutate the normal owner's arena.
    pub(super) fn snapshot(&self, budget: &mut TypeWorkBudget) -> Result<Self, Failure> {
        let mut result = Self::new();
        charge(budget, self.normalized.len().checked_add(self.normalized_by_hash.len())
            .ok_or(Failure::Resource)?)?;
        result.normalized.try_reserve_exact(self.normalized.len()).map_err(|_| Failure::Resource)?;
        result.normalized_by_hash.try_reserve(self.normalized_by_hash.len()).map_err(|_| Failure::Resource)?;
        for environment in &self.normalized { result.normalized.push(environment.copy(budget)?); }
        for (&hash, ids) in &self.normalized_by_hash {
            result.normalized_by_hash.insert(hash, super::copy_slice(ids, budget)?);
        }
        result.normalized_graph = self.normalized_graph;
        charge(budget, self.conditional.len().checked_add(self.conditional_by_hash.len())
            .ok_or(Failure::Resource)?)?;
        result.conditional.try_reserve_exact(self.conditional.len()).map_err(|_| Failure::Resource)?;
        result.conditional_by_hash.try_reserve(self.conditional_by_hash.len()).map_err(|_| Failure::Resource)?;
        for origins in &self.conditional { result.conditional.push(super::copy_slice(origins, budget)?); }
        for (&hash, ids) in &self.conditional_by_hash {
            result.conditional_by_hash.insert(hash, super::copy_slice(ids, budget)?);
        }
        Ok(result)
    }
}
