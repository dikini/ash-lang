//! Private source fragment: child of capture::value, alongside deferred_frame.
//! Input preservation and substitution only. No source/frame admission token.
//! One arena belongs to one immutable Graph and one paired deferred_frame::Arena.

use std::collections::{HashMap, HashSet};

use super::{Atom, Expr, Failure, Graph, ProducerWitness, TypeWorkBudget, charge};
use super::deferred_frame::{Arena as RouteArena, OriginalPort, ProjectionClass, RouteId};
use crate::types::{self, EffectRow, IterativeArgumentOwner, Kind, KindedArgument, Type,
    TypeVariableId};

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(super) struct TypeEnvironmentId(usize);

// OriginalContext is unresolved provenance, never permission to guess a type
// environment from the current owner atoms or from equal static Types.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(super) enum TypeOrigin {
    Environment(TypeEnvironmentId),
    OriginalContext(usize),
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(super) struct Occurrence {
    pub(super) application: OriginalPort,
    pub(super) factory: usize,
    pub(super) creation: usize,
    pub(super) invocation: usize,
}

pub(super) struct Binding {
    // Definition-side binder is the substitution key in the original body.
    // Use-side binder is retained even when the checked relation pairs alpha
    // variants positionally. Neither is a graph expression coordinate.
    definition_binder: TypeVariableId,
    use_binder: TypeVariableId,
    formal: OriginalPort,
    actual: OriginalPort,
    // Complete original argument occurrence head. This preserves its source
    // identity even when two full normalized arguments are equal.
    route: RouteId,
    // Free plus ordered original metadata input heads, only the Merge's LOCAL
    // recipe. The consumer must retain every other original incoming feed.
    local_merge: RouteId,
    normalized: IterativeArgumentOwner,
}

impl Binding {
    pub(super) fn definition_binder(&self) -> TypeVariableId { self.definition_binder }
    pub(super) fn use_binder(&self) -> TypeVariableId { self.use_binder }
    pub(super) fn formal(&self) -> OriginalPort { self.formal }
    pub(super) fn actual(&self) -> OriginalPort { self.actual }
    pub(super) fn route(&self) -> RouteId { self.route }
    pub(super) fn local_merge(&self) -> RouteId { self.local_merge }
    pub(super) fn argument(&self) -> &KindedArgument { self.normalized.as_ref() }
}

pub(super) struct FrameEnvironment {
    occurrence: Occurrence,
    parent: Option<TypeEnvironmentId>,
    // Ordered, full original definition-side Forall header. Kind owns an
    // iterative destructor; arguments below use IterativeArgumentOwner.
    header: Vec<(TypeVariableId, Kind)>,
    bindings: Vec<Binding>,
}

impl FrameEnvironment {
    pub(super) fn occurrence(&self) -> Occurrence { self.occurrence }
    pub(super) fn parent(&self) -> Option<TypeEnvironmentId> { self.parent }
    pub(super) fn header(&self) -> &[(TypeVariableId, Kind)] { &self.header }
    pub(super) fn bindings(&self) -> &[Binding] { &self.bindings }
}

pub(super) struct PendingTypeEnvironment(FrameEnvironment);

// Private fields prevent callers forging positional alpha pairing from kinds
// alone. The token borrows the exact immutable graph/witness records checked
// below. It is NOT a lifetime callee-stream or source-admission certificate.
pub(super) struct CheckedFactoryUse<'g> {
    graph: &'g Graph,
    application: usize,
    factory: usize,
    creation: usize,
    use_header: &'g [(TypeVariableId, Kind)],
    definition_header: &'g [(TypeVariableId, Kind)],
    formals: &'g [usize],
    arguments: &'g [super::ProducerArgument],
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

// This restricted checker needs BOTH independently produced typed witnesses
// AND the unchanged direct Alias -> unique global -> exact factory relation.
// It does not discover factories from equal free-variable/kind lists.
// `callee` must be the actual original Call reader's observed closure. The
// eventual source qualifier must separately prove its lifetime stream/role,
// focus/freeze/recurrence guards and all original creation feeds.
pub(super) fn check_global_factory_use<'g>(
    graph: &'g Graph, application: usize, callee: Atom, budget: &mut TypeWorkBudget,
) -> Result<Option<CheckedFactoryUse<'g>>, Failure> {
    charge(budget, 1)?;
    let Atom::Closure(factory, creation) = callee else { return Ok(None); };
    if creation != 0 { return Ok(None); }
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
    if sources.next() != Some(&(*global, factory)) || sources.next().is_some() { return Ok(None); }
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
    Ok(Some(CheckedFactoryUse { graph, application, factory, creation,
        use_header, definition_header, formals, arguments }))
}

pub(super) struct Arena {
    environments: Vec<FrameEnvironment>,
    // Original occurrence plus inherited occurrence identity, never Type Eq.
    by_occurrence: HashMap<(Occurrence, Option<TypeEnvironmentId>), TypeEnvironmentId>,
    // One original Invoke can union several creation environments. Never
    // overwrite an earlier alternative with the last environment seen.
    contexts: HashMap<usize, Vec<TypeEnvironmentId>>,
    frozen_contexts: Option<usize>,
}

impl Arena {
    pub(super) fn new() -> Self {
        Self { environments: Vec::new(), by_occurrence: HashMap::new(),
            contexts: HashMap::new(), frozen_contexts: None }
    }

    pub(super) fn get(&self, id: TypeEnvironmentId) -> Result<&FrameEnvironment, Failure> {
        self.environments.get(id.0).ok_or(Failure::Invalid)
    }

    // Flat parent IDs must refer strictly backwards. There is no recursive
    // environment ownership or destructor, and traversal cannot form a cycle.
    fn parent_of(&self, id: TypeEnvironmentId) -> Result<Option<TypeEnvironmentId>, Failure> {
        let parent = self.get(id)?.parent;
        if parent.is_some_and(|parent| parent.0 >= id.0) { return Err(Failure::Invalid); }
        Ok(parent)
    }

    // Collect nearest lexical binder first. Parent values have already been
    // composed; shared substitution performs one simultaneous replacement and
    // shields nested Forall binders. Do not recursively resubstitute payloads.
    fn substitutions(&self, parent: Option<TypeEnvironmentId>, budget: &mut TypeWorkBudget)
        -> Result<(HashMap<TypeVariableId, &Type>, HashMap<TypeVariableId, EffectRow>), Failure>
    {
        let mut replacements = HashMap::new();
        let mut rows = HashMap::new();
        let mut seen = HashSet::new();
        let mut cursor = parent;
        while let Some(id) = cursor {
            charge(budget, 1)?;
            let environment = self.get(id)?;
            // One visit plus at most one seen entry and one replacement entry.
            charge(budget, environment.bindings.len().checked_mul(3).ok_or(Failure::Resource)?)?;
            for binding in &environment.bindings {
                let binder = binding.definition_binder;
                if seen.contains(&binder) { continue; }
                seen.try_reserve(1).map_err(|_| Failure::Resource)?;
                seen.insert(binder);
                match binding.argument() {
                    KindedArgument::TypeArg(ty) => {
                        replacements.try_reserve(1).map_err(|_| Failure::Resource)?;
                        replacements.insert(binder, ty);
                    }
                    KindedArgument::RowArg(row) => {
                        let row = types::clone_effect_row_with_budget(row, budget)
                            .map_err(|()| Failure::Resource)?;
                        rows.try_reserve(1).map_err(|_| Failure::Resource)?;
                        rows.insert(binder, row);
                    }
                }
            }
            cursor = self.parent_of(id)?;
        }
        Ok((replacements, rows))
    }

    // Build before capture materialization. No index lookup, slot acquisition,
    // local recipe execution, route-head publication, or owner-atom read here.
    // caller_context and invocation are ORIGINAL occurrence contexts; the
    // source qualifier must authenticate their Call/Invoke correspondence.
    pub(super) fn compose(
        &self, relation: &CheckedFactoryUse<'_>, caller_context: usize, invocation: usize,
        parent: Option<TypeEnvironmentId>, routes: &mut RouteArena,
        budget: &mut TypeWorkBudget,
    ) -> Result<Option<PendingTypeEnvironment>, Failure> {
        if self.frozen_contexts.is_some() { return Err(Failure::Invalid); }
        if let Some(parent) = parent { self.get(parent)?; }
        let (replacements, rows) = self.substitutions(parent, budget)?;
        let header = types::clone_kinded_type_parameters_fallibly_with_budget(
            relation.definition_header, budget,
        ).map_err(|()| Failure::Resource)?;
        charge(budget, relation.arguments.len())?;
        let mut bindings = Vec::new();
        bindings.try_reserve_exact(relation.arguments.len()).map_err(|_| Failure::Resource)?;
        for (((definition, _), (use_binder, _)), (formal, argument)) in relation.definition_header
            .iter().zip(relation.use_header).zip(relation.formals.iter().zip(relation.arguments))
        {
            let normalized = match types::substitute_kinded_argument_borrowed_with(
                argument.value.as_ref(), &replacements, &rows, |cells| budget.charge(cells),
            ).map_err(|()| Failure::Resource)? {
                Ok(value) => IterativeArgumentOwner::new(value),
                Err(_) => return Ok(None),
            };
            let Some(Expr::Merge(inputs)) = relation.graph.expressions.get(argument.port)
                else { return Err(Failure::Invalid); };
            let count = inputs.len().checked_add(1).ok_or(Failure::Resource)?;
            charge(budget, count)?;
            let mut sources = Vec::new();
            sources.try_reserve_exact(count).map_err(|_| Failure::Resource)?;
            // Original Merge contributes Free even when every metadata input
            // is absent/empty. This preserves its exact local readiness fact.
            sources.push(routes.free(budget)?);
            for input in inputs {
                let original = OriginalPort { expression: *input, context: caller_context };
                // Even an exact matching inherited formal may have several
                // original writers. Read its COMPLETE occurrence head; never
                // replace it with one Binding's argument-contribution route.
                sources.push(routes.head(original, budget)?);
            }
            let local_merge = routes.join(ProjectionClass::Metadata, &sources, budget)?;
            let actual = OriginalPort { expression: argument.port, context: caller_context };
            let route = routes.head(actual, budget)?;
            bindings.push(Binding {
                definition_binder: *definition, use_binder: *use_binder,
                formal: OriginalPort { expression: *formal, context: invocation },
                actual, route, local_merge, normalized,
            });
        }
        Ok(Some(PendingTypeEnvironment(FrameEnvironment {
            occurrence: Occurrence {
                application: OriginalPort { expression: relation.application, context: caller_context },
                factory: relation.factory, creation: relation.creation, invocation,
            },
            parent, header, bindings,
        })))
    }

    // Original reader replay reuses this exact occurrence and parent identity.
    // Full argument Types are not the key, and live route heads are not cached
    // value answers. The caller still needs original source/frame admission.
    pub(super) fn build(
        &mut self, relation: &CheckedFactoryUse<'_>, caller_context: usize, invocation: usize,
        parent: Option<TypeEnvironmentId>, routes: &mut RouteArena,
        budget: &mut TypeWorkBudget,
    ) -> Result<Option<TypeEnvironmentId>, Failure> {
        if self.frozen_contexts.is_some() { return Err(Failure::Invalid); }
        let occurrence = Occurrence {
            application: OriginalPort { expression: relation.application, context: caller_context },
            factory: relation.factory, creation: relation.creation, invocation,
        };
        charge(budget, 1)?;
        if let Some(id) = self.by_occurrence.get(&(occurrence, parent)) { return Ok(Some(*id)); }
        let Some(pending) = self.compose(relation, caller_context, invocation, parent, routes, budget)?
            else { return Ok(None); };
        self.append(pending, budget).map(Some)
    }

    // Allocation IDs are fresh per DISTINCT original occurrence/parent, even
    // for equal full terms. Exact replay can reuse the same ID. No Type-based
    // hash-consing, source admission, or dynamic activation merging occurs.
    pub(super) fn append(&mut self, pending: PendingTypeEnvironment, budget: &mut TypeWorkBudget)
        -> Result<TypeEnvironmentId, Failure>
    {
        if self.frozen_contexts.is_some() { return Err(Failure::Invalid); }
        if let Some(parent) = pending.0.parent { self.get(parent)?; }
        let key = (pending.0.occurrence, pending.0.parent);
        charge(budget, 2)?;
        if let Some(id) = self.by_occurrence.get(&key) { return Ok(*id); }
        self.by_occurrence.try_reserve(1).map_err(|_| Failure::Resource)?;
        self.environments.try_reserve(1).map_err(|_| Failure::Resource)?;
        let id = TypeEnvironmentId(self.environments.len());
        self.environments.push(pending.0);
        self.by_occurrence.insert(key, id);
        Ok(id)
    }

    // Bind ONLY after authenticating the original Invoke/creation-to-frame
    // association. An environment record alone is not that authentication.
    // Reserve all caller notification/revision storage before this mutation.
    pub(super) fn bind_context(&mut self, context: usize, environment: TypeEnvironmentId,
        budget: &mut TypeWorkBudget) -> Result<bool, Failure>
    {
        if self.frozen_contexts.is_some() { return Err(Failure::Invalid); }
        self.get(environment)?;
        charge(budget, 2)?;
        if let Some(existing) = self.contexts.get_mut(&context) {
            charge(budget, existing.len())?;
            if existing.contains(&environment) { return Ok(false); }
            existing.try_reserve(1).map_err(|_| Failure::Resource)?;
            existing.push(environment);
        } else {
            let mut alternatives = Vec::new();
            alternatives.try_reserve(1).map_err(|_| Failure::Resource)?;
            alternatives.push(environment);
            self.contexts.try_reserve(1).map_err(|_| Failure::Resource)?;
            self.contexts.insert(context, alternatives);
        }
        Ok(true)
    }

    pub(super) fn context_alternatives(&self, context: usize) -> &[TypeEnvironmentId] {
        self.contexts.get(&context).map(Vec::as_slice).unwrap_or(&[])
    }

    pub(super) fn unique_context(&self, context: usize) -> Option<TypeEnvironmentId> {
        match self.context_alternatives(context) { [id] => Some(*id), _ => None }
    }

    // Preserve IDs/parent links/RouteIds exactly; never relocate them with
    // graph, code or target offsets. Pair with the SAME frame arena's terminal
    // snapshot, whose route IDs are likewise preserved. No query acquisition.
    // A snapshot rejects compose/append/bind, so query use cannot grow it.
    pub(super) fn snapshot(&self, frozen_contexts: usize, budget: &mut TypeWorkBudget)
        -> Result<Self, Failure>
    {
        let frozen_contexts = self.frozen_contexts.map_or(frozen_contexts,
            |existing| existing.min(frozen_contexts));
        let mut result = Self::new();
        result.frozen_contexts = Some(frozen_contexts);
        charge(budget, self.environments.len())?;
        result.environments.try_reserve_exact(self.environments.len()).map_err(|_| Failure::Resource)?;
        charge(budget, self.by_occurrence.len())?;
        result.by_occurrence.try_reserve(self.by_occurrence.len()).map_err(|_| Failure::Resource)?;
        for environment in &self.environments {
            let header = types::clone_kinded_type_parameters_fallibly_with_budget(
                &environment.header, budget,
            ).map_err(|()| Failure::Resource)?;
            charge(budget, environment.bindings.len())?;
            let mut bindings = Vec::new();
            bindings.try_reserve_exact(environment.bindings.len()).map_err(|_| Failure::Resource)?;
            for binding in &environment.bindings {
                let normalized = IterativeArgumentOwner::new(
                    types::clone_kinded_argument_with_budget(binding.argument(), budget)
                        .map_err(|()| Failure::Resource)?,
                );
                bindings.push(Binding { definition_binder: binding.definition_binder,
                    use_binder: binding.use_binder, formal: binding.formal, actual: binding.actual,
                    route: binding.route, local_merge: binding.local_merge, normalized });
            }
            let id = TypeEnvironmentId(result.environments.len());
            result.by_occurrence.insert((environment.occurrence, environment.parent), id);
            result.environments.push(FrameEnvironment { occurrence: environment.occurrence,
                parent: environment.parent, header, bindings });
        }
        charge(budget, self.contexts.len())?;
        result.contexts.try_reserve(self.contexts.len()).map_err(|_| Failure::Resource)?;
        for (&context, alternatives) in &self.contexts {
            if context >= frozen_contexts { continue; }
            charge(budget, alternatives.len())?;
            let mut copied = Vec::new();
            copied.try_reserve_exact(alternatives.len()).map_err(|_| Failure::Resource)?;
            copied.extend_from_slice(alternatives);
            result.contexts.insert(context, copied);
        }
        Ok(result)
    }
}

// Selected evidence is NOT a typed binder substitution. Keep every original
// ordered Requirement/Method/source occurrence, including repeated keys.
// The consumer chooses generic K vs selected T; this helper never unifies them.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct DictionaryInput {
    pub(super) requirement: crate::interface::RequirementId,
    pub(super) method: crate::interface::MethodId,
    pub(super) ordinal: usize,
    pub(super) source: OriginalPort,
    pub(super) route: RouteId,
}

pub(super) fn evidence_inputs(graph: &Graph, evidence: usize, context: usize,
    routes: &mut RouteArena, budget: &mut TypeWorkBudget)
    -> Result<Option<Vec<DictionaryInput>>, Failure>
{
    let Some(Expr::Evidence { bindings, .. }) = graph.expressions.get(evidence) else { return Ok(None); };
    charge(budget, bindings.len())?;
    let mut result = Vec::new();
    result.try_reserve_exact(bindings.len()).map_err(|_| Failure::Resource)?;
    for (ordinal, &(requirement, method, expression)) in bindings.iter().enumerate() {
        if graph.expressions.get(expression).is_none() { return Err(Failure::Invalid); }
        let source = OriginalPort { expression, context };
        result.push(DictionaryInput { requirement, method, ordinal, source,
            route: routes.head(source, budget)? });
    }
    Ok(Some(result))
}
