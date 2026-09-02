//! Shared typed-pattern usefulness and witness construction.

use std::{
    collections::{HashMap, HashSet},
    rc::Rc,
};

use crate::{
    core::{CorePattern, CorePatternKind},
    resolved::ResolvedRegistry,
    types::{ConstructorId, Type, discard_type_iteratively, substitute_type_variables_with},
};

/// A binder-free pattern shape used for coverage witnesses.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum WitnessPattern {
    /// Any value of an open or atomic domain.
    Wildcard,
    /// A Boolean value.
    Boolean(bool),
    /// Unit.
    Unit,
    /// A tuple shape.
    Tuple(Box<[WitnessPattern]>),
    /// A nominal constructor shape.
    Constructor(ConstructorId, Option<Box<WitnessPattern>>),
}

impl WitnessPattern {
    fn is_wildcard(&self) -> bool {
        matches!(self, Self::Wildcard)
    }
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum Head {
    Boolean(bool),
    Unit,
    Tuple(usize),
    Constructor(ConstructorId),
}

#[derive(Clone, Eq, Hash, PartialEq)]
struct State(Vec<Vec<WitnessPattern>>, Vec<WitnessPattern>, Vec<Type>);

impl Drop for State {
    fn drop(&mut self) {
        for ty in self.2.drain(..) {
            discard_type_iteratively(ty);
        }
    }
}

struct TypeReplacementMap(HashMap<crate::types::TypeVariableId, Type>);

impl TypeReplacementMap {
    fn new() -> Self {
        Self(HashMap::new())
    }

    fn try_reserve(&mut self, additional: usize) -> Result<(), std::collections::TryReserveError> {
        self.0.try_reserve(additional)
    }

    fn insert_replacing(&mut self, parameter: crate::types::TypeVariableId, ty: Type) {
        if let Some(displaced) = self.0.insert(parameter, ty) {
            discard_type_iteratively(displaced);
        }
    }

    fn as_map(&self) -> &HashMap<crate::types::TypeVariableId, Type> {
        &self.0
    }
}

impl Drop for TypeReplacementMap {
    fn drop(&mut self) {
        for (_, ty) in self.0.drain() {
            discard_type_iteratively(ty);
        }
    }
}

struct OwnedTypeBuffer(Vec<Type>);

impl OwnedTypeBuffer {
    fn len(&self) -> usize {
        self.0.len()
    }

    fn append_cloned(
        &mut self,
        types: &[Type],
        budget: &mut UsefulnessBudget,
    ) -> Result<(), UsefulnessError> {
        charge_types(types, budget)?;
        self.0.reserve(types.len());
        self.0.extend_from_slice(types);
        Ok(())
    }

    fn into_vec(mut self) -> Vec<Type> {
        std::mem::take(&mut self.0)
    }
}

impl Drop for OwnedTypeBuffer {
    fn drop(&mut self) {
        for ty in self.0.drain(..) {
            discard_type_iteratively(ty);
        }
    }
}

/// Maximum number of distinct usefulness states explored by one query.
pub const USEFULNESS_STATE_LIMIT: usize = 100_000;
/// Maximum cumulative matrix and specialization work for one elaboration pass.
pub const USEFULNESS_WORK_LIMIT: usize = 1_000_000;

/// A compiler resource boundary reached while analyzing pattern coverage.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum UsefulnessError {
    /// The usefulness state budget was exhausted.
    StateLimit,
    /// The cumulative case-group work budget was exhausted.
    WorkLimit,
}

/// Shared deterministic work budget for all usefulness queries in one pass.
#[derive(Clone, Debug)]
pub struct UsefulnessBudget {
    remaining: usize,
}

impl Default for UsefulnessBudget {
    fn default() -> Self {
        Self {
            remaining: USEFULNESS_WORK_LIMIT,
        }
    }
}

impl UsefulnessBudget {
    #[cfg(test)]
    pub(crate) const fn with_limit(limit: usize) -> Self {
        Self { remaining: limit }
    }

    fn charge(&mut self, amount: usize) -> Result<(), UsefulnessError> {
        self.remaining = self
            .remaining
            .checked_sub(amount)
            .ok_or(UsefulnessError::WorkLimit)?;
        Ok(())
    }
}

#[derive(Clone)]
struct Choice {
    child: Rc<State>,
    rebuild: Rebuild,
}

#[derive(Clone, Copy)]
enum Rebuild {
    Head { head: Head, argument_count: usize },
    Wildcard,
}

enum Frame {
    Call(Rc<State>),
    TryChoices {
        state: Rc<State>,
        choices: Vec<Choice>,
        next: usize,
    },
}

/// Returns a concrete witness when `candidate` is useful against `matrix`.
pub fn usefulness(
    matrix: &[Vec<CorePattern>],
    candidate: &[CorePattern],
    types: &[Type],
    registry: &ResolvedRegistry,
) -> Result<Option<Vec<WitnessPattern>>, UsefulnessError> {
    let mut budget = UsefulnessBudget::default();
    usefulness_with_budget(matrix, candidate, types, registry, &mut budget)
}

/// Returns usefulness while sharing a work budget across one case group.
pub fn usefulness_with_budget(
    matrix: &[Vec<CorePattern>],
    candidate: &[CorePattern],
    types: &[Type],
    registry: &ResolvedRegistry,
    budget: &mut UsefulnessBudget,
) -> Result<Option<Vec<WitnessPattern>>, UsefulnessError> {
    budget.charge(matrix.len().saturating_add(candidate.len()))?;
    let matrix = shape_matrix(matrix, budget)?;
    let candidate = shape_row(candidate, budget)?;
    usefulness_shapes(
        &matrix,
        &candidate,
        types,
        registry,
        USEFULNESS_STATE_LIMIT,
        budget,
    )
}

/// Low-level witness query that does not require synthesizing source origins.
pub fn missing_witness_for_types(
    matrix: &[Vec<CorePattern>],
    types: &[Type],
    registry: &ResolvedRegistry,
) -> Result<Option<Vec<WitnessPattern>>, UsefulnessError> {
    let mut budget = UsefulnessBudget::default();
    missing_witness_for_types_with_budget(matrix, types, registry, &mut budget)
}

/// Queries a missing witness while sharing a case-group work budget.
pub fn missing_witness_for_types_with_budget(
    matrix: &[Vec<CorePattern>],
    types: &[Type],
    registry: &ResolvedRegistry,
    budget: &mut UsefulnessBudget,
) -> Result<Option<Vec<WitnessPattern>>, UsefulnessError> {
    budget.charge(matrix.len().saturating_add(types.len()))?;
    let matrix = shape_matrix(matrix, budget)?;
    let candidate = vec![WitnessPattern::Wildcard; types.len()];
    usefulness_shapes(
        &matrix,
        &candidate,
        types,
        registry,
        USEFULNESS_STATE_LIMIT,
        budget,
    )
}

fn shape_matrix(
    matrix: &[Vec<CorePattern>],
    budget: &mut UsefulnessBudget,
) -> Result<Vec<Vec<WitnessPattern>>, UsefulnessError> {
    matrix.iter().map(|row| shape_row(row, budget)).collect()
}

fn shape_row(
    row: &[CorePattern],
    budget: &mut UsefulnessBudget,
) -> Result<Vec<WitnessPattern>, UsefulnessError> {
    row.iter().map(|pattern| shape(pattern, budget)).collect()
}

fn shape(
    pattern: &CorePattern,
    budget: &mut UsefulnessBudget,
) -> Result<WitnessPattern, UsefulnessError> {
    enum Task<'a> {
        Visit(&'a CorePattern),
        FinishTuple(usize),
        FinishConstructor(ConstructorId, bool),
    }

    let mut work = vec![Task::Visit(pattern)];
    let mut rebuilt = Vec::new();
    while let Some(task) = work.pop() {
        match task {
            Task::Visit(pattern) => {
                budget.charge(1)?;
                match &pattern.kind {
                    CorePatternKind::Binder(_) | CorePatternKind::Wildcard => {
                        rebuilt.push(WitnessPattern::Wildcard);
                    }
                    CorePatternKind::Boolean(value) => {
                        rebuilt.push(WitnessPattern::Boolean(*value));
                    }
                    CorePatternKind::Unit => rebuilt.push(WitnessPattern::Unit),
                    CorePatternKind::Tuple(elements) => {
                        work.push(Task::FinishTuple(elements.len()));
                        work.extend(elements.iter().rev().map(Task::Visit));
                    }
                    CorePatternKind::Constructor {
                        constructor,
                        payload,
                    } => {
                        work.push(Task::FinishConstructor(*constructor, payload.is_some()));
                        if let Some(payload) = payload.as_deref() {
                            work.push(Task::Visit(payload));
                        }
                    }
                }
            }
            Task::FinishTuple(count) => {
                let elements = rebuilt.split_off(rebuilt.len().saturating_sub(count));
                rebuilt.push(WitnessPattern::Tuple(elements.into_boxed_slice()));
            }
            Task::FinishConstructor(constructor, has_payload) => {
                let payload = has_payload.then(|| rebuilt.pop().map(Box::new)).flatten();
                rebuilt.push(WitnessPattern::Constructor(constructor, payload));
            }
        }
    }
    Ok(rebuilt.pop().unwrap_or(WitnessPattern::Wildcard))
}

fn usefulness_shapes(
    matrix: &[Vec<WitnessPattern>],
    candidate: &[WitnessPattern],
    types: &[Type],
    registry: &ResolvedRegistry,
    state_limit: usize,
    budget: &mut UsefulnessBudget,
) -> Result<Option<Vec<WitnessPattern>>, UsefulnessError> {
    charge_state_materialization(matrix, candidate, types, budget)?;
    let root = Rc::new(State(matrix.to_vec(), candidate.to_vec(), types.to_vec()));
    let mut memo = HashMap::<Rc<State>, Option<Vec<WitnessPattern>>>::new();
    let mut active = HashSet::new();
    let mut frames = vec![Frame::Call(root)];
    let mut returned = None::<Option<Vec<WitnessPattern>>>;
    let mut explored = 0_usize;

    while let Some(frame) = frames.pop() {
        match frame {
            Frame::Call(state) => {
                if let Some(cached) = memo.get(&state) {
                    charge_optional_witness(cached, budget)?;
                    returned = Some(cached.clone());
                    continue;
                }
                if active.contains(&state) {
                    returned = Some(None);
                    continue;
                }
                explored = explored.checked_add(1).ok_or(UsefulnessError::StateLimit)?;
                budget.charge(1)?;
                if explored > state_limit {
                    return Err(UsefulnessError::StateLimit);
                }
                match immediate_result(&state, budget)? {
                    Some(result) => {
                        charge_optional_witness(&result, budget)?;
                        memo.insert(state, result.clone());
                        returned = Some(result);
                    }
                    None => {
                        let choices = choices(&state, registry, state_limit, budget)?;
                        active.insert(Rc::clone(&state));
                        frames.push(Frame::TryChoices {
                            state,
                            choices,
                            next: 0,
                        });
                    }
                }
            }
            Frame::TryChoices {
                state,
                choices,
                mut next,
            } => {
                if let Some(child_result) = returned.take() {
                    if let Some(choice) = choices.get(next.saturating_sub(1)) {
                        if let Some(witness) = child_result {
                            let result = Some(rebuild_witness(witness, choice.rebuild, budget)?);
                            active.remove(&state);
                            charge_optional_witness(&result, budget)?;
                            memo.insert(state, result.clone());
                            returned = Some(result);
                            continue;
                        }
                    } else {
                        active.remove(&state);
                        memo.insert(state, None);
                        returned = Some(None);
                        continue;
                    }
                }
                let Some(choice) = choices.get(next).cloned() else {
                    active.remove(&state);
                    memo.insert(state, None);
                    returned = Some(None);
                    continue;
                };
                next += 1;
                frames.push(Frame::TryChoices {
                    state,
                    choices,
                    next,
                });
                frames.push(Frame::Call(choice.child));
            }
        }
    }

    Ok(returned.flatten())
}

fn immediate_result(
    state: &State,
    budget: &mut UsefulnessBudget,
) -> Result<Option<Option<Vec<WitnessPattern>>>, UsefulnessError> {
    let State(matrix, candidate, types) = state;
    if candidate.is_empty() {
        return Ok(Some(matrix.is_empty().then(Vec::new)));
    }
    if matrix.is_empty() {
        charge_witnesses(candidate, budget)?;
        return Ok(Some(Some(candidate.clone())));
    }
    if types.len() != candidate.len() || matrix.iter().any(|row| row.len() != candidate.len()) {
        return Ok(Some(None));
    }
    Ok(matrix
        .iter()
        .any(|row| row.iter().all(WitnessPattern::is_wildcard))
        .then_some(None))
}

fn choices(
    state: &State,
    registry: &ResolvedRegistry,
    state_limit: usize,
    budget: &mut UsefulnessBudget,
) -> Result<Vec<Choice>, UsefulnessError> {
    let State(matrix, candidate, types) = state;
    let first_type = &types[0];
    if candidate[0].is_wildcard() {
        if let Some(heads) = heads_for_type(first_type, registry) {
            if heads.len() > state_limit {
                return Err(UsefulnessError::StateLimit);
            }
            budget.charge(heads.len().saturating_mul(matrix.len().max(1)))?;
            let mut result = Vec::with_capacity(heads.len());
            for index in 0..heads.len() {
                result.push(specialized_choice(
                    state,
                    heads.at(index),
                    true,
                    registry,
                    budget,
                )?);
            }
            return Ok(result);
        }
        let default = default_matrix(matrix, budget)?;
        let specialized_candidate = clone_witnesses(&candidate[1..], budget)?;
        let specialized_types = clone_types(&types[1..], budget)?;
        return Ok(vec![Choice {
            child: Rc::new(State(default, specialized_candidate, specialized_types)),
            rebuild: Rebuild::Wildcard,
        }]);
    }

    let Some(head) = pattern_head(&candidate[0]) else {
        return Ok(Vec::new());
    };
    budget.charge(matrix.len().max(1))?;
    Ok(vec![specialized_choice(
        state, head, false, registry, budget,
    )?])
}

fn specialized_choice(
    state: &State,
    head: Head,
    wildcard_candidate: bool,
    registry: &ResolvedRegistry,
    budget: &mut UsefulnessBudget,
) -> Result<Choice, UsefulnessError> {
    let State(matrix, candidate, types) = state;
    let argument_types = OwnedTypeBuffer(head_types(head, &types[0], registry, budget)?);
    let argument_count = argument_types.len();
    let specialized_matrix = specialize_matrix(matrix, head, argument_count, budget)?;
    let mut specialized_candidate = if wildcard_candidate {
        budget.charge(argument_count)?;
        vec![WitnessPattern::Wildcard; argument_count]
    } else {
        pattern_arguments(&candidate[0], budget)?
    };
    append_witnesses(&mut specialized_candidate, &candidate[1..], budget)?;
    let mut specialized_types = argument_types;
    specialized_types.append_cloned(&types[1..], budget)?;
    Ok(Choice {
        child: Rc::new(State(
            specialized_matrix,
            specialized_candidate,
            specialized_types.into_vec(),
        )),
        rebuild: Rebuild::Head {
            head,
            argument_count,
        },
    })
}

fn default_matrix(
    matrix: &[Vec<WitnessPattern>],
    budget: &mut UsefulnessBudget,
) -> Result<Vec<Vec<WitnessPattern>>, UsefulnessError> {
    let mut default = Vec::with_capacity(matrix.len());
    for row in matrix.iter().filter(|row| row[0].is_wildcard()) {
        default.push(clone_witnesses(&row[1..], budget)?);
    }
    Ok(default)
}

fn charge_state_materialization(
    matrix: &[Vec<WitnessPattern>],
    candidate: &[WitnessPattern],
    types: &[Type],
    budget: &mut UsefulnessBudget,
) -> Result<(), UsefulnessError> {
    for row in matrix {
        charge_witnesses(row, budget)?;
    }
    charge_witnesses(candidate, budget)?;
    charge_types(types, budget)
}

fn charge_optional_witness(
    witness: &Option<Vec<WitnessPattern>>,
    budget: &mut UsefulnessBudget,
) -> Result<(), UsefulnessError> {
    if let Some(witness) = witness {
        charge_witnesses(witness, budget)?;
    }
    Ok(())
}

fn clone_witnesses(
    patterns: &[WitnessPattern],
    budget: &mut UsefulnessBudget,
) -> Result<Vec<WitnessPattern>, UsefulnessError> {
    charge_witnesses(patterns, budget)?;
    Ok(patterns.to_vec())
}

fn append_witnesses(
    target: &mut Vec<WitnessPattern>,
    patterns: &[WitnessPattern],
    budget: &mut UsefulnessBudget,
) -> Result<(), UsefulnessError> {
    charge_witnesses(patterns, budget)?;
    target.reserve(patterns.len());
    target.extend_from_slice(patterns);
    Ok(())
}

fn charge_witnesses(
    patterns: &[WitnessPattern],
    budget: &mut UsefulnessBudget,
) -> Result<(), UsefulnessError> {
    enum Task<'a> {
        Pattern(&'a WitnessPattern),
        Slice(std::slice::Iter<'a, WitnessPattern>),
    }

    let mut work = vec![Task::Slice(patterns.iter())];
    while let Some(task) = work.pop() {
        match task {
            Task::Slice(mut remaining) => {
                if let Some(pattern) = remaining.next() {
                    work.push(Task::Slice(remaining));
                    work.push(Task::Pattern(pattern));
                }
            }
            Task::Pattern(pattern) => {
                budget.charge(1)?;
                match pattern {
                    WitnessPattern::Tuple(elements) => {
                        work.push(Task::Slice(elements.iter()));
                    }
                    WitnessPattern::Constructor(_, Some(payload)) => {
                        work.push(Task::Pattern(payload));
                    }
                    WitnessPattern::Wildcard
                    | WitnessPattern::Boolean(_)
                    | WitnessPattern::Unit
                    | WitnessPattern::Constructor(_, None) => {}
                }
            }
        }
    }
    Ok(())
}

fn clone_types(
    types: &[Type],
    budget: &mut UsefulnessBudget,
) -> Result<Vec<Type>, UsefulnessError> {
    charge_types(types, budget)?;
    Ok(types.to_vec())
}

fn charge_types(types: &[Type], budget: &mut UsefulnessBudget) -> Result<(), UsefulnessError> {
    enum Task<'a> {
        Type(&'a Type),
        Slice(std::slice::Iter<'a, Type>),
    }

    let mut work = vec![Task::Slice(types.iter())];
    while let Some(task) = work.pop() {
        match task {
            Task::Slice(mut remaining) => {
                if let Some(ty) = remaining.next() {
                    work.push(Task::Slice(remaining));
                    work.push(Task::Type(ty));
                }
            }
            Task::Type(ty) => {
                budget.charge(1)?;
                match ty {
                    Type::Tuple(elements) => work.push(Task::Slice(elements.iter())),
                    Type::Function(domain, codomain) => {
                        work.push(Task::Type(codomain));
                        work.push(Task::Type(domain));
                    }
                    Type::EffectfulFunction(domain, codomain) => {
                        for argument in codomain.effect_arguments() {
                            work.push(Task::Type(argument));
                        }
                        work.push(Task::Type(&codomain.value));
                        work.push(Task::Type(domain));
                    }
                    Type::Application(function, argument) => {
                        work.push(Task::Type(argument));
                        work.push(Task::Type(function));
                    }
                    Type::Int
                    | Type::Bool
                    | Type::Unit
                    | Type::Nominal(_)
                    | Type::Variable(_)
                    | Type::Inference(_)
                    | Type::Forall(_, _) => {}
                }
            }
        }
    }
    Ok(())
}

fn rebuild_witness(
    mut witness: Vec<WitnessPattern>,
    rebuild: Rebuild,
    budget: &mut UsefulnessBudget,
) -> Result<Vec<WitnessPattern>, UsefulnessError> {
    budget.charge(witness.len().saturating_add(1))?;
    Ok(match rebuild {
        Rebuild::Head {
            head,
            argument_count,
        } => {
            let arguments = witness.drain(..argument_count).collect();
            let mut rebuilt = vec![pattern_from_head(head, arguments)];
            rebuilt.extend(witness);
            rebuilt
        }
        Rebuild::Wildcard => {
            let mut rebuilt = vec![WitnessPattern::Wildcard];
            rebuilt.append(&mut witness);
            rebuilt
        }
    })
}

enum Heads<'a> {
    Boolean,
    Unit,
    Tuple(usize),
    Constructors(&'a [ConstructorId]),
}

impl Heads<'_> {
    fn len(&self) -> usize {
        match self {
            Self::Boolean => 2,
            Self::Unit | Self::Tuple(_) => 1,
            Self::Constructors(constructors) => constructors.len(),
        }
    }

    fn at(&self, index: usize) -> Head {
        match self {
            Self::Boolean => Head::Boolean(index == 0),
            Self::Unit => Head::Unit,
            Self::Tuple(count) => Head::Tuple(*count),
            Self::Constructors(constructors) => Head::Constructor(constructors[index]),
        }
    }
}

fn heads_for_type<'a>(ty: &Type, registry: &'a ResolvedRegistry) -> Option<Heads<'a>> {
    match ty {
        Type::Bool => Some(Heads::Boolean),
        Type::Unit => Some(Heads::Unit),
        Type::Tuple(elements) => Some(Heads::Tuple(elements.len())),
        Type::Nominal(id) => Some(Heads::Constructors(&registry.nominal(*id)?.constructors)),
        Type::Application(_, _) => Some(Heads::Constructors(
            &registry.nominal(ty.outer_nominal()?)?.constructors,
        )),
        Type::Int
        | Type::Function(_, _)
        | Type::EffectfulFunction(_, _)
        | Type::Variable(_)
        | Type::Inference(_)
        | Type::Forall(_, _) => None,
    }
}

fn head_types(
    head: Head,
    ty: &Type,
    registry: &ResolvedRegistry,
    budget: &mut UsefulnessBudget,
) -> Result<Vec<Type>, UsefulnessError> {
    match head {
        Head::Boolean(_) | Head::Unit => Ok(Vec::new()),
        Head::Tuple(count) => match ty {
            Type::Tuple(elements) if elements.len() == count => clone_types(elements, budget),
            _ => Ok(Vec::new()),
        },
        Head::Constructor(id) => {
            let Some(constructor) = registry.constructor(id) else {
                return Ok(Vec::new());
            };
            let Some(owner) = registry.nominal(constructor.owner) else {
                return Ok(Vec::new());
            };
            let payload = if owner.declaration_kind
                == crate::resolved::ResolvedNominalDeclarationKind::Newtype
            {
                owner.representation.as_ref()
            } else {
                constructor.payload.as_ref()
            };
            let Some(payload) = payload else {
                return Ok(Vec::new());
            };
            let instantiated = match ty {
                Type::Application(_, _) if ty.outer_nominal() == Some(constructor.owner) => {
                    let Some(parameters) = registry.nominal_parameters(constructor.owner) else {
                        return Ok(Vec::new());
                    };
                    let mut current = ty;
                    let mut argument_count = 0usize;
                    while let Type::Application(function, argument) = current {
                        budget.charge(1)?;
                        let _ = argument;
                        argument_count = argument_count
                            .checked_add(1)
                            .ok_or(UsefulnessError::WorkLimit)?;
                        current = function;
                    }
                    if parameters.len() != argument_count {
                        return Ok(Vec::new());
                    }
                    budget.charge(parameters.len())?;
                    let mut replacements = TypeReplacementMap::new();
                    replacements
                        .try_reserve(parameters.len())
                        .map_err(|_| UsefulnessError::WorkLimit)?;
                    current = ty;
                    for parameter in parameters.iter().rev() {
                        let Type::Application(function, argument) = current else {
                            return Ok(Vec::new());
                        };
                        charge_types(std::slice::from_ref(argument), budget)?;
                        replacements.insert_replacing(parameter.id, argument.as_ref().clone());
                        current = function;
                    }
                    substitute_type_variables_with(
                        payload,
                        replacements.as_map(),
                        |cells| budget.charge(cells),
                        || UsefulnessError::WorkLimit,
                    )?
                }
                Type::Nominal(owner) if *owner == constructor.owner => {
                    charge_types(std::slice::from_ref(payload), budget)?;
                    payload.clone()
                }
                _ => return Ok(Vec::new()),
            };
            Ok(vec![instantiated])
        }
    }
}

fn pattern_head(pattern: &WitnessPattern) -> Option<Head> {
    match pattern {
        WitnessPattern::Boolean(value) => Some(Head::Boolean(*value)),
        WitnessPattern::Unit => Some(Head::Unit),
        WitnessPattern::Tuple(elements) => Some(Head::Tuple(elements.len())),
        WitnessPattern::Constructor(id, _) => Some(Head::Constructor(*id)),
        WitnessPattern::Wildcard => None,
    }
}

fn pattern_arguments(
    pattern: &WitnessPattern,
    budget: &mut UsefulnessBudget,
) -> Result<Vec<WitnessPattern>, UsefulnessError> {
    match pattern {
        WitnessPattern::Tuple(elements) => clone_witnesses(elements, budget),
        WitnessPattern::Constructor(_, Some(payload)) => {
            clone_witnesses(std::slice::from_ref(payload.as_ref()), budget)
        }
        _ => Ok(Vec::new()),
    }
}

fn specialize_matrix(
    matrix: &[Vec<WitnessPattern>],
    head: Head,
    argument_count: usize,
    budget: &mut UsefulnessBudget,
) -> Result<Vec<Vec<WitnessPattern>>, UsefulnessError> {
    let mut specialized = Vec::with_capacity(matrix.len());
    for row in matrix {
        let mut result = if row[0].is_wildcard() {
            budget.charge(argument_count)?;
            vec![WitnessPattern::Wildcard; argument_count]
        } else if pattern_head(&row[0]) == Some(head) {
            pattern_arguments(&row[0], budget)?
        } else {
            continue;
        };
        append_witnesses(&mut result, &row[1..], budget)?;
        specialized.push(result);
    }
    Ok(specialized)
}

fn pattern_from_head(head: Head, mut arguments: Vec<WitnessPattern>) -> WitnessPattern {
    match head {
        Head::Boolean(value) => WitnessPattern::Boolean(value),
        Head::Unit => WitnessPattern::Unit,
        Head::Tuple(_) => WitnessPattern::Tuple(arguments.into_boxed_slice()),
        Head::Constructor(id) => WitnessPattern::Constructor(
            id,
            (!arguments.is_empty()).then(|| Box::new(arguments.remove(0))),
        ),
    }
}

/// Renders a concrete witness using registry spellings.
#[must_use]
pub fn display_witness(witness: &[WitnessPattern], registry: &ResolvedRegistry) -> String {
    witness
        .iter()
        .map(|pattern| display_pattern(pattern, registry))
        .collect::<Vec<_>>()
        .join(" ")
}

fn display_pattern(pattern: &WitnessPattern, registry: &ResolvedRegistry) -> String {
    match pattern {
        WitnessPattern::Wildcard => "_".into(),
        WitnessPattern::Boolean(value) => value.to_string(),
        WitnessPattern::Unit => "()".into(),
        WitnessPattern::Tuple(elements) => format!(
            "({})",
            elements
                .iter()
                .map(|element| display_pattern(element, registry))
                .collect::<Vec<_>>()
                .join(", ")
        ),
        WitnessPattern::Constructor(id, payload) => {
            let name = registry
                .constructor(*id)
                .map_or("<foreign-constructor>", |constructor| {
                    constructor.spelling.as_str()
                });
            payload.as_ref().map_or_else(
                || name.to_owned(),
                |payload| format!("{name}({})", display_pattern(payload, registry)),
            )
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::resolved::{ResolvedConstructor, ResolvedNominalType, ResolvedTypeVariable};
    use crate::source::{ByteRange, Origin, SourceFile};
    use crate::types::{NominalTypeId, TypeVariableId};

    fn constructor_registry(
        parameter_count: usize,
        payload: Type,
    ) -> (ResolvedRegistry, ConstructorId, NominalTypeId) {
        let source = SourceFile::new("coverage-budget.ash", "Wide").expect("test source");
        let span = source
            .span(ByteRange::new(0, 4).expect("ordered range"))
            .expect("test span");
        let origin = Origin::Source(span);
        let owner = NominalTypeId::new(source.id(), 0);
        let constructor = ConstructorId::new(owner, 0);
        let parameters = (0..parameter_count)
            .map(|index| ResolvedTypeVariable {
                id: TypeVariableId::new(u32::try_from(index).expect("parameter identity")),
                spelling: format!("T{index}"),
                kind: crate::types::Kind::Type,
                origin: origin.clone(),
            })
            .collect();
        let registry = ResolvedRegistry::new(
            vec![ResolvedNominalType {
                representation_provenance: None,
                declaration_kind: crate::resolved::ResolvedNominalDeclarationKind::Data,
                representation: None,
                id: owner,
                spelling: "Wide".to_owned(),
                constructors: vec![constructor].into_boxed_slice(),
                origin: origin.clone(),
            }],
            vec![ResolvedConstructor {
                id: constructor,
                owner,
                spelling: "Make".to_owned(),
                payload: Some(payload),
                origin,
            }],
        )
        .with_type_parameters(vec![(owner, parameters)]);
        (registry, constructor, owner)
    }

    fn wildcard(ty: Type, origin: &Origin) -> CorePattern {
        CorePattern::new(ty, origin.clone(), CorePatternKind::Wildcard)
    }

    #[test]
    fn usefulness_reports_state_budget_exhaustion() {
        let registry = ResolvedRegistry::new(Vec::new(), Vec::new());
        assert_eq!(
            usefulness_shapes(
                &[],
                &[WitnessPattern::Wildcard],
                &[Type::Int],
                &registry,
                0,
                &mut UsefulnessBudget::default(),
            ),
            Err(UsefulnessError::StateLimit)
        );
    }

    #[test]
    fn usefulness_reports_shared_work_budget_exhaustion() {
        let registry = ResolvedRegistry::new(Vec::new(), Vec::new());
        let mut budget = UsefulnessBudget { remaining: 0 };
        assert_eq!(
            usefulness_shapes(
                &[],
                &[WitnessPattern::Wildcard],
                &[Type::Int],
                &registry,
                USEFULNESS_STATE_LIMIT,
                &mut budget,
            ),
            Err(UsefulnessError::WorkLimit)
        );
    }

    #[test]
    fn usefulness_charges_every_pattern_cell_while_shaping() {
        let source = SourceFile::new("wide-pattern.ash", "_").expect("test source");
        let span = source
            .span(ByteRange::new(0, 1).expect("ordered range"))
            .expect("test span");
        let origin = Origin::Source(span);
        let element_types = vec![Type::Int; 8].into_boxed_slice();
        let tuple_type = Type::Tuple(element_types.clone());
        let tuple = CorePattern::new(
            tuple_type.clone(),
            origin.clone(),
            CorePatternKind::Tuple(
                element_types
                    .iter()
                    .cloned()
                    .map(|ty| wildcard(ty, &origin))
                    .collect::<Vec<_>>()
                    .into_boxed_slice(),
            ),
        );
        let registry = ResolvedRegistry::new(Vec::new(), Vec::new());
        let mut budget = UsefulnessBudget { remaining: 6 };

        assert_eq!(
            usefulness_with_budget(&[], &[tuple], &[tuple_type], &registry, &mut budget),
            Err(UsefulnessError::WorkLimit)
        );
    }

    #[test]
    fn usefulness_charges_tuple_type_cells_before_materializing_the_root_state() {
        let tuple_type = Type::Tuple(vec![Type::Int; 8].into_boxed_slice());
        let registry = ResolvedRegistry::new(Vec::new(), Vec::new());
        let mut budget = UsefulnessBudget { remaining: 8 };

        assert_eq!(
            usefulness_shapes(
                &[],
                &[WitnessPattern::Wildcard],
                &[tuple_type],
                &registry,
                USEFULNESS_STATE_LIMIT,
                &mut budget,
            ),
            Err(UsefulnessError::WorkLimit)
        );
    }

    #[test]
    fn constructor_head_types_charge_phantom_replacement_storage_at_the_exact_boundary() {
        const WIDTH: usize = 4_096;

        let (registry, constructor, owner) = constructor_registry(WIDTH, Type::Int);
        let applied = Type::apply_arguments(Type::Nominal(owner), vec![Type::Bool; WIDTH]);
        // W application-spine visits + W replacement records + W retained
        // argument leaves + one substituted payload cell.
        let required = WIDTH * 3 + 1;
        let mut exact = UsefulnessBudget {
            remaining: required,
        };

        assert_eq!(
            head_types(
                Head::Constructor(constructor),
                &applied,
                &registry,
                &mut exact,
            ),
            Ok(vec![Type::Int])
        );
        assert_eq!(exact.remaining, 0);

        let mut short = UsefulnessBudget {
            remaining: required - 1,
        };
        assert_eq!(
            head_types(
                Head::Constructor(constructor),
                &applied,
                &registry,
                &mut short,
            ),
            Err(UsefulnessError::WorkLimit)
        );
    }

    #[test]
    fn constructor_head_types_charge_wide_monomorphic_payloads_at_the_exact_boundary() {
        const WIDTH: usize = 4_096;

        let payload = Type::Tuple(vec![Type::Int; WIDTH].into_boxed_slice());
        let (registry, constructor, owner) = constructor_registry(0, payload.clone());
        let required = WIDTH + 1;
        let mut exact = UsefulnessBudget {
            remaining: required,
        };

        assert_eq!(
            head_types(
                Head::Constructor(constructor),
                &Type::Nominal(owner),
                &registry,
                &mut exact,
            ),
            Ok(vec![payload])
        );
        assert_eq!(exact.remaining, 0);

        let mut short = UsefulnessBudget {
            remaining: required - 1,
        };
        assert_eq!(
            head_types(
                Head::Constructor(constructor),
                &Type::Nominal(owner),
                &registry,
                &mut short,
            ),
            Err(UsefulnessError::WorkLimit)
        );
    }

    #[test]
    fn late_specialization_failure_discards_deep_constructor_argument_types_on_a_small_stack() {
        const DEPTH: usize = 32_768;
        const DEEP_CELLS: usize = DEPTH * 2 + 1;

        std::thread::Builder::new()
            .name("late-specialization-type-disposal".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let mut payload = Type::Unit;
                for _ in 0..DEPTH {
                    payload = Type::Application(Box::new(payload), Box::new(Type::Unit));
                }
                let (registry, constructor, owner) = constructor_registry(0, payload);
                let state = State(
                    Vec::new(),
                    vec![WitnessPattern::Wildcard, WitnessPattern::Wildcard],
                    vec![Type::Nominal(owner), Type::Int],
                );
                let mut one_short = UsefulnessBudget {
                    remaining: DEEP_CELLS + 2,
                };

                assert!(matches!(
                    specialized_choice(
                        &state,
                        Head::Constructor(constructor),
                        true,
                        &registry,
                        &mut one_short,
                    ),
                    Err(UsefulnessError::WorkLimit)
                ));
            })
            .expect("the late-specialization thread should start")
            .join()
            .expect("late specialization failure must dismantle argument types iteratively");
    }
}
#[cfg(test)]
mod replacement_owner_api_tests {
    use super::*;

    fn deep_type(depth: usize) -> Type {
        let mut ty = Type::Int;
        for _ in 0..depth {
            ty = Type::Application(Box::new(ty), Box::new(Type::Unit));
        }
        ty
    }

    #[test]
    fn recursive_type_replacements_do_not_bypass_the_owner_api() {
        let source: String = include_str!("pattern.rs")
            .chars()
            .filter(|character| !character.is_whitespace())
            .collect();
        let raw_field = ["replacements", ".0"].concat();
        assert!(!source.contains(&raw_field));
        let raw_insert = [".0", ".insert("].concat();
        let raw_reserve = [".0", ".try_reserve("].concat();
        assert_eq!(source.matches(&raw_insert).count(), 1);
        assert_eq!(source.matches(&raw_reserve).count(), 1);
        let broad_mutation = ["impl", "DerefMut", "for", "TypeReplacementMap"].concat();
        assert!(!source.contains(&broad_mutation));
    }

    #[test]
    fn duplicate_deep_replacement_is_dismantled_on_a_small_stack() {
        const DEPTH: usize = 32_768;

        std::thread::Builder::new()
            .name("duplicate-pattern-replacement".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let parameter = crate::types::TypeVariableId::new(0);
                let mut replacements = TypeReplacementMap::new();
                replacements.insert_replacing(parameter, deep_type(DEPTH));
                replacements.insert_replacing(parameter, deep_type(DEPTH));
            })
            .expect("the duplicate-replacement thread should start")
            .join()
            .expect("duplicate replacement teardown must stay iterative");
    }
}
