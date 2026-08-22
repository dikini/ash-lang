//! Shared typed-pattern usefulness and witness construction.

use std::collections::{HashMap, HashSet};

use crate::{
    core::{CorePattern, CorePatternKind},
    resolved::ResolvedRegistry,
    types::{ConstructorId, Type},
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

type State = (Vec<Vec<WitnessPattern>>, Vec<WitnessPattern>, Vec<Type>);

/// Maximum number of distinct usefulness states explored by one query.
pub const USEFULNESS_STATE_LIMIT: usize = 100_000;
/// Maximum cumulative matrix and specialization work for one case group.
pub const USEFULNESS_WORK_LIMIT: usize = 1_000_000;

/// A compiler resource boundary reached while analyzing pattern coverage.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum UsefulnessError {
    /// The usefulness state budget was exhausted.
    StateLimit,
    /// The cumulative case-group work budget was exhausted.
    WorkLimit,
}

/// Shared deterministic work budget for all usefulness queries in one group.
#[derive(Debug)]
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
    child: State,
    rebuild: Rebuild,
}

#[derive(Clone, Copy)]
enum Rebuild {
    Head { head: Head, argument_count: usize },
    Wildcard,
}

enum Frame {
    Call(State),
    TryChoices {
        state: State,
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
    let matrix = matrix
        .iter()
        .map(|row| row.iter().map(shape).collect())
        .collect::<Vec<Vec<_>>>();
    let candidate = candidate.iter().map(shape).collect::<Vec<_>>();
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
    let matrix = matrix
        .iter()
        .map(|row| row.iter().map(shape).collect())
        .collect::<Vec<Vec<_>>>();
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

fn shape(pattern: &CorePattern) -> WitnessPattern {
    enum Task<'a> {
        Visit(&'a CorePattern),
        FinishTuple(usize),
        FinishConstructor(ConstructorId, bool),
    }

    let mut work = vec![Task::Visit(pattern)];
    let mut rebuilt = Vec::new();
    while let Some(task) = work.pop() {
        match task {
            Task::Visit(pattern) => match &pattern.kind {
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
            },
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
    rebuilt.pop().unwrap_or(WitnessPattern::Wildcard)
}

fn usefulness_shapes(
    matrix: &[Vec<WitnessPattern>],
    candidate: &[WitnessPattern],
    types: &[Type],
    registry: &ResolvedRegistry,
    state_limit: usize,
    budget: &mut UsefulnessBudget,
) -> Result<Option<Vec<WitnessPattern>>, UsefulnessError> {
    let root = (matrix.to_vec(), candidate.to_vec(), types.to_vec());
    let mut memo = HashMap::<State, Option<Vec<WitnessPattern>>>::new();
    let mut active = HashSet::new();
    let mut frames = vec![Frame::Call(root)];
    let mut returned = None::<Option<Vec<WitnessPattern>>>;
    let mut explored = 0_usize;

    while let Some(frame) = frames.pop() {
        match frame {
            Frame::Call(state) => {
                if let Some(cached) = memo.get(&state) {
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
                match immediate_result(&state) {
                    Some(result) => {
                        memo.insert(state, result.clone());
                        returned = Some(result);
                    }
                    None => {
                        let choices = choices(&state, registry, state_limit, budget)?;
                        active.insert(state.clone());
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
                            let result = Some(rebuild_witness(witness, choice.rebuild));
                            active.remove(&state);
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

fn immediate_result(state: &State) -> Option<Option<Vec<WitnessPattern>>> {
    let (matrix, candidate, types) = state;
    if candidate.is_empty() {
        return Some(matrix.is_empty().then(Vec::new));
    }
    if matrix.is_empty() {
        return Some(Some(candidate.clone()));
    }
    if types.len() != candidate.len() || matrix.iter().any(|row| row.len() != candidate.len()) {
        return Some(None);
    }
    matrix
        .iter()
        .any(|row| row.iter().all(WitnessPattern::is_wildcard))
        .then_some(None)
}

fn choices(
    state: &State,
    registry: &ResolvedRegistry,
    state_limit: usize,
    budget: &mut UsefulnessBudget,
) -> Result<Vec<Choice>, UsefulnessError> {
    let (matrix, candidate, types) = state;
    let first_type = &types[0];
    if candidate[0].is_wildcard() {
        if let Some(heads) = heads_for_type(first_type, registry) {
            if heads.len() > state_limit {
                return Err(UsefulnessError::StateLimit);
            }
            budget.charge(heads.len().saturating_mul(matrix.len().max(1)))?;
            return Ok(heads
                .into_iter()
                .map(|head| {
                    let argument_types = head_types(head, first_type, registry);
                    let argument_count = argument_types.len();
                    let specialized_matrix = specialize_matrix(matrix, head, argument_count);
                    let mut specialized_candidate = vec![WitnessPattern::Wildcard; argument_count];
                    specialized_candidate.extend_from_slice(&candidate[1..]);
                    let mut specialized_types = argument_types;
                    specialized_types.extend_from_slice(&types[1..]);
                    Choice {
                        child: (specialized_matrix, specialized_candidate, specialized_types),
                        rebuild: Rebuild::Head {
                            head,
                            argument_count,
                        },
                    }
                })
                .collect());
        }
        let default = matrix
            .iter()
            .filter(|row| row[0].is_wildcard())
            .map(|row| row[1..].to_vec())
            .collect::<Vec<_>>();
        return Ok(vec![Choice {
            child: (default, candidate[1..].to_vec(), types[1..].to_vec()),
            rebuild: Rebuild::Wildcard,
        }]);
    }

    let Some(head) = pattern_head(&candidate[0]) else {
        return Ok(Vec::new());
    };
    budget.charge(matrix.len().max(1))?;
    let argument_types = head_types(head, first_type, registry);
    let argument_count = argument_types.len();
    let specialized_matrix = specialize_matrix(matrix, head, argument_count);
    let mut specialized_candidate = pattern_arguments(&candidate[0]);
    specialized_candidate.extend_from_slice(&candidate[1..]);
    let mut specialized_types = argument_types;
    specialized_types.extend_from_slice(&types[1..]);
    Ok(vec![Choice {
        child: (specialized_matrix, specialized_candidate, specialized_types),
        rebuild: Rebuild::Head {
            head,
            argument_count,
        },
    }])
}

fn rebuild_witness(mut witness: Vec<WitnessPattern>, rebuild: Rebuild) -> Vec<WitnessPattern> {
    match rebuild {
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
    }
}

fn heads_for_type(ty: &Type, registry: &ResolvedRegistry) -> Option<Vec<Head>> {
    match ty {
        Type::Bool => Some(vec![Head::Boolean(true), Head::Boolean(false)]),
        Type::Unit => Some(vec![Head::Unit]),
        Type::Tuple(elements) => Some(vec![Head::Tuple(elements.len())]),
        Type::Nominal(id) => Some(
            registry
                .nominal(*id)?
                .constructors
                .iter()
                .copied()
                .map(Head::Constructor)
                .collect(),
        ),
        Type::Int | Type::Function(_, _) => None,
    }
}

fn head_types(head: Head, ty: &Type, registry: &ResolvedRegistry) -> Vec<Type> {
    match head {
        Head::Boolean(_) | Head::Unit => Vec::new(),
        Head::Tuple(count) => match ty {
            Type::Tuple(elements) if elements.len() == count => elements.to_vec(),
            _ => Vec::new(),
        },
        Head::Constructor(id) => registry
            .constructor(id)
            .and_then(|constructor| constructor.payload.clone())
            .into_iter()
            .collect(),
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

fn pattern_arguments(pattern: &WitnessPattern) -> Vec<WitnessPattern> {
    match pattern {
        WitnessPattern::Tuple(elements) => elements.to_vec(),
        WitnessPattern::Constructor(_, Some(payload)) => vec![payload.as_ref().clone()],
        _ => Vec::new(),
    }
}

fn specialize_matrix(
    matrix: &[Vec<WitnessPattern>],
    head: Head,
    argument_count: usize,
) -> Vec<Vec<WitnessPattern>> {
    matrix
        .iter()
        .filter_map(|row| {
            if row[0].is_wildcard() {
                let mut result = vec![WitnessPattern::Wildcard; argument_count];
                result.extend_from_slice(&row[1..]);
                Some(result)
            } else if pattern_head(&row[0]) == Some(head) {
                let mut result = pattern_arguments(&row[0]);
                result.extend_from_slice(&row[1..]);
                Some(result)
            } else {
                None
            }
        })
        .collect()
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
}
