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
#[must_use]
pub fn usefulness(
    matrix: &[Vec<CorePattern>],
    candidate: &[CorePattern],
    types: &[Type],
    registry: &ResolvedRegistry,
) -> Option<Vec<WitnessPattern>> {
    let matrix = matrix
        .iter()
        .map(|row| row.iter().map(shape).collect())
        .collect::<Vec<Vec<_>>>();
    let candidate = candidate.iter().map(shape).collect::<Vec<_>>();
    usefulness_shapes(&matrix, &candidate, types, registry)
}

/// Low-level witness query that does not require synthesizing source origins.
#[must_use]
pub fn missing_witness_for_types(
    matrix: &[Vec<CorePattern>],
    types: &[Type],
    registry: &ResolvedRegistry,
) -> Option<Vec<WitnessPattern>> {
    let matrix = matrix
        .iter()
        .map(|row| row.iter().map(shape).collect())
        .collect::<Vec<Vec<_>>>();
    let candidate = vec![WitnessPattern::Wildcard; types.len()];
    usefulness_shapes(&matrix, &candidate, types, registry)
}

fn shape(pattern: &CorePattern) -> WitnessPattern {
    match &pattern.kind {
        CorePatternKind::Binder(_) | CorePatternKind::Wildcard => WitnessPattern::Wildcard,
        CorePatternKind::Boolean(value) => WitnessPattern::Boolean(*value),
        CorePatternKind::Unit => WitnessPattern::Unit,
        CorePatternKind::Tuple(elements) => WitnessPattern::Tuple(
            elements
                .iter()
                .map(shape)
                .collect::<Vec<_>>()
                .into_boxed_slice(),
        ),
        CorePatternKind::Constructor {
            constructor,
            payload,
        } => WitnessPattern::Constructor(*constructor, payload.as_deref().map(shape).map(Box::new)),
    }
}

fn usefulness_shapes(
    matrix: &[Vec<WitnessPattern>],
    candidate: &[WitnessPattern],
    types: &[Type],
    registry: &ResolvedRegistry,
) -> Option<Vec<WitnessPattern>> {
    let root = (matrix.to_vec(), candidate.to_vec(), types.to_vec());
    let mut memo = HashMap::<State, Option<Vec<WitnessPattern>>>::new();
    let mut active = HashSet::new();
    let mut frames = vec![Frame::Call(root)];
    let mut returned = None::<Option<Vec<WitnessPattern>>>;

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
                match immediate_result(&state) {
                    Some(result) => {
                        memo.insert(state, result.clone());
                        returned = Some(result);
                    }
                    None => {
                        let choices = choices(&state, registry);
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

    returned.flatten()
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

fn choices(state: &State, registry: &ResolvedRegistry) -> Vec<Choice> {
    let (matrix, candidate, types) = state;
    let first_type = &types[0];
    if candidate[0].is_wildcard() {
        if let Some(heads) = heads_for_type(first_type, registry) {
            return heads
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
                .collect();
        }
        let default = matrix
            .iter()
            .filter(|row| row[0].is_wildcard())
            .map(|row| row[1..].to_vec())
            .collect::<Vec<_>>();
        return vec![Choice {
            child: (default, candidate[1..].to_vec(), types[1..].to_vec()),
            rebuild: Rebuild::Wildcard,
        }];
    }

    let Some(head) = pattern_head(&candidate[0]) else {
        return Vec::new();
    };
    let argument_types = head_types(head, first_type, registry);
    let argument_count = argument_types.len();
    let specialized_matrix = specialize_matrix(matrix, head, argument_count);
    let mut specialized_candidate = pattern_arguments(&candidate[0]);
    specialized_candidate.extend_from_slice(&candidate[1..]);
    let mut specialized_types = argument_types;
    specialized_types.extend_from_slice(&types[1..]);
    vec![Choice {
        child: (specialized_matrix, specialized_candidate, specialized_types),
        rebuild: Rebuild::Head {
            head,
            argument_count,
        },
    }]
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
