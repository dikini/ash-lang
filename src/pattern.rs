//! Shared typed-pattern usefulness and witness construction.

use std::collections::HashSet;

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
    let mut active = HashSet::new();
    usefulness_inner(matrix, candidate, types, registry, &mut active)
}

fn usefulness_inner(
    matrix: &[Vec<WitnessPattern>],
    candidate: &[WitnessPattern],
    types: &[Type],
    registry: &ResolvedRegistry,
    active: &mut HashSet<State>,
) -> Option<Vec<WitnessPattern>> {
    if candidate.is_empty() {
        return matrix.is_empty().then(Vec::new);
    }
    if matrix.is_empty() {
        return Some(candidate.to_vec());
    }
    if types.len() != candidate.len() || matrix.iter().any(|row| row.len() != candidate.len()) {
        return None;
    }
    if matrix
        .iter()
        .any(|row| row.iter().all(WitnessPattern::is_wildcard))
    {
        return None;
    }
    let state = (matrix.to_vec(), candidate.to_vec(), types.to_vec());
    if !active.insert(state.clone()) {
        return None;
    }

    let first_type = &types[0];
    let result = if candidate[0].is_wildcard() {
        if let Some(heads) = heads_for_type(first_type, registry) {
            heads.into_iter().find_map(|head| {
                let argument_types = head_types(head, first_type, registry);
                let specialized_matrix = specialize_matrix(matrix, head, argument_types.len());
                let mut specialized_candidate =
                    vec![WitnessPattern::Wildcard; argument_types.len()];
                specialized_candidate.extend_from_slice(&candidate[1..]);
                let mut specialized_types = argument_types.clone();
                specialized_types.extend_from_slice(&types[1..]);
                usefulness_inner(
                    &specialized_matrix,
                    &specialized_candidate,
                    &specialized_types,
                    registry,
                    active,
                )
                .map(|mut witness| {
                    let arguments = witness.drain(..argument_types.len()).collect();
                    let mut rebuilt = vec![pattern_from_head(head, arguments)];
                    rebuilt.extend(witness);
                    rebuilt
                })
            })
        } else {
            let default = matrix
                .iter()
                .filter(|row| row[0].is_wildcard())
                .map(|row| row[1..].to_vec())
                .collect::<Vec<_>>();
            usefulness_inner(&default, &candidate[1..], &types[1..], registry, active).map(
                |mut witness| {
                    let mut rebuilt = vec![WitnessPattern::Wildcard];
                    rebuilt.append(&mut witness);
                    rebuilt
                },
            )
        }
    } else {
        let head = pattern_head(&candidate[0])?;
        let argument_types = head_types(head, first_type, registry);
        let specialized_matrix = specialize_matrix(matrix, head, argument_types.len());
        let mut specialized_candidate = pattern_arguments(&candidate[0]);
        specialized_candidate.extend_from_slice(&candidate[1..]);
        let mut specialized_types = argument_types.clone();
        specialized_types.extend_from_slice(&types[1..]);
        usefulness_inner(
            &specialized_matrix,
            &specialized_candidate,
            &specialized_types,
            registry,
            active,
        )
        .map(|mut witness| {
            let arguments = witness.drain(..argument_types.len()).collect();
            let mut rebuilt = vec![pattern_from_head(head, arguments)];
            rebuilt.extend(witness);
            rebuilt
        })
    };
    active.remove(&state);
    result
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
