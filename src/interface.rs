//! Stable typed identities for resolved interfaces and implementations.

use std::{
    collections::HashMap,
    fmt,
    sync::{Arc, OnceLock},
};

use crate::{
    module::ModuleId,
    resolved::BinderId,
    source::{Origin, Span, discard_origin_iteratively},
    types::{
        Type, TypeVariableId, TypeWorkBudget, clone_type_with_budget, discard_type_iteratively,
    },
};

/// Maximum cumulative interface and constraint work across one module graph.
pub const INTERFACE_CONSTRAINT_WORK_LIMIT: usize = 327_680;

/// Graph-wide accounting for interface facts, constraints, and evidence work.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct InterfaceConstraintBudget {
    used: usize,
    limit: usize,
}

impl Default for InterfaceConstraintBudget {
    fn default() -> Self {
        Self {
            used: 0,
            limit: INTERFACE_CONSTRAINT_WORK_LIMIT,
        }
    }
}

impl InterfaceConstraintBudget {
    #[cfg(test)]
    pub(crate) const fn with_limit(limit: usize) -> Self {
        Self { used: 0, limit }
    }

    #[cfg(test)]
    pub(crate) const fn used(&self) -> usize {
        self.used
    }

    pub(crate) fn charge(&mut self, work: usize) -> Result<(), ()> {
        let next = self.used.checked_add(work).ok_or(())?;
        if next > self.limit {
            return Err(());
        }
        self.used = next;
        Ok(())
    }

    pub(crate) fn charge_type(&mut self, root: &Type) -> Result<(), ()> {
        enum Task<'a> {
            Type(&'a Type),
            Sequence(std::slice::Iter<'a, Type>),
        }

        self.charge(1)?;
        let mut pending = Vec::new();
        pending.try_reserve(1).map_err(|_| ())?;
        pending.push(Task::Type(root));
        while let Some(task) = pending.pop() {
            let Task::Type(ty) = task else {
                let Task::Sequence(mut remaining) = task else {
                    unreachable!()
                };
                if let Some(next) = remaining.next() {
                    self.charge(2)?;
                    pending.try_reserve(2).map_err(|_| ())?;
                    pending.push(Task::Sequence(remaining));
                    pending.push(Task::Type(next));
                }
                continue;
            };
            self.charge(1)?;
            match ty {
                Type::Tuple(elements) | Type::AppliedNominal(_, elements) => {
                    self.charge(1)?;
                    pending.try_reserve(1).map_err(|_| ())?;
                    pending.push(Task::Sequence(elements.iter()));
                }
                Type::Function(domain, codomain) => {
                    self.charge(2)?;
                    pending.try_reserve(2).map_err(|_| ())?;
                    pending.push(Task::Type(codomain));
                    pending.push(Task::Type(domain));
                }
                Type::Forall(parameters, body) => {
                    self.charge(parameters.len().saturating_add(1))?;
                    pending.try_reserve(1).map_err(|_| ())?;
                    pending.push(Task::Type(body));
                }
                Type::Int
                | Type::Bool
                | Type::Unit
                | Type::Nominal(_)
                | Type::Variable(_)
                | Type::Inference(_) => {}
            }
        }
        Ok(())
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum OverlapFailure {
    InvalidState,
    Resource,
}

/// Failure while matching one checked implementation head against an obligation.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum HeadMatchFailure {
    /// A checked head contains a forbidden type or an unbound candidate variable.
    InvalidState,
    /// Matching or constraint-side retention exceeded the graph constraint bound.
    ConstraintResource,
    /// Retaining a matched substitution exceeded the structural type bound.
    TypeResource,
}

/// Matches one implementation head against one already determined obligation.
///
/// Only `candidate_parameters` bind. Goal variables remain rigid, and inference
/// variables or rank-1 schemes on either side are invalid checked state.
pub(crate) fn match_implementation_head<I>(
    candidate_parameters: I,
    candidate: &Type,
    goal: &Type,
    constraint_budget: &mut InterfaceConstraintBudget,
    type_budget: &mut TypeWorkBudget,
) -> Result<Option<Box<[EvidenceSubstitution]>>, HeadMatchFailure>
where
    I: ExactSizeIterator<Item = TypeVariableId>,
{
    let parameter_count = candidate_parameters.len();
    constraint_budget
        .charge(parameter_count)
        .map_err(|()| HeadMatchFailure::ConstraintResource)?;
    let mut parameters = Vec::new();
    parameters
        .try_reserve(parameter_count)
        .map_err(|_| HeadMatchFailure::ConstraintResource)?;
    let mut positions = HashMap::new();
    positions
        .try_reserve(parameter_count)
        .map_err(|_| HeadMatchFailure::ConstraintResource)?;
    for (position, parameter) in candidate_parameters.enumerate() {
        constraint_budget
            .charge(1)
            .map_err(|()| HeadMatchFailure::ConstraintResource)?;
        if positions.insert(parameter, position).is_some() {
            return Err(HeadMatchFailure::InvalidState);
        }
        parameters.push(parameter);
    }

    validate_match_type(candidate, Some(&positions), constraint_budget)?;
    validate_match_type(goal, None, constraint_budget)?;

    constraint_budget
        .charge(1)
        .map_err(|()| HeadMatchFailure::ConstraintResource)?;
    let mut pending = Vec::new();
    pending
        .try_reserve(1)
        .map_err(|_| HeadMatchFailure::ConstraintResource)?;
    pending.push((candidate, goal));
    let mut bindings = Vec::new();
    bindings
        .try_reserve(parameter_count)
        .map_err(|_| HeadMatchFailure::ConstraintResource)?;
    bindings.resize(parameter_count, None);
    while let Some((candidate, goal)) = pending.pop() {
        constraint_budget
            .charge(1)
            .map_err(|()| HeadMatchFailure::ConstraintResource)?;
        if let Type::Variable(variable) = candidate {
            let position = positions
                .get(variable)
                .copied()
                .ok_or(HeadMatchFailure::InvalidState)?;
            if let Some(previous) = bindings[position] {
                if !match_types_equal(previous, goal, constraint_budget)? {
                    return Ok(None);
                }
            } else {
                bindings[position] = Some(goal);
            }
            continue;
        }
        match (candidate, goal) {
            (Type::Int, Type::Int) | (Type::Bool, Type::Bool) | (Type::Unit, Type::Unit) => {}
            (Type::Nominal(candidate), Type::Nominal(goal)) if candidate == goal => {}
            (
                Type::AppliedNominal(candidate_id, candidate_types),
                Type::AppliedNominal(goal_id, goal_types),
            ) if candidate_id == goal_id && candidate_types.len() == goal_types.len() => {
                schedule_match_pairs(candidate_types, goal_types, &mut pending, constraint_budget)?;
            }
            (Type::Tuple(candidate_types), Type::Tuple(goal_types))
                if candidate_types.len() == goal_types.len() =>
            {
                schedule_match_pairs(candidate_types, goal_types, &mut pending, constraint_budget)?;
            }
            (
                Type::Function(candidate_domain, candidate_codomain),
                Type::Function(goal_domain, goal_codomain),
            ) => {
                constraint_budget
                    .charge(2)
                    .map_err(|()| HeadMatchFailure::ConstraintResource)?;
                pending
                    .try_reserve(2)
                    .map_err(|_| HeadMatchFailure::ConstraintResource)?;
                pending.push((candidate_codomain, goal_codomain));
                pending.push((candidate_domain, goal_domain));
            }
            (Type::Variable(_), _)
            | (Type::Forall(_, _), _)
            | (_, Type::Forall(_, _))
            | (Type::Inference(_), _)
            | (_, Type::Inference(_)) => return Err(HeadMatchFailure::InvalidState),
            _ => return Ok(None),
        }
    }

    let mut substitution = Vec::new();
    substitution
        .try_reserve(parameter_count)
        .map_err(|_| HeadMatchFailure::ConstraintResource)?;
    for (parameter, binding) in parameters.into_iter().zip(bindings) {
        let binding = binding.ok_or(HeadMatchFailure::InvalidState)?;
        constraint_budget
            .charge(1)
            .map_err(|()| HeadMatchFailure::ConstraintResource)?;
        constraint_budget
            .charge_type(binding)
            .map_err(|()| HeadMatchFailure::ConstraintResource)?;
        let argument = clone_type_with_budget(binding, type_budget)
            .map_err(|()| HeadMatchFailure::TypeResource)?;
        substitution.push(EvidenceSubstitution::new(parameter, argument));
    }
    Ok(Some(substitution.into_boxed_slice()))
}

fn validate_match_type(
    root: &Type,
    candidate_parameters: Option<&HashMap<TypeVariableId, usize>>,
    budget: &mut InterfaceConstraintBudget,
) -> Result<(), HeadMatchFailure> {
    budget
        .charge(1)
        .map_err(|()| HeadMatchFailure::ConstraintResource)?;
    let mut pending = Vec::new();
    pending
        .try_reserve(1)
        .map_err(|_| HeadMatchFailure::ConstraintResource)?;
    pending.push(root);
    while let Some(ty) = pending.pop() {
        budget
            .charge(1)
            .map_err(|()| HeadMatchFailure::ConstraintResource)?;
        match ty {
            Type::Tuple(elements) | Type::AppliedNominal(_, elements) => {
                budget
                    .charge(elements.len())
                    .map_err(|()| HeadMatchFailure::ConstraintResource)?;
                pending
                    .try_reserve(elements.len())
                    .map_err(|_| HeadMatchFailure::ConstraintResource)?;
                pending.extend(elements.iter().rev());
            }
            Type::Function(domain, codomain) => {
                budget
                    .charge(2)
                    .map_err(|()| HeadMatchFailure::ConstraintResource)?;
                pending
                    .try_reserve(2)
                    .map_err(|_| HeadMatchFailure::ConstraintResource)?;
                pending.push(codomain);
                pending.push(domain);
            }
            Type::Variable(variable) => {
                if candidate_parameters.is_some_and(|positions| !positions.contains_key(variable)) {
                    return Err(HeadMatchFailure::InvalidState);
                }
            }
            Type::Forall(_, _) | Type::Inference(_) => {
                return Err(HeadMatchFailure::InvalidState);
            }
            Type::Int | Type::Bool | Type::Unit | Type::Nominal(_) => {}
        }
    }
    Ok(())
}

fn schedule_match_pairs<'a>(
    candidate: &'a [Type],
    goal: &'a [Type],
    pending: &mut Vec<(&'a Type, &'a Type)>,
    budget: &mut InterfaceConstraintBudget,
) -> Result<(), HeadMatchFailure> {
    budget
        .charge(candidate.len())
        .map_err(|()| HeadMatchFailure::ConstraintResource)?;
    pending
        .try_reserve(candidate.len())
        .map_err(|_| HeadMatchFailure::ConstraintResource)?;
    pending.extend(candidate.iter().zip(goal).rev());
    Ok(())
}

fn match_types_equal(
    left: &Type,
    right: &Type,
    budget: &mut InterfaceConstraintBudget,
) -> Result<bool, HeadMatchFailure> {
    budget
        .charge(1)
        .map_err(|()| HeadMatchFailure::ConstraintResource)?;
    let mut pending = Vec::new();
    pending
        .try_reserve(1)
        .map_err(|_| HeadMatchFailure::ConstraintResource)?;
    pending.push((left, right));
    while let Some((left, right)) = pending.pop() {
        budget
            .charge(1)
            .map_err(|()| HeadMatchFailure::ConstraintResource)?;
        match (left, right) {
            (Type::Int, Type::Int) | (Type::Bool, Type::Bool) | (Type::Unit, Type::Unit) => {}
            (Type::Nominal(left), Type::Nominal(right)) if left == right => {}
            (Type::Variable(left), Type::Variable(right)) if left == right => {}
            (
                Type::AppliedNominal(left_id, left_types),
                Type::AppliedNominal(right_id, right_types),
            ) if left_id == right_id && left_types.len() == right_types.len() => {
                schedule_match_pairs(left_types, right_types, &mut pending, budget)?;
            }
            (Type::Tuple(left_types), Type::Tuple(right_types))
                if left_types.len() == right_types.len() =>
            {
                schedule_match_pairs(left_types, right_types, &mut pending, budget)?;
            }
            (
                Type::Function(left_domain, left_codomain),
                Type::Function(right_domain, right_codomain),
            ) => {
                budget
                    .charge(2)
                    .map_err(|()| HeadMatchFailure::ConstraintResource)?;
                pending
                    .try_reserve(2)
                    .map_err(|_| HeadMatchFailure::ConstraintResource)?;
                pending.push((left_codomain, right_codomain));
                pending.push((left_domain, right_domain));
            }
            (Type::Forall(_, _), _)
            | (_, Type::Forall(_, _))
            | (Type::Inference(_), _)
            | (_, Type::Inference(_)) => return Err(HeadMatchFailure::InvalidState),
            _ => return Ok(false),
        }
    }
    Ok(true)
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum OverlapSide {
    Left,
    Right,
}

#[derive(Clone, Copy)]
struct OverlapHead<'a> {
    side: OverlapSide,
    ty: &'a Type,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
struct FreshOverlapVariable {
    side: OverlapSide,
    parameter: usize,
}

pub(crate) fn implementation_heads_overlap<L, R>(
    left_parameters: L,
    left: &Type,
    right_parameters: R,
    right: &Type,
    budget: &mut InterfaceConstraintBudget,
) -> Result<bool, OverlapFailure>
where
    L: ExactSizeIterator<Item = TypeVariableId>,
    R: ExactSizeIterator<Item = TypeVariableId>,
{
    let left_positions = overlap_parameter_positions(left_parameters, budget)?;
    let right_positions = overlap_parameter_positions(right_parameters, budget)?;
    budget.charge(1).map_err(|()| OverlapFailure::Resource)?;
    let mut pending = Vec::new();
    pending
        .try_reserve(1)
        .map_err(|_| OverlapFailure::Resource)?;
    pending.push((
        OverlapHead {
            side: OverlapSide::Left,
            ty: left,
        },
        OverlapHead {
            side: OverlapSide::Right,
            ty: right,
        },
    ));
    let mut solutions = HashMap::new();
    while let Some((left, right)) = pending.pop() {
        let left =
            follow_overlap_solution(left, &solutions, &left_positions, &right_positions, budget)?;
        let right =
            follow_overlap_solution(right, &solutions, &left_positions, &right_positions, budget)?;
        budget.charge(1).map_err(|()| OverlapFailure::Resource)?;
        let left_variable = overlap_variable(left, &left_positions, &right_positions)?;
        let right_variable = overlap_variable(right, &left_positions, &right_positions)?;
        if left_variable.is_some() || right_variable.is_some() {
            if left_variable == right_variable {
                continue;
            }
            let (variable, value) = if let Some(variable) = left_variable {
                (variable, right)
            } else {
                (right_variable.ok_or(OverlapFailure::InvalidState)?, left)
            };
            if overlap_occurs(
                variable,
                value,
                &solutions,
                &left_positions,
                &right_positions,
                budget,
            )? {
                return Ok(false);
            }
            budget.charge(1).map_err(|()| OverlapFailure::Resource)?;
            solutions
                .try_reserve(1)
                .map_err(|_| OverlapFailure::Resource)?;
            solutions.insert(variable, value);
            continue;
        }
        match (left.ty, right.ty) {
            (Type::Int, Type::Int) | (Type::Bool, Type::Bool) | (Type::Unit, Type::Unit) => {}
            (Type::Nominal(left), Type::Nominal(right)) if left == right => {}
            (
                Type::AppliedNominal(left_id, left_types),
                Type::AppliedNominal(right_id, right_types),
            ) if left_id == right_id && left_types.len() == right_types.len() => {
                schedule_overlap_pairs(
                    left_types,
                    left.side,
                    right_types,
                    right.side,
                    &mut pending,
                    budget,
                )?;
            }
            (Type::Tuple(left_types), Type::Tuple(right_types))
                if left_types.len() == right_types.len() =>
            {
                schedule_overlap_pairs(
                    left_types,
                    left.side,
                    right_types,
                    right.side,
                    &mut pending,
                    budget,
                )?;
            }
            (
                Type::Function(left_domain, left_codomain),
                Type::Function(right_domain, right_codomain),
            ) => {
                budget.charge(2).map_err(|()| OverlapFailure::Resource)?;
                pending
                    .try_reserve(2)
                    .map_err(|_| OverlapFailure::Resource)?;
                pending.push((
                    OverlapHead {
                        side: left.side,
                        ty: left_codomain,
                    },
                    OverlapHead {
                        side: right.side,
                        ty: right_codomain,
                    },
                ));
                pending.push((
                    OverlapHead {
                        side: left.side,
                        ty: left_domain,
                    },
                    OverlapHead {
                        side: right.side,
                        ty: right_domain,
                    },
                ));
            }
            (Type::Variable(_), _) | (_, Type::Variable(_)) => {
                return Err(OverlapFailure::InvalidState);
            }
            (Type::Forall(_, _), _)
            | (_, Type::Forall(_, _))
            | (Type::Inference(_), _)
            | (_, Type::Inference(_)) => return Err(OverlapFailure::InvalidState),
            _ => return Ok(false),
        }
    }
    Ok(true)
}

fn overlap_parameter_positions(
    parameters: impl ExactSizeIterator<Item = TypeVariableId>,
    budget: &mut InterfaceConstraintBudget,
) -> Result<HashMap<TypeVariableId, usize>, OverlapFailure> {
    let parameter_count = parameters.len();
    budget
        .charge(parameter_count)
        .map_err(|()| OverlapFailure::Resource)?;
    let mut positions = HashMap::new();
    positions
        .try_reserve(parameter_count)
        .map_err(|_| OverlapFailure::Resource)?;
    for (position, parameter) in parameters.enumerate() {
        budget.charge(1).map_err(|()| OverlapFailure::Resource)?;
        if positions.insert(parameter, position).is_some() {
            return Err(OverlapFailure::InvalidState);
        }
    }
    Ok(positions)
}

fn overlap_variable(
    head: OverlapHead<'_>,
    left_positions: &HashMap<TypeVariableId, usize>,
    right_positions: &HashMap<TypeVariableId, usize>,
) -> Result<Option<FreshOverlapVariable>, OverlapFailure> {
    let Type::Variable(variable) = head.ty else {
        return Ok(None);
    };
    let parameter = match head.side {
        OverlapSide::Left => left_positions.get(variable),
        OverlapSide::Right => right_positions.get(variable),
    }
    .copied()
    .ok_or(OverlapFailure::InvalidState)?;
    Ok(Some(FreshOverlapVariable {
        side: head.side,
        parameter,
    }))
}

fn schedule_overlap_pairs<'a>(
    left: &'a [Type],
    left_side: OverlapSide,
    right: &'a [Type],
    right_side: OverlapSide,
    pending: &mut Vec<(OverlapHead<'a>, OverlapHead<'a>)>,
    budget: &mut InterfaceConstraintBudget,
) -> Result<(), OverlapFailure> {
    budget
        .charge(left.len())
        .map_err(|()| OverlapFailure::Resource)?;
    pending
        .try_reserve(left.len())
        .map_err(|_| OverlapFailure::Resource)?;
    pending.extend(left.iter().zip(right).rev().map(|(left, right)| {
        (
            OverlapHead {
                side: left_side,
                ty: left,
            },
            OverlapHead {
                side: right_side,
                ty: right,
            },
        )
    }));
    Ok(())
}

fn follow_overlap_solution<'a>(
    mut head: OverlapHead<'a>,
    solutions: &HashMap<FreshOverlapVariable, OverlapHead<'a>>,
    left_positions: &HashMap<TypeVariableId, usize>,
    right_positions: &HashMap<TypeVariableId, usize>,
    budget: &mut InterfaceConstraintBudget,
) -> Result<OverlapHead<'a>, OverlapFailure> {
    loop {
        budget.charge(1).map_err(|()| OverlapFailure::Resource)?;
        let Some(variable) = overlap_variable(head, left_positions, right_positions)? else {
            return Ok(head);
        };
        let Some(solution) = solutions.get(&variable) else {
            return Ok(head);
        };
        head = *solution;
    }
}

fn overlap_occurs<'a>(
    needle: FreshOverlapVariable,
    root: OverlapHead<'a>,
    solutions: &HashMap<FreshOverlapVariable, OverlapHead<'a>>,
    left_positions: &HashMap<TypeVariableId, usize>,
    right_positions: &HashMap<TypeVariableId, usize>,
    budget: &mut InterfaceConstraintBudget,
) -> Result<bool, OverlapFailure> {
    budget.charge(1).map_err(|()| OverlapFailure::Resource)?;
    let mut pending = Vec::new();
    pending
        .try_reserve(1)
        .map_err(|_| OverlapFailure::Resource)?;
    pending.push(root);
    while let Some(head) = pending.pop() {
        let head =
            follow_overlap_solution(head, solutions, left_positions, right_positions, budget)?;
        budget.charge(1).map_err(|()| OverlapFailure::Resource)?;
        if let Some(variable) = overlap_variable(head, left_positions, right_positions)? {
            if variable == needle {
                return Ok(true);
            }
            continue;
        }
        match head.ty {
            Type::Tuple(elements) | Type::AppliedNominal(_, elements) => {
                budget
                    .charge(elements.len())
                    .map_err(|()| OverlapFailure::Resource)?;
                pending
                    .try_reserve(elements.len())
                    .map_err(|_| OverlapFailure::Resource)?;
                pending.extend(elements.iter().rev().map(|ty| OverlapHead {
                    side: head.side,
                    ty,
                }));
            }
            Type::Function(domain, codomain) => {
                budget.charge(2).map_err(|()| OverlapFailure::Resource)?;
                pending
                    .try_reserve(2)
                    .map_err(|_| OverlapFailure::Resource)?;
                pending.push(OverlapHead {
                    side: head.side,
                    ty: codomain,
                });
                pending.push(OverlapHead {
                    side: head.side,
                    ty: domain,
                });
            }
            Type::Variable(_) => return Err(OverlapFailure::InvalidState),
            Type::Forall(_, _) | Type::Inference(_) => return Err(OverlapFailure::InvalidState),
            Type::Int | Type::Bool | Type::Unit | Type::Nominal(_) => {}
        }
    }
    Ok(false)
}

/// The interface or implementation header judgment that rejected source.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum InterfaceReason {
    /// An interface method omits its parameter or introduces another type variable.
    MethodParameter,
    /// An interface method signature has no callable function shape.
    MethodNotFunction,
    /// One constrained global repeats an identity-equal requirement.
    DuplicateRequirement,
    /// A requirement mentions a type parameter absent from the value type.
    UndeterminedParameter,
    /// No abstract requirement or available implementation matches the obligation.
    Unsatisfied,
    /// The obligation remains undetermined when evidence selection must begin.
    Ambiguous,
    /// Selecting prerequisites re-entered an active obligation.
    Cycle,
    /// A public constrained global exposes a private interface.
    ConstraintPrivateInterface,
    /// A public implementation or prerequisite exposes a private interface.
    ImplPrivateInterface,
    /// Neither the implemented interface nor outer nominal head is locally owned.
    ImplOrphan,
    /// An implementation head is a bare type variable.
    ImplVariableHead,
    /// Two available implementation heads unify.
    ImplOverlap,
    /// An implementation prerequisite introduces a variable absent from the head.
    ImplPrerequisiteVariable,
    /// A non-ground implementation prerequisite is not a strict head subterm.
    ImplPrerequisiteNotDecreasing,
    /// An implementation omits one required interface method.
    ImplMissingMethod,
    /// An implementation supplies one interface method more than once.
    ImplDuplicateMethod,
    /// An implementation group does not name a method of its interface.
    ImplExtraMethod,
}

impl fmt::Display for InterfaceReason {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(match self {
            Self::MethodParameter => "interface.method-parameter",
            Self::MethodNotFunction => "interface.method-not-function",
            Self::DuplicateRequirement => "constraint.duplicate-requirement",
            Self::UndeterminedParameter => "constraint.undetermined-parameter",
            Self::Unsatisfied => "constraint.unsatisfied",
            Self::Ambiguous => "constraint.ambiguous",
            Self::Cycle => "constraint.cycle",
            Self::ConstraintPrivateInterface => "constraint.private-interface",
            Self::ImplPrivateInterface => "impl.private-interface",
            Self::ImplOrphan => "impl.orphan",
            Self::ImplVariableHead => "impl.variable-head",
            Self::ImplOverlap => "impl.overlap",
            Self::ImplPrerequisiteVariable => "impl.prerequisite-variable",
            Self::ImplPrerequisiteNotDecreasing => "impl.prerequisite-not-decreasing",
            Self::ImplMissingMethod => "impl.missing-method",
            Self::ImplDuplicateMethod => "impl.duplicate-method",
            Self::ImplExtraMethod => "impl.extra-method",
        })
    }
}

/// Stable identity of one interface declaration.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct InterfaceId {
    module: ModuleId,
    declaration: u32,
}

impl InterfaceId {
    /// Creates the identity for one interface declaration in an admitted module.
    #[must_use]
    pub const fn new(module: ModuleId, declaration: u32) -> Self {
        Self {
            module,
            declaration,
        }
    }

    /// Returns the canonical module that owns the declaration.
    #[must_use]
    pub const fn module(self) -> ModuleId {
        self.module
    }

    /// Returns the source-order interface declaration index.
    #[must_use]
    pub const fn declaration(self) -> u32 {
        self.declaration
    }
}

/// Stable identity of one method declared by an interface.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct MethodId {
    interface: InterfaceId,
    declaration: u32,
}

impl MethodId {
    /// Creates the identity for one method in its interface declaration.
    #[must_use]
    pub const fn new(interface: InterfaceId, declaration: u32) -> Self {
        Self {
            interface,
            declaration,
        }
    }

    /// Returns the interface that owns the method.
    #[must_use]
    pub const fn interface(self) -> InterfaceId {
        self.interface
    }

    /// Returns the source-order method declaration index.
    #[must_use]
    pub const fn declaration(self) -> u32 {
        self.declaration
    }
}

/// Stable identity of one implementation declaration.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ImplId {
    module: ModuleId,
    declaration: u32,
}

impl ImplId {
    /// Creates the identity for one implementation declaration in an admitted module.
    #[must_use]
    pub const fn new(module: ModuleId, declaration: u32) -> Self {
        Self {
            module,
            declaration,
        }
    }

    /// Returns the canonical module that owns the declaration.
    #[must_use]
    pub const fn module(self) -> ModuleId {
        self.module
    }

    /// Returns the source-order implementation declaration index.
    #[must_use]
    pub const fn declaration(self) -> u32 {
        self.declaration
    }
}

/// Stable identity of one interface method supplied by an implementation.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ImplMethodId {
    implementation: ImplId,
    method: MethodId,
}

impl ImplMethodId {
    /// Creates the identity for one implemented interface method.
    #[must_use]
    pub const fn new(implementation: ImplId, method: MethodId) -> Self {
        Self {
            implementation,
            method,
        }
    }

    /// Returns the implementation that supplies the method.
    #[must_use]
    pub const fn implementation(self) -> ImplId {
        self.implementation
    }

    /// Returns the interface method supplied by the implementation.
    #[must_use]
    pub const fn method(self) -> MethodId {
        self.method
    }
}

/// Declaration that owns one ordered interface requirement.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum RequirementOwner {
    /// A requirement declared by a module-level global.
    Global(BinderId),
    /// A prerequisite declared by an implementation.
    Impl(ImplId),
}

/// Stable identity of one ordered interface requirement.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct RequirementId {
    owner: RequirementOwner,
    declaration: u32,
}

impl RequirementId {
    /// Creates the identity for one requirement under its declaring owner.
    #[must_use]
    pub const fn new(owner: RequirementOwner, declaration: u32) -> Self {
        Self { owner, declaration }
    }

    /// Returns the global or implementation that owns the requirement.
    #[must_use]
    pub const fn owner(self) -> RequirementOwner {
        self.owner
    }

    /// Returns the source-order requirement declaration index.
    #[must_use]
    pub const fn declaration(self) -> u32 {
        self.declaration
    }
}

/// Stable index of one node in an immutable evidence plan.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct EvidenceNodeId(usize);

impl EvidenceNodeId {
    /// Returns the node's index in its plan.
    #[must_use]
    pub const fn index(self) -> usize {
        self.0
    }
}

/// One ordered implementation-head parameter substitution.
#[derive(Debug, Eq, PartialEq)]
pub struct EvidenceSubstitution {
    parameter: TypeVariableId,
    argument: Type,
}

impl EvidenceSubstitution {
    fn new(parameter: TypeVariableId, argument: Type) -> Self {
        Self {
            parameter,
            argument,
        }
    }

    /// Returns the bound implementation-head parameter.
    #[must_use]
    pub const fn parameter(&self) -> TypeVariableId {
        self.parameter
    }

    /// Returns the matched obligation type retained for that parameter.
    #[must_use]
    pub const fn argument(&self) -> &Type {
        &self.argument
    }
}

impl Drop for EvidenceSubstitution {
    fn drop(&mut self) {
        discard_type_iteratively(std::mem::replace(&mut self.argument, Type::Unit));
    }
}

#[derive(Debug)]
enum EvidenceNodeData {
    Abstract {
        requirement: RequirementId,
        methods: Box<[MethodId]>,
    },
    Implementation {
        implementation: ImplId,
        substitution: Box<[EvidenceSubstitution]>,
        prerequisites: Box<[EvidenceNodeId]>,
        methods: Box<[ImplMethodId]>,
    },
}

#[derive(Debug)]
struct EvidencePlan {
    nodes: Box<[EvidenceNodeData]>,
}

/// Read-only view of one structural evidence node.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum EvidenceNode<'a> {
    /// One exact abstract requirement and its interface method order.
    Abstract {
        /// Requirement binder selected before implementation search.
        requirement: RequirementId,
        /// Interface methods in declaration order.
        methods: &'a [MethodId],
    },
    /// One selected implementation and the evidence needed to apply it.
    Implementation {
        /// Stable selected implementation identity.
        implementation: ImplId,
        /// Candidate parameters and matched obligation arguments in parameter order.
        substitution: &'a [EvidenceSubstitution],
        /// Prerequisite nodes in declaration order.
        prerequisites: &'a [EvidenceNodeId],
        /// Implementation methods in interface declaration order.
        methods: &'a [ImplMethodId],
    },
}

/// One rooted selection backed by an immutable flat evidence plan.
#[derive(Clone, Debug)]
pub struct EvidenceSelection {
    plan: Arc<EvidencePlan>,
    root: EvidenceNodeId,
}

impl EvidenceSelection {
    /// Returns the root node selected for this requirement.
    #[must_use]
    pub const fn root(&self) -> EvidenceNodeId {
        self.root
    }

    /// Returns the number of nodes retained in the flat plan.
    #[must_use]
    pub fn node_count(&self) -> usize {
        self.plan.nodes.len()
    }

    /// Inspects one node from this selection's plan.
    #[must_use]
    pub fn node(&self, id: EvidenceNodeId) -> Option<EvidenceNode<'_>> {
        match self.plan.nodes.get(id.0)? {
            EvidenceNodeData::Abstract {
                requirement,
                methods,
            } => Some(EvidenceNode::Abstract {
                requirement: *requirement,
                methods,
            }),
            EvidenceNodeData::Implementation {
                implementation,
                substitution,
                prerequisites,
                methods,
            } => Some(EvidenceNode::Implementation {
                implementation: *implementation,
                substitution,
                prerequisites,
                methods,
            }),
        }
    }

    /// Reports whether two selections share the same immutable flat plan.
    #[must_use]
    pub fn shares_plan_with(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.plan, &other.plan)
    }
}

impl PartialEq for EvidenceSelection {
    fn eq(&self, other: &Self) -> bool {
        self.root == other.root && Arc::ptr_eq(&self.plan, &other.plan)
    }
}

impl Eq for EvidenceSelection {}

/// Builder for one immutable flat evidence plan.
#[derive(Debug, Default)]
pub(crate) struct EvidenceSelectionBuilder {
    nodes: Vec<EvidenceNodeData>,
}

impl EvidenceSelectionBuilder {
    pub(crate) const fn new() -> Self {
        Self { nodes: Vec::new() }
    }

    pub(crate) fn push_abstract(
        &mut self,
        requirement: RequirementId,
        methods: &[MethodId],
        budget: &mut InterfaceConstraintBudget,
    ) -> Result<EvidenceNodeId, ()> {
        let retained = 1usize.checked_add(methods.len()).ok_or(())?;
        budget.charge(retained)?;
        let methods = try_copy_slice(methods)?;
        self.nodes.try_reserve(1).map_err(|_| ())?;
        let id = EvidenceNodeId(self.nodes.len());
        self.nodes.push(EvidenceNodeData::Abstract {
            requirement,
            methods,
        });
        Ok(id)
    }

    pub(crate) fn push_implementation(
        &mut self,
        implementation: ImplId,
        substitution: Box<[EvidenceSubstitution]>,
        prerequisites: &[EvidenceNodeId],
        methods: &[ImplMethodId],
        budget: &mut InterfaceConstraintBudget,
    ) -> Result<EvidenceNodeId, ()> {
        let retained = 1usize
            .checked_add(substitution.len())
            .and_then(|work| work.checked_add(prerequisites.len()))
            .and_then(|work| work.checked_add(methods.len()))
            .ok_or(())?;
        budget.charge(retained)?;
        if prerequisites
            .iter()
            .any(|prerequisite| prerequisite.0 >= self.nodes.len())
        {
            return Err(());
        }
        let prerequisites = try_copy_slice(prerequisites)?;
        let methods = try_copy_slice(methods)?;
        self.nodes.try_reserve(1).map_err(|_| ())?;
        let id = EvidenceNodeId(self.nodes.len());
        self.nodes.push(EvidenceNodeData::Implementation {
            implementation,
            substitution,
            prerequisites,
            methods,
        });
        Ok(id)
    }

    pub(crate) fn finish(self, root: EvidenceNodeId) -> Result<EvidenceSelection, ()> {
        if root.0 >= self.nodes.len() {
            return Err(());
        }
        Ok(EvidenceSelection {
            plan: Arc::new(EvidencePlan {
                nodes: self.nodes.into_boxed_slice(),
            }),
            root,
        })
    }

    #[cfg(test)]
    const fn node_count(&self) -> usize {
        self.nodes.len()
    }
}

fn try_copy_slice<T: Copy>(values: &[T]) -> Result<Box<[T]>, ()> {
    let mut copied = Vec::new();
    copied.try_reserve(values.len()).map_err(|_| ())?;
    copied.extend_from_slice(values);
    Ok(copied.into_boxed_slice())
}

/// Structural evidence state owned by one resolved constrained occurrence.
pub struct EvidenceSlot {
    selection: Arc<OnceLock<EvidenceSelection>>,
}

impl EvidenceSlot {
    /// Creates one independently fillable empty evidence slot.
    #[must_use]
    pub fn empty() -> Self {
        Self {
            selection: Arc::new(OnceLock::new()),
        }
    }

    /// Returns the selection filled by checking, when available.
    #[must_use]
    pub fn selection(&self) -> Option<&EvidenceSelection> {
        self.selection.get()
    }

    /// Returns a transient capability that fills this exact structural slot.
    pub(crate) fn handle(&self) -> EvidenceSlotHandle {
        EvidenceSlotHandle {
            selection: Arc::clone(&self.selection),
        }
    }
}

impl Default for EvidenceSlot {
    fn default() -> Self {
        Self::empty()
    }
}

impl Clone for EvidenceSlot {
    fn clone(&self) -> Self {
        match self.selection() {
            Some(_) => Self {
                selection: Arc::clone(&self.selection),
            },
            None => Self::empty(),
        }
    }
}

impl fmt::Debug for EvidenceSlot {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.selection() {
            Some(selection) => formatter.debug_tuple("Selected").field(selection).finish(),
            None => formatter.write_str("Empty"),
        }
    }
}

impl PartialEq for EvidenceSlot {
    fn eq(&self, other: &Self) -> bool {
        match (self.selection(), other.selection()) {
            (None, None) => true,
            (Some(left), Some(right)) => left == right,
            _ => false,
        }
    }
}

impl Eq for EvidenceSlot {}

/// Transient capability for filling one exact occurrence's evidence slot.
#[derive(Clone, Debug)]
pub(crate) struct EvidenceSlotHandle {
    selection: Arc<OnceLock<EvidenceSelection>>,
}

impl EvidenceSlotHandle {
    #[cfg(test)]
    pub(crate) fn selection(&self) -> Option<&EvidenceSelection> {
        self.selection.get()
    }

    pub(crate) fn fill(&self, selection: EvidenceSelection) -> Result<(), EvidenceSelection> {
        self.selection.set(selection)
    }
}

/// One admitted requirement in a checked constrained scheme.
#[derive(Debug, Eq, PartialEq)]
pub struct CheckedRequirement {
    /// Stable occurrence identity under its declaring owner.
    pub id: RequirementId,
    /// Stable checked interface identity.
    pub interface: InterfaceId,
    /// Fully resolved requirement argument.
    pub argument: Type,
    /// Causal declaration provenance.
    pub origin: Origin,
    /// Complete source requirement span.
    pub span: Span,
}

impl Drop for CheckedRequirement {
    fn drop(&mut self) {
        discard_type_iteratively(std::mem::replace(&mut self.argument, Type::Unit));
        discard_origin_iteratively(std::mem::replace(
            &mut self.origin,
            Origin::Source(self.span),
        ));
    }
}

/// A checked source scheme whose requirements remain outside ordinary types.
#[derive(Debug, Eq, PartialEq)]
pub struct ConstrainedScheme {
    /// Ordered outer rank-1 type parameters.
    pub type_parameters: Box<[TypeVariableId]>,
    /// Ordered explicit interface requirements.
    pub requirements: Box<[CheckedRequirement]>,
    /// Source value type without an enclosing `forall` node.
    pub value_type: Type,
}

/// Authentication token for one successfully checked local interface.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct CheckedInterface {
    /// Source-order index into the owning module's resolved interface list.
    pub source_index: usize,
    /// Stable checked interface identity.
    pub id: InterfaceId,
}

/// One exact checked implementation-method membership relation.
#[derive(Debug, Eq, PartialEq)]
pub struct CheckedImplMethod {
    /// Source-order index into the owning implementation's method-group list.
    pub source_group: usize,
    /// Stable identity derived from the implementation and interface method.
    pub id: ImplMethodId,
    /// Stable interface method supplied by this body group.
    pub method: MethodId,
    /// Hidden module-qualified binder for the accepted source group.
    pub binder: BinderId,
}

/// One locally checked implementation header with exact method membership.
#[derive(Debug, Eq, PartialEq)]
pub struct CheckedImplementation {
    /// Source-order index into the owning module's resolved implementation list.
    pub source_index: usize,
    /// Stable anonymous implementation identity.
    pub id: ImplId,
    /// Stable implemented interface identity.
    pub interface: InterfaceId,
    /// Exact method mappings in interface declaration order.
    pub methods: Box<[CheckedImplMethod]>,
}

impl ConstrainedScheme {
    #[cfg(test)]
    pub(crate) fn from_rank1_type(scheme: Type) -> Self {
        match scheme {
            Type::Forall(type_parameters, value_type) => Self {
                type_parameters,
                requirements: Box::new([]),
                value_type: *value_type,
            },
            value_type => Self {
                type_parameters: Box::new([]),
                requirements: Box::new([]),
                value_type,
            },
        }
    }

    pub(crate) fn clone_with_budget(&self, budget: &mut TypeWorkBudget) -> Result<Self, ()> {
        budget.charge(
            self.type_parameters
                .len()
                .saturating_add(self.requirements.len()),
        )?;
        let mut type_parameters = Vec::new();
        type_parameters
            .try_reserve(self.type_parameters.len())
            .map_err(|_| ())?;
        type_parameters.extend_from_slice(&self.type_parameters);
        let mut requirements = Vec::new();
        requirements
            .try_reserve(self.requirements.len())
            .map_err(|_| ())?;
        for requirement in &self.requirements {
            requirements.push(CheckedRequirement {
                id: requirement.id,
                interface: requirement.interface,
                argument: clone_type_with_budget(&requirement.argument, budget)?,
                origin: requirement.origin.clone(),
                span: requirement.span,
            });
        }
        Ok(Self {
            type_parameters: type_parameters.into_boxed_slice(),
            requirements: requirements.into_boxed_slice(),
            value_type: clone_type_with_budget(&self.value_type, budget)?,
        })
    }

    /// Reports whether the source scheme requires no interface evidence.
    #[must_use]
    pub const fn is_unconstrained(&self) -> bool {
        self.requirements.is_empty()
    }
}

impl Drop for ConstrainedScheme {
    fn drop(&mut self) {
        for requirement in std::mem::take(&mut self.requirements).into_vec() {
            drop(requirement);
        }
        discard_type_iteratively(std::mem::replace(&mut self.value_type, Type::Unit));
    }
}

#[cfg(test)]
mod tests {
    use std::any::TypeId;

    use super::*;
    use crate::{module::ModuleId, resolved::BinderId};

    #[test]
    fn interface_and_method_identities_preserve_their_components() {
        let module = ModuleId::new(7);
        let interface = InterfaceId::new(module, 3);
        let method = MethodId::new(interface, 5);

        assert_eq!(interface.module(), module);
        assert_eq!(interface.declaration(), 3);
        assert_eq!(method.interface(), interface);
        assert_eq!(method.declaration(), 5);
    }

    #[test]
    fn implementation_and_method_identities_preserve_their_components() {
        let module = ModuleId::new(11);
        let implementation = ImplId::new(module, 13);
        let interface = InterfaceId::new(module, 17);
        let method = MethodId::new(interface, 19);
        let implementation_method = ImplMethodId::new(implementation, method);

        assert_eq!(implementation.module(), module);
        assert_eq!(implementation.declaration(), 13);
        assert_eq!(implementation_method.implementation(), implementation);
        assert_eq!(implementation_method.method(), method);
    }

    #[test]
    fn requirement_identities_preserve_owner_and_declaration_order() {
        let module = ModuleId::new(23);
        let global = RequirementOwner::Global(BinderId::resolved(module, 29));
        let implementation = RequirementOwner::Impl(ImplId::new(module, 31));
        let first = RequirementId::new(global, 0);
        let second = RequirementId::new(global, 1);
        let prerequisite = RequirementId::new(implementation, 0);

        assert_eq!(first.owner(), global);
        assert_eq!(first.declaration(), 0);
        assert_eq!(second.owner(), global);
        assert_eq!(second.declaration(), 1);
        assert_ne!(first, second);
        assert_eq!(prerequisite.owner(), implementation);
        assert_eq!(prerequisite.declaration(), 0);
    }

    #[test]
    fn semantic_identity_categories_remain_distinct_types() {
        assert_ne!(TypeId::of::<InterfaceId>(), TypeId::of::<ImplId>());
        assert_ne!(TypeId::of::<MethodId>(), TypeId::of::<ImplMethodId>());
        assert_ne!(TypeId::of::<RequirementId>(), TypeId::of::<MethodId>());
        assert!(EvidenceSlot::empty().selection().is_none());
    }

    #[test]
    fn empty_evidence_slot_clones_have_independent_one_shot_cells() {
        let slot = EvidenceSlot::empty();
        let clone = slot.clone();
        let handle = slot.handle();
        let pending = handle.clone();
        let selection = abstract_selection(RequirementId::new(
            RequirementOwner::Global(BinderId::resolved(ModuleId::new(41), 0)),
            0,
        ));

        pending
            .fill(selection.clone())
            .expect("the original empty slot should accept one selection");

        assert_eq!(slot.selection(), Some(&selection));
        assert_eq!(handle.selection(), Some(&selection));
        assert!(clone.selection().is_none());
        assert!(handle.fill(selection).is_err());
    }

    #[test]
    fn selected_evidence_slot_clones_share_the_flat_plan() {
        let slot = EvidenceSlot::empty();
        let selection = abstract_selection(RequirementId::new(
            RequirementOwner::Global(BinderId::resolved(ModuleId::new(43), 0)),
            0,
        ));
        slot.handle()
            .fill(selection)
            .expect("the empty slot should accept one selection");

        let clone = slot.clone();
        let original = slot.selection().expect("the original should be selected");
        let cloned = clone.selection().expect("the clone should be selected");

        assert_eq!(original.root(), cloned.root());
        assert!(original.shares_plan_with(cloned));
    }

    #[test]
    fn evidence_builder_charges_nodes_and_ordered_slots_before_retention() {
        let module = ModuleId::new(47);
        let interface = InterfaceId::new(module, 0);
        let methods = [MethodId::new(interface, 0), MethodId::new(interface, 1)];
        let requirement =
            RequirementId::new(RequirementOwner::Global(BinderId::resolved(module, 0)), 0);

        let mut short_builder = EvidenceSelectionBuilder::new();
        assert_eq!(
            short_builder.push_abstract(
                requirement,
                &methods,
                &mut InterfaceConstraintBudget::with_limit(2),
            ),
            Err(())
        );
        assert_eq!(short_builder.node_count(), 0);

        let mut exact_budget = InterfaceConstraintBudget::with_limit(3);
        let mut builder = EvidenceSelectionBuilder::new();
        let root = builder
            .push_abstract(requirement, &methods, &mut exact_budget)
            .expect("one node and two method slots should fit exactly");
        let selection = builder.finish(root).expect("the root should be retained");
        assert_eq!(exact_budget.used(), 3);
        assert_eq!(exact_budget.charge(1), Err(()));
        assert_eq!(selection.node_count(), 1);
        assert_eq!(
            selection.node(root),
            Some(EvidenceNode::Abstract {
                requirement,
                methods: &methods,
            })
        );
    }

    #[test]
    fn implementation_evidence_retains_ordered_substitution_prerequisites_and_methods() {
        let module = ModuleId::new(53);
        let interface = InterfaceId::new(module, 0);
        let implementation = ImplId::new(module, 0);
        let parameter = TypeVariableId::resolved(module, 0);
        let method = MethodId::new(interface, 0);
        let implementation_method = ImplMethodId::new(implementation, method);
        let requirement =
            RequirementId::new(RequirementOwner::Global(BinderId::resolved(module, 0)), 0);
        let mut builder = EvidenceSelectionBuilder::new();
        let prerequisite = builder
            .push_abstract(
                requirement,
                &[method],
                &mut InterfaceConstraintBudget::default(),
            )
            .expect("the prerequisite should fit");
        let substitutions = vec![EvidenceSubstitution::new(parameter, Type::Int)];
        let mut exact = InterfaceConstraintBudget::with_limit(4);

        let root = builder
            .push_implementation(
                implementation,
                substitutions.into_boxed_slice(),
                &[prerequisite],
                &[implementation_method],
                &mut exact,
            )
            .expect("one node and its three retained slots should fit exactly");
        let selection = builder.finish(root).expect("the root should exist");
        let Some(EvidenceNode::Implementation {
            implementation: actual,
            substitution,
            prerequisites,
            methods,
        }) = selection.node(root)
        else {
            panic!("the root should be implementation evidence");
        };

        assert_eq!(actual, implementation);
        assert_eq!(substitution.len(), 1);
        assert_eq!(substitution[0].parameter(), parameter);
        assert_eq!(substitution[0].argument(), &Type::Int);
        assert_eq!(prerequisites, &[prerequisite]);
        assert_eq!(methods, &[implementation_method]);
        assert_eq!(exact.used(), 4);

        let mut short_builder = EvidenceSelectionBuilder::new();
        let prerequisite = short_builder
            .push_abstract(
                requirement,
                &[method],
                &mut InterfaceConstraintBudget::default(),
            )
            .expect("the prerequisite should fit");
        assert_eq!(
            short_builder.push_implementation(
                implementation,
                vec![EvidenceSubstitution::new(parameter, Type::Int)].into_boxed_slice(),
                &[prerequisite],
                &[implementation_method],
                &mut InterfaceConstraintBudget::with_limit(3),
            ),
            Err(())
        );
        assert_eq!(short_builder.node_count(), 1);
    }

    #[test]
    fn one_way_head_matcher_binds_only_candidate_parameters_in_order() {
        let module = ModuleId::new(59);
        let first = TypeVariableId::resolved(module, 0);
        let second = TypeVariableId::resolved(module, 1);
        let candidate =
            Type::Tuple(vec![Type::Variable(second), Type::Variable(first)].into_boxed_slice());
        let goal = Type::Tuple(vec![Type::Bool, Type::Int].into_boxed_slice());
        let mut constraints = InterfaceConstraintBudget::default();
        let mut types = TypeWorkBudget::default();

        let substitutions = match_implementation_head(
            [first, second].into_iter(),
            &candidate,
            &goal,
            &mut constraints,
            &mut types,
        )
        .expect("the checked heads should be valid")
        .expect("the candidate should match");

        assert_eq!(substitutions.len(), 2);
        assert_eq!(substitutions[0].parameter(), first);
        assert_eq!(substitutions[0].argument(), &Type::Int);
        assert_eq!(substitutions[1].parameter(), second);
        assert_eq!(substitutions[1].argument(), &Type::Bool);
    }

    #[test]
    fn one_way_head_matcher_preserves_repeated_candidate_variables() {
        let parameter = TypeVariableId::new(0);
        let candidate = Type::Tuple(
            vec![Type::Variable(parameter), Type::Variable(parameter)].into_boxed_slice(),
        );
        let matching = Type::Tuple(vec![Type::Int, Type::Int].into_boxed_slice());
        let conflicting = Type::Tuple(vec![Type::Int, Type::Bool].into_boxed_slice());

        assert!(
            match_implementation_head(
                std::iter::once(parameter),
                &candidate,
                &matching,
                &mut InterfaceConstraintBudget::default(),
                &mut TypeWorkBudget::default(),
            )
            .expect("the heads should be valid")
            .is_some()
        );
        assert_eq!(
            match_implementation_head(
                std::iter::once(parameter),
                &candidate,
                &conflicting,
                &mut InterfaceConstraintBudget::default(),
                &mut TypeWorkBudget::default(),
            ),
            Ok(None)
        );
    }

    #[test]
    fn one_way_head_matcher_rejects_invalid_checked_state() {
        let parameter = TypeVariableId::new(0);
        for (candidate, goal) in [
            (
                Type::Variable(parameter),
                Type::Inference(crate::types::InferenceVariableId::new(0)),
            ),
            (
                Type::Variable(parameter),
                Type::Forall(Box::new([]), Box::new(Type::Int)),
            ),
            (Type::Variable(TypeVariableId::new(1)), Type::Int),
        ] {
            assert_eq!(
                match_implementation_head(
                    std::iter::once(parameter),
                    &candidate,
                    &goal,
                    &mut InterfaceConstraintBudget::default(),
                    &mut TypeWorkBudget::default(),
                ),
                Err(HeadMatchFailure::InvalidState)
            );
        }
    }

    #[test]
    fn one_way_head_matcher_has_exact_constraint_and_type_clone_boundaries() {
        let parameter = TypeVariableId::new(0);
        let candidate = Type::Variable(parameter);
        let goal = Type::Function(Box::new(Type::Int), Box::new(Type::Bool));

        assert_eq!(
            match_implementation_head(
                std::iter::once(parameter),
                &candidate,
                &goal,
                &mut InterfaceConstraintBudget::with_limit(18),
                &mut TypeWorkBudget::with_limit(3),
            ),
            Err(HeadMatchFailure::ConstraintResource)
        );
        assert_eq!(
            match_implementation_head(
                std::iter::once(parameter),
                &candidate,
                &goal,
                &mut InterfaceConstraintBudget::with_limit(19),
                &mut TypeWorkBudget::with_limit(2),
            ),
            Err(HeadMatchFailure::TypeResource)
        );
        let substitutions = match_implementation_head(
            std::iter::once(parameter),
            &candidate,
            &goal,
            &mut InterfaceConstraintBudget::with_limit(19),
            &mut TypeWorkBudget::with_limit(3),
        )
        .expect("both exact budgets should fit")
        .expect("the candidate should match");
        assert_eq!(substitutions[0].argument(), &goal);
    }

    #[test]
    fn constraint_selection_reasons_have_stable_codes() {
        assert_eq!(
            InterfaceReason::Unsatisfied.to_string(),
            "constraint.unsatisfied"
        );
        assert_eq!(
            InterfaceReason::Ambiguous.to_string(),
            "constraint.ambiguous"
        );
        assert_eq!(InterfaceReason::Cycle.to_string(), "constraint.cycle");
    }

    #[test]
    fn flat_evidence_plan_and_deep_substitution_drop_on_a_small_stack() {
        std::thread::Builder::new()
            .stack_size(64 * 1024)
            .spawn(|| {
                let module = ModuleId::new(61);
                let interface = InterfaceId::new(module, 0);
                let implementation = ImplId::new(module, 0);
                let method = MethodId::new(interface, 0);
                let implementation_method = ImplMethodId::new(implementation, method);
                let parameter = TypeVariableId::resolved(module, 0);
                let requirement =
                    RequirementId::new(RequirementOwner::Global(BinderId::resolved(module, 0)), 0);
                let mut deep_type = Type::Unit;
                for _ in 0..20_000 {
                    deep_type = Type::Function(Box::new(Type::Unit), Box::new(deep_type));
                }
                let mut builder = EvidenceSelectionBuilder::new();
                let mut root = builder
                    .push_abstract(
                        requirement,
                        &[method],
                        &mut InterfaceConstraintBudget::default(),
                    )
                    .expect("the first node should fit");
                for _ in 0..20_000 {
                    root = builder
                        .push_abstract(
                            requirement,
                            &[method],
                            &mut InterfaceConstraintBudget::default(),
                        )
                        .expect("the flat node should fit");
                }
                let substitutions = match_implementation_head(
                    std::iter::once(parameter),
                    &Type::Variable(parameter),
                    &deep_type,
                    &mut InterfaceConstraintBudget::default(),
                    &mut TypeWorkBudget::default(),
                )
                .expect("the deep checked head should be valid")
                .expect("the candidate variable should bind the deep goal");
                discard_type_iteratively(deep_type);
                root = builder
                    .push_implementation(
                        implementation,
                        substitutions,
                        &[root],
                        &[implementation_method],
                        &mut InterfaceConstraintBudget::default(),
                    )
                    .expect("the implementation node should fit");
                let selection = builder.finish(root).expect("the root should exist");
                let clone = selection.clone();
                assert!(selection.shares_plan_with(&clone));
                drop(selection);
                drop(clone);
            })
            .expect("the small-stack evidence thread should start")
            .join()
            .expect("flat evidence and deep substitutions should drop iteratively");
    }

    fn abstract_selection(requirement: RequirementId) -> EvidenceSelection {
        let method = MethodId::new(InterfaceId::new(ModuleId::new(41), 0), 0);
        let mut builder = EvidenceSelectionBuilder::new();
        let root = builder
            .push_abstract(
                requirement,
                &[method],
                &mut InterfaceConstraintBudget::default(),
            )
            .expect("the abstract node should fit");
        builder.finish(root).expect("the root should exist")
    }

    #[test]
    fn constraint_type_traversal_accepts_its_exact_budget_and_rejects_the_next_unit() {
        let ty = Type::Function(Box::new(Type::Int), Box::new(Type::Bool));

        let mut short = InterfaceConstraintBudget::with_limit(5);
        assert_eq!(short.charge_type(&ty), Err(()));

        let mut exact = InterfaceConstraintBudget::with_limit(6);
        exact
            .charge_type(&ty)
            .expect("the exact traversal and worklist budget should fit");
        assert_eq!(exact.charge(1), Err(()));
    }

    #[test]
    fn overlap_unification_accepts_its_exact_budget_and_rejects_the_next_unit() {
        let parameter = TypeVariableId::new(0);
        let variable = Type::Variable(parameter);

        let mut short = InterfaceConstraintBudget::with_limit(9);
        assert_eq!(
            implementation_heads_overlap(
                std::iter::once(parameter),
                &variable,
                std::iter::empty(),
                &Type::Int,
                &mut short,
            ),
            Err(OverlapFailure::Resource)
        );

        let mut exact = InterfaceConstraintBudget::with_limit(10);
        assert_eq!(
            implementation_heads_overlap(
                std::iter::once(parameter),
                &variable,
                std::iter::empty(),
                &Type::Int,
                &mut exact,
            ),
            Ok(true)
        );
        assert_eq!(exact.charge(1), Err(()));
    }

    #[test]
    fn overlap_freshens_equal_raw_parameter_identities_per_side() {
        let parameter = TypeVariableId::new(0);
        let left = Type::Tuple(vec![Type::Variable(parameter), Type::Int].into_boxed_slice());
        let right = Type::Tuple(vec![Type::Bool, Type::Variable(parameter)].into_boxed_slice());

        let mut short = InterfaceConstraintBudget::with_limit(23);
        assert_eq!(
            implementation_heads_overlap(
                std::iter::once(parameter),
                &left,
                std::iter::once(parameter),
                &right,
                &mut short,
            ),
            Err(OverlapFailure::Resource)
        );

        let mut exact = InterfaceConstraintBudget::with_limit(24);
        assert_eq!(
            implementation_heads_overlap(
                std::iter::once(parameter),
                &left,
                std::iter::once(parameter),
                &right,
                &mut exact,
            ),
            Ok(true)
        );
        assert_eq!(exact.used(), 24);
        assert_eq!(exact.charge(1), Err(()));
    }

    #[test]
    fn overlap_preserves_repeated_variables_within_one_head() {
        let parameter = TypeVariableId::new(0);
        let left = Type::Tuple(
            vec![Type::Variable(parameter), Type::Variable(parameter)].into_boxed_slice(),
        );
        let right = Type::Tuple(vec![Type::Int, Type::Bool].into_boxed_slice());

        assert_eq!(
            implementation_heads_overlap(
                std::iter::once(parameter),
                &left,
                std::iter::empty(),
                &right,
                &mut InterfaceConstraintBudget::default(),
            ),
            Ok(false)
        );
    }

    #[test]
    fn overlap_rejects_unlisted_head_variables() {
        let variable = Type::Variable(TypeVariableId::new(0));

        assert_eq!(
            implementation_heads_overlap(
                std::iter::empty(),
                &variable,
                std::iter::empty(),
                &Type::Int,
                &mut InterfaceConstraintBudget::default(),
            ),
            Err(OverlapFailure::InvalidState)
        );
    }

    #[test]
    fn overlap_occurs_check_uses_fresh_side_keys() {
        let left_parameter = TypeVariableId::new(0);
        let right_parameter = TypeVariableId::new(0);
        let left = Type::Tuple(
            vec![
                Type::Variable(left_parameter),
                Type::Variable(left_parameter),
            ]
            .into_boxed_slice(),
        );
        let right = Type::Tuple(
            vec![
                Type::Variable(right_parameter),
                Type::Tuple(vec![Type::Variable(right_parameter), Type::Unit].into_boxed_slice()),
            ]
            .into_boxed_slice(),
        );

        assert_eq!(
            implementation_heads_overlap(
                std::iter::once(left_parameter),
                &left,
                std::iter::once(right_parameter),
                &right,
                &mut InterfaceConstraintBudget::default(),
            ),
            Ok(false)
        );
    }

    #[test]
    fn overlap_rejects_inference_and_forall_in_checked_heads() {
        for invalid in [
            Type::Inference(crate::types::InferenceVariableId::new(0)),
            Type::Forall(Box::new([]), Box::new(Type::Int)),
        ] {
            assert_eq!(
                implementation_heads_overlap(
                    std::iter::empty(),
                    &invalid,
                    std::iter::empty(),
                    &Type::Int,
                    &mut InterfaceConstraintBudget::default(),
                ),
                Err(OverlapFailure::InvalidState)
            );
        }
    }

    #[test]
    fn overlap_matching_is_stack_safe_for_deep_function_heads() {
        std::thread::Builder::new()
            .stack_size(64 * 1024)
            .spawn(|| {
                let nested = || {
                    let mut ty = Type::Unit;
                    for _ in 0..20_000 {
                        ty = Type::Function(Box::new(Type::Unit), Box::new(ty));
                    }
                    ty
                };
                let left = nested();
                let right = nested();
                assert_eq!(
                    implementation_heads_overlap(
                        std::iter::empty(),
                        &left,
                        std::iter::empty(),
                        &right,
                        &mut InterfaceConstraintBudget::default(),
                    ),
                    Ok(true)
                );
                discard_type_iteratively(left);
                discard_type_iteratively(right);
            })
            .expect("the small-stack overlap thread should start")
            .join()
            .expect("deep overlap matching and cleanup should remain iterative");
    }
}
