//! Stable typed identities for resolved interfaces and implementations.

use std::{
    collections::{HashMap, HashSet},
    fmt,
    sync::{Arc, OnceLock},
};

use crate::{
    kind::{
        CanonicalEnvironmentFailure, KindEnvironments, KindFailure, KindWorkLedger,
        canonical_body_free_environments, canonical_type_variable_kind,
    },
    module::ModuleId,
    resolved::{BinderId, ResolvedRegistry},
    source::{Origin, Span, discard_origin_iteratively},
    types::{
        Kind, NominalTypeId, Type, TypeVariableId, TypeWorkBudget, charge_kind_with_charge,
        clone_kinded_type_parameters_with_budget, clone_type_with_budget, discard_type_iteratively,
        same_kinded_type_parameters_with_charge, same_type,
    },
};

impl KindWorkLedger for InterfaceConstraintBudget {
    fn charge(&mut self, work: usize) -> Result<(), ()> {
        InterfaceConstraintBudget::charge(self, work)
    }
}

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
                Type::Tuple(elements) => {
                    self.charge(1)?;
                    pending.try_reserve(1).map_err(|_| ())?;
                    pending.push(Task::Sequence(elements.iter()));
                }
                Type::Application(function, argument) => {
                    self.charge(2)?;
                    pending.try_reserve(2).map_err(|_| ())?;
                    pending.push(Task::Type(argument));
                    pending.push(Task::Type(function));
                }
                Type::Function(domain, codomain) => {
                    self.charge(2)?;
                    pending.try_reserve(2).map_err(|_| ())?;
                    pending.push(Task::Type(codomain));
                    pending.push(Task::Type(domain));
                }
                Type::EffectfulFunction(domain, codomain) => {
                    let children = codomain.effect_argument_count().saturating_add(2);
                    self.charge(children)?;
                    pending.try_reserve(children).map_err(|_| ())?;
                    for argument in codomain.effect_arguments() {
                        pending.push(Task::Type(argument));
                    }
                    pending.push(Task::Type(&codomain.value));
                    pending.push(Task::Type(domain));
                }
                Type::Forall(parameters, body) => {
                    self.charge(parameters.len().saturating_add(1))?;
                    for (_, kind) in parameters {
                        charge_kind_with_charge(kind, || self.charge(1))?;
                    }
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

    /// Authenticates Kind equality with one fallible paired worklist. Each
    /// child is charged before the worklist can grow, so success consumes the
    /// same one-unit-per-node boundary as a single Kind traversal.
    fn charge_equal_kinds(&mut self, left: &Kind, right: &Kind) -> Result<bool, ()> {
        self.charge(1)?;
        let mut pending: Vec<(&Kind, &Kind)> = Vec::new();
        pending.try_reserve(1).map_err(|_| ())?;
        pending.push((left, right));
        while let Some((left, right)) = pending.pop() {
            match (left, right) {
                (Kind::Type, Kind::Type) => {}
                (
                    Kind::Arrow(left_domain, left_codomain),
                    Kind::Arrow(right_domain, right_codomain),
                ) => {
                    self.charge(1)?;
                    self.charge(1)?;
                    pending.try_reserve(2).map_err(|_| ())?;
                    pending.push((left_codomain, right_codomain));
                    pending.push((left_domain, right_domain));
                }
                _ => return Ok(false),
            }
        }
        Ok(true)
    }

    /// Authenticates exact equality during one already-required structural
    /// traversal. Successful work is identical to [`Self::charge_type`] for
    /// `left`; the paired worklist remains fallible and charges before growth.
    pub(crate) fn charge_equal_types(&mut self, left: &Type, right: &Type) -> Result<bool, ()> {
        enum Task<'a> {
            Compare(&'a Type, &'a Type),
            Sequence(std::iter::Zip<std::slice::Iter<'a, Type>, std::slice::Iter<'a, Type>>),
        }

        self.charge(1)?;
        let mut pending = Vec::new();
        pending.try_reserve(1).map_err(|_| ())?;
        pending.push(Task::Compare(left, right));
        while let Some(task) = pending.pop() {
            let Task::Compare(left, right) = task else {
                let Task::Sequence(mut remaining) = task else {
                    unreachable!()
                };
                if let Some((left, right)) = remaining.next() {
                    self.charge(2)?;
                    pending.try_reserve(2).map_err(|_| ())?;
                    pending.push(Task::Sequence(remaining));
                    pending.push(Task::Compare(left, right));
                }
                continue;
            };
            self.charge(1)?;
            match (left, right) {
                (Type::Int, Type::Int) | (Type::Bool, Type::Bool) | (Type::Unit, Type::Unit) => {}
                (Type::Nominal(left), Type::Nominal(right)) if left == right => {}
                (Type::Variable(left), Type::Variable(right)) if left == right => {}
                (Type::Inference(left), Type::Inference(right)) if left == right => {}
                (
                    Type::Application(left_function, left_argument),
                    Type::Application(right_function, right_argument),
                )
                | (
                    Type::Function(left_function, left_argument),
                    Type::Function(right_function, right_argument),
                ) => {
                    self.charge(2)?;
                    pending.try_reserve(2).map_err(|_| ())?;
                    pending.push(Task::Compare(left_argument, right_argument));
                    pending.push(Task::Compare(left_function, right_function));
                }
                (Type::Tuple(left), Type::Tuple(right)) if left.len() == right.len() => {
                    self.charge(1)?;
                    pending.try_reserve(1).map_err(|_| ())?;
                    pending.push(Task::Sequence(left.iter().zip(right.iter())));
                }
                (Type::Forall(left_parameters, left), Type::Forall(right_parameters, right))
                    if left_parameters.len() == right_parameters.len() =>
                {
                    for ((left_id, left_kind), (right_id, right_kind)) in
                        left_parameters.iter().zip(right_parameters)
                    {
                        self.charge(1)?;
                        if left_id != right_id || !self.charge_equal_kinds(left_kind, right_kind)? {
                            return Ok(false);
                        }
                    }
                    self.charge(1)?;
                    pending.try_reserve(1).map_err(|_| ())?;
                    pending.push(Task::Compare(left, right));
                }
                _ => return Ok(false),
            }
        }
        Ok(true)
    }
}

/// Checks the generic implementation prerequisite termination judgment.
///
/// Ground prerequisites are admitted. A prerequisite containing a rigid type
/// variable must be a strict syntactic subterm of the implementation head.
#[cfg(test)]
pub(crate) fn implementation_prerequisite_terminates(
    prerequisite: &Type,
    head: &Type,
    budget: &mut InterfaceConstraintBudget,
) -> Result<bool, ()> {
    if !type_contains_any_variable(prerequisite, budget)? {
        return Ok(true);
    }

    let mut pending = Vec::new();
    schedule_type_children(head, &mut pending, budget)?;
    while let Some(candidate) = pending.pop() {
        if same_type_with_constraint_budget(prerequisite, candidate, budget)? {
            return Ok(true);
        }
        schedule_type_children(candidate, &mut pending, budget)?;
    }
    Ok(false)
}

/// Checks a generic prerequisite against canonical selection-key tuples while
/// retaining full-application groundness as the earlier exemption.
pub(crate) fn implementation_prerequisite_selection_key_terminates(
    complete_prerequisite: &[&Type],
    prerequisite_key: &[&Type],
    head_key: &[&Type],
    budget: &mut InterfaceConstraintBudget,
) -> Result<bool, ()> {
    let mut ground = true;
    for argument in complete_prerequisite {
        if type_contains_any_variable(argument, budget)? {
            ground = false;
        }
    }
    if ground {
        return Ok(true);
    }
    if prerequisite_key.len() != head_key.len() {
        return Ok(false);
    }

    let mut any_strict = false;
    for (prerequisite, head) in prerequisite_key.iter().zip(head_key) {
        budget.charge(1)?;
        if same_type_with_constraint_budget(prerequisite, head, budget)? {
            continue;
        }
        let mut pending = Vec::new();
        schedule_type_children(head, &mut pending, budget)?;
        let mut strict = false;
        while let Some(candidate) = pending.pop() {
            if same_type_with_constraint_budget(prerequisite, candidate, budget)? {
                strict = true;
                break;
            }
            schedule_type_children(candidate, &mut pending, budget)?;
        }
        if !strict {
            return Ok(false);
        }
        any_strict = true;
    }
    Ok(any_strict)
}

fn type_contains_any_variable(
    root: &Type,
    budget: &mut InterfaceConstraintBudget,
) -> Result<bool, ()> {
    budget.charge(1)?;
    let mut pending = Vec::new();
    pending.try_reserve(1).map_err(|_| ())?;
    pending.push(root);
    while let Some(ty) = pending.pop() {
        budget.charge(1)?;
        match ty {
            Type::Variable(_) => return Ok(true),
            Type::Tuple(elements) => {
                budget.charge(elements.len())?;
                pending.try_reserve(elements.len()).map_err(|_| ())?;
                pending.extend(elements.iter().rev());
            }
            Type::Application(function, argument) => {
                budget.charge(2)?;
                pending.try_reserve(2).map_err(|_| ())?;
                pending.push(argument);
                pending.push(function);
            }
            Type::Function(domain, codomain) => {
                budget.charge(2)?;
                pending.try_reserve(2).map_err(|_| ())?;
                pending.push(codomain);
                pending.push(domain);
            }
            Type::EffectfulFunction(domain, codomain) => {
                if codomain.tail_variable().is_some() {
                    return Ok(true);
                }
                let children = codomain.effect_argument_count().saturating_add(2);
                budget.charge(children)?;
                pending.try_reserve(children).map_err(|_| ())?;
                codomain.extend_effect_arguments(&mut pending);
                pending.push(&codomain.value);
                pending.push(domain);
            }
            Type::Forall(parameters, body) => {
                budget.charge(parameters.len().saturating_add(1))?;
                for (_, kind) in parameters {
                    charge_kind_with_charge(kind, || budget.charge(1))?;
                }
                pending.try_reserve(1).map_err(|_| ())?;
                pending.push(body);
            }
            Type::Int | Type::Bool | Type::Unit | Type::Nominal(_) | Type::Inference(_) => {}
        }
    }
    Ok(false)
}

fn schedule_type_children<'a>(
    ty: &'a Type,
    pending: &mut Vec<&'a Type>,
    budget: &mut InterfaceConstraintBudget,
) -> Result<(), ()> {
    match ty {
        Type::Tuple(elements) => {
            budget.charge(elements.len())?;
            pending.try_reserve(elements.len()).map_err(|_| ())?;
            pending.extend(elements.iter().rev());
        }
        Type::Application(function, argument) => {
            budget.charge(2)?;
            pending.try_reserve(2).map_err(|_| ())?;
            pending.push(argument);
            pending.push(function);
        }
        Type::Function(domain, codomain) => {
            budget.charge(2)?;
            pending.try_reserve(2).map_err(|_| ())?;
            pending.push(codomain);
            pending.push(domain);
        }
        Type::EffectfulFunction(domain, codomain) => {
            let children = codomain.effect_argument_count().saturating_add(2);
            budget.charge(children)?;
            pending.try_reserve(children).map_err(|_| ())?;
            codomain.extend_effect_arguments(pending);
            pending.push(&codomain.value);
            pending.push(domain);
        }
        Type::Forall(parameters, body) => {
            budget.charge(parameters.len().saturating_add(1))?;
            for (_, kind) in parameters {
                charge_kind_with_charge(kind, || budget.charge(1))?;
            }
            pending.try_reserve(1).map_err(|_| ())?;
            pending.push(body);
        }
        Type::Int
        | Type::Bool
        | Type::Unit
        | Type::Nominal(_)
        | Type::Variable(_)
        | Type::Inference(_) => {}
    }
    Ok(())
}

pub(crate) fn same_type_with_constraint_budget(
    left: &Type,
    right: &Type,
    budget: &mut InterfaceConstraintBudget,
) -> Result<bool, ()> {
    same_type_with_constraint_budget_inner(left, right, budget, None)
}

#[derive(Debug, Default)]
pub(crate) struct MatchedNominalIdentities {
    seen: HashSet<NominalTypeId>,
    order: Vec<NominalTypeId>,
}

impl MatchedNominalIdentities {
    fn observe(
        &mut self,
        identity: NominalTypeId,
        budget: &mut InterfaceConstraintBudget,
    ) -> Result<(), ()> {
        if self.seen.contains(&identity) {
            return Ok(());
        }
        budget.charge(2)?;
        self.seen.try_reserve(1).map_err(|_| ())?;
        self.order.try_reserve(1).map_err(|_| ())?;
        self.seen.insert(identity);
        self.order.push(identity);
        Ok(())
    }

    pub(crate) fn identities(&self) -> &[NominalTypeId] {
        &self.order
    }
}

pub(crate) fn collect_type_nominal_identities_with_constraint_budget(
    root: &Type,
    budget: &mut InterfaceConstraintBudget,
    nominal_identities: &mut MatchedNominalIdentities,
) -> Result<(), ()> {
    budget.charge(1)?;
    let mut pending = Vec::new();
    pending.try_reserve(1).map_err(|_| ())?;
    pending.push(root);
    while let Some(ty) = pending.pop() {
        match ty {
            Type::Nominal(id) => nominal_identities.observe(*id, budget)?,
            Type::Application(function, argument) | Type::Function(function, argument) => {
                budget.charge(2)?;
                pending.try_reserve(2).map_err(|_| ())?;
                pending.push(argument);
                pending.push(function);
            }
            Type::EffectfulFunction(domain, codomain) => {
                let children = codomain.effect_argument_count().saturating_add(2);
                budget.charge(children)?;
                pending.try_reserve(children).map_err(|_| ())?;
                codomain.extend_effect_arguments(&mut pending);
                pending.push(&codomain.value);
                pending.push(domain);
            }
            Type::Tuple(elements) => {
                budget.charge(elements.len())?;
                pending.try_reserve(elements.len()).map_err(|_| ())?;
                pending.extend(elements.iter().rev());
            }
            Type::Forall(_, body) => {
                budget.charge(1)?;
                pending.try_reserve(1).map_err(|_| ())?;
                pending.push(body);
            }
            Type::Int | Type::Bool | Type::Unit | Type::Variable(_) | Type::Inference(_) => {}
        }
    }
    Ok(())
}

pub(crate) fn same_type_with_constraint_budget_observing_nominals(
    left: &Type,
    right: &Type,
    budget: &mut InterfaceConstraintBudget,
    nominal_identities: &mut MatchedNominalIdentities,
) -> Result<bool, ()> {
    same_type_with_constraint_budget_inner(left, right, budget, Some(nominal_identities))
}

fn same_type_with_constraint_budget_inner(
    left: &Type,
    right: &Type,
    budget: &mut InterfaceConstraintBudget,
    mut nominal_identities: Option<&mut MatchedNominalIdentities>,
) -> Result<bool, ()> {
    budget.charge(1)?;
    let mut pending = Vec::new();
    pending.try_reserve(1).map_err(|_| ())?;
    pending.push((left, right));
    while let Some((left, right)) = pending.pop() {
        budget.charge(1)?;
        match (left, right) {
            (Type::Int, Type::Int) | (Type::Bool, Type::Bool) | (Type::Unit, Type::Unit) => {}
            (Type::Nominal(left), Type::Nominal(right)) if left == right => {
                if let Some(nominal_identities) = nominal_identities.as_deref_mut() {
                    nominal_identities.observe(*left, budget)?;
                }
            }
            (Type::Variable(left), Type::Variable(right)) if left == right => {}
            (Type::Inference(left), Type::Inference(right)) if left == right => {}
            (
                Type::Application(left_function, left_argument),
                Type::Application(right_function, right_argument),
            ) => {
                budget.charge(2)?;
                pending.try_reserve(2).map_err(|_| ())?;
                pending.push((left_argument, right_argument));
                pending.push((left_function, right_function));
            }
            (Type::Forall(left_parameters, left), Type::Forall(right_parameters, right)) => {
                if !same_kinded_type_parameters_with_charge(
                    left_parameters,
                    right_parameters,
                    |work| budget.charge(work),
                )? {
                    return Ok(false);
                }
                budget.charge(1)?;
                pending.try_reserve(1).map_err(|_| ())?;
                pending.push((left, right));
            }
            (Type::Tuple(left), Type::Tuple(right)) if left.len() == right.len() => {
                budget.charge(left.len())?;
                pending.try_reserve(left.len()).map_err(|_| ())?;
                pending.extend(left.iter().zip(right).rev());
            }
            (
                Type::Function(left_domain, left_codomain),
                Type::Function(right_domain, right_codomain),
            ) => {
                budget.charge(2)?;
                pending.try_reserve(2).map_err(|_| ())?;
                pending.push((left_codomain, right_codomain));
                pending.push((left_domain, right_domain));
            }
            _ => return Ok(false),
        }
    }
    Ok(true)
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum OverlapFailure {
    InvalidState,
    Resource,
    TypeResource,
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

/// Source location and ledgers shared by one matching or overlap operation.
pub(crate) struct InterfaceOperationWork<'work> {
    span: Span,
    constraint_budget: &'work mut InterfaceConstraintBudget,
    type_budget: &'work mut TypeWorkBudget,
}

impl<'work> InterfaceOperationWork<'work> {
    pub(crate) const fn new(
        span: Span,
        constraint_budget: &'work mut InterfaceConstraintBudget,
        type_budget: &'work mut TypeWorkBudget,
    ) -> Self {
        Self {
            span,
            constraint_budget,
            type_budget,
        }
    }
}

/// Matches one implementation head against one already checked obligation.
///
/// The caller has already authenticated both complete heads at their source or
/// import boundary. This operation authenticates only each newly created
/// substitution against its defining binder kind. Only `candidate_parameters`
/// bind. Goal variables remain rigid, and inference variables or rank-1 schemes
/// on either side are invalid checked state.
#[cfg(test)]
pub(crate) fn match_implementation_head(
    registry: &ResolvedRegistry,
    candidate_parameters: &[TypeVariableId],
    candidate: &Type,
    goal: &Type,
    span: Span,
    constraint_budget: &mut InterfaceConstraintBudget,
    type_budget: &mut TypeWorkBudget,
) -> Result<Option<Box<[EvidenceSubstitution]>>, HeadMatchFailure> {
    let goal_environments = canonical_body_free_environments(
        registry,
        &[],
        &[goal],
        span,
        constraint_budget,
        type_budget,
    )
    .map_err(map_match_environment_failure)?;
    match_implementation_head_in_environment(
        registry,
        InterfaceOperationWork::new(span, constraint_budget, type_budget),
        &goal_environments,
        candidate_parameters,
        candidate,
        goal,
    )
}

/// Matches with a caller-owned environment for the complete rigid goal.
///
/// Evidence selection builds this once per obligation and reuses it across all
/// candidate inspections. The complete candidate and goal kinds remain a
/// checked-boundary precondition; only retained substitutions are synthesized.
#[cfg(test)]
pub(crate) fn match_implementation_head_in_environment(
    registry: &ResolvedRegistry,
    operation: InterfaceOperationWork<'_>,
    goal_environments: &KindEnvironments<'_>,
    candidate_parameters: &[TypeVariableId],
    candidate: &Type,
    goal: &Type,
) -> Result<Option<Box<[EvidenceSubstitution]>>, HeadMatchFailure> {
    match_implementation_application_head_in_environment(
        registry,
        operation,
        goal_environments,
        candidate_parameters,
        &[candidate],
        &[goal],
    )
}

pub(crate) fn match_implementation_application_head_in_environment(
    registry: &ResolvedRegistry,
    operation: InterfaceOperationWork<'_>,
    goal_environments: &KindEnvironments<'_>,
    candidate_parameters: &[TypeVariableId],
    candidate: &[&Type],
    goal: &[&Type],
) -> Result<Option<Box<[EvidenceSubstitution]>>, HeadMatchFailure> {
    match_implementation_application_head_with_goal_validation(
        registry,
        operation,
        goal_environments,
        candidate_parameters,
        candidate,
        goal,
        true,
    )
}

/// Capability for one exact goal vector whose complete roots have already
/// been authenticated against its canonical kind environments.
pub(crate) struct CanonicalImplementationGoal<'registry, 'goal> {
    environments: KindEnvironments<'registry>,
    roots: &'goal [&'goal Type],
}

/// Authenticates one exact goal vector and binds the roots to the resulting
/// canonical environments. Private fields prevent a later caller from pairing
/// those environments with a different goal.
pub(crate) fn authenticate_implementation_application_goal<'registry, 'goal>(
    registry: &'registry ResolvedRegistry,
    operation: InterfaceOperationWork<'_>,
    roots: &'goal [&'goal Type],
) -> Result<CanonicalImplementationGoal<'registry, 'goal>, HeadMatchFailure> {
    let InterfaceOperationWork {
        span,
        constraint_budget,
        type_budget,
    } = operation;
    let environments = canonical_body_free_environments(
        registry,
        &[],
        roots,
        span,
        constraint_budget,
        type_budget,
    )
    .map_err(map_match_environment_failure)?;
    Ok(CanonicalImplementationGoal {
        environments,
        roots,
    })
}

/// Matches one candidate against the exact goal roots bound into a canonical
/// goal capability.
pub(crate) fn match_implementation_application_head_against_canonical_goal(
    registry: &ResolvedRegistry,
    operation: InterfaceOperationWork<'_>,
    candidate_parameters: &[TypeVariableId],
    candidate: &[&Type],
    goal: &CanonicalImplementationGoal<'_, '_>,
) -> Result<Option<Box<[EvidenceSubstitution]>>, HeadMatchFailure> {
    match_implementation_application_head_with_goal_validation(
        registry,
        operation,
        &goal.environments,
        candidate_parameters,
        candidate,
        goal.roots,
        false,
    )
}

fn match_implementation_application_head_with_goal_validation(
    registry: &ResolvedRegistry,
    operation: InterfaceOperationWork<'_>,
    goal_environments: &KindEnvironments<'_>,
    candidate_parameters: &[TypeVariableId],
    candidate: &[&Type],
    goal: &[&Type],
    validate_goal: bool,
) -> Result<Option<Box<[EvidenceSubstitution]>>, HeadMatchFailure> {
    if candidate.len() != goal.len() {
        return Err(HeadMatchFailure::InvalidState);
    }
    let InterfaceOperationWork {
        span,
        constraint_budget,
        type_budget,
    } = operation;
    match_implementation_head_with(
        candidate_parameters.iter().copied(),
        candidate,
        goal,
        constraint_budget,
        type_budget,
        validate_goal,
        |parameter, binding, constraint_budget, _type_budget| {
            let expected =
                canonical_type_variable_kind(registry, parameter, span, constraint_budget)
                    .map_err(map_match_kind_failure)?;
            goal_environments
                .expect_body_free_exact_kind_with_ledger(binding, expected, span, constraint_budget)
                .map_err(map_match_kind_failure)
        },
    )
}

fn map_match_environment_failure(failure: CanonicalEnvironmentFailure) -> HeadMatchFailure {
    match failure {
        CanonicalEnvironmentFailure::ConstraintResource => HeadMatchFailure::ConstraintResource,
        CanonicalEnvironmentFailure::TypeResource => HeadMatchFailure::TypeResource,
        CanonicalEnvironmentFailure::InvalidState => HeadMatchFailure::InvalidState,
    }
}

fn map_match_kind_failure(failure: KindFailure) -> HeadMatchFailure {
    match failure {
        KindFailure::Resource(_) => HeadMatchFailure::ConstraintResource,
        KindFailure::Internal(_) | KindFailure::Source(_) => HeadMatchFailure::InvalidState,
    }
}

#[cfg(test)]
pub(crate) fn match_implementation_head_structurally<I>(
    candidate_parameters: I,
    candidate: &Type,
    goal: &Type,
    constraint_budget: &mut InterfaceConstraintBudget,
    type_budget: &mut TypeWorkBudget,
) -> Result<Option<Box<[EvidenceSubstitution]>>, HeadMatchFailure>
where
    I: ExactSizeIterator<Item = TypeVariableId>,
{
    match_implementation_head_with(
        candidate_parameters,
        &[candidate],
        &[goal],
        constraint_budget,
        type_budget,
        true,
        |_, _, _, _| Ok(()),
    )
}

fn match_implementation_head_with<I, F>(
    candidate_parameters: I,
    candidate: &[&Type],
    goal: &[&Type],
    constraint_budget: &mut InterfaceConstraintBudget,
    type_budget: &mut TypeWorkBudget,
    validate_goal: bool,
    mut authenticate_binding: F,
) -> Result<Option<Box<[EvidenceSubstitution]>>, HeadMatchFailure>
where
    I: ExactSizeIterator<Item = TypeVariableId>,
    F: FnMut(
        TypeVariableId,
        &Type,
        &mut InterfaceConstraintBudget,
        &mut TypeWorkBudget,
    ) -> Result<(), HeadMatchFailure>,
{
    if candidate.len() != goal.len() {
        return Err(HeadMatchFailure::InvalidState);
    }
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

    for candidate in candidate {
        validate_match_type(candidate, Some(&positions), constraint_budget)?;
    }
    if validate_goal {
        for goal in goal {
            validate_match_type(goal, None, constraint_budget)?;
        }
    }

    constraint_budget
        .charge(candidate.len())
        .map_err(|()| HeadMatchFailure::ConstraintResource)?;
    let mut pending = Vec::new();
    pending
        .try_reserve(candidate.len())
        .map_err(|_| HeadMatchFailure::ConstraintResource)?;
    pending.extend(candidate.iter().copied().zip(goal.iter().copied()).rev());
    let mut bindings = Vec::new();
    constraint_budget
        .charge(parameter_count)
        .map_err(|()| HeadMatchFailure::ConstraintResource)?;
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
                authenticate_binding(*variable, goal, constraint_budget, type_budget)?;
                bindings[position] = Some(goal);
            }
            continue;
        }
        match (candidate, goal) {
            (Type::Int, Type::Int) | (Type::Bool, Type::Bool) | (Type::Unit, Type::Unit) => {}
            (Type::Nominal(candidate), Type::Nominal(goal)) if candidate == goal => {}
            (
                Type::Application(candidate_function, candidate_argument),
                Type::Application(goal_function, goal_argument),
            ) => {
                constraint_budget
                    .charge(2)
                    .map_err(|()| HeadMatchFailure::ConstraintResource)?;
                pending
                    .try_reserve(2)
                    .map_err(|_| HeadMatchFailure::ConstraintResource)?;
                pending.push((candidate_argument, goal_argument));
                pending.push((candidate_function, goal_function));
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
    constraint_budget
        .charge(parameter_count)
        .map_err(|()| HeadMatchFailure::ConstraintResource)?;
    substitution
        .try_reserve(parameter_count)
        .map_err(|_| HeadMatchFailure::ConstraintResource)?;
    for (parameter, binding) in parameters.into_iter().zip(bindings) {
        let binding = binding.ok_or(HeadMatchFailure::InvalidState)?;
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
            Type::Tuple(elements) => {
                budget
                    .charge(elements.len())
                    .map_err(|()| HeadMatchFailure::ConstraintResource)?;
                pending
                    .try_reserve(elements.len())
                    .map_err(|_| HeadMatchFailure::ConstraintResource)?;
                pending.extend(elements.iter().rev());
            }
            Type::Application(function, argument) => {
                budget
                    .charge(2)
                    .map_err(|()| HeadMatchFailure::ConstraintResource)?;
                pending
                    .try_reserve(2)
                    .map_err(|_| HeadMatchFailure::ConstraintResource)?;
                pending.push(argument);
                pending.push(function);
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
            Type::EffectfulFunction(_, _) => return Err(HeadMatchFailure::InvalidState),
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
                Type::Application(left_function, left_argument),
                Type::Application(right_function, right_argument),
            ) => {
                budget
                    .charge(2)
                    .map_err(|()| HeadMatchFailure::ConstraintResource)?;
                pending
                    .try_reserve(2)
                    .map_err(|_| HeadMatchFailure::ConstraintResource)?;
                pending.push((left_argument, right_argument));
                pending.push((left_function, right_function));
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

/// Determines first-order overlap between two already checked heads.
///
/// Source/import validation authenticated the complete heads. This operation
/// independently freshens their binders and kind-authenticates only each new
/// unification solution before caching it.
#[cfg(test)]
pub(crate) fn implementation_heads_overlap(
    registry: &ResolvedRegistry,
    operation: InterfaceOperationWork<'_>,
    left_parameters: &[TypeVariableId],
    left: &Type,
    right_parameters: &[TypeVariableId],
    right: &Type,
) -> Result<bool, OverlapFailure> {
    implementation_application_heads_overlap(
        registry,
        operation,
        left_parameters,
        &[left],
        right_parameters,
        &[right],
    )
}

/// Determines first-order overlap between two complete ordered interface
/// applications while sharing one freshening substitution across positions.
pub(crate) fn implementation_application_heads_overlap(
    registry: &ResolvedRegistry,
    operation: InterfaceOperationWork<'_>,
    left_parameters: &[TypeVariableId],
    left: &[&Type],
    right_parameters: &[TypeVariableId],
    right: &[&Type],
) -> Result<bool, OverlapFailure> {
    if left.len() != right.len() {
        return Err(OverlapFailure::InvalidState);
    }
    let InterfaceOperationWork {
        span,
        constraint_budget,
        type_budget,
    } = operation;
    let root_count = left
        .len()
        .checked_add(right.len())
        .ok_or(OverlapFailure::Resource)?;
    constraint_budget
        .charge(root_count)
        .map_err(|()| OverlapFailure::Resource)?;
    let mut roots = Vec::new();
    roots
        .try_reserve(root_count)
        .map_err(|_| OverlapFailure::Resource)?;
    roots.extend(left.iter().copied());
    roots.extend(right.iter().copied());
    let environments = canonical_body_free_environments(
        registry,
        &[],
        &roots,
        span,
        constraint_budget,
        type_budget,
    )
    .map_err(map_overlap_environment_failure)?;

    implementation_heads_overlap_with(
        left_parameters.iter().copied(),
        left,
        right_parameters.iter().copied(),
        right,
        constraint_budget,
        |variable, value, budget| {
            let parameters = match variable.side {
                OverlapSide::Left => left_parameters,
                OverlapSide::Right => right_parameters,
            };
            let parameter = parameters
                .get(variable.parameter)
                .copied()
                .ok_or(OverlapFailure::InvalidState)?;
            let expected = canonical_type_variable_kind(registry, parameter, span, budget)
                .map_err(map_overlap_kind_failure)?;
            environments
                .expect_body_free_exact_kind_with_ledger(value.ty, expected, span, budget)
                .map_err(map_overlap_kind_failure)
        },
    )
}

fn map_overlap_environment_failure(failure: CanonicalEnvironmentFailure) -> OverlapFailure {
    match failure {
        CanonicalEnvironmentFailure::ConstraintResource => OverlapFailure::Resource,
        CanonicalEnvironmentFailure::TypeResource => OverlapFailure::TypeResource,
        CanonicalEnvironmentFailure::InvalidState => OverlapFailure::InvalidState,
    }
}

fn map_overlap_kind_failure(failure: KindFailure) -> OverlapFailure {
    match failure {
        KindFailure::Resource(_) => OverlapFailure::Resource,
        KindFailure::Internal(_) | KindFailure::Source(_) => OverlapFailure::InvalidState,
    }
}

/// Determines structural overlap after both heads and their declared binders
/// have already been independently kind-authenticated for the same interface
/// parameter kind.
#[cfg(test)]
pub(crate) fn implementation_heads_overlap_structurally<L, R>(
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
    implementation_heads_overlap_with(
        left_parameters,
        &[left],
        right_parameters,
        &[right],
        budget,
        |_, _, _| Ok(()),
    )
}

pub(crate) fn implementation_application_heads_overlap_structurally<L, R>(
    left_parameters: L,
    left: &[&Type],
    right_parameters: R,
    right: &[&Type],
    budget: &mut InterfaceConstraintBudget,
) -> Result<bool, OverlapFailure>
where
    L: ExactSizeIterator<Item = TypeVariableId>,
    R: ExactSizeIterator<Item = TypeVariableId>,
{
    if left.len() != right.len() {
        return Err(OverlapFailure::InvalidState);
    }
    implementation_heads_overlap_with(
        left_parameters,
        left,
        right_parameters,
        right,
        budget,
        |_, _, _| Ok(()),
    )
}

fn implementation_heads_overlap_with<L, R, F>(
    left_parameters: L,
    left: &[&Type],
    right_parameters: R,
    right: &[&Type],
    budget: &mut InterfaceConstraintBudget,
    mut authenticate_solution: F,
) -> Result<bool, OverlapFailure>
where
    L: ExactSizeIterator<Item = TypeVariableId>,
    R: ExactSizeIterator<Item = TypeVariableId>,
    F: FnMut(
        FreshOverlapVariable,
        OverlapHead<'_>,
        &mut InterfaceConstraintBudget,
    ) -> Result<(), OverlapFailure>,
{
    if left.len() != right.len() {
        return Err(OverlapFailure::InvalidState);
    }
    let left_positions = overlap_parameter_positions(left_parameters, budget)?;
    let right_positions = overlap_parameter_positions(right_parameters, budget)?;
    budget
        .charge(left.len())
        .map_err(|()| OverlapFailure::Resource)?;
    let mut pending = Vec::new();
    pending
        .try_reserve(left.len())
        .map_err(|_| OverlapFailure::Resource)?;
    pending.extend(left.iter().zip(right).rev().map(|(left, right)| {
        (
            OverlapHead {
                side: OverlapSide::Left,
                ty: left,
            },
            OverlapHead {
                side: OverlapSide::Right,
                ty: right,
            },
        )
    }));
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
            authenticate_solution(variable, value, budget)?;
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
                Type::Application(left_function, left_argument),
                Type::Application(right_function, right_argument),
            ) => {
                budget.charge(2).map_err(|()| OverlapFailure::Resource)?;
                pending
                    .try_reserve(2)
                    .map_err(|_| OverlapFailure::Resource)?;
                pending.push((
                    OverlapHead {
                        side: left.side,
                        ty: left_argument,
                    },
                    OverlapHead {
                        side: right.side,
                        ty: right_argument,
                    },
                ));
                pending.push((
                    OverlapHead {
                        side: left.side,
                        ty: left_function,
                    },
                    OverlapHead {
                        side: right.side,
                        ty: right_function,
                    },
                ));
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
            Type::Tuple(elements) => {
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
            Type::Application(function, argument) => {
                budget.charge(2).map_err(|()| OverlapFailure::Resource)?;
                pending
                    .try_reserve(2)
                    .map_err(|_| OverlapFailure::Resource)?;
                pending.push(OverlapHead {
                    side: head.side,
                    ty: argument,
                });
                pending.push(OverlapHead {
                    side: head.side,
                    ty: function,
                });
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
            Type::EffectfulFunction(_, _) => return Err(OverlapFailure::InvalidState),
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
    /// An interface application has a different arity from its declaration.
    ArgumentCount,
    /// An interface determination does not partition its parameters exactly once.
    DeterminationParameter,
    /// An interface method omits its parameter or introduces another type variable.
    MethodParameter,
    /// An interface method signature does not have a top-level function arrow.
    MethodNotFunction,
    /// One constrained global repeats an identity-equal requirement.
    DuplicateRequirement,
    /// A requirement mentions a type parameter absent from the value type.
    UndeterminedParameter,
    /// No abstract requirement or available implementation matches the obligation.
    Unsatisfied,
    /// The obligation remains undetermined when evidence selection must begin.
    Ambiguous,
    /// A determined source and the pending dependent tuple disagree.
    DeterminationConflict,
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
    /// A determined implementation dependent contains a variable absent from its key.
    ImplDeterminationCoverage,
    /// Two available implementation heads unify.
    ImplOverlap,
    /// Two available implementation heads share a key but disagree on dependents.
    ImplDeterminationConflict,
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
            Self::ArgumentCount => "interface.argument-count",
            Self::DeterminationParameter => "interface.determination-parameter",
            Self::MethodParameter => "interface.method-parameter",
            Self::MethodNotFunction => "interface.method-not-function",
            Self::DuplicateRequirement => "constraint.duplicate-requirement",
            Self::UndeterminedParameter => "constraint.undetermined-parameter",
            Self::Unsatisfied => "constraint.unsatisfied",
            Self::Ambiguous => "constraint.ambiguous",
            Self::DeterminationConflict => "constraint.determination-conflict",
            Self::Cycle => "constraint.cycle",
            Self::ConstraintPrivateInterface => "constraint.private-interface",
            Self::ImplPrivateInterface => "impl.private-interface",
            Self::ImplOrphan => "impl.orphan",
            Self::ImplVariableHead => "impl.variable-head",
            Self::ImplDeterminationCoverage => "impl.determination-coverage",
            Self::ImplOverlap => "impl.overlap",
            Self::ImplDeterminationConflict => "impl.determination-conflict",
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

/// One complete checked interface application in declaration argument order.
///
/// This compiler-private carrier is shared by checked requirements,
/// implementation heads, selected evidence, and independent authentication.
/// Its argument vector is never encoded as an Ash tuple type.
#[derive(Debug, Eq, PartialEq)]
#[cfg_attr(test, derive(Clone))]
pub(crate) struct InterfaceApplication {
    interface: InterfaceId,
    arguments: Box<[Type]>,
}

struct InterfaceArgumentBuffer(Vec<Type>);

impl InterfaceArgumentBuffer {
    fn into_boxed_slice(mut self) -> Box<[Type]> {
        std::mem::take(&mut self.0).into_boxed_slice()
    }
}

impl Drop for InterfaceArgumentBuffer {
    fn drop(&mut self) {
        while let Some(argument) = self.0.pop() {
            discard_type_iteratively(argument);
        }
    }
}

impl InterfaceApplication {
    pub(crate) const fn new(interface: InterfaceId, arguments: Box<[Type]>) -> Self {
        Self {
            interface,
            arguments,
        }
    }

    pub(crate) const fn interface(&self) -> InterfaceId {
        self.interface
    }

    pub(crate) const fn arguments(&self) -> &[Type] {
        &self.arguments
    }

    pub(crate) fn into_parts(mut self) -> (InterfaceId, Box<[Type]>) {
        (self.interface, std::mem::take(&mut self.arguments))
    }

    #[cfg(test)]
    pub(crate) fn arguments_mut_for_summary_test(&mut self) -> &mut Box<[Type]> {
        &mut self.arguments
    }

    pub(crate) fn clone_with_budget(&self, budget: &mut TypeWorkBudget) -> Result<Self, ()> {
        budget.charge(self.arguments.len())?;
        let mut arguments = InterfaceArgumentBuffer(Vec::new());
        arguments
            .0
            .try_reserve(self.arguments.len())
            .map_err(|_| ())?;
        for argument in &self.arguments {
            arguments.0.push(clone_type_with_budget(argument, budget)?);
        }
        Ok(Self::new(self.interface, arguments.into_boxed_slice()))
    }
}

impl Drop for InterfaceApplication {
    fn drop(&mut self) {
        for argument in std::mem::take(&mut self.arguments).into_vec() {
            discard_type_iteratively(argument);
        }
    }
}

/// One ordered implementation-head parameter substitution.
#[derive(Debug, Eq, PartialEq)]
pub struct EvidenceSubstitution {
    parameter: TypeVariableId,
    argument: Type,
}

impl EvidenceSubstitution {
    pub(crate) fn new(parameter: TypeVariableId, argument: Type) -> Self {
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
    application: InterfaceApplication,
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
    /// Returns the checked interface obligation authenticated by this selection.
    #[must_use]
    pub fn interface(&self) -> InterfaceId {
        self.plan.application.interface()
    }

    /// Returns the zonked checked obligation arguments in declaration order.
    #[must_use]
    pub fn arguments(&self) -> &[Type] {
        self.plan.application.arguments()
    }

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

    pub(crate) fn finish(
        self,
        root: EvidenceNodeId,
        application: InterfaceApplication,
    ) -> Result<EvidenceSelection, ()> {
        if root.0 >= self.nodes.len() {
            drop(application);
            return Err(());
        }
        Ok(EvidenceSelection {
            plan: Arc::new(EvidencePlan {
                application,
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

#[derive(Debug)]
struct FilledEvidenceSlot {
    checked_method: Option<MethodId>,
    checked_application: InterfaceApplication,
    method_arguments: Box<[Type]>,
    checked_value_type: Option<Type>,
    selection: EvidenceSelection,
}

impl Drop for FilledEvidenceSlot {
    fn drop(&mut self) {
        for argument in std::mem::take(&mut self.method_arguments).into_vec() {
            discard_type_iteratively(argument);
        }
        if let Some(ty) = self.checked_value_type.take() {
            discard_type_iteratively(ty);
        }
    }
}

/// Atomic checked-goal and evidence state owned by one constrained occurrence.
pub struct EvidenceSlot {
    filled: Arc<OnceLock<FilledEvidenceSlot>>,
}

impl EvidenceSlot {
    /// Creates one independently fillable empty evidence slot.
    #[must_use]
    pub fn empty() -> Self {
        Self {
            filled: Arc::new(OnceLock::new()),
        }
    }

    /// Returns the selection filled together with the checked goal, when available.
    #[must_use]
    pub fn selection(&self) -> Option<&EvidenceSelection> {
        self.filled.get().map(|filled| &filled.selection)
    }

    /// Returns the ordered inference-free method-local instantiation arguments.
    #[must_use]
    pub fn method_arguments(&self) -> &[Type] {
        self.filled
            .get()
            .map_or(&[], |filled| &filled.method_arguments)
    }

    pub(crate) fn filled(&self) -> Option<(&InterfaceApplication, &EvidenceSelection)> {
        let filled = self.filled.get()?;
        if filled.checked_method.is_some()
            || !filled.method_arguments.is_empty()
            || filled.checked_value_type.is_some()
        {
            return None;
        }
        Some((&filled.checked_application, &filled.selection))
    }

    pub(crate) fn filled_method(
        &self,
    ) -> Option<(
        MethodId,
        &InterfaceApplication,
        &[Type],
        &Type,
        &EvidenceSelection,
    )> {
        let filled = self.filled.get()?;
        Some((
            filled.checked_method?,
            &filled.checked_application,
            &filled.method_arguments,
            filled.checked_value_type.as_ref()?,
            &filled.selection,
        ))
    }

    pub(crate) fn storage_id(&self) -> usize {
        Arc::as_ptr(&self.filled) as usize
    }

    /// Returns a transient capability that fills this exact structural slot.
    pub(crate) fn handle(&self) -> EvidenceSlotHandle {
        EvidenceSlotHandle {
            filled: Arc::clone(&self.filled),
        }
    }

    #[cfg(test)]
    pub(crate) fn replace_selection_for_test(&mut self, replacement: EvidenceSelection) -> bool {
        let Some(filled) = Arc::get_mut(&mut self.filled).and_then(OnceLock::get_mut) else {
            return false;
        };
        filled.selection = replacement;
        true
    }

    #[cfg(test)]
    pub(crate) fn replace_method_arguments_for_test(&mut self, replacement: Box<[Type]>) -> bool {
        let Some(filled) = Arc::get_mut(&mut self.filled).and_then(OnceLock::get_mut) else {
            return false;
        };
        for argument in std::mem::replace(&mut filled.method_arguments, replacement).into_vec() {
            discard_type_iteratively(argument);
        }
        true
    }

    #[cfg(test)]
    pub(crate) fn replace_checked_value_type_for_test(&mut self, replacement: Type) -> bool {
        let Some(filled) = Arc::get_mut(&mut self.filled).and_then(OnceLock::get_mut) else {
            discard_type_iteratively(replacement);
            return false;
        };
        if let Some(previous) = filled.checked_value_type.replace(replacement) {
            discard_type_iteratively(previous);
        }
        true
    }

    #[cfg(test)]
    pub(crate) fn replace_checked_method_for_test(&mut self, replacement: MethodId) -> bool {
        let Some(filled) = Arc::get_mut(&mut self.filled).and_then(OnceLock::get_mut) else {
            return false;
        };
        filled.checked_method = Some(replacement);
        true
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
                filled: Arc::clone(&self.filled),
            },
            None => Self::empty(),
        }
    }
}

impl fmt::Debug for EvidenceSlot {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.filled.get() {
            Some(filled) => formatter.debug_tuple("Selected").field(filled).finish(),
            None => formatter.write_str("Empty"),
        }
    }
}

impl PartialEq for EvidenceSlot {
    fn eq(&self, other: &Self) -> bool {
        match (self.filled.get(), other.filled.get()) {
            (None, None) => true,
            (Some(left), Some(right)) => {
                left.checked_application == right.checked_application
                    && left.method_arguments.len() == right.method_arguments.len()
                    && left
                        .method_arguments
                        .iter()
                        .zip(&right.method_arguments)
                        .all(|(left, right)| same_type(left, right))
                    && match (&left.checked_value_type, &right.checked_value_type) {
                        (Some(left), Some(right)) => same_type(left, right),
                        (None, None) => true,
                        _ => false,
                    }
                    && left.checked_method == right.checked_method
                    && left.selection == right.selection
            }
            _ => false,
        }
    }
}

impl Eq for EvidenceSlot {}

/// Transient capability for atomically filling one exact occurrence's evidence slot.
#[derive(Clone, Debug)]
pub(crate) struct EvidenceSlotHandle {
    filled: Arc<OnceLock<FilledEvidenceSlot>>,
}

impl EvidenceSlotHandle {
    #[cfg(test)]
    pub(crate) fn selection(&self) -> Option<&EvidenceSelection> {
        self.filled.get().map(|filled| &filled.selection)
    }

    pub(crate) fn storage_id(&self) -> usize {
        Arc::as_ptr(&self.filled) as usize
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.filled.get().is_none()
    }

    pub(crate) fn fill(
        &self,
        checked_method: Option<MethodId>,
        checked_application: InterfaceApplication,
        method_arguments: Box<[Type]>,
        checked_value_type: Option<Type>,
        selection: EvidenceSelection,
    ) -> Result<(), ()> {
        self.filled
            .set(FilledEvidenceSlot {
                checked_method,
                checked_application,
                method_arguments,
                checked_value_type,
                selection,
            })
            .map_err(drop)
    }

    pub(crate) fn fill_preflighted(
        &self,
        checked_method: Option<MethodId>,
        checked_application: InterfaceApplication,
        method_arguments: Box<[Type]>,
        checked_value_type: Option<Type>,
        selection: EvidenceSelection,
    ) {
        assert!(
            self.fill(
                checked_method,
                checked_application,
                method_arguments,
                checked_value_type,
                selection,
            )
            .is_ok(),
            "a preflighted evidence occurrence must remain one-shot empty"
        );
    }
}

/// One admitted requirement in a checked constrained scheme.
#[derive(Debug, Eq, PartialEq)]
pub struct CheckedRequirement {
    /// Stable occurrence identity under its declaring owner.
    pub id: RequirementId,
    /// Complete checked application in declaration order.
    pub(crate) application: InterfaceApplication,
    /// Causal declaration provenance.
    pub origin: Origin,
    /// Complete source requirement span.
    pub span: Span,
}

impl Drop for CheckedRequirement {
    fn drop(&mut self) {
        discard_origin_iteratively(std::mem::replace(
            &mut self.origin,
            Origin::Source(self.span),
        ));
    }
}

impl CheckedRequirement {
    /// Returns the stable checked interface identity.
    #[must_use]
    pub const fn interface(&self) -> InterfaceId {
        self.application.interface()
    }

    /// Borrows the complete requirement arguments in declaration order.
    #[must_use]
    pub const fn arguments(&self) -> &[Type] {
        self.application.arguments()
    }

    pub(crate) const fn application(&self) -> &InterfaceApplication {
        &self.application
    }
}

/// A checked source scheme whose requirements remain outside ordinary types.
#[derive(Debug, Eq, PartialEq)]
pub struct ConstrainedScheme {
    /// Ordered outer rank-1 type parameters and their fixed kinds.
    pub type_parameters: Box<[(TypeVariableId, Kind)]>,
    /// Ordered explicit interface requirements.
    pub requirements: Box<[CheckedRequirement]>,
    /// Source value type without an enclosing `forall` node.
    pub(crate) value_type: Type,
}

/// One checked total determinant key in interface declaration coordinates.
///
/// The dependent complement is intentionally derived from the complete
/// parameter vector. This carrier does not retain the source edge, parameter
/// identities, or a redundant dependent-position vector.
#[derive(Debug, Eq, PartialEq)]
pub(crate) struct DeterminationKey {
    positions: Box<[usize]>,
}

impl DeterminationKey {
    pub(crate) fn new(positions: Box<[usize]>) -> Self {
        Self { positions }
    }

    pub(crate) const fn positions(&self) -> &[usize] {
        &self.positions
    }

    pub(crate) fn clone_with_budget(
        &self,
        budget: &mut InterfaceConstraintBudget,
    ) -> Result<Self, ()> {
        budget.charge(self.positions.len())?;
        let mut positions = Vec::new();
        positions
            .try_reserve_exact(self.positions.len())
            .map_err(|_| ())?;
        positions.extend_from_slice(&self.positions);
        Ok(Self::new(positions.into_boxed_slice()))
    }
}

/// Authentication token for one successfully checked local interface.
#[derive(Debug, Eq, PartialEq)]
pub struct CheckedInterface {
    /// Source-order index into the owning module's resolved interface list.
    pub source_index: usize,
    /// Stable checked interface identity.
    pub id: InterfaceId,
    /// Optional checked total determinant key in declaration coordinates.
    determination: Option<DeterminationKey>,
}

impl CheckedInterface {
    pub(crate) fn new(
        source_index: usize,
        id: InterfaceId,
        determination: Option<DeterminationKey>,
    ) -> Self {
        Self {
            source_index,
            id,
            determination,
        }
    }

    /// Returns the determinant declaration positions when this interface has a key.
    #[must_use]
    pub(crate) fn determinant_positions(&self) -> Option<&[usize]> {
        self.determination.as_ref().map(DeterminationKey::positions)
    }

    pub(crate) const fn determination(&self) -> Option<&DeterminationKey> {
        self.determination.as_ref()
    }

    #[cfg(test)]
    pub(crate) fn replace_determination_for_test(
        &mut self,
        determination: Option<DeterminationKey>,
    ) {
        self.determination = determination;
    }
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
    /// Complete checked implementation-head application.
    application: InterfaceApplication,
    /// Exact method mappings in interface declaration order.
    pub methods: Box<[CheckedImplMethod]>,
}

impl CheckedImplementation {
    pub(crate) const fn new(
        source_index: usize,
        id: ImplId,
        application: InterfaceApplication,
        methods: Box<[CheckedImplMethod]>,
    ) -> Self {
        Self {
            source_index,
            id,
            application,
            methods,
        }
    }

    /// Returns the stable implemented interface identity.
    #[must_use]
    pub const fn interface(&self) -> InterfaceId {
        self.application.interface()
    }

    /// Returns the complete ordered implementation-head arguments.
    #[must_use]
    pub fn arguments(&self) -> &[Type] {
        self.application.arguments()
    }

    pub(crate) const fn application(&self) -> &InterfaceApplication {
        &self.application
    }
}

impl ConstrainedScheme {
    /// Borrows the source value type without its outer rank-1 binders.
    #[must_use]
    pub const fn value_type(&self) -> &Type {
        &self.value_type
    }

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
        budget.charge(self.requirements.len())?;
        let type_parameters =
            clone_kinded_type_parameters_with_budget(&self.type_parameters, budget)?;
        let mut requirements = Vec::new();
        requirements
            .try_reserve(self.requirements.len())
            .map_err(|_| ())?;
        for requirement in &self.requirements {
            requirements.push(CheckedRequirement {
                id: requirement.id,
                application: requirement.application.clone_with_budget(budget)?,
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
    use crate::{
        module::ModuleId,
        resolved::{BinderId, ResolvedNominalType, ResolvedRegistry, ResolvedTypeVariable},
        source::{ByteRange, Origin, SourceFile},
        types::{IterativeTypeOwner, Kind, NominalTypeId, TypeVariableId},
    };

    #[test]
    fn determination_key_clone_charges_each_retained_position_before_publication() {
        let key = DeterminationKey::new(Box::new([0, 2]));

        let mut short = InterfaceConstraintBudget::with_limit(1);
        assert_eq!(key.clone_with_budget(&mut short), Err(()));
        assert_eq!(
            short.used(),
            0,
            "the key reserves its full charge atomically"
        );

        let mut exact = InterfaceConstraintBudget::with_limit(2);
        let cloned = key
            .clone_with_budget(&mut exact)
            .expect("the exact determinant-position boundary should fit");
        assert_eq!(cloned.positions(), [0, 2]);
        assert_eq!(exact.used(), 2);
    }

    #[test]
    fn rank1_type_binders_retain_their_fixed_kind() {
        let parameter = TypeVariableId::resolved(ModuleId::new(5), 7);
        let scheme = ConstrainedScheme::from_rank1_type(Type::Forall(
            Box::new([(parameter, Kind::Type)]),
            Box::new(Type::Variable(parameter)),
        ));

        let [(retained, kind)] = scheme.type_parameters.as_ref() else {
            panic!("the predecessor scheme should retain one canonical binder");
        };
        assert_eq!(*retained, parameter);
        assert_eq!(kind, &Kind::Type);
    }

    #[test]
    fn constrained_schemes_retain_row_kind_binders_and_occurrence_lacks() {
        let parameter = TypeVariableId::resolved(ModuleId::new(5), 8);
        let member = crate::types::EffectInstance::new(
            crate::types::EffectId::new(ModuleId::new(5), 0),
            Box::new([Type::Int]),
        );
        let scheme = ConstrainedScheme::from_rank1_type(Type::Forall(
            Box::new([(parameter, Kind::EffectRow)]),
            Box::new(Type::function_computation(
                Type::Unit,
                crate::types::ComputationType::new(
                    Type::Int,
                    crate::types::EffectRow::with_tail(
                        Box::new([member.clone()]),
                        crate::types::EffectRowVariable::rigid(parameter),
                        Box::new([member.clone()]),
                    ),
                ),
            )),
        ));
        let cloned = scheme
            .clone_with_budget(&mut TypeWorkBudget::default())
            .expect("the row-bearing constrained scheme should clone");

        assert!(matches!(
            cloned.type_parameters.as_ref(),
            [(identity, Kind::EffectRow)] if *identity == parameter
        ));
        let Type::EffectfulFunction(_, codomain) = cloned.value_type() else {
            panic!("the scheme should retain its latent computation row");
        };
        let tail = codomain
            .effects()
            .tail()
            .expect("the generalized row should remain open");
        assert_eq!(
            tail.variable(),
            crate::types::EffectRowVariable::rigid(parameter)
        );
        assert_eq!(tail.lacks(), &[member]);
    }

    #[test]
    fn constrained_scheme_clone_charges_binder_record_and_kind_nodes() {
        // One binder record, three Kind nodes, and one value-Type node.
        const WORK: usize = 5;
        let parameter = TypeVariableId::resolved(ModuleId::new(5), 9);
        let scheme = ConstrainedScheme {
            type_parameters: Box::new([(
                parameter,
                Kind::Arrow(Box::new(Kind::Type), Box::new(Kind::Type)),
            )]),
            requirements: Box::new([]),
            value_type: Type::Variable(parameter),
        };

        let mut short = TypeWorkBudget::with_limit(WORK - 1);
        assert_eq!(scheme.clone_with_budget(&mut short), Err(()));
        assert_eq!(short.used(), WORK - 1);

        let mut exact = TypeWorkBudget::with_limit(WORK);
        let cloned = scheme
            .clone_with_budget(&mut exact)
            .expect("the exact scheme-clone budget should succeed");
        assert_eq!(exact.used(), WORK);
        assert_eq!(cloned, scheme);
    }

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
            .fill(
                None,
                InterfaceApplication::new(selection.interface(), Box::new([Type::Int])),
                Box::new([]),
                None,
                selection.clone(),
            )
            .expect("the original empty slot should accept one selection");

        assert_eq!(slot.selection(), Some(&selection));
        assert_eq!(handle.selection(), Some(&selection));
        assert!(
            matches!(slot.filled(), Some((application, _)) if application.arguments() == [Type::Int])
        );
        assert!(clone.selection().is_none());
        assert!(
            handle
                .fill(
                    None,
                    InterfaceApplication::new(
                        InterfaceId::new(ModuleId::new(41), 0),
                        Box::new([Type::Bool]),
                    ),
                    Box::new([]),
                    None,
                    selection,
                )
                .is_err()
        );
        assert!(
            matches!(slot.filled(), Some((application, _)) if application.arguments() == [Type::Int])
        );
    }

    #[test]
    fn selected_evidence_slot_clones_share_the_flat_plan() {
        let slot = EvidenceSlot::empty();
        let selection = abstract_selection(RequirementId::new(
            RequirementOwner::Global(BinderId::resolved(ModuleId::new(43), 0)),
            0,
        ));
        slot.handle()
            .fill(
                None,
                InterfaceApplication::new(selection.interface(), Box::new([Type::Int])),
                Box::new([]),
                None,
                selection,
            )
            .expect("the empty slot should accept one selection");

        let clone = slot.clone();
        let original = slot.selection().expect("the original should be selected");
        let cloned = clone.selection().expect("the clone should be selected");

        assert!(
            matches!(slot.filled(), Some((application, _)) if application.arguments() == [Type::Int])
        );
        assert!(
            matches!(clone.filled(), Some((application, _)) if application.arguments() == [Type::Int])
        );
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
        let selection = builder
            .finish(
                root,
                InterfaceApplication::new(interface, Box::new([Type::Int])),
            )
            .expect("the root should be retained");
        assert_eq!(exact_budget.used(), 3);
        assert_eq!(exact_budget.charge(1), Err(()));
        assert_eq!(selection.interface(), interface);
        assert_eq!(selection.arguments(), &[Type::Int]);
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
        let selection = builder
            .finish(
                root,
                InterfaceApplication::new(interface, Box::new([Type::Int])),
            )
            .expect("the root should exist");
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

        let substitutions = match_implementation_head_structurally(
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
    fn one_way_head_matcher_rejects_a_wrong_kinded_goal_before_binding() {
        let module = ModuleId::new(60);
        let interface_parameter = TypeVariableId::resolved(module, 0);
        let candidate_parameter = TypeVariableId::resolved(module, 1);
        let source = SourceFile::new("higher-kinded-head-match.ash", "F")
            .expect("the matcher fixture source should fit");
        let span = source
            .span(ByteRange::new(0, 1).expect("the matcher fixture range should be ordered"))
            .expect("the matcher fixture span should fit");
        let constructor_kind = Kind::Arrow(Box::new(Kind::Type), Box::new(Kind::Type));
        let registry = ResolvedRegistry::new(Vec::new(), Vec::new())
            .with_additional_type_variables([
                ResolvedTypeVariable {
                    id: interface_parameter,
                    spelling: "I".into(),
                    kind: constructor_kind.clone(),
                    origin: Origin::Source(span),
                },
                ResolvedTypeVariable {
                    id: candidate_parameter,
                    spelling: "F".into(),
                    kind: constructor_kind,
                    origin: Origin::Source(span),
                },
            ]);

        assert_eq!(
            match_implementation_head(
                &registry,
                &[candidate_parameter],
                &Type::Variable(candidate_parameter),
                &Type::Int,
                span,
                &mut InterfaceConstraintBudget::default(),
                &mut TypeWorkBudget::default(),
            ),
            Err(HeadMatchFailure::InvalidState),
            "a Type-kinded goal must fail before a higher-kinded binding is retained"
        );
    }

    #[test]
    fn kind_preserving_head_match_has_exact_independent_resource_boundaries() {
        // Constraint work: 4 cells discover the rigid goal environment, 12
        // cells perform structural matching (including the retained binding
        // slot), and 8 cells authenticate the first binding (one canonical
        // binder lookup plus seven nominal Kind synthesis/comparison cells).
        const CONSTRAINT_WORK: usize = 4 + 12 + 8;
        // Type work: one XI record plus its three derived Kind nodes, and one
        // cloned nominal substitution argument.
        const TYPE_WORK: usize = 4 + 1;

        let module = ModuleId::new(62);
        let interface_parameter = TypeVariableId::resolved(module, 0);
        let candidate_parameter = TypeVariableId::resolved(module, 1);
        let nominal_parameter = TypeVariableId::resolved(module, 2);
        let option = NominalTypeId::new(module, 0);
        let source = SourceFile::new("kind-preserving-head-match.ash", "Option")
            .expect("the matcher fixture source should fit");
        let span = source
            .span(ByteRange::new(0, 6).expect("the matcher fixture range should be ordered"))
            .expect("the matcher fixture span should fit");
        let constructor_kind = Kind::Arrow(Box::new(Kind::Type), Box::new(Kind::Type));
        let registry = ResolvedRegistry::new(
            vec![ResolvedNominalType {
                id: option,
                spelling: "Option".into(),
                constructors: Box::new([]),
                origin: Origin::Source(span),
            }],
            Vec::new(),
        )
        .with_type_parameters(vec![(
            option,
            vec![ResolvedTypeVariable {
                id: nominal_parameter,
                spelling: "A".into(),
                kind: Kind::Type,
                origin: Origin::Source(span),
            }],
        )])
        .with_additional_type_variables([
            ResolvedTypeVariable {
                id: interface_parameter,
                spelling: "I".into(),
                kind: constructor_kind.clone(),
                origin: Origin::Source(span),
            },
            ResolvedTypeVariable {
                id: candidate_parameter,
                spelling: "F".into(),
                kind: constructor_kind,
                origin: Origin::Source(span),
            },
        ]);
        let candidate = Type::Variable(candidate_parameter);
        let goal = Type::Nominal(option);

        let mut measured_constraints = InterfaceConstraintBudget::default();
        let mut measured_types = TypeWorkBudget::default();
        let substitution = match_implementation_head(
            &registry,
            &[candidate_parameter],
            &candidate,
            &goal,
            span,
            &mut measured_constraints,
            &mut measured_types,
        )
        .expect("the measured matcher should fit")
        .expect("the constructor-kinded head should match");
        assert_eq!(measured_constraints.used(), CONSTRAINT_WORK);
        assert_eq!(measured_types.used(), TYPE_WORK);
        assert_eq!(substitution[0].argument(), &goal);

        let mut authentication_short = InterfaceConstraintBudget::with_limit(CONSTRAINT_WORK - 3);
        assert_eq!(
            match_implementation_head(
                &registry,
                &[candidate_parameter],
                &candidate,
                &goal,
                span,
                &mut authentication_short,
                &mut TypeWorkBudget::with_limit(TYPE_WORK),
            ),
            Err(HeadMatchFailure::ConstraintResource),
            "one missing first-binding authentication unit must not publish a substitution"
        );
        assert_eq!(authentication_short.used(), CONSTRAINT_WORK - 3);

        assert_eq!(
            match_implementation_head(
                &registry,
                &[candidate_parameter],
                &candidate,
                &goal,
                span,
                &mut InterfaceConstraintBudget::with_limit(CONSTRAINT_WORK - 1),
                &mut TypeWorkBudget::with_limit(TYPE_WORK),
            ),
            Err(HeadMatchFailure::ConstraintResource)
        );
        assert_eq!(
            match_implementation_head(
                &registry,
                &[candidate_parameter],
                &candidate,
                &goal,
                span,
                &mut InterfaceConstraintBudget::with_limit(CONSTRAINT_WORK),
                &mut TypeWorkBudget::with_limit(TYPE_WORK - 1),
            ),
            Err(HeadMatchFailure::TypeResource)
        );
        let exact = match_implementation_head(
            &registry,
            &[candidate_parameter],
            &candidate,
            &goal,
            span,
            &mut InterfaceConstraintBudget::with_limit(CONSTRAINT_WORK),
            &mut TypeWorkBudget::with_limit(TYPE_WORK),
        )
        .expect("the exact matcher budgets should fit")
        .expect("the exact matcher should publish one substitution");
        assert_eq!(exact.len(), 1);
        assert_eq!(exact[0].argument(), &goal);
    }

    #[test]
    fn late_second_binding_kind_failure_dismantles_deep_borrowed_state_on_a_small_stack() {
        const DEPTH: usize = 4_096;

        std::thread::Builder::new()
            .name("late-second-head-binding".into())
            .stack_size(256 * 1024)
            .spawn(|| {
                let module = ModuleId::new(63);
                let first = TypeVariableId::resolved(module, 0);
                let second = TypeVariableId::resolved(module, 1);
                let wrong = TypeVariableId::resolved(module, 2);
                let source = SourceFile::new("late-binding.ash", "F")
                    .expect("the late-binding source should fit");
                let span = source
                    .span(ByteRange::new(0, 1).expect("the late-binding range is ordered"))
                    .expect("the late-binding span should fit");
                let registry = ResolvedRegistry::new(Vec::new(), Vec::new())
                    .with_additional_type_variables([
                        ResolvedTypeVariable {
                            id: first,
                            spelling: "A".into(),
                            kind: Kind::Type,
                            origin: Origin::Source(span),
                        },
                        ResolvedTypeVariable {
                            id: second,
                            spelling: "F".into(),
                            kind: Kind::Arrow(Box::new(Kind::Type), Box::new(Kind::Type)),
                            origin: Origin::Source(span),
                        },
                        ResolvedTypeVariable {
                            id: wrong,
                            spelling: "Wrong".into(),
                            kind: Kind::Type,
                            origin: Origin::Source(span),
                        },
                    ]);
                let candidate = Type::Tuple(
                    vec![
                        Type::Variable(first),
                        Type::Application(Box::new(Type::Variable(second)), Box::new(Type::Int)),
                    ]
                    .into_boxed_slice(),
                );
                let mut deep = Type::Unit;
                for _ in 0..DEPTH {
                    deep = Type::Function(Box::new(Type::Unit), Box::new(deep));
                }
                let goal = IterativeTypeOwner::new(Type::Tuple(
                    vec![
                        deep,
                        Type::Application(Box::new(Type::Variable(wrong)), Box::new(Type::Int)),
                    ]
                    .into_boxed_slice(),
                ));

                assert_eq!(
                    match_implementation_head(
                        &registry,
                        &[first, second],
                        &candidate,
                        &goal,
                        span,
                        &mut InterfaceConstraintBudget::default(),
                        &mut TypeWorkBudget::default(),
                    ),
                    Err(HeadMatchFailure::InvalidState),
                    "the second binding must fail before the authenticated first binding is cloned"
                );
            })
            .expect("the late-binding worker should spawn")
            .join()
            .expect("late binding failure and deep borrowed teardown should remain iterative");
    }

    #[test]
    fn wide_binding_slots_fit_default_work_and_fail_atomically_one_unit_short() {
        const WIDTH: usize = 16_384;

        std::thread::Builder::new()
            .name("wide-head-match".into())
            .stack_size(256 * 1024)
            .spawn(|| {
                let module = ModuleId::new(67);
                let source = SourceFile::new("wide-head-match.ash", "F")
                    .expect("the wide matcher source should fit");
                let span = source
                    .span(ByteRange::new(0, 1).expect("the wide matcher range is ordered"))
                    .expect("the wide matcher span should fit");
                let parameters = (0..WIDTH)
                    .map(|index| TypeVariableId::resolved(module, index as u32))
                    .collect::<Vec<_>>();
                let registry = ResolvedRegistry::new(Vec::new(), Vec::new())
                    .with_additional_type_variables(parameters.iter().map(|parameter| {
                        ResolvedTypeVariable {
                            id: *parameter,
                            spelling: "A".into(),
                            kind: Kind::Type,
                            origin: Origin::Source(span),
                        }
                    }));
                let candidate = Type::Tuple(
                    parameters
                        .iter()
                        .copied()
                        .map(Type::Variable)
                        .collect::<Vec<_>>()
                        .into_boxed_slice(),
                );
                let goal = Type::Tuple(vec![Type::Int; WIDTH].into_boxed_slice());
                let mut measured_constraints = InterfaceConstraintBudget::default();
                let mut measured_types = TypeWorkBudget::default();
                let substitutions = match_implementation_head(
                    &registry,
                    &parameters,
                    &candidate,
                    &goal,
                    span,
                    &mut measured_constraints,
                    &mut measured_types,
                )
                .expect("the default budgets should admit the wide binding set")
                .expect("the wide checked heads should match");
                assert_eq!(substitutions.len(), WIDTH);
                let constraint_work = measured_constraints.used();
                let type_work = measured_types.used();
                assert_eq!(constraint_work, 18 * WIDTH + 8);
                assert_eq!(type_work, WIDTH);
                assert!(constraint_work < INTERFACE_CONSTRAINT_WORK_LIMIT);

                const PREFIX_BEFORE_SUBSTITUTION_RECORDS_PER_BINDING: usize = 15;
                const FIXED_PREFIX: usize = 8;
                let prefix_before_substitution_records =
                    PREFIX_BEFORE_SUBSTITUTION_RECORDS_PER_BINDING * WIDTH + FIXED_PREFIX;
                let mut record_short = InterfaceConstraintBudget::with_limit(
                    prefix_before_substitution_records + WIDTH - 1,
                );
                let mut record_short_types = TypeWorkBudget::with_limit(type_work);
                assert_eq!(
                    match_implementation_head(
                        &registry,
                        &parameters,
                        &candidate,
                        &goal,
                        span,
                        &mut record_short,
                        &mut record_short_types,
                    ),
                    Err(HeadMatchFailure::ConstraintResource),
                    "the binding-record charge must fail atomically before substitution allocation"
                );
                assert_eq!(record_short.used(), prefix_before_substitution_records);
                assert_eq!(record_short_types.used(), 0);

                let mut short = InterfaceConstraintBudget::with_limit(constraint_work - 1);
                let mut short_types = TypeWorkBudget::with_limit(type_work);
                assert_eq!(
                    match_implementation_head(
                        &registry,
                        &parameters,
                        &candidate,
                        &goal,
                        span,
                        &mut short,
                        &mut short_types,
                    ),
                    Err(HeadMatchFailure::ConstraintResource),
                    "one short wide run must not return a partial substitution"
                );
                assert_eq!(short.used(), constraint_work - 1);
                assert_eq!(short_types.used(), type_work - 1);
            })
            .expect("the wide matcher worker should spawn")
            .join()
            .expect("wide matcher success and failure should tear down on a small stack");
    }

    #[test]
    fn one_way_head_matching_visits_application_function_and_argument_separately() {
        let function_parameter = TypeVariableId::new(0);
        let argument_parameter = TypeVariableId::new(1);
        let function_candidate = Type::Application(
            Box::new(Type::Variable(function_parameter)),
            Box::new(Type::Bool),
        );
        let goal = Type::Application(Box::new(Type::Int), Box::new(Type::Bool));

        let function_substitution = match_implementation_head_structurally(
            std::iter::once(function_parameter),
            &function_candidate,
            &goal,
            &mut InterfaceConstraintBudget::default(),
            &mut TypeWorkBudget::default(),
        )
        .expect("the checked application heads should be valid")
        .expect("the function position should match");
        assert_eq!(function_substitution.len(), 1);
        assert_eq!(function_substitution[0].parameter(), function_parameter);
        assert_eq!(function_substitution[0].argument(), &Type::Int);

        let argument_candidate = Type::Application(
            Box::new(Type::Int),
            Box::new(Type::Variable(argument_parameter)),
        );
        let argument_substitution = match_implementation_head_structurally(
            std::iter::once(argument_parameter),
            &argument_candidate,
            &goal,
            &mut InterfaceConstraintBudget::default(),
            &mut TypeWorkBudget::default(),
        )
        .expect("the checked application heads should be valid")
        .expect("the argument position should match");
        assert_eq!(argument_substitution.len(), 1);
        assert_eq!(argument_substitution[0].parameter(), argument_parameter);
        assert_eq!(argument_substitution[0].argument(), &Type::Bool);
    }

    #[test]
    fn canonical_application_matching_uses_both_children_without_refining_the_rigid_goal() {
        let module = ModuleId::new(69);
        let function_parameter = TypeVariableId::resolved(module, 0);
        let argument_parameter = TypeVariableId::resolved(module, 1);
        let rigid_goal = TypeVariableId::resolved(module, 2);
        let option_parameter = TypeVariableId::resolved(module, 3);
        let other_parameter = TypeVariableId::resolved(module, 4);
        let option = NominalTypeId::new(module, 0);
        let other = NominalTypeId::new(module, 1);
        let source = SourceFile::new("canonical-application-match.ash", "Option Other")
            .expect("the canonical matcher source should fit");
        let span = source
            .span(ByteRange::new(0, 6).expect("the canonical matcher range is ordered"))
            .expect("the canonical matcher span should fit");
        let nominal = |id, spelling| ResolvedNominalType {
            id,
            spelling,
            constructors: Box::new([]),
            origin: Origin::Source(span),
        };
        let nominal_parameter = |id| ResolvedTypeVariable {
            id,
            spelling: "A".into(),
            kind: Kind::Type,
            origin: Origin::Source(span),
        };
        let registry = ResolvedRegistry::new(
            vec![
                nominal(option, "Option".into()),
                nominal(other, "Other".into()),
            ],
            Vec::new(),
        )
        .with_type_parameters(vec![
            (option, vec![nominal_parameter(option_parameter)]),
            (other, vec![nominal_parameter(other_parameter)]),
        ])
        .with_additional_type_variables([
            ResolvedTypeVariable {
                id: function_parameter,
                spelling: "F".into(),
                kind: Kind::Arrow(Box::new(Kind::Type), Box::new(Kind::Type)),
                origin: Origin::Source(span),
            },
            ResolvedTypeVariable {
                id: argument_parameter,
                spelling: "A".into(),
                kind: Kind::Type,
                origin: Origin::Source(span),
            },
            ResolvedTypeVariable {
                id: rigid_goal,
                spelling: "R".into(),
                kind: Kind::Type,
                origin: Origin::Source(span),
            },
        ]);
        let application =
            |function, argument| Type::Application(Box::new(function), Box::new(argument));

        let function_substitution = match_implementation_head(
            &registry,
            &[function_parameter],
            &application(Type::Variable(function_parameter), Type::Int),
            &application(Type::Nominal(option), Type::Int),
            span,
            &mut InterfaceConstraintBudget::default(),
            &mut TypeWorkBudget::default(),
        )
        .expect("the canonical function-child heads should be valid")
        .expect("the function child should determine the constructor binding");
        assert_eq!(function_substitution[0].argument(), &Type::Nominal(option));

        let rigid_application = application(Type::Nominal(option), Type::Variable(rigid_goal));
        let argument_substitution = match_implementation_head(
            &registry,
            &[argument_parameter],
            &application(Type::Nominal(option), Type::Variable(argument_parameter)),
            &rigid_application,
            span,
            &mut InterfaceConstraintBudget::default(),
            &mut TypeWorkBudget::default(),
        )
        .expect("the canonical argument-child heads should be valid")
        .expect("the argument child should bind to the rigid goal variable");
        assert_eq!(
            argument_substitution[0].argument(),
            &Type::Variable(rigid_goal)
        );
        assert_eq!(
            rigid_application,
            application(Type::Nominal(option), Type::Variable(rigid_goal))
        );

        assert_eq!(
            match_implementation_head(
                &registry,
                &[argument_parameter],
                &application(Type::Nominal(option), Type::Variable(argument_parameter)),
                &application(Type::Nominal(other), Type::Variable(rigid_goal)),
                span,
                &mut InterfaceConstraintBudget::default(),
                &mut TypeWorkBudget::default(),
            ),
            Ok(None),
            "distinct canonical function children must fail before argument binding"
        );
        assert_eq!(
            match_implementation_head(
                &registry,
                &[],
                &application(Type::Nominal(option), Type::Int),
                &application(Type::Nominal(option), Type::Bool),
                span,
                &mut InterfaceConstraintBudget::default(),
                &mut TypeWorkBudget::default(),
            ),
            Ok(None),
            "distinct canonical argument children must fail independently"
        );
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
            match_implementation_head_structurally(
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
            match_implementation_head_structurally(
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
                match_implementation_head_structurally(
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
    fn canonical_goal_capability_rejects_hidden_malformed_roots_and_matches_full_validation() {
        let module = ModuleId::new(70);
        let parameter = TypeVariableId::resolved(module, 0);
        let source = SourceFile::new("canonical-goal-capability.ash", "goal")
            .expect("the capability source should fit");
        let span = source
            .span(ByteRange::new(0, 4).expect("the capability range is ordered"))
            .expect("the capability span should fit");
        let registry = ResolvedRegistry::new(Vec::new(), Vec::new())
            .with_additional_type_variables([ResolvedTypeVariable {
                id: parameter,
                spelling: "A".into(),
                kind: Kind::Type,
                origin: Origin::Source(span),
            }]);
        let candidate = Type::Variable(parameter);
        let goal = Type::Int;
        let goal_roots = [&goal];
        let mut capability_constraints = InterfaceConstraintBudget::default();
        let mut capability_types = TypeWorkBudget::default();
        let canonical_goal = authenticate_implementation_application_goal(
            &registry,
            InterfaceOperationWork::new(span, &mut capability_constraints, &mut capability_types),
            &goal_roots,
        )
        .expect("the concrete goal should authenticate once");
        let capability_result = match_implementation_application_head_against_canonical_goal(
            &registry,
            InterfaceOperationWork::new(span, &mut capability_constraints, &mut capability_types),
            &[parameter],
            &[&candidate],
            &canonical_goal,
        );
        let full_result = match_implementation_head(
            &registry,
            &[parameter],
            &candidate,
            &goal,
            span,
            &mut InterfaceConstraintBudget::default(),
            &mut TypeWorkBudget::default(),
        );
        assert_eq!(capability_result, full_result);

        for invalid in [
            Type::Inference(crate::types::InferenceVariableId::new(0)),
            Type::Forall(Box::new([]), Box::new(Type::Int)),
        ] {
            let malformed = Type::Tuple(Box::new([Type::Bool, invalid]));
            let malformed_roots = [&malformed];
            assert!(matches!(
                authenticate_implementation_application_goal(
                    &registry,
                    InterfaceOperationWork::new(
                        span,
                        &mut InterfaceConstraintBudget::default(),
                        &mut TypeWorkBudget::default(),
                    ),
                    &malformed_roots,
                ),
                Err(HeadMatchFailure::InvalidState),
            ));
        }

        assert_eq!(
            match_implementation_head(
                &registry,
                &[],
                &Type::Bool,
                &Type::Int,
                span,
                &mut InterfaceConstraintBudget::default(),
                &mut TypeWorkBudget::default(),
            ),
            Ok(None),
            "the ordinary full-validation entry point remains available",
        );
    }

    #[test]
    fn one_way_head_matcher_has_exact_constraint_and_type_clone_boundaries() {
        let parameter = TypeVariableId::new(0);
        let candidate = Type::Variable(parameter);
        let goal = Type::Function(Box::new(Type::Int), Box::new(Type::Bool));

        assert_eq!(
            match_implementation_head_structurally(
                std::iter::once(parameter),
                &candidate,
                &goal,
                &mut InterfaceConstraintBudget::with_limit(19),
                &mut TypeWorkBudget::with_limit(3),
            ),
            Err(HeadMatchFailure::ConstraintResource)
        );
        assert_eq!(
            match_implementation_head_structurally(
                std::iter::once(parameter),
                &candidate,
                &goal,
                &mut InterfaceConstraintBudget::with_limit(20),
                &mut TypeWorkBudget::with_limit(2),
            ),
            Err(HeadMatchFailure::TypeResource)
        );
        let substitutions = match_implementation_head_structurally(
            std::iter::once(parameter),
            &candidate,
            &goal,
            &mut InterfaceConstraintBudget::with_limit(20),
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
                let substitutions = match_implementation_head_structurally(
                    std::iter::once(parameter),
                    &Type::Variable(parameter),
                    &deep_type,
                    &mut InterfaceConstraintBudget::default(),
                    &mut TypeWorkBudget::default(),
                )
                .expect("the deep checked head should be valid")
                .expect("the candidate variable should bind the deep goal");
                root = builder
                    .push_implementation(
                        implementation,
                        substitutions,
                        &[root],
                        &[implementation_method],
                        &mut InterfaceConstraintBudget::default(),
                    )
                    .expect("the implementation node should fit");
                let selection = builder
                    .finish(
                        root,
                        InterfaceApplication::new(interface, Box::new([deep_type])),
                    )
                    .expect("the root should exist");
                let clone = selection.clone();
                assert!(selection.shares_plan_with(&clone));
                let [selected_argument] = selection.arguments() else {
                    panic!("the unary fixture should retain one argument");
                };
                let checked_argument =
                    clone_type_with_budget(selected_argument, &mut TypeWorkBudget::default())
                        .expect("the checked occurrence argument should fit");
                let slot = EvidenceSlot::empty();
                slot.handle()
                    .fill(
                        None,
                        InterfaceApplication::new(interface, Box::new([checked_argument])),
                        Box::new([]),
                        None,
                        selection.clone(),
                    )
                    .expect("the deep checked evidence should fill atomically");
                let slot_clone = slot.clone();
                drop(selection);
                drop(clone);
                drop(slot);
                drop(slot_clone);
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
        builder
            .finish(
                root,
                InterfaceApplication::new(method.interface(), Box::new([Type::Int])),
            )
            .expect("the root should exist")
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
    fn constraint_type_equality_reuses_the_exact_traversal_boundary() {
        const EXACT_WORK: usize = 6;
        let left = Type::Function(Box::new(Type::Int), Box::new(Type::Bool));
        let equal = Type::Function(Box::new(Type::Int), Box::new(Type::Bool));
        let different = Type::Function(Box::new(Type::Int), Box::new(Type::Unit));

        let mut short = InterfaceConstraintBudget::with_limit(EXACT_WORK - 1);
        assert_eq!(short.charge_equal_types(&left, &equal), Err(()));
        assert_eq!(short.used(), EXACT_WORK - 1);

        for _ in 0..2 {
            let mut exact = InterfaceConstraintBudget::with_limit(EXACT_WORK);
            assert_eq!(exact.charge_equal_types(&left, &equal), Ok(true));
            assert_eq!(exact.used(), EXACT_WORK);
        }

        let mut mismatch = InterfaceConstraintBudget::with_limit(EXACT_WORK);
        assert_eq!(mismatch.charge_equal_types(&left, &different), Ok(false));
        assert_eq!(mismatch.used(), EXACT_WORK);
    }

    #[test]
    fn constraint_kind_and_structural_type_equality_have_exact_parity_and_retry() {
        const TUPLE_WORK: usize = 12;
        const FORALL_WORK: usize = 10;
        const KIND_WORK: usize = 5;

        let tuple = Type::Tuple(vec![Type::Int, Type::Bool, Type::Unit].into_boxed_slice());
        let equal_tuple = Type::Tuple(vec![Type::Int, Type::Bool, Type::Unit].into_boxed_slice());
        let different_tuple =
            Type::Tuple(vec![Type::Int, Type::Bool, Type::Bool].into_boxed_slice());
        let parameter = TypeVariableId::new(0);
        let nested_kind = Kind::Arrow(
            Box::new(Kind::Type),
            Box::new(Kind::Arrow(Box::new(Kind::Type), Box::new(Kind::Type))),
        );
        let different_kind = Kind::Arrow(Box::new(Kind::Type), Box::new(Kind::Type));
        let forall = Type::Forall(
            vec![(parameter, nested_kind.clone())].into_boxed_slice(),
            Box::new(Type::Unit),
        );
        let equal_forall = Type::Forall(
            vec![(parameter, nested_kind.clone())].into_boxed_slice(),
            Box::new(Type::Unit),
        );
        let different_forall = Type::Forall(
            vec![(parameter, different_kind.clone())].into_boxed_slice(),
            Box::new(Type::Unit),
        );

        for (left, right, exact_work) in [
            (&tuple, &equal_tuple, TUPLE_WORK),
            (&forall, &equal_forall, FORALL_WORK),
        ] {
            let mut traversal = InterfaceConstraintBudget::with_limit(exact_work);
            traversal
                .charge_type(left)
                .expect("the exact structural traversal must fit");
            assert_eq!(traversal.used(), exact_work);

            let mut short = InterfaceConstraintBudget::with_limit(exact_work - 1);
            assert_eq!(short.charge_equal_types(left, right), Err(()));
            assert_eq!(short.used(), exact_work - 1);
            for _ in 0..2 {
                let mut exact = InterfaceConstraintBudget::with_limit(exact_work);
                assert_eq!(exact.charge_equal_types(left, right), Ok(true));
                assert_eq!(exact.used(), exact_work);
            }
        }

        let mut mismatch = InterfaceConstraintBudget::with_limit(TUPLE_WORK);
        assert_eq!(
            mismatch.charge_equal_types(&tuple, &different_tuple),
            Ok(false)
        );
        assert_eq!(mismatch.used(), TUPLE_WORK);

        let mut forall_mismatch = InterfaceConstraintBudget::with_limit(6);
        assert_eq!(
            forall_mismatch.charge_equal_types(&forall, &different_forall),
            Ok(false)
        );
        assert_eq!(forall_mismatch.used(), 6);

        let mut kind_mismatch = InterfaceConstraintBudget::with_limit(3);
        assert_eq!(
            kind_mismatch.charge_equal_kinds(&nested_kind, &different_kind),
            Ok(false)
        );
        assert_eq!(kind_mismatch.used(), 3);

        let mut kind_short = InterfaceConstraintBudget::with_limit(KIND_WORK - 1);
        assert_eq!(
            kind_short.charge_equal_kinds(&nested_kind, &nested_kind),
            Err(())
        );
        assert_eq!(kind_short.used(), KIND_WORK - 1);
        for _ in 0..2 {
            let mut kind_exact = InterfaceConstraintBudget::with_limit(KIND_WORK);
            assert_eq!(
                kind_exact.charge_equal_kinds(&nested_kind, &nested_kind),
                Ok(true)
            );
            assert_eq!(kind_exact.used(), KIND_WORK);
        }
    }

    #[test]
    fn constraint_forall_kind_equality_is_fallible_and_small_stack_safe() {
        const DEPTH: usize = 32_768;
        const EXACT_WORK: usize = 2 * DEPTH + 6;

        std::thread::Builder::new()
            .name("deep-constraint-kind-equality".to_owned())
            .stack_size(64 * 1024)
            .spawn(|| {
                let deep_forall = || {
                    let mut kind = Kind::Type;
                    for _ in 0..DEPTH {
                        kind = Kind::Arrow(Box::new(Kind::Type), Box::new(kind));
                    }
                    IterativeTypeOwner::new(Type::Forall(
                        vec![(TypeVariableId::new(0), kind)].into_boxed_slice(),
                        Box::new(Type::Unit),
                    ))
                };
                let left = deep_forall();
                let right = deep_forall();

                let mut short = InterfaceConstraintBudget::with_limit(EXACT_WORK - 1);
                assert_eq!(short.charge_equal_types(&left, &right), Err(()));
                assert_eq!(short.used(), EXACT_WORK - 1);
                for _ in 0..2 {
                    let mut exact = InterfaceConstraintBudget::with_limit(EXACT_WORK);
                    assert_eq!(exact.charge_equal_types(&left, &right), Ok(true));
                    assert_eq!(exact.used(), EXACT_WORK);
                }
            })
            .expect("the deep paired-kind worker should spawn")
            .join()
            .expect("deep paired-kind comparison and teardown must remain stack-safe");
    }

    #[test]
    fn constraint_type_equality_is_exact_and_reusable_on_a_small_stack() {
        const DEPTH: usize = 32_768;
        const EXACT_WORK: usize = 4 * DEPTH + 2;

        std::thread::Builder::new()
            .name("deep-constraint-type-equality".to_owned())
            .stack_size(64 * 1024)
            .spawn(|| {
                let deep_type = || {
                    let mut ty = Type::Unit;
                    for _ in 0..DEPTH {
                        ty = Type::Function(Box::new(Type::Int), Box::new(ty));
                    }
                    IterativeTypeOwner::new(ty)
                };
                let left = deep_type();
                let right = deep_type();

                let mut short = InterfaceConstraintBudget::with_limit(EXACT_WORK - 1);
                assert_eq!(short.charge_equal_types(&left, &right), Err(()));
                assert_eq!(short.used(), EXACT_WORK - 1);

                for _ in 0..2 {
                    let mut exact = InterfaceConstraintBudget::with_limit(EXACT_WORK);
                    assert_eq!(exact.charge_equal_types(&left, &right), Ok(true));
                    assert_eq!(exact.used(), EXACT_WORK);
                }
            })
            .expect("the deep equality worker should spawn")
            .join()
            .expect("deep equality and teardown should remain stack-safe");
    }

    #[test]
    fn nominal_identity_collection_is_first_occurrence_ordered_and_exact_across_roots() {
        const FIRST_ROOT_TYPE_CELLS: usize = 9;
        const UNIQUE_IDENTITIES: usize = 3;
        const FIRST_ROOT_WORK: usize = FIRST_ROOT_TYPE_CELLS + 2 * UNIQUE_IDENTITIES;
        const SECOND_ROOT_TYPE_CELLS: usize = 3;
        const TOTAL_WORK: usize = FIRST_ROOT_WORK + SECOND_ROOT_TYPE_CELLS;

        let module = ModuleId::new(40_100);
        let first = NominalTypeId::new(module, 0);
        let second = NominalTypeId::new(module, 1);
        let third = NominalTypeId::new(module, 2);
        let first_root = Type::Tuple(
            vec![
                Type::Application(
                    Box::new(Type::Nominal(first)),
                    Box::new(Type::Nominal(second)),
                ),
                Type::Function(
                    Box::new(Type::Nominal(first)),
                    Box::new(Type::Tuple(
                        vec![Type::Nominal(third), Type::Int].into_boxed_slice(),
                    )),
                ),
            ]
            .into_boxed_slice(),
        );
        let second_root = Type::Application(
            Box::new(Type::Nominal(third)),
            Box::new(Type::Nominal(second)),
        );

        let mut short_identities = MatchedNominalIdentities::default();
        let mut short = InterfaceConstraintBudget::with_limit(FIRST_ROOT_WORK - 1);
        assert_eq!(
            collect_type_nominal_identities_with_constraint_budget(
                &first_root,
                &mut short,
                &mut short_identities,
            ),
            Err(())
        );
        assert_eq!(
            short.used(),
            FIRST_ROOT_WORK - 2,
            "the final first-seen nominal reserves both indexes atomically",
        );

        let mut identities = MatchedNominalIdentities::default();
        let mut exact = InterfaceConstraintBudget::with_limit(TOTAL_WORK);
        collect_type_nominal_identities_with_constraint_budget(
            &first_root,
            &mut exact,
            &mut identities,
        )
        .expect("the first root's V + 2U formula should fit exactly");
        assert_eq!(identities.identities(), [first, second, third]);
        collect_type_nominal_identities_with_constraint_budget(
            &second_root,
            &mut exact,
            &mut identities,
        )
        .expect("a later root should charge V but deduplicate every observed identity");
        assert_eq!(identities.identities(), [first, second, third]);
        assert_eq!(exact.used(), TOTAL_WORK);
        assert_eq!(exact.charge(1), Err(()));
    }

    #[test]
    fn nominal_identity_collection_is_stack_safe_at_depth_32768() {
        const DEPTH: usize = 32_768;
        const TYPE_CELLS: usize = 2 * DEPTH + 1;
        const EXACT_WORK: usize = TYPE_CELLS + 2;

        std::thread::Builder::new()
            .name("deep-nominal-identity-collection".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let identity = NominalTypeId::new(ModuleId::new(40_101), 0);
                let mut root = Type::Nominal(identity);
                for _ in 0..DEPTH {
                    root = Type::Application(Box::new(root), Box::new(Type::Nominal(identity)));
                }
                let root = IterativeTypeOwner::new(root);

                let mut short_identities = MatchedNominalIdentities::default();
                assert_eq!(
                    collect_type_nominal_identities_with_constraint_budget(
                        &root,
                        &mut InterfaceConstraintBudget::with_limit(EXACT_WORK - 1),
                        &mut short_identities,
                    ),
                    Err(())
                );

                let mut identities = MatchedNominalIdentities::default();
                let mut exact = InterfaceConstraintBudget::with_limit(EXACT_WORK);
                collect_type_nominal_identities_with_constraint_budget(
                    &root,
                    &mut exact,
                    &mut identities,
                )
                .expect("the exact deep V + 2U collector formula should fit");
                assert_eq!(exact.used(), EXACT_WORK);
                assert_eq!(identities.identities(), [identity]);
            })
            .expect("the deep nominal-identity worker should spawn")
            .join()
            .expect("accepted and rejected collectors must tear down on a small stack");
    }

    #[test]
    fn wide_nominal_identity_collection_precharges_every_tuple_task() {
        const WIDTH: usize = 32_768;
        // The Tuple root and each Unit element schedule exactly one visit; no
        // nominal identity is retained, so V + 2U = WIDTH + 1.
        const EXACT_WORK: usize = WIDTH + 1;

        std::thread::Builder::new()
            .name("wide-nominal-identity-collection".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let root = IterativeTypeOwner::new(Type::Tuple(
                    std::iter::repeat_n(Type::Unit, WIDTH)
                        .collect::<Vec<_>>()
                        .into_boxed_slice(),
                ));

                let mut short_identities = MatchedNominalIdentities::default();
                let mut short = InterfaceConstraintBudget::with_limit(EXACT_WORK - 1);
                assert_eq!(
                    collect_type_nominal_identities_with_constraint_budget(
                        &root,
                        &mut short,
                        &mut short_identities,
                    ),
                    Err(()),
                );
                assert_eq!(
                    short.used(),
                    1,
                    "the WIDTH-child scheduling charge must be atomic before reserve",
                );
                assert!(short_identities.identities().is_empty());

                let mut exact_identities = MatchedNominalIdentities::default();
                let mut exact = InterfaceConstraintBudget::with_limit(EXACT_WORK);
                collect_type_nominal_identities_with_constraint_budget(
                    &root,
                    &mut exact,
                    &mut exact_identities,
                )
                .expect("the exact wide V + 2U formula should fit");
                assert_eq!(exact.used(), EXACT_WORK);
                assert!(exact_identities.identities().is_empty());
            })
            .expect("the wide nominal-identity worker should start")
            .join()
            .expect("wide success, rejection, and teardown must fit 256 KiB");
    }

    #[test]
    fn overlap_unification_accepts_its_exact_budget_and_rejects_the_next_unit() {
        let parameter = TypeVariableId::new(0);
        let variable = Type::Variable(parameter);

        let mut short = InterfaceConstraintBudget::with_limit(9);
        assert_eq!(
            implementation_heads_overlap_structurally(
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
            implementation_heads_overlap_structurally(
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
    fn canonical_higher_kinded_overlap_is_first_order_and_exactly_bounded() {
        // Constraint work: two cells retain the aligned application roots, 16
        // discover one environment spanning both checked heads, and 26 perform
        // first-order unification plus one authenticated/cached F -> Option
        // solution. Complete heads are not redundantly synthesized here.
        const CONSTRAINT_WORK: usize = 2 + 16 + 26;
        // Type work: one left DELTA record and one right XI record retaining
        // the three nodes of Option's derived Type -> Type Kind.
        const TYPE_WORK: usize = 1 + 4;

        let module = ModuleId::new(64);
        let interface_parameter = TypeVariableId::resolved(module, 0);
        let left_parameter = TypeVariableId::resolved(module, 1);
        let nominal_parameter = TypeVariableId::resolved(module, 2);
        let option = NominalTypeId::new(module, 0);
        let source = SourceFile::new("higher-kinded-overlap.ash", "Option")
            .expect("the overlap fixture source should fit");
        let span = source
            .span(ByteRange::new(0, 6).expect("the overlap fixture range should be ordered"))
            .expect("the overlap fixture span should fit");
        let constructor_kind = Kind::Arrow(Box::new(Kind::Type), Box::new(Kind::Type));
        let registry = ResolvedRegistry::new(
            vec![ResolvedNominalType {
                id: option,
                spelling: "Option".into(),
                constructors: Box::new([]),
                origin: Origin::Source(span),
            }],
            Vec::new(),
        )
        .with_type_parameters(vec![(
            option,
            vec![ResolvedTypeVariable {
                id: nominal_parameter,
                spelling: "A".into(),
                kind: Kind::Type,
                origin: Origin::Source(span),
            }],
        )])
        .with_additional_type_variables([
            ResolvedTypeVariable {
                id: interface_parameter,
                spelling: "I".into(),
                kind: Kind::Type,
                origin: Origin::Source(span),
            },
            ResolvedTypeVariable {
                id: left_parameter,
                spelling: "F".into(),
                kind: constructor_kind,
                origin: Origin::Source(span),
            },
        ]);
        let left = Type::Application(
            Box::new(Type::Variable(left_parameter)),
            Box::new(Type::Int),
        );
        let overlapping = Type::Application(Box::new(Type::Nominal(option)), Box::new(Type::Int));
        let higher_order_only =
            Type::Application(Box::new(Type::Nominal(option)), Box::new(Type::Bool));

        let mut measured_constraints = InterfaceConstraintBudget::default();
        let mut measured_types = TypeWorkBudget::default();
        assert_eq!(
            implementation_heads_overlap(
                &registry,
                InterfaceOperationWork::new(span, &mut measured_constraints, &mut measured_types,),
                &[left_parameter],
                &left,
                &[],
                &overlapping,
            ),
            Ok(true)
        );
        assert_eq!(measured_constraints.used(), CONSTRAINT_WORK);
        assert_eq!(measured_types.used(), TYPE_WORK);

        let mut authentication_short = InterfaceConstraintBudget::with_limit(CONSTRAINT_WORK - 2);
        assert_eq!(
            implementation_heads_overlap(
                &registry,
                InterfaceOperationWork::new(
                    span,
                    &mut authentication_short,
                    &mut TypeWorkBudget::with_limit(TYPE_WORK),
                ),
                &[left_parameter],
                &left,
                &[],
                &overlapping,
            ),
            Err(OverlapFailure::Resource),
            "one missing solution-authentication unit must not cache a partial solution"
        );
        assert_eq!(authentication_short.used(), CONSTRAINT_WORK - 2);

        assert_eq!(
            implementation_heads_overlap(
                &registry,
                InterfaceOperationWork::new(
                    span,
                    &mut InterfaceConstraintBudget::with_limit(CONSTRAINT_WORK - 1),
                    &mut TypeWorkBudget::with_limit(TYPE_WORK),
                ),
                &[left_parameter],
                &left,
                &[],
                &overlapping,
            ),
            Err(OverlapFailure::Resource)
        );
        assert_eq!(
            implementation_heads_overlap(
                &registry,
                InterfaceOperationWork::new(
                    span,
                    &mut InterfaceConstraintBudget::with_limit(CONSTRAINT_WORK),
                    &mut TypeWorkBudget::with_limit(TYPE_WORK - 1),
                ),
                &[left_parameter],
                &left,
                &[],
                &overlapping,
            ),
            Err(OverlapFailure::TypeResource)
        );
        assert_eq!(
            implementation_heads_overlap(
                &registry,
                InterfaceOperationWork::new(
                    span,
                    &mut InterfaceConstraintBudget::default(),
                    &mut TypeWorkBudget::default(),
                ),
                &[left_parameter],
                &left,
                &[],
                &higher_order_only,
            ),
            Ok(false),
            "overlap remains first-order and does not invent a type lambda"
        );
    }

    #[test]
    fn deep_higher_kinded_head_match_has_exact_atomic_small_stack_boundaries() {
        const DEPTH: usize = 32_768;
        const KIND_NODES: usize = 2 * DEPTH + 1;
        const MATCH_CONSTRAINT_WORK: usize = 2 * KIND_NODES + 18;
        const MATCH_TYPE_WORK: usize = 2;

        std::thread::Builder::new()
            .name("deep-higher-kinded-head-match".into())
            .stack_size(256 * 1024)
            .spawn(|| {
                let deep_kind = |extra_result_arrow| {
                    let mut kind = if extra_result_arrow {
                        Kind::Arrow(Box::new(Kind::Type), Box::new(Kind::Type))
                    } else {
                        Kind::Type
                    };
                    for _ in 0..DEPTH {
                        kind = Kind::Arrow(Box::new(Kind::Type), Box::new(kind));
                    }
                    kind
                };
                let module = ModuleId::new(65);
                let candidate_parameter = TypeVariableId::resolved(module, 0);
                let accepted_goal = TypeVariableId::resolved(module, 1);
                let rejected_goal = TypeVariableId::resolved(module, 2);
                let source = SourceFile::new("deep-head-match.ash", "F")
                    .expect("the deep matcher source should fit");
                let span = source
                    .span(ByteRange::new(0, 1).expect("the deep matcher range is ordered"))
                    .expect("the deep matcher span should fit");
                let registry = ResolvedRegistry::new(Vec::new(), Vec::new())
                    .with_additional_type_variables([
                        ResolvedTypeVariable {
                            id: candidate_parameter,
                            spelling: "F".into(),
                            kind: deep_kind(false),
                            origin: Origin::Source(span),
                        },
                        ResolvedTypeVariable {
                            id: accepted_goal,
                            spelling: "G".into(),
                            kind: deep_kind(false),
                            origin: Origin::Source(span),
                        },
                        ResolvedTypeVariable {
                            id: rejected_goal,
                            spelling: "H".into(),
                            kind: deep_kind(true),
                            origin: Origin::Source(span),
                        },
                    ]);
                let candidate = Type::Variable(candidate_parameter);
                let accepted = Type::Variable(accepted_goal);
                let rejected = Type::Variable(rejected_goal);

                let mut short_constraints =
                    InterfaceConstraintBudget::with_limit(MATCH_CONSTRAINT_WORK - 1);
                let mut short_types = TypeWorkBudget::with_limit(MATCH_TYPE_WORK);
                assert_eq!(
                    match_implementation_head(
                        &registry,
                        &[candidate_parameter],
                        &candidate,
                        &accepted,
                        span,
                        &mut short_constraints,
                        &mut short_types,
                    ),
                    Err(HeadMatchFailure::ConstraintResource),
                    "one-short matching must return no partial substitution"
                );
                assert_eq!(short_constraints.used(), MATCH_CONSTRAINT_WORK - 1);
                assert_eq!(short_constraints.charge(1), Err(()));
                assert_eq!(
                    short_types.used(),
                    MATCH_TYPE_WORK - 1,
                    "the failed final constraint charge must precede substitution cloning"
                );

                // Reuse the same registry and heads after rejection. Matching
                // borrows them, and a failed operation publishes no state that
                // can affect this exact-budget retry.
                let mut constraint_work =
                    InterfaceConstraintBudget::with_limit(MATCH_CONSTRAINT_WORK);
                let mut type_work = TypeWorkBudget::with_limit(MATCH_TYPE_WORK);
                let substitutions = match_implementation_head(
                    &registry,
                    &[candidate_parameter],
                    &candidate,
                    &accepted,
                    span,
                    &mut constraint_work,
                    &mut type_work,
                )
                .expect("the default matcher budgets should admit the deep Kind")
                .expect("equal deep binder kinds should match");
                assert_eq!(substitutions.len(), 1);
                assert_eq!(substitutions[0].parameter(), candidate_parameter);
                assert_eq!(substitutions[0].argument(), &accepted);
                // Two complete deep-Kind traversals authenticate the binding;
                // the constant covers canonical lookup, environment discovery,
                // structural preflight/matching, binding-slot retention, and
                // substitution retention.
                assert_eq!(constraint_work.used(), MATCH_CONSTRAINT_WORK);
                assert_eq!(constraint_work.charge(1), Err(()));
                assert_eq!(type_work.used(), MATCH_TYPE_WORK);
                assert_eq!(type_work.charge(1), Err(()));

                assert_eq!(
                    match_implementation_head(
                        &registry,
                        &[candidate_parameter],
                        &candidate,
                        &rejected,
                        span,
                        &mut InterfaceConstraintBudget::default(),
                        &mut TypeWorkBudget::default(),
                    ),
                    Err(HeadMatchFailure::InvalidState),
                    "a mismatch at the deep Kind result must fail before substitution publication"
                );
            })
            .expect("the small-stack matcher worker should spawn")
            .join()
            .expect("deep matching, failure, and teardown should remain iterative");
    }

    #[test]
    fn deep_higher_kinded_overlap_has_exact_atomic_small_stack_boundaries() {
        const DEPTH: usize = 32_768;
        const KIND_NODES: usize = 2 * DEPTH + 1;
        // Two application-root cells precede the prior environment,
        // unification, and cached-solution work.
        const OVERLAP_CONSTRAINT_WORK: usize = 2 + 2 * KIND_NODES + 22;
        const OVERLAP_TYPE_WORK: usize = 2;

        std::thread::Builder::new()
            .name("deep-higher-kinded-overlap".into())
            .stack_size(256 * 1024)
            .spawn(|| {
                let deep_kind = |extra_result_arrow| {
                    let mut kind = if extra_result_arrow {
                        Kind::Arrow(Box::new(Kind::Type), Box::new(Kind::Type))
                    } else {
                        Kind::Type
                    };
                    for _ in 0..DEPTH {
                        kind = Kind::Arrow(Box::new(Kind::Type), Box::new(kind));
                    }
                    kind
                };
                let module = ModuleId::new(66);
                let left_parameter = TypeVariableId::resolved(module, 0);
                let accepted_right = TypeVariableId::resolved(module, 1);
                let rejected_right = TypeVariableId::resolved(module, 2);
                let source = SourceFile::new("deep-overlap.ash", "F")
                    .expect("the deep overlap source should fit");
                let span = source
                    .span(ByteRange::new(0, 1).expect("the deep overlap range is ordered"))
                    .expect("the deep overlap span should fit");
                let registry = ResolvedRegistry::new(Vec::new(), Vec::new())
                    .with_additional_type_variables([
                        ResolvedTypeVariable {
                            id: left_parameter,
                            spelling: "F".into(),
                            kind: deep_kind(false),
                            origin: Origin::Source(span),
                        },
                        ResolvedTypeVariable {
                            id: accepted_right,
                            spelling: "G".into(),
                            kind: deep_kind(false),
                            origin: Origin::Source(span),
                        },
                        ResolvedTypeVariable {
                            id: rejected_right,
                            spelling: "H".into(),
                            kind: deep_kind(true),
                            origin: Origin::Source(span),
                        },
                    ]);
                let left = Type::Variable(left_parameter);
                let accepted = Type::Variable(accepted_right);
                let rejected = Type::Variable(rejected_right);

                let mut short_constraints =
                    InterfaceConstraintBudget::with_limit(OVERLAP_CONSTRAINT_WORK - 1);
                let mut short_types = TypeWorkBudget::with_limit(OVERLAP_TYPE_WORK);
                assert_eq!(
                    implementation_heads_overlap(
                        &registry,
                        InterfaceOperationWork::new(
                            span,
                            &mut short_constraints,
                            &mut short_types,
                        ),
                        &[left_parameter],
                        &left,
                        &[accepted_right],
                        &accepted,
                    ),
                    Err(OverlapFailure::Resource),
                    "one-short overlap must fail before caching its solution"
                );
                assert_eq!(short_constraints.used(), OVERLAP_CONSTRAINT_WORK - 1);
                assert_eq!(short_constraints.charge(1), Err(()));
                assert_eq!(short_types.used(), OVERLAP_TYPE_WORK);

                // The overlap cache is operation-local. Reusing the same
                // immutable registry and heads after failure must therefore
                // produce the ordinary result at the exact boundary.
                let mut constraint_work =
                    InterfaceConstraintBudget::with_limit(OVERLAP_CONSTRAINT_WORK);
                let mut type_work = TypeWorkBudget::with_limit(OVERLAP_TYPE_WORK);
                assert_eq!(
                    implementation_heads_overlap(
                        &registry,
                        InterfaceOperationWork::new(span, &mut constraint_work, &mut type_work,),
                        &[left_parameter],
                        &left,
                        &[accepted_right],
                        &accepted,
                    ),
                    Ok(true),
                    "equal deep binder kinds should admit the cached solution"
                );
                // Two complete deep-Kind traversals authenticate the solution;
                // the constant covers both parameter maps, shared environment
                // discovery, unification/occurs work, and cached-solution storage.
                assert_eq!(constraint_work.used(), OVERLAP_CONSTRAINT_WORK);
                assert_eq!(constraint_work.charge(1), Err(()));
                assert_eq!(type_work.used(), OVERLAP_TYPE_WORK);
                assert_eq!(type_work.charge(1), Err(()));
                assert_eq!(
                    implementation_heads_overlap(
                        &registry,
                        InterfaceOperationWork::new(
                            span,
                            &mut InterfaceConstraintBudget::default(),
                            &mut TypeWorkBudget::default(),
                        ),
                        &[left_parameter],
                        &left,
                        &[rejected_right],
                        &rejected,
                    ),
                    Err(OverlapFailure::InvalidState),
                    "a mismatch at the deep Kind result must fail before solution caching"
                );
            })
            .expect("the small-stack overlap worker should spawn")
            .join()
            .expect("deep overlap, failure, and teardown should remain iterative");
    }

    #[test]
    fn overlap_freshens_equal_raw_parameter_identities_per_side() {
        let parameter = TypeVariableId::new(0);
        let left = Type::Tuple(vec![Type::Variable(parameter), Type::Int].into_boxed_slice());
        let right = Type::Tuple(vec![Type::Bool, Type::Variable(parameter)].into_boxed_slice());

        let mut short = InterfaceConstraintBudget::with_limit(23);
        assert_eq!(
            implementation_heads_overlap_structurally(
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
            implementation_heads_overlap_structurally(
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
    fn late_second_overlap_solution_kind_failure_does_not_publish_partial_state() {
        let module = ModuleId::new(68);
        let left_first = TypeVariableId::resolved(module, 0);
        let left_second = TypeVariableId::resolved(module, 1);
        let right_first = TypeVariableId::resolved(module, 2);
        let right_second = TypeVariableId::resolved(module, 3);
        let source = SourceFile::new("late-overlap-solution.ash", "F")
            .expect("the late overlap source should fit");
        let span = source
            .span(ByteRange::new(0, 1).expect("the late overlap range is ordered"))
            .expect("the late overlap span should fit");
        let constructor_kind = Kind::Arrow(Box::new(Kind::Type), Box::new(Kind::Type));
        let registry = ResolvedRegistry::new(Vec::new(), Vec::new())
            .with_additional_type_variables([
                ResolvedTypeVariable {
                    id: left_first,
                    spelling: "A".into(),
                    kind: Kind::Type,
                    origin: Origin::Source(span),
                },
                ResolvedTypeVariable {
                    id: left_second,
                    spelling: "F".into(),
                    kind: constructor_kind,
                    origin: Origin::Source(span),
                },
                ResolvedTypeVariable {
                    id: right_first,
                    spelling: "B".into(),
                    kind: Kind::Type,
                    origin: Origin::Source(span),
                },
                ResolvedTypeVariable {
                    id: right_second,
                    spelling: "Wrong".into(),
                    kind: Kind::Type,
                    origin: Origin::Source(span),
                },
            ]);
        let left = Type::Tuple(
            vec![
                Type::Variable(left_first),
                Type::Application(Box::new(Type::Variable(left_second)), Box::new(Type::Int)),
            ]
            .into_boxed_slice(),
        );
        let right = Type::Tuple(
            vec![
                Type::Variable(right_first),
                Type::Application(Box::new(Type::Variable(right_second)), Box::new(Type::Int)),
            ]
            .into_boxed_slice(),
        );

        assert_eq!(
            implementation_heads_overlap(
                &registry,
                InterfaceOperationWork::new(
                    span,
                    &mut InterfaceConstraintBudget::default(),
                    &mut TypeWorkBudget::default(),
                ),
                &[left_first, left_second],
                &left,
                &[right_first, right_second],
                &right,
            ),
            Err(OverlapFailure::InvalidState),
            "the second solution mismatch must discard the first authenticated cache entry"
        );
    }

    #[test]
    fn overlap_preserves_repeated_variables_within_one_head() {
        let parameter = TypeVariableId::new(0);
        let left = Type::Tuple(
            vec![Type::Variable(parameter), Type::Variable(parameter)].into_boxed_slice(),
        );
        let right = Type::Tuple(vec![Type::Int, Type::Bool].into_boxed_slice());

        assert_eq!(
            implementation_heads_overlap_structurally(
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
    fn overlap_considers_decisive_variables_in_each_application_position() {
        let left_function = TypeVariableId::new(0);
        let function_variable_head = Type::Application(
            Box::new(Type::Variable(left_function)),
            Box::new(Type::Bool),
        );
        let concrete = Type::Application(Box::new(Type::Int), Box::new(Type::Bool));

        assert_eq!(
            implementation_heads_overlap_structurally(
                std::iter::once(left_function),
                &function_variable_head,
                std::iter::empty(),
                &concrete,
                &mut InterfaceConstraintBudget::default(),
            ),
            Ok(true)
        );

        let right_argument = TypeVariableId::new(1);
        let argument_variable_head = Type::Application(
            Box::new(Type::Int),
            Box::new(Type::Variable(right_argument)),
        );
        assert_eq!(
            implementation_heads_overlap_structurally(
                std::iter::empty(),
                &concrete,
                std::iter::once(right_argument),
                &argument_variable_head,
                &mut InterfaceConstraintBudget::default(),
            ),
            Ok(true)
        );

        let rigid_function_mismatch = Type::Application(Box::new(Type::Bool), Box::new(Type::Bool));
        assert_eq!(
            implementation_heads_overlap_structurally(
                std::iter::empty(),
                &rigid_function_mismatch,
                std::iter::once(right_argument),
                &argument_variable_head,
                &mut InterfaceConstraintBudget::default(),
            ),
            Ok(false)
        );
        let rigid_argument_mismatch = Type::Application(Box::new(Type::Int), Box::new(Type::Int));
        assert_eq!(
            implementation_heads_overlap_structurally(
                std::iter::once(left_function),
                &function_variable_head,
                std::iter::empty(),
                &rigid_argument_mismatch,
                &mut InterfaceConstraintBudget::default(),
            ),
            Ok(false)
        );
    }

    #[test]
    fn strict_subterm_termination_visits_application_function_and_argument() {
        const FUNCTION_SUCCESS_WORK: usize = 14;
        const ARGUMENT_SUCCESS_WORK: usize = 14;
        const LATE_FAILURE_WORK: usize = 14;

        let module = ModuleId::new(70);
        let constructor = NominalTypeId::new(module, 0);
        let function_variable = TypeVariableId::new(0);
        let argument_variable = TypeVariableId::new(1);
        let absent_variable = TypeVariableId::new(2);
        let function_subterm = Type::Application(
            Box::new(Type::Nominal(constructor)),
            Box::new(Type::Variable(function_variable)),
        );
        let argument_subterm = Type::Variable(argument_variable);
        let head = Type::Application(
            Box::new(function_subterm.clone()),
            Box::new(argument_subterm.clone()),
        );

        let mut function_work = InterfaceConstraintBudget::default();
        assert_eq!(
            implementation_prerequisite_terminates(&function_subterm, &head, &mut function_work,),
            Ok(true)
        );
        assert_eq!(function_work.used(), FUNCTION_SUCCESS_WORK);
        assert_eq!(
            implementation_prerequisite_terminates(
                &function_subterm,
                &head,
                &mut InterfaceConstraintBudget::with_limit(FUNCTION_SUCCESS_WORK - 1),
            ),
            Err(())
        );
        assert_eq!(
            implementation_prerequisite_terminates(
                &function_subterm,
                &head,
                &mut InterfaceConstraintBudget::with_limit(FUNCTION_SUCCESS_WORK),
            ),
            Ok(true)
        );

        let mut argument_work = InterfaceConstraintBudget::default();
        assert_eq!(
            implementation_prerequisite_terminates(&argument_subterm, &head, &mut argument_work,),
            Ok(true)
        );
        assert_eq!(argument_work.used(), ARGUMENT_SUCCESS_WORK);
        assert_eq!(
            implementation_prerequisite_terminates(
                &argument_subterm,
                &head,
                &mut InterfaceConstraintBudget::with_limit(ARGUMENT_SUCCESS_WORK - 1),
            ),
            Err(())
        );
        assert_eq!(
            implementation_prerequisite_terminates(
                &argument_subterm,
                &head,
                &mut InterfaceConstraintBudget::with_limit(ARGUMENT_SUCCESS_WORK),
            ),
            Ok(true)
        );

        let mut late_failure_work = InterfaceConstraintBudget::default();
        assert_eq!(
            implementation_prerequisite_terminates(
                &Type::Variable(absent_variable),
                &head,
                &mut late_failure_work,
            ),
            Ok(false)
        );
        assert_eq!(late_failure_work.used(), LATE_FAILURE_WORK);
        assert_eq!(
            implementation_prerequisite_terminates(
                &Type::Variable(absent_variable),
                &head,
                &mut InterfaceConstraintBudget::with_limit(LATE_FAILURE_WORK - 1),
            ),
            Err(())
        );
        assert_eq!(
            implementation_prerequisite_terminates(
                &Type::Variable(absent_variable),
                &head,
                &mut InterfaceConstraintBudget::with_limit(LATE_FAILURE_WORK),
            ),
            Ok(false)
        );
    }

    #[test]
    fn strict_subterm_termination_handles_a_deep_canonical_application_spine_on_a_small_stack() {
        const DEPTH: usize = 32_768;

        std::thread::Builder::new()
            .name("deep-canonical-termination".into())
            .stack_size(256 * 1024)
            .spawn(|| {
                let module = ModuleId::new(71);
                let constructor = NominalTypeId::new(module, 0);
                let variable = TypeVariableId::resolved(module, 0);
                let mut head = Type::Nominal(constructor);
                for _ in 0..DEPTH {
                    head = Type::Application(Box::new(head), Box::new(Type::Variable(variable)));
                }
                let head = IterativeTypeOwner::new(head);
                let Type::Application(function_child, _) = &*head else {
                    panic!("the deep canonical head should be an application");
                };
                let mut work = InterfaceConstraintBudget::default();
                assert_eq!(
                    implementation_prerequisite_terminates(function_child, &head, &mut work),
                    Ok(true)
                );
                assert!(work.used() < INTERFACE_CONSTRAINT_WORK_LIMIT);
            })
            .expect("the deep termination worker should spawn")
            .join()
            .expect("deep termination traversal and teardown should remain iterative");
    }

    #[test]
    fn overlap_rejects_unlisted_head_variables() {
        let variable = Type::Variable(TypeVariableId::new(0));

        assert_eq!(
            implementation_heads_overlap_structurally(
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
            implementation_heads_overlap_structurally(
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
                implementation_heads_overlap_structurally(
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
                    implementation_heads_overlap_structurally(
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
