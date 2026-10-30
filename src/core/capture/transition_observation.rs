//! Focus-local, non-authoritative retirement/acknowledgement call observations.
//!
//! This draft deliberately does not propagate a CurrentLedger: the checked
//! call's provider/capture evidence and modeled normal-return correspondence
//! are still required. Its result may not escape the owning validator query.

use super::*;
use crate::core::ledger_checker::{
    acknowledgement::ConditionalAcknowledgementCall, closure::ConditionalClosureCall,
    retirement::ConditionalRetirementCall,
};

#[derive(Clone, Copy)]
pub(super) enum TransitionCall<'a, 'arena> {
    Retirement(&'a ConditionalRetirementCall<'arena>),
    Closure(&'a ConditionalClosureCall<'arena>),
    Acknowledgement(&'a ConditionalAcknowledgementCall<'arena>),
}

impl TransitionCall<'_, '_> {
    pub(super) fn argument_constructor(
        self,
        work: &mut TypeWorkBudget,
    ) -> Result<Option<(crate::core::NodeId, crate::core::NodeId)>, Failure> {
        let checked = match self {
            Self::Retirement(call) => call.checked_work_argument(work),
            Self::Closure(call) => call.checked_work_argument(work),
            Self::Acknowledgement(call) => call.checked_work_argument(work),
        };
        match checked {
            Ok(pair) => Ok(Some(pair)),
            Err(crate::core::ledger_checker::Rejection::Unsupported) => Ok(None),
            Err(crate::core::ledger_checker::Rejection::Exhausted) => Err(Failure::Resource),
        }
    }
    pub(super) fn same_definition(self, other: Self) -> bool {
        match (self, other) {
            (Self::Retirement(a), Self::Retirement(b)) => a.same_definition(b),
            (Self::Closure(a), Self::Closure(b)) => a.same_definition(b),
            (Self::Acknowledgement(a), Self::Acknowledgement(b)) => a.same_definition(b),
            _ => false,
        }
    }
    pub(super) fn provider_api(self) -> crate::module::ModuleId {
        match self {
            Self::Retirement(call) => call.provider_api(),
            Self::Closure(call) => call.provider_api(),
            Self::Acknowledgement(call) => call.provider_api(),
        }
    }

    pub(super) fn argument_binding(self) -> crate::core::NodeId {
        match self {
            Self::Retirement(call) => call.argument_binding(),
            Self::Closure(call) => call.argument_binding(),
            Self::Acknowledgement(call) => call.argument_binding(),
        }
    }

    pub(super) fn definition(self) -> DefinitionProvenance {
        match self {
            Self::Retirement(call) => DefinitionProvenance {
                query: call.definition_query(),
                binding: call.definition_binding(),
                context: call.definition_context(),
                closure: call.closure(),
            },
            Self::Closure(call) => DefinitionProvenance {
                query: call.definition_query(),
                binding: call.definition_binding(),
                context: call.definition_context(),
                closure: call.closure(),
            },
            Self::Acknowledgement(call) => DefinitionProvenance {
                query: call.definition_query(),
                binding: call.definition_binding(),
                context: call.definition_context(),
                closure: call.closure(),
            },
        }
    }

    pub(super) fn extend_roots(
        self,
        roots: &mut Vec<crate::core::NodeId>,
        work: &mut TypeWorkBudget,
    ) -> Result<(), Failure> {
        match self {
            Self::Retirement(call) => extend_charged(roots, &call.definition_roots(), work),
            Self::Closure(call) => extend_charged(roots, &call.definition_roots(), work),
            Self::Acknowledgement(call) => extend_charged(roots, &call.definition_roots(), work),
        }
    }

    pub(super) fn extend_helpers(
        self,
        helpers: &mut Vec<(crate::resolved::BinderId, crate::core::NodeId)>,
        work: &mut TypeWorkBudget,
    ) -> Result<(), Failure> {
        match self {
            Self::Retirement(call) => extend_charged(helpers, &call.linked_helpers(), work),
            Self::Closure(call) => extend_charged(helpers, &call.linked_helpers(), work),
            Self::Acknowledgement(call) => extend_charged(helpers, &call.linked_helpers(), work),
        }
    }
    pub(super) fn call(self) -> crate::core::NodeId {
        match self {
            Self::Retirement(call) => call.call(),
            Self::Closure(call) => call.call(),
            Self::Acknowledgement(call) => call.call(),
        }
    }

    pub(super) fn input(self) -> crate::core::NodeId {
        match self {
            Self::Retirement(call) => call.input(),
            Self::Closure(call) => call.input(),
            Self::Acknowledgement(call) => call.input(),
        }
    }

    pub(super) fn closure(self) -> crate::core::NodeId {
        match self {
            Self::Retirement(call) => call.closure(),
            Self::Closure(call) => call.closure(),
            Self::Acknowledgement(call) => call.closure(),
        }
    }
}

fn extend_charged<T: Copy>(
    destination: &mut Vec<T>,
    values: &[T],
    work: &mut TypeWorkBudget,
) -> Result<(), Failure> {
    charge(work, values.len())?;
    destination
        .try_reserve(values.len())
        .map_err(|_| Failure::Resource)?;
    destination.extend_from_slice(values);
    Ok(())
}

/// A conditional successor token in the exact owning focus. Its use still
/// requires the represented input and faithful primitive premises of the
/// reviewed transition mapping, full validation, and (for acknowledgement)
/// authenticated peer and nonnegative integer representation. It carries no
/// public currentness, peer authentication, or network permission.
pub(super) struct ConditionalTransitionSuccessor<'focus, 'graph> {
    _focus: &'focus control::CompletionFocus<'graph>,
    owner: crate::core::NodeId,
    side: u8,
    call_node: crate::core::NodeId,
    _call_state: usize,
    return_state: usize,
    _input: usize,
    returned: usize,
    caller_context: usize,
    pub(super) peer_authentication_required: bool,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ArgumentPhase {
    Ready,
    Preparing,
    Running(usize),
}

/// Follow only the checked Bind of a returned Ledger into the next nominated
/// call. The returned points remain conditional on the predecessor's premises.
fn advance_successor(
    scope: &NetworkNativeIdentityScope<'_>,
    graph: &SummaryGraph,
    focus: &control::CompletionFocus<'_>,
    current: &ProvisionalCurrentLedger<'_, '_, '_>,
    successor: &ConditionalTransitionSuccessor<'_, '_>,
    binding: crate::core::NodeId,
    next: TransitionCall<'_, '_>,
    index: &network_completion::MatchedReturnIndex<'_, '_>,
    outgoing: &[Vec<usize>],
    edges: &[(usize, usize, control::CompletionTransition)],
    details: &HashMap<usize, control::CompletionDetail>,
    work: &mut TypeWorkBudget,
) -> Result<Vec<(usize, usize, usize, crate::resolved::BinderId)>, Failure> {
    use crate::core::{EffectExprKind, PureComputation, PureExprKind};
    if !std::ptr::eq(successor._focus, focus)
        || successor.owner != current.owner
        || successor.side != current.side
        || binding.arena() != scope.arena()
        || next.input().arena() != scope.arena()
    {
        return Err(Failure::Invalid);
    }
    let Some(EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Bind(bind)))) = scope
        .nodes()
        .get(binding.index().map_err(|_| Failure::Invalid)?)
        .map(|node| &node.kind)
    else {
        return Err(Failure::Invalid);
    };
    let Some(EffectExprKind::Pure(PureExprKind::Variable(input))) = scope
        .nodes()
        .get(next.input().index().map_err(|_| Failure::Invalid)?)
        .map(|node| &node.kind)
    else {
        return Err(Failure::Invalid);
    };
    if bind.initializer() != successor.call_node || bind.binder().id() != input.binder() {
        return Err(Failure::Invalid);
    }
    let binding_code = binding
        .index()
        .map_err(|_| Failure::Invalid)?
        .checked_add(1)
        .ok_or(Failure::Resource)?;
    if focus
        .values()
        .original_control_node(binding_code, scope.nodes(), work)?
        != binding.index().map_err(|_| Failure::Invalid)?
    {
        return Err(Failure::Invalid);
    }
    let (binder, initializer) =
        focus
            .values()
            .existing_binding_ports(binding_code, successor.caller_context, work)?;
    if initializer != successor.returned {
        return Err(Failure::Invalid);
    }

    let argument_constructor = next.argument_constructor(work)?;
    if let Some(pair) = argument_constructor {
        charge(work, current.argument_constructors.len())?;
        if !current.argument_constructors.contains(&pair) {
            return Err(Failure::Invalid);
        }
    }
    let trace = focus.trace()?;
    let mut queue = VecDeque::new();
    let mut reached = HashSet::new();
    let mut traversed = HashSet::new();
    let mut points = Vec::new();
    let mut phases = HashMap::new();
    queue.try_reserve(1).map_err(|_| Failure::Resource)?;
    queue.push_back((successor.return_state, ArgumentPhase::Ready));
    while let Some((id, mut phase)) = queue.pop_front() {
        charge(work, 1)?;
        phases.try_reserve(1).map_err(|_| Failure::Resource)?;
        if phases.insert(id, phase).is_some_and(|old| old != phase) {
            return Err(Failure::Invalid);
        }
        reached.try_reserve(1).map_err(|_| Failure::Resource)?;
        if !reached.insert(id) {
            continue;
        }
        let before = trace.state(id, work)?;
        let saved_caller = current.query_caller_contexts.get(&id);
        if !matches!(phase, ArgumentPhase::Running(_))
            && (saved_caller.is_some_and(|saved| *saved != successor.caller_context)
                || (before.value_context != successor.caller_context
                    && saved_caller != Some(&successor.caller_context)))
        {
            return Err(Failure::Invalid);
        }
        if phase == ArgumentPhase::Ready
            && saved_caller.is_none()
            && source_position(scope, focus, before, next.call(), work)?
        {
            // An Apply's source coordinate also appears while its strict
            // operands are being evaluated. It is a usable call point only
            // after every outgoing alternative is the nominated actual call.
            let entries = outgoing.get(id).ok_or(Failure::Invalid)?;
            let mut calls = 0usize;
            for &number in entries {
                charge(work, 1)?;
                let &(from, to, transition) = edges.get(number).ok_or(Failure::Invalid)?;
                if from != id {
                    return Err(Failure::Invalid);
                }
                if let control::CompletionTransition::Call { target, .. } = transition {
                    if target != next.closure().index().map_err(|_| Failure::Invalid)? {
                        return Err(Failure::Invalid);
                    }
                    let _ = entered_call(graph, focus, from, to, transition, next.closure(), work)?;
                    calls = calls.checked_add(1).ok_or(Failure::Resource)?;
                }
            }
            if calls != 0 {
                if calls != entries.len() {
                    return Err(Failure::Invalid);
                }
                points.try_reserve(1).map_err(|_| Failure::Resource)?;
                points.push((id, binder, successor.caller_context, bind.binder().id()));
                continue;
            }
        }
        let control = graph
            .code
            .get(before.position.code)
            .ok_or(Failure::Invalid)?;
        let source =
            match focus
                .values()
                .original_control_node(before.position.code, scope.nodes(), work)
            {
                Ok(source) => Some(source),
                Err(Failure::Invalid) => None,
                Err(other) => return Err(other),
            };
        if let Some(source) = source {
            let is_closure = matches!(
                scope.nodes().get(source).map(|node| &node.kind),
                Some(EffectExprKind::Pure(PureExprKind::Value(
                    crate::core::PureValue::Function(_)
                ))) | Some(EffectExprKind::Operation(
                    crate::core::EffectOperation::RegionClosure(_)
                ))
            );
            if is_closure {
                let expected = argument_constructor
                    .is_some_and(|(_, closure)| closure.index().ok() == Some(source));
                if !expected || matches!(phase, ArgumentPhase::Running(_)) || saved_caller.is_some()
                {
                    return Err(Failure::Invalid);
                }
                phase = ArgumentPhase::Preparing;
            }
        }
        let region =
            matches!(control, control::Control::Request(request) if request.region_service);
        let original = if region {
            Some(
                checked_region_source(
                    scope,
                    graph,
                    focus,
                    before.position.code,
                    &current.checked_nodes,
                    work,
                )?
                .ok_or(Failure::Invalid)?,
            )
        } else {
            None
        };
        match control {
            control::Control::Request(request)
                if !request.region_service && !current.verified_query_requests.contains(&id) =>
            {
                return Err(Failure::Invalid);
            }
            control::Control::Resume { .. } if !current.verified_query_resumes.contains(&id) => {
                return Err(Failure::Invalid);
            }
            control::Control::NetworkEvent { .. }
            | control::Control::Unavailable
            | control::Control::WorkerInputStart { .. }
            | control::Control::WorkerInputDone { .. }
            | control::Control::Handler { .. }
            | control::Control::Cleanup { .. }
            | control::Control::Resource { .. }
            | control::Control::Registration { .. }
            | control::Control::NativeInterpret { .. }
            | control::Control::RetainedRoot { .. }
            | control::Control::Retain { .. }
            | control::Control::Continue { .. }
            | control::Control::Discard { .. } => return Err(Failure::Invalid),
            _ => {}
        }
        let entries = outgoing.get(id).ok_or(Failure::Invalid)?;
        if entries.is_empty() {
            return Err(Failure::Invalid);
        }
        for &number in entries {
            charge(work, 1)?;
            let &(from, to, transition) = edges.get(number).ok_or(Failure::Invalid)?;
            if from != id {
                return Err(Failure::Invalid);
            }
            if let Some(original) = original {
                let control::CompletionTransition::Detail(detail) = transition else {
                    return Err(Failure::Invalid);
                };
                checked_body_region_return(
                    scope,
                    graph,
                    focus,
                    before,
                    trace.state(to, work)?,
                    *details.get(&detail).ok_or(Failure::Invalid)?,
                    &current.query_origins,
                    &current.checked_nodes,
                    original,
                    next.provider_api(),
                    work,
                )?;
            }
            let mut next_phase = phase;
            if matches!(transition, control::CompletionTransition::Call { .. }) {
                let Some((call, closure)) = argument_constructor else {
                    return Err(Failure::Invalid);
                };
                if phase != ArgumentPhase::Preparing
                    || before.value_context != successor.caller_context
                    || !source_position(scope, focus, before, call, work)?
                {
                    return Err(Failure::Invalid);
                }
                let witness = entered_call(graph, focus, from, to, transition, closure, work)?;
                authenticate_body_call(
                    scope,
                    graph,
                    focus,
                    from,
                    to,
                    transition,
                    &current.body_calls,
                    &current.body_closures,
                    &current.helpers,
                    &current.closure_origins,
                    &current.query_origins,
                    work,
                )?;
                next_phase = ArgumentPhase::Running(witness);
            }
            if let (
                ArgumentPhase::Running(witness),
                control::CompletionTransition::Detail(detail),
            ) = (phase, transition)
            {
                let returned = match details.get(&detail) {
                    Some(control::CompletionDetail::Return(edge)) => Some((*edge, false)),
                    Some(control::CompletionDetail::NativeReturn {
                        boundary: None,
                        edge: Some(edge),
                        ..
                    }) if region => Some((*edge, true)),
                    _ => None,
                };
                if let Some((edge, native)) = returned {
                    if matches!(edge.frame, control::Frame::CallReturn { witness: actual, .. } if actual == witness)
                    {
                        let (call, closure) = argument_constructor.ok_or(Failure::Invalid)?;
                        let matched = matched_source_return(
                            scope, focus, index, from, to, edge, native, call, closure, work,
                        )?
                        .ok_or(Failure::Invalid)?;
                        if matched.caller_value_context != successor.caller_context {
                            return Err(Failure::Invalid);
                        }
                        next_phase = ArgumentPhase::Ready;
                    }
                }
            }
            traversed.try_reserve(1).map_err(|_| Failure::Resource)?;
            traversed.insert(number);
            queue.try_reserve(1).map_err(|_| Failure::Resource)?;
            queue.push_back((to, next_phase));
        }
    }
    if points.is_empty() {
        return Err(Failure::Invalid);
    }
    // This conservative intersection also refuses cycles and joins whose
    // other incoming paths have not carried the same predecessor token.
    for (number, &(from, to, _)) in edges.iter().enumerate() {
        charge(work, 1)?;
        if reached.contains(&to) && to != successor.return_state && !traversed.contains(&number) {
            return Err(Failure::Invalid);
        }
        if traversed.contains(&number) && (!reached.contains(&from) || !reached.contains(&to)) {
            return Err(Failure::Invalid);
        }
    }
    // Fail closed on cycles: every noninitial state must have an earlier
    // topological predecessor. The bounded sort does not assume termination.
    let mut indegree = HashMap::new();
    charge(work, reached.len())?;
    indegree
        .try_reserve(reached.len())
        .map_err(|_| Failure::Resource)?;
    for &id in &reached {
        indegree.insert(id, 0usize);
    }
    for &number in &traversed {
        charge(work, 1)?;
        let &(_, to, _) = edges.get(number).ok_or(Failure::Invalid)?;
        let degree = indegree.get_mut(&to).ok_or(Failure::Invalid)?;
        *degree = degree.checked_add(1).ok_or(Failure::Resource)?;
    }
    let mut ready = VecDeque::new();
    ready
        .try_reserve(indegree.len())
        .map_err(|_| Failure::Resource)?;
    for (&id, &degree) in &indegree {
        if degree == 0 {
            ready.push_back(id);
        }
    }
    let mut removed = 0usize;
    while let Some(id) = ready.pop_front() {
        charge(work, 1)?;
        removed = removed.checked_add(1).ok_or(Failure::Resource)?;
        for &number in outgoing.get(id).ok_or(Failure::Invalid)? {
            charge(work, 1)?;
            if !traversed.contains(&number) {
                continue;
            }
            let &(_, to, _) = edges.get(number).ok_or(Failure::Invalid)?;
            let degree = indegree.get_mut(&to).ok_or(Failure::Invalid)?;
            *degree = degree.checked_sub(1).ok_or(Failure::Invalid)?;
            if *degree == 0 {
                ready.push_back(to);
            }
        }
    }
    if removed != reached.len() {
        return Err(Failure::Invalid);
    }
    charge(
        work,
        reached
            .capacity()
            .checked_add(traversed.capacity())
            .and_then(|n| n.checked_add(queue.capacity()))
            .and_then(|n| n.checked_add(indegree.capacity()))
            .and_then(|n| n.checked_add(ready.capacity()))
            .and_then(|n| n.checked_add(points.capacity()))
            .and_then(|n| n.checked_add(phases.capacity()))
            .ok_or(Failure::Resource)?,
    )?;
    Ok(points)
}

pub(super) fn observe_transition_calls<'focus, 'graph>(
    scope: &NetworkNativeIdentityScope<'_>,
    graph: &SummaryGraph,
    focus: &'focus control::CompletionFocus<'graph>,
    current: &ProvisionalCurrentLedger<'focus, 'graph, '_>,
    nominated: TransitionCall<'_, '_>,
    side: u8,
    previous: Option<(&ConditionalTransitionSuccessor<'_, '_>, crate::core::NodeId)>,
    work: &mut TypeWorkBudget,
) -> Result<Vec<ConditionalTransitionSuccessor<'focus, 'graph>>, Failure> {
    if !std::ptr::eq(current._focus, focus)
        || current.owner != scope.owner()
        || current.side != side
        || scope.entry(usize::from(side)).is_none()
    {
        return Err(Failure::Invalid);
    }
    charge(work, current.transition_calls.len())?;
    if !current
        .transition_calls
        .contains(&(nominated.call(), nominated.closure()))
    {
        return Err(Failure::Invalid);
    }
    if [nominated.call(), nominated.input(), nominated.closure()]
        .iter()
        .any(|node| node.arena() != scope.arena())
    {
        return Err(Failure::Invalid);
    }
    let trace = focus.trace()?;
    let index = network_completion::MatchedReturnIndex::new(focus, work)?;
    let edges = trace.indexed_edges(work)?;
    let mut outgoing = Vec::new();
    charge(work, index.states().len())?;
    outgoing
        .try_reserve_exact(index.states().len())
        .map_err(|_| Failure::Resource)?;
    outgoing.resize_with(index.states().len(), Vec::new);
    for (number, &(from, to, _)) in edges.iter().enumerate() {
        charge(work, 1)?;
        if to >= index.states().len() {
            return Err(Failure::Invalid);
        }
        let entries = outgoing.get_mut(from).ok_or(Failure::Invalid)?;
        entries.try_reserve(1).map_err(|_| Failure::Resource)?;
        entries.push(number);
    }
    for entries in &outgoing {
        charge(work, entries.capacity())?;
    }
    let mut current_points = HashMap::new();
    charge(work, current.current.len())?;
    current_points
        .try_reserve(current.current.len())
        .map_err(|_| Failure::Resource)?;
    if previous.is_none() {
        for &(state, port, context, role) in &current.current {
            if current_points
                .insert(state, (port, context, role))
                .is_some_and(|old| old != (port, context, role))
            {
                return Err(Failure::Invalid);
            }
        }
    }
    let mut details = HashMap::new();
    trace.visit_details(work, |id, detail, work| {
        charge(work, 1)?;
        details.try_reserve(1).map_err(|_| Failure::Resource)?;
        if details.insert(id, detail).is_some() {
            return Err(Failure::Invalid);
        }
        Ok(())
    })?;
    if let Some((successor, binding)) = previous {
        for (state, port, context, role) in advance_successor(
            scope, graph, focus, current, successor, binding, nominated, &index, &outgoing, &edges,
            &details, work,
        )? {
            charge(work, 1)?;
            current_points
                .try_reserve(1)
                .map_err(|_| Failure::Resource)?;
            if current_points
                .insert(state, (port, context, role))
                .is_some_and(|old| old != (port, context, role))
            {
                return Err(Failure::Invalid);
            }
        }
    }
    let mut entered = Vec::new();
    for &(from, to, transition) in &edges {
        charge(work, 1)?;
        let Some(&(port, context, role)) = current_points.get(&from) else {
            continue;
        };
        if !matches!(transition, control::CompletionTransition::Call { .. }) {
            continue;
        }
        let state = trace.state(from, work)?;
        if !source_position(scope, focus, state, nominated.call(), work)? {
            continue;
        }
        if state.value_context != context {
            return Err(Failure::Invalid);
        }
        let input = nominated.input().index().map_err(|_| Failure::Invalid)?;
        let Some(crate::core::EffectExprKind::Pure(crate::core::PureExprKind::Variable(variable))) =
            scope.nodes().get(input).map(|node| &node.kind)
        else {
            return Err(Failure::Invalid);
        };
        if variable.binder() != role {
            return Err(Failure::Invalid);
        }
        let input_code = input.checked_add(1).ok_or(Failure::Resource)?;
        if focus
            .values()
            .original_control_node(input_code, scope.nodes(), work)?
            != input
        {
            return Err(Failure::Invalid);
        }
        let (_, source) = focus
            .values()
            .existing_forward_ports(input_code, context, work)?;
        if source != port {
            return Err(Failure::Invalid);
        }
        let witness = entered_call(
            graph,
            focus,
            from,
            to,
            transition,
            nominated.closure(),
            work,
        )?;
        checked_context_capture(
            scope,
            focus,
            nominated.definition(),
            trace.call(witness, work)?,
            &current.query_origins,
            work,
        )?;
        entered.try_reserve(1).map_err(|_| Failure::Resource)?;
        entered.push((from, to, transition, port, context, witness));
    }
    if entered.is_empty() {
        return Err(Failure::Invalid);
    }
    let mut result = Vec::new();
    for (call_state, entry_state, call_edge, input, context, witness) in entered {
        // Explore this entered invocation only. This remains a provisional
        // observation: joins, termination and the transition mapping must be
        // established before a successor can acquire currentness.
        let mut pending = VecDeque::new();
        let mut reached = HashSet::new();
        let mut reached_edges = HashSet::new();
        pending.try_reserve(1).map_err(|_| Failure::Resource)?;
        pending.push_back(entry_state);
        while let Some(id) = pending.pop_front() {
            charge(work, 1)?;
            reached.try_reserve(1).map_err(|_| Failure::Resource)?;
            if !reached.insert(id) {
                continue;
            }
            let before = trace.state(id, work)?;
            let control = graph
                .code
                .get(before.position.code)
                .ok_or(Failure::Invalid)?;
            let original = match focus.values().original_control_node(
                before.position.code,
                scope.nodes(),
                work,
            ) {
                Ok(original) => Some(original),
                Err(Failure::Invalid) => None,
                Err(other) => return Err(other),
            };
            if let Some(original) = original {
                match scope.nodes().get(original).map(|node| &node.kind) {
                    Some(crate::core::EffectExprKind::Pure(crate::core::PureExprKind::Value(
                        crate::core::PureValue::Function(_),
                    ))) => return Err(Failure::Invalid),
                    Some(crate::core::EffectExprKind::Operation(
                        crate::core::EffectOperation::RegionClosure(closure),
                    )) if !current.body_closures.contains(&original)
                        || closure.api != nominated.provider_api()
                        || !current.closure_origins.contains_key(&original) =>
                    {
                        return Err(Failure::Invalid);
                    }
                    _ => {}
                }
            }
            let region =
                matches!(control, control::Control::Request(request) if request.region_service);
            let source = if region {
                Some(
                    checked_region_source(
                        scope,
                        graph,
                        focus,
                        before.position.code,
                        &current.checked_nodes,
                        work,
                    )?
                    .ok_or(Failure::Invalid)?,
                )
            } else {
                None
            };
            match control {
                control::Control::Request(request)
                    if !request.region_service
                        && !current.verified_query_requests.contains(&id) =>
                {
                    return Err(Failure::Invalid);
                }
                control::Control::Resume { .. }
                    if !current.verified_query_resumes.contains(&id) =>
                {
                    return Err(Failure::Invalid);
                }
                control::Control::NetworkEvent { .. }
                | control::Control::Unavailable
                | control::Control::WorkerInputStart { .. }
                | control::Control::WorkerInputDone { .. }
                | control::Control::Handler { .. }
                | control::Control::Cleanup { .. }
                | control::Control::Resource { .. }
                | control::Control::Registration { .. }
                | control::Control::NativeInterpret { .. }
                | control::Control::RetainedRoot { .. }
                | control::Control::Retain { .. }
                | control::Control::Continue { .. }
                | control::Control::Discard { .. } => return Err(Failure::Invalid),
                _ => {}
            }
            let entries = outgoing.get(id).ok_or(Failure::Invalid)?;
            if entries.is_empty() {
                return Err(Failure::Invalid);
            }
            for &number in entries {
                charge(work, 1)?;
                let &(from, to, transition) = edges.get(number).ok_or(Failure::Invalid)?;
                if from != id {
                    return Err(Failure::Invalid);
                }
                reached_edges
                    .try_reserve(1)
                    .map_err(|_| Failure::Resource)?;
                reached_edges.insert(number);
                if let control::CompletionTransition::Call { target, .. } = transition {
                    if target == nominated.closure().index().map_err(|_| Failure::Invalid)? {
                        return Err(Failure::Invalid);
                    }
                    authenticate_body_call(
                        scope,
                        graph,
                        focus,
                        from,
                        to,
                        transition,
                        &current.body_calls,
                        &current.body_closures,
                        &current.helpers,
                        &current.closure_origins,
                        &current.query_origins,
                        work,
                    )?;
                }
                if let Some(original) = source {
                    let control::CompletionTransition::Detail(detail) = transition else {
                        return Err(Failure::Invalid);
                    };
                    checked_body_region_return(
                        scope,
                        graph,
                        focus,
                        before,
                        trace.state(to, work)?,
                        *details.get(&detail).ok_or(Failure::Invalid)?,
                        &current.query_origins,
                        &current.checked_nodes,
                        original,
                        nominated.provider_api(),
                        work,
                    )?;
                }
                let returned = match transition {
                    control::CompletionTransition::Detail(detail) => match details.get(&detail) {
                        Some(control::CompletionDetail::Return(edge))
                        | Some(control::CompletionDetail::NativeReturn {
                            edge: Some(edge), ..
                        }) => {
                            matches!(edge.frame, control::Frame::CallReturn { witness: actual, .. } if actual == witness)
                        }
                        _ => false,
                    },
                    _ => false,
                };
                if !returned {
                    pending.try_reserve(1).map_err(|_| Failure::Resource)?;
                    pending.push_back(to);
                }
            }
        }
        // A merged state may not inherit this invocation merely because one
        // predecessor entered it. Reject foreign predecessors conservatively;
        // this observation still does not establish termination or a current
        // successor.
        for &(from, to, transition) in &edges {
            charge(work, 1)?;
            if reached.contains(&to)
                && !reached.contains(&from)
                && !(from == call_state && to == entry_state && transition == call_edge)
            {
                return Err(Failure::Invalid);
            }
        }
        // Recursive checked list helpers may produce cycles in the finite
        // trace abstraction. The worklist checks every reached alternative;
        // only an actual matching normal exit can yield a successor. Finite
        // input and the reviewed helper laws remain consuming premises.
        charge(
            work,
            reached
                .capacity()
                .checked_add(reached_edges.capacity())
                .and_then(|size| size.checked_add(pending.capacity()))
                .ok_or(Failure::Resource)?,
        )?;
        let mut matched = 0usize;
        for (number, &(from, to, transition)) in edges.iter().enumerate() {
            charge(work, 1)?;
            if !reached_edges.contains(&number) {
                continue;
            }
            let control::CompletionTransition::Detail(detail) = transition else {
                continue;
            };
            let (edge, native_return) = match details.get(&detail) {
                Some(control::CompletionDetail::Return(edge)) => (edge, false),
                Some(control::CompletionDetail::NativeReturn {
                    edge: Some(edge), ..
                }) if matches!(edge.frame, control::Frame::CallReturn { witness: actual, .. } if actual == witness) =>
                {
                    // The reached-edge traversal above has checked every
                    // alternative of this exact Region request, including
                    // its selected provider and normal return.
                    let before = trace.state(from, work)?;
                    if !matches!(graph.code.get(before.position.code), Some(control::Control::Request(request)) if request.region_service)
                    {
                        return Err(Failure::Invalid);
                    }
                    (edge, true)
                }
                _ => continue,
            };
            if !matches!(edge.frame, control::Frame::CallReturn { witness: actual, .. } if actual == witness)
            {
                continue;
            }
            let call = matched_source_return(
                scope,
                focus,
                &index,
                from,
                to,
                *edge,
                native_return,
                nominated.call(),
                nominated.closure(),
                work,
            )?
            .ok_or(Failure::Invalid)?;
            if call.caller_value_context != context {
                return Err(Failure::Invalid);
            }
            // A returned state only carries this token when every incoming
            // alternative is a checked normal return of the same invocation
            // and names the same result port.
            for (incoming_number, &(incoming_from, incoming_to, incoming)) in
                edges.iter().enumerate()
            {
                charge(work, 1)?;
                if incoming_to != to {
                    continue;
                }
                if !reached_edges.contains(&incoming_number) {
                    return Err(Failure::Invalid);
                }
                let control::CompletionTransition::Detail(detail) = incoming else {
                    return Err(Failure::Invalid);
                };
                let (incoming_edge, native) = match details.get(&detail) {
                    Some(control::CompletionDetail::Return(edge)) => (edge, false),
                    Some(control::CompletionDetail::NativeReturn {
                        edge: Some(edge), ..
                    }) => {
                        let before = trace.state(incoming_from, work)?;
                        if !matches!(graph.code.get(before.position.code), Some(control::Control::Request(request)) if request.region_service)
                        {
                            return Err(Failure::Invalid);
                        }
                        (edge, true)
                    }
                    _ => return Err(Failure::Invalid),
                };
                if !matches!(incoming_edge.frame, control::Frame::CallReturn { witness: actual, .. } if actual == witness)
                {
                    return Err(Failure::Invalid);
                }
                let incoming_call = matched_source_return(
                    scope,
                    focus,
                    &index,
                    incoming_from,
                    incoming_to,
                    *incoming_edge,
                    native,
                    nominated.call(),
                    nominated.closure(),
                    work,
                )?
                .ok_or(Failure::Invalid)?;
                if incoming_call.result != call.result
                    || incoming_call.caller_value_context != context
                {
                    return Err(Failure::Invalid);
                }
            }
            matched = matched.checked_add(1).ok_or(Failure::Resource)?;
            result.try_reserve(1).map_err(|_| Failure::Resource)?;
            result.push(ConditionalTransitionSuccessor {
                _focus: focus,
                owner: current.owner,
                side: current.side,
                call_node: nominated.call(),
                _call_state: call_state,
                return_state: to,
                _input: input,
                returned: call.result,
                caller_context: context,
                peer_authentication_required: matches!(
                    nominated,
                    TransitionCall::Acknowledgement(_)
                ) || previous
                    .is_some_and(|(prior, _)| prior.peer_authentication_required),
            });
        }
        if matched == 0 {
            return Err(Failure::Invalid);
        }
    }
    charge(
        work,
        current_points
            .capacity()
            .checked_add(details.capacity())
            .and_then(|size| size.checked_add(outgoing.capacity()))
            .ok_or(Failure::Resource)?,
    )?;
    Ok(result)
}
