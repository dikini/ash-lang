//! Authentication of the actual one-way End-to-finish control path.
//!
//! The eventual route is only a candidate for separately checked processing,
//! cleanup, and runtime correspondence. It is never a completion fact.

use super::{Failure, SummaryGraph, charge};
use crate::{
    core::{
        NodeId,
        dialect::PureComputation,
        effect::{EffectExprKind, EffectOperation},
    },
    types::TypeWorkBudget,
};

// Temporary test diagnostics for pinpointing the side-0 refusal.
fn end_invalid(line: u32) -> Failure {
    #[cfg(test)]
    eprintln!("End Invalid at network_end.rs:{line}");
    #[cfg(not(test))]
    let _ = line;
    Failure::Invalid
}

/// A checked route; runtime completion remains a separate obligation.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct WorkerEndRoute {
    pub(super) owner: NodeId,
    pub(super) entry: crate::resolved::BinderId,
    pub(super) side: usize,
    pub(super) receive: NodeId,
    pub(super) end_match: NodeId,
    pub(super) end_arm: usize,
    pub(super) outcome_match: NodeId,
    pub(super) outcome_arm: usize,
    pub(super) finish_call: NodeId,
    pub(super) finish: NodeId,
}

fn original<'a>(
    scope: &'a super::super::validate::NetworkNativeIdentityScope<'_>,
    id: NodeId,
) -> Result<&'a super::StoredNode<super::super::effect::EffectOperationFamily>, Failure> {
    if id.arena() != scope.arena() {
        return Err(end_invalid(line!()));
    }
    scope
        .nodes()
        .get(id.index().map_err(|_| Failure::Invalid)?)
        .ok_or(Failure::Invalid)
}

/// The supported loop has only a false literal or a direct recursive call on
/// each non-End normal return. A one-arm irrefutable Match can run processing
/// before that tail call; processing completion is checked separately.
fn checked_loop_result(
    scope: &super::super::validate::NetworkNativeIdentityScope<'_>,
    matching: NodeId,
    recursive: crate::resolved::BinderId,
    budget: &mut TypeWorkBudget,
) -> Result<(usize, Vec<NodeId>), Failure> {
    use super::{PureExprKind, PureValue};
    use crate::core::data::CorePatternKind;
    charge(budget, 1)?;
    let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Match(node))) =
        &original(scope, matching)?.kind
    else {
        return Err(end_invalid(line!()));
    };
    let EffectExprKind::Operation(EffectOperation::Network(owner)) =
        &original(scope, scope.owner())?.kind
    else {
        return Err(end_invalid(line!()));
    };
    let end = crate::types::ConstructorId::new(
        crate::types::NominalTypeId::new(owner.acquisition.builtin, 6),
        2,
    );
    charge(budget, node.arms().len())?;
    let mut end_arm = None;
    let mut recursive_calls = Vec::new();
    recursive_calls
        .try_reserve(node.arms().len())
        .map_err(|_| Failure::Resource)?;
    for (ordinal, arm) in node.arms().iter().enumerate() {
        charge(budget, 3)?;
        let CorePatternKind::Constructor {
            constructor,
            payload,
        } = &arm.pattern().kind
        else {
            return Err(end_invalid(line!()));
        };
        if *constructor == end {
            if payload.is_some()
                || end_arm.replace(ordinal).is_some()
                || !matches!(&original(scope, arm.body())?.kind,
                    EffectExprKind::Pure(PureExprKind::Value(PureValue::Boolean(value))) if value.value())
            {
                return Err(end_invalid(line!()));
            }
            continue;
        }
        let mut body = arm.body();
        if matches!(&original(scope, body)?.kind,
            EffectExprKind::Pure(PureExprKind::Value(PureValue::Boolean(value))) if !value.value())
        {
            continue;
        }
        // Any prefix is evaluated before recursion, not as a saved suffix.
        if let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Match(prefix))) =
            &original(scope, body)?.kind
        {
            let [branch] = prefix.arms() else {
                return Err(end_invalid(line!()));
            };
            let irrefutable = match &branch.pattern().kind {
                CorePatternKind::Wildcard => true,
                CorePatternKind::Tuple(fields) => {
                    charge(budget, fields.len())?;
                    !fields.is_empty()
                        && fields.iter().all(|field| {
                            matches!(
                                &field.kind,
                                CorePatternKind::Binder(_) | CorePatternKind::Wildcard
                            )
                        })
                }
                _ => false,
            };
            if !irrefutable {
                return Err(end_invalid(line!()));
            }
            body = branch.body();
        }
        let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Apply(call))) =
            &original(scope, body)?.kind
        else {
            return Err(end_invalid(line!()));
        };
        if called_binder(scope, call.function(), budget)? != recursive {
            return Err(end_invalid(line!()));
        }
        recursive_calls.push(body);
    }
    Ok((
        end_arm.ok_or_else(|| end_invalid(line!()))?,
        recursive_calls,
    ))
}

fn called_binder(
    scope: &super::super::validate::NetworkNativeIdentityScope<'_>,
    mut node: NodeId,
    budget: &mut TypeWorkBudget,
) -> Result<crate::resolved::BinderId, Failure> {
    use super::PureExprKind;
    // Accept the direct type instantiation emitted for a linked global.
    charge(budget, 2)?;
    if let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::TypeApplication(
        application,
    ))) = &original(scope, node)?.kind
    {
        node = application.function();
    }
    let EffectExprKind::Pure(PureExprKind::Variable(variable)) = &original(scope, node)?.kind
    else {
        return Err(end_invalid(line!()));
    };
    Ok(variable.binder())
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct FinishContext {
    matching: NodeId,
    arm: usize,
    code: usize,
    context: usize,
    value_context: usize,
    call: NodeId,
    witness: usize,
}

/// Reconstruct the candidate finish caller from the exact worker-local trace.
/// The caller must still prove all actual return paths before issuing a route.
fn finish_contexts(
    scope: &super::super::validate::NetworkNativeIdentityScope<'_>,
    side: usize,
    graph: &SummaryGraph,
    focus: &super::control::CompletionFocus<'_>,
    budget: &mut TypeWorkBudget,
) -> Result<(NodeId, Vec<FinishContext>), Failure> {
    use super::PureExprKind;
    use super::control::{Address, Control, Frame, NetworkEventStage};
    use crate::core::data::CorePatternKind;
    let EffectExprKind::Operation(EffectOperation::Network(owner)) =
        &original(scope, scope.owner())?.kind
    else {
        return Err(end_invalid(line!()));
    };
    let api = crate::resolved::NetworkApi::for_module(owner.acquisition.builtin)
        .ok_or_else(|| end_invalid(line!()))?;
    let mut site = None;
    let mut contexts = Vec::new();
    let trace = focus.trace()?;
    trace.visit_states(budget, |_, state, budget| {
        let Some(Control::NetworkEvent {
            operation,
            stage: NetworkEventStage::Observed,
            ..
        }) = graph.code.get(state.position.code)
        else {
            return Ok(());
        };
        let EffectExprKind::Operation(EffectOperation::RegionBuffer(buffer)) =
            &original(scope, *operation)?.kind
        else {
            return Err(end_invalid(line!()));
        };
        let crate::core::region::RegionBufferOperation::Network {
            effect,
            operation: actual,
        } = &buffer.operation
        else {
            return Err(end_invalid(line!()));
        };
        if *actual != crate::types::OperationId::new(api.io(), 7) {
            return Ok(());
        }
        if effect.effect() != api.io() || site.is_some_and(|prior| prior != *operation) {
            return Err(end_invalid(line!()));
        }
        if focus.values().existing_original_worker_origin(
            buffer.operand.ok_or_else(|| end_invalid(line!()))?,
            scope.arena(),
            scope.nodes(),
            state.value_context,
            budget,
        )? != (
            scope.owner(),
            u8::try_from(side).map_err(|_| Failure::Invalid)?,
        ) {
            return Err(end_invalid(line!()));
        }
        site = Some(*operation);
        let mut address = state.stack;
        let mut seen = std::collections::HashSet::new();
        let mut finish_call = None;
        let mut found = None;
        while !matches!(address, Address::Empty | Address::End) {
            charge(
                budget,
                state.heap.len().checked_add(1).ok_or(Failure::Resource)?,
            )?;
            seen.try_reserve(1).map_err(|_| Failure::Resource)?;
            if !seen.insert(address) || matches!(address, Address::Slot { old: true, .. }) {
                return Err(end_invalid(line!()));
            }
            let mut edges = state.heap.iter().filter(|edge| edge.address == address);
            let edge = edges.next().ok_or_else(|| end_invalid(line!()))?;
            if edges.next().is_some() {
                return Err(end_invalid(line!()));
            }
            match edge.frame {
                Frame::CallReturn { code, witness, .. } if finish_call.is_none() => {
                    let index =
                        focus
                            .values()
                            .original_control_node(code, scope.nodes(), budget)?;
                    finish_call = Some((
                        NodeId::new(
                            scope.arena(),
                            u32::try_from(index).map_err(|_| Failure::Resource)?,
                        ),
                        witness,
                    ));
                }
                Frame::CaseReturn {
                    code,
                    ordinal,
                    context,
                    value_context,
                } => {
                    let index =
                        match focus
                            .values()
                            .original_control_node(code, scope.nodes(), budget)
                        {
                            Ok(index) => index,
                            Err(Failure::Invalid) => {
                                address = edge.next;
                                continue;
                            }
                            Err(other) => return Err(other),
                        };
                    let id = NodeId::new(
                        scope.arena(),
                        u32::try_from(index).map_err(|_| Failure::Resource)?,
                    );
                    let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Match(
                        matching,
                    ))) = &original(scope, id)?.kind
                    else {
                        return Err(end_invalid(line!()));
                    };
                    let Some(arm) = matching.arms().get(ordinal) else {
                        return Err(end_invalid(line!()));
                    };
                    if !matches!(&arm.pattern().kind, CorePatternKind::Boolean(true)) {
                        address = edge.next;
                        continue;
                    }
                    let (call, witness) = finish_call.ok_or_else(|| end_invalid(line!()))?;
                    // The selected true arm evaluates this exact call first;
                    // no other source computation can reach this finish site.
                    let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Match(
                        after,
                    ))) = &original(scope, arm.body())?.kind
                    else {
                        return Err(end_invalid(line!()));
                    };
                    let [one] = after.arms() else {
                        return Err(end_invalid(line!()));
                    };
                    if after.scrutinee() != call
                        || !matches!(&one.pattern().kind, CorePatternKind::Wildcard)
                    {
                        return Err(end_invalid(line!()));
                    }
                    found = Some(FinishContext {
                        matching: id,
                        arm: ordinal,
                        code,
                        context,
                        value_context,
                        call,
                        witness,
                    });
                    break;
                }
                _ => {}
            }
            address = edge.next;
        }
        let found = found.ok_or_else(|| end_invalid(line!()))?;
        charge(budget, contexts.len())?;
        if !contexts.contains(&found) {
            contexts.try_reserve(1).map_err(|_| Failure::Resource)?;
            contexts.push(found);
        }
        Ok(())
    })?;
    Ok((site.ok_or_else(|| end_invalid(line!()))?, contexts))
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(super) struct ContextQuery {
    pub(super) clause: super::control::Edge,
    pub(super) resume: usize,
    pub(super) value: usize,
}

/// Match a request successor to the actual selected direct-resume clause.
pub(super) fn context_query(
    scope: &super::super::validate::NetworkNativeIdentityScope<'_>,
    graph: &SummaryGraph,
    focus: &super::control::CompletionFocus<'_>,
    before: &super::control::State,
    after: &super::control::State,
    budget: &mut TypeWorkBudget,
) -> Result<ContextQuery, Failure> {
    use super::control::{Address, Control, Frame};
    use super::{PureExprKind, PureValue};
    let Control::Request(request) = graph
        .code
        .get(before.position.code)
        .ok_or_else(|| end_invalid(line!()))?
    else {
        return Err(end_invalid(line!()));
    };
    let effect = request
        .effect
        .as_ref()
        .ok_or_else(|| end_invalid(line!()))?;
    let api = crate::resolved::RegionApi::for_module(effect.effect().module())
        .ok_or_else(|| end_invalid(line!()))?;
    let op = crate::types::OperationId::new(api.default_alloc(), 1);
    if effect.effect() != api.default_alloc()
        || !effect.arguments().is_empty()
        || request.operation != Some(op)
        || request.ambiguous_instance
        || request.opaque_row.is_some()
    {
        return Err(end_invalid(line!()));
    }
    let index =
        focus
            .values()
            .original_control_node(before.position.code, scope.nodes(), budget)?;
    let node = scope
        .nodes()
        .get(index)
        .ok_or_else(|| end_invalid(line!()))?;
    let EffectExprKind::Operation(EffectOperation::Request(source)) = &node.kind else {
        return Err(end_invalid(line!()));
    };
    if source.effect().effect() != api.default_alloc()
        || source.operation() != op
        || !source.effect().arguments().is_empty()
        || !matches!(
            &original(scope, source.operand())?.kind,
            EffectExprKind::Pure(PureExprKind::Value(PureValue::Unit(_)))
        )
    {
        return Err(end_invalid(line!()));
    }
    charge(budget, after.heap.len())?;
    let mut top = after.heap.iter().filter(|edge| edge.address == after.stack);
    let clause_edge = *top.next().ok_or_else(|| end_invalid(line!()))?;
    if top.next().is_some() || matches!(after.stack, Address::Slot { old: true, .. }) {
        return Err(end_invalid(line!()));
    }
    let Frame::Clause {
        handler,
        ordinal,
        owner,
        context,
        value_context: _,
        capture,
        capture_context: _,
        clause_context,
        event,
        consumed: false,
    } = clause_edge.frame
    else {
        return Err(end_invalid(line!()));
    };
    if event.code != before.position.code
        || event.unknown
        || event.port
            != Some(
                focus
                    .values()
                    .existing_port(event.code, before.value_context, budget)?,
            )
        || matches!(capture, Address::Empty | Address::End)
        || after.context != context
        || after.value_context != clause_context
    {
        return Err(end_invalid(line!()));
    }
    // The retained C3 request-to-Clause successor already records the
    // selected dispatch over every summarized stack alternative.
    let Control::Handler {
        clauses,
        effect: selected_effect,
        ..
    } = graph
        .code
        .get(handler)
        .ok_or_else(|| end_invalid(line!()))?
    else {
        return Err(end_invalid(line!()));
    };
    let clause = clauses.get(ordinal).ok_or_else(|| end_invalid(line!()))?;
    if selected_effect.effect.as_ref().map(|e| e.effect()) != Some(api.default_alloc())
        || clause.operation != Some(op)
        || clause.owner != owner
        || after.position.code != clause.body
    {
        return Err(end_invalid(line!()));
    }
    let Control::Resume {
        owner: resume_owner,
        value,
    } = graph
        .code
        .get(clause.body)
        .ok_or_else(|| end_invalid(line!()))?
    else {
        return Err(end_invalid(line!()));
    };
    if *resume_owner != owner || !matches!(graph.code.get(*value), Some(Control::Return)) {
        return Err(end_invalid(line!()));
    }
    let value_index = focus
        .values()
        .original_control_node(*value, scope.nodes(), budget)?;
    let value_node = scope
        .nodes()
        .get(value_index)
        .ok_or_else(|| end_invalid(line!()))?;
    if value_node.ty != crate::types::Type::Nominal(api.region_view())
        || !matches!(
            &value_node.kind,
            EffectExprKind::Pure(PureExprKind::Variable(_))
        )
    {
        return Err(end_invalid(line!()));
    }
    Ok(ContextQuery {
        clause: clause_edge,
        resume: clause.body,
        value: *value,
    })
}

/// State facts are local to this exact final trace and value snapshot.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
#[expect(
    clippy::large_enum_variant,
    reason = "Copy facts avoid allocation during bounded predecessor traversal"
)]
enum EndFact {
    None,
    Receive {
        port: usize,
        outcome: u32,
    },
    Boolean {
        port: usize,
        value: bool,
        authenticated: bool,
    },
    Selected,
    Query(ContextQuery),
}

impl EndFact {
    fn port(self) -> Option<usize> {
        match self {
            Self::Receive { port, .. } | Self::Boolean { port, .. } => Some(port),
            _ => None,
        }
    }
    fn move_port(self, next: usize) -> Self {
        match self {
            Self::Receive { outcome, .. } => Self::Receive {
                port: next,
                outcome,
            },
            Self::Boolean {
                value,
                authenticated,
                ..
            } => Self::Boolean {
                port: next,
                value,
                authenticated,
            },
            other => other,
        }
    }
}

/// A generated host-outcome selector performs no source computation before
/// the observed event; authenticate every branch to the exact finish node.
fn finish_outcome_choice(
    graph: &SummaryGraph,
    route: WorkerEndRoute,
    code: usize,
    budget: &mut TypeWorkBudget,
) -> Result<bool, Failure> {
    use super::control::{Control, NetworkEventStage};
    let operation = route
        .finish
        .index()
        .map_err(|_| Failure::Invalid)?
        .checked_add(1)
        .ok_or(Failure::Resource)?;
    let Some(Control::Sequence(children)) = graph.code.get(operation) else {
        return Ok(false);
    };
    charge(budget, children.len())?;
    if children.last().copied() != Some(code) {
        return Ok(false);
    }
    let Some(Control::Choice(arms)) = graph.code.get(code) else {
        return Ok(false);
    };
    charge(budget, arms.len())?;
    if arms.is_empty() {
        return Ok(false);
    }
    for &arm in arms {
        let Some(Control::Sequence(path)) = graph.code.get(arm) else {
            return Ok(false);
        };
        charge(budget, path.len())?;
        let Some(&first) = path.first() else {
            return Ok(false);
        };
        if !matches!(graph.code.get(first), Some(Control::NetworkEvent { operation: site, operation_control, stage: NetworkEventStage::Observed, .. }) if *site == route.finish && *operation_control == operation)
        {
            return Ok(false);
        }
    }
    Ok(true)
}

/// Check every compatible predecessor in the existing worker trace. The
/// caller's runtime guard must separately match the authenticated End reply,
/// its actual Location and Match occurrence, and its current generation.
#[allow(clippy::too_many_arguments)]
fn check_end_return_paths(
    scope: &super::super::validate::NetworkNativeIdentityScope<'_>,
    graph: &SummaryGraph,
    focus: &super::control::CompletionFocus<'_>,
    route: WorkerEndRoute,
    return_index: &super::network_completion::MatchedReturnIndex<'_, '_>,
    budget: &mut TypeWorkBudget,
) -> Result<(), Failure> {
    use super::control::{
        Address, CompletionDetail, CompletionTransition, Control, Frame, NetworkEventStage,
        NetworkOutcome,
    };
    use crate::core::data::CorePatternKind;
    use std::collections::{HashMap, HashSet, VecDeque};
    let trace = focus.trace()?;
    let states = return_index.states();
    let edges = trace.indexed_edges(budget)?;
    charge(
        budget,
        states
            .len()
            .checked_add(edges.len())
            .ok_or(Failure::Resource)?,
    )?;
    let mut outgoing: Vec<Vec<(usize, CompletionTransition)>> = Vec::new();
    outgoing
        .try_reserve_exact(states.len())
        .map_err(|_| Failure::Resource)?;
    outgoing.resize_with(states.len(), Vec::new);
    for &(from, to, transition) in &edges {
        if to >= states.len() {
            return Err(end_invalid(line!()));
        }
        let bucket = outgoing.get_mut(from).ok_or_else(|| end_invalid(line!()))?;
        charge(budget, 1)?;
        bucket.try_reserve(1).map_err(|_| Failure::Resource)?;
        bucket.push((to, transition));
    }
    let mut details = HashMap::new();
    trace.visit_details(budget, |id, detail, budget| {
        charge(budget, 1)?;
        details.try_reserve(1).map_err(|_| Failure::Resource)?;
        if details.insert(id, detail).is_some() {
            return Err(end_invalid(line!()));
        }
        Ok(())
    })?;
    let EffectExprKind::Operation(EffectOperation::Network(owner)) =
        &original(scope, scope.owner())?.kind
    else {
        return Err(end_invalid(line!()));
    };
    let module = owner.acquisition.builtin;
    let receive_type = crate::types::NominalTypeId::new(module, 6);
    let root_code = scope
        .root()
        .index()
        .map_err(|_| Failure::Invalid)?
        .checked_add(1)
        .ok_or(Failure::Resource)?;
    let mut initial = None;
    charge(budget, states.len())?;
    for (id, state) in states.iter().enumerate() {
        let state = state.ok_or_else(|| end_invalid(line!()))?;
        if state.position.code == root_code
            && state.position.next == 0
            && state.context == 0
            && state.value_context == 0
            && state.stack == Address::Empty
            && state.heap.is_empty()
            && initial.replace(id).is_some()
        {
            return Err(end_invalid(line!()));
        }
    }
    let mut pending = VecDeque::new();
    pending.try_reserve(1).map_err(|_| Failure::Resource)?;
    pending.push_back((initial.ok_or_else(|| end_invalid(line!()))?, EndFact::None));
    let mut seen = HashSet::new();
    let mut finish_count = 0usize;
    while let Some((id, mut fact)) = pending.pop_front() {
        charge(budget, 1)?;
        seen.try_reserve(1).map_err(|_| Failure::Resource)?;
        if !seen.insert((id, fact)) {
            continue;
        }
        let state = states
            .get(id)
            .copied()
            .flatten()
            .ok_or_else(|| end_invalid(line!()))?;
        let control = graph
            .code
            .get(state.position.code)
            .ok_or_else(|| end_invalid(line!()))?;
        if let Control::NetworkEvent {
            operation,
            operation_control,
            stage,
            outcome,
        } = control
        {
            if *operation == route.receive {
                if *stage == NetworkEventStage::Observed {
                    fact = EndFact::None;
                }
                if *stage == NetworkEventStage::Reply {
                    let tag = match outcome {
                        NetworkOutcome::Message => 0,
                        NetworkOutcome::Empty => 1,
                        NetworkOutcome::End => 2,
                        NetworkOutcome::Failure => 3,
                        _ => return Err(Failure::Invalid),
                    };
                    let constructor = crate::types::ConstructorId::new(receive_type, tag);
                    let (port, _, _) = focus.values().existing_network_result(
                        *operation_control,
                        state.value_context,
                        constructor,
                        budget,
                    )?;
                    fact = EndFact::Receive { port, outcome: tag };
                }
            } else if *operation == route.finish && *stage == NetworkEventStage::Observed {
                if fact != EndFact::Selected {
                    return Err(end_invalid(line!()));
                }
                finish_count = finish_count.checked_add(1).ok_or(Failure::Resource)?;
                fact = EndFact::None;
            } else if fact != EndFact::None {
                fact = EndFact::None;
            }
        }
        // Only controls whose transfer is checked below may carry an End
        // fact. In particular, entering a new cleanup, handler, resource or
        // retained root cannot preserve it across the pending boundary.
        if fact != EndFact::None {
            match control {
                Control::Return
                | Control::Sequence(_)
                | Control::Choice(_)
                | Control::NetworkEvent { .. } => {}
                Control::Call { .. } => {
                    match focus.values().original_control_node(
                        state.position.code,
                        scope.nodes(),
                        budget,
                    ) {
                        Ok(index)
                            if index
                                == route.finish_call.index().map_err(|_| Failure::Invalid)? => {}
                        Ok(_) | Err(Failure::Invalid) => fact = EndFact::None,
                        Err(other) => return Err(other),
                    }
                }
                Control::Request(_) if fact == EndFact::Selected => {}
                Control::Resume { .. } if matches!(fact, EndFact::Query(_)) => {}
                _ => fact = EndFact::None,
            }
        }
        let successors = outgoing.get(id).ok_or_else(|| end_invalid(line!()))?;
        if successors.is_empty()
            && (matches!(fact, EndFact::Query(_))
                || (fact == EndFact::Selected && matches!(control, Control::Request(_))))
        {
            return Err(end_invalid(line!()));
        }
        for &(to, transition) in successors {
            charge(budget, 1)?;
            let mut next = fact;
            if fact == EndFact::Selected && matches!(control, Control::Request(_)) {
                let after = states
                    .get(to)
                    .copied()
                    .flatten()
                    .ok_or_else(|| end_invalid(line!()))?;
                next = EndFact::Query(context_query(scope, graph, focus, state, after, budget)?);
            } else if let EndFact::Query(query) = fact {
                let after = states
                    .get(to)
                    .copied()
                    .flatten()
                    .ok_or_else(|| end_invalid(line!()))?;
                match control {
                    Control::Resume { value, .. }
                        if state.position.code == query.resume
                            && *value == query.value
                            && state.position.next == 0 =>
                    {
                        if after.position.code != query.value {
                            return Err(end_invalid(line!()));
                        }
                    }
                    Control::Return if state.position.code == query.value => {
                        if after.position.code != query.resume || after.position.next != 1 {
                            return Err(end_invalid(line!()));
                        }
                    }
                    Control::Resume { owner, value }
                        if state.position.code == query.resume
                            && *value == query.value
                            && state.position.next == 1 =>
                    {
                        charge(budget, state.heap.len())?;
                        let mut top = state.heap.iter().filter(|edge| edge.address == state.stack);
                        let edge = top.next().ok_or_else(|| end_invalid(line!()))?;
                        if top.next().is_some()
                            || *edge != query.clause
                            || !matches!(edge.frame, Frame::Clause { owner: actual, consumed: false, .. } if actual == *owner)
                        {
                            return Err(end_invalid(line!()));
                        }
                        // The same-trace completed Resume restores the
                        // selected capture under C3's copy semantics.
                        if after.position.code != 0 {
                            return Err(end_invalid(line!()));
                        }
                        next = EndFact::Selected;
                    }
                    _ => return Err(Failure::Invalid),
                }
            }
            if let CompletionTransition::Choice { ordinal } = transition
                && matches!(control, Control::Choice(_))
            {
                if fact == EndFact::Selected
                    && finish_outcome_choice(graph, route, state.position.code, budget)?
                {
                    let Control::Choice(arms) = control else {
                        return Err(end_invalid(line!()));
                    };
                    let child = *arms.get(ordinal).ok_or_else(|| end_invalid(line!()))?;
                    let after = states
                        .get(to)
                        .copied()
                        .flatten()
                        .ok_or_else(|| end_invalid(line!()))?;
                    if after.position.code != child {
                        return Err(end_invalid(line!()));
                    }
                    charge(budget, 1)?;
                    pending.try_reserve(1).map_err(|_| Failure::Resource)?;
                    pending.push_back((to, next));
                    continue;
                }
                let index = match focus.values().original_control_node(
                    state.position.code,
                    scope.nodes(),
                    budget,
                ) {
                    Ok(index) => index,
                    Err(Failure::Invalid) => {
                        if fact != EndFact::None {
                            next = EndFact::None;
                        }
                        charge(budget, 1)?;
                        pending.try_reserve(1).map_err(|_| Failure::Resource)?;
                        pending.push_back((to, next));
                        continue;
                    }
                    Err(other) => return Err(other),
                };
                if index != route.end_match.index().map_err(|_| Failure::Invalid)?
                    && index != route.outcome_match.index().map_err(|_| Failure::Invalid)?
                {
                    if fact != EndFact::None {
                        next = EndFact::None;
                    }
                    charge(budget, 1)?;
                    pending.try_reserve(1).map_err(|_| Failure::Resource)?;
                    pending.push_back((to, next));
                    continue;
                }
                let (scrutinee, _, _) = focus
                    .values()
                    .existing_choice(state.position.code, state.value_context, budget)?
                    .ok_or_else(|| end_invalid(line!()))?;
                if index == route.end_match.index().map_err(|_| Failure::Invalid)? {
                    let EffectExprKind::Pure(super::PureExprKind::Computation(
                        PureComputation::Match(matching),
                    )) = &original(scope, route.end_match)?.kind
                    else {
                        return Err(end_invalid(line!()));
                    };
                    let arm = matching
                        .arms()
                        .get(ordinal)
                        .ok_or_else(|| end_invalid(line!()))?;
                    let known = match fact {
                        EndFact::Receive { port, outcome } if port == scrutinee => Some(outcome),
                        _ => None,
                    };
                    if let Some(tag) = known {
                        let expected = crate::types::ConstructorId::new(receive_type, tag);
                        if matches!(&arm.pattern().kind, CorePatternKind::Constructor { constructor, .. } if *constructor != expected)
                        {
                            continue;
                        }
                    }
                    if ordinal == route.end_arm {
                        let body = arm
                            .body()
                            .index()
                            .map_err(|_| Failure::Invalid)?
                            .checked_add(1)
                            .ok_or(Failure::Resource)?;
                        let port =
                            focus
                                .values()
                                .existing_port(body, state.value_context, budget)?;
                        next = EndFact::Boolean {
                            port,
                            value: true,
                            authenticated: known == Some(2),
                        };
                    } else if matches!(&original(scope, arm.body())?.kind,
                        EffectExprKind::Pure(super::PureExprKind::Value(super::PureValue::Boolean(v))) if !v.value())
                    {
                        let body = arm
                            .body()
                            .index()
                            .map_err(|_| Failure::Invalid)?
                            .checked_add(1)
                            .ok_or(Failure::Resource)?;
                        next = EndFact::Boolean {
                            port: focus.values().existing_port(
                                body,
                                state.value_context,
                                budget,
                            )?,
                            value: false,
                            authenticated: false,
                        };
                    } else {
                        next = EndFact::None;
                    }
                } else if index == route.outcome_match.index().map_err(|_| Failure::Invalid)? {
                    match fact {
                        EndFact::Boolean {
                            port,
                            value,
                            authenticated,
                        } if port == scrutinee => {
                            if (ordinal == route.outcome_arm) != value {
                                continue;
                            }
                            next = if value && authenticated {
                                EndFact::Selected
                            } else {
                                EndFact::None
                            };
                        }
                        _ => next = EndFact::None,
                    }
                } else if fact != EndFact::None {
                    next = EndFact::None;
                }
            }
            if !matches!(fact, EndFact::Query(_))
                && !matches!(next, EndFact::Query(_))
                && let CompletionTransition::Detail(detail_id) = transition
                && let Some(CompletionDetail::Return(edge)) = details.get(&detail_id)
            {
                match edge.frame {
                    Frame::CaseReturn {
                        code,
                        ordinal,
                        value_context,
                        ..
                    } => {
                        if let Some(port) = next.port() {
                            let Control::Choice(arms) =
                                graph.code.get(code).ok_or_else(|| end_invalid(line!()))?
                            else {
                                return Err(end_invalid(line!()));
                            };
                            let arm = *arms.get(ordinal).ok_or_else(|| end_invalid(line!()))?;
                            let body = focus.values().existing_port(arm, value_context, budget)?;
                            next = if port == body {
                                next.move_port(focus.values().existing_port(
                                    code,
                                    value_context,
                                    budget,
                                )?)
                            } else {
                                EndFact::None
                            };
                        } else if next == EndFact::Selected {
                            next = EndFact::None;
                        }
                    }
                    Frame::CallReturn { .. } => {
                        if let Some(port) = next.port() {
                            let returned = return_index.matched_return(id, to, *edge, budget)?;
                            // The canonical receive wrapper's function body is
                            // a Bind whose body is the exact network operation.
                            // Reconstruct the same linked body/result relation
                            // used by the Message checker; equality of types or
                            // independently nominated ports is not sufficient.
                            let mut forwarded = returned.call.body == port;
                            if !forwarded
                                && matches!(next, EndFact::Receive { .. })
                                && matches!(control, Control::NetworkEvent { operation, stage: NetworkEventStage::Reply, .. } if *operation == route.receive)
                                && returned.call.target == returned.call.expression
                                && let Some(node) = scope.nodes().get(returned.call.expression)
                                && let EffectExprKind::Operation(EffectOperation::RegionClosure(
                                    closure,
                                )) = &node.kind
                                && closure.captures.is_empty()
                                && let Some(function) = closure.code.function()
                                && let Ok(body) = original(scope, function.body())
                                && let EffectExprKind::Pure(super::PureExprKind::Computation(
                                    PureComputation::Bind(binding),
                                )) = &body.kind
                                && binding.body() == route.receive
                            {
                                let receive =
                                    route.receive.index().map_err(|_| Failure::Invalid)?;
                                let code = receive.checked_add(1).ok_or(Failure::Resource)?;
                                let actual = focus.values().existing_bind_body_port(
                                    returned.call.body,
                                    receive,
                                    budget,
                                )?;
                                forwarded = actual == port
                                    && focus.values().existing_port(
                                        code,
                                        returned.call.callee_value_context,
                                        budget,
                                    )? == port;
                            }
                            next = if forwarded {
                                next.move_port(returned.call.result)
                            } else {
                                EndFact::None
                            };
                        } else if next == EndFact::Selected {
                            next = EndFact::None;
                        }
                    }
                    // A sequence frame advances control without changing the
                    // result port; later computations remain checked below.
                    Frame::Next { .. } => {}
                    _ if next != EndFact::None => next = EndFact::None,
                    _ => {}
                }
            }
            charge(budget, 1)?;
            pending.try_reserve(1).map_err(|_| Failure::Resource)?;
            pending.push_back((to, next));
        }
    }
    if finish_count == 0 {
        return Err(end_invalid(line!()));
    }
    Ok(())
}

/// Reconstruct the actual Boolean loop and each reachable finish caller. This
/// emits no route until the complete predecessor check also succeeds.
pub(super) fn worker_end_route(
    scope: &super::super::validate::NetworkNativeIdentityScope<'_>,
    side: usize,
    graph: &SummaryGraph,
    worker: &super::control::Analysis<'_>,
    budget: &mut TypeWorkBudget,
) -> Result<Option<WorkerEndRoute>, Failure> {
    use super::PureExprKind;
    use super::control::{CompletionDetail, CompletionTransition, Frame};
    use crate::core::data::CorePatternKind;
    use std::collections::{HashMap, HashSet};
    let focus = worker
        .completion_foci
        .last()
        .ok_or_else(|| end_invalid(line!()))?;
    let trace = focus.trace()?;
    if trace.focus().is_ok() || scope.entry(side).is_none() {
        return Err(end_invalid(line!()));
    }
    let EffectExprKind::Operation(EffectOperation::Network(owner)) =
        &original(scope, scope.owner())?.kind
    else {
        return Err(end_invalid(line!()));
    };
    let entry = *owner
        .entries
        .get(side)
        .ok_or_else(|| end_invalid(line!()))?;
    let (finish, contexts) =
        finish_contexts(scope, side, graph, focus, budget).inspect_err(|error| {
            #[cfg(test)]
            eprintln!("End finish contexts side={side}: {error:?}");
            let _ = error;
        })?;
    #[cfg(test)]
    eprintln!("End side={side} finish={finish:?}, contexts={contexts:?}");
    let return_index = super::network_completion::MatchedReturnIndex::new(focus, budget)?;
    let states = return_index.states();
    let edges = trace.indexed_edges(budget)?;
    let mut calls = HashMap::new();
    trace.visit_calls(budget, |witness, call, budget| {
        charge(budget, 1)?;
        calls.try_reserve(1).map_err(|_| Failure::Resource)?;
        if calls.insert(witness, call).is_some() {
            return Err(end_invalid(line!()));
        }
        Ok(())
    })?;
    let mut details = HashMap::new();
    trace.visit_details(budget, |id, detail, budget| {
        charge(budget, 1)?;
        details.try_reserve(1).map_err(|_| Failure::Resource)?;
        if details.insert(id, detail).is_some() {
            return Err(end_invalid(line!()));
        }
        Ok(())
    })?;
    let mut needed = HashSet::new();
    let mut required_returns = HashSet::new();
    let mut route = None;
    let mut target = None;
    let mut recursive_sites = Vec::new();
    for context in &contexts {
        charge(budget, 4)?;
        let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Match(outcome))) =
            &original(scope, context.matching)?.kind
        else {
            return Err(end_invalid(line!()));
        };
        let [first, second] = outcome.arms() else {
            return Err(end_invalid(line!()));
        };
        if context.arm != 0
            || !matches!(first.pattern().kind, CorePatternKind::Boolean(true))
            || !matches!(second.pattern().kind, CorePatternKind::Boolean(false))
        {
            return Err(end_invalid(line!()));
        }
        let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Apply(loop_call))) =
            &original(scope, outcome.scrutinee())?.kind
        else {
            return Err(end_invalid(line!()));
        };
        let binder = called_binder(scope, loop_call.function(), budget)?;
        let (scrutinee, _, _) = focus
            .values()
            .existing_choice(context.code, context.value_context, budget)?
            .ok_or_else(|| end_invalid(line!()))?;
        let worker_argument = match &original(scope, loop_call.argument())?.kind {
            EffectExprKind::Pure(PureExprKind::Variable(_)) => loop_call.argument(),
            _ => {
                super::network_completion::generated_tuple_fields(
                    scope,
                    loop_call.argument(),
                    budget,
                )?[0]
                    .0
            }
        };
        if worker_argument == loop_call.argument()
            && focus.values().existing_original_worker_origin(
                worker_argument,
                scope.arena(),
                scope.nodes(),
                context.value_context,
                budget,
            )? != (
                scope.owner(),
                u8::try_from(side).map_err(|_| Failure::Invalid)?,
            )
        {
            return Err(end_invalid(line!()));
        }
        let expected_index = outcome.scrutinee().index().map_err(|_| Failure::Invalid)?;
        let mut found = false;
        charge(budget, calls.capacity())?;
        for (&witness, call) in &calls {
            if call.caller_context != context.context
                || call.caller_value_context != context.value_context
            {
                continue;
            }
            let actual =
                match focus
                    .values()
                    .original_control_node(call.code, scope.nodes(), budget)
                {
                    Ok(actual) => actual,
                    Err(Failure::Invalid) => continue,
                    Err(other) => return Err(other),
                };
            if actual != expected_index {
                continue;
            }
            if call.result != scrutinee || call.target != call.expression {
                return Err(end_invalid(line!()));
            }
            let EffectExprKind::Operation(EffectOperation::RegionClosure(closure)) = &scope
                .nodes()
                .get(call.expression)
                .ok_or_else(|| end_invalid(line!()))?
                .kind
            else {
                return Err(end_invalid(line!()));
            };
            let body = if worker_argument == loop_call.argument() {
                closure
                    .code
                    .function()
                    .ok_or_else(|| end_invalid(line!()))?
                    .body()
            } else {
                super::network_completion::checked_worker_tuple_call(
                    scope,
                    side,
                    focus.values(),
                    *call,
                    loop_call.argument(),
                    budget,
                )?
                .0
            };
            let (end_arm, recursion) = checked_loop_result(scope, body, binder, budget).inspect_err(|error| {
                #[cfg(test)] eprintln!("End loop side={side} body={body:?} binder={binder:?} witness={witness}: {error:?}");
                let _ = error;
            })?;
            let candidate = WorkerEndRoute {
                owner: scope.owner(),
                entry,
                side,
                receive: scope.receive(),
                end_match: body,
                end_arm,
                outcome_match: context.matching,
                outcome_arm: context.arm,
                finish_call: context.call,
                finish,
            };
            if route.is_some_and(|prior| prior != candidate)
                || target.is_some_and(|prior| prior != call.target)
            {
                return Err(end_invalid(line!()));
            }
            route = Some(candidate);
            target = Some(call.target);
            charge(budget, recursion.len())?;
            recursive_sites
                .try_reserve(recursion.len())
                .map_err(|_| Failure::Resource)?;
            for site in recursion {
                if !recursive_sites.contains(&site) {
                    recursive_sites.push(site);
                }
            }
            needed.try_reserve(1).map_err(|_| Failure::Resource)?;
            needed.insert(witness);
            required_returns
                .try_reserve(1)
                .map_err(|_| Failure::Resource)?;
            required_returns.insert(witness);
            found = true;
        }
        if !found {
            return Err(end_invalid(line!()));
        }
        // The actual finish wrapper call must be the frame selected by C3.
        if !calls.contains_key(&context.witness) {
            return Err(end_invalid(line!()));
        }
        needed.try_reserve(1).map_err(|_| Failure::Resource)?;
        needed.insert(context.witness);
    }
    let route = route.ok_or_else(|| end_invalid(line!()))?;
    let target = target.ok_or_else(|| end_invalid(line!()))?;
    let mut recursion_seen = HashSet::new();
    charge(budget, calls.capacity())?;
    for (&witness, call) in &calls {
        let index = match focus
            .values()
            .original_control_node(call.code, scope.nodes(), budget)
        {
            Ok(index) => index,
            Err(Failure::Invalid) => continue,
            Err(other) => return Err(other),
        };
        charge(budget, recursive_sites.len())?;
        let Some(site) = recursive_sites
            .iter()
            .find(|site| site.index().ok() == Some(index))
            .copied()
        else {
            continue;
        };
        if call.target != target || call.expression != target {
            return Err(end_invalid(line!()));
        }
        let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Apply(application))) =
            &original(scope, site)?.kind
        else {
            return Err(end_invalid(line!()));
        };
        let worker_argument = match &original(scope, application.argument())?.kind {
            EffectExprKind::Pure(PureExprKind::Variable(_)) => application.argument(),
            _ => {
                let (body, _, fields) = super::network_completion::checked_worker_tuple_call(
                    scope,
                    side,
                    focus.values(),
                    *call,
                    application.argument(),
                    budget,
                )?;
                if body != route.end_match {
                    return Err(end_invalid(line!()));
                }
                fields[0].0
            }
        };
        if worker_argument == application.argument()
            && focus.values().existing_original_worker_origin(
                worker_argument,
                scope.arena(),
                scope.nodes(),
                call.caller_value_context,
                budget,
            )? != (
                scope.owner(),
                u8::try_from(side).map_err(|_| Failure::Invalid)?,
            )
        {
            return Err(end_invalid(line!()));
        }
        recursion_seen
            .try_reserve(1)
            .map_err(|_| Failure::Resource)?;
        recursion_seen.insert(site);
        needed.try_reserve(1).map_err(|_| Failure::Resource)?;
        needed.insert(witness);
    }
    charge(budget, recursive_sites.len())?;
    if recursive_sites
        .iter()
        .any(|site| !recursion_seen.contains(site))
    {
        return Err(end_invalid(line!()));
    }
    let mut entered = HashSet::new();
    let mut returned = HashSet::new();
    for &(from, to, transition) in &edges {
        charge(budget, 1)?;
        if let CompletionTransition::Call {
            target,
            value_context,
            expression,
            creation,
        } = transition
        {
            let after = states
                .get(to)
                .copied()
                .flatten()
                .ok_or_else(|| end_invalid(line!()))?;
            charge(budget, after.heap.len())?;
            for edge in after.heap.iter().filter(|edge| edge.address == after.stack) {
                let Frame::CallReturn { witness, .. } = edge.frame else {
                    continue;
                };
                if !needed.contains(&witness) || entered.contains(&witness) {
                    continue;
                }
                let call = *calls.get(&witness).ok_or_else(|| end_invalid(line!()))?;
                if (target, value_context, expression, creation)
                    != (
                        call.target,
                        call.callee_value_context,
                        call.expression,
                        call.creation,
                    )
                {
                    continue;
                }
                let _ = super::network_completion::enter_call(
                    graph,
                    focus,
                    from,
                    to,
                    transition,
                    witness,
                    &HashSet::new(),
                    budget,
                )?;
                entered.try_reserve(1).map_err(|_| Failure::Resource)?;
                entered.insert(witness);
            }
        }
        if let CompletionTransition::Detail(id) = transition
            && let Some(CompletionDetail::Return(edge)) = details.get(&id)
            && let Frame::CallReturn { witness, .. } = edge.frame
            && needed.contains(&witness)
        {
            let returned_call = return_index.matched_return(from, to, *edge, budget)?;
            if returned_call.call != *calls.get(&witness).ok_or_else(|| end_invalid(line!()))? {
                return Err(end_invalid(line!()));
            }
            returned.try_reserve(1).map_err(|_| Failure::Resource)?;
            returned.insert(witness);
        }
    }
    charge(
        budget,
        needed
            .capacity()
            .checked_add(required_returns.capacity())
            .ok_or(Failure::Resource)?,
    )?;
    if needed.iter().any(|witness| !entered.contains(witness))
        || required_returns
            .iter()
            .any(|witness| !returned.contains(witness))
    {
        return Err(end_invalid(line!()));
    }
    check_end_return_paths(scope, graph, focus, route, &return_index, budget).inspect_err(
        |error| {
            #[cfg(test)]
            eprintln!("End predecessors side={side}, route={route:?}: {error:?}");
            let _ = error;
        },
    )?;
    Ok(Some(route))
}
