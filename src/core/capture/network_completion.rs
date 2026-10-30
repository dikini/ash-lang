//! Linked-Core inputs for the one-way completion analysis.
//!
//! Extraction never creates completion authority. The solver must establish
//! that the returned operand is the matched return value, is independent of
//! every outstanding message, and belongs to the actual caller continuation.

#[cfg(test)]
use super::StoredNode;
use super::control::{CompletionCall, CompletionFocus, CompletionTransition, Edge, Frame, State};
use super::{Failure, PureComputation, PureExprKind, SummaryGraph, charge};
#[cfg(test)]
use crate::core::{dialect::ArenaId, effect::EffectOperationFamily};
use crate::{
    core::{NodeId, effect::EffectExprKind},
    resolved::BinderId,
    types::TypeWorkBudget,
};
use std::collections::{HashMap, HashSet, VecDeque};

/// An actual linked forwarding node and its operand, in evaluation order.
#[derive(Debug, Eq, PartialEq)]
#[cfg(test)]
pub(super) enum ForwardingNode {
    Alias { node: NodeId, binder: BinderId },
    Newtype { node: NodeId, child: NodeId },
}

/// Port transfers for an exact call/return pair, scoped to the same focused
/// analysis that discovered the edge. These mappings are not completion facts.
pub(super) struct MatchedReturn {
    pub(super) call: CompletionCall,
    #[cfg_attr(
        not(test),
        expect(
            dead_code,
            reason = "The port pairs support focused return diagnostics"
        )
    )]
    pub(super) arguments: Vec<(usize, usize)>,
    #[cfg_attr(
        not(test),
        expect(
            dead_code,
            reason = "The port pairs support focused return diagnostics"
        )
    )]
    pub(super) captures: Vec<(usize, usize)>,
}

/// A caller's dependency state is retained with its actual entered call and
/// focused analysis, so a return cannot reuse another call's snapshot.
pub(super) struct EnteredCall<'focus, 'graph> {
    #[cfg_attr(
        not(test),
        expect(
            dead_code,
            reason = "The saved caller supports focused return diagnostics"
        )
    )]
    focus: &'focus CompletionFocus<'graph>,
    call: CompletionCall,
    #[cfg_attr(
        not(test),
        expect(
            dead_code,
            reason = "The saved caller supports focused return diagnostics"
        )
    )]
    caller: HashSet<usize>,
}

fn copy_dependencies(
    dependencies: &HashSet<usize>,
    budget: &mut TypeWorkBudget,
) -> Result<HashSet<usize>, Failure> {
    // HashSet iteration scans its backing table, including vacant buckets.
    charge(budget, dependencies.capacity())?;
    let mut copied = HashSet::new();
    copied
        .try_reserve(dependencies.len())
        .map_err(|_| Failure::Resource)?;
    copied.extend(dependencies.iter().copied());
    Ok(copied)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sparse_dependency_copy_charges_the_source_table() {
        let mut dependencies = HashSet::with_capacity(256);
        dependencies.insert(7);
        dependencies.remove(&7);
        let capacity = dependencies.capacity();
        assert!(capacity > 0);
        assert!(matches!(
            copy_dependencies(&dependencies, &mut TypeWorkBudget::with_limit(capacity - 1)),
            Err(Failure::Resource)
        ));
        let mut exact = TypeWorkBudget::with_limit(capacity);
        assert!(
            copy_dependencies(&dependencies, &mut exact)
                .unwrap()
                .is_empty()
        );
        assert_eq!(exact.used(), capacity);
    }
}

/// Transfer argument and capture dependencies simultaneously on one actual
/// traced call edge. All reads use the caller snapshot before any write.
#[expect(
    clippy::too_many_arguments,
    reason = "The actual edge, witness, focus and budget are distinct checked inputs"
)]
pub(super) fn enter_call<'focus, 'graph>(
    graph: &SummaryGraph,
    focus: &'focus CompletionFocus<'graph>,
    from: usize,
    to: usize,
    transition: CompletionTransition,
    witness: usize,
    dependencies: &HashSet<usize>,
    budget: &mut TypeWorkBudget,
) -> Result<(EnteredCall<'focus, 'graph>, HashSet<usize>), Failure> {
    let CompletionTransition::Call {
        target,
        value_context,
        expression,
        creation,
    } = transition
    else {
        return Err(Failure::Invalid);
    };
    let trace = focus.trace()?;
    if !trace.contains_call_edge(from, to, transition, budget)? {
        return Err(Failure::Invalid);
    }
    let call = trace.call(witness, budget)?;
    let before = trace.state(from, budget)?;
    let after = trace.state(to, budget)?;
    if (target, value_context, expression, creation)
        != (
            call.target,
            call.callee_value_context,
            call.expression,
            call.creation,
        )
        || before.position.code != call.code
        || before.context != call.caller_context
        || before.value_context != call.caller_value_context
        || after.value_context != call.callee_value_context
        || after.position.code != graph.callables.get(target, budget)?.body
    {
        return Err(Failure::Invalid);
    }
    charge(budget, after.heap.len())?;
    let mut matches = after.heap.iter().filter(|edge| {
        edge.address == after.stack && matches!(edge.frame, Frame::CallReturn { witness: selected, .. } if selected == witness)
    });
    let Some(edge) = matches.next() else {
        return Err(Failure::Invalid);
    };
    if matches.next().is_some()
        || !matches!(edge.frame,
        Frame::CallReturn { code, result, body, context, value_context, .. }
            if (code, result, body, context, value_context) ==
                (call.code, call.result, call.body, call.caller_context, call.caller_value_context))
    {
        return Err(Failure::Invalid);
    }
    let (result, body, arguments, captures) = focus.values().existing_call_ports(
        call.code,
        call.caller_value_context,
        call.expression,
        call.callee_value_context,
        call.creation,
        budget,
    )?;
    if (result, body) != (call.result, call.body) {
        return Err(Failure::Invalid);
    }
    let caller = copy_dependencies(dependencies, budget)?;
    let mut callee = copy_dependencies(dependencies, budget)?;
    let count = arguments
        .len()
        .checked_add(captures.len())
        .ok_or(Failure::Resource)?;
    charge(budget, count.checked_mul(2).ok_or(Failure::Resource)?)?;
    let mut writes = HashMap::new();
    writes.try_reserve(count).map_err(|_| Failure::Resource)?;
    for (destination, source) in arguments.into_iter().chain(captures) {
        let derived = dependencies.contains(&source);
        writes
            .entry(destination)
            .and_modify(|prior| *prior |= derived)
            .or_insert(derived);
    }
    callee
        .try_reserve(writes.len())
        .map_err(|_| Failure::Resource)?;
    for (destination, derived) in writes {
        callee.remove(&destination);
        if derived {
            callee.insert(destination);
        }
    }
    Ok((
        EnteredCall {
            focus,
            call,
            caller,
        },
        callee,
    ))
}

/// Restore only the matching caller snapshot, replacing its result dependency
/// with the actual returned body's dependency.
#[cfg(test)]
pub(super) fn return_call(
    entered: &EnteredCall<'_, '_>,
    from: usize,
    to: usize,
    edge: Edge,
    callee: &HashSet<usize>,
    budget: &mut TypeWorkBudget,
) -> Result<HashSet<usize>, Failure> {
    let returned = matched_call_return(entered.focus, from, to, edge, budget)?;
    if returned.call != entered.call {
        return Err(Failure::Invalid);
    }
    charge(budget, 2)?;
    let derived = callee.contains(&returned.call.body);
    let mut caller = copy_dependencies(&entered.caller, budget)?;
    caller.try_reserve(1).map_err(|_| Failure::Resource)?;
    caller.remove(&returned.call.result);
    if derived {
        caller.insert(returned.call.result);
    }
    Ok(caller)
}

/// Reuse exact immutable state and call identities within one final focus.
/// Construction and retained capacity are charged once; the borrow prevents
/// using this index with a different focus or value revision.
pub(super) struct MatchedReturnIndex<'focus, 'graph> {
    focus: &'focus CompletionFocus<'graph>,
    states: Vec<Option<&'focus State>>,
    calls: HashMap<usize, CompletionCall>,
}

impl<'focus, 'graph> MatchedReturnIndex<'focus, 'graph> {
    pub(super) fn new(
        focus: &'focus CompletionFocus<'graph>,
        budget: &mut TypeWorkBudget,
    ) -> Result<Self, Failure> {
        let trace = focus.trace()?;
        let states = trace.indexed_states(budget)?;
        let mut calls = HashMap::new();
        trace.visit_calls(budget, |id, call, budget| {
            charge(budget, 1)?;
            calls.try_reserve(1).map_err(|_| Failure::Resource)?;
            if calls.insert(id, call).is_some() {
                return Err(Failure::Invalid);
            }
            Ok(())
        })?;
        charge(budget, calls.capacity())?;
        Ok(Self {
            focus,
            states,
            calls,
        })
    }

    pub(super) fn states(&self) -> &[Option<&'focus State>] {
        &self.states
    }

    pub(super) fn matched_return(
        &self,
        from: usize,
        to: usize,
        edge: Edge,
        budget: &mut TypeWorkBudget,
    ) -> Result<MatchedReturn, Failure> {
        let Frame::CallReturn { witness, .. } = edge.frame else {
            return Err(Failure::Invalid);
        };
        if !self
            .focus
            .trace()?
            .contains_return_edge(from, to, edge, budget)?
        {
            return Err(Failure::Invalid);
        }
        charge(budget, 3)?;
        let call = *self.calls.get(&witness).ok_or(Failure::Invalid)?;
        let before = self
            .states
            .get(from)
            .copied()
            .flatten()
            .ok_or(Failure::Invalid)?;
        let after = self
            .states
            .get(to)
            .copied()
            .flatten()
            .ok_or(Failure::Invalid)?;
        matched_return_checked(self.focus, edge, call, before, after, budget)
    }
}

pub(super) fn matched_call_return(
    focus: &CompletionFocus<'_>,
    from: usize,
    to: usize,
    edge: Edge,
    budget: &mut TypeWorkBudget,
) -> Result<MatchedReturn, Failure> {
    let Frame::CallReturn { witness, .. } = edge.frame else {
        return Err(Failure::Invalid);
    };
    let trace = focus.trace()?;
    if !trace.contains_return_edge(from, to, edge, budget)? {
        return Err(Failure::Invalid);
    }
    let call = trace.call(witness, budget)?;
    let before = trace.state(from, budget)?;
    let after = trace.state(to, budget)?;
    matched_return_checked(focus, edge, call, before, after, budget)
}

pub(super) fn matched_return_checked(
    focus: &CompletionFocus<'_>,
    edge: Edge,
    call: CompletionCall,
    before: &State,
    after: &State,
    budget: &mut TypeWorkBudget,
) -> Result<MatchedReturn, Failure> {
    let Frame::CallReturn {
        code,
        result,
        body,
        context,
        value_context,
        ..
    } = edge.frame
    else {
        return Err(Failure::Invalid);
    };
    if before.stack != edge.address
        || before.value_context != call.callee_value_context
        || after.stack != edge.next
        || after.context != call.caller_context
        || after.value_context != call.caller_value_context
        || (code, result, body, context, value_context)
            != (
                call.code,
                call.result,
                call.body,
                call.caller_context,
                call.caller_value_context,
            )
    {
        return Err(Failure::Invalid);
    }
    let (actual_result, actual_body, arguments, captures) = focus.values().existing_call_ports(
        call.code,
        call.caller_value_context,
        call.expression,
        call.callee_value_context,
        call.creation,
        budget,
    )?;
    if (actual_result, actual_body) != (result, body) {
        return Err(Failure::Invalid);
    }
    Ok(MatchedReturn {
        call,
        arguments,
        captures,
    })
}

/// Extract the narrow allocation-free expression fragment from actual Core.
/// The caller must independently establish that `root` is the actual pending
/// suffix and that the alias resolves to the matched return's value port.
#[cfg(test)]
pub(super) fn forwarding_suffix(
    nodes: &[StoredNode<EffectOperationFamily>],
    arena: ArenaId,
    root: NodeId,
    budget: &mut TypeWorkBudget,
) -> Result<Vec<ForwardingNode>, Failure> {
    let mut current = root;
    let mut seen = HashSet::new();
    let mut result = Vec::new();
    loop {
        charge(budget, 2)?;
        if current.arena() != arena {
            return Err(Failure::Invalid);
        }
        let index = current.index().map_err(|_| Failure::Invalid)?;
        let node = nodes.get(index).ok_or(Failure::Invalid)?;
        seen.try_reserve(1).map_err(|_| Failure::Resource)?;
        if !seen.insert(current) {
            return Err(Failure::Invalid);
        }
        result.try_reserve(1).map_err(|_| Failure::Resource)?;
        match &node.kind {
            EffectExprKind::Pure(PureExprKind::Variable(variable)) => {
                result.push(ForwardingNode::Alias {
                    node: current,
                    binder: variable.binder(),
                });
                return Ok(result);
            }
            EffectExprKind::Pure(PureExprKind::Computation(
                PureComputation::NewtypeConversion(conversion),
            )) => {
                let child = conversion.child();
                result.push(ForwardingNode::Newtype {
                    node: current,
                    child,
                });
                current = child;
            }
            // In particular, Tuple and nullary Constructor allocate Ash heap
            // cells. Bind and Match also allocate interpreter environment
            // storage; their admissibility needs a checked correspondence.
            _ => return Err(Failure::Invalid),
        }
    }
}

/// Exact structural sites seen on the converged worker trace. This is a
/// preliminary input to the all-path Message-arm judgment, never a route.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct WorkerRootSites {
    pub(super) receive: NodeId,
    pub(super) root: NodeId,
    pub(super) handler: NodeId,
    pub(super) store: NodeId,
}

/// Reconstruct the one supported receive and root/Store site from every
/// reachable occurrence. The actual Match-result and all-path correspondence
/// must still be proved before any route may be emitted.
pub(super) fn worker_root_sites(
    scope: &super::super::validate::NetworkNativeIdentityScope<'_>,
    side: usize,
    graph: &SummaryGraph,
    worker: &super::control::Analysis<'_>,
    budget: &mut TypeWorkBudget,
) -> Result<Option<WorkerRootSites>, Failure> {
    use super::control::{CompletionDetail, Control, NetworkEventStage, NetworkOutcome};
    use crate::core::effect::EffectOperation;
    let focus = worker.completion_foci.last().ok_or(Failure::Invalid)?;
    let trace = focus.trace()?;
    // The last retained focus is the original whole-worker trace, not one of
    // the freshly relocated focused Store traces.
    if trace.focus().is_ok() {
        return Err(Failure::Invalid);
    }
    let EffectExprKind::Operation(EffectOperation::Network(owner)) = &scope
        .nodes()
        .get(scope.owner().index().map_err(|_| Failure::Invalid)?)
        .ok_or(Failure::Invalid)?
        .kind
    else {
        return Err(Failure::Invalid);
    };
    let api = crate::resolved::NetworkApi::for_module(owner.acquisition.builtin)
        .ok_or(Failure::Invalid)?;
    let mut commits = false;
    let mut replies = false;
    trace.visit_states(budget, |_, state, budget| {
        let Some(Control::NetworkEvent {
            operation,
            stage,
            outcome,
            ..
        }) = graph.code.get(state.position.code)
        else {
            return Ok(());
        };
        let node = scope
            .nodes()
            .get(operation.index().map_err(|_| Failure::Invalid)?)
            .ok_or(Failure::Invalid)?;
        if operation.arena() != scope.arena() {
            return Err(Failure::Invalid);
        }
        let EffectExprKind::Operation(EffectOperation::RegionBuffer(buffer)) = &node.kind else {
            return Err(Failure::Invalid);
        };
        let crate::core::region::RegionBufferOperation::Network {
            effect,
            operation: actual,
        } = &buffer.operation
        else {
            return Err(Failure::Invalid);
        };
        if *actual != crate::types::OperationId::new(api.io(), 2) {
            return Ok(());
        }
        if *operation != scope.receive() || effect.effect() != api.io() {
            return Err(Failure::Invalid);
        }
        let operand = buffer.operand.ok_or(Failure::Invalid)?;
        if focus.values().existing_original_worker_origin(
            operand,
            scope.arena(),
            scope.nodes(),
            state.value_context,
            budget,
        )? != (
            scope.owner(),
            u8::try_from(side).map_err(|_| Failure::Invalid)?,
        ) {
            return Err(Failure::Invalid);
        }
        commits |=
            *stage == NetworkEventStage::MessageCommit && *outcome == NetworkOutcome::Message;
        replies |= *stage == NetworkEventStage::Reply && *outcome == NetworkOutcome::Message;
        Ok(())
    })?;
    let mut details = HashMap::new();
    trace.visit_details(budget, |id, detail, budget| {
        charge(budget, 1)?;
        details.try_reserve(1).map_err(|_| Failure::Resource)?;
        if details.insert(id, detail).is_some() {
            return Err(Failure::Invalid);
        }
        Ok(())
    })?;
    let mut root_sites = None;
    trace.visit_edges(budget, |from, _, transition, budget| {
        let CompletionTransition::Detail(id) = transition else {
            return Ok(());
        };
        let Some(CompletionDetail::EnterRoot { store, code, .. }) = details.get(&id).copied()
        else {
            return Ok(());
        };
        let root_index = focus
            .values()
            .original_control_node(code, scope.nodes(), budget)?;
        let EffectExprKind::Operation(EffectOperation::RetainedRoot(root)) =
            &scope.nodes()[root_index].kind
        else {
            return Err(Failure::Invalid);
        };
        let state = trace.state(from, budget)?;
        charge(budget, state.heap.len())?;
        let mut selected = None;
        for edge in state.heap.iter().filter(|edge| edge.address == store) {
            let Frame::Resource { code, .. } = edge.frame else {
                return Err(Failure::Invalid);
            };
            let store_index = focus
                .values()
                .original_control_node(code, scope.nodes(), budget)?;
            if !matches!(
                &scope.nodes()[store_index].kind,
                EffectExprKind::Operation(EffectOperation::Store(_))
            ) {
                return Err(Failure::Invalid);
            }
            if selected.is_some_and(|prior| prior != store_index) {
                return Err(Failure::Invalid);
            }
            selected = Some(store_index);
        }
        let store_index = selected.ok_or(Failure::Invalid)?;
        let candidate = WorkerRootSites {
            receive: scope.receive(),
            root: NodeId::new(
                scope.arena(),
                u32::try_from(root_index).map_err(|_| Failure::Resource)?,
            ),
            handler: root.handler,
            store: NodeId::new(
                scope.arena(),
                u32::try_from(store_index).map_err(|_| Failure::Resource)?,
            ),
        };
        if root_sites.is_some_and(|prior| prior != candidate) {
            return Err(Failure::Invalid);
        }
        root_sites = Some(candidate);
        Ok(())
    })?;
    if root_sites.is_some() && !(commits && replies) {
        return Err(Failure::Invalid);
    }
    Ok(root_sites)
}

/// A reached Application arm whose scrutinee is the checked canonical
/// receive wrapper result. This is not yet a root-correlation judgment.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct WorkerMessageArm {
    pub(super) matching: NodeId,
    pub(super) arm: usize,
}

/// Source coordinates for the narrow Unit-result worker fragment. These are
/// only inputs to the same-focus call and continuation checks.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct WorkerProcessingFragment {
    helper_call: NodeId,
    tail_match: NodeId,
    tail_call: NodeId,
    tail_argument: NodeId,
    tail_binder: BinderId,
    payload: BinderId,
    worker: BinderId,
    expected: Option<BinderId>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ProcessingHelper {
    Native(NodeId),
    Pure {
        recursive: NodeId,
        equal: NodeId,
        equal_target: usize,
    },
}

// Test-only location of the first refused structural predicate.
macro_rules! reject_processing {
    () => {{
        #[cfg(test)]
        eprintln!("processing source refusal at {}", line!());
        return Err(Failure::Invalid);
    }};
}

/// Read the two variable fields of the compiler's explicit Region tuple
/// construction. Provider provenance is checked separately in the worker C3
/// query; this structural check alone carries no completion authority.
pub(super) fn generated_tuple_fields(
    scope: &super::super::validate::NetworkNativeIdentityScope<'_>,
    id: NodeId,
    budget: &mut TypeWorkBudget,
) -> Result<[(NodeId, BinderId); 2], Failure> {
    use crate::core::effect::EffectOperation;
    charge(budget, 8)?;
    let node = |id: NodeId| {
        if id.arena() != scope.arena() {
            reject_processing!();
        }
        scope
            .nodes()
            .get(id.index().map_err(|_| Failure::Invalid)?)
            .ok_or(Failure::Invalid)
    };
    let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Bind(binding))) =
        &node(id)?.kind
    else {
        reject_processing!();
    };
    let EffectExprKind::Operation(EffectOperation::Request(query)) =
        &node(binding.initializer())?.kind
    else {
        reject_processing!();
    };
    let api = crate::resolved::RegionApi::for_module(query.effect().effect().module())
        .ok_or(Failure::Invalid)?;
    if query.effect().effect() != api.default_alloc()
        || !query.effect().arguments().is_empty()
        || query.operation() != crate::types::OperationId::new(api.default_alloc(), 1)
        || !matches!(
            &node(query.operand())?.kind,
            EffectExprKind::Pure(PureExprKind::Value(super::PureValue::Unit(_)))
        )
    {
        reject_processing!();
    }
    let EffectExprKind::Operation(EffectOperation::RegionTuple(tuple)) =
        &node(binding.body())?.kind
    else {
        reject_processing!();
    };
    let EffectExprKind::Pure(PureExprKind::Variable(context)) = &node(tuple.context)?.kind else {
        reject_processing!();
    };
    let EffectExprKind::Operation(EffectOperation::RegionAllocate(allocation)) =
        &node(tuple.storage)?.kind
    else {
        reject_processing!();
    };
    let EffectExprKind::Operation(EffectOperation::RegionValueRequest(request)) =
        &node(allocation.request)?.kind
    else {
        reject_processing!();
    };
    if tuple.constructor.is_some()
        || tuple.api != api.module()
        || allocation.api != tuple.api
        || allocation.context != tuple.context
        || context.binder() != binding.binder().id()
        || request.api != tuple.api
        || request.fields != 2
    {
        reject_processing!();
    }
    let [first, second] = tuple.fields.as_ref() else {
        reject_processing!();
    };
    let field = |id| match &node(id)?.kind {
        EffectExprKind::Pure(PureExprKind::Variable(value)) => Ok((id, value.binder())),
        _ => Err(Failure::Invalid),
    };
    Ok([field(*first)?, field(*second)?])
}

/// Authenticate one actual ordered `(Worker, Bytes)` call and its callee's
/// outer tuple destructuring in the same converged value focus.
#[expect(
    clippy::type_complexity,
    reason = "The checked tuple carries its actual node, parameter binders and ordered fields"
)]
pub(super) fn checked_worker_tuple_call(
    scope: &super::super::validate::NetworkNativeIdentityScope<'_>,
    side: usize,
    values: &super::value::Analysis<'_>,
    call: CompletionCall,
    argument: NodeId,
    budget: &mut TypeWorkBudget,
) -> Result<(NodeId, [BinderId; 2], [(NodeId, BinderId); 2]), Failure> {
    use crate::core::{data::CorePatternKind, effect::EffectOperation};
    let fields = generated_tuple_fields(scope, argument, budget)?;
    let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Bind(binding))) = &scope
        .nodes()
        .get(argument.index().map_err(|_| Failure::Invalid)?)
        .ok_or(Failure::Invalid)?
        .kind
    else {
        return Err(Failure::Invalid);
    };
    let EffectExprKind::Operation(EffectOperation::RegionClosure(closure)) = &scope
        .nodes()
        .get(call.expression)
        .ok_or(Failure::Invalid)?
        .kind
    else {
        return Err(Failure::Invalid);
    };
    if call.target != call.expression {
        return Err(Failure::Invalid);
    }
    let function = closure.code.function().ok_or(Failure::Invalid)?;
    let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Match(outer))) = &scope
        .nodes()
        .get(function.body().index().map_err(|_| Failure::Invalid)?)
        .ok_or(Failure::Invalid)?
        .kind
    else {
        return Err(Failure::Invalid);
    };
    let EffectExprKind::Pure(PureExprKind::Variable(parameter)) = &scope
        .nodes()
        .get(outer.scrutinee().index().map_err(|_| Failure::Invalid)?)
        .ok_or(Failure::Invalid)?
        .kind
    else {
        return Err(Failure::Invalid);
    };
    let [arm] = outer.arms() else {
        return Err(Failure::Invalid);
    };
    let CorePatternKind::Tuple(pattern) = &arm.pattern().kind else {
        return Err(Failure::Invalid);
    };
    let [worker, carried] = pattern.as_ref() else {
        return Err(Failure::Invalid);
    };
    let (CorePatternKind::Binder(worker), CorePatternKind::Binder(carried)) =
        (&worker.kind, &carried.kind)
    else {
        return Err(Failure::Invalid);
    };
    if parameter.binder() != function.parameter().id() || worker.id() == carried.id() {
        return Err(Failure::Invalid);
    }
    let (_, _, arguments, _) = values.existing_call_ports(
        call.code,
        call.caller_value_context,
        call.expression,
        call.callee_value_context,
        call.creation,
        budget,
    )?;
    if arguments.len() != 1 {
        return Err(Failure::Invalid);
    }
    let (argument_port, worker_origin) = values
        .existing_original_tuple_worker_origin(
            argument,
            binding.body(),
            [fields[0].0, fields[1].0],
            scope.arena(),
            scope.nodes(),
            call.caller_value_context,
            budget,
        )
        .inspect_err(|error| {
            #[cfg(test)]
            eprintln!("tuple call: original fields: {error:?}");
            let _ = error;
        })?;
    if arguments[0].1 != argument_port {
        return Err(Failure::Invalid);
    }
    if worker_origin
        != (
            scope.owner(),
            u8::try_from(side).map_err(|_| Failure::Invalid)?,
        )
    {
        return Err(Failure::Invalid);
    }
    let outer_code = function
        .body()
        .index()
        .map_err(|_| Failure::Invalid)?
        .checked_add(1)
        .ok_or(Failure::Resource)?;
    let (projection_context, formal_port) =
        values.existing_worker_projection_context(call, budget)?;
    let bindings = values
        .existing_arm_bindings(outer_code, 0, projection_context, budget)
        .inspect_err(|error| {
            #[cfg(test)]
            eprintln!("tuple call: arm bindings: {error:?}");
            let _ = error;
        })?;
    if bindings.len() != 2 {
        return Err(Failure::Invalid);
    }
    let scrutinee_code = outer
        .scrutinee()
        .index()
        .map_err(|_| Failure::Invalid)?
        .checked_add(1)
        .ok_or(Failure::Resource)?;
    let (scrutinee, parameter) = values
        .existing_forward_ports(scrutinee_code, projection_context, budget)
        .inspect_err(|error| {
            #[cfg(test)]
            eprintln!("tuple call: scrutinee ports: {error:?}");
            let _ = error;
        })?;
    if parameter != formal_port {
        return Err(Failure::Invalid);
    }
    // Pattern lowering uses a LIFO worklist, so binding enumeration is not
    // field order. Authenticate each original projection's explicit ordinal.
    let mut seen = [false; 2];
    for (_, projection) in &bindings {
        let (source, field, constructor) =
            values.existing_pattern_projection(*projection, budget)?;
        if source != scrutinee || constructor.is_some() || field >= seen.len() || seen[field] {
            return Err(Failure::Invalid);
        }
        seen[field] = true;
    }
    if seen != [true, true] {
        return Err(Failure::Invalid);
    }
    Ok((arm.body(), [worker.id(), carried.id()], fields))
}

fn worker_processing_fragment(
    scope: &super::super::validate::NetworkNativeIdentityScope<'_>,
    route: &crate::core::dialect::NetworkProcessingRoute,
    budget: &mut TypeWorkBudget,
) -> Result<WorkerProcessingFragment, Failure> {
    use crate::core::{data::CorePatternKind, effect::EffectOperation};
    use crate::types::Type;
    // The supported fragment has a fixed number of source nodes; all node
    // lookups and the single clause/arm checks are paid before inspection.
    charge(budget, 32)?;
    let node = |id: NodeId| {
        if id.arena() != scope.arena() {
            reject_processing!();
        }
        scope
            .nodes()
            .get(id.index().map_err(|_| Failure::Invalid)?)
            .ok_or(Failure::Invalid)
    };
    let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Match(receive))) =
        &node(route.message_match)?.kind
    else {
        reject_processing!();
    };
    let arm = receive.arms().get(route.arm).ok_or(Failure::Invalid)?;
    let CorePatternKind::Constructor {
        payload: Some(pattern),
        ..
    } = &arm.pattern().kind
    else {
        reject_processing!();
    };
    let CorePatternKind::Tuple(fields) = &pattern.kind else {
        reject_processing!();
    };
    let [_, payload] = fields.as_ref() else {
        reject_processing!();
    };
    let CorePatternKind::Binder(payload) = &payload.kind else {
        reject_processing!();
    };
    let EffectExprKind::Operation(EffectOperation::Store(store)) = &node(route.store)?.kind else {
        reject_processing!();
    };
    if store.body != route.root
        || !matches!(
            &node(store.initializer)?.kind,
            EffectExprKind::Pure(PureExprKind::Value(super::PureValue::Unit(_)))
        )
    {
        reject_processing!();
    }
    let EffectExprKind::Operation(EffectOperation::RetainedRoot(root)) = &node(route.root)?.kind
    else {
        reject_processing!();
    };
    let EffectExprKind::Pure(PureExprKind::Variable(store_handle)) = &node(root.store)?.kind else {
        reject_processing!();
    };
    if root.handler != route.handler || store_handle.binder() != store.handle.id() {
        reject_processing!();
    }
    let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Apply(receive_call))) =
        &node(receive.scrutinee())?.kind
    else {
        reject_processing!();
    };
    let EffectExprKind::Pure(PureExprKind::Variable(receive_worker)) =
        &node(receive_call.argument())?.kind
    else {
        reject_processing!();
    };
    let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Match(after_store))) =
        &node(arm.body())?.kind
    else {
        reject_processing!();
    };
    if after_store.scrutinee() != route.store || node(route.store)?.ty != Type::Unit {
        reject_processing!();
    }
    let [after_arm] = after_store.arms() else {
        reject_processing!();
    };
    if !matches!(after_arm.pattern().kind, CorePatternKind::Wildcard)
        || after_arm.pattern().ty != Type::Unit
    {
        reject_processing!();
    }
    let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Apply(tail))) =
        &node(after_arm.body())?.kind
    else {
        reject_processing!();
    };
    let (tail_worker, expected) = match &node(tail.argument())?.kind {
        EffectExprKind::Pure(PureExprKind::Variable(worker)) => (worker.binder(), None),
        _ => {
            let [(_, worker), (_, expected)] =
                generated_tuple_fields(scope, tail.argument(), budget)?;
            (worker, Some(expected))
        }
    };
    if tail_worker != receive_worker.binder()
        || tail_worker == payload.id()
        || expected == Some(payload.id())
        || expected == Some(tail_worker)
    {
        reject_processing!();
    }
    let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::TypeApplication(
        tail_type,
    ))) = &node(tail.function())?.kind
    else {
        reject_processing!();
    };
    let EffectExprKind::Pure(PureExprKind::Variable(tail_function)) =
        &node(tail_type.function())?.kind
    else {
        reject_processing!();
    };
    let EffectExprKind::Operation(EffectOperation::Handler(handler)) = &node(route.handler)?.kind
    else {
        reject_processing!();
    };
    let [clause] = handler.clauses() else {
        reject_processing!();
    };
    let EffectExprKind::Operation(EffectOperation::Resume(resume)) = &node(clause.body())?.kind
    else {
        reject_processing!();
    };
    if resume.handler() != handler.id()
        || resume.owner() != clause.resume()
        || !matches!(
            &node(resume.value())?.kind,
            EffectExprKind::Pure(PureExprKind::Value(super::PureValue::Unit(_)))
        )
    {
        reject_processing!();
    }
    let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Match(process))) =
        &node(handler.body())?.kind
    else {
        reject_processing!();
    };
    let [process_arm] = process.arms() else {
        reject_processing!();
    };
    if !matches!(process_arm.pattern().kind, CorePatternKind::Wildcard)
        || process_arm.pattern().ty != Type::Unit
    {
        reject_processing!();
    }
    let EffectExprKind::Operation(EffectOperation::Request(request)) =
        &node(process.scrutinee())?.kind
    else {
        reject_processing!();
    };
    if request.effect() != handler.effect()
        || request.operation() != clause.operation()
        || !matches!(
            &node(request.operand())?.kind,
            EffectExprKind::Pure(PureExprKind::Value(super::PureValue::Unit(_)))
        )
    {
        reject_processing!();
    }
    let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Apply(helper))) =
        &node(process_arm.body())?.kind
    else {
        reject_processing!();
    };
    match expected {
        None => {
            let EffectExprKind::Pure(PureExprKind::Variable(argument)) =
                &node(helper.argument())?.kind
            else {
                reject_processing!();
            };
            if argument.binder() != payload.id() {
                reject_processing!();
            }
        }
        Some(expected) => {
            let [(_, message), (_, carried)] =
                generated_tuple_fields(scope, helper.argument(), budget)?;
            if message != payload.id() || carried != expected {
                reject_processing!();
            }
        }
    }
    Ok(WorkerProcessingFragment {
        helper_call: process_arm.body(),
        tail_match: arm.body(),
        tail_call: after_arm.body(),
        tail_argument: tail.argument(),
        tail_binder: tail_function.binder(),
        payload: payload.id(),
        worker: tail_worker,
        expected,
    })
}

/// Authenticate the narrow imported helper body: the actual parameter is
/// supplied to one admitted Void native request and its result is discarded
/// before returning literal Unit. Host behavior remains an external premise.
fn checked_native_unit_helper(
    scope: &super::super::validate::NetworkNativeIdentityScope<'_>,
    call: CompletionCall,
    budget: &mut TypeWorkBudget,
) -> Result<NodeId, Failure> {
    use crate::core::{data::CorePatternKind, effect::EffectOperation};
    use crate::types::Type;
    charge(budget, 16)?;
    if call.target != call.expression || call.creation != 0 {
        return Err(Failure::Invalid);
    }
    let node = |id: NodeId| {
        if id.arena() != scope.arena() {
            return Err(Failure::Invalid);
        }
        scope
            .nodes()
            .get(id.index().map_err(|_| Failure::Invalid)?)
            .ok_or(Failure::Invalid)
    };
    let expression = NodeId::new(
        scope.arena(),
        u32::try_from(call.expression).map_err(|_| Failure::Resource)?,
    );
    let EffectExprKind::Operation(EffectOperation::RegionClosure(closure)) =
        &node(expression)?.kind
    else {
        return Err(Failure::Invalid);
    };
    let function = closure.code.function().ok_or(Failure::Invalid)?;
    let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Match(body))) =
        &node(function.body())?.kind
    else {
        return Err(Failure::Invalid);
    };
    let [arm] = body.arms() else {
        return Err(Failure::Invalid);
    };
    if !matches!(arm.pattern().kind, CorePatternKind::Wildcard)
        || arm.pattern().ty != Type::Unit
        || !matches!(
            &node(arm.body())?.kind,
            EffectExprKind::Pure(PureExprKind::Value(super::PureValue::Unit(_)))
        )
    {
        return Err(Failure::Invalid);
    }
    let request_id = body.scrutinee();
    let EffectExprKind::Operation(EffectOperation::Request(request)) = &node(request_id)?.kind
    else {
        return Err(Failure::Invalid);
    };
    if node(request_id)?.ty != Type::Unit {
        return Err(Failure::Invalid);
    }
    let EffectExprKind::Pure(PureExprKind::Variable(argument)) = &node(request.operand())?.kind
    else {
        return Err(Failure::Invalid);
    };
    if argument.binder() != function.parameter().id() {
        return Err(Failure::Invalid);
    }
    let EffectExprKind::Operation(EffectOperation::NativeInterpret(native)) =
        &node(scope.root())?.kind
    else {
        return Err(Failure::Invalid);
    };
    charge(budget, native.interpretations().len())?;
    let mut admitted = false;
    for interpretation in native.interpretations() {
        if interpretation.effect() != request.effect()
            || interpretation.symbol().operation() != request.operation()
        {
            continue;
        }
        if admitted
            || interpretation.symbol().result()
                != crate::foreign::checked_source::NativeResult::Void
            || !scope
                .authenticates(interpretation, budget)
                .map_err(|_| Failure::Resource)?
        {
            return Err(Failure::Invalid);
        }
        admitted = true;
    }
    if admitted {
        Ok(request_id)
    } else {
        Err(Failure::Invalid)
    }
}

/// Recognize the closed two-Bytes comparison loop used by the copied-message
/// worker. A recursive edge is only an inspected body edge: a return must
/// still be witnessed by the focused completion trace.
fn checked_pure_unit_helper(
    scope: &super::super::validate::NetworkNativeIdentityScope<'_>,
    call: CompletionCall,
    budget: &mut TypeWorkBudget,
) -> Result<(NodeId, NodeId, usize), Failure> {
    use crate::core::{data::CorePatternKind, effect::EffectOperation, packed::Intrinsic};
    charge(
        budget,
        24usize.saturating_add(scope.bindings().len().saturating_mul(2)),
    )?;
    let node = |id: NodeId| {
        if id.arena() != scope.arena() {
            reject_processing!();
        }
        scope
            .nodes()
            .get(id.index().map_err(|_| Failure::Invalid)?)
            .ok_or(Failure::Invalid)
    };
    if call.target != call.expression {
        reject_processing!();
    }
    let expression = NodeId::new(
        scope.arena(),
        u32::try_from(call.expression).map_err(|_| Failure::Resource)?,
    );
    let EffectExprKind::Operation(EffectOperation::RegionClosure(closure)) =
        &node(expression)?.kind
    else {
        reject_processing!();
    };
    let function = closure.code.function().ok_or(Failure::Invalid)?;
    let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Match(pattern))) =
        &node(function.body())?.kind
    else {
        reject_processing!();
    };
    let EffectExprKind::Pure(PureExprKind::Variable(parameter)) = &node(pattern.scrutinee())?.kind
    else {
        reject_processing!();
    };
    let [arm] = pattern.arms() else {
        reject_processing!();
    };
    let CorePatternKind::Tuple(fields) = &arm.pattern().kind else {
        reject_processing!();
    };
    let [first, second] = fields.as_ref() else {
        reject_processing!();
    };
    let (CorePatternKind::Binder(first), CorePatternKind::Binder(second)) =
        (&first.kind, &second.kind)
    else {
        reject_processing!();
    };
    if parameter.binder() != function.parameter().id() || first.id() == second.id() {
        reject_processing!();
    }
    let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Match(result))) =
        &node(arm.body())?.kind
    else {
        reject_processing!();
    };
    let [yes, no] = result.arms() else {
        reject_processing!();
    };
    if !matches!(yes.pattern().kind, CorePatternKind::Boolean(true))
        || !matches!(no.pattern().kind, CorePatternKind::Boolean(false))
        || !matches!(
            &node(yes.body())?.kind,
            EffectExprKind::Pure(PureExprKind::Value(super::PureValue::Unit(_)))
        )
    {
        reject_processing!();
    }
    let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Apply(equal))) =
        &node(result.scrutinee())?.kind
    else {
        reject_processing!();
    };
    let EffectExprKind::Pure(PureExprKind::Variable(equal_name)) = &node(equal.function())?.kind
    else {
        reject_processing!();
    };
    let [(_, equal_first), (_, equal_second)] =
        generated_tuple_fields(scope, equal.argument(), budget)?;
    if (equal_first, equal_second) != (first.id(), second.id()) {
        reject_processing!();
    }
    let mut equal_bindings = scope
        .bindings()
        .iter()
        .filter(|(binder, _)| *binder == equal_name.binder());
    let equal_definition = equal_bindings.next().ok_or(Failure::Invalid)?.1;
    if equal_bindings.next().is_some() {
        reject_processing!();
    }
    let EffectExprKind::Pure(PureExprKind::Value(super::PureValue::Intrinsic(intrinsic))) =
        &node(equal_definition)?.kind
    else {
        reject_processing!();
    };
    if intrinsic.operation() != Intrinsic::BytesEqual || !intrinsic.module().is_builtin_bytes() {
        reject_processing!();
    }
    let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Apply(recursive))) =
        &node(no.body())?.kind
    else {
        reject_processing!();
    };
    let EffectExprKind::Pure(PureExprKind::Variable(self_name)) = &node(recursive.function())?.kind
    else {
        reject_processing!();
    };
    let [(_, recur_first), (_, recur_second)] =
        generated_tuple_fields(scope, recursive.argument(), budget)?;
    if (recur_first, recur_second) != (first.id(), second.id()) {
        reject_processing!();
    }
    let mut self_bindings = scope
        .bindings()
        .iter()
        .filter(|(binder, _)| *binder == self_name.binder());
    let initializer = self_bindings.next().ok_or(Failure::Invalid)?.1;
    if self_bindings.next().is_some() {
        reject_processing!();
    }
    let (actual, _) = crate::core::region::closure_initializer::<
        crate::core::effect::EffectOperationFamily,
    >(initializer, |id| node(id).ok().map(|node| &node.kind))
    .ok_or(Failure::Invalid)?;
    if actual != expression {
        reject_processing!();
    }
    charge(budget, closure.captures.len())?;
    let mut found_self = false;
    let mut found_equal = false;
    for capture in &closure.captures {
        let EffectExprKind::Pure(PureExprKind::Variable(variable)) = &node(*capture)?.kind else {
            reject_processing!();
        };
        if variable.binder() == self_name.binder() {
            found_self = true;
        } else if variable.binder() == equal_name.binder() {
            found_equal = true;
        } else {
            reject_processing!();
        }
    }
    if !found_self || !found_equal {
        reject_processing!();
    }
    Ok((
        no.body(),
        result.scrutinee(),
        equal_definition.index().map_err(|_| Failure::Invalid)?,
    ))
}

/// Check one real tail/caller alternative against the linked, pre-message
/// global factory. Each snapshot retains its own creation and capture ports.
fn checked_global_worker_call(
    scope: &super::super::validate::NetworkNativeIdentityScope<'_>,
    route: &crate::core::dialect::NetworkProcessingRoute,
    fragment: WorkerProcessingFragment,
    values: &super::value::Analysis<'_>,
    call: CompletionCall,
    budget: &mut TypeWorkBudget,
) -> Result<(), Failure> {
    use crate::core::effect::EffectOperation;
    charge(budget, scope.bindings().len())?;
    let mut bindings = scope
        .bindings()
        .iter()
        .filter(|(binder, _)| *binder == fragment.tail_binder);
    let initializer = bindings.next().ok_or(Failure::Invalid)?.1;
    if bindings.next().is_some() {
        reject_processing!();
    }
    let mut cursor = initializer;
    let mut parameters = Vec::new();
    loop {
        charge(budget, 1)?;
        if cursor.arena() != scope.arena() {
            reject_processing!();
        }
        let Some(node) = scope
            .nodes()
            .get(cursor.index().map_err(|_| Failure::Invalid)?)
        else {
            reject_processing!();
        };
        let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::TypeAbstraction(
            abstraction,
        ))) = &node.kind
        else {
            break;
        };
        charge(budget, abstraction.parameters().len())?;
        parameters
            .try_reserve(abstraction.parameters().len())
            .map_err(|_| Failure::Resource)?;
        parameters.extend(
            abstraction
                .parameters()
                .iter()
                .map(|(parameter, _)| *parameter),
        );
        cursor = abstraction.body();
    }
    if parameters.is_empty()
        || !matches!(
            &scope.nodes()[cursor.index().map_err(|_| Failure::Invalid)?].kind,
            EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Bind(_)))
        )
    {
        reject_processing!();
    }
    let [target, _] = super::linked_worker_functions(
        scope.nodes(),
        scope.arena(),
        [initializer, initializer],
        budget,
    )?;
    if call.target != target || call.expression != target {
        reject_processing!();
    }
    let EffectExprKind::Operation(EffectOperation::RegionClosure(closure)) =
        &scope.nodes().get(target).ok_or(Failure::Invalid)?.kind
    else {
        reject_processing!();
    };
    let function = closure.code.function().ok_or(Failure::Invalid)?;
    if let Some(expected) = fragment.expected {
        use crate::core::data::CorePatternKind;
        let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Match(outer))) = &scope
            .nodes()
            .get(function.body().index().map_err(|_| Failure::Invalid)?)
            .ok_or(Failure::Invalid)?
            .kind
        else {
            reject_processing!();
        };
        let EffectExprKind::Pure(PureExprKind::Variable(parameter)) = &scope
            .nodes()
            .get(outer.scrutinee().index().map_err(|_| Failure::Invalid)?)
            .ok_or(Failure::Invalid)?
            .kind
        else {
            reject_processing!();
        };
        let [arm] = outer.arms() else {
            reject_processing!();
        };
        let CorePatternKind::Tuple(fields) = &arm.pattern().kind else {
            reject_processing!();
        };
        let [worker, carried] = fields.as_ref() else {
            reject_processing!();
        };
        if parameter.binder() != function.parameter().id()
            || arm.body() != route.message_match
            || !matches!(&worker.kind, CorePatternKind::Binder(b) if b.id() == fragment.worker)
            || !matches!(&carried.kind, CorePatternKind::Binder(b) if b.id() == expected)
        {
            reject_processing!();
        }
    } else if function.body() != route.message_match {
        reject_processing!();
    }
    #[cfg(test)]
    if fragment.expected.is_some() {
        eprintln!("pure tail: loop body authenticated");
    }
    let EffectExprKind::Operation(EffectOperation::Region(region)) = &scope
        .nodes()
        .get(scope.entry_region().index().map_err(|_| Failure::Invalid)?)
        .ok_or(Failure::Invalid)?
        .kind
    else {
        reject_processing!();
    };
    charge(
        budget,
        closure
            .captures
            .len()
            .checked_mul(scope.bindings().len().saturating_add(1))
            .ok_or(Failure::Resource)?,
    )?;
    for capture in &closure.captures {
        if capture.arena() != scope.arena() {
            reject_processing!();
        }
        let EffectExprKind::Pure(PureExprKind::Variable(variable)) = &scope
            .nodes()
            .get(capture.index().map_err(|_| Failure::Invalid)?)
            .ok_or(Failure::Invalid)?
            .kind
        else {
            reject_processing!();
        };
        let binder = variable.binder();
        if binder == fragment.payload
            || binder == fragment.worker
            || (binder != region.access.id()
                && !scope.bindings().iter().any(|(global, _)| *global == binder))
        {
            reject_processing!();
        }
    }
    #[cfg(test)]
    if fragment.expected.is_some() {
        eprintln!("pure tail: captures authenticated");
    }
    let original = values.original_control_node(call.code, scope.nodes(), budget)?;
    let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Apply(application))) =
        &scope.nodes().get(original).ok_or(Failure::Invalid)?.kind
    else {
        reject_processing!();
    };
    if original == fragment.tail_call.index().map_err(|_| Failure::Invalid)?
        && application.argument() != fragment.tail_argument
    {
        reject_processing!();
    }
    let worker_argument = if let Some(expected) = fragment.expected {
        let [(worker, _), (_, carried)] =
            generated_tuple_fields(scope, application.argument(), budget)?;
        // The only accepted initial value is the Bytes projection of the
        // actual authenticated worker entry; recursive invocations must carry
        // the loop's own immutable projection unchanged.
        let (mut entry, _) = scope.entry(route.side).ok_or(Failure::Invalid)?;
        loop {
            charge(budget, 1)?;
            match &scope
                .nodes()
                .get(entry.index().map_err(|_| Failure::Invalid)?)
                .ok_or(Failure::Invalid)?
                .kind
            {
                EffectExprKind::Pure(PureExprKind::Computation(
                    PureComputation::TypeAbstraction(abstraction),
                )) => entry = abstraction.body(),
                _ => break,
            }
        }
        let (_, entry_closure) = crate::core::region::closure_initializer::<
            crate::core::effect::EffectOperationFamily,
        >(entry, |id| {
            (id.arena() == scope.arena())
                .then(|| scope.nodes().get(id.index().ok()?))
                .flatten()
                .map(|node| &node.kind)
        })
        .ok_or(Failure::Invalid)?;
        let entry_function = entry_closure.code.function().ok_or(Failure::Invalid)?;
        let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Match(entry_match))) =
            &scope
                .nodes()
                .get(
                    entry_function
                        .body()
                        .index()
                        .map_err(|_| Failure::Invalid)?,
                )
                .ok_or(Failure::Invalid)?
                .kind
        else {
            reject_processing!();
        };
        let [entry_arm] = entry_match.arms() else {
            reject_processing!();
        };
        let crate::core::data::CorePatternKind::Tuple(fields) = &entry_arm.pattern().kind else {
            reject_processing!();
        };
        let [_, entry_bytes] = fields.as_ref() else {
            reject_processing!();
        };
        let crate::core::data::CorePatternKind::Binder(entry_bytes) = &entry_bytes.kind else {
            reject_processing!();
        };
        let EffectExprKind::Pure(PureExprKind::Variable(entry_parameter)) = &scope
            .nodes()
            .get(
                entry_match
                    .scrutinee()
                    .index()
                    .map_err(|_| Failure::Invalid)?,
            )
            .ok_or(Failure::Invalid)?
            .kind
        else {
            reject_processing!();
        };
        if entry_parameter.binder() != entry_function.parameter().id()
            || (carried != expected && carried != entry_bytes.id())
        {
            reject_processing!();
        }
        worker
    } else {
        application.argument()
    };
    if fragment.expected.is_none() {
        let worker_origin = values.existing_original_worker_origin(
            worker_argument,
            scope.arena(),
            scope.nodes(),
            call.caller_value_context,
            budget,
        )?;
        if worker_origin
            != (
                route.owner,
                u8::try_from(route.side).map_err(|_| Failure::Invalid)?,
            )
        {
            reject_processing!();
        }
    }
    #[cfg(test)]
    if fragment.expected.is_some() {
        eprintln!("pure tail: entry/carry/worker authenticated");
    }
    let (_, _, arguments, captures) = values.existing_call_ports(
        call.code,
        call.caller_value_context,
        call.expression,
        call.callee_value_context,
        call.creation,
        budget,
    )?;
    if arguments.len() != 1 {
        reject_processing!();
    }
    #[cfg(test)]
    if fragment.expected.is_some() {
        eprintln!("pure tail: actual call ports found");
    }
    if let Some(expected) = fragment.expected {
        let (body, binders, _) = checked_worker_tuple_call(
            scope,
            route.side,
            values,
            call,
            application.argument(),
            budget,
        )
        .inspect_err(|error| {
            #[cfg(test)]
            eprintln!("pure tail: tuple port relation: {error:?}");
            let _ = error;
        })?;
        if body != route.message_match || binders != [fragment.worker, expected] {
            reject_processing!();
        }
    }
    values.check_closed_global_capture_ports(
        target,
        call.creation,
        call.callee_value_context,
        &closure.captures,
        closure.context,
        &parameters,
        scope.arena(),
        scope.nodes(),
        &captures,
        budget,
    )
}

/// Check the actual canonical receive result and ordered Application arm.
/// Every candidate remains focus-local until the subsequent all-path check.
pub(super) fn worker_message_arm(
    scope: &super::super::validate::NetworkNativeIdentityScope<'_>,
    graph: &SummaryGraph,
    worker: &super::control::Analysis<'_>,
    sites: WorkerRootSites,
    budget: &mut TypeWorkBudget,
) -> Result<WorkerMessageArm, Failure> {
    use super::control::{CompletionDetail, Control};
    use crate::core::{data::CorePatternKind, effect::EffectOperation};
    let focus = worker.completion_foci.last().ok_or(Failure::Invalid)?;
    let trace = focus.trace()?;
    if trace.focus().is_ok() {
        return Err(Failure::Invalid);
    }
    let EffectExprKind::Operation(EffectOperation::Network(owner)) = &scope
        .nodes()
        .get(scope.owner().index().map_err(|_| Failure::Invalid)?)
        .ok_or(Failure::Invalid)?
        .kind
    else {
        return Err(Failure::Invalid);
    };
    let module = owner.acquisition.builtin;
    let message = crate::types::ConstructorId::new(crate::types::NominalTypeId::new(module, 6), 0);
    let application =
        crate::types::ConstructorId::new(crate::types::NominalTypeId::new(module, 3), 0);

    // All indices borrow the same final trace and value revision. Traversal
    // and allocation are prepaid; no index survives this query.
    let states = trace.indexed_states(budget)?;
    let edges = trace.indexed_edges(budget)?;
    let mut calls: HashMap<(usize, usize, usize), Vec<(usize, CompletionCall)>> = HashMap::new();
    trace.visit_calls(budget, |witness, call, budget| {
        let original = match focus
            .values()
            .original_control_node(call.code, scope.nodes(), budget)
        {
            Ok(original) => original,
            Err(Failure::Invalid) => return Ok(()),
            Err(other) => return Err(other),
        };
        charge(budget, 4)?;
        calls.try_reserve(1).map_err(|_| Failure::Resource)?;
        let bucket = calls
            .entry((original, call.caller_context, call.caller_value_context))
            .or_default();
        bucket.try_reserve(1).map_err(|_| Failure::Resource)?;
        bucket.push((witness, call));
        Ok(())
    })?;
    let mut details = HashMap::new();
    trace.visit_details(budget, |id, detail, budget| {
        charge(budget, 1)?;
        details.try_reserve(1).map_err(|_| Failure::Resource)?;
        if details.insert(id, detail).is_some() {
            return Err(Failure::Invalid);
        }
        Ok(())
    })?;
    let mut needed: HashMap<usize, CompletionCall> = HashMap::new();
    let mut found = None;
    let mut inspected = HashSet::new();
    charge(budget, edges.len())?;
    for &(from, _, transition) in &edges {
        let CompletionTransition::Choice { ordinal } = transition else {
            continue;
        };
        charge(budget, 1)?;
        if inspected.contains(&(from, ordinal)) {
            continue;
        }
        inspected.try_reserve(1).map_err(|_| Failure::Resource)?;
        inspected.insert((from, ordinal));
        let before = states
            .get(from)
            .copied()
            .flatten()
            .ok_or(Failure::Invalid)?;
        if !matches!(
            graph.code.get(before.position.code),
            Some(Control::Choice(_))
        ) {
            continue;
        }
        let match_index =
            focus
                .values()
                .original_control_node(before.position.code, scope.nodes(), budget)?;
        let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Match(matching))) =
            &scope.nodes()[match_index].kind
        else {
            continue;
        };
        let Some(arm) = matching.arms().get(ordinal) else {
            return Err(Failure::Invalid);
        };
        let CorePatternKind::Constructor {
            constructor,
            payload: Some(payload),
        } = &arm.pattern().kind
        else {
            continue;
        };
        if *constructor != message {
            continue;
        }
        let CorePatternKind::Tuple(fields) = &payload.kind else {
            continue;
        };
        let [kind, payload] = fields.as_ref() else {
            continue;
        };
        if !matches!(&kind.kind, CorePatternKind::Constructor { constructor, payload: None } if *constructor == application)
            || !matches!(
                &payload.kind,
                CorePatternKind::Binder(_) | CorePatternKind::Wildcard
            )
        {
            continue;
        }
        let (scrutinee, _, _) = focus
            .values()
            .existing_choice(before.position.code, before.value_context, budget)?
            .ok_or(Failure::Invalid)?;
        let scrutinee_index = matching.scrutinee().index().map_err(|_| Failure::Invalid)?;
        if matching.scrutinee().arena() != scope.arena() {
            return Err(Failure::Invalid);
        }
        let bindings = focus.values().existing_arm_bindings(
            before.position.code,
            ordinal,
            before.value_context,
            budget,
        )?;
        if matches!(&payload.kind, CorePatternKind::Binder(_)) {
            let [(_, value)] = bindings.as_slice() else {
                return Err(Failure::Invalid);
            };
            let (message_payload, field, constructor) =
                focus.values().existing_pattern_projection(*value, budget)?;
            if field != 1 || constructor.is_some() {
                return Err(Failure::Invalid);
            }
            let (source, field, constructor) = focus
                .values()
                .existing_pattern_projection(message_payload, budget)?;
            if source != scrutinee || field != 0 || constructor != Some(message) {
                return Err(Failure::Invalid);
            }
        } else if !bindings.is_empty() {
            return Err(Failure::Invalid);
        }
        let compatible = calls
            .get(&(scrutinee_index, before.context, before.value_context))
            .ok_or(Failure::Invalid)?;
        if compatible.is_empty() {
            return Err(Failure::Invalid);
        }
        charge(budget, compatible.len())?;
        for &(witness, call) in compatible {
            if call.result != scrutinee || call.target != call.expression {
                return Err(Failure::Invalid);
            }
            let EffectExprKind::Operation(EffectOperation::RegionClosure(closure)) = &scope
                .nodes()
                .get(call.expression)
                .ok_or(Failure::Invalid)?
                .kind
            else {
                return Err(Failure::Invalid);
            };
            let function = closure.code.function().ok_or(Failure::Invalid)?;
            let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Bind(binding))) =
                &scope
                    .nodes()
                    .get(function.body().index().map_err(|_| Failure::Invalid)?)
                    .ok_or(Failure::Invalid)?
                    .kind
            else {
                return Err(Failure::Invalid);
            };
            if binding.body() != sites.receive || !closure.captures.is_empty() {
                return Err(Failure::Invalid);
            }
            let receive_index = sites.receive.index().map_err(|_| Failure::Invalid)?;
            let actual_body =
                focus
                    .values()
                    .existing_bind_body_port(call.body, receive_index, budget)?;
            let receive_code = receive_index.checked_add(1).ok_or(Failure::Resource)?;
            if focus
                .values()
                .original_control_node(receive_code, scope.nodes(), budget)?
                != receive_index
                || actual_body
                    != focus.values().existing_port(
                        receive_code,
                        call.callee_value_context,
                        budget,
                    )?
            {
                return Err(Failure::Invalid);
            }
            charge(budget, 1)?;
            needed.try_reserve(1).map_err(|_| Failure::Resource)?;
            if needed
                .insert(witness, call)
                .is_some_and(|prior| prior != call)
            {
                return Err(Failure::Invalid);
            }
        }
        let candidate = WorkerMessageArm {
            matching: NodeId::new(
                scope.arena(),
                u32::try_from(match_index).map_err(|_| Failure::Resource)?,
            ),
            arm: ordinal,
        };
        if found.is_some_and(|prior| prior != candidate) {
            return Err(Failure::Invalid);
        }
        found = Some(candidate);
    }
    let result = found.ok_or(Failure::Invalid)?;
    let mut entered = HashSet::new();
    let mut returned = HashSet::new();
    charge(budget, edges.len())?;
    for &(from, to, transition) in &edges {
        if let CompletionTransition::Call {
            target,
            value_context,
            expression,
            creation,
        } = transition
        {
            let before = states
                .get(from)
                .copied()
                .flatten()
                .ok_or(Failure::Invalid)?;
            let after = states.get(to).copied().flatten().ok_or(Failure::Invalid)?;
            charge(budget, after.heap.len())?;
            for edge in after.heap.iter().filter(|edge| edge.address == after.stack) {
                let Frame::CallReturn { witness, .. } = edge.frame else {
                    continue;
                };
                let Some(&call) = needed.get(&witness) else {
                    continue;
                };
                if (before.position.code, before.context, before.value_context)
                    != (call.code, call.caller_context, call.caller_value_context)
                    || (target, value_context, expression, creation)
                        != (
                            call.target,
                            call.callee_value_context,
                            call.expression,
                            call.creation,
                        )
                {
                    continue;
                }
                let _ = enter_call(
                    graph,
                    focus,
                    from,
                    to,
                    transition,
                    witness,
                    &HashSet::new(),
                    budget,
                )?;
                charge(budget, 1)?;
                entered.try_reserve(1).map_err(|_| Failure::Resource)?;
                entered.insert(witness);
            }
        }
        if let CompletionTransition::Detail(id) = transition
            && let Some(CompletionDetail::Return(edge)) = details.get(&id)
            && let Frame::CallReturn { witness, .. } = edge.frame
            && let Some(&call) = needed.get(&witness)
        {
            if matched_call_return(focus, from, to, *edge, budget)?.call != call {
                return Err(Failure::Invalid);
            }
            charge(budget, 1)?;
            returned.try_reserve(1).map_err(|_| Failure::Resource)?;
            returned.insert(witness);
        }
    }
    charge(budget, needed.capacity())?;
    if needed
        .keys()
        .any(|id| !entered.contains(id) || !returned.contains(id))
    {
        return Err(Failure::Invalid);
    }
    check_message_root_paths(
        scope, graph, focus, sites, result, &states, &edges, &details, budget,
    )?;
    Ok(result)
}

/// Every reached root must come from the same selected Application arm.
/// The two taint states preserve uncertainty instead of choosing one path;
/// no completion, cleanup or eventual-return claim follows from this check.
#[allow(clippy::too_many_arguments)]
fn check_message_root_paths(
    scope: &super::super::validate::NetworkNativeIdentityScope<'_>,
    graph: &SummaryGraph,
    focus: &CompletionFocus<'_>,
    sites: WorkerRootSites,
    arm: WorkerMessageArm,
    states: &[Option<&super::control::State>],
    edges: &[(usize, usize, CompletionTransition)],
    details: &HashMap<usize, super::control::CompletionDetail>,
    budget: &mut TypeWorkBudget,
) -> Result<(), Failure> {
    use super::control::{Address, CompletionDetail, Control, NetworkEventStage};
    charge(
        budget,
        states
            .len()
            .checked_add(edges.len())
            .ok_or(Failure::Resource)?,
    )?;
    let mut outgoing: Vec<Vec<usize>> = Vec::new();
    outgoing
        .try_reserve_exact(states.len())
        .map_err(|_| Failure::Resource)?;
    outgoing.resize_with(states.len(), Vec::new);
    for (index, &(from, to, _)) in edges.iter().enumerate() {
        if to >= states.len() {
            return Err(Failure::Invalid);
        }
        let list = outgoing.get_mut(from).ok_or(Failure::Invalid)?;
        charge(budget, 1)?;
        list.try_reserve(1).map_err(|_| Failure::Resource)?;
        list.push(index);
    }
    let root_code = scope
        .root()
        .index()
        .map_err(|_| Failure::Invalid)?
        .checked_add(1)
        .ok_or(Failure::Resource)?;
    let mut initial = None;
    for (id, state) in states.iter().enumerate() {
        let state = state.ok_or(Failure::Invalid)?;
        charge(budget, 1)?;
        if state.position.code == root_code
            && state.position.next == 0
            && state.context == 0
            && state.value_context == 0
            && state.stack == Address::Empty
            && state.heap.is_empty()
            && initial.replace(id).is_some()
        {
            return Err(Failure::Invalid);
        }
    }
    // 0: no selected Message, 1: its direct prefix, 2: marker entered,
    // 3: an unsupported/reentrant prefix. State 3 never authorizes a root.
    let mut seen = Vec::new();
    charge(budget, states.len())?;
    seen.try_reserve_exact(states.len())
        .map_err(|_| Failure::Resource)?;
    seen.resize(states.len(), 0u8);
    let mut pending = VecDeque::new();
    pending.try_reserve(1).map_err(|_| Failure::Resource)?;
    pending.push_back((initial.ok_or(Failure::Invalid)?, 0u8));
    let mut roots = 0usize;
    while let Some((id, phase)) = pending.pop_front() {
        charge(budget, 1)?;
        let bit = 1u8.checked_shl(u32::from(phase)).ok_or(Failure::Invalid)?;
        let slot = seen.get_mut(id).ok_or(Failure::Invalid)?;
        if *slot & bit != 0 {
            continue;
        }
        *slot |= bit;
        let state = states.get(id).copied().flatten().ok_or(Failure::Invalid)?;
        let control = graph
            .code
            .get(state.position.code)
            .ok_or(Failure::Invalid)?;
        let mut prefix = phase;
        if phase == 1 {
            match control {
                Control::Call { .. }
                | Control::NetworkEvent { .. }
                | Control::Retain { .. }
                | Control::Continue { .. }
                | Control::Discard { .. }
                | Control::Unavailable => prefix = 3,
                Control::Request(request) if !request.region_service => prefix = 3,
                _ => {}
            }
        } else if phase == 2
            && matches!(control,
            Control::NetworkEvent { operation, stage: NetworkEventStage::Observed, .. } if *operation == sites.receive)
        {
            prefix = 3;
        }
        for &edge_index in outgoing.get(id).ok_or(Failure::Invalid)? {
            charge(budget, 1)?;
            let (_, to, transition) = *edges.get(edge_index).ok_or(Failure::Invalid)?;
            let mut next = prefix;
            if let CompletionTransition::Choice { ordinal } = transition
                && matches!(control, Control::Choice(_))
                && focus.values().original_control_node(
                    state.position.code,
                    scope.nodes(),
                    budget,
                )? == arm.matching.index().map_err(|_| Failure::Invalid)?
                && ordinal == arm.arm
            {
                next = if phase == 0 { 1 } else { 3 };
            }
            if let CompletionTransition::Detail(detail) = transition {
                match details.get(&detail).ok_or(Failure::Invalid)? {
                    CompletionDetail::EnterRoot { code, .. } => {
                        if focus
                            .values()
                            .original_control_node(*code, scope.nodes(), budget)?
                            != sites.root.index().map_err(|_| Failure::Invalid)?
                            || next != 1
                        {
                            return Err(Failure::Invalid);
                        }
                        roots = roots.checked_add(1).ok_or(Failure::Resource)?;
                        next = 2;
                    }
                    CompletionDetail::Return(edge) => {
                        if let Frame::RetainedRoot { code, .. } = edge.frame
                            && focus
                                .values()
                                .original_control_node(code, scope.nodes(), budget)?
                                == sites.root.index().map_err(|_| Failure::Invalid)?
                        {
                            if phase != 2 {
                                return Err(Failure::Invalid);
                            }
                            next = 0;
                        }
                    }
                    CompletionDetail::NativeReturn { boundary: None, .. } if phase == 1 => next = 3,
                    _ => {}
                }
            }
            charge(budget, 1)?;
            pending.try_reserve(1).map_err(|_| Failure::Resource)?;
            pending.push_back((to, next));
        }
    }
    if roots == 0 {
        return Err(Failure::Invalid);
    }
    Ok(())
}

/// Construct a route only after the same final worker trace establishes the
/// canonical receive, Message arm and every root predecessor. This does not
/// authorize marker retirement, finish, or any host assumption.
pub(super) fn worker_processing_route(
    scope: &super::super::validate::NetworkNativeIdentityScope<'_>,
    side: usize,
    graph: &SummaryGraph,
    worker: &super::control::Analysis<'_>,
    budget: &mut TypeWorkBudget,
) -> Result<Option<crate::core::dialect::NetworkProcessingRoute>, Failure> {
    use crate::core::effect::EffectOperation;
    let Some(sites) = worker_root_sites(scope, side, graph, worker, budget)? else {
        return Ok(None);
    };
    let arm = worker_message_arm(scope, graph, worker, sites, budget)?;
    let EffectExprKind::Operation(EffectOperation::Network(owner)) = &scope
        .nodes()
        .get(scope.owner().index().map_err(|_| Failure::Invalid)?)
        .ok_or(Failure::Invalid)?
        .kind
    else {
        return Err(Failure::Invalid);
    };
    let entry = *owner.entries.get(side).ok_or(Failure::Invalid)?;
    if scope.entry(side).is_none() {
        return Err(Failure::Invalid);
    }
    Ok(Some(crate::core::dialect::NetworkProcessingRoute {
        owner: scope.owner(),
        entry,
        side,
        receive: sites.receive,
        message_match: arm.matching,
        arm: arm.arm,
        root: sites.root,
        handler: sites.handler,
        store: sites.store,
    }))
}

/// Inspect all final focused Store exits belonging to this route. This is an
/// intermediate C3 coverage check, not a processing cut: marker correlation,
/// message escape and saved-suffix obligations remain separate.
pub(super) fn worker_store_exit_coverage(
    scope: &super::super::validate::NetworkNativeIdentityScope<'_>,
    route: &crate::core::dialect::NetworkProcessingRoute,
    graph: &SummaryGraph,
    worker: &super::control::Analysis<'_>,
    budget: &mut TypeWorkBudget,
) -> Result<(usize, usize), Failure> {
    use super::control::{CompletionDetail, DrainWork, Frame};
    let EffectExprKind::Operation(crate::core::effect::EffectOperation::Network(network)) = &scope
        .nodes()
        .get(scope.owner().index().map_err(|_| Failure::Invalid)?)
        .ok_or(Failure::Invalid)?
        .kind
    else {
        return Err(Failure::Invalid);
    };
    if route.owner != scope.owner()
        || route.store.arena() != scope.arena()
        || scope.entry(route.side).is_none()
        || network.entries.get(route.side) != Some(&route.entry)
    {
        return Err(Failure::Invalid);
    }
    let EffectExprKind::Operation(crate::core::effect::EffectOperation::Store(store)) = &scope
        .nodes()
        .get(route.store.index().map_err(|_| Failure::Invalid)?)
        .ok_or(Failure::Invalid)?
        .kind
    else {
        return Err(Failure::Invalid);
    };
    if store.body.arena() != scope.arena() {
        return Err(Failure::Invalid);
    }
    let body = store.body.index().map_err(|_| Failure::Invalid)?;
    let fragment = worker_processing_fragment(scope, route, budget).inspect_err(|error| {
        #[cfg(test)]
        eprintln!("pure cut: source fragment rejected: {error:?}");
        let _ = error;
    })?;
    #[cfg(test)]
    if fragment.expected.is_some() {
        eprintln!("pure cut: source fragment {fragment:?}");
    }
    let whole = worker.completion_foci.last().ok_or(Failure::Invalid)?;
    if whole.trace()?.focus().is_ok() {
        return Err(Failure::Invalid);
    }
    let mut tail_targets = HashSet::new();
    whole.trace()?.visit_calls(budget, |_, call, budget| {
        let original = match whole
            .values()
            .original_control_node(call.code, scope.nodes(), budget)
        {
            Ok(original) => original,
            Err(Failure::Invalid) => return Ok(()),
            Err(other) => return Err(other),
        };
        if original != fragment.tail_call.index().map_err(|_| Failure::Invalid)? {
            return Ok(());
        }
        checked_global_worker_call(scope, route, fragment, whole.values(), call, budget)
            .inspect_err(|error| {
                #[cfg(test)]
                eprintln!("pure cut: tail call rejected {call:?}: {error:?}");
                let _ = error;
            })?;
        charge(budget, 1)?;
        tail_targets.try_reserve(1).map_err(|_| Failure::Resource)?;
        tail_targets.insert((call.target, call.expression));
        Ok(())
    })?;
    if tail_targets.is_empty() {
        #[cfg(test)]
        eprintln!("pure cut: no tail targets");
        return Err(Failure::Invalid);
    }
    #[cfg(test)]
    if fragment.expected.is_some() {
        eprintln!("pure cut: tail targets {tail_targets:?}");
    }
    if fragment.expected.is_some() {
        // Every actual invocation of the same loop must respect the carry
        // invariant, including invocations from other receive arms.
        whole.trace()?.visit_calls(budget, |_, call, budget| {
            charge(budget, tail_targets.capacity())?;
            let target_matches = tail_targets.contains(&(call.target, call.expression));
            let source_matches = match whole.values().original_control_node(call.code, scope.nodes(), budget) {
                Ok(original) => {
                    let Some(node) = scope.nodes().get(original) else { return Err(Failure::Invalid); };
                    if let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Apply(application))) = &node.kind {
                        let function = scope.nodes().get(application.function().index().map_err(|_| Failure::Invalid)?).ok_or(Failure::Invalid)?;
                        let candidate = match &function.kind {
                            EffectExprKind::Pure(PureExprKind::Computation(PureComputation::TypeApplication(application))) =>
                                scope.nodes().get(application.function().index().map_err(|_| Failure::Invalid)?).ok_or(Failure::Invalid)?,
                            _ => function,
                        };
                        matches!(&candidate.kind, EffectExprKind::Pure(PureExprKind::Variable(variable)) if variable.binder() == fragment.tail_binder)
                    } else { false }
                }
                Err(Failure::Invalid) => false,
                Err(error) => return Err(error),
            };
            if target_matches || source_matches {
                checked_global_worker_call(scope, route, fragment, whole.values(), call, budget).inspect_err(|error| {
                    #[cfg(test)] eprintln!("pure cut: loop call rejected {call:?}: {error:?}");
                    let _ = error;
                })?;
            }
            Ok(())
        })?;
    }
    charge(budget, worker.completion_foci.len())?;
    let mut focuses = 0usize;
    let mut exits = 0usize;
    let mut returned_exits = 0usize;
    for focus in &worker.completion_foci {
        let trace = focus.trace()?;
        let Ok((code, context, value_context)) = trace.focus() else {
            continue;
        };
        if focus
            .values()
            .original_control_node(code, scope.nodes(), budget)?
            != body
        {
            continue;
        }
        focuses = focuses.checked_add(1).ok_or(Failure::Resource)?;
        let mut helper = None;
        trace.visit_calls(budget, |witness, call, budget| {
            let original =
                match focus
                    .values()
                    .original_control_node(call.code, scope.nodes(), budget)
                {
                    Ok(original) => original,
                    Err(Failure::Invalid) => return Ok(()),
                    Err(other) => return Err(other),
                };
            if original != fragment.helper_call.index().map_err(|_| Failure::Invalid)? {
                return Ok(());
            }
            let kind = if fragment.expected.is_some() {
                let (recursive, equal, equal_target) =
                    checked_pure_unit_helper(scope, call, budget).inspect_err(|error| {
                        #[cfg(test)]
                        eprintln!("pure cut: helper rejected {call:?}: {error:?}");
                        let _ = error;
                    })?;
                ProcessingHelper::Pure {
                    recursive,
                    equal,
                    equal_target,
                }
            } else {
                ProcessingHelper::Native(checked_native_unit_helper(scope, call, budget)?)
            };
            let (_, _, arguments, captures) = focus.values().existing_call_ports(
                call.code,
                call.caller_value_context,
                call.expression,
                call.callee_value_context,
                call.creation,
                budget,
            )?;
            if let ProcessingHelper::Pure { .. } = kind {
                let EffectExprKind::Operation(crate::core::effect::EffectOperation::RegionClosure(
                    closure,
                )) = &scope
                    .nodes()
                    .get(call.expression)
                    .ok_or(Failure::Invalid)?
                    .kind
                else {
                    return Err(Failure::Invalid);
                };
                focus.values().check_closed_global_capture_ports(
                    call.expression,
                    call.creation,
                    call.callee_value_context,
                    &closure.captures,
                    closure.context,
                    &[],
                    scope.arena(),
                    scope.nodes(),
                    &captures,
                    budget,
                )?;
            }
            if arguments.len() != 1 || helper.is_some_and(|prior| prior != (witness, call, kind)) {
                return Err(Failure::Invalid);
            }
            helper = Some((witness, call, kind));
            Ok(())
        })?;
        let (helper_witness, helper_call, helper_kind) = helper.ok_or(Failure::Invalid)?;
        #[cfg(test)]
        if fragment.expected.is_some() {
            eprintln!(
                "pure cut: helper focus={focuses} witness={helper_witness} call={helper_call:?} kind={helper_kind:?}"
            );
        }
        let states = trace.indexed_states(budget)?;
        let seed = states.first().copied().flatten().ok_or(Failure::Invalid)?;
        if (seed.position.code, seed.context, seed.value_context) != (code, context, value_context)
        {
            return Err(Failure::Invalid);
        }
        check_focused_store_address(
            focus,
            scope,
            route,
            seed,
            seed.stack,
            context,
            value_context,
            budget,
        )?;
        let mut exit_states = HashSet::new();
        trace.visit_exits(budget, |from, edge, budget| {
            let state = states.get(from).copied().flatten().ok_or(Failure::Invalid)?;
            if state.stack != edge.address
                || !matches!(edge.frame, Frame::Resource {
                    code: actual, context: actual_context, value_context: actual_value_context, focused: true,
                } if actual_context == context && actual_value_context == value_context
                    && focus.values().original_control_node(actual, scope.nodes(), budget)?
                        == route.store.index().map_err(|_| Failure::Invalid)?)
                || !matches!(state.drain.as_ref().map(|drain| drain.work), Some(DrainWork::Empty))
            { return Err(Failure::Invalid); }
            check_worker_tail_suffix(focus, scope, route, fragment, &tail_targets, state, edge.next, budget).inspect_err(|error| {
                #[cfg(test)] eprintln!("pure cut: suffix focus={focuses} from={from}: {error:?}");
                let _ = error;
            })?;
            charge(budget, 1)?;
            exit_states.try_reserve(1).map_err(|_| Failure::Resource)?;
            exit_states.insert(from);
            exits = exits.checked_add(1).ok_or(Failure::Resource)?;
            Ok(())
        })?;
        let edges = trace.indexed_edges(budget)?;
        #[cfg(test)]
        if fragment.expected.is_some() {
            eprintln!("pure cut: exits focus={focuses}, exits={exits}");
        }
        let mut details = HashMap::new();
        trace.visit_details(budget, |id, detail, budget| {
            charge(budget, 1)?;
            details.try_reserve(1).map_err(|_| Failure::Resource)?;
            if details.insert(id, detail).is_some() {
                return Err(Failure::Invalid);
            }
            Ok(())
        })?;
        charge(
            budget,
            states
                .len()
                .checked_add(edges.len())
                .ok_or(Failure::Resource)?,
        )?;
        let mut outgoing = Vec::new();
        outgoing
            .try_reserve_exact(states.len())
            .map_err(|_| Failure::Resource)?;
        outgoing.resize_with(states.len(), Vec::new);
        for (index, &(from, to, _)) in edges.iter().enumerate() {
            if to >= states.len() {
                return Err(Failure::Invalid);
            }
            let bucket = outgoing.get_mut(from).ok_or(Failure::Invalid)?;
            charge(budget, 1)?;
            bucket.try_reserve(1).map_err(|_| Failure::Resource)?;
            bucket.push(index);
        }
        // 0: before the marker; 1: root entered; 2: helper entered;
        // 3: native returned; 4: helper returned; 5: root returned.
        // Bypass exits cannot satisfy the runtime MarkerReturned premise.
        let mut seen = Vec::new();
        charge(budget, states.len())?;
        seen.try_reserve_exact(states.len())
            .map_err(|_| Failure::Resource)?;
        seen.resize(states.len(), 0u8);
        let mut pending = VecDeque::new();
        pending.try_reserve(1).map_err(|_| Failure::Resource)?;
        pending.push_back((0usize, 0u8));
        while let Some((id, phase)) = pending.pop_front() {
            charge(budget, 1)?;
            let bit = 1u8.checked_shl(u32::from(phase)).ok_or(Failure::Invalid)?;
            let slot = seen.get_mut(id).ok_or(Failure::Invalid)?;
            if *slot & bit != 0 {
                continue;
            }
            *slot |= bit;
            if exit_states.contains(&id) {
                if (1..5).contains(&phase) {
                    return Err(Failure::Invalid);
                }
                if phase == 5 {
                    returned_exits = returned_exits.checked_add(1).ok_or(Failure::Resource)?;
                }
            }
            let state = states.get(id).copied().flatten().ok_or(Failure::Invalid)?;
            for &index in outgoing.get(id).ok_or(Failure::Invalid)? {
                charge(budget, 1)?;
                let (_, to, transition) = *edges.get(index).ok_or(Failure::Invalid)?;
                let mut next = phase;
                if let CompletionTransition::Call { .. } = transition
                    && (1..5).contains(&phase)
                {
                    let after = states.get(to).copied().flatten().ok_or(Failure::Invalid)?;
                    charge(budget, after.heap.len())?;
                    let mut matching = after.heap.iter().filter(|edge| edge.address == after.stack);
                    let edge = matching.next().ok_or(Failure::Invalid)?;
                    let Frame::CallReturn { witness, .. } = edge.frame else {
                        return Err(Failure::Invalid);
                    };
                    if matching.next().is_some() {
                        return Err(Failure::Invalid);
                    }
                    let (entered, _) = enter_call(
                        graph,
                        focus,
                        id,
                        to,
                        transition,
                        witness,
                        &HashSet::new(),
                        budget,
                    )?;
                    if phase == 1
                        && state.position.code == helper_call.code
                        && witness == helper_witness
                    {
                        if entered.call != helper_call {
                            return Err(Failure::Invalid);
                        }
                        next = 2;
                    } else if let ProcessingHelper::Pure {
                        recursive,
                        equal,
                        equal_target,
                    } = helper_kind
                    {
                        if phase != 2 {
                            return Err(Failure::Invalid);
                        }
                        let original = focus.values().original_control_node(
                            entered.call.code,
                            scope.nodes(),
                            budget,
                        )?;
                        let (expected_node, expected_target) =
                            if original == recursive.index().map_err(|_| Failure::Invalid)? {
                                (recursive, helper_call.target)
                            } else {
                                (equal, equal_target)
                            };
                        if original != expected_node.index().map_err(|_| Failure::Invalid)?
                            || entered.call.target != expected_target
                            || entered.call.expression != expected_target
                        {
                            return Err(Failure::Invalid);
                        }
                        if original == recursive.index().map_err(|_| Failure::Invalid)? {
                            let EffectExprKind::Operation(
                                crate::core::effect::EffectOperation::RegionClosure(closure),
                            ) = &scope
                                .nodes()
                                .get(entered.call.expression)
                                .ok_or(Failure::Invalid)?
                                .kind
                            else {
                                return Err(Failure::Invalid);
                            };
                            let (_, _, arguments, captures) = focus.values().existing_call_ports(
                                entered.call.code,
                                entered.call.caller_value_context,
                                entered.call.expression,
                                entered.call.callee_value_context,
                                entered.call.creation,
                                budget,
                            )?;
                            if arguments.len() != 1 {
                                return Err(Failure::Invalid);
                            }
                            focus.values().check_closed_global_capture_ports(
                                entered.call.expression,
                                entered.call.creation,
                                entered.call.callee_value_context,
                                &closure.captures,
                                closure.context,
                                &[],
                                scope.arena(),
                                scope.nodes(),
                                &captures,
                                budget,
                            )?;
                        }
                    } else {
                        return Err(Failure::Invalid);
                    }
                }
                if let CompletionTransition::Detail(detail_id) = transition {
                    match details.get(&detail_id).ok_or(Failure::Invalid)? {
                        CompletionDetail::EnterRoot {
                            store, code: root, ..
                        } => {
                            if focus
                                .values()
                                .original_control_node(*root, scope.nodes(), budget)?
                                != route.root.index().map_err(|_| Failure::Invalid)?
                                || phase != 0
                            {
                                return Err(Failure::Invalid);
                            }
                            check_focused_store_address(
                                focus,
                                scope,
                                route,
                                state,
                                *store,
                                context,
                                value_context,
                                budget,
                            )?;
                            next = 1;
                        }
                        CompletionDetail::Return(edge) => {
                            if let Frame::RetainedRoot {
                                code: root, store, ..
                            } = edge.frame
                            {
                                if focus.values().original_control_node(
                                    root,
                                    scope.nodes(),
                                    budget,
                                )? != route.root.index().map_err(|_| Failure::Invalid)?
                                    || phase != 4
                                    || state.stack != edge.address
                                {
                                    return Err(Failure::Invalid);
                                }
                                check_focused_store_address(
                                    focus,
                                    scope,
                                    route,
                                    state,
                                    store,
                                    context,
                                    value_context,
                                    budget,
                                )?;
                                next = 5;
                            } else if matches!(edge.frame, Frame::CallReturn { witness, .. } if witness == helper_witness)
                            {
                                let expected_phase =
                                    if matches!(helper_kind, ProcessingHelper::Native(_)) {
                                        3
                                    } else {
                                        2
                                    };
                                if phase != expected_phase
                                    || matched_call_return(focus, id, to, *edge, budget)?.call
                                        != helper_call
                                {
                                    return Err(Failure::Invalid);
                                }
                                next = 4;
                            } else if let (
                                2,
                                ProcessingHelper::Pure {
                                    recursive,
                                    equal,
                                    equal_target,
                                },
                                Frame::CallReturn { .. },
                            ) = (phase, helper_kind, edge.frame)
                            {
                                let returned = matched_call_return(focus, id, to, *edge, budget)?;
                                let original = focus.values().original_control_node(
                                    returned.call.code,
                                    scope.nodes(),
                                    budget,
                                )?;
                                let expected_target = if original
                                    == recursive.index().map_err(|_| Failure::Invalid)?
                                {
                                    helper_call.target
                                } else if original == equal.index().map_err(|_| Failure::Invalid)? {
                                    equal_target
                                } else {
                                    return Err(Failure::Invalid);
                                };
                                if returned.call.target != expected_target
                                    || returned.call.expression != expected_target
                                {
                                    return Err(Failure::Invalid);
                                }
                            }
                        }
                        CompletionDetail::NativeReturn {
                            event,
                            boundary,
                            edge,
                        } if (1..5).contains(&phase) => {
                            if matches!(helper_kind, ProcessingHelper::Pure { .. })
                                && boundary.is_none()
                            {
                                let returned = edge.ok_or(Failure::Invalid)?;
                                let after =
                                    states.get(to).copied().flatten().ok_or(Failure::Invalid)?;
                                let work = state
                                    .drain
                                    .as_ref()
                                    .map(|drain| drain.work)
                                    .ok_or(Failure::Invalid)?;
                                if event.unknown
                                    || state.position.code != event.code
                                    || matches!(work, DrainWork::Unknown)
                                    || after.drain.as_ref().map(|drain| drain.work) != Some(work)
                                    || state.stack != returned.address
                                    || after.stack != returned.next
                                    || !state.heap.contains(&returned)
                                    || !matches!(returned.frame, Frame::Next { .. })
                                {
                                    return Err(Failure::Invalid);
                                }
                                let original = focus.values().original_control_node(
                                    event.code,
                                    scope.nodes(),
                                    budget,
                                )?;
                                if !matches!(
                                    &scope.nodes().get(original).ok_or(Failure::Invalid)?.kind,
                                    EffectExprKind::Operation(
                                        crate::core::effect::EffectOperation::RegionAllocate(_)
                                    )
                                ) {
                                    return Err(Failure::Invalid);
                                }
                                charge(budget, 1)?;
                                pending.try_reserve(1).map_err(|_| Failure::Resource)?;
                                pending.push_back((to, next));
                                continue;
                            }
                            let (Some(boundary), Some(returned)) = (boundary, edge) else {
                                return Err(Failure::Invalid);
                            };
                            let Frame::NativeInterpret { code: native, .. } = boundary.frame else {
                                return Err(Failure::Invalid);
                            };
                            let ProcessingHelper::Native(native_request) = helper_kind else {
                                return Err(Failure::Invalid);
                            };
                            if phase != 2
                                || event.unknown
                                || state.position.code != event.code
                                || focus.values().original_control_node(
                                    event.code,
                                    scope.nodes(),
                                    budget,
                                )? != native_request.index().map_err(|_| Failure::Invalid)?
                                || focus.values().original_control_node(
                                    native,
                                    scope.nodes(),
                                    budget,
                                )? != scope.root().index().map_err(|_| Failure::Invalid)?
                                || !state.heap.contains(boundary)
                                || !state.heap.contains(returned)
                            {
                                return Err(Failure::Invalid);
                            }
                            next = 3;
                        }
                        _ => {}
                    }
                }
                charge(budget, 1)?;
                pending.try_reserve(1).map_err(|_| Failure::Resource)?;
                pending.push_back((to, next));
            }
        }
    }
    if focuses == 0 || exits == 0 || returned_exits == 0 {
        return Err(Failure::Invalid);
    }
    Ok((focuses, exits))
}

#[allow(clippy::too_many_arguments)]
fn check_worker_tail_suffix(
    focus: &CompletionFocus<'_>,
    scope: &super::super::validate::NetworkNativeIdentityScope<'_>,
    route: &crate::core::dialect::NetworkProcessingRoute,
    fragment: WorkerProcessingFragment,
    tail_targets: &HashSet<(usize, usize)>,
    state: &super::control::State,
    address: super::control::Address,
    budget: &mut TypeWorkBudget,
) -> Result<(), Failure> {
    let unique = |address, budget: &mut TypeWorkBudget| -> Result<Edge, Failure> {
        charge(budget, state.heap.len())?;
        let mut edges = state.heap.iter().filter(|edge| edge.address == address);
        let edge = *edges.next().ok_or(Failure::Invalid)?;
        if edges.next().is_some() {
            return Err(Failure::Invalid);
        }
        Ok(edge)
    };
    let next = unique(address, budget)?;
    let Frame::Next { position, .. } = next.frame else {
        return Err(Failure::Invalid);
    };
    if position.next != 1
        || focus
            .values()
            .original_control_node(position.code, scope.nodes(), budget)?
            != fragment.tail_match.index().map_err(|_| Failure::Invalid)?
    {
        return Err(Failure::Invalid);
    }
    let case = unique(next.next, budget)?;
    let Frame::CaseReturn { code, ordinal, .. } = case.frame else {
        return Err(Failure::Invalid);
    };
    if ordinal != route.arm
        || focus
            .values()
            .original_control_node(code, scope.nodes(), budget)?
            != route.message_match.index().map_err(|_| Failure::Invalid)?
    {
        return Err(Failure::Invalid);
    }
    let next_caller = unique(case.next, budget)?;
    let (caller, tuple_case) = if fragment.expected.is_some() {
        let Frame::CaseReturn { code, ordinal, .. } = next_caller.frame else {
            return Err(Failure::Invalid);
        };
        if ordinal != 0 {
            return Err(Failure::Invalid);
        }
        (unique(next_caller.next, budget)?, Some(code))
    } else {
        (next_caller, None)
    };
    let Frame::CallReturn {
        code,
        result,
        body,
        context,
        value_context,
        witness,
    } = caller.frame
    else {
        return Err(Failure::Invalid);
    };
    let call = focus.trace()?.call(witness, budget)?;
    if let Some(tuple_case) = tuple_case {
        let EffectExprKind::Operation(crate::core::effect::EffectOperation::RegionClosure(closure)) =
            &scope
                .nodes()
                .get(call.expression)
                .ok_or(Failure::Invalid)?
                .kind
        else {
            return Err(Failure::Invalid);
        };
        let body = closure.code.function().ok_or(Failure::Invalid)?.body();
        if focus
            .values()
            .original_control_node(tuple_case, scope.nodes(), budget)?
            != body.index().map_err(|_| Failure::Invalid)?
        {
            return Err(Failure::Invalid);
        }
    }
    if (code, result, body, context, value_context)
        != (
            call.code,
            call.result,
            call.body,
            call.caller_context,
            call.caller_value_context,
        )
    {
        return Err(Failure::Invalid);
    }
    let (actual_result, actual_body, _, _) = focus.values().existing_call_ports(
        call.code,
        call.caller_value_context,
        call.expression,
        call.callee_value_context,
        call.creation,
        budget,
    )?;
    if (actual_result, actual_body) != (result, body) {
        return Err(Failure::Invalid);
    }
    checked_global_worker_call(scope, route, fragment, focus.values(), call, budget)?;
    charge(budget, tail_targets.capacity())?;
    if tail_targets
        .iter()
        .any(|target| *target != (call.target, call.expression))
    {
        return Err(Failure::Invalid);
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn check_focused_store_address(
    focus: &CompletionFocus<'_>,
    scope: &super::super::validate::NetworkNativeIdentityScope<'_>,
    route: &crate::core::dialect::NetworkProcessingRoute,
    state: &super::control::State,
    address: super::control::Address,
    context: usize,
    value_context: usize,
    budget: &mut TypeWorkBudget,
) -> Result<(), Failure> {
    charge(budget, state.heap.len())?;
    let mut matched = false;
    for edge in state.heap.iter().filter(|edge| edge.address == address) {
        let Frame::Resource {
            code,
            context: actual_context,
            value_context: actual_value_context,
            focused: true,
        } = edge.frame
        else {
            return Err(Failure::Invalid);
        };
        if actual_context != context
            || actual_value_context != value_context
            || focus
                .values()
                .original_control_node(code, scope.nodes(), budget)?
                != route.store.index().map_err(|_| Failure::Invalid)?
            || matched
        {
            return Err(Failure::Invalid);
        }
        matched = true;
    }
    if matched {
        Ok(())
    } else {
        Err(Failure::Invalid)
    }
}
