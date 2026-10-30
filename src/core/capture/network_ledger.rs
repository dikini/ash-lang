//! Same-focus ledger currentness analysis (under development).
//!
//! This module must not publish a ledger fact until every selected Region
//! request and its normal resumption have been authenticated, and unknown
//! effects, captures and re-entry have been excluded. The trace and its value
//! ports are meaningful only within the owning worker query.

#[path = "transition_observation.rs"]
mod transition_observation;

use super::{Failure, SummaryGraph, charge, control, network_completion};
use crate::core::ledger_checker::{
    ConditionalInitializationCall, ConditionalRegistrationCall, RegistrationResultMatch,
};
use crate::core::validate::NetworkNativeIdentityScope;
use crate::types::TypeWorkBudget;
use std::collections::{HashMap, HashSet, VecDeque};

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum ReceiveStage {
    Before,
    Observed(control::NetworkOutcome),
    Committed,
    Replied,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum Phase {
    BeforeInitialization,
    Invalidated,
    Initializing(usize),
    Initialized {
        port: usize,
        context: usize,
    },
    Transitioning {
        site: usize,
        witness: usize,
        input: usize,
        context: usize,
        ordinal: usize,
    },
    TransitionReturned {
        site: usize,
        port: usize,
        context: usize,
        ordinal: usize,
    },
    Receiving {
        receive: usize,
        witness: usize,
        port: usize,
        context: usize,
        ordinal: usize,
        role: crate::resolved::BinderId,
        stage: ReceiveStage,
    },
    EnteringDriver {
        driver: usize,
        witness: usize,
        formal_port: usize,
        context: usize,
        ordinal: usize,
    },
    Registering {
        witness: usize,
        input: usize,
        ordinal: usize,
    },
    Returned {
        port: usize,
        context: usize,
        input: usize,
        ordinal: usize,
    },
    Projected {
        ledger: usize,
        status: usize,
        input: usize,
        context: usize,
        ordinal: usize,
    },
    Current {
        port: usize,
        context: usize,
        ordinal: usize,
        role: crate::resolved::BinderId,
    },
    PreparingArgument {
        port: usize,
        context: usize,
        ordinal: usize,
        role: crate::resolved::BinderId,
        constructor: usize,
    },
    RunningArgument {
        port: usize,
        context: usize,
        ordinal: usize,
        role: crate::resolved::BinderId,
        constructor: usize,
        witness: usize,
    },
}

#[derive(Clone, Copy)]
struct DefinitionProvenance {
    query: crate::core::NodeId,
    binding: crate::core::NodeId,
    context: crate::core::NodeId,
    closure: crate::core::NodeId,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
struct LocalOrigin {
    binding: usize,
    binder: crate::resolved::BinderId,
    context: usize,
    port: usize,
}

fn record_query_path(
    paths: &mut HashMap<usize, usize>,
    state: usize,
    caller: usize,
    work: &mut TypeWorkBudget,
) -> Result<(), Failure> {
    charge(work, 1)?;
    paths.try_reserve(1).map_err(|_| Failure::Resource)?;
    if paths.insert(state, caller).is_some_and(|old| old != caller) {
        return Err(Failure::Invalid);
    }
    Ok(())
}

/// Collect actual lexical query binders once, without inferring a provider
/// from an effect name. Each reached query is authenticated on the trace.
fn query_bindings(
    scope: &NetworkNativeIdentityScope<'_>,
    checked_nodes: &HashSet<usize>,
    module: crate::module::ModuleId,
    work: &mut TypeWorkBudget,
) -> Result<HashMap<usize, (usize, crate::resolved::BinderId)>, Failure> {
    use crate::core::{EffectExprKind, EffectOperation, PureComputation, PureExprKind};
    let api = crate::resolved::RegionApi::for_module(module).ok_or(Failure::Invalid)?;
    let mut result = HashMap::new();
    charge(work, checked_nodes.capacity())?;
    for &index in checked_nodes {
        let node = scope.nodes().get(index).ok_or(Failure::Invalid)?;
        let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Bind(binding))) =
            &node.kind
        else {
            continue;
        };
        if binding.initializer().arena() != scope.arena() {
            return Err(Failure::Invalid);
        }
        let query = binding
            .initializer()
            .index()
            .map_err(|_| Failure::Invalid)?;
        let Some(EffectExprKind::Operation(EffectOperation::Request(request))) =
            scope.nodes().get(query).map(|node| &node.kind)
        else {
            continue;
        };
        if request.effect().effect() != api.default_alloc()
            || request.operation() != crate::types::OperationId::new(api.default_alloc(), 1)
        {
            continue;
        }
        charge(work, 1)?;
        result.try_reserve(1).map_err(|_| Failure::Resource)?;
        if result
            .insert(query, (index, binding.binder().id()))
            .is_some()
        {
            return Err(Failure::Invalid);
        }
    }
    charge(work, result.capacity())?;
    Ok(result)
}

/// Reuse only the canonical stored closures already inside checked bodies.
/// Each coordinate is still tied to an actually resumed query and call below.
fn closure_bindings(
    scope: &NetworkNativeIdentityScope<'_>,
    bindings: &HashMap<usize, (usize, crate::resolved::BinderId)>,
    module: crate::module::ModuleId,
    work: &mut TypeWorkBudget,
) -> Result<HashMap<usize, DefinitionProvenance>, Failure> {
    use crate::core::{EffectExprKind, PureExprKind};
    let mut result = HashMap::new();
    charge(work, bindings.capacity())?;
    for (&query, &(binding, binder)) in bindings {
        let node = crate::core::NodeId::new(
            scope.arena(),
            u32::try_from(binding).map_err(|_| Failure::Resource)?,
        );
        let Some((closure_id, closure)) = crate::core::region::closure_initializer::<
            crate::core::EffectOperationFamily,
        >(node, |id| {
            if id.arena() != scope.arena() {
                None
            } else {
                scope.nodes().get(id.index().ok()?).map(|node| &node.kind)
            }
        }) else {
            continue;
        };
        if closure.api != module
            || closure.code.function().is_none()
            || closure.context.arena() != scope.arena()
        {
            return Err(Failure::Invalid);
        }
        let EffectExprKind::Pure(PureExprKind::Variable(context)) = &scope
            .nodes()
            .get(closure.context.index().map_err(|_| Failure::Invalid)?)
            .ok_or(Failure::Invalid)?
            .kind
        else {
            return Err(Failure::Invalid);
        };
        if context.binder() != binder {
            return Err(Failure::Invalid);
        }
        let coordinate = DefinitionProvenance {
            query: crate::core::NodeId::new(
                scope.arena(),
                u32::try_from(query).map_err(|_| Failure::Resource)?,
            ),
            binding: node,
            context: closure.context,
            closure: closure_id,
        };
        charge(work, 1)?;
        result.try_reserve(1).map_err(|_| Failure::Resource)?;
        if result
            .insert(
                closure_id.index().map_err(|_| Failure::Invalid)?,
                coordinate,
            )
            .is_some()
        {
            return Err(Failure::Invalid);
        }
    }
    charge(work, result.capacity())?;
    Ok(result)
}

/// The exact already-reconstructed bodies bound the set of callable code and
/// call sites that can participate in this conditional registration run.
fn checked_call_sites(
    scope: &NetworkNativeIdentityScope<'_>,
    initialization: &ConditionalInitializationCall<'_>,
    registration: &ConditionalRegistrationCall<'_>,
    extra_roots: &[crate::core::NodeId],
    work: &mut TypeWorkBudget,
) -> Result<(HashSet<usize>, HashSet<usize>, HashSet<usize>), Failure> {
    use crate::core::{EffectExprKind, EffectOperation, PureComputation, PureExprKind, PureValue};
    let mut pending = Vec::new();
    let mut visited = HashSet::new();
    let mut calls = HashSet::new();
    let mut closures = HashSet::new();
    let roots = registration.definition_roots();
    let count = roots
        .len()
        .checked_add(extra_roots.len())
        .and_then(|n| n.checked_add(1))
        .ok_or(Failure::Resource)?;
    charge(work, count)?;
    pending.try_reserve(count).map_err(|_| Failure::Resource)?;
    pending.extend(roots);
    pending.extend_from_slice(extra_roots);
    pending.push(initialization.definition_binding());
    while let Some(id) = pending.pop() {
        charge(work, 1)?;
        if id.arena() != scope.arena() {
            return Err(Failure::Invalid);
        }
        let index = id.index().map_err(|_| Failure::Invalid)?;
        visited.try_reserve(1).map_err(|_| Failure::Resource)?;
        if !visited.insert(index) {
            continue;
        }
        let kind = &scope.nodes().get(index).ok_or(Failure::Invalid)?.kind;
        if matches!(
            kind,
            EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Apply(_)))
        ) {
            calls.try_reserve(1).map_err(|_| Failure::Resource)?;
            calls.insert(index);
        }
        if matches!(kind, EffectExprKind::Operation(EffectOperation::RegionClosure(closure)) if closure.code.function().is_some())
            || matches!(
                kind,
                EffectExprKind::Pure(PureExprKind::Value(PureValue::Function(_)))
            )
        {
            closures.try_reserve(1).map_err(|_| Failure::Resource)?;
            closures.insert(index);
        }
        let count = kind.child_count();
        charge(work, count)?;
        pending.try_reserve(count).map_err(|_| Failure::Resource)?;
        for ordinal in 0..count {
            pending.push(kind.child_at(ordinal).ok_or(Failure::Invalid)?);
        }
    }
    charge(
        work,
        visited
            .capacity()
            .checked_add(calls.capacity())
            .and_then(|n| n.checked_add(closures.capacity()))
            .ok_or(Failure::Resource)?,
    )?;
    Ok((calls, closures, visited))
}

/// Include the actual nominated call's argument tree only for query/operand
/// inspection; it never expands the trusted helper-call set.
fn include_argument_nodes(
    scope: &NetworkNativeIdentityScope<'_>,
    root: crate::core::NodeId,
    nodes: &mut HashSet<usize>,
    work: &mut TypeWorkBudget,
) -> Result<(), Failure> {
    let mut pending = Vec::new();
    charge(work, 1)?;
    pending.try_reserve(1).map_err(|_| Failure::Resource)?;
    pending.push(root);
    while let Some(node) = pending.pop() {
        charge(work, 1)?;
        if node.arena() != scope.arena() {
            return Err(Failure::Invalid);
        }
        let index = node.index().map_err(|_| Failure::Invalid)?;
        nodes.try_reserve(1).map_err(|_| Failure::Resource)?;
        if !nodes.insert(index) {
            continue;
        }
        let kind = &scope.nodes().get(index).ok_or(Failure::Invalid)?.kind;
        let count = kind.child_count();
        charge(work, count)?;
        pending.try_reserve(count).map_err(|_| Failure::Resource)?;
        for ordinal in 0..count {
            pending.push(kind.child_at(ordinal).ok_or(Failure::Invalid)?);
        }
    }
    charge(work, pending.capacity())?;
    Ok(())
}

fn authenticate_body_call(
    scope: &NetworkNativeIdentityScope<'_>,
    graph: &SummaryGraph,
    focus: &control::CompletionFocus<'_>,
    from: usize,
    to: usize,
    transition: control::CompletionTransition,
    calls: &HashSet<usize>,
    closures: &HashSet<usize>,
    helpers: &[(crate::resolved::BinderId, crate::core::NodeId)],
    closure_origins: &HashMap<usize, DefinitionProvenance>,
    query_origins: &HashMap<usize, LocalOrigin>,
    work: &mut TypeWorkBudget,
) -> Result<(), Failure> {
    use crate::core::{EffectExprKind, EffectOperation, PureComputation, PureExprKind};
    let control::CompletionTransition::Call { target, .. } = transition else {
        return Err(Failure::Invalid);
    };
    if !closures.contains(&target) {
        return Err(Failure::Invalid);
    }
    let witness = entered_call(
        graph,
        focus,
        from,
        to,
        transition,
        crate::core::NodeId::new(
            scope.arena(),
            u32::try_from(target).map_err(|_| Failure::Resource)?,
        ),
        work,
    )?;
    let call = focus.trace()?.call(witness, work)?;
    checked_context_capture(
        scope,
        focus,
        *closure_origins.get(&target).ok_or(Failure::Invalid)?,
        call,
        query_origins,
        work,
    )?;
    let original = focus
        .values()
        .original_control_node(call.code, scope.nodes(), work)?;
    if !calls.contains(&original) {
        return Err(Failure::Invalid);
    }
    let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Apply(application))) =
        &scope.nodes().get(original).ok_or(Failure::Invalid)?.kind
    else {
        return Err(Failure::Invalid);
    };
    if application.function().arena() != scope.arena() {
        return Err(Failure::Invalid);
    }
    match &scope
        .nodes()
        .get(
            application
                .function()
                .index()
                .map_err(|_| Failure::Invalid)?,
        )
        .ok_or(Failure::Invalid)?
        .kind
    {
        EffectExprKind::Pure(PureExprKind::Variable(variable)) => {
            charge(work, helpers.len())?;
            let mut expected = helpers
                .iter()
                .filter(|(binder, _)| *binder == variable.binder());
            let (_, closure) = expected.next().ok_or(Failure::Invalid)?;
            if expected.next().is_some() || closure.index().map_err(|_| Failure::Invalid)? != target
            {
                return Err(Failure::Invalid);
            }
        }
        _ => {
            let (closure, _) = crate::core::region::closure_initializer::<
                crate::core::EffectOperationFamily,
            >(application.function(), |id| {
                if id.arena() != scope.arena() {
                    None
                } else {
                    scope.nodes().get(id.index().ok()?).map(|node| &node.kind)
                }
            })
            .ok_or(Failure::Invalid)?;
            if closure.index().map_err(|_| Failure::Invalid)? != target {
                return Err(Failure::Invalid);
            }
        }
    }
    let EffectExprKind::Operation(EffectOperation::RegionClosure(closure)) =
        &scope.nodes().get(target).ok_or(Failure::Invalid)?.kind
    else {
        return Err(Failure::Invalid);
    };
    let (_, _, _, pairs) = focus.values().existing_call_ports(
        call.code,
        call.caller_value_context,
        call.expression,
        call.callee_value_context,
        call.creation,
        work,
    )?;
    focus.values().check_closed_global_capture_ports(
        target,
        call.creation,
        call.callee_value_context,
        &closure.captures,
        closure.context,
        &[],
        scope.arena(),
        scope.nodes(),
        &pairs,
        work,
    )?;
    let source_ports = focus.values().existing_original_capture_ports(
        target,
        call.creation,
        &closure.captures,
        scope.arena(),
        scope.nodes(),
        work,
    )?;
    for (node, port) in closure.captures.iter().zip(source_ports) {
        if node.arena() != scope.arena() {
            return Err(Failure::Invalid);
        }
        let EffectExprKind::Pure(PureExprKind::Variable(variable)) = &scope
            .nodes()
            .get(node.index().map_err(|_| Failure::Invalid)?)
            .ok_or(Failure::Invalid)?
            .kind
        else {
            return Err(Failure::Invalid);
        };
        charge(work, helpers.len())?;
        let mut matches = helpers
            .iter()
            .filter(|(binder, _)| *binder == variable.binder());
        if let Some((_, expected)) = matches.next() {
            if matches.next().is_some() {
                return Err(Failure::Invalid);
            }
            let actual = focus.values().existing_closures_at_port(port, work)?;
            if !matches!(actual.as_slice(), [(target, _)] if *target == expected.index().map_err(|_| Failure::Invalid)?)
            {
                return Err(Failure::Invalid);
            }
        }
    }
    Ok(())
}

fn checked_context_capture(
    scope: &NetworkNativeIdentityScope<'_>,
    focus: &control::CompletionFocus<'_>,
    definition: DefinitionProvenance,
    call: control::CompletionCall,
    origins: &HashMap<usize, LocalOrigin>,
    work: &mut TypeWorkBudget,
) -> Result<(), Failure> {
    let binding_index = definition.binding.index().map_err(|_| Failure::Invalid)?;
    let binding = binding_index.checked_add(1).ok_or(Failure::Resource)?;
    let original_creation =
        match focus
            .values()
            .existing_binding_ports(binding, call.creation, work)
        {
            Ok(_) => call.creation,
            Err(Failure::Invalid) => focus.values().existing_type_application_creation(
                call,
                definition.context,
                scope.arena(),
                scope.nodes(),
                work,
            )?,
            Err(error) => return Err(error),
        };
    let (binder_port, query_port) =
        focus
            .values()
            .existing_binding_ports(binding, original_creation, work)?;
    let origin = origins.get(&query_port).ok_or(Failure::Invalid)?;
    if origin.binding != binding_index || origin.context != original_creation {
        return Err(Failure::Invalid);
    }
    let context = definition
        .context
        .index()
        .map_err(|_| Failure::Invalid)?
        .checked_add(1)
        .ok_or(Failure::Resource)?;
    let (context_port, context_source) =
        focus
            .values()
            .existing_forward_ports(context, original_creation, work)?;
    if context_source != binder_port {
        return Err(Failure::Invalid);
    }
    let context_port = if original_creation == call.creation {
        context_port
    } else {
        focus
            .values()
            .existing_forward_ports(context, call.creation, work)?
            .0
    };
    let (_, _, _, captures) = focus.values().existing_call_ports(
        call.code,
        call.caller_value_context,
        call.expression,
        call.callee_value_context,
        call.creation,
        work,
    )?;
    charge(work, captures.len())?;
    if captures
        .iter()
        .filter(|(_, source)| *source == context_port)
        .count()
        != 1
    {
        return Err(Failure::Invalid);
    }
    Ok(())
}

/// Bind a generated RegionBuffer service to the one checked Core Add whose
/// existing strict control sequence contains it. Explicit Region allocations
/// retain their ordinary original-node mapping.
fn checked_region_source(
    scope: &NetworkNativeIdentityScope<'_>,
    graph: &SummaryGraph,
    focus: &control::CompletionFocus<'_>,
    code: usize,
    checked_nodes: &HashSet<usize>,
    work: &mut TypeWorkBudget,
) -> Result<Option<usize>, Failure> {
    use crate::core::{EffectExprKind, EffectOperation};
    match focus
        .values()
        .original_control_node(code, scope.nodes(), work)
    {
        Ok(original) => return Ok(checked_nodes.contains(&original).then_some(original)),
        Err(Failure::Invalid) => {}
        Err(other) => return Err(other),
    }
    charge(work, checked_nodes.capacity())?;
    let mut found = None;
    for &original in checked_nodes {
        charge(work, 1)?;
        let Some(EffectExprKind::Operation(EffectOperation::RegionBuffer(buffer))) =
            scope.nodes().get(original).map(|node| &node.kind)
        else {
            continue;
        };
        if !matches!(
            &buffer.operation,
            crate::core::region::RegionBufferOperation::IntegerArithmetic(
                crate::core::Primitive::Add
            )
        ) {
            continue;
        }
        let (Some(left), Some(right)) = (buffer.operand, buffer.right) else {
            continue;
        };
        if [buffer.context, left, right]
            .iter()
            .any(|node| node.arena() != scope.arena())
        {
            return Err(Failure::Invalid);
        }
        let parent = original.checked_add(1).ok_or(Failure::Resource)?;
        if focus
            .values()
            .original_control_node(parent, scope.nodes(), work)?
            != original
        {
            return Err(Failure::Invalid);
        }
        let Some(control::Control::Sequence(children)) = graph.code.get(parent) else {
            return Err(Failure::Invalid);
        };
        let coordinates = [buffer.context, left, right].map(|node| node.index());
        let [Ok(context), Ok(left), Ok(right)] = coordinates else {
            return Err(Failure::Invalid);
        };
        let expected = [
            context.checked_add(1),
            left.checked_add(1),
            right.checked_add(1),
            Some(code),
        ];
        if expected.iter().any(Option::is_none) {
            return Err(Failure::Resource);
        }
        if children.as_slice() == expected.map(Option::unwrap) {
            if found.replace(original).is_some() {
                return Err(Failure::Invalid);
            }
        }
    }
    Ok(found)
}

/// Bind a generated receive path step to the exact currently active receive
/// sequence and its latest preceding observed outcome.
fn checked_receive_path_source(
    scope: &NetworkNativeIdentityScope<'_>,
    graph: &SummaryGraph,
    focus: &control::CompletionFocus<'_>,
    before: &control::State,
    outcome: control::NetworkOutcome,
    checked_nodes: &HashSet<usize>,
    work: &mut TypeWorkBudget,
) -> Result<usize, Failure> {
    use crate::core::{EffectExprKind, EffectOperation};
    let receive = scope.receive();
    if receive.arena() != scope.arena() {
        return Err(Failure::Invalid);
    }
    let original = receive.index().map_err(|_| Failure::Invalid)?;
    charge(work, 1)?;
    if !checked_nodes.contains(&original) {
        return Err(Failure::Invalid);
    }
    let Some(EffectExprKind::Operation(EffectOperation::RegionBuffer(buffer))) =
        scope.nodes().get(original).map(|node| &node.kind)
    else {
        return Err(Failure::Invalid);
    };
    let Some(EffectExprKind::Operation(EffectOperation::Network(owner))) = scope
        .nodes()
        .get(scope.owner().index().map_err(|_| Failure::Invalid)?)
        .map(|node| &node.kind)
    else {
        return Err(Failure::Invalid);
    };
    let api = crate::resolved::NetworkApi::for_module(owner.acquisition.builtin)
        .ok_or(Failure::Invalid)?;
    let crate::core::region::RegionBufferOperation::Network { effect, operation } =
        &buffer.operation
    else {
        return Err(Failure::Invalid);
    };
    if effect.effect() != api.io()
        || *operation != crate::types::OperationId::new(api.io(), 2)
        || buffer.right.is_some()
        || buffer.context.arena() != scope.arena()
    {
        return Err(Failure::Invalid);
    }
    let operand = buffer.operand.ok_or(Failure::Invalid)?;
    if operand.arena() != scope.arena() {
        return Err(Failure::Invalid);
    }
    let parent = original.checked_add(1).ok_or(Failure::Resource)?;
    if focus
        .values()
        .original_control_node(parent, scope.nodes(), work)?
        != original
    {
        return Err(Failure::Invalid);
    }
    let Some(control::Control::Sequence(parent_children)) = graph.code.get(parent) else {
        return Err(Failure::Invalid);
    };
    let [context, input, choice] = parent_children.as_slice() else {
        return Err(Failure::Invalid);
    };
    if *context
        != buffer
            .context
            .index()
            .map_err(|_| Failure::Invalid)?
            .checked_add(1)
            .ok_or(Failure::Resource)?
        || *input
            != operand
                .index()
                .map_err(|_| Failure::Invalid)?
                .checked_add(1)
                .ok_or(Failure::Resource)?
    {
        return Err(Failure::Invalid);
    }
    let Some(control::Control::Choice(branches)) = graph.code.get(*choice) else {
        return Err(Failure::Invalid);
    };
    charge(
        work,
        before
            .heap
            .len()
            .checked_add(branches.len())
            .ok_or(Failure::Resource)?,
    )?;
    let mut top = before
        .heap
        .iter()
        .filter(|edge| edge.address == before.stack);
    let edge = top.next().ok_or(Failure::Invalid)?;
    if top.next().is_some() {
        return Err(Failure::Invalid);
    }
    let control::Frame::Next {
        position,
        context,
        value_context,
    } = edge.frame
    else {
        return Err(Failure::Invalid);
    };
    if context != before.context
        || value_context != before.value_context
        || !branches.contains(&position.code)
    {
        return Err(Failure::Invalid);
    }
    let Some(control::Control::Sequence(children)) = graph.code.get(position.code) else {
        return Err(Failure::Invalid);
    };
    let ordinal = position.next.checked_sub(1).ok_or(Failure::Invalid)?;
    if children.get(ordinal) != Some(&before.position.code) {
        return Err(Failure::Invalid);
    }
    charge(work, ordinal)?;
    let mut observed = None;
    for &child in &children[..ordinal] {
        if let Some(control::Control::NetworkEvent {
            operation,
            operation_control,
            stage: control::NetworkEventStage::Observed,
            outcome,
            ..
        }) = graph.code.get(child)
        {
            if *operation != receive || *operation_control != parent {
                return Err(Failure::Invalid);
            }
            observed = Some(*outcome);
        }
    }
    if observed != Some(outcome) {
        return Err(Failure::Invalid);
    }
    Ok(original)
}

/// Check a reached body allocation or integer Add against its own previously
/// resumed DefaultAlloc query and actual operand port. This only accepts the
/// outward host route with one exact normal Next, case or matched call return;
/// all other alternatives refuse.
fn checked_body_region_return(
    scope: &NetworkNativeIdentityScope<'_>,
    graph: &SummaryGraph,
    focus: &control::CompletionFocus<'_>,
    before: &control::State,
    after: &control::State,
    detail: control::CompletionDetail,
    origins: &HashMap<usize, LocalOrigin>,
    checked_nodes: &HashSet<usize>,
    original: usize,
    module: crate::module::ModuleId,
    work: &mut TypeWorkBudget,
) -> Result<(), Failure> {
    use crate::core::{EffectExprKind, EffectOperation, PureComputation, PureExprKind};
    let api = crate::resolved::RegionApi::for_module(module).ok_or(Failure::Invalid)?;
    let Some(control::Control::Request(request)) = graph.code.get(before.position.code) else {
        return Err(Failure::Invalid);
    };
    if !request.region_service
        || request.operation != Some(crate::types::OperationId::new(api.default_alloc(), 0))
    {
        return Err(Failure::Invalid);
    }
    let context = match &scope.nodes().get(original).ok_or(Failure::Invalid)?.kind {
        EffectExprKind::Operation(EffectOperation::RegionAllocate(allocation))
            if allocation.api == module =>
        {
            allocation.context
        }
        EffectExprKind::Operation(EffectOperation::RegionBuffer(buffer))
            if buffer.api == module
                && (original == scope.receive().index().map_err(|_| Failure::Invalid)?
                    || matches!(
                        &buffer.operation,
                        crate::core::region::RegionBufferOperation::IntegerArithmetic(
                            crate::core::Primitive::Add
                        )
                    )) =>
        {
            buffer.context
        }
        _ => return Err(Failure::Invalid),
    };
    if context.arena() != scope.arena() {
        return Err(Failure::Invalid);
    }
    let EffectExprKind::Pure(PureExprKind::Variable(variable)) = &scope
        .nodes()
        .get(context.index().map_err(|_| Failure::Invalid)?)
        .ok_or(Failure::Invalid)?
        .kind
    else {
        return Err(Failure::Invalid);
    };
    charge(work, origins.capacity())?;
    let mut matching = origins.values().filter(|origin| {
        origin.binder == variable.binder() && origin.context == before.value_context
    });
    let origin = *matching.next().ok_or(Failure::Invalid)?;
    if matching.next().is_some() {
        return Err(Failure::Invalid);
    }
    let control::CompletionDetail::NativeReturn {
        event,
        boundary: None,
        edge: Some(returned),
    } = detail
    else {
        return Err(Failure::Invalid);
    };
    let (request_port, operand_port) = focus.values().existing_request_operand_ports(
        before.position.code,
        before.value_context,
        work,
    )?;
    if event.code != before.position.code
        || event.unknown
        || event.port != Some(request_port)
        || before.stack != returned.address
        || after.stack != returned.next
    {
        return Err(Failure::Invalid);
    }
    charge(work, before.heap.len())?;
    let mut top = before
        .heap
        .iter()
        .filter(|edge| edge.address == before.stack);
    if top.next() != Some(&returned) || top.next().is_some() {
        return Err(Failure::Invalid);
    }
    match returned.frame {
        control::Frame::Next {
            position,
            context,
            value_context,
        } if after.position == position
            && after.context == context
            && after.value_context == value_context => {}
        control::Frame::CallReturn { witness, .. } => {
            if after.position != (control::Position { code: 0, next: 0 }) {
                return Err(Failure::Invalid);
            }
            let call = focus.trace()?.call(witness, work)?;
            network_completion::matched_return_checked(focus, returned, call, before, after, work)?;
        }
        control::Frame::CaseReturn {
            code,
            ordinal,
            context,
            value_context,
        } => {
            if after.position != (control::Position { code: 0, next: 0 })
                || after.context != context
                || after.value_context != value_context
                || before.value_context != value_context
            {
                return Err(Failure::Invalid);
            }
            let original = focus
                .values()
                .original_control_node(code, scope.nodes(), work)?;
            if !checked_nodes.contains(&original)
                || !matches!(
                    scope.nodes().get(original).map(|node| &node.kind),
                    Some(EffectExprKind::Pure(PureExprKind::Computation(
                        PureComputation::Match(_)
                    )))
                )
            {
                return Err(Failure::Invalid);
            }
            let _ = focus
                .values()
                .existing_case_arm_ports(code, ordinal, value_context, work)?;
        }
        _ => return Err(Failure::Invalid),
    }
    let binding = origin.binding.checked_add(1).ok_or(Failure::Resource)?;
    let (binder_port, query_port) =
        focus
            .values()
            .existing_binding_ports(binding, origin.context, work)?;
    let context_code = context
        .index()
        .map_err(|_| Failure::Invalid)?
        .checked_add(1)
        .ok_or(Failure::Resource)?;
    let (context_port, context_source) =
        focus
            .values()
            .existing_forward_ports(context_code, before.value_context, work)?;
    if query_port != origin.port || context_source != binder_port || context_port != operand_port {
        return Err(Failure::Invalid);
    }
    Ok(())
}

/// Conditional result owned by one worker focus. This remains provisional:
/// its caller must bind the focus to the validator-owned side and publish only
/// after the entire validation succeeds. It grants no network permission.
struct ProvisionalCurrentLedger<'focus, 'graph, 'arena> {
    _focus: &'focus control::CompletionFocus<'graph>,
    _initialization: &'focus ConditionalInitializationCall<'arena>,
    _registrations: &'focus [(
        &'focus ConditionalRegistrationCall<'arena>,
        &'focus RegistrationResultMatch,
    )],
    owner: crate::core::NodeId,
    side: u8,
    requires_exclusive_update: bool,
    requires_peer_authentication: bool,
    _transition_returns: Vec<(usize, usize, usize, usize, usize)>,
    transition_bindings: Vec<(usize, crate::core::NodeId, crate::resolved::BinderId)>,
    transitions: Vec<(usize, usize, usize, usize)>,
    current: Vec<(usize, usize, usize, crate::resolved::BinderId)>,
    transition_calls: Vec<(crate::core::NodeId, crate::core::NodeId)>,
    argument_constructors: Vec<(crate::core::NodeId, crate::core::NodeId)>,
    checked_nodes: HashSet<usize>,
    body_calls: HashSet<usize>,
    body_closures: HashSet<usize>,
    helpers: Vec<(crate::resolved::BinderId, crate::core::NodeId)>,
    closure_origins: HashMap<usize, DefinitionProvenance>,
    query_origins: HashMap<usize, LocalOrigin>,
    verified_query_requests: HashSet<usize>,
    verified_query_resumes: HashSet<usize>,
    query_caller_contexts: HashMap<usize, usize>,
}

fn source_position(
    scope: &NetworkNativeIdentityScope<'_>,
    focus: &control::CompletionFocus<'_>,
    state: &control::State,
    node: crate::core::NodeId,
    work: &mut TypeWorkBudget,
) -> Result<bool, Failure> {
    if node.arena() != scope.arena() {
        return Err(Failure::Invalid);
    }
    match focus
        .values()
        .original_control_node(state.position.code, scope.nodes(), work)
    {
        Ok(original) => Ok(original == node.index().map_err(|_| Failure::Invalid)?),
        Err(Failure::Invalid) => Ok(false),
        Err(error) => Err(error),
    }
}

fn entered_call(
    graph: &SummaryGraph,
    focus: &control::CompletionFocus<'_>,
    from: usize,
    to: usize,
    transition: control::CompletionTransition,
    closure: crate::core::NodeId,
    work: &mut TypeWorkBudget,
) -> Result<usize, Failure> {
    let state = focus.trace()?.state(to, work)?;
    charge(work, state.heap.len())?;
    let mut matches = state.heap.iter().filter_map(|edge| match edge.frame {
        control::Frame::CallReturn { witness, .. } if edge.address == state.stack => Some(witness),
        _ => None,
    });
    let witness = matches.next().ok_or(Failure::Invalid)?;
    if matches.next().is_some() {
        return Err(Failure::Invalid);
    }
    let call = focus.trace()?.call(witness, work)?;
    let expected = closure.index().map_err(|_| Failure::Invalid)?;
    if call.target != expected || call.expression != expected {
        return Err(Failure::Invalid);
    }
    // This verifies the actual call edge, caller/callee contexts, frame and
    // existing argument/capture ports in the owning focus.
    let _ = network_completion::enter_call(
        graph,
        focus,
        from,
        to,
        transition,
        witness,
        &HashSet::new(),
        work,
    )?;
    Ok(witness)
}

/// Confirm one actual call's normal return against the checked source node
/// and stored closure. This is an observation, not a current-state fact.
fn matched_source_return(
    scope: &NetworkNativeIdentityScope<'_>,
    focus: &control::CompletionFocus<'_>,
    index: &network_completion::MatchedReturnIndex<'_, '_>,
    from: usize,
    to: usize,
    edge: control::Edge,
    native_return: bool,
    call_node: crate::core::NodeId,
    closure_node: crate::core::NodeId,
    work: &mut TypeWorkBudget,
) -> Result<Option<control::CompletionCall>, Failure> {
    if call_node.arena() != scope.arena() || closure_node.arena() != scope.arena() {
        return Err(Failure::Invalid);
    }
    let returned = if native_return {
        let control::Frame::CallReturn { witness, .. } = edge.frame else {
            return Err(Failure::Invalid);
        };
        let trace = focus.trace()?;
        let before = trace.state(from, work)?;
        let after = trace.state(to, work)?;
        network_completion::matched_return_checked(
            focus,
            edge,
            trace.call(witness, work)?,
            before,
            after,
            work,
        )?
    } else {
        index.matched_return(from, to, edge, work)?
    };
    let call = returned.call;
    let original = focus
        .values()
        .original_control_node(call.code, scope.nodes(), work)?;
    if original != call_node.index().map_err(|_| Failure::Invalid)? {
        return Ok(None);
    }
    let closure = closure_node.index().map_err(|_| Failure::Invalid)?;
    if call.target != closure || call.expression != closure {
        return Err(Failure::Invalid);
    }
    Ok(Some(call))
}

/// Find the exact pair projections of the returned call at an actual reached
/// Match arm. The stored source witness fixes the arm and field order; this
/// check binds them to existing ports in the same settled focus.
fn returned_ledger_port(
    scope: &NetworkNativeIdentityScope<'_>,
    focus: &control::CompletionFocus<'_>,
    state: &control::State,
    ordinal: usize,
    expected: &RegistrationResultMatch,
    result_port: usize,
    work: &mut TypeWorkBudget,
) -> Result<Option<(usize, usize)>, Failure> {
    let original =
        focus
            .values()
            .original_control_node(state.position.code, scope.nodes(), work)?;
    if expected.matching.arena() != scope.arena()
        || original != expected.matching.index().map_err(|_| Failure::Invalid)?
    {
        return Ok(None);
    }
    if ordinal != 0 {
        return Err(Failure::Invalid);
    }
    let (scrutinee, _, _) = focus
        .values()
        .existing_choice(state.position.code, state.value_context, work)?
        .ok_or(Failure::Invalid)?;
    if scrutinee != result_port {
        return Err(Failure::Invalid);
    }
    let bindings = focus.values().existing_arm_bindings(
        state.position.code,
        ordinal,
        state.value_context,
        work,
    )?;
    if bindings.len() != 2 {
        return Err(Failure::Invalid);
    }
    let mut ledger = None;
    let mut status = None;
    for (binding, value) in bindings {
        let (source, field, constructor) =
            focus.values().existing_pattern_projection(value, work)?;
        if source != scrutinee || constructor.is_some() {
            return Err(Failure::Invalid);
        }
        let slot = match field {
            0 => &mut ledger,
            1 => &mut status,
            _ => return Err(Failure::Invalid),
        };
        if slot.replace(binding).is_some() {
            return Err(Failure::Invalid);
        }
    }
    let ledger = ledger.ok_or(Failure::Invalid)?;
    let status = status.ok_or(Failure::Invalid)?;
    if ledger == status {
        return Err(Failure::Invalid);
    }
    Ok(Some((ledger, status)))
}

/// Authenticate one actual driver invocation and its Ledger tuple projection.
/// The result stays private until the actual parameter match arm executes.
fn entered_driver(
    scope: &NetworkNativeIdentityScope<'_>,
    graph: &SummaryGraph,
    focus: &control::CompletionFocus<'_>,
    from: usize,
    to: usize,
    edge: control::CompletionTransition,
    driver: &crate::core::ledger_checker::driver::CheckedDriverCall<'_>,
    role: crate::resolved::BinderId,
    source_port: usize,
    source_context: usize,
    query_origins: &HashMap<usize, LocalOrigin>,
    work: &mut TypeWorkBudget,
) -> Result<(usize, usize, usize), Failure> {
    if driver.input_role() != role {
        return Err(Failure::Invalid);
    }
    let before = focus.trace()?.state(from, work)?;
    if before.value_context != source_context
        || !source_position(scope, focus, before, driver.call(), work)?
    {
        return Err(Failure::Invalid);
    }
    let witness = entered_call(graph, focus, from, to, edge, driver.closure(), work)?;
    let call = focus.trace()?.call(witness, work)?;
    checked_context_capture(
        scope,
        focus,
        DefinitionProvenance {
            query: driver.definition_query(),
            binding: driver.definition_binding(),
            context: driver.definition_context(),
            closure: driver.closure(),
        },
        call,
        query_origins,
        work,
    )?;
    let (_, _, pairs, captures) = focus.values().existing_call_ports(
        call.code,
        call.caller_value_context,
        call.expression,
        call.callee_value_context,
        call.creation,
        work,
    )?;
    let [(_, actual_argument)] = pairs.as_slice() else {
        return Err(Failure::Invalid);
    };
    focus.values().check_closed_global_capture_ports(
        call.target,
        call.creation,
        call.callee_value_context,
        driver.captures(),
        driver.definition_context(),
        driver.type_parameters(),
        scope.arena(),
        scope.nodes(),
        &captures,
        work,
    )?;
    for capture in driver.captures() {
        charge(work, scope.bindings().len())?;
        let Some(crate::core::EffectExprKind::Pure(crate::core::PureExprKind::Variable(variable))) =
            scope
                .nodes()
                .get(capture.index().map_err(|_| Failure::Invalid)?)
                .map(|node| &node.kind)
        else {
            return Err(Failure::Invalid);
        };
        if variable.binder() == role
            || scope
                .bindings()
                .iter()
                .filter(|(binder, _)| *binder == variable.binder())
                .count()
                != 1
        {
            return Err(Failure::Invalid);
        }
    }
    // No additional captured or tuple field may transport the current ledger.
    charge(work, captures.len())?;
    if captures.iter().any(|&(_, source)| source == source_port) {
        return Err(Failure::Invalid);
    }
    let (tuple_port, alternatives) = focus.values().existing_original_tuple_fields(
        driver.binding(),
        driver.tuple(),
        driver.fields(),
        scope.arena(),
        scope.nodes(),
        call.caller_value_context,
        work,
    )?;
    if tuple_port != *actual_argument {
        return Err(Failure::Invalid);
    }
    for (creation, fields) in alternatives {
        if creation != source_context {
            return Err(Failure::Invalid);
        }
        let field = *fields.get(driver.field()).ok_or(Failure::Invalid)?;
        let code = driver
            .argument_field()
            .index()
            .map_err(|_| Failure::Invalid)?
            .checked_add(1)
            .ok_or(Failure::Resource)?;
        let (actual, source) = focus
            .values()
            .existing_forward_ports(code, creation, work)?;
        if actual != field || source != source_port {
            return Err(Failure::Invalid);
        }
        for (ordinal, field) in fields.iter().enumerate() {
            charge(work, 1)?;
            if ordinal == driver.field() {
                continue;
            }
            if *field == source_port {
                return Err(Failure::Invalid);
            }
            let other = driver.fields()[ordinal]
                .index()
                .map_err(|_| Failure::Invalid)?;
            if matches!(scope.nodes().get(other).map(|node| &node.kind),
                Some(crate::core::EffectExprKind::Pure(crate::core::PureExprKind::Variable(variable))) if variable.binder() == role)
            {
                return Err(Failure::Invalid);
            }
        }
    }
    let (projection_context, formal_port) = focus
        .values()
        .existing_worker_projection_context(call, work)?;
    if projection_context != call.callee_value_context {
        return Err(Failure::Invalid);
    }
    Ok((witness, formal_port, projection_context))
}

fn driver_formal_projection(
    scope: &NetworkNativeIdentityScope<'_>,
    focus: &control::CompletionFocus<'_>,
    before: &control::State,
    arm: usize,
    driver: &crate::core::ledger_checker::driver::CheckedDriverCall<'_>,
    formal_port: usize,
    work: &mut TypeWorkBudget,
) -> Result<Option<usize>, Failure> {
    if !source_position(scope, focus, before, driver.parameter_match(), work)? {
        return Ok(None);
    }
    if arm != 0 {
        return Err(Failure::Invalid);
    }
    let (scrutinee, _, _) = focus
        .values()
        .existing_choice(before.position.code, before.value_context, work)?
        .ok_or(Failure::Invalid)?;
    let original = driver
        .parameter_match()
        .index()
        .map_err(|_| Failure::Invalid)?;
    let Some(crate::core::EffectExprKind::Pure(crate::core::PureExprKind::Computation(
        crate::core::PureComputation::Match(branch),
    ))) = scope.nodes().get(original).map(|node| &node.kind)
    else {
        return Err(Failure::Invalid);
    };
    let scrutinee_code = branch
        .scrutinee()
        .index()
        .map_err(|_| Failure::Invalid)?
        .checked_add(1)
        .ok_or(Failure::Resource)?;
    let (actual, source) =
        focus
            .values()
            .existing_forward_ports(scrutinee_code, before.value_context, work)?;
    if actual != scrutinee || source != formal_port {
        return Err(Failure::Invalid);
    }
    let bindings = focus.values().existing_arm_bindings(
        before.position.code,
        arm,
        before.value_context,
        work,
    )?;
    if bindings.len() != driver.fields().len() {
        return Err(Failure::Invalid);
    }
    let mut result = None;
    let mut ordinals = HashSet::new();
    ordinals
        .try_reserve(bindings.len())
        .map_err(|_| Failure::Resource)?;
    for (binding, value) in bindings {
        charge(work, 1)?;
        let (source, field, constructor) =
            focus.values().existing_pattern_projection(value, work)?;
        if source != scrutinee
            || constructor.is_some()
            || field >= driver.fields().len()
            || !ordinals.insert(field)
        {
            return Err(Failure::Invalid);
        }
        if field == driver.field() && result.replace(binding).is_some() {
            return Err(Failure::Invalid);
        }
    }
    Ok(Some(result.ok_or(Failure::Invalid)?))
}

/// Follow an initializer and a finite set of nominated registrations on every
/// reached predecessor. Only the checked initializer binding and exact
/// returned-ledger forwarding are supported; other calls lose the candidate.
/// Observations stay private to this focus until the enclosing validation
/// succeeds and the remaining provider premises are established.
fn observe_direct_registration<'focus, 'graph, 'arena>(
    scope: &NetworkNativeIdentityScope<'_>,
    graph: &SummaryGraph,
    focus: &'focus control::CompletionFocus<'graph>,
    initialization: &'focus ConditionalInitializationCall<'arena>,
    registrations: &'focus [(
        &'focus ConditionalRegistrationCall<'arena>,
        &'focus RegistrationResultMatch,
    )],
    drivers: &[crate::core::ledger_checker::driver::CheckedDriverCall<'arena>],
    receives: &[crate::core::ledger_checker::driver::CheckedReceiveCall<'arena>],
    initial_binding: Option<crate::core::NodeId>,
    transitions: &[transition_observation::TransitionCall<'focus, 'arena>],
    default_handler: crate::core::NodeId,
    side: u8,
    work: &mut TypeWorkBudget,
) -> Result<ProvisionalCurrentLedger<'focus, 'graph, 'arena>, Failure> {
    let (registration, _) = *registrations.first().ok_or(Failure::Invalid)?;
    if scope.entry(usize::from(side)).is_none()
        || (drivers.is_empty()
            && initial_binding.is_none()
            && initialization.call() != registration.input())
        || initialization.provider_api() != registration.provider_api()
    {
        return Err(Failure::Invalid);
    }
    // The table is a finite set of actual call sites. Reuse of the same
    // authenticated definition is permitted, but ambiguous call or result
    // coordinates and a different provider/closure fail closed.
    let mut calls = HashSet::new();
    let mut matches = HashSet::new();
    for &(site, result) in registrations {
        charge(work, 1)?;
        if !site.same_definition(registration)
            || site.closure() != registration.closure()
            || site.provider_api() != registration.provider_api()
            || site.definition_query() != registration.definition_query()
        {
            return Err(Failure::Invalid);
        }
        calls.try_reserve(1).map_err(|_| Failure::Resource)?;
        matches.try_reserve(1).map_err(|_| Failure::Resource)?;
        if !calls.insert(site.call()) || !matches.insert(result.matching) {
            return Err(Failure::Invalid);
        }
    }
    charge(
        work,
        calls
            .capacity()
            .checked_add(matches.capacity())
            .ok_or(Failure::Resource)?,
    )?;
    if let Some(binding) = initial_binding {
        use crate::core::{EffectExprKind, PureComputation, PureExprKind};
        if binding.arena() != scope.arena() || registration.input().arena() != scope.arena() {
            return Err(Failure::Invalid);
        }
        let Some(EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Bind(bind)))) =
            scope
                .nodes()
                .get(binding.index().map_err(|_| Failure::Invalid)?)
                .map(|node| &node.kind)
        else {
            return Err(Failure::Invalid);
        };
        let Some(EffectExprKind::Pure(PureExprKind::Variable(input))) = scope
            .nodes()
            .get(registration.input().index().map_err(|_| Failure::Invalid)?)
            .map(|node| &node.kind)
        else {
            return Err(Failure::Invalid);
        };
        if bind.initializer() != initialization.call()
            || (drivers.is_empty() && bind.binder().id() != input.binder())
        {
            return Err(Failure::Invalid);
        }
    }
    let initial_definitions = [
        DefinitionProvenance {
            query: initialization.definition_query(),
            binding: initialization.definition_binding(),
            context: initialization.definition_context(),
            closure: initialization.closure(),
        },
        DefinitionProvenance {
            query: registration.definition_query(),
            binding: registration.definition_binding(),
            context: registration.definition_context(),
            closure: registration.closure(),
        },
    ];
    if initial_definitions[0].query == initial_definitions[1].query
        || initial_definitions[0].closure == initial_definitions[1].closure
    {
        return Err(Failure::Invalid);
    }
    let mut definitions = Vec::new();
    charge(
        work,
        transitions.len().checked_add(2).ok_or(Failure::Resource)?,
    )?;
    definitions
        .try_reserve(transitions.len().checked_add(2).ok_or(Failure::Resource)?)
        .map_err(|_| Failure::Resource)?;
    definitions.extend(initial_definitions);
    let mut extra_roots = Vec::new();
    let mut argument_constructors = Vec::new();
    for (position, &transition) in transitions.iter().enumerate() {
        if transition.provider_api() != initialization.provider_api() {
            return Err(Failure::Invalid);
        }
        let definition = transition.definition();
        if definitions
            .iter()
            .any(|old| old.query == definition.query || old.closure == definition.closure)
        {
            charge(work, position)?;
            if !transitions[..position]
                .iter()
                .any(|old| old.same_definition(transition))
            {
                return Err(Failure::Invalid);
            }
        } else {
            definitions.push(definition);
        }
        transition.extend_roots(&mut extra_roots, work)?;
        if let Some(pair) = transition.argument_constructor(work)? {
            charge(
                work,
                argument_constructors
                    .len()
                    .checked_add(1)
                    .ok_or(Failure::Resource)?,
            )?;
            if argument_constructors
                .iter()
                .any(|&(call, closure)| call == pair.0 || closure == pair.1)
            {
                return Err(Failure::Invalid);
            }
            argument_constructors
                .try_reserve(1)
                .map_err(|_| Failure::Resource)?;
            argument_constructors.push(pair);
        }
    }
    for (driver_index, driver) in drivers.iter().enumerate() {
        charge(
            work,
            definitions
                .len()
                .checked_add(driver_index)
                .and_then(|n| n.checked_add(1))
                .ok_or(Failure::Resource)?,
        )?;
        for previous in &drivers[..driver_index] {
            if previous.closure() == driver.closure()
                && (previous.formal() != driver.formal()
                    || previous.field() != driver.field()
                    || previous.fields().len() != driver.fields().len()
                    || previous.definition_binding() != driver.definition_binding()
                    || previous.definition_context() != driver.definition_context())
            {
                return Err(Failure::Invalid);
            }
        }
        if driver.provider_api() != initialization.provider_api() {
            return Err(Failure::Invalid);
        }
        let definition = DefinitionProvenance {
            query: driver.definition_query(),
            binding: driver.definition_binding(),
            context: driver.definition_context(),
            closure: driver.closure(),
        };
        if let Some(old) = definitions
            .iter()
            .find(|old| old.query == definition.query || old.closure == definition.closure)
        {
            if old.query != definition.query
                || old.binding != definition.binding
                || old.context != definition.context
                || old.closure != definition.closure
            {
                return Err(Failure::Invalid);
            }
        } else {
            definitions.try_reserve(1).map_err(|_| Failure::Resource)?;
            definitions.push(definition);
            charge(work, 1)?;
            extra_roots.try_reserve(1).map_err(|_| Failure::Resource)?;
            extra_roots.push(driver.definition_root());
        }
    }
    for receive in receives {
        charge(
            work,
            definitions.len().checked_add(1).ok_or(Failure::Resource)?,
        )?;
        if receive.provider_api() != initialization.provider_api() {
            return Err(Failure::Invalid);
        }
        let definition = DefinitionProvenance {
            query: receive.definition_query(),
            binding: receive.definition_binding(),
            context: receive.definition_context(),
            closure: receive.closure(),
        };
        if let Some(old) = definitions
            .iter()
            .find(|old| old.query == definition.query || old.closure == definition.closure)
        {
            if old.query != definition.query
                || old.binding != definition.binding
                || old.context != definition.context
                || old.closure != definition.closure
            {
                return Err(Failure::Invalid);
            }
        } else {
            definitions.try_reserve(1).map_err(|_| Failure::Resource)?;
            definitions.push(definition);
            charge(work, 1)?;
            extra_roots.try_reserve(1).map_err(|_| Failure::Resource)?;
            extra_roots.push(receive.definition_binding());
        }
    }
    let root = scope.root().index().map_err(|_| Failure::Invalid)?;
    let root_code = root.checked_add(1).ok_or(Failure::Resource)?;
    if focus
        .values()
        .original_control_node(root_code, scope.nodes(), work)?
        != root
    {
        return Err(Failure::Invalid);
    }
    let trace = focus.trace()?;
    if trace.focus().is_ok() {
        return Err(Failure::Invalid);
    }
    let (mut body_calls, mut body_closures, mut checked_nodes) =
        checked_call_sites(scope, initialization, registration, &extra_roots, work)?;
    include_argument_nodes(
        scope,
        registration.argument_binding(),
        &mut checked_nodes,
        work,
    )?;
    for &(next, _) in registrations.iter().skip(1) {
        include_argument_nodes(scope, next.argument_binding(), &mut checked_nodes, work)?;
    }
    for driver in drivers {
        include_argument_nodes(scope, driver.binding(), &mut checked_nodes, work)?;
    }
    for receive in receives {
        include_argument_nodes(scope, receive.call(), &mut checked_nodes, work)?;
    }
    for &transition in transitions {
        include_argument_nodes(
            scope,
            transition.argument_binding(),
            &mut checked_nodes,
            work,
        )?;
        charge(work, 1)?;
        body_calls.try_reserve(1).map_err(|_| Failure::Resource)?;
        body_calls.insert(transition.call().index().map_err(|_| Failure::Invalid)?);
    }
    for &(call, closure) in &argument_constructors {
        charge(work, 1)?;
        body_calls.try_reserve(1).map_err(|_| Failure::Resource)?;
        body_closures
            .try_reserve(1)
            .map_err(|_| Failure::Resource)?;
        body_calls.insert(call.index().map_err(|_| Failure::Invalid)?);
        body_closures.insert(closure.index().map_err(|_| Failure::Invalid)?);
    }
    let base_helpers = registration.linked_helpers();
    let mut candidates = Vec::new();
    charge(work, base_helpers.len())?;
    candidates
        .try_reserve(base_helpers.len())
        .map_err(|_| Failure::Resource)?;
    candidates.extend(base_helpers);
    for &transition in transitions {
        transition.extend_helpers(&mut candidates, work)?;
    }
    let mut helpers = Vec::new();
    for (binder, closure) in candidates {
        charge(work, helpers.len().checked_add(1).ok_or(Failure::Resource)?)?;
        if let Some((_, existing)) = helpers.iter().find(|(existing, _)| *existing == binder) {
            if *existing != closure {
                return Err(Failure::Invalid);
            }
            continue;
        }
        helpers.try_reserve(1).map_err(|_| Failure::Resource)?;
        helpers.push((binder, closure));
    }
    let index = network_completion::MatchedReturnIndex::new(focus, work)?;
    let states = index.states();
    let edges = trace.indexed_edges(work)?;
    let mut details = HashMap::new();
    trace.visit_details(work, |id, detail, work| {
        charge(work, 1)?;
        details.try_reserve(1).map_err(|_| Failure::Resource)?;
        if details.insert(id, detail).is_some() {
            return Err(Failure::Invalid);
        }
        Ok(())
    })?;
    charge(work, details.capacity())?;
    charge(
        work,
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
    for (number, &(from, to, _)) in edges.iter().enumerate() {
        if to >= states.len() {
            return Err(Failure::Invalid);
        }
        let entries = outgoing.get_mut(from).ok_or(Failure::Invalid)?;
        charge(work, 1)?;
        entries.try_reserve(1).map_err(|_| Failure::Resource)?;
        entries.push(number);
    }
    for entries in &outgoing {
        charge(work, entries.capacity())?;
    }
    // Authenticate this actual initialization closure's context query on the
    // same converged startup trace. The selected handler must be the checked
    // entry provider and each reached alternative must follow its direct
    // normal Resume. This is only the first part of provider correspondence:
    // the returned port has not yet been tied to closure captures or uses.
    let bindings = query_bindings(scope, &checked_nodes, initialization.provider_api(), work)?;
    let closure_origins = closure_bindings(scope, &bindings, initialization.provider_api(), work)?;
    let mut query_count = Vec::new();
    charge(work, definitions.len())?;
    query_count
        .try_reserve_exact(definitions.len())
        .map_err(|_| Failure::Resource)?;
    query_count.resize(definitions.len(), 0usize);
    let mut query_origins = HashMap::new();
    let mut verified_query_requests = HashSet::new();
    let mut verified_query_resumes = HashSet::new();
    let mut query_caller_contexts = HashMap::new();
    for (id, maybe_state) in states.iter().enumerate() {
        charge(work, 1)?;
        let state = maybe_state.ok_or(Failure::Invalid)?;
        if !matches!(
            graph.code.get(state.position.code),
            Some(control::Control::Request(_))
        ) {
            continue;
        }
        let original =
            match focus
                .values()
                .original_control_node(state.position.code, scope.nodes(), work)
            {
                Ok(index) => index,
                Err(Failure::Invalid) => continue,
                Err(other) => return Err(other),
            };
        let Some(&(binding, binder)) = bindings.get(&original) else {
            continue;
        };
        let mut owner = None;
        for (i, definition) in definitions.iter().enumerate() {
            if source_position(scope, focus, state, definition.query, work)? {
                if owner.replace(i).is_some() {
                    return Err(Failure::Invalid);
                }
            }
        }
        if let Some(owner) = owner {
            query_count[owner] = query_count[owner].checked_add(1).ok_or(Failure::Resource)?;
        }
        let query_port =
            focus
                .values()
                .existing_port(state.position.code, state.value_context, work)?;
        let local_origin = LocalOrigin {
            binding,
            binder,
            context: state.value_context,
            port: query_port,
        };
        let successors = outgoing.get(id).ok_or(Failure::Invalid)?;
        if successors.is_empty() {
            return Err(Failure::Invalid);
        }
        for &number in successors {
            let (from, to, _) = *edges.get(number).ok_or(Failure::Invalid)?;
            if from != id {
                return Err(Failure::Invalid);
            }
            let after = states.get(to).copied().flatten().ok_or(Failure::Invalid)?;
            let query = super::network_end::context_query(scope, graph, focus, state, after, work)?;
            let control::Frame::Clause { handler, .. } = query.clause.frame else {
                return Err(Failure::Invalid);
            };
            if default_handler.arena() != scope.arena()
                || focus
                    .values()
                    .original_control_node(handler, scope.nodes(), work)?
                    != default_handler.index().map_err(|_| Failure::Invalid)?
            {
                return Err(Failure::Invalid);
            }
            let mut paths = VecDeque::new();
            charge(work, 1)?;
            paths.try_reserve(1).map_err(|_| Failure::Resource)?;
            paths.push_back((to, 0u8));
            while let Some((current, stage)) = paths.pop_front() {
                charge(work, 1)?;
                let current_state = states
                    .get(current)
                    .copied()
                    .flatten()
                    .ok_or(Failure::Invalid)?;
                let current_control = graph
                    .code
                    .get(current_state.position.code)
                    .ok_or(Failure::Invalid)?;
                let next_edges = outgoing.get(current).ok_or(Failure::Invalid)?;
                if next_edges.is_empty() {
                    return Err(Failure::Invalid);
                }
                for &next_number in next_edges {
                    charge(work, 1)?;
                    let (_, next_id, _) = *edges.get(next_number).ok_or(Failure::Invalid)?;
                    let next_state = states
                        .get(next_id)
                        .copied()
                        .flatten()
                        .ok_or(Failure::Invalid)?;
                    match (stage, current_control) {
                        (0, control::Control::Resume { value, .. })
                            if current_state.position.code == query.resume
                                && *value == query.value
                                && current_state.position.next == 0
                                && next_state.position.code == query.value =>
                        {
                            record_query_path(
                                &mut query_caller_contexts,
                                current,
                                state.value_context,
                                work,
                            )?;
                            charge(work, 1)?;
                            verified_query_resumes
                                .try_reserve(1)
                                .map_err(|_| Failure::Resource)?;
                            verified_query_resumes.insert(current);
                        }
                        (1, control::Control::Return)
                            if current_state.position.code == query.value
                                && next_state.position.code == query.resume
                                && next_state.position.next == 1 =>
                        {
                            record_query_path(
                                &mut query_caller_contexts,
                                current,
                                state.value_context,
                                work,
                            )?;
                        }
                        (2, control::Control::Resume { owner, value })
                            if current_state.position.code == query.resume
                                && *value == query.value
                                && current_state.position.next == 1 =>
                        {
                            charge(work, current_state.heap.len())?;
                            let mut top = current_state
                                .heap
                                .iter()
                                .filter(|edge| edge.address == current_state.stack);
                            let edge = top.next().ok_or(Failure::Invalid)?;
                            if top.next().is_some()
                                || *edge != query.clause
                                || !matches!(edge.frame, control::Frame::Clause { owner: actual, consumed: false, .. } if actual == *owner)
                                || next_state.position.code != 0
                            {
                                return Err(Failure::Invalid);
                            }
                            record_query_path(
                                &mut query_caller_contexts,
                                current,
                                state.value_context,
                                work,
                            )?;
                            // The direct resume reinstalls the actual captured
                            // continuation. Check every return from its top
                            // frame restores this query's saved caller.
                            if !matches!(
                                graph.code.get(next_state.position.code),
                                Some(control::Control::Return)
                            ) {
                                return Err(Failure::Invalid);
                            }
                            charge(work, next_state.heap.len())?;
                            let mut restored_top = next_state
                                .heap
                                .iter()
                                .filter(|edge| edge.address == next_state.stack);
                            let restored = *restored_top.next().ok_or(Failure::Invalid)?;
                            if restored_top.next().is_some() {
                                return Err(Failure::Invalid);
                            }
                            let control::Frame::Next {
                                position,
                                context,
                                value_context,
                            } = restored.frame
                            else {
                                return Err(Failure::Invalid);
                            };
                            if context != state.context || value_context != state.value_context {
                                return Err(Failure::Invalid);
                            }
                            let restore_edges = outgoing.get(next_id).ok_or(Failure::Invalid)?;
                            if restore_edges.is_empty() {
                                return Err(Failure::Invalid);
                            }
                            for &restore_number in restore_edges {
                                charge(work, 1)?;
                                let (restore_from, restore_to, transition) =
                                    *edges.get(restore_number).ok_or(Failure::Invalid)?;
                                let control::CompletionTransition::Detail(detail_id) = transition
                                else {
                                    return Err(Failure::Invalid);
                                };
                                let Some(control::CompletionDetail::Return(actual)) =
                                    details.get(&detail_id)
                                else {
                                    return Err(Failure::Invalid);
                                };
                                let restored_state = states
                                    .get(restore_to)
                                    .copied()
                                    .flatten()
                                    .ok_or(Failure::Invalid)?;
                                if restore_from != next_id
                                    || *actual != restored
                                    || restored_state.stack != restored.next
                                    || restored_state.position != position
                                    || restored_state.context != context
                                    || restored_state.value_context != value_context
                                {
                                    return Err(Failure::Invalid);
                                }
                            }
                            record_query_path(
                                &mut query_caller_contexts,
                                next_id,
                                state.value_context,
                                work,
                            )?;
                            charge(work, 1)?;
                            verified_query_resumes
                                .try_reserve(1)
                                .map_err(|_| Failure::Resource)?;
                            verified_query_resumes.insert(current);
                            continue;
                        }
                        _ => return Err(Failure::Invalid),
                    }
                    charge(work, 1)?;
                    paths.try_reserve(1).map_err(|_| Failure::Resource)?;
                    paths.push_back((next_id, stage + 1));
                }
            }
            charge(work, paths.capacity())?;
        }
        charge(work, 1)?;
        query_origins
            .try_reserve(1)
            .map_err(|_| Failure::Resource)?;
        if query_origins
            .insert(query_port, local_origin)
            .is_some_and(|previous| previous != local_origin)
        {
            return Err(Failure::Invalid);
        }
        charge(work, 1)?;
        verified_query_requests
            .try_reserve(1)
            .map_err(|_| Failure::Resource)?;
        verified_query_requests.insert(id);
    }
    if query_count.contains(&0) {
        return Err(Failure::Invalid);
    }
    charge(
        work,
        query_origins
            .capacity()
            .checked_add(verified_query_requests.capacity())
            .ok_or(Failure::Resource)?
            .checked_add(verified_query_resumes.capacity())
            .ok_or(Failure::Resource)?
            .checked_add(query_caller_contexts.capacity())
            .ok_or(Failure::Resource)?,
    )?;
    #[cfg(test)]
    eprintln!(
        "N3 initializer/registration context queries: {query_count:?} reached states; later allocation and reentry checks remain open"
    );
    let mut pending = VecDeque::new();
    let mut seen = HashSet::new();
    let mut requires_exclusive_update = false;
    let mut requires_peer_authentication = false;
    let mut transition_returns = Vec::new();
    let mut transition_bindings = Vec::new();
    let mut projected = HashMap::new();
    let mut current = HashMap::new();
    pending.try_reserve(1).map_err(|_| Failure::Resource)?;
    pending.push_back((0usize, Phase::BeforeInitialization));
    while let Some((id, mut phase)) = pending.pop_front() {
        charge(work, 1)?;
        seen.try_reserve(1).map_err(|_| Failure::Resource)?;
        if !seen.insert((id, phase)) {
            continue;
        }
        if let Phase::Projected {
            ledger,
            status,
            input,
            context,
            ordinal,
        } = phase
        {
            if states
                .get(id)
                .copied()
                .flatten()
                .ok_or(Failure::Invalid)?
                .value_context
                != context
            {
                return Err(Failure::Invalid);
            }
            charge(work, 1)?;
            projected.try_reserve(1).map_err(|_| Failure::Resource)?;
            if projected
                .insert(id, (ledger, status, input, context, ordinal))
                .is_some_and(|old| old != (ledger, status, input, context, ordinal))
            {
                return Err(Failure::Invalid);
            }
            phase = Phase::Current {
                port: ledger,
                context,
                ordinal,
                role: registrations.get(ordinal).ok_or(Failure::Invalid)?.1.ledger,
            };
        }
        let before = states.get(id).copied().flatten().ok_or(Failure::Invalid)?;
        if let Phase::Current {
            port,
            context,
            ordinal,
            role,
        } = phase
        {
            let original = match focus.values().original_control_node(
                before.position.code,
                scope.nodes(),
                work,
            ) {
                Ok(original) => Some(original),
                Err(Failure::Invalid) => None,
                Err(other) => return Err(other),
            };
            charge(work, argument_constructors.len())?;
            if let Some((constructor, _)) = argument_constructors
                .iter()
                .enumerate()
                .find(|(_, (_, closure))| closure.index().ok() == original)
            {
                if before.value_context != context || query_caller_contexts.contains_key(&id) {
                    return Err(Failure::Invalid);
                }
                phase = Phase::PreparingArgument {
                    port,
                    context,
                    ordinal,
                    role,
                    constructor,
                };
            }
        }
        let region_source = if matches!(graph.code.get(before.position.code), Some(control::Control::Request(request)) if request.region_service)
        {
            let mut source = checked_region_source(
                scope,
                graph,
                focus,
                before.position.code,
                &checked_nodes,
                work,
            )?;
            if source.is_none()
                && let Phase::Receiving {
                    stage: ReceiveStage::Observed(outcome),
                    ..
                } = phase
            {
                source = Some(checked_receive_path_source(
                    scope,
                    graph,
                    focus,
                    before,
                    outcome,
                    &checked_nodes,
                    work,
                )?);
            }
            source
        } else {
            None
        };
        if let Phase::Current { context, .. } = phase {
            if query_caller_contexts
                .get(&id)
                .is_some_and(|saved| *saved != context)
                || (before.value_context != context
                    && query_caller_contexts.get(&id) != Some(&context))
            {
                phase = Phase::Invalidated;
            }
        }
        if let Phase::PreparingArgument { context, .. } = phase {
            if query_caller_contexts
                .get(&id)
                .is_some_and(|saved| *saved != context)
                || (before.value_context != context
                    && query_caller_contexts.get(&id) != Some(&context))
            {
                return Err(Failure::Invalid);
            }
        }
        if matches!(
            phase,
            Phase::PreparingArgument { .. } | Phase::RunningArgument { .. }
        ) {
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
                let is_closure = matches!(
                    scope.nodes().get(original).map(|node| &node.kind),
                    Some(crate::core::EffectExprKind::Pure(
                        crate::core::PureExprKind::Value(crate::core::PureValue::Function(_))
                    )) | Some(crate::core::EffectExprKind::Operation(
                        crate::core::EffectOperation::RegionClosure(_)
                    ))
                );
                let permitted = if let Phase::PreparingArgument { constructor, .. } = phase {
                    argument_constructors
                        .get(constructor)
                        .is_some_and(|(_, closure)| closure.index().ok() == Some(original))
                } else {
                    false
                };
                if is_closure && !permitted {
                    return Err(Failure::Invalid);
                }
            }
        }
        if let Phase::Current {
            port,
            context,
            role,
            ..
        } = phase
        {
            if before.value_context == context && !query_caller_contexts.contains_key(&id) {
                charge(work, 1)?;
                current.try_reserve(1).map_err(|_| Failure::Resource)?;
                if current
                    .insert(id, (port, context, role))
                    .is_some_and(|old| old != (port, context, role))
                {
                    return Err(Failure::Invalid);
                }
            }
        }
        if matches!(
            phase,
            Phase::Current { .. }
                | Phase::Initialized { .. }
                | Phase::Returned { .. }
                | Phase::TransitionReturned { .. }
        ) {
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
            let constructs_closure = original.is_some_and(|original| {
                matches!(
                    scope.nodes().get(original).map(|node| &node.kind),
                    Some(crate::core::EffectExprKind::Pure(
                        crate::core::PureExprKind::Value(crate::core::PureValue::Function(_))
                    )) | Some(crate::core::EffectExprKind::Operation(
                        crate::core::EffectOperation::RegionClosure(_)
                    ))
                )
            });
            let unknown_region = matches!(control, control::Control::Request(request) if request.region_service)
                && region_source.is_none();
            if (matches!(control, control::Control::Request(request) if !request.region_service)
                && !verified_query_requests.contains(&id))
                || constructs_closure
                || unknown_region
                || matches!(
                    control,
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
                        | control::Control::Discard { .. }
                )
                || (matches!(control, control::Control::Resume { .. })
                    && !verified_query_resumes.contains(&id))
            {
                phase = Phase::Invalidated;
            }
        }
        if matches!(
            phase,
            Phase::Initializing(_)
                | Phase::Initialized { .. }
                | Phase::Registering { .. }
                | Phase::Transitioning { .. }
                | Phase::TransitionReturned { .. }
                | Phase::Receiving { .. }
                | Phase::Returned { .. }
                | Phase::Current { .. }
                | Phase::PreparingArgument { .. }
                | Phase::RunningArgument { .. }
        ) {
            match graph
                .code
                .get(before.position.code)
                .ok_or(Failure::Invalid)?
            {
                control::Control::Request(request) if !request.region_service => {
                    if !verified_query_requests.contains(&id) {
                        return Err(Failure::Invalid);
                    }
                }
                control::Control::NetworkEvent { .. }
                    if !matches!(phase, Phase::Receiving { .. }) =>
                {
                    return Err(Failure::Invalid);
                }
                control::Control::Unavailable
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
                control::Control::Resume { .. } if !verified_query_resumes.contains(&id) => {
                    return Err(Failure::Invalid);
                }
                _ => {}
            }
        }
        let body_region = (region_source.is_some()
            || matches!(
                phase,
                Phase::Initializing(_)
                    | Phase::Initialized { .. }
                    | Phase::Registering { .. }
                    | Phase::Transitioning { .. }
                    | Phase::TransitionReturned { .. }
                    | Phase::Receiving { .. }
                    | Phase::PreparingArgument { .. }
                    | Phase::RunningArgument { .. }
            ))
            && matches!(graph.code.get(before.position.code), Some(control::Control::Request(request)) if request.region_service);
        if body_region && outgoing.get(id).ok_or(Failure::Invalid)?.is_empty() {
            return Err(Failure::Invalid);
        }
        for &number in outgoing.get(id).ok_or(Failure::Invalid)? {
            charge(work, 1)?;
            let (from, to, transition) = *edges.get(number).ok_or(Failure::Invalid)?;
            if from != id {
                return Err(Failure::Invalid);
            }
            if matches!(
                phase,
                Phase::Initializing(_) | Phase::Registering { .. } | Phase::Transitioning { .. }
            ) && let control::CompletionTransition::Call { target, .. } = transition
            {
                if target
                    == initialization
                        .closure()
                        .index()
                        .map_err(|_| Failure::Invalid)?
                    || target
                        == registration
                            .closure()
                            .index()
                            .map_err(|_| Failure::Invalid)?
                    || transitions
                        .iter()
                        .any(|candidate| candidate.closure().index().ok() == Some(target))
                {
                    return Err(Failure::Invalid);
                }
                authenticate_body_call(
                    scope,
                    graph,
                    focus,
                    from,
                    to,
                    transition,
                    &body_calls,
                    &body_closures,
                    &helpers,
                    &closure_origins,
                    &query_origins,
                    work,
                )?;
            }
            if body_region {
                let control::CompletionTransition::Detail(detail_id) = transition else {
                    return Err(Failure::Invalid);
                };
                checked_body_region_return(
                    scope,
                    graph,
                    focus,
                    before,
                    states.get(to).copied().flatten().ok_or(Failure::Invalid)?,
                    *details.get(&detail_id).ok_or(Failure::Invalid)?,
                    &query_origins,
                    &checked_nodes,
                    region_source.ok_or(Failure::Invalid)?,
                    initialization.provider_api(),
                    work,
                )?;
            }
            let mut next = phase;
            if let Phase::Receiving {
                receive,
                witness,
                port,
                context,
                ordinal,
                role,
                stage,
            } = phase
            {
                if matches!(transition, control::CompletionTransition::Call { .. }) {
                    return Err(Failure::Invalid);
                }
                if let Some(control::Control::NetworkEvent {
                    operation,
                    stage: event_stage,
                    outcome,
                    ..
                }) = graph.code.get(before.position.code)
                {
                    if *operation != scope.receive() || operation.arena() != scope.arena() {
                        return Err(Failure::Invalid);
                    }
                    let Some(crate::core::EffectExprKind::Operation(
                        crate::core::EffectOperation::RegionBuffer(buffer),
                    )) = scope
                        .nodes()
                        .get(operation.index().map_err(|_| Failure::Invalid)?)
                        .map(|node| &node.kind)
                    else {
                        return Err(Failure::Invalid);
                    };
                    let Some(crate::core::EffectExprKind::Operation(
                        crate::core::EffectOperation::Network(owner),
                    )) = scope
                        .nodes()
                        .get(scope.owner().index().map_err(|_| Failure::Invalid)?)
                        .map(|node| &node.kind)
                    else {
                        return Err(Failure::Invalid);
                    };
                    let api = crate::resolved::NetworkApi::for_module(owner.acquisition.builtin)
                        .ok_or(Failure::Invalid)?;
                    let crate::core::region::RegionBufferOperation::Network {
                        effect,
                        operation: actual,
                    } = &buffer.operation
                    else {
                        return Err(Failure::Invalid);
                    };
                    if effect.effect() != api.io()
                        || *actual != crate::types::OperationId::new(api.io(), 2)
                    {
                        return Err(Failure::Invalid);
                    }
                    let operand = buffer.operand.ok_or(Failure::Invalid)?;
                    if focus.values().existing_original_worker_origin(
                        operand,
                        scope.arena(),
                        scope.nodes(),
                        before.value_context,
                        work,
                    )? != (scope.owner(), side)
                    {
                        return Err(Failure::Invalid);
                    }
                    let next_stage = match (stage, *event_stage, *outcome) {
                        (ReceiveStage::Before, control::NetworkEventStage::Observed, outcome) => {
                            ReceiveStage::Observed(outcome)
                        }
                        (
                            ReceiveStage::Observed(control::NetworkOutcome::Message),
                            control::NetworkEventStage::Observed,
                            control::NetworkOutcome::Failure,
                        ) => {
                            checked_receive_path_source(
                                scope,
                                graph,
                                focus,
                                before,
                                control::NetworkOutcome::Message,
                                &checked_nodes,
                                work,
                            )?;
                            ReceiveStage::Observed(control::NetworkOutcome::Failure)
                        }
                        (
                            ReceiveStage::Observed(control::NetworkOutcome::Message),
                            control::NetworkEventStage::MessageCommit,
                            control::NetworkOutcome::Message,
                        ) => ReceiveStage::Committed,
                        (
                            ReceiveStage::Committed,
                            control::NetworkEventStage::Reply,
                            control::NetworkOutcome::Message,
                        ) => ReceiveStage::Replied,
                        (
                            ReceiveStage::Observed(old),
                            control::NetworkEventStage::Reply,
                            outcome,
                        ) if old == outcome && outcome != control::NetworkOutcome::Message => {
                            ReceiveStage::Replied
                        }
                        _ => return Err(Failure::Invalid),
                    };
                    next = Phase::Receiving {
                        receive,
                        witness,
                        port,
                        context,
                        ordinal,
                        role,
                        stage: next_stage,
                    };
                }
            }
            // Transfer the source role only on the actual second child of an
            // original Bind, after its initializer's saved Next has returned.
            if let (
                Phase::Current {
                    port,
                    context,
                    ordinal,
                    role,
                },
                control::CompletionTransition::Sequence { ordinal: 1 },
            ) = (phase, transition)
            {
                let original = match focus.values().original_control_node(
                    before.position.code,
                    scope.nodes(),
                    work,
                ) {
                    Ok(original) => Some(original),
                    Err(Failure::Invalid) => None,
                    Err(error) => return Err(error),
                };
                if let Some(crate::core::EffectExprKind::Pure(
                    crate::core::PureExprKind::Computation(crate::core::PureComputation::Bind(
                        bind,
                    )),
                )) = original
                    .and_then(|id| scope.nodes().get(id))
                    .map(|node| &node.kind)
                {
                    let init = bind.initializer().index().map_err(|_| Failure::Invalid)?;
                    if matches!(scope.nodes().get(init).map(|node| &node.kind), Some(crate::core::EffectExprKind::Pure(crate::core::PureExprKind::Variable(variable))) if variable.binder() == role)
                    {
                        let body = bind.body().index().map_err(|_| Failure::Invalid)?;
                        let Some(control::Control::Sequence(children)) =
                            graph.code.get(before.position.code)
                        else {
                            return Err(Failure::Invalid);
                        };
                        if children.as_slice()
                            != [
                                init.checked_add(1).ok_or(Failure::Resource)?,
                                body.checked_add(1).ok_or(Failure::Resource)?,
                            ]
                            || before.position.next != 1
                        {
                            return Err(Failure::Invalid);
                        }
                        let after = trace.state(to, work)?;
                        if before.value_context != context
                            || after.value_context != context
                            || after.position.code
                                != body.checked_add(1).ok_or(Failure::Resource)?
                        {
                            return Err(Failure::Invalid);
                        }
                        let (binder_port, initializer_port) = focus
                            .values()
                            .existing_binding_ports(before.position.code, context, work)?;
                        if initializer_port != port {
                            return Err(Failure::Invalid);
                        }
                        next = Phase::Current {
                            port: binder_port,
                            context,
                            ordinal,
                            role: bind.binder().id(),
                        };
                    }
                }
            }
            if let (
                Phase::TransitionReturned {
                    site,
                    port,
                    context,
                    ordinal,
                },
                control::CompletionTransition::Sequence { ordinal: 1 },
            ) = (phase, transition)
            {
                let candidate = *transitions.get(site).ok_or(Failure::Invalid)?;
                let original = focus.values().original_control_node(
                    before.position.code,
                    scope.nodes(),
                    work,
                )?;
                let Some(crate::core::EffectExprKind::Pure(
                    crate::core::PureExprKind::Computation(crate::core::PureComputation::Bind(
                        bind,
                    )),
                )) = scope.nodes().get(original).map(|node| &node.kind)
                else {
                    return Err(Failure::Invalid);
                };
                if bind.initializer() != candidate.call() {
                    // The returned value may flow through an enclosing match or
                    // expression. Without an exact direct binding, discard the
                    // current role; later nominated uses must establish it.
                    next = Phase::Invalidated;
                } else {
                    if before.position.next != 1 {
                        return Err(Failure::Invalid);
                    }
                    let body = bind
                        .body()
                        .index()
                        .map_err(|_| Failure::Invalid)?
                        .checked_add(1)
                        .ok_or(Failure::Resource)?;
                    let init = bind
                        .initializer()
                        .index()
                        .map_err(|_| Failure::Invalid)?
                        .checked_add(1)
                        .ok_or(Failure::Resource)?;
                    let Some(control::Control::Sequence(children)) =
                        graph.code.get(before.position.code)
                    else {
                        return Err(Failure::Invalid);
                    };
                    let after = trace.state(to, work)?;
                    if children.as_slice() != [init, body]
                        || before.value_context != context
                        || after.value_context != context
                        || after.position.code != body
                    {
                        return Err(Failure::Invalid);
                    }
                    let (binder, initializer) = focus.values().existing_binding_ports(
                        before.position.code,
                        context,
                        work,
                    )?;
                    if initializer != port {
                        return Err(Failure::Invalid);
                    }
                    let binding = crate::core::NodeId::new(
                        scope.arena(),
                        u32::try_from(original).map_err(|_| Failure::Resource)?,
                    );
                    charge(
                        work,
                        transition_bindings
                            .len()
                            .checked_add(1)
                            .ok_or(Failure::Resource)?,
                    )?;
                    let item = (site, binding, bind.binder().id());
                    if !transition_bindings.contains(&item) {
                        transition_bindings
                            .try_reserve(1)
                            .map_err(|_| Failure::Resource)?;
                        transition_bindings.push(item);
                    }
                    next = Phase::Current {
                        port: binder,
                        context,
                        ordinal,
                        role: bind.binder().id(),
                    };
                }
            }
            if let Phase::EnteringDriver { context, .. } = phase {
                if before.value_context != context
                    || !matches!(
                        graph.code.get(before.position.code),
                        Some(
                            control::Control::Sequence(_)
                                | control::Control::Choice(_)
                                | control::Control::Return
                        )
                    )
                    || matches!(
                        transition,
                        control::CompletionTransition::Call { .. }
                            | control::CompletionTransition::WorkerInputAllocation
                    )
                {
                    return Err(Failure::Invalid);
                }
            }
            if matches!(transition, control::CompletionTransition::Call { .. }) {
                if let Phase::PreparingArgument {
                    port,
                    context,
                    ordinal,
                    role,
                    constructor,
                } = phase
                {
                    let &(call_node, closure) = argument_constructors
                        .get(constructor)
                        .ok_or(Failure::Invalid)?;
                    if before.value_context != context
                        || !source_position(scope, focus, before, call_node, work)?
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
                        &body_calls,
                        &body_closures,
                        &helpers,
                        &closure_origins,
                        &query_origins,
                        work,
                    )?;
                    next = Phase::RunningArgument {
                        port,
                        context,
                        ordinal,
                        role,
                        constructor,
                        witness,
                    };
                } else if matches!(phase, Phase::RunningArgument { .. }) {
                    return Err(Failure::Invalid);
                } else if source_position(scope, focus, before, initialization.call(), work)? {
                    if phase != Phase::BeforeInitialization {
                        return Err(Failure::Invalid);
                    }
                    next = Phase::Initializing(entered_call(
                        graph,
                        focus,
                        from,
                        to,
                        transition,
                        initialization.closure(),
                        work,
                    )?);
                    let Phase::Initializing(witness) = next else {
                        return Err(Failure::Invalid);
                    };
                    let call = trace.call(witness, work)?;
                    checked_context_capture(
                        scope,
                        focus,
                        definitions[0],
                        call,
                        &query_origins,
                        work,
                    )?;
                } else {
                    let mut receive_site = None;
                    for (index, receive) in receives.iter().enumerate() {
                        charge(work, 1)?;
                        if source_position(scope, focus, before, receive.call(), work)? {
                            if receive_site.replace((index, receive)).is_some() {
                                return Err(Failure::Invalid);
                            }
                        }
                    }
                    if let Some((receive_index, receive)) = receive_site {
                        let Phase::Current {
                            port,
                            context,
                            ordinal,
                            role,
                        } = phase
                        else {
                            return Err(Failure::Invalid);
                        };
                        if before.value_context != context {
                            return Err(Failure::Invalid);
                        }
                        let body_index = receive
                            .definition_body()
                            .index()
                            .map_err(|_| Failure::Invalid)?;
                        let Some(crate::core::EffectExprKind::Pure(
                            crate::core::PureExprKind::Computation(
                                crate::core::PureComputation::Bind(bind),
                            ),
                        )) = scope.nodes().get(body_index).map(|node| &node.kind)
                        else {
                            return Err(Failure::Invalid);
                        };
                        if bind.body() != scope.receive() {
                            return Err(Failure::Invalid);
                        }
                        let witness = entered_call(
                            graph,
                            focus,
                            from,
                            to,
                            transition,
                            receive.closure(),
                            work,
                        )?;
                        let call = trace.call(witness, work)?;
                        checked_context_capture(
                            scope,
                            focus,
                            DefinitionProvenance {
                                query: receive.definition_query(),
                                binding: receive.definition_binding(),
                                context: receive.definition_context(),
                                closure: receive.closure(),
                            },
                            call,
                            &query_origins,
                            work,
                        )?;
                        let (_, _, pairs, captures) = focus.values().existing_call_ports(
                            call.code,
                            call.caller_value_context,
                            call.expression,
                            call.callee_value_context,
                            call.creation,
                            work,
                        )?;
                        if pairs.len() != 1 || pairs[0].1 == port {
                            return Err(Failure::Invalid);
                        }
                        focus.values().check_closed_global_capture_ports(
                            call.target,
                            call.creation,
                            call.callee_value_context,
                            &[],
                            receive.definition_context(),
                            receive.type_parameters(),
                            scope.arena(),
                            scope.nodes(),
                            &captures,
                            work,
                        )?;
                        requires_exclusive_update = true;
                        next = Phase::Receiving {
                            receive: receive_index,
                            witness,
                            port,
                            context,
                            ordinal,
                            role,
                            stage: ReceiveStage::Before,
                        };
                    } else {
                        let mut driver_site = None;
                        for (index, driver) in drivers.iter().enumerate() {
                            charge(work, 1)?;
                            if source_position(scope, focus, before, driver.call(), work)? {
                                if driver_site.replace((index, driver)).is_some() {
                                    return Err(Failure::Invalid);
                                }
                            }
                        }
                        if let Some((driver_index, driver)) = driver_site {
                            let (port, context, role, ordinal) = match phase {
                                Phase::Current {
                                    port,
                                    context,
                                    role,
                                    ordinal,
                                } => (port, context, role, ordinal),
                                Phase::Initialized { port, context } => {
                                    let binding = initial_binding.ok_or(Failure::Invalid)?;
                                    let Some(crate::core::EffectExprKind::Pure(
                                        crate::core::PureExprKind::Computation(
                                            crate::core::PureComputation::Bind(bind),
                                        ),
                                    )) = scope
                                        .nodes()
                                        .get(binding.index().map_err(|_| Failure::Invalid)?)
                                        .map(|node| &node.kind)
                                    else {
                                        return Err(Failure::Invalid);
                                    };
                                    let code = binding
                                        .index()
                                        .map_err(|_| Failure::Invalid)?
                                        .checked_add(1)
                                        .ok_or(Failure::Resource)?;
                                    let (binder, initializer) = focus
                                        .values()
                                        .existing_binding_ports(code, context, work)?;
                                    if initializer != port {
                                        return Err(Failure::Invalid);
                                    }
                                    (binder, context, bind.binder().id(), 0)
                                }
                                _ => return Err(Failure::Invalid),
                            };
                            let (witness, formal_port, context) = entered_driver(
                                scope,
                                graph,
                                focus,
                                from,
                                to,
                                transition,
                                driver,
                                role,
                                port,
                                context,
                                &query_origins,
                                work,
                            )?;
                            next = Phase::EnteringDriver {
                                driver: driver_index,
                                witness,
                                formal_port,
                                context,
                                ordinal,
                            };
                        } else {
                            let mut selected_site = None;
                            for (ordinal, &(site, _)) in registrations.iter().enumerate() {
                                charge(work, 1)?;
                                if source_position(scope, focus, before, site.call(), work)? {
                                    if selected_site.replace((ordinal, site)).is_some() {
                                        return Err(Failure::Invalid);
                                    }
                                }
                            }
                            if let Some((ordinal, selected)) = selected_site {
                                let (port, context, from_initial, current_role) = match phase {
                                    Phase::Initialized { port, context } => {
                                        (port, context, true, None)
                                    }
                                    Phase::Current {
                                        port,
                                        context,
                                        role,
                                        ..
                                    } => (port, context, false, Some(role)),
                                    _ => return Err(Failure::Invalid),
                                };
                                let input =
                                    selected.input().index().map_err(|_| Failure::Invalid)?;
                                // An abstract value port can summarize more than one dynamic
                                // value. Require the actual source binder to be the previous
                                // checked successor; port equality alone is not currentness.
                                if let Some(expected_role) = current_role {
                                    let Some(crate::core::EffectExprKind::Pure(
                                        crate::core::PureExprKind::Variable(variable),
                                    )) = scope.nodes().get(input).map(|node| &node.kind)
                                    else {
                                        return Err(Failure::Invalid);
                                    };
                                    if variable.binder() != expected_role {
                                        return Err(Failure::Invalid);
                                    }
                                }
                                let code = input.checked_add(1).ok_or(Failure::Resource)?;
                                if before.value_context != context
                                    || focus.values().original_control_node(
                                        code,
                                        scope.nodes(),
                                        work,
                                    )? != input
                                {
                                    return Err(Failure::Invalid);
                                }
                                if from_initial && initial_binding.is_none() {
                                    if focus.values().existing_port(code, context, work)? != port {
                                        return Err(Failure::Invalid);
                                    }
                                } else {
                                    let (_, source) = focus
                                        .values()
                                        .existing_forward_ports(code, context, work)?;
                                    let expected = if from_initial {
                                        let binding = initial_binding.ok_or(Failure::Invalid)?;
                                        let binding_code = binding
                                            .index()
                                            .map_err(|_| Failure::Invalid)?
                                            .checked_add(1)
                                            .ok_or(Failure::Resource)?;
                                        let (binder, initialized) = focus
                                            .values()
                                            .existing_binding_ports(binding_code, context, work)?;
                                        if initialized != port {
                                            return Err(Failure::Invalid);
                                        }
                                        binder
                                    } else {
                                        port
                                    };
                                    if source != expected {
                                        return Err(Failure::Invalid);
                                    }
                                }
                                let witness = entered_call(
                                    graph,
                                    focus,
                                    from,
                                    to,
                                    transition,
                                    selected.closure(),
                                    work,
                                )?;
                                next = Phase::Registering {
                                    witness,
                                    input: port,
                                    ordinal,
                                };
                                checked_context_capture(
                                    scope,
                                    focus,
                                    definitions[1],
                                    trace.call(witness, work)?,
                                    &query_origins,
                                    work,
                                )?;
                            } else {
                                let mut selected = None;
                                for (site, &candidate) in transitions.iter().enumerate() {
                                    charge(work, 1)?;
                                    if source_position(
                                        scope,
                                        focus,
                                        before,
                                        candidate.call(),
                                        work,
                                    )? {
                                        if selected.replace((site, candidate)).is_some() {
                                            return Err(Failure::Invalid);
                                        }
                                    }
                                }
                                if let Some((site, candidate)) = selected {
                                    let Phase::Current {
                                        port,
                                        context,
                                        ordinal,
                                        role,
                                    } = phase
                                    else {
                                        return Err(Failure::Invalid);
                                    };
                                    let input =
                                        candidate.input().index().map_err(|_| Failure::Invalid)?;
                                    let Some(crate::core::EffectExprKind::Pure(
                                        crate::core::PureExprKind::Variable(variable),
                                    )) = scope.nodes().get(input).map(|node| &node.kind)
                                    else {
                                        return Err(Failure::Invalid);
                                    };
                                    if variable.binder() != role || before.value_context != context
                                    {
                                        return Err(Failure::Invalid);
                                    }
                                    let code = input.checked_add(1).ok_or(Failure::Resource)?;
                                    let (_, source) = focus
                                        .values()
                                        .existing_forward_ports(code, context, work)?;
                                    if source != port {
                                        return Err(Failure::Invalid);
                                    }
                                    let witness = entered_call(
                                        graph,
                                        focus,
                                        from,
                                        to,
                                        transition,
                                        candidate.closure(),
                                        work,
                                    )?;
                                    checked_context_capture(
                                        scope,
                                        focus,
                                        candidate.definition(),
                                        trace.call(witness, work)?,
                                        &query_origins,
                                        work,
                                    )?;
                                    if matches!(
                                        candidate,
                                        transition_observation::TransitionCall::Acknowledgement(_)
                                    ) {
                                        requires_peer_authentication = true;
                                    }
                                    next = Phase::Transitioning {
                                        site,
                                        witness,
                                        input: port,
                                        context,
                                        ordinal,
                                    };
                                } else if matches!(
                                    phase,
                                    Phase::Initialized { .. }
                                        | Phase::Returned { .. }
                                        | Phase::Current { .. }
                                        | Phase::TransitionReturned { .. }
                                ) {
                                    next = Phase::Invalidated;
                                }
                            }
                        }
                    }
                }
            }
            if let control::CompletionTransition::Detail(detail) = transition {
                let returned = match details.get(&detail) {
                    Some(control::CompletionDetail::Return(edge)) => Some((*edge, false)),
                    Some(control::CompletionDetail::NativeReturn {
                        boundary: None,
                        edge: Some(edge),
                        ..
                    }) if body_region => Some((*edge, true)),
                    _ => None,
                };
                if let Some((edge, native_return)) = returned {
                    if let control::Frame::CallReturn { witness, .. } = edge.frame {
                        // A receive Reply can restore its caller on this same
                        // edge. Use the checked event's updated stage for that
                        // one case; all other returns inspect the incoming phase.
                        let return_phase = if matches!(
                            next,
                            Phase::Receiving {
                                stage: ReceiveStage::Replied,
                                ..
                            }
                        ) {
                            next
                        } else {
                            phase
                        };
                        match return_phase {
                            Phase::Transitioning {
                                site,
                                witness: expected,
                                input,
                                context,
                                ordinal,
                            } if witness == expected => {
                                let candidate = *transitions.get(site).ok_or(Failure::Invalid)?;
                                let call = matched_source_return(
                                    scope,
                                    focus,
                                    &index,
                                    from,
                                    to,
                                    edge,
                                    native_return,
                                    candidate.call(),
                                    candidate.closure(),
                                    work,
                                )?
                                .ok_or(Failure::Invalid)?;
                                if call.caller_value_context != context {
                                    return Err(Failure::Invalid);
                                }
                                charge(work, 1)?;
                                transition_returns
                                    .try_reserve(1)
                                    .map_err(|_| Failure::Resource)?;
                                transition_returns.push((site, from, to, input, call.result));
                                next = Phase::TransitionReturned {
                                    site,
                                    port: call.result,
                                    context,
                                    ordinal,
                                };
                            }
                            Phase::Receiving {
                                receive,
                                witness: expected,
                                port,
                                context,
                                ordinal,
                                role,
                                stage: ReceiveStage::Replied,
                            } if witness == expected => {
                                let nominated = receives.get(receive).ok_or(Failure::Invalid)?;
                                let call = matched_source_return(
                                    scope,
                                    focus,
                                    &index,
                                    from,
                                    to,
                                    edge,
                                    native_return,
                                    nominated.call(),
                                    nominated.closure(),
                                    work,
                                )?
                                .ok_or(Failure::Invalid)?;
                                if call.caller_value_context != context {
                                    return Err(Failure::Invalid);
                                }
                                next = Phase::Current {
                                    port,
                                    context,
                                    ordinal,
                                    role,
                                };
                            }
                            Phase::RunningArgument {
                                port,
                                context,
                                ordinal,
                                role,
                                constructor,
                                witness: expected,
                            } if witness == expected => {
                                let &(call_node, closure) = argument_constructors
                                    .get(constructor)
                                    .ok_or(Failure::Invalid)?;
                                let call = matched_source_return(
                                    scope,
                                    focus,
                                    &index,
                                    from,
                                    to,
                                    edge,
                                    native_return,
                                    call_node,
                                    closure,
                                    work,
                                )?
                                .ok_or(Failure::Invalid)?;
                                if call.caller_value_context != context {
                                    return Err(Failure::Invalid);
                                }
                                next = Phase::Current {
                                    port,
                                    context,
                                    ordinal,
                                    role,
                                };
                            }
                            Phase::Initializing(expected) if witness == expected => {
                                let call = matched_source_return(
                                    scope,
                                    focus,
                                    &index,
                                    from,
                                    to,
                                    edge,
                                    native_return,
                                    initialization.call(),
                                    initialization.closure(),
                                    work,
                                )?
                                .ok_or(Failure::Invalid)?;
                                next = Phase::Initialized {
                                    port: call.result,
                                    context: call.caller_value_context,
                                };
                            }
                            Phase::Registering {
                                witness: expected,
                                input,
                                ordinal,
                            } if witness == expected => {
                                let selected =
                                    registrations.get(ordinal).ok_or(Failure::Invalid)?.0;
                                let call = matched_source_return(
                                    scope,
                                    focus,
                                    &index,
                                    from,
                                    to,
                                    edge,
                                    native_return,
                                    selected.call(),
                                    selected.closure(),
                                    work,
                                )?
                                .ok_or(Failure::Invalid)?;
                                next = Phase::Returned {
                                    port: call.result,
                                    context: call.caller_value_context,
                                    input,
                                    ordinal,
                                };
                            }
                            _ => {}
                        }
                    }
                }
            }
            if let control::CompletionTransition::Choice { ordinal } = transition {
                if let Phase::EnteringDriver {
                    driver,
                    witness: _,
                    formal_port,
                    context,
                    ordinal: last,
                } = phase
                {
                    if before.value_context != context {
                        return Err(Failure::Invalid);
                    }
                    let plan = drivers.get(driver).ok_or(Failure::Invalid)?;
                    let port = driver_formal_projection(
                        scope,
                        focus,
                        before,
                        ordinal,
                        plan,
                        formal_port,
                        work,
                    )?
                    .ok_or(Failure::Invalid)?;
                    next = Phase::Current {
                        port,
                        context,
                        ordinal: last,
                        role: plan.formal(),
                    };
                }
                let mut matching_site = None;
                for (index, &(_, result)) in registrations.iter().enumerate() {
                    charge(work, 1)?;
                    if source_position(scope, focus, before, result.matching, work)? {
                        if matching_site.replace(index).is_some() {
                            return Err(Failure::Invalid);
                        }
                    }
                }
                if let Some(matching_site) = matching_site {
                    let Phase::Returned {
                        port,
                        context,
                        input,
                        ordinal: call_ordinal,
                    } = phase
                    else {
                        return Err(Failure::Invalid);
                    };
                    if before.value_context != context || matching_site != call_ordinal {
                        return Err(Failure::Invalid);
                    }
                    let selected_result =
                        registrations.get(call_ordinal).ok_or(Failure::Invalid)?.1;
                    let (ledger, status) = returned_ledger_port(
                        scope,
                        focus,
                        before,
                        ordinal,
                        selected_result,
                        port,
                        work,
                    )?
                    .ok_or(Failure::Invalid)?;
                    next = Phase::Projected {
                        ledger,
                        status,
                        input,
                        context,
                        ordinal: call_ordinal,
                    };
                }
            }
            charge(work, 1)?;
            pending.try_reserve(1).map_err(|_| Failure::Resource)?;
            pending.push_back((to, next));
        }
    }
    charge(
        work,
        seen.capacity()
            .checked_add(pending.capacity())
            .ok_or(Failure::Resource)?,
    )?;
    if projected.is_empty() {
        return Err(Failure::Invalid);
    }
    // Publish a point only when every reached predecessor carries the same
    // current port and context. An unknown or stale path therefore removes
    // that point from the provisional result rather than joining by union.
    charge(work, seen.capacity())?;
    for (state, phase) in &seen {
        if let Some(&(port, context, role)) = current.get(state) {
            let agrees = match *phase {
                Phase::Current {
                    port: actual,
                    context: actual_context,
                    role: actual_role,
                    ..
                } => (actual, actual_context, actual_role) == (port, context, role),
                Phase::Projected {
                    ledger: actual,
                    context: actual_context,
                    ordinal,
                    ..
                } => {
                    (actual, actual_context) == (port, context)
                        && registrations
                            .get(ordinal)
                            .is_some_and(|(_, result)| result.ledger == role)
                }
                _ => false,
            };
            if !agrees {
                return Err(Failure::Invalid);
            }
        }
    }
    // Each nominated call must be observed; an unreachable or omitted site
    // cannot silently become part of a published plan.
    for ordinal in 0..registrations.len() {
        charge(work, projected.len())?;
        if !projected.values().any(|entry| entry.4 == ordinal) {
            return Err(Failure::Invalid);
        }
    }
    for site in 0..transitions.len() {
        charge(work, transition_returns.len())?;
        if !transition_returns.iter().any(|entry| entry.0 == site) {
            return Err(Failure::Invalid);
        }
    }
    charge(
        work,
        projected
            .capacity()
            .checked_add(current.capacity())
            .ok_or(Failure::Resource)?,
    )?;
    let mut result = Vec::new();
    result
        .try_reserve_exact(projected.len())
        .map_err(|_| Failure::Resource)?;
    result.extend(
        projected
            .into_iter()
            .map(|(state, (ledger, status, input, _, _))| (state, input, ledger, status)),
    );
    let mut current_points = Vec::new();
    current_points
        .try_reserve_exact(current.len())
        .map_err(|_| Failure::Resource)?;
    current_points.extend(
        current
            .into_iter()
            .map(|(state, (port, context, role))| (state, port, context, role)),
    );
    let mut transition_calls = Vec::new();
    charge(work, transitions.len())?;
    transition_calls
        .try_reserve_exact(transitions.len())
        .map_err(|_| Failure::Resource)?;
    transition_calls.extend(transitions.iter().map(|call| (call.call(), call.closure())));
    Ok(ProvisionalCurrentLedger {
        _focus: focus,
        _initialization: initialization,
        _registrations: registrations,
        owner: scope.owner(),
        side,
        requires_exclusive_update,
        requires_peer_authentication,
        _transition_returns: transition_returns,
        transition_bindings,
        transitions: result,
        current: current_points,
        transition_calls,
        argument_constructors,
        checked_nodes,
        body_calls,
        body_closures,
        helpers,
        closure_origins,
        query_origins,
        verified_query_requests,
        verified_query_resumes,
        query_caller_contexts,
    })
}

/// Reconstructed source-step coordinates for revalidation in the same worker
/// focus. These do not assert that the step is current on every path and do
/// not retain the temporary graph's state or port identifiers.
#[allow(dead_code)]
pub(in crate::core) struct PendingLedgerStep {
    pub(in crate::core) call: crate::core::NodeId,
    pub(in crate::core) target: crate::core::NodeId,
    pub(in crate::core) input: crate::core::NodeId,
    pub(in crate::core) successor_site: crate::core::NodeId,
    pub(in crate::core) successor: crate::resolved::BinderId,
}

/// A private observation owned by the complete validator query. Its source
/// coordinates require revalidation in a live focus; it conveys no peer,
/// completion, release, or unqualified ledger authority.
#[allow(dead_code)]
pub(in crate::core) struct PendingLedgerObservation {
    pub(in crate::core) owner: crate::core::NodeId,
    pub(in crate::core) entry: crate::core::NodeId,
    pub(in crate::core) side: u8,
    pub(in crate::core) initialization: crate::core::NodeId,
    pub(in crate::core) initialization_target: crate::core::NodeId,
    pub(in crate::core) initialization_role: crate::core::ledger_checker::InitializationRole,
    pub(in crate::core) allocator: crate::core::NodeId,
    pub(in crate::core) steps: Vec<PendingLedgerStep>,
    pub(in crate::core) current_sites: Vec<(crate::core::NodeId, crate::resolved::BinderId)>,
    pub(in crate::core) requires_history_and_peer_allocator: bool,
    pub(in crate::core) requires_exclusive_update: bool,
    pub(in crate::core) requires_peer_authentication: bool,
}

/// A live, conditional query over the exact worker focus that reconstructed a
/// plan. It cannot be retained as a currentness or network permission. The
/// caller must separately authenticate its selected operation and keep any
/// candidate private until complete validation succeeds.
#[allow(dead_code)]
pub(super) struct SameFocusLedger<'a> {
    scope: &'a NetworkNativeIdentityScope<'a>,
    focus: &'a control::CompletionFocus<'a>,
    entry: crate::core::NodeId,
    side: u8,
    current: &'a [(usize, usize, usize, crate::resolved::BinderId)],
    requires_exclusive_update: bool,
    requires_peer_authentication: bool,
}

/// A successful check remains conditional on history, peer identity and the
/// explicitly recorded receive/exclusive-update premises. It borrows the same
/// focus, so it cannot outlive the worker query.
#[allow(dead_code)]
pub(super) struct CheckedCurrentLedgerInput<'a> {
    _focus: &'a control::CompletionFocus<'a>,
    pub(super) owner: crate::core::NodeId,
    pub(super) entry: crate::core::NodeId,
    pub(super) side: u8,
    pub(super) site: crate::core::NodeId,
    pub(super) input: crate::core::NodeId,
    pub(super) role: crate::resolved::BinderId,
    pub(super) requires_history_and_peer_allocator: bool,
    pub(super) requires_exclusive_update: bool,
    pub(super) requires_peer_authentication: bool,
}

impl<'a> SameFocusLedger<'a> {
    /// Check a selected source input at one reached state in this exact focus.
    /// The consumer must independently bind that input to its nominated call
    /// or field; this checks only the actual variable-to-current-port relation.
    pub(super) fn checked_input(
        &self,
        state: usize,
        site: crate::core::NodeId,
        input: crate::core::NodeId,
        role: crate::resolved::BinderId,
        work: &mut TypeWorkBudget,
    ) -> Result<Option<CheckedCurrentLedgerInput<'_>>, Failure> {
        if site.arena() != self.scope.arena() || input.arena() != self.scope.arena() {
            return Err(Failure::Invalid);
        }
        charge(work, self.current.len())?;
        let mut matches = self.current.iter().filter(|(id, _, _, _)| *id == state);
        let Some(&(_, port, context, actual_role)) = matches.next() else {
            return Ok(None);
        };
        if matches.next().is_some() || actual_role != role {
            return Ok(None);
        }
        let before = self.focus.trace()?.state(state, work)?;
        if before.value_context != context
            || !source_position(self.scope, self.focus, before, site, work)?
        {
            return Ok(None);
        }
        let index = input.index().map_err(|_| Failure::Invalid)?;
        let Some(crate::core::EffectExprKind::Pure(crate::core::PureExprKind::Variable(variable))) =
            self.scope.nodes().get(index).map(|node| &node.kind)
        else {
            return Ok(None);
        };
        if variable.binder() != role {
            return Ok(None);
        }
        let code = index.checked_add(1).ok_or(Failure::Resource)?;
        let (_, source) = self
            .focus
            .values()
            .existing_forward_ports(code, context, work)?;
        if source != port {
            return Ok(None);
        }
        Ok(Some(CheckedCurrentLedgerInput {
            _focus: self.focus,
            owner: self.scope.owner(),
            entry: self.entry,
            side: self.side,
            site,
            input,
            role,
            requires_history_and_peer_allocator: true,
            requires_exclusive_update: self.requires_exclusive_update,
            requires_peer_authentication: self.requires_peer_authentication,
        }))
    }
}

enum CheckedPlannedTransition<'a> {
    Closure(crate::core::ledger_checker::closure::ConditionalClosureCall<'a>),
    Retirement(crate::core::ledger_checker::retirement::ConditionalRetirementCall<'a>),
    Acknowledgement(
        crate::core::ledger_checker::acknowledgement::ConditionalAcknowledgementCall<'a>,
    ),
}
impl CheckedPlannedTransition<'_> {
    fn as_call(&self) -> transition_observation::TransitionCall<'_, '_> {
        match self {
            Self::Closure(call) => transition_observation::TransitionCall::Closure(call),
            Self::Retirement(call) => transition_observation::TransitionCall::Retirement(call),
            Self::Acknowledgement(call) => {
                transition_observation::TransitionCall::Acknowledgement(call)
            }
        }
    }
}

fn plan_rejection(error: crate::core::ledger_checker::Rejection) -> Failure {
    match error {
        crate::core::ledger_checker::Rejection::Unsupported => Failure::Invalid,
        crate::core::ledger_checker::Rejection::Exhausted => Failure::Resource,
    }
}

/// Reconstruct nominated source coordinates, then consume them against the
/// same worker focus and cumulative work budget as the owning validator.
pub(super) fn observe_ledger_plan(
    scope: &NetworkNativeIdentityScope<'_>,
    graph: &SummaryGraph,
    worker: &control::Analysis<'_>,
    program: &crate::core::UnvalidatedEffectProgram,
    linked: &crate::evidence_validation::ValidatedInterfaceProgram,
    plan: &crate::core::ledger_checker::plan::LedgerPlan<'_>,
    work: &mut TypeWorkBudget,
) -> Result<PendingLedgerObservation, Failure> {
    with_observed_ledger_plan(scope, graph, worker, program, linked, plan, work, |_, _| {
        Ok(())
    })
    .map(|(pending, ())| pending)
}

/// Inspect exact current inputs inside the worker focus. Callback results are
/// provisional and must be dropped if any subsequent validator step fails.
#[allow(dead_code)]
#[expect(
    clippy::too_many_arguments,
    reason = "the linked source, plan, worker focus and consumer are distinct inputs"
)]
pub(super) fn with_observed_ledger_plan<R>(
    scope: &NetworkNativeIdentityScope<'_>,
    graph: &SummaryGraph,
    worker: &control::Analysis<'_>,
    program: &crate::core::UnvalidatedEffectProgram,
    linked: &crate::evidence_validation::ValidatedInterfaceProgram,
    plan: &crate::core::ledger_checker::plan::LedgerPlan<'_>,
    work: &mut TypeWorkBudget,
    inspect: impl FnOnce(&SameFocusLedger<'_>, &mut TypeWorkBudget) -> Result<R, Failure>,
) -> Result<(PendingLedgerObservation, R), Failure> {
    use crate::core::ledger_checker::plan::TransitionNomination;
    use crate::core::ledger_checker::{
        check_nominated_initialization_call, check_nominated_registration_call,
        check_registration_result_match, checked_entry_default_handler,
    };
    if plan.owner != scope.owner() || plan.side > 1 || plan.registrations.is_empty() {
        return Err(Failure::Invalid);
    }
    let entry = scope
        .entry(usize::from(plan.side))
        .ok_or(Failure::Invalid)?
        .0;
    let initialization = check_nominated_initialization_call(
        program,
        linked,
        plan.initialization_call,
        plan.initialization,
        plan.initialization_constructors,
        plan.initialization_role,
        work,
    )
    .map_err(plan_rejection)?;
    let mut registrations = Vec::new();
    let mut results = Vec::new();
    charge(work, plan.registrations.len())?;
    registrations
        .try_reserve_exact(plan.registrations.len())
        .map_err(|_| Failure::Resource)?;
    results
        .try_reserve_exact(plan.registrations.len())
        .map_err(|_| Failure::Resource)?;
    for item in plan.registrations {
        let checked = check_nominated_registration_call(
            program,
            linked,
            item.call,
            item.definitions,
            item.constructors,
            work,
        )
        .map_err(plan_rejection)?;
        let result = check_registration_result_match(program, &checked, item.result_match, work)
            .map_err(plan_rejection)?;
        registrations.push(checked);
        results.push(result);
    }
    // The modeled issued history has one fixed allocator per worker. For
    // this fragment every nominated call must use the same actual nonnegative
    // integer literal. Forwarded or computed labels remain unsupported.
    let mut fixed_allocator = None;
    let mut fixed_value = None;
    for registration in &registrations {
        let node = registration.allocator();
        if node.arena() != scope.arena() {
            return Err(Failure::Invalid);
        }
        let Some(crate::core::EffectExprKind::Pure(crate::core::PureExprKind::Value(
            crate::core::PureValue::Integer(integer),
        ))) = scope
            .nodes()
            .get(node.index().map_err(|_| Failure::Invalid)?)
            .map(|item| &item.kind)
        else {
            return Err(Failure::Invalid);
        };
        let bytes = usize::try_from(integer.value().magnitude_byte_length())
            .map_err(|_| Failure::Resource)?;
        charge(
            work,
            bytes
                .checked_mul(2)
                .and_then(|n| n.checked_add(1))
                .ok_or(Failure::Resource)?,
        )?;
        if integer.value().sign_magnitude().0 {
            return Err(Failure::Invalid);
        }
        if let Some(value) = fixed_value {
            if value != integer.value() {
                return Err(Failure::Invalid);
            }
        } else {
            fixed_allocator = Some(node);
            fixed_value = Some(integer.value());
        }
    }
    let fixed_allocator = fixed_allocator.ok_or(Failure::Invalid)?;
    let mut registration_refs = Vec::new();
    charge(work, registrations.len())?;
    registration_refs
        .try_reserve_exact(registrations.len())
        .map_err(|_| Failure::Resource)?;
    registration_refs.extend(registrations.iter().zip(&results));
    let mut transitions = Vec::new();
    charge(work, plan.transitions.len())?;
    transitions
        .try_reserve_exact(plan.transitions.len())
        .map_err(|_| Failure::Resource)?;
    for item in plan.transitions {
        let checked = match item {
            TransitionNomination::Closure {
                call,
                definitions,
                constructors,
            } => CheckedPlannedTransition::Closure(
                crate::core::ledger_checker::closure::check_nominated_closure_call(
                    program,
                    linked,
                    *call,
                    *definitions,
                    *constructors,
                    work,
                )
                .map_err(plan_rejection)?,
            ),
            TransitionNomination::Retirement {
                call,
                definitions,
                constructors,
            } => CheckedPlannedTransition::Retirement(
                crate::core::ledger_checker::retirement::check_nominated_retirement_call(
                    program,
                    linked,
                    *call,
                    *definitions,
                    *constructors,
                    work,
                )
                .map_err(plan_rejection)?,
            ),
            TransitionNomination::Acknowledgement {
                call,
                definitions,
                constructors,
            } => CheckedPlannedTransition::Acknowledgement(
                crate::core::ledger_checker::acknowledgement::check_nominated_acknowledgement_call(
                    program,
                    linked,
                    *call,
                    *definitions,
                    *constructors,
                    work,
                )
                .map_err(plan_rejection)?,
            ),
        };
        transitions.push(checked);
    }
    let mut transition_refs = Vec::new();
    charge(work, transitions.len())?;
    transition_refs
        .try_reserve_exact(transitions.len())
        .map_err(|_| Failure::Resource)?;
    transition_refs.extend(transitions.iter().map(CheckedPlannedTransition::as_call));
    let mut drivers = Vec::new();
    charge(work, plan.drivers.len())?;
    drivers
        .try_reserve_exact(plan.drivers.len())
        .map_err(|_| Failure::Resource)?;
    for item in plan.drivers {
        drivers.push(
            crate::core::ledger_checker::driver::check_nominated_driver_call(
                program, linked, item, work,
            )
            .map_err(plan_rejection)?,
        );
    }
    let mut receives = Vec::new();
    charge(work, plan.receives.len())?;
    receives
        .try_reserve_exact(plan.receives.len())
        .map_err(|_| Failure::Resource)?;
    for item in plan.receives {
        receives.push(
            crate::core::ledger_checker::driver::check_nominated_receive_call(
                program, linked, item, work,
            )
            .map_err(plan_rejection)?,
        );
    }
    let default_handler = checked_entry_default_handler(program, work).map_err(plan_rejection)?;
    let focus = worker.completion_foci.last().ok_or(Failure::Invalid)?;
    let observed = observe_direct_registration(
        scope,
        graph,
        focus,
        &initialization,
        &registration_refs,
        &drivers,
        &receives,
        plan.initialization_binding,
        &transition_refs,
        default_handler,
        plan.side,
        work,
    )?;
    if observed.current.is_empty() || observed.transitions.is_empty() {
        return Err(Failure::Invalid);
    }
    let checked = inspect(
        &SameFocusLedger {
            scope,
            focus,
            entry,
            side: plan.side,
            current: &observed.current,
            requires_exclusive_update: observed.requires_exclusive_update,
            requires_peer_authentication: observed.requires_peer_authentication,
        },
        work,
    )?;
    let step_count = registration_refs
        .len()
        .checked_add(observed.transition_bindings.len())
        .ok_or(Failure::Resource)?;
    charge(work, step_count)?;
    let mut steps = Vec::new();
    steps
        .try_reserve_exact(step_count)
        .map_err(|_| Failure::Resource)?;
    for &(call, result) in &registration_refs {
        steps.push(PendingLedgerStep {
            call: call.call(),
            target: call.closure(),
            input: call.input(),
            successor_site: result.matching,
            successor: result.ledger,
        });
    }
    for &(site, binding, successor) in &observed.transition_bindings {
        let call = *transition_refs.get(site).ok_or(Failure::Invalid)?;
        steps.push(PendingLedgerStep {
            call: call.call(),
            target: call.closure(),
            input: call.input(),
            successor_site: binding,
            successor,
        });
    }
    // The coordinate is only a request to revalidate: different dynamic
    // contexts can reach the same source node with different current values.
    charge(work, observed.current.len())?;
    let mut current_sites = Vec::new();
    current_sites
        .try_reserve_exact(observed.current.len())
        .map_err(|_| Failure::Resource)?;
    for &(state, _, _, role) in &observed.current {
        let state = focus.trace()?.state(state, work)?;
        let original =
            match focus
                .values()
                .original_control_node(state.position.code, scope.nodes(), work)
            {
                Ok(original) => original,
                Err(Failure::Invalid) => continue,
                Err(error) => return Err(error),
            };
        current_sites.push((
            crate::core::NodeId::new(
                scope.arena(),
                u32::try_from(original).map_err(|_| Failure::Resource)?,
            ),
            role,
        ));
    }
    if current_sites.is_empty() {
        return Err(Failure::Invalid);
    }
    Ok((
        PendingLedgerObservation {
            owner: plan.owner,
            entry,
            side: plan.side,
            initialization: initialization.call(),
            initialization_target: initialization.closure(),
            initialization_role: plan.initialization_role,
            allocator: fixed_allocator,
            steps,
            current_sites,
            // Distinctness against the peer and history simulation are separate.
            requires_history_and_peer_allocator: true,
            requires_exclusive_update: observed.requires_exclusive_update,
            requires_peer_authentication: observed.requires_peer_authentication,
        },
        checked,
    ))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::core::ledger_checker::{
        DefinitionCandidate, InitializationConstructors, InitializationRole,
        RegistrationConstructors, RegistrationDefinitions, check_nominated_initialization_call,
        check_nominated_registration_call, check_registration_result_match,
        checked_entry_default_handler,
    };
    use crate::core::{EffectExprKind, EffectOperation, NodeId, PureComputation, PureExprKind};
    use crate::resolved::ResolvedDefinitionKind;

    #[test]
    fn actual_worker_initialization_registration_result_stays_focus_local() {
        let source = include_str!("../../../tests/fixtures/n3-ledger-worker.ash");
        run_worker_case(source, true, false, None, None);
        let unknown = source
            .replace(
                "initial (), 0, LedgerTypes.Root, 0, payload",
                "initial (), unknown_int (), LedgerTypes.Root, 0, payload",
            )
            .replace(
                "main : Unit -> Unit",
                "unknown_int : Unit -> Int\nunknown_int () = 0\n\nmain : Unit -> Unit",
            );
        assert_ne!(unknown, source);
        run_worker_case(&unknown, false, false, None, None);
        // The extra call runs after the outer initializer has returned and
        // re-enters the actual registration definition with a different
        // ledger before the nominated outer call can consume its input.
        let reentry = source
            .replace(
                "initial (), 0, LedgerTypes.Root, 0, payload",
                "initial (), reenter_int (), LedgerTypes.Root, 0, payload",
            )
            .replace(
                "main : Unit -> Unit",
                "reenter_int : Unit -> Int\nreenter_int () = match reserve_job (initial (), 0, LedgerTypes.Root, 0, ByteOps.empty ()) {\n    (successor, status) => 0\n}\n\nmain : Unit -> Unit",
            );
        assert_ne!(reentry, source);
        run_worker_case(&reentry, false, false, None, None);
    }

    #[test]
    fn current_successor_is_accepted_and_original_alias_is_stale() {
        let source = include_str!("../../../tests/fixtures/n3-ledger-worker.ash");
        let two_calls = source.replace(
            "    let ignored = match reserve_job (initial (), 0, LedgerTypes.Root, 0, payload) {\n        (successor, status) => successor\n    }",
            "    let original = initial ()\n    let ignored = match reserve_job (original, 0, LedgerTypes.Root, 0, payload) {\n        (successor, status) => match reserve_job (successor, 0, LedgerTypes.Root, 0, payload) {\n            (final_ledger, final_status) => final_ledger\n        }\n    }",
        );
        assert_ne!(two_calls, source);
        run_worker_case(&two_calls, true, true, None, None);
        let stale = two_calls.replace(
            "reserve_job (successor, 0, LedgerTypes.Root, 0, payload)",
            "reserve_job (original, 0, LedgerTypes.Root, 0, payload)",
        );
        assert_ne!(stale, two_calls);
        run_worker_case(&stale, false, true, None, None);
    }

    #[test]
    fn canonical_receive_preserves_current_successor_under_exclusive_update() {
        let source = include_str!("../../../tests/fixtures/n3-ledger-worker.ash");
        let source = source.replace("    let received = Network.try_receive endpoint\n", "").replace(
            "    let ignored = match reserve_job (initial (), 0, LedgerTypes.Root, 0, payload) {\n        (successor, status) => successor\n    }",
            "    let original = initial ()\n    let ignored = match reserve_job (original, 0, LedgerTypes.Root, 0, payload) {\n        (successor, status) => {\n            let received = Network.try_receive endpoint\n            match reserve_job (successor, 0, LedgerTypes.Root, 0, payload) {\n                (final_ledger, final_status) => final_ledger\n            }\n        }\n    }",
        );
        assert!(source.contains("            let received = Network.try_receive endpoint"));
        let completed = completed_worker(&source);
        run_worker_case(&completed, true, true, None, Some(true));
        let changed_allocator = completed.replace(
            "reserve_job (successor, 0, LedgerTypes.Root, 0, payload)",
            "reserve_job (successor, 1, LedgerTypes.Root, 0, payload)",
        );
        assert_ne!(changed_allocator, completed);
        run_worker_case(&changed_allocator, true, true, None, Some(false));
        let stale = source.replace(
            "reserve_job (successor, 0, LedgerTypes.Root, 0, payload)",
            "reserve_job (original, 0, LedgerTypes.Root, 0, payload)",
        );
        assert_ne!(stale, source);
        run_worker_case(&stale, false, true, None, None);
    }

    #[test]
    fn recursive_driver_uses_returned_successor_on_backedge() {
        let source = include_str!("../../../tests/fixtures/n3-ledger-recursive-worker.ash");
        run_worker_case(source, true, false, None, None);
        let completed = source
            .replace(
                "driver<N> : (Network.Worker<N>, Ledger) -> Unit ! {Network.IO<N>}",
                "driver<N> : (Network.Worker<N>, Ledger) -> Bool ! {Network.IO<N>}",
            )
            .replace("    Network.Message(Network.Control, _) => ()", "    Network.Message(Network.Control, _) => false")
            .replace("    Network.End => ()", "    Network.End => true")
            .replace("    Network.ReceiveFailed(_) => ()", "    Network.ReceiveFailed(_) => false")
            .replace(
                "    let ledger = initial ()\n    driver (endpoint, ledger)",
                "    let _ = Network.finish_send endpoint\n    let ledger = initial ()\n    match driver (endpoint, ledger) {\n        true => {\n            let _ = Network.finish_receive endpoint\n            ()\n        }\n        false => ()\n    }",
            );
        assert_ne!(completed, source);
        assert!(completed.contains("Network.End => true"));
        run_worker_case(&completed, true, false, None, Some(true));
        let stale = source.replace("driver (endpoint, successor)", "driver (endpoint, ledger)");
        assert_ne!(stale, source);
        run_worker_case(&stale, false, false, None, None);
    }

    #[test]
    fn retirement_successor_is_acknowledgement_input_and_old_alias_is_stale() {
        let source = include_str!("../../../tests/fixtures/n3-ledger-transitions.ash");
        run_worker_case(source, true, false, Some(true), None);
        let completed = completed_worker(source);
        run_worker_case(&completed, true, false, Some(true), Some(true));
        let stale = source.replace(
            "acknowledge (retired, LedgerTypes.Root, LedgerTypes.Work(0, 0), 0)",
            "acknowledge (successor, LedgerTypes.Root, LedgerTypes.Work(0, 0), 0)",
        );
        assert_ne!(stale, source);
        // The joint worklist rejects the stale acknowledgement input before
        // producing any transition observation.
        run_worker_case(&stale, false, false, Some(false), None);
    }

    #[test]
    fn requested_ledger_plan_runs_inside_full_linked_validation() {
        let source = include_str!("../../../tests/fixtures/n3-ledger-worker.ash");
        // The ordinary N2 completion gate must still reject the original worker,
        // which never observes End or completes either polarity.
        run_worker_case(source, true, false, None, Some(false));
        let completed = completed_worker(source);
        run_worker_case(&completed, true, false, None, Some(true));
        let renamed = completed.replace("successor", "renamed_successor");
        assert_ne!(renamed, completed);
        run_worker_case(&renamed, true, false, None, Some(true));
    }

    #[test]
    fn both_workers_use_distinct_fixed_allocator_labels() {
        let source = completed_worker(include_str!("../../../tests/fixtures/n3-ledger-worker.ash"));
        let source = source.replace(
            "(1, worker, worker, ByteOps.empty (), ByteOps.empty ())",
            "(1, worker_leaf, worker, ByteOps.empty (), ByteOps.empty ())",
        ).replace(
            "main : Unit -> Unit",
            "worker_leaf<N> : (Network.Worker<N>, Bytes) -> Unit ! {Network.IO<N>}\nworker_leaf (endpoint, payload) = {\n    let ignored = match reserve_job (initial_worker (), 1, LedgerTypes.Root, 0, payload) {\n        (successor, status) => successor\n    }\n    let _ = Network.finish_send endpoint\n    match await_end endpoint {\n        true => {\n            let _ = Network.finish_receive endpoint\n            ()\n        }\n        false => ()\n    }\n}\n\ninitial_worker : Unit -> Ledger\ninitial_worker () = Ledger(0, NoRecords, NoOutputs)\n\nmain : Unit -> Unit",
        );
        assert!(source.contains("(1, worker_leaf, worker,"));
        run_worker_case(&source, true, false, None, Some(true));
        let duplicate = source.replace(
            "reserve_job (initial_worker (), 1, LedgerTypes.Root, 0, payload)",
            "reserve_job (initial_worker (), 0, LedgerTypes.Root, 0, payload)",
        );
        assert_ne!(duplicate, source);
        run_worker_case(&duplicate, true, false, None, Some(false));
        let both_roots = source.replace(
            "initial_worker () = Ledger(0, NoRecords, NoOutputs)",
            "initial_worker () = Ledger(0, RecordCons(Record(LedgerTypes.Root, LedgerTypes.NoParent, Open, Empty), NoRecords), NoOutputs)",
        );
        assert_ne!(both_roots, source);
        run_worker_case(&both_roots, true, false, None, Some(false));
    }

    #[test]
    fn linked_ledger_plan_budget_is_shared_and_failures_publish_nothing() {
        let source = completed_worker(include_str!("../../../tests/fixtures/n3-ledger-worker.ash"));
        run_worker_case_with_budget(&source, true, false, None, Some(false), Some((1, 1, true)));
    }

    fn completed_worker(source: &str) -> String {
        let completed = source.replace(
            "    ()\n}\n\nmain : Unit -> Unit",
            "    let _ = Network.finish_send endpoint\n    match await_end endpoint {\n        true => {\n            let _ = Network.finish_receive endpoint\n            ()\n        }\n        false => ()\n    }\n}\n\nawait_end<N> : Network.Worker<N> -> Bool ! {Network.IO<N>}\nawait_end endpoint = match Network.try_receive endpoint {\n    Network.Empty => await_end endpoint\n    Network.End => true\n    Network.Message(_, _) => false\n    Network.ReceiveFailed(_) => false\n}\n\nmain : Unit -> Unit",
        );
        assert_ne!(completed, source);
        completed
    }

    fn run_worker_case(
        source: &str,
        expect_current: bool,
        two_calls: bool,
        transition_case: Option<bool>,
        exercise_plan: Option<bool>,
    ) {
        let _ = run_worker_case_with_budget(
            source,
            expect_current,
            two_calls,
            transition_case,
            exercise_plan,
            None,
        );
    }

    fn run_worker_case_with_budget(
        source: &str,
        expect_current: bool,
        two_calls: bool,
        transition_case: Option<bool>,
        exercise_plan: Option<bool>,
        budget: Option<(usize, usize, bool)>,
    ) -> Option<usize> {
        let (program, provenance, linked) =
            super::super::tests::retained_drain_fixture_with_linked(source);
        let recursive_driver = source.contains("driver<N> :");
        let candidate = |name: &str| {
            let binder = linked
                .groups()
                .iter()
                .flat_map(|g| g.definitions())
                .find_map(|d| {
                    let ResolvedDefinitionKind::Equational(def) = d.kind() else {
                        return None;
                    };
                    (def.interface.name.spelling == name).then_some(def.interface.name.id)
                })
                .expect("fixture binder");
            let initializer = program
                .nodes
                .iter()
                .find_map(|node| {
                    let EffectExprKind::Pure(PureExprKind::Computation(
                        PureComputation::RecursiveBind(group),
                    )) = &node.kind
                    else {
                        return None;
                    };
                    group
                        .members()
                        .iter()
                        .find(|member| member.binder().id() == binder)
                        .map(|member| member.initializer())
                })
                .expect("fixture initializer");
            DefinitionCandidate {
                binder,
                initializer,
            }
        };
        let network_types_module = provenance
            .iter()
            .find_map(|(module, source)| {
                (source.text() == include_str!("../../../libraries/network_types.ash"))
                    .then_some(*module)
            })
            .expect("linked shared network types");
        let constructor = |name: &str| {
            let module = if matches!(
                name,
                "Root" | "Work" | "NoParent" | "Parent" | "WorkOut" | "AckOut"
            ) {
                network_types_module
            } else {
                linked.entry()
            };
            program
                .registry
                .constructors()
                .iter()
                .find(|item| item.spelling == name && item.id.owner().module() == module)
                .expect("fixture constructor")
                .id
        };
        let state = InitializationConstructors {
            ledger: constructor("Ledger"),
            record: constructor("Record"),
            root: constructor("Root"),
            work: constructor("Work"),
            no_parent: constructor("NoParent"),
            parent: constructor("Parent"),
            open: constructor("Open"),
            closed: constructor("Closed"),
            children_empty: constructor("Empty"),
            children_more: constructor("More"),
            records_empty: constructor("NoRecords"),
            records_more: constructor("RecordCons"),
            outputs_empty: constructor("NoOutputs"),
            outputs_more: constructor("OutputCons"),
        };
        let definitions = RegistrationDefinitions {
            entry: candidate("reserve_job"),
            find: candidate("find_record"),
            finish: candidate("finish_registration"),
            commit: candidate("commit_registration"),
            append_child: candidate("append_child"),
            update: candidate("update_record"),
            append_output: candidate("append_output"),
            comparison: candidate("same_id"),
            projection: candidate("record_id"),
        };
        let constructors = RegistrationConstructors {
            state,
            no_record: constructor("NoRecord"),
            has_record: constructor("HasRecord"),
            rejected: constructor("Rejected"),
            registered: constructor("Registered"),
            child: constructor("Child"),
            work_out: constructor("WorkOut"),
        };
        let calls: Vec<NodeId> = program
            .nodes
            .iter()
            .enumerate()
            .filter_map(|(i, node)| {
                let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Apply(app))) =
                    &node.kind
                else {
                    return None;
                };
                let EffectExprKind::Pure(PureExprKind::Variable(variable)) =
                    &program.nodes.get(app.function().index().ok()?)?.kind
                else {
                    return None;
                };
                (variable.binder() == definitions.entry.binder)
                    .then(|| NodeId::new(program.arena, i as u32))
            })
            .collect();
        let pair_workers = source.contains("worker_leaf<N> :");
        let mut selection_work = TypeWorkBudget::with_limit(500_000_000);
        let initial_binder = candidate("initial").binder;
        let initial_for = |call: NodeId, work: &mut TypeWorkBudget| {
            let checked = check_nominated_registration_call(
                &program,
                &linked,
                call,
                definitions,
                constructors,
                work,
            )
            .ok()?;
            let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Apply(app))) =
                &program.nodes.get(checked.input().index().ok()?)?.kind
            else {
                return None;
            };
            let EffectExprKind::Pure(PureExprKind::Variable(function)) =
                &program.nodes.get(app.function().index().ok()?)?.kind
            else {
                return None;
            };
            Some((function.binder(), checked.input()))
        };
        let call = if pair_workers {
            *calls
                .iter()
                .find(|&&call| {
                    initial_for(call, &mut selection_work)
                        .is_some_and(|(binder, _)| binder == initial_binder)
                })
                .expect("root worker registration")
        } else {
            *calls.first().expect("actual worker registration call")
        };
        let matching = |call: NodeId| {
            program
                .nodes
                .iter()
                .enumerate()
                .find_map(|(i, node)| {
                    let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Match(
                        branch,
                    ))) = &node.kind
                    else {
                        return None;
                    };
                    (branch.scrutinee() == call).then(|| NodeId::new(program.arena, i as u32))
                })
                .expect("actual returned pair match")
        };
        let binding = if two_calls || recursive_driver {
            let initial = candidate("initial").binder;
            Some(
                program
                    .nodes
                    .iter()
                    .enumerate()
                    .find_map(|(i, node)| {
                        let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Bind(
                            binding,
                        ))) = &node.kind
                        else {
                            return None;
                        };
                        let initializer =
                            &program.nodes.get(binding.initializer().index().ok()?)?.kind;
                        let EffectExprKind::Pure(PureExprKind::Computation(
                            PureComputation::Apply(app),
                        )) = initializer
                        else {
                            return None;
                        };
                        let EffectExprKind::Pure(PureExprKind::Variable(function)) =
                            &program.nodes.get(app.function().index().ok()?)?.kind
                        else {
                            return None;
                        };
                        (function.binder() == initial)
                            .then(|| (NodeId::new(program.arena, i as u32), binding.initializer()))
                    })
                    .expect("actual initializer binding"),
            )
        } else {
            None
        };
        let owner = program
            .nodes
            .iter()
            .enumerate()
            .find_map(|(i, node)| {
                matches!(
                    &node.kind,
                    EffectExprKind::Operation(EffectOperation::Network(_))
                )
                .then(|| NodeId::new(program.arena, i as u32))
            })
            .expect("actual Network owner");
        let mut work = TypeWorkBudget::with_limit(500_000_000);
        let registration = check_nominated_registration_call(
            &program,
            &linked,
            call,
            definitions,
            constructors,
            &mut work,
        )
        .unwrap();
        let initialization = check_nominated_initialization_call(
            &program,
            &linked,
            binding.map_or(registration.input(), |(_, call)| call),
            candidate("initial"),
            state,
            InitializationRole::Root,
            &mut work,
        )
        .unwrap();
        let result =
            check_registration_result_match(&program, &registration, matching(call), &mut work)
                .unwrap();
        let following = if two_calls {
            let next = *calls.get(1).expect("second actual registration");
            let summary = check_nominated_registration_call(
                &program,
                &linked,
                next,
                definitions,
                constructors,
                &mut work,
            )
            .unwrap();
            let result =
                check_registration_result_match(&program, &summary, matching(next), &mut work)
                    .unwrap();
            Some((summary, result))
        } else {
            None
        };
        let mut registrations = vec![(&registration, &result)];
        if let Some((next, next_result)) = following.as_ref() {
            registrations.push((next, next_result));
        }
        let receive_plan = if recursive_driver
            || (two_calls
                && source.contains("            let received = Network.try_receive endpoint"))
        {
            let definition = candidate("try_receive");
            let calls: Vec<_> = program
                .nodes
                .iter()
                .enumerate()
                .filter_map(|(index, node)| {
                    let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Apply(
                        application,
                    ))) = &node.kind
                    else {
                        return None;
                    };
                    let mut function = application.function();
                    loop {
                        match &program.nodes.get(function.index().ok()?)?.kind {
                            EffectExprKind::Pure(PureExprKind::Computation(
                                PureComputation::TypeApplication(applied),
                            )) => function = applied.function(),
                            EffectExprKind::Pure(PureExprKind::Variable(variable))
                                if variable.binder() == definition.binder =>
                            {
                                break;
                            }
                            _ => return None,
                        }
                    }
                    let call = NodeId::new(program.arena, index as u32);
                    (recursive_driver || program.nodes.iter().any(|node| matches!(
                        &node.kind,
                        EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Bind(bind)))
                            if bind.initializer() == call
                    ))).then_some(call)
                })
                .collect();
            let [call] = calls.as_slice() else {
                panic!(
                    "expected the unique bound receive call, found {}",
                    calls.len()
                );
            };
            let call = *call;
            Some(crate::core::ledger_checker::driver::ReceiveNomination { definition, call })
        } else {
            None
        };
        let receives: Vec<_> = receive_plan
            .iter()
            .map(|plan| {
                crate::core::ledger_checker::driver::check_nominated_receive_call(
                    &program, &linked, plan, &mut work,
                )
                .expect("actual linked receive")
            })
            .collect();
        let mut driver_capture_binders = Vec::new();
        let mut driver_calls = Vec::new();
        let driver_definition = if recursive_driver {
            let definition = candidate("driver");
            let mut body = definition.initializer;
            loop {
                match &program.nodes[body.index().unwrap()].kind {
                    EffectExprKind::Pure(PureExprKind::Computation(
                        PureComputation::TypeAbstraction(abstraction),
                    )) => body = abstraction.body(),
                    _ => break,
                }
            }
            let (_, closure) = crate::core::region::closure_initializer::<
                crate::core::EffectOperationFamily,
            >(body, |id| {
                program.nodes.get(id.index().ok()?).map(|node| &node.kind)
            })
            .expect("actual driver closure");
            for capture in &closure.captures {
                let EffectExprKind::Pure(PureExprKind::Variable(variable)) =
                    &program.nodes[capture.index().unwrap()].kind
                else {
                    panic!("driver capture must be a linked variable");
                };
                driver_capture_binders.push(variable.binder());
            }
            for (index, node) in program.nodes.iter().enumerate() {
                let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Apply(
                    application,
                ))) = &node.kind
                else {
                    continue;
                };
                let mut function = application.function();
                loop {
                    match &program.nodes[function.index().unwrap()].kind {
                        EffectExprKind::Pure(PureExprKind::Computation(
                            PureComputation::TypeApplication(applied),
                        )) => function = applied.function(),
                        EffectExprKind::Pure(PureExprKind::Variable(variable))
                            if variable.binder() == definition.binder =>
                        {
                            driver_calls.push(NodeId::new(program.arena, index as u32));
                            break;
                        }
                        _ => break,
                    }
                }
            }
            assert!(
                driver_calls.len() >= 3,
                "entry and recursive driver calls must be nominated"
            );
            Some(definition)
        } else {
            None
        };
        let driver_plans: Vec<_> = driver_calls
            .iter()
            .map(
                |&call| crate::core::ledger_checker::driver::DriverNomination {
                    definition: driver_definition.expect("driver definition"),
                    captures: &driver_capture_binders,
                    call,
                    arity: 2,
                    ledger_field: 1,
                },
            )
            .collect();
        let drivers: Vec<_> = driver_plans
            .iter()
            .map(|plan| {
                crate::core::ledger_checker::driver::check_nominated_driver_call(
                    &program, &linked, plan, &mut work,
                )
                .expect("actual driver call")
            })
            .collect();
        let transition_calls = if transition_case.is_some() {
            use crate::core::ledger_checker::{
                acknowledgement::{
                    AcknowledgementConstructors, AcknowledgementDefinitions,
                    check_nominated_acknowledgement_call,
                },
                retirement::{
                    RetirementConstructors, RetirementDefinitions, check_nominated_retirement_call,
                },
            };
            let find_call = |entry: DefinitionCandidate| {
                program
                    .nodes
                    .iter()
                    .enumerate()
                    .find_map(|(i, node)| {
                        let EffectExprKind::Pure(PureExprKind::Computation(
                            PureComputation::Apply(app),
                        )) = &node.kind
                        else {
                            return None;
                        };
                        let EffectExprKind::Pure(PureExprKind::Variable(variable)) =
                            &program.nodes.get(app.function().index().ok()?)?.kind
                        else {
                            return None;
                        };
                        (variable.binder() == entry.binder)
                            .then(|| NodeId::new(program.arena, i as u32))
                    })
                    .expect("actual transition call")
            };
            let retire = candidate("retire");
            let acknowledge = candidate("acknowledge");
            let close = candidate("close_record");
            let retire_call = find_call(retire);
            let ack_call = find_call(acknowledge);
            let close_call = find_call(close);
            let close_definitions = crate::core::ledger_checker::closure::ClosureDefinitions {
                entry: close,
                finish: candidate("finish_close"),
                lookup: candidate("find_record"),
                update: candidate("update_record"),
                comparison: candidate("same_id"),
                projection: candidate("record_id"),
            };
            let close_constructors = crate::core::ledger_checker::closure::ClosureConstructors {
                state,
                no_record: constructor("NoRecord"),
                has_record: constructor("HasRecord"),
            };
            let closure = crate::core::ledger_checker::closure::check_nominated_closure_call(
                &program,
                &linked,
                close_call,
                close_definitions,
                close_constructors,
                &mut work,
            )
            .unwrap();
            let retired_binding = program
                .nodes
                .iter()
                .enumerate()
                .find_map(|(i, node)| {
                    let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Bind(
                        bind,
                    ))) = &node.kind
                    else {
                        return None;
                    };
                    (bind.initializer() == retire_call)
                        .then(|| NodeId::new(program.arena, i as u32))
                })
                .expect("actual retirement result binding");
            let retirement = check_nominated_retirement_call(
                &program,
                &linked,
                retire_call,
                RetirementDefinitions {
                    entry: retire,
                    work: candidate("retire_work"),
                    found: candidate("retire_found"),
                    parent: candidate("retire_parent"),
                    phase: candidate("retire_phase"),
                    children: candidate("retire_children"),
                    commit: candidate("commit_retirement"),
                    lookup: candidate("find_record"),
                    removal: candidate("remove_record"),
                    append_output: candidate("append_output"),
                    comparison: candidate("same_id"),
                    projection: candidate("record_id"),
                },
                RetirementConstructors {
                    state,
                    no_record: constructor("NoRecord"),
                    has_record: constructor("HasRecord"),
                    found: constructor("Found"),
                    missing: constructor("Missing"),
                    ack: constructor("AckOut"),
                },
                &mut work,
            )
            .unwrap();
            let acknowledgement = check_nominated_acknowledgement_call(
                &program,
                &linked,
                ack_call,
                AcknowledgementDefinitions {
                    entry: acknowledge,
                    record: candidate("ack_found"),
                    child: candidate("ack_child"),
                    commit: candidate("ack_commit"),
                    record_lookup: candidate("find_record"),
                    child_lookup: candidate("find_child"),
                    record_update: candidate("update_record"),
                    child_removal: candidate("remove_child"),
                    comparison: candidate("same_id"),
                    record_projection: candidate("record_id"),
                    child_projection: candidate("child_id"),
                },
                AcknowledgementConstructors {
                    state,
                    child: constructor("Child"),
                    no_record: constructor("NoRecord"),
                    has_record: constructor("HasRecord"),
                    no_child: constructor("NoChild"),
                    has_child: constructor("HasChild"),
                    removed: constructor("Found"),
                    missing: constructor("Missing"),
                },
                &mut work,
            )
            .unwrap();
            Some((
                retirement,
                acknowledgement,
                retired_binding,
                closure,
                close_definitions,
                close_constructors,
            ))
        } else {
            None
        };
        let plan_registration = crate::core::ledger_checker::plan::RegistrationNomination {
            call,
            result_match: matching(call),
            definitions,
            constructors,
        };
        let plan_initial = candidate("initial");
        let plan_initial_call = initialization.call();
        let default_handler = checked_entry_default_handler(&program, &mut work).unwrap();
        let check_budget = budget.is_some();
        crate::core::validate::with_network_native_scope_diagnostic(
            &program,
            &provenance,
            &linked,
            owner,
            &mut work,
            |scope, budget| {
                super::super::with_network_worker_resources(
                    scope,
                    1,
                    budget,
                    |graph, worker, budget| {
                        let focus = worker.completion_foci.last().ok_or(Failure::Invalid)?;
                        let nominations =
                            transition_calls
                                .as_ref()
                                .map(|(retirement, acknowledgement, _, closure, _, _)| {
                                    [
                                        transition_observation::TransitionCall::Retirement(retirement),
                                        transition_observation::TransitionCall::Acknowledgement(acknowledgement),
                                        transition_observation::TransitionCall::Closure(closure),
                                    ]
                                });
                        let observed = observe_direct_registration(
                            scope,
                            graph,
                            focus,
                            &initialization,
                            &registrations,
                            &drivers,
                            &receives,
                            binding.map(|(node, _)| node),
                            nominations
                                .as_ref()
                                .map_or(&[][..], |items| items.as_slice()),
                            default_handler,
                            1,
                            budget,
                        );
                        if !expect_current {
                            assert!(matches!(observed, Err(Failure::Invalid)));
                            return Ok(());
                        }
                        let observed = observed?;
                        assert!(!observed.transitions.is_empty());
                        assert!(!observed.current.is_empty());
                        if !receives.is_empty() {
                            assert!(observed.requires_exclusive_update);
                        }
                        if two_calls {
                            assert!(observed.transitions.len() >= 2);
                        }
                        if two_calls && exercise_plan != Some(false) {
                            let following_call = *calls.get(1).ok_or(Failure::Invalid)?;
                            let requested = [
                                crate::core::ledger_checker::plan::RegistrationNomination {
                                    call, result_match: matching(call), definitions, constructors,
                                },
                                crate::core::ledger_checker::plan::RegistrationNomination {
                                    call: following_call, result_match: matching(following_call), definitions, constructors,
                                },
                            ];
                            let plan = crate::core::ledger_checker::plan::LedgerPlan {
                                owner, side: 1, initialization_call: plan_initial_call,
                                initialization: plan_initial, initialization_constructors: state,
                                initialization_role: InitializationRole::Root,
                                initialization_binding: binding.map(|(node, _)| node),
                                registrations: &requested, transitions: &[], drivers: &[],
                                receives: receive_plan.as_ref().map_or(&[], std::slice::from_ref),
                            };
                            let actual_input = registrations[1].0.input();
                            let role = registrations[0].1.ledger;
                            let (pending, ()) = with_observed_ledger_plan(
                                scope, graph, worker, &program, &linked, &plan, budget,
                                |query, work| {
                                    let mut matched = false;
                                    for &(id, _, _, _) in query.current {
                                        if let Some(witness) = query.checked_input(id, following_call, actual_input, role, work)? {
                                            if witness.owner != owner || witness.side != 1 || witness.role != role
                                                || !witness.requires_history_and_peer_allocator
                                                || (receive_plan.is_some() && !witness.requires_exclusive_update) {
                                                return Err(Failure::Invalid);
                                            }
                                            if query.checked_input(id, following_call, registrations[0].0.input(), role, work)?.is_some() {
                                                return Err(Failure::Invalid);
                                            }
                                            matched = true;
                                        }
                                    }
                                    if !matched { return Err(Failure::Invalid); }
                                    Ok(())
                                },
                            )?;
                            if pending.steps.len() != 2 || pending.steps[1].target != registrations[1].0.closure() {
                                return Err(Failure::Invalid);
                            }
                        }
                        assert_eq!(observed.owner, scope.owner());
                        assert_eq!(observed.side, 1);
                        if let (Some(expected), Some((_, _, binding, _, _, _)), Some(nominations)) = (
                            transition_case,
                            transition_calls.as_ref(),
                            nominations.as_ref(),
                        ) {
                            let retired = transition_observation::observe_transition_calls(
                                scope,
                                graph,
                                focus,
                                &observed,
                                nominations[0],
                                1,
                                None,
                                budget,
                            )?;
                            if retired.is_empty() {
                                return Err(Failure::Invalid);
                            }
                            for token in &retired {
                                let acknowledged = transition_observation::observe_transition_calls(
                                    scope,
                                    graph,
                                    focus,
                                    &observed,
                                    nominations[1],
                                    1,
                                    Some((token, *binding)),
                                    budget,
                                );
                                if expected {
                                    let acknowledged = acknowledged?;
                                    if acknowledged.is_empty()
                                        || acknowledged
                                            .iter()
                                            .any(|token| !token.peer_authentication_required)
                                    {
                                        return Err(Failure::Invalid);
                                    }
                                } else if !matches!(acknowledged, Err(Failure::Invalid)) {
                                    return Err(Failure::Invalid);
                                }
                            }
                        }
                        if check_budget {
                            let run = |work: &mut TypeWorkBudget| observe_direct_registration(
                                scope, graph, focus, &initialization, &registrations, &drivers,
                                &receives, binding.map(|(node, _)| node),
                                nominations.as_ref().map_or(&[][..], |items| items.as_slice()),
                                default_handler, 1, work,
                            );
                            let mut measured = TypeWorkBudget::with_limit(500_000_000);
                            let _ = run(&mut measured)?;
                            let exact = measured.used();
                            if exact < 2 { return Err(Failure::Invalid); }
                            let mut same = TypeWorkBudget::with_limit(exact);
                            let _ = run(&mut same)?;
                            let mut short = TypeWorkBudget::with_limit(exact - 1);
                            if !matches!(run(&mut short), Err(Failure::Resource)) {
                                return Err(Failure::Invalid);
                            }
                            let mut spent = TypeWorkBudget::with_limit(exact);
                            spent.charge(1).map_err(|()| Failure::Resource)?;
                            if !matches!(run(&mut spent), Err(Failure::Resource)) {
                                return Err(Failure::Invalid);
                            }
                            if !matches!(run(&mut short), Err(Failure::Resource))
                                || !matches!(run(&mut spent), Err(Failure::Resource))
                            {
                                return Err(Failure::Invalid);
                            }
                        }
                        assert!(matches!(
                            observe_direct_registration(
                                scope,
                                graph,
                                focus,
                                &initialization,
                                &registrations,
                                &drivers,
                                &receives,
                                binding.map(|(node, _)| node),
                                nominations
                                    .as_ref()
                                    .map_or(&[][..], |items| items.as_slice()),
                                default_handler,
                                1,
                                &mut TypeWorkBudget::with_limit(0)
                            ),
                            Err(Failure::Resource)
                        ));
                        Ok(())
                    },
                )
                .expect("actual worker trace must connect the three source observations");
                Ok(())
            },
        )
        .expect("validator scope must authenticate");
        eprintln!(
            "focus-local N3 test used {} work; no provider/currentness fact is issued",
            work.used()
        );
        if let Some(expect_success) = exercise_plan {
            let mut nominations = vec![plan_registration];
            if two_calls {
                let next = *calls.get(1).expect("second actual registration");
                nominations.push(crate::core::ledger_checker::plan::RegistrationNomination {
                    call: next,
                    result_match: matching(next),
                    definitions,
                    constructors,
                });
            }
            let transition_plans = if let Some((
                retirement,
                acknowledgement,
                _,
                closure,
                close_definitions,
                close_constructors,
            )) = transition_calls.as_ref()
            {
                use crate::core::ledger_checker::{
                    acknowledgement::{AcknowledgementConstructors, AcknowledgementDefinitions},
                    plan::TransitionNomination,
                    retirement::{RetirementConstructors, RetirementDefinitions},
                };
                vec![
                    TransitionNomination::Closure {
                        call: closure.call(),
                        definitions: *close_definitions,
                        constructors: *close_constructors,
                    },
                    TransitionNomination::Retirement {
                        call: retirement.call(),
                        definitions: RetirementDefinitions {
                            entry: candidate("retire"),
                            work: candidate("retire_work"),
                            found: candidate("retire_found"),
                            parent: candidate("retire_parent"),
                            phase: candidate("retire_phase"),
                            children: candidate("retire_children"),
                            commit: candidate("commit_retirement"),
                            lookup: candidate("find_record"),
                            removal: candidate("remove_record"),
                            append_output: candidate("append_output"),
                            comparison: candidate("same_id"),
                            projection: candidate("record_id"),
                        },
                        constructors: RetirementConstructors {
                            state,
                            no_record: constructor("NoRecord"),
                            has_record: constructor("HasRecord"),
                            found: constructor("Found"),
                            missing: constructor("Missing"),
                            ack: constructor("AckOut"),
                        },
                    },
                    TransitionNomination::Acknowledgement {
                        call: acknowledgement.call(),
                        definitions: AcknowledgementDefinitions {
                            entry: candidate("acknowledge"),
                            record: candidate("ack_found"),
                            child: candidate("ack_child"),
                            commit: candidate("ack_commit"),
                            record_lookup: candidate("find_record"),
                            child_lookup: candidate("find_child"),
                            record_update: candidate("update_record"),
                            child_removal: candidate("remove_child"),
                            comparison: candidate("same_id"),
                            record_projection: candidate("record_id"),
                            child_projection: candidate("child_id"),
                        },
                        constructors: AcknowledgementConstructors {
                            state,
                            child: constructor("Child"),
                            no_record: constructor("NoRecord"),
                            has_record: constructor("HasRecord"),
                            no_child: constructor("NoChild"),
                            has_child: constructor("HasChild"),
                            removed: constructor("Found"),
                            missing: constructor("Missing"),
                        },
                    },
                ]
            } else {
                Vec::new()
            };
            let receive_plans: Vec<_> = receive_plan.into_iter().collect();
            let leaf_initial = pair_workers.then(|| candidate("initial_worker"));
            let leaf_call = leaf_initial.map(|initial| {
                *calls
                    .iter()
                    .find(|&&call| {
                        initial_for(call, &mut selection_work)
                            .is_some_and(|(binder, _)| binder == initial.binder)
                    })
                    .expect("leaf worker registration")
            });
            let leaf_nominations: Vec<_> = leaf_call
                .into_iter()
                .map(
                    |call| crate::core::ledger_checker::plan::RegistrationNomination {
                        call,
                        result_match: matching(call),
                        definitions,
                        constructors,
                    },
                )
                .collect();
            let leaf_initial_call = leaf_call.map(|call| {
                initial_for(call, &mut selection_work)
                    .expect("leaf initializer")
                    .1
            });
            let mut plans = vec![crate::core::ledger_checker::plan::LedgerPlan {
                owner,
                side: 1,
                initialization_call: plan_initial_call,
                initialization: plan_initial,
                initialization_constructors: state,
                initialization_role: InitializationRole::Root,
                initialization_binding: binding.map(|(node, _)| node),
                registrations: &nominations,
                transitions: &transition_plans,
                drivers: &driver_plans,
                receives: &receive_plans,
            }];
            if let (Some(initialization), Some(initialization_call)) =
                (leaf_initial, leaf_initial_call)
            {
                plans.push(crate::core::ledger_checker::plan::LedgerPlan {
                    owner,
                    side: 0,
                    initialization_call,
                    initialization,
                    initialization_constructors: state,
                    initialization_role: if source
                        .contains("initial_worker () = Ledger(0, RecordCons(")
                    {
                        InitializationRole::Root
                    } else {
                        InitializationRole::Worker
                    },
                    initialization_binding: None,
                    registrations: &leaf_nominations,
                    transitions: &[],
                    drivers: &[],
                    receives: &[],
                });
            }
            let sources: Vec<_> = provenance.iter().map(|(_, source)| source).collect();
            let relations: Vec<_> = provenance
                .iter()
                .map(|(module, source)| (*module, source.id()))
                .collect();
            let (limit, spent, resource_failure) = budget.unwrap_or((500_000_000, 0, false));
            let mut allowance = TypeWorkBudget::with_limit(limit);
            allowance
                .charge(spent)
                .expect("preset work fits its budget");
            let outcome = crate::core::validate::validate_effect_modules_linked_with_ledger_plans(
                program,
                &sources,
                &relations,
                &linked,
                &plans,
                &mut allowance,
            );
            if expect_success {
                let (_, observations) =
                    outcome.expect("the requested linked ledger plan must survive full validation");
                assert_eq!(observations.len(), if pair_workers { 2 } else { 1 });
                let observation = observations
                    .iter()
                    .find(|observation| observation.side == 1)
                    .expect("root worker observation");
                assert_eq!(observation.owner, owner);
                assert_eq!(observation.side, 1);
                assert_eq!(observation.initialization, plan_initial_call);
                assert_eq!(
                    observation.steps.len(),
                    nominations.len() + if transition_case.is_some() { 2 } else { 0 }
                );
                if transition_case.is_some() {
                    assert!(observation.requires_peer_authentication);
                    use crate::core::ledger_checker::plan::TransitionNomination;
                    for nomination in &transition_plans[..2] {
                        let call = match nomination {
                            TransitionNomination::Closure { call, .. }
                            | TransitionNomination::Retirement { call, .. } => *call,
                            TransitionNomination::Acknowledgement { .. } => unreachable!(),
                        };
                        assert!(observation.steps.iter().any(|step| step.call == call));
                    }
                }
                for (step, nomination) in observation.steps.iter().zip(&nominations) {
                    assert_eq!(step.call, nomination.call);
                    assert_eq!(step.successor_site, nomination.result_match);
                }
                assert!(!observation.current_sites.is_empty());
                assert!(observation.requires_history_and_peer_allocator);
                if !receive_plans.is_empty() {
                    assert!(observation.requires_exclusive_update);
                }
            } else if resource_failure {
                assert!(
                    matches!(outcome, Err(error) if error.reason() == crate::core::validate::ValidationReason::Resource)
                );
            } else {
                assert!(
                    matches!(outcome, Err(error) if error.reason() == crate::core::validate::ValidationReason::Registry)
                );
            }
            return Some(allowance.used());
        }
        None
    }
}
