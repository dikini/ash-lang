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
    Encoding {
        port: usize,
        context: usize,
        ordinal: usize,
        role: crate::resolved::BinderId,
        entry: usize,
        witness: usize,
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

#[derive(Clone, Copy, Eq, PartialEq)]
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
#[expect(
    clippy::type_complexity,
    reason = "The returned sets distinguish code, call sites and closures"
)]
fn checked_call_sites(
    scope: &NetworkNativeIdentityScope<'_>,
    initialization: &ConditionalInitializationCall<'_>,
    registration: &ConditionalRegistrationCall<'_>,
    extra_roots: &[crate::core::NodeId],
    work: &mut TypeWorkBudget,
) -> Result<(HashSet<usize>, HashSet<usize>, HashSet<usize>), Failure> {
    let roots = registration.definition_roots();
    let count = roots
        .len()
        .checked_add(extra_roots.len())
        .and_then(|n| n.checked_add(1))
        .ok_or(Failure::Resource)?;
    charge(work, count)?;
    let mut all = Vec::new();
    all.try_reserve(count).map_err(|_| Failure::Resource)?;
    all.extend(roots);
    all.extend_from_slice(extra_roots);
    all.push(initialization.definition_binding());
    checked_call_roots_owned(scope, all, work)
}

#[expect(
    clippy::type_complexity,
    reason = "the actual call, closure and visited-node sets are distinct bounded results"
)]
fn checked_call_roots(
    scope: &NetworkNativeIdentityScope<'_>,
    roots: &[crate::core::NodeId],
    work: &mut TypeWorkBudget,
) -> Result<(HashSet<usize>, HashSet<usize>, HashSet<usize>), Failure> {
    charge(work, roots.len())?;
    let mut pending = Vec::new();
    pending
        .try_reserve(roots.len())
        .map_err(|_| Failure::Resource)?;
    pending.extend_from_slice(roots);
    checked_call_roots_owned(scope, pending, work)
}

#[expect(
    clippy::type_complexity,
    reason = "the actual call, closure and visited-node sets are distinct bounded results"
)]
fn checked_call_roots_owned(
    scope: &NetworkNativeIdentityScope<'_>,
    mut pending: Vec<crate::core::NodeId>,
    work: &mut TypeWorkBudget,
) -> Result<(HashSet<usize>, HashSet<usize>, HashSet<usize>), Failure> {
    use crate::core::{EffectExprKind, EffectOperation, PureComputation, PureExprKind, PureValue};
    let mut visited = HashSet::new();
    let mut calls = HashSet::new();
    let mut closures = HashSet::new();
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

#[expect(
    clippy::too_many_arguments,
    reason = "The actual scope, control coordinates, checked definitions and work budget are distinct inputs"
)]
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
    authenticate_known_body_call(
        scope,
        focus,
        call,
        calls,
        closures,
        helpers,
        closure_origins,
        query_origins,
        work,
    )
}

/// Authenticate only the checked linked bytes-length intrinsic in the
/// encoder's live focus. It has no stored context or captures.
#[allow(clippy::too_many_arguments)]
fn authenticate_encoder_length_call(
    scope: &NetworkNativeIdentityScope<'_>,
    graph: &SummaryGraph,
    focus: &control::CompletionFocus<'_>,
    from: usize,
    to: usize,
    transition: control::CompletionTransition,
    calls: &HashSet<usize>,
    binder: crate::resolved::BinderId,
    intrinsic: crate::core::NodeId,
    work: &mut TypeWorkBudget,
) -> Result<(), Failure> {
    let witness = entered_call(graph, focus, from, to, transition, intrinsic, work)?;
    let call = focus.trace()?.call(witness, work)?;
    check_encoder_length_call(scope, focus, call, calls, binder, intrinsic, work)
}

#[allow(clippy::too_many_arguments)]
fn check_encoder_length_call(
    scope: &NetworkNativeIdentityScope<'_>,
    focus: &control::CompletionFocus<'_>,
    call: control::CompletionCall,
    calls: &HashSet<usize>,
    binder: crate::resolved::BinderId,
    intrinsic: crate::core::NodeId,
    work: &mut TypeWorkBudget,
) -> Result<(), Failure> {
    use crate::core::{
        EffectExprKind, PureComputation, PureExprKind, PureValue, packed::Intrinsic,
    };
    charge(work, 4)?;
    if intrinsic.arena() != scope.arena() {
        return Err(Failure::Invalid);
    }
    let target = intrinsic.index().map_err(|_| Failure::Invalid)?;
    let Some(EffectExprKind::Pure(PureExprKind::Value(PureValue::Intrinsic(actual)))) =
        scope.nodes().get(target).map(|node| &node.kind)
    else {
        return Err(Failure::Invalid);
    };
    if !actual.authentic_module()
        || !actual.module().is_builtin_bytes()
        || actual.operation() != Intrinsic::BytesLength
        || binder.module() != Some(actual.module())
    {
        return Err(Failure::Invalid);
    }
    if call.target != target || call.expression != target {
        return Err(Failure::Invalid);
    }
    let original = focus
        .values()
        .original_control_node(call.code, scope.nodes(), work)?;
    if !calls.contains(&original) {
        return Err(Failure::Invalid);
    }
    let Some(EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Apply(app)))) =
        scope.nodes().get(original).map(|node| &node.kind)
    else {
        return Err(Failure::Invalid);
    };
    if app.function().arena() != scope.arena() || app.argument().arena() != scope.arena() {
        return Err(Failure::Invalid);
    }
    let function = app.function().index().map_err(|_| Failure::Invalid)?;
    if !matches!(scope.nodes().get(function).map(|node| &node.kind),
        Some(EffectExprKind::Pure(PureExprKind::Variable(variable))) if variable.binder() == binder)
    {
        return Err(Failure::Invalid);
    }
    let (_, _, arguments, captures) = focus.values().existing_call_ports(
        call.code,
        call.caller_value_context,
        call.expression,
        call.callee_value_context,
        call.creation,
        work,
    )?;
    let argument_code = app
        .argument()
        .index()
        .map_err(|_| Failure::Invalid)?
        .checked_add(1)
        .ok_or(Failure::Resource)?;
    let (argument, _) =
        focus
            .values()
            .existing_forward_ports(argument_code, call.caller_value_context, work)?;
    if arguments.len() != 1 || arguments[0].1 != argument || !captures.is_empty() {
        return Err(Failure::Invalid);
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn authenticate_known_body_call(
    scope: &NetworkNativeIdentityScope<'_>,
    focus: &control::CompletionFocus<'_>,
    call: control::CompletionCall,
    calls: &HashSet<usize>,
    closures: &HashSet<usize>,
    helpers: &[(crate::resolved::BinderId, crate::core::NodeId)],
    closure_origins: &HashMap<usize, DefinitionProvenance>,
    query_origins: &HashMap<usize, LocalOrigin>,
    work: &mut TypeWorkBudget,
) -> Result<(), Failure> {
    use crate::core::{EffectExprKind, EffectOperation, PureComputation, PureExprKind};
    let target = call.target;
    if call.expression != target || !closures.contains(&target) {
        return Err(Failure::Invalid);
    }
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
/// Bind a generated RegionBuffer service to its unique checked Core parent
/// and exact strict operands and service family. Codec primitives require an
/// explicit codec nomination; ordinary ledger Add remains separately checked.
/// Explicit Region allocations retain their original-node mapping.
fn checked_region_source(
    scope: &NetworkNativeIdentityScope<'_>,
    graph: &SummaryGraph,
    focus: &control::CompletionFocus<'_>,
    code: usize,
    checked_nodes: &HashSet<usize>,
    codec_buffers: Option<&HashSet<usize>>,
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
        let ledger_add = matches!(
            &buffer.operation,
            crate::core::region::RegionBufferOperation::IntegerArithmetic(
                crate::core::Primitive::Add
            )
        );
        let codec_allowed = codec_buffers.is_some_and(|nodes| nodes.contains(&original));
        if (!ledger_add || buffer.right.is_none()) && !codec_allowed {
            continue;
        }
        let family = if codec_allowed {
            use crate::core::{packed::Intrinsic, region::RegionBufferOperation};
            charge(work, 3)?;
            match &buffer.operation {
                RegionBufferOperation::Intrinsic(intrinsic)
                    if intrinsic.module().is_builtin_bytes() =>
                {
                    if buffer.right.is_some() {
                        return Err(Failure::Invalid);
                    }
                    match intrinsic.operation() {
                        Intrinsic::BytesAt { .. } | Intrinsic::BytesEmpty => 1,
                        Intrinsic::BytesAppendByte { .. } => 2,
                        _ => continue,
                    }
                }
                RegionBufferOperation::Intrinsic(intrinsic)
                    if intrinsic.module().is_builtin_integer()
                        && matches!(intrinsic.operation(), Intrinsic::IntegerSplit256 { .. }) =>
                {
                    if buffer.right.is_some() {
                        return Err(Failure::Invalid);
                    }
                    3
                }
                RegionBufferOperation::IntegerArithmetic(
                    crate::core::Primitive::Add | crate::core::Primitive::Multiply,
                ) => {
                    if buffer.right.is_none() {
                        return Err(Failure::Invalid);
                    }
                    1
                }
                _ => continue,
            }
        } else {
            1
        };
        let Some(left) = buffer.operand else { continue };
        if buffer.context.arena() != scope.arena()
            || left.arena() != scope.arena()
            || buffer
                .right
                .is_some_and(|right| right.arena() != scope.arena())
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
        let context = buffer
            .context
            .index()
            .map_err(|_| Failure::Invalid)?
            .checked_add(1)
            .ok_or(Failure::Resource)?;
        let left = left
            .index()
            .map_err(|_| Failure::Invalid)?
            .checked_add(1)
            .ok_or(Failure::Resource)?;
        let (prefix, tail) = match children.split_last() {
            Some((tail, prefix)) => (prefix, *tail),
            None => continue,
        };
        let operands_match = if let Some(right) = buffer.right {
            let right = right
                .index()
                .map_err(|_| Failure::Invalid)?
                .checked_add(1)
                .ok_or(Failure::Resource)?;
            prefix == [context, left, right]
        } else {
            prefix == [context, left]
        };
        let service_match = if family == 1 {
            tail == code
        } else if let Some(control::Control::Choice(choices)) = graph.code.get(tail) {
            let twice = choices.get(1).and_then(|index| graph.code.get(*index));
            let two = matches!(twice, Some(control::Control::Sequence(parts)) if parts.as_slice() == [code, code]);
            let three = if family == 3 {
                matches!(choices.get(2).and_then(|index| graph.code.get(*index)),
                    Some(control::Control::Sequence(parts)) if parts.as_slice() == [code, code, code])
            } else {
                true
            };
            choices.len() == family && choices.first() == Some(&code) && two && three
        } else {
            false
        };
        if operands_match && service_match && found.replace(original).is_some() {
            return Err(Failure::Invalid);
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
#[expect(
    clippy::too_many_arguments,
    reason = "The actual scope, control coordinates, checked definitions and work budget are distinct inputs"
)]
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
    codec_buffers: Option<&HashSet<usize>>,
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
                    )
                    || codec_buffers.is_some_and(|nodes| nodes.contains(&original))) =>
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
    #[cfg_attr(
        not(test),
        expect(dead_code, reason = "used by the focused transition observer")
    )]
    owner: crate::core::NodeId,
    #[cfg_attr(
        not(test),
        expect(dead_code, reason = "used by the focused transition observer")
    )]
    side: u8,
    requires_exclusive_update: bool,
    requires_peer_authentication: bool,
    _transition_returns: Vec<(usize, usize, usize, usize, usize)>,
    encoder_returns: Vec<(usize, usize, usize, usize)>,
    #[cfg(test)]
    saw_encoder_length: bool,
    transition_bindings: Vec<(usize, crate::core::NodeId, crate::resolved::BinderId)>,
    transitions: Vec<(usize, usize, usize, usize)>,
    current: Vec<(usize, usize, usize, crate::resolved::BinderId)>,
    #[cfg_attr(
        not(test),
        expect(dead_code, reason = "used by the focused transition observer")
    )]
    transition_calls: Vec<(crate::core::NodeId, crate::core::NodeId)>,
    #[cfg_attr(
        not(test),
        expect(dead_code, reason = "used by the focused transition observer")
    )]
    argument_constructors: Vec<(crate::core::NodeId, crate::core::NodeId)>,
    #[cfg_attr(
        not(test),
        expect(dead_code, reason = "used by the focused transition observer")
    )]
    checked_nodes: HashSet<usize>,
    #[cfg_attr(
        not(test),
        expect(dead_code, reason = "used by the focused transition observer")
    )]
    body_calls: HashSet<usize>,
    #[cfg_attr(
        not(test),
        expect(dead_code, reason = "used by the focused transition observer")
    )]
    body_closures: HashSet<usize>,
    #[cfg_attr(
        not(test),
        expect(dead_code, reason = "used by the focused transition observer")
    )]
    helpers: Vec<(crate::resolved::BinderId, crate::core::NodeId)>,
    #[cfg_attr(
        not(test),
        expect(dead_code, reason = "used by the focused transition observer")
    )]
    closure_origins: HashMap<usize, DefinitionProvenance>,
    #[cfg_attr(
        not(test),
        expect(dead_code, reason = "used by the focused transition observer")
    )]
    query_origins: HashMap<usize, LocalOrigin>,
    #[cfg_attr(
        not(test),
        expect(dead_code, reason = "used by the focused transition observer")
    )]
    verified_query_requests: HashSet<usize>,
    #[cfg_attr(
        not(test),
        expect(dead_code, reason = "used by the focused transition observer")
    )]
    verified_query_resumes: HashSet<usize>,
    #[cfg_attr(
        not(test),
        expect(dead_code, reason = "used by the focused transition observer")
    )]
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
#[expect(
    clippy::too_many_arguments,
    reason = "The actual scope, control coordinates, checked definitions and work budget are distinct inputs"
)]
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
#[expect(
    clippy::too_many_arguments,
    reason = "The actual scope, control coordinates, checked definitions and work budget are distinct inputs"
)]
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

struct CheckedQueries {
    closure_origins: HashMap<usize, DefinitionProvenance>,
    query_origins: HashMap<usize, LocalOrigin>,
    verified_query_requests: HashSet<usize>,
    verified_query_resumes: HashSet<usize>,
    query_caller_contexts: HashMap<usize, usize>,
}

/// Verify the actual query/handler/resume paths in one settled focus. No
/// value port returned here can be transferred to any other focus.
#[allow(clippy::too_many_arguments)]
fn checked_queries(
    scope: &NetworkNativeIdentityScope<'_>,
    graph: &SummaryGraph,
    focus: &control::CompletionFocus<'_>,
    checked_nodes: &HashSet<usize>,
    definitions: &[DefinitionProvenance],
    provider_api: crate::module::ModuleId,
    default_handler: crate::core::NodeId,
    states: &[Option<&control::State>],
    edges: &[(usize, usize, control::CompletionTransition)],
    details: &HashMap<usize, control::CompletionDetail>,
    outgoing: &[Vec<usize>],
    require_all_definitions: bool,
    work: &mut TypeWorkBudget,
) -> Result<CheckedQueries, Failure> {
    // Authenticate this actual initialization closure's context query on the
    // same converged startup trace. The selected handler must be the checked
    // entry provider and each reached alternative must follow its direct
    // normal Resume. This is only the first part of provider correspondence:
    // the returned port has not yet been tied to closure captures or uses.
    let bindings = query_bindings(scope, checked_nodes, provider_api, work)?;
    let closure_origins = closure_bindings(scope, &bindings, provider_api, work)?;
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
            if source_position(scope, focus, state, definition.query, work)?
                && owner.replace(i).is_some()
            {
                return Err(Failure::Invalid);
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
    if require_all_definitions && query_count.contains(&0) {
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
    Ok(CheckedQueries {
        closure_origins,
        query_origins,
        verified_query_requests,
        verified_query_resumes,
        query_caller_contexts,
    })
}

/// Follow an initializer and a finite set of nominated registrations on every
/// reached predecessor. Only the checked initializer binding and exact
/// returned-ledger forwarding are supported; other calls lose the candidate.
/// Observations stay private to this focus until the enclosing validation
/// succeeds and the remaining provider premises are established.
pub(super) struct EncoderNomination<'a, 'arena> {
    pub(super) invocation: &'a crate::core::ledger_checker::codec::NominatedCodecCall<'arena>,
    pub(super) result: &'a crate::core::ledger_checker::codec::CodecResultMatch,
}

#[expect(
    clippy::too_many_arguments,
    reason = "The actual scope, control coordinates, checked definitions and work budget are distinct inputs"
)]
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
    encoder: Option<&EncoderNomination<'_, 'arena>>,
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
    let mut codec_roots = Vec::new();
    let mut codec_helpers = Vec::new();
    let mut codec_definitions = Vec::new();
    let mut codec_buffers = HashSet::new();
    if let Some(encoder) = encoder {
        use crate::core::ledger_checker::codec::CodecResultArm;
        let invocation = encoder.invocation;
        if invocation.provider_api() != initialization.provider_api()
            || encoder.result.call() != invocation.call()
            || !matches!(encoder.result.arm(0), Some(CodecResultArm::Encoded { .. }))
        {
            return Err(Failure::Invalid);
        }
        let descriptors = invocation.helpers(work).map_err(plan_rejection)?;
        charge(
            work,
            descriptors.len().checked_mul(3).ok_or(Failure::Resource)?,
        )?;
        codec_roots
            .try_reserve_exact(descriptors.len())
            .map_err(|_| Failure::Resource)?;
        codec_helpers
            .try_reserve_exact(descriptors.len())
            .map_err(|_| Failure::Resource)?;
        codec_definitions
            .try_reserve(descriptors.len())
            .map_err(|_| Failure::Resource)?;
        for descriptor in descriptors {
            let definition = DefinitionProvenance {
                query: descriptor.query(),
                binding: descriptor.root(),
                context: descriptor.context(),
                closure: descriptor.closure(),
            };
            if [
                definition.query,
                definition.binding,
                definition.context,
                definition.closure,
            ]
            .iter()
            .any(|node| node.arena() != scope.arena())
            {
                return Err(Failure::Invalid);
            }
            charge(
                work,
                definitions
                    .len()
                    .checked_add(codec_definitions.len())
                    .and_then(|n| n.checked_add(codec_helpers.len()))
                    .ok_or(Failure::Resource)?,
            )?;
            if definitions
                .iter()
                .any(|old| old.query == definition.query || old.closure == definition.closure)
                || codec_definitions.iter().any(|old: &DefinitionProvenance| {
                    old.query == definition.query || old.closure == definition.closure
                })
                || codec_helpers
                    .iter()
                    .any(|(binder, _)| *binder == descriptor.binder())
            {
                return Err(Failure::Invalid);
            }
            codec_definitions.push(definition);
            codec_roots.push(definition.binding);
            codec_helpers.push((descriptor.binder(), definition.closure));
        }
        for node in invocation.buffer_nodes(work).map_err(plan_rejection)? {
            if node.arena() != scope.arena() {
                return Err(Failure::Invalid);
            }
            charge(work, 1)?;
            codec_buffers
                .try_reserve(1)
                .map_err(|_| Failure::Resource)?;
            codec_buffers.insert(node.index().map_err(|_| Failure::Invalid)?);
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
    let (mut codec_calls, codec_closures, codec_nodes) = if encoder.is_some() {
        checked_call_roots(scope, &codec_roots, work)?
    } else {
        (HashSet::new(), HashSet::new(), HashSet::new())
    };
    if let Some(encoder) = encoder {
        let call = encoder.invocation.call();
        if call.arena() != scope.arena() {
            return Err(Failure::Invalid);
        }
        charge(work, 1)?;
        codec_calls.try_reserve(1).map_err(|_| Failure::Resource)?;
        codec_calls.insert(call.index().map_err(|_| Failure::Invalid)?);
    }
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
    let CheckedQueries {
        closure_origins,
        query_origins,
        verified_query_requests,
        verified_query_resumes,
        query_caller_contexts,
    } = checked_queries(
        scope,
        graph,
        focus,
        &checked_nodes,
        &definitions,
        initialization.provider_api(),
        default_handler,
        states,
        &edges,
        &details,
        &outgoing,
        true,
        work,
    )?;
    let codec_queries = if encoder.is_some() {
        Some(checked_queries(
            scope,
            graph,
            focus,
            &codec_nodes,
            &codec_definitions,
            initialization.provider_api(),
            default_handler,
            states,
            &edges,
            &details,
            &outgoing,
            true,
            work,
        )?)
    } else {
        None
    };
    let mut pending = VecDeque::new();
    let mut seen = HashSet::new();
    let mut requires_exclusive_update = false;
    let mut requires_peer_authentication = false;
    let mut transition_returns = Vec::new();
    let mut encoder_returns = Vec::new();
    #[cfg(test)]
    let mut saw_encoder_length = false;
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
            let encoding = matches!(phase, Phase::Encoding { .. });
            let mut source = checked_region_source(
                scope,
                graph,
                focus,
                before.position.code,
                if encoding {
                    &codec_nodes
                } else {
                    &checked_nodes
                },
                encoding.then_some(&codec_buffers),
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
        if let Phase::Current { context, .. } = phase
            && (query_caller_contexts
                .get(&id)
                .is_some_and(|saved| *saved != context)
                || (before.value_context != context
                    && query_caller_contexts.get(&id) != Some(&context)))
        {
            phase = Phase::Invalidated;
        }
        if let Phase::PreparingArgument { context, .. } = phase
            && (query_caller_contexts
                .get(&id)
                .is_some_and(|saved| *saved != context)
                || (before.value_context != context
                    && query_caller_contexts.get(&id) != Some(&context)))
        {
            return Err(Failure::Invalid);
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
            && before.value_context == context
            && !query_caller_contexts.contains_key(&id)
        {
            charge(work, 1)?;
            current.try_reserve(1).map_err(|_| Failure::Resource)?;
            if current
                .insert(id, (port, context, role))
                .is_some_and(|old| old != (port, context, role))
            {
                return Err(Failure::Invalid);
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
        let (active_requests, active_resumes, active_origins) =
            if matches!(phase, Phase::Encoding { .. }) {
                let queries = codec_queries.as_ref().ok_or(Failure::Invalid)?;
                (
                    &queries.verified_query_requests,
                    &queries.verified_query_resumes,
                    &queries.query_origins,
                )
            } else {
                (
                    &verified_query_requests,
                    &verified_query_resumes,
                    &query_origins,
                )
            };
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
                | Phase::Encoding { .. }
                | Phase::PreparingArgument { .. }
                | Phase::RunningArgument { .. }
        ) {
            match graph
                .code
                .get(before.position.code)
                .ok_or(Failure::Invalid)?
            {
                control::Control::Request(request) if !request.region_service => {
                    if !active_requests.contains(&id) {
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
                control::Control::Resume { .. } if !active_resumes.contains(&id) => {
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
                    | Phase::Encoding { .. }
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
            if matches!(phase, Phase::Encoding { .. })
                && let control::CompletionTransition::Call { target, .. } = transition
            {
                let entry = encoder.ok_or(Failure::Invalid)?.invocation.closure();
                if target == entry.index().map_err(|_| Failure::Invalid)? {
                    return Err(Failure::Invalid);
                }
                let length = encoder.and_then(|item| item.invocation.encoder_length());
                if let Some((binder, intrinsic)) = length
                    && intrinsic.index().ok() == Some(target)
                {
                    authenticate_encoder_length_call(
                        scope,
                        graph,
                        focus,
                        from,
                        to,
                        transition,
                        &codec_calls,
                        binder,
                        intrinsic,
                        work,
                    )?;
                    #[cfg(test)]
                    {
                        if !saw_encoder_length {
                            eprintln!("checked encoder bytes-length target: {target}");
                        }
                        saw_encoder_length = true;
                    }
                } else {
                    let queries = codec_queries.as_ref().ok_or(Failure::Invalid)?;
                    authenticate_body_call(
                        scope,
                        graph,
                        focus,
                        from,
                        to,
                        transition,
                        &codec_calls,
                        &codec_closures,
                        &codec_helpers,
                        &queries.closure_origins,
                        &queries.query_origins,
                        work,
                    )?;
                }
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
                    active_origins,
                    if matches!(phase, Phase::Encoding { .. }) {
                        &codec_nodes
                    } else {
                        &checked_nodes
                    },
                    region_source.ok_or(Failure::Invalid)?,
                    initialization.provider_api(),
                    matches!(phase, Phase::Encoding { .. }).then_some(&codec_buffers),
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
            if let Phase::EnteringDriver { context, .. } = phase
                && (before.value_context != context
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
                    ))
            {
                return Err(Failure::Invalid);
            }
            if matches!(transition, control::CompletionTransition::Call { .. }) {
                if matches!(phase, Phase::Encoding { .. }) {
                    // Every nested call was authenticated against the codec catalog above.
                } else if let Phase::PreparingArgument {
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
                } else if let Some(encoder) = encoder
                    && source_position(scope, focus, before, encoder.invocation.call(), work)?
                {
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
                    let invocation = encoder.invocation;
                    let witness = entered_call(
                        graph,
                        focus,
                        from,
                        to,
                        transition,
                        invocation.closure(),
                        work,
                    )?;
                    let actual = trace.call(witness, work)?;
                    let queries = codec_queries.as_ref().ok_or(Failure::Invalid)?;
                    authenticate_known_body_call(
                        scope,
                        focus,
                        actual,
                        &codec_calls,
                        &codec_closures,
                        &codec_helpers,
                        &queries.closure_origins,
                        &queries.query_origins,
                        work,
                    )?;
                    let (_, _, arguments, _) = focus.values().existing_call_ports(
                        actual.code,
                        actual.caller_value_context,
                        actual.expression,
                        actual.callee_value_context,
                        actual.creation,
                        work,
                    )?;
                    let argument = invocation.argument();
                    if argument.arena() != scope.arena() {
                        return Err(Failure::Invalid);
                    }
                    let argument_code = argument
                        .index()
                        .map_err(|_| Failure::Invalid)?
                        .checked_add(1)
                        .ok_or(Failure::Resource)?;
                    let (argument_port, _) =
                        focus
                            .values()
                            .existing_forward_ports(argument_code, context, work)?;
                    if arguments.len() != 1 || arguments[0].1 != argument_port {
                        return Err(Failure::Invalid);
                    }
                    // Any suspension still requires exclusive ownership of
                    // the checked current ledger until this call returns.
                    requires_exclusive_update = true;
                    next = Phase::Encoding {
                        port,
                        context,
                        ordinal,
                        role,
                        entry: from,
                        witness,
                    };
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
                        if source_position(scope, focus, before, receive.call(), work)?
                            && receive_site.replace((index, receive)).is_some()
                        {
                            return Err(Failure::Invalid);
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
                            if source_position(scope, focus, before, driver.call(), work)?
                                && driver_site.replace((index, driver)).is_some()
                            {
                                return Err(Failure::Invalid);
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
                                if source_position(scope, focus, before, site.call(), work)?
                                    && selected_site.replace((ordinal, site)).is_some()
                                {
                                    return Err(Failure::Invalid);
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
                                    )? && selected.replace((site, candidate)).is_some()
                                    {
                                        return Err(Failure::Invalid);
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
                if let Some((edge, native_return)) = returned
                    && let control::Frame::CallReturn { witness, .. } = edge.frame
                {
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
                        Phase::Encoding {
                            port,
                            context,
                            ordinal,
                            role,
                            entry,
                            witness: expected,
                        } if witness == expected => {
                            let invocation = encoder.ok_or(Failure::Invalid)?.invocation;
                            let call = matched_source_return(
                                scope,
                                focus,
                                &index,
                                from,
                                to,
                                edge,
                                native_return,
                                invocation.call(),
                                invocation.closure(),
                                work,
                            )?
                            .ok_or(Failure::Invalid)?;
                            if call.caller_value_context != context {
                                return Err(Failure::Invalid);
                            }
                            let returned = (entry, to, witness, call.result);
                            charge(
                                work,
                                encoder_returns
                                    .len()
                                    .checked_add(1)
                                    .ok_or(Failure::Resource)?,
                            )?;
                            if !encoder_returns.contains(&returned) {
                                encoder_returns
                                    .try_reserve(1)
                                    .map_err(|_| Failure::Resource)?;
                                encoder_returns.push(returned);
                            }
                            next = Phase::Current {
                                port,
                                context,
                                ordinal,
                                role,
                            };
                        }
                        Phase::Encoding { .. } => {
                            let call = trace.call(witness, work)?;
                            let length = encoder
                                .and_then(|item| item.invocation.encoder_length())
                                .filter(|(_, node)| node.index().ok() == Some(call.target));
                            if let Some((binder, intrinsic)) = length {
                                check_encoder_length_call(
                                    scope,
                                    focus,
                                    call,
                                    &codec_calls,
                                    binder,
                                    intrinsic,
                                    work,
                                )?;
                            } else if !codec_closures.contains(&call.target)
                                || call.expression != call.target
                            {
                                return Err(Failure::Invalid);
                            }
                            let before = states
                                .get(from)
                                .copied()
                                .flatten()
                                .ok_or(Failure::Invalid)?;
                            let after =
                                states.get(to).copied().flatten().ok_or(Failure::Invalid)?;
                            network_completion::matched_return_checked(
                                focus, edge, call, before, after, work,
                            )?;
                        }
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
                            let selected = registrations.get(ordinal).ok_or(Failure::Invalid)?.0;
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
                    if source_position(scope, focus, before, result.matching, work)?
                        && matching_site.replace(index).is_some()
                    {
                        return Err(Failure::Invalid);
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
        encoder_returns,
        #[cfg(test)]
        saw_encoder_length,
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
    encoder_returns: &'a [(usize, usize, usize, usize)],
    ledger_constructor: crate::types::ConstructorId,
    output_cons: crate::types::ConstructorId,
    requires_exclusive_update: bool,
    requires_peer_authentication: bool,
}

/// Untrusted coordinates for a direct match of the current ledger's output
/// head followed by a call. State identifiers belong only to this focus.
#[allow(dead_code)]
#[derive(Clone, Copy)]
pub(super) struct OutputHeadCall {
    pub(super) ledger_state: usize,
    pub(super) output_state: usize,
    pub(super) call_state: usize,
    pub(super) ledger_match: crate::core::NodeId,
    pub(super) ledger_arm: usize,
    pub(super) output_match: crate::core::NodeId,
    pub(super) output_arm: usize,
    pub(super) call: crate::core::NodeId,
    pub(super) role: crate::resolved::BinderId,
}

/// The selected call argument is the selected head of this current ledger's
/// outputs. An encoder consumer must authenticate this exact state and value
/// context in the borrowed focus, not just the source call coordinate. This
/// says nothing about dequeue, encoding, sending or a peer.
#[allow(dead_code)]
pub(super) struct CheckedCurrentOutputArgument<'a> {
    _focus: &'a control::CompletionFocus<'a>,
    pub(super) owner: crate::core::NodeId,
    pub(super) entry: crate::core::NodeId,
    pub(super) side: u8,
    pub(super) call: crate::core::NodeId,
    pub(super) argument: crate::core::NodeId,
    pub(super) call_state: usize,
    pub(super) value_context: usize,
    pub(super) role: crate::resolved::BinderId,
    ledger_input: crate::core::NodeId,
    result_match: Option<crate::core::NodeId>,
    ledger_code: usize,
    ledger_arm: usize,
    output_code: usize,
    output_arm: usize,
    pub(super) requires_history_and_peer_allocator: bool,
    pub(super) requires_exclusive_update: bool,
    pub(super) requires_peer_authentication: bool,
}

/// A focus-local successful encoder result. Its private port can only be
/// inspected while the same focus is borrowed; it grants no send authority.
#[allow(dead_code)]
pub(super) struct CheckedEncodedOutput<'a, 'focus> {
    _output: &'a CheckedCurrentOutputArgument<'focus>,
    call_state: usize,
    return_witness: usize,
    result_state: usize,
    bytes_binder: crate::resolved::BinderId,
    bytes_port: usize,
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
    #[cfg_attr(
        not(test),
        expect(dead_code, reason = "reserved for the N4 same-focus consumer")
    )]
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

    /// Check the direct source shape `match ledger { Ledger(_, _, outputs) =>
    /// match outputs { OutputCons(head, _) => call(head), ... } }` or an
    /// immediately matched call result at the actual selected edges. The
    /// caller must separately authenticate the nominated call and its result
    /// match in this focus.
    #[cfg_attr(
        not(test),
        expect(dead_code, reason = "reserved for the N4 same-focus consumer")
    )]
    pub(super) fn checked_output_head_call(
        &self,
        nominated: &OutputHeadCall,
        work: &mut TypeWorkBudget,
    ) -> Result<CheckedCurrentOutputArgument<'_>, Failure> {
        use crate::core::{CorePatternKind, EffectExprKind, PureComputation, PureExprKind};

        let nodes = self.scope.nodes();
        let matching = |id: crate::core::NodeId| {
            if id.arena() != self.scope.arena() {
                return Err(Failure::Invalid);
            }
            let index = id.index().map_err(|_| Failure::Invalid)?;
            match nodes.get(index).map(|node| &node.kind) {
                Some(EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Match(
                    matching,
                )))) => Ok(matching),
                _ => Err(Failure::Invalid),
            }
        };
        charge(work, 3)?;
        let ledger = matching(nominated.ledger_match)?;
        let output = matching(nominated.output_match)?;
        let ledger_arm = ledger
            .arms()
            .get(nominated.ledger_arm)
            .ok_or(Failure::Invalid)?;
        let output_arm = output
            .arms()
            .get(nominated.output_arm)
            .ok_or(Failure::Invalid)?;
        if ledger_arm.body() != nominated.output_match {
            return Err(Failure::Invalid);
        }
        let result_match = if output_arm.body() == nominated.call {
            None
        } else {
            let wrapper = matching(output_arm.body())?;
            if wrapper.scrutinee() != nominated.call {
                return Err(Failure::Invalid);
            }
            Some(output_arm.body())
        };
        let CorePatternKind::Constructor {
            constructor,
            payload: Some(payload),
        } = &ledger_arm.pattern().kind
        else {
            return Err(Failure::Invalid);
        };
        if *constructor != self.ledger_constructor {
            return Err(Failure::Invalid);
        }
        let CorePatternKind::Tuple(fields) = &payload.kind else {
            return Err(Failure::Invalid);
        };
        let [first, second, outputs] = fields.as_ref() else {
            return Err(Failure::Invalid);
        };
        let (
            CorePatternKind::Wildcard,
            CorePatternKind::Wildcard,
            CorePatternKind::Binder(outputs),
        ) = (&first.kind, &second.kind, &outputs.kind)
        else {
            return Err(Failure::Invalid);
        };
        let CorePatternKind::Constructor {
            constructor,
            payload: Some(payload),
        } = &output_arm.pattern().kind
        else {
            return Err(Failure::Invalid);
        };
        if *constructor != self.output_cons {
            return Err(Failure::Invalid);
        }
        let CorePatternKind::Tuple(fields) = &payload.kind else {
            return Err(Failure::Invalid);
        };
        let [head, tail] = fields.as_ref() else {
            return Err(Failure::Invalid);
        };
        let (CorePatternKind::Binder(head), CorePatternKind::Wildcard) = (&head.kind, &tail.kind)
        else {
            return Err(Failure::Invalid);
        };
        let variable = |id: crate::core::NodeId| {
            if id.arena() != self.scope.arena() {
                return Err(Failure::Invalid);
            }
            let index = id.index().map_err(|_| Failure::Invalid)?;
            match nodes.get(index).map(|node| &node.kind) {
                Some(EffectExprKind::Pure(PureExprKind::Variable(variable))) => {
                    Ok(variable.binder())
                }
                _ => Err(Failure::Invalid),
            }
        };
        if variable(ledger.scrutinee())? != nominated.role
            || variable(output.scrutinee())? != outputs.id()
        {
            return Err(Failure::Invalid);
        }
        if nominated.call.arena() != self.scope.arena() {
            return Err(Failure::Invalid);
        }
        let call_index = nominated.call.index().map_err(|_| Failure::Invalid)?;
        let Some(EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Apply(call)))) =
            nodes.get(call_index).map(|node| &node.kind)
        else {
            return Err(Failure::Invalid);
        };
        let argument = call.argument();
        if variable(argument)? != head.id() {
            return Err(Failure::Invalid);
        }

        let trace = self.focus.trace()?;
        let before_ledger = trace.state(nominated.ledger_state, work)?;
        let before_output = trace.state(nominated.output_state, work)?;
        let before_call = trace.state(nominated.call_state, work)?;
        if (before_ledger.context, before_ledger.value_context)
            != (before_output.context, before_output.value_context)
            || (before_output.context, before_output.value_context)
                != (before_call.context, before_call.value_context)
            || !source_position(
                self.scope,
                self.focus,
                before_output,
                nominated.output_match,
                work,
            )?
            || !source_position(self.scope, self.focus, before_call, nominated.call, work)?
        {
            return Err(Failure::Invalid);
        }
        for (state, site) in [
            (nominated.ledger_state, nominated.ledger_match),
            (nominated.output_state, nominated.output_match),
            (nominated.call_state, nominated.call),
        ] {
            self.checked_input(state, site, ledger.scrutinee(), nominated.role, work)?
                .ok_or(Failure::Invalid)?;
        }
        let mut selected = [false; 2];
        trace.visit_edges(work, |from, _, transition, _| {
            if transition
                == (control::CompletionTransition::Choice {
                    ordinal: nominated.ledger_arm,
                })
                && from == nominated.ledger_state
            {
                selected[0] = true;
            }
            if transition
                == (control::CompletionTransition::Choice {
                    ordinal: nominated.output_arm,
                })
                && from == nominated.output_state
            {
                selected[1] = true;
            }
            Ok(())
        })?;
        if selected != [true, true] {
            return Err(Failure::Invalid);
        }
        let mut address = before_call.stack;
        if let Some(result_match) = result_match {
            charge(work, before_call.heap.len())?;
            let mut edges = before_call
                .heap
                .iter()
                .filter(|edge| edge.address == address);
            let edge = edges.next().ok_or(Failure::Invalid)?;
            let code = result_match
                .index()
                .map_err(|_| Failure::Invalid)?
                .checked_add(1)
                .ok_or(Failure::Resource)?;
            if edges.next().is_some()
                || edge.frame
                    != (control::Frame::Next {
                        position: control::Position { code, next: 1 },
                        context: before_call.context,
                        value_context: before_call.value_context,
                    })
            {
                return Err(Failure::Invalid);
            }
            address = edge.next;
        }
        for (code, ordinal) in [
            (before_output.position.code, nominated.output_arm),
            (before_ledger.position.code, nominated.ledger_arm),
        ] {
            charge(work, before_call.heap.len())?;
            let mut edges = before_call
                .heap
                .iter()
                .filter(|edge| edge.address == address);
            let edge = edges.next().ok_or(Failure::Invalid)?;
            if edges.next().is_some()
                || edge.frame
                    != (control::Frame::CaseReturn {
                        code,
                        ordinal,
                        context: before_call.context,
                        value_context: before_call.value_context,
                    })
            {
                return Err(Failure::Invalid);
            }
            address = edge.next;
        }
        let values = self.focus.values();
        let project =
            |state: &control::State, ordinal, constructor, field, work: &mut TypeWorkBudget| {
                let (source, _, _) = values
                    .existing_choice(state.position.code, state.value_context, work)?
                    .ok_or(Failure::Invalid)?;
                let bindings = values.existing_arm_bindings(
                    state.position.code,
                    ordinal,
                    state.value_context,
                    work,
                )?;
                let [(binding, projection)] = bindings.as_slice() else {
                    return Err(Failure::Invalid);
                };
                let (payload, actual_field, actual_constructor) =
                    values.existing_pattern_projection(*projection, work)?;
                let (actual_source, payload_field, payload_constructor) =
                    values.existing_pattern_projection(payload, work)?;
                if actual_source != source
                    || payload_field != 0
                    || payload_constructor != Some(constructor)
                    || actual_field != field
                    || actual_constructor.is_some()
                {
                    return Err(Failure::Invalid);
                }
                Ok((source, *binding))
            };
        let (ledger_source, outputs_port) = project(
            before_ledger,
            nominated.ledger_arm,
            self.ledger_constructor,
            2,
            work,
        )?;
        let (output_source, head_port) = project(
            before_output,
            nominated.output_arm,
            self.output_cons,
            0,
            work,
        )?;
        let output_code = output
            .scrutinee()
            .index()
            .map_err(|_| Failure::Invalid)?
            .checked_add(1)
            .ok_or(Failure::Resource)?;
        let (actual_output, output_origin) =
            values.existing_forward_ports(output_code, before_output.value_context, work)?;
        let argument_code = argument
            .index()
            .map_err(|_| Failure::Invalid)?
            .checked_add(1)
            .ok_or(Failure::Resource)?;
        let (_, argument_origin) =
            values.existing_forward_ports(argument_code, before_call.value_context, work)?;
        let input_code = ledger
            .scrutinee()
            .index()
            .map_err(|_| Failure::Invalid)?
            .checked_add(1)
            .ok_or(Failure::Resource)?;
        let (actual_ledger, _) =
            values.existing_forward_ports(input_code, before_ledger.value_context, work)?;
        if actual_ledger != ledger_source
            || actual_output != output_source
            || output_origin != outputs_port
            || argument_origin != head_port
        {
            return Err(Failure::Invalid);
        }
        Ok(CheckedCurrentOutputArgument {
            _focus: self.focus,
            owner: self.scope.owner(),
            entry: self.entry,
            side: self.side,
            call: nominated.call,
            argument,
            call_state: nominated.call_state,
            value_context: before_call.value_context,
            role: nominated.role,
            ledger_input: ledger.scrutinee(),
            result_match,
            ledger_code: before_ledger.position.code,
            ledger_arm: nominated.ledger_arm,
            output_code: before_output.position.code,
            output_arm: nominated.output_arm,
            requires_history_and_peer_allocator: true,
            requires_exclusive_update: self.requires_exclusive_update,
            requires_peer_authentication: self.requires_peer_authentication,
        })
    }

    /// Bind a checked output occurrence to the actual matched normal return
    /// and selected Encoded payload. Failure arms yield no such witness.
    #[cfg_attr(
        not(test),
        expect(dead_code, reason = "reserved for the N4 same-focus consumer")
    )]
    pub(super) fn checked_encoded_output<'query, 'focus>(
        &'query self,
        output: &'query CheckedCurrentOutputArgument<'focus>,
        result: &crate::core::ledger_checker::codec::CodecResultMatch,
        state_id: usize,
        work: &mut TypeWorkBudget,
    ) -> Result<CheckedEncodedOutput<'query, 'focus>, Failure> {
        use crate::core::ledger_checker::codec::CodecResultArm;
        use crate::core::{CorePatternKind, EffectExprKind, PureComputation, PureExprKind};
        if !std::ptr::eq(output._focus, self.focus)
            || result.call() != output.call
            || output.result_match != Some(result.matching())
        {
            return Err(Failure::Invalid);
        }
        let Some(CodecResultArm::Encoded { bytes, .. }) = result.arm(0) else {
            return Err(Failure::Invalid);
        };
        let trace = self.focus.trace()?;
        let choice = trace.state(state_id, work)?;
        if choice.value_context != output.value_context
            || !source_position(self.scope, self.focus, choice, result.matching(), work)?
            || self
                .checked_input(
                    state_id,
                    result.matching(),
                    output.ledger_input,
                    output.role,
                    work,
                )?
                .is_none()
        {
            return Err(Failure::Invalid);
        }
        let match_index = result.matching().index().map_err(|_| Failure::Invalid)?;
        let Some(EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Match(matching)))) =
            self.scope.nodes().get(match_index).map(|node| &node.kind)
        else {
            return Err(Failure::Invalid);
        };
        let arm = matching.arms().first().ok_or(Failure::Invalid)?;
        let CorePatternKind::Constructor {
            constructor,
            payload: Some(payload),
        } = &arm.pattern().kind
        else {
            return Err(Failure::Invalid);
        };
        if !matches!(&payload.kind, CorePatternKind::Binder(binder) if binder.id() == bytes) {
            return Err(Failure::Invalid);
        }
        // Select only actual returns from this call occurrence which reach
        // the nominated Choice through its saved Match continuation. Distinct
        // return states may represent different encoder branches.
        charge(work, self.encoder_returns.len())?;
        let code = match_index.checked_add(1).ok_or(Failure::Resource)?;
        let mut selected_return = None;
        for &(entry, returned, witness, result_port) in self.encoder_returns {
            if entry != output.call_state {
                continue;
            }
            let returned_state = trace.state(returned, work)?;
            charge(work, returned_state.heap.len())?;
            let mut top = returned_state
                .heap
                .iter()
                .filter(|edge| edge.address == returned_state.stack);
            let Some(&next) = top.next() else { continue };
            if top.next().is_some()
                || next.frame
                    != (control::Frame::Next {
                        position: control::Position { code, next: 1 },
                        context: choice.context,
                        value_context: choice.value_context,
                    })
            {
                continue;
            }
            let mut details = Vec::new();
            trace.visit_details(work, |id, detail, work| {
                if detail == control::CompletionDetail::Return(next) {
                    charge(work, 1)?;
                    details.try_reserve(1).map_err(|_| Failure::Resource)?;
                    details.push(id);
                }
                Ok(())
            })?;
            let mut intermediates = Vec::new();
            let mut selected = false;
            trace.visit_edges(work, |from, to, transition, work| {
                charge(work, details.len())?;
                if from == returned
                    && matches!(transition, control::CompletionTransition::Detail(id) if details.contains(&id))
                {
                    charge(work, 1)?;
                    intermediates.try_reserve(1).map_err(|_| Failure::Resource)?;
                    intermediates.push(to);
                }
                if from == state_id
                    && transition == (control::CompletionTransition::Choice { ordinal: 0 })
                {
                    selected = true;
                }
                Ok(())
            })?;
            let mut connected = false;
            trace.visit_edges(work, |from, to, transition, work| {
                charge(work, intermediates.len())?;
                if intermediates.contains(&from)
                    && to == state_id
                    && transition == (control::CompletionTransition::Sequence { ordinal: 1 })
                {
                    connected = true;
                }
                Ok(())
            })?;
            if selected && connected {
                let actual = (witness, result_port);
                if selected_return
                    .replace(actual)
                    .is_some_and(|old| old != actual)
                {
                    return Err(Failure::Invalid);
                }
            }
        }
        let (witness, result_port) = selected_return.ok_or(Failure::Invalid)?;
        let (scrutinee, _, _) = self
            .focus
            .values()
            .existing_choice(choice.position.code, choice.value_context, work)?
            .ok_or(Failure::Invalid)?;
        if scrutinee != result_port {
            return Err(Failure::Invalid);
        }
        let bindings = self.focus.values().existing_arm_bindings(
            choice.position.code,
            0,
            choice.value_context,
            work,
        )?;
        let [(bytes_port, projection)] = bindings.as_slice() else {
            return Err(Failure::Invalid);
        };
        let (source, field, projected) = self
            .focus
            .values()
            .existing_pattern_projection(*projection, work)?;
        if source != result_port || field != 0 || projected != Some(*constructor) {
            return Err(Failure::Invalid);
        }
        let mut address = choice.stack;
        for (code, ordinal) in [
            (output.output_code, output.output_arm),
            (output.ledger_code, output.ledger_arm),
        ] {
            charge(work, choice.heap.len())?;
            let mut edges = choice.heap.iter().filter(|edge| edge.address == address);
            let edge = edges.next().ok_or(Failure::Invalid)?;
            if edges.next().is_some()
                || edge.frame
                    != (control::Frame::CaseReturn {
                        code,
                        ordinal,
                        context: choice.context,
                        value_context: choice.value_context,
                    })
            {
                return Err(Failure::Invalid);
            }
            address = edge.next;
        }
        Ok(CheckedEncodedOutput {
            _output: output,
            call_state: output.call_state,
            return_witness: witness,
            result_state: state_id,
            bytes_binder: bytes,
            bytes_port: *bytes_port,
        })
    }
}

#[expect(
    clippy::large_enum_variant,
    reason = "Keep checked witnesses inline without adding an uncharged allocation"
)]
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
    with_observed_ledger_plan_and_encoder(
        scope, graph, worker, program, linked, plan, None, work, inspect,
    )
}

#[expect(
    clippy::too_many_arguments,
    reason = "The optional encoder is checked in the same worker focus"
)]
pub(super) fn with_observed_ledger_plan_and_encoder<R>(
    scope: &NetworkNativeIdentityScope<'_>,
    graph: &SummaryGraph,
    worker: &control::Analysis<'_>,
    program: &crate::core::UnvalidatedEffectProgram,
    linked: &crate::evidence_validation::ValidatedInterfaceProgram,
    plan: &crate::core::ledger_checker::plan::LedgerPlan<'_>,
    encoder: Option<&EncoderNomination<'_, '_>>,
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
        encoder,
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
            encoder_returns: &observed.encoder_returns,
            ledger_constructor: plan.initialization_constructors.ledger,
            output_cons: plan.initialization_constructors.outputs_more,
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
    fn current_output_head_is_the_direct_call_argument() {
        let source = include_str!("../../../tests/fixtures/n3-ledger-worker.ash");
        let source = source.replace(
            "    let ignored = match reserve_job (initial (), 0, LedgerTypes.Root, 0, payload) {\n        (successor, status) => successor\n    }",
            "    let decoy = LedgerTypes.AckOut(LedgerTypes.NoParent, LedgerTypes.Root)\n    let original = initial ()\n    let ignored = match reserve_job (original, 0, LedgerTypes.Root, 0, payload) {\n        (successor, status) => match successor {\n            Ledger(_, _, outputs) => match outputs {\n                NoOutputs => sink_empty decoy\n                OutputCons(head, _) => sink_output head\n            }\n        }\n    }",
        ).replace(
            "main : Unit -> Unit",
            "sink_output : LedgerTypes.Envelope -> Unit\nsink_output _ = ()\nsink_empty : LedgerTypes.Envelope -> Unit\nsink_empty _ = ()\n\nmain : Unit -> Unit",
        );
        assert!(source.contains("OutputCons(head, _) => sink_output head"));
        run_worker_case(&source, true, false, None, None);
        let stale = source.replace(
            "match successor {\n            Ledger",
            "match original {\n            Ledger",
        );
        assert_ne!(source, stale);
        run_worker_case(&stale, true, false, None, None);
        let wrong_head = source.replace("sink_output head", "sink_output decoy");
        assert_ne!(source, wrong_head);
        run_worker_case(&wrong_head, true, false, None, None);
        let matched = source
            .replace(
                "sink_output : LedgerTypes.Envelope -> Unit\nsink_output _ = ()",
                "type SinkResult =\n    Encoded\n    | EncodeFailed\nsink_output : LedgerTypes.Envelope -> SinkResult\nsink_output _ = Encoded",
            )
            .replace(
                "OutputCons(head, _) => sink_output head",
                "OutputCons(head, _) => match sink_output head {\n                    Encoded => ()\n                    EncodeFailed => ()\n                }",
            )
            .replace(
                "    let ignored = match reserve_job (original, 0, LedgerTypes.Root, 0, payload) {\n        (successor, status) => match successor {",
                "    let (successor, status) = reserve_job (original, 0, LedgerTypes.Root, 0, payload)\n    let ignored = match successor {",
            )
            .replace("            }\n        }\n    }\n    ()\n}", "            }\n    }\n    ()\n}");
        assert_ne!(source, matched);
        run_worker_case(&matched, true, false, None, None);
    }

    #[test]
    fn actual_encoder_receives_the_current_output_head() {
        let source = include_str!("../../../tests/fixtures/n3-ledger-worker.ash");
        let source = source.replace(
            "import network_types as LedgerTypes",
            "import network_types as LedgerTypes\nimport network_codec as Codec",
        ).replace(
            "worker (endpoint, payload) = {\n    let received = Network.try_receive endpoint\n    let ignored = match reserve_job (initial (), 0, LedgerTypes.Root, 0, payload) {\n        (successor, status) => successor\n    }\n    ()\n}",
            "worker (endpoint, payload) = {\n    let received = Network.try_receive endpoint\n    let original = initial ()\n    let (successor, status) = reserve_job (original, 0, LedgerTypes.Root, 0, payload)\n    let encoded_success = match successor {\n        Ledger(_, _, outputs) => match outputs {\n            NoOutputs => false\n            OutputCons(head, _) => match Codec.encode head {\n                Codec.Encoded(bytes) => true\n                Codec.EncodeFailed => false\n            }\n        }\n    }\n    ()\n}",
        );
        assert!(source.contains("match Codec.encode head"));
        run_worker_case(&source, true, false, None, None);
        let stale = source.replace(
            "match successor {\n        Ledger",
            "match original {\n        Ledger",
        );
        assert_ne!(source, stale);
        run_worker_case(&stale, true, false, None, None);
        let wrong_head = source
            .replace("    let original = initial ()", "    let decoy = LedgerTypes.AckOut(LedgerTypes.NoParent, LedgerTypes.Root)\n    let original = initial ()")
            .replace("Codec.encode head", "Codec.encode decoy");
        assert_ne!(source, wrong_head);
        run_worker_case(&wrong_head, true, false, None, None);
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
    fn imported_ledger_and_transformed_core_are_rechecked() {
        let source = completed_worker(include_str!("../../../tests/fixtures/n3-ledger-worker.ash"));
        let (entry, declarations) = source
            .split_once("\n\ntype Child = ")
            .expect("ledger fixture boundary");
        let entry = format!("import ledger_helper as Ledger\n{entry}")
            .replace("reserve_job (", "Ledger.reserve_job (")
            .replace("initial ()", "Ledger.initial ()");
        let declarations = format!("type Child = {declarations}");
        let declarations = declarations
            .replace("\ntype ", "\npub type ")
            .replacen("type Child =", "pub type Child =", 1)
            .replace("\ninitial :", "\npub initial :")
            .replace("\nreserve_job :", "\npub reserve_job :");
        let module = format!("import network_types as LedgerTypes\n{declarations}");
        run_worker_case_variant(
            &entry,
            true,
            false,
            None,
            Some(true),
            None,
            FixtureVariation {
                ledger_module: Some(&module),
                transform: false,
                expect_bad_helper: false,
            },
        );
        run_worker_case_variant(
            &entry,
            true,
            false,
            None,
            Some(true),
            None,
            FixtureVariation {
                ledger_module: Some(&module),
                transform: true,
                expect_bad_helper: false,
            },
        );
        let changed = module.replace(
            "Ledger(next + 1, remaining, outgoing)",
            "Ledger(next + 2, remaining, outgoing)",
        );
        assert_ne!(changed, module);
        run_worker_case_variant(
            &entry,
            true,
            false,
            None,
            None,
            None,
            FixtureVariation {
                ledger_module: Some(&changed),
                transform: false,
                expect_bad_helper: true,
            },
        );
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
        run_worker_case_variant(
            source,
            expect_current,
            two_calls,
            transition_case,
            exercise_plan,
            budget,
            FixtureVariation {
                ledger_module: None,
                transform: false,
                expect_bad_helper: false,
            },
        )
    }

    struct FixtureVariation<'a> {
        ledger_module: Option<&'a str>,
        transform: bool,
        expect_bad_helper: bool,
    }

    fn run_worker_case_variant(
        source: &str,
        expect_current: bool,
        two_calls: bool,
        transition_case: Option<bool>,
        exercise_plan: Option<bool>,
        budget: Option<(usize, usize, bool)>,
        variation: FixtureVariation<'_>,
    ) -> Option<usize> {
        let FixtureVariation {
            ledger_module,
            transform,
            expect_bad_helper,
        } = variation;
        let (program, provenance, linked) = match ledger_module {
            Some(module) => {
                super::super::tests::retained_drain_fixture_with_ledger_module(source, module)
            }
            None => super::super::tests::retained_drain_fixture_with_linked(source),
        };
        if transform {
            let sources: Vec<_> = provenance.iter().map(|(_, source)| source).collect();
            let relations: Vec<_> = provenance
                .iter()
                .map(|(module, source)| (*module, source.id()))
                .collect();
            let mut original_work = TypeWorkBudget::with_limit(500_000_000);
            let checked = crate::core::validate::validate_effect_modules_linked_with_work(
                program,
                &sources,
                &relations,
                &linked,
                &mut original_work,
            )
            .expect("original linked Core validates before transformation");
            assert!(
                matches!(
                    crate::core::transform::identity_effect_traversal(&checked),
                    Err(crate::core::transform::TransformError::InvalidValidatedInput)
                ),
                "Network effect transformation must reject before publishing a ledger fact"
            );
            return None;
        }
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
            if source.contains("import network_codec as Codec")
                && matches!(
                    name,
                    "Encoded" | "EncodeFailed" | "Parts" | "Negative" | "ByteAt" | "InvalidIndex"
                )
            {
                return program
                    .registry
                    .constructors()
                    .iter()
                    .find(|item| {
                        let module = item.id.owner().module();
                        item.spelling == name
                            && match name {
                                "Parts" | "Negative" => module.is_builtin_integer(),
                                "ByteAt" | "InvalidIndex" => module.is_builtin_bytes(),
                                _ => provenance.iter().any(|(id, file)| {
                                    *id == module
                                        && file.text()
                                            == include_str!("../../../libraries/network_codec.ash")
                                }),
                            }
                    })
                    .expect("actual codec constructor")
                    .id;
            }
            let module = if matches!(
                name,
                "Root" | "Work" | "NoParent" | "Parent" | "WorkOut" | "AckOut"
            ) {
                network_types_module
            } else if let Some(module_source) = ledger_module {
                provenance
                    .iter()
                    .find_map(|(module, source)| {
                        (source.text() == module_source).then_some(*module)
                    })
                    .expect("independent linked ledger module")
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
        let binding = if two_calls
            || recursive_driver
            || source.contains("sink_output :")
            || source.contains("import network_codec as Codec")
        {
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
        if expect_bad_helper {
            let initial = candidate("initial");
            let initialization_call = program
                .nodes
                .iter()
                .enumerate()
                .find_map(|(index, node)| {
                    let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Apply(
                        app,
                    ))) = &node.kind
                    else {
                        return None;
                    };
                    let EffectExprKind::Pure(PureExprKind::Variable(variable)) =
                        &program.nodes.get(app.function().index().ok()?)?.kind
                    else {
                        return None;
                    };
                    (variable.binder() == initial.binder)
                        .then(|| NodeId::new(program.arena, index as u32))
                })
                .expect("actual imported initializer call");
            let nominations = [crate::core::ledger_checker::plan::RegistrationNomination {
                call,
                result_match: matching(call),
                definitions,
                constructors,
            }];
            let plans = [crate::core::ledger_checker::plan::LedgerPlan {
                owner,
                side: 1,
                initialization_call,
                initialization: initial,
                initialization_constructors: state,
                initialization_role: InitializationRole::Root,
                initialization_binding: None,
                registrations: &nominations,
                transitions: &[],
                drivers: &[],
                receives: &[],
            }];
            let sources: Vec<_> = provenance.iter().map(|(_, source)| source).collect();
            let relations: Vec<_> = provenance
                .iter()
                .map(|(module, source)| (*module, source.id()))
                .collect();
            let mut allowance = TypeWorkBudget::with_limit(500_000_000);
            let outcome = crate::core::validate::validate_effect_modules_linked_with_ledger_plans(
                program,
                &sources,
                &relations,
                &linked,
                &plans,
                &mut allowance,
            );
            assert!(
                matches!(outcome, Err(error) if error.reason() == crate::core::validate::ValidationReason::Registry),
                "changed imported helper must reject before publication"
            );
            return None;
        }
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
            while let EffectExprKind::Pure(PureExprKind::Computation(
                PureComputation::TypeAbstraction(abstraction),
            )) = &program.nodes[body.index().unwrap()].kind
            {
                body = abstraction.body();
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
        let encoder = if source.contains("import network_codec as Codec") {
            use crate::core::ledger_checker::codec::{
                EncoderConstructors, EncoderDefinitions, check_encode_result_match,
                nominate_encode_call,
            };
            let encode = candidate("encode");
            let encode_call = program
                .nodes
                .iter()
                .enumerate()
                .find_map(|(index, node)| {
                    let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Apply(
                        app,
                    ))) = &node.kind
                    else {
                        return None;
                    };
                    let EffectExprKind::Pure(PureExprKind::Variable(variable)) =
                        &program.nodes.get(app.function().index().ok()?)?.kind
                    else {
                        return None;
                    };
                    (variable.binder() == encode.binder)
                        .then(|| NodeId::new(program.arena, index as u32))
                })
                .expect("actual encoder call");
            let definitions = EncoderDefinitions {
                encode,
                work: candidate("encode_work"),
                ack: candidate("encode_ack"),
                work_parent: candidate("encode_work_parent"),
                work_payload: candidate("encode_work_payload"),
                copy: candidate("copy_bytes"),
                address: candidate("write_address"),
                identity: candidate("write_identity"),
                nat: candidate("write_nat"),
                digits: candidate("write_digits"),
                append: candidate("append"),
                split: candidate("split_base256"),
                append_byte: candidate("append_byte"),
                empty: candidate("empty"),
                length: candidate("length"),
                at: candidate("at"),
            };
            let constructors = EncoderConstructors {
                root: constructor("Root"),
                work_id: constructor("Work"),
                no_parent: constructor("NoParent"),
                parent: constructor("Parent"),
                work_out: constructor("WorkOut"),
                ack_out: constructor("AckOut"),
                encoded: constructor("Encoded"),
                encode_failed: constructor("EncodeFailed"),
                split_parts: constructor("Parts"),
                split_negative: constructor("Negative"),
                byte_at: constructor("ByteAt"),
                invalid_index: constructor("InvalidIndex"),
            };
            let invocation = nominate_encode_call(
                &program,
                &linked,
                encode_call,
                definitions,
                constructors,
                &mut work,
            )
            .expect("actual linked encoder");
            let result =
                check_encode_result_match(&program, &invocation, matching(encode_call), &mut work)
                    .expect("actual encoder result match");
            Some((invocation, result))
        } else {
            None
        };
        let encoder_nomination = encoder
            .as_ref()
            .map(|(invocation, result)| EncoderNomination { invocation, result });
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
                            encoder_nomination.as_ref(),
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
                        if source.contains("sink_output :") || encoder.is_some() {
                            let sink = encoder.as_ref().map_or_else(|| candidate("sink_output").binder, |_| candidate("encode").binder);
                            let sink_call = program.nodes.iter().enumerate().find_map(|(index, node)| {
                                let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Apply(app))) = &node.kind else { return None };
                                let EffectExprKind::Pure(PureExprKind::Variable(variable)) = &program.nodes.get(app.function().index().ok()?)?.kind else { return None };
                                (variable.binder() == sink).then(|| NodeId::new(program.arena, index as u32))
                            }).expect("actual output sink call");
                            let find_parent_match = |body: NodeId| {
                                program.nodes.iter().enumerate().find_map(|(index, node)| {
                                    let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Match(matching))) = &node.kind else { return None };
                                    matching.arms().iter().position(|arm| arm.body() == body)
                                        .map(|arm| (NodeId::new(program.arena, index as u32), arm))
                                }).expect("actual enclosing match")
                            };
                            let sink_body = if let Some((_, result)) = &encoder {
                                result.matching()
                            } else if source.contains("type SinkResult =") {
                                program.nodes.iter().enumerate().find_map(|(index, node)| {
                                    let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Match(matching))) = &node.kind else { return None };
                                    (matching.scrutinee() == sink_call).then(|| NodeId::new(program.arena, index as u32))
                                }).expect("actual sink result match")
                            } else {
                                sink_call
                            };
                            let (output_match, output_arm) = find_parent_match(sink_body);
                            let (ledger_match, ledger_arm) = find_parent_match(output_match);
                            let plan = crate::core::ledger_checker::plan::LedgerPlan {
                                owner, side: 1, initialization_call: plan_initial_call,
                                initialization: plan_initial, initialization_constructors: state,
                                initialization_role: InitializationRole::Root,
                                initialization_binding: binding.map(|(node, _)| node),
                                registrations: std::slice::from_ref(&plan_registration), transitions: &[], drivers: &[],
                                receives: receive_plan.as_slice(),
                            };
                            let stale = source.contains("match original {\n            Ledger")
                                || source.contains("match original {\n        Ledger")
                                || source.contains("sink_output decoy") || source.contains("Codec.encode decoy");
                            let (_, ()) = with_observed_ledger_plan_and_encoder(
                                scope, graph, worker, &program, &linked, &plan, encoder_nomination.as_ref(), budget,
                                |query, work| {
                                    let states = query.focus.trace()?.indexed_states(work)?;
                                    let mut positions = [Vec::new(), Vec::new(), Vec::new()];
                                    for &(id, _, _, _) in query.current {
                                        let actual = states.get(id).copied().flatten().ok_or(Failure::Invalid)?;
                                        for (slot, node) in [ledger_match, output_match, sink_call].into_iter().enumerate() {
                                            if source_position(scope, query.focus, actual, node, work)? {
                                                positions[slot].push(id);
                                            }
                                        }
                                    }
                                    if !stale {
                                        if encoder.is_some() {
                                            assert!(observed.saw_encoder_length, "the actual encoder must call checked bytes length");
                                        }
                                        assert!(positions.iter().all(|items| !items.is_empty()), "all three source sites must be reached with a current ledger");
                                    }
                                    let mut found = false;
                                    let mut encoded = false;
                                    for &ledger_state in &positions[0] {
                                        for &output_state in &positions[1] {
                                            for &call_state in &positions[2] {
                                                let nomination = OutputHeadCall {
                                                    ledger_state, output_state, call_state, ledger_match, ledger_arm,
                                                    output_match, output_arm, call: sink_call,
                                                    role: registrations[0].1.ledger,
                                                };
                                                let before = work.used();
                                                match query.checked_output_head_call(&nomination, work) {
                                                    Ok(witness) => {
                                                        let exact = work.used().checked_sub(before).ok_or(Failure::Invalid)?;
                                                        assert_eq!((witness.owner, witness.entry, witness.side, witness.call), (owner, query.entry, 1, sink_call));
                                                        assert_eq!((witness.call_state, witness.role), (call_state, registrations[0].1.ledger));
                                                        assert_eq!(witness.value_context, states[call_state].ok_or(Failure::Invalid)?.value_context);
                                                        assert!(witness.requires_history_and_peer_allocator);
                                                        if let Some((_, result)) = &encoder {
                                                            for &(result_state, _, _, _) in query.current {
                                                                let actual = states.get(result_state).copied().flatten().ok_or(Failure::Invalid)?;
                                                                if source_position(scope, query.focus, actual, result.matching(), work)? {
                                                                    let before = work.used();
                                                                    match query.checked_encoded_output(&witness, result, result_state, work) {
                                                                        Ok(encoded_output) => {
                                                                            let exact = work.used().checked_sub(before).ok_or(Failure::Invalid)?;
                                                                            assert_eq!(encoded_output.call_state, call_state);
                                                                            assert_eq!(encoded_output.result_state, result_state);
                                                                            assert!(encoded_output._output.requires_exclusive_update);
                                                                            assert!(encoded_output._output.requires_history_and_peer_allocator);
                                                                            if !encoded {
                                                                                assert!(exact > 1);
                                                                                let mut same = TypeWorkBudget::with_limit(exact);
                                                                                let _ = query.checked_encoded_output(&witness, result, result_state, &mut same)?;
                                                                                let mut short = TypeWorkBudget::with_limit(exact - 1);
                                                                                assert!(matches!(query.checked_encoded_output(&witness, result, result_state, &mut short), Err(Failure::Resource)));
                                                                                assert!(matches!(query.checked_encoded_output(&witness, result, result_state, &mut short), Err(Failure::Resource)));
                                                                                let mut spent = TypeWorkBudget::with_limit(exact);
                                                                                spent.charge(1).map_err(|()| Failure::Resource)?;
                                                                                assert!(matches!(query.checked_encoded_output(&witness, result, result_state, &mut spent), Err(Failure::Resource)));
                                                                            }
                                                                            encoded = true;
                                                                        }
                                                                        Err(Failure::Invalid) => {}
                                                                        Err(error) => return Err(error),
                                                                    }
                                                                }
                                                            }
                                                            assert!(matches!(query.checked_encoded_output(&witness, result, call_state, work), Err(Failure::Invalid)), "the call occurrence is not an Encoded result arm");
                                                        }
                                                        let wrong_arm = OutputHeadCall { output_arm: output_arm + 1, ..nomination };
                                                        assert!(matches!(query.checked_output_head_call(&wrong_arm, work), Err(Failure::Invalid)));
                                                        if !found {
                                                            assert!(exact > 1);
                                                            let mut same = TypeWorkBudget::with_limit(exact);
                                                            let _ = query.checked_output_head_call(&nomination, &mut same)?;
                                                            let mut short = TypeWorkBudget::with_limit(exact - 1);
                                                            assert!(matches!(query.checked_output_head_call(&nomination, &mut short), Err(Failure::Resource)));
                                                            assert!(matches!(query.checked_output_head_call(&nomination, &mut short), Err(Failure::Resource)), "retry must use the remaining budget");
                                                            let mut spent = TypeWorkBudget::with_limit(exact);
                                                            spent.charge(1).map_err(|()| Failure::Resource)?;
                                                            assert!(matches!(query.checked_output_head_call(&nomination, &mut spent), Err(Failure::Resource)));
                                                        }
                                                        found = true;
                                                    }
                                                    Err(Failure::Invalid) => {}
                                                    Err(error) => return Err(error),
                                                }
                                            }
                                        }
                                    }
                                    assert_eq!(found, !stale, "only the current successor's actual output may reach the sink");
                                    if encoder.is_some() && !stale {
                                        assert!(encoded, "actual Encoded result must follow a matched call return; returns: {:?}", query.encoder_returns);
                                    }
                                    Ok(())
                                },
                            )?;
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
                                receives: receive_plan.as_slice(),
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
                                None, default_handler, 1, work,
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
                                None,
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
