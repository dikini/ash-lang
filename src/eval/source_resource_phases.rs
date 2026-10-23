//! Source-authored resource policy in the existing evaluator machine.
//! Native guards belong to activation frames; source values carry only keys.

use super::{
    ActivationKey, Control, EffectExprKind, EffectOperation, EffectTraceEvent, Environment,
    ExecutableNode, Frame, HeapCell, Machine, NodeId, ProviderPhase, RuntimeFailure, RuntimePhase,
    SourceResourceBoundary, Value, charge_effect_work, matches_pattern_with_work,
    resolve_location_with_work,
};

impl Machine<'_> {
    pub(super) fn source_resource_scope(
        &self,
        node: NodeId,
    ) -> Option<&crate::core::source_resource::SourceResourceScopeNode> {
        match self.program.node(node)? {
            ExecutableNode::Effect(expression) => match &expression.kind {
                EffectExprKind::Operation(EffectOperation::SourceResourceScope(scope)) => {
                    Some(scope)
                }
                _ => None,
            },
            _ => None,
        }
    }

    /// Authenticate typed access positions after ordinary handler selection and
    /// before invoking a source clause. Tuple and nominal payload traversal uses
    /// the original instantiated operand type, never private resource data.
    pub(super) fn authenticate_source_handler_access(
        &mut self,
        selected: usize,
        request_node: NodeId,
        caller: &super::Instantiation,
        value: &Value,
    ) -> Result<(), RuntimeFailure> {
        let program = self.program.clone();
        let Frame::HandlerBoundary {
            node,
            environment,
            provider,
            ..
        } = &self.frames[selected]
        else {
            return Err(RuntimeFailure::InvalidControlState);
        };
        let Some(ExecutableNode::Effect(expression)) = program.node(*node) else {
            return Err(RuntimeFailure::InvalidControlState);
        };
        let EffectExprKind::Operation(EffectOperation::SourceResourceScope(scope)) =
            &expression.kind
        else {
            return Ok(());
        };
        let key = provider.ok_or(RuntimeFailure::InvalidControlState)?;
        charge_effect_work(&mut self.instantiation_work, selected, RuntimePhase::Access)?;
        let mut found = false;
        for frame in &self.frames[..selected] {
            if let Frame::SourceResourceBoundary(boundary) = frame
                && boundary.key == key
            {
                if found
                    || boundary.node != *node
                    || boundary.phase != ProviderPhase::Body
                    || boundary.owner.as_ref().is_none_or(|owner| {
                        !std::sync::Arc::ptr_eq(owner.owner(), &scope.header().owner)
                    })
                {
                    return Err(RuntimeFailure::InvalidControlState);
                }
                if boundary
                    .owner
                    .as_ref()
                    .is_some_and(|owner| !owner.ordinary_live())
                {
                    // Quarantine revokes ordinary provider access. An already
                    // admitted dependent Finish may still obtain the enclosing
                    // owner's exact local State; this grants no ordinary read,
                    // client access or transitive dependency operand.
                    charge_effect_work(
                        &mut self.instantiation_work,
                        self.frames.len(),
                        RuntimePhase::Access,
                    )?;
                    let completion = self
                        .frames
                        .iter()
                        .rev()
                        .find_map(|frame| match frame {
                            Frame::SourceResourceBoundary(boundary) => Some(boundary),
                            _ => None,
                        })
                        .ok_or(RuntimeFailure::InvalidControlState)?;
                    if completion.phase != ProviderPhase::Finish || completion.consumed {
                        return Err(RuntimeFailure::InvalidControlState);
                    }
                    let Some(ExecutableNode::Effect(finishing)) = program.node(completion.node)
                    else {
                        return Err(RuntimeFailure::InvalidControlState);
                    };
                    let EffectExprKind::Operation(EffectOperation::SourceResourceScope(finishing)) =
                        &finishing.kind
                    else {
                        return Err(RuntimeFailure::InvalidControlState);
                    };
                    let guard = completion
                        .owner
                        .as_ref()
                        .ok_or(RuntimeFailure::InvalidControlState)?;
                    if guard.completion_address().is_none()
                        || !std::sync::Arc::ptr_eq(guard.owner(), &finishing.header().owner)
                    {
                        return Err(RuntimeFailure::InvalidControlState);
                    }
                    let Some(ExecutableNode::Effect(request)) = program.node(request_node) else {
                        return Err(RuntimeFailure::InvalidControlState);
                    };
                    let state = crate::types::IterativeTypeOwner::new(
                        caller.ty(&request.ty, &mut self.instantiation_work)?,
                    );
                    let dependency = self
                        .source_bindings
                        .ok_or(RuntimeFailure::ForeignBinding)?
                        .borrowed_owner(
                            key.0 as usize,
                            &state,
                            crate::foreign::source_runtime::NativeOwnerViewKind::State,
                            Some(guard),
                            &mut self.instantiation_work,
                        )?;
                    charge_effect_work(
                        &mut self.instantiation_work,
                        completion.dependencies.len(),
                        RuntimePhase::Access,
                    )?;
                    if !guard.retains(&dependency) {
                        return Err(RuntimeFailure::ForeignBinding);
                    }
                }
                found = true;
            }
        }
        if !found {
            return Err(RuntimeFailure::InvalidControlState);
        }

        let Some(ExecutableNode::Effect(expression)) = program.node(request_node) else {
            return Err(RuntimeFailure::InvalidControlState);
        };
        let EffectExprKind::Operation(EffectOperation::Request(request)) = &expression.kind else {
            return Err(RuntimeFailure::InvalidControlState);
        };
        let operand = match program
            .node(request.operand())
            .ok_or(RuntimeFailure::InvalidControlState)?
        {
            ExecutableNode::Pure(expression) => &expression.ty,
            ExecutableNode::Effect(expression) => &expression.ty,
        };
        let operand = crate::types::IterativeTypeOwner::new(
            caller.ty(operand, &mut self.instantiation_work)?,
        );
        let access = crate::types::IterativeTypeOwner::new(
            environment
                .instantiation
                .ty(scope.handle.ty(), &mut self.instantiation_work)?,
        );
        authenticate_typed_access(
            &self.heap,
            program.registry(),
            operand,
            &access,
            key,
            value,
            &mut self.instantiation_work,
        )
    }

    pub(super) fn enter_source_resource(
        &mut self,
        node: NodeId,
        mut environment: Environment,
        initializer: Value,
    ) -> Result<(), RuntimeFailure> {
        let program = self.program.clone();
        let Some(ExecutableNode::Effect(expression)) = program.node(node) else {
            return Err(RuntimeFailure::ForeignBinding);
        };
        let EffectExprKind::Operation(EffectOperation::SourceResourceScope(scope)) =
            &expression.kind
        else {
            return Err(RuntimeFailure::ForeignBinding);
        };
        let input = crate::types::IterativeTypeOwner::new(
            environment
                .instantiation
                .ty(scope.acquire.parameter.ty(), &mut self.instantiation_work)?,
        );
        // Declared lifetime roles are interpreted before introducing the new
        // identity. A phantom retained role still keeps its original owner live,
        // while a runtime value cannot add an undeclared dependency or donor.
        let mut declared = Vec::new();
        let mut dependencies = Vec::new();
        for dependency in &scope.header().dependencies {
            charge_effect_work(
                &mut self.instantiation_work,
                scope.header().original.parameters.len(),
                RuntimePhase::Acquisition,
            )?;
            let position = scope
                .header()
                .original
                .parameters
                .iter()
                .position(|parameter| parameter.id == *dependency)
                .ok_or(RuntimeFailure::ForeignBinding)?;
            let argument = environment.instantiation.argument(
                scope
                    .arguments()
                    .get(position)
                    .ok_or(RuntimeFailure::ForeignBinding)?,
                &mut self.instantiation_work,
            )?;
            let crate::types::KindedArgument::TypeArg(crate::types::Type::Inference(identity)) =
                &*argument
            else {
                return Err(RuntimeFailure::ForeignBinding);
            };
            let key = ActivationKey(identity.value());
            charge_effect_work(
                &mut self.instantiation_work,
                declared.len(),
                RuntimePhase::Acquisition,
            )?;
            if declared.contains(&key) {
                continue;
            }
            let bindings = self.source_bindings.ok_or(RuntimeFailure::ForeignBinding)?;
            let receipt =
                bindings.declared_owner_dependency(key.0 as usize, &mut self.instantiation_work)?;
            charge_effect_work(&mut self.instantiation_work, 2, RuntimePhase::Acquisition)?;
            declared
                .try_reserve(1)
                .map_err(|_| RuntimeFailure::EnvironmentCapacity)?;
            dependencies
                .try_reserve(1)
                .map_err(|_| RuntimeFailure::EnvironmentCapacity)?;
            declared.push(key);
            dependencies.push(receipt);
        }
        visit_typed_source_values(
            &self.heap,
            program.registry(),
            input,
            &initializer,
            &mut self.instantiation_work,
            |ty, value, work| {
                let (key, kind) = match value {
                    Value::NativeStateView(key) => (
                        *key,
                        crate::foreign::source_runtime::NativeOwnerViewKind::State,
                    ),
                    Value::ResourceHandle(key) => (
                        *key,
                        crate::foreign::source_runtime::NativeOwnerViewKind::Access,
                    ),
                    _ => return Ok(false),
                };
                charge_effect_work(work, declared.len(), RuntimePhase::Acquisition)?;
                if !declared.contains(&key) {
                    return Err(RuntimeFailure::ForeignBinding);
                }
                let bindings = self.source_bindings.ok_or(RuntimeFailure::ForeignBinding)?;
                let dependency = bindings.borrowed_owner(key.0 as usize, ty, kind, None, work)?;
                charge_effect_work(work, dependencies.len(), RuntimePhase::Acquisition)?;
                if !dependencies
                    .iter()
                    .any(|recorded| recorded.same_slot(&dependency))
                {
                    return Err(RuntimeFailure::ForeignBinding);
                }
                Ok(true)
            },
        )?;
        let acquire_parameter = scope.acquire.parameter.id();
        let acquire_body = scope.acquire.body;
        let identity = scope.identity();
        let live = self
            .live_resources
            .checked_add(1)
            .filter(|count| *count <= self.resource_limit)
            .ok_or(RuntimeFailure::ResourceCapacity)?;
        let key = ActivationKey(self.next_activation);
        let next = self
            .next_activation
            .checked_add(1)
            .ok_or(RuntimeFailure::ResourceCapacity)?;
        // The frame and its empty owner slot exist before any native acquisition.
        // Whole-program admission has already checked both generated bindings.
        charge_effect_work(&mut self.instantiation_work, 1, RuntimePhase::Acquisition)?;
        self.frames
            .try_reserve(1)
            .map_err(|_| RuntimeFailure::ResourceCapacity)?;
        environment.instantiation = environment.instantiation.acquire(
            identity,
            key,
            &mut self.instantiation_work,
            Some(RuntimePhase::Acquisition),
        )?;
        let acquisition_environment = environment.clone().extend(acquire_parameter, initializer)?;
        let boundary = Box::new(SourceResourceBoundary {
            checked: None,
            node,
            key,
            environment,
            owner: None,
            dependencies,
            phase: ProviderPhase::Acquire,
            payload: None,
            saved: None,
            consumed: false,
            blocked: false,
            discarded: false,
        });
        self.frames.push(Frame::SourceResourceBoundary(boundary));
        self.live_resources = live;
        self.next_activation = next;
        self.control = Some(Control::Evaluate(acquire_body, acquisition_environment));
        Ok(())
    }

    fn source_pair(
        &mut self,
        value: Value,
        phase: RuntimePhase,
    ) -> Result<[Value; 2], RuntimeFailure> {
        let Value::Location(location) = value else {
            return Err(RuntimeFailure::ForeignBinding);
        };
        let location =
            resolve_location_with_work(&self.heap, location, &mut self.instantiation_work)?;
        charge_effect_work(&mut self.instantiation_work, 2, phase)?;
        let Some(HeapCell::Tuple(fields)) = self.heap.get(location) else {
            return Err(RuntimeFailure::ForeignBinding);
        };
        let [first, second] = fields.as_ref() else {
            return Err(RuntimeFailure::ForeignBinding);
        };
        Ok([first.clone(), second.clone()])
    }

    pub(super) fn return_source_resource(
        &mut self,
        boundary: Box<SourceResourceBoundary>,
        value: Value,
    ) -> Result<(), RuntimeFailure> {
        let checked = boundary
            .checked
            .as_ref()
            .map(|control| control.prepaid_scope_observer());
        let result = self.return_source_resource_inner(boundary, value);
        if result.is_err()
            && let Some(control) = checked
        {
            control.output_failed();
        }
        result
    }
    fn return_source_resource_inner(
        &mut self,
        mut boundary: Box<SourceResourceBoundary>,
        value: Value,
    ) -> Result<(), RuntimeFailure> {
        let key = boundary.key;
        let scope = self
            .source_resource_scope(boundary.node)
            .ok_or(RuntimeFailure::ForeignBinding)?;
        let protocol = scope.header().codec;
        match boundary.phase {
            ProviderPhase::Acquire => {
                if boundary.discarded {
                    // Acquisition has not published state or private data. Its
                    // pending native guard is revoked without fabricating either.
                    drop(boundary.owner.take());
                    self.live_resources = self
                        .live_resources
                        .checked_sub(1)
                        .ok_or(RuntimeFailure::InvalidControlState)?;
                    self.control = Some(Control::Return(Value::Unit));
                    return Ok(());
                }
                let (constructor, payload) =
                    self.foreign_report(&value, RuntimePhase::Acquisition)?;
                if constructor == protocol.acquire[1] {
                    // Refusal revokes a pending unpublished guard before reporting.
                    // An acquired native object may be refused by source policy.
                    drop(boundary.owner.take());
                    let error = payload.ok_or(RuntimeFailure::ForeignBinding)?;
                    self.live_resources = self
                        .live_resources
                        .checked_sub(1)
                        .ok_or(RuntimeFailure::InvalidControlState)?;
                    let report = self.foreign_constructor(
                        protocol.report.refusal(),
                        Some(error),
                        RuntimePhase::Acquisition,
                    )?;
                    self.control = Some(Control::Return(report));
                    return Ok(());
                }
                if constructor != protocol.acquire[0] || boundary.owner.is_none() {
                    return Err(RuntimeFailure::ForeignBinding);
                }
                let [state, data] = self.source_pair(
                    payload.ok_or(RuntimeFailure::ForeignBinding)?,
                    RuntimePhase::Acquisition,
                )?;
                if !matches!(state, Value::NativeStateView(actual) if actual == key) {
                    return Err(RuntimeFailure::ForeignBinding);
                }
                let source_program = self.program.clone();
                let Some(ExecutableNode::Effect(expression)) = source_program.node(boundary.node)
                else {
                    return Err(RuntimeFailure::ForeignBinding);
                };
                let EffectExprKind::Operation(EffectOperation::SourceResourceScope(scope)) =
                    &expression.kind
                else {
                    return Err(RuntimeFailure::ForeignBinding);
                };
                let state_data =
                    self.foreign_tuple(&[state, data.clone()], RuntimePhase::Acquisition)?;
                let mut bindings = Vec::new();
                if !matches_pattern_with_work(
                    &scope.handler_pattern,
                    &state_data,
                    &self.heap,
                    &mut bindings,
                    Some((&mut self.instantiation_work, RuntimePhase::Acquisition)),
                )? {
                    return Err(RuntimeFailure::ForeignBinding);
                }
                let mut handler_environment = boundary
                    .environment
                    .clone()
                    .extend(scope.handler_state.id(), state_data)?;
                for (binder, value) in bindings {
                    handler_environment = handler_environment.extend(binder, value)?;
                }
                let body_environment = boundary
                    .environment
                    .clone()
                    .extend(scope.handle.id(), Value::ResourceHandle(key))?;
                self.frames
                    .try_reserve(2)
                    .map_err(|_| RuntimeFailure::ResourceCapacity)?;
                let node = boundary.node;
                let body = scope.handler.body();
                let handler = scope.handler.id();
                boundary.payload = Some(data);
                if let Some(checked) = &boundary.checked {
                    checked
                        .publish(key.0 as usize, boundary.node, &mut self.instantiation_work)
                        .map_err(|error| match error {
                            crate::foreign::source_runtime::NativeOwnerAdmissionError::Work => {
                                super::effect_work_failure(
                                    &self.instantiation_work,
                                    None,
                                    RuntimePhase::Acquisition,
                                )
                            }
                            _ => RuntimeFailure::ForeignBinding,
                        })?;
                }
                boundary.phase = ProviderPhase::Body;
                self.frames.push(Frame::SourceResourceBoundary(boundary));
                self.frames.push(Frame::HandlerBoundary {
                    node,
                    environment: handler_environment,
                    registration: None,
                    provider: Some(key),
                });
                self.trace_effect(EffectTraceEvent::ResourceAcquired(key.0));
                self.trace_effect(EffectTraceEvent::HandlerActivated(handler));
                self.control = Some(Control::Evaluate(body, body_environment));
            }
            ProviderPhase::Body => {
                let finish_parameter = scope.finish.parameter.id();
                let finish_body = scope.finish.body;
                let data = boundary
                    .payload
                    .as_ref()
                    .cloned()
                    .ok_or(RuntimeFailure::ForeignBinding)?;
                let state_data = self
                    .foreign_tuple(&[Value::NativeStateView(key), data], RuntimePhase::Cleanup)?;
                let finish_environment = boundary
                    .environment
                    .clone()
                    .extend(finish_parameter, state_data)?;
                self.frames
                    .try_reserve(1)
                    .map_err(|_| RuntimeFailure::ResourceCapacity)?;
                if let Some(checked) = &boundary.checked {
                    checked
                        .closing(key.0 as usize, boundary.node, &mut self.instantiation_work)
                        .map_err(|error| match error {
                            crate::foreign::source_runtime::NativeOwnerAdmissionError::Work => {
                                super::effect_work_failure(
                                    &self.instantiation_work,
                                    None,
                                    RuntimePhase::Cleanup,
                                )
                            }
                            _ => RuntimeFailure::ForeignBinding,
                        })?;
                }
                boundary.phase = ProviderPhase::Finish;
                boundary.saved = (!boundary.discarded).then_some(value);
                self.frames.push(Frame::SourceResourceBoundary(boundary));
                self.control = Some(Control::Evaluate(finish_body, finish_environment));
            }
            ProviderPhase::Finish => {
                // Ordinary source constructors cannot consume an owner. The
                // native transition recorded consumption before this report.
                let (constructor, payload) = self.foreign_report(&value, RuntimePhase::Cleanup)?;
                let consumed = constructor == protocol.finish[0] && payload.is_none();
                let consumed_failure = constructor == protocol.finish[1] && payload.is_some();
                let retained = constructor == protocol.finish[2] && payload.is_some();
                let error = if retained {
                    if boundary.consumed {
                        return Err(RuntimeFailure::ForeignBinding);
                    }
                    let [state, error] = self.source_pair(
                        payload.ok_or(RuntimeFailure::ForeignBinding)?,
                        RuntimePhase::Cleanup,
                    )?;
                    if !matches!(state, Value::NativeStateView(actual) if actual == key) {
                        return Err(RuntimeFailure::ForeignBinding);
                    }
                    let owner = boundary
                        .owner
                        .as_mut()
                        .ok_or(RuntimeFailure::ForeignBinding)?;
                    owner.quarantine();
                    Some(error)
                } else {
                    if !boundary.consumed
                        || boundary.owner.is_some()
                        || (!consumed && !consumed_failure)
                    {
                        return Err(RuntimeFailure::ForeignBinding);
                    }
                    payload
                };
                if boundary.discarded {
                    self.live_resources = self
                        .live_resources
                        .checked_sub(1)
                        .ok_or(RuntimeFailure::InvalidControlState)?;
                    self.trace_effect(EffectTraceEvent::ResourceReleased(key.0));
                    if consumed_failure || retained {
                        // Owned discard has no body value to report. Quarantine
                        // was recorded above; later host destruction cannot turn
                        // this failed source completion into cleanup success.
                        return Err(RuntimeFailure::ResourceCompletion);
                    }
                    // No abandoned body value or Scope report exists on discard.
                    if let Some(checked) = &boundary.checked {
                        checked
                            .source_continued(key.0 as usize, boundary.node)
                            .map_err(|_| RuntimeFailure::ForeignBinding)?;
                    }
                    self.control = Some(Control::Return(Value::Unit));
                    return Ok(());
                }
                let body = boundary
                    .saved
                    .take()
                    .ok_or(RuntimeFailure::InvalidControlState)?;
                let report = match protocol.report {
                    crate::core::source_resource::SourceResourceReportCodec::CheckedScope {
                        ..
                    } => return Err(RuntimeFailure::ForeignBinding),
                    crate::core::source_resource::SourceResourceReportCodec::Scope {
                        report,
                        completion,
                    } => {
                        let completion = self.foreign_constructor(
                            completion[if retained {
                                2
                            } else {
                                usize::from(consumed_failure)
                            }],
                            error,
                            RuntimePhase::Cleanup,
                        )?;
                        let fields =
                            self.foreign_tuple(&[body, completion], RuntimePhase::Cleanup)?;
                        Some(self.foreign_constructor(
                            report[1],
                            Some(fields),
                            RuntimePhase::Cleanup,
                        )?)
                    }
                    crate::core::source_resource::SourceResourceReportCodec::AcquiredOnly {
                        report,
                    } => {
                        if consumed_failure || retained {
                            None
                        } else {
                            Some(self.foreign_constructor(
                                report[0],
                                Some(body),
                                RuntimePhase::Cleanup,
                            )?)
                        }
                    }
                };
                self.live_resources = self
                    .live_resources
                    .checked_sub(1)
                    .ok_or(RuntimeFailure::InvalidControlState)?;
                self.trace_effect(EffectTraceEvent::ResourceReleased(key.0));
                let report = report.ok_or(RuntimeFailure::ResourceCompletion)?;
                // The current CheckedScope report guard above remains closed.
                // This connection cannot mark the authored continuation complete
                // until the source Finish has actually returned and its report exists.
                if let Some(checked) = &boundary.checked {
                    checked
                        .source_continued(key.0 as usize, boundary.node)
                        .map_err(|_| RuntimeFailure::ForeignBinding)?;
                }
                self.control = Some(Control::Return(report));
            }
        }
        Ok(())
    }
}

struct AccessReplacements(
    std::collections::HashMap<crate::types::TypeVariableId, crate::types::Type>,
);
impl Drop for AccessReplacements {
    fn drop(&mut self) {
        for (_, ty) in self.0.drain() {
            crate::types::discard_type_iteratively(ty);
        }
    }
}

fn authenticate_typed_access(
    heap: &[HeapCell],
    registry: &crate::resolved::ResolvedRegistry,
    operand: crate::types::IterativeTypeOwner,
    access: &crate::types::Type,
    key: ActivationKey,
    value: &Value,
    work: &mut crate::types::TypeWorkBudget,
) -> Result<(), RuntimeFailure> {
    visit_typed_source_values(heap, registry, operand, value, work, |ty, value, work| {
        if crate::types::same_type_with_budget(ty, access, work)
            .map_err(|_| super::effect_work_failure(work, None, RuntimePhase::Access))?
        {
            if !matches!(value, Value::ResourceHandle(actual) if *actual == key) {
                return Err(RuntimeFailure::InvalidControlState);
            }
            return Ok(true);
        }
        if matches!(value, Value::ResourceHandle(_) | Value::NativeStateView(_)) {
            return Err(RuntimeFailure::InvalidControlState);
        }
        Ok(false)
    })
}

pub(super) fn visit_typed_source_values(
    heap: &[HeapCell],
    registry: &crate::resolved::ResolvedRegistry,
    operand: crate::types::IterativeTypeOwner,
    value: &Value,
    work: &mut crate::types::TypeWorkBudget,
    mut visit: impl FnMut(
        &crate::types::Type,
        &Value,
        &mut crate::types::TypeWorkBudget,
    ) -> Result<bool, RuntimeFailure>,
) -> Result<(), RuntimeFailure> {
    use crate::types::{
        IterativeTypeOwner, Type, clone_type_with_budget, substitute_type_variables_with,
    };
    let mut pending = Vec::new();
    charge_effect_work(work, 1, RuntimePhase::Access)?;
    pending
        .try_reserve(1)
        .map_err(|_| RuntimeFailure::EnvironmentCapacity)?;
    pending.push((operand, value));
    while let Some((ty, value)) = pending.pop() {
        charge_effect_work(work, 1, RuntimePhase::Access)?;
        if visit(&ty, value, work)? {
            continue;
        }
        let Value::Location(location) = value else {
            // Tuple and nominal values require their ordinary heap shape. A
            // malformed scalar must not bypass nested typed access positions.
            if matches!(
                &*ty,
                Type::Tuple(_) | Type::Nominal(_) | Type::Application(_, _)
            ) {
                return Err(RuntimeFailure::InvalidControlState);
            }
            continue;
        };
        let location = resolve_location_with_work(heap, *location, work)?;
        match (heap.get(location), &*ty) {
            (Some(HeapCell::Tuple(values)), Type::Tuple(types)) => {
                if values.len() != types.len() {
                    return Err(RuntimeFailure::InvalidControlState);
                }
                charge_effect_work(work, types.len(), RuntimePhase::Access)?;
                pending
                    .try_reserve(types.len())
                    .map_err(|_| RuntimeFailure::EnvironmentCapacity)?;
                for (ty, value) in types.iter().zip(values.iter()).rev() {
                    let ty = IterativeTypeOwner::new(clone_type_with_budget(ty, work).map_err(
                        |_| super::effect_work_failure(work, None, RuntimePhase::Access),
                    )?);
                    pending.push((ty, value));
                }
            }
            (Some(HeapCell::Constructor(id, value)), _) => {
                let mut arguments = Vec::new();
                let mut head = &*ty;
                while let Type::Application(function, argument) = head {
                    charge_effect_work(work, 1, RuntimePhase::Access)?;
                    arguments
                        .try_reserve(1)
                        .map_err(|_| RuntimeFailure::EnvironmentCapacity)?;
                    arguments.push(argument.as_ref());
                    head = function;
                }
                let Type::Nominal(owner) = head else {
                    return Err(RuntimeFailure::InvalidControlState);
                };
                let constructor = registry
                    .constructor(*id)
                    .ok_or(RuntimeFailure::InvalidControlState)?;
                let parameters = registry
                    .nominal_parameters(*owner)
                    .ok_or(RuntimeFailure::InvalidControlState)?;
                if constructor.owner != *owner || parameters.len() != arguments.len() {
                    return Err(RuntimeFailure::InvalidControlState);
                }
                match (value, constructor.payload.as_ref()) {
                    (None, None) => {}
                    (Some(value), Some(payload)) => {
                        charge_effect_work(work, parameters.len(), RuntimePhase::Access)?;
                        let mut replacements = AccessReplacements(std::collections::HashMap::new());
                        replacements
                            .0
                            .try_reserve(parameters.len())
                            .map_err(|_| RuntimeFailure::EnvironmentCapacity)?;
                        for (parameter, argument) in parameters.iter().zip(arguments.iter().rev()) {
                            replacements.0.insert(
                                parameter.id,
                                clone_type_with_budget(argument, work).map_err(|_| {
                                    super::effect_work_failure(work, None, RuntimePhase::Access)
                                })?,
                            );
                        }
                        let payload = IterativeTypeOwner::new(substitute_type_variables_with(
                            payload,
                            &replacements.0,
                            |cells| charge_effect_work(work, cells, RuntimePhase::Access),
                            || RuntimeFailure::EnvironmentCapacity,
                        )?);
                        charge_effect_work(work, 1, RuntimePhase::Access)?;
                        pending
                            .try_reserve(1)
                            .map_err(|_| RuntimeFailure::EnvironmentCapacity)?;
                        pending.push((payload, value));
                    }
                    _ => return Err(RuntimeFailure::InvalidControlState),
                }
            }
            _ => return Err(RuntimeFailure::InvalidControlState),
        }
    }
    Ok(())
}

/// An injected legacy-shaped return exercises the existing phase branch. It is
/// NOT a well-typed CheckedFinish result, authored Trace or checked activation.
#[cfg(test)]
#[test]
fn checked_owner_boundary_discarded_finish_continuation_model() {
    use crate::foreign::source_runtime::CheckedOwnerContinuation;
    for failure in [false, true] {
        crate::foreign::source_bindings::with_recorded_boundary_for_test(
            |program, node, checked| {
                let mut machine = Machine::new_effect(program);
                machine.instantiation_work = crate::types::TypeWorkBudget::default();
                machine.live_resources = 1;
                machine.control = None;
                let codec = machine.source_resource_scope(node).unwrap().header().codec;
                let observed = checked.prepaid_scope_observer();
                assert_eq!(
                    observed.snapshot().continuation,
                    CheckedOwnerContinuation::Required
                );
                // Deliberately injected legacy-shaped data, not checked report admission.
                let value = machine
                    .foreign_constructor(
                        codec.finish[usize::from(failure)],
                        failure.then_some(Value::Unit),
                        RuntimePhase::Cleanup,
                    )
                    .unwrap();
                let boundary = Box::new(SourceResourceBoundary {
                    checked: Some(checked),
                    node,
                    key: ActivationKey(111),
                    environment: Environment::new(),
                    owner: None,
                    dependencies: Vec::new(),
                    phase: ProviderPhase::Finish,
                    payload: None,
                    saved: None,
                    consumed: true,
                    blocked: false,
                    discarded: true,
                });
                let result = machine.return_source_resource(boundary, value);
                if failure {
                    assert!(result.is_err());
                    assert_eq!(
                        observed.snapshot().continuation,
                        CheckedOwnerContinuation::Required
                    );
                    assert!(observed.snapshot().terminal);
                } else {
                    result.unwrap();
                    assert!(matches!(
                        machine.control,
                        Some(Control::Return(Value::Unit))
                    ));
                    assert_eq!(
                        observed.snapshot().continuation,
                        CheckedOwnerContinuation::Completed
                    );
                    assert!(observed.source_continued(111, node).is_err());
                }
                assert!(machine.source_bindings.is_none()); // no evaluator native callback
            },
        );
    }
}

#[cfg(test)]
mod typed_access_tests {
    // These tests call the typed predicate directly. They do not exercise
    // handler selection, native guard ownership, or entry into a source clause.
    use super::{ActivationKey, HeapCell, RuntimeFailure, RuntimePhase, Value};
    use crate::{
        core::{EffectExprKind, EffectOperation},
        eval::{ResourceFailureCause, RuntimeResource},
        resolved::ResolvedRegistry,
        types::{
            ConstructorId, IterativeTypeOwner, RowReservationSite, Type, TypeWorkBudget,
            clone_type_with_budget, row_reservation_fault,
        },
    };
    use std::{
        fs,
        path::PathBuf,
        sync::{
            Arc,
            atomic::{AtomicU64, Ordering},
        },
    };

    struct Fixture(PathBuf);

    impl Fixture {
        fn new() -> Self {
            static IDS: AtomicU64 = AtomicU64::new(0);
            let directory = std::env::temp_dir().join(format!(
                "ash-typed-source-access-{}-{}",
                std::process::id(),
                IDS.fetch_add(1, Ordering::Relaxed)
            ));
            fs::create_dir(&directory).unwrap();
            let original = include_str!("../../tests/fixtures/source-owner/forwarding_owner.ash");
            let owner = original.replace(
                "pub interface ProbeProvider",
                "pub type AccessWrap<T> = AccessWrap(T)\n\
                 pub type AccessPair<A, B> = AccessPair(A, B)\n\
                 pub type AccessEmpty = AccessEmpty\n\n\
                 pub interface ProbeProvider",
            );
            assert_ne!(
                original, owner,
                "the fixture declares real wrapper constructors"
            );
            fs::write(directory.join("owner.ash"), owner).unwrap();
            fs::write(
                directory.join("entry.ash"),
                r#"import owner as Owner

main : Unit -> Owner.Scope<Unit, Unit, (Int, Int)>
main () = resource Owner.Probe<{}, R, {}> owner = 5 {
    (Owner.read owner, Owner.offset (owner, 3))
}
"#,
            )
            .unwrap();
            Self(directory)
        }

        fn facts(&self) -> Facts {
            let compiled = crate::driver::compile_path(crate::driver::RunConfiguration {
                entry: self.0.join("entry.ash"),
                roots: crate::module::ModuleRoots::empty(),
            })
            .expect("ordinary two-method source fixture compiles");
            let (checked, _) = compiled.effect_build_input().expect("source Effect Core");
            let access = checked
                .nodes()
                .iter()
                .find_map(|stored| match &stored.kind {
                    EffectExprKind::Operation(EffectOperation::SourceResourceScope(scope)) => {
                        Some(copy_type(scope.handle.ty()))
                    }
                    _ => None,
                })
                .expect("the actual source scope supplies the complete access type");
            let registry = checked.registry().clone();
            let constructor = |spelling| {
                registry
                    .constructors()
                    .iter()
                    .find(|constructor| constructor.spelling == spelling)
                    .expect("constructor identity comes from the compiled source")
                    .id
            };
            let wrap = constructor("AccessWrap");
            let pair = constructor("AccessPair");
            let empty = constructor("AccessEmpty");
            Facts {
                registry,
                access,
                wrap,
                pair,
                empty,
            }
        }
    }

    impl Drop for Fixture {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.0);
        }
    }

    struct Facts {
        registry: Arc<ResolvedRegistry>,
        access: IterativeTypeOwner,
        wrap: ConstructorId,
        pair: ConstructorId,
        empty: ConstructorId,
    }

    fn copy_type(ty: &Type) -> IterativeTypeOwner {
        IterativeTypeOwner::new(
            clone_type_with_budget(ty, &mut TypeWorkBudget::unbounded()).unwrap(),
        )
    }

    fn applied(constructor: ConstructorId, arguments: Vec<Type>) -> IterativeTypeOwner {
        let mut ty = Type::Nominal(constructor.owner());
        for argument in arguments {
            ty = Type::Application(Box::new(ty), Box::new(argument));
        }
        IterativeTypeOwner::new(ty)
    }

    fn authenticate(
        facts: &Facts,
        heap: &[HeapCell],
        operand: &Type,
        selected: ActivationKey,
        value: &Value,
        work: &mut TypeWorkBudget,
    ) -> Result<(), RuntimeFailure> {
        // Fixture/type copying is outside the measured predicate ledger.
        super::authenticate_typed_access(
            heap,
            &facts.registry,
            copy_type(operand),
            &facts.access,
            selected,
            value,
            work,
        )
    }

    fn assert_invalid(result: Result<(), RuntimeFailure>) {
        assert_eq!(result, Err(RuntimeFailure::InvalidControlState));
    }

    fn assert_access_work_refusal(result: Result<(), RuntimeFailure>) {
        let Err(RuntimeFailure::Report(report)) = result else {
            panic!("the predicate must report exhausted access work")
        };
        assert_eq!(report.primary.reason_code(), "runtime.environment-capacity");
        assert!(report.teardown.is_none());
        let details = report.primary.resource().expect("access work details");
        assert_eq!(details.cause, ResourceFailureCause::WorkBudgetExhausted);
        assert_eq!(details.phase, RuntimePhase::Access);
        assert_eq!(details.resource, RuntimeResource::WorkUnits);
        assert!(details.available.is_some());
    }

    #[test]
    fn selected_key_requires_public_access_not_stale_state_or_scalar() {
        let facts = Fixture::new().facts();
        let selected = ActivationKey(12);
        assert!(
            authenticate(
                &facts,
                &[],
                &facts.access,
                selected,
                &Value::ResourceHandle(selected),
                &mut TypeWorkBudget::unbounded(),
            )
            .is_ok()
        );
        // Direct key fixtures model donor and prior-execution identities. They
        // do not prove that the selected activation has a live native guard.
        for value in [
            Value::ResourceHandle(ActivationKey(13)),
            Value::ResourceHandle(ActivationKey(11)),
            Value::NativeStateView(selected),
            Value::Unit,
            Value::Integer(crate::integer::Integer::from_i64(5)),
        ] {
            assert_invalid(authenticate(
                &facts,
                &[],
                &facts.access,
                selected,
                &value,
                &mut TypeWorkBudget::unbounded(),
            ));
        }
        for value in [
            Value::ResourceHandle(selected),
            Value::NativeStateView(selected),
        ] {
            assert_invalid(authenticate(
                &facts,
                &[],
                &Type::Int,
                selected,
                &value,
                &mut TypeWorkBudget::unbounded(),
            ));
        }
    }

    #[test]
    fn every_tuple_access_position_rejects_a_same_typed_donor_key() {
        let facts = Fixture::new().facts();
        let selected = ActivationKey(21);
        let operand = IterativeTypeOwner::new(Type::Tuple(Box::new([
            copy_type(&facts.access).into_inner(),
            Type::Int,
            Type::Tuple(Box::new([
                Type::Unit,
                copy_type(&facts.access).into_inner(),
                copy_type(&facts.access).into_inner(),
            ])),
            copy_type(&facts.access).into_inner(),
        ])));
        for rejected_position in 0..=4 {
            let access = |position| {
                Value::ResourceHandle(if rejected_position == position {
                    ActivationKey(22)
                } else {
                    selected
                })
            };
            let heap = [
                HeapCell::Tuple(Box::new([Value::Unit, access(2), access(3)])),
                HeapCell::Tuple(Box::new([
                    access(1),
                    Value::Integer(crate::integer::Integer::from_i64(3)),
                    Value::Location(0),
                    access(4),
                ])),
            ];
            let result = authenticate(
                &facts,
                &heap,
                &operand,
                selected,
                &Value::Location(1),
                &mut TypeWorkBudget::unbounded(),
            );
            if rejected_position == 0 {
                assert!(result.is_ok());
            } else {
                assert_invalid(result);
            }
        }
    }

    #[test]
    fn nested_nominal_payloads_and_aliases_preserve_exact_access() {
        let facts = Fixture::new().facts();
        let selected = ActivationKey(31);
        let inner = applied(facts.wrap, vec![copy_type(&facts.access).into_inner()]);
        let operand = applied(facts.wrap, vec![inner.into_inner()]);
        for payload in [
            Value::ResourceHandle(selected),
            Value::ResourceHandle(ActivationKey(32)),
            Value::NativeStateView(selected),
            Value::Integer(crate::integer::Integer::from_i64(5)),
        ] {
            let accepted = matches!(payload, Value::ResourceHandle(key) if key == selected);
            let heap = [
                HeapCell::Constructor(facts.wrap, Some(payload)),
                HeapCell::Alias(0),
                HeapCell::Constructor(facts.wrap, Some(Value::Location(1))),
                HeapCell::Alias(2),
                HeapCell::Alias(3),
            ];
            let result = authenticate(
                &facts,
                &heap,
                &operand,
                selected,
                &Value::Location(4),
                &mut TypeWorkBudget::unbounded(),
            );
            if accepted {
                assert!(result.is_ok());
            } else {
                assert_invalid(result);
            }
        }
    }

    #[test]
    fn nominal_parameter_order_retains_each_typed_access_position() {
        let facts = Fixture::new().facts();
        let selected = ActivationKey(41);
        for position in 0..2 {
            let arguments = if position == 0 {
                vec![copy_type(&facts.access).into_inner(), Type::Int]
            } else {
                vec![Type::Int, copy_type(&facts.access).into_inner()]
            };
            let operand = applied(facts.pair, arguments);
            for key in [selected, ActivationKey(42)] {
                let mut fields = [
                    Value::Integer(crate::integer::Integer::from_i64(6)),
                    Value::Integer(crate::integer::Integer::from_i64(7)),
                ];
                fields[position] = Value::ResourceHandle(key);
                let heap = [
                    HeapCell::Tuple(Box::new(fields)),
                    HeapCell::Constructor(facts.pair, Some(Value::Location(0))),
                ];
                let result = authenticate(
                    &facts,
                    &heap,
                    &operand,
                    selected,
                    &Value::Location(1),
                    &mut TypeWorkBudget::unbounded(),
                );
                if key == selected {
                    assert!(result.is_ok());
                } else {
                    assert_invalid(result);
                }
            }
        }
    }

    #[test]
    fn real_donor_constructors_and_malformed_payload_shapes_are_rejected() {
        let facts = Fixture::new().facts();
        let selected = ActivationKey(51);
        let wrapped = applied(facts.wrap, vec![copy_type(&facts.access).into_inner()]);
        for cell in [
            HeapCell::Constructor(facts.empty, None),
            HeapCell::Constructor(facts.pair, Some(Value::ResourceHandle(selected))),
            HeapCell::Constructor(facts.wrap, None),
        ] {
            assert_invalid(authenticate(
                &facts,
                &[cell],
                &wrapped,
                selected,
                &Value::Location(0),
                &mut TypeWorkBudget::unbounded(),
            ));
        }
        let heap = [HeapCell::Constructor(
            facts.wrap,
            Some(Value::ResourceHandle(selected)),
        )];
        for malformed in [
            applied(facts.wrap, vec![]),
            applied(
                facts.wrap,
                vec![copy_type(&facts.access).into_inner(), Type::Int],
            ),
        ] {
            assert_invalid(authenticate(
                &facts,
                &heap,
                &malformed,
                selected,
                &Value::Location(0),
                &mut TypeWorkBudget::unbounded(),
            ));
        }
        assert_invalid(authenticate(
            &facts,
            &[HeapCell::Constructor(facts.empty, Some(Value::Unit))],
            &Type::Nominal(facts.empty.owner()),
            selected,
            &Value::Location(0),
            &mut TypeWorkBudget::unbounded(),
        ));
    }

    #[test]
    fn structural_heap_frontiers_refuse_wrong_arity_and_broken_aliases() {
        let facts = Fixture::new().facts();
        let selected = ActivationKey(61);
        let operand = IterativeTypeOwner::new(Type::Tuple(Box::new([
            copy_type(&facts.access).into_inner(),
            Type::Unit,
        ])));
        assert_invalid(authenticate(
            &facts,
            &[HeapCell::Tuple(Box::new([Value::ResourceHandle(selected)]))],
            &operand,
            selected,
            &Value::Location(0),
            &mut TypeWorkBudget::unbounded(),
        ));
        for (heap, expected) in [
            (vec![HeapCell::Alias(0)], RuntimeFailure::AliasLoop),
            (vec![HeapCell::Alias(1)], RuntimeFailure::InvalidLocation),
            (
                vec![HeapCell::Uninitialized],
                RuntimeFailure::UninitializedLocation,
            ),
        ] {
            assert_eq!(
                authenticate(
                    &facts,
                    &heap,
                    &operand,
                    selected,
                    &Value::Location(0),
                    &mut TypeWorkBudget::unbounded(),
                ),
                Err(expected)
            );
        }
    }

    #[test]
    fn scalar_replacement_of_an_access_aggregate_cannot_skip_authentication() {
        // Internal representation regression. Independently checked source
        // cannot substitute these scalars for aggregate values; the predicate
        // still fails closed before skipping nested typed access positions.
        let facts = Fixture::new().facts();
        let selected = ActivationKey(66);
        let tuple = IterativeTypeOwner::new(Type::Tuple(Box::new([
            copy_type(&facts.access).into_inner(),
            Type::Unit,
        ])));
        let wrapped = applied(facts.wrap, vec![copy_type(&facts.access).into_inner()]);
        for operand in [&*tuple, &*wrapped] {
            for value in [
                Value::Unit,
                Value::Integer(crate::integer::Integer::from_i64(5)),
            ] {
                assert_invalid(authenticate(
                    &facts,
                    &[],
                    operand,
                    selected,
                    &value,
                    &mut TypeWorkBudget::unbounded(),
                ));
            }
        }
    }

    #[test]
    fn ordinary_scalar_and_constructor_callable_need_no_access_key() {
        let facts = Fixture::new().facts();
        let selected = ActivationKey(67);
        let result = applied(facts.wrap, vec![Type::Int]);
        let callable = IterativeTypeOwner::new(Type::Function(
            Box::new(Type::Int),
            Box::new(result.into_inner()),
        ));
        for (operand, value) in [
            (&Type::Unit, Value::Unit),
            (
                &Type::Int,
                Value::Integer(crate::integer::Integer::from_i64(5)),
            ),
            (&*callable, Value::ConstructorFunction(facts.wrap)),
        ] {
            assert!(
                authenticate(
                    &facts,
                    &[],
                    operand,
                    selected,
                    &value,
                    &mut TypeWorkBudget::unbounded(),
                )
                .is_ok()
            );
        }
    }

    fn exact_budget_and_retry(facts: &Facts, heap: &[HeapCell], operand: &Type, value: &Value) {
        let selected = ActivationKey(71);
        let mut measured = TypeWorkBudget::unbounded();
        authenticate(facts, heap, operand, selected, value, &mut measured).unwrap();
        let required = measured.used();
        assert!(required > 0);
        for prefix in [0, 7] {
            for available in [0, required - 1] {
                let mut short = TypeWorkBudget::with_limit(prefix + available);
                short.charge(prefix).unwrap();
                assert_access_work_refusal(authenticate(
                    facts, heap, operand, selected, value, &mut short,
                ));
                for _ in 0..2 {
                    let mut fresh = TypeWorkBudget::with_limit(prefix + required);
                    fresh.charge(prefix).unwrap();
                    authenticate(facts, heap, operand, selected, value, &mut fresh).unwrap();
                    assert_eq!(fresh.used(), prefix + required);
                }
            }
        }
    }

    #[test]
    fn direct_tuple_and_nominal_access_use_exact_budget_and_fresh_retry() {
        let facts = Fixture::new().facts();
        let selected = ActivationKey(71);
        exact_budget_and_retry(&facts, &[], &facts.access, &Value::ResourceHandle(selected));
        let tuple = IterativeTypeOwner::new(Type::Tuple(Box::new([
            Type::Int,
            copy_type(&facts.access).into_inner(),
        ])));
        let heap = [HeapCell::Tuple(Box::new([
            Value::Integer(crate::integer::Integer::from_i64(4)),
            Value::ResourceHandle(selected),
        ]))];
        exact_budget_and_retry(&facts, &heap, &tuple, &Value::Location(0));
        let inner = applied(facts.wrap, vec![copy_type(&facts.access).into_inner()]);
        let nominal = applied(facts.wrap, vec![inner.into_inner()]);
        let heap = [
            HeapCell::Constructor(facts.wrap, Some(Value::ResourceHandle(selected))),
            HeapCell::Constructor(facts.wrap, Some(Value::Location(0))),
            HeapCell::Alias(1),
        ];
        exact_budget_and_retry(&facts, &heap, &nominal, &Value::Location(2));
    }

    #[test]
    fn existing_comparison_reservation_refusal_stops_authentication_and_retries() {
        let facts = Fixture::new().facts();
        let selected = ActivationKey(81);
        // The failpoint covers the borrowed type comparison worklist only.
        // It does not inject failure into the access walk's Vec or HashMap.
        let operand = copy_type(&facts.access);
        {
            let _fault = row_reservation_fault::fail(RowReservationSite::ComparisonWork, 0);
            assert!(
                super::authenticate_typed_access(
                    &[],
                    &facts.registry,
                    operand,
                    &facts.access,
                    selected,
                    &Value::ResourceHandle(selected),
                    &mut TypeWorkBudget::unbounded(),
                )
                .is_err()
            );
            assert_eq!(row_reservation_fault::hits(), 1);
        }
        assert!(
            authenticate(
                &facts,
                &[],
                &facts.access,
                selected,
                &Value::ResourceHandle(selected),
                &mut TypeWorkBudget::unbounded(),
            )
            .is_ok()
        );
    }

    #[test]
    fn refused_deep_operand_ownership_is_disposed_on_a_small_stack() {
        let facts = Fixture::new().facts();
        std::thread::Builder::new()
            .stack_size(64 * 1024)
            .spawn(move || {
                for available in [0, 32] {
                    let mut operand = copy_type(&facts.access).into_inner();
                    let mut value = Value::ResourceHandle(ActivationKey(91));
                    let mut heap = Vec::new();
                    for _ in 0..16_384 {
                        operand = Type::Tuple(Box::new([operand, Type::Unit]));
                        let location = heap.len();
                        heap.push(HeapCell::Tuple(Box::new([value, Value::Unit])));
                        value = Value::Location(location);
                    }
                    assert_access_work_refusal(super::authenticate_typed_access(
                        &heap,
                        &facts.registry,
                        IterativeTypeOwner::new(operand),
                        &facts.access,
                        ActivationKey(91),
                        &value,
                        &mut TypeWorkBudget::with_limit(available),
                    ));
                }
            })
            .expect("direct access disposal thread starts")
            .join()
            .expect("refused owned operand drains without recursive destruction");
    }
}

#[cfg(test)]
mod source_handler_entry_tests {
    // These are injected guard / machine-entry preflight witnesses. Native
    // acquisition policy and C memory are not executed by this module.
    use super::super::Instantiation;
    use super::{
        ActivationKey, Control, EffectExprKind, EffectOperation, EffectTraceEvent, Environment,
        ExecutableNode, Frame, Machine, NodeId, ProviderPhase, RuntimeFailure, RuntimePhase,
        SourceResourceBoundary, Value,
    };
    use crate::{
        core::ValidatedEffectProgram,
        driver::{CompiledProgram, RunConfiguration, compile_path},
        foreign::{
            source_owner::CheckedForeignOwner,
            source_runtime::{
                NativeOwnerCallReturned, NativeOwnerGuard, NativeOwnerGuardReady,
                NativeScalarCallError, NativeScalarValue,
            },
        },
        module::ModuleRoots,
        types::TypeWorkBudget,
    };
    use std::{
        cell::Cell,
        collections::HashSet,
        fs,
        path::PathBuf,
        ptr::NonNull,
        sync::{
            Arc,
            atomic::{AtomicU64, Ordering},
        },
    };

    thread_local! {
        static ARMED: Cell<usize> = const { Cell::new(0) };
        static DESTROYED: Cell<usize> = const { Cell::new(0) };
        static BYTE: Cell<u8> = const { Cell::new(0) };
        static BYTE_READS: Cell<usize> = const { Cell::new(0) };
        static BYTE_WRITES: Cell<usize> = const { Cell::new(0) };
    }

    fn reset_counts() {
        assert_eq!(
            ARMED.get(),
            DESTROYED.get(),
            "previous injected guards were destroyed"
        );
        ARMED.set(0);
        DESTROYED.set(0);
    }

    fn destroy_sentinel(arguments: &[crate::foreign::source_runtime::NativeOwnerOperand]) {
        let [crate::foreign::source_runtime::NativeOwnerOperand::Address(address)] = arguments
        else {
            panic!("admitted sentinel address");
        };
        let address = *address;
        assert_eq!(address, NonNull::<u8>::dangling().as_ptr().cast());
        DESTROYED.set(DESTROYED.get() + 1);
    }

    fn acquire_sentinel(
        arguments: &[crate::foreign::source_runtime::NativeOwnerOperand],
        readiness: NativeOwnerGuardReady,
    ) -> Result<NativeOwnerCallReturned, NativeScalarCallError> {
        let [
            crate::foreign::source_runtime::NativeOwnerOperand::Scalar(NativeScalarValue::USize(
                42,
            )),
        ] = arguments
        else {
            return Err(NativeScalarCallError::ArgumentContract);
        };
        ARMED.set(ARMED.get() + 1);
        Ok(readiness.returned(NonNull::<u8>::dangling().as_ptr().cast()))
    }

    fn injected_guard(owner: Arc<CheckedForeignOwner>) -> NativeOwnerGuard {
        // This is the existing post-record test model: the address is never
        // dereferenced and the safe destructor counts one ownership edge.
        acquire_sentinel(
            &[crate::foreign::source_runtime::NativeOwnerOperand::Scalar(
                NativeScalarValue::USize(42),
            )],
            NativeOwnerGuardReady::new(owner, destroy_sentinel),
        )
        .expect("the injected acquisition receives its declared scalar")
        .record()
        .into_guard()
        .expect("the sentinel records a nonnull injected guard")
    }

    fn read_byte_sentinel(address: *mut core::ffi::c_void, index: usize) -> u8 {
        assert_eq!(address, NonNull::<u8>::dangling().as_ptr().cast());
        assert_eq!(index, 0);
        BYTE_READS.set(BYTE_READS.get() + 1);
        BYTE.get()
    }

    fn write_byte_sentinel(address: *mut core::ffi::c_void, index: usize, byte: u8) {
        assert_eq!(address, NonNull::<u8>::dangling().as_ptr().cast());
        assert_eq!(index, 0);
        BYTE_WRITES.set(BYTE_WRITES.get() + 1);
        BYTE.set(byte);
    }

    #[test]
    fn byte_guard_bounds_and_complete_reply_admission_precede_callbacks() {
        use super::super::source_byte_phases::{ByteReplyReady, report_reservation_fault};
        use crate::foreign::source_runtime::NativeByteCallbacks;
        reset_counts();
        BYTE.set(0);
        BYTE_READS.set(0);
        BYTE_WRITES.set(0);
        let facts = Fixture::compile_with_bytes(false, true);
        let machine = Machine::new_effect(facts.program());
        let source = machine.source_resource_scope(facts.scope).unwrap();
        let returned = source.header().acquire.call_codec().ids().returned;
        let mut ready =
            NativeOwnerGuardReady::new(Arc::clone(&source.header().owner), destroy_sentinel);
        ready.prepare_byte_callbacks(NativeByteCallbacks {
            read: read_byte_sentinel,
            write: write_byte_sentinel,
        });
        ready.prepare_initialized_bytes(Some(1));
        let guard = acquire_sentinel(
            &[crate::foreign::source_runtime::NativeOwnerOperand::Scalar(
                NativeScalarValue::USize(42),
            )],
            ready,
        )
        .unwrap()
        .record()
        .into_guard()
        .unwrap();
        assert_eq!(guard.initialized_bytes(), Some(1));
        assert!(guard.byte_access(1).is_none());
        assert!(guard.byte_access(usize::MAX).is_none());
        assert_eq!((BYTE_READS.get(), BYTE_WRITES.get()), (0, 0));
        let mut heap = Vec::new();
        for read in [false, true] {
            let mut short = TypeWorkBudget::with_limit(1 + usize::from(read));
            assert!(ByteReplyReady::admit(&mut heap, &mut short, returned, read).is_err());
            assert!(heap.is_empty());
            assert_eq!((BYTE_READS.get(), BYTE_WRITES.get()), (0, 0));
            assert_eq!(BYTE.get(), 0);
        }
        for read in [false, true] {
            let _fault = report_reservation_fault::fail_next();
            let mut exact = TypeWorkBudget::with_limit(2 + usize::from(read));
            assert!(ByteReplyReady::admit(&mut heap, &mut exact, returned, read).is_err());
            assert_eq!(exact.remaining(), 0);
            assert_eq!(report_reservation_fault::hits(), 1);
            assert!(heap.is_empty());
            assert_eq!((BYTE_READS.get(), BYTE_WRITES.get()), (0, 0));
            assert_eq!(BYTE.get(), 0, "refused storage precedes any native write");
        }
        let mut zero_work = TypeWorkBudget::with_limit(3);
        let zero = ByteReplyReady::admit(&mut heap, &mut zero_work, returned, true).unwrap();
        let Value::Location(zero_location) = zero.read(guard.byte_access(0).unwrap()) else {
            panic!("prepaid zero byte report")
        };
        assert!(
            matches!(&heap[zero_location], super::super::HeapCell::Constructor(found, Some(Value::Integer(value))) if *found == returned && value.to_u64() == Some(0))
        );
        let mut write_work = TypeWorkBudget::with_limit(2);
        let write = ByteReplyReady::admit(&mut heap, &mut write_work, returned, false).unwrap();
        assert_eq!(write_work.remaining(), 0);
        let output = write.write(guard.byte_access(0).unwrap(), 255);
        assert!(matches!(output, Value::Location(_)));
        assert_eq!(
            (BYTE_READS.get(), BYTE_WRITES.get(), BYTE.get()),
            (1, 1, 255)
        );
        for _ in 0..2 {
            let mut read_work = TypeWorkBudget::with_limit(3);
            let read = ByteReplyReady::admit(&mut heap, &mut read_work, returned, true).unwrap();
            assert_eq!(read_work.remaining(), 0);
            let Value::Location(location) = read.read(guard.byte_access(0).unwrap()) else {
                panic!("prepaid byte report")
            };
            assert!(
                matches!(&heap[location], super::super::HeapCell::Constructor(found, Some(Value::Integer(value))) if *found == returned && value.to_u64() == Some(255))
            );
        }
        assert_eq!((BYTE_READS.get(), BYTE_WRITES.get()), (3, 1));
        drop(guard);
        assert_eq!(DESTROYED.get(), 1);
        let opaque = Fixture::compile(false);
        let machine = Machine::new_effect(opaque.program());
        let guard = injected_guard(Arc::clone(
            &machine
                .source_resource_scope(opaque.scope)
                .unwrap()
                .header()
                .owner,
        ));
        assert!(guard.byte_access(0).is_none());
        drop(guard);
        assert_eq!(ARMED.get(), DESTROYED.get());
    }

    #[test]
    fn byte_guard_missing_initialization_zero_extent_and_null_never_grant_access() {
        use crate::foreign::source_runtime::NativeByteCallbacks;
        reset_counts();
        BYTE_READS.set(0);
        BYTE_WRITES.set(0);
        let facts = Fixture::compile_with_bytes(false, true);
        let machine = Machine::new_effect(facts.program());
        let owner = &machine
            .source_resource_scope(facts.scope)
            .unwrap()
            .header()
            .owner;
        for extent in [None, Some(0)] {
            let mut ready = NativeOwnerGuardReady::new(Arc::clone(owner), destroy_sentinel);
            ready.prepare_byte_callbacks(NativeByteCallbacks {
                read: read_byte_sentinel,
                write: write_byte_sentinel,
            });
            ready.prepare_initialized_bytes(extent);
            let guard = acquire_sentinel(
                &[crate::foreign::source_runtime::NativeOwnerOperand::Scalar(
                    NativeScalarValue::USize(42),
                )],
                ready,
            )
            .unwrap()
            .record()
            .into_guard()
            .unwrap();
            assert_eq!(guard.initialized_bytes(), extent);
            assert!(guard.byte_access(0).is_none());
            assert_eq!((BYTE_READS.get(), BYTE_WRITES.get()), (0, 0));
            drop(guard);
            assert_eq!(ARMED.get(), DESTROYED.get());
        }
        let mut missing_callbacks = NativeOwnerGuardReady::new(Arc::clone(owner), destroy_sentinel);
        missing_callbacks.prepare_initialized_bytes(Some(1));
        let guard = acquire_sentinel(
            &[crate::foreign::source_runtime::NativeOwnerOperand::Scalar(
                NativeScalarValue::USize(42),
            )],
            missing_callbacks,
        )
        .unwrap()
        .record()
        .into_guard()
        .unwrap();
        assert!(guard.byte_access(0).is_none());
        drop(guard);
        let mut null = NativeOwnerGuardReady::new(Arc::clone(owner), destroy_sentinel);
        null.prepare_byte_callbacks(NativeByteCallbacks {
            read: read_byte_sentinel,
            write: write_byte_sentinel,
        });
        null.prepare_initialized_bytes(Some(7));
        assert!(
            null.returned(std::ptr::null_mut())
                .record()
                .into_guard()
                .is_none()
        );
        assert_eq!(ARMED.get(), DESTROYED.get());
        assert_eq!((BYTE_READS.get(), BYTE_WRITES.get()), (0, 0));
    }

    struct Fixture(PathBuf);

    impl Fixture {
        fn compile(ordinary_override: bool) -> Facts {
            Self::compile_with_bytes(ordinary_override, false)
        }

        fn compile_with_bytes(ordinary_override: bool, bytes: bool) -> Facts {
            static IDS: AtomicU64 = AtomicU64::new(0);
            let directory = std::env::temp_dir().join(format!(
                "ash-source-handler-entry-{}-{}",
                std::process::id(),
                IDS.fetch_add(1, Ordering::Relaxed)
            ));
            fs::create_dir(&directory).unwrap();
            let fixture = Self(directory);
            let mut owner =
                include_str!("../../tests/fixtures/source-owner/forwarding_owner.ash").to_owned();
            if bytes {
                owner = owner.replace("repr Address = opaque", "repr Address = bytes")
                    .replace("outcome result nonnull { readable result }", "outcome result nonnull { readable result, initialized_bytes result from 0 }");
            }
            fs::write(fixture.0.join("owner.ash"), owner).unwrap();
            let body = if ordinary_override {
                r#"handle (Owner.read owner) with Owner.ProbeOps<Owner.Probe<{}, R, {}>> {
        read access => resume 84
        offset (access, delta) => resume 105
    }"#
            } else {
                "Owner.read owner"
            };
            let entry = format!(
                "import owner as Owner\n\nmain : Unit -> Owner.Scope<Unit, Unit, Int>\n\
                 main () = resource Owner.Probe<{{}}, R, {{}}> owner = 42 {{\n    {body}\n}}\n"
            );
            fs::write(fixture.0.join("entry.ash"), entry).unwrap();
            let compiled = compile_path(RunConfiguration {
                entry: fixture.0.join("entry.ash"),
                roots: ModuleRoots::empty(),
            })
            .expect("ordinary source provider fixture compiles");
            let (program, _) = compiled.effect_build_input().expect("source Effect Core");
            let graph = descendants(program, program.root());
            let scope = graph
                .iter()
                .copied()
                .find(|node| {
                    matches!(
                        program.node(*node).unwrap().kind,
                        EffectExprKind::Operation(EffectOperation::SourceResourceScope(_))
                    )
                })
                .expect("actual source scope");
            let EffectExprKind::Operation(EffectOperation::SourceResourceScope(source)) =
                &program.node(scope).unwrap().kind
            else {
                unreachable!()
            };
            let effect = source.handler.effect().effect();
            let requests = descendants(program, source.handler.body());
            let request = |spelling: &str| {
                requests
                    .iter()
                    .copied()
                    .find(|node| {
                        let EffectExprKind::Operation(EffectOperation::Request(request)) =
                            &program.node(*node).unwrap().kind
                        else {
                            return false;
                        };
                        request.effect().effect() == effect
                            && program
                                .registry()
                                .effect(effect)
                                .unwrap()
                                .operations
                                .iter()
                                .any(|operation| {
                                    operation.id == request.operation()
                                        && operation.spelling == spelling
                                })
                    })
                    .expect("actual generated forwarding request by declared name")
            };
            let read = request("read");
            let offset = request("offset");
            let ordinary = graph.iter().copied().find(|node| {
                matches!(&program.node(*node).unwrap().kind,
                    EffectExprKind::Operation(EffectOperation::Handler(handler))
                    if handler.effect().effect() == effect)
            });
            assert_eq!(ordinary.is_some(), ordinary_override);
            Facts {
                compiled,
                scope,
                read,
                offset,
                ordinary,
            }
        }
    }

    impl Drop for Fixture {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.0);
        }
    }

    struct Facts {
        compiled: CompiledProgram,
        scope: NodeId,
        read: NodeId,
        offset: NodeId,
        ordinary: Option<NodeId>,
    }

    impl Facts {
        fn program(&self) -> &ValidatedEffectProgram {
            self.compiled.effect_build_input().unwrap().0
        }
    }

    fn descendants(program: &ValidatedEffectProgram, root: NodeId) -> Vec<NodeId> {
        let mut pending = vec![root];
        let mut visited = HashSet::new();
        let mut nodes = Vec::new();
        while let Some(node) = pending.pop() {
            if !visited.insert(node) {
                continue;
            }
            let expression = program.node(node).expect("existing checked graph edge");
            nodes.push(node);
            pending.extend(
                (0..expression.kind.child_count())
                    .filter_map(|index| expression.kind.child_at(index)),
            );
        }
        nodes
    }

    fn publish(machine: &mut Machine<'_>, scope: NodeId) -> ActivationKey {
        let source = machine.source_resource_scope(scope).unwrap();
        let owner = Arc::clone(&source.header().owner);
        let acquired = source.header().codec.acquire[0];
        machine
            .enter_source_resource(scope, Environment::new(), integer(42))
            .unwrap();
        let Some(Frame::SourceResourceBoundary(mut boundary)) = machine.frames.pop() else {
            panic!("actual activation preparation installs the unique owner slot")
        };
        let key = boundary.key;
        boundary.owner = Some(injected_guard(owner));
        let pair = machine
            .foreign_tuple(
                &[Value::NativeStateView(key), integer(42)],
                RuntimePhase::Acquisition,
            )
            .unwrap();
        let report = machine
            .foreign_constructor(acquired, Some(pair), RuntimePhase::Acquisition)
            .unwrap();
        machine.return_source_resource(boundary, report).unwrap();
        // The tests stop at an operand-return checkpoint; no source clause or
        // foreign call is evaluated after publication.
        machine.control = None;
        machine.instantiation_work = TypeWorkBudget::unbounded();
        key
    }

    fn integer(value: i64) -> Value {
        Value::Integer(crate::integer::Integer::from_i64(value))
    }

    fn caller(machine: &Machine<'_>, selected: usize) -> Instantiation {
        let Frame::HandlerBoundary { environment, .. } = &machine.frames[selected] else {
            panic!("selected handler boundary")
        };
        environment.instantiation.clone()
    }

    fn assert_before_clause(machine: &Machine<'_>) {
        assert!(machine.control.is_none());
        assert_eq!(machine.captured_cells, 0);
        assert!(machine.pending_source_call.is_none());
        assert!(machine.pending_source_owner_call.is_none());
        assert!(
            !machine
                .frames
                .iter()
                .any(|frame| matches!(frame, Frame::ClauseBoundary { .. }))
        );
    }

    #[test]
    fn source_control_transfer_refusal_preserves_the_same_unique_guard() {
        // Direct transfer checkpoints use real admitted source metadata and an
        // injected guard; generated-host tests establish actual typed cuts.
        let facts = Fixture::compile(false);
        let source = match &facts.program().node(facts.scope).unwrap().kind {
            crate::core::EffectExprKind::Operation(
                crate::core::EffectOperation::SourceResourceScope(scope),
            ) => scope,
            _ => unreachable!(),
        };
        let handler = source.handler.id();
        let owner = source.handler.clauses()[0].resume();
        let resume = descendants(facts.program(), source.handler.clauses()[0].body())
            .into_iter()
            .find(|id| {
                matches!(&facts.program().node(*id).unwrap().kind,
                crate::core::EffectExprKind::Operation(crate::core::EffectOperation::Resume(resume))
                    if resume.handler() == handler && resume.owner() == owner)
            })
            .unwrap();
        for cause in [
            crate::eval::ResourceFailureCause::AllocatorRefused,
            crate::eval::ResourceFailureCause::StorageReservationFailed,
        ] {
            reset_counts();
            let mut machine = Machine::new_effect(facts.program());
            let key = publish(&mut machine, facts.scope);
            machine.capture_limit = 1;
            assert!(machine.capture_from(0).is_err());
            assert_eq!(machine.frames.len(), 2);
            assert_eq!(machine.captured_cells, 0);
            machine.capture_limit = 2;
            super::super::machine_test_hooks::FAIL_CONTROL_RESERVATION.set(Some(cause));
            assert!(machine.capture_from(0).is_err());
            assert_eq!(machine.frames.len(), 2);
            assert_eq!(machine.captured_cells, 0);
            assert_eq!(DESTROYED.get(), 0);
            let captured = machine.capture_from(0).unwrap();
            assert_eq!(machine.captured_cells, 2);
            assert!(
                matches!(&captured.frames[0], Frame::SourceResourceBoundary(boundary) if boundary.key == key && boundary.owner.is_some())
            );
            machine.frames.push(Frame::ClauseBoundary {
                handler,
                owner,
                continuation: Some(captured),
                registration: None,
            });
            for discard in [false, true] {
                super::super::machine_test_hooks::FAIL_CONTROL_RESERVATION.set(Some(cause));
                let failed = if discard {
                    machine.discard(handler, owner)
                } else {
                    machine.return_resume(resume, integer(42))
                };
                assert!(failed.is_err());
                assert_eq!(machine.captured_cells, 2);
                assert!(
                    matches!(&machine.frames[0], Frame::ClauseBoundary { continuation: Some(capture), .. } if matches!(&capture.frames[0], Frame::SourceResourceBoundary(boundary) if boundary.key == key && boundary.owner.is_some()))
                );
                assert_eq!(DESTROYED.get(), 0);
            }
            machine.instantiation_work = TypeWorkBudget::with_limit(0);
            assert!(machine.discard(handler, owner).is_err());
            assert_eq!(machine.captured_cells, 2);
            machine.instantiation_work = TypeWorkBudget::unbounded();
            machine.discard(handler, owner).unwrap();
            assert_eq!(machine.captured_cells, 0);
            assert!(machine.frames.iter().any(|frame| matches!(frame, Frame::SourceResourceBoundary(boundary) if boundary.key == key && boundary.discarded && boundary.owner.is_some() && boundary.saved.is_none())));
            assert_eq!(DESTROYED.get(), 0);
            drop(machine);
            assert_eq!(ARMED.get(), 1);
            assert_eq!(DESTROYED.get(), 1);
        }
    }

    #[test]
    fn source_control_discard_work_is_exact_before_consumption_and_source_guards_drop_iteratively()
    {
        let facts = Fixture::compile(false);
        let source = match &facts.program().node(facts.scope).unwrap().kind {
            crate::core::EffectExprKind::Operation(
                crate::core::EffectOperation::SourceResourceScope(scope),
            ) => scope,
            _ => unreachable!(),
        };
        let handler = source.handler.id();
        let owner = source.handler.clauses()[0].resume();
        let setup = || {
            reset_counts();
            let mut machine = Machine::new_effect(facts.program());
            let key = publish(&mut machine, facts.scope);
            let capture = machine.capture_from(0).unwrap();
            machine.frames.push(Frame::ClauseBoundary {
                handler,
                owner,
                continuation: Some(capture),
                registration: None,
            });
            machine.instantiation_work = TypeWorkBudget::unbounded();
            (machine, key)
        };
        let (mut measured, _) = setup();
        measured.discard(handler, owner).unwrap();
        let required = measured.instantiation_work.used();
        drop(measured);
        for prefix in [0, 5] {
            for available in [required - 1, required, required] {
                let (mut machine, key) = setup();
                machine.instantiation_work = TypeWorkBudget::with_limit(prefix + available);
                machine.instantiation_work.charge(prefix).unwrap();
                let result = machine.discard(handler, owner);
                if available < required {
                    let RuntimeFailure::Report(report) = result.unwrap_err() else {
                        panic!("bounded capture refusal")
                    };
                    assert_eq!(
                        report.primary.resource().unwrap().cause,
                        crate::eval::ResourceFailureCause::WorkBudgetExhausted
                    );
                    assert_eq!(machine.captured_cells, 2);
                    assert!(
                        matches!(&machine.frames[0], Frame::ClauseBoundary { continuation: Some(capture), .. }
                        if matches!(&capture.frames[0], Frame::SourceResourceBoundary(boundary) if boundary.key == key && !boundary.discarded && boundary.owner.is_some()))
                    );
                } else {
                    result.unwrap();
                    assert_eq!(machine.instantiation_work.used(), prefix + required);
                    assert_eq!(machine.captured_cells, 0);
                }
                assert_eq!(DESTROYED.get(), 0);
                drop(machine);
                assert_eq!(ARMED.get(), 1);
                assert_eq!(DESTROYED.get(), 1);
            }
        }
        let metadata = Arc::clone(&source.header().owner);
        let node = facts.scope;
        std::thread::Builder::new()
            .stack_size(64 * 1024)
            .spawn(move || {
                reset_counts();
                let mut captured = super::super::CapturedContinuation { frames: Vec::new() };
                for depth in 0..32_768u32 {
                    captured = super::super::CapturedContinuation {
                        frames: vec![
                            Frame::SourceResourceBoundary(Box::new(
                                super::super::SourceResourceBoundary {
                                    checked: None,
                                    node,
                                    key: ActivationKey(depth),
                                    phase: super::super::ProviderPhase::Body,
                                    environment: Environment::new(),
                                    owner: Some(injected_guard(Arc::clone(&metadata))),
                                    dependencies: Vec::new(),
                                    consumed: false,
                                    blocked: false,
                                    payload: Some(integer(42)),
                                    saved: None,
                                    discarded: false,
                                },
                            )),
                            Frame::ClauseBoundary {
                                handler,
                                owner,
                                registration: None,
                                continuation: Some(captured),
                            },
                        ],
                    };
                }
                drop(captured);
                assert_eq!(ARMED.get(), 32_768);
                assert_eq!(DESTROYED.get(), 32_768);
            })
            .unwrap()
            .join()
            .unwrap();
        println!(
            "source discard admission work={required}; exact/one-short/prefix/fresh retry, 32768 injected guards disposed on 64KiB"
        );
    }

    #[test]
    fn exact_published_guard_passes_hook_then_source_machine_entry() {
        reset_counts();
        let facts = Fixture::compile(false);
        let mut machine = Machine::new_effect(facts.program());
        let key = publish(&mut machine, facts.scope);
        let caller = caller(&machine, 1);
        let events = machine.effect_trace.clone();
        machine
            .authenticate_source_handler_access(1, facts.read, &caller, &Value::ResourceHandle(key))
            .unwrap();
        assert_eq!(machine.effect_trace, events);
        assert_eq!(machine.frames.len(), 2);
        assert_before_clause(&machine);
        assert_eq!(DESTROYED.get(), 0);
        let source = machine.source_resource_scope(facts.scope).unwrap();
        let handler = source.handler.id();
        machine
            .return_request(facts.read, &caller, Value::ResourceHandle(key))
            .unwrap();
        assert!(machine.effect_trace.as_ref().unwrap().iter().any(|event| {
            matches!(event, EffectTraceEvent::ClauseEntered(actual, _) if *actual == handler)
        }));
        assert!(matches!(machine.control, Some(Control::Evaluate(_, _))));
        assert_eq!(DESTROYED.get(), 0);
        drop(machine);
        assert_eq!(ARMED.get(), 1);
        assert_eq!(DESTROYED.get(), 1);
    }

    #[test]
    fn hook_rejects_donor_stale_state_and_scalar_before_entry() {
        reset_counts();
        let facts = Fixture::compile(false);
        let mut machine = Machine::new_effect(facts.program());
        let key = publish(&mut machine, facts.scope);
        let caller = caller(&machine, 1);
        let events = machine.effect_trace.clone();
        for value in [
            Value::ResourceHandle(ActivationKey(key.0 + 1)),
            Value::ResourceHandle(ActivationKey(u32::MAX)),
            Value::NativeStateView(key),
            integer(42),
        ] {
            assert_eq!(
                machine.authenticate_source_handler_access(1, facts.read, &caller, &value,),
                Err(RuntimeFailure::InvalidControlState)
            );
            assert_eq!(machine.effect_trace, events);
            assert_eq!(machine.frames.len(), 2);
            assert_before_clause(&machine);
            assert_eq!(DESTROYED.get(), 0);
        }
        drop(machine);
        assert_eq!(DESTROYED.get(), 1);
    }

    #[test]
    fn selected_source_hook_authenticates_original_owner_and_unique_boundary() {
        #[derive(Clone, Copy, Debug)]
        enum Mutation {
            NoOwner,
            WrongOwner,
            WrongKey,
            WrongNode,
            AcquirePhase,
            FinishPhase,
            MissingProvider,
            StaleProvider,
            MissingBoundary,
            DuplicateBoundary,
        }
        let facts = Fixture::compile(false);
        let donor = Fixture::compile(false);
        let donor_machine = Machine::new_effect(donor.program());
        let donor_owner = Arc::clone(
            &donor_machine
                .source_resource_scope(donor.scope)
                .unwrap()
                .header()
                .owner,
        );
        for mutation in [
            Mutation::NoOwner,
            Mutation::WrongOwner,
            Mutation::WrongKey,
            Mutation::WrongNode,
            Mutation::AcquirePhase,
            Mutation::FinishPhase,
            Mutation::MissingProvider,
            Mutation::StaleProvider,
            Mutation::MissingBoundary,
            Mutation::DuplicateBoundary,
        ] {
            reset_counts();
            let mut machine = Machine::new_effect(facts.program());
            let key = publish(&mut machine, facts.scope);
            let context = caller(&machine, 1);
            let mut held_guards = Vec::new();
            let mut held_frames = Vec::new();
            let mut selected = 1;
            let program_root = machine.program.root();
            match mutation {
                Mutation::MissingBoundary => {
                    held_frames.push(machine.frames.remove(0));
                    selected = 0;
                }
                Mutation::MissingProvider | Mutation::StaleProvider => {
                    let Frame::HandlerBoundary { provider, .. } = &mut machine.frames[1] else {
                        unreachable!()
                    };
                    *provider = if matches!(mutation, Mutation::MissingProvider) {
                        None
                    } else {
                        Some(ActivationKey(u32::MAX))
                    };
                }
                Mutation::DuplicateBoundary => {
                    let Frame::SourceResourceBoundary(original) = &machine.frames[0] else {
                        unreachable!()
                    };
                    let copy = SourceResourceBoundary {
                        checked: None,
                        node: original.node,
                        key: original.key,
                        environment: original.environment.clone(),
                        owner: Some(injected_guard(Arc::clone(
                            original.owner.as_ref().unwrap().owner(),
                        ))),
                        dependencies: Vec::new(),
                        phase: ProviderPhase::Body,
                        payload: original.payload.clone(),
                        saved: None,
                        consumed: false,
                        blocked: false,
                        discarded: false,
                    };
                    machine
                        .frames
                        .insert(1, Frame::SourceResourceBoundary(Box::new(copy)));
                    selected = 2;
                }
                _ => {
                    let Frame::SourceResourceBoundary(boundary) = &mut machine.frames[0] else {
                        unreachable!()
                    };
                    match mutation {
                        Mutation::NoOwner => held_guards.push(boundary.owner.take().unwrap()),
                        Mutation::WrongOwner => {
                            assert!(!Arc::ptr_eq(
                                boundary.owner.as_ref().unwrap().owner(),
                                &donor_owner
                            ));
                            held_guards.push(
                                boundary
                                    .owner
                                    .replace(injected_guard(Arc::clone(&donor_owner)))
                                    .unwrap(),
                            );
                        }
                        Mutation::WrongKey => boundary.key = ActivationKey(u32::MAX),
                        Mutation::WrongNode => boundary.node = program_root,
                        Mutation::AcquirePhase => boundary.phase = ProviderPhase::Acquire,
                        Mutation::FinishPhase => boundary.phase = ProviderPhase::Finish,
                        _ => unreachable!(),
                    }
                }
            }
            let events = machine.effect_trace.clone();
            let count = machine.frames.len();
            let acquisitions = ARMED.get();
            assert_eq!(
                machine.authenticate_source_handler_access(
                    selected,
                    facts.read,
                    &context,
                    &Value::ResourceHandle(key),
                ),
                Err(RuntimeFailure::InvalidControlState),
                "{mutation:?}"
            );
            assert_eq!(machine.frames.len(), count);
            assert_eq!(ARMED.get(), acquisitions);
            assert_eq!(machine.effect_trace, events);
            assert_before_clause(&machine);
            assert_eq!(DESTROYED.get(), 0);
            drop(machine);
            drop(held_guards);
            drop(held_frames);
            assert_eq!(DESTROYED.get(), ARMED.get(), "{mutation:?}");
        }
    }

    #[test]
    fn machine_selection_refuses_unchanged_bad_access_before_clause_commit() {
        reset_counts();
        let facts = Fixture::compile(false);
        let mut machine = Machine::new_effect(facts.program());
        let key = publish(&mut machine, facts.scope);
        let context = caller(&machine, 1);
        let donor = ActivationKey(key.0 + 1);
        let tuple = machine
            .foreign_tuple(
                &[Value::ResourceHandle(donor), integer(3)],
                RuntimePhase::Access,
            )
            .unwrap();
        let events = machine.effect_trace.clone();
        let heap = format!("{:?}", machine.heap);
        let acquisitions = ARMED.get();
        for (request, value) in [
            (facts.read, Value::ResourceHandle(donor)),
            (facts.read, Value::NativeStateView(key)),
            (facts.offset, tuple),
        ] {
            assert_eq!(
                machine.return_request(request, &context, value),
                Err(RuntimeFailure::InvalidControlState)
            );
            assert_eq!(machine.frames.len(), 2);
            assert_eq!(machine.effect_trace, events);
            assert_eq!(format!("{:?}", machine.heap), heap);
            assert_eq!(ARMED.get(), acquisitions);
            assert_before_clause(&machine);
            assert_eq!(DESTROYED.get(), 0);
        }
        drop(machine);
        assert_eq!(DESTROYED.get(), 1);
    }

    #[test]
    fn repeated_same_source_publication_keeps_distinct_selected_activations() {
        reset_counts();
        let facts = Fixture::compile(false);
        let mut machine = Machine::new_effect(facts.program());
        let outer = publish(&mut machine, facts.scope);
        let inner = publish(&mut machine, facts.scope);
        assert_ne!(outer, inner);
        let context = caller(&machine, 3);
        let events = machine.effect_trace.clone();
        assert_eq!(
            machine.authenticate_source_handler_access(
                3,
                facts.read,
                &context,
                &Value::ResourceHandle(outer),
            ),
            Err(RuntimeFailure::InvalidControlState)
        );
        machine
            .authenticate_source_handler_access(
                3,
                facts.read,
                &context,
                &Value::ResourceHandle(inner),
            )
            .unwrap();
        assert_eq!(machine.effect_trace, events);
        assert_eq!(machine.frames.len(), 4);
        assert_before_clause(&machine);
        assert_eq!(DESTROYED.get(), 0);
        drop(machine);
        assert_eq!(ARMED.get(), 2);
        assert_eq!(DESTROYED.get(), 2);
    }

    #[test]
    fn selected_source_hook_has_exact_work_and_fresh_retry_without_callback_replay() {
        reset_counts();
        let facts = Fixture::compile(false);
        let mut machine = Machine::new_effect(facts.program());
        let key = publish(&mut machine, facts.scope);
        let context = caller(&machine, 1);
        let events = machine.effect_trace.clone();
        machine
            .authenticate_source_handler_access(
                1,
                facts.read,
                &context,
                &Value::ResourceHandle(key),
            )
            .unwrap();
        let required = machine.instantiation_work.used();
        assert!(required > 0);
        println!("selected source handler admission work={required}");
        for prefix in [0, 5] {
            for available in [0, required - 1] {
                machine.instantiation_work = TypeWorkBudget::with_limit(prefix + available);
                machine.instantiation_work.charge(prefix).unwrap();
                let failure = machine
                    .authenticate_source_handler_access(
                        1,
                        facts.read,
                        &context,
                        &Value::ResourceHandle(key),
                    )
                    .unwrap_err();
                let RuntimeFailure::Report(report) = failure else {
                    panic!("hook work refusal retains bounded resource details")
                };
                let details = report.primary.resource().unwrap();
                assert_eq!(
                    details.cause,
                    crate::eval::ResourceFailureCause::WorkBudgetExhausted
                );
                assert_eq!(details.resource, crate::eval::RuntimeResource::WorkUnits);
                for _ in 0..2 {
                    machine.instantiation_work = TypeWorkBudget::with_limit(prefix + required);
                    machine.instantiation_work.charge(prefix).unwrap();
                    machine
                        .authenticate_source_handler_access(
                            1,
                            facts.read,
                            &context,
                            &Value::ResourceHandle(key),
                        )
                        .unwrap();
                    assert_eq!(machine.instantiation_work.used(), prefix + required);
                    assert_eq!(machine.frames.len(), 2);
                    assert_eq!(machine.effect_trace, events);
                    assert_before_clause(&machine);
                    assert_eq!(ARMED.get(), 1);
                    assert_eq!(DESTROYED.get(), 0);
                }
            }
        }
        drop(machine);
        assert_eq!(DESTROYED.get(), 1);
    }

    #[test]
    fn ordinary_selection_bypasses_outer_source_authentication() {
        reset_counts();
        let facts = Fixture::compile(true);
        let mut machine = Machine::new_effect(facts.program());
        let key = publish(&mut machine, facts.scope);
        let context = caller(&machine, 1);
        let Frame::HandlerBoundary { environment, .. } = &machine.frames[1] else {
            unreachable!()
        };
        let environment = environment.clone();
        let ordinary = facts.ordinary.unwrap();
        machine.frames.push(Frame::HandlerBoundary {
            node: ordinary,
            environment,
            registration: None,
            provider: None,
        });
        let Frame::SourceResourceBoundary(boundary) = &mut machine.frames[0] else {
            unreachable!()
        };
        let held_guard = boundary.owner.take().unwrap();
        let events = machine.effect_trace.clone();
        machine.instantiation_work = TypeWorkBudget::with_limit(0);
        // Deliberately invalid outer owner topology cannot grant an ordinary
        // handler a new requirement to authenticate the source provider.
        machine
            .authenticate_source_handler_access(
                2,
                facts.read,
                &context,
                &Value::ResourceHandle(key),
            )
            .unwrap();
        assert_eq!(machine.instantiation_work.used(), 0);
        assert_eq!(machine.effect_trace, events);
        assert_before_clause(&machine);
        machine.instantiation_work = TypeWorkBudget::unbounded();
        let Some(ExecutableNode::Effect(expression)) = machine.program.node(ordinary) else {
            unreachable!()
        };
        let EffectExprKind::Operation(EffectOperation::Handler(handler)) = &expression.kind else {
            unreachable!()
        };
        let selected_handler = handler.id();
        machine
            .return_request(facts.read, &context, Value::ResourceHandle(key))
            .unwrap();
        assert!(machine.effect_trace.as_ref().unwrap().iter().any(|event| {
            matches!(event, EffectTraceEvent::ClauseEntered(actual, _) if *actual == selected_handler)
        }));
        assert_eq!(DESTROYED.get(), 0);
        drop(machine);
        drop(held_guard);
        assert_eq!(DESTROYED.get(), 1);
    }
}
