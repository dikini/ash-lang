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

    pub(super) fn enter_source_resource(
        &mut self,
        node: NodeId,
        mut environment: Environment,
        initializer: Value,
    ) -> Result<(), RuntimeFailure> {
        let scope = self
            .source_resource_scope(node)
            .ok_or(RuntimeFailure::ForeignBinding)?;
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
            node,
            key,
            environment,
            owner: None,
            phase: ProviderPhase::Acquire,
            payload: None,
            saved: None,
            consumed: false,
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
                    .take()
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
                boundary.phase = ProviderPhase::Finish;
                boundary.saved = Some(value);
                self.frames.push(Frame::SourceResourceBoundary(boundary));
                self.control = Some(Control::Evaluate(finish_body, finish_environment));
            }
            ProviderPhase::Finish => {
                // Ordinary source constructors cannot consume an owner. The
                // native transition recorded consumption before this report.
                if !boundary.consumed || boundary.owner.is_some() {
                    return Err(RuntimeFailure::ForeignBinding);
                }
                let (constructor, payload) = self.foreign_report(&value, RuntimePhase::Cleanup)?;
                let consumed = constructor == protocol.finish[0] && payload.is_none();
                let consumed_failure = constructor == protocol.finish[1] && payload.is_some();
                if !consumed && !consumed_failure {
                    return Err(RuntimeFailure::ForeignBinding);
                }
                let body = boundary
                    .saved
                    .take()
                    .ok_or(RuntimeFailure::InvalidControlState)?;
                let report = match protocol.report {
                    crate::core::source_resource::SourceResourceReportCodec::Scope {
                        report,
                        completion,
                    } => {
                        let completion = self.foreign_constructor(
                            completion[usize::from(consumed_failure)],
                            payload,
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
                        if consumed_failure {
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
                self.control = Some(Control::Return(report));
            }
        }
        Ok(())
    }
}
