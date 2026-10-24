//! Original direct lifecycle calls can deny an exact physical owner group.
//! Authentication and borrowed cause inspection precede denial. Ordinary Ash
//! result construction follows it and may fail terminally without undoing it.
use super::{
    Control, ExecutableNode, Frame, HeapCell, Machine, ProviderPhase, RuntimeFailure, RuntimePhase,
    Value,
};
use crate::{
    core::{
        EffectExprKind, EffectOperation, PureComputation, PureExprKind,
        packed::Intrinsic,
        source_resource::{SourceByteCall, SourceResourcePhase},
    },
    foreign::{
        scalar_preflight::ForeignScalarPreflightRole as Role,
        source_bindings::{SourceOwnerViolationRequest, owner_admission_failure},
    },
    module::{ForeignCheckedNominalRole as Nominal, ModuleId},
    types::{ConstructorId, IterativeTypeOwner, NominalTypeId, Type, TypeWorkBudget},
};

fn phase(phase: ProviderPhase) -> SourceResourcePhase {
    match phase {
        ProviderPhase::Acquire => SourceResourcePhase::Acquire,
        ProviderPhase::Body => SourceResourcePhase::Handler,
        ProviderPhase::Finish => SourceResourcePhase::Finish,
    }
}
fn validation(error: crate::core::ValidationError, work: &TypeWorkBudget) -> RuntimeFailure {
    if error.reason() == crate::core::ValidationReason::Resource {
        super::effect_work_failure(work, None, RuntimePhase::Access)
    } else {
        RuntimeFailure::ForeignBinding
    }
}
fn constructor(module: ModuleId, role: Nominal, ordinal: u32) -> ConstructorId {
    ConstructorId::new(NominalTypeId::new(module, role.local()), ordinal)
}

/// Only fixed constructor/tuple shape is read. Integer payloads are borrowed,
/// never cloned, converted, scanned or promoted into native observations.
fn cause(
    heap: &[HeapCell],
    location: usize,
    module: ModuleId,
    work: &mut TypeWorkBudget,
) -> Result<(), RuntimeFailure> {
    let location = super::resolve_location_with_work(heap, location, work)?;
    super::charge_effect_work(work, 2, RuntimePhase::Access)?;
    let Some(HeapCell::Constructor(id, payload)) = heap.get(location) else {
        return Err(RuntimeFailure::ForeignBinding);
    };
    for ordinal in [0, 1, 3] {
        if *id == constructor(module, Nominal::ViolationCause, ordinal) {
            return if matches!(payload, Some(Value::Integer(_))) {
                Ok(())
            } else {
                Err(RuntimeFailure::ForeignBinding)
            };
        }
    }
    if *id == constructor(module, Nominal::ViolationCause, 2) && payload.is_none() {
        return Ok(());
    }
    if *id != constructor(module, Nominal::ViolationCause, 4) {
        return Err(RuntimeFailure::ForeignBinding);
    }
    let Some(Value::Location(location)) = payload else {
        return Err(RuntimeFailure::ForeignBinding);
    };
    let location = super::resolve_location_with_work(heap, *location, work)?;
    super::charge_effect_work(work, 3, RuntimePhase::Access)?;
    if matches!(heap.get(location), Some(HeapCell::Tuple(fields))
        if matches!(fields.as_ref(), [Value::Integer(_), Value::Integer(_)]))
    {
        Ok(())
    } else {
        Err(RuntimeFailure::ForeignBinding)
    }
}

impl Machine<'_> {
    #[inline(never)]
    pub(super) fn return_source_violation_call(
        &mut self,
        apply: super::NodeId,
        callable: super::SourceByteCallable,
        caller: super::Instantiation,
        value: Value,
    ) -> Result<(), RuntimeFailure> {
        let (function, role) = match callable.intrinsic.operation() {
            Intrinsic::ForeignQuarantine { function } => (function, Role::CheckedQuarantine),
            Intrinsic::ForeignRejectAcquisition { function } => {
                (function, Role::CheckedRejectAcquisition)
            }
            _ => return Err(RuntimeFailure::ForeignBinding),
        };
        let reject = role == Role::CheckedRejectAcquisition;
        let program = self.program.clone();
        let fact = program
            .registry()
            .scalar_preflight(function)
            .ok_or(RuntimeFailure::ForeignBinding)?;
        if fact.role() != role || fact.module() != callable.intrinsic.module() {
            return Err(RuntimeFailure::ForeignBinding);
        }
        let Value::Location(location) = value else {
            return Err(RuntimeFailure::ForeignBinding);
        };
        let (key, cause_location) = if reject {
            (None, location)
        } else {
            let location = super::resolve_location_with_work(
                &self.heap,
                location,
                &mut self.instantiation_work,
            )?;
            super::charge_effect_work(&mut self.instantiation_work, 3, RuntimePhase::Access)?;
            let Some(HeapCell::Tuple(fields)) = self.heap.get(location) else {
                return Err(RuntimeFailure::ForeignBinding);
            };
            let [Value::NativeStateView(key), Value::Location(cause)] = fields.as_ref() else {
                return Err(RuntimeFailure::ForeignBinding);
            };
            (Some(*key), *cause)
        };
        cause(
            &self.heap,
            cause_location,
            fact.module(),
            &mut self.instantiation_work,
        )?;
        let PureExprKind::Computation(PureComputation::TypeApplication(application)) =
            super::pure_expression(&program, callable.application)?
        else {
            return Err(RuntimeFailure::ForeignBinding);
        };
        if application.arguments().len() != if reject { 1 } else { 2 }
            || !application.row_arguments().is_empty()
        {
            return Err(RuntimeFailure::ForeignBinding);
        }
        let mut selected = None;
        for (index, frame) in self.frames.iter().enumerate().rev() {
            super::charge_effect_work(&mut self.instantiation_work, 1, RuntimePhase::Access)?;
            let Frame::SourceResourceBoundary(boundary) = frame else {
                continue;
            };
            let Some(ExecutableNode::Effect(node)) = program.node(boundary.node) else {
                return Err(RuntimeFailure::ForeignBinding);
            };
            let EffectExprKind::Operation(EffectOperation::SourceResourceScope(scope)) = &node.kind
            else {
                return Err(RuntimeFailure::ForeignBinding);
            };
            let acquisition = if reject {
                boundary
                    .checked
                    .as_ref()
                    .and_then(|checked| checked.acquisition_request())
            } else {
                None
            };
            let call = SourceByteCall {
                apply: Some(apply),
                application: callable.application,
                function,
                acquisition,
            };
            if !scope
                .contains_violation_call(phase(boundary.phase), call, &mut self.instantiation_work)
                .map_err(|error| validation(error, &self.instantiation_work))?
            {
                continue;
            }
            if selected.is_some() || boundary.consumed || boundary.discarded {
                return Err(RuntimeFailure::ForeignBinding);
            }
            // Exact copied forest, every ordered Type/Row argument, selected H
            // and both original/actual callable instantiations remain fresh.
            for argument in scope.arguments() {
                let expected = boundary
                    .environment
                    .instantiation
                    .argument(argument, &mut self.instantiation_work)?;
                for context in [&callable.caller, &caller] {
                    let actual = context.argument(argument, &mut self.instantiation_work)?;
                    if !crate::types::same_kinded_argument_with_budget(
                        &expected,
                        &actual,
                        &mut self.instantiation_work,
                    )
                    .map_err(|()| {
                        super::effect_work_failure(
                            &self.instantiation_work,
                            None,
                            RuntimePhase::Access,
                        )
                    })? {
                        return Err(RuntimeFailure::ForeignBinding);
                    }
                }
            }
            let host = scope
                .header()
                .original
                .host
                .ok_or(RuntimeFailure::ForeignBinding)?;
            let selected_host = scope
                .arguments()
                .get(host.position)
                .ok_or(RuntimeFailure::ForeignBinding)?;
            let expected = boundary
                .environment
                .instantiation
                .argument(selected_host, &mut self.instantiation_work)?;
            let crate::types::KindedArgument::TypeArg(expected) = &*expected else {
                return Err(RuntimeFailure::ForeignBinding);
            };
            let applied = IterativeTypeOwner::new(
                callable
                    .caller
                    .ty(&application.arguments()[0], &mut self.instantiation_work)?,
            );
            let formal = role
                .host_parameter(fact.module())
                .ok_or(RuntimeFailure::ForeignBinding)?;
            let defining = IterativeTypeOwner::new(
                callable
                    .defining
                    .ty(&Type::Variable(formal), &mut self.instantiation_work)?,
            );
            for actual in [&applied, &defining] {
                if !crate::types::same_type_with_budget(
                    expected,
                    actual,
                    &mut self.instantiation_work,
                )
                .map_err(|()| {
                    super::effect_work_failure(&self.instantiation_work, None, RuntimePhase::Access)
                })? {
                    return Err(RuntimeFailure::ForeignBinding);
                }
            }
            selected = Some((index, call));
        }
        let (index, call) = selected.ok_or(RuntimeFailure::ForeignBinding)?;
        let Frame::SourceResourceBoundary(boundary) = &self.frames[index] else {
            return Err(RuntimeFailure::ForeignBinding);
        };
        let receipt = SourceOwnerViolationRequest::admit(
            &program,
            boundary.node,
            phase(boundary.phase),
            call,
            &mut self.instantiation_work,
        )?;
        let target = if reject {
            super::charge_effect_work(&mut self.instantiation_work, 1, RuntimePhase::Access)?;
            boundary
                .checked
                .as_ref()
                .ok_or(RuntimeFailure::ForeignBinding)?
                .prepaid_scope_observer()
        } else {
            let key = key.ok_or(RuntimeFailure::ForeignBinding)?;
            let PureExprKind::Computation(PureComputation::Apply(actual)) =
                super::pure_expression(&program, apply)?
            else {
                return Err(RuntimeFailure::ForeignBinding);
            };
            let operand = match program
                .node(actual.argument())
                .ok_or(RuntimeFailure::ForeignBinding)?
            {
                ExecutableNode::Effect(node) => &node.ty,
                ExecutableNode::Pure(node) => &node.ty,
            };
            let Type::Tuple(fields) = operand else {
                return Err(RuntimeFailure::ForeignBinding);
            };
            if fields.len() != 2 {
                return Err(RuntimeFailure::ForeignBinding);
            }
            let state =
                IterativeTypeOwner::new(caller.ty(&fields[0], &mut self.instantiation_work)?);
            let applied = IterativeTypeOwner::new(
                callable
                    .caller
                    .ty(&application.arguments()[1], &mut self.instantiation_work)?,
            );
            let formal = role
                .state_parameter(fact.module())
                .ok_or(RuntimeFailure::ForeignBinding)?;
            let defining = IterativeTypeOwner::new(
                callable
                    .defining
                    .ty(&Type::Variable(formal), &mut self.instantiation_work)?,
            );
            for actual in [&applied, &defining] {
                if !crate::types::same_type_with_budget(
                    &state,
                    actual,
                    &mut self.instantiation_work,
                )
                .map_err(|()| {
                    super::effect_work_failure(&self.instantiation_work, None, RuntimePhase::Access)
                })? {
                    return Err(RuntimeFailure::ForeignBinding);
                }
            }
            if key == boundary.key {
                if boundary.phase == ProviderPhase::Acquire {
                    return Err(RuntimeFailure::ForeignBinding);
                }
                let Some(ExecutableNode::Effect(node)) = program.node(boundary.node) else {
                    return Err(RuntimeFailure::ForeignBinding);
                };
                let EffectExprKind::Operation(EffectOperation::SourceResourceScope(scope)) =
                    &node.kind
                else {
                    return Err(RuntimeFailure::ForeignBinding);
                };
                let Type::Tuple(original) = scope.finish.parameter.ty() else {
                    return Err(RuntimeFailure::ForeignBinding);
                };
                let original = IterativeTypeOwner::new(boundary.environment.instantiation.ty(
                    original.first().ok_or(RuntimeFailure::ForeignBinding)?,
                    &mut self.instantiation_work,
                )?);
                if !crate::types::same_type_with_budget(
                    &state,
                    &original,
                    &mut self.instantiation_work,
                )
                .map_err(|()| {
                    super::effect_work_failure(&self.instantiation_work, None, RuntimePhase::Access)
                })? {
                    return Err(RuntimeFailure::ForeignBinding);
                }
                let owner = boundary
                    .owner
                    .as_ref()
                    .ok_or(RuntimeFailure::ForeignBinding)?;
                if !std::sync::Arc::ptr_eq(owner.owner(), &scope.header().owner)
                    || !owner.physically_live()
                {
                    return Err(RuntimeFailure::ForeignBinding);
                }
                owner
                    .checked_boundary(&mut self.instantiation_work)
                    .map_err(|error| owner_admission_failure(error, &self.instantiation_work))?
                    .ok_or(RuntimeFailure::ForeignBinding)?
            } else {
                let bindings = self.source_bindings.ok_or(RuntimeFailure::ForeignBinding)?;
                let dependency =
                    bindings.denial_owner(key.0 as usize, &state, &mut self.instantiation_work)?;
                let retained = if let Some(owner) = boundary.owner.as_ref() {
                    super::charge_effect_work(
                        &mut self.instantiation_work,
                        owner.retained_dependency_count(),
                        RuntimePhase::Access,
                    )?;
                    owner.retains(&dependency)
                } else if boundary.phase == ProviderPhase::Acquire {
                    super::charge_effect_work(
                        &mut self.instantiation_work,
                        boundary.dependencies.len(),
                        RuntimePhase::Access,
                    )?;
                    boundary
                        .dependencies
                        .iter()
                        .any(|original| original.same_slot(&dependency))
                } else {
                    false
                };
                if !retained {
                    return Err(RuntimeFailure::ForeignBinding);
                }
                dependency
                    .checked_boundary(&mut self.instantiation_work)
                    .map_err(|error| owner_admission_failure(error, &self.instantiation_work))?
            }
        };
        // No caller/cause data is copied into these independent native facts.
        let (native, unresolved, status) = target
            .deny(
                &receipt,
                boundary.key.0 as usize,
                &mut self.instantiation_work,
            )
            .map_err(|error| owner_admission_failure(error, &self.instantiation_work))?;
        let Frame::SourceResourceBoundary(boundary) = &mut self.frames[index] else {
            unreachable!();
        };
        boundary.blocked = true;
        let native = match native {
            crate::foreign::source_runtime::CheckedNativeFact::NoOwner => {
                crate::eval::ResourceNativeFact::NoOwner
            }
            crate::foreign::source_runtime::CheckedNativeFact::Owned => {
                crate::eval::ResourceNativeFact::Owned
            }
            crate::foreign::source_runtime::CheckedNativeFact::Consumed => {
                crate::eval::ResourceNativeFact::Consumed
            }
        };
        // Any work/storage failure from here is terminal X1 with the shared
        // denial already installed. This ordinary value is no Finish witness.
        let module = fact.module();
        let record = self.checked_observation_record(module, native, unresolved, status)?;
        let failure = self.foreign_constructor(
            constructor(module, Nominal::BoundaryFailure, 2),
            Some(record),
            RuntimePhase::Access,
        )?;
        let result = self.foreign_constructor(
            constructor(module, Nominal::CheckedCall, 2),
            Some(failure),
            RuntimePhase::Access,
        )?;
        self.control = Some(Control::Return(result));
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::core::PureValue;
    use crate::foreign::source_bindings::with_violation_boundary_for_test;
    use crate::types::Kind;

    #[test]
    fn checked_violation_dispatch_preserves_native_facts_and_never_mints_finish() {
        for (reject, present) in [(true, false), (true, true), (false, true)] {
            with_violation_boundary_for_test(reject, present, |fixture| {
                let mut machine = Machine::new_effect(fixture.program);
                machine.control = None;
                let before = fixture.boundary.snapshot();
                let checked = fixture.boundary.prepaid_scope_observer();
                let module = fixture
                    .program
                    .registry()
                    .scalar_preflight(fixture.call.function)
                    .unwrap()
                    .module();
                let intrinsic = fixture.program.nodes().iter().find_map(|node| match &node.kind {
                    EffectExprKind::Pure(PureExprKind::Value(PureValue::Intrinsic(intrinsic)))
                        if matches!(intrinsic.operation(), Intrinsic::ForeignQuarantine { function }
                            | Intrinsic::ForeignRejectAcquisition { function } if function == fixture.call.function) => Some(*intrinsic),
                    _ => None,
                }).unwrap();
                let role = if reject {
                    Role::CheckedRejectAcquisition
                } else {
                    Role::CheckedQuarantine
                };
                let caller = super::super::Instantiation::default();
                let PureExprKind::Computation(PureComputation::TypeApplication(application)) =
                    super::super::pure_expression(&machine.program, fixture.call.application)
                        .unwrap()
                else {
                    unreachable!();
                };
                let mut parameters = vec![(role.host_parameter(module).unwrap(), Kind::Type)];
                if let Some(state) = role.state_parameter(module) {
                    parameters.push((state, Kind::Type));
                }
                let defining = super::super::Instantiation::default()
                    .apply(
                        &caller,
                        &parameters,
                        application.arguments(),
                        application.row_arguments(),
                        &mut TypeWorkBudget::default(),
                    )
                    .unwrap();
                let callable = super::super::SourceByteCallable {
                    intrinsic,
                    application: fixture.call.application,
                    caller: caller.clone(),
                    defining,
                };
                let boundary = Box::new(super::super::SourceResourceBoundary {
                    checked: Some(fixture.boundary),
                    report_slot: None,
                    node: fixture.scope,
                    key: super::super::ActivationKey(111),
                    environment: super::super::Environment::new(),
                    owner: fixture.guard,
                    dependencies: Vec::new(),
                    phase: if reject {
                        ProviderPhase::Acquire
                    } else {
                        ProviderPhase::Body
                    },
                    payload: None,
                    saved: None,
                    consumed: false,
                    blocked: false,
                    discarded: false,
                });
                machine.frames.push(Frame::SourceResourceBoundary(boundary));
                let cause = machine
                    .foreign_constructor(
                        constructor(module, Nominal::ViolationCause, 0),
                        Some(Value::Integer(if reject {
                            crate::integer::Integer::from_i64(999)
                        } else {
                            crate::integer::Integer::parse_decimal(&"9".repeat(8192)).unwrap()
                        })),
                        RuntimePhase::Access,
                    )
                    .unwrap();
                let value = if reject {
                    cause
                } else {
                    machine
                        .foreign_tuple(
                            &[
                                Value::NativeStateView(super::super::ActivationKey(111)),
                                cause,
                            ],
                            RuntimePhase::Access,
                        )
                        .unwrap()
                };
                let repeated_callable = callable.clone();
                let repeated_caller = caller.clone();
                let repeated_value =
                    super::super::copy_generic_cell_value(&value, &mut machine.instantiation_work)
                        .unwrap();
                machine
                    .return_source_violation_call(
                        fixture.call.apply.unwrap(),
                        callable,
                        caller,
                        value,
                    )
                    .unwrap();
                machine.control = None;
                machine
                    .return_source_violation_call(
                        fixture.call.apply.unwrap(),
                        repeated_callable,
                        repeated_caller,
                        repeated_value,
                    )
                    .unwrap();
                let after = checked.snapshot();
                assert_eq!(
                    (after.native, after.k, after.observations, after.history),
                    (before.native, before.k, before.observations, before.history)
                );
                assert!(
                    machine.checked_reports.is_none(),
                    "primitive inserts no completion report"
                );
                let Some(Control::Return(Value::Location(result))) = machine.control.as_ref()
                else {
                    panic!("ordinary BoundaryFailed value");
                };
                assert!(
                    matches!(machine.heap.get(*result), Some(HeapCell::Constructor(id, _))
                    if *id == constructor(module, Nominal::CheckedCall, 2))
                );
                let Frame::SourceResourceBoundary(boundary) = &machine.frames[0] else {
                    unreachable!();
                };
                assert!(boundary.blocked);
                assert!(
                    !boundary
                        .owner
                        .as_ref()
                        .is_some_and(|owner| owner.ordinary_live())
                );
                assert_eq!(checked.retains_backing(), present);
                // Exercise the actual source-request preparation/operand loop,
                // including the Rust-backed route whose denied raw address may
                // not be fetched. Only that matched request produces K6.
                if !reject {
                    machine.source_bindings = Some(&fixture.bindings);
                    let mut setup = TypeWorkBudget::default();
                    let mut reports =
                        crate::eval::checked_reports::ResourceReports::reserve(1, &mut setup)
                            .unwrap();
                    let slot = reports.reserve_owner(&mut setup).unwrap();
                    machine.checked_reports = Some(reports);
                    machine.live_resources = 1;
                    let Frame::SourceResourceBoundary(boundary) = &mut machine.frames[0] else {
                        unreachable!();
                    };
                    boundary.report_slot = Some(slot);
                    boundary.phase = ProviderPhase::Finish;
                    boundary.saved = Some(Value::Integer(crate::integer::Integer::from_i64(42)));
                    checked.closing(111, fixture.scope, &mut setup).unwrap();
                    machine.control = None;
                    machine
                        .prepare_source_owner_request(
                            fixture.finish_node,
                            fixture.finish_symbol.operation(),
                            fixture.finish_instance.clone(),
                            Value::NativeStateView(super::super::ActivationKey(111)),
                            &fixture.finish_symbol,
                        )
                        .unwrap();
                    assert!(machine.step_source_owner().unwrap());
                    assert_eq!(
                        checked.snapshot().k,
                        crate::foreign::source_runtime::CheckedLocalCompletion::Discharged
                    );
                    assert_eq!(checked.snapshot().native, before.native);
                    assert_eq!(checked.snapshot().observations, before.observations);
                    // Invocation discharges K6; recording and source reporting
                    // remain separate mandatory machine transitions.
                    assert!(machine.step_source_owner().unwrap());
                    assert!(machine.step_source_owner().unwrap());
                    let Some(Control::Return(Value::Location(result))) = machine.control.take()
                    else {
                        panic!("matched teardown report");
                    };
                    let Some(HeapCell::Constructor(id, Some(Value::Location(reason)))) =
                        machine.heap.get(result)
                    else {
                        panic!("private synthetic failure");
                    };
                    assert_eq!(*id, constructor(module, Nominal::CheckedCall, 2));
                    let reason = *reason;
                    let finish = machine
                        .foreign_constructor(
                            constructor(module, Nominal::CheckedFinish, 2),
                            Some(Value::Location(reason)),
                            RuntimePhase::Cleanup,
                        )
                        .unwrap();
                    let Some(Frame::SourceResourceBoundary(boundary)) = machine.frames.pop() else {
                        unreachable!();
                    };
                    machine.return_source_resource(boundary, finish).unwrap();
                    assert_eq!(
                        checked.snapshot().continuation,
                        crate::foreign::source_runtime::CheckedOwnerContinuation::Completed
                    );
                    assert_eq!(machine.checked_reports.as_ref().unwrap().record_count(), 1);
                    assert!(checked.retains_backing());
                }
            });
        }
    }

    #[test]
    fn checked_violation_report_exhaustion_preserves_installed_denial() {
        with_violation_boundary_for_test(false, true, |fixture| {
            let mut machine = Machine::new_effect(fixture.program);
            machine.control = None;
            let mut work = TypeWorkBudget::default();
            let receipt = SourceOwnerViolationRequest::admit(
                &machine.program,
                fixture.scope,
                SourceResourcePhase::Handler,
                fixture.call,
                &mut work,
            )
            .unwrap();
            let before = fixture.boundary.snapshot();
            let (native, unresolved, status) =
                fixture.boundary.deny(&receipt, 111, &mut work).unwrap();
            assert_eq!(native, before.native);
            let module = fixture
                .program
                .registry()
                .scalar_preflight(fixture.call.function)
                .unwrap()
                .module();
            machine.instantiation_work = TypeWorkBudget::with_limit(0);
            assert!(
                machine
                    .checked_observation_record(
                        module,
                        crate::eval::ResourceNativeFact::Owned,
                        unresolved,
                        status
                    )
                    .is_err()
            );
            assert!(
                machine.control.is_none(),
                "no healthy continuation after mandatory report failure"
            );
            assert!(!fixture.guard.as_ref().unwrap().ordinary_live());
            let after = fixture.boundary.snapshot();
            assert_eq!(
                (after.native, after.k, after.observations),
                (before.native, before.k, before.observations)
            );
            assert!(fixture.boundary.retains_backing());
        });
    }
}
