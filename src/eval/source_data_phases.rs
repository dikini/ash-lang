//! Ordinary payload access under one original source descriptor and live guard.
//! These operations cannot invoke native code or change ownership disposition.

use super::{
    Control, ExecutableNode, Frame, HeapCell, Machine, ProviderPhase, RuntimeFailure, RuntimePhase,
    Value,
};
use crate::{
    core::{EffectExprKind, EffectOperation, PureComputation, PureExprKind, packed::Intrinsic},
    foreign::{scalar_preflight::ForeignScalarPreflightRole, source_runtime::NativeOwnerViewKind},
    types::{IterativeTypeOwner, Type},
};

impl Machine<'_> {
    #[inline(never)]
    pub(super) fn return_source_data_call(
        &mut self,
        apply: super::NodeId,
        callable: super::SourceByteCallable,
        caller: super::Instantiation,
        value: Value,
    ) -> Result<(), RuntimeFailure> {
        let (function, role) = match callable.intrinsic.operation() {
            Intrinsic::ForeignDataOf { function } => (function, ForeignScalarPreflightRole::DataOf),
            Intrinsic::ForeignReplaceData { function } => {
                (function, ForeignScalarPreflightRole::ReplaceData)
            }
            _ => return Err(RuntimeFailure::ForeignBinding),
        };
        let replace = role == ForeignScalarPreflightRole::ReplaceData;
        let program = self.program.clone();
        let fact = program
            .registry()
            .scalar_preflight(function)
            .ok_or(RuntimeFailure::ForeignBinding)?;
        if fact.function() != function
            || fact.role() != role
            || fact.module() != callable.intrinsic.module()
        {
            return Err(RuntimeFailure::ForeignBinding);
        }
        let state_parameter = role
            .state_parameter(fact.module())
            .ok_or(RuntimeFailure::ForeignBinding)?;
        let data_parameter = role
            .data_parameter(fact.module())
            .ok_or(RuntimeFailure::ForeignBinding)?;
        let (state, replacement) = if replace {
            let Value::Location(location) = &value else {
                return Err(RuntimeFailure::ForeignBinding);
            };
            let location = super::resolve_location_with_work(
                &self.heap,
                *location,
                &mut self.instantiation_work,
            )?;
            let Some(HeapCell::Tuple(fields)) = self.heap.get(location) else {
                return Err(RuntimeFailure::ForeignBinding);
            };
            super::charge_effect_work(
                &mut self.instantiation_work,
                fields.len(),
                RuntimePhase::Access,
            )?;
            if fields.len() != 2 {
                return Err(RuntimeFailure::ForeignBinding);
            }
            (fields[0].clone(), Some(fields[1].clone()))
        } else {
            (value, None)
        };
        let Value::NativeStateView(key) = state else {
            return Err(RuntimeFailure::ForeignBinding);
        };
        let PureExprKind::Computation(PureComputation::TypeApplication(application)) =
            super::pure_expression(&program, callable.application)?
        else {
            return Err(RuntimeFailure::ForeignBinding);
        };
        if application.arguments().len() != 2 || !application.row_arguments().is_empty() {
            return Err(RuntimeFailure::ForeignBinding);
        }
        let PureExprKind::Computation(PureComputation::Apply(call)) =
            super::pure_expression(&program, apply)?
        else {
            return Err(RuntimeFailure::ForeignBinding);
        };
        let argument_type = match program
            .node(call.argument())
            .ok_or(RuntimeFailure::ForeignBinding)?
        {
            ExecutableNode::Pure(node) => &node.ty,
            ExecutableNode::Effect(node) => &node.ty,
        };
        let (operand_state, operand_data) = if replace {
            let Type::Tuple(fields) = argument_type else {
                return Err(RuntimeFailure::ForeignBinding);
            };
            if fields.len() != 2 {
                return Err(RuntimeFailure::ForeignBinding);
            }
            (&fields[0], &fields[1])
        } else {
            let output = match program.node(apply).ok_or(RuntimeFailure::ForeignBinding)? {
                ExecutableNode::Pure(node) => &node.ty,
                ExecutableNode::Effect(node) => &node.ty,
            };
            (argument_type, output)
        };
        let mut selected = None;
        let mut payload_type = None;
        for (index, frame) in self.frames.iter().enumerate().rev() {
            super::charge_effect_work(&mut self.instantiation_work, 1, RuntimePhase::Access)?;
            let Frame::SourceResourceBoundary(boundary) = frame else {
                continue;
            };
            if boundary.key != key {
                continue;
            }
            if selected.is_some()
                || boundary.consumed
                || boundary.phase == ProviderPhase::Acquire
                || boundary.payload.is_none()
            {
                return Err(RuntimeFailure::ForeignBinding);
            }
            let Some(ExecutableNode::Effect(stored)) = program.node(boundary.node) else {
                return Err(RuntimeFailure::ForeignBinding);
            };
            let EffectExprKind::Operation(EffectOperation::SourceResourceScope(scope)) =
                &stored.kind
            else {
                return Err(RuntimeFailure::ForeignBinding);
            };
            let owner = boundary
                .owner
                .as_ref()
                .ok_or(RuntimeFailure::ForeignBinding)?;
            if !std::sync::Arc::ptr_eq(owner.owner(), &scope.header().owner)
                || boundary.phase == ProviderPhase::Body && !owner.ordinary_live()
                || !scope
                    .contains_byte_call(
                        if boundary.phase == ProviderPhase::Finish {
                            crate::core::source_resource::SourceResourcePhase::Finish
                        } else {
                            crate::core::source_resource::SourceResourcePhase::Handler
                        },
                        apply,
                        callable.application,
                        function,
                        &mut self.instantiation_work,
                    )
                    .map_err(|failure| {
                        if failure.reason() == crate::core::ValidationReason::Resource {
                            super::effect_work_failure(
                                &self.instantiation_work,
                                None,
                                RuntimePhase::Access,
                            )
                        } else {
                            RuntimeFailure::ForeignBinding
                        }
                    })?
            {
                return Err(RuntimeFailure::ForeignBinding);
            }
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
            let Type::Tuple(state_data) = scope.finish.parameter.ty() else {
                return Err(RuntimeFailure::ForeignBinding);
            };
            if state_data.len() != 2 {
                return Err(RuntimeFailure::ForeignBinding);
            }
            for (position, formal, operand) in [
                (0, state_parameter, operand_state),
                (1, data_parameter, operand_data),
            ] {
                let expected = IterativeTypeOwner::new(
                    boundary
                        .environment
                        .instantiation
                        .ty(&state_data[position], &mut self.instantiation_work)?,
                );
                let operand =
                    IterativeTypeOwner::new(caller.ty(operand, &mut self.instantiation_work)?);
                let applied = IterativeTypeOwner::new(callable.caller.ty(
                    &application.arguments()[position],
                    &mut self.instantiation_work,
                )?);
                let defining = IterativeTypeOwner::new(
                    callable
                        .defining
                        .ty(&Type::Variable(formal), &mut self.instantiation_work)?,
                );
                for actual in [&operand, &applied, &defining] {
                    if !crate::types::same_type_with_budget(
                        &expected,
                        actual,
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
                if position == 1 {
                    payload_type = Some(expected);
                }
            }
            selected = Some(index);
        }
        let selected = selected.ok_or(RuntimeFailure::ForeignBinding)?;
        let payload_type = payload_type.ok_or(RuntimeFailure::ForeignBinding)?;
        let Frame::SourceResourceBoundary(boundary) = &self.frames[selected] else {
            return Err(RuntimeFailure::ForeignBinding);
        };
        let payload = replacement.unwrap_or_else(|| {
            boundary
                .payload
                .as_ref()
                .expect("checked current payload")
                .clone()
        });
        let bindings = self.source_bindings.ok_or(RuntimeFailure::ForeignBinding)?;
        // A copied or replacement value cannot add a donor, closing identity,
        // State/view or dependency beyond the closure admitted on acquisition.
        super::source_resource_phases::visit_typed_source_values(
            &self.heap,
            program.registry(),
            payload_type,
            &payload,
            &mut self.instantiation_work,
            |ty, value, work| {
                let Value::ResourceHandle(key) = value else {
                    return if matches!(value, Value::NativeStateView(_)) {
                        Err(RuntimeFailure::ForeignBinding)
                    } else {
                        Ok(false)
                    };
                };
                let dependency = bindings.borrowed_owner(
                    key.0 as usize,
                    ty,
                    NativeOwnerViewKind::Access,
                    if boundary.phase == ProviderPhase::Finish {
                        boundary.owner.as_ref()
                    } else {
                        None
                    },
                    work,
                )?;
                let owner = boundary
                    .owner
                    .as_ref()
                    .ok_or(RuntimeFailure::ForeignBinding)?;
                super::charge_effect_work(
                    work,
                    owner.retained_dependency_count(),
                    RuntimePhase::Access,
                )?;
                if !owner.retains(&dependency) {
                    return Err(RuntimeFailure::ForeignBinding);
                }
                Ok(true)
            },
        )?;
        super::charge_effect_work(&mut self.instantiation_work, 1, RuntimePhase::Access)?;
        // Dispose complete owned specialization metadata before publishing a
        // replacement. The remaining commit cannot allocate, charge or call C.
        drop(callable);
        drop(caller);
        if replace {
            let Frame::SourceResourceBoundary(boundary) = &mut self.frames[selected] else {
                return Err(RuntimeFailure::ForeignBinding);
            };
            boundary.payload = Some(payload);
            self.control = Some(Control::Return(Value::Unit));
        } else {
            self.control = Some(Control::Return(payload));
        }
        Ok(())
    }
}
