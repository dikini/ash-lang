//! Exact nonowning lexical-window activation and copied-result admission.
//!
//! A window does not acquire, release or clone an owner. The original source
//! forest, full specialization and selected lifecycle phase remain independent
//! of the physical guard and of every generated callback.

use std::sync::Arc;

use super::{
    ActivationKey, Control, Environment, ExecutableNode, Frame, Machine, NodeId, ProviderPhase,
    RuntimeFailure, RuntimePhase, SourceWindowBoundary, Value,
};
use crate::{
    core::{EffectExprKind, EffectOperation, source_resource::SourceResourcePhase},
    foreign::{
        checked_source::{CheckedForeignSymbol, ForeignAdmissionError},
        source_runtime::{NativeOwnerViewKind, NativeViewReturned},
    },
    types::{IterativeTypeOwner, TypeWorkBudget},
};

/// Private coordinate of a view in one live lexical activation. It carries no
/// pointer, owner or source permission and has no ordinary Ash constructor.
#[doc(hidden)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct WindowViewKey {
    window: ActivationKey,
    slot: usize,
}

/// A copied length still names the exact originating view. No ordinary Int can
/// be converted to this opaque evidence.
#[doc(hidden)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct WindowExtentKey {
    view: WindowViewKey,
    length: usize,
}

#[derive(Debug)]
pub(super) struct WindowView {
    raw: NativeViewReturned,
    symbol: Arc<CheckedForeignSymbol>,
    // Retain immutable, already evaluated logical key leaves. Native integer
    // widths need not agree between the view producer and its extent query.
    operands: Value,
}

#[derive(Debug)]
pub(super) struct WindowArguments(Vec<crate::types::KindedArgument>);
impl Drop for WindowArguments {
    fn drop(&mut self) {
        for argument in self.0.drain(..) {
            crate::types::discard_kinded_argument_iteratively(argument);
        }
    }
}

pub(super) fn phase(phase: ProviderPhase) -> SourceResourcePhase {
    match phase {
        ProviderPhase::Acquire => SourceResourcePhase::Acquire,
        ProviderPhase::Body => SourceResourcePhase::Handler,
        ProviderPhase::Finish => SourceResourcePhase::Finish,
    }
}

pub(super) fn foreign_failure(
    error: ForeignAdmissionError,
    work: &TypeWorkBudget,
) -> RuntimeFailure {
    if error.is_resource_exhaustion() {
        super::effect_work_failure(work, None, RuntimePhase::Access)
    } else {
        RuntimeFailure::ForeignBinding
    }
}

pub(super) fn validation_failure(
    error: crate::core::ValidationError,
    work: &TypeWorkBudget,
) -> RuntimeFailure {
    if error.reason() == crate::core::ValidationReason::Resource {
        super::effect_work_failure(work, None, RuntimePhase::Access)
    } else {
        RuntimeFailure::ForeignBinding
    }
}

impl Machine<'_> {
    #[inline(never)]
    pub(super) fn enter_source_window(
        &mut self,
        node: NodeId,
        mut environment: Environment,
        state: Value,
    ) -> Result<(), RuntimeFailure> {
        let Value::NativeStateView(owner_key) = state else {
            return Err(RuntimeFailure::ForeignBinding);
        };
        let program = self.program.clone();
        let Some(ExecutableNode::Effect(expression)) = program.node(node) else {
            return Err(RuntimeFailure::ForeignBinding);
        };
        let EffectExprKind::Operation(EffectOperation::SourceCopyWindow(window)) = &expression.kind
        else {
            return Err(RuntimeFailure::ForeignBinding);
        };
        let (original_owner, state_type) = crate::foreign::source_access::window_state_type(
            window.family(),
            window.arguments().iter(),
            window.identity(),
            program.registry(),
            &mut self.instantiation_work,
        )
        .map_err(|error| foreign_failure(error, &self.instantiation_work))?;
        let state_type = IterativeTypeOwner::new(
            environment
                .instantiation
                .ty(&state_type, &mut self.instantiation_work)?,
        );
        let mut provider = None;
        for (index, frame) in self.frames.iter().enumerate().rev() {
            super::charge_effect_work(&mut self.instantiation_work, 1, RuntimePhase::Access)?;
            let Frame::SourceResourceBoundary(boundary) = frame else {
                continue;
            };
            let Some(ExecutableNode::Effect(expression)) = program.node(boundary.node) else {
                return Err(RuntimeFailure::ForeignBinding);
            };
            let EffectExprKind::Operation(EffectOperation::SourceResourceScope(scope)) =
                &expression.kind
            else {
                return Err(RuntimeFailure::ForeignBinding);
            };
            if !scope
                .contains_phase_window(phase(boundary.phase), node, &mut self.instantiation_work)
                .map_err(|error| validation_failure(error, &self.instantiation_work))?
            {
                continue;
            }
            if (boundary.consumed || boundary.blocked) && boundary.key == owner_key {
                return Err(RuntimeFailure::ForeignBinding);
            }
            // The same original window occurrence must still run in its
            // defining provider specialization, including phantom row actuals.
            for argument in scope.arguments() {
                let original = boundary
                    .environment
                    .instantiation
                    .argument(argument, &mut self.instantiation_work)?;
                let current = environment
                    .instantiation
                    .argument(argument, &mut self.instantiation_work)?;
                if !crate::types::same_kinded_argument_with_budget(
                    &original,
                    &current,
                    &mut self.instantiation_work,
                )
                .map_err(|()| {
                    super::effect_work_failure(&self.instantiation_work, None, RuntimePhase::Access)
                })? {
                    return Err(RuntimeFailure::ForeignBinding);
                }
            }
            provider = Some(index);
            break;
        }
        let provider = provider.ok_or(RuntimeFailure::ForeignBinding)?;
        let Frame::SourceResourceBoundary(boundary) = &self.frames[provider] else {
            return Err(RuntimeFailure::ForeignBinding);
        };
        let provider_key = boundary.key;
        if owner_key == provider_key {
            let guard = boundary
                .owner
                .as_ref()
                .ok_or(RuntimeFailure::ForeignBinding)?;
            // A related owner can deny this group without changing this frame's
            // local blocked flag, including while Finish uses cached windows.
            if guard.shared_group_denied(&mut self.instantiation_work)
                .map_err(|error| crate::foreign::source_bindings::owner_admission_failure(error, &self.instantiation_work))?
            {
                return Err(RuntimeFailure::ForeignBinding);
            }
            if boundary.phase == ProviderPhase::Body {
                guard.pay_group_checks(1, &mut self.instantiation_work)
                    .map_err(|error| crate::foreign::source_bindings::owner_admission_failure(error, &self.instantiation_work))?;
            }
            if !Arc::ptr_eq(guard.owner(), &original_owner)
                || !guard.physically_live()
                || boundary.phase == ProviderPhase::Body && !guard.ordinary_live()
            {
                return Err(RuntimeFailure::ForeignBinding);
            }
            let Some(ExecutableNode::Effect(expression)) = program.node(boundary.node) else {
                return Err(RuntimeFailure::ForeignBinding);
            };
            let EffectExprKind::Operation(EffectOperation::SourceResourceScope(scope)) =
                &expression.kind
            else {
                return Err(RuntimeFailure::ForeignBinding);
            };
            let crate::types::Type::Tuple(fields) = scope.finish.parameter.ty() else {
                return Err(RuntimeFailure::ForeignBinding);
            };
            let expected = IterativeTypeOwner::new(boundary.environment.instantiation.ty(
                fields.first().ok_or(RuntimeFailure::ForeignBinding)?,
                &mut self.instantiation_work,
            )?);
            if !crate::types::same_type_with_budget(
                &state_type,
                &expected,
                &mut self.instantiation_work,
            )
            .map_err(|()| {
                super::effect_work_failure(&self.instantiation_work, None, RuntimePhase::Access)
            })? {
                return Err(RuntimeFailure::ForeignBinding);
            }
        } else {
            let bindings = self.source_bindings.ok_or(RuntimeFailure::ForeignBinding)?;
            let completion = (boundary.phase == ProviderPhase::Finish)
                .then_some(boundary.owner.as_ref())
                .flatten();
            let dependency = bindings.borrowed_owner(
                owner_key.0 as usize,
                &state_type,
                NativeOwnerViewKind::State,
                completion,
                &mut self.instantiation_work,
            )?;
            if dependency.shared_group_denied(&mut self.instantiation_work)
                .map_err(|error| crate::foreign::source_bindings::owner_admission_failure(error, &self.instantiation_work))?
            {
                return Err(RuntimeFailure::ForeignBinding);
            }
            super::charge_effect_work(
                &mut self.instantiation_work,
                boundary.dependencies.len(),
                RuntimePhase::Access,
            )?;
            if !boundary
                .dependencies
                .iter()
                .any(|known| known.same_slot(&dependency))
                || completion.is_some_and(|guard| !guard.retains(&dependency))
            {
                return Err(RuntimeFailure::ForeignBinding);
            }
            // A blocked close permits no native access to that physical owner,
            // even when the selected completing provider is another resource.
            for frame in &self.frames {
                super::charge_effect_work(&mut self.instantiation_work, 1, RuntimePhase::Access)?;
                if matches!(frame, Frame::SourceResourceBoundary(owner) if owner.key == owner_key && (owner.blocked || owner.consumed))
                {
                    return Err(RuntimeFailure::ForeignBinding);
                }
            }
        }
        let key = ActivationKey(self.next_activation);
        let next = self
            .next_activation
            .checked_add(1)
            .ok_or(RuntimeFailure::ResourceCapacity)?;
        super::charge_effect_work(&mut self.instantiation_work, 1, RuntimePhase::Access)?;
        self.frames
            .try_reserve(1)
            .map_err(|_| RuntimeFailure::ResourceCapacity)?;
        environment.instantiation = environment.instantiation.acquire(
            window.identity(),
            key,
            &mut self.instantiation_work,
            Some(RuntimePhase::Access),
        )?;
        let mut arguments = WindowArguments(Vec::new());
        super::charge_effect_work(
            &mut self.instantiation_work,
            window.arguments().len(),
            RuntimePhase::Access,
        )?;
        arguments
            .0
            .try_reserve_exact(window.arguments().len())
            .map_err(|_| RuntimeFailure::EnvironmentCapacity)?;
        for argument in window.arguments() {
            arguments.0.push(
                environment
                    .instantiation
                    .argument(argument, &mut self.instantiation_work)?
                    .into_inner(),
            );
        }
        let boundary = Box::new(SourceWindowBoundary {
            node,
            key,
            provider: provider_key,
            owner: owner_key,
            environment: environment.clone(),
            views: Vec::new(),
            arguments,
        });
        self.frames.push(Frame::SourceWindowBoundary(boundary));
        self.next_activation = next;
        self.max_frame_depth = self.max_frame_depth.max(self.frames.len());
        self.control = Some(Control::Evaluate(window.body(), environment));
        Ok(())
    }
}

impl Machine<'_> {
    /// Admit every active window's preservation rule before selecting the exact
    /// lexical interpretation. Ordinary native interpretation cannot replace it.
    #[inline(never)]
    pub(super) fn prepare_source_window_request(
        &mut self,
        request: NodeId,
        instance: crate::types::EffectInstance,
        value: Value,
        symbol: &Arc<CheckedForeignSymbol>,
    ) -> Result<(), RuntimeFailure> {
        use crate::foreign::{
            source_bindings::SourceWindowRaw,
            source_contract::{
                PreparedAccessResult, PreparedOperandSource, PreparedOwnerCall,
                PreparedRepresentation,
            },
            source_runtime::{
                NativeOwnerOperand, NativeScalarConversionError, PrepaidScalarReport,
                narrow_gnu_scalar, widen_gnu_reply,
            },
        };
        if self.pending_source_owner_call.is_some()
            || self.pending_source_call.is_some()
            || self.control.is_some()
        {
            return Err(RuntimeFailure::ForeignBinding);
        }
        let program = self.program.clone();
        let mut selected = None;
        for (index, frame) in self.frames.iter().enumerate().rev() {
            super::charge_effect_work(&mut self.instantiation_work, 1, RuntimePhase::Access)?;
            let Frame::SourceWindowBoundary(boundary) = frame else {
                continue;
            };
            let Some(ExecutableNode::Effect(expression)) = program.node(boundary.node) else {
                return Err(RuntimeFailure::ForeignBinding);
            };
            let EffectExprKind::Operation(EffectOperation::SourceCopyWindow(window)) =
                &expression.kind
            else {
                return Err(RuntimeFailure::ForeignBinding);
            };
            if !crate::foreign::source_access::window_operation_matches(
                window.family(),
                &boundary.arguments.0,
                symbol,
                &instance,
                program.registry(),
                &mut self.instantiation_work,
            )
            .map_err(|error| foreign_failure(error, &self.instantiation_work))?
            {
                return Err(RuntimeFailure::ForeignBinding);
            }
            if selected.is_some() {
                continue;
            }
            for interpretation in window.interpretations() {
                super::charge_effect_work(&mut self.instantiation_work, 1, RuntimePhase::Access)?;
                if !Arc::ptr_eq(interpretation.symbol(), symbol) {
                    continue;
                }
                let expected = boundary.environment.instantiation.effect(
                    interpretation.effect(),
                    &mut self.instantiation_work,
                    Some(RuntimePhase::Access),
                )?;
                if super::source_owner_phases::same_instance(
                    &expected,
                    &instance,
                    &mut self.instantiation_work,
                )? {
                    selected = Some(index);
                    break;
                }
            }
        }
        let selected = selected.ok_or(RuntimeFailure::ForeignBinding)?;
        let Frame::SourceWindowBoundary(window) = &self.frames[selected] else {
            return Err(RuntimeFailure::ForeignBinding);
        };
        let provider_key = window.provider;
        let owner_key = window.owner;
        let window_key = window.key;
        super::charge_effect_work(
            &mut self.instantiation_work,
            self.frames.len(),
            RuntimePhase::Access,
        )?;
        let provider = self.frames.iter().rposition(|frame| matches!(frame, Frame::SourceResourceBoundary(boundary) if boundary.key == provider_key)).ok_or(RuntimeFailure::ForeignBinding)?;
        let Frame::SourceResourceBoundary(boundary) = &self.frames[provider] else {
            return Err(RuntimeFailure::ForeignBinding);
        };
        let source_phase = phase(boundary.phase);
        let bindings = self.source_bindings.ok_or(RuntimeFailure::ForeignBinding)?;
        let invocation = bindings.admit_source_window_invocation(
            &program,
            boundary.node,
            window.node,
            request,
            source_phase,
            &window.arguments.0,
            &instance,
            symbol,
            &mut self.instantiation_work,
        )?;
        let Some(PreparedOwnerCall::Borrow {
            current_operand, ..
        }) = symbol.owner_role()
        else {
            return Err(RuntimeFailure::ForeignBinding);
        };
        let extent_view = if let Some(PreparedAccessResult::Extent { view, keys, .. }) =
            symbol.symbol().access_result()
        {
            let Value::NativeWindowView(key) =
                value_leaf(&self.heap, &value, view, &mut self.instantiation_work)?
            else {
                return Err(RuntimeFailure::ForeignBinding);
            };
            if key.window != window_key {
                return Err(RuntimeFailure::ForeignBinding);
            }
            let record = window
                .views
                .get(key.slot)
                .ok_or(RuntimeFailure::ForeignBinding)?;
            let Some(PreparedAccessResult::View {
                keys: original_keys,
                ..
            }) = record.symbol.symbol().access_result()
            else {
                return Err(RuntimeFailure::ForeignBinding);
            };
            if original_keys.len() != keys.len() {
                return Err(RuntimeFailure::ForeignBinding);
            }
            for (original, current) in original_keys.iter().zip(keys) {
                let original = super::source_scalar_phases::source_integer_leaf(
                    &self.heap,
                    &record.operands,
                    original,
                    &mut self.instantiation_work,
                )?;
                let current = super::source_scalar_phases::source_integer_leaf(
                    &self.heap,
                    &value,
                    current,
                    &mut self.instantiation_work,
                )?;
                let units = original
                    .magnitude_byte_length()
                    .checked_add(current.magnitude_byte_length())
                    .and_then(|units| usize::try_from(units).ok())
                    .ok_or(RuntimeFailure::ResourceCapacity)?;
                super::charge_effect_work(
                    &mut self.instantiation_work,
                    units.saturating_add(1),
                    RuntimePhase::Access,
                )?;
                if original != current {
                    self.control = Some(Control::Return(
                        super::source_owner_phases::prepare_conversion_refusal_cells(
                            &mut self.heap,
                            invocation.hidden_error_constructor(),
                            invocation.conversion_failed_constructor(),
                            &mut self.instantiation_work,
                        )?,
                    ));
                    return Ok(());
                }
            }
            Some(*key)
        } else {
            None
        };
        let mut operands = Vec::new();
        super::charge_effect_work(
            &mut self.instantiation_work,
            symbol.symbol().operands().len(),
            RuntimePhase::Access,
        )?;
        operands
            .try_reserve_exact(symbol.symbol().operands().len())
            .map_err(|_| RuntimeFailure::ResourceCapacity)?;
        for (position, operand) in symbol.symbol().operands().iter().enumerate() {
            let native = match operand.source() {
                PreparedOperandSource::Current(path) if position == *current_operand => {
                    if super::source_owner_phases::current_key(
                        &self.heap,
                        &value,
                        path,
                        &mut self.instantiation_work,
                    )? != owner_key
                    {
                        return Err(RuntimeFailure::ForeignBinding);
                    }
                    let mut guard = None;
                    for frame in self.frames.iter().rev() {
                        super::charge_effect_work(
                            &mut self.instantiation_work,
                            1,
                            RuntimePhase::Access,
                        )?;
                        let Frame::SourceResourceBoundary(owner) = frame else {
                            continue;
                        };
                        if owner.key != owner_key {
                            continue;
                        }
                        if guard.is_some() || owner.consumed || owner.blocked {
                            return Err(RuntimeFailure::ForeignBinding);
                        }
                        let actual = owner.owner.as_ref().ok_or(RuntimeFailure::ForeignBinding)?;
                        actual.pay_group_checks(usize::from(source_phase == SourceResourcePhase::Handler) + usize::from(!invocation.uses_checked_leaf()), &mut self.instantiation_work)
                            .map_err(|error| crate::foreign::source_bindings::owner_admission_failure(error, &self.instantiation_work))?;
                        if !Arc::ptr_eq(
                            actual.owner(),
                            symbol.owner().ok_or(RuntimeFailure::ForeignBinding)?,
                        ) || source_phase == SourceResourcePhase::Handler
                            && !actual.ordinary_live()
                        {
                            return Err(RuntimeFailure::ForeignBinding);
                        }
                        if invocation.uses_checked_leaf() {
                            if !actual.physically_live() { return Err(RuntimeFailure::ForeignBinding); }
                            // Presence only; no physical address is projected.
                            guard = Some(None);
                            continue;
                        }
                        guard = Some(Some(
                            actual
                                .completion_address()
                                .ok_or(RuntimeFailure::ForeignBinding)?,
                        ));
                    }
                    let address = guard.ok_or(RuntimeFailure::ForeignBinding)?;
                    if invocation.uses_checked_leaf() { continue; }
                    NativeOwnerOperand::Address(address.ok_or(RuntimeFailure::ForeignBinding)?)
                }
                PreparedOperandSource::Enclosing(path) => {
                    self.window_enclosing_operand(provider, selected, request, &value, path)?
                }
                PreparedOperandSource::Constant(index) => {
                    NativeOwnerOperand::Scalar(super::source_owner_phases::admit_constant_operand(
                        symbol,
                        *index,
                        operand.representation(),
                        &mut self.instantiation_work,
                        RuntimePhase::Access,
                    )?)
                }
                PreparedOperandSource::Source(path) => {
                    let integer = super::source_scalar_phases::source_integer_leaf(
                        &self.heap,
                        &value,
                        path,
                        &mut self.instantiation_work,
                    )?;
                    let PreparedRepresentation::Scalar(representation) = operand.representation()
                    else {
                        return Err(RuntimeFailure::ForeignBinding);
                    };
                    match narrow_gnu_scalar(integer, representation, &mut self.instantiation_work) {
                        Ok(value) => NativeOwnerOperand::Scalar(value),
                        Err(NativeScalarConversionError::OutOfRange) => {
                            self.control = Some(Control::Return(
                                super::source_owner_phases::prepare_conversion_refusal_cells(
                                    &mut self.heap,
                                    invocation.hidden_error_constructor(),
                                    invocation.conversion_failed_constructor(),
                                    &mut self.instantiation_work,
                                )?,
                            ));
                            return Ok(());
                        }
                        Err(NativeScalarConversionError::WorkExhausted) => {
                            return Err(super::effect_work_failure(
                                &self.instantiation_work,
                                None,
                                RuntimePhase::Access,
                            ));
                        }
                        Err(_) => return Err(RuntimeFailure::ForeignBinding),
                    }
                }
                _ => return Err(RuntimeFailure::ForeignBinding),
            };
            operands.push(native);
        }
        let is_view = matches!(
            symbol.symbol().access_result(),
            Some(PreparedAccessResult::View { .. })
        );
        let report = if is_view {
            None
        } else {
            Some(
                PrepaidScalarReport::admit(symbol.symbol().result(), &mut self.instantiation_work)
                    .map_err(|error| match error {
                        NativeScalarConversionError::WorkExhausted => super::effect_work_failure(
                            &self.instantiation_work,
                            None,
                            RuntimePhase::Access,
                        ),
                        _ => RuntimeFailure::ForeignBinding,
                    })?,
            )
        };
        // All source projection, mathematical narrowing, result cells and view
        // slots are reserved before C. Reporting below neither charges the
        // shared ledger nor allocates or retries a native operation.
        let cells = if is_view { 3 } else { 1 };
        super::charge_effect_work(
            &mut self.instantiation_work,
            cells + 2 + usize::from(extent_view.is_some()) * 9,
            RuntimePhase::Access,
        )?;
        self.heap
            .try_reserve(cells)
            .map_err(|_| RuntimeFailure::ResourceCapacity)?;
        let start = self.heap.len();
        for _ in 0..cells {
            self.heap.push(super::HeapCell::Uninitialized);
        }
        let returned = invocation.returned_constructor();
        let prepared_view = if is_view {
            let Frame::SourceWindowBoundary(window) = &mut self.frames[selected] else {
                return Err(RuntimeFailure::ForeignBinding);
            };
            window
                .views
                .try_reserve(1)
                .map_err(|_| RuntimeFailure::ResourceCapacity)?;
            Some((Arc::clone(symbol), value.clone()))
        } else {
            None
        };
        let codec = symbol.owner_codec().ok_or(RuntimeFailure::ForeignBinding)?;
        let nullable = *codec.nullable_constructors();
        let readable = codec.output_constructors()[1];
        let Frame::SourceResourceBoundary(boundary) = &self.frames[provider] else {
            return Err(RuntimeFailure::ForeignBinding);
        };
        let invocation = invocation.prepare_checked_boundary(
            boundary
                .owner
                .as_ref()
                .ok_or(RuntimeFailure::ForeignBinding)?,
            owner_key.0 as usize,
            &mut self.instantiation_work,
        )?;
        super::disposal::check()?;
        let (authority, raw) = invocation
            .invoke(&operands)
            .map_err(|_| RuntimeFailure::ForeignBinding)?;
        let reported = (|| {
            let result = match raw {
                SourceWindowRaw::View(raw) if is_view => {
                    let payload = if raw.is_null() {
                        super::HeapCell::Constructor(nullable[0], None)
                    } else {
                        let Frame::SourceWindowBoundary(window) = &mut self.frames[selected] else {
                            unreachable!("window cannot move during synchronous callback")
                        };
                        let key = WindowViewKey {
                            window: window_key,
                            slot: window.views.len(),
                        };
                        let (symbol, operands) =
                            prepared_view.expect("view readiness owns passive record");
                        window.views.push(WindowView {
                            raw,
                            symbol,
                            operands,
                        });
                        super::HeapCell::Constructor(
                            nullable[1],
                            Some(Value::NativeWindowView(key)),
                        )
                    };
                    self.heap[start] = payload;
                    self.heap[start + 1] =
                        super::HeapCell::Constructor(readable, Some(Value::Location(start)));
                    self.heap[start + 2] =
                        super::HeapCell::Constructor(returned, Some(Value::Location(start + 1)));
                    Value::Location(start + 2)
                }
                SourceWindowRaw::Scalar(raw) if !is_view => {
                    let integer = widen_gnu_reply(
                        raw,
                        report.expect("scalar readiness owns report allowance"),
                    )
                    .map_err(|_| RuntimeFailure::ForeignBinding)?
                    .ok_or(RuntimeFailure::ForeignBinding)?;
                    let payload = if let Some(view) = extent_view {
                        let length = integer.to_usize().ok_or(RuntimeFailure::ForeignBinding)?;
                        Value::NativeWindowExtent(WindowExtentKey { view, length })
                    } else {
                        Value::Integer(integer)
                    };
                    self.heap[start] = super::HeapCell::Constructor(returned, Some(payload));
                    Value::Location(start)
                }
                _ => return Err(RuntimeFailure::ForeignBinding),
            };
            self.control = Some(Control::Return(result));
            Ok(())
        })();
        if reported.is_err() {
            authority.output_failed();
        }
        reported
    }

    fn window_enclosing_operand(
        &mut self,
        provider: usize,
        selected: usize,
        request: NodeId,
        value: &Value,
        path: &[usize],
    ) -> Result<crate::foreign::source_runtime::NativeOwnerOperand, RuntimeFailure> {
        let key = super::source_owner_phases::current_key(
            &self.heap,
            value,
            path,
            &mut self.instantiation_work,
        )?;
        let program = self.program.clone();
        let Some(ExecutableNode::Effect(expression)) = program.node(request) else {
            return Err(RuntimeFailure::ForeignBinding);
        };
        let EffectExprKind::Operation(EffectOperation::Request(call)) = &expression.kind else {
            return Err(RuntimeFailure::ForeignBinding);
        };
        let ty = match program
            .node(call.operand())
            .ok_or(RuntimeFailure::ForeignBinding)?
        {
            ExecutableNode::Pure(node) => &node.ty,
            ExecutableNode::Effect(node) => &node.ty,
        };
        let leaf =
            super::source_owner_phases::source_type_leaf(ty, path, &mut self.instantiation_work)?;
        let Frame::SourceWindowBoundary(window) = &self.frames[selected] else {
            return Err(RuntimeFailure::ForeignBinding);
        };
        let ty = IterativeTypeOwner::new(
            window
                .environment
                .instantiation
                .ty(leaf, &mut self.instantiation_work)?,
        );
        let Frame::SourceResourceBoundary(boundary) = &self.frames[provider] else {
            return Err(RuntimeFailure::ForeignBinding);
        };
        let completion = if boundary.phase == ProviderPhase::Finish {
            boundary.owner.as_ref()
        } else {
            None
        };
        let dependency = self
            .source_bindings
            .ok_or(RuntimeFailure::ForeignBinding)?
            .borrowed_owner(
                key.0 as usize,
                &ty,
                NativeOwnerViewKind::State,
                completion,
                &mut self.instantiation_work,
            )?;
        super::charge_effect_work(
            &mut self.instantiation_work,
            boundary.dependencies.len(),
            RuntimePhase::Access,
        )?;
        if !boundary
            .dependencies
            .iter()
            .any(|known| known.same_slot(&dependency))
            || completion.is_some_and(|owner| !owner.retains(&dependency))
        {
            return Err(RuntimeFailure::ForeignBinding);
        }
        for frame in &self.frames {
            super::charge_effect_work(&mut self.instantiation_work, 1, RuntimePhase::Access)?;
            if matches!(frame, Frame::SourceResourceBoundary(owner) if owner.key == key && (owner.blocked || owner.consumed))
            {
                return Err(RuntimeFailure::ForeignBinding);
            }
        }
        dependency.pay_group_checks(1, &mut self.instantiation_work)
            .map_err(|error| crate::foreign::source_bindings::owner_admission_failure(error, &self.instantiation_work))?;
        Ok(crate::foreign::source_runtime::NativeOwnerOperand::Address(
            dependency.address().ok_or(RuntimeFailure::ForeignBinding)?,
        ))
    }
}

fn value_leaf<'a>(
    heap: &'a [super::HeapCell],
    mut value: &'a Value,
    path: &[usize],
    work: &mut TypeWorkBudget,
) -> Result<&'a Value, RuntimeFailure> {
    let Some((first, rest)) = path.split_first() else {
        return Err(RuntimeFailure::ForeignBinding);
    };
    super::charge_effect_work(work, 1, RuntimePhase::Access)?;
    if let Value::Location(location) = value {
        let location = super::resolve_location_with_work(heap, *location, work)?;
        let Some(super::HeapCell::Tuple(fields)) = heap.get(location) else {
            return Err(RuntimeFailure::ForeignBinding);
        };
        value = fields.get(*first).ok_or(RuntimeFailure::ForeignBinding)?;
    } else if *first != 0 {
        return Err(RuntimeFailure::ForeignBinding);
    }
    for position in rest {
        super::charge_effect_work(work, 1, RuntimePhase::Access)?;
        let Value::Location(location) = value else {
            return Err(RuntimeFailure::ForeignBinding);
        };
        let location = super::resolve_location_with_work(heap, *location, work)?;
        let Some(super::HeapCell::Tuple(fields)) = heap.get(location) else {
            return Err(RuntimeFailure::ForeignBinding);
        };
        value = fields
            .get(*position)
            .ok_or(RuntimeFailure::ForeignBinding)?;
    }
    Ok(value)
}

/// Physical barrier shared by cached extent and copy access. Source
/// occurrence/type admission remains in the caller; this grants none.
fn require_cached_window_owner(
    frames: &[Frame],
    owner_key: ActivationKey,
    provider_phase: ProviderPhase,
    work: &mut TypeWorkBudget,
) -> Result<(), RuntimeFailure> {
    // The same original physical guard must still exist. View and extent
    // tokens cannot substitute a same-typed activation or revive consumed,
    // blocked or ordinarily revoked access.
    let mut live = false;
    for frame in frames.iter().rev() {
        super::charge_effect_work(work, 1, RuntimePhase::Access)?;
        let Frame::SourceResourceBoundary(owner) = frame else {
            continue;
        };
        if owner.key != owner_key {
            continue;
        }
        let guard = owner.owner.as_ref().ok_or(RuntimeFailure::ForeignBinding)?;
        // A related owner can deny this group without changing this frame's
        // local blocked flag, including while Finish uses cached windows.
        if guard.shared_group_denied(work)
            .map_err(|error| crate::foreign::source_bindings::owner_admission_failure(error, work))?
        {
            return Err(RuntimeFailure::ForeignBinding);
        }
        if provider_phase == ProviderPhase::Body {
            guard.pay_group_checks(1, work)
                .map_err(|error| crate::foreign::source_bindings::owner_admission_failure(error, work))?;
        }
        if live
            || owner.consumed
            || owner.blocked
            || !guard.physically_live()
            || provider_phase == ProviderPhase::Body && !guard.ordinary_live()
        {
            return Err(RuntimeFailure::ForeignBinding);
        }
        live = true;
    }
    if !live {
        return Err(RuntimeFailure::ForeignBinding);
    }
    Ok(())
}


impl Machine<'_> {
    #[inline(never)]
    pub(super) fn return_source_view_call(
        &mut self,
        apply: NodeId,
        callable: super::SourceByteCallable,
        caller: super::Instantiation,
        value: Value,
    ) -> Result<(), RuntimeFailure> {
        use crate::{
            core::{PureComputation, PureExprKind, packed::Intrinsic},
            foreign::{
                scalar_preflight::ForeignScalarPreflightRole as Role,
                source_contract::PreparedForeignExtent,
            },
            types::Type,
        };
        let (function, role) = match callable.intrinsic.operation() {
            Intrinsic::ForeignCopyBytes { function } => (function, Role::CopyBytes),
            Intrinsic::ForeignCopyNul { function } => (function, Role::CopyNul),
            Intrinsic::ForeignExtentValue { function } => (function, Role::ExtentValue),
            _ => return Err(RuntimeFailure::ForeignBinding),
        };
        let program = self.program.clone();
        let fact = program
            .registry()
            .scalar_preflight(function)
            .ok_or(RuntimeFailure::ForeignBinding)?;
        let checked_copy = fact.role() == Role::CheckedCopyBytes && role == Role::CopyBytes;
        if fact.function() != function
            || (fact.role() != role && !checked_copy)
            || fact.module() != callable.intrinsic.module()
        {
            return Err(RuntimeFailure::ForeignBinding);
        }
        let (view_key, extent) = if role == Role::ExtentValue {
            let Value::NativeWindowExtent(extent) = &value else {
                return Err(RuntimeFailure::ForeignBinding);
            };
            (extent.view, Some(*extent))
        } else {
            let Value::NativeWindowView(view) =
                value_leaf(&self.heap, &value, &[0], &mut self.instantiation_work)?
            else {
                return Err(RuntimeFailure::ForeignBinding);
            };
            let extent = if role == Role::CopyBytes {
                let Value::NativeWindowExtent(extent) =
                    value_leaf(&self.heap, &value, &[1], &mut self.instantiation_work)?
                else {
                    return Err(RuntimeFailure::ForeignBinding);
                };
                Some(*extent)
            } else {
                None
            };
            (*view, extent)
        };
        let mut selected = None;
        for (index, frame) in self.frames.iter().enumerate().rev() {
            super::charge_effect_work(&mut self.instantiation_work, 1, RuntimePhase::Access)?;
            let Frame::SourceWindowBoundary(window) = frame else {
                continue;
            };
            if window.key != view_key.window {
                continue;
            }
            if selected.is_some() || window.views.get(view_key.slot).is_none() {
                return Err(RuntimeFailure::ForeignBinding);
            }
            selected = Some(index);
        }
        let selected = selected.ok_or(RuntimeFailure::ForeignBinding)?;
        let Frame::SourceWindowBoundary(window) = &self.frames[selected] else {
            return Err(RuntimeFailure::ForeignBinding);
        };
        super::charge_effect_work(
            &mut self.instantiation_work,
            self.frames.len(),
            RuntimePhase::Access,
        )?;
        let provider = self.frames.iter().rposition(|frame| matches!(frame, Frame::SourceResourceBoundary(boundary) if boundary.key == window.provider)).ok_or(RuntimeFailure::ForeignBinding)?;
        let Frame::SourceResourceBoundary(boundary) = &self.frames[provider] else {
            return Err(RuntimeFailure::ForeignBinding);
        };
        let Some(ExecutableNode::Effect(expression)) = program.node(boundary.node) else {
            return Err(RuntimeFailure::ForeignBinding);
        };
        let EffectExprKind::Operation(EffectOperation::SourceResourceScope(scope)) =
            &expression.kind
        else {
            return Err(RuntimeFailure::ForeignBinding);
        };
        if !scope
            .contains_byte_call(
                phase(boundary.phase),
                apply,
                callable.application,
                function,
                &mut self.instantiation_work,
            )
            .map_err(|error| validation_failure(error, &self.instantiation_work))?
        {
            return Err(RuntimeFailure::ForeignBinding);
        }
        for argument in scope.arguments() {
            let original = boundary
                .environment
                .instantiation
                .argument(argument, &mut self.instantiation_work)?;
            for context in [&callable.caller, &caller] {
                let actual = context.argument(argument, &mut self.instantiation_work)?;
                if !crate::types::same_kinded_argument_with_budget(
                    &original,
                    &actual,
                    &mut self.instantiation_work,
                )
                .map_err(|()| {
                    super::effect_work_failure(&self.instantiation_work, None, RuntimePhase::Access)
                })? {
                    return Err(RuntimeFailure::ForeignBinding);
                }
            }
        }
        let PureExprKind::Computation(PureComputation::TypeApplication(application)) =
            super::pure_expression(&program, callable.application)?
        else {
            return Err(RuntimeFailure::ForeignBinding);
        };
        let offset = usize::from(checked_copy);
        if application.arguments().len() != 1 + offset || !application.row_arguments().is_empty() {
            return Err(RuntimeFailure::ForeignBinding);
        }
        if checked_copy {
            let selector = scope
                .header()
                .original
                .host
                .ok_or(RuntimeFailure::ForeignBinding)?;
            let selected = scope
                .arguments()
                .get(selector.position)
                .ok_or(RuntimeFailure::ForeignBinding)?;
            let expected = boundary
                .environment
                .instantiation
                .argument(selected, &mut self.instantiation_work)?;
            let crate::types::KindedArgument::TypeArg(expected) = &*expected else {
                return Err(RuntimeFailure::ForeignBinding);
            };
            let applied = IterativeTypeOwner::new(
                callable
                    .caller
                    .ty(&application.arguments()[0], &mut self.instantiation_work)?,
            );
            let formal = fact
                .role()
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
        }
        let PureExprKind::Computation(PureComputation::Apply(call)) =
            super::pure_expression(&program, apply)?
        else {
            return Err(RuntimeFailure::ForeignBinding);
        };
        let operand = match program
            .node(call.argument())
            .ok_or(RuntimeFailure::ForeignBinding)?
        {
            ExecutableNode::Pure(node) => &node.ty,
            ExecutableNode::Effect(node) => &node.ty,
        };
        let operand_view = if role == Role::ExtentValue {
            let Type::Application(head, view) = operand else {
                return Err(RuntimeFailure::ForeignBinding);
            };
            let nominal = crate::foreign::source_access::extent_nominal(
                fact.call_codec(),
                program.registry(),
                &mut self.instantiation_work,
            )
            .map_err(|error| foreign_failure(error, &self.instantiation_work))?;
            if **head != Type::Nominal(nominal) {
                return Err(RuntimeFailure::ForeignBinding);
            }
            view.as_ref()
        } else {
            let Type::Tuple(fields) = operand else {
                return Err(RuntimeFailure::ForeignBinding);
            };
            if fields.len() != 2 {
                return Err(RuntimeFailure::ForeignBinding);
            }
            &fields[0]
        };
        let operand_view =
            IterativeTypeOwner::new(caller.ty(operand_view, &mut self.instantiation_work)?);
        let applied_view = IterativeTypeOwner::new(callable.caller.ty(
            &application.arguments()[offset],
            &mut self.instantiation_work,
        )?);
        let formal = fact
            .role()
            .view_parameter(fact.module())
            .ok_or(RuntimeFailure::ForeignBinding)?;
        let defining_view = IterativeTypeOwner::new(
            callable
                .defining
                .ty(&Type::Variable(formal), &mut self.instantiation_work)?,
        );
        for actual in [&applied_view, &defining_view] {
            if !crate::types::same_type_with_budget(
                &operand_view,
                actual,
                &mut self.instantiation_work,
            )
            .map_err(|()| {
                super::effect_work_failure(&self.instantiation_work, None, RuntimePhase::Access)
            })? {
                return Err(RuntimeFailure::ForeignBinding);
            }
        }
        let Some(ExecutableNode::Effect(expression)) = program.node(window.node) else {
            return Err(RuntimeFailure::ForeignBinding);
        };
        let EffectExprKind::Operation(EffectOperation::SourceCopyWindow(descriptor)) =
            &expression.kind
        else {
            return Err(RuntimeFailure::ForeignBinding);
        };
        if !crate::core::source_window::matches_view_type(
            descriptor.family(),
            &window.arguments.0,
            &operand_view,
            &mut self.instantiation_work,
        )
        .map_err(|()| {
            super::effect_work_failure(&self.instantiation_work, None, RuntimePhase::Access)
        })? || role == Role::CopyBytes
            && descriptor.family().declaration().extent() != PreparedForeignExtent::Bytes
            || role == Role::CopyNul
                && descriptor.family().declaration().extent() != PreparedForeignExtent::Nul
        {
            return Err(RuntimeFailure::ForeignBinding);
        }
        require_cached_window_owner(&self.frames, window.owner, boundary.phase, &mut self.instantiation_work)?;
        if extent.is_some_and(|extent| extent.view != view_key) {
            if checked_copy {
                return Err(RuntimeFailure::ForeignBinding);
            }
            let error = fact
                .conversion_error_constructor()
                .ok_or(RuntimeFailure::ForeignBinding)?;
            self.control = Some(Control::Return(
                super::source_owner_phases::prepare_conversion_refusal_cells(
                    &mut self.heap,
                    error,
                    fact.call_codec().ids().conversion_failed,
                    &mut self.instantiation_work,
                )?,
            ));
            return Ok(());
        }
        if role == Role::ExtentValue {
            let length = extent.ok_or(RuntimeFailure::ForeignBinding)?.length;
            super::charge_effect_work(
                &mut self.instantiation_work,
                std::mem::size_of::<usize>() + 1,
                RuntimePhase::Access,
            )?;
            drop(callable);
            drop(caller);
            self.control = Some(Control::Return(Value::Integer(
                crate::integer::Integer::from_usize(length),
            )));
            return Ok(());
        }
        let mut copy_record: Option<crate::foreign::source_runtime::NativeOwnerCopyRecord> =
            if checked_copy {
                // The supported independent owner must be this window's physical
                // provider. Dependency-owner windows remain explicitly unsupported.
                if boundary.key != window.owner {
                    return Err(RuntimeFailure::ForeignBinding);
                }
                let receipt = crate::foreign::source_bindings::SourceOwnerCopyRequest::admit(
                    &program,
                    boundary.node,
                    window.node,
                    apply,
                    callable.application,
                    function,
                    phase(boundary.phase),
                    &mut self.instantiation_work,
                )?;
                Some(
                    boundary
                        .owner
                        .as_ref()
                        .ok_or(RuntimeFailure::ForeignBinding)?
                        .prepare_checked_copy(
                            &receipt,
                            usize::try_from(boundary.key.0)
                                .map_err(|_| RuntimeFailure::ForeignBinding)?,
                            &mut self.instantiation_work,
                        )
                        .map_err(|error| {
                            crate::foreign::source_bindings::owner_admission_failure(
                                error,
                                &self.instantiation_work,
                            )
                        })?,
                )
            } else {
                None
            };
        let returned = fact.call_codec().ids().returned;
        let ready = if role == Role::CopyBytes {
            CopyReplyReady::admit(
                CopyMode::Bytes(extent.ok_or(RuntimeFailure::ForeignBinding)?.length),
                returned,
                None,
                &mut self.heap,
                &mut self.instantiation_work,
            )?
        } else {
            let integer = super::source_scalar_phases::source_integer_leaf(
                &self.heap,
                &value,
                &[1],
                &mut self.instantiation_work,
            )?;
            let bound = match crate::foreign::source_runtime::narrow_gnu_scalar(
                integer,
                crate::foreign::source_contract::PreparedScalarRepresentation::SizeT,
                &mut self.instantiation_work,
            ) {
                Ok(crate::foreign::source_runtime::NativeScalarValue::USize(bound)) => bound,
                Err(crate::foreign::source_runtime::NativeScalarConversionError::OutOfRange) => {
                    self.control = Some(Control::Return(
                        super::source_owner_phases::prepare_conversion_refusal_cells(
                            &mut self.heap,
                            fact.conversion_error_constructor()
                                .ok_or(RuntimeFailure::ForeignBinding)?,
                            fact.call_codec().ids().conversion_failed,
                            &mut self.instantiation_work,
                        )?,
                    ));
                    return Ok(());
                }
                Err(crate::foreign::source_runtime::NativeScalarConversionError::WorkExhausted) => {
                    return Err(super::effect_work_failure(
                        &self.instantiation_work,
                        None,
                        RuntimePhase::Access,
                    ));
                }
                _ => return Err(RuntimeFailure::ForeignBinding),
            };
            CopyReplyReady::admit(
                CopyMode::Nul(bound),
                returned,
                Some((
                    fact.call_codec().ids().conversion_failed,
                    fact.conversion_error_constructor()
                        .ok_or(RuntimeFailure::ForeignBinding)?,
                )),
                &mut self.heap,
                &mut self.instantiation_work,
            )?
        };
        drop(callable);
        drop(caller);
        super::disposal::check()?;
        let Frame::SourceWindowBoundary(window) = &self.frames[selected] else {
            unreachable!("prepaid window remains selected")
        };
        let view = &window.views[view_key.slot];
        #[cfg(any(test, ash_checked_owner_root = "v1"))]
        if view.raw.is_checked_leaf() {
            let value = ready.copy_checked_leaf(&view.raw, copy_record.take().ok_or(RuntimeFailure::ForeignBinding)?, &mut self.heap, &self.instantiation_work)?;
            self.control = Some(Control::Return(value));
            return Ok(());
        }
        if let Some(record) = &mut copy_record {
            record.begin().map_err(|error| {
                crate::foreign::source_bindings::owner_admission_failure(
                    error,
                    &self.instantiation_work,
                )
            })?;
        }
        let copied = ready.copy(
            AdmittedWindowRead { raw: &view.raw },
            &mut self.heap,
            &mut self.instantiation_work,
        );
        let copied = match copied {
            Ok(value) => {
                if let Some(record) = copy_record {
                    let _observed = record.returned();
                }
                value
            }
            Err(error) => {
                if let Some(record) = copy_record {
                    record.output_failed();
                }
                return Err(error);
            }
        };
        self.control = Some(Control::Return(copied));
        Ok(())
    }
}

#[derive(Clone, Copy, Debug)]
enum CopyMode {
    Bytes(usize),
    Nul(usize),
}

/// This module creates a read loan only after the complete original-call,
/// current-window and physical-guard admission above. It owns no pointer.
struct AdmittedWindowRead<'view> {
    raw: &'view NativeViewReturned,
}

struct CopyReplyReady {
    bytes: Option<Arc<[u8]>>,
    mode: CopyMode,
    report: super::Location,
    returned: crate::types::ConstructorId,
    failure: Option<(crate::types::ConstructorId, super::Location)>,
}
impl CopyReplyReady {
    #[cfg(any(test, ash_checked_owner_root = "v1"))]
    fn copy_checked_leaf(mut self, view: &NativeViewReturned, record: crate::foreign::source_runtime::NativeOwnerCopyRecord, heap: &mut [super::HeapCell], work: &TypeWorkBudget) -> Result<Value, RuntimeFailure> {
        if !matches!(self.mode, CopyMode::Bytes(_)) { return Err(RuntimeFailure::ForeignBinding); }
        let bytes = Arc::get_mut(self.bytes.as_mut().ok_or(RuntimeFailure::ForeignBinding)?).ok_or(RuntimeFailure::ForeignBinding)?;
        record.copy_checked_leaf(view, bytes).map_err(|error| crate::foreign::source_bindings::owner_admission_failure(error, work))?;
        heap[self.report] = super::HeapCell::Constructor(self.returned, Some(Value::Bytes(self.bytes.take().expect("prepaid checked bytes"))));
        Ok(Value::Location(self.report))
    }

    fn admit(
        mode: CopyMode,
        returned: crate::types::ConstructorId,
        failure: Option<(crate::types::ConstructorId, crate::types::ConstructorId)>,
        heap: &mut Vec<super::HeapCell>,
        work: &mut TypeWorkBudget,
    ) -> Result<Self, RuntimeFailure> {
        let (length, units, cells) = match mode {
            CopyMode::Bytes(length) if failure.is_none() => {
                (Some(length), length.checked_add(2), 1usize)
            }
            CopyMode::Nul(bound) if failure.is_some() => {
                // The caller's bound limits observations, not an allocation.
                // Preserve the checked bound and reserve both reports now.
                bound
                    .checked_add(1)
                    .ok_or_else(|| super::effect_work_failure(work, None, RuntimePhase::Access))?;
                (None, Some(3), 2)
            }
            _ => return Err(RuntimeFailure::ForeignBinding),
        };
        let units =
            units.ok_or_else(|| super::effect_work_failure(work, None, RuntimePhase::Access))?;
        super::charge_effect_work(work, units, RuntimePhase::Access)?;
        let bytes = if let Some(length) = length {
            let mut bytes = Vec::new();
            bytes
                .try_reserve_exact(length)
                .map_err(|_| RuntimeFailure::ResourceCapacity)?;
            bytes.resize(length, 0);
            Some(Arc::from(bytes))
        } else {
            None
        };
        #[cfg(test)]
        if copy_reservation_fault::REJECT.replace(false) {
            return Err(RuntimeFailure::ResourceCapacity);
        }
        heap.try_reserve(cells)
            .map_err(|_| RuntimeFailure::ResourceCapacity)?;
        let failure = failure.map(|(failed, error)| {
            let location = heap.len();
            heap.push(super::HeapCell::Constructor(error, None));
            (failed, location)
        });
        let report = heap.len();
        heap.push(super::HeapCell::Uninitialized);
        Ok(Self {
            bytes,
            mode,
            report,
            returned,
            failure,
        })
    }

    /// Exact byte copies own their complete work/storage before reading. NUL
    /// scans pay before each bounded observation, then reserve the observed
    /// prefix's exact independent storage and copying work. No native call or
    /// invalidating operation interleaves, and no partial reply is published.
    fn copy(
        mut self,
        view: AdmittedWindowRead<'_>,
        heap: &mut [super::HeapCell],
        work: &mut TypeWorkBudget,
    ) -> Result<Value, RuntimeFailure> {
        let length = match self.mode {
            CopyMode::Bytes(length) => Some(length),
            CopyMode::Nul(bound) => {
                let mut found = None;
                for index in 0..=bound {
                    super::charge_effect_work(work, 1, RuntimePhase::Access)?;
                    if view.raw.read(index) == 0 {
                        found = Some(index);
                        break;
                    }
                }
                found
            }
        };
        let cell = if let Some(length) = length {
            if self.bytes.is_none() {
                let units = length
                    .checked_mul(2)
                    .and_then(|units| units.checked_add(1))
                    .ok_or_else(|| super::effect_work_failure(work, None, RuntimePhase::Access))?;
                super::charge_effect_work(work, units, RuntimePhase::Access)?;
                #[cfg(test)]
                if copy_reservation_fault::REJECT_NUL_PAYLOAD.replace(false) {
                    return Err(RuntimeFailure::ResourceCapacity);
                }
                let mut bytes = Vec::new();
                bytes
                    .try_reserve_exact(length)
                    .map_err(|_| RuntimeFailure::ResourceCapacity)?;
                bytes.resize(length, 0);
                self.bytes = Some(Arc::from(bytes));
            }
            let bytes = Arc::get_mut(self.bytes.as_mut().expect("admitted independent storage"))
                .expect("unpublished independent copy");
            for (index, byte) in bytes.iter_mut().enumerate() {
                *byte = view.raw.read(index);
            }
            let bytes = self.bytes.take().expect("filled independent storage");
            let bytes = match self.mode {
                CopyMode::Bytes(_) => Value::Bytes(bytes),
                CopyMode::Nul(_) => {
                    Value::BytePrefix(super::super::value::BytePrefix::new(bytes, length))
                }
            };
            super::HeapCell::Constructor(self.returned, Some(bytes))
        } else {
            let (failed, error) = self.failure.expect("NUL readiness owns refusal cell");
            super::HeapCell::Constructor(failed, Some(Value::Location(error)))
        };
        heap[self.report] = cell;
        Ok(Value::Location(self.report))
    }
}

#[cfg(test)]
mod copy_reservation_fault {
    use std::cell::Cell;
    thread_local! {
        pub(super) static REJECT: Cell<bool> = const { Cell::new(false) };
        pub(super) static REJECT_NUL_PAYLOAD: Cell<bool> = const { Cell::new(false) };
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::cell::Cell;
    thread_local! {
        static READS: Cell<usize> = const { Cell::new(0) };
        static CONTENT: Cell<u8> = const { Cell::new(0) };
    }
    fn read(address: *mut core::ffi::c_void, index: usize) -> u8 {
        assert_eq!(address, std::ptr::NonNull::<u8>::dangling().as_ptr().cast());
        READS.set(READS.get() + 1);
        match CONTENT.get() {
            0 => [1, 2, 3][index],
            1 => [65, 66, 0, 99][index],
            2 => [0][index],
            3 => [65, 66, 67, 68][index],
            4 => {
                if index == 128 {
                    0
                } else {
                    65
                }
            }
            _ => panic!("unselected read fixture"),
        }
    }
    fn raw() -> NativeViewReturned {
        NativeViewReturned::new(std::ptr::NonNull::<u8>::dangling().as_ptr().cast(), read)
    }
    fn constructors() -> [crate::types::ConstructorId; 3] {
        let nominal = crate::types::NominalTypeId::new(crate::module::ModuleId::new(1), 0);
        [0, 1, 2].map(|tag| crate::types::ConstructorId::new(nominal, tag))
    }
    fn payload<'a>(heap: &'a [super::super::HeapCell], value: &Value) -> &'a Value {
        let Value::Location(location) = value else {
            panic!("expected report");
        };
        let super::super::HeapCell::Constructor(_, Some(value)) = &heap[*location] else {
            panic!("expected payload");
        };
        value
    }

    /// Injected storage/read mechanism only. No C, source authority or live
    /// owner permission is inferred from this passive callback fixture.
    #[test]
    fn independent_byte_copy_reserves_exact_prefix_budget_and_storage_before_reads() {
        let [returned, _, _] = constructors();
        let mut work = TypeWorkBudget::with_limit(64);
        let mut heap = Vec::new();
        READS.set(0);
        CONTENT.set(0);
        let ready = CopyReplyReady::admit(CopyMode::Bytes(3), returned, None, &mut heap, &mut work)
            .unwrap();
        let required = work.used();
        assert_eq!(READS.get(), 0);
        let value = ready
            .copy(AdmittedWindowRead { raw: &raw() }, &mut heap, &mut work)
            .unwrap();
        assert_eq!(payload(&heap, &value).bytes(), Some([1, 2, 3].as_slice()));
        assert_eq!(READS.get(), 3);
        for prefix in [0, 7] {
            for available in 0..=required {
                let mut work = TypeWorkBudget::with_limit(prefix + available);
                work.charge(prefix).unwrap();
                let mut heap = Vec::new();
                READS.set(0);
                let result =
                    CopyReplyReady::admit(CopyMode::Bytes(3), returned, None, &mut heap, &mut work);
                if available < required {
                    assert!(result.is_err());
                    assert_eq!(READS.get(), 0);
                    assert!(heap.is_empty());
                } else {
                    let ready = result.unwrap();
                    assert_eq!(READS.get(), 0);
                    let value = ready
                        .copy(AdmittedWindowRead { raw: &raw() }, &mut heap, &mut work)
                        .unwrap();
                    assert_eq!(payload(&heap, &value).bytes(), Some([1, 2, 3].as_slice()));
                    assert_eq!(work.used(), prefix + required);
                    assert_eq!(READS.get(), 3);
                }
            }
        }
        copy_reservation_fault::REJECT.set(true);
        READS.set(0);
        let mut heap = Vec::new();
        assert!(
            CopyReplyReady::admit(
                CopyMode::Bytes(3),
                returned,
                None,
                &mut heap,
                &mut TypeWorkBudget::with_limit(required)
            )
            .is_err()
        );
        assert!(heap.is_empty());
        assert_eq!(READS.get(), 0);
        // Fresh exact retry gets no credit or storage from the failed attempt.
        let mut work = TypeWorkBudget::with_limit(required);
        let ready = CopyReplyReady::admit(CopyMode::Bytes(3), returned, None, &mut heap, &mut work)
            .unwrap();
        ready
            .copy(AdmittedWindowRead { raw: &raw() }, &mut heap, &mut work)
            .unwrap();
        assert_eq!(READS.get(), 3);
    }

    #[test]
    fn nul_copy_observes_only_the_prefix_under_the_existing_diagnostic_bound() {
        let [returned, failed, error] = constructors();
        READS.set(0);
        CONTENT.set(1);
        let mut heap = Vec::new();
        let mut work = TypeWorkBudget::with_limit(64);
        let ready = CopyReplyReady::admit(
            CopyMode::Nul(crate::types::TYPE_WORK_LIMIT),
            returned,
            Some((failed, error)),
            &mut heap,
            &mut work,
        )
        .unwrap();
        let value = ready
            .copy(AdmittedWindowRead { raw: &raw() }, &mut heap, &mut work)
            .unwrap();
        assert_eq!(payload(&heap, &value).bytes(), Some(b"AB".as_slice()));
        assert!(work.used() < 64);
    }

    #[test]
    fn bounded_nul_copy_reserves_reports_then_pays_the_observed_prefix() {
        let [returned, failed, error] = constructors();
        for (content, bound, expected, reads) in [
            (1, 3, Some(b"AB".as_slice()), 5),
            (1, 2, Some(b"AB".as_slice()), 5),
            (2, 0, Some(b"".as_slice()), 1),
            (3, 2, None, 3),
            (3, 0, None, 1),
        ] {
            READS.set(0);
            CONTENT.set(content);
            let mut heap = Vec::new();
            let mut work = TypeWorkBudget::with_limit(64);
            let ready = CopyReplyReady::admit(
                CopyMode::Nul(bound),
                returned,
                Some((failed, error)),
                &mut heap,
                &mut work,
            )
            .unwrap();
            assert_eq!(READS.get(), 0);
            let value = ready
                .copy(AdmittedWindowRead { raw: &raw() }, &mut heap, &mut work)
                .unwrap();
            let required = work.used();
            assert_eq!(READS.get(), reads);
            let Value::Location(location) = value else {
                panic!("report");
            };
            let super::super::HeapCell::Constructor(tag, Some(payload)) = &heap[location] else {
                panic!("report");
            };
            if let Some(expected) = expected {
                assert_eq!(*tag, returned);
                CONTENT.set(3);
                assert_eq!(payload.bytes(), Some(expected));
            } else {
                assert_eq!(*tag, failed);
            }
            for prefix in [0, 7] {
                for available in 0..=required {
                    CONTENT.set(content);
                    READS.set(0);
                    let mut work = TypeWorkBudget::with_limit(prefix + available);
                    work.charge(prefix).unwrap();
                    let mut heap = Vec::new();
                    let result = CopyReplyReady::admit(
                        CopyMode::Nul(bound),
                        returned,
                        Some((failed, error)),
                        &mut heap,
                        &mut work,
                    )
                    .and_then(|ready| {
                        ready.copy(AdmittedWindowRead { raw: &raw() }, &mut heap, &mut work)
                    });
                    if available < required {
                        assert!(result.is_err());
                        assert!(heap.last().is_none_or(|cell| matches!(
                            cell,
                            super::super::HeapCell::Uninitialized
                        )));
                    } else {
                        assert!(result.is_ok());
                        assert_eq!(work.used(), prefix + required);
                        assert_eq!(READS.get(), reads);
                    }
                    // A fresh retry receives no work or storage from refusal.
                    READS.set(0);
                    let mut fresh = TypeWorkBudget::with_limit(required);
                    let mut heap = Vec::new();
                    let ready = CopyReplyReady::admit(
                        CopyMode::Nul(bound),
                        returned,
                        Some((failed, error)),
                        &mut heap,
                        &mut fresh,
                    )
                    .unwrap();
                    assert!(
                        ready
                            .copy(AdmittedWindowRead { raw: &raw() }, &mut heap, &mut fresh)
                            .is_ok()
                    );
                    assert_eq!(READS.get(), reads);
                    assert_eq!(fresh.used(), required);
                }
            }
        }
        READS.set(0);
        assert!(
            CopyReplyReady::admit(
                CopyMode::Nul(usize::MAX),
                returned,
                Some((failed, error)),
                &mut Vec::new(),
                &mut TypeWorkBudget::with_limit(64)
            )
            .is_err()
        );
        assert_eq!(READS.get(), 0);
    }

    #[test]
    fn nul_prefix_storage_refusal_is_terminal_without_partial_report() {
        let [returned, failed, error] = constructors();
        READS.set(0);
        CONTENT.set(1);
        let mut heap = Vec::new();
        let mut work = TypeWorkBudget::with_limit(64);
        let ready = CopyReplyReady::admit(
            CopyMode::Nul(327_680),
            returned,
            Some((failed, error)),
            &mut heap,
            &mut work,
        )
        .unwrap();
        let report = ready.report;
        copy_reservation_fault::REJECT_NUL_PAYLOAD.set(true);
        assert!(
            ready
                .copy(AdmittedWindowRead { raw: &raw() }, &mut heap, &mut work)
                .is_err()
        );
        assert_eq!(
            READS.get(),
            3,
            "the complete scan precedes exact payload reservation"
        );
        assert!(matches!(
            heap[report],
            super::super::HeapCell::Uninitialized
        ));
        READS.set(0);
        CONTENT.set(4);
        let mut heap = Vec::new();
        let mut work = TypeWorkBudget::with_limit(512);
        let ready = CopyReplyReady::admit(
            CopyMode::Nul(128),
            returned,
            Some((failed, error)),
            &mut heap,
            &mut work,
        )
        .unwrap();
        let value = ready
            .copy(AdmittedWindowRead { raw: &raw() }, &mut heap, &mut work)
            .unwrap();
        assert_eq!(payload(&heap, &value).bytes().unwrap(), &[65; 128]);
        assert_eq!(READS.get(), 257);
    }

    #[test]
    fn window_argument_disposal_retains_fixed_host_stack() {
        std::thread::Builder::new()
            .stack_size(64 * 1024)
            .spawn(|| {
                let mut ty = crate::types::Type::Unit;
                for _ in 0..32_768 {
                    ty = crate::types::Type::Application(
                        Box::new(ty),
                        Box::new(crate::types::Type::Unit),
                    );
                }
                drop(WindowArguments(vec![
                    crate::types::KindedArgument::TypeArg(ty),
                ]));
            })
            .unwrap()
            .join()
            .unwrap();
    }
}

#[cfg(test)]
#[path = "checked_copy_boundary_tests.rs"]
mod checked_copy_boundary_tests;
