//! Consuming source-owner native phases. Guards remain outside ordinary Ash
//! values and every reporting cell is reserved before irreversible native work.

use std::sync::Arc;

use super::{ActivationKey, HeapCell, Location, Value};
use crate::{
    foreign::{
        source_bindings::{
            AdmittedSourceOwnerAcquireInvocation, AdmittedSourceOwnerTeardownInvocation,
            SourceOwnerReturnedAuthority,
        },
        source_runtime::{
            NativeOwnerCallReturned, NativeOwnerConsumed, NativeOwnerGuard, NativeScalarCallError,
            NativeScalarValue,
        },
    },
    types::{ConstructorId, TypeWorkBudget},
};

#[derive(Debug)]
pub(super) enum OwnerPhaseFailure {
    WorkReservation,
    HeapReservation(usize),
    HeapSlotInvariant,
    Authority,
    Wrapper(NativeScalarCallError),
}

#[derive(Debug)]
struct PrepaidOwnerRecord;

#[derive(Debug)]
struct AcquireReportSlots {
    boundary: usize,
    nullable: Location,
    output: Location,
    returned: Location,
    null: ConstructorId,
    nonnull: ConstructorId,
    readable: ConstructorId,
    returned_constructor: ConstructorId,
    activation: ActivationKey,
}

#[derive(Debug)]
pub(super) struct OwnerAcquireReady<'binding> {
    invocation: AdmittedSourceOwnerAcquireInvocation<'binding>,
    operands: Vec<NativeScalarValue>,
    recording: PrepaidOwnerRecord,
    slots: AcquireReportSlots,
}

#[derive(Debug)]
pub(super) struct OwnerAcquireReturned<'binding> {
    authority: SourceOwnerReturnedAuthority<'binding>,
    raw: NativeOwnerCallReturned,
    recording: PrepaidOwnerRecord,
    slots: AcquireReportSlots,
}

#[derive(Debug)]
pub(super) struct OwnerAcquireRecorded<'binding> {
    _authority: SourceOwnerReturnedAuthority<'binding>,
    guard: Option<NativeOwnerGuard>,
    slots: AcquireReportSlots,
}

#[derive(Debug)]
pub(super) struct OwnerAcquireReported {
    boundary: usize,
    activation: ActivationKey,
    value: Value,
    guard: Option<NativeOwnerGuard>,
}

#[derive(Debug)]
struct TeardownReportSlots {
    boundary: usize,
    activation: ActivationKey,
    disposition: Location,
    returned: Location,
    consumed: ConstructorId,
    returned_constructor: ConstructorId,
}

/// Report and recording storage are prepared while the boundary still owns its
/// live guard. Only after successful admission may the caller detach ownership.
#[derive(Debug)]
pub(super) struct OwnerTeardownPrepared<'binding> {
    invocation: AdmittedSourceOwnerTeardownInvocation<'binding>,
    recording: PrepaidOwnerRecord,
    slots: TeardownReportSlots,
}

#[derive(Debug)]
pub(super) struct OwnerTeardownReady<'binding> {
    invocation: AdmittedSourceOwnerTeardownInvocation<'binding>,
    guard: NativeOwnerGuard,
    recording: PrepaidOwnerRecord,
    slots: TeardownReportSlots,
}

#[derive(Debug)]
pub(super) struct OwnerTeardownReturned<'binding> {
    authority: SourceOwnerReturnedAuthority<'binding>,
    consumed: NativeOwnerConsumed,
    recording: PrepaidOwnerRecord,
    slots: TeardownReportSlots,
}

#[derive(Debug)]
pub(super) struct OwnerTeardownRecorded<'binding> {
    _authority: SourceOwnerReturnedAuthority<'binding>,
    consumed: NativeOwnerConsumed,
    slots: TeardownReportSlots,
}

#[derive(Debug)]
pub(super) struct OwnerTeardownReported {
    boundary: usize,
    activation: ActivationKey,
    value: Value,
    consumed: NativeOwnerConsumed,
}

#[derive(Debug)]
pub(super) enum SourceOwnerCallProgress<'binding> {
    AcquireReady(OwnerAcquireReady<'binding>),
    AcquireReturned(OwnerAcquireReturned<'binding>),
    AcquireRecorded(OwnerAcquireRecorded<'binding>),
    TeardownReady(OwnerTeardownReady<'binding>),
    TeardownReturned(OwnerTeardownReturned<'binding>),
    TeardownRecorded(OwnerTeardownRecorded<'binding>),
}

fn reserve_slots(
    heap: &mut Vec<HeapCell>,
    work: &mut TypeWorkBudget,
    count: usize,
) -> Result<Location, OwnerPhaseFailure> {
    // Recording and the final fixed authority check are separate obligations
    // from the exact report constructor cells, all charged before native entry.
    work.charge(count + 2)
        .map_err(|()| OwnerPhaseFailure::WorkReservation)?;
    heap.try_reserve(count)
        .map_err(|_| OwnerPhaseFailure::HeapReservation(count))?;
    let first = heap.len();
    for _ in 0..count {
        heap.push(HeapCell::Uninitialized);
    }
    Ok(first)
}

fn empty_slots(heap: &[HeapCell], first: Location, count: usize) -> bool {
    first
        .checked_add(count)
        .and_then(|end| heap.get(first..end))
        .is_some_and(|cells| {
            cells
                .iter()
                .all(|cell| matches!(cell, HeapCell::Uninitialized))
        })
}

impl<'binding> OwnerAcquireReady<'binding> {
    /// The invocation already retains the exact sealed teardown and its inline
    /// empty guard. Mathematical operand projection/narrowing precedes this
    /// final report preflight; no failure here invokes acquisition.
    pub(super) fn admit(
        invocation: AdmittedSourceOwnerAcquireInvocation<'binding>,
        operands: Vec<NativeScalarValue>,
        initialized_bytes: Option<usize>,
        activation: ActivationKey,
        boundary: usize,
        heap: &mut Vec<HeapCell>,
        work: &mut TypeWorkBudget,
    ) -> Result<Self, OwnerPhaseFailure> {
        let invocation = invocation
            .prepare_initialized_bytes(initialized_bytes, work)
            .map_err(|error| {
                if matches!(error, super::RuntimeFailure::Report(_)) {
                    OwnerPhaseFailure::WorkReservation
                } else {
                    OwnerPhaseFailure::Authority
                }
            })?;
        let nullable = invocation.nullable_constructors();
        let readable = invocation.readable_constructor();
        let returned_constructor = invocation.returned_constructor();
        let first = reserve_slots(heap, work, 3)?;
        Ok(Self {
            invocation,
            operands,
            recording: PrepaidOwnerRecord,
            slots: AcquireReportSlots {
                boundary,
                nullable: first,
                output: first + 1,
                returned: first + 2,
                null: nullable[0],
                nonnull: nullable[1],
                readable,
                returned_constructor,
                activation,
            },
        })
    }

    pub(super) fn invoke(self) -> Result<OwnerAcquireReturned<'binding>, OwnerPhaseFailure> {
        let Self {
            invocation,
            operands,
            recording,
            slots,
        } = self;
        let (authority, raw) = invocation
            .invoke(&operands)
            .map_err(OwnerPhaseFailure::Wrapper)?;
        Ok(OwnerAcquireReturned {
            authority,
            raw,
            recording,
            slots,
        })
    }
}

impl<'binding> OwnerAcquireReturned<'binding> {
    /// Immediately records already-armed native ownership. No allocation,
    /// disposal check, shared charge, codec conversion or refusal can intervene.
    pub(super) fn record(self) -> OwnerAcquireRecorded<'binding> {
        let Self {
            authority,
            raw,
            recording: PrepaidOwnerRecord,
            slots,
        } = self;
        let guard = raw.record().into_guard();
        OwnerAcquireRecorded {
            _authority: authority,
            guard,
            slots,
        }
    }
}

impl OwnerAcquireRecorded<'_> {
    /// Returns the unique guard separately. The caller must place it in its
    /// reserved exact scope boundary before exposing this nonowning Ash token.
    /// Failure keeps the unpublished guard owned here until safe destruction.
    pub(super) fn report(
        self,
        heap: &mut [HeapCell],
    ) -> Result<OwnerAcquireReported, OwnerPhaseFailure> {
        if !empty_slots(heap, self.slots.nullable, 3) {
            return Err(OwnerPhaseFailure::HeapSlotInvariant);
        }
        let (constructor, payload) = if self.guard.is_some() {
            (
                self.slots.nonnull,
                Some(Value::NativeStateView(self.slots.activation)),
            )
        } else {
            (self.slots.null, None)
        };
        heap[self.slots.nullable] = HeapCell::Constructor(constructor, payload);
        heap[self.slots.output] = HeapCell::Constructor(
            self.slots.readable,
            Some(Value::Location(self.slots.nullable)),
        );
        heap[self.slots.returned] = HeapCell::Constructor(
            self.slots.returned_constructor,
            Some(Value::Location(self.slots.output)),
        );
        Ok(OwnerAcquireReported {
            boundary: self.slots.boundary,
            activation: self.slots.activation,
            value: Value::Location(self.slots.returned),
            guard: self.guard,
        })
    }
}

impl OwnerAcquireReported {
    pub(super) fn boundary(&self) -> usize {
        self.boundary
    }
    pub(super) fn activation(&self) -> ActivationKey {
        self.activation
    }
    pub(super) fn into_parts(self) -> (Value, Option<NativeOwnerGuard>) {
        (self.value, self.guard)
    }
}

impl<'binding> OwnerTeardownPrepared<'binding> {
    pub(super) fn admit(
        invocation: AdmittedSourceOwnerTeardownInvocation<'binding>,
        guard: &NativeOwnerGuard,
        activation: ActivationKey,
        boundary: usize,
        heap: &mut Vec<HeapCell>,
        work: &mut TypeWorkBudget,
    ) -> Result<Self, OwnerPhaseFailure> {
        // Authentication happens while the enclosing boundary retains its
        // ownership edge, before any native call or detached readiness exists.
        if !Arc::ptr_eq(invocation.owner(), guard.owner()) {
            return Err(OwnerPhaseFailure::Authority);
        }
        let consumed = invocation.consumed_constructor();
        let returned_constructor = invocation.returned_constructor();
        let first = reserve_slots(heap, work, 2)?;
        Ok(Self {
            invocation,
            recording: PrepaidOwnerRecord,
            slots: TeardownReportSlots {
                boundary,
                activation,
                disposition: first,
                returned: first + 1,
                consumed,
                returned_constructor,
            },
        })
    }

    pub(super) fn ready(
        self,
        guard: NativeOwnerGuard,
    ) -> Result<OwnerTeardownReady<'binding>, OwnerPhaseFailure> {
        if !Arc::ptr_eq(self.invocation.owner(), guard.owner()) {
            return Err(OwnerPhaseFailure::Authority);
        }
        Ok(OwnerTeardownReady {
            invocation: self.invocation,
            guard,
            recording: self.recording,
            slots: self.slots,
        })
    }
}

impl<'binding> OwnerTeardownReady<'binding> {
    /// The unique guard holds the exact teardown sealed before acquisition.
    /// Its unconditional void call consumes once and yields a non-Clone receipt.
    pub(super) fn invoke(self) -> OwnerTeardownReturned<'binding> {
        let Self {
            invocation,
            guard,
            recording,
            slots,
        } = self;
        let (authority, consumed) = invocation.invoke(guard);
        OwnerTeardownReturned {
            authority,
            consumed,
            recording,
            slots,
        }
    }
}

impl<'binding> OwnerTeardownReturned<'binding> {
    pub(super) fn record(self) -> OwnerTeardownRecorded<'binding> {
        let Self {
            authority,
            consumed,
            recording: PrepaidOwnerRecord,
            slots,
        } = self;
        OwnerTeardownRecorded {
            _authority: authority,
            consumed,
            slots,
        }
    }
}

impl OwnerTeardownRecorded<'_> {
    pub(super) fn report(
        self,
        heap: &mut [HeapCell],
    ) -> Result<OwnerTeardownReported, OwnerPhaseFailure> {
        if !empty_slots(heap, self.slots.disposition, 2) {
            return Err(OwnerPhaseFailure::HeapSlotInvariant);
        }
        heap[self.slots.disposition] =
            HeapCell::Constructor(self.slots.consumed, Some(Value::Unit));
        heap[self.slots.returned] = HeapCell::Constructor(
            self.slots.returned_constructor,
            Some(Value::Location(self.slots.disposition)),
        );
        Ok(OwnerTeardownReported {
            boundary: self.slots.boundary,
            activation: self.slots.activation,
            value: Value::Location(self.slots.returned),
            consumed: self.consumed,
        })
    }
}

impl OwnerTeardownReported {
    pub(super) fn boundary(&self) -> usize {
        self.boundary
    }
    pub(super) fn activation(&self) -> ActivationKey {
        self.activation
    }
    pub(super) fn into_parts(self) -> (Value, NativeOwnerConsumed) {
        (self.value, self.consumed)
    }
}

/// Pre-call scalar conversion refusal is an ordinary Call report. Neither a
/// readiness phase nor owner publication exists when these cells are built.
pub(super) fn prepare_conversion_refusal(
    heap: &mut Vec<HeapCell>,
    invocation: &AdmittedSourceOwnerAcquireInvocation<'_>,
    work: &mut TypeWorkBudget,
) -> Result<Value, super::RuntimeFailure> {
    super::charge_effect_work(work, 2, super::RuntimePhase::Access)?;
    heap.try_reserve(2).map_err(|_| {
        super::resource_failure(
            super::ResourceFailureCause::StorageReservationFailed,
            super::RuntimePhase::Access,
            super::RuntimeResource::ResultHeapCells,
            Some(2),
            None,
        )
    })?;
    let error = heap.len();
    heap.push(HeapCell::Constructor(
        invocation.hidden_error_constructor(),
        None,
    ));
    let report = heap.len();
    heap.push(HeapCell::Constructor(
        invocation.conversion_failed_constructor(),
        Some(Value::Location(error)),
    ));
    Ok(Value::Location(report))
}

pub(super) fn phase_failure(
    error: OwnerPhaseFailure,
    work: &TypeWorkBudget,
) -> super::RuntimeFailure {
    match error {
        OwnerPhaseFailure::WorkReservation => {
            super::effect_work_failure(work, None, super::RuntimePhase::Access)
        }
        OwnerPhaseFailure::HeapReservation(count) => super::resource_failure(
            super::ResourceFailureCause::StorageReservationFailed,
            super::RuntimePhase::Access,
            super::RuntimeResource::ResultHeapCells,
            Some(count),
            None,
        ),
        OwnerPhaseFailure::HeapSlotInvariant => super::RuntimeFailure::InvalidControlState,
        OwnerPhaseFailure::Authority
        | OwnerPhaseFailure::Wrapper(NativeScalarCallError::ArgumentContract) => {
            super::RuntimeFailure::ForeignBinding
        }
    }
}

impl<'runtime> super::Machine<'runtime> {
    /// Selects an exact live source boundary and a request in its authenticated
    /// lifecycle forest. Full runtime Type/Row substitution is compared before
    /// either acquisition or consumption readiness can exist.
    pub(super) fn prepare_source_owner_request(
        &mut self,
        request: crate::core::NodeId,
        operation: crate::types::OperationId,
        effect: crate::types::EffectInstance,
        value: Value,
        symbol: &Arc<crate::foreign::checked_source::CheckedForeignSymbol>,
    ) -> Result<(), super::RuntimeFailure> {
        use crate::foreign::{
            source_bindings::{AdmittedSourceOwnerInvocation, SourceOwnerPhase},
            source_contract::{
                PreparedOperandSource, PreparedOwnerCall, PreparedRepresentation,
                PreparedScalarRepresentation,
            },
            source_runtime::{NativeScalarConversionError, narrow_gnu_scalar},
        };
        if self.pending_source_owner_call.is_some()
            || self.pending_source_call.is_some()
            || self.control.is_some()
            || operation != symbol.operation()
            || effect.effect() != symbol.effect()
        {
            return Err(super::RuntimeFailure::ForeignBinding);
        }
        let bindings = self
            .source_bindings
            .ok_or(super::RuntimeFailure::ForeignBinding)?;
        let phase = match symbol.owner_role() {
            Some(PreparedOwnerCall::Acquire { .. }) => SourceOwnerPhase::Acquire,
            Some(PreparedOwnerCall::Teardown { .. }) => SourceOwnerPhase::Finish,
            None => return Err(super::RuntimeFailure::ForeignBinding),
        };
        let expected_phase = match phase {
            SourceOwnerPhase::Acquire => super::ProviderPhase::Acquire,
            SourceOwnerPhase::Finish => super::ProviderPhase::Finish,
        };
        let mut selected = None;
        for (index, frame) in self.frames.iter().enumerate().rev() {
            super::charge_effect_work(
                &mut self.instantiation_work,
                1,
                super::RuntimePhase::Access,
            )?;
            let super::Frame::SourceResourceBoundary(boundary) = frame else {
                continue;
            };
            let Some(super::ExecutableNode::Effect(scope_node)) = self.program.node(boundary.node)
            else {
                return Err(super::RuntimeFailure::InvalidControlState);
            };
            let crate::core::EffectExprKind::Operation(
                crate::core::EffectOperation::SourceResourceScope(scope),
            ) = &scope_node.kind
            else {
                return Err(super::RuntimeFailure::InvalidControlState);
            };
            super::charge_effect_work(
                &mut self.instantiation_work,
                scope.native_interpretations().len(),
                super::RuntimePhase::Access,
            )?;
            let Some(interpretation) =
                scope
                    .native_interpretations()
                    .iter()
                    .find(|interpretation| {
                        interpretation.symbol().operation() == operation
                            && Arc::ptr_eq(interpretation.symbol(), symbol)
                    })
            else {
                continue;
            };
            let actual = boundary.environment.instantiation.effect(
                interpretation.effect(),
                &mut self.instantiation_work,
                Some(super::RuntimePhase::Access),
            )?;
            if !same_instance(&actual, &effect, &mut self.instantiation_work)? {
                continue;
            }
            if boundary.phase != expected_phase
                || boundary.consumed
                || phase == SourceOwnerPhase::Acquire && boundary.owner.is_some()
            {
                return Err(super::RuntimeFailure::ForeignBinding);
            }
            selected = Some((index, boundary.node, boundary.key));
            break;
        }
        let (index, node, key) = selected.ok_or(super::RuntimeFailure::ForeignBinding)?;
        let invocation = bindings.admit_source_owner_invocation(
            &self.program,
            node,
            request,
            phase,
            &effect,
            symbol,
            &mut self.instantiation_work,
        )?;
        match invocation {
            AdmittedSourceOwnerInvocation::Acquire(invocation) => {
                let source = invocation.symbol().symbol();
                let Some(PreparedOwnerCall::Acquire {
                    initialized_bytes, ..
                }) = invocation.symbol().owner_role()
                else {
                    return Err(super::RuntimeFailure::ForeignBinding);
                };
                // This path is the original authored source leaf. It need not
                // be an ABI operand, and private resource data grants no extent.
                let initialized_bytes = if let Some(initialized) = initialized_bytes {
                    #[cfg(test)]
                    post_record_test::initialized_extent_preflight(&mut self.instantiation_work);
                    let integer = super::source_scalar_phases::source_integer_leaf(
                        &self.heap,
                        &value,
                        initialized.extent(),
                        &mut self.instantiation_work,
                    )?;
                    match narrow_gnu_scalar(
                        integer,
                        PreparedScalarRepresentation::SizeT,
                        &mut self.instantiation_work,
                    ) {
                        Ok(NativeScalarValue::USize(extent)) => Some(extent),
                        Err(NativeScalarConversionError::OutOfRange) => {
                            self.control =
                                Some(super::Control::Return(prepare_conversion_refusal(
                                    &mut self.heap,
                                    &invocation,
                                    &mut self.instantiation_work,
                                )?));
                            return Ok(());
                        }
                        Err(NativeScalarConversionError::WorkExhausted) => {
                            return Err(super::effect_work_failure(
                                &self.instantiation_work,
                                None,
                                super::RuntimePhase::Access,
                            ));
                        }
                        _ => return Err(super::RuntimeFailure::ForeignBinding),
                    }
                } else {
                    None
                };
                let mut operands = Vec::new();
                super::charge_effect_work(
                    &mut self.instantiation_work,
                    source.operands().len(),
                    super::RuntimePhase::Access,
                )?;
                operands
                    .try_reserve_exact(source.operands().len())
                    .map_err(|_| operand_storage(source.operands().len()))?;
                for operand in source.operands() {
                    let PreparedOperandSource::Source(path) = operand.source() else {
                        return Err(super::RuntimeFailure::ForeignBinding);
                    };
                    let integer = super::source_scalar_phases::source_integer_leaf(
                        &self.heap,
                        &value,
                        path,
                        &mut self.instantiation_work,
                    )?;
                    let PreparedRepresentation::Scalar(representation) = operand.representation()
                    else {
                        return Err(super::RuntimeFailure::ForeignBinding);
                    };
                    match narrow_gnu_scalar(integer, representation, &mut self.instantiation_work) {
                        Ok(operand) => operands.push(operand),
                        Err(NativeScalarConversionError::OutOfRange) => {
                            self.control =
                                Some(super::Control::Return(prepare_conversion_refusal(
                                    &mut self.heap,
                                    &invocation,
                                    &mut self.instantiation_work,
                                )?));
                            return Ok(());
                        }
                        Err(NativeScalarConversionError::WorkExhausted) => {
                            return Err(super::effect_work_failure(
                                &self.instantiation_work,
                                None,
                                super::RuntimePhase::Access,
                            ));
                        }
                        Err(_) => return Err(super::RuntimeFailure::ForeignBinding),
                    }
                }
                let ready = OwnerAcquireReady::admit(
                    invocation,
                    operands,
                    initialized_bytes,
                    key,
                    index,
                    &mut self.heap,
                    &mut self.instantiation_work,
                )
                .map_err(|error| phase_failure(error, &self.instantiation_work))?;
                self.pending_source_owner_call = Some(SourceOwnerCallProgress::AcquireReady(ready));
            }
            AdmittedSourceOwnerInvocation::Teardown(invocation) => {
                // The bounded runtime admits exactly one Current opaque operand;
                // it is the nonowning state key of this exact live activation.
                let [operand] = symbol.symbol().operands() else {
                    return Err(super::RuntimeFailure::ForeignBinding);
                };
                let PreparedOperandSource::Current(path) = operand.source() else {
                    return Err(super::RuntimeFailure::ForeignBinding);
                };
                if current_key(&self.heap, &value, path, &mut self.instantiation_work)? != key {
                    return Err(super::RuntimeFailure::ForeignBinding);
                }
                let super::Frame::SourceResourceBoundary(boundary) = &self.frames[index] else {
                    return Err(super::RuntimeFailure::InvalidControlState);
                };
                let guard = boundary
                    .owner
                    .as_ref()
                    .ok_or(super::RuntimeFailure::ForeignBinding)?;
                let prepared = OwnerTeardownPrepared::admit(
                    invocation,
                    guard,
                    key,
                    index,
                    &mut self.heap,
                    &mut self.instantiation_work,
                )
                .map_err(|error| phase_failure(error, &self.instantiation_work))?;
                // Every fallible operand/report/authority admission precedes
                // removal of the boundary's one native ownership edge.
                let super::Frame::SourceResourceBoundary(boundary) = &mut self.frames[index] else {
                    return Err(super::RuntimeFailure::InvalidControlState);
                };
                let guard = boundary
                    .owner
                    .take()
                    .ok_or(super::RuntimeFailure::InvalidControlState)?;
                let ready = prepared
                    .ready(guard)
                    .map_err(|error| phase_failure(error, &self.instantiation_work))?;
                self.pending_source_owner_call =
                    Some(SourceOwnerCallProgress::TeardownReady(ready));
            }
        }
        Ok(())
    }

    /// Returned transitions run before every disposal check. Postnative
    /// recording cannot fail; terminal reporting keeps the unique guard safe.
    pub(super) fn step_source_owner(&mut self) -> Result<bool, super::RuntimeFailure> {
        let Some(progress) = self.pending_source_owner_call.take() else {
            return Ok(false);
        };
        match progress {
            SourceOwnerCallProgress::AcquireReturned(returned) => {
                #[cfg(test)]
                let returned =
                    post_record_test::acquire_returned(returned, &mut self.instantiation_work);
                let recorded = returned.record();
                #[cfg(test)]
                post_record_test::acquire_recorded(&recorded, &self.heap, &self.instantiation_work);
                self.pending_source_owner_call =
                    Some(SourceOwnerCallProgress::AcquireRecorded(recorded));
            }
            SourceOwnerCallProgress::TeardownReturned(returned) => {
                #[cfg(test)]
                let returned =
                    post_record_test::teardown_returned(returned, &mut self.instantiation_work);
                let recorded = returned.record();
                #[cfg(test)]
                post_record_test::teardown_recorded(
                    &recorded,
                    &self.heap,
                    &self.instantiation_work,
                );
                self.pending_source_owner_call =
                    Some(SourceOwnerCallProgress::TeardownRecorded(recorded));
            }
            SourceOwnerCallProgress::AcquireReady(ready) => {
                super::disposal::check()?;
                let returned = ready
                    .invoke()
                    .map_err(|error| phase_failure(error, &self.instantiation_work))?;
                self.pending_source_owner_call =
                    Some(SourceOwnerCallProgress::AcquireReturned(returned));
            }
            SourceOwnerCallProgress::TeardownReady(ready) => {
                super::disposal::check()?;
                self.pending_source_owner_call =
                    Some(SourceOwnerCallProgress::TeardownReturned(ready.invoke()));
            }
            SourceOwnerCallProgress::AcquireRecorded(recorded) => {
                super::disposal::check()?;
                let reported = recorded.report(&mut self.heap);
                #[cfg(test)]
                post_record_test::acquire_reported(&reported, &self.heap);
                let reported =
                    reported.map_err(|error| phase_failure(error, &self.instantiation_work))?;
                let key = reported.activation();
                let boundary_index = reported.boundary();
                let (value, guard) = reported.into_parts();
                let Some(super::Frame::SourceResourceBoundary(boundary)) =
                    self.frames.get_mut(boundary_index)
                else {
                    return Err(super::RuntimeFailure::InvalidControlState);
                };
                if boundary.key != key
                    || boundary.phase != super::ProviderPhase::Acquire
                    || boundary.owner.is_some()
                    || boundary.consumed
                {
                    return Err(super::RuntimeFailure::InvalidControlState);
                }
                // No charge or allocation can intervene between ownership
                // placement and publication of its nonowning state token.
                boundary.owner = guard;
                self.control = Some(super::Control::Return(value));
            }
            SourceOwnerCallProgress::TeardownRecorded(recorded) => {
                super::disposal::check()?;
                let reported = recorded.report(&mut self.heap);
                #[cfg(test)]
                post_record_test::teardown_reported(&reported, &self.heap);
                let reported =
                    reported.map_err(|error| phase_failure(error, &self.instantiation_work))?;
                let key = reported.activation();
                let boundary_index = reported.boundary();
                let (value, consumed) = reported.into_parts();
                let Some(super::Frame::SourceResourceBoundary(boundary)) =
                    self.frames.get_mut(boundary_index)
                else {
                    return Err(super::RuntimeFailure::InvalidControlState);
                };
                if boundary.key != key
                    || boundary.phase != super::ProviderPhase::Finish
                    || boundary.owner.is_some()
                    || boundary.consumed
                {
                    return Err(super::RuntimeFailure::InvalidControlState);
                }
                // This non-Clone receipt has no callback. It cannot replay the
                // destructor, even if later source report handling fails.
                let _authority = consumed.owner();
                boundary.consumed = true;
                self.control = Some(super::Control::Return(value));
            }
        }
        Ok(true)
    }
}

fn same_instance(
    expected: &crate::types::EffectInstance,
    actual: &crate::types::EffectInstance,
    work: &mut TypeWorkBudget,
) -> Result<bool, super::RuntimeFailure> {
    super::charge_effect_work(
        work,
        expected.arguments().len(),
        super::RuntimePhase::Access,
    )?;
    if expected.effect() != actual.effect()
        || expected.arguments().len() != actual.arguments().len()
    {
        return Ok(false);
    }
    for (expected, actual) in expected.arguments().iter().zip(actual.arguments()) {
        if !crate::types::same_kinded_argument_with_budget(expected, actual, work)
            .map_err(|()| super::effect_work_failure(work, None, super::RuntimePhase::Access))?
        {
            return Ok(false);
        }
    }
    Ok(true)
}

fn current_key<'value>(
    heap: &'value [HeapCell],
    mut value: &'value Value,
    path: &[usize],
    work: &mut TypeWorkBudget,
) -> Result<ActivationKey, super::RuntimeFailure> {
    let (first, rest) = path
        .split_first()
        .ok_or(super::RuntimeFailure::ForeignBinding)?;
    super::charge_effect_work(work, 1, super::RuntimePhase::Access)?;
    if let Value::Location(location) = value {
        let location = super::resolve_location_with_work(heap, *location, work)?;
        let Some(HeapCell::Tuple(fields)) = heap.get(location) else {
            return Err(super::RuntimeFailure::ForeignBinding);
        };
        value = fields
            .get(*first)
            .ok_or(super::RuntimeFailure::ForeignBinding)?;
    } else if *first != 0 {
        return Err(super::RuntimeFailure::ForeignBinding);
    }
    for component in rest {
        super::charge_effect_work(work, 1, super::RuntimePhase::Access)?;
        let Value::Location(location) = value else {
            return Err(super::RuntimeFailure::ForeignBinding);
        };
        let location = super::resolve_location_with_work(heap, *location, work)?;
        let Some(HeapCell::Tuple(fields)) = heap.get(location) else {
            return Err(super::RuntimeFailure::ForeignBinding);
        };
        value = fields
            .get(*component)
            .ok_or(super::RuntimeFailure::ForeignBinding)?;
    }
    match value {
        Value::NativeStateView(key) => Ok(*key),
        _ => Err(super::RuntimeFailure::ForeignBinding),
    }
}

fn operand_storage(units: usize) -> super::RuntimeFailure {
    super::resource_failure(
        super::ResourceFailureCause::StorageReservationFailed,
        super::RuntimePhase::Access,
        super::RuntimeResource::ForeignCodecStorage,
        Some(units),
        None,
    )
}

/// Scoped test-only continuation-work refusal after generated acquisition or
/// teardown returns. It grants no native callback or source lifecycle authority.
#[cfg(test)]
pub(crate) mod post_record_test {
    use super::{
        HeapCell, NativeOwnerGuard, OwnerAcquireRecorded, OwnerAcquireReported,
        OwnerAcquireReturned, OwnerPhaseFailure, OwnerTeardownRecorded, OwnerTeardownReported,
        OwnerTeardownReturned, TypeWorkBudget, Value, empty_slots,
    };
    use std::cell::Cell;

    #[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
    pub(crate) struct Observation {
        pub(crate) returned: usize,
        pub(crate) recorded: usize,
        pub(crate) reported: usize,
        pub(crate) recorded_with_zero_shared_work: bool,
        pub(crate) recorded_live_owner: bool,
        pub(crate) initialized_bytes: Option<usize>,
        pub(crate) report_slot_published: bool,
        pub(crate) teardown_returned: usize,
        pub(crate) teardown_recorded: usize,
        pub(crate) teardown_reported: usize,
        pub(crate) teardown_recorded_with_zero_shared_work: bool,
        pub(crate) teardown_consumed_report_published: bool,
    }

    #[derive(Clone, Copy)]
    struct State {
        inject: bool,
        phase: Phase,
        slot: Option<usize>,
        teardown_slots: Option<(usize, usize, crate::types::ConstructorId)>,
        observation: Observation,
    }
    thread_local! {
        static STATE: Cell<Option<State>> = const { Cell::new(None) };
    }

    #[derive(Clone, Copy, Eq, PartialEq)]
    enum Phase {
        AcquireReturn,
        TeardownReturn,
        InitializedExtentPreflight,
    }

    pub(crate) fn observe<T>(inject: bool, run: impl FnOnce() -> T) -> (T, Observation) {
        observe_phase(inject, Phase::AcquireReturn, run)
    }

    pub(crate) fn observe_teardown<T>(inject: bool, run: impl FnOnce() -> T) -> (T, Observation) {
        observe_phase(inject, Phase::TeardownReturn, run)
    }

    pub(crate) fn observe_extent_preflight<T>(run: impl FnOnce() -> T) -> (T, Observation) {
        observe_phase(true, Phase::InitializedExtentPreflight, run)
    }

    pub(super) fn initialized_extent_preflight(work: &mut TypeWorkBudget) {
        if STATE
            .get()
            .is_some_and(|state| state.inject && state.phase == Phase::InitializedExtentPreflight)
        {
            *work = TypeWorkBudget::with_limit(0);
        }
    }

    fn observe_phase<T>(inject: bool, phase: Phase, run: impl FnOnce() -> T) -> (T, Observation) {
        struct Scope;
        impl Drop for Scope {
            fn drop(&mut self) {
                STATE.set(None);
            }
        }
        assert!(
            STATE.get().is_none(),
            "single scoped owner boundary witness"
        );
        STATE.set(Some(State {
            inject,
            phase,
            slot: None,
            teardown_slots: None,
            observation: Observation::default(),
        }));
        let scope = Scope;
        let result = run();
        let observation = STATE.get().unwrap().observation;
        drop(scope);
        (result, observation)
    }

    pub(super) fn acquire_returned<'binding>(
        returned: OwnerAcquireReturned<'binding>,
        work: &mut TypeWorkBudget,
    ) -> OwnerAcquireReturned<'binding> {
        if let Some(mut state) = STATE.get() {
            state.observation.returned += 1;
            state.slot = Some(returned.slots.returned);
            if state.inject && state.phase == Phase::AcquireReturn {
                *work = TypeWorkBudget::with_limit(0);
            }
            STATE.set(Some(state));
        }
        returned
    }

    pub(super) fn acquire_recorded(
        recorded: &OwnerAcquireRecorded<'_>,
        heap: &[HeapCell],
        work: &TypeWorkBudget,
    ) {
        if let Some(mut state) = STATE.get() {
            assert_eq!(state.observation.returned, 1);
            assert_eq!(state.slot, Some(recorded.slots.returned));
            assert!(empty_slots(heap, recorded.slots.nullable, 3));
            state.observation.recorded += 1;
            state.observation.recorded_with_zero_shared_work = work.remaining() == 0;
            state.observation.recorded_live_owner = recorded.guard.is_some();
            state.observation.initialized_bytes = recorded
                .guard
                .as_ref()
                .and_then(NativeOwnerGuard::initialized_bytes);
            STATE.set(Some(state));
        }
    }

    pub(super) fn acquire_reported(
        result: &Result<OwnerAcquireReported, OwnerPhaseFailure>,
        heap: &[HeapCell],
    ) {
        if let Some(mut state) = STATE.get() {
            assert_eq!(
                state.observation.recorded, 1,
                "record precedes owner report/refusal"
            );
            if result.is_ok() {
                state.observation.reported += 1;
                state.observation.report_slot_published = matches!(
                    heap.get(state.slot.unwrap()),
                    Some(HeapCell::Constructor(_, _))
                );
            }
            STATE.set(Some(state));
        }
    }

    pub(super) fn teardown_returned<'binding>(
        returned: OwnerTeardownReturned<'binding>,
        work: &mut TypeWorkBudget,
    ) -> OwnerTeardownReturned<'binding> {
        if let Some(mut state) = STATE.get() {
            state.observation.teardown_returned += 1;
            state.teardown_slots = Some((
                returned.slots.returned,
                returned.slots.disposition,
                returned.slots.consumed,
            ));
            if state.inject && state.phase == Phase::TeardownReturn {
                *work = TypeWorkBudget::with_limit(0);
            }
            STATE.set(Some(state));
        }
        returned
    }

    pub(super) fn teardown_recorded(
        recorded: &OwnerTeardownRecorded<'_>,
        heap: &[HeapCell],
        work: &TypeWorkBudget,
    ) {
        if let Some(mut state) = STATE.get() {
            assert_eq!(state.observation.teardown_returned, 1);
            assert_eq!(
                state.teardown_slots,
                Some((
                    recorded.slots.returned,
                    recorded.slots.disposition,
                    recorded.slots.consumed
                ))
            );
            assert!(empty_slots(heap, recorded.slots.disposition, 2));
            // This phase owns only the non-Clone consumed receipt, whose type
            // contains original authority and no destructor callback.
            let _consumed_authority = recorded.consumed.owner();
            state.observation.teardown_recorded += 1;
            state.observation.teardown_recorded_with_zero_shared_work = work.remaining() == 0;
            STATE.set(Some(state));
        }
    }

    pub(super) fn teardown_reported(
        result: &Result<OwnerTeardownReported, OwnerPhaseFailure>,
        heap: &[HeapCell],
    ) {
        if let Some(mut state) = STATE.get() {
            assert_eq!(
                state.observation.teardown_recorded, 1,
                "consumption records before reporting"
            );
            if result.is_ok() {
                state.observation.teardown_reported += 1;
                let (returned, disposition, consumed) = state.teardown_slots.unwrap();
                state.observation.teardown_consumed_report_published = matches!(
                    heap.get(returned),
                    Some(HeapCell::Constructor(_, Some(Value::Location(actual)))) if *actual == disposition
                ) && matches!(
                    heap.get(disposition),
                    Some(HeapCell::Constructor(actual, Some(Value::Unit))) if *actual == consumed
                );
            }
            STATE.set(Some(state));
        }
    }
}
