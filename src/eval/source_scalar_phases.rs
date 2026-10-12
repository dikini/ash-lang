//! Consuming native-call phases in the existing evaluator machine.

use super::{HeapCell, Location, Value};

use crate::{
    foreign::source_runtime::{
        NativeScalarCallError, NativeScalarConversionError, NativeScalarReply, NativeScalarValue,
        PrepaidScalarReport, widen_gnu_reply,
    },
    types::{ConstructorId, TypeWorkBudget},
};

// Root supplies this non-Clone per-request ticket after exact registry/binding,
// complete Type/Row instance, interpreter and operand-vector admission. It
// retains the original checked-symbol allocation and invokes only its sealed
// generated function. It is not constructible from a spelling or fn pointer.
use crate::foreign::source_bindings::{
    AdmittedSourceScalarInvocation, SourceScalarReturnedAuthority,
};

#[derive(Debug)]
pub(super) enum ScalarPhaseFailure {
    Conversion(NativeScalarConversionError),
    Wrapper(NativeScalarCallError),
    HeapReservation,
    HeapSlotInvariant,
}

// No fields, Clone, borrowed work ledger or public constructor. This one-step
// allowance has already been charged before native invocation. Recording uses
// no fallible charge/allocation; consuming this token discharges its work.
#[derive(Debug)]
struct PrepaidScalarRecord;

// This pre-published placeholder is Machine heap capacity already admitted and
// initialized before the call. It is inaccessible to Ash until reporting.
#[derive(Debug)]
struct ReservedReturnedSlot {
    location: Location,
    returned: ConstructorId,
}

#[derive(Debug)]
pub(super) struct ScalarCallReady<'binding> {
    invocation: AdmittedSourceScalarInvocation<'binding>,
    operands: Vec<NativeScalarValue>,
    report: PrepaidScalarReport,
    recording: PrepaidScalarRecord,
    slot: ReservedReturnedSlot,
}

#[derive(Debug)]
pub(super) struct ScalarCallReturned<'binding> {
    authority: SourceScalarReturnedAuthority<'binding>,
    raw: NativeScalarReply,
    report: PrepaidScalarReport,
    recording: PrepaidScalarRecord,
    slot: ReservedReturnedSlot,
}

#[derive(Debug)]
pub(super) struct ScalarCallRecorded<'binding> {
    // Retain the exact original descriptor and complete instance through report
    // publication; do not reconstruct source identity from raw reply values.
    _authority: SourceScalarReturnedAuthority<'binding>,
    raw: NativeScalarReply,
    report: PrepaidScalarReport,
    slot: ReservedReturnedSlot,
}

#[derive(Debug)]
pub(super) struct ScalarCallReported {
    value: Value,
}

#[derive(Debug)]
pub(super) enum ScalarCallProgress<'binding> {
    Ready(ScalarCallReady<'binding>),
    Returned(ScalarCallReturned<'binding>),
    Recorded(ScalarCallRecorded<'binding>),
}

impl<'binding> ScalarCallReady<'binding> {
    /// Operands have already been fallibly reserved, projected once in native
    /// order and narrowed, with their mathematical-magnitude work charged.
    /// This final preflight pays reporting, recording and heap construction;
    /// refusal destroys only owner-free scratch and never calls native code.
    pub(super) fn admit(
        invocation: AdmittedSourceScalarInvocation<'binding>,
        operands: Vec<NativeScalarValue>,
        heap: &mut Vec<HeapCell>,
        caller_work: &mut TypeWorkBudget,
    ) -> Result<Self, ScalarPhaseFailure> {
        let report = PrepaidScalarReport::admit(invocation.result(), caller_work)
            .map_err(ScalarPhaseFailure::Conversion)?;
        // One fixed recording step and one Returned heap constructor. These
        // are distinct work obligations from mathematical reply widening.
        caller_work.charge(2).map_err(|()| {
            ScalarPhaseFailure::Conversion(NativeScalarConversionError::WorkExhausted)
        })?;
        heap.try_reserve(1)
            .map_err(|_| ScalarPhaseFailure::HeapReservation)?;
        let slot = ReservedReturnedSlot {
            location: heap.len(),
            returned: invocation.returned_constructor(),
        };
        heap.push(HeapCell::Uninitialized);
        Ok(Self {
            invocation,
            operands,
            report,
            recording: PrepaidScalarRecord,
            slot,
        })
    }

    /// Consuming readiness makes this the sole native-invocation transition.
    /// The sealed generated wrapper may reject before the external call; its
    /// failure is terminal and cannot recover readiness for retry.
    pub(super) fn invoke(self) -> Result<ScalarCallReturned<'binding>, ScalarPhaseFailure> {
        let Self {
            invocation,
            operands,
            report,
            recording,
            slot,
        } = self;
        let (authority, raw) = invocation
            .invoke(&operands)
            .map_err(ScalarPhaseFailure::Wrapper)?;
        Ok(ScalarCallReturned {
            authority,
            raw,
            report,
            recording,
            slot,
        })
    }
}

impl<'binding> ScalarCallReturned<'binding> {
    /// The admitted subset has no owners, access, output slots or unreadable
    /// scalar results. This fixed-size transition records its bare raw scalar
    /// (or void) and initialized-report-slot receipt. It allocates nothing,
    /// charges no shared ledger, performs no Ash conversion and cannot refuse.
    pub(super) fn record(self) -> ScalarCallRecorded<'binding> {
        let Self {
            authority,
            raw,
            report,
            recording: PrepaidScalarRecord,
            slot,
        } = self;
        ScalarCallRecorded {
            _authority: authority,
            raw,
            report,
            slot,
        }
    }
}

impl ScalarCallRecorded<'_> {
    /// This is the first phase allowed to construct an Ash integer. Neither a
    /// conversion failure nor an invalid report slot can restore readiness.
    /// Integer's internal BigInt allocation still has its existing limitation.
    pub(super) fn report(
        self,
        heap: &mut [HeapCell],
    ) -> Result<ScalarCallReported, ScalarPhaseFailure> {
        let integer =
            widen_gnu_reply(self.raw, self.report).map_err(ScalarPhaseFailure::Conversion)?;
        let cell = heap
            .get_mut(self.slot.location)
            .ok_or(ScalarPhaseFailure::HeapSlotInvariant)?;
        if !matches!(cell, HeapCell::Uninitialized) {
            return Err(ScalarPhaseFailure::HeapSlotInvariant);
        }
        let payload = integer.map_or(Value::Unit, Value::Integer);
        *cell = HeapCell::Constructor(self.slot.returned, Some(payload));
        Ok(ScalarCallReported {
            value: Value::Location(self.slot.location),
        })
    }
}

impl ScalarCallReported {
    pub(super) fn into_value(self) -> Value {
        self.value
    }
}

impl<'runtime> super::Machine<'runtime> {
    /// This exact source-native path cannot select an ordinary handler or use a
    /// legacy manifest fallback. Request frames have already been consumed;
    /// every continuation frame remains in place until the ordinary return.
    pub(super) fn prepare_source_scalar_request(
        &mut self,
        operation: crate::types::OperationId,
        effect: crate::types::EffectInstance,
        value: Value,
        symbol: &std::sync::Arc<crate::foreign::checked_source::CheckedForeignSymbol>,
    ) -> Result<(), super::RuntimeFailure> {
        use crate::foreign::source_contract::PreparedOperandSource;
        use crate::foreign::source_runtime::narrow_gnu_scalar;
        if self.pending_source_call.is_some()
            || self.control.is_some()
            || operation != symbol.operation()
            || effect.effect() != symbol.effect()
        {
            return Err(super::RuntimeFailure::ForeignBinding);
        }
        let bindings = self
            .source_bindings
            .ok_or(super::RuntimeFailure::ForeignBinding)?;
        super::charge_effect_work(&mut self.instantiation_work, 1, super::RuntimePhase::Access)?;
        let errors = self
            .source_errors
            .ok_or(super::RuntimeFailure::ForeignBinding)?;
        let hidden = *errors
            .get(&symbol.call_codec().module())
            .ok_or(super::RuntimeFailure::ForeignBinding)?;
        let invocation = bindings.request(symbol, effect, hidden, &mut self.instantiation_work)?;
        let source = invocation.symbol().symbol();
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
            let integer =
                source_integer_leaf(&self.heap, &value, path, &mut self.instantiation_work)?;
            let crate::foreign::source_contract::PreparedRepresentation::Scalar(representation) =
                operand.representation()
            else {
                return Err(super::RuntimeFailure::ForeignBinding);
            };
            match narrow_gnu_scalar(integer, representation, &mut self.instantiation_work) {
                Ok(operand) => operands.push(operand),
                Err(NativeScalarConversionError::OutOfRange) => {
                    self.control = Some(super::Control::Return(prepare_conversion_refusal(
                        &mut self.heap,
                        &invocation,
                        &mut self.instantiation_work,
                    )?));
                    return Ok(());
                }
                Err(error) => return Err(conversion_failure(error, &self.instantiation_work)),
            }
        }
        let ready = ScalarCallReady::admit(
            invocation,
            operands,
            &mut self.heap,
            &mut self.instantiation_work,
        )
        .map_err(|error| phase_failure(error, &self.instantiation_work))?;
        self.pending_source_call = Some(ScalarCallProgress::Ready(ready));
        Ok(())
    }

    /// Returns true when one native phase ran. Returned is deliberately handled
    /// before disposal checks: recording cannot refuse, allocate or charge work.
    pub(super) fn step_source_scalar(&mut self) -> Result<bool, super::RuntimeFailure> {
        let Some(progress) = self.pending_source_call.take() else {
            return Ok(false);
        };
        match progress {
            ScalarCallProgress::Returned(returned) => {
                #[cfg(test)]
                let returned = post_record_test::returned(returned, &mut self.instantiation_work);
                let recorded = returned.record();
                #[cfg(test)]
                post_record_test::recorded(&recorded, &self.heap, &self.instantiation_work);
                self.pending_source_call = Some(ScalarCallProgress::Recorded(recorded));
            }
            ScalarCallProgress::Ready(ready) => {
                super::disposal::check()?;
                let returned = ready
                    .invoke()
                    .map_err(|error| phase_failure(error, &self.instantiation_work))?;
                self.pending_source_call = Some(ScalarCallProgress::Returned(returned));
            }
            ScalarCallProgress::Recorded(recorded) => {
                super::disposal::check()?;
                let reported = recorded.report(&mut self.heap);
                #[cfg(test)]
                post_record_test::reported(&reported, &self.heap);
                let reported =
                    reported.map_err(|error| phase_failure(error, &self.instantiation_work))?;
                self.control = Some(super::Control::Return(reported.into_value()));
            }
        }
        Ok(true)
    }
}

fn prepare_conversion_refusal(
    heap: &mut Vec<HeapCell>,
    invocation: &AdmittedSourceScalarInvocation<'_>,
    work: &mut TypeWorkBudget,
) -> Result<Value, super::RuntimeFailure> {
    // The canonical private error role is NULLARY, never a fabricated Unit
    // payload. Both cells/work are admitted before either constructor exists;
    // refusal is pre-call and publishes no CallReady phase.
    super::charge_effect_work(work, 2, super::RuntimePhase::Access)?;
    heap.try_reserve(2).map_err(|_| source_storage(2))?;
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

pub(super) fn source_integer_leaf<'value>(
    heap: &'value [HeapCell],
    mut value: &'value Value,
    path: &[usize],
    work: &mut TypeWorkBudget,
) -> Result<&'value crate::integer::Integer, super::RuntimeFailure> {
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
    if let Value::Integer(integer) = value {
        Ok(integer)
    } else {
        Err(super::RuntimeFailure::ForeignBinding)
    }
}

fn phase_failure(error: ScalarPhaseFailure, work: &TypeWorkBudget) -> super::RuntimeFailure {
    match error {
        ScalarPhaseFailure::Conversion(error) => conversion_failure(error, work),
        ScalarPhaseFailure::Wrapper(NativeScalarCallError::ArgumentContract) => {
            super::RuntimeFailure::ForeignBinding
        }
        ScalarPhaseFailure::HeapReservation => source_storage(1),
        ScalarPhaseFailure::HeapSlotInvariant => super::RuntimeFailure::InvalidControlState,
    }
}
fn conversion_failure(
    error: NativeScalarConversionError,
    work: &TypeWorkBudget,
) -> super::RuntimeFailure {
    match error {
        NativeScalarConversionError::WorkExhausted => {
            super::effect_work_failure(work, None, super::RuntimePhase::Access)
        }
        NativeScalarConversionError::OutOfRange
        | NativeScalarConversionError::InvalidRepresentation
        | NativeScalarConversionError::UnsupportedHost => super::RuntimeFailure::ForeignBinding,
    }
}
fn source_storage(units: usize) -> super::RuntimeFailure {
    super::resource_failure(
        super::ResourceFailureCause::StorageReservationFailed,
        super::RuntimePhase::Access,
        super::RuntimeResource::ResultHeapCells,
        Some(units),
        None,
    )
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

// One narrowly scoped injected continuation-work refusal witness. This instrumentation has
// no production fields, constructors, failure API or callback authority.
#[cfg(test)]
pub(crate) mod post_record_test {
    use super::*;
    use std::cell::Cell;

    #[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
    pub(crate) struct Observation {
        pub(crate) returned: usize,
        pub(crate) recorded: usize,
        pub(crate) reported: usize,
        pub(crate) recorded_with_zero_shared_work: bool,
        pub(crate) report_slot_published: bool,
    }

    #[derive(Clone, Copy)]
    struct State {
        inject: bool,
        slot: Option<usize>,
        observation: Observation,
    }

    thread_local! {
        static STATE: Cell<Option<State>> = const { Cell::new(None) };
    }

    pub(crate) fn observe<T>(inject: bool, run: impl FnOnce() -> T) -> (T, Observation) {
        struct Scope;
        impl Drop for Scope {
            fn drop(&mut self) {
                STATE.set(None);
            }
        }
        assert!(STATE.get().is_none(), "single scoped boundary witness");
        STATE.set(Some(State {
            inject,
            slot: None,
            observation: Observation::default(),
        }));
        let scope = Scope;
        let result = run();
        let observation = STATE.get().unwrap().observation;
        drop(scope);
        (result, observation)
    }

    pub(super) fn returned<'binding>(
        returned: ScalarCallReturned<'binding>,
        work: &mut TypeWorkBudget,
    ) -> ScalarCallReturned<'binding> {
        if let Some(mut state) = STATE.get() {
            state.observation.returned += 1;
            state.slot = Some(returned.slot.location);
            if state.inject {
                // Exhaust only this Machine's continuation allowance after
                // the valid typed callback returned. Readiness/report allowance
                // was prepaid. This is an injected resource failure, not a
                // native ABI/codec error or arbitrary execution authority.
                assert!(matches!(
                    returned.raw,
                    NativeScalarReply::Scalar(NativeScalarValue::I8(41))
                ));
                *work = TypeWorkBudget::with_limit(0);
            }
            STATE.set(Some(state));
        }
        returned
    }

    pub(super) fn recorded(
        recorded: &ScalarCallRecorded<'_>,
        heap: &[HeapCell],
        work: &TypeWorkBudget,
    ) {
        if let Some(mut state) = STATE.get() {
            assert_eq!(state.observation.returned, 1);
            assert_eq!(state.slot, Some(recorded.slot.location));
            assert!(matches!(
                heap.get(recorded.slot.location),
                Some(HeapCell::Uninitialized)
            ));
            state.observation.recorded += 1;
            state.observation.recorded_with_zero_shared_work = work.remaining() == 0;
            STATE.set(Some(state));
        }
    }

    pub(super) fn reported(
        result: &Result<ScalarCallReported, ScalarPhaseFailure>,
        heap: &[HeapCell],
    ) {
        if let Some(mut state) = STATE.get() {
            assert_eq!(
                state.observation.recorded, 1,
                "record precedes report/refusal"
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
}
