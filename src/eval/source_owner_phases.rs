//! Guarded source-owner native phases. Guards remain outside ordinary Ash
//! values and every reporting cell is reserved before irreversible native work.

use std::sync::Arc;

use super::{ActivationKey, HeapCell, Location, Value};
use crate::{
    foreign::{
        source_bindings::{
            AdmittedSourceOwnerAcquireInvocation, AdmittedSourceOwnerBorrowInvocation,
            AdmittedSourceOwnerTeardownInvocation, SourceOwnerReturnedAuthority,
        },
        source_runtime::{
            NativeOwnerCallReturned, NativeOwnerDisposition, NativeOwnerGuard, NativeOwnerOperand,
            NativeScalarCallError, NativeScalarConversionError, NativeScalarValue,
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

/// The live source boundary retains its guard while this single-use ticket
/// owns all scalar reporting work/storage. It never moves or consumes an owner.
#[derive(Debug)]
pub(super) struct OwnerBorrowReady<'binding> {
    invocation: AdmittedSourceOwnerBorrowInvocation<'binding>,
    operands: Vec<NativeOwnerOperand>,
    report: crate::foreign::source_runtime::PrepaidScalarReport,
    returned: ConstructorId,
    location: Location,
    input_storage: Vec<Vec<u8>>,
}
impl<'binding> OwnerBorrowReady<'binding> {
    fn admit(
        invocation: AdmittedSourceOwnerBorrowInvocation<'binding>,
        operands: Vec<NativeOwnerOperand>,
        heap: &mut Vec<HeapCell>,
        work: &mut TypeWorkBudget,
    ) -> Result<Self, OwnerPhaseFailure> {
        let report =
            crate::foreign::source_runtime::PrepaidScalarReport::admit(invocation.result(), work)
                .map_err(|error| match error {
                NativeScalarConversionError::WorkExhausted => OwnerPhaseFailure::WorkReservation,
                _ => OwnerPhaseFailure::Authority,
            })?;
        work.charge(2)
            .map_err(|_| OwnerPhaseFailure::WorkReservation)?;
        heap.try_reserve(1)
            .map_err(|_| OwnerPhaseFailure::HeapReservation(1))?;
        let location = heap.len();
        heap.push(HeapCell::Uninitialized);
        let returned = invocation.returned_constructor();
        Ok(Self {
            invocation,
            operands,
            report,
            returned,
            location,
            input_storage: Vec::new(),
        })
    }
    fn with_inputs(mut self, input_storage: Vec<Vec<u8>>) -> Self {
        self.input_storage = input_storage;
        self
    }
    fn invoke_and_report(self, heap: &mut [HeapCell]) -> Result<Value, OwnerPhaseFailure> {
        let (_recorded_authority, raw) = self
            .invocation
            .invoke(&self.operands)
            .map_err(OwnerPhaseFailure::Wrapper)?;
        // Only the exact callback borrows these stable temporary addresses.
        // They are released after C returns, including every failure path.
        drop(self.input_storage);
        // Bare raw status is retained before extraction. Post-call failure is
        // terminal; neither this ticket nor a guard can be recovered for replay.
        let integer = crate::foreign::source_runtime::widen_gnu_reply(raw, self.report)
            .map_err(|_| OwnerPhaseFailure::Authority)?;
        let cell = heap
            .get_mut(self.location)
            .ok_or(OwnerPhaseFailure::HeapSlotInvariant)?;
        if !matches!(cell, HeapCell::Uninitialized) {
            return Err(OwnerPhaseFailure::HeapSlotInvariant);
        }
        *cell = HeapCell::Constructor(
            self.returned,
            Some(integer.map_or(Value::Unit, Value::Integer)),
        );
        Ok(Value::Location(self.location))
    }
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
    status: Option<AcquireStatusStorage>,
    offset: Option<AcquireOffsetStorage>,
}

#[derive(Debug)]
struct AcquireOffsetStorage {
    location: Location,
    nullable: Location,
    unreadable: ConstructorId,
    descriptor: crate::foreign::source_contract::PreparedOffsetOutput,
    input_start: usize,
    input_length: usize,
    prepaid: crate::foreign::source_runtime::PrepaidScalarReport,
}

#[derive(Debug)]
struct AcquireStatusStorage {
    prepaid: crate::foreign::source_runtime::PrepaidScalarReport,
    location: Location,
    fields: Box<[Value]>,
}

#[derive(Debug)]
pub(super) struct OwnerAcquireReady<'binding> {
    invocation: AdmittedSourceOwnerAcquireInvocation<'binding>,
    operands: Vec<NativeOwnerOperand>,
    recording: PrepaidOwnerRecord,
    slots: AcquireReportSlots,
    input_storage: Vec<Vec<u8>>,
}

#[derive(Debug)]
pub(super) struct OwnerAcquireReturned<'binding> {
    authority: SourceOwnerReturnedAuthority<'binding>,
    raw: NativeOwnerCallReturned,
    recording: PrepaidOwnerRecord,
    slots: AcquireReportSlots,
    input_storage: Vec<Vec<u8>>,
}

#[derive(Debug)]
pub(super) struct OwnerAcquireRecorded<'binding> {
    _authority: SourceOwnerReturnedAuthority<'binding>,
    guard: Option<NativeOwnerGuard>,
    slots: AcquireReportSlots,
    scalar: Option<crate::foreign::source_runtime::NativeScalarReply>,
    offset: Option<*mut core::ffi::c_void>,
    input_storage: Vec<Vec<u8>>,
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
    retained: ConstructorId,
    blocked: ConstructorId,
    returned_constructor: ConstructorId,
    status: Option<StatusReportStorage>,
}

#[derive(Debug)]
struct StatusReportStorage {
    prepaid: crate::foreign::source_runtime::PrepaidScalarReport,
}

/// Report and recording storage are prepared while the boundary still owns its
/// live guard. Only after successful admission may the caller detach ownership.
#[derive(Debug)]
pub(super) struct OwnerTeardownPrepared<'binding> {
    invocation: AdmittedSourceOwnerTeardownInvocation<'binding>,
    recording: PrepaidOwnerRecord,
    slots: TeardownReportSlots,
    blocked: bool,
}

#[derive(Debug)]
pub(super) struct OwnerTeardownReady<'binding> {
    invocation: AdmittedSourceOwnerTeardownInvocation<'binding>,
    guard: NativeOwnerGuard,
    operands: Vec<NativeOwnerOperand>,
    blocked: bool,
    recording: PrepaidOwnerRecord,
    slots: TeardownReportSlots,
}

#[derive(Debug)]
pub(super) struct OwnerTeardownReturned<'binding> {
    authority: SourceOwnerReturnedAuthority<'binding>,
    consumed: NativeOwnerDisposition,
    status: Option<crate::foreign::source_runtime::NativeOwnerStatus>,
    recording: PrepaidOwnerRecord,
    slots: TeardownReportSlots,
}

#[derive(Debug)]
pub(super) struct OwnerTeardownRecorded<'binding> {
    _authority: SourceOwnerReturnedAuthority<'binding>,
    consumed: NativeOwnerDisposition,
    status: Option<crate::foreign::source_runtime::NativeOwnerStatus>,
    slots: TeardownReportSlots,
}

#[derive(Debug)]
pub(super) struct OwnerTeardownReported {
    boundary: usize,
    activation: ActivationKey,
    value: Value,
    consumed: NativeOwnerDisposition,
}

#[derive(Debug)]
pub(super) enum SourceOwnerCallProgress<'binding> {
    BorrowReady(OwnerBorrowReady<'binding>),
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
        operands: Vec<NativeOwnerOperand>,
        initialized_bytes: Option<usize>,
        activation: ActivationKey,
        boundary: usize,
        heap: &mut Vec<HeapCell>,
        work: &mut TypeWorkBudget,
    ) -> Result<Self, OwnerPhaseFailure> {
        #[cfg(test)]
        let admission_budget = post_record_test::initialized_bytes_admission_begin(work);
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
        let offset = match invocation.symbol().owner_role() {
            Some(crate::foreign::source_contract::PreparedOwnerCall::OutputAcquire {
                offset,
                ..
            }) => *offset,
            _ => None,
        };
        let status = if matches!(
            invocation.symbol().owner_role(),
            Some(crate::foreign::source_contract::PreparedOwnerCall::OutputAcquire { .. })
        ) {
            let prepaid = crate::foreign::source_runtime::PrepaidScalarReport::admit(
                invocation.symbol().symbol().result(),
                work,
            )
            .map_err(|error| match error {
                NativeScalarConversionError::WorkExhausted => OwnerPhaseFailure::WorkReservation,
                _ => OwnerPhaseFailure::Authority,
            })?;
            let count = 2 + usize::from(offset.is_some());
            work.charge(count)
                .map_err(|()| OwnerPhaseFailure::WorkReservation)?;
            let mut fields = Vec::new();
            fields
                .try_reserve_exact(count)
                .map_err(|_| OwnerPhaseFailure::HeapReservation(count))?;
            for _ in 0..count {
                fields.push(Value::Unit);
            }
            Some((prepaid, fields.into_boxed_slice()))
        } else {
            None
        };
        let offset = offset
            .map(|descriptor| {
                // The extra fixed unit prepays the raw-result outcome comparison.
                work.charge(1)
                    .map_err(|()| OwnerPhaseFailure::WorkReservation)?;
                let prepaid = crate::foreign::source_runtime::PrepaidScalarReport::admit(
                    crate::foreign::source_contract::PreparedAbiResult::Scalar(
                        crate::foreign::source_contract::PreparedScalarRepresentation::SizeT,
                    ),
                    work,
                )
                .map_err(|_| OwnerPhaseFailure::WorkReservation)?;
                Ok((descriptor, prepaid))
            })
            .transpose()?;
        let first = reserve_slots(
            heap,
            work,
            3 + usize::from(status.is_some()) + 2 * usize::from(offset.is_some()),
        )?;
        let status = status.map(|(prepaid, fields)| AcquireStatusStorage {
            prepaid,
            fields,
            location: first + 3,
        });
        let offset = offset.map(|(descriptor, prepaid)| AcquireOffsetStorage {
            location: first + 5,
            nullable: first + 4,
            unreadable: invocation
                .symbol()
                .owner_codec()
                .expect("admitted output codec")
                .output_constructors()[0],
            descriptor,
            input_start: 0,
            input_length: 0,
            prepaid,
        });
        #[cfg(test)]
        post_record_test::initialized_bytes_admission_end(work, admission_budget);
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
                status,
                offset,
            },
            input_storage: Vec::new(),
        })
    }

    fn with_inputs(
        mut self,
        inputs: Vec<Vec<u8>>,
        work: &mut TypeWorkBudget,
    ) -> Result<Self, OwnerPhaseFailure> {
        if let Some(offset) = &mut self.slots.offset {
            work.charge(inputs.len().saturating_add(1))
                .map_err(|()| OwnerPhaseFailure::WorkReservation)?;
            let Some(NativeOwnerOperand::Address(input)) =
                self.operands.get(offset.descriptor.input_operand)
            else {
                return Err(OwnerPhaseFailure::Authority);
            };
            let mut selected = None;
            for bytes in &inputs {
                if bytes.as_ptr().cast_mut().cast::<core::ffi::c_void>() == *input
                    && selected.replace(bytes).is_some()
                {
                    return Err(OwnerPhaseFailure::Authority);
                }
            }
            let bytes = selected.ok_or(OwnerPhaseFailure::Authority)?;
            offset.input_start = bytes.as_ptr() as usize;
            offset.input_length = bytes
                .len()
                .checked_sub(1)
                .ok_or(OwnerPhaseFailure::Authority)?;
        }
        self.input_storage = inputs;
        Ok(self)
    }

    pub(super) fn invoke(self) -> Result<OwnerAcquireReturned<'binding>, OwnerPhaseFailure> {
        let Self {
            invocation,
            operands,
            recording,
            slots,
            input_storage,
        } = self;
        let (authority, raw) = invocation
            .invoke(&operands)
            .map_err(OwnerPhaseFailure::Wrapper)?;
        Ok(OwnerAcquireReturned {
            authority,
            raw,
            recording,
            slots,
            input_storage,
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
            input_storage,
        } = self;
        let (guard, scalar, offset) = raw.record().into_parts();
        OwnerAcquireRecorded {
            _authority: authority,
            guard,
            slots,
            scalar,
            offset,
            input_storage,
        }
    }
}

/// Integer-address comparison does not dereference an untrusted native pointer.
/// The exact call's stable NUL input owns the inclusive end position.
fn input_relative_offset(start: usize, length: usize, pointer: usize) -> Option<usize> {
    pointer
        .checked_sub(start)
        .filter(|distance| *distance <= length)
}

fn raw_scalar_literal(
    reply: crate::foreign::source_runtime::NativeScalarReply,
) -> Option<crate::foreign::source_contract::PreparedScalarValue> {
    use crate::foreign::source_runtime::NativeScalarReply;
    let (negative, magnitude) = match reply {
        NativeScalarReply::Scalar(NativeScalarValue::I8(value)) => {
            (value < 0, i64::from(value).unsigned_abs())
        }
        NativeScalarReply::Scalar(NativeScalarValue::I32(value)) => {
            (value < 0, i64::from(value).unsigned_abs())
        }
        NativeScalarReply::Scalar(NativeScalarValue::I64(value)) => {
            (value < 0, value.unsigned_abs())
        }
        NativeScalarReply::Scalar(NativeScalarValue::U8(value)) => (false, u64::from(value)),
        NativeScalarReply::Scalar(NativeScalarValue::U32(value)) => (false, u64::from(value)),
        NativeScalarReply::Scalar(NativeScalarValue::U64(value)) => (false, value),
        NativeScalarReply::Scalar(NativeScalarValue::USize(value)) => (false, value as u64),
        _ => return None,
    };
    Some(crate::foreign::source_contract::PreparedScalarValue {
        negative,
        magnitude,
    })
}

impl OwnerAcquireRecorded<'_> {
    /// Returns the unique guard separately. The caller must place it in its
    /// reserved exact scope boundary before exposing this nonowning Ash token.
    /// Failure keeps the unpublished guard owned here until safe destruction.
    pub(super) fn report(
        self,
        heap: &mut [HeapCell],
    ) -> Result<OwnerAcquireReported, OwnerPhaseFailure> {
        if !empty_slots(
            heap,
            self.slots.nullable,
            3 + usize::from(self.slots.status.is_some())
                + 2 * usize::from(self.slots.offset.is_some()),
        ) {
            return Err(OwnerPhaseFailure::HeapSlotInvariant);
        }
        let offset_value = match (self.slots.offset, self.offset) {
            (None, None) => None,
            (Some(offset), pointer) => {
                let raw = self.scalar.ok_or(OwnerPhaseFailure::Authority)?;
                let literal = raw_scalar_literal(raw).ok_or(OwnerPhaseFailure::Authority)?;
                let readable = literal == offset.descriptor.status;
                let output = if readable {
                    let pointer = pointer.ok_or(OwnerPhaseFailure::Authority)?;
                    let (constructor, payload) = if pointer.is_null() {
                        (self.slots.null, None)
                    } else {
                        let distance = input_relative_offset(
                            offset.input_start,
                            offset.input_length,
                            pointer as usize,
                        )
                        .ok_or(OwnerPhaseFailure::Authority)?;
                        let integer = crate::foreign::source_runtime::widen_gnu_reply(
                            crate::foreign::source_runtime::NativeScalarReply::Scalar(
                                NativeScalarValue::USize(distance),
                            ),
                            offset.prepaid,
                        )
                        .map_err(|_| OwnerPhaseFailure::Authority)?
                        .ok_or(OwnerPhaseFailure::Authority)?;
                        (self.slots.nonnull, Some(Value::Integer(integer)))
                    };
                    heap[offset.nullable] = HeapCell::Constructor(constructor, payload);
                    HeapCell::Constructor(
                        self.slots.readable,
                        Some(Value::Location(offset.nullable)),
                    )
                } else {
                    if pointer.is_some() {
                        return Err(OwnerPhaseFailure::Authority);
                    }
                    // A reserved unused nullable slot remains internal scratch.
                    HeapCell::Constructor(offset.unreadable, None)
                };
                heap[offset.location] = output;
                Some(Value::Location(offset.location))
            }
            _ => return Err(OwnerPhaseFailure::Authority),
        };
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
        let payload = match (self.slots.status, self.scalar) {
            (Some(mut status), Some(scalar)) => {
                let integer =
                    crate::foreign::source_runtime::widen_gnu_reply(scalar, status.prepaid)
                        .map_err(|_| OwnerPhaseFailure::Authority)?
                        .ok_or(OwnerPhaseFailure::Authority)?;
                status.fields[0] = Value::Integer(integer);
                status.fields[1] = Value::Location(self.slots.output);
                if let Some(offset) = offset_value {
                    status.fields[2] = offset;
                }
                heap[status.location] = HeapCell::Tuple(status.fields);
                Value::Location(status.location)
            }
            (None, None) => Value::Location(self.slots.output),
            _ => return Err(OwnerPhaseFailure::Authority),
        };
        heap[self.slots.returned] =
            HeapCell::Constructor(self.slots.returned_constructor, Some(payload));
        // Stable input scratch outlives owner recording and output extraction.
        drop(self.input_storage);
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
        let [consumed, retained, blocked] = invocation.disposition_constructors();
        let has_dependents = guard
            .preflight_dependents(work)
            .map_err(|error| match error {
                crate::foreign::source_runtime::NativeOwnerAdmissionError::Work => {
                    OwnerPhaseFailure::WorkReservation
                }
                _ => OwnerPhaseFailure::Authority,
            })?;
        let returned_constructor = invocation.returned_constructor();
        let status = if matches!(
            invocation.result(),
            crate::foreign::source_contract::PreparedAbiResult::Scalar(_)
        ) {
            let prepaid = crate::foreign::source_runtime::PrepaidScalarReport::admit(
                invocation.result(),
                work,
            )
            .map_err(|error| match error {
                crate::foreign::source_runtime::NativeScalarConversionError::WorkExhausted => {
                    OwnerPhaseFailure::WorkReservation
                }
                _ => OwnerPhaseFailure::Authority,
            })?;
            Some(StatusReportStorage { prepaid })
        } else {
            None
        };
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
                retained,
                blocked,
                returned_constructor,
                status,
            },
            blocked: has_dependents,
        })
    }

    pub(super) fn ready(
        self,
        guard: NativeOwnerGuard,
        operands: Vec<NativeOwnerOperand>,
    ) -> Result<OwnerTeardownReady<'binding>, OwnerPhaseFailure> {
        if !Arc::ptr_eq(self.invocation.owner(), guard.owner()) {
            return Err(OwnerPhaseFailure::Authority);
        }
        Ok(OwnerTeardownReady {
            invocation: self.invocation,
            guard,
            operands,
            blocked: self.blocked,
            recording: self.recording,
            slots: self.slots,
        })
    }
}

impl<'binding> OwnerTeardownReady<'binding> {
    /// The unique guard holds the exact teardown sealed before acquisition.
    /// Its original void/status call records disposition and yields a non-Clone receipt.
    pub(super) fn invoke(self) -> OwnerTeardownReturned<'binding> {
        let Self {
            invocation,
            guard,
            operands,
            blocked,
            recording,
            slots,
        } = self;
        let (authority, consumed, status) = invocation.invoke(guard, &operands, blocked);
        OwnerTeardownReturned {
            authority,
            consumed,
            status,
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
            status,
            recording: PrepaidOwnerRecord,
            slots,
        } = self;
        OwnerTeardownRecorded {
            _authority: authority,
            consumed,
            status,
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
        let mut payload = Value::Unit;
        if !self.consumed.is_blocked() {
            match (self.status, self.slots.status) {
                (Some(raw), Some(report)) => {
                    if !raw.valid || !raw.readable {
                        return Err(OwnerPhaseFailure::Authority);
                    }
                    let value =
                        crate::foreign::source_runtime::widen_gnu_reply(raw.reply, report.prepaid)
                            .map_err(|_| OwnerPhaseFailure::Authority)?
                            .ok_or(OwnerPhaseFailure::Authority)?;
                    payload = Value::Integer(value);
                }
                (None, None) => {}
                _ => return Err(OwnerPhaseFailure::Authority),
            }
        }
        let constructor = if self.consumed.is_blocked() {
            self.slots.blocked
        } else if self.consumed.is_retained() {
            self.slots.retained
        } else {
            self.slots.consumed
        };
        heap[self.slots.disposition] = HeapCell::Constructor(
            constructor,
            (!self.consumed.is_blocked()).then_some(payload),
        );
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
    pub(super) fn into_parts(self) -> (Value, NativeOwnerDisposition) {
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
    prepare_conversion_refusal_cells(
        heap,
        invocation.hidden_error_constructor(),
        invocation.conversion_failed_constructor(),
        work,
    )
}

pub(super) fn prepare_conversion_refusal_cells(
    heap: &mut Vec<HeapCell>,
    hidden_error: ConstructorId,
    conversion_failed: ConstructorId,
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
    heap.push(HeapCell::Constructor(hidden_error, None));
    let report = heap.len();
    heap.push(HeapCell::Constructor(
        conversion_failed,
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
            source_runtime::narrow_gnu_scalar,
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
            Some(PreparedOwnerCall::Borrow { .. }) => {
                SourceOwnerPhase::Borrow(crate::core::source_resource::SourceResourcePhase::Handler)
            }
            Some(PreparedOwnerCall::Acquire { .. } | PreparedOwnerCall::OutputAcquire { .. }) => {
                SourceOwnerPhase::Acquire
            }
            Some(PreparedOwnerCall::Teardown { .. } | PreparedOwnerCall::StatusTeardown { .. }) => {
                SourceOwnerPhase::Finish
            }
            None => return Err(super::RuntimeFailure::ForeignBinding),
        };
        #[cfg(test)]
        if matches!(phase, SourceOwnerPhase::Borrow(_)) {
            post_record_test::block_borrow_boundary(&mut self.frames);
        }
        let expected_phase = match phase {
            SourceOwnerPhase::Acquire => Some(super::ProviderPhase::Acquire),
            SourceOwnerPhase::Finish => Some(super::ProviderPhase::Finish),
            SourceOwnerPhase::Borrow(_) => None,
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
            if expected_phase.is_some_and(|expected| boundary.phase != expected)
                || boundary.consumed
                || boundary.blocked
                || phase == SourceOwnerPhase::Acquire && boundary.owner.is_some()
            {
                return Err(super::RuntimeFailure::ForeignBinding);
            }
            let actual_phase = match boundary.phase {
                super::ProviderPhase::Acquire => {
                    crate::core::source_resource::SourceResourcePhase::Acquire
                }
                super::ProviderPhase::Body => {
                    crate::core::source_resource::SourceResourcePhase::Handler
                }
                super::ProviderPhase::Finish => {
                    crate::core::source_resource::SourceResourcePhase::Finish
                }
            };
            selected = Some((index, boundary.node, boundary.key, actual_phase));
            break;
        }
        let (index, node, key, actual_phase) =
            selected.ok_or(super::RuntimeFailure::ForeignBinding)?;
        let phase = if matches!(phase, SourceOwnerPhase::Borrow(_)) {
            SourceOwnerPhase::Borrow(actual_phase)
        } else {
            phase
        };
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
            AdmittedSourceOwnerInvocation::Borrow(invocation) => {
                let Some(PreparedOwnerCall::Borrow {
                    current_operand, ..
                }) = symbol.owner_role()
                else {
                    return Err(super::RuntimeFailure::ForeignBinding);
                };
                let source = symbol.symbol();
                let mut operands = Vec::new();
                super::charge_effect_work(
                    &mut self.instantiation_work,
                    source.operands().len(),
                    super::RuntimePhase::Access,
                )?;
                operands
                    .try_reserve_exact(source.operands().len())
                    .map_err(|_| operand_storage(source.operands().len()))?;
                let mut input_storage = Vec::new();
                super::charge_effect_work(
                    &mut self.instantiation_work,
                    source.operands().len(),
                    super::RuntimePhase::Access,
                )?;
                input_storage
                    .try_reserve_exact(source.operands().len())
                    .map_err(|_| operand_storage(source.operands().len()))?;
                for (position, operand) in source.operands().iter().enumerate() {
                    let native = match operand.source() {
                        PreparedOperandSource::Bytes { path, extent, .. } => {
                            let length = super::source_scalar_phases::source_integer_leaf(
                                &self.heap,
                                &value,
                                extent,
                                &mut self.instantiation_work,
                            )?;
                            let length = match narrow_gnu_scalar(
                                length,
                                PreparedScalarRepresentation::SizeT,
                                &mut self.instantiation_work,
                            ) {
                                Ok(NativeScalarValue::USize(length)) => Some(length),
                                Err(NativeScalarConversionError::OutOfRange) => None,
                                Err(NativeScalarConversionError::WorkExhausted) => {
                                    return Err(super::effect_work_failure(
                                        &self.instantiation_work,
                                        None,
                                        super::RuntimePhase::Access,
                                    ));
                                }
                                _ => return Err(super::RuntimeFailure::ForeignBinding),
                            };
                            let bytes = source_bytes_leaf(
                                &self.heap,
                                &value,
                                path,
                                &mut self.instantiation_work,
                            )?;
                            let Some(length) = length.filter(|length| *length <= bytes.len())
                            else {
                                self.control =
                                    Some(super::Control::Return(prepare_conversion_refusal_cells(
                                        &mut self.heap,
                                        invocation.hidden_error_constructor(),
                                        invocation.conversion_failed_constructor(),
                                        &mut self.instantiation_work,
                                    )?));
                                return Ok(());
                            };
                            let capacity = length.max(1);
                            super::charge_effect_work(
                                &mut self.instantiation_work,
                                capacity,
                                super::RuntimePhase::Access,
                            )?;
                            let mut copied = Vec::new();
                            copied
                                .try_reserve_exact(capacity)
                                .map_err(|_| operand_storage(capacity))?;
                            copied.extend_from_slice(&bytes[..length]);
                            let address = copied.as_mut_ptr().cast();
                            input_storage.push(copied);
                            NativeOwnerOperand::Address(address)
                        }
                        PreparedOperandSource::Sentinel(position) => {
                            NativeOwnerOperand::Scalar(admit_sentinel_operand(
                                symbol,
                                *position,
                                operand.representation(),
                                &mut self.instantiation_work,
                                super::RuntimePhase::Access,
                            )?)
                        }
                        PreparedOperandSource::Current(path) if position == *current_operand => {
                            if current_key(&self.heap, &value, path, &mut self.instantiation_work)?
                                != key
                            {
                                return Err(super::RuntimeFailure::ForeignBinding);
                            }
                            let super::Frame::SourceResourceBoundary(boundary) =
                                &self.frames[index]
                            else {
                                return Err(super::RuntimeFailure::InvalidControlState);
                            };
                            let owner = boundary
                                .owner
                                .as_ref()
                                .ok_or(super::RuntimeFailure::ForeignBinding)?;
                            if !Arc::ptr_eq(
                                owner.owner(),
                                symbol
                                    .owner()
                                    .ok_or(super::RuntimeFailure::ForeignBinding)?,
                            ) || actual_phase
                                == crate::core::source_resource::SourceResourcePhase::Handler
                                && !owner.ordinary_live()
                            {
                                return Err(super::RuntimeFailure::ForeignBinding);
                            }
                            NativeOwnerOperand::Address(
                                owner
                                    .completion_address()
                                    .ok_or(super::RuntimeFailure::ForeignBinding)?,
                            )
                        }
                        PreparedOperandSource::Enclosing(path) => self.enclosing_owner_operand(
                            index,
                            request,
                            &value,
                            path,
                            actual_phase
                                == crate::core::source_resource::SourceResourcePhase::Finish,
                        )?,
                        PreparedOperandSource::Constant(position) => {
                            NativeOwnerOperand::Scalar(admit_constant_operand(
                                symbol,
                                *position,
                                operand.representation(),
                                &mut self.instantiation_work,
                                super::RuntimePhase::Access,
                            )?)
                        }
                        PreparedOperandSource::Source(path) => {
                            let integer = super::source_scalar_phases::source_integer_leaf(
                                &self.heap,
                                &value,
                                path,
                                &mut self.instantiation_work,
                            )?;
                            let PreparedRepresentation::Scalar(representation) =
                                operand.representation()
                            else {
                                return Err(super::RuntimeFailure::ForeignBinding);
                            };
                            match narrow_gnu_scalar(
                                integer,
                                representation,
                                &mut self.instantiation_work,
                            ) {
                                Ok(value) => NativeOwnerOperand::Scalar(value),
                                Err(NativeScalarConversionError::OutOfRange) => {
                                    self.control = Some(super::Control::Return(
                                        prepare_conversion_refusal_cells(
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
                                        super::RuntimePhase::Access,
                                    ));
                                }
                                Err(_) => return Err(super::RuntimeFailure::ForeignBinding),
                            }
                        }
                        _ => return Err(super::RuntimeFailure::ForeignBinding),
                    };
                    operands.push(native);
                }
                let ready = OwnerBorrowReady::admit(
                    invocation,
                    operands,
                    &mut self.heap,
                    &mut self.instantiation_work,
                )
                .map_err(|error| phase_failure(error, &self.instantiation_work))?
                .with_inputs(input_storage);
                self.pending_source_owner_call = Some(SourceOwnerCallProgress::BorrowReady(ready));
            }
            AdmittedSourceOwnerInvocation::Acquire(invocation) => {
                let source = invocation.symbol().symbol();
                let initialized_bytes = match invocation.symbol().owner_role() {
                    Some(PreparedOwnerCall::Acquire {
                        initialized_bytes, ..
                    }) => initialized_bytes.as_ref(),
                    Some(PreparedOwnerCall::OutputAcquire { .. }) => None,
                    _ => return Err(super::RuntimeFailure::ForeignBinding),
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
                let mut input_storage = Vec::new();
                super::charge_effect_work(
                    &mut self.instantiation_work,
                    source.operands().len(),
                    super::RuntimePhase::Access,
                )?;
                input_storage
                    .try_reserve_exact(source.operands().len())
                    .map_err(|_| operand_storage(source.operands().len()))?;
                for operand in source.operands() {
                    if let PreparedOperandSource::Nul(path) = operand.source() {
                        let text = source_string_leaf(
                            &self.heap,
                            &value,
                            path,
                            &mut self.instantiation_work,
                        )?;
                        super::charge_effect_work(
                            &mut self.instantiation_work,
                            text.len(),
                            super::RuntimePhase::Access,
                        )?;
                        if text.as_bytes().contains(&0) {
                            self.control =
                                Some(super::Control::Return(prepare_conversion_refusal(
                                    &mut self.heap,
                                    &invocation,
                                    &mut self.instantiation_work,
                                )?));
                            return Ok(());
                        }
                        let count = text
                            .len()
                            .checked_add(1)
                            .ok_or_else(|| operand_storage(text.len()))?;
                        super::charge_effect_work(
                            &mut self.instantiation_work,
                            count,
                            super::RuntimePhase::Access,
                        )?;
                        let mut bytes = Vec::new();
                        bytes
                            .try_reserve_exact(count)
                            .map_err(|_| operand_storage(count))?;
                        bytes.extend_from_slice(text.as_bytes());
                        bytes.push(0);
                        operands.push(NativeOwnerOperand::Address(bytes.as_mut_ptr().cast()));
                        input_storage.push(bytes);
                        continue;
                    }
                    if matches!(operand.source(), PreparedOperandSource::Null) {
                        operands.push(NativeOwnerOperand::Address(std::ptr::null_mut()));
                        continue;
                    }
                    if matches!(operand.source(), PreparedOperandSource::OwnerOutput) {
                        operands.push(NativeOwnerOperand::OwnerOutput);
                        continue;
                    }
                    if matches!(operand.source(), PreparedOperandSource::OffsetOutput) {
                        operands.push(NativeOwnerOperand::OffsetOutput);
                        continue;
                    }
                    if let PreparedOperandSource::Sentinel(position) = operand.source() {
                        operands.push(NativeOwnerOperand::Scalar(admit_sentinel_operand(
                            invocation.symbol(),
                            *position,
                            operand.representation(),
                            &mut self.instantiation_work,
                            super::RuntimePhase::Access,
                        )?));
                        continue;
                    }
                    if let PreparedOperandSource::Constant(position) = operand.source() {
                        operands.push(NativeOwnerOperand::Scalar(admit_constant_operand(
                            invocation.symbol(),
                            *position,
                            operand.representation(),
                            &mut self.instantiation_work,
                            super::RuntimePhase::Access,
                        )?));
                        continue;
                    }
                    if let PreparedOperandSource::Enclosing(path) = operand.source() {
                        operands.push(
                            self.enclosing_owner_operand(index, request, &value, path, false)?,
                        );
                        continue;
                    }
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
                        Ok(operand) => operands.push(NativeOwnerOperand::Scalar(operand)),
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
                let program = self.program.clone();
                let scope = match program.node(node) {
                    Some(super::ExecutableNode::Effect(expression)) => match &expression.kind {
                        crate::core::EffectExprKind::Operation(
                            crate::core::EffectOperation::SourceResourceScope(scope),
                        ) => scope,
                        _ => return Err(super::RuntimeFailure::ForeignBinding),
                    },
                    _ => return Err(super::RuntimeFailure::ForeignBinding),
                };
                let super::Frame::SourceResourceBoundary(boundary) = &self.frames[index] else {
                    return Err(super::RuntimeFailure::InvalidControlState);
                };
                let crate::types::Type::Tuple(state_data) = scope.finish.parameter.ty() else {
                    return Err(super::RuntimeFailure::ForeignBinding);
                };
                let state = crate::types::IterativeTypeOwner::new(
                    boundary.environment.instantiation.ty(
                        state_data
                            .first()
                            .ok_or(super::RuntimeFailure::ForeignBinding)?,
                        &mut self.instantiation_work,
                    )?,
                );
                let access = crate::types::IterativeTypeOwner::new(
                    boundary
                        .environment
                        .instantiation
                        .ty(scope.handle.ty(), &mut self.instantiation_work)?,
                );
                let destruction = prepare_destruction_operands(
                    invocation.destructor(),
                    &state,
                    &boundary.dependencies,
                    &mut self.instantiation_work,
                )?;
                let super::Frame::SourceResourceBoundary(boundary) = &mut self.frames[index] else {
                    return Err(super::RuntimeFailure::InvalidControlState);
                };
                let dependencies = std::mem::take(&mut boundary.dependencies);
                let invocation = invocation.prepare_owner_authority(
                    key.0 as usize,
                    state,
                    access,
                    dependencies,
                    destruction,
                    &mut self.instantiation_work,
                )?;
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
                let ready = ready
                    .with_inputs(input_storage, &mut self.instantiation_work)
                    .map_err(|error| phase_failure(error, &self.instantiation_work))?;
                self.pending_source_owner_call = Some(SourceOwnerCallProgress::AcquireReady(ready));
            }
            AdmittedSourceOwnerInvocation::Teardown(invocation) => {
                let Some(
                    PreparedOwnerCall::Teardown {
                        current_operand, ..
                    }
                    | PreparedOwnerCall::StatusTeardown {
                        current_operand, ..
                    },
                ) = symbol.owner_role()
                else {
                    return Err(super::RuntimeFailure::ForeignBinding);
                };
                let mut operands = Vec::new();
                super::charge_effect_work(
                    &mut self.instantiation_work,
                    symbol.symbol().operands().len(),
                    super::RuntimePhase::Access,
                )?;
                operands
                    .try_reserve_exact(symbol.symbol().operands().len())
                    .map_err(|_| operand_storage(symbol.symbol().operands().len()))?;
                for (position, operand) in symbol.symbol().operands().iter().enumerate() {
                    let native = match operand.source() {
                        PreparedOperandSource::Sentinel(index) => {
                            NativeOwnerOperand::Scalar(admit_sentinel_operand(
                                symbol,
                                *index,
                                operand.representation(),
                                &mut self.instantiation_work,
                                super::RuntimePhase::Access,
                            )?)
                        }
                        PreparedOperandSource::Constant(index) => {
                            NativeOwnerOperand::Scalar(admit_constant_operand(
                                symbol,
                                *index,
                                operand.representation(),
                                &mut self.instantiation_work,
                                super::RuntimePhase::Access,
                            )?)
                        }
                        PreparedOperandSource::Current(path) if position == *current_operand => {
                            if current_key(&self.heap, &value, path, &mut self.instantiation_work)?
                                != key
                            {
                                return Err(super::RuntimeFailure::ForeignBinding);
                            }
                            let super::Frame::SourceResourceBoundary(boundary) =
                                &self.frames[index]
                            else {
                                return Err(super::RuntimeFailure::InvalidControlState);
                            };
                            NativeOwnerOperand::Address(
                                boundary
                                    .owner
                                    .as_ref()
                                    .and_then(NativeOwnerGuard::completion_address)
                                    .ok_or(super::RuntimeFailure::ForeignBinding)?,
                            )
                        }
                        PreparedOperandSource::Enclosing(path) => {
                            self.enclosing_owner_operand(index, request, &value, path, true)?
                        }
                        _ => return Err(super::RuntimeFailure::ForeignBinding),
                    };
                    operands.push(native);
                }
                let super::Frame::SourceResourceBoundary(boundary) = &self.frames[index] else {
                    return Err(super::RuntimeFailure::InvalidControlState);
                };
                let guard = boundary
                    .owner
                    .as_ref()
                    .ok_or(super::RuntimeFailure::ForeignBinding)?;
                #[cfg(test)]
                post_record_test::teardown_preflight(&mut self.instantiation_work);
                let prepared = OwnerTeardownPrepared::admit(
                    invocation,
                    guard,
                    key,
                    index,
                    &mut self.heap,
                    &mut self.instantiation_work,
                );
                #[cfg(test)]
                post_record_test::teardown_preflight_completed(&self.instantiation_work);
                let prepared =
                    prepared.map_err(|error| phase_failure(error, &self.instantiation_work))?;
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
                    .ready(guard, operands)
                    .map_err(|error| phase_failure(error, &self.instantiation_work))?;
                self.pending_source_owner_call =
                    Some(SourceOwnerCallProgress::TeardownReady(ready));
            }
        }
        Ok(())
    }

    fn enclosing_owner_operand(
        &mut self,
        boundary_index: usize,
        request: crate::core::NodeId,
        value: &Value,
        path: &[usize],
        finishing: bool,
    ) -> Result<NativeOwnerOperand, super::RuntimeFailure> {
        let key = current_key(&self.heap, value, path, &mut self.instantiation_work)?;
        let program = self.program.clone();
        let Some(super::ExecutableNode::Effect(expression)) = program.node(request) else {
            return Err(super::RuntimeFailure::ForeignBinding);
        };
        let crate::core::EffectExprKind::Operation(crate::core::EffectOperation::Request(call)) =
            &expression.kind
        else {
            return Err(super::RuntimeFailure::ForeignBinding);
        };
        let ty = match program
            .node(call.operand())
            .ok_or(super::RuntimeFailure::ForeignBinding)?
        {
            super::ExecutableNode::Effect(node) => &node.ty,
            super::ExecutableNode::Pure(node) => &node.ty,
        };
        let leaf = source_type_leaf(ty, path, &mut self.instantiation_work)?;
        let super::Frame::SourceResourceBoundary(boundary) = &self.frames[boundary_index] else {
            return Err(super::RuntimeFailure::InvalidControlState);
        };
        let leaf = crate::types::IterativeTypeOwner::new(
            boundary
                .environment
                .instantiation
                .ty(leaf, &mut self.instantiation_work)?,
        );
        let bindings = self
            .source_bindings
            .ok_or(super::RuntimeFailure::ForeignBinding)?;
        let completion = if finishing {
            boundary.owner.as_ref()
        } else {
            None
        };
        let dependency = bindings.borrowed_owner(
            key.0 as usize,
            &leaf,
            crate::foreign::source_runtime::NativeOwnerViewKind::State,
            completion,
            &mut self.instantiation_work,
        )?;
        let permitted = match boundary.owner.as_ref() {
            Some(guard) => {
                // Acquisition moved these receipts into the guard. Membership
                // does not grant ordinary access to a quarantined dependency:
                // borrowed_owner above receives completion permission only
                // during Finish.
                super::charge_effect_work(
                    &mut self.instantiation_work,
                    guard.retained_dependency_count(),
                    super::RuntimePhase::Access,
                )?;
                guard.retains(&dependency)
            }
            None if !finishing => {
                super::charge_effect_work(
                    &mut self.instantiation_work,
                    boundary.dependencies.len(),
                    super::RuntimePhase::Access,
                )?;
                boundary
                    .dependencies
                    .iter()
                    .any(|admitted| admitted.same_slot(&dependency))
            }
            None => false,
        };
        if !permitted {
            return Err(super::RuntimeFailure::ForeignBinding);
        }
        Ok(NativeOwnerOperand::Address(
            dependency
                .address()
                .ok_or(super::RuntimeFailure::ForeignBinding)?,
        ))
    }

    /// Returned transitions run before every disposal check. Postnative
    /// recording cannot fail; terminal reporting keeps the unique guard safe.
    pub(super) fn step_source_owner(&mut self) -> Result<bool, super::RuntimeFailure> {
        let Some(progress) = self.pending_source_owner_call.take() else {
            return Ok(false);
        };
        match progress {
            SourceOwnerCallProgress::BorrowReady(ready) => {
                super::disposal::check()?;
                let value = ready
                    .invoke_and_report(&mut self.heap)
                    .map_err(|error| phase_failure(error, &self.instantiation_work))?;
                self.control = Some(super::Control::Return(value));
            }
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
                boundary.consumed = !consumed.is_retained();
                boundary.blocked = consumed.is_blocked();
                boundary.owner = consumed.into_retained();
                self.control = Some(super::Control::Return(value));
            }
        }
        Ok(true)
    }
}

pub(super) fn same_instance(
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

pub(super) fn source_type_leaf<'a>(
    mut ty: &'a crate::types::Type,
    path: &[usize],
    work: &mut TypeWorkBudget,
) -> Result<&'a crate::types::Type, super::RuntimeFailure> {
    for (index, component) in path.iter().enumerate() {
        super::charge_effect_work(work, 1, super::RuntimePhase::Access)?;
        if let crate::types::Type::Tuple(fields) = ty {
            ty = fields
                .get(*component)
                .ok_or(super::RuntimeFailure::ForeignBinding)?;
        } else if index != 0 || *component != 0 {
            return Err(super::RuntimeFailure::ForeignBinding);
        }
    }
    if path.is_empty() {
        return Err(super::RuntimeFailure::ForeignBinding);
    }
    Ok(ty)
}

struct OwnerTypeReplacements(
    std::collections::HashMap<crate::types::TypeVariableId, crate::types::Type>,
    std::collections::HashMap<crate::types::TypeVariableId, crate::types::EffectRow>,
);
impl OwnerTypeReplacements {
    fn insert(&mut self, variable: crate::types::TypeVariableId, ty: crate::types::Type) {
        if let Some(previous) = self.0.insert(variable, ty) {
            crate::types::discard_type_iteratively(previous);
        }
    }
}
impl Drop for OwnerTypeReplacements {
    fn drop(&mut self) {
        for (_, ty) in self.0.drain() {
            crate::types::discard_type_iteratively(ty);
        }
    }
}

/// The original declared host destructor is not a new source effect request.
/// Its state/dependency views are specialized from this owner and initializer
/// receipts, and every operand is retained before acquisition can enter C.
fn prepare_destruction_operands(
    destructor: &crate::foreign::checked_source::CheckedForeignSymbol,
    state: &crate::types::Type,
    dependencies: &[crate::foreign::source_runtime::NativeOwnerDependency],
    work: &mut TypeWorkBudget,
) -> Result<Vec<NativeOwnerOperand>, super::RuntimeFailure> {
    use crate::foreign::source_contract::{
        PreparedOperandSource, PreparedOwnerArgument, PreparedOwnerCall,
    };
    use crate::types::IterativeTypeOwner;
    let owner = destructor
        .owner()
        .ok_or(super::RuntimeFailure::ForeignBinding)?;
    let Some(
        PreparedOwnerCall::Teardown {
            application,
            current_operand,
            ..
        }
        | PreparedOwnerCall::StatusTeardown {
            application,
            current_operand,
            ..
        },
    ) = destructor.owner_role()
    else {
        return Err(super::RuntimeFailure::ForeignBinding);
    };
    let arguments = crate::foreign::source_owner::state_arguments(
        state,
        owner.nominal(),
        owner.parameters(),
        application.span(),
        work,
    )
    .map_err(|error| {
        if error.is_resource_exhaustion() {
            super::effect_work_failure(work, None, super::RuntimePhase::Acquisition)
        } else {
            super::RuntimeFailure::ForeignBinding
        }
    })?;
    if arguments.len() != application.arguments().len() {
        return Err(super::RuntimeFailure::ForeignBinding);
    }
    let mut replacements = OwnerTypeReplacements(
        std::collections::HashMap::new(),
        std::collections::HashMap::new(),
    );
    super::charge_effect_work(work, arguments.len(), super::RuntimePhase::Acquisition)?;
    let type_count = arguments
        .iter()
        .filter(|argument| {
            matches!(
                argument,
                crate::foreign::source_owner::StateArgument::Type(_)
            )
        })
        .count();
    replacements
        .0
        .try_reserve(type_count)
        .map_err(|_| operand_storage(type_count))?;
    replacements
        .1
        .try_reserve(arguments.len() - type_count)
        .map_err(|_| operand_storage(arguments.len() - type_count))?;
    for (formal, argument) in application.arguments().iter().zip(arguments) {
        let position = match formal {
            PreparedOwnerArgument::Type(position) | PreparedOwnerArgument::EffectRow(position) => {
                *position
            }
        };
        let parameter = *destructor
            .parameter_ids()
            .get(position)
            .ok_or(super::RuntimeFailure::ForeignBinding)?;
        match (formal, argument) {
            (
                PreparedOwnerArgument::Type(_),
                crate::foreign::source_owner::StateArgument::Type(argument),
            ) => {
                let argument =
                    crate::types::clone_type_with_budget(argument, work).map_err(|()| {
                        super::effect_work_failure(work, None, super::RuntimePhase::Acquisition)
                    })?;
                replacements.insert(parameter, argument);
            }
            (
                PreparedOwnerArgument::EffectRow(_),
                crate::foreign::source_owner::StateArgument::EffectRow(argument),
            ) => {
                let argument =
                    crate::types::clone_effect_row_with_budget(argument, work).map_err(|()| {
                        super::effect_work_failure(work, None, super::RuntimePhase::Acquisition)
                    })?;
                replacements.1.insert(parameter, argument);
            }
            _ => return Err(super::RuntimeFailure::ForeignBinding),
        }
    }
    let signature = destructor
        .source_signature()
        .function_view()
        .ok_or(super::RuntimeFailure::ForeignBinding)?;
    let domain = IterativeTypeOwner::new(
        crate::types::substitute_type_and_row_variables_with(
            signature.domain(),
            &replacements.0,
            &replacements.1,
            |cells| super::charge_effect_work(work, cells, super::RuntimePhase::Acquisition),
            || operand_storage(1),
        )?
        .map_err(|_| super::RuntimeFailure::ForeignBinding)?,
    );
    let mut operands = Vec::new();
    super::charge_effect_work(
        work,
        destructor.symbol().operands().len(),
        super::RuntimePhase::Acquisition,
    )?;
    operands
        .try_reserve_exact(destructor.symbol().operands().len())
        .map_err(|_| operand_storage(destructor.symbol().operands().len()))?;
    for (position, operand) in destructor.symbol().operands().iter().enumerate() {
        let native = match operand.source() {
            PreparedOperandSource::Sentinel(index) => {
                NativeOwnerOperand::Scalar(admit_sentinel_operand(
                    destructor,
                    *index,
                    operand.representation(),
                    work,
                    super::RuntimePhase::Acquisition,
                )?)
            }
            PreparedOperandSource::Constant(index) => {
                NativeOwnerOperand::Scalar(admit_constant_operand(
                    destructor,
                    *index,
                    operand.representation(),
                    work,
                    super::RuntimePhase::Acquisition,
                )?)
            }
            PreparedOperandSource::Current(_) if position == *current_operand => {
                NativeOwnerOperand::Address(std::ptr::null_mut())
            }
            PreparedOperandSource::Enclosing(path) => {
                let ty = source_type_leaf(&domain, path, work)?;
                let mut selected = None;
                super::charge_effect_work(
                    work,
                    dependencies.len(),
                    super::RuntimePhase::Acquisition,
                )?;
                for dependency in dependencies {
                    let state = dependency.state(work).map_err(|error| {
                        crate::foreign::source_bindings::owner_admission_failure(error, work)
                    })?;
                    if crate::types::same_type_with_budget(ty, &state, work).map_err(|()| {
                        super::effect_work_failure(work, None, super::RuntimePhase::Acquisition)
                    })? {
                        if selected.is_some_and(
                            |previous: &crate::foreign::source_runtime::NativeOwnerDependency| {
                                !previous.same_slot(dependency)
                            },
                        ) {
                            return Err(super::RuntimeFailure::ForeignBinding);
                        }
                        selected = Some(dependency);
                    }
                }
                NativeOwnerOperand::Address(
                    selected
                        .and_then(|dependency| dependency.address())
                        .ok_or(super::RuntimeFailure::ForeignBinding)?,
                )
            }
            _ => return Err(super::RuntimeFailure::ForeignBinding),
        };
        operands.push(native);
    }
    Ok(operands)
}

fn admit_sentinel_operand(
    symbol: &crate::foreign::checked_source::CheckedForeignSymbol,
    index: usize,
    representation: crate::foreign::source_contract::PreparedRepresentation,
    work: &mut TypeWorkBudget,
    phase: super::RuntimePhase,
) -> Result<NativeScalarValue, super::RuntimeFailure> {
    if representation
        != crate::foreign::source_contract::PreparedRepresentation::FunctionAddressSentinel
    {
        return Err(super::RuntimeFailure::ForeignBinding);
    }
    crate::foreign::source_runtime::admit_gnu_declared_sentinel(symbol.prepared(), index, work)
        .map_err(|error| match error {
            NativeScalarConversionError::WorkExhausted => {
                super::effect_work_failure(work, None, phase)
            }
            _ => super::RuntimeFailure::ForeignBinding,
        })
}

pub(super) fn admit_constant_operand(
    symbol: &crate::foreign::checked_source::CheckedForeignSymbol,
    index: usize,
    representation: crate::foreign::source_contract::PreparedRepresentation,
    work: &mut TypeWorkBudget,
    phase: super::RuntimePhase,
) -> Result<NativeScalarValue, super::RuntimeFailure> {
    let crate::foreign::source_contract::PreparedRepresentation::Scalar(representation) =
        representation
    else {
        return Err(super::RuntimeFailure::ForeignBinding);
    };
    crate::foreign::source_runtime::narrow_gnu_declared_constant(
        symbol.prepared(),
        index,
        representation,
        work,
    )
    .map_err(|error| match error {
        NativeScalarConversionError::WorkExhausted => super::effect_work_failure(work, None, phase),
        _ => super::RuntimeFailure::ForeignBinding,
    })
}

fn source_string_leaf<'value>(
    heap: &'value [HeapCell],
    mut value: &'value Value,
    path: &[usize],
    work: &mut TypeWorkBudget,
) -> Result<&'value str, super::RuntimeFailure> {
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
        Value::String(text) => Ok(text),
        _ => Err(super::RuntimeFailure::ForeignBinding),
    }
}

fn source_bytes_leaf<'value>(
    heap: &'value [HeapCell],
    mut value: &'value Value,
    path: &[usize],
    work: &mut TypeWorkBudget,
) -> Result<&'value [u8], super::RuntimeFailure> {
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
        Value::String(text) => Ok(text.as_bytes()),
        value => value.bytes().ok_or(super::RuntimeFailure::ForeignBinding),
    }
}

pub(super) fn current_key<'value>(
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
    pub(crate) struct BlockedBorrowObservation {
        pub(crate) marked: usize,
        pub(crate) completion_address_retained: bool,
        pub(crate) ordinary_live: bool,
    }
    thread_local! {
        static BLOCK_BORROW: Cell<Option<BlockedBorrowObservation>> = const { Cell::new(None) };
    }
    pub(crate) fn observe_blocked_borrow<T>(
        run: impl FnOnce() -> T,
    ) -> (T, BlockedBorrowObservation) {
        assert!(
            BLOCK_BORROW
                .replace(Some(BlockedBorrowObservation::default()))
                .is_none()
        );
        struct Reset;
        impl Drop for Reset {
            fn drop(&mut self) {
                BLOCK_BORROW.set(None);
            }
        }
        let reset = Reset;
        let result = run();
        let observed = BLOCK_BORROW.get().unwrap();
        drop(reset);
        (result, observed)
    }
    pub(super) fn block_borrow_boundary(frames: &mut [super::super::Frame]) {
        let Some(mut observed) = BLOCK_BORROW.get() else {
            return;
        };
        if observed.marked != 0 {
            return;
        }
        for frame in frames.iter_mut().rev() {
            let super::super::Frame::SourceResourceBoundary(boundary) = frame else {
                continue;
            };
            if boundary.phase != super::super::ProviderPhase::Finish {
                continue;
            }
            let Some(owner) = &mut boundary.owner else {
                continue;
            };
            // Inject only private runtime state after fresh program/binding
            // admission. No valid source is granted a blocked-owner operation.
            boundary.blocked = true;
            owner.quarantine();
            observed.marked = 1;
            observed.completion_address_retained = owner.completion_address().is_some();
            observed.ordinary_live = owner.ordinary_live();
            BLOCK_BORROW.set(Some(observed));
            break;
        }
    }

    #[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
    pub(crate) struct Observation {
        pub(crate) returned: usize,
        pub(crate) recorded: usize,
        pub(crate) reported: usize,
        pub(crate) recorded_with_zero_shared_work: bool,
        pub(crate) recorded_live_owner: bool,
        pub(crate) initialized_bytes: Option<usize>,
        pub(crate) initialized_admission_used: Option<usize>,
        pub(crate) report_slot_published: bool,
        pub(crate) teardown_returned: usize,
        pub(crate) teardown_recorded: usize,
        pub(crate) teardown_reported: usize,
        pub(crate) teardown_recorded_with_zero_shared_work: bool,
        pub(crate) teardown_consumed_report_published: bool,
        pub(crate) teardown_preflight_used: Option<usize>,
        pub(crate) teardown_recorded_retained: bool,
        pub(crate) teardown_failed_without_report: bool,
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
        TeardownExtraction,
        InitializedExtentPreflight,
        InitializedBytesAdmission { prefix: usize, allowance: usize },
        TeardownPreflight { prefix: usize, allowance: usize },
    }

    pub(crate) fn observe<T>(inject: bool, run: impl FnOnce() -> T) -> (T, Observation) {
        observe_phase(inject, Phase::AcquireReturn, run)
    }

    pub(crate) fn observe_teardown<T>(inject: bool, run: impl FnOnce() -> T) -> (T, Observation) {
        observe_phase(inject, Phase::TeardownReturn, run)
    }

    pub(crate) fn observe_teardown_extraction<T>(run: impl FnOnce() -> T) -> (T, Observation) {
        observe_phase(true, Phase::TeardownExtraction, run)
    }

    pub(crate) fn observe_teardown_preflight<T>(
        prefix: usize,
        allowance: usize,
        run: impl FnOnce() -> T,
    ) -> (T, Observation) {
        observe_phase(true, Phase::TeardownPreflight { prefix, allowance }, run)
    }
    pub(super) fn teardown_preflight(work: &mut TypeWorkBudget) {
        if let Some(State {
            phase: Phase::TeardownPreflight { prefix, allowance },
            ..
        }) = STATE.get()
        {
            *work = TypeWorkBudget::with_limit(prefix + allowance);
            work.charge(prefix).unwrap();
        }
    }
    pub(super) fn teardown_preflight_completed(work: &TypeWorkBudget) {
        if let Some(mut state) = STATE.get()
            && matches!(state.phase, Phase::TeardownPreflight { .. })
        {
            state.observation.teardown_preflight_used = Some(work.used());
            STATE.set(Some(state));
        }
    }

    pub(crate) fn observe_extent_preflight<T>(run: impl FnOnce() -> T) -> (T, Observation) {
        observe_phase(true, Phase::InitializedExtentPreflight, run)
    }

    pub(crate) fn observe_initialized_bytes_admission<T>(
        prefix: usize,
        allowance: usize,
        run: impl FnOnce() -> T,
    ) -> (T, Observation) {
        observe_phase(
            true,
            Phase::InitializedBytesAdmission { prefix, allowance },
            run,
        )
    }

    pub(super) fn initialized_bytes_admission_begin(
        work: &mut TypeWorkBudget,
    ) -> Option<TypeWorkBudget> {
        let State {
            phase: Phase::InitializedBytesAdmission { prefix, allowance },
            ..
        } = STATE.get()?
        else {
            return None;
        };
        let original = work.clone();
        *work = TypeWorkBudget::with_limit(prefix + allowance);
        work.charge(prefix).unwrap();
        Some(original)
    }

    pub(super) fn initialized_bytes_admission_end(
        work: &mut TypeWorkBudget,
        original: Option<TypeWorkBudget>,
    ) {
        if let Some(mut original) = original {
            let mut state = STATE.get().unwrap();
            let Phase::InitializedBytesAdmission { prefix, .. } = state.phase else {
                unreachable!();
            };
            state.observation.initialized_admission_used = Some(work.used());
            STATE.set(Some(state));
            // Isolate this admission boundary, then retain its actual charge
            // under the original unchanged limit for the source continuation.
            original.charge(work.used() - prefix).unwrap();
            *work = original;
        }
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
        mut returned: OwnerTeardownReturned<'binding>,
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
            if state.inject && state.phase == Phase::TeardownExtraction {
                // The original scalar selected and recorded disposition before
                // this injection. A generated typed scalar cannot return Void.
                returned.status.as_mut().unwrap().reply =
                    crate::foreign::source_runtime::NativeScalarReply::Void;
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
            state.observation.teardown_recorded_retained = recorded.consumed.is_retained();
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
                    Some(HeapCell::Constructor(actual, Some(Value::Unit | Value::Integer(_)))) if *actual == consumed
                );
            } else {
                let (returned, disposition, _) = state.teardown_slots.unwrap();
                state.observation.teardown_failed_without_report =
                    empty_slots(heap, disposition, 2)
                        && matches!(heap.get(returned), Some(HeapCell::Uninitialized));
            }
            STATE.set(Some(state));
        }
    }
}
