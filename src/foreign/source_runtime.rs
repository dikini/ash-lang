//! Scalar transport between generated typed native calls and the common runtime.
//!
//! These values carry no source-operation or ownership authority. Invocation
//! admission must separately authenticate the original checked contract and
//! its complete arguments before constructing a native operand vector.

use std::{error::Error, fmt};

#[path = "source_owner_runtime.rs"]
mod owner;

pub(crate) use owner::{
    NativeByteAccess, NativeByteCallbacks, NativeOwnerAdmissionError, NativeOwnerDependency,
    NativeOwnerDisposition, NativeOwnerGuard, NativeOwnerStorage, NativeOwnerViewKind,
};
#[doc(hidden)]
pub use owner::{
    NativeByteReadCallback, NativeByteWriteCallback, NativeOwnerAcquireCallback,
    NativeOwnerCallReturned, NativeOwnerGuardReady, NativeOwnerOperand,
    NativeOwnerTeardownCallback,
};

use crate::{
    foreign::source_contract::{PreparedAbiResult, PreparedScalarRepresentation},
    integer::Integer,
    types::TypeWorkBudget,
};

/// One already narrowed native scalar in the admitted ABI profile.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum NativeScalarValue {
    /// Signed 8-bit scalar.
    I8(i8),
    /// Unsigned 8-bit scalar.
    U8(u8),
    /// Signed 32-bit scalar.
    I32(i32),
    /// Unsigned 32-bit scalar.
    U32(u32),
    /// Signed 64-bit scalar.
    I64(i64),
    /// Unsigned 64-bit scalar.
    U64(u64),
    /// The bounded profile's native size_t.
    USize(usize),
}

/// The direct native reply before common Ash reporting.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum NativeScalarReply {
    /// A void call returned without reading a native result.
    Void,
    /// A scalar result is ready for exact widening.
    Scalar(NativeScalarValue),
}

/// Refusal by a generated wrapper before its typed native call.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum NativeScalarCallError {
    /// The native operand count or scalar tags disagree with its admitted plan.
    ArgumentContract,
}

impl fmt::Display for NativeScalarCallError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str("generated native call operand contract disagrees")
    }
}

impl Error for NativeScalarCallError {}

/// A conversion boundary refuses mathematical range errors separately from
/// terminal binding/profile/work failures. This grants no execution authority.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum NativeScalarConversionError {
    OutOfRange,
    InvalidRepresentation,
    UnsupportedHost,
    WorkExhausted,
}

fn charge_scalar_conversion(
    work: &mut TypeWorkBudget,
    units: usize,
) -> Result<(), NativeScalarConversionError> {
    work.charge(units)
        .map_err(|()| NativeScalarConversionError::WorkExhausted)
}

fn require_gnu_scalar_host() -> Result<(), NativeScalarConversionError> {
    if cfg!(all(
        target_arch = "x86_64",
        target_os = "linux",
        target_env = "gnu",
        target_pointer_width = "64"
    )) {
        Ok(())
    } else {
        Err(NativeScalarConversionError::UnsupportedHost)
    }
}

/// Borrows a mathematical Int and narrows it for the admitted GNU64 profile.
///
/// The caller has already authenticated the original contract, complete effect
/// arguments and bridge. This helper neither invokes native code nor creates a
/// Call report. Only OutOfRange may become pre-call ConversionFailed; all other
/// errors are terminal. Magnitude work is paid before any integer conversion.
pub(crate) fn narrow_gnu_scalar(
    value: &Integer,
    representation: PreparedScalarRepresentation,
    work: &mut TypeWorkBudget,
) -> Result<NativeScalarValue, NativeScalarConversionError> {
    charge_scalar_conversion(work, 1)?;
    require_gnu_scalar_host()?;
    if !matches!(
        representation,
        PreparedScalarRepresentation::Signed(8 | 32 | 64)
            | PreparedScalarRepresentation::Unsigned(8 | 32 | 64)
            | PreparedScalarRepresentation::SizeT
    ) {
        return Err(NativeScalarConversionError::InvalidRepresentation);
    }
    let bytes = usize::try_from(value.magnitude_byte_length())
        .map_err(|_| NativeScalarConversionError::WorkExhausted)?;
    charge_scalar_conversion(work, bytes.max(1))?;
    let narrowed = match representation {
        PreparedScalarRepresentation::Signed(8) => value
            .to_i64()
            .and_then(|integer| i8::try_from(integer).ok())
            .map(NativeScalarValue::I8),
        PreparedScalarRepresentation::Unsigned(8) => value
            .to_u64()
            .and_then(|integer| u8::try_from(integer).ok())
            .map(NativeScalarValue::U8),
        PreparedScalarRepresentation::Signed(32) => value
            .to_i64()
            .and_then(|integer| i32::try_from(integer).ok())
            .map(NativeScalarValue::I32),
        PreparedScalarRepresentation::Unsigned(32) => value
            .to_u64()
            .and_then(|integer| u32::try_from(integer).ok())
            .map(NativeScalarValue::U32),
        PreparedScalarRepresentation::Signed(64) => value.to_i64().map(NativeScalarValue::I64),
        PreparedScalarRepresentation::Unsigned(64) => value.to_u64().map(NativeScalarValue::U64),
        PreparedScalarRepresentation::SizeT => value
            .to_u64()
            .and_then(|integer| usize::try_from(integer).ok())
            .map(NativeScalarValue::USize),
        _ => return Err(NativeScalarConversionError::InvalidRepresentation),
    };
    narrowed.ok_or(NativeScalarConversionError::OutOfRange)
}

fn charge_reply_magnitude(
    magnitude: u64,
    work: &mut TypeWorkBudget,
) -> Result<(), NativeScalarConversionError> {
    let bytes = usize::try_from((u64::BITS - magnitude.leading_zeros()).div_ceil(8))
        .map_err(|_| NativeScalarConversionError::WorkExhausted)?;
    charge_scalar_conversion(work, bytes.max(1))
}

fn widen_signed_reply(
    value: i64,
    work: &mut TypeWorkBudget,
) -> Result<Option<Integer>, NativeScalarConversionError> {
    charge_reply_magnitude(value.unsigned_abs(), work)?;
    Ok(Some(Integer::from_i64(value)))
}

fn widen_unsigned_reply(
    value: u64,
    work: &mut TypeWorkBudget,
) -> Result<Option<Integer>, NativeScalarConversionError> {
    charge_reply_magnitude(value, work)?;
    Ok(Some(Integer::from_u64(value)))
}

/// The report work admitted before invocation. Private fields and absence of
/// Clone prevent callers from replacing or replaying its prepaid allowance.
/// This is work evidence only, not symbol, bridge or heap-storage authority.
#[derive(Debug)]
pub(crate) struct PrepaidScalarReport {
    expected: PreparedAbiResult,
    allowance: TypeWorkBudget,
}

impl PrepaidScalarReport {
    /// Pays the caller ledger once, before it can enter CallReady. Each bound
    /// includes one reply-tag check plus the largest admitted magnitude. Unused
    /// allowance is not refunded or transferable to another native call.
    pub(crate) fn admit(
        expected: PreparedAbiResult,
        caller_work: &mut TypeWorkBudget,
    ) -> Result<Self, NativeScalarConversionError> {
        require_gnu_scalar_host()?;
        let units = match expected {
            PreparedAbiResult::Void => 1,
            PreparedAbiResult::Scalar(PreparedScalarRepresentation::Signed(8))
            | PreparedAbiResult::Scalar(PreparedScalarRepresentation::Unsigned(8)) => 2,
            PreparedAbiResult::Scalar(PreparedScalarRepresentation::Signed(32))
            | PreparedAbiResult::Scalar(PreparedScalarRepresentation::Unsigned(32)) => 5,
            PreparedAbiResult::Scalar(PreparedScalarRepresentation::Signed(64))
            | PreparedAbiResult::Scalar(PreparedScalarRepresentation::Unsigned(64))
            | PreparedAbiResult::Scalar(PreparedScalarRepresentation::SizeT) => 9,
            _ => return Err(NativeScalarConversionError::InvalidRepresentation),
        };
        charge_scalar_conversion(caller_work, units)?;
        Ok(Self {
            expected,
            allowance: TypeWorkBudget::with_limit(units),
        })
    }
}

/// Consumes the prepaid report token and widens exactly after CallRecorded.
///
/// None denotes the token's admitted void result; the report caller supplies
/// Unit. A scalar result is always an Integer, with no signed cast or host-width
/// loss. Reply-tag disagreement is terminal and cannot replay the native call.
/// The helper has no access to the caller ledger and cannot double-charge it.
///
/// Readiness separately prepays recording and reserves constructor heap/storage.
/// Integer construction follows the existing mathematical Integer storage model
/// after recording; this helper does not make the BigInt allocator fallible.
pub(crate) fn widen_gnu_reply(
    reply: NativeScalarReply,
    report: PrepaidScalarReport,
) -> Result<Option<Integer>, NativeScalarConversionError> {
    let PrepaidScalarReport {
        expected,
        mut allowance,
    } = report;
    let report_work = &mut allowance;
    charge_scalar_conversion(report_work, 1)?;
    match (expected, reply) {
        (PreparedAbiResult::Void, NativeScalarReply::Void) => Ok(None),
        (
            PreparedAbiResult::Scalar(PreparedScalarRepresentation::Signed(8)),
            NativeScalarReply::Scalar(NativeScalarValue::I8(value)),
        ) => widen_signed_reply(i64::from(value), report_work),
        (
            PreparedAbiResult::Scalar(PreparedScalarRepresentation::Unsigned(8)),
            NativeScalarReply::Scalar(NativeScalarValue::U8(value)),
        ) => widen_unsigned_reply(u64::from(value), report_work),
        (
            PreparedAbiResult::Scalar(PreparedScalarRepresentation::Signed(32)),
            NativeScalarReply::Scalar(NativeScalarValue::I32(value)),
        ) => widen_signed_reply(i64::from(value), report_work),
        (
            PreparedAbiResult::Scalar(PreparedScalarRepresentation::Unsigned(32)),
            NativeScalarReply::Scalar(NativeScalarValue::U32(value)),
        ) => widen_unsigned_reply(u64::from(value), report_work),
        (
            PreparedAbiResult::Scalar(PreparedScalarRepresentation::Signed(64)),
            NativeScalarReply::Scalar(NativeScalarValue::I64(value)),
        ) => widen_signed_reply(value, report_work),
        (
            PreparedAbiResult::Scalar(PreparedScalarRepresentation::Unsigned(64)),
            NativeScalarReply::Scalar(NativeScalarValue::U64(value)),
        ) => widen_unsigned_reply(value, report_work),
        (
            PreparedAbiResult::Scalar(PreparedScalarRepresentation::SizeT),
            NativeScalarReply::Scalar(NativeScalarValue::USize(value)),
        ) => widen_unsigned_reply(
            u64::try_from(value).map_err(|_| NativeScalarConversionError::InvalidRepresentation)?,
            report_work,
        ),
        _ => Err(NativeScalarConversionError::InvalidRepresentation),
    }
}

pub(crate) use super::source_bindings::admit_source_native_program;
pub use super::source_bindings::{AdmittedSourceNativeProgram, SourceNativeBindings};
