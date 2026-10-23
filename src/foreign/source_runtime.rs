//! Scalar transport between generated typed native calls and the common runtime.
//!
//! These values carry no source-operation or ownership authority. Invocation
//! admission must separately authenticate the original checked contract and
//! its complete arguments before constructing a native operand vector.

use std::{error::Error, fmt};

// Crate-private observation data only. The control module and all witness
// constructors remain private; these names grant no activation or native entry.
pub(crate) use super::checked_control::{
    Completion as CheckedCompletion, K as CheckedLocalCompletion,
    Native as CheckedNativeFact, SyntheticFinishWitness,
};

#[path = "source_owner_runtime.rs"]
mod owner;
#[path = "source_view_runtime.rs"]
mod view;
#[doc(hidden)]
pub use view::{NativeViewCallback, NativeViewReadCallback, NativeViewReturned};

pub(crate) use owner::{
    NativeByteAccess, NativeByteCallbacks, NativeOwnerAdmissionError, NativeOwnerBorrowRecord,
    NativeOwnerBoundary, NativeOwnerCopyRecord, NativeOwnerDependency, NativeOwnerDestruction,
    NativeOwnerDisposition, NativeOwnerGuard, NativeOwnerStatus, NativeOwnerStorage,
    NativeOwnerViewKind,
};
#[doc(hidden)]
pub use owner::{
    NativeByteReadCallback, NativeByteWriteCallback, NativeOwnerAcquireCallback,
    NativeOwnerCallReturned, NativeOwnerGuardReady, NativeOwnerOperand,
    NativeOwnerStatusTeardownCallback, NativeOwnerTeardownCallback,
};

use crate::{
    foreign::source_contract::{PreparedAbiResult, PreparedScalarRepresentation},
    integer::Integer,
    types::TypeWorkBudget,
};

/// One admitted native input. Fixed sentinel tokens carry no ordinary value.
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
    /// Non-callable all-one function-address bits, only for a checked fixed operand.
    FunctionAddressAllBitsOne,
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

/// Admit the fixed non-callable literal without creating an Int or pointer value.
pub(crate) fn admit_gnu_declared_sentinel(
    library: &crate::foreign::source_contract::PreparedForeignLibrary,
    index: usize,
    work: &mut TypeWorkBudget,
) -> Result<NativeScalarValue, NativeScalarConversionError> {
    charge_scalar_conversion(work, 1)?;
    require_gnu_scalar_host()?;
    let sentinel = library
        .sentinels()
        .get(index)
        .ok_or(NativeScalarConversionError::InvalidRepresentation)?;
    if library
        .representations()
        .get(sentinel.representation_index())
        .is_none_or(|value| {
            value.representation()
                != crate::foreign::source_contract::PreparedRepresentation::FunctionAddressSentinel
        })
    {
        return Err(NativeScalarConversionError::InvalidRepresentation);
    }
    Ok(NativeScalarValue::FunctionAddressAllBitsOne)
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

/// Selects only the original descriptor's already checked scalar literal.
/// Range, tags and finite magnitude work are still admitted before C.
pub(crate) fn narrow_gnu_declared_constant(
    library: &super::source_contract::PreparedForeignLibrary,
    index: usize,
    representation: PreparedScalarRepresentation,
    work: &mut TypeWorkBudget,
) -> Result<NativeScalarValue, NativeScalarConversionError> {
    charge_scalar_conversion(work, 1)?;
    require_gnu_scalar_host()?;
    let constant = library
        .constants()
        .get(index)
        .filter(|constant| constant.representation() == representation)
        .ok_or(NativeScalarConversionError::InvalidRepresentation)?;
    let integer = constant
        .value()
        .checked_integer()
        .ok_or(NativeScalarConversionError::InvalidRepresentation)?;
    narrow_gnu_scalar(&integer, representation, work)
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

pub(crate) use super::checked_control::BoundaryLimits as CheckedOwnerLimits;

#[cfg(test)]
pub(crate) use super::checked_control::Continuation as CheckedOwnerContinuation;

#[cfg(test)]
mod declared_constant_tests {
    use super::*;
    use crate::{
        foreign::source_contract::prepare_foreign_library,
        lexer::lex,
        module::ModuleId,
        parser::{parse, project_module},
        source::SourceFile,
    };

    #[test]
    fn declared_constant_narrowing_has_atomic_exact_short_prefix_and_fresh_retry() {
        let source = SourceFile::new("constant-work", "foreign library Limits {\n    profile \"x86_64-unknown-linux-gnu\"\n    repr I8 = signed(8)\n    const Value : I8 = -7\n}\n").unwrap();
        let tree = parse(lex(&source).unwrap());
        let surface = project_module(&source, &tree).unwrap();
        let library =
            prepare_foreign_library(ModuleId::new(0), &surface.foreign_libraries[0]).unwrap();
        let mut work = TypeWorkBudget::default();
        assert_eq!(
            narrow_gnu_declared_constant(
                &library,
                0,
                PreparedScalarRepresentation::Signed(8),
                &mut work
            ),
            Ok(NativeScalarValue::I8(-7))
        );
        assert_eq!(work.used(), 3); // member lookup, host/tag preflight, one magnitude byte.
        for prefix in [0, 5] {
            let mut short = TypeWorkBudget::with_limit(prefix + 2);
            short.charge(prefix).unwrap();
            assert_eq!(
                narrow_gnu_declared_constant(
                    &library,
                    0,
                    PreparedScalarRepresentation::Signed(8),
                    &mut short
                ),
                Err(NativeScalarConversionError::WorkExhausted)
            );
            assert_eq!(short.used(), prefix + 2);
            for _ in 0..2 {
                let mut exact = TypeWorkBudget::with_limit(prefix + 3);
                exact.charge(prefix).unwrap();
                assert_eq!(
                    narrow_gnu_declared_constant(
                        &library,
                        0,
                        PreparedScalarRepresentation::Signed(8),
                        &mut exact
                    ),
                    Ok(NativeScalarValue::I8(-7))
                );
                assert_eq!(exact.used(), prefix + 3);
            }
        }
        for (index, representation) in [
            (1, PreparedScalarRepresentation::Signed(8)),
            (0, PreparedScalarRepresentation::Unsigned(8)),
        ] {
            let mut work = TypeWorkBudget::default();
            assert_eq!(
                narrow_gnu_declared_constant(&library, index, representation, &mut work),
                Err(NativeScalarConversionError::InvalidRepresentation)
            );
            assert_eq!(work.used(), 1);
        }
    }

    #[test]
    fn sentinel_transport_is_fixed_noncallable_and_preadmitted_with_atomic_budget() {
        let source = SourceFile::new("sentinel-work", "foreign library Fixed {\n    profile \"x86_64-unknown-linux-gnu\"\n    repr Destructor = function_address\n    sentinel Transient : Destructor = all_bits_one\n}\n").unwrap();
        let tree = parse(lex(&source).unwrap());
        let surface = project_module(&source, &tree).unwrap();
        let library =
            prepare_foreign_library(ModuleId::new(0), &surface.foreign_libraries[0]).unwrap();
        for prefix in [0, 5] {
            let mut short = TypeWorkBudget::with_limit(prefix);
            short.charge(prefix).unwrap();
            assert_eq!(
                admit_gnu_declared_sentinel(&library, 0, &mut short),
                Err(NativeScalarConversionError::WorkExhausted)
            );
            assert_eq!(short.used(), prefix);
            for _ in 0..2 {
                let mut exact = TypeWorkBudget::with_limit(prefix + 1);
                exact.charge(prefix).unwrap();
                assert_eq!(
                    admit_gnu_declared_sentinel(&library, 0, &mut exact),
                    Ok(NativeScalarValue::FunctionAddressAllBitsOne)
                );
                assert_eq!(exact.used(), prefix + 1);
            }
        }
        let mut work = TypeWorkBudget::default();
        assert_eq!(
            admit_gnu_declared_sentinel(&library, 1, &mut work),
            Err(NativeScalarConversionError::InvalidRepresentation)
        );
        let prepaid = PrepaidScalarReport::admit(
            PreparedAbiResult::Scalar(PreparedScalarRepresentation::Unsigned(64)),
            &mut work,
        )
        .unwrap();
        assert!(
            widen_gnu_reply(
                NativeScalarReply::Scalar(NativeScalarValue::FunctionAddressAllBitsOne),
                prepaid
            )
            .is_err()
        );
    }
}
