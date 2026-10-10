//! Scalar transport between generated typed native calls and the common runtime.
//!
//! These values carry no source-operation or ownership authority. Invocation
//! admission must separately authenticate the original checked contract and
//! its complete arguments before constructing a native operand vector.

use std::{error::Error, fmt};

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
