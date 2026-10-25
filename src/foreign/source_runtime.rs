//! Raw data-pointer transport for generated typed calls. No ownership policy.
use std::{error::Error, fmt};

/// One C data-pointer argument. The caller separately retains any managed backing.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct NativeArgument(pub *mut core::ffi::c_void);
/// The direct C result, with no implicit conversion or policy wrapper.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum NativeReply {
    Address(*mut core::ffi::c_void),
    Void,
}
/// The generated callback was supplied an incompatible argument vector.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct NativeCallError;
impl fmt::Display for NativeCallError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("native callback argument mismatch")
    }
}
impl Error for NativeCallError {}
/// Typed callbacks are emitted by the native host builder.
pub type NativeCallback = fn(&[NativeArgument]) -> Result<NativeReply, NativeCallError>;
pub(crate) use super::source_bindings::admit_source_native_program;
pub use super::source_bindings::{AdmittedSourceNativeProgram, SourceNativeBindings};
