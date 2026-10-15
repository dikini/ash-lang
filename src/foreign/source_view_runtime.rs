//! Nonowning typed pointer results from generated native view queries.
//!
//! This passive transport carries no source, window, guard or read permission.
//! Only the exact admitted lexical-window request may retain it, and every read
//! additionally requires that window's selected live owner and prepaid bound.

use std::{fmt, ptr::NonNull};

/// A generated synchronous byte observation. No address enters an Ash value.
#[doc(hidden)]
pub type NativeViewReadCallback = fn(*mut core::ffi::c_void, usize) -> u8;

/// Bare native pointer result, separate from scalar and owning acquisition replies.
#[doc(hidden)]
pub struct NativeViewReturned {
    address: Option<NonNull<core::ffi::c_void>>,
    read: NativeViewReadCallback,
}
impl fmt::Debug for NativeViewReturned {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("NativeViewReturned")
            .field("nonnull", &self.address.is_some())
            .finish_non_exhaustive()
    }
}
impl NativeViewReturned {
    /// Generated glue supplies the exact raw return and its isolated typed read.
    /// Creating this passive value does not admit an invocation or any memory read.
    #[doc(hidden)]
    pub fn new(address: *mut core::ffi::c_void, read: NativeViewReadCallback) -> Self {
        Self {
            address: NonNull::new(address),
            read,
        }
    }
    pub(crate) fn is_null(&self) -> bool {
        self.address.is_none()
    }
    /// The caller must already own the exact live-window read ticket and have
    /// prepaid the complete bounded copy. This transport supplies no such proof.
    pub(crate) fn read(&self, index: usize) -> u8 {
        (self.read)(self.address.expect("admitted nonnull view").as_ptr(), index)
    }
}

#[doc(hidden)]
pub type NativeViewCallback =
    fn(&[super::NativeOwnerOperand]) -> Result<NativeViewReturned, super::NativeScalarCallError>;
