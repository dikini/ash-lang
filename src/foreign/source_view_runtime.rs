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
    read: Option<NativeViewReadCallback>,
    #[cfg(test)]
    checked: Option<(super::owner::NativeOwnerBoundary, Option<crate::foreign::checked_leaf_transport::ViewDescriptor>)>,
}
impl fmt::Debug for NativeViewReturned {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("NativeViewReturned")
            .field("nonnull", &!self.is_null())
            .finish_non_exhaustive()
    }
}
impl NativeViewReturned {
    #[cfg(test)]
    pub(in crate::foreign) fn checked(
        boundary: super::owner::NativeOwnerBoundary,
        descriptor: Option<crate::foreign::checked_leaf_transport::ViewDescriptor>,
    ) -> Self { Self { address: None, read: None, checked: Some((boundary, descriptor)) } }
    #[cfg(test)]
    pub(crate) fn is_checked_leaf(&self) -> bool {
        self.checked.is_some()
    }
    #[cfg(test)]
    pub(in crate::foreign) fn checked_descriptor(&self) -> Option<(&super::owner::NativeOwnerBoundary, &crate::foreign::checked_leaf_transport::ViewDescriptor)> {
        self.checked.as_ref().and_then(|(owner, descriptor)| descriptor.as_ref().map(|descriptor| (owner, descriptor)))
    }

    /// Generated glue supplies the exact raw return and its isolated typed read.
    /// Creating this passive value does not admit an invocation or any memory read.
    #[doc(hidden)]
    pub fn new(address: *mut core::ffi::c_void, read: NativeViewReadCallback) -> Self {
        Self {
            address: NonNull::new(address),
            read: Some(read),
            #[cfg(test)]
            checked: None,
        }
    }
    pub(crate) fn is_null(&self) -> bool {
        #[cfg(test)]
        if let Some((_, descriptor)) = &self.checked { return descriptor.is_none(); }
        self.address.is_none()
    }
    /// The caller must already own the exact live-window read ticket and have
    /// prepaid the complete bounded copy. This transport supplies no such proof.
    pub(crate) fn read(&self, index: usize) -> u8 {
        (self.read.expect("opaque checked view refuses raw reads"))(self.address.expect("admitted nonnull view").as_ptr(), index)
    }
}

#[doc(hidden)]
pub type NativeViewCallback =
    fn(&[super::NativeOwnerOperand]) -> Result<NativeViewReturned, super::NativeScalarCallError>;
