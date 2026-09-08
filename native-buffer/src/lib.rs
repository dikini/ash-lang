//! Owns one bounded byte buffer allocated through the supported host C runtime.

#[cfg(not(all(
    target_os = "linux",
    any(target_arch = "x86_64", target_arch = "aarch64")
)))]
compile_error!("ash-native-buffer supports only Linux x86-64 and ARM64 targets");

use std::{ffi::c_void, ptr::NonNull};

#[link(name = "c")]
unsafe extern "C" {
    fn calloc(count: usize, size: usize) -> *mut c_void;
    fn free(pointer: *mut c_void);
}

fn allocate_zeroed(len: usize) -> *mut u8 {
    #[cfg(test)]
    if test_support::before_allocation() {
        return std::ptr::null_mut();
    }
    #[cfg(test)]
    test_support::record_native_allocation();

    // SAFETY: `calloc` accepts all `usize` count and size values. The caller
    // has bounded the positive byte count by `isize::MAX`, and a one-byte
    // element size cannot overflow the requested allocation size.
    unsafe { calloc(len, 1).cast::<u8>() }
}

fn release(pointer: NonNull<u8>) {
    #[cfg(test)]
    test_support::record_native_release();

    // SAFETY: This private function is called only by `NativeBuffer::drop` with
    // the unique non-null result of `calloc`, and that Drop is the sole caller
    // for each successfully constructed owner.
    unsafe { free(pointer.as_ptr().cast::<c_void>()) };
}

#[cfg(test)]
mod test_support {
    use std::cell::Cell;

    std::thread_local! {
        static FAIL_NEXT_ALLOCATION: Cell<bool> = const { Cell::new(false) };
        static ALLOCATION_ATTEMPTS: Cell<usize> = const { Cell::new(0) };
        static NATIVE_ALLOCATION_CALLS: Cell<usize> = const { Cell::new(0) };
        static NATIVE_RELEASE_CALLS: Cell<usize> = const { Cell::new(0) };
    }

    pub(super) fn reset() {
        FAIL_NEXT_ALLOCATION.set(false);
        ALLOCATION_ATTEMPTS.set(0);
        NATIVE_ALLOCATION_CALLS.set(0);
        NATIVE_RELEASE_CALLS.set(0);
    }

    pub(super) fn fail_next_allocation() {
        FAIL_NEXT_ALLOCATION.set(true);
    }

    pub(super) fn before_allocation() -> bool {
        ALLOCATION_ATTEMPTS.set(ALLOCATION_ATTEMPTS.get() + 1);
        FAIL_NEXT_ALLOCATION.replace(false)
    }

    pub(super) fn record_native_allocation() {
        NATIVE_ALLOCATION_CALLS.set(NATIVE_ALLOCATION_CALLS.get() + 1);
    }

    pub(super) fn record_native_release() {
        NATIVE_RELEASE_CALLS.set(NATIVE_RELEASE_CALLS.get() + 1);
    }

    pub(super) fn allocation_attempts() -> usize {
        ALLOCATION_ATTEMPTS.get()
    }

    pub(super) fn native_allocation_calls() -> usize {
        NATIVE_ALLOCATION_CALLS.get()
    }

    pub(super) fn native_release_calls() -> usize {
        NATIVE_RELEASE_CALLS.get()
    }
}

/// Failure to create a native byte buffer.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum AllocationError {
    /// The requested length is zero or exceeds the addressable allocation bound.
    InvalidLength,
    /// The host allocator returned no block.
    AllocationFailed,
}

/// Sole owner of one native byte buffer.
#[must_use = "dropping the owner immediately releases the native buffer"]
pub struct NativeBuffer {
    pointer: NonNull<u8>,
    len: usize,
}

impl NativeBuffer {
    /// Allocates a zero-initialized native byte buffer.
    ///
    /// # Errors
    ///
    /// Returns [`AllocationError::InvalidLength`] when `len` is zero or greater
    /// than `isize::MAX`. Returns [`AllocationError::AllocationFailed`] when the
    /// host allocator returns no block.
    pub fn allocate(len: usize) -> Result<Self, AllocationError> {
        if len == 0 || len > isize::MAX as usize {
            return Err(AllocationError::InvalidLength);
        }

        let pointer = allocate_zeroed(len);
        let pointer = NonNull::new(pointer).ok_or(AllocationError::AllocationFailed)?;

        Ok(Self { pointer, len })
    }

    /// Returns the allocation's positive byte length.
    #[must_use]
    #[allow(
        clippy::len_without_is_empty,
        reason = "native buffers reject empty allocations"
    )]
    pub const fn len(&self) -> usize {
        self.len
    }

    /// Copies the byte at `index`, or returns `None` when it is out of bounds.
    #[must_use]
    pub fn read(&self, index: usize) -> Option<u8> {
        if index >= self.len {
            return None;
        }

        // SAFETY: Allocation accepts only lengths through `isize::MAX` and
        // stores the original length. The check above keeps `index` within the
        // live allocation, which `calloc` initialized byte-for-byte.
        Some(unsafe { self.pointer.as_ptr().add(index).read() })
    }

    /// Writes `value` at `index`, returning whether the index was in bounds.
    #[must_use]
    pub fn write(&mut self, index: usize, value: u8) -> bool {
        if index >= self.len {
            return false;
        }

        // SAFETY: Allocation accepts only lengths through `isize::MAX` and
        // stores the original length. The check above keeps `index` within the
        // live allocation, and exclusive access to `self` prevents safe callers
        // from concurrently reading or writing through this owner.
        unsafe { self.pointer.as_ptr().add(index).write(value) };
        true
    }
}

impl Drop for NativeBuffer {
    fn drop(&mut self) {
        release(self.pointer);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn invalid_lengths_are_rejected() {
        test_support::reset();

        assert!(matches!(
            NativeBuffer::allocate(0),
            Err(AllocationError::InvalidLength)
        ));
        assert!(matches!(
            NativeBuffer::allocate(usize::MAX),
            Err(AllocationError::InvalidLength)
        ));
        assert_eq!(test_support::allocation_attempts(), 0);
        assert_eq!(test_support::native_allocation_calls(), 0);
        assert_eq!(test_support::native_release_calls(), 0);
    }

    #[test]
    fn positive_allocation_has_requested_length_and_zeroed_bytes() {
        test_support::reset();
        let buffer = NativeBuffer::allocate(4).expect("positive native allocation should succeed");

        assert_eq!(test_support::allocation_attempts(), 1);
        assert_eq!(test_support::native_allocation_calls(), 1);
        assert_eq!(buffer.len(), 4);
        assert_eq!(
            (0..buffer.len())
                .map(|index| buffer.read(index))
                .collect::<Vec<_>>(),
            vec![Some(0), Some(0), Some(0), Some(0)]
        );
    }

    #[test]
    fn write_updates_the_selected_byte() {
        let mut buffer =
            NativeBuffer::allocate(2).expect("positive native allocation should succeed");

        assert!(buffer.write(1, 255));
        assert_eq!(buffer.read(0), Some(0));
        assert_eq!(buffer.read(1), Some(255));
    }

    #[test]
    fn out_of_bounds_access_is_rejected_without_mutation() {
        let mut buffer =
            NativeBuffer::allocate(2).expect("positive native allocation should succeed");
        assert!(buffer.write(0, 7));

        assert!(!buffer.write(2, 9));
        assert_eq!(buffer.read(0), Some(7));
        assert_eq!(buffer.read(2), None);
    }

    #[test]
    fn injected_null_allocation_returns_failure_without_release() {
        test_support::reset();
        test_support::fail_next_allocation();

        assert!(matches!(
            NativeBuffer::allocate(1),
            Err(AllocationError::AllocationFailed)
        ));
        assert_eq!(test_support::allocation_attempts(), 1);
        assert_eq!(test_support::native_allocation_calls(), 0);
        assert_eq!(test_support::native_release_calls(), 0);
    }

    #[test]
    fn moving_an_owner_still_releases_exactly_once() {
        test_support::reset();
        let buffer = NativeBuffer::allocate(1).expect("positive native allocation should succeed");
        let moved = buffer;

        assert_eq!(test_support::allocation_attempts(), 1);
        assert_eq!(test_support::native_allocation_calls(), 1);
        assert_eq!(test_support::native_release_calls(), 0);
        drop(moved);
        assert_eq!(test_support::native_release_calls(), 1);
    }
}
