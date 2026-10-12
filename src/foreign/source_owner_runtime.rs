//! Unique native storage for dependency-free opaque and initialized byte owners.
//!
//! Checked resource admission supplies the exact owner and teardown callback.
//! Generated code contains the unsafe native call; this module never dereferences
//! an address or exposes it as an ordinary Ash value.

use std::{fmt, ptr::NonNull, sync::Arc};

use crate::foreign::{
    source_owner::CheckedForeignOwner,
    source_runtime::{NativeScalarCallError, NativeScalarValue},
};

/// A generated acquisition call receives already admitted destruction storage.
/// This transport supplies no source lifecycle permission by itself.
#[doc(hidden)]
pub type NativeOwnerAcquireCallback = fn(
    &[NativeScalarValue],
    NativeOwnerGuardReady,
) -> Result<NativeOwnerCallReturned, NativeScalarCallError>;

/// The generated unconditional consuming teardown; unsafe code stays in the host.
/// Its callback is admitted against the exact checked owner before acquisition.
#[doc(hidden)]
pub type NativeOwnerTeardownCallback = fn(*mut core::ffi::c_void);

struct RawOwnerGuard {
    address: Option<NonNull<core::ffi::c_void>>,
    teardown: NativeOwnerTeardownCallback,
}

impl fmt::Debug for RawOwnerGuard {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("RawOwnerGuard")
            .field("live", &self.address.is_some())
            .finish_non_exhaustive()
    }
}

impl RawOwnerGuard {
    fn empty(teardown: NativeOwnerTeardownCallback) -> Self {
        Self {
            address: None,
            teardown,
        }
    }

    fn consume(&mut self) {
        if let Some(address) = self.address.take() {
            // The sealed generated callback consumes this dependency-free opaque
            // owner unconditionally. Taking first prevents replay during unwind.
            (self.teardown)(address.as_ptr());
        }
    }
}

impl Drop for RawOwnerGuard {
    fn drop(&mut self) {
        self.consume();
    }
}

/// One non-cloneable native guard. The address never enters the Ash heap.
#[derive(Debug)]
pub(crate) struct NativeOwnerGuard {
    raw: RawOwnerGuard,
    owner: Arc<CheckedForeignOwner>,
    initialized_bytes: Option<usize>,
}

impl NativeOwnerGuard {
    pub(crate) fn owner(&self) -> &Arc<CheckedForeignOwner> {
        &self.owner
    }

    #[cfg(test)]
    pub(crate) fn initialized_bytes(&self) -> Option<usize> {
        self.initialized_bytes
    }

    /// Consumes native state once and returns original authority without a call
    /// capability. No Ash result allocation or shared work charge occurs here.
    pub(crate) fn finish(mut self) -> NativeOwnerConsumed {
        let receipt = NativeOwnerConsumed {
            owner: Arc::clone(&self.owner),
        };
        let _ = self.initialized_bytes.take();
        self.raw.consume();
        receipt
    }
}

/// Recorded consumption retains defining authority but cannot invoke native code.
#[derive(Debug)]
pub(crate) struct NativeOwnerConsumed {
    owner: Arc<CheckedForeignOwner>,
}

impl NativeOwnerConsumed {
    pub(crate) fn owner(&self) -> &Arc<CheckedForeignOwner> {
        &self.owner
    }
}

/// An inline empty guard prepared before the irreversible acquisition call.
/// Only the checked binding/resource path may create it.
#[doc(hidden)]
#[derive(Debug)]
pub struct NativeOwnerGuardReady {
    guard: NativeOwnerGuard,
    prepared_initialized_bytes: Option<usize>,
}

impl NativeOwnerGuardReady {
    pub(crate) fn new(
        owner: Arc<CheckedForeignOwner>,
        teardown: NativeOwnerTeardownCallback,
    ) -> Self {
        Self {
            guard: NativeOwnerGuard {
                raw: RawOwnerGuard::empty(teardown),
                owner,
                initialized_bytes: None,
            },
            prepared_initialized_bytes: None,
        }
    }

    /// Retains the already checked original source extent before native entry.
    /// This is preparation only; a null reply establishes no initialized region.
    pub(crate) fn prepare_initialized_bytes(&mut self, extent: Option<usize>) {
        self.prepared_initialized_bytes = extent;
    }

    /// Called immediately by the generated typed wrapper after native return.
    /// It arms already prepared storage without allocation or a work charge.
    /// A null result carries no owner; non-null results are guarded even before
    /// the evaluator records or constructs an ordinary report.
    #[doc(hidden)]
    pub fn returned(mut self, address: *mut core::ffi::c_void) -> NativeOwnerCallReturned {
        self.guard.raw.address = NonNull::new(address);
        NativeOwnerCallReturned {
            guard: self.guard,
            prepared_initialized_bytes: self.prepared_initialized_bytes,
        }
    }
}

/// A raw native return with destruction already armed and no acquisition callback.
#[doc(hidden)]
#[derive(Debug)]
pub struct NativeOwnerCallReturned {
    guard: NativeOwnerGuard,
    prepared_initialized_bytes: Option<usize>,
}

impl NativeOwnerCallReturned {
    /// The first post-return transition records ownership without refusal.
    pub(crate) fn record(mut self) -> NativeOwnerCallRecorded {
        if self.guard.raw.address.is_some() {
            self.guard.initialized_bytes = self.prepared_initialized_bytes;
        }
        NativeOwnerCallRecorded { guard: self.guard }
    }
}

/// Recorded nullness and unique storage; ordinary reporting may now proceed.
#[derive(Debug)]
pub(crate) struct NativeOwnerCallRecorded {
    guard: NativeOwnerGuard,
}

impl NativeOwnerCallRecorded {
    pub(crate) fn into_guard(self) -> Option<NativeOwnerGuard> {
        self.guard.raw.address.is_some().then_some(self.guard)
    }
}

#[cfg(test)]
mod tests {
    use super::RawOwnerGuard;
    use std::ptr::NonNull;
    use std::sync::atomic::{AtomicUsize, Ordering};

    static DESTRUCTIONS: AtomicUsize = AtomicUsize::new(0);

    fn destroy(address: *mut core::ffi::c_void) {
        assert_eq!(address, std::ptr::dangling_mut::<u8>().cast());
        DESTRUCTIONS.fetch_add(1, Ordering::SeqCst);
    }

    #[test]
    fn raw_guard_destroys_only_nonnull_storage_and_consumption_cannot_replay() {
        DESTRUCTIONS.store(0, Ordering::SeqCst);
        drop(RawOwnerGuard::empty(destroy));
        assert_eq!(DESTRUCTIONS.load(Ordering::SeqCst), 0);

        let mut guard = RawOwnerGuard::empty(destroy);
        guard.address = NonNull::new(std::ptr::dangling_mut::<u8>().cast());
        guard.consume();
        assert_eq!(DESTRUCTIONS.load(Ordering::SeqCst), 1);
        drop(guard);
        assert_eq!(DESTRUCTIONS.load(Ordering::SeqCst), 1);

        let mut unpublished = RawOwnerGuard::empty(destroy);
        unpublished.address = NonNull::new(std::ptr::dangling_mut::<u8>().cast());
        drop(unpublished);
        assert_eq!(DESTRUCTIONS.load(Ordering::SeqCst), 2);
    }
}
