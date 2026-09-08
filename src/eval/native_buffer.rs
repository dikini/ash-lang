//! Safe evaluator ownership of the fixed native adapter.

use ash_native_buffer::{AllocationError, NativeBuffer};

pub(super) struct NativeOwner {
    buffer: NativeBuffer,
}

impl std::fmt::Debug for NativeOwner {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("NativeOwner")
            .field("len", &self.len())
            .finish()
    }
}

impl NativeOwner {
    pub(super) fn allocate(len: usize) -> Result<Self, AllocationError> {
        #[cfg(test)]
        {
            tests::ATTEMPTS.set(tests::ATTEMPTS.get() + 1);
            if tests::FAIL_ALLOCATION.replace(false) {
                if tests::PROBE_REFUSAL.replace(false) {
                    crate::types::reset_type_discard_observation();
                    crate::eval::disposal::reset_growth_attempts();
                    tests::REFUSAL_PROBE_ACTIVE.set(true);
                }
                return Err(AllocationError::AllocationFailed);
            }
            tests::ADAPTER_CALLS.set(tests::ADAPTER_CALLS.get() + 1);
        }
        let buffer = NativeBuffer::allocate(len)?;
        #[cfg(test)]
        tests::OWNERS.set(tests::OWNERS.get() + 1);
        Ok(Self { buffer })
    }

    pub(super) fn len(&self) -> usize {
        self.buffer.len()
    }

    pub(super) fn read(&self, index: usize) -> Option<u8> {
        #[cfg(test)]
        tests::READS.set(tests::READS.get() + 1);
        self.buffer.read(index)
    }

    pub(super) fn write(&mut self, index: usize, byte: u8) -> bool {
        #[cfg(test)]
        tests::WRITES.set(tests::WRITES.get() + 1);
        self.buffer.write(index, byte)
    }
}

// Counts evaluator transfers to the adapter's fixed Drop. Actual C calls are
// separately checked inside the adapter package; injected failures never count
// as adapter calls or successful native owners.
#[cfg(test)]
impl Drop for NativeOwner {
    fn drop(&mut self) {
        tests::RELEASES.set(tests::RELEASES.get() + 1);
    }
}

#[cfg(test)]
pub(super) mod tests {
    use std::cell::Cell;

    std::thread_local! {
        pub(crate) static FAIL_ALLOCATION: Cell<bool> = const { Cell::new(false) };
        pub(crate) static FAIL_PUBLICATION: Cell<bool> = const { Cell::new(false) };
        pub(crate) static FAIL_WRITE_RESULT: Cell<bool> = const { Cell::new(false) };
        pub(crate) static FAIL_DISPOSAL_GROWTH: Cell<bool> = const { Cell::new(false) };
        pub(crate) static FAIL_CONTROL_RESERVATION: Cell<Option<crate::eval::ResourceFailureCause>> = const { Cell::new(None) };
        pub(crate) static REFUSAL_PROBE_ACTIVE: Cell<bool> = const { Cell::new(false) };
        pub(crate) static PROBE_REFUSAL: Cell<bool> = const { Cell::new(false) };
        pub(crate) static REFUSAL_ENV_GROWTH: Cell<usize> = const { Cell::new(0) };
        pub(crate) static ATTEMPTS: Cell<usize> = const { Cell::new(0) };
        pub(crate) static ADAPTER_CALLS: Cell<usize> = const { Cell::new(0) };
        pub(crate) static OWNERS: Cell<usize> = const { Cell::new(0) };
        pub(crate) static RELEASES: Cell<usize> = const { Cell::new(0) };
        pub(crate) static READS: Cell<usize> = const { Cell::new(0) };
        pub(crate) static WRITES: Cell<usize> = const { Cell::new(0) };
        pub(crate) static CAPTURE_DISPOSAL_GROWTH: Cell<usize> = const { Cell::new(0) };
    }

    pub(crate) fn reset() {
        FAIL_ALLOCATION.set(false);
        FAIL_PUBLICATION.set(false);
        FAIL_WRITE_RESULT.set(false);
        FAIL_DISPOSAL_GROWTH.set(false);
        FAIL_CONTROL_RESERVATION.set(None);
        REFUSAL_PROBE_ACTIVE.set(false);
        PROBE_REFUSAL.set(false);
        REFUSAL_ENV_GROWTH.set(0);
        ATTEMPTS.set(0);
        ADAPTER_CALLS.set(0);
        OWNERS.set(0);
        RELEASES.set(0);
        READS.set(0);
        WRITES.set(0);
        CAPTURE_DISPOSAL_GROWTH.set(0);
    }
}
