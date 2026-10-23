//! Private physical transport only. Neither type availability nor a prepared
//! acquisition supplies source, protected-context or native-entry permission.

#[cfg(ash_checked_owner_root = "v1")]
pub(crate) use crate::checked_owner_root::transport::{FreeObservation, OwnerCell, ViewDescriptor};

#[cfg(all(test, not(ash_checked_owner_root = "v1")))]
mod injected {
    use std::{cell::Cell, fmt};

    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    pub(crate) enum Refusal {
        Profile,
        Identity,
        Range,
        Owner,
    }
    #[derive(Debug)]
    pub(crate) enum AcquirePreparationFailure {
        DestinationOccupied,
        NotEntered(Refusal),
    }
    pub(crate) struct AcquireReturned {
        nonnull: bool,
    }
    pub(crate) enum FreeObservation {
        NoOwner,
        Returned(ReleaseReturned),
    }
    pub(crate) struct ReleaseReturned;
    struct Owner {
        serial: u64,
        bytes: Box<[u8; 8]>,
    }
    pub(crate) struct OwnerCell {
        owner: Option<Owner>,
    }
    pub(crate) struct ViewDescriptor {
        serial: u64,
        offset: usize,
        available: usize,
    }
    pub(crate) struct PreparedAcquire<'a> {
        destination: &'a mut OwnerCell,
        prepared: Option<Owner>,
    }
    thread_local! {
        static SERIAL: Cell<u64> = const { Cell::new(1) };
        static NULL: Cell<bool> = const { Cell::new(false) };
        static IDENTITY_REFUSAL: Cell<bool> = const { Cell::new(false) };
        static CALLS: Cell<[usize; 5]> = const { Cell::new([0; 5]) };
    }
    fn call(index: usize) {
        let mut n = CALLS.get();
        n[index] += 1;
        CALLS.set(n);
    }
    impl fmt::Debug for OwnerCell {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            f.debug_struct("InjectedOwnerCell")
                .field("occupied", &self.is_occupied())
                .finish()
        }
    }
    impl fmt::Debug for ViewDescriptor {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            f.write_str("InjectedViewDescriptor { .. }")
        }
    }
    impl AcquireReturned {
        pub(crate) fn nonnull(&self) -> bool {
            self.nonnull
        }
    }
    impl OwnerCell {
        pub(crate) fn vacant() -> Self {
            Self { owner: None }
        }
        pub(crate) fn is_occupied(&self) -> bool {
            self.owner.is_some()
        }
        pub(crate) fn prepare_acquire(
            &mut self,
            capacity: usize,
            initialized: usize,
        ) -> Result<PreparedAcquire<'_>, AcquirePreparationFailure> {
            if self.is_occupied() {
                return Err(AcquirePreparationFailure::DestinationOccupied);
            }
            if capacity != 8 || initialized != 8 {
                return Err(AcquirePreparationFailure::NotEntered(Refusal::Profile));
            }
            if IDENTITY_REFUSAL.replace(false) {
                return Err(AcquirePreparationFailure::NotEntered(Refusal::Identity));
            }
            let serial = SERIAL.get();
            SERIAL.set(
                serial
                    .checked_add(1)
                    .ok_or(AcquirePreparationFailure::NotEntered(Refusal::Identity))?,
            );
            // Rust-only injected storage is allocated before the simulated
            // entry, never between the returned owner and destination arming.
            let prepared = (!NULL.replace(false)).then(|| Owner {
                serial,
                bytes: Box::new([5, 255, 0, 65, 66, 67, 0, 9]),
            });
            Ok(PreparedAcquire {
                destination: self,
                prepared,
            })
        }
        pub(crate) fn query(&self, key: usize) -> Result<Option<ViewDescriptor>, Refusal> {
            let owner = self.owner.as_ref().ok_or(Refusal::Owner)?;
            call(1);
            if key > owner.bytes.len() {
                return Err(Refusal::Range);
            }
            Ok(Some(ViewDescriptor {
                serial: owner.serial,
                offset: key,
                available: owner.bytes.len() - key,
            }))
        }
        pub(crate) fn length(&self, key: usize) -> Result<usize, Refusal> {
            let owner = self.owner.as_ref().ok_or(Refusal::Owner)?;
            call(2);
            owner.bytes.len().checked_sub(key).ok_or(Refusal::Range)
        }
        pub(crate) fn copy(
            &self,
            descriptor: &ViewDescriptor,
            offset: usize,
            destination: &mut [u8],
        ) -> Result<(), Refusal> {
            let owner = self.owner.as_ref().ok_or(Refusal::Owner)?;
            if descriptor.serial != owner.serial {
                return Err(Refusal::Owner);
            }
            let end = offset
                .checked_add(destination.len())
                .ok_or(Refusal::Range)?;
            if end > descriptor.available {
                return Err(Refusal::Range);
            }
            let start = descriptor
                .offset
                .checked_add(offset)
                .ok_or(Refusal::Range)?;
            let end = start.checked_add(destination.len()).ok_or(Refusal::Range)?;
            let source = owner.bytes.get(start..end).ok_or(Refusal::Range)?;
            call(3);
            destination.copy_from_slice(source);
            Ok(())
        }
        pub(crate) fn free(mut self) -> FreeObservation {
            if self.owner.take().is_none() {
                return FreeObservation::NoOwner;
            }
            call(4);
            FreeObservation::Returned(ReleaseReturned)
        }
    }
    impl PreparedAcquire<'_> {
        pub(crate) fn invoke(self) -> AcquireReturned {
            call(0);
            self.destination.owner = self.prepared;
            AcquireReturned {
                nonnull: self.destination.owner.is_some(),
            }
        }
    }
    pub(crate) fn reset() {
        CALLS.set([0; 5]);
        NULL.set(false);
        IDENTITY_REFUSAL.set(false);
    }
    pub(crate) fn null_next() {
        NULL.set(true);
    }
    pub(crate) fn refuse_identity_next() {
        IDENTITY_REFUSAL.set(true);
    }
    pub(crate) fn calls() -> [usize; 5] {
        CALLS.get()
    }
}

#[cfg(all(test, not(ash_checked_owner_root = "v1")))]
pub(crate) use injected::*;

#[cfg(all(test, not(ash_checked_owner_root = "v1")))]
mod tests {
    use super::*;

    #[test]
    fn preparation_refuses_before_entry_and_dropped_readiness_performs_no_call() {
        reset();
        let mut cell = OwnerCell::vacant();
        assert!(matches!(
            cell.prepare_acquire(7, 8),
            Err(AcquirePreparationFailure::NotEntered(Refusal::Profile))
        ));
        refuse_identity_next();
        assert!(matches!(
            cell.prepare_acquire(8, 8),
            Err(AcquirePreparationFailure::NotEntered(Refusal::Identity))
        ));
        drop(cell.prepare_acquire(8, 8).unwrap());
        assert!(!cell.is_occupied());
        assert_eq!(calls(), [0; 5]);
        assert!(cell.prepare_acquire(8, 8).unwrap().invoke().nonnull());
        assert!(matches!(
            cell.prepare_acquire(8, 8),
            Err(AcquirePreparationFailure::DestinationOccupied)
        ));
        drop(cell);
        assert_eq!(
            calls(),
            [1, 0, 0, 0, 0],
            "physical storage Drop is never native Free"
        );
    }

    #[test]
    fn descriptor_requires_same_live_owner_and_complete_bounds_before_copy() {
        reset();
        let mut owner = OwnerCell::vacant();
        assert!(owner.prepare_acquire(8, 8).unwrap().invoke().nonnull());
        let descriptor = owner.query(0).unwrap().unwrap();
        assert_eq!(owner.length(0).unwrap(), 8);
        let mut donor = OwnerCell::vacant();
        donor.prepare_acquire(8, 8).unwrap().invoke();
        let mut bytes = [0; 8];
        assert_eq!(donor.copy(&descriptor, 0, &mut bytes), Err(Refusal::Owner));
        assert_eq!(owner.copy(&descriptor, 1, &mut bytes), Err(Refusal::Range));
        assert_eq!(bytes, [0; 8]);
        assert_eq!(calls()[3], 0);
        owner.copy(&descriptor, 0, &mut bytes).unwrap();
        assert_eq!(bytes, [5, 255, 0, 65, 66, 67, 0, 9]);
        assert!(matches!(owner.free(), FreeObservation::Returned(_)));
        drop(donor);
        assert_eq!(calls(), [2, 1, 1, 1, 1]);
    }
}
