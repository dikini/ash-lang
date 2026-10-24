//! Private physical transport only. Neither type availability nor a prepared
//! acquisition supplies source, protected-context or native-entry permission.

#[cfg(ash_checked_owner_root = "v1")]
pub(crate) use crate::checked_owner_root::transport::{OwnerCell, ViewDescriptor, RawScalar, DisposalReturned};

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
    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    pub(crate) enum RawScalar { I8(i8), U8(u8), I32(i32), U32(u32), I64(i64), U64(u64), USize(usize) }
    pub(crate) struct DisposalReturned { disposition: Option<bool>, status: Option<RawScalar>, readable: bool }
    impl DisposalReturned {
        pub(crate) fn disposition(&self) -> Option<bool> { self.disposition }
        pub(crate) fn status(&self) -> Option<RawScalar> { self.status }
        pub(crate) fn readable(&self) -> bool { self.readable }
    }
    pub(crate) struct OutputAcquireReturned { nonnull: bool, status: RawScalar, offset: Option<*mut core::ffi::c_void> }
    impl OutputAcquireReturned {
        pub(crate) fn nonnull(&self) -> bool { self.nonnull }
        pub(crate) fn status(&self) -> RawScalar { self.status }
        pub(crate) fn offset(&self) -> Option<*mut core::ffi::c_void> { self.offset }
    }
    pub(crate) struct PreparedOutputAcquire<'s, 'i> {
        destination: &'s mut OwnerCell, prepared: Option<Owner>, _input: &'i [u8], status: i32,
        parent: Option<&'s OwnerCell>,
    }
    pub(crate) struct PreparedTeardown<'s> { destination: &'s mut OwnerCell }

    struct Owner {
        serial: u64,
        bytes: Box<[u8; 8]>,
        opaque: bool,
        unresolved: bool,
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
        static OUTPUT_STATUS: Cell<i32> = const { Cell::new(0) };
        static DISPOSAL: Cell<(Option<bool>, Option<i32>, bool)> = const { Cell::new((Some(true), None, true)) };
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
                opaque: false, unresolved: false,
            });
            Ok(PreparedAcquire {
                destination: self,
                prepared,
            })
        }
        pub(crate) fn prepare_output_acquire<'s, 'i>(&'s mut self, input: &'i [u8])
            -> Result<PreparedOutputAcquire<'s, 'i>, Refusal> {
            if self.is_occupied() { return Err(Refusal::Owner); }
            let Some((&0, prefix)) = input.split_last() else { return Err(Refusal::Profile); };
            if prefix.contains(&0) { return Err(Refusal::Profile); }
            let serial = SERIAL.get();
            SERIAL.set(serial.checked_add(1).ok_or(Refusal::Identity)?);
            let prepared = (!NULL.replace(false)).then(||Owner {
                serial, bytes: Box::new([0; 8]), opaque: true, unresolved: false,
            });
            Ok(PreparedOutputAcquire { destination: self, prepared, _input: input, status: OUTPUT_STATUS.get(), parent: None })
        }
        pub(crate) fn prepare_dependent_output_acquire<'s, 'i>(&'s mut self, parent: &'s OwnerCell,
            input: &'i [u8], length: i32) -> Result<PreparedOutputAcquire<'s, 'i>, Refusal> {
            let owner = parent.owner.as_ref().ok_or(Refusal::Owner)?;
            if !owner.opaque || owner.unresolved { return Err(Refusal::Owner); }
            if usize::try_from(length).ok().is_none_or(|length|length > input.len()) { return Err(Refusal::Range); }
            let mut prepared = self.prepare_output_acquire(input)?;
            prepared.parent = Some(parent);
            Ok(prepared)
        }
        pub(crate) fn mark_unresolved_for_test(&mut self) {
            self.owner.as_mut().expect("injected occupied owner").unresolved = true;
        }
        pub(crate) fn prepare_teardown(&mut self) -> Result<PreparedTeardown<'_>, Refusal> {
            if self.owner.as_ref().is_none_or(|owner|owner.unresolved) { return Err(Refusal::Owner); }
            Ok(PreparedTeardown { destination: self })
        }
        pub(crate) fn query(&self, key: usize) -> Result<Option<ViewDescriptor>, Refusal> {
            let owner = self.owner.as_ref().ok_or(Refusal::Owner)?;
            if owner.opaque || owner.unresolved { return Err(Refusal::Profile); }
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
            if owner.opaque || owner.unresolved { return Err(Refusal::Profile); }
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
            if owner.opaque || owner.unresolved { return Err(Refusal::Profile); }
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
    impl PreparedOutputAcquire<'_, '_> {
        pub(crate) fn invoke(self) -> OutputAcquireReturned {
            call(0);
            self.destination.owner = self.prepared;
            OutputAcquireReturned { nonnull: self.destination.owner.is_some(), status: RawScalar::I32(self.status),
                offset: (self.parent.is_some() && self.status == 0).then(||self._input.as_ptr().wrapping_add(self._input.len() - 1).cast_mut().cast()) }
        }
    }
    impl PreparedTeardown<'_> {
        pub(crate) fn invoke(self) -> DisposalReturned {
            call(4);
            let owner = self.destination.owner.as_ref().expect("held prepared owner");
            let (disposition, status, readable) = if owner.opaque { DISPOSAL.get() } else { (Some(true), None, true) };
            match disposition {
                Some(true) => self.destination.owner = None,
                Some(false) => {},
                None => self.destination.owner.as_mut().unwrap().unresolved = true,
            }
            DisposalReturned { disposition, status: if disposition.is_some() {status.map(RawScalar::I32)} else {None}, readable }
        }
    }
    pub(crate) fn output_status(value: i32) { OUTPUT_STATUS.set(value); }
    pub(crate) fn disposal(disposition: Option<bool>, status: Option<i32>, readable: bool) {
        DISPOSAL.set((disposition, status, readable));
    }
    pub(crate) fn reset() {
        CALLS.set([0; 5]);
        OUTPUT_STATUS.set(0);
        DISPOSAL.set((Some(true), None, true));
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
    #[cfg(test)]
    mod output_status_tests {
        use super::*;
        #[test]
        fn dependent_transport_holds_parent_and_destination_without_address_escape() {
            reset();
            let mut parent = OwnerCell::vacant();
            parent.prepare_output_acquire(b"name\0").unwrap().invoke();
            let mut child = OwnerCell::vacant();
            let absent = OwnerCell::vacant();
            assert!(child.prepare_dependent_output_acquire(&absent, b"SELECT 1;\0", 10).is_err());
            assert!(child.prepare_dependent_output_acquire(&parent, b"SELECT 1;\0", -1).is_err());
            drop(child.prepare_dependent_output_acquire(&parent, b"SELECT 1;\0", 4).unwrap());
            assert_eq!(calls()[0], 1);
            assert!(child.prepare_dependent_output_acquire(&parent, b"SELECT 1;\0", 11).is_err());
            let input = b"SELECT 1;\0";
            let returned = child.prepare_dependent_output_acquire(&parent, input, 10).unwrap().invoke();
            assert!(returned.nonnull());
            assert!(parent.is_occupied());
            assert_eq!(returned.offset(), Some(input.as_ptr().wrapping_add(9).cast_mut().cast()));
            assert!(child.query(0).is_err());
            disposal(Some(true), Some(-3), true);
            assert_eq!(child.prepare_teardown().unwrap().invoke().disposition(), Some(true));
            assert!(parent.is_occupied());
            assert!(!child.is_occupied());
        }
        #[test]
        fn transport_model_arms_error_output_and_retains_exact_owner_on_status() {
            reset(); output_status(-11);
            let mut cell = OwnerCell::vacant();
            drop(cell.prepare_output_acquire(b"name\0").unwrap());
            assert!(!cell.is_occupied()); assert_eq!(calls(), [0; 5]);
            assert!(cell.prepare_output_acquire(b"bad\0tail\0").is_err());
            let returned = cell.prepare_output_acquire(b"name\0").unwrap().invoke();
            assert!(returned.nonnull()); assert_eq!(returned.status(), RawScalar::I32(-11));
            let serial = cell.owner.as_ref().unwrap().serial;
            disposal(Some(false), Some(7), false);
            let returned = cell.prepare_teardown().unwrap().invoke();
            assert_eq!(returned.disposition(), Some(false));
            assert_eq!(returned.status(), Some(RawScalar::I32(7)));
            assert!(!returned.readable());
            assert_eq!(cell.owner.as_ref().unwrap().serial, serial);
            assert!(cell.query(0).is_err());
            disposal(Some(true), Some(0), true);
            let returned = cell.prepare_teardown().unwrap().invoke();
            assert_eq!(returned.disposition(), Some(true)); assert!(!cell.is_occupied());
            assert!(cell.prepare_teardown().is_err());
            assert_eq!(calls(), [1, 0, 0, 0, 2]);
        }
        #[test]
        fn transport_model_null_and_no_o4_never_fabricate_owner_or_retry() {
            reset(); null_next();
            let mut empty = OwnerCell::vacant();
            assert!(!empty.prepare_output_acquire(b"name\0").unwrap().invoke().nonnull());
            assert!(empty.prepare_teardown().is_err());
            let mut cell = OwnerCell::vacant();
            cell.prepare_output_acquire(b"name\0").unwrap().invoke();
            let serial = cell.owner.as_ref().unwrap().serial;
            disposal(None, Some(99), true);
            let returned = cell.prepare_teardown().unwrap().invoke();
            assert_eq!(returned.disposition(), None); assert_eq!(returned.status(), None);
            assert_eq!(cell.owner.as_ref().unwrap().serial, serial);
            assert!(cell.is_occupied()); assert!(cell.prepare_teardown().is_err());
            drop(cell); drop(empty);
            assert_eq!(calls(), [2, 0, 0, 0, 1]);
        }
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
