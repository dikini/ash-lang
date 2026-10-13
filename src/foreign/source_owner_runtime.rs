//! Unique native storage for dependent opaque and initialized byte owners.
//!
//! Checked resource admission supplies the exact owner and teardown callback.
//! Generated code contains the unsafe native call; this module never dereferences
//! an address or exposes it as an ordinary Ash value.

use std::{cell::RefCell, fmt, ptr::NonNull, rc::Rc, sync::Arc};

use crate::foreign::{
    source_owner::CheckedForeignOwner,
    source_runtime::{NativeScalarCallError, NativeScalarReply, NativeScalarValue},
};
use crate::types::{IterativeTypeOwner, Type, TypeWorkBudget};

#[derive(Debug)]
pub(crate) enum NativeOwnerAdmissionError {
    Authority,
    Work,
    Storage(usize),
}

#[derive(Clone, Copy)]
pub(crate) enum NativeOwnerViewKind {
    State,
    Access,
}

fn pay(work: &mut TypeWorkBudget, count: usize) -> Result<(), NativeOwnerAdmissionError> {
    work.charge(count)
        .map_err(|()| NativeOwnerAdmissionError::Work)
}

/// Nonowning receipt for an exact live typed slot. Slot-to-slot dependencies
/// retain indices, never these Rc handles, so no recursive ownership graph forms.
#[derive(Debug)]
pub(crate) struct NativeOwnerDependency {
    storage: Rc<NativeOwnerStorage>,
    slot: usize,
}

impl NativeOwnerDependency {
    pub(crate) fn same_slot(&self, other: &Self) -> bool {
        Rc::ptr_eq(&self.storage, &other.storage) && self.slot == other.slot
    }
    pub(crate) fn address(&self) -> Option<*mut core::ffi::c_void> {
        self.storage.slots.borrow()[self.slot]
            .raw
            .address
            .map(NonNull::as_ptr)
    }
    pub(crate) fn state(
        &self,
        work: &mut TypeWorkBudget,
    ) -> Result<IterativeTypeOwner, NativeOwnerAdmissionError> {
        let slots = self.storage.slots.borrow();
        let authority = slots[self.slot]
            .authority
            .as_ref()
            .ok_or(NativeOwnerAdmissionError::Authority)?;
        crate::types::clone_type_with_budget(&authority.state, work)
            .map(IterativeTypeOwner::new)
            .map_err(|()| NativeOwnerAdmissionError::Work)
    }
}

struct NativeOwnerSlotAuthority {
    activation: usize,
    state: IterativeTypeOwner,
    access: IterativeTypeOwner,
}

impl fmt::Debug for NativeOwnerSlotAuthority {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("NativeOwnerSlotAuthority")
            .field("activation", &self.activation)
            .finish_non_exhaustive()
    }
}

/// A generated acquisition call receives already admitted destruction storage.
/// This transport supplies no source lifecycle permission by itself.
#[doc(hidden)]
pub type NativeOwnerAcquireCallback = fn(
    &[NativeOwnerOperand],
    NativeOwnerGuardReady,
) -> Result<NativeOwnerCallReturned, NativeScalarCallError>;

/// A generated void teardown; unsafe code stays in the host.
/// Its separate original disposition is admitted before acquisition.
#[doc(hidden)]
pub type NativeOwnerTeardownCallback = fn(&[NativeOwnerOperand]);

/// The exact typed scalar reply from a generated owner teardown.
#[doc(hidden)]
pub type NativeOwnerStatusTeardownCallback = fn(&[NativeOwnerOperand]) -> NativeScalarReply;

#[derive(Debug)]
pub(crate) enum NativeOwnerDestruction {
    Void {
        callback: NativeOwnerTeardownCallback,
        consumes: bool,
    },
    Status {
        callback: NativeOwnerStatusTeardownCallback,
        symbol: Arc<crate::foreign::checked_source::CheckedForeignSymbol>,
    },
}

#[derive(Clone, Copy, Debug)]
pub(crate) struct NativeOwnerStatus {
    pub(crate) reply: NativeScalarReply,
    pub(crate) readable: bool,
    pub(crate) valid: bool,
}

impl NativeOwnerDestruction {
    // This exact descriptor and its finite traversal were admitted before C.
    // No conversion, allocation, reservation or caller charge occurs here.
    pub(crate) fn invoke(
        &self,
        operands: &[NativeOwnerOperand],
    ) -> (bool, Option<NativeOwnerStatus>) {
        match self {
            Self::Void { callback, consumes } => {
                callback(operands);
                (*consumes, None)
            }
            Self::Status { callback, symbol } => {
                use crate::foreign::source_contract::{
                    PreparedAbiResult, PreparedOwnerCall, PreparedScalarRepresentation as Repr,
                    PreparedScalarValue,
                };
                let reply = callback(operands);
                let scalar = match (symbol.symbol().result(), reply) {
                    (
                        PreparedAbiResult::Scalar(Repr::Signed(8)),
                        NativeScalarReply::Scalar(NativeScalarValue::I8(value)),
                    ) => Some((value < 0, i64::from(value).unsigned_abs())),
                    (
                        PreparedAbiResult::Scalar(Repr::Signed(32)),
                        NativeScalarReply::Scalar(NativeScalarValue::I32(value)),
                    ) => Some((value < 0, i64::from(value).unsigned_abs())),
                    (
                        PreparedAbiResult::Scalar(Repr::Signed(64)),
                        NativeScalarReply::Scalar(NativeScalarValue::I64(value)),
                    ) => Some((value < 0, value.unsigned_abs())),
                    (
                        PreparedAbiResult::Scalar(Repr::Unsigned(8)),
                        NativeScalarReply::Scalar(NativeScalarValue::U8(value)),
                    ) => Some((false, u64::from(value))),
                    (
                        PreparedAbiResult::Scalar(Repr::Unsigned(32)),
                        NativeScalarReply::Scalar(NativeScalarValue::U32(value)),
                    ) => Some((false, u64::from(value))),
                    (
                        PreparedAbiResult::Scalar(Repr::Unsigned(64)),
                        NativeScalarReply::Scalar(NativeScalarValue::U64(value)),
                    ) => Some((false, value)),
                    (
                        PreparedAbiResult::Scalar(Repr::SizeT),
                        NativeScalarReply::Scalar(NativeScalarValue::USize(value)),
                    ) => Some((false, value as u64)),
                    _ => None,
                };
                if let (
                    Some((negative, magnitude)),
                    Some(PreparedOwnerCall::StatusTeardown { outcomes, .. }),
                ) = (scalar, symbol.owner_role())
                {
                    let value = PreparedScalarValue {
                        negative,
                        magnitude,
                    };
                    if let Some(outcome) = outcomes.iter().find(|outcome| {
                        outcome
                            .predicates
                            .iter()
                            .all(|predicate| predicate.value == value)
                    }) {
                        return (
                            outcome.consumes,
                            Some(NativeOwnerStatus {
                                reply,
                                readable: outcome.readable,
                                valid: true,
                            }),
                        );
                    }
                }
                // A trusted typed wrapper cannot disagree. An injected malformed
                // reply leaves the same owner quarantined and reports terminally.
                (
                    false,
                    Some(NativeOwnerStatus {
                        reply,
                        readable: false,
                        valid: false,
                    }),
                )
            }
        }
    }
}

/// Already admitted native operands. Addresses are borrowed from guarded slots;
/// this transport alone grants neither source access nor owner disposition.
#[doc(hidden)]
#[derive(Clone, Copy, Debug)]
pub enum NativeOwnerOperand {
    Scalar(NativeScalarValue),
    Address(*mut core::ffi::c_void),
}

/// Generated byte callbacks receive only an already checked live address/index.
/// They carry no source permission and are never exposed as Ash values.
#[doc(hidden)]
pub type NativeByteReadCallback = fn(*mut core::ffi::c_void, usize) -> u8;
#[doc(hidden)]
pub type NativeByteWriteCallback = fn(*mut core::ffi::c_void, usize, u8);

#[derive(Clone, Copy, Debug)]
pub(crate) struct NativeByteCallbacks {
    pub(crate) read: NativeByteReadCallback,
    pub(crate) write: NativeByteWriteCallback,
}

/// A borrowed checked position, tied to the original non-cloneable guard.
/// Source call/instantiation admission must precede requesting this capability.
pub(crate) struct NativeByteAccess<'guard> {
    _guard: &'guard NativeOwnerGuard,
    address: NonNull<core::ffi::c_void>,
    index: usize,
    callbacks: NativeByteCallbacks,
}

impl NativeByteAccess<'_> {
    pub(crate) fn read(self) -> u8 {
        (self.callbacks.read)(self.address.as_ptr(), self.index)
    }

    pub(crate) fn write(self, byte: u8) {
        (self.callbacks.write)(self.address.as_ptr(), self.index, byte);
    }
}

struct RawOwnerGuard {
    address: Option<NonNull<core::ffi::c_void>>,
    teardown: NativeOwnerDestruction,
    operands: Vec<NativeOwnerOperand>,
    current: usize,
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
    #[cfg(test)]
    fn empty(
        teardown: NativeOwnerTeardownCallback,
        count: usize,
        current: usize,
    ) -> Result<Self, ()> {
        Self::with_plan(
            NativeOwnerDestruction::Void {
                callback: teardown,
                consumes: true,
            },
            count,
            current,
        )
    }

    fn with_plan(
        teardown: NativeOwnerDestruction,
        count: usize,
        current: usize,
    ) -> Result<Self, ()> {
        let mut operands = Vec::new();
        operands.try_reserve_exact(count).map_err(|_| ())?;
        operands.resize(count, NativeOwnerOperand::Address(std::ptr::null_mut()));
        Ok(Self {
            address: None,
            teardown,
            operands,
            current,
        })
    }

    fn consume(&mut self) {
        if let Some(address) = self.address.take() {
            // Storage has admitted consumption and kept declared dependencies
            // live. Taking the address first prevents replay during unwind.
            self.operands[self.current] = NativeOwnerOperand::Address(address.as_ptr());
            let _ = self.teardown.invoke(&self.operands);
        }
    }
}

impl Drop for RawOwnerGuard {
    fn drop(&mut self) {
        self.consume();
    }
}

/// Flat stable storage, shared only by nonowning receipts and the host binding
/// table. Each slot owns its one native address; dependencies never own another
/// token or form a recursive Rust destruction chain.
#[derive(Debug, Default)]
pub(crate) struct NativeOwnerStorage {
    slots: RefCell<Vec<NativeOwnerSlot>>,
}

#[derive(Debug)]
struct NativeOwnerSlot {
    raw: RawOwnerGuard,
    quarantined: bool,
    host_attempted: bool,
    authority: Option<NativeOwnerSlotAuthority>,
    dependencies: Box<[usize]>,
    closure: Box<[usize]>,
    live_dependents: usize,
}

impl NativeOwnerStorage {
    fn reserve(
        &self,
        teardown: NativeOwnerDestruction,
        count: usize,
        current: usize,
    ) -> Result<usize, ()> {
        let mut slots = self.slots.borrow_mut();
        slots.try_reserve(1).map_err(|_| ())?;
        let index = slots.len();
        slots.push(NativeOwnerSlot {
            raw: RawOwnerGuard::with_plan(teardown, count, current)?,
            quarantined: false,
            host_attempted: false,
            authority: None,
            dependencies: Box::new([]),
            closure: Box::new([]),
            live_dependents: 0,
        });
        Ok(index)
    }

    fn has_dependents(slots: &[NativeOwnerSlot], index: usize) -> bool {
        slots[index].live_dependents != 0
    }

    fn record_consumed(slots: &mut [NativeOwnerSlot], index: usize) {
        slots[index].raw.address = None;
        for position in 0..slots[index].dependencies.len() {
            let dependency = slots[index].dependencies[position];
            slots[dependency].live_dependents = slots[dependency]
                .live_dependents
                .checked_sub(1)
                .expect("one recorded live dependency edge");
        }
    }

    fn quarantine(slots: &mut [NativeOwnerSlot], index: usize) {
        slots[index].quarantined = true;
        for position in 0..slots[index].closure.len() {
            let dependency = slots[index].closure[position];
            slots[dependency].quarantined = true;
        }
    }

    fn destroy(slots: &mut [NativeOwnerSlot], index: usize) {
        if slots[index].host_attempted || Self::has_dependents(slots, index) {
            return;
        }
        let slot = &mut slots[index];
        slot.host_attempted = true;
        if let Some(address) = slot.raw.address.take() {
            slot.raw.operands[slot.raw.current] = NativeOwnerOperand::Address(address.as_ptr());
            let (consumes, _) = slot.raw.teardown.invoke(&slot.raw.operands);
            if !consumes {
                slot.raw.address = Some(address);
                Self::quarantine(slots, index);
            } else {
                Self::record_consumed(slots, index);
            }
        }
    }

    fn abandon(&self, index: usize) {
        let mut slots = self.slots.borrow_mut();
        if !slots[index].quarantined {
            Self::destroy(&mut slots, index);
        }
    }

    /// One host pass, independent of source finish. No result cell, work charge,
    /// reservation or source code runs here. Unresolved storage is not retried.
    pub(crate) fn close(&self) -> bool {
        let mut slots = self.slots.borrow_mut();
        for index in (0..slots.len()).rev() {
            Self::destroy(&mut slots, index);
        }
        slots.iter().all(|slot| slot.raw.address.is_none())
    }

    pub(crate) fn view(
        self: &Rc<Self>,
        activation: usize,
        ty: &Type,
        kind: NativeOwnerViewKind,
        completion: Option<&NativeOwnerGuard>,
        work: &mut TypeWorkBudget,
    ) -> Result<NativeOwnerDependency, NativeOwnerAdmissionError> {
        let slots = self.slots.borrow();
        pay(work, slots.len())?;
        let mut selected = None;
        for (index, slot) in slots.iter().enumerate() {
            let Some(authority) = &slot.authority else {
                continue;
            };
            if authority.activation != activation || slot.raw.address.is_none() {
                continue;
            }
            let expected = match kind {
                NativeOwnerViewKind::State => &authority.state,
                NativeOwnerViewKind::Access => &authority.access,
            };
            let matches = crate::types::same_type_with_budget(expected, ty, work)
                .map_err(|()| NativeOwnerAdmissionError::Work)?;
            if !matches {
                continue;
            }
            if slot.quarantined
                && !completion.is_some_and(|guard| {
                    Rc::ptr_eq(self, &guard.storage)
                        && slots[guard.slot].dependencies.contains(&index)
                })
            {
                return Err(NativeOwnerAdmissionError::Authority);
            }
            if selected.replace(index).is_some() {
                return Err(NativeOwnerAdmissionError::Authority);
            }
        }
        let slot = selected.ok_or(NativeOwnerAdmissionError::Authority)?;
        Ok(NativeOwnerDependency {
            storage: Rc::clone(self),
            slot,
        })
    }

    /// A declared retained identity is already instantiated to its unique
    /// preceding activation. This retains a lifetime edge only; obtaining a
    /// native operand still requires the exact typed view and original call.
    pub(crate) fn declared_dependency(
        self: &Rc<Self>,
        activation: usize,
        work: &mut TypeWorkBudget,
    ) -> Result<NativeOwnerDependency, NativeOwnerAdmissionError> {
        let slots = self.slots.borrow();
        pay(work, slots.len())?;
        let mut selected = None;
        for (index, slot) in slots.iter().enumerate() {
            if slot
                .authority
                .as_ref()
                .is_none_or(|authority| authority.activation != activation)
            {
                continue;
            }
            if slot.raw.address.is_none() || slot.quarantined || selected.replace(index).is_some() {
                return Err(NativeOwnerAdmissionError::Authority);
            }
        }
        let slot = selected.ok_or(NativeOwnerAdmissionError::Authority)?;
        Ok(NativeOwnerDependency {
            storage: Rc::clone(self),
            slot,
        })
    }
}

impl Drop for NativeOwnerStorage {
    fn drop(&mut self) {
        let _ = self.close();
        let slots = self.slots.get_mut();
        for slot in slots {
            // No storage handle remains. An unresolved native closure must stay
            // allocated after incomplete host destruction; RawOwnerGuard may
            // not retry it or release a blocked parent. Disarm only that raw
            // callback. Typed authority and operand metadata still dispose via
            // their ordinary iterative owners, without leaking the slot table.
            slot.raw.address = None;
        }
    }
}

/// One non-Clone lifecycle token for the original slot. Addresses never enter
/// the Ash heap; copying this storage handle grants no invocation authority.
#[derive(Debug)]
pub(crate) struct NativeOwnerGuard {
    storage: Rc<NativeOwnerStorage>,
    slot: usize,
    owner: Arc<CheckedForeignOwner>,
    initialized_bytes: Option<usize>,
    bytes: Option<NativeByteCallbacks>,
}

impl NativeOwnerGuard {
    pub(crate) fn owner(&self) -> &Arc<CheckedForeignOwner> {
        &self.owner
    }
    pub(crate) fn completion_address(&self) -> Option<*mut core::ffi::c_void> {
        self.storage.slots.borrow()[self.slot]
            .raw
            .address
            .map(NonNull::as_ptr)
    }
    pub(crate) fn retains(&self, dependency: &NativeOwnerDependency) -> bool {
        Rc::ptr_eq(&self.storage, &dependency.storage)
            && self.storage.slots.borrow()[self.slot]
                .dependencies
                .contains(&dependency.slot)
    }
    pub(crate) fn initialized_bytes(&self) -> Option<usize> {
        self.initialized_bytes
    }
    pub(crate) fn ordinary_live(&self) -> bool {
        let slots = self.storage.slots.borrow();
        let slot = &slots[self.slot];
        slot.raw.address.is_some() && !slot.quarantined
    }
    pub(crate) fn quarantine(&mut self) {
        self.initialized_bytes = None;
        NativeOwnerStorage::quarantine(&mut self.storage.slots.borrow_mut(), self.slot);
    }
    pub(crate) fn preflight_dependents(
        &self,
        work: &mut TypeWorkBudget,
    ) -> Result<bool, NativeOwnerAdmissionError> {
        let slots = self.storage.slots.borrow();
        pay(work, 1)?;
        Ok(NativeOwnerStorage::has_dependents(&slots, self.slot))
    }
    pub(crate) fn byte_access(&self, index: usize) -> Option<NativeByteAccess<'_>> {
        if !self.ordinary_live() {
            return None;
        }
        self.completion_byte_access(index)
    }

    /// Only the evaluator's exact original Finish occurrence may request this
    /// view. Quarantine revokes ordinary access, while required completion can
    /// still borrow the same physically live initialized owner before consumption.
    pub(crate) fn completion_byte_access(&self, index: usize) -> Option<NativeByteAccess<'_>> {
        if self.owner.owner().representation()
            != crate::foreign::source_contract::PreparedAddressRepresentation::Bytes
            || index >= self.initialized_bytes?
        {
            return None;
        }
        Some(NativeByteAccess {
            _guard: self,
            address: self.storage.slots.borrow()[self.slot].raw.address?,
            index,
            callbacks: self.bytes?,
        })
    }

    /// Invoke the independently admitted source finishing member. Its declared
    /// total disposition is recorded before any ordinary report construction.
    #[cfg(test)]
    pub(crate) fn finish(
        self,
        callback: NativeOwnerTeardownCallback,
        consumes: bool,
        operands: &[NativeOwnerOperand],
        blocked: bool,
    ) -> NativeOwnerDisposition {
        self.finish_with_plan(
            &NativeOwnerDestruction::Void { callback, consumes },
            operands,
            blocked,
        )
        .0
    }

    pub(crate) fn finish_with_plan(
        mut self,
        plan: &NativeOwnerDestruction,
        operands: &[NativeOwnerOperand],
        blocked: bool,
    ) -> (NativeOwnerDisposition, Option<NativeOwnerStatus>) {
        if blocked {
            self.quarantine();
            return (NativeOwnerDisposition::Blocked(self), None);
        }
        let (consumes, status);
        {
            let mut slots = self.storage.slots.borrow_mut();
            let slot = &mut slots[self.slot];
            let _address = slot.raw.address.expect("admitted live owner");
            (consumes, status) = plan.invoke(operands);
            if consumes {
                NativeOwnerStorage::record_consumed(&mut slots, self.slot);
            } else {
                NativeOwnerStorage::quarantine(&mut slots, self.slot);
            }
        }
        self.initialized_bytes = None;
        if consumes {
            (
                NativeOwnerDisposition::Consumed(Arc::clone(&self.owner)),
                status,
            )
        } else {
            (NativeOwnerDisposition::Retained(self), status)
        }
    }
}

impl Drop for NativeOwnerGuard {
    fn drop(&mut self) {
        self.storage.abandon(self.slot);
    }
}

/// Native disposition recorded without a reusable native callback. A retained
/// result carries the same unique lifecycle token, never a newly acquired owner.
#[derive(Debug)]
pub(crate) enum NativeOwnerDisposition {
    Consumed(Arc<CheckedForeignOwner>),
    Retained(NativeOwnerGuard),
    Blocked(NativeOwnerGuard),
}

impl NativeOwnerDisposition {
    pub(crate) fn owner(&self) -> &Arc<CheckedForeignOwner> {
        match self {
            Self::Consumed(owner) => owner,
            Self::Retained(guard) | Self::Blocked(guard) => guard.owner(),
        }
    }
    pub(crate) fn is_retained(&self) -> bool {
        !matches!(self, Self::Consumed(_))
    }
    pub(crate) fn is_blocked(&self) -> bool {
        matches!(self, Self::Blocked(_))
    }
    pub(crate) fn into_retained(self) -> Option<NativeOwnerGuard> {
        match self {
            Self::Consumed(_) => None,
            Self::Retained(guard) | Self::Blocked(guard) => Some(guard),
        }
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
    #[cfg(test)]
    pub(crate) fn new(
        owner: Arc<CheckedForeignOwner>,
        teardown: NativeOwnerTeardownCallback,
    ) -> Self {
        Self::in_storage(
            owner,
            teardown,
            true,
            1,
            0,
            Rc::new(NativeOwnerStorage::default()),
        )
        .expect("injected standalone guard storage")
    }

    #[cfg(test)]
    pub(crate) fn in_storage(
        owner: Arc<CheckedForeignOwner>,
        teardown: NativeOwnerTeardownCallback,
        destructor_consumes: bool,
        count: usize,
        current: usize,
        storage: Rc<NativeOwnerStorage>,
    ) -> Result<Self, ()> {
        Self::in_storage_plan(
            owner,
            NativeOwnerDestruction::Void {
                callback: teardown,
                consumes: destructor_consumes,
            },
            count,
            current,
            storage,
        )
    }

    pub(crate) fn in_storage_plan(
        owner: Arc<CheckedForeignOwner>,
        plan: NativeOwnerDestruction,
        count: usize,
        current: usize,
        storage: Rc<NativeOwnerStorage>,
    ) -> Result<Self, ()> {
        let slot = storage.reserve(plan, count, current)?;
        Ok(Self {
            guard: NativeOwnerGuard {
                storage,
                slot,
                owner,
                initialized_bytes: None,
                bytes: None,
            },
            prepared_initialized_bytes: None,
        })
    }

    pub(crate) fn prepare_byte_callbacks(&mut self, callbacks: NativeByteCallbacks) {
        self.guard.bytes = Some(callbacks);
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn prepare_authority(
        &mut self,
        activation: usize,
        state: IterativeTypeOwner,
        access: IterativeTypeOwner,
        dependencies: Vec<NativeOwnerDependency>,
        destruction: Vec<NativeOwnerOperand>,
        work: &mut TypeWorkBudget,
    ) -> Result<(), NativeOwnerAdmissionError> {
        let mut slots = self.guard.storage.slots.borrow_mut();
        let index = self.guard.slot;
        if slots[index].raw.address.is_some()
            || slots[index].authority.is_some()
            || destruction.len() != slots[index].raw.operands.len()
        {
            return Err(NativeOwnerAdmissionError::Authority);
        }
        let mut direct = Vec::new();
        let mut closure = Vec::new();
        pay(work, dependencies.len())?;
        direct
            .try_reserve_exact(dependencies.len())
            .map_err(|_| NativeOwnerAdmissionError::Storage(dependencies.len()))?;
        for dependency in dependencies {
            if !Rc::ptr_eq(&dependency.storage, &self.guard.storage)
                || dependency.slot >= index
                || slots[dependency.slot].raw.address.is_none()
                || slots[dependency.slot].quarantined
            {
                return Err(NativeOwnerAdmissionError::Authority);
            }
            pay(work, direct.len())?;
            if direct.contains(&dependency.slot) {
                continue;
            }
            slots[dependency.slot]
                .live_dependents
                .checked_add(1)
                .ok_or(NativeOwnerAdmissionError::Authority)?;
            direct.push(dependency.slot);
            let inherited = &slots[dependency.slot].closure;
            let requested = inherited
                .len()
                .checked_add(1)
                .ok_or(NativeOwnerAdmissionError::Storage(usize::MAX))?;
            pay(work, requested)?;
            closure
                .try_reserve(requested)
                .map_err(|_| NativeOwnerAdmissionError::Storage(requested))?;
            for inherited in std::iter::once(&dependency.slot).chain(inherited) {
                pay(work, closure.len())?;
                if !closure.contains(inherited) {
                    closure.push(*inherited);
                }
            }
        }
        let slot = &mut slots[index];
        slot.authority = Some(NativeOwnerSlotAuthority {
            activation,
            state,
            access,
        });
        slot.dependencies = direct.into_boxed_slice();
        slot.closure = closure.into_boxed_slice();
        slot.raw.operands = destruction;
        Ok(())
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
    pub fn returned(self, address: *mut core::ffi::c_void) -> NativeOwnerCallReturned {
        {
            let mut slots = self.guard.storage.slots.borrow_mut();
            let index = self.guard.slot;
            slots[index].raw.address = NonNull::new(address);
            if slots[index].raw.address.is_some() {
                for position in 0..slots[index].dependencies.len() {
                    let dependency = slots[index].dependencies[position];
                    slots[dependency].live_dependents += 1;
                }
            }
        }
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
        if self.guard.storage.slots.borrow()[self.guard.slot]
            .raw
            .address
            .is_some()
        {
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
        let nonnull = self.guard.storage.slots.borrow()[self.guard.slot]
            .raw
            .address
            .is_some();
        nonnull.then_some(self.guard)
    }
}

#[cfg(test)]
mod tests {
    use super::RawOwnerGuard;
    use std::ptr::NonNull;
    use std::sync::atomic::{AtomicUsize, Ordering};

    static DESTRUCTIONS: AtomicUsize = AtomicUsize::new(0);

    thread_local! {
        static HOST_ORDER: std::cell::RefCell<Vec<usize>> = const { std::cell::RefCell::new(Vec::new()) };
        static SOURCE_FINISHES: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
    }

    fn model_destroy(arguments: &[super::NativeOwnerOperand]) {
        let super::NativeOwnerOperand::Address(address) = arguments[0] else {
            panic!("typed owner address");
        };
        HOST_ORDER.with(|order| order.borrow_mut().push(address as usize));
    }

    fn model_retain(_: &[super::NativeOwnerOperand]) {
        SOURCE_FINISHES.set(SOURCE_FINISHES.get() + 1);
    }

    fn original_owner() -> std::sync::Arc<crate::foreign::source_owner::CheckedForeignOwner> {
        let path = std::env::temp_dir().join(format!("ash-owner-store-{}", std::process::id()));
        std::fs::create_dir(&path).unwrap();
        std::fs::write(
            path.join("owner.ash"),
            include_str!("../../tests/fixtures/source-owner/owner.ash"),
        )
        .unwrap();
        std::fs::write(path.join("entry.ash"), "import owner as Owner\nmain : Unit -> Owner.Scope<Unit, Unit, Int>\nmain () = resource Owner.Probe<{}, Fresh, {}> owner = 42 {\n    Owner.read owner\n}\n").unwrap();
        let compiled = crate::driver::compile_path(crate::driver::RunConfiguration {
            entry: path.join("entry.ash"),
            roots: crate::module::ModuleRoots::empty(),
        })
        .unwrap();
        let (program, _) = compiled.effect_build_input().unwrap();
        let mut pending = vec![program.root()];
        let owner = loop {
            let node = program.node(pending.pop().unwrap()).unwrap();
            if let crate::core::EffectExprKind::Operation(
                crate::core::EffectOperation::SourceResourceScope(scope),
            ) = &node.kind
            {
                break std::sync::Arc::clone(&scope.header().owner);
            }
            pending
                .extend((0..node.kind.child_count()).filter_map(|index| node.kind.child_at(index)));
        };
        std::fs::remove_dir_all(path).unwrap();
        owner
    }

    // These injected slots use distinct sentinel addresses and deliberately
    // equal value types for donor keys. They do not call or dereference C and
    // do not replace source/Core/native contract evidence.
    fn model_ready(
        owner: &std::sync::Arc<crate::foreign::source_owner::CheckedForeignOwner>,
        storage: &std::rc::Rc<super::NativeOwnerStorage>,
        activation: usize,
        dependencies: Vec<super::NativeOwnerDependency>,
        work: &mut crate::types::TypeWorkBudget,
    ) -> Result<super::NativeOwnerGuardReady, super::NativeOwnerAdmissionError> {
        let mut ready = super::NativeOwnerGuardReady::in_storage(
            std::sync::Arc::clone(owner),
            model_destroy,
            true,
            1,
            0,
            std::rc::Rc::clone(storage),
        )
        .unwrap();
        ready.prepare_authority(
            activation,
            crate::types::IterativeTypeOwner::new(crate::types::Type::Int),
            crate::types::IterativeTypeOwner::new(crate::types::Type::Bool),
            dependencies,
            vec![super::NativeOwnerOperand::Address(std::ptr::null_mut())],
            work,
        )?;
        Ok(ready)
    }

    #[test]
    fn injected_owner_dependencies_preserve_exact_work_affinity_quarantine_and_once_only_order() {
        use super::{NativeOwnerAdmissionError, NativeOwnerDisposition, NativeOwnerViewKind};
        use crate::types::{Type, TypeWorkBudget};
        let owner = original_owner();
        // One dependency costs its original direct edge and closure entry.
        // A one-short failure leaves the parent ready and invokes no child.
        {
            HOST_ORDER.with(|order| order.borrow_mut().clear());
            let storage = std::rc::Rc::new(super::NativeOwnerStorage::default());
            let parent = model_ready(
                &owner,
                &storage,
                0,
                Vec::new(),
                &mut TypeWorkBudget::unbounded(),
            )
            .unwrap()
            .returned(std::ptr::without_provenance_mut::<u8>(1).cast())
            .record()
            .into_guard()
            .unwrap();
            let dependency = storage
                .declared_dependency(0, &mut TypeWorkBudget::unbounded())
                .unwrap();
            let mut short = TypeWorkBudget::with_limit(38);
            short.charge(37).unwrap();
            assert!(matches!(
                model_ready(&owner, &storage, 1, vec![dependency], &mut short),
                Err(NativeOwnerAdmissionError::Work)
            ));
            assert_eq!(short.used(), 38);
            assert!(
                !parent
                    .preflight_dependents(&mut TypeWorkBudget::with_limit(1))
                    .unwrap()
            );
            HOST_ORDER.with(|order| assert!(order.borrow().is_empty()));
            drop(parent);
            HOST_ORDER.with(|order| assert_eq!(&*order.borrow(), &[1]));
        }
        for _ in 0..2 {
            HOST_ORDER.with(|order| order.borrow_mut().clear());
            SOURCE_FINISHES.set(0);
            let storage = std::rc::Rc::new(super::NativeOwnerStorage::default());
            let parent = model_ready(
                &owner,
                &storage,
                0,
                Vec::new(),
                &mut TypeWorkBudget::unbounded(),
            )
            .unwrap()
            .returned(std::ptr::without_provenance_mut::<u8>(1).cast())
            .record()
            .into_guard()
            .unwrap();
            for (activation, ty, kind) in [
                (0, Type::Bool, NativeOwnerViewKind::State),
                (0, Type::Int, NativeOwnerViewKind::Access),
                (99, Type::Int, NativeOwnerViewKind::State),
            ] {
                assert!(matches!(
                    storage.view(
                        activation,
                        &ty,
                        kind,
                        None,
                        &mut TypeWorkBudget::unbounded()
                    ),
                    Err(NativeOwnerAdmissionError::Authority)
                ));
            }
            let dependency = storage
                .view(
                    0,
                    &Type::Bool,
                    NativeOwnerViewKind::Access,
                    None,
                    &mut TypeWorkBudget::unbounded(),
                )
                .unwrap();
            let mut exact = TypeWorkBudget::with_limit(39);
            exact.charge(37).unwrap();
            let ready = model_ready(&owner, &storage, 1, vec![dependency], &mut exact).unwrap();
            assert_eq!(exact.remaining(), 0);
            assert!(
                !parent
                    .preflight_dependents(&mut TypeWorkBudget::with_limit(1))
                    .unwrap()
            );
            let child = ready
                .returned(std::ptr::without_provenance_mut::<u8>(2).cast())
                .record()
                .into_guard()
                .unwrap();
            let mut zero = TypeWorkBudget::with_limit(0);
            assert!(matches!(
                parent.preflight_dependents(&mut zero),
                Err(NativeOwnerAdmissionError::Work)
            ));
            assert_eq!(zero.used(), 0);
            assert!(
                parent
                    .preflight_dependents(&mut TypeWorkBudget::with_limit(1))
                    .unwrap()
            );
            let child = child
                .finish(model_retain, false, &[], false)
                .into_retained()
                .unwrap();
            assert_eq!(SOURCE_FINISHES.get(), 1);
            assert!(!parent.ordinary_live());
            assert!(!child.ordinary_live());
            assert!(
                storage
                    .declared_dependency(0, &mut TypeWorkBudget::unbounded())
                    .is_err()
            );
            assert!(
                storage
                    .view(
                        0,
                        &Type::Int,
                        NativeOwnerViewKind::State,
                        None,
                        &mut TypeWorkBudget::unbounded()
                    )
                    .is_err()
            );
            let completion = storage
                .view(
                    0,
                    &Type::Int,
                    NativeOwnerViewKind::State,
                    Some(&child),
                    &mut TypeWorkBudget::unbounded(),
                )
                .unwrap();
            assert!(child.retains(&completion));
            let donor = model_ready(
                &owner,
                &storage,
                9,
                Vec::new(),
                &mut TypeWorkBudget::unbounded(),
            )
            .unwrap()
            .returned(std::ptr::without_provenance_mut::<u8>(3).cast())
            .record()
            .into_guard()
            .unwrap();
            let donor_view = storage
                .view(
                    9,
                    &Type::Int,
                    NativeOwnerViewKind::State,
                    None,
                    &mut TypeWorkBudget::unbounded(),
                )
                .unwrap();
            assert!(
                !child.retains(&donor_view),
                "a same-typed donor grants no recorded dependency edge"
            );
            let parent = parent.finish(model_destroy, true, &[], true);
            assert!(matches!(parent, NativeOwnerDisposition::Blocked(_)));
            HOST_ORDER.with(|order| assert!(order.borrow().is_empty()));
            let parent = parent.into_retained().unwrap();
            drop(donor);
            assert!(storage.close());
            assert!(storage.close());
            HOST_ORDER.with(|order| assert_eq!(&*order.borrow(), &[3, 2, 1]));
            assert!(
                storage
                    .view(
                        0,
                        &Type::Int,
                        NativeOwnerViewKind::State,
                        Some(&child),
                        &mut TypeWorkBudget::unbounded()
                    )
                    .is_err(),
                "consumed activation is stale even for completion"
            );
            drop(child);
            drop(parent);
            assert_eq!(SOURCE_FINISHES.get(), 1);
            HOST_ORDER.with(|order| assert_eq!(&*order.borrow(), &[3, 2, 1]));
        }
    }

    fn destroy(arguments: &[super::NativeOwnerOperand]) {
        let [super::NativeOwnerOperand::Address(address)] = arguments else {
            panic!("admitted raw owner address");
        };
        let address = *address;
        assert_eq!(address, std::ptr::dangling_mut::<u8>().cast());
        DESTRUCTIONS.fetch_add(1, Ordering::SeqCst);
    }

    #[test]
    fn raw_guard_destroys_only_nonnull_storage_and_consumption_cannot_replay() {
        DESTRUCTIONS.store(0, Ordering::SeqCst);
        drop(RawOwnerGuard::empty(destroy, 1, 0).unwrap());
        assert_eq!(DESTRUCTIONS.load(Ordering::SeqCst), 0);

        let mut guard = RawOwnerGuard::empty(destroy, 1, 0).unwrap();
        guard.address = NonNull::new(std::ptr::dangling_mut::<u8>().cast());
        guard.consume();
        assert_eq!(DESTRUCTIONS.load(Ordering::SeqCst), 1);
        drop(guard);
        assert_eq!(DESTRUCTIONS.load(Ordering::SeqCst), 1);

        let mut unpublished = RawOwnerGuard::empty(destroy, 1, 0).unwrap();
        unpublished.address = NonNull::new(std::ptr::dangling_mut::<u8>().cast());
        drop(unpublished);
        assert_eq!(DESTRUCTIONS.load(Ordering::SeqCst), 2);
    }
}
