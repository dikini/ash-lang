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
    /// Pay new selected checked-root lookups before source preflight. Legacy
    /// slots retain their existing tariff; this grants no entry permission.
    pub(crate) fn pay_group_checks(&self, count: usize, work: &mut TypeWorkBudget)
        -> Result<(), NativeOwnerAdmissionError> {
        if self.storage.slots.borrow()[self.slot].checked_group_root.is_some() {
            pay(work, count.checked_mul(2).ok_or(NativeOwnerAdmissionError::Work)?)?;
        }
        Ok(())
    }

    pub(crate) fn same_slot(&self, other: &Self) -> bool {
        Rc::ptr_eq(&self.storage, &other.storage) && self.slot == other.slot
    }
    pub(crate) fn checked_boundary(
        &self, work: &mut TypeWorkBudget,
    ) -> Result<NativeOwnerBoundary, NativeOwnerAdmissionError> {
        let slots = self.storage.slots.borrow();
        if slots[self.slot].checked.is_none() {
            return Err(NativeOwnerAdmissionError::Authority);
        }
        pay(work, 1)?;
        Ok(NativeOwnerBoundary { storage: Rc::clone(&self.storage), slot: self.slot })
    }
    pub(crate) fn address(&self) -> Option<*mut core::ffi::c_void> {
        let slots = self.storage.slots.borrow();
        if slots[self.slot].checked_group_root.is_some_and(|root| slots[root].checked_group_denied) {
            return None;
        }
        slots[self.slot].raw_address().map(NonNull::as_ptr)
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
    #[cfg(any(test, ash_checked_owner_root = "v1"))]
    CheckedLeaf,
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
impl NativeOwnerStatus {
    /// Fixed-size observation only; unreadable or invalid output is absence,
    /// never a fabricated numeric status. No allocation or narrowing occurs.
    pub(crate) fn independent(self) -> Option<i128> {
        if !self.readable || !self.valid { return None; }
        match self.reply {
            NativeScalarReply::Void => None,
            NativeScalarReply::Scalar(value) => match value {
                NativeScalarValue::I8(value) => Some(i128::from(value)),
                NativeScalarValue::U8(value) => Some(i128::from(value)),
                NativeScalarValue::I32(value) => Some(i128::from(value)),
                NativeScalarValue::U32(value) => Some(i128::from(value)),
                NativeScalarValue::I64(value) => Some(i128::from(value)),
                NativeScalarValue::U64(value) => Some(i128::from(value)),
                NativeScalarValue::USize(value) => Some(value as i128),
                NativeScalarValue::FunctionAddressAllBitsOne => None,
            },
        }
    }
}

fn observed_scalar_status(reply: NativeScalarReply) -> Option<i128> {
    match reply {
        NativeScalarReply::Void => None,
        NativeScalarReply::Scalar(value) => match value {
            NativeScalarValue::I8(value) => Some(i128::from(value)),
            NativeScalarValue::U8(value) => Some(i128::from(value)),
            NativeScalarValue::I32(value) => Some(i128::from(value)),
            NativeScalarValue::U32(value) => Some(i128::from(value)),
            NativeScalarValue::I64(value) => Some(i128::from(value)),
            NativeScalarValue::U64(value) => Some(i128::from(value)),
            NativeScalarValue::USize(value) => Some(value as i128),
            NativeScalarValue::FunctionAddressAllBitsOne => None,
        },
    }
}

impl NativeOwnerDestruction {
    // This exact descriptor and its finite traversal were admitted before C.
    // No conversion, allocation, reservation or caller charge occurs here.
    pub(crate) fn invoke(
        &self,
        operands: &[NativeOwnerOperand],
    ) -> (bool, Option<NativeOwnerStatus>) {
        match self {
            #[cfg(any(test, ash_checked_owner_root = "v1"))]
            Self::CheckedLeaf => unreachable!("opaque checked release never uses a raw callback"),
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
    /// A private, null-initialized output slot supplied by the typed wrapper.
    OwnerOutput,
    /// A private initialized pointer-output slot, separate from the owner slot.
    OffsetOutput,
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
    #[cfg(any(test, ash_checked_owner_root = "v1"))]
    leaf: Option<CheckedLeafBacking>,
    quarantined: bool,
    // Stable indexes into this never-removed arena; no owner/member backedges.
    // Legacy slots have no checked group. Only the root's denial bit is read.
    checked_group_root: Option<usize>,
    checked_group_denied: bool,
    host_attempted: bool,
    authority: Option<NativeOwnerSlotAuthority>,
    dependencies: Box<[usize]>,
    closure: Box<[usize]>,
    live_dependents: usize,
    checked: Option<crate::foreign::checked_control::RuntimeBoundary>,
    closing_status: Option<i128>,
    // Optional numeric status of the latest admitted native observation, not
    // a sticky last-number register. Source bookkeeping/refusal never writes it.
    last_observed_status: Option<i128>,
}

#[cfg(any(test, ash_checked_owner_root = "v1"))]
#[derive(Debug)]
enum CheckedLeafBacking {
    Cell(super::super::checked_leaf_transport::OwnerCell),
    Consumed,
}
impl NativeOwnerSlot {
    fn physically_live(&self) -> bool {
        #[cfg(any(test, ash_checked_owner_root = "v1"))]
        if let Some(leaf) = &self.leaf {
            return match leaf {
                CheckedLeafBacking::Cell(cell) => cell.is_occupied(),
                CheckedLeafBacking::Consumed => false,
            };
        }
        self.raw.address.is_some()
    }
    fn raw_address(&self) -> Option<NonNull<core::ffi::c_void>> {
        #[cfg(any(test, ash_checked_owner_root = "v1"))]
        if self.leaf.is_some() { return None; }
        self.raw.address
    }
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
        #[cfg(any(test, ash_checked_owner_root = "v1"))]
        let leaf = if matches!(teardown, NativeOwnerDestruction::CheckedLeaf) {
            if count != 0 || current != 0 { return Err(()); }
            Some(CheckedLeafBacking::Cell(super::super::checked_leaf_transport::OwnerCell::vacant()))
        } else { None };
        slots.push(NativeOwnerSlot {
            raw: RawOwnerGuard::with_plan(teardown, count, current)?,
            #[cfg(any(test, ash_checked_owner_root = "v1"))]
            leaf,
            quarantined: false,
            checked_group_root: None,
            checked_group_denied: false,
            host_attempted: false,
            authority: None,
            dependencies: Box::new([]),
            closure: Box::new([]),
            live_dependents: 0,
            checked: None,
            closing_status: None,
            last_observed_status: None,
        });
        Ok(index)
    }

    fn validated_group_root(
        slots: &[NativeOwnerSlot], index: usize,
    ) -> Result<Option<usize>, NativeOwnerAdmissionError> {
        let slot = slots.get(index).ok_or(NativeOwnerAdmissionError::Authority)?;
        if let Some(root) = slot.checked_group_root
            && (root > index
                || slots.get(root).is_none_or(|slot| slot.checked_group_root != Some(root)))
        {
            return Err(NativeOwnerAdmissionError::Authority);
        }
        Ok(slot.checked_group_root)
    }

    fn denied(slots: &[NativeOwnerSlot], index: usize) -> bool {
        let slot = &slots[index];
        slot.quarantined || slot.checked_group_root
            .is_some_and(|root| slots[root].checked_group_denied)
    }

    fn entry_allowed(
        slots: &mut [NativeOwnerSlot], index: usize, require_live: bool,
    ) -> Result<(), NativeOwnerAdmissionError> {
        if slots[index].checked_group_root.is_none() {
            return Ok(()); // legacy entry keeps its existing checks/tariff
        }
        if let Some(control) = &mut slots[index].checked {
            control.check_group_entry().map_err(control_error)?;
        }
        if Self::denied(slots, index) || (require_live && !slots[index].physically_live()) {
            return Err(NativeOwnerAdmissionError::Authority);
        }
        Ok(())
    }

    fn sync_group_denial(slots: &mut [NativeOwnerSlot], index: usize) {
        if Self::denied(slots, index)
            && let Some(control) = &mut slots[index].checked
        {
            // Denial changes no native observation or K. The existing owner's
            // later structural finish selects its own synthetic witness.
            control.quarantine();
        }
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
        if let Some(checked) = &mut slots[index].checked {
            checked.quarantine();
        }
        for position in 0..slots[index].closure.len() {
            let dependency = slots[index].closure[position];
            slots[dependency].quarantined = true;
            if let Some(checked) = &mut slots[dependency].checked {
                checked.quarantine();
            }
        }
    }

    fn destroy(slots: &mut [NativeOwnerSlot], index: usize) {
        if slots[index].checked_group_root.is_some_and(|root| slots[root].checked_group_denied)
            || slots[index].host_attempted || Self::has_dependents(slots, index) {
            return;
        }
        let slot = &mut slots[index];
        #[cfg(any(test, ash_checked_owner_root = "v1"))]
        if slot.leaf.is_some() {
            // Physical checked backing never enters an implicit destructor.
            // Keep it unresolved for the pre-funded host transfer/report path.
            if slot.physically_live() {
                slot.quarantined = true;
                if let Some(checked) = &mut slot.checked { checked.output_failed(); }
            }
            return;
        }
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
        if !Self::denied(&slots, index) {
            Self::destroy(&mut slots, index);
        }
    }

    /// One host pass, independent of source finish. No result cell, work charge,
    /// reservation or source code runs here. Unresolved storage is not retried.
    pub(crate) fn close(&self) -> bool {
        let mut slots = self.slots.borrow_mut();
        for slot in slots.iter_mut() {
            if let Some(checked) = &mut slot.checked {
                checked.output_failed();
            }
        }
        for index in (0..slots.len()).rev() {
            Self::destroy(&mut slots, index);
        }
        slots.iter().all(|slot| !slot.physically_live())
    }

    /// Exact typed State lookup only for a direct conservative-denial call.
    /// The evaluator still proves original Current/Enclosing membership. This
    /// receipt exposes no address after denial and grants no ordinary access.
    pub(crate) fn denial_dependency(
        self: &Rc<Self>, activation: usize, ty: &Type, work: &mut TypeWorkBudget,
    ) -> Result<NativeOwnerDependency, NativeOwnerAdmissionError> {
        let slots = self.slots.borrow();
        pay(work, slots.len())?;
        let mut selected = None;
        for (index, slot) in slots.iter().enumerate() {
            let Some(authority) = &slot.authority else { continue; };
            if authority.activation != activation || !slot.physically_live() { continue; }
            if !crate::types::same_type_with_budget(&authority.state, ty, work)
                .map_err(|()| NativeOwnerAdmissionError::Work)? { continue; }
            pay(work, 2)?;
            NativeOwnerStorage::validated_group_root(&slots, index)?
                .ok_or(NativeOwnerAdmissionError::Authority)?;
            if selected.replace(index).is_some() { return Err(NativeOwnerAdmissionError::Authority); }
        }
        let slot = selected.ok_or(NativeOwnerAdmissionError::Authority)?;
        pay(work, 1)?;
        Ok(NativeOwnerDependency { storage: Rc::clone(self), slot })
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
            if authority.activation != activation || !slot.physically_live() {
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
            if slot.checked_group_root.is_some() { pay(work, 2)?; }
            if Self::denied(&slots, index)
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
            if slot.checked_group_root.is_some() { pay(work, 2)?; }
            if !slot.physically_live() || Self::denied(&slots, index) || selected.replace(index).is_some() {
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
    #[cfg(any(test, ash_checked_owner_root = "v1"))]
    backing: GuardBacking,
    storage: Rc<NativeOwnerStorage>,
    slot: usize,
    owner: Arc<CheckedForeignOwner>,
    initialized_bytes: Option<usize>,
    bytes: Option<NativeByteCallbacks>,
}

#[cfg(any(test, ash_checked_owner_root = "v1"))]
#[derive(Debug)]
enum GuardBacking { Legacy, CheckedLeaf }

impl NativeOwnerGuard {
    /// Pay new selected checked-root lookups before source preflight. Legacy
    /// slots retain their existing tariff; this grants no entry permission.
    pub(crate) fn pay_group_checks(&self, count: usize, work: &mut TypeWorkBudget)
        -> Result<(), NativeOwnerAdmissionError> {
        if self.storage.slots.borrow()[self.slot].checked_group_root.is_some() {
            pay(work, count.checked_mul(2).ok_or(NativeOwnerAdmissionError::Work)?)?;
        }
        Ok(())
    }

    pub(crate) fn shared_group_denied(&self, work: &mut TypeWorkBudget)
        -> Result<bool, NativeOwnerAdmissionError> {
        let slots = self.storage.slots.borrow();
        if let Some(root) = slots[self.slot].checked_group_root {
            pay(work, 2)?;
            Ok(slots[root].checked_group_denied)
        } else { Ok(false) }
    }
    pub(crate) fn owner(&self) -> &Arc<CheckedForeignOwner> {
        &self.owner
    }
    pub(crate) fn physically_live(&self) -> bool {
        self.storage.slots.borrow()[self.slot].physically_live()
    }
    pub(crate) fn completion_address(&self) -> Option<*mut core::ffi::c_void> {
        let slots = self.storage.slots.borrow();
        if slots[self.slot].checked_group_root.is_some_and(|root| slots[root].checked_group_denied) {
            return None;
        }
        slots[self.slot].raw_address().map(NonNull::as_ptr)
    }
    pub(crate) fn retained_dependency_count(&self) -> usize {
        self.storage.slots.borrow()[self.slot].dependencies.len()
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
        slot.physically_live() && !NativeOwnerStorage::denied(&slots, self.slot)
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
        let address = self.completion_address()?;
        Some(NativeByteAccess {
            _guard: self,
            address: NonNull::new(address)?,
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

    /// Consume the preflighted one-shot decision before dispatch. A synthetic
    /// return retains the exact physical owner and closing witness, and never
    /// invokes the native plan or fabricates a scalar status.
    pub(crate) fn finish_checked_admitted(
        mut self,
        plan: &NativeOwnerDestruction,
        operands: &[NativeOwnerOperand],
        blocked: bool,
    ) -> Result<(NativeOwnerDisposition, Option<NativeOwnerStatus>), NativeOwnerAdmissionError> {
        #[cfg(any(test, ash_checked_owner_root = "v1"))]
        if matches!(plan, NativeOwnerDestruction::CheckedLeaf) {
            if !operands.is_empty() { return Err(NativeOwnerAdmissionError::Authority); }
            return self.finish_checked_leaf(blocked);
        }
        let entry = match self.begin_checked_finish_entry() {
            Ok(Some(entry)) => entry,
            Ok(None) => {
                self.quarantine();
                return Err(NativeOwnerAdmissionError::Authority);
            }
            Err(error) => {
                self.quarantine();
                return Err(error);
            }
        };
        match entry {
            crate::foreign::checked_control::FinishEntry::NativeReady => {
                Ok(self.finish_with_plan(plan, operands, blocked))
            }
            crate::foreign::checked_control::FinishEntry::Synthetic(witness) => Ok((
                NativeOwnerDisposition::Synthetic { guard: self, witness },
                None,
            )),
        }
    }

    #[cfg(any(test, ash_checked_owner_root = "v1"))]
    fn finish_checked_leaf(
        self,
        blocked: bool,
    ) -> Result<(NativeOwnerDisposition, Option<NativeOwnerStatus>), NativeOwnerAdmissionError> {
        use super::super::checked_leaf_transport::FreeObservation;
        let mut slots = self.storage.slots.try_borrow_mut()
            .map_err(|_| NativeOwnerAdmissionError::Authority)?;
        NativeOwnerStorage::sync_group_denial(&mut slots, self.slot);
        let blocked = blocked || slots[self.slot].checked_group_root.is_some_and(|root| slots[root].checked_group_denied);
        let slot = slots.get_mut(self.slot).ok_or(NativeOwnerAdmissionError::Authority)?;
        if !slot.physically_live() || !slot.dependencies.is_empty() {
            return Err(NativeOwnerAdmissionError::Authority);
        }
        let NativeOwnerSlot { leaf, checked, quarantined, closing_status, last_observed_status, .. } = slot;
        let control = checked.as_mut().ok_or(NativeOwnerAdmissionError::Authority)?;
        let entry = control.begin_finish_entry_with_blocked(blocked).map_err(control_error)?;
        match entry {
            crate::foreign::checked_control::FinishEntry::Synthetic(witness) => {
                drop(slots);
                Ok((NativeOwnerDisposition::Synthetic { guard: self, witness }, None))
            }
            crate::foreign::checked_control::FinishEntry::NativeReady => {
                let Some(CheckedLeafBacking::Cell(cell)) = leaf.take() else {
                    control.output_failed();
                    return Err(NativeOwnerAdmissionError::Authority);
                };
                *leaf = Some(CheckedLeafBacking::Consumed);
                match cell.free() {
                    FreeObservation::Returned(_) => {
                        // Both fields are reserved observations. No storage
                        // reborrow, allocation or source construction follows C.
                        *closing_status = None;
                        *last_observed_status = None;
                        control.finished(true);
                    }
                    FreeObservation::NoOwner => {
                        *quarantined = true;
                        control.output_failed();
                        return Err(NativeOwnerAdmissionError::Authority);
                    }
                }
                drop(slots);
                Ok((NativeOwnerDisposition::Consumed(Arc::clone(&self.owner)), None))
            }
        }
    }

    pub(crate) fn finish_with_plan(
        mut self,
        plan: &NativeOwnerDestruction,
        operands: &[NativeOwnerOperand],
        blocked: bool,
    ) -> (NativeOwnerDisposition, Option<NativeOwnerStatus>) {
        let denied = {
            let slots = self.storage.slots.borrow();
            slots[self.slot].checked_group_root.is_some()
                && NativeOwnerStorage::denied(&slots, self.slot)
        };
        if blocked || denied {
            self.quarantine();
            return (NativeOwnerDisposition::Blocked(self), None);
        }
        let (consumes, status);
        {
            let mut slots = self.storage.slots.borrow_mut();
            let slot = &mut slots[self.slot];
            let _address = slot.raw.address.expect("admitted live owner");
            (consumes, status) = plan.invoke(operands);
            // Preserve the actual primitive status alongside the native fact,
            // before any later source-output/report-capacity refusal.
            slot.closing_status = status.and_then(NativeOwnerStatus::independent);
            slot.last_observed_status = slot.closing_status;
            if consumes {
                NativeOwnerStorage::record_consumed(&mut slots, self.slot);
            }
            if let Some(checked) = &mut slots[self.slot].checked {
                checked.finished(consumes);
            }
            if !consumes {
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
        #[cfg(any(test, ash_checked_owner_root = "v1"))]
        if matches!(self.backing, GuardBacking::CheckedLeaf) {
            // Refusal while another live storage borrow exists must not reborrow
            // in Drop. The slot still owns its opaque cell; the ordinary host
            // close records transfer once that external borrow has ended.
            if let Ok(mut slots) = self.storage.slots.try_borrow_mut()
                && !NativeOwnerStorage::denied(&slots, self.slot)
            {
                NativeOwnerStorage::destroy(&mut slots, self.slot);
            }
            return;
        }
        self.storage.abandon(self.slot);
    }
}

/// Nonowning bookkeeping for an already reserved physical slot. It has no
/// address/callback/entry method and cannot approve or invoke native code.
#[derive(Debug)]
pub(crate) struct NativeOwnerBoundary {
    storage: Rc<NativeOwnerStorage>,
    slot: usize,
}
impl NativeOwnerBoundary {
    pub(crate) fn acquisition_request(&self) -> Option<crate::core::NodeId> {
        self.storage.slots.borrow()[self.slot].checked.as_ref()
            .and_then(|checked| checked.acquisition_request())
    }
    /// The evaluator has authenticated the original call and exact selected
    /// Current/Enclosing slot. No cause data enters this native observation.
    /// All checks/work precede the irreversible denial; the returned scalars
    /// need no allocation, ledger transition, source K or report insertion.
    pub(crate) fn deny(
        &self, receipt: &super::super::source_bindings::SourceOwnerViolationRequest,
        activation: usize, work: &mut TypeWorkBudget,
    ) -> Result<(crate::foreign::checked_control::Native, bool, Option<i128>), NativeOwnerAdmissionError> {
        pay(work, 4)?;
        let mut slots = self.storage.slots.try_borrow_mut()
            .map_err(|_| NativeOwnerAdmissionError::Authority)?;
        let root = NativeOwnerStorage::validated_group_root(&slots, self.slot)?
            .ok_or(NativeOwnerAdmissionError::Authority)?;
        let slot = &slots[self.slot];
        let checked = slot.checked.as_ref().ok_or(NativeOwnerAdmissionError::Authority)?;
        if receipt.reject {
            checked.authorize_rejection(receipt, activation, work).map_err(control_error)?;
        } else if !slot.physically_live() {
            return Err(NativeOwnerAdmissionError::Authority);
        }
        // No fallible operation follows this store. Synchronizing this owner's
        // existing ledger only denies continuation; it asserts no native event.
        slots[root].checked_group_denied = true;
        NativeOwnerStorage::sync_group_denial(&mut slots, self.slot);
        let slot = &slots[self.slot];
        let (_, _, native, unresolved) = slot.checked.as_ref().expect("checked above").closing_record();
        Ok((native, unresolved, slot.last_observed_status))
    }
    /// Same-slot backing inspection only. Presence proves neither native
    /// permission nor protected retention; absence does not prove disposal.
    pub(crate) fn retains_backing(&self) -> bool {
        self.storage.slots.borrow()[self.slot].physically_live()
    }
    pub(crate) fn closing_status(&self) -> Option<i128> {
        self.storage.slots.borrow()[self.slot].closing_status
    }
    pub(crate) fn closing_record(&self) -> Result<(
        Option<crate::foreign::checked_control::Completion>,
        crate::foreign::checked_control::K,
        crate::foreign::checked_control::Native,
        bool,
    ), NativeOwnerAdmissionError> {
        let slots = self.storage.slots.borrow();
        let checked = slots[self.slot].checked.as_ref()
            .ok_or(NativeOwnerAdmissionError::Authority)?;
        Ok(checked.closing_record())
    }
    pub(crate) fn publish(
        &self,
        activation: usize,
        scope: crate::core::NodeId,
        work: &mut TypeWorkBudget,
    ) -> Result<(), NativeOwnerAdmissionError> {
        let mut slots = self.storage.slots.borrow_mut();
        if NativeOwnerStorage::denied(&slots, self.slot) {
            return Err(NativeOwnerAdmissionError::Authority);
        }
        slots[self.slot].checked.as_mut()
            .ok_or(NativeOwnerAdmissionError::Authority)?
            .publish(activation, scope, work)
            .map_err(control_error)
    }
    /// Exactly the Acquire/Body/Finish boundary-return observers are prepaid
    /// at reservation. This retain supplies no native entry or owner authority.
    pub(crate) fn prepaid_scope_observer(&self) -> Self {
        Self {
            storage: Rc::clone(&self.storage),
            slot: self.slot,
        }
    }
    pub(crate) fn closing(
        &self,
        activation: usize,
        scope: crate::core::NodeId,
        work: &mut TypeWorkBudget,
    ) -> Result<(), NativeOwnerAdmissionError> {
        let mut slots = self.storage.slots.borrow_mut();
        NativeOwnerStorage::sync_group_denial(&mut slots, self.slot);
        slots[self.slot].checked.as_mut()
            .ok_or(NativeOwnerAdmissionError::Authority)?
            .closing(activation, scope, work)
            .map_err(control_error)
    }
    pub(crate) fn output_failed(&self) {
        if let Some(control) = &mut self.storage.slots.borrow_mut()[self.slot].checked {
            control.output_failed();
        }
    }
    pub(crate) fn source_continued(
        &self,
        activation: usize,
        scope: crate::core::NodeId,
    ) -> Result<(), NativeOwnerAdmissionError> {
        self.storage.slots.borrow_mut()[self.slot]
            .checked
            .as_mut()
            .ok_or(NativeOwnerAdmissionError::Authority)?
            .source_continued(activation, scope)
            .map_err(control_error)
    }
    #[cfg(test)]
    pub(crate) fn snapshot(&self) -> crate::foreign::checked_control::BoundarySnapshot {
        self.storage.slots.borrow()[self.slot]
            .checked
            .as_ref()
            .unwrap()
            .snapshot()
    }
}
#[derive(Debug)]
pub(crate) struct NativeOwnerBorrowRecord {
    boundary: NativeOwnerBoundary,
    original: Arc<crate::foreign::checked_source::CheckedForeignSymbol>,
}
impl NativeOwnerBorrowRecord {
    #[cfg(any(test, ash_checked_owner_root = "v1"))]
    pub(in crate::foreign) fn invoke_leaf(self, key: usize, query: bool) -> Result<(NativeOwnerBoundary, super::super::source_bindings::SourceWindowRaw), NativeScalarCallError> {
        // Query's additional nonowning view retain is paid during preparation.
        let view_boundary = query.then(|| NativeOwnerBoundary { storage: Rc::clone(&self.boundary.storage), slot: self.boundary.slot });
        let mut slots = self.boundary.storage.slots.try_borrow_mut().map_err(|_| NativeScalarCallError::ArgumentContract)?;
        NativeOwnerStorage::entry_allowed(&mut slots, self.boundary.slot, true)
            .map_err(|_| NativeScalarCallError::ArgumentContract)?;
        let slot = slots.get_mut(self.boundary.slot).ok_or(NativeScalarCallError::ArgumentContract)?;
        let NativeOwnerSlot { leaf, checked, last_observed_status, .. } = slot;
        let Some(CheckedLeafBacking::Cell(cell)) = leaf else { return Err(NativeScalarCallError::ArgumentContract); };
        if !cell.is_occupied() { return Err(NativeScalarCallError::ArgumentContract); }
        let control = checked.as_mut().ok_or(NativeScalarCallError::ArgumentContract)?;
        control.begin_borrow(&self.original).map_err(|_| NativeScalarCallError::ArgumentContract)?;
        let result = if query {
            cell.query(key).map(|descriptor| super::super::source_bindings::SourceWindowRaw::View(
                super::view::NativeViewReturned::checked(view_boundary.expect("query retain"), descriptor)))
        } else { cell.length(key).map(|length| super::super::source_bindings::SourceWindowRaw::Scalar(NativeScalarReply::Scalar(NativeScalarValue::USize(length)))) };
        // The native borrow returned even when its pointer/range validation refused.
        *last_observed_status = result.as_ref().ok().and_then(|raw| match raw {
            super::super::source_bindings::SourceWindowRaw::Scalar(scalar) => observed_scalar_status(*scalar),
            super::super::source_bindings::SourceWindowRaw::View(_) => None,
        });
        control.borrowed();
        if result.is_err() { control.output_failed(); }
        drop(slots);
        result.map(|result| (self.boundary, result)).map_err(|_| NativeScalarCallError::ArgumentContract)
    }

    pub(crate) fn begin(&self) -> Result<(), NativeOwnerAdmissionError> {
        let mut slots = self.boundary.storage.slots.borrow_mut();
        NativeOwnerStorage::entry_allowed(&mut slots, self.boundary.slot, true)?;
        slots[self.boundary.slot].checked.as_mut()
            .ok_or(NativeOwnerAdmissionError::Authority)?
            .begin_borrow(&self.original)
            .map_err(control_error)
    }
    pub(crate) fn returned(self, status: Option<NativeScalarReply>) -> NativeOwnerBoundary {
        let mut slots = self.boundary.storage.slots.borrow_mut();
        slots[self.boundary.slot].last_observed_status = status.and_then(observed_scalar_status);
        slots[self.boundary.slot].checked.as_mut()
            .expect("prepared borrow record").borrowed();
        drop(slots);
        self.boundary
    }
    pub(crate) fn output_failed(&self) {
        self.boundary.output_failed();
    }
}
/// Single-use bookkeeping for an authenticated primitive, never a callback or
/// protected approval. Physical read admission remains in the evaluator.
#[derive(Debug)]
pub(crate) struct NativeOwnerCopyRecord {
    boundary: NativeOwnerBoundary,
    identity: super::super::source_bindings::SourceOwnerCopyIdentity,
    entry_work: TypeWorkBudget,
}
impl NativeOwnerCopyRecord {
    #[cfg(any(test, ash_checked_owner_root = "v1"))]
    pub(crate) fn copy_checked_leaf(mut self, view: &super::view::NativeViewReturned, destination: &mut [u8]) -> Result<(), NativeOwnerAdmissionError> {
        let (owner, descriptor) = view.checked_descriptor().ok_or(NativeOwnerAdmissionError::Authority)?;
        if owner.slot != self.boundary.slot || !Rc::ptr_eq(&owner.storage, &self.boundary.storage) { return Err(NativeOwnerAdmissionError::Authority); }
        let mut slots = self.boundary.storage.slots.try_borrow_mut().map_err(|_| NativeOwnerAdmissionError::Authority)?;
        NativeOwnerStorage::entry_allowed(&mut slots, self.boundary.slot, true)?;
        let slot = slots.get_mut(self.boundary.slot).ok_or(NativeOwnerAdmissionError::Authority)?;
        let NativeOwnerSlot { leaf, checked, last_observed_status, .. } = slot;
        let Some(CheckedLeafBacking::Cell(cell)) = leaf else { return Err(NativeOwnerAdmissionError::Authority); };
        if !cell.is_occupied() { return Err(NativeOwnerAdmissionError::Authority); }
        let control = checked.as_mut().ok_or(NativeOwnerAdmissionError::Authority)?;
        control.begin_copy(self.identity, &mut self.entry_work).map_err(control_error)?;
        let result = cell.copy(descriptor, 0, destination);
        *last_observed_status = None;
        control.copied();
        if result.is_err() { control.output_failed(); }
        result.map_err(|_| NativeOwnerAdmissionError::Authority)
    }

    pub(crate) fn begin(&mut self) -> Result<(), NativeOwnerAdmissionError> {
        let mut slots = self.boundary.storage.slots.borrow_mut();
        NativeOwnerStorage::entry_allowed(&mut slots, self.boundary.slot, true)?;
        slots[self.boundary.slot].checked.as_mut()
            .ok_or(NativeOwnerAdmissionError::Authority)?
            .begin_copy(self.identity, &mut self.entry_work)
            .map_err(control_error)
    }
    pub(crate) fn returned(self) -> NativeOwnerBoundary {
        let mut slots = self.boundary.storage.slots.borrow_mut();
        slots[self.boundary.slot].last_observed_status = None;
        slots[self.boundary.slot].checked.as_mut()
            .expect("prepared primitive copy record").copied();
        drop(slots);
        self.boundary
    }
    pub(crate) fn output_failed(&self) {
        self.boundary.output_failed();
    }
}
fn control_error(error: crate::foreign::checked_control::Failure) -> NativeOwnerAdmissionError {
    if error == crate::foreign::checked_control::Failure::Resource {
        NativeOwnerAdmissionError::Work
    } else {
        NativeOwnerAdmissionError::Authority
    }
}
impl NativeOwnerGuard {
    pub(crate) fn checked_boundary(
        &self,
        work: &mut TypeWorkBudget,
    ) -> Result<Option<NativeOwnerBoundary>, NativeOwnerAdmissionError> {
        if self.storage.slots.borrow()[self.slot].checked.is_none() {
            return Ok(None);
        }
        pay(work, 1)?; // one nonowning Rc retain; never a second owner/authority
        Ok(Some(NativeOwnerBoundary {
            storage: Rc::clone(&self.storage),
            slot: self.slot,
        }))
    }
    pub(in crate::foreign) fn prepare_checked_borrow(
        &self,
        receipt: &super::super::source_bindings::SourceOwnerScopeRequest,
        original: &Arc<crate::foreign::checked_source::CheckedForeignSymbol>,
        activation: usize,
        work: &mut TypeWorkBudget,
    ) -> Result<Option<NativeOwnerBorrowRecord>, NativeOwnerAdmissionError> {
        {
            let slots = self.storage.slots.borrow();
            if slots[self.slot].checked_group_root.is_some() { pay(work, 2)?; }
            if NativeOwnerStorage::denied(&slots, self.slot)
                || !slots[self.slot].physically_live()
            {
                return Err(NativeOwnerAdmissionError::Authority);
            }
            if let Some(control) = &slots[self.slot].checked {
                control
                    .borrow_request(receipt, activation, original, work)
                    .map_err(control_error)?;
            } else if receipt._scope.header().original.host.is_some() {
                return Err(NativeOwnerAdmissionError::Authority);
            } else {
                return Ok(None);
            }
        }
        pay(work, 1)?; // retain this exact admitted original, not its operation ID
        let boundary = self
            .checked_boundary(work)?
            .ok_or(NativeOwnerAdmissionError::Authority)?;
        Ok(Some(NativeOwnerBorrowRecord {
            boundary,
            original: Arc::clone(original),
        }))
    }
    pub(crate) fn prepare_checked_copy(
        &self,
        receipt: &super::super::source_bindings::SourceOwnerCopyRequest,
        activation: usize,
        work: &mut TypeWorkBudget,
    ) -> Result<NativeOwnerCopyRecord, NativeOwnerAdmissionError> {
        {
            let slots = self.storage.slots.borrow();
            if slots[self.slot].checked_group_root.is_some() { pay(work, 2)?; }
            if NativeOwnerStorage::denied(&slots, self.slot)
                || !slots[self.slot].physically_live()
            {
                return Err(NativeOwnerAdmissionError::Authority);
            }
            slots[self.slot]
                .checked
                .as_ref()
                .ok_or(NativeOwnerAdmissionError::Authority)?
                .copy_request(receipt, activation, work)
                .map_err(control_error)?;
        }
        // Every attempted primitive entry pays its own fixed check/commit
        // work now. A stale/capacity-refused attempt cannot drain the mandatory
        // native Finish reserve. Observation storage was reserved up front.
        pay(work, 12)?;
        let boundary = self
            .checked_boundary(work)?
            .ok_or(NativeOwnerAdmissionError::Authority)?;
        Ok(NativeOwnerCopyRecord {
            boundary,
            identity: receipt.identity,
            entry_work: TypeWorkBudget::with_limit(12),
        })
    }
    pub(in crate::foreign) fn prepare_checked_finish(
        &self,
        receipt: &super::super::source_bindings::SourceOwnerScopeRequest,
        activation: usize,
        blocked: bool,
        work: &mut TypeWorkBudget,
    ) -> Result<(), NativeOwnerAdmissionError> {
        let mut slots = self.storage.slots.borrow_mut();
        NativeOwnerStorage::sync_group_denial(&mut slots, self.slot);
        if let Some(control) = &mut slots[self.slot].checked {
            control
                .prepare_finish(receipt, activation, blocked, work)
                .map_err(control_error)?;
        } else if receipt._scope.header().original.host.is_some() {
            return Err(NativeOwnerAdmissionError::Authority);
        }
        Ok(())
    }
    pub(crate) fn begin_checked_finish_entry(
        &self,
    ) -> Result<Option<crate::foreign::checked_control::FinishEntry>, NativeOwnerAdmissionError> {
        let mut slots = self.storage.slots.borrow_mut();
        NativeOwnerStorage::sync_group_denial(&mut slots, self.slot);
        let blocked = slots[self.slot].checked_group_root.is_some_and(|root| slots[root].checked_group_denied);
        slots[self.slot].checked.as_mut()
            .map(|control| control.begin_finish_entry_with_blocked(blocked).map_err(control_error))
            .transpose()
    }
    #[cfg(test)]
    pub(crate) fn begin_checked_finish(&self) -> Result<(), NativeOwnerAdmissionError> {
        if let Some(control) = &mut self.storage.slots.borrow_mut()[self.slot].checked {
            control.begin_finish().map_err(control_error)?;
        }
        Ok(())
    }
}

/// Native disposition recorded without a reusable native callback. A retained
/// result carries the same unique lifecycle token, never a newly acquired owner.
#[derive(Debug)]
pub(crate) enum NativeOwnerDisposition {
    Consumed(Arc<CheckedForeignOwner>),
    Retained(NativeOwnerGuard),
    Blocked(NativeOwnerGuard),
    Synthetic {
        guard: NativeOwnerGuard,
        witness: crate::foreign::checked_control::SyntheticFinishWitness,
    },
}

impl NativeOwnerDisposition {
    pub(crate) fn owner(&self) -> &Arc<CheckedForeignOwner> {
        match self {
            Self::Consumed(owner) => owner,
            Self::Retained(guard) | Self::Blocked(guard) | Self::Synthetic { guard, .. } => guard.owner(),
        }
    }
    pub(crate) fn is_retained(&self) -> bool {
        !matches!(self, Self::Consumed(_))
    }
    pub(crate) fn is_blocked(&self) -> bool {
        matches!(self, Self::Blocked(_) | Self::Synthetic { .. })
    }
    pub(crate) fn synthetic_witness(&self) -> Option<&crate::foreign::checked_control::SyntheticFinishWitness> {
        match self {
            Self::Synthetic { witness, .. } => Some(witness),
            _ => None,
        }
    }
    pub(crate) fn into_retained(self) -> Option<NativeOwnerGuard> {
        match self {
            Self::Consumed(_) => None,
            Self::Retained(guard) | Self::Blocked(guard) | Self::Synthetic { guard, .. } => Some(guard),
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
        #[cfg(any(test, ash_checked_owner_root = "v1"))]
        let backing = if matches!(plan, NativeOwnerDestruction::CheckedLeaf) { GuardBacking::CheckedLeaf } else { GuardBacking::Legacy };
        let slot = storage.reserve(plan, count, current)?;
        Ok(Self {
            guard: NativeOwnerGuard {
                #[cfg(any(test, ash_checked_owner_root = "v1"))]
                backing,
                storage,
                slot,
                owner,
                initialized_bytes: None,
                bytes: None,
            },
            prepared_initialized_bytes: None,
        })
    }

    pub(in crate::foreign) fn prepare_checked_boundary(
        &mut self,
        receipt: &super::super::source_bindings::SourceOwnerScopeRequest,
        activation: usize,
        limits: Option<crate::foreign::checked_control::BoundaryLimits>,
        work: &mut TypeWorkBudget,
    ) -> Result<(), NativeOwnerAdmissionError> {
        if receipt._scope.header().original.host.is_none() {
            return Ok(());
        }
        pay(work, 3)?; // owner identity, existing slot authority and activation
        {
            let slots = self.guard.storage.slots.borrow();
            let slot = &slots[self.guard.slot];
            if !Arc::ptr_eq(self.guard.owner(), &receipt._scope.header().owner)
                || slot.checked.is_some()
                || slot.checked_group_root.is_none()
                || !slot
                    .authority
                    .as_ref()
                    .is_some_and(|authority| authority.activation == activation)
            {
                return Err(NativeOwnerAdmissionError::Authority);
            }
        }
        let checked = crate::foreign::checked_control::RuntimeBoundary::reserve(
            receipt,
            activation,
            limits.ok_or(NativeOwnerAdmissionError::Authority)?,
            work,
        )
        .map_err(control_error)?;
        self.guard.storage.slots.borrow_mut()[self.guard.slot].checked = Some(checked);
        Ok(())
    }
    pub(crate) fn checked_boundary(
        &self,
        work: &mut TypeWorkBudget,
    ) -> Result<Option<NativeOwnerBoundary>, NativeOwnerAdmissionError> {
        self.guard.checked_boundary(work)
    }
    pub(crate) fn begin_checked_acquire(&mut self) -> Result<(), NativeOwnerAdmissionError> {
        let mut slots = self.guard.storage.slots.borrow_mut();
        NativeOwnerStorage::entry_allowed(&mut slots, self.guard.slot, false)?;
        if let Some(control) = &mut slots[self.guard.slot].checked {
            control.begin_acquire().map_err(control_error)?;
        }
        Ok(())
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
        if slots[index].physically_live()
            || slots[index].authority.is_some()
            || destruction.len() != slots[index].raw.operands.len()
        {
            return Err(NativeOwnerAdmissionError::Authority);
        }
        let checked_owner = self.guard.owner.prepared().checked_contract().is_some();
        let mut group_root = None;
        let mut direct = Vec::new();
        let mut closure = Vec::new();
        pay(work, dependencies.len())?;
        direct
            .try_reserve_exact(dependencies.len())
            .map_err(|_| NativeOwnerAdmissionError::Storage(dependencies.len()))?;
        for dependency in dependencies {
            if !Rc::ptr_eq(&dependency.storage, &self.guard.storage)
                || dependency.slot >= index
                || !slots[dependency.slot].physically_live()
            {
                return Err(NativeOwnerAdmissionError::Authority);
            }
            if checked_owner || slots[dependency.slot].checked_group_root.is_some() {
                pay(work, 2)?;
                let dependency_root = NativeOwnerStorage::validated_group_root(&slots, dependency.slot)?;
                if NativeOwnerStorage::denied(&slots, dependency.slot) {
                    return Err(NativeOwnerAdmissionError::Authority);
                }
                if checked_owner {
                    let root = dependency_root.ok_or(NativeOwnerAdmissionError::Authority)?;
                    if group_root.is_some_and(|previous| previous != root) {
                        return Err(NativeOwnerAdmissionError::Authority);
                    }
                    group_root = Some(root);
                }
            } else if slots[dependency.slot].quarantined {
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
        if checked_owner {
            pay(work, 1)?;
            // This is a fresh reserved slot; inherited roots are never reset.
            slots[index].checked_group_root = Some(group_root.unwrap_or(index));
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

    /// The exact checked route owns the slot borrow before transport preparation
    /// and C. Profile/identity refusal happens before the ledger enters; after
    /// invocation both physical arming and mandatory observation use this borrow.
    #[cfg(any(test, ash_checked_owner_root = "v1"))]
    pub(in crate::foreign) fn invoke_checked_leaf(
        mut self,
        capacity: usize,
        initialized: usize,
    ) -> Result<NativeOwnerCallReturned, NativeScalarCallError> {
        let mut slots = self.guard.storage.slots.try_borrow_mut()
            .map_err(|_| NativeScalarCallError::ArgumentContract)?;
        let index = self.guard.slot;
        NativeOwnerStorage::entry_allowed(&mut slots, index, false)
            .map_err(|_| NativeScalarCallError::ArgumentContract)?;
        let slot = slots.get_mut(index).ok_or(NativeScalarCallError::ArgumentContract)?;
        if !slot.dependencies.is_empty()
            || self.prepared_initialized_bytes != Some(initialized) {
            return Err(NativeScalarCallError::ArgumentContract);
        }
        let NativeOwnerSlot { leaf, checked, last_observed_status, .. } = slot;
        let Some(CheckedLeafBacking::Cell(cell)) = leaf else {
            return Err(NativeScalarCallError::ArgumentContract);
        };
        let control = checked.as_mut().ok_or(NativeScalarCallError::ArgumentContract)?;
        let prepared = cell.prepare_acquire(capacity, initialized)
            .map_err(|_| NativeScalarCallError::ArgumentContract)?;
        control.begin_acquire().map_err(|_| NativeScalarCallError::ArgumentContract)?;
        let returned = prepared.invoke();
        let present = returned.nonnull();
        *last_observed_status = None;
        control.acquired(present);
        if present { self.guard.initialized_bytes = self.prepared_initialized_bytes; }
        drop(slots);
        Ok(NativeOwnerCallReturned {
            guard: self.guard,
            prepared_initialized_bytes: self.prepared_initialized_bytes,
            scalar: None,
            offset: None,
            recorded: true,
        })
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
            scalar: None,
            offset: None,
            recorded: false,
        }
    }

    /// Arms the returned owner before exposing its independent bare scalar.
    #[doc(hidden)]
    pub fn returned_output(
        self,
        address: *mut core::ffi::c_void,
        scalar: NativeScalarValue,
    ) -> NativeOwnerCallReturned {
        let mut returned = self.returned(address);
        returned.scalar = Some(NativeScalarReply::Scalar(scalar));
        returned
    }
}

/// A raw native return with destruction already armed and no acquisition callback.
#[doc(hidden)]
#[derive(Debug)]
pub struct NativeOwnerCallReturned {
    recorded: bool,
    guard: NativeOwnerGuard,
    prepared_initialized_bytes: Option<usize>,
    scalar: Option<NativeScalarReply>,
    offset: Option<*mut core::ffi::c_void>,
}

impl NativeOwnerCallReturned {
    /// Attaches only an outcome-readable pointer after ownership is armed.
    /// Common reporting still authenticates and bounds the input-relative value.
    #[doc(hidden)]
    pub fn with_output_offset(mut self, offset: Option<*mut core::ffi::c_void>) -> Self {
        self.offset = offset;
        self
    }
    /// The first post-return transition records ownership without refusal.
    pub(crate) fn record(mut self) -> NativeOwnerCallRecorded {
        if !self.recorded {
        if self.guard.storage.slots.borrow()[self.guard.slot]
            .raw
            .address
            .is_some()
        {
            self.guard.initialized_bytes = self.prepared_initialized_bytes;
        }
        {
            let mut slots = self.guard.storage.slots.borrow_mut();
            let index = self.guard.slot;
            let present = slots[index].raw.address.is_some();
            slots[index].last_observed_status = self.scalar.and_then(observed_scalar_status);
            if let Some(checked) = &mut slots[index].checked {
                checked.acquired(present);
            }
        }
        }
        NativeOwnerCallRecorded {
            guard: self.guard,
            scalar: self.scalar,
            offset: self.offset,
        }
    }
}

/// Recorded nullness and unique storage; ordinary reporting may now proceed.
#[derive(Debug)]
pub(crate) struct NativeOwnerCallRecorded {
    guard: NativeOwnerGuard,
    scalar: Option<NativeScalarReply>,
    offset: Option<*mut core::ffi::c_void>,
}

impl NativeOwnerCallRecorded {
    pub(crate) fn into_parts(
        self,
    ) -> (
        Option<NativeOwnerGuard>,
        Option<NativeScalarReply>,
        Option<*mut core::ffi::c_void>,
    ) {
        let scalar = self.scalar;
        let offset = self.offset;
        (self.into_guard(), scalar, offset)
    }
    pub(crate) fn into_guard(self) -> Option<NativeOwnerGuard> {
        let nonnull = self.guard.storage.slots.borrow()[self.guard.slot].physically_live();
        nonnull.then_some(self.guard)
    }
}

#[cfg(all(test, not(ash_checked_owner_root = "v1")))]
impl NativeOwnerGuardReady {
    pub(crate) fn assert_leaf_borrow_refusal_for_test(self) {
        let storage = Rc::clone(&self.guard.storage);
        let held = storage.slots.borrow_mut();
        assert!(self.invoke_checked_leaf(8, 8).is_err());
        drop(held);
        assert!(storage.close());
    }
}
#[cfg(all(test, not(ash_checked_owner_root = "v1")))]
impl NativeOwnerGuard {
    pub(crate) fn assert_leaf_finish_borrow_refusal_for_test(self) {
        let storage = Rc::clone(&self.storage);
        let index = self.slot;
        let held = storage.slots.borrow_mut();
        assert!(self.finish_checked_admitted(&NativeOwnerDestruction::CheckedLeaf, &[], false).is_err());
        drop(held);
        assert!(storage.slots.borrow()[index].physically_live());
        assert!(!storage.close());
        assert!(storage.slots.borrow()[index].physically_live());
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
    fn checked_group_denial_preserves_siblings_backing_and_skips_all_destructors() {
        use crate::types::TypeWorkBudget;
        // Actual immutable checked owner metadata; the returns below are private
        // Rust slot injections, not native calls or source admission evidence.
        let (program, _) = crate::elaborate::checked_owner_passive_program();
        let mut pending = vec![program.root()];
        let owner = loop {
            let node = program.node(pending.pop().unwrap()).unwrap();
            if let crate::core::EffectExprKind::Operation(
                crate::core::EffectOperation::SourceResourceScope(scope),
            ) = &node.kind {
                break std::sync::Arc::clone(&scope.header().owner);
            }
            pending.extend((0..node.kind.child_count()).filter_map(|i| node.kind.child_at(i)));
        };
        assert!(owner.prepared().checked_contract().is_some());
        HOST_ORDER.with(|order| order.borrow_mut().clear());
        let storage = std::rc::Rc::new(super::NativeOwnerStorage::default());
        let mut work = TypeWorkBudget::default();
        let parent = model_ready(&owner, &storage, 1, Vec::new(), &mut work).unwrap()
            .returned(std::ptr::without_provenance_mut::<u8>(1).cast())
            .record().into_guard().unwrap();
        let first = model_ready(&owner, &storage, 2,
            vec![storage.declared_dependency(1, &mut work).unwrap()], &mut work).unwrap()
            .returned(std::ptr::without_provenance_mut::<u8>(2).cast())
            .record().into_guard().unwrap();
        let sibling = model_ready(&owner, &storage, 3,
            vec![storage.declared_dependency(1, &mut work).unwrap()], &mut work).unwrap()
            .returned(std::ptr::without_provenance_mut::<u8>(3).cast())
            .record().into_guard().unwrap();
        let descendant = model_ready(&owner, &storage, 4,
            vec![storage.declared_dependency(2, &mut work).unwrap()], &mut work).unwrap()
            .returned(std::ptr::without_provenance_mut::<u8>(4).cast())
            .record().into_guard().unwrap();
        let independent = model_ready(&owner, &storage, 5, Vec::new(), &mut work).unwrap()
            .returned(std::ptr::without_provenance_mut::<u8>(5).cast())
            .record().into_guard().unwrap();
        assert!(model_ready(&owner, &storage, 6, vec![
            storage.declared_dependency(1, &mut work).unwrap(),
            storage.declared_dependency(5, &mut work).unwrap(),
        ], &mut work).is_err(), "cross-group dependency refuses before edge commit");
        let before = {
            let slots = storage.slots.borrow();
            assert_eq!(slots[parent.slot].live_dependents, 2);
            assert_eq!(slots[first.slot].live_dependents, 1);
            assert_eq!(slots[independent.slot].live_dependents, 0);
            for member in [&parent, &first, &sibling, &descendant] {
                assert_eq!(slots[member.slot].checked_group_root, Some(parent.slot));
            }
            slots.iter().map(|slot| slot.live_dependents).collect::<Vec<_>>()
        };
        assert!(parent.ordinary_live() && sibling.ordinary_live() && descendant.ordinary_live());
        // Model the explicit primitive's irreversible store, not ordinary
        // local/ancestor quarantine (whose host-close semantics are unchanged).
        storage.slots.borrow_mut()[parent.slot].checked_group_denied = true;
        assert!(!parent.ordinary_live() && !first.ordinary_live());
        assert!(!sibling.ordinary_live() && !descendant.ordinary_live());
        assert!(independent.ordinary_live(), "same host/storage does not merge independent roots");
        let parent_state = crate::types::IterativeTypeOwner::new({
            let slots = storage.slots.borrow();
            crate::types::clone_type_with_budget(&slots[parent.slot].authority.as_ref().unwrap().state, &mut work).unwrap()
        });
        for _ in 0..2 {
            let denial = storage.denial_dependency(1, &parent_state, &mut work).unwrap();
            assert_eq!(denial.slot, parent.slot);
            assert!(denial.address().is_none(), "denial lookup grants no ordinary/raw access");
            assert!(storage.view(1, &parent_state, super::NativeOwnerViewKind::State, None, &mut work).is_err());
        }
        drop(parent_state);
        drop(first);
        drop(descendant);
        drop(sibling);
        drop(parent);
        HOST_ORDER.with(|order| assert!(order.borrow().is_empty(), "no suspect Drop destructor"));
        drop(independent);
        HOST_ORDER.with(|order| assert_eq!(&*order.borrow(), &[5]));
        assert!(!storage.close());
        let slots = storage.slots.borrow();
        for index in 0..4 {
            assert!(slots[index].physically_live(), "quarantine retains native backing");
            assert_eq!(slots[index].live_dependents, before[index]);
        }
        HOST_ORDER.with(|order| assert_eq!(&*order.borrow(), &[5], "explicit close also denies"));
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
