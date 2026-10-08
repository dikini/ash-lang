//! Physical arena backing for the bounded A-0 experiment.
//!
//! Layout tags and allocation keys authenticate no Ash type or scope. The later
//! bridge supplies checked layout evidence and enforces source ownership.

use std::{
    alloc::{Layout, alloc_zeroed, dealloc},
    fmt,
    num::NonZeroU64,
    ptr::NonNull,
    sync::atomic::{AtomicU64, Ordering},
};

/// Opaque physical layout discriminator, not authenticated Ash Layout evidence.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct LayoutTag(u64);
impl LayoutTag {
    /// Creates an unauthenticated native discriminator.
    #[must_use]
    pub const fn new(value: u64) -> Self {
        Self(value)
    }
    /// Returns the native discriminator, without establishing Ash Layout authority.
    #[must_use]
    pub const fn value(self) -> u64 {
        self.0
    }
}
/// Encoded extent and natural alignment supplied by the later checked codec.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct PayloadLayout {
    tag: LayoutTag,
    size: usize,
    alignment: usize,
}
impl PayloadLayout {
    /// Checks native size and alignment only.
    ///
    /// # Errors
    /// Rejects extents beyond pointer-offset limits or unsupported alignments.
    pub fn new(tag: LayoutTag, size: usize, alignment: usize) -> Result<Self, AllocationError> {
        if size > isize::MAX as usize {
            return Err(AllocationError::InvalidPayload);
        }
        if !alignment.is_power_of_two() || alignment > 64 {
            return Err(AllocationError::InvalidAlignment);
        }
        Ok(Self {
            tag,
            size,
            alignment,
        })
    }
    /// Returns the unauthenticated physical layout discriminator.
    #[must_use]
    pub const fn tag(self) -> LayoutTag {
        self.tag
    }
    /// Returns the encoded byte extent.
    #[must_use]
    pub const fn size(self) -> usize {
        self.size
    }
    /// Returns the checked native natural alignment.
    #[must_use]
    pub const fn natural_alignment(self) -> usize {
        self.alignment
    }
}
/// Non-owning allocation candidate containing exactly two 64-bit identities.
#[repr(C)]
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct AllocationKey {
    owner: NonZeroU64,
    object: NonZeroU64,
}
impl AllocationKey {
    /// Creates an unauthenticated candidate from two nonzero IDs.
    ///
    /// Neither existence, liveness, layout nor Ash Ref authority is established.
    #[must_use]
    pub const fn from_ids(owner: u64, object: u64) -> Option<Self> {
        let Some(owner) = NonZeroU64::new(owner) else {
            return None;
        };
        let Some(object) = NonZeroU64::new(object) else {
            return None;
        };
        Some(Self { owner, object })
    }
    /// Returns the encoded owner ID without keeping its owner alive.
    #[must_use]
    pub const fn owner_id(self) -> u64 {
        self.owner.get()
    }
    /// Returns the owner-local published object ID.
    #[must_use]
    pub const fn object_id(self) -> u64 {
        self.object.get()
    }
}
/// Failure to acquire the physical block/table.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ArenaInitError {
    /// Counts or layout arithmetic exceed native limits.
    InvalidConfiguration,
    /// A native backing allocation returned null.
    AllocationFailed,
    /// Unique owner identities are exhausted; source mapping remains pending.
    IdentityExhausted,
}
/// Native reservation refusal before publication.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum AllocationError {
    /// Payload extent or its alignment padding exceeds capacity.
    OutOfPayload,
    /// No unpublished object-record slot remains.
    OutOfObjects,
    /// Alignment is unsupported or weaker than natural alignment.
    InvalidAlignment,
    /// Encoded extent exceeds the native pointer-offset bound.
    InvalidPayload,
}
/// A reservation refusal or caller initializer failure.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum AllocationFailure<E> {
    /// No reservation was published.
    Refused(AllocationError),
    /// Caller initialization failed; no key or cursor advance was published.
    Initialization(E),
}
/// A checked unpublished allocation candidate. It retains no native owner.
///
/// Its key is physical metadata, not Ash reference authority. Dropping this
/// candidate changes no native storage. Commit must validate the same owner
/// and unchanged publication position before exposing any reservation bytes.
#[derive(Debug)]
pub struct PreparedAllocation {
    key: AllocationKey,
    layout: PayloadLayout,
    alignment: usize,
    cursor: usize,
    objects: usize,
    start: usize,
    end: usize,
}
impl PreparedAllocation {
    /// Returns the unpublished physical key, granting no existence or Ash authority.
    #[must_use]
    pub const fn candidate_key(&self) -> AllocationKey {
        self.key
    }
}
/// Failure before a prepared native allocation publishes a record.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum PreparedCommitFailure<E> {
    /// The owner or publication position changed; initialization was not called.
    InvalidPreparation,
    /// Initialization failed and its unpublished bytes were rolled back.
    Initialization(E),
}

/// Failure to read a key against this owner and layout context.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum AccessError {
    /// Candidate belongs to a different or completed owner.
    ForeignOwner,
    /// Candidate object is not published by this owner.
    UnknownObject,
    /// Expected layout differs from the published record.
    LayoutMismatch,
    /// A private object record violates backing invariants.
    InvalidRecord,
}
/// Logical usage; alignment padding counts as used payload bytes.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Usage {
    /// Cursor after the last successful publication.
    pub used_payload_bytes: usize,
    /// Admitted payload capacity.
    pub payload_capacity: usize,
    /// Published object count, including zero-sized objects.
    pub object_count: usize,
    /// Admitted object-record capacity.
    pub object_capacity: usize,
}
/// Requested native allocation layouts and inline Rust metadata, excluding
/// allocator overhead/RSS and caller codec scratch.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct PhysicalUsage {
    /// Requested payload allocator bytes.
    pub payload_allocation_bytes: usize,
    /// Requested table allocator bytes.
    pub object_table_bytes: usize,
    /// Actual inline size of one native object record.
    pub object_record_bytes: usize,
    /// Actual inline size of the unique Rust arena owner.
    pub owner_inline_bytes: usize,
}
const PAYLOAD_ALIGNMENT: usize = 64;
static NEXT_OWNER: AtomicU64 = AtomicU64::new(1);

#[derive(Clone, Copy)]
struct ObjectRecord {
    offset: usize,
    extent: usize,
    layout: LayoutTag,
}

struct RawBlock {
    pointer: NonNull<u8>,
    layout: Layout,
}
impl RawBlock {
    fn new(layout: Layout) -> Result<Self, ArenaInitError> {
        if layout.size() == 0 {
            return Ok(Self {
                pointer: NonNull::dangling(),
                layout,
            });
        }
        #[cfg(test)]
        if private_allocation_probe::refuse() {
            return Err(ArenaInitError::AllocationFailed);
        }
        // SAFETY: The checked nonzero Layout satisfies allocator size/alignment
        // limits. This unique guard takes ownership of a successful allocation.
        let pointer = NonNull::new(unsafe { alloc_zeroed(layout) })
            .ok_or(ArenaInitError::AllocationFailed)?;
        #[cfg(test)]
        private_allocation_probe::allocated(layout);
        Ok(Self { pointer, layout })
    }
    fn reservation(&mut self, offset: usize, extent: usize) -> &mut [u8] {
        if extent == 0 {
            return &mut [];
        }
        // SAFETY: Only commit_prepared calls this after revalidating the complete
        // range against the fixed block. The exclusive owner borrow excludes reads or
        // another reservation. Every byte was initialized by alloc_zeroed.
        unsafe { std::slice::from_raw_parts_mut(self.pointer.as_ptr().add(offset), extent) }
    }
}
impl Drop for RawBlock {
    fn drop(&mut self) {
        if self.layout.size() != 0 {
            // SAFETY: This block uniquely owns the allocation returned for this
            // exact Layout, and no payload/table borrow survives owner Drop.
            unsafe { dealloc(self.pointer.as_ptr(), self.layout) };
            #[cfg(test)]
            private_allocation_probe::deallocated(self.layout);
        }
    }
}

struct Reservation<'a> {
    bytes: &'a mut [u8],
    published: bool,
}
impl<'a> Reservation<'a> {
    fn new(bytes: &'a mut [u8]) -> Self {
        bytes.fill(0);
        Self {
            bytes,
            published: false,
        }
    }
    fn publish(mut self) {
        self.published = true;
    }
}
impl Drop for Reservation<'_> {
    fn drop(&mut self) {
        if !self.published {
            self.bytes.fill(0);
        }
    }
}

fn issue_owner_id(next: &AtomicU64) -> Result<NonZeroU64, ArenaInitError> {
    // Zero is a permanent exhausted sentinel. MAX is issued once, then checked
    // addition sets that sentinel instead of wrapping to an earlier owner ID.
    let issued = next
        .fetch_update(Ordering::Relaxed, Ordering::Relaxed, |id| {
            (id != 0).then(|| id.checked_add(1).unwrap_or(0))
        })
        .map_err(|_| ArenaInitError::IdentityExhausted)?;
    NonZeroU64::new(issued).ok_or(ArenaInitError::IdentityExhausted)
}

fn checked_range(cursor: usize, extent: usize, alignment: usize) -> Option<(usize, usize)> {
    let mask = alignment.checked_sub(1)?;
    let start = cursor.checked_add(mask)? & !mask;
    let end = start.checked_add(extent)?;
    Some((start, end))
}

/// Unique owner of fixed native payload and object-record backing.
///
/// Published bytes are immutable. Keys never retain this owner; a read borrows
/// it explicitly. Callback bytes are zeroed before initialization, so a native
/// caller may leave bytes zero without exposing uninitialized or failed data.
/// The later codec must establish complete semantic encoding independently.
pub struct Arena {
    owner: NonZeroU64,
    payload: RawBlock,
    records: RawBlock,
    cursor: usize,
    objects: usize,
    object_slots: usize,
}
impl Arena {
    /// Preallocates the block and fixed metadata table before returning an owner.
    ///
    /// # Errors
    /// Rejects invalid capacities, backing allocation failure, or ID exhaustion.
    /// ID exhaustion is a host error; source terminal/error mapping is pending.
    pub fn new(payload_bytes: usize, object_slots: usize) -> Result<Self, ArenaInitError> {
        Self::new_with_ids(payload_bytes, object_slots, &NEXT_OWNER)
    }
    fn new_with_ids(
        payload_bytes: usize,
        object_slots: usize,
        ids: &AtomicU64,
    ) -> Result<Self, ArenaInitError> {
        let payload_layout = Layout::from_size_align(payload_bytes, PAYLOAD_ALIGNMENT)
            .map_err(|_| ArenaInitError::InvalidConfiguration)?;
        let record_layout = Layout::array::<ObjectRecord>(object_slots)
            .map_err(|_| ArenaInitError::InvalidConfiguration)?;
        if u64::try_from(object_slots).is_err() {
            return Err(ArenaInitError::InvalidConfiguration);
        }
        // Both layouts are checked before any backing allocation. The first
        // guard drops if table allocation or unique ID issuance fails.
        let payload = RawBlock::new(payload_layout)?;
        let records = RawBlock::new(record_layout)?;
        let owner = issue_owner_id(ids)?;
        Ok(Self {
            owner,
            payload,
            records,
            cursor: 0,
            objects: 0,
            object_slots,
        })
    }
    /// Prepares a physical key and checked range without mutating native counters.
    ///
    /// The caller can complete result admission before committing this candidate.
    /// This API establishes no source type, layout authority or owner lifetime.
    ///
    /// # Errors
    /// Refuses invalid layout/alignment or insufficient byte/object capacity.
    pub fn prepare_allocation(
        &self,
        layout: PayloadLayout,
        requested_alignment: usize,
    ) -> Result<PreparedAllocation, AllocationError> {
        let alignment = if requested_alignment == 0 {
            layout.alignment
        } else {
            requested_alignment
        };
        if !alignment.is_power_of_two()
            || alignment < layout.alignment
            || alignment > PAYLOAD_ALIGNMENT
        {
            return Err(AllocationError::InvalidAlignment);
        }
        let (start, end) = checked_range(self.cursor, layout.size, alignment)
            .filter(|(_, end)| *end <= self.payload.layout.size())
            .ok_or(AllocationError::OutOfPayload)?;
        if self.objects >= self.object_slots {
            return Err(AllocationError::OutOfObjects);
        }
        let object = self
            .objects
            .checked_add(1)
            .and_then(|count| u64::try_from(count).ok())
            .and_then(NonZeroU64::new)
            .ok_or(AllocationError::OutOfObjects)?;
        Ok(PreparedAllocation {
            key: AllocationKey {
                owner: self.owner,
                object,
            },
            layout,
            alignment,
            cursor: self.cursor,
            objects: self.objects,
            start,
            end,
        })
    }
    /// Initializes and publishes an admitted candidate on this exact owner.
    ///
    /// All fallible result admission must precede this call. No caller code or
    /// conversion follows a successful initializer before native publication.
    ///
    /// # Errors
    /// Rejects a stale or foreign candidate before initialization, or rolls back
    /// an initializer failure. A panicking initializer also rolls back.
    pub fn commit_prepared<E>(
        &mut self,
        prepared: PreparedAllocation,
        initialize: impl FnOnce(&mut [u8]) -> Result<(), E>,
    ) -> Result<AllocationKey, PreparedCommitFailure<E>> {
        let next_count = self
            .objects
            .checked_add(1)
            .ok_or(PreparedCommitFailure::InvalidPreparation)?;
        if prepared.key.owner != self.owner
            || prepared.cursor != self.cursor
            || prepared.objects != self.objects
            || next_count > self.object_slots
            || u64::try_from(next_count).ok() != Some(prepared.key.object.get())
            || !prepared.alignment.is_power_of_two()
            || prepared.alignment < prepared.layout.alignment
            || prepared.alignment > PAYLOAD_ALIGNMENT
            || checked_range(self.cursor, prepared.layout.size, prepared.alignment)
                != Some((prepared.start, prepared.end))
            || prepared.end > self.payload.layout.size()
        {
            return Err(PreparedCommitFailure::InvalidPreparation);
        }
        let record = ObjectRecord {
            offset: prepared.start,
            extent: prepared.layout.size,
            layout: prepared.layout.tag,
        };
        let reservation = Reservation::new(
            self.payload
                .reservation(prepared.start, prepared.layout.size),
        );
        initialize(reservation.bytes).map_err(PreparedCommitFailure::Initialization)?;
        // The pending result has already been admitted by the caller. All native
        // checks also preceded initialization. Publication allocates nothing and
        // invokes no further caller code or fallible conversion.
        reservation.publish();
        // SAFETY: The checked next_count is within the fixed aligned table.
        // This slot is unpublished. The POD record contains initialized integer
        // metadata, and no payload borrow survives the exclusive owner borrow.
        unsafe {
            self.records
                .pointer
                .cast::<ObjectRecord>()
                .as_ptr()
                .add(self.objects)
                .write(record)
        };
        self.cursor = prepared.end;
        self.objects = next_count;
        Ok(prepared.key)
    }

    /// Initializes an unpublished range, then publishes its non-owning key.
    ///
    /// Zero requested alignment uses the natural alignment. Otherwise it must
    /// be a power of two between natural alignment and 64. Padding consumes
    /// payload capacity. No backing/table allocation occurs during publication.
    ///
    /// Returning `Ok` from the callback commits immediately. A bridge must
    /// complete all fallible conversion, Ref/result storage reservation and
    /// runtime admission first, or use [`Self::prepare_allocation`] and
    /// [`Self::commit_prepared`] to admit its candidate result before publication.
    /// Published objects have no rollback/removal operation. Layout/tag inputs
    /// must come from its authenticated dictionary; this backing establishes
    /// neither Ash Layout nor Ref authority.
    ///
    /// # Errors
    /// Returns refusal before reservation or caller failure after rollback.
    /// A panicking initializer also rolls back during unwinding; aborting panic
    /// terminates the process. Caller codec scratch/error policy is independent.
    pub fn allocate<E>(
        &mut self,
        layout: PayloadLayout,
        requested_alignment: usize,
        initialize: impl FnOnce(&mut [u8]) -> Result<(), E>,
    ) -> Result<AllocationKey, AllocationFailure<E>> {
        let prepared = self
            .prepare_allocation(layout, requested_alignment)
            .map_err(AllocationFailure::Refused)?;
        // No external code runs between preparation and validation. Staleness
        // cannot occur through this immediate API; preserve a checked failure
        // rather than panicking if an internal invariant is violated.
        self.commit_prepared(prepared, initialize)
            .map_err(|failure| match failure {
                PreparedCommitFailure::InvalidPreparation => {
                    AllocationFailure::Refused(AllocationError::InvalidPayload)
                }
                PreparedCommitFailure::Initialization(error) => {
                    AllocationFailure::Initialization(error)
                }
            })
    }
    /// Reads a published record through an independently supplied layout context.
    ///
    /// The returned slice borrows this unique owner; it has no owner keepalive.
    /// Expected tag equality establishes physical layout consistency only.
    ///
    /// # Errors
    /// Rejects owner/object/layout mismatch or a broken private record.
    pub fn read(&self, key: AllocationKey, expected: LayoutTag) -> Result<&[u8], AccessError> {
        if key.owner != self.owner {
            return Err(AccessError::ForeignOwner);
        }
        let index =
            usize::try_from(key.object.get() - 1).map_err(|_| AccessError::UnknownObject)?;
        if index >= self.objects {
            return Err(AccessError::UnknownObject);
        }
        // SAFETY: Only successful publication writes a record and advances
        // objects. This index is within that initialized immutable prefix.
        let record = unsafe {
            self.records
                .pointer
                .cast::<ObjectRecord>()
                .as_ptr()
                .add(index)
                .read()
        };
        if record.layout != expected {
            return Err(AccessError::LayoutMismatch);
        }
        let end = record
            .offset
            .checked_add(record.extent)
            .ok_or(AccessError::InvalidRecord)?;
        if end > self.cursor || end > self.payload.layout.size() {
            return Err(AccessError::InvalidRecord);
        }
        if record.extent == 0 {
            return Ok(&[]);
        }
        // SAFETY: The validated published range is inside the initialized stable
        // block. It never mutates/moves, and this borrow cannot outlive self.
        Ok(unsafe {
            std::slice::from_raw_parts(
                self.payload.pointer.as_ptr().add(record.offset),
                record.extent,
            )
        })
    }
    /// Returns logical usage, excluding metadata bytes.
    #[must_use]
    pub fn usage(&self) -> Usage {
        Usage {
            used_payload_bytes: self.cursor,
            payload_capacity: self.payload.layout.size(),
            object_count: self.objects,
            object_capacity: self.object_slots,
        }
    }
    /// Returns requested backing-layout and inline metadata measures.
    ///
    /// These are actual allocated Layout sizes, not allocator overhead/RSS.
    /// Zero-capacity backing requests no allocation. Caller codec scratch,
    /// runtime bookkeeping and foreign-library allocation remain separate.
    #[must_use]
    pub fn physical_usage(&self) -> PhysicalUsage {
        PhysicalUsage {
            payload_allocation_bytes: self.payload.layout.size(),
            object_table_bytes: self.records.layout.size(),
            object_record_bytes: size_of::<ObjectRecord>(),
            owner_inline_bytes: size_of::<Self>(),
        }
    }
}
impl fmt::Debug for Arena {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Arena")
            .field("owner", &self.owner)
            .field("usage", &self.usage())
            .field("physical", &self.physical_usage())
            .finish()
    }
}
impl fmt::Display for ArenaInitError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{self:?}")
    }
}
impl std::error::Error for ArenaInitError {}

impl fmt::Display for AllocationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{self:?}")
    }
}
impl std::error::Error for AllocationError {}
impl fmt::Display for AccessError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{self:?}")
    }
}
impl std::error::Error for AccessError {}
impl<E: fmt::Display> fmt::Display for AllocationFailure<E> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Refused(error) => write!(f, "arena allocation refused: {error}"),
            Self::Initialization(error) => write!(f, "arena initializer failed: {error}"),
        }
    }
}
impl<E: std::error::Error + 'static> std::error::Error for AllocationFailure<E> {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Refused(error) => Some(error),
            Self::Initialization(error) => Some(error),
        }
    }
}

#[cfg(test)]
mod private_allocation_probe {
    use super::*;
    use std::cell::RefCell;
    #[derive(Clone, Copy, Default)]
    pub(super) struct Counts {
        pub calls: usize,
        pub allocations: usize,
        pub deallocations: usize,
        pub live: usize,
        pub requested_bytes: usize,
    }
    #[derive(Default)]
    struct State {
        enabled: bool,
        fail_on_call: Option<usize>,
        counts: Counts,
    }
    thread_local! {static STATE: RefCell<State> = RefCell::new(State::default());}
    pub(super) struct Probe;
    impl Probe {
        pub(super) fn start(fail_on_call: Option<usize>) -> Self {
            STATE.with(|state| {
                let mut state = state.borrow_mut();
                assert!(!state.enabled);
                *state = State {
                    enabled: true,
                    fail_on_call,
                    counts: Counts::default(),
                };
            });
            Self
        }
        pub(super) fn counts(&self) -> Counts {
            STATE.with(|state| state.borrow().counts)
        }
    }
    impl Drop for Probe {
        fn drop(&mut self) {
            STATE.with(|state| state.borrow_mut().enabled = false);
        }
    }
    pub(super) fn refuse() -> bool {
        STATE.with(|state| {
            let mut state = state.borrow_mut();
            if !state.enabled {
                return false;
            }
            state.counts.calls += 1;
            state.fail_on_call == Some(state.counts.calls)
        })
    }
    pub(super) fn allocated(layout: Layout) {
        STATE.with(|state| {
            let mut state = state.borrow_mut();
            if state.enabled {
                state.counts.allocations += 1;
                state.counts.live += 1;
                state.counts.requested_bytes += layout.size();
            }
        });
    }
    pub(super) fn deallocated(layout: Layout) {
        STATE.with(|state| {
            let mut state = state.borrow_mut();
            if state.enabled {
                state.counts.deallocations += 1;
                state.counts.live -= 1;
                state.counts.requested_bytes -= layout.size();
            }
        });
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use private_allocation_probe::Probe;

    #[test]
    fn private_fault_injected_table_allocation_failure_drops_partial_payload() {
        let probe = Probe::start(Some(2));
        let ids = AtomicU64::new(17);
        assert_eq!(
            Arena::new_with_ids(128, 2, &ids).unwrap_err(),
            ArenaInitError::AllocationFailed
        );
        assert_eq!(ids.load(Ordering::Relaxed), 17);
        let counts = probe.counts();
        assert_eq!(
            (
                counts.calls,
                counts.allocations,
                counts.deallocations,
                counts.live,
                counts.requested_bytes
            ),
            (2, 1, 1, 0, 0)
        );
    }
    #[test]
    fn private_fault_injected_payload_failure_has_no_partial_owner_or_table() {
        let probe = Probe::start(Some(1));
        assert_eq!(
            Arena::new(128, 2).unwrap_err(),
            ArenaInitError::AllocationFailed
        );
        let counts = probe.counts();
        assert_eq!(
            (
                counts.calls,
                counts.allocations,
                counts.deallocations,
                counts.live
            ),
            (1, 0, 0, 0)
        );
    }
    #[test]
    fn private_identity_exhaustion_fault_releases_both_real_backing_allocations() {
        let probe = Probe::start(None);
        let exhausted = AtomicU64::new(0);
        assert_eq!(
            Arena::new_with_ids(128, 2, &exhausted).unwrap_err(),
            ArenaInitError::IdentityExhausted
        );
        let counts = probe.counts();
        assert_eq!(
            (
                counts.allocations,
                counts.deallocations,
                counts.live,
                counts.requested_bytes
            ),
            (2, 2, 0, 0)
        );
    }
    #[test]
    fn publications_never_allocate_more_backing_and_drop_releases_requested_layouts() {
        let probe = Probe::start(Some(3));
        let mut arena = Arena::new(512, 64).unwrap();
        let physical = arena.physical_usage();
        let before = probe.counts();
        assert_eq!(before.calls, 2);
        assert_eq!(
            before.requested_bytes,
            physical.payload_allocation_bytes + physical.object_table_bytes
        );
        let layout = PayloadLayout::new(LayoutTag::new(12), 8, 8).unwrap();
        for _ in 0..64 {
            arena
                .allocate(layout, 0, |bytes| {
                    bytes.fill(42);
                    Ok::<_, ()>(())
                })
                .unwrap();
        }
        assert_eq!(probe.counts().calls, 2);
        assert_eq!(arena.usage().object_count, 64);
        drop(arena);
        let after = probe.counts();
        assert_eq!(
            (after.deallocations, after.live, after.requested_bytes),
            (2, 0, 0)
        );
    }
    #[test]
    fn owner_identity_exhaustion_never_wraps_or_reuses_a_published_id() {
        let ids = AtomicU64::new(u64::MAX - 1);
        assert_eq!(issue_owner_id(&ids).unwrap().get(), u64::MAX - 1);
        assert_eq!(issue_owner_id(&ids).unwrap().get(), u64::MAX);
        assert_eq!(issue_owner_id(&ids), Err(ArenaInitError::IdentityExhausted));
        assert_eq!(issue_owner_id(&ids), Err(ArenaInitError::IdentityExhausted));
        assert_eq!(ids.load(Ordering::Relaxed), 0);
    }
    #[test]
    fn checked_alignment_and_end_arithmetic_refuse_overflow_without_a_backing_request() {
        assert_eq!(checked_range(usize::MAX, 0, 2), None);
        assert_eq!(checked_range(usize::MAX - 2, 0, 4), None);
        assert_eq!(
            checked_range(usize::MAX - 3, 3, 4),
            Some((usize::MAX - 3, usize::MAX))
        );
        assert_eq!(checked_range(usize::MAX - 3, 4, 4), None);
        assert_eq!(checked_range(0, 0, 64), Some((0, 0)));
    }
    #[test]
    fn private_corrupt_record_fault_rejects_before_exposing_any_payload_slice() {
        let mut arena = Arena::new(8, 1).unwrap();
        let layout = PayloadLayout::new(LayoutTag::new(13), 8, 8).unwrap();
        let key = arena
            .allocate(layout, 0, |bytes| {
                bytes.fill(42);
                Ok::<_, ()>(())
            })
            .unwrap();
        // SAFETY: Test-only corruption of the initialized in-bounds POD record;
        // no pointer/ownership field changes. Read must reject its overflowing range.
        unsafe {
            arena
                .records
                .pointer
                .cast::<ObjectRecord>()
                .as_ptr()
                .write(ObjectRecord {
                    offset: usize::MAX,
                    extent: 1,
                    layout: layout.tag,
                })
        };
        assert_eq!(arena.read(key, layout.tag), Err(AccessError::InvalidRecord));
    }
}
