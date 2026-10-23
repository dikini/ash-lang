//! CP-0024 O/X/K bookkeeping connected to existing physical owner slots.
//! Checked activation remains closed; source-bound copy observations are distinct
//! from injected or trusted native return facts.
//!
//! A native observation is an input from a future trusted bridge, not evidence
//! manufactured by this ledger. Source E and native addresses never enter it.
#![allow(
    dead_code,
    reason = "TASK0053 passive implementation is not runtime activation"
)]

use crate::{core::source_resource::CheckedSourceResourceHeader, types::TypeWorkBudget};
use std::sync::atomic::{AtomicU64, Ordering};

static NEXT: AtomicU64 = AtomicU64::new(1);

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum Failure {
    Resource,
    Stale,
    State,
    Original,
    Unsupported,
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct Group {
    ledger: u64,
    index: usize,
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct Owner {
    ledger: u64,
    index: usize,
    generation: u64,
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct Call {
    owner: Owner,
    serial: u64,
    kind: CallKind,
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum CallKind {
    Acquire,
    Borrow,
    Finish,
    CopyBytes(super::source_bindings::SourceOwnerCopyIdentity),
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum Native {
    NoOwner,
    Owned,
    Consumed,
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum K {
    Absent,
    Pending,
    Closing,
    Discharged,
    Transferred,
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum Delivery {
    Pending,
    Published,
    Failed,
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum Access {
    Unpublished,
    Usable,
    Quarantined,
    Retired,
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Outcome {
    call: Call,
    observed: Observed,
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct ClosingSnapshot {
    owner: Owner,
    operation: crate::types::OperationId,
    completion: Completion,
    native: Native,
    unresolved: bool,
}
/// One locally issued finish result. Non-Clone; never replaces source execution.
pub(super) struct FinishWitness(ClosingSnapshot);

/// Exact local closing evidence. Its constructor stays in this ledger module;
/// it is not a native-entry permission or the later source-continuation witness.
#[derive(Debug)]
pub(crate) struct SyntheticFinishWitness(ClosingSnapshot);
impl SyntheticFinishWitness {
    pub(crate) fn completion(&self) -> Completion {
        self.0.completion
    }
    pub(crate) fn native(&self) -> Native {
        self.0.native
    }
    pub(crate) fn unresolved(&self) -> bool {
        self.0.unresolved
    }
}

/// A one-shot finish entry decision. Local completion must never dispatch Free.
#[derive(Debug)]
pub(crate) enum FinishEntry {
    NativeReady,
    Synthetic(SyntheticFinishWitness),
}

fn synthetic_finish_record(
    record: &Record<'_>,
    owner: Owner,
) -> Result<SyntheticFinishWitness, Failure> {
    let snapshot = record.closing.ok_or(Failure::State)?;
    if record.k != K::Discharged
        || record.continuation != Continuation::Required
        || snapshot.owner != owner
        || snapshot.operation != record.header.teardown.operation()
        || matches!(snapshot.completion, Completion::Observed(_))
    {
        return Err(Failure::State);
    }
    Ok(SyntheticFinishWitness(snapshot))
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum History {
    Native(Outcome),
    Closed(ClosingSnapshot),
    Transferred {
        owner: Owner,
        native: Native,
        unresolved: bool,
        pending: Option<Call>,
    },
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum Continuation {
    Absent,
    Required,
    Completed,
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum Completion {
    Observed(Native),
    SessionLost,
    Quarantined,
    DependencyBlocked,
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum Close {
    NativeFinish,
    Local,
    Wait,
    Already,
    Transferred,
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum Observed {
    Copied,
    Acquired,
    Null,
    Borrowed,
    FinishedConsumed,
    FinishedRetained,
}

struct GroupState {
    lost: bool,
    quarantined: bool,
    owner_bound: bool,
}
enum Header<'p> {
    Borrowed(&'p CheckedSourceResourceHeader),
    Owned(std::sync::Arc<CheckedSourceResourceHeader>),
}
impl std::ops::Deref for Header<'_> {
    type Target = CheckedSourceResourceHeader;
    fn deref(&self) -> &Self::Target {
        match self {
            Self::Borrowed(header) => header,
            Self::Owned(header) => header,
        }
    }
}

struct Record<'p> {
    // These exact originals outlive every record and pending observation.
    header: Header<'p>,
    group: Group,
    generation: u64,
    serial: u64,
    pending: Option<Call>,
    access: Access,
    native: Native,
    unresolved: bool,
    k: K,
    delivery: Delivery,
    continuation: Continuation,
    completion: Option<Completion>,
    closing: Option<ClosingSnapshot>,
    witness_issued: bool,
}

pub(super) struct Ledger<'p> {
    identity: u64,
    groups: Vec<GroupState>,
    records: Vec<Record<'p>>,
    group_limit: usize,
    owner_limit: usize,
    history: Vec<History>,
    observed_calls: usize,
    call_limit: usize,
    in_flight: usize,
    terminal: bool,
}

fn pay(work: &mut TypeWorkBudget, count: usize) -> Result<(), Failure> {
    work.charge(count).map_err(|()| Failure::Resource)
}

impl<'p> Ledger<'p> {
    pub(super) fn reserve(
        groups: usize,
        owners: usize,
        calls: usize,
        work: &mut TypeWorkBudget,
    ) -> Result<Self, Failure> {
        // Fixed owner cells include pending, observation, K, report and source
        // continuation. Terminal transfer and native-return writes are prepaid.
        let cells = owners
            .checked_mul(24)
            .and_then(|n| n.checked_add(groups.checked_mul(3)?))
            .and_then(|n| n.checked_add(calls.checked_mul(6)?))
            .and_then(|n| n.checked_add(groups.checked_mul(owners)?.checked_mul(4)?))
            .and_then(|n| n.checked_add(4))
            .ok_or(Failure::Resource)?;
        pay(work, cells)?;
        let mut group_cells = Vec::new();
        group_cells
            .try_reserve_exact(groups)
            .map_err(|_| Failure::Resource)?;
        let mut records = Vec::new();
        records
            .try_reserve_exact(owners)
            .map_err(|_| Failure::Resource)?;
        let mut history = Vec::new();
        history
            .try_reserve_exact(calls.checked_add(owners).ok_or(Failure::Resource)?)
            .map_err(|_| Failure::Resource)?;
        let identity = NEXT
            .fetch_update(Ordering::Relaxed, Ordering::Relaxed, |n| n.checked_add(1))
            .map_err(|_| Failure::Resource)?;
        Ok(Self {
            identity,
            groups: group_cells,
            records,
            group_limit: groups,
            owner_limit: owners,
            history,
            observed_calls: 0,
            call_limit: calls,
            in_flight: 0,
            terminal: false,
        })
    }

    pub(super) fn group(&mut self, work: &mut TypeWorkBudget) -> Result<Group, Failure> {
        pay(work, 4)?;
        if self.terminal || self.groups.len() == self.group_limit {
            return Err(Failure::Resource);
        }
        let group = Group {
            ledger: self.identity,
            index: self.groups.len(),
        };
        self.groups.push(GroupState {
            lost: false,
            quarantined: false,
            owner_bound: false,
        });
        Ok(group)
    }

    fn group_index(&self, group: Group) -> Result<usize, Failure> {
        if group.ledger != self.identity || group.index >= self.groups.len() {
            return Err(Failure::Stale);
        }
        Ok(group.index)
    }

    pub(super) fn owner(
        &mut self,
        group: Group,
        header: &'p CheckedSourceResourceHeader,
        work: &mut TypeWorkBudget,
    ) -> Result<Owner, Failure> {
        self.owner_header(group, Header::Borrowed(header), work)
    }

    fn owner_header(
        &mut self,
        group: Group,
        header: Header<'p>,
        work: &mut TypeWorkBudget,
    ) -> Result<Owner, Failure> {
        pay(work, 10)?;
        let group_index = self.group_index(group)?;
        // An independent owner consumes one fresh provisional group, even if
        // another owner uses the same source H/header. Dependencies are unsupported.
        if self.groups[group_index].owner_bound {
            return Err(Failure::State);
        }
        if self.terminal
            || self.groups[group_index].lost
            || self.groups[group_index].quarantined
            || self.records.len() == self.owner_limit
        {
            return Err(Failure::Resource);
        }
        // This first increment supports the dependency-free exact void finish.
        // It does not reinterpret status-dependent contracts as void contracts.
        if !header.dependencies.is_empty()
            || header.original.host.is_none()
            || !matches!(
                header.codec.report,
                crate::core::source_resource::SourceResourceReportCodec::CheckedScope { .. }
            )
            || !matches!(
                header.teardown.owner_role(),
                Some(super::source_contract::PreparedOwnerCall::Teardown { .. })
            )
            || !header
                .acquire
                .owner()
                .is_some_and(|owner| std::sync::Arc::ptr_eq(owner, &header.owner))
            || !header
                .teardown
                .owner()
                .is_some_and(|owner| std::sync::Arc::ptr_eq(owner, &header.owner))
        {
            return Err(Failure::Unsupported);
        }
        let owner = Owner {
            ledger: self.identity,
            index: self.records.len(),
            generation: 1,
        };
        self.records.push(Record {
            header,
            group,
            generation: 1,
            serial: 0,
            pending: None,
            access: Access::Unpublished,
            native: Native::NoOwner,
            unresolved: false,
            k: K::Absent,
            delivery: Delivery::Pending,
            continuation: Continuation::Absent,
            completion: None,
            closing: None,
            witness_issued: false,
        });
        self.groups[group_index].owner_bound = true;
        Ok(owner)
    }

    fn index(&self, owner: Owner) -> Result<usize, Failure> {
        if owner.ledger != self.identity {
            return Err(Failure::Stale);
        }
        match self.records.get(owner.index) {
            Some(record) if record.generation == owner.generation => Ok(owner.index),
            _ => Err(Failure::Stale),
        }
    }

    pub(super) fn enter(
        &mut self,
        owner: Owner,
        kind: CallKind,
        original: &std::sync::Arc<super::checked_source::CheckedForeignSymbol>,
        work: &mut TypeWorkBudget,
    ) -> Result<Call, Failure> {
        // Pay all fixed observation/commit work BEFORE marking native entry.
        pay(work, 12)?;
        let index = self.index(owner)?;
        if matches!(kind, CallKind::Borrow)
            && self
                .observed_calls
                .checked_add(self.in_flight)
                .and_then(|n| n.checked_add(1))
                .is_none_or(|n| n >= self.call_limit)
        {
            return Err(Failure::Resource);
        }
        if self
            .observed_calls
            .checked_add(self.in_flight)
            .is_none_or(|n| n >= self.call_limit)
        {
            return Err(Failure::Resource);
        }
        let record = &mut self.records[index];
        let group = &self.groups[record.group.index];
        if self.terminal
            || group.lost
            || group.quarantined
            || record.pending.is_some()
            || record.unresolved
        {
            return Err(Failure::State);
        }
        let expected = match kind {
            CallKind::Acquire
                if record.k == K::Absent
                    && record.native == Native::NoOwner
                    && record.serial == 0 =>
            {
                &record.header.acquire
            }
            CallKind::Finish if record.k == K::Closing && record.native == Native::Owned => {
                &record.header.teardown
            }
            CallKind::Borrow
                if record.native == Native::Owned
                    && matches!(record.k, K::Pending | K::Closing)
                    && original.owner().is_some_and(|owner| {
                        std::sync::Arc::ptr_eq(owner, &record.header.owner)
                    })
                    && matches!(
                        original.owner_role(),
                        Some(super::source_contract::PreparedOwnerCall::Borrow { .. })
                    ) =>
            {
                original
            }
            _ => return Err(Failure::Unsupported),
        };
        if !std::sync::Arc::ptr_eq(expected, original) {
            return Err(Failure::Original);
        }
        let serial = record.serial.checked_add(1).ok_or(Failure::Resource)?;
        let call = Call {
            owner,
            serial,
            kind,
        };
        record.serial = serial;
        self.in_flight += 1;
        record.pending = Some(call);
        record.unresolved = true;
        Ok(call)
    }

    fn enter_copy(
        &mut self,
        owner: Owner,
        identity: super::source_bindings::SourceOwnerCopyIdentity,
        work: &mut TypeWorkBudget,
    ) -> Result<Call, Failure> {
        pay(work, 12)?;
        let index = self.index(owner)?;
        if self
            .observed_calls
            .checked_add(self.in_flight)
            .and_then(|n| n.checked_add(1))
            .is_none_or(|n| n >= self.call_limit)
        {
            return Err(Failure::Resource);
        }
        let record = &mut self.records[index];
        let group = &self.groups[record.group.index];
        if self.terminal
            || group.lost
            || group.quarantined
            || record.pending.is_some()
            || record.unresolved
            || record.native != Native::Owned
            || !matches!(record.k, K::Pending | K::Closing)
        {
            return Err(Failure::State);
        }
        let serial = record.serial.checked_add(1).ok_or(Failure::Resource)?;
        let call = Call {
            owner,
            serial,
            kind: CallKind::CopyBytes(identity),
        };
        record.serial = serial;
        self.in_flight += 1;
        record.pending = Some(call);
        record.unresolved = true;
        Ok(call)
    }

    pub(super) fn observed(&mut self, call: Call, observation: Observed) -> Result<(), Failure> {
        let index = self.index(call.owner)?;
        let record = &mut self.records[index];
        let group = &self.groups[record.group.index];
        if self.terminal
            || group.lost
            || group.quarantined
            || record.k == K::Discharged
            || record.pending != Some(call)
        {
            return Err(Failure::Stale);
        }
        let native = match (call.kind, observation) {
            (CallKind::Acquire, Observed::Acquired) => Native::Owned,
            (CallKind::Acquire, Observed::Null) => Native::NoOwner,
            (CallKind::CopyBytes(_), Observed::Copied) if record.native == Native::Owned => {
                Native::Owned
            }
            (CallKind::Borrow, Observed::Borrowed) if record.native == Native::Owned => {
                Native::Owned
            }
            (CallKind::Finish, Observed::FinishedConsumed)
                if matches!(
                    record.header.teardown.owner_role(),
                    Some(super::source_contract::PreparedOwnerCall::Teardown {
                        consumes: true,
                        ..
                    })
                ) =>
            {
                Native::Consumed
            }
            (CallKind::Finish, Observed::FinishedRetained)
                if matches!(
                    record.header.teardown.owner_role(),
                    Some(super::source_contract::PreparedOwnerCall::Teardown {
                        consumes: false,
                        ..
                    })
                ) =>
            {
                Native::Owned
            }
            _ => return Err(Failure::Original),
        };
        // O4 and K3: no allocation, conversion, reporting or callback intervenes.
        self.history.push(History::Native(Outcome {
            call,
            observed: observation,
        }));
        self.observed_calls += 1;
        self.in_flight -= 1;
        record.native = native;
        record.unresolved = false;
        record.pending = None;
        record.delivery = Delivery::Pending;
        if call.kind == CallKind::Finish {
            record.completion = Some(Completion::Observed(native));
            let snapshot = ClosingSnapshot {
                owner: call.owner,
                operation: record.header.teardown.operation(),
                completion: Completion::Observed(native),
                native,
                unresolved: false,
            };
            record.closing = Some(snapshot);
            self.history.push(History::Closed(snapshot));
            record.k = K::Discharged;
        }
        Ok(())
    }

    pub(super) fn publish_acquired(
        &mut self,
        owner: Owner,
        work: &mut TypeWorkBudget,
    ) -> Result<(), Failure> {
        pay(work, 4)?;
        let index = self.index(owner)?;
        let record = &mut self.records[index];
        let group = &self.groups[record.group.index];
        if self.terminal
            || group.lost
            || group.quarantined
            || record.unresolved
            || record.pending.is_some()
            || record.native != Native::Owned
            || record.k != K::Absent
            || record.serial == 0
        {
            return Err(Failure::State);
        }
        record.access = Access::Usable;
        record.k = K::Pending;
        record.delivery = Delivery::Published;
        Ok(())
    }

    pub(super) fn close(
        &mut self,
        owner: Owner,
        structural: bool,
        dependency_blocked: bool,
        work: &mut TypeWorkBudget,
    ) -> Result<Close, Failure> {
        pay(work, 8)?;
        let index = self.index(owner)?;
        let record = &mut self.records[index];
        if matches!(record.k, K::Discharged | K::Transferred) {
            return Ok(Close::Already);
        } // K7
        if self.terminal {
            if matches!(record.k, K::Pending | K::Closing) {
                record.k = K::Transferred;
                return Ok(Close::Transferred);
            }
            return Err(Failure::State);
        } // K8 applies only to unfinished published obligations
        if record.k == K::Pending && !structural {
            return Ok(Close::Wait);
        }
        if record.k == K::Pending {
            record.access = Access::Retired;
            record.k = K::Closing;
            record.continuation = Continuation::Required;
        }
        if record.k != K::Closing {
            return Err(Failure::State);
        }
        let group = &self.groups[record.group.index];
        let local = if group.lost {
            Some(Completion::SessionLost)
        } else if group.quarantined {
            Some(Completion::Quarantined)
        } else if dependency_blocked {
            Some(Completion::DependencyBlocked)
        } else {
            None
        };
        if let Some(completion) = local {
            record.completion = Some(completion);
            let snapshot = ClosingSnapshot {
                owner,
                operation: record.header.teardown.operation(),
                completion,
                native: record.native,
                unresolved: record.unresolved,
            };
            record.closing = Some(snapshot);
            self.history.push(History::Closed(snapshot));
            record.k = K::Discharged;
            return Ok(Close::Local);
        }
        if record.pending.is_some() {
            return Err(Failure::State);
        }
        Ok(Close::NativeFinish)
    }

    pub(super) fn lose_group(&mut self, group: Group, quarantine: bool) -> Result<(), Failure> {
        let index = self.group_index(group)?;
        if if quarantine {
            self.groups[index].quarantined
        } else {
            self.groups[index].lost
        } {
            return Ok(());
        }
        // Each group can install these two irreversible events once. Reservation
        // prepays two full owner revocation walks; no event is erased by X1.
        if quarantine {
            self.groups[index].quarantined = true;
        } else {
            self.groups[index].lost = true;
        }
        // Group flags revoke access without changing the last observation.
        for record in &mut self.records {
            if record.group == group {
                record.access = if quarantine {
                    Access::Quarantined
                } else {
                    Access::Retired
                };
            }
        }
        // Entered unresolved facts stay unresolved; neither loss nor quarantine
        // creates a native observation or pretends ownership was consumed.
        Ok(())
    }

    pub(super) fn output_failed(&mut self) {
        // O8/K8 storage and traversal were reserved before any owner entry.
        if self.terminal {
            return;
        }
        self.terminal = true;
        for (index, record) in self.records.iter_mut().enumerate() {
            record.access = Access::Retired;
            record.delivery = Delivery::Failed;
            if matches!(record.k, K::Pending | K::Closing) {
                self.history.push(History::Transferred {
                    owner: Owner {
                        ledger: self.identity,
                        index,
                        generation: record.generation,
                    },
                    native: record.native,
                    unresolved: record.unresolved,
                    pending: record.pending,
                });
                record.k = K::Transferred;
            }
        }
    }

    pub(super) fn finish_witness(
        &mut self,
        owner: Owner,
        work: &mut TypeWorkBudget,
    ) -> Result<FinishWitness, Failure> {
        pay(work, 4)?;
        let index = self.index(owner)?;
        let record = &mut self.records[index];
        if self.terminal || record.k != K::Discharged || record.witness_issued {
            return Err(Failure::State);
        }
        let snapshot = record.closing.ok_or(Failure::State)?;
        record.witness_issued = true;
        Ok(FinishWitness(snapshot))
    }

    pub(super) fn source_continued(
        &mut self,
        owner: Owner,
        witness: FinishWitness,
        work: &mut TypeWorkBudget,
    ) -> Result<(), Failure> {
        pay(work, 3)?;
        let index = self.index(owner)?;
        let record = &mut self.records[index];
        if self.terminal
            || record.k != K::Discharged
            || record.continuation != Continuation::Required
            || !record.witness_issued
            || record.closing != Some(witness.0)
            || witness.0.owner != owner
        {
            return Err(Failure::State);
        }
        record.continuation = Continuation::Completed;
        record.delivery = Delivery::Published;
        Ok(())
    }
}

/// Finite resource data only. It is neither protected policy nor approval.
#[derive(Clone, Copy, Debug)]
pub(crate) struct BoundaryLimits {
    pub(crate) groups: usize,
    pub(crate) owners: usize,
    pub(crate) pending: usize,
    pub(crate) observations: usize,
    pub(crate) history: usize,
    pub(crate) continuations: usize,
}

/// Runtime bookkeeping stored in the existing physical owner slot. It carries
/// no native callback, address, executable approval or invocation constructor.
pub(super) struct RuntimeBoundary {
    ledger: Ledger<'static>,
    owner: Owner,
    group: Group,
    scope: std::sync::Arc<crate::core::source_resource::CheckedSourceResourceTemplate>,
    scope_node: crate::core::NodeId,
    activation: usize,
    acquire_request: crate::core::NodeId,
    pending: Option<Call>,
    finish_prepared: Option<FinishEntry>,
    finish_claimed: bool,
    // These fixed future ledger operations were paid before native entry.
    prepaid: TypeWorkBudget,
}
impl std::fmt::Debug for RuntimeBoundary {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("RuntimeBoundary")
            .field("activation", &self.activation)
            .finish_non_exhaustive()
    }
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct BoundarySnapshot {
    pub(crate) identity: u64,
    pub(crate) native: Native,
    pub(crate) k: K,
    pub(crate) unresolved: bool,
    pub(crate) continuation: Continuation,
    pub(crate) terminal: bool,
    pub(crate) observations: usize,
    pub(crate) history: usize,
    pub(super) last_copy: Option<super::source_bindings::SourceOwnerCopyIdentity>,
}
#[cfg(test)]
impl BoundarySnapshot {
    pub(crate) fn last_copy_coordinates(
        self,
    ) -> Option<(
        crate::core::NodeId,
        crate::core::NodeId,
        crate::core::NodeId,
        crate::resolved::BinderId,
    )> {
        self.last_copy.map(|identity| {
            (
                identity.window,
                identity.apply,
                identity.application,
                identity.function,
            )
        })
    }
}
impl RuntimeBoundary {
    pub(super) fn reserve(
        receipt: &super::source_bindings::SourceOwnerScopeRequest,
        activation: usize,
        limits: BoundaryLimits,
        work: &mut TypeWorkBudget,
    ) -> Result<Self, Failure> {
        pay(work, 6)?;
        let minimum = receipt
            ._scope
            .header()
            .original
            .interpreted
            .len()
            .max(2)
            .checked_add(receipt._copy_calls.ok_or(Failure::Unsupported)?)
            .and_then(|n| n.checked_add(receipt._window_calls))
            .ok_or(Failure::Resource)?;
        if limits.groups != 1
            || limits.owners != 1
            || limits.pending < 1
            || limits.observations < minimum
            || limits.continuations < 1
            || limits.history
                < limits
                    .observations
                    .checked_add(1)
                    .ok_or(Failure::Resource)?
        {
            return Err(Failure::Resource);
        }
        if receipt._phase != super::source_bindings::SourceOwnerPhase::Acquire
            || receipt._window.is_some()
        {
            return Err(Failure::Original);
        }
        // Pay scope/header retention and a bounded set of nonowning slot handles.
        // Future enter/commit/witness operations use only the prepaid meter.
        let future = limits
            .observations
            .checked_mul(12)
            .and_then(|n| n.checked_add(8 + 8 + 4 + 3 + 3 + 8))
            .ok_or(Failure::Resource)?;
        pay(work, future.checked_add(2 + 3).ok_or(Failure::Resource)?)?;
        let mut ledger = Ledger::reserve(limits.groups, limits.owners, limits.observations, work)?;
        let group = ledger.group(work)?;
        let owner = ledger.owner_header(
            group,
            Header::Owned(std::sync::Arc::clone(receipt._scope.header())),
            work,
        )?;
        Ok(Self {
            ledger,
            owner,
            group,
            scope: std::sync::Arc::clone(&receipt._scope),
            scope_node: receipt._scope_node,
            activation,
            acquire_request: receipt._request,
            pending: None,
            finish_prepared: None,
            finish_claimed: false,
            prepaid: TypeWorkBudget::with_limit(future),
        })
    }
    pub(super) fn begin_acquire(&mut self) -> Result<(), Failure> {
        let call = self.ledger.enter(
            self.owner,
            CallKind::Acquire,
            &self.scope.header().acquire,
            &mut self.prepaid,
        )?;
        self.pending = Some(call);
        Ok(())
    }
    pub(super) fn acquired(&mut self, present: bool) {
        if let Some(call) = self.pending.take() {
            // The single-use native ticket and exclusive slot borrow establish
            // this exact transition before conversion or source reporting.
            self.ledger
                .observed(
                    call,
                    if present {
                        Observed::Acquired
                    } else {
                        Observed::Null
                    },
                )
                .expect("reserved acquisition observation");
        }
    }
    pub(super) fn publish(
        &mut self,
        activation: usize,
        scope: crate::core::NodeId,
        work: &mut TypeWorkBudget,
    ) -> Result<(), Failure> {
        pay(work, 2)?;
        if activation != self.activation || scope != self.scope_node {
            return Err(Failure::Original);
        }
        self.ledger.publish_acquired(self.owner, work)
    }
    pub(super) fn borrow_request(
        &self,
        receipt: &super::source_bindings::SourceOwnerScopeRequest,
        activation: usize,
        original: &std::sync::Arc<super::checked_source::CheckedForeignSymbol>,
        work: &mut TypeWorkBudget,
    ) -> Result<(), Failure> {
        pay(work, 6)?;
        if activation != self.activation
            || receipt._scope_node != self.scope_node
            || !std::sync::Arc::ptr_eq(&receipt._scope, &self.scope)
            || !matches!(
                receipt._phase,
                super::source_bindings::SourceOwnerPhase::Borrow(
                    crate::core::source_resource::SourceResourcePhase::Handler
                        | crate::core::source_resource::SourceResourcePhase::Finish
                )
            )
            || !original
                .owner()
                .is_some_and(|owner| std::sync::Arc::ptr_eq(owner, &self.scope.header().owner))
            || !matches!(
                original.owner_role(),
                Some(super::source_contract::PreparedOwnerCall::Borrow { .. })
            )
        {
            return Err(Failure::Original);
        }
        let record = &self.ledger.records[self.owner.index];
        if self.ledger.terminal
            || record.unresolved
            || record.pending.is_some()
            || record.native != Native::Owned
            || !matches!(record.k, K::Pending | K::Closing)
        {
            return Err(Failure::State);
        }
        if self
            .ledger
            .observed_calls
            .checked_add(self.ledger.in_flight)
            .and_then(|n| n.checked_add(1))
            .is_none_or(|n| n >= self.ledger.call_limit)
        {
            return Err(Failure::Resource);
        }
        Ok(())
    }
    pub(super) fn copy_request(
        &self,
        receipt: &super::source_bindings::SourceOwnerCopyRequest,
        activation: usize,
        work: &mut TypeWorkBudget,
    ) -> Result<(), Failure> {
        pay(work, 5)?;
        if activation != self.activation
            || receipt.scope_node != self.scope_node
            || !std::sync::Arc::ptr_eq(&receipt.scope, &self.scope)
            || !matches!(
                receipt.phase,
                crate::core::source_resource::SourceResourcePhase::Handler
                    | crate::core::source_resource::SourceResourcePhase::Finish
            )
        {
            return Err(Failure::Original);
        }
        let record = &self.ledger.records[self.owner.index];
        if self.ledger.terminal
            || record.unresolved
            || record.pending.is_some()
            || record.native != Native::Owned
            || !matches!(record.k, K::Pending | K::Closing)
        {
            return Err(Failure::State);
        }
        if self
            .ledger
            .observed_calls
            .checked_add(self.ledger.in_flight)
            .and_then(|n| n.checked_add(1))
            .is_none_or(|n| n >= self.ledger.call_limit)
        {
            return Err(Failure::Resource);
        }
        Ok(())
    }
    pub(super) fn begin_copy(
        &mut self,
        identity: super::source_bindings::SourceOwnerCopyIdentity,
        entry_work: &mut TypeWorkBudget,
    ) -> Result<(), Failure> {
        self.pending = Some(self.ledger.enter_copy(self.owner, identity, entry_work)?);
        Ok(())
    }
    pub(super) fn copied(&mut self) {
        let call = self.pending.take().expect("single entered primitive copy");
        self.ledger
            .observed(call, Observed::Copied)
            .expect("reserved copy observation");
    }
    pub(super) fn begin_borrow(
        &mut self,
        original: &std::sync::Arc<super::checked_source::CheckedForeignSymbol>,
    ) -> Result<(), Failure> {
        self.pending =
            Some(
                self.ledger
                    .enter(self.owner, CallKind::Borrow, original, &mut self.prepaid)?,
            );
        Ok(())
    }
    pub(super) fn borrowed(&mut self) {
        let call = self.pending.take().expect("single entered borrow request");
        self.ledger
            .observed(call, Observed::Borrowed)
            .expect("reserved borrow observation");
    }
    pub(super) fn closing(
        &mut self,
        activation: usize,
        scope: crate::core::NodeId,
        work: &mut TypeWorkBudget,
    ) -> Result<(), Failure> {
        pay(work, 2)?;
        if activation != self.activation || scope != self.scope_node {
            return Err(Failure::Original);
        }
        match self
            .ledger
            .close(self.owner, true, false, &mut self.prepaid)?
        {
            Close::NativeFinish | Close::Local => Ok(()),
            _ => Err(Failure::State),
        }
    }
    pub(super) fn prepare_finish(
        &mut self,
        receipt: &super::source_bindings::SourceOwnerScopeRequest,
        activation: usize,
        blocked: bool,
        work: &mut TypeWorkBudget,
    ) -> Result<(), Failure> {
        pay(work, 6)?;
        if activation != self.activation
            || receipt._scope_node != self.scope_node
            || receipt._phase != super::source_bindings::SourceOwnerPhase::Finish
            || receipt._window.is_some()
            || receipt._request == self.acquire_request
            || !std::sync::Arc::ptr_eq(&receipt._scope, &self.scope)
        {
            return Err(Failure::Original);
        }
        if self.finish_claimed || self.finish_prepared.is_some() || self.pending.is_some() {
            return Err(Failure::State);
        }
        let entry = match self
            .ledger
            .close(self.owner, true, blocked, &mut self.prepaid)?
        {
            Close::NativeFinish => FinishEntry::NativeReady,
            Close::Local | Close::Already => {
                pay(&mut self.prepaid, 8)?;
                FinishEntry::Synthetic(synthetic_finish_record(
                    &self.ledger.records[self.owner.index],
                    self.owner,
                )?)
            }
            _ => return Err(Failure::State),
        };
        self.finish_claimed = true;
        self.finish_prepared = Some(entry);
        Ok(())
    }
    pub(super) fn begin_finish_entry(&mut self) -> Result<FinishEntry, Failure> {
        pay(&mut self.prepaid, 3)?;
        let entry = self.finish_prepared.take().ok_or(Failure::State)?;
        match &entry {
            FinishEntry::NativeReady => {
                self.pending = Some(self.ledger.enter(
                    self.owner,
                    CallKind::Finish,
                    &self.scope.header().teardown,
                    &mut self.prepaid,
                )?);
            }
            FinishEntry::Synthetic(witness) => {
                let record = &self.ledger.records[self.owner.index];
                if self.ledger.terminal
                    || record.k != K::Discharged
                    || record.closing != Some(witness.0)
                    || record.continuation != Continuation::Required
                {
                    return Err(Failure::State);
                }
            }
        }
        Ok(entry)
    }
    /// Legacy teardown dispatch accepts only actual native readiness. The
    /// checked path must consume the complete entry decision instead.
    pub(super) fn begin_finish(&mut self) -> Result<(), Failure> {
        match self.begin_finish_entry()? {
            FinishEntry::NativeReady => Ok(()),
            FinishEntry::Synthetic(_) => Err(Failure::State),
        }
    }
    pub(super) fn finished(&mut self, consumed: bool) {
        if let Some(call) = self.pending.take() {
            self.ledger
                .observed(
                    call,
                    if consumed {
                        Observed::FinishedConsumed
                    } else {
                        Observed::FinishedRetained
                    },
                )
                .expect("reserved finish observation");
        }
    }
    pub(super) fn quarantine(&mut self) {
        self.ledger
            .lose_group(self.group, true)
            .expect("reserved owner group");
    }
    pub(super) fn output_failed(&mut self) {
        self.ledger.output_failed();
    }
    pub(super) fn source_continued(
        &mut self,
        activation: usize,
        scope: crate::core::NodeId,
    ) -> Result<(), Failure> {
        if activation != self.activation || scope != self.scope_node {
            return Err(Failure::Original);
        }
        if !self.finish_claimed || self.finish_prepared.is_some() || self.pending.is_some() {
            return Err(Failure::State);
        }
        let witness = self.ledger.finish_witness(self.owner, &mut self.prepaid)?;
        self.ledger
            .source_continued(self.owner, witness, &mut self.prepaid)
    }
    /// Fixed-size admitted facts only. Unlike the diagnostic snapshot, this
    /// does not scan history or reconstruct a native transition.
    pub(super) fn closing_record(&self) -> (Option<Completion>, K, Native, bool) {
        let record = &self.ledger.records[self.owner.index];
        (record.completion, record.k, record.native, record.unresolved)
    }
    pub(super) fn snapshot(&self) -> BoundarySnapshot {
        let record = &self.ledger.records[self.owner.index];
        BoundarySnapshot {
            last_copy: self
                .ledger
                .history
                .iter()
                .rev()
                .find_map(|history| match history {
                    History::Native(Outcome {
                        call:
                            Call {
                                kind: CallKind::CopyBytes(identity),
                                ..
                            },
                        observed: Observed::Copied,
                    }) => Some(*identity),
                    _ => None,
                }),
            identity: self.ledger.identity,
            native: record.native,
            k: record.k,
            unresolved: record.unresolved,
            continuation: record.continuation,
            terminal: self.ledger.terminal,
            observations: self.ledger.observed_calls,
            history: self.ledger.history.len(),
        }
    }
}

#[cfg(test)]
pub(crate) fn assert_dependent_header_refused_before_entry(
    parent: &CheckedSourceResourceHeader,
    child: &CheckedSourceResourceHeader,
) {
    assert!(parent.dependencies.is_empty());
    assert!(!child.dependencies.is_empty());
    let mut work = TypeWorkBudget::default();
    let mut ledger = Ledger::reserve(2, 2, 2, &mut work).unwrap();
    let parent_group = ledger.group(&mut work).unwrap();
    ledger.owner(parent_group, parent, &mut work).unwrap();
    let child_group = ledger.group(&mut work).unwrap();
    let before = (
        ledger.records.len(),
        ledger.history.len(),
        ledger.observed_calls,
        ledger.in_flight,
    );
    assert!(matches!(
        ledger.owner(child_group, child, &mut work),
        Err(Failure::Unsupported)
    ));
    assert_eq!(
        (
            ledger.records.len(),
            ledger.history.len(),
            ledger.observed_calls,
            ledger.in_flight
        ),
        before
    );
    assert!(!ledger.groups[child_group.index].owner_bound);
    assert_eq!(ledger.records.len(), 1);
    assert_eq!(ledger.records[0].native, Native::NoOwner);
    assert_eq!(ledger.records[0].k, K::Absent);
    assert!(ledger.records[0].pending.is_none());
    assert!(ledger.history.is_empty());
    assert_eq!(ledger.observed_calls, 0);
    assert_eq!(ledger.in_flight, 0);
}

#[cfg(test)]
mod tests {
    use super::*;

    fn with_header(test: impl FnOnce(&CheckedSourceResourceHeader)) {
        let (program, _provenance) = crate::elaborate::checked_owner_passive_program();
        let fact = program
            .registry()
            .source_resource_facts()
            .find(|fact| {
                matches!(
                    fact.codec.kind,
                    crate::surface::SurfaceResourceReportCodecKind::CheckedScope
                )
            })
            .unwrap();
        let header = CheckedSourceResourceHeader::admit(
            fact,
            program.registry(),
            &mut TypeWorkBudget::default(),
        )
        .unwrap();
        test(&header);
    }

    fn acquired<'p>(header: &'p CheckedSourceResourceHeader) -> (Ledger<'p>, Owner) {
        let mut work = TypeWorkBudget::default();
        let mut ledger = Ledger::reserve(2, 2, 4, &mut work).unwrap();
        let group = ledger.group(&mut work).unwrap();
        let owner = ledger.owner(group, header, &mut work).unwrap();
        let call = ledger
            .enter(owner, CallKind::Acquire, &header.acquire, &mut work)
            .unwrap();
        ledger.observed(call, Observed::Acquired).unwrap();
        ledger.publish_acquired(owner, &mut work).unwrap();
        (ledger, owner)
    }

    #[test]
    fn local_finish_has_exact_non_native_witness_and_preserves_continuation() {
        with_header(|header| {
            let (mut ledger, owner) = acquired(header);
            let group = ledger.records[owner.index].group;
            ledger.lose_group(group, true).unwrap();
            let mut work = TypeWorkBudget::default();
            assert_eq!(
                ledger.close(owner, true, false, &mut work),
                Ok(Close::Local)
            );
            let witness = synthetic_finish_record(&ledger.records[owner.index], owner).unwrap();
            assert_eq!(witness.completion(), Completion::Quarantined);
            assert_eq!(witness.native(), Native::Owned);
            assert!(!witness.unresolved());
            assert_eq!(ledger.observed_calls, 1); // no fabricated native Finish
            assert_eq!(
                ledger.records[owner.index].continuation,
                Continuation::Required
            );
            assert!(
                ledger
                    .enter(owner, CallKind::Finish, &header.teardown, &mut work)
                    .is_err()
            );
            let source = ledger.finish_witness(owner, &mut work).unwrap();
            ledger.source_continued(owner, source, &mut work).unwrap();
            assert!(synthetic_finish_record(&ledger.records[owner.index], owner).is_err());

            let (mut native, owner) = acquired(header);
            assert_eq!(
                native.close(owner, true, false, &mut work),
                Ok(Close::NativeFinish)
            );
            let call = native
                .enter(owner, CallKind::Finish, &header.teardown, &mut work)
                .unwrap();
            native.observed(call, Observed::FinishedConsumed).unwrap();
            assert!(synthetic_finish_record(&native.records[owner.index], owner).is_err());
        });
    }

    #[test]
    fn checked_control_finish_commit_survives_source_failure_without_replay() {
        with_header(|header| {
            let (mut ledger, owner) = acquired(header);
            let mut work = TypeWorkBudget::default();
            assert_eq!(
                ledger.close(owner, true, false, &mut work),
                Ok(Close::NativeFinish)
            );
            let call = ledger
                .enter(owner, CallKind::Finish, &header.teardown, &mut work)
                .unwrap();
            ledger.observed(call, Observed::FinishedConsumed).unwrap();
            let witness = ledger.finish_witness(owner, &mut work).unwrap();
            assert!(ledger.finish_witness(owner, &mut work).is_err());
            ledger.output_failed();
            let record = &ledger.records[owner.index];
            assert_eq!(record.native, Native::Consumed);
            assert_eq!(ledger.history.len(), 3);
            assert!(matches!(
                ledger.history[1],
                History::Native(Outcome {
                    observed: Observed::FinishedConsumed,
                    ..
                })
            ));
            assert!(matches!(
                ledger.history[2],
                History::Closed(ClosingSnapshot {
                    completion: Completion::Observed(Native::Consumed),
                    ..
                })
            ));
            assert_eq!(record.k, K::Discharged);
            assert_eq!(
                record.completion,
                Some(Completion::Observed(Native::Consumed))
            );
            assert_eq!(record.continuation, Continuation::Required);
            assert_eq!(
                ledger.close(owner, true, true, &mut work),
                Ok(Close::Already)
            ); // K7 before K8
            assert_eq!(
                ledger.observed(call, Observed::FinishedConsumed),
                Err(Failure::Stale)
            );
            assert!(
                ledger
                    .enter(owner, CallKind::Finish, &header.teardown, &mut work)
                    .is_err()
            );
            assert!(ledger.source_continued(owner, witness, &mut work).is_err());
        });
    }

    #[test]
    fn checked_control_groups_loss_precedence_and_stale_handles_are_distinct() {
        with_header(|header| {
            let (mut ledger, owner) = acquired(header);
            let mut work = TypeWorkBudget::default();
            let first_group = ledger.records[owner.index].group;
            assert_eq!(
                ledger.owner(first_group, header, &mut work),
                Err(Failure::State)
            );
            assert_eq!(ledger.records.len(), 1);
            let other_group = ledger.group(&mut work).unwrap();
            assert_ne!(first_group, other_group);
            let other = ledger.owner(other_group, header, &mut work).unwrap(); // same header/H, different group
            assert_eq!(
                ledger.owner(other_group, header, &mut work),
                Err(Failure::State)
            );
            assert_eq!(ledger.records.len(), 2);
            let other_call = ledger
                .enter(other, CallKind::Acquire, &header.acquire, &mut work)
                .unwrap();
            ledger.observed(other_call, Observed::Acquired).unwrap();
            ledger.publish_acquired(other, &mut work).unwrap();
            let group = ledger.records[owner.index].group;
            ledger.lose_group(group, true).unwrap();
            ledger.lose_group(group, false).unwrap();
            assert_eq!(ledger.close(owner, false, true, &mut work), Ok(Close::Wait));
            assert_eq!(ledger.close(owner, true, true, &mut work), Ok(Close::Local));
            assert_eq!(
                ledger.records[owner.index].completion,
                Some(Completion::SessionLost)
            );
            assert_eq!(ledger.records[owner.index].native, Native::Owned); // no fabricated consumption
            assert_eq!(
                ledger.close(other, true, false, &mut work),
                Ok(Close::NativeFinish)
            );
            let stale = Owner {
                generation: 2,
                ..other
            };
            assert_eq!(
                ledger.enter(stale, CallKind::Finish, &header.teardown, &mut work),
                Err(Failure::Stale)
            );
            assert_eq!(
                ledger.enter(other, CallKind::Finish, &header.acquire, &mut work),
                Err(Failure::Original)
            );
            let call = ledger
                .enter(other, CallKind::Finish, &header.teardown, &mut work)
                .unwrap();
            ledger.output_failed(); // K8 preserves unresolved call, does not finish/replay it
            assert_eq!(ledger.records[other.index].k, K::Transferred);
            assert!(ledger.records[other.index].unresolved);
            assert_eq!(
                ledger.observed(call, Observed::FinishedConsumed),
                Err(Failure::Stale)
            );
        });
    }

    #[test]
    fn checked_control_unpublished_guard_and_prepaid_loss_survive_terminal() {
        with_header(|header| {
            let mut work = TypeWorkBudget::default();
            let mut ledger = Ledger::reserve(1, 1, 2, &mut work).unwrap();
            let group = ledger.group(&mut work).unwrap();
            let owner = ledger.owner(group, header, &mut work).unwrap();
            let call = ledger
                .enter(owner, CallKind::Acquire, &header.acquire, &mut work)
                .unwrap();
            ledger.observed(call, Observed::Acquired).unwrap();
            ledger.output_failed();
            assert_eq!(ledger.records[owner.index].k, K::Absent);
            assert_eq!(ledger.records[owner.index].native, Native::Owned);
            assert_eq!(ledger.records[owner.index].access, Access::Retired);
            assert_eq!(ledger.records[owner.index].group, group);
            assert_eq!(
                ledger.close(owner, true, false, &mut work),
                Err(Failure::State)
            );
            // No native guard/disposal is wired yet: the retained fact cannot
            // be presented as a disposed allocation or a discharged K.

            let (mut ledger, owner) = acquired(header);
            let group = ledger.records[owner.index].group;
            assert_eq!(
                ledger.close(owner, true, false, &mut work),
                Ok(Close::NativeFinish)
            );
            let call = ledger
                .enter(owner, CallKind::Finish, &header.teardown, &mut work)
                .unwrap();
            let mut exhausted = TypeWorkBudget::with_limit(0);
            ledger.lose_group(group, true).unwrap(); // prepaid irreversible event
            ledger.lose_group(group, false).unwrap();
            assert_eq!(exhausted.used(), 0);
            assert_eq!(
                ledger.close(owner, true, false, &mut exhausted),
                Err(Failure::Resource)
            );
            ledger.output_failed();
            assert!(ledger.groups[group.index].lost && ledger.groups[group.index].quarantined);
            assert_eq!(ledger.records[owner.index].native, Native::Owned);
            assert!(ledger.records[owner.index].unresolved);
            assert_eq!(ledger.records[owner.index].pending, Some(call));
            assert_eq!(ledger.records[owner.index].access, Access::Retired);
            assert_eq!(ledger.records[owner.index].k, K::Transferred);
        });
    }

    #[test]
    fn checked_control_local_close_witness_retains_reason_and_required_source_step() {
        with_header(|header| {
            for quarantine in [false, true] {
                let (mut ledger, owner) = acquired(header);
                let mut work = TypeWorkBudget::default();
                if quarantine {
                    ledger
                        .lose_group(ledger.records[owner.index].group, true)
                        .unwrap();
                }
                assert_eq!(ledger.close(owner, true, true, &mut work), Ok(Close::Local));
                let expected = if quarantine {
                    Completion::Quarantined
                } else {
                    Completion::DependencyBlocked
                };
                let witness = ledger.finish_witness(owner, &mut work).unwrap();
                assert_eq!(witness.0.owner, owner);
                assert_eq!(witness.0.operation, header.teardown.operation());
                assert_eq!(witness.0.completion, expected);
                assert_eq!(witness.0.native, Native::Owned);
                assert!(!witness.0.unresolved);
                assert!(ledger.finish_witness(owner, &mut work).is_err());
                assert_eq!(
                    ledger.records[owner.index].continuation,
                    Continuation::Required
                );
                // This is a passive transition input, not authentication of a
                // dependency graph or execution of the authored source finish.
                ledger.source_continued(owner, witness, &mut work).unwrap();
                assert_eq!(
                    ledger.records[owner.index].continuation,
                    Continuation::Completed
                );
                assert_eq!(
                    ledger.close(owner, true, true, &mut work),
                    Ok(Close::Already)
                );
            }
        });
    }

    #[test]
    fn checked_control_short_work_and_capacity_refuse_before_entry_and_retry_fresh() {
        with_header(|header| {
            let measure = |work: &mut TypeWorkBudget| {
                let mut ledger = Ledger::reserve(1, 1, 2, work)?;
                let group = ledger.group(work)?;
                let owner = ledger.owner(group, header, work)?;
                ledger.enter(owner, CallKind::Acquire, &header.acquire, work)?;
                Ok::<_, Failure>(ledger)
            };
            let mut measured = TypeWorkBudget::default();
            measure(&mut measured).unwrap();
            for prefix in [0, 7] {
                let mut exact = TypeWorkBudget::with_limit(prefix + measured.used());
                exact.charge(prefix).unwrap();
                assert!(measure(&mut exact).is_ok());
                let mut short = TypeWorkBudget::with_limit(prefix + measured.used() - 1);
                short.charge(prefix).unwrap();
                assert!(matches!(measure(&mut short), Err(Failure::Resource)));
                assert!(matches!(measure(&mut short), Err(Failure::Resource))); // spent retry
            }
            assert!(measure(&mut TypeWorkBudget::default()).is_ok());
            let mut work = TypeWorkBudget::default();
            let mut ledger = Ledger::reserve(1, 0, 0, &mut work).unwrap();
            let group = ledger.group(&mut work).unwrap();
            assert_eq!(
                ledger.owner(group, header, &mut work),
                Err(Failure::Resource)
            );
            assert!(ledger.records.is_empty());
        });
    }
}
