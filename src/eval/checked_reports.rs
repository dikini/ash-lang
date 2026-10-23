//! Independent checked-resource observations. These values confer no authority.
use super::{Evaluation, RuntimeFailure};
use crate::types::TypeWorkBudget;
use std::{cell::Cell, rc::Rc, sync::atomic::{AtomicU64, Ordering}};

static NEXT_REPORTS: AtomicU64 = AtomicU64::new(1);

/// Last admitted native ownership fact, distinct from later uncertainty.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ResourceNativeFact {
    /// No native owner was returned.
    NoOwner,
    /// A native owner was observed live.
    Owned,
    /// Native consumption was observed.
    Consumed,
    /// The admitted native observation was unknown.
    Unknown,
}

/// Primary structural closing reason; source result E is kept separately.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ResourceClosing {
    /// A returning native finish consumed the owner.
    NativeConsumed,
    /// A returning native finish retained the owner.
    NativeRetained,
    /// Session loss prevented native completion.
    SessionLost,
    /// A live dependent prevented native completion.
    DependencyBlocked,
    /// Quarantine prevented native completion.
    Quarantined,
    /// A terminal path transferred the outstanding obligation.
    Transferred,
}

/// Actual backing observation for unpublished guard disposal. It is not source K,
/// disposal success or an authenticated protected-retention promise.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum GuardBackingObservation {
    /// The same private owner slot still retains native backing at observation.
    Retained,
    /// No independent disposal or retained-backing observation was available.
    Unknown,
}

/// Actual placement of a nonauthorizing guard observation.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum GuardInspectionPoint {
    /// Snapshot after the unpublished guard's host disposal path returned.
    /// Backing absence alone still does not establish native consumption.
    AfterUnpublishedDisposal,
    /// Snapshot at terminal traversal before physical owner quarantine.
    TerminalBeforeQuarantine,
    /// Snapshot after a failed return path has disposed its boundary owner.
    ReturnFailureAfterDisposal,
}

/// Separate supervisor inspection for a never-published acquisition. This is
/// deliberately outside the K3–6 ordered scope-closing channel.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct UnpublishedGuardInspection {
    native: ResourceNativeFact,
    unresolved: bool,
    status: Option<i128>,
    backing: GuardBackingObservation,
    point: GuardInspectionPoint,
}
impl UnpublishedGuardInspection {
    pub(crate) fn observed(native: ResourceNativeFact, unresolved: bool, status: Option<i128>, backing: GuardBackingObservation, point: GuardInspectionPoint) -> Self {
        Self { native, unresolved, status, backing, point }
    }
    /// Last recorded native fact, without source ownership publication.
    pub fn native(&self) -> ResourceNativeFact { self.native }
    /// Whether the native transition remains unresolved.
    pub fn unresolved(&self) -> bool { self.unresolved }
    /// Exact recorded scalar status or genuine absence.
    pub fn status(&self) -> Option<i128> { self.status }
    /// Backing at this observation; not a promise of later disposal.
    pub fn backing(&self) -> GuardBackingObservation { self.backing }
    /// Structural point where these particular backing facts were observed.
    pub fn point(&self) -> GuardInspectionPoint { self.point }
}

/// Independent diagnostic data, never a replacement for mandatory facts.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ResourceDiagnostic {
    /// This operation declares no requested diagnostic.
    NotRequested,
    /// Optional diagnostic allowance was refused.
    AllowanceRefused,
    /// Native code provided no diagnostic.
    NativeAbsent,
    /// A bounded scan did not find a permitted end.
    ScanBoundExceeded,
    /// Native diagnostic bytes had invalid encoding.
    InvalidEncoding,
    /// A diagnostic was lost before independent admission.
    Lost,
    /// Independently copied bounded diagnostic text.
    Text(Box<str>),
}

/// Immutable closing observation. It contains neither source A/E nor addresses.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResourceReport {
    closing: ResourceClosing,
    native: ResourceNativeFact,
    unresolved: bool,
    // Every scalar ABI in the selected GNU profile fits exactly in i128.
    // In particular, absence must not be replaced with numeric zero.
    status: Option<i128>,
    diagnostic: ResourceDiagnostic,
}
impl ResourceReport {
    /// Copy only the fixed ledger facts. Native status is supplied by the
    /// actual returned-call recorder, never reconstructed from the closing kind.
    pub(crate) fn closing_facts(
        completion: Option<crate::foreign::source_runtime::CheckedCompletion>,
        k: crate::foreign::source_runtime::CheckedLocalCompletion,
        native: crate::foreign::source_runtime::CheckedNativeFact,
        unresolved: bool,
        status: Option<i128>,
    ) -> Option<Self> {
        use crate::foreign::source_runtime::{
            CheckedCompletion as Completion, CheckedLocalCompletion as K,
            CheckedNativeFact as Native,
        };
        let closing = match (completion, k) {
            (_, K::Transferred) => ResourceClosing::Transferred,
            (Some(Completion::Observed(Native::Consumed)), K::Discharged) => ResourceClosing::NativeConsumed,
            (Some(Completion::Observed(Native::Owned)), K::Discharged) => ResourceClosing::NativeRetained,
            (Some(Completion::SessionLost), K::Discharged) => ResourceClosing::SessionLost,
            (Some(Completion::DependencyBlocked), K::Discharged) => ResourceClosing::DependencyBlocked,
            (Some(Completion::Quarantined), K::Discharged) => ResourceClosing::Quarantined,
            _ => return None,
        };
        let native = match native {
            Native::NoOwner => ResourceNativeFact::NoOwner,
            Native::Owned => ResourceNativeFact::Owned,
            Native::Consumed => ResourceNativeFact::Consumed,
        };
        Some(Self::observed(closing, native, unresolved, status, ResourceDiagnostic::NotRequested))
    }
    pub(crate) fn observed(
        closing: ResourceClosing,
        native: ResourceNativeFact,
        unresolved: bool,
        status: Option<i128>,
        diagnostic: ResourceDiagnostic,
    ) -> Self {
        Self {
            closing,
            native,
            unresolved,
            status,
            diagnostic,
        }
    }
    /// Primary closing reason.
    pub fn closing(&self) -> ResourceClosing {
        self.closing
    }
    /// Last admitted native ownership fact.
    pub fn native(&self) -> ResourceNativeFact {
        self.native
    }
    /// Whether a later native transition remains unresolved.
    pub fn unresolved(&self) -> bool {
        self.unresolved
    }
    /// Exact native scalar status, or genuine absence.
    pub fn status(&self) -> Option<i128> {
        self.status
    }
    /// Independent optional diagnostic observation.
    pub fn diagnostic(&self) -> &ResourceDiagnostic {
        &self.diagnostic
    }
}

/// Checked result and independent reports, preserved on both success and failure.
/// Construction is private; inspecting this data does not authorize execution.
#[derive(Debug)]
pub struct CheckedEvaluation {
    result: Result<Evaluation, RuntimeFailure>,
    reports: Vec<ResourceReport>,
    unpublished: Vec<UnpublishedGuardInspection>,
    failure_effect_trace: Option<Vec<super::EffectTraceEvent>>,
}
impl CheckedEvaluation {
    pub(crate) fn from_parts(
        result: Result<Evaluation, RuntimeFailure>,
        reports: Vec<ResourceReport>,
    ) -> Self {
        Self { result, reports, unpublished: Vec::new(), failure_effect_trace: None }
    }
    pub(crate) fn with_inspections_and_trace(result: Result<Evaluation, RuntimeFailure>, reports: Vec<ResourceReport>, unpublished: Vec<UnpublishedGuardInspection>, failure_effect_trace: Option<Vec<super::EffectTraceEvent>>) -> Self {
        Self { result, reports, unpublished, failure_effect_trace }
    }
    /// Actual machine trace or its terminal prefix; None means unavailable.
    #[cfg(any(test, ash_checked_owner_root = "v1"))]
    pub(crate) fn effect_trace(&self) -> Option<&[super::EffectTraceEvent]> {
        match &self.result {
            Ok(evaluation) => evaluation.retained_effect_trace(),
            Err(_) => self.failure_effect_trace.as_deref(),
        }
    }
    /// Ordinary evaluation outcome, unchanged by resource inspection.
    pub fn result(&self) -> Result<&Evaluation, RuntimeFailure> {
        self.result.as_ref().map_err(|error| *error)
    }
    /// Independent records in structural closing order, including on failure.
    pub fn resource_reports(&self) -> &[ResourceReport] {
        &self.reports
    }
    /// Guard/supervisor observations, never scope-closing records or witnesses.
    pub fn unpublished_guards(&self) -> &[UnpublishedGuardInspection] { &self.unpublished }
    /// Move all independent observation categories without dropping guard data.
    pub fn into_inspections(self) -> (Result<Evaluation, RuntimeFailure>, Vec<ResourceReport>, Vec<UnpublishedGuardInspection>) {
        (self.result, self.reports, self.unpublished)
    }
    /// Move the result and scope-closing records without copying.
    /// Guard inspections are omitted; use `into_inspections` to retain them.
    pub fn into_parts(self) -> (Result<Evaluation, RuntimeFailure>, Vec<ResourceReport>) {
        (self.result, self.reports)
    }
}

/// Storage is funded before native entry. A ready writer holds its exclusive
/// borrow before the call, so commit cannot allocate or replace an older record.
#[derive(Debug)]
pub(crate) struct ResourceReports {
    records: Vec<ResourceReport>,
    limit: usize,
    identity: u64,
    reserved: usize,
    unpublished: Vec<UnpublishedGuardInspection>,
}
#[derive(Clone, Copy, Debug)]
enum Publication { Reserved, Published(usize), GuardObserved, Cancelled }
/// Storage bookkeeping only, never native or protected-context authority.
/// The private shared state survives a popped frame and can publish only once.
#[derive(Debug)]
pub(crate) struct ResourceReportSlot {
    collector: u64,
    publication: Rc<Cell<Publication>>,
}
impl ResourceReportSlot {
    pub(crate) fn observer(&self) -> Self {
        Self { collector: self.collector, publication: Rc::clone(&self.publication) }
    }
    pub(crate) fn published(&self) -> Option<usize> {
        match self.publication.get() { Publication::Published(index) => Some(index), _ => None }
    }
    pub(crate) fn settled(&self) -> bool { !matches!(self.publication.get(), Publication::Reserved) }
    pub(crate) fn cancel_unacquired(&self) {
        if matches!(self.publication.get(), Publication::Reserved) {
            self.publication.set(Publication::Cancelled);
        }
    }
}
pub(crate) struct ReadyResourceReport<'a> {
    records: &'a mut Vec<ResourceReport>,
}
impl ResourceReports {
    pub(crate) fn reserve(
        capacity: usize,
        work: &mut TypeWorkBudget,
    ) -> Result<Self, RuntimeFailure> {
        let cells = capacity.checked_mul(2).ok_or(RuntimeFailure::ResourceCapacity)?;
        super::failure::charge_runtime_work(work, cells, super::RuntimePhase::Acquisition)?;
        let mut records = Vec::new();
        records.try_reserve_exact(capacity).map_err(|_| {
            super::failure::resource_failure(
                super::ResourceFailureCause::StorageReservationFailed,
                super::RuntimePhase::Acquisition,
                super::RuntimeResource::ForeignCodecStorage,
                Some(capacity),
                None,
            )
        })?;
        let mut unpublished = Vec::new();
        unpublished.try_reserve_exact(capacity).map_err(|_| super::failure::resource_failure(
            super::ResourceFailureCause::StorageReservationFailed, super::RuntimePhase::Acquisition,
            super::RuntimeResource::ForeignCodecStorage, Some(capacity), None))?;
        Ok(Self {
            records,
            limit: capacity,
            identity: NEXT_REPORTS.fetch_update(Ordering::Relaxed, Ordering::Relaxed, |value| value.checked_add(1))
                .map_err(|_| super::failure::resource_failure(super::ResourceFailureCause::ConfiguredCapacity,
                    super::RuntimePhase::Acquisition, super::RuntimeResource::ForeignCodecStorage, Some(1), Some(0)))?,
            reserved: 0,
            unpublished,
        })
    }
    pub(crate) fn reserve_owner(&mut self, work: &mut TypeWorkBudget) -> Result<ResourceReportSlot, RuntimeFailure> {
        // Initial state/identity and shared observers plus fixed future fact
        // copy/publication are paid before the acquisition can enter C.
        super::failure::charge_runtime_work(work, 16, super::RuntimePhase::Acquisition)?;
        if self.reserved == self.limit {
            return Err(super::failure::resource_failure(super::ResourceFailureCause::ConfiguredCapacity,
                super::RuntimePhase::Acquisition, super::RuntimeResource::ForeignCodecStorage, Some(1), Some(0)));
        }
        self.reserved += 1;
        Ok(ResourceReportSlot { collector: self.identity, publication: Rc::new(Cell::new(Publication::Reserved)) })
    }
    pub(crate) fn owns_pending(&self, slot: &ResourceReportSlot) -> bool {
        slot.collector == self.identity && matches!(slot.publication.get(), Publication::Reserved)
    }
    pub(crate) fn commit_owner(&mut self, slot: &ResourceReportSlot, report: ResourceReport) -> usize {
        // Private one-shot state and cumulative reservations prove spare
        // capacity. There is no allocation or capacity refusal after native entry.
        assert!(self.owns_pending(slot));
        assert!(self.records.len() + self.unpublished.len() < self.reserved && self.reserved <= self.limit);
        let index = self.records.len();
        self.records.push(report);
        slot.publication.set(Publication::Published(index));
        index
    }
    pub(crate) fn commit_guard(&mut self, slot: &ResourceReportSlot, observation: UnpublishedGuardInspection) {
        assert!(self.owns_pending(slot));
        assert!(self.records.len() + self.unpublished.len() < self.reserved && self.reserved <= self.limit);
        self.unpublished.push(observation);
        slot.publication.set(Publication::GuardObserved);
    }
    pub(crate) fn ready(&mut self) -> Result<ReadyResourceReport<'_>, RuntimeFailure> {
        if self.reserved == self.limit {
            return Err(super::failure::resource_failure(
                super::ResourceFailureCause::ConfiguredCapacity,
                super::RuntimePhase::Cleanup,
                super::RuntimeResource::ForeignCodecStorage,
                Some(1),
                Some(0),
            ));
        }
        // This DATA-only writer also spends one cumulative reservation; it
        // cannot consume a slot already promised to an armed owner.
        self.reserved += 1;
        Ok(ReadyResourceReport {
            records: &mut self.records,
        })
    }
    pub(crate) fn into_records(self) -> Vec<ResourceReport> {
        self.records
    }
    pub(crate) fn into_inspections(self) -> (Vec<ResourceReport>, Vec<UnpublishedGuardInspection>) {
        (self.records, self.unpublished)
    }
    pub(crate) fn record(&self, index: usize) -> Option<&ResourceReport> {
        self.records.get(index)
    }
    pub(crate) fn record_count(&self) -> usize { self.records.len() }
    pub(crate) fn record_for(&self, slot: &ResourceReportSlot) -> Option<&ResourceReport> {
        if slot.collector != self.identity { return None; }
        self.record(slot.published()?)
    }
}
impl ReadyResourceReport<'_> {
    pub(crate) fn commit(self, report: ResourceReport) -> usize {
        // The exclusive pre-entry borrow preserves the admitted spare slot.
        let index = self.records.len();
        self.records.push(report);
        index
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn owner_report_slots_are_funded_once_before_entry_and_keep_publication_order() {
        let mut setup = TypeWorkBudget::default();
        let mut reports = ResourceReports::reserve(2, &mut setup).unwrap();
        let mut short = TypeWorkBudget::with_limit(15);
        assert!(reports.reserve_owner(&mut short).is_err());
        assert_eq!(reports.reserved, 0); // No native owner can enter on this refusal.
        let mut exact = TypeWorkBudget::with_limit(16);
        let first = reports.reserve_owner(&mut exact).unwrap();
        assert_eq!(exact.used(), 16);
        let first_observer = first.observer();
        let second = reports.reserve_owner(&mut setup).unwrap();
        // A generic DATA writer cannot steal capacity promised to an owner.
        assert!(reports.ready().is_err());
        assert!(reports.reserve_owner(&mut setup).is_err());
        let closing = |status| ResourceReport::observed(ResourceClosing::Transferred,
            ResourceNativeFact::Owned, true, status, ResourceDiagnostic::NotRequested);
        let second_index = reports.commit_owner(&second, closing(None));
        let first_index = reports.commit_owner(&first, closing(Some(0)));
        assert_eq!((second_index, first_index), (0, 1)); // Structural, not acquisition, order.
        assert_eq!(first_observer.published(), Some(first_index));
        assert!(!reports.owns_pending(&first)); // No second publication is available.
        assert_eq!(reports.record_for(&first_observer).unwrap().status(), Some(0));
        assert_eq!(reports.record_for(&second).unwrap().status(), None);
        let mut other = ResourceReports::reserve(1, &mut setup).unwrap();
        let donor = other.reserve_owner(&mut setup).unwrap();
        assert!(!reports.owns_pending(&donor));
        assert!(reports.record_for(&donor).is_none());
        let mut fresh = ResourceReports::reserve(1, &mut setup).unwrap();
        let cancelled = fresh.reserve_owner(&mut setup).unwrap();
        cancelled.cancel_unacquired();
        assert!(!fresh.owns_pending(&cancelled));
        assert!(fresh.reserve_owner(&mut setup).is_err()); // Cumulative attempt bound, no recycling.
    }
    #[test]
    fn independent_reports_keep_absence_last_fact_and_order_on_failure() {
        let mut work = TypeWorkBudget::with_limit(4);
        let mut reports = ResourceReports::reserve(2, &mut work).unwrap();
        assert_eq!(work.used(), 4);
        reports.ready().unwrap().commit(ResourceReport::observed(
            ResourceClosing::NativeConsumed,
            ResourceNativeFact::Consumed,
            false,
            None,
            ResourceDiagnostic::NotRequested,
        ));
        reports.ready().unwrap().commit(ResourceReport::observed(
            ResourceClosing::Transferred,
            ResourceNativeFact::Owned,
            true,
            Some(0),
            ResourceDiagnostic::Lost,
        ));
        assert!(reports.ready().is_err());
        let outcome = CheckedEvaluation::from_parts(
            Err(RuntimeFailure::ResourceCompletion),
            reports.into_records(),
        );
        assert_eq!(
            outcome.result().unwrap_err(),
            RuntimeFailure::ResourceCompletion
        );
        assert_eq!(outcome.resource_reports()[0].status(), None);
        assert_eq!(outcome.resource_reports()[1].status(), Some(0));
        assert_eq!(
            outcome.resource_reports()[1].native(),
            ResourceNativeFact::Owned
        );
        assert!(outcome.resource_reports()[1].unresolved());
        assert_eq!(
            outcome.resource_reports()[0].closing(),
            ResourceClosing::NativeConsumed
        );
        assert!(ResourceReports::reserve(2, &mut TypeWorkBudget::with_limit(1)).is_err());
        let mut fresh = TypeWorkBudget::with_limit(4);
        assert!(ResourceReports::reserve(2, &mut fresh).is_ok());
    }
}
