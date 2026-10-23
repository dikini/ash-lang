//! Independent checked-resource observations. These values confer no authority.
use super::{Evaluation, RuntimeFailure};
use crate::types::TypeWorkBudget;

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
}
impl CheckedEvaluation {
    pub(crate) fn from_parts(
        result: Result<Evaluation, RuntimeFailure>,
        reports: Vec<ResourceReport>,
    ) -> Self {
        Self { result, reports }
    }
    /// Ordinary evaluation outcome, unchanged by resource inspection.
    pub fn result(&self) -> Result<&Evaluation, RuntimeFailure> {
        self.result.as_ref().map_err(|error| *error)
    }
    /// Independent records in structural closing order, including on failure.
    pub fn resource_reports(&self) -> &[ResourceReport] {
        &self.reports
    }
    /// Move the ordinary result and independent observations without copying.
    pub fn into_parts(self) -> (Result<Evaluation, RuntimeFailure>, Vec<ResourceReport>) {
        (self.result, self.reports)
    }
}

/// Storage is funded before native entry. A ready writer holds its exclusive
/// borrow before the call, so commit cannot allocate or replace an older record.
pub(crate) struct ResourceReports {
    records: Vec<ResourceReport>,
    limit: usize,
}
pub(crate) struct ReadyResourceReport<'a> {
    records: &'a mut Vec<ResourceReport>,
}
impl ResourceReports {
    pub(crate) fn reserve(
        capacity: usize,
        work: &mut TypeWorkBudget,
    ) -> Result<Self, RuntimeFailure> {
        super::failure::charge_runtime_work(work, capacity, super::RuntimePhase::Acquisition)?;
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
        Ok(Self {
            records,
            limit: capacity,
        })
    }
    pub(crate) fn ready(&mut self) -> Result<ReadyResourceReport<'_>, RuntimeFailure> {
        if self.records.len() == self.limit {
            return Err(super::failure::resource_failure(
                super::ResourceFailureCause::ConfiguredCapacity,
                super::RuntimePhase::Cleanup,
                super::RuntimeResource::ForeignCodecStorage,
                Some(1),
                Some(0),
            ));
        }
        Ok(ReadyResourceReport {
            records: &mut self.records,
        })
    }
    pub(crate) fn into_records(self) -> Vec<ResourceReport> {
        self.records
    }
}
impl ReadyResourceReport<'_> {
    pub(crate) fn commit(self, report: ResourceReport) {
        // The exclusive pre-entry borrow preserves the admitted spare slot.
        self.records.push(report);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn independent_reports_keep_absence_last_fact_and_order_on_failure() {
        let mut work = TypeWorkBudget::with_limit(2);
        let mut reports = ResourceReports::reserve(2, &mut work).unwrap();
        assert_eq!(work.used(), 2);
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
        let mut fresh = TypeWorkBudget::with_limit(2);
        assert!(ResourceReports::reserve(2, &mut fresh).is_ok());
    }
}
