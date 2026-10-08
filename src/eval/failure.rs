//! Fixed-size details for detected runtime resource failure.

/// The detected cause, without inferring physical memory quotas.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ResourceFailureCause {
    /// A configured or representational capacity cannot admit the request.
    ConfiguredCapacity,
    /// A fallible host storage reservation was refused.
    AllocatorRefused,
    /// Host storage reservation failed; the API does not expose whether the
    /// cause was allocator refusal or an internal representation bound.
    StorageReservationFailed,
    /// Resource admission failed, but the detecting boundary erased whether
    /// work or storage caused the refusal.
    ResourceAdmissionRefused,
    /// The runtime work ledger cannot admit the charge.
    WorkBudgetExhausted,
}

/// The resource whose admission failed, with units when the boundary knows them.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum RuntimeResource {
    /// Foreign operation or codec admission whose work or storage cause is unavailable.
    ForeignAdmission,
    /// Foreign codec scratch and executable binding admission storage.
    ForeignCodecStorage,
    /// Ordinary immutable packed byte storage.
    PackedBytes,
    /// Pending structural type destruction tasks.
    TypeDisposal,
    /// Pending kind destruction tasks.
    KindDisposal,
    /// Pending uniquely owned environment entries.
    EnvironmentDisposal,
    /// Pending captured control frames.
    CapturedDisposal,
    /// Runtime work ledger units.
    WorkUnits,
    /// Concurrent live resource owners.
    ResourceOwners,
    /// Concurrent live source cleanup owners.
    CleanupOwners,
    /// Concurrent live registration owners.
    RegistrationOwners,
    /// Representable fresh registration identities.
    RegistrationKeys,
    /// Pending invocations retained by a registration owner.
    RegistrationInvocations,
    /// Representable fresh activation keys.
    ActivationKeys,
    /// Representable lexical environment bindings.
    EnvironmentBindings,
    /// Retained control frames.
    FrameStorage,
    /// Effect trace events.
    EffectTrace,
    /// Ordinary evaluator trace events.
    EvaluationTrace,
    /// Prepared result heap cells.
    ResultHeapCells,
    /// Ordinary evaluator heap cells.
    HeapCells,
    /// Retained instantiation map entries.
    InstantiationEntries,
    /// Temporary structural metadata retained during instantiation.
    InstantiationStorage,
    /// Pending references used to inspect captured control before discard.
    CaptureInspection,
    /// Registration identities retained while inspecting captured control.
    RegistrationIdentities,
}

impl RuntimeResource {
    /// Returns the static resource and unit label.
    #[must_use]
    pub const fn label(self) -> &'static str {
        match self {
            Self::ForeignAdmission => "foreign admission",
            Self::ForeignCodecStorage => "foreign codec storage",
            Self::PackedBytes => "packed bytes",
            Self::TypeDisposal => "type disposal tasks",
            Self::KindDisposal => "kind disposal tasks",
            Self::EnvironmentDisposal => "environment disposal entries",
            Self::CapturedDisposal => "captured disposal frames",
            Self::WorkUnits => "runtime work units",
            Self::ResourceOwners => "resource owners",
            Self::CleanupOwners => "cleanup owners",
            Self::RegistrationOwners => "registration owners",
            Self::RegistrationKeys => "representable registration keys",
            Self::RegistrationInvocations => "registration invocations",
            Self::ActivationKeys => "representable activation keys",
            Self::EnvironmentBindings => "representable environment bindings",
            Self::FrameStorage => "control frames",
            Self::EffectTrace => "effect trace events",
            Self::EvaluationTrace => "evaluation trace events",
            Self::ResultHeapCells => "result heap cells",
            Self::HeapCells => "runtime heap cells",
            Self::InstantiationEntries => "instantiation entries",
            Self::InstantiationStorage => "instantiation storage cells",
            Self::CaptureInspection => "capture inspection entries",
            Self::RegistrationIdentities => "registration identities",
        }
    }
}

impl ResourceFailureCause {
    /// Returns the stable diagnostic reason.
    #[must_use]
    pub const fn reason_code(self) -> &'static str {
        match self {
            Self::ConfiguredCapacity => "runtime.capacity-exhausted",
            Self::AllocatorRefused => "runtime.allocator-refused",
            Self::StorageReservationFailed => "runtime.storage-reservation-failed",
            Self::ResourceAdmissionRefused => "runtime.resource-admission-refused",
            Self::WorkBudgetExhausted => "runtime.work-budget-exhausted",
        }
    }
}

/// The phase that detected a resource failure.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum RuntimePhase {
    /// Preparing or publishing a resource scope.
    Acquisition,
    /// Retaining, restoring or consuming suspended control.
    Capture,
    /// Ordinary source evaluation.
    Evaluation,
    /// Preparing a source cleanup action, not host destruction.
    Cleanup,
    /// Selecting or performing an effect operation.
    Access,
    /// Destroying retained runtime state after evaluation stops.
    Teardown,
    /// Preparing a diagnostic.
    DiagnosticPreparation,
}

impl RuntimePhase {
    /// Returns a static diagnostic label.
    #[must_use]
    pub const fn label(self) -> &'static str {
        match self {
            Self::Acquisition => "acquisition",
            Self::Capture => "capture",
            Self::Evaluation => "evaluation",
            Self::Cleanup => "source cleanup",
            Self::Access => "access",
            Self::Teardown => "teardown",
            Self::DiagnosticPreparation => "diagnostic preparation",
        }
    }
}

/// What host destruction established about cleanup completion.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CleanupStatus {
    /// Host destruction completed.
    Complete,
    /// Host destruction stopped before all retained state was released.
    Incomplete,
    /// Completion has not been established.
    Unknown,
}

impl CleanupStatus {
    /// Returns a static diagnostic label.
    #[must_use]
    pub const fn label(self) -> &'static str {
        match self {
            Self::Complete => "complete",
            Self::Incomplete => "incomplete",
            Self::Unknown => "unknown",
        }
    }
}

/// Allocation-independent details of one detected resource failure.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ResourceFailure {
    /// The observed failure cause.
    pub cause: ResourceFailureCause,
    /// The detecting phase.
    pub phase: RuntimePhase,
    /// The resource whose units are reported.
    pub resource: RuntimeResource,
    /// Requested additional units, if known and representable.
    pub requested: Option<usize>,
    /// Available additional units, if known and representable.
    pub available: Option<usize>,
}

impl ResourceFailure {
    /// Creates details using only fixed-size values.
    #[must_use]
    pub const fn new(
        cause: ResourceFailureCause,
        phase: RuntimePhase,
        resource: RuntimeResource,
        requested: Option<usize>,
        available: Option<usize>,
    ) -> Self {
        Self {
            cause,
            phase,
            resource,
            requested,
            available,
        }
    }
}

/// A primary reason and optional resource details, without recursive errors.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct RuntimeFailureSummary {
    pub(crate) reason: &'static str,
    pub(crate) resource: Option<ResourceFailure>,
}

impl RuntimeFailureSummary {
    /// Returns the original stable reason, including legacy invariant reasons.
    #[must_use]
    pub const fn reason_code(self) -> &'static str {
        self.reason
    }

    /// Returns resource details when the original failure supplied them.
    #[must_use]
    pub const fn resource(self) -> Option<ResourceFailure> {
        self.resource
    }
}

/// A bounded report retaining the primary failure and first teardown failure.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct RuntimeFailureReport {
    /// Original failure reason and details.
    pub primary: RuntimeFailureSummary,
    /// First detected secondary teardown failure, if any.
    pub teardown: Option<ResourceFailure>,
    /// Observed host cleanup status.
    pub cleanup: CleanupStatus,
}

pub(crate) fn resource_failure(
    cause: ResourceFailureCause,
    phase: RuntimePhase,
    resource: RuntimeResource,
    requested: Option<usize>,
    available: Option<usize>,
) -> super::RuntimeFailure {
    super::RuntimeFailure::resource(ResourceFailure::new(
        cause, phase, resource, requested, available,
    ))
}

pub(crate) fn charge_runtime_work(
    work: &mut crate::types::TypeWorkBudget,
    requested: usize,
    phase: RuntimePhase,
) -> Result<(), super::RuntimeFailure> {
    work.charge(requested).map_err(|()| {
        resource_failure(
            ResourceFailureCause::WorkBudgetExhausted,
            phase,
            RuntimeResource::WorkUnits,
            Some(requested),
            Some(work.remaining()),
        )
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::eval::RuntimeFailure;

    #[test]
    fn report_retains_legacy_primary_and_first_secondary_in_fixed_storage() {
        let secondary = ResourceFailure::new(
            ResourceFailureCause::AllocatorRefused,
            RuntimePhase::Teardown,
            RuntimeResource::FrameStorage,
            Some(4),
            None,
        );
        let later = ResourceFailure::new(
            ResourceFailureCause::WorkBudgetExhausted,
            RuntimePhase::Teardown,
            RuntimeResource::WorkUnits,
            Some(1),
            Some(0),
        );
        let failure = RuntimeFailure::MissingBinding
            .with_teardown_failure(secondary, CleanupStatus::Incomplete)
            .with_teardown_failure(later, CleanupStatus::Incomplete);
        let RuntimeFailure::Report(report) = failure else {
            panic!("bounded report")
        };
        assert_eq!(report.primary.reason_code(), "runtime.missing-binding");
        assert_eq!(report.primary.resource(), None);
        assert_eq!(report.teardown, Some(secondary));
        assert_eq!(report.cleanup, CleanupStatus::Incomplete);
        assert!(!std::mem::needs_drop::<RuntimeFailure>());
        assert!(std::mem::size_of::<RuntimeFailure>() <= 128);
    }

    #[test]
    fn report_keeps_each_phase_and_known_or_unknown_amounts_distinct() {
        for phase in [
            RuntimePhase::Acquisition,
            RuntimePhase::Capture,
            RuntimePhase::Access,
            RuntimePhase::Teardown,
            RuntimePhase::Evaluation,
            RuntimePhase::Cleanup,
            RuntimePhase::DiagnosticPreparation,
        ] {
            for cause in [
                ResourceFailureCause::ConfiguredCapacity,
                ResourceFailureCause::AllocatorRefused,
                ResourceFailureCause::WorkBudgetExhausted,
            ] {
                let details = ResourceFailure::new(
                    cause,
                    phase,
                    RuntimeResource::WorkUnits,
                    Some(usize::MAX),
                    None,
                );
                let RuntimeFailure::Report(report) = RuntimeFailure::resource(details) else {
                    panic!("bounded report")
                };
                assert_eq!(report.primary.resource(), Some(details));
                assert_eq!(report.primary.reason_code(), cause.reason_code());
                assert_eq!(report.cleanup, CleanupStatus::Unknown);
            }
        }
    }
}
