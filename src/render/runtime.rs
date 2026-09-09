//! Runtime text prepared before execution and written without formatting after failure.

use super::{decimal, fragment};
use crate::{
    eval::{
        CleanupStatus, ResourceFailure, ResourceFailureCause, RuntimeFailure, RuntimePhase,
        RuntimeResource,
    },
    message::{Catalogue, CatalogueError, Message},
};
use std::io::{self, Write};

/// Localized runtime text prepared before program execution.
///
/// Preparation may allocate and format catalogues. Reporting only borrows these
/// strings and existing fixed-size failure data; it performs no preparation.
pub struct PreparedRuntimeMessages {
    reasons: [(&'static str, String); 18],
    phases: [(RuntimePhase, String); 7],
    resources: [(RuntimeResource, String); 21],
    cleanup: [(CleanupStatus, String); 3],
    cause: String,
    phase: String,
    resource: String,
    requested: String,
    available: String,
    teardown: String,
    cleanup_label: String,
}

impl PreparedRuntimeMessages {
    /// Prepares every runtime message from the selected embedded catalogue.
    ///
    /// # Errors
    /// Returns any catalogue defect before execution starts.
    pub fn new(catalogue: &Catalogue) -> Result<Self, CatalogueError> {
        Ok(Self {
            reasons: [
                (
                    RuntimeFailure::MissingNode.reason_code(),
                    catalogue.format(&Message::runtime_missing_node())?,
                ),
                (
                    RuntimeFailure::UnexpectedPrimitiveValue.reason_code(),
                    catalogue.format(&Message::runtime_unexpected_primitive_value())?,
                ),
                (
                    RuntimeFailure::UnexpectedFunctionValue.reason_code(),
                    catalogue.format(&Message::runtime_unexpected_function_value())?,
                ),
                (
                    RuntimeFailure::MissingBinding.reason_code(),
                    catalogue.format(&Message::runtime_missing_binding())?,
                ),
                (
                    RuntimeFailure::UnexpectedRecursiveBinding.reason_code(),
                    catalogue.format(&Message::runtime_unexpected_recursive_binding())?,
                ),
                (
                    RuntimeFailure::EnvironmentCapacity.reason_code(),
                    catalogue.format(&Message::runtime_environment_capacity())?,
                ),
                (
                    RuntimeFailure::InvalidControlState.reason_code(),
                    catalogue.format(&Message::runtime_invalid_control_state())?,
                ),
                (
                    RuntimeFailure::HeapCapacity.reason_code(),
                    catalogue.format(&Message::runtime_heap_capacity())?,
                ),
                (
                    RuntimeFailure::CapturedControlCapacity.reason_code(),
                    catalogue.format(&Message::runtime_captured_control_capacity())?,
                ),
                (
                    RuntimeFailure::ResourceCapacity.reason_code(),
                    catalogue.format(&Message::runtime_resource_capacity())?,
                ),
                (
                    RuntimeFailure::InvalidLocation.reason_code(),
                    catalogue.format(&Message::runtime_invalid_location())?,
                ),
                (
                    RuntimeFailure::UninitializedLocation.reason_code(),
                    catalogue.format(&Message::runtime_uninitialized_location())?,
                ),
                (
                    RuntimeFailure::AliasLoop.reason_code(),
                    catalogue.format(&Message::runtime_alias_loop())?,
                ),
                (
                    RuntimeFailure::ImpossibleMatch.reason_code(),
                    catalogue.format(&Message::runtime_impossible_match())?,
                ),
                (
                    ResourceFailureCause::ConfiguredCapacity.reason_code(),
                    catalogue.format(&Message::runtime_capacity_exhausted())?,
                ),
                (
                    ResourceFailureCause::AllocatorRefused.reason_code(),
                    catalogue.format(&Message::runtime_allocator_refused())?,
                ),
                (
                    ResourceFailureCause::StorageReservationFailed.reason_code(),
                    catalogue.format(&Message::runtime_storage_reservation_failed())?,
                ),
                (
                    ResourceFailureCause::WorkBudgetExhausted.reason_code(),
                    catalogue.format(&Message::runtime_work_budget_exhausted())?,
                ),
            ],
            phases: [
                (
                    RuntimePhase::Acquisition,
                    catalogue.format(&Message::runtime_phase_acquisition())?,
                ),
                (
                    RuntimePhase::Capture,
                    catalogue.format(&Message::runtime_phase_capture())?,
                ),
                (
                    RuntimePhase::Evaluation,
                    catalogue.format(&Message::runtime_phase_evaluation())?,
                ),
                (
                    RuntimePhase::Cleanup,
                    catalogue.format(&Message::runtime_phase_cleanup())?,
                ),
                (
                    RuntimePhase::Access,
                    catalogue.format(&Message::runtime_phase_access())?,
                ),
                (
                    RuntimePhase::Teardown,
                    catalogue.format(&Message::runtime_phase_teardown())?,
                ),
                (
                    RuntimePhase::DiagnosticPreparation,
                    catalogue.format(&Message::runtime_phase_diagnostic_preparation())?,
                ),
            ],
            resources: [
                (
                    RuntimeResource::TypeDisposal,
                    catalogue.format(&Message::runtime_resource_type_disposal())?,
                ),
                (
                    RuntimeResource::KindDisposal,
                    catalogue.format(&Message::runtime_resource_kind_disposal())?,
                ),
                (
                    RuntimeResource::EnvironmentDisposal,
                    catalogue.format(&Message::runtime_resource_environment_disposal())?,
                ),
                (
                    RuntimeResource::CapturedDisposal,
                    catalogue.format(&Message::runtime_resource_captured_disposal())?,
                ),
                (
                    RuntimeResource::WorkUnits,
                    catalogue.format(&Message::runtime_resource_work_units())?,
                ),
                (
                    RuntimeResource::ResourceOwners,
                    catalogue.format(&Message::runtime_resource_resource_owners())?,
                ),
                (
                    RuntimeResource::CleanupOwners,
                    catalogue.format(&Message::runtime_resource_cleanup_owners())?,
                ),
                (
                    RuntimeResource::RegistrationOwners,
                    catalogue.format(&Message::runtime_resource_registration_owners())?,
                ),
                (
                    RuntimeResource::RegistrationKeys,
                    catalogue.format(&Message::runtime_resource_registration_keys())?,
                ),
                (
                    RuntimeResource::RegistrationInvocations,
                    catalogue.format(&Message::runtime_resource_registration_invocations())?,
                ),
                (
                    RuntimeResource::ActivationKeys,
                    catalogue.format(&Message::runtime_resource_activation_keys())?,
                ),
                (
                    RuntimeResource::EnvironmentBindings,
                    catalogue.format(&Message::runtime_resource_environment_bindings())?,
                ),
                (
                    RuntimeResource::FrameStorage,
                    catalogue.format(&Message::runtime_resource_frame_storage())?,
                ),
                (
                    RuntimeResource::EffectTrace,
                    catalogue.format(&Message::runtime_resource_effect_trace())?,
                ),
                (
                    RuntimeResource::EvaluationTrace,
                    catalogue.format(&Message::runtime_resource_evaluation_trace())?,
                ),
                (
                    RuntimeResource::ResultHeapCells,
                    catalogue.format(&Message::runtime_resource_result_heap_cells())?,
                ),
                (
                    RuntimeResource::HeapCells,
                    catalogue.format(&Message::runtime_resource_heap_cells())?,
                ),
                (
                    RuntimeResource::InstantiationEntries,
                    catalogue.format(&Message::runtime_resource_instantiation_entries())?,
                ),
                (
                    RuntimeResource::InstantiationStorage,
                    catalogue.format(&Message::runtime_resource_instantiation_storage())?,
                ),
                (
                    RuntimeResource::CaptureInspection,
                    catalogue.format(&Message::runtime_resource_capture_inspection())?,
                ),
                (
                    RuntimeResource::RegistrationIdentities,
                    catalogue.format(&Message::runtime_resource_registration_identities())?,
                ),
            ],
            cleanup: [
                (
                    CleanupStatus::Complete,
                    catalogue.format(&Message::runtime_cleanup_complete())?,
                ),
                (
                    CleanupStatus::Incomplete,
                    catalogue.format(&Message::runtime_cleanup_incomplete())?,
                ),
                (
                    CleanupStatus::Unknown,
                    catalogue.format(&Message::runtime_cleanup_unknown())?,
                ),
            ],
            cause: catalogue.format(&Message::runtime_label_cause())?,
            phase: catalogue.format(&Message::runtime_label_phase())?,
            resource: catalogue.format(&Message::runtime_label_resource())?,
            requested: catalogue.format(&Message::runtime_label_requested())?,
            available: catalogue.format(&Message::runtime_label_available())?,
            teardown: catalogue.format(&Message::runtime_label_teardown())?,
            cleanup_label: catalogue.format(&Message::runtime_label_cleanup())?,
        })
    }
}

fn prepared<T: PartialEq>(entries: &[(T, String)], key: T) -> io::Result<&str> {
    entries
        .iter()
        .find(|(candidate, _)| *candidate == key)
        .map(|(_, value)| value.as_str())
        .ok_or_else(|| io::ErrorKind::InvalidData.into())
}

/// Writes one runtime diagnostic using the selected format and prepared text.
///
/// If pre-execution catalogue preparation failed, pass `None` to retain the
/// original diagnostic as allocation-independent JSON in every format. This
/// interface never prepares messages or attempts to recover from a writer error.
///
/// # Errors
/// Returns the first reporting error without retry or recursive reporting.
pub fn write_runtime_diagnostic(
    writer: &mut impl Write,
    failure: RuntimeFailure,
    format: crate::diagnostic_options::MessageFormat,
    messages: Option<&PreparedRuntimeMessages>,
) -> io::Result<()> {
    use crate::diagnostic_options::MessageFormat;
    match (format, messages) {
        (MessageFormat::Json, _) | (_, None) => super::write_runtime_json(writer, failure),
        (MessageFormat::Human, Some(messages)) => write_runtime_human(writer, failure, messages),
        (MessageFormat::Short, Some(messages)) => write_runtime_short(writer, failure, messages),
    }
}

/// Writes a human-first runtime report using previously prepared messages.
///
/// The writer owns its storage policy. Reporting allocates no storage, invokes
/// no catalogue formatter and attempts no recovery.
///
/// # Errors
/// Stops on the first write or flush failure without retry, including Interrupted.
/// Returns InvalidData if the prepared messages do not cover the failure.
pub fn write_runtime_human(
    writer: &mut impl Write,
    failure: RuntimeFailure,
    messages: &PreparedRuntimeMessages,
) -> io::Result<()> {
    write_text(writer, failure, messages, b"\n")
}

/// Writes one compact, localized runtime report on one line.
///
/// Uses the same pre-execution preparation and failure guarantees as
/// [`write_runtime_human`].
///
/// # Errors
/// Returns the first write, flush or missing-prepared-message error without retry.
pub fn write_runtime_short(
    writer: &mut impl Write,
    failure: RuntimeFailure,
    messages: &PreparedRuntimeMessages,
) -> io::Result<()> {
    write_text(writer, failure, messages, b"; ")
}

fn write_text(
    writer: &mut impl Write,
    failure: RuntimeFailure,
    messages: &PreparedRuntimeMessages,
    separator: &[u8],
) -> io::Result<()> {
    reason(writer, failure.reason_code(), messages)?;
    let cleanup = if let RuntimeFailure::Report(report) = failure {
        if let Some(resource) = report.primary.resource() {
            if failure.reason_code() != resource.cause.reason_code() {
                field(writer, separator, &messages.cause)?;
                reason(writer, resource.cause.reason_code(), messages)?;
            }
            details(writer, resource, messages, separator)?;
        }
        if let Some(resource) = report.teardown {
            field(writer, separator, &messages.teardown)?;
            reason(writer, resource.cause.reason_code(), messages)?;
            details(writer, resource, messages, separator)?;
        }
        report.cleanup
    } else {
        CleanupStatus::Unknown
    };
    field(writer, separator, &messages.cleanup_label)?;
    fragment(writer, prepared(&messages.cleanup, cleanup)?.as_bytes())?;
    fragment(writer, b"\n")?;
    writer.flush()
}

fn reason(
    writer: &mut impl Write,
    code: &'static str,
    messages: &PreparedRuntimeMessages,
) -> io::Result<()> {
    fragment(writer, prepared(&messages.reasons, code)?.as_bytes())?;
    fragment(writer, b" [")?;
    fragment(writer, code.as_bytes())?;
    fragment(writer, b"]")
}

fn field(writer: &mut impl Write, separator: &[u8], label: &str) -> io::Result<()> {
    fragment(writer, separator)?;
    fragment(writer, label.as_bytes())?;
    fragment(writer, b": ")
}

fn details(
    writer: &mut impl Write,
    failure: ResourceFailure,
    messages: &PreparedRuntimeMessages,
    separator: &[u8],
) -> io::Result<()> {
    field(writer, separator, &messages.phase)?;
    fragment(
        writer,
        prepared(&messages.phases, failure.phase)?.as_bytes(),
    )?;
    field(writer, separator, &messages.resource)?;
    fragment(
        writer,
        prepared(&messages.resources, failure.resource)?.as_bytes(),
    )?;
    for (label, amount) in [
        (&messages.requested, failure.requested),
        (&messages.available, failure.available),
    ] {
        if let Some(amount) = amount {
            field(writer, separator, label)?;
            decimal(writer, amount)?;
        }
    }
    Ok(())
}
