//! Explicit first-order evaluation of independently validated Core families.

mod checked_reports;
pub(crate) mod disposal;
mod failure;
pub use checked_reports::{
    CheckedEvaluation, ResourceClosing, ResourceDiagnostic, ResourceNativeFact, ResourceReport,
    GuardBackingObservation, GuardInspectionPoint, UnpublishedGuardInspection,
};
mod machine;
mod value;

pub use failure::{
    CleanupStatus, ResourceFailure, ResourceFailureCause, RuntimeFailureReport,
    RuntimeFailureSummary, RuntimePhase, RuntimeResource,
};

pub use machine::{
    Control, EffectTraceEvent, Environment, Evaluation, RuntimeFailure, TraceEvent, evaluate,
    evaluate_effect, evaluate_effect_with_foreign_runtime,
    evaluate_effect_with_source_native_program,
};
pub(crate) use value::ObservedHeap;
pub use value::{Closure, ExecutableNode, ExecutableProgram, ObservedValue, Value};

#[cfg(test)]
pub(crate) use machine::source_owner_post_record_test;
#[cfg(test)]
pub(crate) use machine::source_scalar_post_record_test;
