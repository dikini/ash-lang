//! Explicit first-order evaluation of independently validated Core families.

pub(crate) mod disposal;
mod failure;
mod machine;
mod value;

pub use failure::{
    CleanupStatus, ResourceFailure, ResourceFailureCause, RuntimeFailureReport,
    RuntimeFailureSummary, RuntimePhase, RuntimeResource,
};

pub use machine::{
    Control, EffectTraceEvent, Environment, Evaluation, RuntimeFailure, TraceEvent, evaluate,
    evaluate_effect, evaluate_effect_with_foreign_runtime,
};
#[cfg(test)]
pub(crate) use machine::{native_buffer_counters_for_test, reset_native_buffer_counters_for_test};
pub(crate) use value::ObservedHeap;
pub use value::{Closure, ExecutableNode, ExecutableProgram, ObservedValue, Value};
