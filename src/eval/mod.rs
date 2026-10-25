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
    evaluate_effect, evaluate_effect_with_source_native_program,
};
pub(crate) use value::ObservedHeap;
pub use value::{Address, Closure, ExecutableNode, ExecutableProgram, ObservedValue, Value};

#[doc(hidden)]
pub use value::{NativeByteStorage, NativeTupleAdapter, NativeTupleStorage};
