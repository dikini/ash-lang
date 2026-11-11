pub(crate) mod disposal;
mod failure;

mod machine;
#[cfg(test)]
pub(crate) use machine::machine_test_hooks;
mod network_transport;
mod value;

pub use failure::{
    CleanupStatus, ResourceFailure, ResourceFailureCause, RuntimeFailureReport,
    RuntimeFailureSummary, RuntimePhase, RuntimeResource,
};

pub use machine::{
    Control, EffectTraceEvent, Environment, Evaluation, RuntimeFailure, TraceEvent, evaluate,
    evaluate_effect, evaluate_effect_with_source_native_program,
};
pub(crate) use machine::{
    evaluate_effect_with_quote_guards, evaluate_effect_with_source_native_quote_guards,
    evaluate_transformer_with_owners,
};
#[doc(hidden)]
pub use value::CompilerSyntaxHandle;
pub(crate) use value::ObservedHeap;
pub use value::{Address, Closure, ExecutableNode, ExecutableProgram, ObservedValue, Value};

#[doc(hidden)]
pub use value::{NativeByteStorage, NativeTupleAdapter, NativeTupleStorage};
