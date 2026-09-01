//! Explicit first-order evaluation of independently validated Core families.

mod machine;
mod value;

pub use machine::{
    Control, EffectTraceEvent, Environment, Evaluation, RuntimeFailure, TraceEvent, evaluate,
    evaluate_effect,
};
pub(crate) use value::ObservedHeap;
pub use value::{Closure, ExecutableNode, ExecutableProgram, ObservedValue, Value};
