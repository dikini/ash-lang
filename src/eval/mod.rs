//! Explicit first-order evaluation of independently validated pure Core.

mod machine;
mod value;

pub use machine::{Control, Environment, Evaluation, RuntimeFailure, TraceEvent, evaluate};
pub(crate) use value::ObservedHeap;
pub use value::{Closure, ObservedValue, Value};
