//! Explicit first-order evaluation of independently validated pure Core.

mod machine;
mod value;

pub use machine::{Control, Environment, Evaluation, RuntimeFailure, TraceEvent, evaluate};
pub use value::Value;
