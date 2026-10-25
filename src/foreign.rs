//! Passive byte/address source declarations and generated typed native calls.
//! Foreign behavior and memory lifetime are interpreted by ordinary Ash modules.
pub mod checked_source;
pub(crate) mod source_bindings;
pub mod source_contract;
pub mod source_runtime;
