//! Implementation foundation for the Ash compiler and runtime.
//!
//! Ash does not yet have implemented language semantics.

pub mod core;
pub mod diagnostic;
pub mod integer;
pub mod lexer;
pub mod parser;
pub mod resolve;
pub mod resolved;
pub mod source;
pub mod surface;
pub mod types;
