//! Compiler and interpreter components for the retained Mini-Ash language.
//!
//! The crate exposes the stage-preserving source pipeline through [`driver`].
//! [`driver::run_source`] runs admitted UTF-8 source, while
//! [`driver::run_path`] reads and runs one source file. Successful observations
//! contain the evaluated value and structural type; failures preserve their
//! owning compiler or runtime stage.
//!
//! The repository's `spec` directory defines Ash language semantics. These Rust
//! interfaces and their implementation do not define additional language
//! behavior.

pub mod core;
pub mod diagnostic;
pub mod driver;
pub mod elaborate;
pub mod eval;
pub mod extended;
pub mod integer;
pub mod lexer;
pub mod parser;
pub mod pattern;
pub mod render;
pub mod resolve;
pub mod resolved;
pub mod source;
pub mod surface;
pub mod types;
