//! Compiler and interpreter components for the Ash language.
//!
//! The crate exposes the stage-preserving modular source pipeline through
//! [`driver`]. [`driver::run_path`] loads and runs one entry module and its
//! dependency graph. Successful observations contain the evaluated value and
//! structural type; failures preserve their owning compiler or runtime stage.
//!
//! The repository's `spec` directory defines Ash language semantics. These Rust
//! interfaces and their implementation do not define additional language
//! behavior.

pub mod core;
pub mod diagnostic;
pub mod driver;
pub mod elaborate;
pub mod eval;
mod evidence;
mod evidence_audit;
pub mod evidence_validation;
#[cfg(test)]
pub(crate) use evidence_validation::validate_interface_evidence as validate_linked_facts_for_test;
pub mod diagnostic_options;
pub mod integer;
pub mod interface;
pub mod kind;
pub mod lexer;
pub mod message;
pub mod module;
pub mod parser;
pub mod pattern;
pub mod presentation;
pub mod render;
pub mod resolve;
pub mod resolved;
pub mod source;
pub mod surface;
mod syntax_resource;
pub mod types;
