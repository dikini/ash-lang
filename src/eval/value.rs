//! Runtime values for the retained Mini-Ash evaluator.

use std::{fmt, sync::Arc};

use super::machine::Environment;
use crate::{
    core::{NodeId, PureProgram},
    integer::Integer,
    resolved::BinderId,
    source::Origin,
};

/// An inspectable lexical Ash function value.
#[derive(Clone)]
pub struct Closure {
    /// Resolver identity bound when the function is applied.
    pub parameter: BinderId,
    /// Core body evaluated after parameter binding.
    pub body: NodeId,
    /// Validated code arena containing `body`.
    pub program: Arc<PureProgram>,
    /// Immutable lexical environment captured at function evaluation.
    pub environment: Environment,
    /// Causal source provenance of the function value.
    pub origin: Origin,
}

impl fmt::Debug for Closure {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("Closure")
            .field("parameter", &self.parameter)
            .field("body", &self.body)
            .field("program_node_count", &self.program.node_count())
            .field("environment", &self.environment)
            .field("origin", &self.origin)
            .finish()
    }
}

/// A fully evaluated Mini-Ash value.
///
/// Values intentionally do not implement host equality because Ash functions
/// have no equality operation or observable identity.
#[derive(Clone, Debug)]
pub enum Value {
    /// An arbitrary-precision mathematical integer.
    Integer(Integer),
    /// A Boolean value.
    Boolean(bool),
    /// The unit value.
    Unit,
    /// A lexical unary function and its captured Ash environment.
    Function(Closure),
}

impl fmt::Display for Value {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Integer(value) => value.fmt(formatter),
            Self::Boolean(value) => value.fmt(formatter),
            Self::Unit => formatter.write_str("()"),
            Self::Function(_) => formatter.write_str("<function>"),
        }
    }
}
