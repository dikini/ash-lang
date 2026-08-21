//! Function values and strict applications in typed Core.

use super::{dialect::NodeId, variable::TypedBinder};

/// A unary function value payload.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FunctionNode {
    parameter: TypedBinder,
    body: NodeId,
}

impl FunctionNode {
    pub(super) const fn new(parameter: TypedBinder, body: NodeId) -> Self {
        Self { parameter, body }
    }

    /// Returns the parameter definition.
    #[must_use]
    pub const fn parameter(&self) -> &TypedBinder {
        &self.parameter
    }

    /// Returns the function body.
    #[must_use]
    pub const fn body(&self) -> NodeId {
        self.body
    }
}

/// A strict unary application payload.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ApplicationNode {
    function: NodeId,
    argument: NodeId,
}

impl ApplicationNode {
    pub(super) const fn new(function: NodeId, argument: NodeId) -> Self {
        Self { function, argument }
    }

    /// Returns the function position.
    #[must_use]
    pub const fn function(self) -> NodeId {
        self.function
    }

    /// Returns the argument position.
    #[must_use]
    pub const fn argument(self) -> NodeId {
        self.argument
    }
}
