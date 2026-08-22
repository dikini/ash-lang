//! Explicit rank-1 type abstraction and application Core payloads.

use super::NodeId;
use crate::types::{Type, TypeVariableId};

/// A type-erased abstraction over one or more rank-1 type parameters.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TypeAbstractionNode {
    parameters: Box<[TypeVariableId]>,
    body: NodeId,
}

impl TypeAbstractionNode {
    pub(crate) fn new(parameters: Vec<TypeVariableId>, body: NodeId) -> Self {
        Self {
            parameters: parameters.into_boxed_slice(),
            body,
        }
    }

    /// Returns the ordered bound type-variable identities.
    #[must_use]
    pub fn parameters(&self) -> &[TypeVariableId] {
        &self.parameters
    }

    /// Returns the polymorphic body expression.
    #[must_use]
    pub const fn body(&self) -> NodeId {
        self.body
    }
}

/// An erased application of one Core type scheme to monotype arguments.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TypeApplicationNode {
    function: NodeId,
    arguments: Box<[Type]>,
}

impl TypeApplicationNode {
    pub(crate) fn new(function: NodeId, arguments: Vec<Type>) -> Self {
        Self {
            function,
            arguments: arguments.into_boxed_slice(),
        }
    }

    /// Returns the expression exposing the applied scheme.
    #[must_use]
    pub const fn function(&self) -> NodeId {
        self.function
    }

    /// Returns the ordered type arguments.
    #[must_use]
    pub fn arguments(&self) -> &[Type] {
        &self.arguments
    }

    pub(super) fn rewrite_types<F>(&mut self, rewrite: &mut F) -> Result<(), super::BuildError>
    where
        F: FnMut(&Type) -> Result<Type, super::BuildError>,
    {
        for argument in &mut self.arguments {
            *argument = rewrite(argument)?;
        }
        Ok(())
    }
}
