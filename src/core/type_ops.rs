//! Explicit rank-1 type abstraction and application Core payloads.

use super::NodeId;
use crate::types::{
    Kind, Type, TypeVariableId, discard_type_iteratively, replace_type_iteratively,
};

/// A type-erased abstraction over one or more rank-1 type parameters.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TypeAbstractionNode {
    parameters: Box<[(TypeVariableId, Kind)]>,
    body: NodeId,
}

impl TypeAbstractionNode {
    pub(crate) fn new(parameters: Vec<(TypeVariableId, Kind)>, body: NodeId) -> Self {
        Self {
            parameters: parameters.into_boxed_slice(),
            body,
        }
    }

    /// Returns the ordered bound type-variable identities and fixed kinds.
    #[must_use]
    pub fn parameters(&self) -> &[(TypeVariableId, Kind)] {
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
            let rewritten = rewrite(argument)?;
            replace_type_iteratively(argument, rewritten);
        }
        Ok(())
    }

    pub(super) fn discard_metadata(self) {
        for argument in self.arguments.into_vec() {
            discard_type_iteratively(argument);
        }
    }
}
