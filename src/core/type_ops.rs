//! Explicit rank-1 type abstraction and application Core payloads.

use super::NodeId;
use crate::types::{
    EffectRow, Kind, NominalTypeId, Type, TypeVariableId, discard_type_iteratively,
    replace_type_iteratively,
};

/// The direction of one explicit module-newtype representation conversion.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum NewtypeConversionDirection {
    /// Converts the representation into its distinct nominal owner.
    Wrap,
    /// Converts the nominal owner into its representation.
    Unwrap,
}

/// One typed, erased module-newtype representation conversion.
///
/// Child and result types remain on their ordinary Core expression envelopes;
/// this payload retains only the canonical nominal identity needed to
/// authenticate their relation.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct NewtypeConversionNode {
    owner: NominalTypeId,
    direction: NewtypeConversionDirection,
    child: NodeId,
}

/// A compile-time lexical nominal scope. Evaluation enters its child directly.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct LocalNominalScopeNode {
    owner: crate::types::NominalTypeId,
    body: NodeId,
}

impl LocalNominalScopeNode {
    pub(crate) const fn new(owner: crate::types::NominalTypeId, body: NodeId) -> Self {
        Self { owner, body }
    }

    /// Returns the lexical nominal introduced by this scope.
    #[must_use]
    pub const fn owner(self) -> crate::types::NominalTypeId {
        self.owner
    }

    /// Returns the scoped computation.
    #[must_use]
    pub const fn body(self) -> NodeId {
        self.body
    }
}

impl NewtypeConversionNode {
    pub(crate) const fn new(
        owner: NominalTypeId,
        direction: NewtypeConversionDirection,
        child: NodeId,
    ) -> Self {
        Self {
            owner,
            direction,
            child,
        }
    }

    /// Returns the stable nominal identity whose representation is converted.
    #[must_use]
    pub const fn owner(self) -> NominalTypeId {
        self.owner
    }

    /// Returns whether this conversion wraps or unwraps its child.
    #[must_use]
    pub const fn direction(self) -> NewtypeConversionDirection {
        self.direction
    }

    /// Returns the sole converted child expression.
    #[must_use]
    pub const fn child(self) -> NodeId {
        self.child
    }
}

/// An explicit abstraction over one or more rank-1 type parameters.
/// Pure execution erases it; Effect execution retains its lexical instantiation.
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

/// An explicit application of one Core type scheme to monotype arguments.
/// Pure execution erases it; Effect execution applies its lexical instantiation.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TypeApplicationNode {
    function: NodeId,
    arguments: Box<[Type]>,
    row_arguments: Box<[EffectRow]>,
}

impl TypeApplicationNode {
    #[cfg_attr(
        not(test),
        allow(
            dead_code,
            reason = "validation and transform tests construct pure type applications directly"
        )
    )]
    pub(crate) fn new(function: NodeId, arguments: Vec<Type>) -> Self {
        Self::new_with_row_arguments(function, arguments, Vec::new())
    }

    pub(crate) fn new_with_row_arguments(
        function: NodeId,
        arguments: Vec<Type>,
        row_arguments: Vec<EffectRow>,
    ) -> Self {
        Self {
            function,
            arguments: arguments.into_boxed_slice(),
            row_arguments: row_arguments.into_boxed_slice(),
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

    /// Returns the ordered complete effect-row arguments.
    #[must_use]
    pub fn row_arguments(&self) -> &[EffectRow] {
        &self.row_arguments
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

    pub(super) fn rewrite_row_arguments<F>(
        &mut self,
        rewrite: &mut F,
    ) -> Result<(), super::BuildError>
    where
        F: FnMut(&EffectRow) -> Result<EffectRow, super::BuildError>,
    {
        for argument in &mut self.row_arguments {
            *argument = rewrite(argument)?;
        }
        Ok(())
    }

    pub(super) fn discard_metadata(self) {
        for argument in self.arguments.into_vec() {
            discard_type_iteratively(argument);
        }
        drop(self.row_arguments);
    }
}
