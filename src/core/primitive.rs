//! Primitive operations in typed Core.

use super::dialect::NodeId;
use crate::types::Type;

/// A primitive operation implemented directly by Ash.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Primitive {
    /// Integer addition.
    Add,
    /// Integer multiplication.
    Multiply,
    /// Integer equality.
    Equal,
}

impl Primitive {
    pub(super) const fn signature(self) -> (Type, Type, Type) {
        match self {
            Self::Add | Self::Multiply => (Type::Int, Type::Int, Type::Int),
            Self::Equal => (Type::Int, Type::Int, Type::Bool),
        }
    }
}

/// A binary primitive application payload.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct PrimitiveNode {
    primitive: Primitive,
    left: NodeId,
    right: NodeId,
}

impl PrimitiveNode {
    pub(super) const fn new(primitive: Primitive, left: NodeId, right: NodeId) -> Self {
        Self {
            primitive,
            left,
            right,
        }
    }

    /// Returns the selected primitive.
    #[must_use]
    pub const fn primitive(self) -> Primitive {
        self.primitive
    }

    /// Returns the left operand.
    #[must_use]
    pub const fn left(self) -> NodeId {
        self.left
    }

    /// Returns the right operand.
    #[must_use]
    pub const fn right(self) -> NodeId {
        self.right
    }

    pub(super) const fn children(self) -> [Option<NodeId>; 2] {
        [Some(self.left), Some(self.right)]
    }
}
