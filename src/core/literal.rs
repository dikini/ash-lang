//! Literal payloads in typed Core.

use crate::{integer::Integer, types::Type};

/// An integer literal payload.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct IntegerNode {
    value: Integer,
}

impl IntegerNode {
    pub(super) const fn new(value: Integer) -> Self {
        Self { value }
    }

    /// Returns the literal value.
    #[must_use]
    pub const fn value(&self) -> &Integer {
        &self.value
    }

    pub(super) const fn expected_type(&self) -> Type {
        Type::Int
    }
}

/// A Boolean literal payload.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct BooleanNode {
    value: bool,
}

impl BooleanNode {
    pub(super) const fn new(value: bool) -> Self {
        Self { value }
    }

    /// Returns the literal value.
    #[must_use]
    pub const fn value(self) -> bool {
        self.value
    }

    pub(super) const fn expected_type(self) -> Type {
        Type::Bool
    }
}

/// The unit literal payload.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct UnitNode;

impl UnitNode {
    pub(super) const fn expected_type(self) -> Type {
        Type::Unit
    }
}
