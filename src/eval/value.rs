//! Runtime values for the retained Mini-Ash evaluator.

use std::fmt;

use crate::integer::Integer;

/// A fully evaluated primitive Mini-Ash value.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Value {
    /// An arbitrary-precision mathematical integer.
    Integer(Integer),
    /// A Boolean value.
    Boolean(bool),
    /// The unit value.
    Unit,
}

impl fmt::Display for Value {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Integer(value) => value.fmt(formatter),
            Self::Boolean(value) => value.fmt(formatter),
            Self::Unit => formatter.write_str("()"),
        }
    }
}
