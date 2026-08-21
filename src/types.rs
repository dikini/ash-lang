//! Structural types shared by elaboration and Core.

use std::fmt;

/// A structural Mini-Ash type.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum Type {
    /// Arbitrary-precision integers.
    Int,
    /// Boolean values.
    Bool,
    /// The unit value.
    Unit,
    /// A unary function from a domain to a codomain.
    Function(Box<Type>, Box<Type>),
}

impl fmt::Display for Type {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Int => formatter.write_str("Int"),
            Self::Bool => formatter.write_str("Bool"),
            Self::Unit => formatter.write_str("Unit"),
            Self::Function(domain, codomain) => {
                if matches!(domain.as_ref(), Self::Function(_, _)) {
                    write!(formatter, "({domain})")?;
                } else {
                    write!(formatter, "{domain}")?;
                }
                write!(formatter, " -> {codomain}")
            }
        }
    }
}
