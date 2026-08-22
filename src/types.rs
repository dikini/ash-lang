//! Structural types shared by elaboration and Core.

use std::{fmt, hash::Hash};

use crate::source::SourceId;

/// Stable identity of one nominal type declaration.
///
/// The declaration index is assigned in source order. Combining it with the
/// admitted source identity keeps same-spelled declarations in different
/// source files distinct without relying on process-global interning.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct NominalTypeId {
    source: SourceId,
    declaration: u32,
}

/// Stable identity of one constructor declaration.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct ConstructorId {
    owner: NominalTypeId,
    constructor: u32,
}

impl ConstructorId {
    /// Creates one source-order constructor identity under its nominal owner.
    #[must_use]
    pub const fn new(owner: NominalTypeId, constructor: u32) -> Self {
        Self { owner, constructor }
    }

    /// Returns the nominal declaration that owns this constructor.
    #[must_use]
    pub const fn owner(self) -> NominalTypeId {
        self.owner
    }

    /// Returns the source-order index within the owning declaration.
    #[must_use]
    pub const fn constructor(self) -> u32 {
        self.constructor
    }
}

impl NominalTypeId {
    /// Creates the identity for one declaration in an admitted source.
    #[must_use]
    pub const fn new(source: SourceId, declaration: u32) -> Self {
        Self {
            source,
            declaration,
        }
    }

    /// Returns the source that owns the declaration.
    #[must_use]
    pub const fn source(self) -> SourceId {
        self.source
    }

    /// Returns the source-order declaration index.
    #[must_use]
    pub const fn declaration(self) -> u32 {
        self.declaration
    }
}

/// A structural Mini-Ash type.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum Type {
    /// Arbitrary-precision integers.
    Int,
    /// Boolean values.
    Bool,
    /// The unit value.
    Unit,
    /// An ordered structural product with at least two elements.
    Tuple(Box<[Type]>),
    /// A nominal algebraic data type identified by its declaration.
    Nominal(NominalTypeId),
    /// A unary function from a domain to a codomain.
    Function(Box<Type>, Box<Type>),
}

impl fmt::Display for Type {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Int => formatter.write_str("Int"),
            Self::Bool => formatter.write_str("Bool"),
            Self::Unit => formatter.write_str("Unit"),
            Self::Tuple(elements) => {
                formatter.write_str("(")?;
                for (index, element) in elements.iter().enumerate() {
                    if index > 0 {
                        formatter.write_str(", ")?;
                    }
                    element.fmt(formatter)?;
                }
                formatter.write_str(")")
            }
            Self::Nominal(identity) => write!(
                formatter,
                "<type:{}:{}>",
                identity.source.value(),
                identity.declaration
            ),
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

/// Applies the single semantic type-equality rule used across the compiler.
///
/// Nominal types compare by declaration identity. Tuples and functions compare
/// structurally. The explicit work stack avoids host recursion at the admitted
/// type-depth boundary.
#[must_use]
pub fn same_type(left: &Type, right: &Type) -> bool {
    let mut pending = vec![(left, right)];
    while let Some((left, right)) = pending.pop() {
        match (left, right) {
            (Type::Int, Type::Int) | (Type::Bool, Type::Bool) | (Type::Unit, Type::Unit) => {}
            (Type::Nominal(left), Type::Nominal(right)) if left == right => {}
            (Type::Tuple(left), Type::Tuple(right)) if left.len() == right.len() => {
                pending.extend(left.iter().zip(right.iter()));
            }
            (
                Type::Function(left_domain, left_codomain),
                Type::Function(right_domain, right_codomain),
            ) => {
                pending.push((left_codomain, right_codomain));
                pending.push((left_domain, right_domain));
            }
            _ => return false,
        }
    }
    true
}
