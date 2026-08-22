//! Structural types shared by elaboration and Core.

use std::{collections::HashMap, fmt, hash::Hash};

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

/// Stable identity of one source or generated type binder.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct TypeVariableId(u32);

impl TypeVariableId {
    /// Creates one program-local type-variable identity.
    #[must_use]
    pub const fn new(value: u32) -> Self {
        Self(value)
    }

    /// Returns the program-local numeric identity.
    #[must_use]
    pub const fn value(self) -> u32 {
        self.0
    }
}

/// Elaborator-private identity of one first-order inference variable.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct InferenceVariableId(u32);

impl InferenceVariableId {
    /// Creates one inference identity inside an elaboration.
    #[must_use]
    pub const fn new(value: u32) -> Self {
        Self(value)
    }

    /// Returns the elaboration-local numeric identity.
    #[must_use]
    pub const fn value(self) -> u32 {
        self.0
    }
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
    /// A rigid or bound type variable identified by its binder.
    Variable(TypeVariableId),
    /// A temporary first-order inference variable, forbidden in validated Core.
    Inference(InferenceVariableId),
    /// A nominal type constructor saturated with its ordered arguments.
    AppliedNominal(NominalTypeId, Box<[Type]>),
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
            Self::Variable(identity) => write!(formatter, "<type-variable:{}>", identity.value()),
            Self::Inference(identity) => write!(formatter, "?{}", identity.value()),
            Self::AppliedNominal(identity, arguments) => {
                write!(
                    formatter,
                    "<type:{}:{}><",
                    identity.source.value(),
                    identity.declaration
                )?;
                for (index, argument) in arguments.iter().enumerate() {
                    if index > 0 {
                        formatter.write_str(", ")?;
                    }
                    argument.fmt(formatter)?;
                }
                formatter.write_str(">")
            }
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
            (Type::Variable(left), Type::Variable(right)) if left == right => {}
            (Type::Inference(left), Type::Inference(right)) if left == right => {}
            (Type::AppliedNominal(left_id, left), Type::AppliedNominal(right_id, right))
                if left_id == right_id && left.len() == right.len() =>
            {
                pending.extend(left.iter().zip(right.iter()));
            }
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

/// Replaces rigid type variables according to one capture-free substitution.
#[must_use]
pub(crate) fn substitute_type_variables(
    ty: &Type,
    replacements: &HashMap<TypeVariableId, Type>,
) -> Type {
    match ty {
        Type::Variable(identity) => replacements
            .get(identity)
            .cloned()
            .unwrap_or_else(|| ty.clone()),
        Type::Tuple(elements) => Type::Tuple(
            elements
                .iter()
                .map(|element| substitute_type_variables(element, replacements))
                .collect::<Vec<_>>()
                .into_boxed_slice(),
        ),
        Type::AppliedNominal(owner, arguments) => Type::AppliedNominal(
            *owner,
            arguments
                .iter()
                .map(|argument| substitute_type_variables(argument, replacements))
                .collect::<Vec<_>>()
                .into_boxed_slice(),
        ),
        Type::Function(domain, codomain) => Type::Function(
            Box::new(substitute_type_variables(domain, replacements)),
            Box::new(substitute_type_variables(codomain, replacements)),
        ),
        Type::Int | Type::Bool | Type::Unit | Type::Nominal(_) | Type::Inference(_) => ty.clone(),
    }
}
