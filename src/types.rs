//! Structural types shared by elaboration and Core.

use std::{collections::HashMap, fmt, hash::Hash};

use crate::source::SourceId;

/// Maximum cumulative structural type cells processed by one compiler phase.
pub const TYPE_WORK_LIMIT: usize = 327_680;

/// Cumulative accounting for compiler-owned structural type work.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub(crate) struct TypeWorkBudget {
    used: usize,
}

impl TypeWorkBudget {
    pub(crate) fn charge(&mut self, cells: usize) -> Result<(), ()> {
        let next = self.used.checked_add(cells).ok_or(())?;
        if next > TYPE_WORK_LIMIT {
            return Err(());
        }
        self.used = next;
        Ok(())
    }
}

pub(crate) fn charge_type_cells(ty: &Type, budget: &mut TypeWorkBudget) -> Result<(), ()> {
    enum Task<'a> {
        Visit(&'a Type),
        Sequence(std::slice::Iter<'a, Type>),
    }
    let mut work = vec![Task::Visit(ty)];
    while let Some(task) = work.pop() {
        let Task::Visit(ty) = task else {
            let Task::Sequence(mut remaining) = task else {
                unreachable!()
            };
            if let Some(ty) = remaining.next() {
                work.push(Task::Sequence(remaining));
                work.push(Task::Visit(ty));
            }
            continue;
        };
        budget.charge(1)?;
        match ty {
            Type::Tuple(elements) | Type::AppliedNominal(_, elements) => {
                work.push(Task::Sequence(elements.iter()));
            }
            Type::Function(domain, codomain) => {
                work.push(Task::Visit(codomain));
                work.push(Task::Visit(domain));
            }
            Type::Forall(parameters, body) => {
                budget.charge(parameters.len())?;
                work.push(Task::Visit(body));
            }
            Type::Int
            | Type::Bool
            | Type::Unit
            | Type::Nominal(_)
            | Type::Variable(_)
            | Type::Inference(_) => {}
        }
    }
    Ok(())
}

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
    /// A rank-1 type scheme binding variables in its monotype body.
    Forall(Box<[TypeVariableId]>, Box<Type>),
    /// A unary function from a domain to a codomain.
    Function(Box<Type>, Box<Type>),
}

/// Destroys an owned type without following host-language recursion.
pub(crate) fn discard_type_iteratively(root: Type) {
    enum Task {
        Visit(Type),
        Sequence(std::vec::IntoIter<Type>),
    }

    let mut work = vec![Task::Visit(root)];
    while let Some(task) = work.pop() {
        match task {
            Task::Visit(Type::Tuple(elements) | Type::AppliedNominal(_, elements)) => {
                work.push(Task::Sequence(elements.into_vec().into_iter()));
            }
            Task::Visit(Type::Function(domain, codomain)) => {
                work.push(Task::Visit(*codomain));
                work.push(Task::Visit(*domain));
            }
            Task::Visit(Type::Forall(_, body)) => work.push(Task::Visit(*body)),
            Task::Visit(
                Type::Int
                | Type::Bool
                | Type::Unit
                | Type::Nominal(_)
                | Type::Variable(_)
                | Type::Inference(_),
            ) => {}
            Task::Sequence(mut remaining) => {
                if let Some(ty) = remaining.next() {
                    work.push(Task::Sequence(remaining));
                    work.push(Task::Visit(ty));
                }
            }
        }
    }
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
            Self::Forall(parameters, body) => {
                formatter.write_str("forall ")?;
                for (index, parameter) in parameters.iter().enumerate() {
                    if index > 0 {
                        formatter.write_str(", ")?;
                    }
                    write!(formatter, "<type-variable:{}>", parameter.value())?;
                }
                write!(formatter, ". {body}")
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
    enum Task<'a> {
        Compare(&'a Type, &'a Type),
        Sequence(std::iter::Zip<std::slice::Iter<'a, Type>, std::slice::Iter<'a, Type>>),
    }
    let mut pending = vec![Task::Compare(left, right)];
    while let Some(task) = pending.pop() {
        let Task::Compare(left, right) = task else {
            let Task::Sequence(mut remaining) = task else {
                unreachable!()
            };
            if let Some((left, right)) = remaining.next() {
                pending.push(Task::Sequence(remaining));
                pending.push(Task::Compare(left, right));
            }
            continue;
        };
        match (left, right) {
            (Type::Int, Type::Int) | (Type::Bool, Type::Bool) | (Type::Unit, Type::Unit) => {}
            (Type::Nominal(left), Type::Nominal(right)) if left == right => {}
            (Type::Variable(left), Type::Variable(right)) if left == right => {}
            (Type::Inference(left), Type::Inference(right)) if left == right => {}
            (Type::AppliedNominal(left_id, left), Type::AppliedNominal(right_id, right))
                if left_id == right_id && left.len() == right.len() =>
            {
                pending.push(Task::Sequence(left.iter().zip(right.iter())));
            }
            (Type::Forall(left_parameters, left), Type::Forall(right_parameters, right))
                if left_parameters == right_parameters =>
            {
                pending.push(Task::Compare(left, right));
            }
            (Type::Tuple(left), Type::Tuple(right)) if left.len() == right.len() => {
                pending.push(Task::Sequence(left.iter().zip(right.iter())));
            }
            (
                Type::Function(left_domain, left_codomain),
                Type::Function(right_domain, right_codomain),
            ) => {
                pending.push(Task::Compare(left_codomain, right_codomain));
                pending.push(Task::Compare(left_domain, right_domain));
            }
            _ => return false,
        }
    }
    true
}

/// Charges the expanded result before applying one capture-free substitution.
pub(crate) fn substitute_type_variables_with<E>(
    ty: &Type,
    replacements: &HashMap<TypeVariableId, Type>,
    mut charge: impl FnMut(usize) -> Result<(), E>,
) -> Result<Type, E> {
    enum ChargeTask<'a> {
        Visit(&'a Type, bool),
        Slice(std::slice::Iter<'a, Type>, bool),
    }

    let mut work = vec![ChargeTask::Visit(ty, true)];
    while let Some(task) = work.pop() {
        match task {
            ChargeTask::Visit(Type::Variable(identity), true)
                if replacements.contains_key(identity) =>
            {
                work.push(ChargeTask::Visit(&replacements[identity], false));
            }
            ChargeTask::Visit(Type::Tuple(elements), substitute)
            | ChargeTask::Visit(Type::AppliedNominal(_, elements), substitute) => {
                charge(1)?;
                work.push(ChargeTask::Slice(elements.iter(), substitute));
            }
            ChargeTask::Visit(Type::Function(domain, codomain), substitute) => {
                charge(1)?;
                work.push(ChargeTask::Visit(codomain, substitute));
                work.push(ChargeTask::Visit(domain, substitute));
            }
            ChargeTask::Visit(Type::Forall(parameters, body), substitute) => {
                charge(1)?;
                let substitute = substitute
                    && !parameters
                        .iter()
                        .any(|parameter| replacements.contains_key(parameter));
                work.push(ChargeTask::Visit(body, substitute));
            }
            ChargeTask::Visit(
                Type::Int
                | Type::Bool
                | Type::Unit
                | Type::Nominal(_)
                | Type::Variable(_)
                | Type::Inference(_),
                _,
            ) => charge(1)?,
            ChargeTask::Slice(mut remaining, substitute) => {
                if let Some(element) = remaining.next() {
                    work.push(ChargeTask::Slice(remaining, substitute));
                    work.push(ChargeTask::Visit(element, substitute));
                }
            }
        }
    }

    Ok(substitute_type_variables(ty, replacements))
}

fn substitute_type_variables(ty: &Type, replacements: &HashMap<TypeVariableId, Type>) -> Type {
    enum Task<'a> {
        Visit(&'a Type, bool),
        Sequence(std::slice::Iter<'a, Type>, bool),
        FinishTuple(usize),
        FinishApplied(NominalTypeId, usize),
        FinishFunction,
        FinishForall(Box<[TypeVariableId]>),
    }

    let mut work = vec![Task::Visit(ty, true)];
    let mut rebuilt = Vec::new();
    while let Some(task) = work.pop() {
        match task {
            Task::Visit(Type::Variable(identity), true) if replacements.contains_key(identity) => {
                work.push(Task::Visit(&replacements[identity], false));
            }
            Task::Visit(Type::Int, _) => rebuilt.push(Type::Int),
            Task::Visit(Type::Bool, _) => rebuilt.push(Type::Bool),
            Task::Visit(Type::Unit, _) => rebuilt.push(Type::Unit),
            Task::Visit(Type::Nominal(owner), _) => rebuilt.push(Type::Nominal(*owner)),
            Task::Visit(Type::Variable(identity), _) => rebuilt.push(Type::Variable(*identity)),
            Task::Visit(Type::Inference(identity), _) => rebuilt.push(Type::Inference(*identity)),
            Task::Visit(Type::Tuple(elements), substitute) => {
                work.push(Task::FinishTuple(elements.len()));
                work.push(Task::Sequence(elements.iter(), substitute));
            }
            Task::Visit(Type::AppliedNominal(owner, arguments), substitute) => {
                work.push(Task::FinishApplied(*owner, arguments.len()));
                work.push(Task::Sequence(arguments.iter(), substitute));
            }
            Task::Visit(Type::Function(domain, codomain), substitute) => {
                work.push(Task::FinishFunction);
                work.push(Task::Visit(codomain, substitute));
                work.push(Task::Visit(domain, substitute));
            }
            Task::Visit(Type::Forall(parameters, body), substitute) => {
                work.push(Task::FinishForall(parameters.clone()));
                let substitute = substitute
                    && !parameters
                        .iter()
                        .any(|parameter| replacements.contains_key(parameter));
                work.push(Task::Visit(body, substitute));
            }
            Task::Sequence(mut remaining, substitute) => {
                if let Some(ty) = remaining.next() {
                    work.push(Task::Sequence(remaining, substitute));
                    work.push(Task::Visit(ty, substitute));
                }
            }
            Task::FinishTuple(count) => {
                let elements = rebuilt.split_off(rebuilt.len() - count);
                rebuilt.push(Type::Tuple(elements.into_boxed_slice()));
            }
            Task::FinishApplied(owner, count) => {
                let arguments = rebuilt.split_off(rebuilt.len() - count);
                rebuilt.push(Type::AppliedNominal(owner, arguments.into_boxed_slice()));
            }
            Task::FinishFunction => {
                let codomain = rebuilt.pop().expect("type reconstruction codomain");
                let domain = rebuilt.pop().expect("type reconstruction domain");
                rebuilt.push(Type::Function(Box::new(domain), Box::new(codomain)));
            }
            Task::FinishForall(parameters) => {
                let body = rebuilt.pop().expect("type reconstruction scheme body");
                rebuilt.push(Type::Forall(parameters, Box::new(body)));
            }
        }
    }
    rebuilt.pop().expect("one reconstructed type")
}

/// The internal kind language used to check type constructors.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Kind {
    /// The kind of every source-admitted value type.
    Type,
    /// An internal unary type-constructor kind.
    Arrow(Box<Kind>, Box<Kind>),
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn substitution_charges_the_expanded_result_before_rebuilding() {
        let parameter = TypeVariableId::new(0);
        let source = Type::Tuple(vec![Type::Variable(parameter); 16].into_boxed_slice());
        let replacements = HashMap::from([(
            parameter,
            Type::Tuple(vec![Type::Int; 16].into_boxed_slice()),
        )]);
        let mut remaining = 128_usize;

        let result = substitute_type_variables_with(&source, &replacements, |cells| {
            remaining = remaining.checked_sub(cells).ok_or(())?;
            Ok(())
        });

        assert_eq!(result, Err(()));
        assert_eq!(remaining, 0);
    }
}
