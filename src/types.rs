//! Structural types shared by elaboration and Core.

use std::{
    collections::HashMap,
    fmt,
    hash::{Hash, Hasher},
};

use crate::module::ModuleId;

/// Maximum cumulative structural type cells processed by one compiler phase.
pub const TYPE_WORK_LIMIT: usize = 327_680;

/// Cumulative accounting for compiler-owned structural type work.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct TypeWorkBudget {
    used: usize,
    limit: usize,
}

impl Default for TypeWorkBudget {
    fn default() -> Self {
        Self {
            used: 0,
            limit: TYPE_WORK_LIMIT,
        }
    }
}

impl TypeWorkBudget {
    #[cfg(test)]
    pub(crate) const fn with_limit(limit: usize) -> Self {
        Self { used: 0, limit }
    }

    #[cfg(test)]
    pub(crate) const fn used(&self) -> usize {
        self.used
    }

    pub(crate) fn charge(&mut self, cells: usize) -> Result<(), ()> {
        let next = self.used.checked_add(cells).ok_or(())?;
        if next > self.limit {
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
            Type::Tuple(elements) => work.push(Task::Sequence(elements.iter())),
            Type::Application(function, argument) => {
                work.push(Task::Visit(argument));
                work.push(Task::Visit(function));
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

pub(crate) fn clone_type_with_budget(ty: &Type, budget: &mut TypeWorkBudget) -> Result<Type, ()> {
    enum Task<'a> {
        Visit(&'a Type),
        Sequence(std::slice::Iter<'a, Type>),
        Tuple(usize),
        Application,
        Function,
        Forall(Box<[TypeVariableId]>),
    }

    charge_type_cells(ty, budget)?;
    let mut work = vec![Task::Visit(ty)];
    let mut rebuilt = Vec::new();
    while let Some(task) = work.pop() {
        match task {
            Task::Visit(Type::Int) => rebuilt.push(Type::Int),
            Task::Visit(Type::Bool) => rebuilt.push(Type::Bool),
            Task::Visit(Type::Unit) => rebuilt.push(Type::Unit),
            Task::Visit(Type::Nominal(id)) => rebuilt.push(Type::Nominal(*id)),
            Task::Visit(Type::Variable(id)) => rebuilt.push(Type::Variable(*id)),
            Task::Visit(Type::Inference(id)) => rebuilt.push(Type::Inference(*id)),
            Task::Visit(Type::Tuple(elements)) => {
                work.push(Task::Tuple(elements.len()));
                work.push(Task::Sequence(elements.iter()));
            }
            Task::Visit(Type::Application(function, argument)) => {
                work.push(Task::Application);
                work.push(Task::Visit(argument));
                work.push(Task::Visit(function));
            }
            Task::Visit(Type::Function(domain, codomain)) => {
                work.push(Task::Function);
                work.push(Task::Visit(codomain));
                work.push(Task::Visit(domain));
            }
            Task::Visit(Type::Forall(parameters, body)) => {
                work.push(Task::Forall(parameters.clone()));
                work.push(Task::Visit(body));
            }
            Task::Sequence(mut remaining) => {
                if let Some(next) = remaining.next() {
                    work.push(Task::Sequence(remaining));
                    work.push(Task::Visit(next));
                }
            }
            Task::Tuple(count) => {
                let elements = rebuilt.split_off(rebuilt.len() - count);
                rebuilt.push(Type::Tuple(elements.into_boxed_slice()));
            }
            Task::Application => {
                let argument = rebuilt.pop().expect("cloned application argument");
                let function = rebuilt.pop().expect("cloned application function");
                rebuilt.push(Type::Application(Box::new(function), Box::new(argument)));
            }
            Task::Function => {
                let codomain = rebuilt.pop().expect("cloned function codomain");
                let domain = rebuilt.pop().expect("cloned function domain");
                rebuilt.push(Type::Function(Box::new(domain), Box::new(codomain)));
            }
            Task::Forall(parameters) => {
                let body = rebuilt.pop().expect("cloned scheme body");
                rebuilt.push(Type::Forall(parameters, Box::new(body)));
            }
        }
    }
    rebuilt.pop().ok_or(())
}

fn clone_type(ty: &Type) -> Type {
    let mut unbounded = TypeWorkBudget {
        used: 0,
        limit: usize::MAX,
    };
    match clone_type_with_budget(ty, &mut unbounded) {
        Ok(cloned) => cloned,
        Err(()) => unreachable!("an in-memory type cannot exceed the address-space work bound"),
    }
}

/// Stable identity of one nominal type declaration.
///
/// The declaration index is assigned in source order within its defining
/// canonical module.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct NominalTypeId {
    module: ModuleId,
    declaration: u32,
}

/// Stable identity of one constructor declaration.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ConstructorId {
    owner: NominalTypeId,
    constructor: u32,
}

/// Stable identity of one resolved or compiler-generated type binder.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum TypeVariableId {
    /// A source type binder qualified by its defining canonical module.
    Resolved {
        /// Defining module identity.
        module: ModuleId,
        /// Source-order type-binder index within that module.
        local: u32,
    },
    /// An elaborator-generated type binder.
    Generated(u32),
}

impl TypeVariableId {
    /// Creates one compiler-generated type-variable identity.
    ///
    /// Retained as the compatibility spelling for Core and type fixtures.
    #[must_use]
    pub const fn new(local: u32) -> Self {
        Self::generated(local)
    }

    /// Creates one module-qualified source type-variable identity.
    #[must_use]
    pub const fn resolved(module: ModuleId, local: u32) -> Self {
        Self::Resolved { module, local }
    }

    /// Creates one compiler-generated type-variable identity.
    #[must_use]
    pub const fn generated(local: u32) -> Self {
        Self::Generated(local)
    }

    /// Returns the defining module for a source type binder.
    #[must_use]
    pub const fn module(self) -> Option<ModuleId> {
        match self {
            Self::Resolved { module, .. } => Some(module),
            Self::Generated(_) => None,
        }
    }

    /// Returns the module-local or generated-program-local index.
    #[must_use]
    pub const fn local(self) -> u32 {
        match self {
            Self::Resolved { local, .. } | Self::Generated(local) => local,
        }
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
    pub fn new(module: impl Into<ModuleId>, declaration: u32) -> Self {
        Self {
            module: module.into(),
            declaration,
        }
    }

    /// Returns the canonical module that owns the declaration.
    #[must_use]
    pub const fn module(self) -> ModuleId {
        self.module
    }

    /// Returns the source-order declaration index.
    #[must_use]
    pub const fn declaration(self) -> u32 {
        self.declaration
    }
}

/// A structural Ash type.
#[derive(Debug)]
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
    /// One structural application of a type function to one type argument.
    Application(Box<Type>, Box<Type>),
    /// A rank-1 type scheme binding variables in its monotype body.
    Forall(Box<[TypeVariableId]>, Box<Type>),
    /// A unary function from a domain to a codomain.
    Function(Box<Type>, Box<Type>),
}

/// Crate-internal ownership guard for a type crossing fallible work.
///
/// The contained type is dismantled iteratively unless it is explicitly
/// transferred with [`Self::into_inner`].
pub(crate) struct IterativeTypeOwner(Option<Type>);

impl IterativeTypeOwner {
    pub(crate) const fn new(ty: Type) -> Self {
        Self(Some(ty))
    }

    pub(crate) fn into_inner(mut self) -> Type {
        self.0
            .take()
            .expect("an iterative type owner transfers once")
    }

    pub(crate) fn replace(&mut self, ty: Type) {
        if let Some(displaced) = self.0.replace(ty) {
            discard_type_iteratively(displaced);
        }
    }
}

impl std::ops::Deref for IterativeTypeOwner {
    type Target = Type;

    fn deref(&self) -> &Self::Target {
        self.0
            .as_ref()
            .expect("an iterative type owner remains initialized")
    }
}

impl Drop for IterativeTypeOwner {
    fn drop(&mut self) {
        if let Some(ty) = self.0.take() {
            discard_type_iteratively(ty);
        }
    }
}

impl Type {
    /// Returns the nominal constructor at the left edge of an application.
    #[must_use]
    pub fn outer_nominal(&self) -> Option<NominalTypeId> {
        let mut current = self;
        loop {
            match current {
                Self::Nominal(identity) => return Some(*identity),
                Self::Application(function, _) => current = function,
                _ => return None,
            }
        }
    }

    pub(crate) fn apply_arguments(
        function: Type,
        arguments: impl IntoIterator<Item = Type>,
    ) -> Type {
        arguments.into_iter().fold(function, |function, argument| {
            Self::Application(Box::new(function), Box::new(argument))
        })
    }
}

impl Clone for Type {
    fn clone(&self) -> Self {
        clone_type(self)
    }
}

impl PartialEq for Type {
    fn eq(&self, other: &Self) -> bool {
        same_type(self, other)
    }
}

impl Eq for Type {}

impl Hash for Type {
    fn hash<H: Hasher>(&self, state: &mut H) {
        hash_type(self, state);
    }
}

/// Destroys an owned type without following host-language recursion.
///
/// Use this when consuming a potentially deep [`Type`] returned by a public
/// API. Ordinary Rust drop follows the boxed structural tree recursively,
/// while this operation keeps host-stack use bounded.
pub fn discard_type_iteratively(root: Type) {
    enum Task {
        Visit(Type),
        Sequence(std::vec::IntoIter<Type>),
    }

    let mut work = vec![Task::Visit(root)];
    while let Some(task) = work.pop() {
        match task {
            Task::Visit(Type::Tuple(elements)) => {
                work.push(Task::Sequence(elements.into_vec().into_iter()));
            }
            Task::Visit(Type::Application(function, argument)) => {
                work.push(Task::Visit(*argument));
                work.push(Task::Visit(*function));
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

/// Replaces one owned type while destroying the displaced tree iteratively.
///
/// Assigning directly to a [`Type`] follows Rust's recursive drop path for the
/// displaced value. Internal metadata rewrites use this helper so replacing a
/// valid, deeply nested type keeps host-stack use bounded.
pub(crate) fn replace_type_iteratively(target: &mut Type, replacement: Type) {
    let displaced = std::mem::replace(target, replacement);
    discard_type_iteratively(displaced);
}

impl fmt::Display for Type {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write_type(self, formatter)
    }
}

fn write_type(ty: &Type, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
    enum Task<'a> {
        Visit(&'a Type),
        ApplicationSpine(&'a Type),
        Text(&'static str),
        Sequence(std::slice::Iter<'a, Type>),
    }

    let mut work = vec![Task::Visit(ty)];
    while let Some(task) = work.pop() {
        match task {
            Task::Text(text) => formatter.write_str(text)?,
            Task::Sequence(mut remaining) => {
                if let Some(next) = remaining.next() {
                    if !remaining.as_slice().is_empty() {
                        work.push(Task::Sequence(remaining));
                        work.push(Task::Text(", "));
                    }
                    work.push(Task::Visit(next));
                }
            }
            Task::Visit(Type::Int) => formatter.write_str("Int")?,
            Task::Visit(Type::Bool) => formatter.write_str("Bool")?,
            Task::Visit(Type::Unit) => formatter.write_str("Unit")?,
            Task::Visit(Type::Tuple(elements)) => {
                work.push(Task::Text(")"));
                work.push(Task::Sequence(elements.iter()));
                work.push(Task::Text("("));
            }
            Task::Visit(Type::Nominal(identity)) => write!(
                formatter,
                "<type:{}:{}>",
                identity.module, identity.declaration
            )?,
            Task::Visit(Type::Variable(TypeVariableId::Resolved { module, local })) => {
                write!(formatter, "<type-variable:{module}:{local}>")?;
            }
            Task::Visit(Type::Variable(TypeVariableId::Generated(local))) => {
                write!(formatter, "<type-variable:generated:{local}>")?;
            }
            Task::Visit(Type::Inference(identity)) => write!(formatter, "?{}", identity.value())?,
            Task::Visit(application @ Type::Application(_, _)) => {
                work.push(Task::Text(">"));
                work.push(Task::ApplicationSpine(application));
            }
            Task::ApplicationSpine(Type::Application(function, argument)) => {
                work.push(Task::Visit(argument));
                if matches!(function.as_ref(), Type::Application(_, _)) {
                    work.push(Task::Text(", "));
                    work.push(Task::ApplicationSpine(function));
                } else {
                    work.push(Task::Text("<"));
                    if matches!(function.as_ref(), Type::Function(_, _) | Type::Forall(_, _)) {
                        work.push(Task::Text(")"));
                        work.push(Task::Visit(function));
                        work.push(Task::Text("("));
                    } else {
                        work.push(Task::Visit(function));
                    }
                }
            }
            Task::ApplicationSpine(_) => unreachable!("application spine tasks are closed"),
            Task::Visit(Type::Forall(parameters, body)) => {
                formatter.write_str("forall ")?;
                for (index, parameter) in parameters.iter().enumerate() {
                    if index > 0 {
                        formatter.write_str(", ")?;
                    }
                    write!(formatter, "<type-variable:{}>", parameter.local())?;
                }
                formatter.write_str(". ")?;
                work.push(Task::Visit(body));
            }
            Task::Visit(Type::Function(domain, codomain)) => {
                work.push(Task::Visit(codomain));
                work.push(Task::Text(" -> "));
                if matches!(domain.as_ref(), Type::Function(_, _)) {
                    work.push(Task::Text(")"));
                    work.push(Task::Visit(domain));
                    work.push(Task::Text("("));
                } else {
                    work.push(Task::Visit(domain));
                }
            }
        }
    }
    Ok(())
}

#[cfg(test)]
pub(crate) fn render_type_with_budget(
    ty: &Type,
    budget: &mut TypeWorkBudget,
) -> Result<String, ()> {
    charge_type_cells(ty, budget)?;
    Ok(ty.to_string())
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
            (
                Type::Application(left_function, left_argument),
                Type::Application(right_function, right_argument),
            ) => {
                pending.push(Task::Compare(left_argument, right_argument));
                pending.push(Task::Compare(left_function, right_function));
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

#[cfg(test)]
pub(crate) fn same_type_with_budget(
    left: &Type,
    right: &Type,
    budget: &mut TypeWorkBudget,
) -> Result<bool, ()> {
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
        budget.charge(1)?;
        match (left, right) {
            (Type::Int, Type::Int) | (Type::Bool, Type::Bool) | (Type::Unit, Type::Unit) => {}
            (Type::Nominal(left), Type::Nominal(right)) if left == right => {}
            (Type::Variable(left), Type::Variable(right)) if left == right => {}
            (Type::Inference(left), Type::Inference(right)) if left == right => {}
            (
                Type::Application(left_function, left_argument),
                Type::Application(right_function, right_argument),
            ) => {
                pending.push(Task::Compare(left_argument, right_argument));
                pending.push(Task::Compare(left_function, right_function));
            }
            (Type::Forall(left_parameters, left), Type::Forall(right_parameters, right))
                if left_parameters.len() == right_parameters.len() =>
            {
                budget.charge(left_parameters.len())?;
                if left_parameters != right_parameters {
                    return Ok(false);
                }
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
            _ => return Ok(false),
        }
    }
    Ok(true)
}

fn hash_type<H: Hasher>(ty: &Type, state: &mut H) {
    enum Task<'a> {
        Visit(&'a Type),
        Sequence(std::slice::Iter<'a, Type>),
    }

    let mut work = vec![Task::Visit(ty)];
    while let Some(task) = work.pop() {
        match task {
            Task::Sequence(mut remaining) => {
                if let Some(next) = remaining.next() {
                    work.push(Task::Sequence(remaining));
                    work.push(Task::Visit(next));
                }
            }
            Task::Visit(Type::Int) => 0_u8.hash(state),
            Task::Visit(Type::Bool) => 1_u8.hash(state),
            Task::Visit(Type::Unit) => 2_u8.hash(state),
            Task::Visit(Type::Tuple(elements)) => {
                3_u8.hash(state);
                elements.len().hash(state);
                work.push(Task::Sequence(elements.iter()));
            }
            Task::Visit(Type::Nominal(identity)) => {
                4_u8.hash(state);
                identity.hash(state);
            }
            Task::Visit(Type::Variable(identity)) => {
                5_u8.hash(state);
                identity.hash(state);
            }
            Task::Visit(Type::Inference(identity)) => {
                6_u8.hash(state);
                identity.hash(state);
            }
            Task::Visit(Type::Application(function, argument)) => {
                7_u8.hash(state);
                work.push(Task::Visit(argument));
                work.push(Task::Visit(function));
            }
            Task::Visit(Type::Forall(parameters, body)) => {
                8_u8.hash(state);
                parameters.hash(state);
                work.push(Task::Visit(body));
            }
            Task::Visit(Type::Function(domain, codomain)) => {
                9_u8.hash(state);
                work.push(Task::Visit(codomain));
                work.push(Task::Visit(domain));
            }
        }
    }
}

#[cfg(test)]
pub(crate) fn hash_type_with_budget<H: Hasher>(
    ty: &Type,
    state: &mut H,
    budget: &mut TypeWorkBudget,
) -> Result<(), ()> {
    charge_type_cells(ty, budget)?;
    hash_type(ty, state);
    Ok(())
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
            ChargeTask::Visit(Type::Tuple(elements), substitute) => {
                charge(1)?;
                work.push(ChargeTask::Slice(elements.iter(), substitute));
            }
            ChargeTask::Visit(Type::Application(function, argument), substitute) => {
                charge(1)?;
                work.push(ChargeTask::Visit(argument, substitute));
                work.push(ChargeTask::Visit(function, substitute));
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
        FinishApplication,
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
            Task::Visit(Type::Application(function, argument), substitute) => {
                work.push(Task::FinishApplication);
                work.push(Task::Visit(argument, substitute));
                work.push(Task::Visit(function, substitute));
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
            Task::FinishApplication => {
                let argument = rebuilt.pop().expect("type reconstruction argument");
                let function = rebuilt.pop().expect("type reconstruction function");
                rebuilt.push(Type::Application(Box::new(function), Box::new(argument)));
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
    use crate::module::ModuleId;
    use std::{
        collections::hash_map::DefaultHasher,
        hash::{Hash, Hasher},
    };

    #[test]
    fn canonical_application_is_unary_and_injective() {
        let result = NominalTypeId::new(ModuleId::new(0), 0);
        let application = Type::Application(
            Box::new(Type::Application(
                Box::new(Type::Nominal(result)),
                Box::new(Type::Int),
            )),
            Box::new(Type::Bool),
        );
        let different_function =
            Type::Application(Box::new(Type::Nominal(result)), Box::new(Type::Bool));
        let different_argument = Type::Application(
            Box::new(Type::Application(
                Box::new(Type::Nominal(result)),
                Box::new(Type::Int),
            )),
            Box::new(Type::Unit),
        );

        assert_eq!(Type::Nominal(result).outer_nominal(), Some(result));
        assert_eq!(different_function.outer_nominal(), Some(result));
        assert_eq!(application.outer_nominal(), Some(result));
        assert_eq!(
            Type::Application(Box::new(Type::Int), Box::new(Type::Bool)).outer_nominal(),
            None,
        );
        assert_ne!(application, different_function);
        assert_ne!(application, different_argument);
        assert_eq!(
            application.to_string(),
            format!("{}<Int, Bool>", Type::Nominal(result))
        );

        // One unit for each of the two application nodes and their three leaves.
        const APPLICATION_CELLS: usize = 5;
        let mut clone_exact = TypeWorkBudget::with_limit(APPLICATION_CELLS);
        let mut clone_short = TypeWorkBudget::with_limit(APPLICATION_CELLS - 1);
        assert_eq!(
            clone_type_with_budget(&application, &mut clone_exact),
            Ok(application.clone())
        );
        assert_eq!(
            clone_type_with_budget(&application, &mut clone_short),
            Err(())
        );

        let mut equality_exact = TypeWorkBudget::with_limit(APPLICATION_CELLS);
        let mut equality_short = TypeWorkBudget::with_limit(APPLICATION_CELLS - 1);
        assert_eq!(
            same_type_with_budget(&application, &application, &mut equality_exact),
            Ok(true)
        );
        assert_eq!(
            same_type_with_budget(&application, &application, &mut equality_short),
            Err(())
        );

        let mut hash_exact = TypeWorkBudget::with_limit(APPLICATION_CELLS);
        let mut hash_short = TypeWorkBudget::with_limit(APPLICATION_CELLS - 1);
        let mut exact_hasher = DefaultHasher::new();
        let mut short_hasher = DefaultHasher::new();
        assert_eq!(
            hash_type_with_budget(&application, &mut exact_hasher, &mut hash_exact),
            Ok(())
        );
        assert_eq!(
            hash_type_with_budget(&application, &mut short_hasher, &mut hash_short),
            Err(())
        );
        assert_ne!(exact_hasher.finish(), 0);

        let mut render_exact = TypeWorkBudget::with_limit(APPLICATION_CELLS);
        let mut render_short = TypeWorkBudget::with_limit(APPLICATION_CELLS - 1);
        assert_eq!(
            render_type_with_budget(&application, &mut render_exact),
            Ok(application.to_string())
        );
        assert_eq!(
            render_type_with_budget(&application, &mut render_short),
            Err(())
        );

        std::thread::Builder::new()
            .name("canonical-application-disposal".to_owned())
            .stack_size(256 * 1024)
            .spawn(move || {
                let mut deep = Type::Nominal(result);
                for _ in 0..32_768 {
                    deep = Type::Application(Box::new(deep), Box::new(Type::Unit));
                }
                discard_type_iteratively(deep);
            })
            .expect("deep-disposal thread should start")
            .join()
            .expect("canonical application disposal should remain within 256 KiB");
    }

    #[test]
    fn deep_application_operations_remain_bounded_on_a_small_stack() {
        const DEPTH: usize = 32_768;
        const CELLS: usize = 2 * DEPTH + 1;

        std::thread::Builder::new()
            .name("deep-canonical-application-operations".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let owner = NominalTypeId::new(ModuleId::new(0), 0);
                let mut application = Type::Nominal(owner);
                for _ in 0..DEPTH {
                    application = Type::Application(Box::new(application), Box::new(Type::Unit));
                }

                let cloned = application.clone();
                assert_eq!(&application, &cloned);

                let mut application_hasher = DefaultHasher::new();
                application.hash(&mut application_hasher);
                let mut clone_hasher = DefaultHasher::new();
                cloned.hash(&mut clone_hasher);
                assert_eq!(application_hasher.finish(), clone_hasher.finish());

                let rendered = application.to_string();
                assert!(rendered.starts_with(&format!("{}<Unit", Type::Nominal(owner))));
                assert!(rendered.ends_with('>'));
                assert_eq!(rendered.matches("Unit").count(), DEPTH);

                let mut clone_exact = TypeWorkBudget::with_limit(CELLS);
                let charged_clone = clone_type_with_budget(&application, &mut clone_exact)
                    .expect("the exact deep clone budget should succeed");
                let mut clone_short = TypeWorkBudget::with_limit(CELLS - 1);
                assert_eq!(
                    clone_type_with_budget(&application, &mut clone_short),
                    Err(())
                );

                let mut equality_exact = TypeWorkBudget::with_limit(CELLS);
                assert_eq!(
                    same_type_with_budget(&application, &cloned, &mut equality_exact),
                    Ok(true)
                );
                let mut equality_short = TypeWorkBudget::with_limit(CELLS - 1);
                assert_eq!(
                    same_type_with_budget(&application, &cloned, &mut equality_short),
                    Err(())
                );

                let mut hash_exact = TypeWorkBudget::with_limit(CELLS);
                let mut exact_hasher = DefaultHasher::new();
                assert_eq!(
                    hash_type_with_budget(&application, &mut exact_hasher, &mut hash_exact),
                    Ok(())
                );
                let mut hash_short = TypeWorkBudget::with_limit(CELLS - 1);
                let mut short_hasher = DefaultHasher::new();
                assert_eq!(
                    hash_type_with_budget(&application, &mut short_hasher, &mut hash_short),
                    Err(())
                );

                let mut render_exact = TypeWorkBudget::with_limit(CELLS);
                assert_eq!(
                    render_type_with_budget(&application, &mut render_exact),
                    Ok(rendered)
                );
                let mut render_short = TypeWorkBudget::with_limit(CELLS - 1);
                assert_eq!(
                    render_type_with_budget(&application, &mut render_short),
                    Err(())
                );

                discard_type_iteratively(charged_clone);
                discard_type_iteratively(cloned);
                discard_type_iteratively(application);
            })
            .expect("deep-operation thread should start")
            .join()
            .expect("deep canonical application operations should remain within 256 KiB");
    }

    #[test]
    fn retained_type_clones_charge_every_cell_before_rebuilding() {
        let ty = Type::Function(Box::new(Type::Unit), Box::new(Type::Bool));
        let mut exact = TypeWorkBudget {
            used: TYPE_WORK_LIMIT - 3,
            ..TypeWorkBudget::default()
        };
        let mut short = TypeWorkBudget {
            used: TYPE_WORK_LIMIT - 2,
            ..TypeWorkBudget::default()
        };

        assert_eq!(clone_type_with_budget(&ty, &mut exact), Ok(ty.clone()));
        assert_eq!(clone_type_with_budget(&ty, &mut short), Err(()));
    }

    #[test]
    fn charged_forall_equality_counts_binder_identities_exactly() {
        const WIDTH: usize = 16;
        const CELLS: usize = WIDTH + 2;
        let ty = Type::Forall(
            (0..WIDTH)
                .map(|index| TypeVariableId::new(u32::try_from(index).expect("identity fits")))
                .collect::<Vec<_>>()
                .into_boxed_slice(),
            Box::new(Type::Unit),
        );
        let mut exact = TypeWorkBudget::with_limit(CELLS);
        let mut short = TypeWorkBudget::with_limit(CELLS - 1);

        assert_eq!(same_type_with_budget(&ty, &ty, &mut exact), Ok(true));
        assert_eq!(same_type_with_budget(&ty, &ty, &mut short), Err(()));
    }

    #[test]
    fn application_substitution_rebuilds_function_and_argument_children() {
        let function = TypeVariableId::new(0);
        let argument = TypeVariableId::new(1);
        let owner = NominalTypeId::new(ModuleId::new(0), 0);
        let application = Type::Application(
            Box::new(Type::Variable(function)),
            Box::new(Type::Variable(argument)),
        );
        let replacements =
            HashMap::from([(function, Type::Nominal(owner)), (argument, Type::Bool)]);
        let mut exact = 3usize;
        let mut short = 2usize;

        let rebuilt = substitute_type_variables_with(&application, &replacements, |cells| {
            exact = exact.checked_sub(cells).ok_or(())?;
            Ok::<(), ()>(())
        })
        .expect("the exact rebuilt application should fit");
        assert_eq!(
            rebuilt,
            Type::Application(Box::new(Type::Nominal(owner)), Box::new(Type::Bool)),
        );
        assert_eq!(exact, 0);
        assert_eq!(
            substitute_type_variables_with(&application, &replacements, |cells| {
                short = short.checked_sub(cells).ok_or(())?;
                Ok::<(), ()>(())
            }),
            Err(()),
        );
    }

    #[test]
    fn declaration_identities_separate_modules_and_generated_variables() {
        let first_nominal = NominalTypeId::new(ModuleId::new(0), 0);
        let second_nominal = NominalTypeId::new(ModuleId::new(1), 0);
        let resolved = TypeVariableId::resolved(ModuleId::new(0), 0);
        let generated = TypeVariableId::generated(0);

        assert_ne!(first_nominal, second_nominal);
        assert_ne!(resolved, generated);
        assert_eq!(first_nominal.module(), ModuleId::new(0));
        assert_eq!(resolved.module(), Some(ModuleId::new(0)));
        assert_eq!(generated.module(), None);
    }

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
