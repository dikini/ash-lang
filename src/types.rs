//! Structural types shared by elaboration and Core.

use std::{
    collections::HashMap,
    fmt,
    hash::{Hash, Hasher},
};

use crate::module::ModuleId;

/// Shared base capacity for cumulative structural Type cells, Kind nodes, and
/// retained or visited binder-kind records.
///
/// Most compiler phases use this capacity directly. Independent Core
/// validation has an accepted validator-local multiplier because it
/// reauthenticates the complete Core program across several cumulative passes.
pub const TYPE_WORK_LIMIT: usize = 327_680;

/// Cumulative accounting for compiler-owned Type, Kind, and binder-kind work.
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
    pub(crate) const fn unbounded() -> Self {
        Self {
            used: 0,
            limit: usize::MAX,
        }
    }

    pub(crate) const fn with_limit(limit: usize) -> Self {
        Self { used: 0, limit }
    }

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
                charge_kinded_type_parameters(parameters, budget)?;
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

pub(crate) fn charge_kinded_type_parameters(
    parameters: &[(TypeVariableId, Kind)],
    budget: &mut TypeWorkBudget,
) -> Result<(), ()> {
    budget.charge(parameters.len())?;
    for (_, kind) in parameters {
        charge_kind_nodes(kind, budget)?;
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
        Forall(Box<[(TypeVariableId, Kind)]>),
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
    let mut unbounded = TypeWorkBudget::unbounded();
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
    Forall(Box<[(TypeVariableId, Kind)]>, Box<Type>),
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
                for (index, (parameter, kind)) in parameters.iter().enumerate() {
                    if index > 0 {
                        formatter.write_str(", ")?;
                    }
                    write!(formatter, "<type-variable:{}> : {kind}", parameter.local())?;
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
                if same_kinded_type_parameters(left_parameters, right_parameters) =>
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

fn same_kinded_type_parameters(
    left: &[(TypeVariableId, Kind)],
    right: &[(TypeVariableId, Kind)],
) -> bool {
    left.len() == right.len()
        && left
            .iter()
            .zip(right)
            .all(|((left_id, left_kind), (right_id, right_kind))| {
                left_id == right_id && same_kind(left_kind, right_kind)
            })
}

pub(crate) fn same_kinded_type_parameters_with_budget(
    left: &[(TypeVariableId, Kind)],
    right: &[(TypeVariableId, Kind)],
    budget: &mut TypeWorkBudget,
) -> Result<bool, ()> {
    same_kinded_type_parameters_with_charge(left, right, |work| budget.charge(work))
}

pub(crate) fn same_kinded_type_parameters_with_charge(
    left: &[(TypeVariableId, Kind)],
    right: &[(TypeVariableId, Kind)],
    mut charge: impl FnMut(usize) -> Result<(), ()>,
) -> Result<bool, ()> {
    if left.len() != right.len() {
        return Ok(false);
    }
    for ((left_id, left_kind), (right_id, right_kind)) in left.iter().zip(right) {
        charge(1)?;
        if left_id != right_id || !same_kind_with_charge(left_kind, right_kind, || charge(1))? {
            return Ok(false);
        }
    }
    Ok(true)
}

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
                if !same_kinded_type_parameters_with_budget(
                    left_parameters,
                    right_parameters,
                    budget,
                )? {
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
                for (_, kind) in parameters {
                    charge(1)?;
                    let mut kinds = vec![kind];
                    while let Some(kind) = kinds.pop() {
                        charge(1)?;
                        if let Kind::Arrow(domain, codomain) = kind {
                            kinds.push(codomain);
                            kinds.push(domain);
                        }
                    }
                }
                let substitute = substitute
                    && !parameters
                        .iter()
                        .any(|(parameter, _)| replacements.contains_key(parameter));
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
        FinishForall(Box<[(TypeVariableId, Kind)]>),
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
                        .any(|(parameter, _)| replacements.contains_key(parameter));
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
pub enum Kind {
    /// The kind of every source-admitted value type.
    Type,
    /// An internal unary type-constructor kind.
    Arrow(Box<Kind>, Box<Kind>),
}

#[cfg_attr(
    not(test),
    allow(
        dead_code,
        reason = "Task 4 tests close the budgeted multi-arrow fold; production uses single-arrow reconstruction until later Core and inference consumers need the fold"
    )
)]
pub(crate) fn arrows_with_budget(
    domains: impl IntoIterator<Item = Kind>,
    result: Kind,
    budget: &mut TypeWorkBudget,
) -> Result<Kind, ()> {
    charge_kind_nodes(&result, budget)?;
    let mut retained_domains = Vec::new();
    for domain in domains {
        charge_kind_nodes(&domain, budget)?;
        budget.charge(1)?;
        retained_domains.try_reserve(1).map_err(|_| ())?;
        retained_domains.push(domain);
    }

    Ok(retained_domains
        .into_iter()
        .rev()
        .fold(result, |codomain, domain| {
            Kind::Arrow(Box::new(domain), Box::new(codomain))
        }))
}

#[cfg(test)]
thread_local! {
    static KIND_NODE_CHARGE_VISITS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
    static KIND_RENDER_MAX_LIVE_STATES: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

#[cfg(test)]
pub(crate) fn reset_kind_node_charge_visits() {
    KIND_NODE_CHARGE_VISITS.set(0);
}

#[cfg(test)]
pub(crate) fn kind_node_charge_visits() -> usize {
    KIND_NODE_CHARGE_VISITS.get()
}

#[cfg(test)]
fn reset_kind_render_max_live_states() {
    KIND_RENDER_MAX_LIVE_STATES.set(0);
}

#[cfg(test)]
fn kind_render_max_live_states() -> usize {
    KIND_RENDER_MAX_LIVE_STATES.get()
}

#[cfg(test)]
fn observe_kind_render_live_states(states: usize) {
    KIND_RENDER_MAX_LIVE_STATES.set(KIND_RENDER_MAX_LIVE_STATES.get().max(states));
}

pub(crate) fn charge_kind_nodes(kind: &Kind, budget: &mut TypeWorkBudget) -> Result<(), ()> {
    charge_kind_with_charge(kind, || budget.charge(1))
}

pub(crate) fn charge_kind_with_charge(
    kind: &Kind,
    mut charge: impl FnMut() -> Result<(), ()>,
) -> Result<(), ()> {
    let mut work = vec![kind];
    while let Some(kind) = work.pop() {
        #[cfg(test)]
        KIND_NODE_CHARGE_VISITS.set(KIND_NODE_CHARGE_VISITS.get().saturating_add(1));
        charge()?;
        if let Kind::Arrow(domain, codomain) = kind {
            work.push(codomain);
            work.push(domain);
        }
    }
    Ok(())
}

/// Charges every Kind node below an already charged root.
pub(crate) fn charge_kind_descendants(kind: &Kind, budget: &mut TypeWorkBudget) -> Result<(), ()> {
    match kind {
        Kind::Type => Ok(()),
        Kind::Arrow(domain, codomain) => {
            charge_kind_nodes(domain, budget)?;
            charge_kind_nodes(codomain, budget)
        }
    }
}

pub(crate) fn clone_kind_with_budget(kind: &Kind, budget: &mut TypeWorkBudget) -> Result<Kind, ()> {
    enum Task<'a> {
        Visit(&'a Kind),
        Arrow,
    }

    charge_kind_nodes(kind, budget)?;
    let mut work = vec![Task::Visit(kind)];
    let mut rebuilt = Vec::new();
    while let Some(task) = work.pop() {
        match task {
            Task::Visit(Kind::Type) => rebuilt.push(Kind::Type),
            Task::Visit(Kind::Arrow(domain, codomain)) => {
                work.push(Task::Arrow);
                work.push(Task::Visit(codomain));
                work.push(Task::Visit(domain));
            }
            Task::Arrow => {
                let codomain = rebuilt.pop().expect("cloned kind codomain");
                let domain = rebuilt.pop().expect("cloned kind domain");
                rebuilt.push(Kind::Arrow(Box::new(domain), Box::new(codomain)));
            }
        }
    }
    rebuilt.pop().ok_or(())
}

pub(crate) fn clone_kinded_type_parameters_with_budget(
    parameters: &[(TypeVariableId, Kind)],
    budget: &mut TypeWorkBudget,
) -> Result<Vec<(TypeVariableId, Kind)>, ()> {
    budget.charge(parameters.len())?;
    let mut cloned = Vec::new();
    cloned.try_reserve(parameters.len()).map_err(|_| ())?;
    for (parameter, kind) in parameters {
        cloned.push((*parameter, clone_kind_with_budget(kind, budget)?));
    }
    Ok(cloned)
}

fn clone_kind(kind: &Kind) -> Kind {
    let mut unbounded = TypeWorkBudget::unbounded();
    match clone_kind_with_budget(kind, &mut unbounded) {
        Ok(cloned) => cloned,
        Err(()) => unreachable!("an in-memory kind cannot exceed the address-space work bound"),
    }
}

impl Clone for Kind {
    fn clone(&self) -> Self {
        clone_kind(self)
    }
}

fn same_kind(left: &Kind, right: &Kind) -> bool {
    let mut unbounded = TypeWorkBudget::unbounded();
    match same_kind_with_budget(left, right, &mut unbounded) {
        Ok(equal) => equal,
        Err(()) => {
            unreachable!("an in-memory kind comparison cannot exceed the address-space work bound")
        }
    }
}

pub(crate) fn same_kind_with_budget(
    left: &Kind,
    right: &Kind,
    budget: &mut TypeWorkBudget,
) -> Result<bool, ()> {
    same_kind_with_charge(left, right, || budget.charge(1))
}

pub(crate) fn same_kind_with_charge(
    left: &Kind,
    right: &Kind,
    mut charge: impl FnMut() -> Result<(), ()>,
) -> Result<bool, ()> {
    let mut work = vec![(left, right)];
    while let Some((left, right)) = work.pop() {
        charge()?;
        match (left, right) {
            (Kind::Type, Kind::Type) => {}
            (
                Kind::Arrow(left_domain, left_codomain),
                Kind::Arrow(right_domain, right_codomain),
            ) => {
                work.push((left_codomain, right_codomain));
                work.push((left_domain, right_domain));
            }
            _ => return Ok(false),
        }
    }
    Ok(true)
}

impl PartialEq for Kind {
    fn eq(&self, other: &Self) -> bool {
        same_kind(self, other)
    }
}

impl Eq for Kind {}

pub(crate) fn hash_kind_with_budget<H: Hasher>(
    kind: &Kind,
    state: &mut H,
    budget: &mut TypeWorkBudget,
) -> Result<(), ()> {
    charge_kind_nodes(kind, budget)?;
    let mut work = vec![kind];
    while let Some(kind) = work.pop() {
        match kind {
            Kind::Type => 0_u8.hash(state),
            Kind::Arrow(domain, codomain) => {
                1_u8.hash(state);
                work.push(codomain);
                work.push(domain);
            }
        }
    }
    Ok(())
}

impl Hash for Kind {
    fn hash<H: Hasher>(&self, state: &mut H) {
        let mut unbounded = TypeWorkBudget::unbounded();
        if hash_kind_with_budget(self, state, &mut unbounded).is_err() {
            unreachable!("an in-memory kind hash cannot exceed the address-space work bound");
        }
    }
}

fn write_kind(kind: &Kind, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
    #[derive(Clone, Copy)]
    enum Phase {
        Start,
        AfterDomain,
        AfterCodomain,
    }

    struct Task<'a> {
        kind: &'a Kind,
        phase: Phase,
        parenthesized: bool,
    }

    let mut work = Vec::new();
    work.try_reserve(1).map_err(|_| fmt::Error)?;
    work.push(Task {
        kind,
        phase: Phase::Start,
        parenthesized: false,
    });
    #[cfg(test)]
    observe_kind_render_live_states(work.len());
    while !work.is_empty() {
        let mut child = None;
        let mut finished = false;
        {
            let task = work.last_mut().expect("nonempty Kind render work");
            match task.kind {
                Kind::Type => {
                    formatter.write_str("Type")?;
                    finished = true;
                }
                Kind::Arrow(domain, codomain) => match task.phase {
                    Phase::Start => {
                        if task.parenthesized {
                            formatter.write_str("(")?;
                        }
                        task.phase = Phase::AfterDomain;
                        child = Some(Task {
                            kind: domain,
                            phase: Phase::Start,
                            parenthesized: matches!(domain.as_ref(), Kind::Arrow(_, _)),
                        });
                    }
                    Phase::AfterDomain => {
                        formatter.write_str(" -> ")?;
                        task.phase = Phase::AfterCodomain;
                        child = Some(Task {
                            kind: codomain,
                            phase: Phase::Start,
                            parenthesized: false,
                        });
                    }
                    Phase::AfterCodomain => {
                        if task.parenthesized {
                            formatter.write_str(")")?;
                        }
                        finished = true;
                    }
                },
            }
        }
        if finished {
            let _ = work.pop();
        } else if let Some(child) = child {
            work.try_reserve(1).map_err(|_| fmt::Error)?;
            work.push(child);
        } else {
            unreachable!("an unfinished Kind render task schedules one child");
        }
        #[cfg(test)]
        observe_kind_render_live_states(work.len());
    }
    Ok(())
}

pub(crate) fn render_kind_with_budget(
    kind: &Kind,
    budget: &mut TypeWorkBudget,
) -> Result<String, ()> {
    charge_kind_nodes(kind, budget)?;
    struct RenderedKind<'a>(&'a Kind);

    impl fmt::Display for RenderedKind<'_> {
        fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
            write_kind(self.0, formatter)
        }
    }

    Ok(format!("{}", RenderedKind(kind)))
}

impl fmt::Display for Kind {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut unbounded = TypeWorkBudget::unbounded();
        match render_kind_with_budget(self, &mut unbounded) {
            Ok(rendered) => formatter.write_str(&rendered),
            Err(()) => {
                unreachable!("an in-memory kind render cannot exceed the address-space work bound")
            }
        }
    }
}

impl fmt::Debug for Kind {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self, formatter)
    }
}

impl Drop for Kind {
    fn drop(&mut self) {
        let Self::Arrow(domain, codomain) = self else {
            return;
        };
        if matches!(domain.as_ref(), Self::Type) && matches!(codomain.as_ref(), Self::Type) {
            return;
        }

        let mut work = Vec::new();
        work.push(std::mem::replace(codomain.as_mut(), Self::Type));
        work.push(std::mem::replace(domain.as_mut(), Self::Type));
        while let Some(mut kind) = work.pop() {
            if let Self::Arrow(domain, codomain) = &mut kind {
                work.push(std::mem::replace(codomain.as_mut(), Self::Type));
                work.push(std::mem::replace(domain.as_mut(), Self::Type));
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::module::ModuleId;
    use std::{
        cell::Cell,
        collections::hash_map::DefaultHasher,
        hash::{Hash, Hasher},
    };

    #[test]
    fn arrow_folding_stops_domain_consumption_at_budget_failure() {
        let yielded = Cell::new(0);
        let domains = std::iter::from_fn(|| {
            let next = yielded.get() + 1;
            yielded.set(next);
            assert!(next <= 2, "the fold requested an unbudgeted third domain");
            Some(Kind::Type)
        });
        let mut budget = TypeWorkBudget::with_limit(4);

        assert_eq!(
            arrows_with_budget(domains, Kind::Type, &mut budget),
            Err(()),
        );
        assert_eq!(yielded.get(), 2);
        assert_eq!(budget.used(), 4);
    }

    #[test]
    fn kind_algebra_is_iterative_and_exactly_budgeted() {
        // Folding charges every retained input node plus one new Arrow per domain.
        // Here the inputs have five nodes and two domains retain two new arrows,
        // so the complete tree has three arrows and four Type leaves: seven nodes.
        const NODES: usize = 7;
        let mut fold_exact = TypeWorkBudget::with_limit(NODES);
        let kind = arrows_with_budget(
            [
                Kind::Arrow(Box::new(Kind::Type), Box::new(Kind::Type)),
                Kind::Type,
            ],
            Kind::Type,
            &mut fold_exact,
        )
        .expect("the exact arrow-fold budget should succeed");
        let mut fold_short = TypeWorkBudget::with_limit(NODES - 1);
        assert_eq!(
            arrows_with_budget(
                [
                    Kind::Arrow(Box::new(Kind::Type), Box::new(Kind::Type)),
                    Kind::Type,
                ],
                Kind::Type,
                &mut fold_short,
            ),
            Err(()),
        );
        assert_eq!(kind.to_string(), "(Type -> Type) -> Type -> Type");

        let mut clone_exact = TypeWorkBudget::with_limit(NODES);
        let cloned = clone_kind_with_budget(&kind, &mut clone_exact)
            .expect("the exact kind clone budget should succeed");
        let mut clone_short = TypeWorkBudget::with_limit(NODES - 1);
        assert_eq!(clone_kind_with_budget(&kind, &mut clone_short), Err(()));

        let mut equality_exact = TypeWorkBudget::with_limit(NODES);
        assert_eq!(
            same_kind_with_budget(&kind, &cloned, &mut equality_exact),
            Ok(true),
        );
        let mut equality_short = TypeWorkBudget::with_limit(NODES - 1);
        assert_eq!(
            same_kind_with_budget(&kind, &cloned, &mut equality_short),
            Err(()),
        );

        let mut hash_exact = TypeWorkBudget::with_limit(NODES);
        let mut exact_hasher = DefaultHasher::new();
        assert_eq!(
            hash_kind_with_budget(&kind, &mut exact_hasher, &mut hash_exact),
            Ok(()),
        );
        let mut hash_short = TypeWorkBudget::with_limit(NODES - 1);
        let mut short_hasher = DefaultHasher::new();
        17_u8.hash(&mut short_hasher);
        let mut untouched_hasher = DefaultHasher::new();
        17_u8.hash(&mut untouched_hasher);
        assert_eq!(
            hash_kind_with_budget(&kind, &mut short_hasher, &mut hash_short),
            Err(()),
        );
        assert_eq!(short_hasher.finish(), untouched_hasher.finish());
        let mut ordinary_hasher = DefaultHasher::new();
        kind.hash(&mut ordinary_hasher);
        assert_eq!(exact_hasher.finish(), ordinary_hasher.finish());

        let mut render_exact = TypeWorkBudget::with_limit(NODES);
        assert_eq!(
            render_kind_with_budget(&kind, &mut render_exact),
            Ok("(Type -> Type) -> Type -> Type".to_owned()),
        );
        let mut render_short = TypeWorkBudget::with_limit(NODES - 1);
        assert_eq!(render_kind_with_budget(&kind, &mut render_short), Err(()),);

        let right_associated = Kind::Arrow(
            Box::new(Kind::Type),
            Box::new(Kind::Arrow(Box::new(Kind::Type), Box::new(Kind::Type))),
        );
        assert_eq!(right_associated.to_string(), "Type -> Type -> Type");
        assert_ne!(kind, right_associated);

        drop(right_associated);
        drop(cloned);
        drop(kind);
    }

    #[test]
    fn deep_kind_operations_and_destruction_are_stack_safe() {
        const DEPTH: usize = 32_768;
        const NODES: usize = 2 * DEPTH + 1;

        std::thread::Builder::new()
            .name("deep-kind-operations".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let mut kind = Kind::Type;
                for _ in 0..DEPTH {
                    kind = Kind::Arrow(Box::new(Kind::Type), Box::new(kind));
                }

                let cloned = kind.clone();
                assert_eq!(&kind, &cloned);

                let mut kind_hasher = DefaultHasher::new();
                kind.hash(&mut kind_hasher);
                let mut clone_hasher = DefaultHasher::new();
                cloned.hash(&mut clone_hasher);
                assert_eq!(kind_hasher.finish(), clone_hasher.finish());

                let rendered = kind.to_string();
                assert!(rendered.starts_with("Type -> Type"));
                assert!(rendered.ends_with("Type"));
                assert_eq!(rendered.matches("Type").count(), DEPTH + 1);

                let mut clone_exact = TypeWorkBudget::with_limit(NODES);
                let charged_clone = clone_kind_with_budget(&kind, &mut clone_exact)
                    .expect("the exact deep kind clone budget should succeed");
                let mut clone_short = TypeWorkBudget::with_limit(NODES - 1);
                assert_eq!(clone_kind_with_budget(&kind, &mut clone_short), Err(()));

                let mut equality_exact = TypeWorkBudget::with_limit(NODES);
                assert_eq!(
                    same_kind_with_budget(&kind, &cloned, &mut equality_exact),
                    Ok(true),
                );
                let mut equality_short = TypeWorkBudget::with_limit(NODES - 1);
                assert_eq!(
                    same_kind_with_budget(&kind, &cloned, &mut equality_short),
                    Err(()),
                );

                let mut hash_exact = TypeWorkBudget::with_limit(NODES);
                let mut exact_hasher = DefaultHasher::new();
                assert_eq!(
                    hash_kind_with_budget(&kind, &mut exact_hasher, &mut hash_exact),
                    Ok(()),
                );
                let mut hash_short = TypeWorkBudget::with_limit(NODES - 1);
                let mut short_hasher = DefaultHasher::new();
                assert_eq!(
                    hash_kind_with_budget(&kind, &mut short_hasher, &mut hash_short),
                    Err(()),
                );

                let mut render_exact = TypeWorkBudget::with_limit(NODES);
                assert_eq!(
                    render_kind_with_budget(&kind, &mut render_exact),
                    Ok(rendered),
                );
                let mut render_short = TypeWorkBudget::with_limit(NODES - 1);
                assert_eq!(render_kind_with_budget(&kind, &mut render_short), Err(()),);

                // Ordinary accepted values and the rejected clone's partial state all
                // dismantle through the same bounded automatic owner path.
                drop(charged_clone);
                drop(cloned);
                drop(kind);
            })
            .expect("deep-kind thread should start")
            .join()
            .expect("deep kind operations should remain within 256 KiB");
    }

    #[test]
    fn kind_rendering_states_are_one_per_node_and_exact() {
        const DEPTH: usize = 32_768;
        const NODES: usize = 2 * DEPTH + 1;

        let parenthesized = Kind::Arrow(
            Box::new(Kind::Arrow(Box::new(Kind::Type), Box::new(Kind::Type))),
            Box::new(Kind::Type),
        );
        reset_kind_render_max_live_states();
        let mut exact = TypeWorkBudget::with_limit(5);
        assert_eq!(
            render_kind_with_budget(&parenthesized, &mut exact),
            Ok("(Type -> Type) -> Type".to_owned())
        );
        assert!(kind_render_max_live_states() <= 5);
        let mut short = TypeWorkBudget::with_limit(4);
        assert_eq!(render_kind_with_budget(&parenthesized, &mut short), Err(()));

        std::thread::Builder::new()
            .name("deep-left-kind-render".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let mut kind = Kind::Type;
                for _ in 0..DEPTH {
                    kind = Kind::Arrow(Box::new(kind), Box::new(Kind::Type));
                }
                reset_kind_render_max_live_states();
                let mut exact = TypeWorkBudget::with_limit(NODES);
                let rendered = render_kind_with_budget(&kind, &mut exact)
                    .expect("the exact left-nested Kind-node budget should render");
                assert_eq!(exact.used(), NODES);
                assert_eq!(rendered.matches("Type").count(), DEPTH + 1);
                assert!(
                    kind_render_max_live_states() <= NODES,
                    "rendering retained {} states for {NODES} Kind nodes",
                    kind_render_max_live_states(),
                );
                let mut short = TypeWorkBudget::with_limit(NODES - 1);
                assert_eq!(render_kind_with_budget(&kind, &mut short), Err(()));
                drop(kind);
            })
            .expect("the deep left-render thread should start")
            .join()
            .expect("deep left rendering and teardown should fit 256 KiB");
    }

    #[test]
    fn deep_wide_arrow_folding_is_exact_transactional_and_stack_safe() {
        const DOMAINS: usize = 32_768;
        const DOMAIN_DEPTH: usize = 32_768;
        // Result Type + (DOMAINS-1) simple domains + the 2D+1-node deep
        // domain + one Arrow per domain.
        const EXACT_NODES: usize = 2 * DOMAINS + 2 * DOMAIN_DEPTH + 1;

        std::thread::Builder::new()
            .name("deep-wide-kind-arrow-fold".into())
            .stack_size(256 * 1024)
            .spawn(|| {
                let make_deep_domain = || {
                    let mut kind = Kind::Type;
                    for _ in 0..DOMAIN_DEPTH {
                        kind = Kind::Arrow(Box::new(Kind::Type), Box::new(kind));
                    }
                    kind
                };

                let mut exact = TypeWorkBudget::with_limit(EXACT_NODES);
                let folded = arrows_with_budget(
                    (0..DOMAINS).map(|index| {
                        if index + 1 == DOMAINS {
                            make_deep_domain()
                        } else {
                            Kind::Type
                        }
                    }),
                    Kind::Type,
                    &mut exact,
                )
                .expect("the published deep/wide arrow formula should fit exactly");
                assert_eq!(exact.used(), EXACT_NODES);

                let yielded = Cell::new(0);
                let late_domains = std::iter::from_fn(|| {
                    let next = yielded.get() + 1;
                    yielded.set(next);
                    assert!(
                        next <= DOMAINS,
                        "late failure requested a domain beyond the charged fold"
                    );
                    Some(if next == DOMAINS {
                        make_deep_domain()
                    } else {
                        Kind::Type
                    })
                });
                let mut short = TypeWorkBudget::with_limit(EXACT_NODES - 1);
                assert_eq!(
                    arrows_with_budget(late_domains, Kind::Type, &mut short),
                    Err(())
                );
                assert_eq!(short.used(), EXACT_NODES - 1);
                assert_eq!(yielded.get(), DOMAINS);
                drop(folded);
            })
            .expect("the deep/wide fold thread should start")
            .join()
            .expect("fold success, late failure, and teardown must fit 256 KiB");
    }

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
    fn charged_forall_equality_counts_binder_records_and_kinds_exactly() {
        const WIDTH: usize = 16;
        const CELLS: usize = 2 * WIDTH + 2;
        let ty = Type::Forall(
            (0..WIDTH)
                .map(|index| {
                    (
                        TypeVariableId::new(u32::try_from(index).expect("identity fits")),
                        Kind::Type,
                    )
                })
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
    fn kinded_forall_operations_charge_records_and_kind_nodes_exactly() {
        // One Forall node + two binder records + one Type node + three Arrow
        // kind nodes + one body node.
        const CELLS: usize = 1 + 2 + 1 + 3 + 1;
        let first = TypeVariableId::new(0);
        let second = TypeVariableId::new(1);
        let ty = Type::Forall(
            vec![
                (first, Kind::Type),
                (
                    second,
                    Kind::Arrow(Box::new(Kind::Type), Box::new(Kind::Type)),
                ),
            ]
            .into_boxed_slice(),
            Box::new(Type::Variable(first)),
        );

        let mut clone_exact = TypeWorkBudget::with_limit(CELLS);
        let cloned = clone_type_with_budget(&ty, &mut clone_exact)
            .expect("the complete scheme budget should retain every pair");
        assert_eq!(cloned, ty);
        let mut clone_short = TypeWorkBudget::with_limit(CELLS - 1);
        assert_eq!(clone_type_with_budget(&ty, &mut clone_short), Err(()));

        let mut equality_exact = TypeWorkBudget::with_limit(CELLS);
        assert_eq!(
            same_type_with_budget(&ty, &ty, &mut equality_exact),
            Ok(true)
        );
        let mut equality_short = TypeWorkBudget::with_limit(CELLS - 1);
        assert_eq!(
            same_type_with_budget(&ty, &ty, &mut equality_short),
            Err(())
        );

        discard_type_iteratively(cloned);
        discard_type_iteratively(ty);
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
