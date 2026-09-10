//! Structural types shared by elaboration and Core.

use std::{
    cmp::Ordering,
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

    pub(crate) const fn remaining(&self) -> usize {
        self.limit - self.used
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

pub(crate) trait TypeWorkMeter {
    type Error;
    fn charge(&mut self, cells: usize) -> Result<(), Self::Error>;
}

impl TypeWorkMeter for TypeWorkBudget {
    type Error = ();
    fn charge(&mut self, cells: usize) -> Result<(), ()> {
        Self::charge(self, cells)
    }
}

impl<E, F: FnMut(usize) -> Result<(), E>> TypeWorkMeter for F {
    type Error = E;
    fn charge(&mut self, cells: usize) -> Result<(), E> {
        self(cells)
    }
}

fn allocation_error<B: TypeWorkMeter>(budget: &mut B) -> B::Error {
    budget.charge(usize::MAX).expect_err("allocation failure")
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum RowReservationSite {
    CloneMembers,
    CloneArguments,
    CloneLacks,
    RebuildArguments,
    RebuildRetained,
    RebuildMembers,
    RebuildLacks,
    CanonicalMembers,
    ComparisonWork,
}

fn reserve_row<T>(
    storage: &mut Vec<T>,
    additional: usize,
    _site: RowReservationSite,
) -> Result<(), std::collections::TryReserveError> {
    #[cfg(test)]
    let additional = row_reservation_fault::request(_site, additional);
    storage.try_reserve(additional)
}

#[cfg(test)]
pub(crate) mod row_reservation_fault {
    use super::RowReservationSite;
    use std::cell::Cell;

    #[derive(Clone, Copy, Default)]
    struct State {
        site: Option<RowReservationSite>,
        skip: usize,
        failed: bool,
        hits: usize,
    }

    thread_local! { static STATE: Cell<State> = const { Cell::new(State {site: None, skip: 0, failed: false, hits: 0}) }; }

    pub(crate) struct Guard(State);
    pub(crate) fn fail(site: RowReservationSite, skip: usize) -> Guard {
        Guard(STATE.replace(State {
            site: Some(site),
            skip,
            ..State::default()
        }))
    }
    impl Drop for Guard {
        fn drop(&mut self) {
            STATE.set(self.0);
        }
    }
    pub(crate) fn hits() -> usize {
        STATE.get().hits
    }
    pub(super) fn request(site: RowReservationSite, additional: usize) -> usize {
        let mut state = STATE.get();
        let mut requested = additional;
        if state.site == Some(site) {
            state.hits += 1;
            if state.skip > 0 {
                state.skip -= 1;
            } else if !state.failed {
                state.failed = true;
                // A real TryReserveError, without requesting physical memory.
                requested = usize::MAX;
            }
            STATE.set(state);
        }
        requested
    }
}
pub(crate) fn charge_type_cells<B: TypeWorkMeter>(
    ty: &Type,
    budget: &mut B,
) -> Result<(), B::Error> {
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
            Type::EffectfulFunction(domain, codomain) => {
                budget.charge(1)?;
                budget.charge(1)?;
                for instance in &codomain.effects.known {
                    budget.charge(1)?;
                    work.push(Task::Sequence(instance.arguments.iter()));
                }
                if let Some(tail) = &codomain.effects.tail {
                    budget.charge(1)?;
                    for instance in &tail.lacks {
                        budget.charge(1)?;
                        work.push(Task::Sequence(instance.arguments.iter()));
                    }
                }
                work.push(Task::Visit(&codomain.value));
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

pub(crate) fn charge_effect_row_cells<B: TypeWorkMeter>(
    row: &EffectRow,
    budget: &mut B,
) -> Result<(), B::Error> {
    budget.charge(1)?;
    for instance in &row.known {
        budget.charge(1)?;
        for argument in &instance.arguments {
            charge_type_cells(argument, budget)?;
        }
    }
    if let Some(tail) = &row.tail {
        budget.charge(1)?;
        for instance in &tail.lacks {
            budget.charge(1)?;
            for argument in &instance.arguments {
                charge_type_cells(argument, budget)?;
            }
        }
    }
    Ok(())
}

pub(crate) fn clone_effect_row_with_budget<B: TypeWorkMeter>(
    row: &EffectRow,
    budget: &mut B,
) -> Result<EffectRow, B::Error> {
    charge_effect_row_cells(row, budget)?;
    Ok(clone_effect_row(row))
}

fn clone_effect_row(row: &EffectRow) -> EffectRow {
    clone_effect_row_with_failure(row, || ()).expect("an in-memory row can reserve its clone")
}

pub(crate) fn clone_effect_row_with_budget_and_failure<B: TypeWorkMeter>(
    row: &EffectRow,
    budget: &mut B,
    mut storage_error: impl FnMut(&mut B) -> B::Error,
) -> Result<EffectRow, B::Error> {
    charge_effect_row_cells(row, budget)?;
    clone_effect_row_with_failure(row, || storage_error(budget))
}

fn clone_effect_row_with_failure<E>(
    row: &EffectRow,
    mut storage_error: impl FnMut() -> E,
) -> Result<EffectRow, E> {
    fn clone_instance<E>(
        instance: &EffectInstance,
        storage_error: &mut impl FnMut() -> E,
    ) -> Result<EffectInstance, E> {
        let mut arguments = Vec::new();
        reserve_row(
            &mut arguments,
            instance.arguments.len(),
            RowReservationSite::CloneArguments,
        )
        .map_err(|_| storage_error())?;
        for argument in &instance.arguments {
            arguments.push(clone_type(argument));
        }
        Ok(EffectInstance::new(
            instance.effect,
            arguments.into_boxed_slice(),
        ))
    }
    let mut known = Vec::new();
    reserve_row(
        &mut known,
        row.known.len(),
        RowReservationSite::CloneMembers,
    )
    .map_err(|_| storage_error())?;
    for instance in &row.known {
        known.push(clone_instance(instance, &mut storage_error)?);
    }
    let tail = if let Some(tail) = &row.tail {
        let mut lacks = Vec::new();
        reserve_row(&mut lacks, tail.lacks.len(), RowReservationSite::CloneLacks)
            .map_err(|_| storage_error())?;
        for instance in &tail.lacks {
            lacks.push(clone_instance(instance, &mut storage_error)?);
        }
        Some(EffectRowTail {
            variable: tail.variable,
            lacks: lacks.into_boxed_slice(),
        })
    } else {
        None
    };
    Ok(EffectRow {
        known: known.into_boxed_slice(),
        tail,
    })
}

#[allow(
    dead_code,
    reason = "the effect syntax and checked-summary steps consume this charged clone seam"
)]
pub(crate) fn clone_computation_type_with_budget(
    computation: &ComputationType,
    budget: &mut TypeWorkBudget,
) -> Result<ComputationType, ()> {
    budget.charge(1)?;
    Ok(ComputationType::new(
        clone_type_with_budget(&computation.value, budget)?,
        clone_effect_row_with_budget(&computation.effects, budget)?,
    ))
}

pub(crate) fn charge_kinded_type_parameters<B: TypeWorkMeter>(
    parameters: &[(TypeVariableId, Kind)],
    budget: &mut B,
) -> Result<(), B::Error> {
    budget.charge(parameters.len())?;
    for (_, kind) in parameters {
        charge_kind_nodes(kind, budget)?;
    }
    Ok(())
}

#[allow(
    clippy::type_complexity,
    reason = "the local traversal shape mirrors the effect-row carrier without a public alias"
)]
pub(crate) fn clone_type_with_budget<B: TypeWorkMeter>(
    ty: &Type,
    budget: &mut B,
) -> Result<Type, B::Error> {
    struct RowShape {
        known: Box<[(EffectId, usize)]>,
        tail: Option<(EffectRowVariable, Box<[(EffectId, usize)]>)>,
        argument_count: usize,
    }

    enum Task<'a> {
        Visit(&'a Type),
        Sequence(std::slice::Iter<'a, Type>),
        Tuple(usize),
        Application,
        Function,
        EffectfulFunction(RowShape),
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
            Task::Visit(Type::EffectfulFunction(domain, codomain)) => {
                let known = codomain
                    .effects
                    .known
                    .iter()
                    .map(|instance| (instance.effect, instance.arguments.len()))
                    .collect::<Vec<_>>()
                    .into_boxed_slice();
                let tail = codomain.effects.tail.as_ref().map(|tail| {
                    (
                        tail.variable,
                        tail.lacks
                            .iter()
                            .map(|instance| (instance.effect, instance.arguments.len()))
                            .collect::<Vec<_>>()
                            .into_boxed_slice(),
                    )
                });
                let arguments = codomain
                    .effects
                    .known
                    .iter()
                    .chain(
                        codomain
                            .effects
                            .tail
                            .iter()
                            .flat_map(|tail| tail.lacks.iter()),
                    )
                    .flat_map(|instance| instance.arguments.iter())
                    .collect::<Vec<_>>();
                let shape = RowShape {
                    known,
                    tail,
                    argument_count: arguments.len(),
                };
                work.push(Task::EffectfulFunction(shape));
                for argument in arguments.into_iter().rev() {
                    work.push(Task::Visit(argument));
                }
                work.push(Task::Visit(&codomain.value));
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
                rebuilt.push(Type::function(domain, codomain));
            }
            Task::EffectfulFunction(shape) => {
                let arguments = rebuilt.split_off(rebuilt.len() - shape.argument_count);
                let mut arguments = arguments.into_iter();
                let rebuild_instances =
                    |instances: Box<[(EffectId, usize)]>,
                     arguments: &mut std::vec::IntoIter<Type>| {
                        instances
                            .into_vec()
                            .into_iter()
                            .map(|(effect, count)| {
                                EffectInstance::new(
                                    effect,
                                    arguments
                                        .by_ref()
                                        .take(count)
                                        .collect::<Vec<_>>()
                                        .into_boxed_slice(),
                                )
                            })
                            .collect::<Vec<_>>()
                            .into_boxed_slice()
                    };
                let known = rebuild_instances(shape.known, &mut arguments);
                let tail = shape.tail.map(|(variable, lacks)| EffectRowTail {
                    variable,
                    lacks: rebuild_instances(lacks, &mut arguments),
                });
                debug_assert!(arguments.next().is_none());
                let effects = EffectRow { known, tail };
                let codomain = rebuilt.pop().expect("cloned function codomain");
                let domain = rebuilt.pop().expect("cloned function domain");
                rebuilt.push(Type::function_computation(
                    domain,
                    ComputationType::new(codomain, effects),
                ));
            }
            Task::Forall(parameters) => {
                let body = rebuilt.pop().expect("cloned scheme body");
                rebuilt.push(Type::Forall(parameters, Box::new(body)));
            }
        }
    }
    Ok(rebuilt.pop().expect("one cloned type"))
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
/// Module declarations and lexical declarations use distinct owner classes.
/// The declaration coordinate is stable within the same canonical module.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct NominalTypeId {
    module: ModuleId,
    owner: NominalOwner,
    declaration: u32,
}

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum NominalOwner {
    Module,
    Lexical,
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

/// Stable identity of one effect declaration.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct EffectId {
    module: ModuleId,
    declaration: u32,
}

impl EffectId {
    /// Creates the identity for one source-order effect declaration.
    #[must_use]
    pub const fn new(module: ModuleId, declaration: u32) -> Self {
        Self {
            module,
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

/// Stable identity of one operation within an effect declaration.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct OperationId {
    owner: EffectId,
    operation: u32,
}

impl OperationId {
    /// Creates one source-order operation identity.
    #[must_use]
    pub const fn new(owner: EffectId, operation: u32) -> Self {
        Self { owner, operation }
    }

    /// Returns the effect declaration that owns this operation.
    #[must_use]
    pub const fn owner(self) -> EffectId {
        self.owner
    }

    /// Returns the source-order index within the owning effect.
    #[must_use]
    pub const fn operation(self) -> u32 {
        self.operation
    }
}

/// A rigid or inference variable used only as an effect-row tail.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum EffectRowVariable {
    /// A source or generalized rank-1 binder of kind [`Kind::EffectRow`].
    Rigid(TypeVariableId),
    /// An elaborator inference variable registered at [`Kind::EffectRow`].
    Inference(InferenceVariableId),
}

impl EffectRowVariable {
    /// Creates a rigid row-tail occurrence.
    #[must_use]
    pub const fn rigid(identity: TypeVariableId) -> Self {
        Self::Rigid(identity)
    }

    /// Creates an inference row-tail occurrence.
    #[must_use]
    pub const fn inference(identity: InferenceVariableId) -> Self {
        Self::Inference(identity)
    }
}

/// One exact effect application in a computation row.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct EffectInstance {
    effect: EffectId,
    arguments: Box<[Type]>,
}

impl EffectInstance {
    /// Creates one exact effect instance from its stable identity and arguments.
    #[must_use]
    pub const fn new(effect: EffectId, arguments: Box<[Type]>) -> Self {
        Self { effect, arguments }
    }

    /// Returns the stable effect declaration identity.
    #[must_use]
    pub const fn effect(&self) -> EffectId {
        self.effect
    }

    /// Borrows the complete ordered type arguments.
    #[must_use]
    pub const fn arguments(&self) -> &[Type] {
        &self.arguments
    }

    pub(crate) fn into_parts(mut self) -> (EffectId, Box<[Type]>) {
        (self.effect, std::mem::take(&mut self.arguments))
    }
}

impl Drop for EffectInstance {
    fn drop(&mut self) {
        for argument in std::mem::take(&mut self.arguments).into_vec() {
            discard_type_iteratively(argument);
        }
    }
}

pub(crate) fn clone_effect_instance_with_budget(
    instance: &EffectInstance,
    budget: &mut TypeWorkBudget,
) -> Result<EffectInstance, ()> {
    budget.charge(instance.arguments().len())?;
    let mut arguments = Vec::new();
    arguments
        .try_reserve_exact(instance.arguments().len())
        .map_err(|_| ())?;
    for argument in instance.arguments() {
        arguments.push(IterativeTypeOwner::new(clone_type_with_budget(
            argument, budget,
        )?));
    }
    budget.charge(instance.arguments().len())?;
    let mut retained = Vec::new();
    retained
        .try_reserve_exact(instance.arguments().len())
        .map_err(|_| ())?;
    retained.extend(arguments.into_iter().map(IterativeTypeOwner::into_inner));
    Ok(EffectInstance::new(
        instance.effect(),
        retained.into_boxed_slice(),
    ))
}

/// One effect-row tail and the exact instances known absent from it.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct EffectRowTail {
    variable: EffectRowVariable,
    lacks: Box<[EffectInstance]>,
}

impl EffectRowTail {
    /// Returns the rigid or inference row variable.
    #[must_use]
    pub const fn variable(&self) -> EffectRowVariable {
        self.variable
    }

    /// Borrows the canonical exact instances known absent from the variable.
    #[must_use]
    pub const fn lacks(&self) -> &[EffectInstance] {
        &self.lacks
    }
}

/// A canonical unordered set of exact effect instances with at most one tail.
#[derive(Debug, Default)]
pub struct EffectRow {
    known: Box<[EffectInstance]>,
    tail: Option<EffectRowTail>,
}

/// A bounded effect-row algebra failure.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum EffectRowError {
    /// The operation would strengthen or equate unrelated open tails.
    Ambiguous,
    /// Exact removal proved that the requested instance is absent.
    Missing,
    /// A row-tail substitution would make the tail contain itself.
    Infinite,
}

impl EffectRow {
    /// Returns the closed empty effect row.
    #[must_use]
    pub fn empty() -> Self {
        Self {
            known: Box::new([]),
            tail: None,
        }
    }

    /// Returns a closed singleton row.
    #[must_use]
    pub fn singleton(instance: EffectInstance) -> Self {
        Self {
            known: Box::new([instance]),
            tail: None,
        }
    }

    /// Returns a canonical open row with no known members.
    #[must_use]
    pub fn open(variable: EffectRowVariable, lacks: Box<[EffectInstance]>) -> Self {
        Self::with_tail(Box::new([]), variable, lacks)
    }

    /// Returns a canonical open row and preserves all supplied lacks facts.
    #[must_use]
    pub fn with_tail(
        known: Box<[EffectInstance]>,
        variable: EffectRowVariable,
        lacks: Box<[EffectInstance]>,
    ) -> Self {
        let known = canonical_instances(known.into_vec()).into_boxed_slice();
        let mut lacks = lacks.into_vec();
        lacks.extend(known.iter().cloned());
        let lacks = canonical_instances(lacks).into_boxed_slice();
        Self {
            known,
            tail: Some(EffectRowTail { variable, lacks }),
        }
    }

    /// Returns a canonical closed row, coalescing repeated inferred members.
    #[must_use]
    pub fn closed(known: Box<[EffectInstance]>) -> Self {
        Self {
            known: canonical_instances(known.into_vec()).into_boxed_slice(),
            tail: None,
        }
    }

    /// Borrows the canonical known members.
    #[must_use]
    pub const fn known(&self) -> &[EffectInstance] {
        &self.known
    }

    /// Borrows the optional open tail.
    #[must_use]
    pub const fn tail(&self) -> Option<&EffectRowTail> {
        self.tail.as_ref()
    }

    #[allow(
        clippy::type_complexity,
        reason = "the pair is the direct owned form of the row's known members and optional tail"
    )]
    pub(crate) fn into_parts(
        mut self,
    ) -> (
        Box<[EffectInstance]>,
        Option<(EffectRowVariable, Box<[EffectInstance]>)>,
    ) {
        let known = std::mem::take(&mut self.known);
        let tail = self.tail.take().map(|tail| (tail.variable, tail.lacks));
        (known, tail)
    }

    /// Reports whether this row is closed and has no known members.
    #[must_use]
    pub const fn is_empty(&self) -> bool {
        self.known.is_empty() && self.tail.is_none()
    }

    /// Computes the least principal union admitted by the one-tail kernel.
    pub fn union(&self, other: &Self) -> Result<Self, EffectRowError> {
        let mut budget = TypeWorkBudget::unbounded();
        match self.union_with_budget(other, &mut budget) {
            Ok(result) => result,
            Err(()) => unreachable!("an in-memory row cannot exceed the address-space work bound"),
        }
    }

    pub(crate) fn union_with_budget(
        &self,
        other: &Self,
        budget: &mut TypeWorkBudget,
    ) -> Result<Result<Self, EffectRowError>, ()> {
        match (&self.tail, &other.tail) {
            (Some(left), Some(right)) if left.variable != right.variable => {
                return Ok(Err(EffectRowError::Ambiguous));
            }
            _ => {}
        }

        if let Some(tail) = &self.tail {
            for instance in &other.known {
                if contains_instance_with_budget(&self.known, instance, budget)? {
                    continue;
                }
                let admitted_by_shared_tail = if let Some(other_tail) = &other.tail {
                    other_tail.variable == tail.variable
                        && contains_instance_with_budget(&other_tail.lacks, instance, budget)?
                } else {
                    false
                };
                if !contains_instance_with_budget(&tail.lacks, instance, budget)?
                    && !admitted_by_shared_tail
                {
                    return Ok(Err(EffectRowError::Ambiguous));
                }
            }
        }
        if let Some(tail) = &other.tail {
            for instance in &self.known {
                if contains_instance_with_budget(&other.known, instance, budget)? {
                    continue;
                }
                let admitted_by_shared_tail = if let Some(self_tail) = &self.tail {
                    self_tail.variable == tail.variable
                        && contains_instance_with_budget(&self_tail.lacks, instance, budget)?
                } else {
                    false
                };
                if !contains_instance_with_budget(&tail.lacks, instance, budget)?
                    && !admitted_by_shared_tail
                {
                    return Ok(Err(EffectRowError::Ambiguous));
                }
            }
        }

        let known = self.known.iter().chain(other.known.iter());
        let rebuilt = match (&self.tail, &other.tail) {
            (None, None) => rebuild_effect_row_with_budget(
                known,
                None,
                std::iter::empty(),
                clone_type_with_budget,
                budget,
            )?,
            (Some(tail), None) | (None, Some(tail)) => rebuild_effect_row_with_budget(
                known,
                Some(tail.variable),
                tail.lacks.iter(),
                clone_type_with_budget,
                budget,
            )?,
            (Some(left), Some(right)) => rebuild_effect_row_with_budget(
                known,
                Some(left.variable),
                left.lacks.iter().chain(right.lacks.iter()),
                clone_type_with_budget,
                budget,
            )?,
        };
        Ok(Ok(rebuilt))
    }

    /// Removes one exact member without masking another instance of the API.
    pub fn remove_exact(&self, target: &EffectInstance) -> Result<Self, EffectRowError> {
        let mut budget = TypeWorkBudget::unbounded();
        match self.remove_exact_with_budget(target, &mut budget) {
            Ok(result) => result,
            Err(()) => unreachable!("an in-memory row cannot exceed the address-space work bound"),
        }
    }

    pub(crate) fn remove_exact_with_budget(
        &self,
        target: &EffectInstance,
        budget: &mut TypeWorkBudget,
    ) -> Result<Result<Self, EffectRowError>, ()> {
        if let Some(index) = find_instance_index_with_budget(&self.known, target, budget)? {
            return rebuild_effect_row_with_budget(
                self.known[..index]
                    .iter()
                    .chain(self.known[index + 1..].iter()),
                self.tail.as_ref().map(|tail| tail.variable),
                self.tail.iter().flat_map(|tail| tail.lacks.iter()),
                clone_type_with_budget,
                budget,
            )
            .map(Ok);
        }
        match &self.tail {
            Some(tail) if !contains_instance_with_budget(&tail.lacks, target, budget)? => {
                Ok(Err(EffectRowError::Ambiguous))
            }
            _ => Ok(Err(EffectRowError::Missing)),
        }
    }

    /// Applies capture-free ordinary type substitution to every exact instance.
    ///
    /// Row tails remain row variables; their own substitution is performed by
    /// the elaborator's fixed-kind row transaction.
    #[must_use]
    pub fn substitute_type_variables(&self, replacements: &HashMap<TypeVariableId, Type>) -> Self {
        let mut budget = TypeWorkBudget::unbounded();
        self.substitute_type_variables_with_budget(replacements, &mut budget)
            .expect("an in-memory row cannot exceed the address-space work bound")
    }

    pub(crate) fn substitute_type_variables_with_budget(
        &self,
        replacements: &HashMap<TypeVariableId, Type>,
        budget: &mut TypeWorkBudget,
    ) -> Result<Self, ()> {
        rebuild_effect_row_with_budget(
            self.known.iter(),
            self.tail.as_ref().map(|tail| tail.variable),
            self.tail.iter().flat_map(|tail| tail.lacks.iter()),
            |argument, budget| {
                substitute_type_variables_with(
                    argument,
                    replacements,
                    |cells| budget.charge(cells),
                    || (),
                )
            },
            budget,
        )
    }

    pub(crate) fn substitute_tail_once_with_budget<B: TypeWorkMeter>(
        &self,
        target: EffectRowVariable,
        replacement: &Self,
        budget: &mut B,
    ) -> Result<Result<Self, EffectRowError>, B::Error> {
        self.substitute_tail_once_with_budget_and_failure(
            target,
            replacement,
            budget,
            allocation_error,
        )
    }

    fn substitute_tail_once_with_budget_and_failure<B: TypeWorkMeter>(
        &self,
        target: EffectRowVariable,
        replacement: &Self,
        budget: &mut B,
        mut storage_error: impl FnMut(&mut B) -> B::Error,
    ) -> Result<Result<Self, EffectRowError>, B::Error> {
        let Some(tail) = &self.tail else {
            return clone_effect_row_with_budget_and_failure(self, budget, storage_error).map(Ok);
        };
        if tail.variable != target {
            return clone_effect_row_with_budget_and_failure(self, budget, storage_error).map(Ok);
        }
        if replacement
            .tail
            .as_ref()
            .is_some_and(|replacement_tail| replacement_tail.variable == target)
        {
            return Ok(Err(EffectRowError::Infinite));
        }
        for member in &replacement.known {
            if find_instance_index_with_budget_and_failure(
                &tail.lacks,
                member,
                budget,
                &mut storage_error,
            )?
            .is_some()
            {
                return Ok(Err(EffectRowError::Missing));
            }
        }

        match &replacement.tail {
            None => rebuild_effect_row_with_budget_and_failure(
                self.known.iter().chain(replacement.known.iter()),
                None,
                std::iter::empty(),
                |argument, budget| clone_type_with_budget(argument, budget),
                budget,
                &mut storage_error,
            )
            .map(Ok),
            Some(replacement_tail) => rebuild_effect_row_with_budget_and_failure(
                self.known.iter().chain(replacement.known.iter()),
                Some(replacement_tail.variable),
                tail.lacks.iter().chain(replacement_tail.lacks.iter()),
                |argument, budget| clone_type_with_budget(argument, budget),
                budget,
                &mut storage_error,
            )
            .map(Ok),
        }
    }

    pub(crate) fn map_type_arguments_with_budget<E>(
        &self,
        map: impl FnMut(&Type, &mut TypeWorkBudget) -> Result<Type, E>,
        budget: &mut TypeWorkBudget,
    ) -> Result<Self, E>
    where
        E: From<()>,
    {
        rebuild_effect_row_with_budget(
            self.known.iter(),
            self.tail.as_ref().map(|tail| tail.variable),
            self.tail.iter().flat_map(|tail| tail.lacks.iter()),
            map,
            budget,
        )
    }
}

pub(crate) fn rebuild_effect_row_with_budget<'a, E, B: TypeWorkMeter>(
    known: impl IntoIterator<Item = &'a EffectInstance>,
    tail: Option<EffectRowVariable>,
    lacks: impl IntoIterator<Item = &'a EffectInstance>,
    map: impl FnMut(&Type, &mut B) -> Result<Type, E>,
    budget: &mut B,
) -> Result<EffectRow, E>
where
    E: From<B::Error>,
{
    rebuild_effect_row_with_budget_and_failure(known, tail, lacks, map, budget, allocation_error)
}

fn rebuild_effect_row_with_budget_and_failure<'a, E, B: TypeWorkMeter>(
    known: impl IntoIterator<Item = &'a EffectInstance>,
    tail: Option<EffectRowVariable>,
    lacks: impl IntoIterator<Item = &'a EffectInstance>,
    mut map: impl FnMut(&Type, &mut B) -> Result<Type, E>,
    budget: &mut B,
    mut storage_error: impl FnMut(&mut B) -> B::Error,
) -> Result<EffectRow, E>
where
    E: From<B::Error>,
{
    fn rebuild_instance<E, B: TypeWorkMeter>(
        instance: &EffectInstance,
        map: &mut impl FnMut(&Type, &mut B) -> Result<Type, E>,
        budget: &mut B,
        storage_error: &mut impl FnMut(&mut B) -> B::Error,
    ) -> Result<EffectInstance, E>
    where
        E: From<B::Error>,
    {
        let mut arguments = Vec::new();
        for argument in &instance.arguments {
            let argument = IterativeTypeOwner::new(map(argument, budget)?);
            budget.charge(1).map_err(E::from)?;
            reserve_row(&mut arguments, 1, RowReservationSite::RebuildArguments)
                .map_err(|_| E::from(storage_error(budget)))?;
            arguments.push(argument);
        }
        let mut retained = Vec::new();
        budget.charge(arguments.len()).map_err(E::from)?;
        reserve_row(
            &mut retained,
            arguments.len(),
            RowReservationSite::RebuildRetained,
        )
        .map_err(|_| E::from(storage_error(budget)))?;
        retained.extend(arguments.into_iter().map(IterativeTypeOwner::into_inner));
        Ok(EffectInstance::new(
            instance.effect,
            retained.into_boxed_slice(),
        ))
    }

    let mut rebuilt_known = Vec::new();
    for instance in known {
        let instance = rebuild_instance(instance, &mut map, budget, &mut storage_error)?;
        budget.charge(1).map_err(E::from)?;
        reserve_row(&mut rebuilt_known, 1, RowReservationSite::RebuildMembers)
            .map_err(|_| E::from(storage_error(budget)))?;
        rebuilt_known.push(instance);
    }
    let rebuilt_tail = if let Some(variable) = tail {
        let mut rebuilt_lacks = Vec::new();
        for instance in lacks {
            let instance = rebuild_instance(instance, &mut map, budget, &mut storage_error)?;
            budget.charge(1).map_err(E::from)?;
            reserve_row(&mut rebuilt_lacks, 1, RowReservationSite::RebuildLacks)
                .map_err(|_| E::from(storage_error(budget)))?;
            rebuilt_lacks.push(instance);
        }
        Some((variable, rebuilt_lacks))
    } else {
        None
    };
    effect_row_from_owned_parts_with_budget_and_failure(
        rebuilt_known,
        rebuilt_tail,
        budget,
        storage_error,
    )
    .map_err(E::from)
}

fn contains_instance_with_budget<B: TypeWorkMeter>(
    instances: &[EffectInstance],
    target: &EffectInstance,
    budget: &mut B,
) -> Result<bool, B::Error> {
    Ok(find_instance_index_with_budget(instances, target, budget)?.is_some())
}

fn find_instance_index_with_budget<B: TypeWorkMeter>(
    instances: &[EffectInstance],
    target: &EffectInstance,
    budget: &mut B,
) -> Result<Option<usize>, B::Error> {
    find_instance_index_with_budget_and_failure(instances, target, budget, &mut allocation_error)
}

fn find_instance_index_with_budget_and_failure<B: TypeWorkMeter>(
    instances: &[EffectInstance],
    target: &EffectInstance,
    budget: &mut B,
    storage_error: &mut impl FnMut(&mut B) -> B::Error,
) -> Result<Option<usize>, B::Error> {
    for (index, instance) in instances.iter().enumerate() {
        if compare_effect_instances_with_charge(instance, target, budget, storage_error)?
            == Ordering::Equal
        {
            return Ok(Some(index));
        }
    }
    Ok(None)
}

fn canonical_instances_with_budget<B: TypeWorkMeter>(
    instances: Vec<EffectInstance>,
    budget: &mut B,
    storage_error: &mut impl FnMut(&mut B) -> B::Error,
) -> Result<Vec<EffectInstance>, B::Error> {
    let mut canonical = Vec::new();
    for instance in instances {
        let mut position = 0;
        let mut duplicate = false;
        while position < canonical.len() {
            match compare_effect_instances_with_charge(
                &canonical[position],
                &instance,
                budget,
                storage_error,
            )? {
                Ordering::Less => position += 1,
                Ordering::Equal => {
                    duplicate = true;
                    break;
                }
                Ordering::Greater => break,
            }
        }
        if duplicate {
            continue;
        }
        budget.charge(1)?;
        reserve_row(&mut canonical, 1, RowReservationSite::CanonicalMembers)
            .map_err(|_| storage_error(budget))?;
        canonical.insert(position, instance);
    }
    Ok(canonical)
}

fn canonical_instances(instances: Vec<EffectInstance>) -> Vec<EffectInstance> {
    canonical_instances_with_budget(
        instances,
        &mut TypeWorkBudget::unbounded(),
        &mut allocation_error,
    )
    .expect("an in-memory row can reserve its canonical member vector")
}

pub(crate) fn effect_row_from_owned_parts_with_budget<B: TypeWorkMeter>(
    known: Vec<EffectInstance>,
    tail: Option<(EffectRowVariable, Vec<EffectInstance>)>,
    budget: &mut B,
) -> Result<EffectRow, B::Error> {
    effect_row_from_owned_parts_with_budget_and_failure(known, tail, budget, allocation_error)
}

fn effect_row_from_owned_parts_with_budget_and_failure<B: TypeWorkMeter>(
    known: Vec<EffectInstance>,
    tail: Option<(EffectRowVariable, Vec<EffectInstance>)>,
    budget: &mut B,
    mut storage_error: impl FnMut(&mut B) -> B::Error,
) -> Result<EffectRow, B::Error> {
    budget.charge(1)?;
    let known =
        canonical_instances_with_budget(known, budget, &mut storage_error)?.into_boxed_slice();
    let tail = if let Some((variable, lacks)) = tail {
        budget.charge(1)?;
        Some(EffectRowTail {
            variable,
            lacks: canonical_instances_with_budget(lacks, budget, &mut storage_error)?
                .into_boxed_slice(),
        })
    } else {
        None
    };
    Ok(EffectRow { known, tail })
}

/// Retains a source row whose known instances are already in canonical order.
pub(crate) fn effect_row_from_canonical_source_parts_with_budget<B: TypeWorkMeter>(
    known: Vec<EffectInstance>,
    tail: Option<EffectRowVariable>,
    budget: &mut B,
) -> Result<EffectRow, B::Error> {
    if let Some(variable) = tail {
        return rebuild_effect_row_with_budget(
            known.iter(),
            Some(variable),
            known.iter(),
            clone_type_with_budget,
            budget,
        );
    }
    budget.charge(1)?;
    let known = known.into_boxed_slice();
    Ok(EffectRow { known, tail: None })
}

pub(crate) fn compare_effect_instances_with_budget<B: TypeWorkMeter>(
    left: &EffectInstance,
    right: &EffectInstance,
    budget: &mut B,
) -> Result<Ordering, B::Error> {
    compare_effect_instances_with_charge(left, right, budget, &mut allocation_error)
}

fn compare_effect_instances_with_charge<B: TypeWorkMeter>(
    left: &EffectInstance,
    right: &EffectInstance,
    charge: &mut B,
    storage_error: &mut impl FnMut(&mut B) -> B::Error,
) -> Result<Ordering, B::Error> {
    charge.charge(1)?;
    let effects = left.effect.cmp(&right.effect);
    if effects != Ordering::Equal {
        return Ok(effects);
    }
    let lengths = left.arguments.len().cmp(&right.arguments.len());
    if lengths != Ordering::Equal {
        return Ok(lengths);
    }
    for (left, right) in left.arguments.iter().zip(&right.arguments) {
        let ordering = compare_types_with_charge(left, right, charge, storage_error)?;
        if ordering != Ordering::Equal {
            return Ok(ordering);
        }
    }
    Ok(Ordering::Equal)
}

pub(crate) fn same_effect_rows_with_budget(
    left: &EffectRow,
    right: &EffectRow,
    budget: &mut TypeWorkBudget,
) -> Result<bool, ()> {
    same_effect_rows_with_charge(left, right, |work| budget.charge(work))
}

pub(crate) fn same_effect_rows_with_charge(
    left: &EffectRow,
    right: &EffectRow,
    mut charge: impl FnMut(usize) -> Result<(), ()>,
) -> Result<bool, ()> {
    charge(1)?;
    if left.known.len() != right.known.len() {
        return Ok(false);
    }
    match (&left.tail, &right.tail) {
        (None, None) => {}
        (Some(left), Some(right)) => {
            charge(1)?;
            if left.variable != right.variable || left.lacks.len() != right.lacks.len() {
                return Ok(false);
            }
            for (left, right) in left.lacks.iter().zip(&right.lacks) {
                if compare_effect_instances_with_charge(
                    left,
                    right,
                    &mut charge,
                    &mut allocation_error,
                )? != Ordering::Equal
                {
                    return Ok(false);
                }
            }
        }
        _ => return Ok(false),
    }
    for (left, right) in left.known.iter().zip(&right.known) {
        if compare_effect_instances_with_charge(left, right, &mut charge, &mut allocation_error)?
            != Ordering::Equal
        {
            return Ok(false);
        }
    }
    Ok(true)
}

fn compare_types_with_charge<B: TypeWorkMeter>(
    left: &Type,
    right: &Type,
    charge: &mut B,
    storage_error: &mut impl FnMut(&mut B) -> B::Error,
) -> Result<Ordering, B::Error> {
    enum Task<'a> {
        Types(&'a Type, &'a Type),
        Kinds(&'a Kind, &'a Kind),
        Rows(&'a EffectRow, &'a EffectRow),
        Instances(&'a EffectInstance, &'a EffectInstance),
    }

    fn type_tag(ty: &Type) -> u8 {
        match ty {
            Type::Int => 0,
            Type::Bool => 1,
            Type::Unit => 2,
            Type::Tuple(_) => 3,
            Type::Nominal(_) => 4,
            Type::Variable(_) => 5,
            Type::Inference(_) => 6,
            Type::Application(_, _) => 7,
            Type::Forall(_, _) => 8,
            Type::Function(_, _) | Type::EffectfulFunction(_, _) => 9,
        }
    }

    fn kind_tag(kind: &Kind) -> u8 {
        match kind {
            Kind::Type => 0,
            Kind::EffectRow => 1,
            Kind::Arrow(_, _) => 2,
        }
    }

    fn variable_order(left: EffectRowVariable, right: EffectRowVariable) -> Ordering {
        match (left, right) {
            (EffectRowVariable::Rigid(left), EffectRowVariable::Rigid(right)) => left.cmp(&right),
            (EffectRowVariable::Inference(left), EffectRowVariable::Inference(right)) => {
                left.value().cmp(&right.value())
            }
            (EffectRowVariable::Rigid(_), EffectRowVariable::Inference(_)) => Ordering::Less,
            (EffectRowVariable::Inference(_), EffectRowVariable::Rigid(_)) => Ordering::Greater,
        }
    }

    let mut work = Vec::new();
    macro_rules! schedule {
        ($task:expr) => {{
            charge.charge(1)?;
            reserve_row(&mut work, 1, RowReservationSite::ComparisonWork)
                .map_err(|_| storage_error(charge))?;
            work.push($task);
        }};
    }
    schedule!(Task::Types(left, right));
    while let Some(task) = work.pop() {
        let ordering = match task {
            Task::Types(left, right) => {
                let tags = type_tag(left).cmp(&type_tag(right));
                if tags != Ordering::Equal {
                    tags
                } else {
                    match (left, right) {
                        (Type::Int, Type::Int)
                        | (Type::Bool, Type::Bool)
                        | (Type::Unit, Type::Unit) => Ordering::Equal,
                        (Type::Nominal(left), Type::Nominal(right)) => left.cmp(right),
                        (Type::Variable(left), Type::Variable(right)) => left.cmp(right),
                        (Type::Inference(left), Type::Inference(right)) => {
                            left.value().cmp(&right.value())
                        }
                        (Type::Tuple(left), Type::Tuple(right)) => {
                            let lengths = left.len().cmp(&right.len());
                            if lengths == Ordering::Equal {
                                for (left, right) in left.iter().zip(right).rev() {
                                    schedule!(Task::Types(left, right));
                                }
                            }
                            lengths
                        }
                        (
                            Type::Application(left_function, left_argument),
                            Type::Application(right_function, right_argument),
                        ) => {
                            schedule!(Task::Types(left_argument, right_argument));
                            schedule!(Task::Types(left_function, right_function));
                            Ordering::Equal
                        }
                        (
                            Type::Forall(left_parameters, left),
                            Type::Forall(right_parameters, right),
                        ) => {
                            let lengths = left_parameters.len().cmp(&right_parameters.len());
                            if lengths == Ordering::Equal {
                                schedule!(Task::Types(left, right));
                                for ((left_id, left_kind), (right_id, right_kind)) in
                                    left_parameters.iter().zip(right_parameters).rev()
                                {
                                    schedule!(Task::Kinds(left_kind, right_kind));
                                    if left_id != right_id {
                                        return Ok(left_id.cmp(right_id));
                                    }
                                }
                            }
                            lengths
                        }
                        (
                            Type::Function(left_domain, left_value),
                            Type::Function(right_domain, right_value),
                        ) => {
                            schedule!(Task::Types(left_value, right_value));
                            schedule!(Task::Types(left_domain, right_domain));
                            Ordering::Equal
                        }
                        (
                            Type::EffectfulFunction(left_domain, left_computation),
                            Type::EffectfulFunction(right_domain, right_computation),
                        ) => {
                            schedule!(Task::Rows(
                                &left_computation.effects,
                                &right_computation.effects,
                            ));
                            schedule!(Task::Types(
                                &left_computation.value,
                                &right_computation.value,
                            ));
                            schedule!(Task::Types(left_domain, right_domain));
                            Ordering::Equal
                        }
                        (
                            Type::Function(left_domain, left_value),
                            Type::EffectfulFunction(right_domain, right_computation),
                        ) if right_computation.effects.is_empty() => {
                            schedule!(Task::Types(left_value, &right_computation.value));
                            schedule!(Task::Types(left_domain, right_domain));
                            Ordering::Equal
                        }
                        (
                            Type::EffectfulFunction(left_domain, left_computation),
                            Type::Function(right_domain, right_value),
                        ) if left_computation.effects.is_empty() => {
                            schedule!(Task::Types(&left_computation.value, right_value));
                            schedule!(Task::Types(left_domain, right_domain));
                            Ordering::Equal
                        }
                        (Type::Function(_, _), Type::EffectfulFunction(_, _)) => Ordering::Less,
                        (Type::EffectfulFunction(_, _), Type::Function(_, _)) => Ordering::Greater,
                        _ => unreachable!("equal type tags have one structural family"),
                    }
                }
            }
            Task::Kinds(left, right) => {
                let tags = kind_tag(left).cmp(&kind_tag(right));
                if tags != Ordering::Equal {
                    tags
                } else if let (
                    Kind::Arrow(left_domain, left_codomain),
                    Kind::Arrow(right_domain, right_codomain),
                ) = (left, right)
                {
                    schedule!(Task::Kinds(left_codomain, right_codomain));
                    schedule!(Task::Kinds(left_domain, right_domain));
                    Ordering::Equal
                } else {
                    Ordering::Equal
                }
            }
            Task::Rows(left, right) => {
                let lengths = left.known.len().cmp(&right.known.len());
                if lengths != Ordering::Equal {
                    lengths
                } else {
                    match (&left.tail, &right.tail) {
                        (None, Some(_)) => return Ok(Ordering::Less),
                        (Some(_), None) => return Ok(Ordering::Greater),
                        (Some(left_tail), Some(right_tail)) => {
                            let variables = variable_order(left_tail.variable, right_tail.variable);
                            if variables != Ordering::Equal {
                                return Ok(variables);
                            }
                            let lacks_lengths = left_tail.lacks.len().cmp(&right_tail.lacks.len());
                            if lacks_lengths != Ordering::Equal {
                                return Ok(lacks_lengths);
                            }
                            for (left, right) in left_tail.lacks.iter().zip(&right_tail.lacks).rev()
                            {
                                schedule!(Task::Instances(left, right));
                            }
                        }
                        (None, None) => {}
                    }
                    for (left, right) in left.known.iter().zip(&right.known).rev() {
                        schedule!(Task::Instances(left, right));
                    }
                    Ordering::Equal
                }
            }
            Task::Instances(left, right) => {
                let effects = left.effect.cmp(&right.effect);
                if effects != Ordering::Equal {
                    effects
                } else {
                    let lengths = left.arguments.len().cmp(&right.arguments.len());
                    if lengths == Ordering::Equal {
                        for (left, right) in left.arguments.iter().zip(&right.arguments).rev() {
                            schedule!(Task::Types(left, right));
                        }
                    }
                    lengths
                }
            }
        };
        if ordering != Ordering::Equal {
            return Ok(ordering);
        }
    }
    Ok(Ordering::Equal)
}

impl Clone for EffectRow {
    fn clone(&self) -> Self {
        Self {
            known: self.known.clone(),
            tail: self.tail.clone(),
        }
    }
}

impl PartialEq for EffectRow {
    fn eq(&self, other: &Self) -> bool {
        fn same_instances(left: &[EffectInstance], right: &[EffectInstance]) -> bool {
            left.len() == right.len()
                && left.iter().zip(right).all(|(left, right)| {
                    left.effect == right.effect
                        && left.arguments.len() == right.arguments.len()
                        && left
                            .arguments
                            .iter()
                            .zip(right.arguments.iter())
                            .all(|(left, right)| same_type(left, right))
                })
        }

        same_instances(&self.known, &other.known)
            && match (&self.tail, &other.tail) {
                (None, None) => true,
                (Some(left), Some(right)) => {
                    left.variable == right.variable && same_instances(&left.lacks, &right.lacks)
                }
                _ => false,
            }
    }
}

impl Eq for EffectRow {}

impl Hash for EffectRow {
    fn hash<H: Hasher>(&self, state: &mut H) {
        hash_type_or_effect_row(TypeHashTask::EffectRow(self), state);
    }
}

impl Drop for EffectRow {
    fn drop(&mut self) {
        drop(std::mem::take(&mut self.known));
        if let Some(tail) = self.tail.take() {
            drop(tail.lacks);
        }
    }
}

impl fmt::Display for EffectRow {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str("{")?;
        for (index, instance) in self.known.iter().enumerate() {
            if index > 0 {
                formatter.write_str(", ")?;
            }
            write!(
                formatter,
                "<effect:{}:{}>",
                instance.effect.module, instance.effect.declaration
            )?;
            if !instance.arguments.is_empty() {
                formatter.write_str("<")?;
                for (argument_index, argument) in instance.arguments.iter().enumerate() {
                    if argument_index > 0 {
                        formatter.write_str(", ")?;
                    }
                    write!(formatter, "{argument}")?;
                }
                formatter.write_str(">")?;
            }
        }
        if let Some(tail) = &self.tail {
            if !self.known.is_empty() {
                formatter.write_str(" ")?;
            }
            formatter.write_str("| ")?;
            match tail.variable {
                EffectRowVariable::Rigid(TypeVariableId::Resolved { module, local }) => {
                    write!(formatter, "<row-variable:{module}:{local}>")?;
                }
                EffectRowVariable::Rigid(TypeVariableId::Generated(local)) => {
                    write!(formatter, "<row-variable:generated:{local}>")?;
                }
                EffectRowVariable::Inference(identity) => {
                    write!(formatter, "?row{}", identity.value())?;
                }
            }
        }
        formatter.write_str("}")
    }
}

/// A computation result pairs one value type with one effect row.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct ComputationType {
    pub(crate) value: Type,
    pub(crate) effects: EffectRow,
}

impl ComputationType {
    /// Creates a computation type from its value and effect components.
    #[must_use]
    pub const fn new(value: Type, effects: EffectRow) -> Self {
        Self { value, effects }
    }

    /// Compatibility constructor for a pure computation result.
    #[must_use]
    pub fn pure(value: Type) -> Self {
        Self::new(value, EffectRow::empty())
    }

    /// Borrows the returned value type.
    #[must_use]
    pub const fn value(&self) -> &Type {
        &self.value
    }

    /// Borrows the latent effect row.
    #[must_use]
    pub const fn effects(&self) -> &EffectRow {
        &self.effects
    }

    pub(crate) fn tail_variable(&self) -> Option<EffectRowVariable> {
        self.effects.tail.as_ref().map(|tail| tail.variable)
    }

    pub(crate) fn effect_arguments(&self) -> impl Iterator<Item = &Type> {
        self.effects
            .known
            .iter()
            .chain(self.effects.tail.iter().flat_map(|tail| tail.lacks.iter()))
            .flat_map(|instance| instance.arguments.iter())
    }

    pub(crate) fn effect_argument_count(&self) -> usize {
        self.effect_arguments().count()
    }

    pub(crate) fn extend_effect_arguments<'a>(&'a self, output: &mut Vec<&'a Type>) {
        output.extend(self.effect_arguments());
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
            owner: NominalOwner::Module,
            declaration,
        }
    }

    /// Creates the identity for one lexical nominal declaration.
    #[must_use]
    pub fn lexical(module: impl Into<ModuleId>, declaration: u32) -> Self {
        Self {
            module: module.into(),
            owner: NominalOwner::Lexical,
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

    /// Reports whether this identity belongs to a lexical declaration.
    #[must_use]
    pub const fn is_lexical(self) -> bool {
        matches!(self.owner, NominalOwner::Lexical)
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
    /// A unary function whose canonical computation codomain has an empty row.
    Function(Box<Type>, Box<Type>),
    /// A unary function whose computation codomain has a nonempty or open row.
    EffectfulFunction(Box<Type>, Box<ComputationType>),
}

/// Borrowed semantic view of one function value type.
#[derive(Clone, Copy)]
pub struct FunctionTypeView<'a> {
    domain: &'a Type,
    value: &'a Type,
    effects: Option<&'a EffectRow>,
}

impl<'a> FunctionTypeView<'a> {
    #[must_use]
    pub const fn domain(self) -> &'a Type {
        self.domain
    }

    #[must_use]
    pub const fn value(self) -> &'a Type {
        self.value
    }

    /// Returns `None` for the canonical empty computation row.
    #[must_use]
    pub const fn effects(self) -> Option<&'a EffectRow> {
        self.effects
    }
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
    /// Borrows the semantic domain and computation codomain of a function.
    #[must_use]
    pub fn function_view(&self) -> Option<FunctionTypeView<'_>> {
        match self {
            Self::Function(domain, value) => Some(FunctionTypeView {
                domain,
                value,
                effects: None,
            }),
            Self::EffectfulFunction(domain, computation) => Some(FunctionTypeView {
                domain,
                value: computation.value(),
                effects: (!computation.effects().is_empty()).then_some(computation.effects()),
            }),
            _ => None,
        }
    }

    /// Compatibility constructor for a function with an empty latent row.
    #[must_use]
    pub fn function(domain: Type, codomain: Type) -> Self {
        Self::Function(Box::new(domain), Box::new(codomain))
    }

    /// Creates a function and canonicalizes an empty computation row.
    #[must_use]
    pub fn function_computation(domain: Type, codomain: ComputationType) -> Self {
        if codomain.effects.is_empty() {
            Self::function(domain, codomain.value)
        } else {
            Self::EffectfulFunction(Box::new(domain), Box::new(codomain))
        }
    }

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

#[cfg(test)]
thread_local! {
    static TYPE_DISCARD_VISITS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
    static TYPE_DISCARD_PENDING: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
    static TYPE_DISCARD_PENDING_PEAK: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

#[cfg(test)]
pub(crate) fn reset_type_discard_observation() {
    TYPE_DISCARD_VISITS.set(0);
    TYPE_DISCARD_PENDING.set(0);
    TYPE_DISCARD_PENDING_PEAK.set(0);
}

#[cfg(test)]
pub(crate) fn type_discard_visits() -> usize {
    TYPE_DISCARD_VISITS.get()
}

#[cfg(test)]
fn type_discard_pending() -> usize {
    TYPE_DISCARD_PENDING.get()
}

#[cfg(test)]
fn type_discard_pending_peak() -> usize {
    TYPE_DISCARD_PENDING_PEAK.get()
}

#[cfg(test)]
fn begin_type_discard_observation() {
    TYPE_DISCARD_PENDING.set(1);
    TYPE_DISCARD_PENDING_PEAK.set(1);
}

#[cfg(test)]
fn observe_type_discard_visit(children: usize) {
    TYPE_DISCARD_VISITS.set(TYPE_DISCARD_VISITS.get() + 1);
    let pending = TYPE_DISCARD_PENDING
        .get()
        .checked_sub(1)
        .and_then(|pending| pending.checked_add(children))
        .expect("a visited Type node must be pending exactly once");
    TYPE_DISCARD_PENDING.set(pending);
    TYPE_DISCARD_PENDING_PEAK.set(TYPE_DISCARD_PENDING_PEAK.get().max(pending));
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
        EffectInstances(std::vec::IntoIter<EffectInstance>),
    }

    let mut work = crate::eval::disposal::Pending::new(crate::eval::RuntimeResource::TypeDisposal);
    work.push(Task::Visit(root));
    #[cfg(test)]
    begin_type_discard_observation();
    while let Some(task) = work.pop() {
        #[cfg(test)]
        if let Task::Visit(ty) = &task {
            let children = match ty {
                Type::Tuple(elements) => elements.len(),
                Type::Application(_, _) => 2,
                Type::Function(_, _) => 2,
                Type::EffectfulFunction(_, codomain) => {
                    2 + codomain
                        .effects
                        .known
                        .iter()
                        .chain(
                            codomain
                                .effects
                                .tail
                                .iter()
                                .flat_map(|tail| tail.lacks.iter()),
                        )
                        .map(|instance| instance.arguments.len())
                        .sum::<usize>()
                }
                Type::Forall(_, _) => 1,
                Type::Int
                | Type::Bool
                | Type::Unit
                | Type::Nominal(_)
                | Type::Variable(_)
                | Type::Inference(_) => 0,
            };
            observe_type_discard_visit(children);
        }
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
            Task::Visit(Type::EffectfulFunction(domain, codomain)) => {
                let ComputationType { value, mut effects } = *codomain;
                let known = std::mem::take(&mut effects.known).into_vec().into_iter();
                let lacks = effects
                    .tail
                    .take()
                    .map(|tail| tail.lacks.into_vec().into_iter());
                drop(effects);
                if let Some(lacks) = lacks {
                    work.push(Task::EffectInstances(lacks));
                }
                work.push(Task::EffectInstances(known));
                work.push(Task::Visit(value));
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
            Task::EffectInstances(mut remaining) => {
                if let Some(mut instance) = remaining.next() {
                    let arguments = std::mem::take(&mut instance.arguments)
                        .into_vec()
                        .into_iter();
                    drop(instance);
                    work.push(Task::EffectInstances(remaining));
                    work.push(Task::Sequence(arguments));
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
        EffectRow(&'a EffectRow),
        EffectInstances(std::slice::Iter<'a, EffectInstance>),
        EffectInstance(&'a EffectInstance),
        EffectRowTail(&'a EffectRowTail, bool),
        Text(&'static str),
        Sequence(std::slice::Iter<'a, Type>),
    }

    let mut work = vec![Task::Visit(ty)];
    while let Some(task) = work.pop() {
        match task {
            Task::Text(text) => formatter.write_str(text)?,
            Task::EffectRow(row) => {
                formatter.write_str("{")?;
                work.push(Task::Text("}"));
                if let Some(tail) = &row.tail {
                    work.push(Task::EffectRowTail(tail, !row.known.is_empty()));
                }
                work.push(Task::EffectInstances(row.known.iter()));
            }
            Task::EffectInstances(mut remaining) => {
                if let Some(next) = remaining.next() {
                    if !remaining.as_slice().is_empty() {
                        work.push(Task::EffectInstances(remaining));
                        work.push(Task::Text(", "));
                    }
                    work.push(Task::EffectInstance(next));
                }
            }
            Task::EffectInstance(instance) => {
                write!(
                    formatter,
                    "<effect:{}:{}>",
                    instance.effect.module, instance.effect.declaration
                )?;
                if !instance.arguments.is_empty() {
                    work.push(Task::Text(">"));
                    work.push(Task::Sequence(instance.arguments.iter()));
                    work.push(Task::Text("<"));
                }
            }
            Task::EffectRowTail(tail, after_known) => {
                formatter.write_str(if after_known { " | " } else { "| " })?;
                match tail.variable {
                    EffectRowVariable::Rigid(TypeVariableId::Resolved { module, local }) => {
                        write!(formatter, "<row-variable:{module}:{local}>")?;
                    }
                    EffectRowVariable::Rigid(TypeVariableId::Generated(local)) => {
                        write!(formatter, "<row-variable:generated:{local}>")?;
                    }
                    EffectRowVariable::Inference(identity) => {
                        write!(formatter, "?row{}", identity.value())?;
                    }
                }
            }
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
            Task::Visit(Type::Nominal(identity)) => {
                if identity.is_lexical() {
                    write!(
                        formatter,
                        "<local-type:{}:{}>",
                        identity.module, identity.declaration
                    )?;
                } else {
                    write!(
                        formatter,
                        "<type:{}:{}>",
                        identity.module, identity.declaration
                    )?;
                }
            }
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
                    if matches!(
                        function.as_ref(),
                        Type::Function(_, _) | Type::EffectfulFunction(_, _) | Type::Forall(_, _)
                    ) {
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
                if matches!(
                    domain.as_ref(),
                    Type::Function(_, _) | Type::EffectfulFunction(_, _)
                ) {
                    work.push(Task::Text(")"));
                    work.push(Task::Visit(domain));
                    work.push(Task::Text("("));
                } else {
                    work.push(Task::Visit(domain));
                }
            }
            Task::Visit(Type::EffectfulFunction(domain, codomain)) => {
                if !codomain.effects.is_empty() {
                    work.push(Task::EffectRow(&codomain.effects));
                    work.push(Task::Text(" ! "));
                }
                work.push(Task::Visit(&codomain.value));
                work.push(Task::Text(" -> "));
                if matches!(
                    domain.as_ref(),
                    Type::Function(_, _) | Type::EffectfulFunction(_, _)
                ) {
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
        CompareRows(&'a EffectRow, &'a EffectRow),
        Sequence(std::iter::Zip<std::slice::Iter<'a, Type>, std::slice::Iter<'a, Type>>),
    }
    let mut pending = vec![Task::Compare(left, right)];
    while let Some(task) = pending.pop() {
        let Task::Compare(left, right) = task else {
            match task {
                Task::Sequence(mut remaining) => {
                    if let Some((left, right)) = remaining.next() {
                        pending.push(Task::Sequence(remaining));
                        pending.push(Task::Compare(left, right));
                    }
                }
                Task::CompareRows(left, right) => {
                    if left.known.len() != right.known.len() {
                        return false;
                    }
                    for (left, right) in left.known.iter().zip(right.known.iter()) {
                        if left.effect != right.effect
                            || left.arguments.len() != right.arguments.len()
                        {
                            return false;
                        }
                        pending.push(Task::Sequence(
                            left.arguments.iter().zip(right.arguments.iter()),
                        ));
                    }
                    match (&left.tail, &right.tail) {
                        (None, None) => {}
                        (Some(left), Some(right))
                            if left.variable == right.variable
                                && left.lacks.len() == right.lacks.len() =>
                        {
                            for (left, right) in left.lacks.iter().zip(right.lacks.iter()) {
                                if left.effect != right.effect
                                    || left.arguments.len() != right.arguments.len()
                                {
                                    return false;
                                }
                                pending.push(Task::Sequence(
                                    left.arguments.iter().zip(right.arguments.iter()),
                                ));
                            }
                        }
                        _ => return false,
                    }
                }
                Task::Compare(_, _) => unreachable!(),
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
            (
                Type::EffectfulFunction(left_domain, left_codomain),
                Type::EffectfulFunction(right_domain, right_codomain),
            ) => {
                pending.push(Task::CompareRows(
                    &left_codomain.effects,
                    &right_codomain.effects,
                ));
                pending.push(Task::Compare(&left_codomain.value, &right_codomain.value));
                pending.push(Task::Compare(left_domain, right_domain));
            }
            (
                Type::Function(left_domain, left_codomain),
                Type::EffectfulFunction(right_domain, right_codomain),
            )
            | (
                Type::EffectfulFunction(right_domain, right_codomain),
                Type::Function(left_domain, left_codomain),
            ) if right_codomain.effects.is_empty() => {
                pending.push(Task::Compare(left_codomain, &right_codomain.value));
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
        CompareRows(&'a EffectRow, &'a EffectRow),
        Sequence(std::iter::Zip<std::slice::Iter<'a, Type>, std::slice::Iter<'a, Type>>),
    }

    let mut pending = vec![Task::Compare(left, right)];
    while let Some(task) = pending.pop() {
        let Task::Compare(left, right) = task else {
            match task {
                Task::Sequence(mut remaining) => {
                    if let Some((left, right)) = remaining.next() {
                        pending.push(Task::Sequence(remaining));
                        pending.push(Task::Compare(left, right));
                    }
                }
                Task::CompareRows(left, right) => {
                    budget.charge(1)?;
                    if left.known.len() != right.known.len() {
                        return Ok(false);
                    }
                    budget.charge(left.known.len())?;
                    for (left, right) in left.known.iter().zip(right.known.iter()) {
                        if left.effect != right.effect
                            || left.arguments.len() != right.arguments.len()
                        {
                            return Ok(false);
                        }
                        pending.push(Task::Sequence(
                            left.arguments.iter().zip(right.arguments.iter()),
                        ));
                    }
                    match (&left.tail, &right.tail) {
                        (None, None) => {}
                        (Some(left), Some(right))
                            if left.variable == right.variable
                                && left.lacks.len() == right.lacks.len() =>
                        {
                            budget.charge(1_usize.saturating_add(left.lacks.len()))?;
                            for (left, right) in left.lacks.iter().zip(right.lacks.iter()) {
                                if left.effect != right.effect
                                    || left.arguments.len() != right.arguments.len()
                                {
                                    return Ok(false);
                                }
                                pending.push(Task::Sequence(
                                    left.arguments.iter().zip(right.arguments.iter()),
                                ));
                            }
                        }
                        _ => return Ok(false),
                    }
                }
                Task::Compare(_, _) => unreachable!(),
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
            (
                Type::EffectfulFunction(left_domain, left_codomain),
                Type::EffectfulFunction(right_domain, right_codomain),
            ) => {
                budget.charge(1)?;
                pending.push(Task::CompareRows(
                    &left_codomain.effects,
                    &right_codomain.effects,
                ));
                pending.push(Task::Compare(&left_codomain.value, &right_codomain.value));
                pending.push(Task::Compare(left_domain, right_domain));
            }
            (
                Type::Function(left_domain, left_codomain),
                Type::EffectfulFunction(right_domain, right_codomain),
            )
            | (
                Type::EffectfulFunction(right_domain, right_codomain),
                Type::Function(left_domain, left_codomain),
            ) if right_codomain.effects.is_empty() => {
                budget.charge(2)?;
                pending.push(Task::Compare(left_codomain, &right_codomain.value));
                pending.push(Task::Compare(left_domain, right_domain));
            }
            _ => return Ok(false),
        }
    }
    Ok(true)
}

enum TypeHashTask<'a> {
    Visit(&'a Type),
    EffectRow(&'a EffectRow),
    Instances(std::slice::Iter<'a, EffectInstance>),
    Instance(&'a EffectInstance),
    Sequence(std::slice::Iter<'a, Type>),
}

fn hash_type<H: Hasher>(ty: &Type, state: &mut H) {
    hash_type_or_effect_row(TypeHashTask::Visit(ty), state);
}

fn hash_type_or_effect_row<H: Hasher>(root: TypeHashTask<'_>, state: &mut H) {
    let mut work = vec![root];
    while let Some(task) = work.pop() {
        match task {
            TypeHashTask::Sequence(mut remaining) => {
                if let Some(next) = remaining.next() {
                    work.push(TypeHashTask::Sequence(remaining));
                    work.push(TypeHashTask::Visit(next));
                }
            }
            TypeHashTask::EffectRow(row) => {
                10_u8.hash(state);
                row.known.len().hash(state);
                match &row.tail {
                    None => 0_u8.hash(state),
                    Some(tail) => {
                        1_u8.hash(state);
                        tail.variable.hash(state);
                        tail.lacks.len().hash(state);
                        work.push(TypeHashTask::Instances(tail.lacks.iter()));
                    }
                }
                work.push(TypeHashTask::Instances(row.known.iter()));
            }
            TypeHashTask::Instances(mut remaining) => {
                if let Some(next) = remaining.next() {
                    work.push(TypeHashTask::Instances(remaining));
                    work.push(TypeHashTask::Instance(next));
                }
            }
            TypeHashTask::Instance(instance) => {
                instance.effect.hash(state);
                instance.arguments.len().hash(state);
                work.push(TypeHashTask::Sequence(instance.arguments.iter()));
            }
            TypeHashTask::Visit(Type::Int) => 0_u8.hash(state),
            TypeHashTask::Visit(Type::Bool) => 1_u8.hash(state),
            TypeHashTask::Visit(Type::Unit) => 2_u8.hash(state),
            TypeHashTask::Visit(Type::Tuple(elements)) => {
                3_u8.hash(state);
                elements.len().hash(state);
                work.push(TypeHashTask::Sequence(elements.iter()));
            }
            TypeHashTask::Visit(Type::Nominal(identity)) => {
                4_u8.hash(state);
                identity.hash(state);
            }
            TypeHashTask::Visit(Type::Variable(identity)) => {
                5_u8.hash(state);
                identity.hash(state);
            }
            TypeHashTask::Visit(Type::Inference(identity)) => {
                6_u8.hash(state);
                identity.hash(state);
            }
            TypeHashTask::Visit(Type::Application(function, argument)) => {
                7_u8.hash(state);
                work.push(TypeHashTask::Visit(argument));
                work.push(TypeHashTask::Visit(function));
            }
            TypeHashTask::Visit(Type::Forall(parameters, body)) => {
                8_u8.hash(state);
                parameters.hash(state);
                work.push(TypeHashTask::Visit(body));
            }
            TypeHashTask::Visit(Type::Function(domain, codomain)) => {
                9_u8.hash(state);
                EffectRow::empty().hash(state);
                work.push(TypeHashTask::Visit(codomain));
                work.push(TypeHashTask::Visit(domain));
            }
            TypeHashTask::Visit(Type::EffectfulFunction(domain, codomain)) => {
                9_u8.hash(state);
                work.push(TypeHashTask::Visit(&codomain.value));
                work.push(TypeHashTask::Visit(domain));
                work.push(TypeHashTask::EffectRow(&codomain.effects));
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
    mut allocation_error: impl FnMut() -> E,
) -> Result<Type, E> {
    match substitute_type_and_row_variables(
        ty,
        replacements,
        &HashMap::new(),
        &mut charge,
        &mut allocation_error,
    )? {
        Ok(ty) => Ok(ty),
        Err(_) => unreachable!("ordinary type substitution cannot violate row constraints"),
    }
}

pub(crate) fn substitute_type_and_row_variables_with<E>(
    ty: &Type,
    replacements: &HashMap<TypeVariableId, Type>,
    row_replacements: &HashMap<TypeVariableId, EffectRow>,
    mut charge: impl FnMut(usize) -> Result<(), E>,
    mut allocation_error: impl FnMut() -> E,
) -> Result<Result<Type, EffectRowError>, E> {
    substitute_type_and_row_variables(
        ty,
        replacements,
        row_replacements,
        &mut charge,
        &mut allocation_error,
    )
}

#[allow(
    clippy::type_complexity,
    reason = "the local traversal shape mirrors substitution state without a module-level alias"
)]
fn substitute_type_and_row_variables<E>(
    ty: &Type,
    replacements: &HashMap<TypeVariableId, Type>,
    row_replacements: &HashMap<TypeVariableId, EffectRow>,
    charge: &mut impl FnMut(usize) -> Result<(), E>,
    allocation_error: &mut impl FnMut() -> E,
) -> Result<Result<Type, EffectRowError>, E> {
    struct RowShape<'a> {
        known: Box<[(EffectId, usize)]>,
        tail: Option<(EffectRowVariable, Box<[(EffectId, usize)]>)>,
        argument_count: usize,
        replacement: Option<(EffectRowVariable, &'a EffectRow)>,
    }

    enum Task<'a> {
        Visit(&'a Type, bool),
        Sequence(std::slice::Iter<'a, Type>, bool),
        EnterForall(&'a [(TypeVariableId, Kind)]),
        ExitForall(&'a [(TypeVariableId, Kind)]),
        FinishTuple(usize),
        FinishApplication,
        FinishFunction,
        FinishEffectfulFunction(RowShape<'a>),
        FinishForall(Box<[(TypeVariableId, Kind)]>),
    }

    let mut active_shadows = HashMap::new();
    let mut work = vec![Task::Visit(ty, true)];
    let mut rebuilt: Vec<IterativeTypeOwner> = Vec::new();
    while let Some(task) = work.pop() {
        match task {
            Task::Visit(Type::Variable(identity), true) => {
                if active_shadows
                    .get(identity)
                    .is_some_and(|count| *count != 0)
                {
                    charge(1)?;
                    rebuilt.push(IterativeTypeOwner::new(Type::Variable(*identity)));
                } else if let Some(replacement) = replacements.get(identity) {
                    work.push(Task::Visit(replacement, false));
                } else {
                    charge(1)?;
                    rebuilt.push(IterativeTypeOwner::new(Type::Variable(*identity)));
                }
            }
            Task::Visit(
                ty @ (Type::Int
                | Type::Bool
                | Type::Unit
                | Type::Nominal(_)
                | Type::Variable(_)
                | Type::Inference(_)),
                _,
            ) => {
                charge(1)?;
                rebuilt.push(IterativeTypeOwner::new(clone_type(ty)));
            }
            Task::Visit(Type::Tuple(elements), substitute) => {
                charge(1)?;
                work.push(Task::FinishTuple(elements.len()));
                work.push(Task::Sequence(elements.iter(), substitute));
            }
            Task::Visit(Type::Application(function, argument), substitute) => {
                charge(1)?;
                work.push(Task::FinishApplication);
                work.push(Task::Visit(argument, substitute));
                work.push(Task::Visit(function, substitute));
            }
            Task::Visit(Type::Function(domain, codomain), substitute) => {
                charge(1)?;
                work.push(Task::FinishFunction);
                work.push(Task::Visit(codomain, substitute));
                work.push(Task::Visit(domain, substitute));
            }
            Task::Visit(Type::EffectfulFunction(domain, codomain), substitute) => {
                charge(3)?;
                charge(codomain.effects.known.len())?;
                if let Some(tail) = &codomain.effects.tail {
                    charge(1)?;
                    charge(tail.lacks.len())?;
                }
                let instances = codomain.effects.known.iter().chain(
                    codomain
                        .effects
                        .tail
                        .iter()
                        .flat_map(|tail| tail.lacks.iter()),
                );
                let argument_count = instances.clone().try_fold(0usize, |count, instance| {
                    count
                        .checked_add(instance.arguments.len())
                        .ok_or_else(&mut *allocation_error)
                })?;
                // The label scan is already admitted. Admit every queued argument
                // before scanning the arguments or retaining proportional work.
                charge(argument_count)?;
                let pending = argument_count
                    .checked_add(3)
                    .ok_or_else(&mut *allocation_error)?;
                work.try_reserve(pending).map_err(|_| allocation_error())?;
                let mut known = Vec::new();
                known
                    .try_reserve(codomain.effects.known.len())
                    .map_err(|_| allocation_error())?;
                known.extend(
                    codomain
                        .effects
                        .known
                        .iter()
                        .map(|instance| (instance.effect, instance.arguments.len())),
                );
                let replacement =
                    codomain
                        .effects
                        .tail
                        .as_ref()
                        .and_then(|tail| match tail.variable {
                            EffectRowVariable::Rigid(identity)
                                if substitute
                                    && !active_shadows
                                        .get(&identity)
                                        .is_some_and(|count| *count != 0) =>
                            {
                                row_replacements
                                    .get(&identity)
                                    .map(|row| (tail.variable, row))
                            }
                            _ => None,
                        });
                let tail = if let Some(tail) = &codomain.effects.tail {
                    let mut lacks = Vec::new();
                    lacks
                        .try_reserve(tail.lacks.len())
                        .map_err(|_| allocation_error())?;
                    lacks.extend(
                        tail.lacks
                            .iter()
                            .map(|instance| (instance.effect, instance.arguments.len())),
                    );
                    Some((tail.variable, lacks.into_boxed_slice()))
                } else {
                    None
                };
                work.push(Task::FinishEffectfulFunction(RowShape {
                    known: known.into_boxed_slice(),
                    tail,
                    argument_count,
                    replacement,
                }));
                for instance in instances.rev() {
                    for argument in instance.arguments.iter().rev() {
                        work.push(Task::Visit(argument, substitute));
                    }
                }
                work.push(Task::Visit(&codomain.value, substitute));
                work.push(Task::Visit(domain, substitute));
            }
            Task::Visit(Type::Forall(parameters, body), substitute) => {
                charge(1)?;
                charge(parameters.len())?;
                for (_, kind) in parameters {
                    charge_kind_with_charge(kind, || charge(1))?;
                }
                work.push(Task::FinishForall(parameters.clone()));
                if substitute {
                    work.push(Task::ExitForall(parameters));
                    work.push(Task::Visit(body, substitute));
                    work.push(Task::EnterForall(parameters));
                } else {
                    work.push(Task::Visit(body, substitute));
                }
            }
            Task::Sequence(mut remaining, substitute) => {
                if let Some(ty) = remaining.next() {
                    work.push(Task::Sequence(remaining, substitute));
                    work.push(Task::Visit(ty, substitute));
                }
            }
            Task::EnterForall(parameters) => {
                for (parameter, _) in parameters {
                    if !replacements.contains_key(parameter)
                        && !row_replacements.contains_key(parameter)
                    {
                        continue;
                    }
                    if !active_shadows.contains_key(parameter) {
                        charge(1)?;
                        active_shadows
                            .try_reserve(1)
                            .map_err(|_| allocation_error())?;
                        active_shadows.insert(*parameter, 0usize);
                    }
                    charge(1)?;
                    let count = active_shadows
                        .get_mut(parameter)
                        .expect("an overlapping shadow key was retained before entry");
                    *count = count
                        .checked_add(1)
                        .expect("an active shadow count cannot exceed source nesting");
                }
            }
            Task::ExitForall(parameters) => {
                for (parameter, _) in parameters {
                    let Some(count) = active_shadows.get_mut(parameter) else {
                        continue;
                    };
                    charge(1)?;
                    *count = count
                        .checked_sub(1)
                        .expect("each exited shadow must have been entered");
                }
            }
            Task::FinishTuple(count) => {
                let elements = rebuilt.split_off(rebuilt.len() - count);
                rebuilt.push(IterativeTypeOwner::new(Type::Tuple(
                    elements
                        .into_iter()
                        .map(IterativeTypeOwner::into_inner)
                        .collect(),
                )));
            }
            Task::FinishApplication => {
                let argument = rebuilt
                    .pop()
                    .expect("type reconstruction argument")
                    .into_inner();
                let function = rebuilt
                    .pop()
                    .expect("type reconstruction function")
                    .into_inner();
                rebuilt.push(IterativeTypeOwner::new(Type::Application(
                    Box::new(function),
                    Box::new(argument),
                )));
            }
            Task::FinishFunction => {
                let codomain = rebuilt
                    .pop()
                    .expect("type reconstruction codomain")
                    .into_inner();
                let domain = rebuilt
                    .pop()
                    .expect("type reconstruction domain")
                    .into_inner();
                rebuilt.push(IterativeTypeOwner::new(Type::function(domain, codomain)));
            }
            Task::FinishEffectfulFunction(shape) => {
                let arguments = rebuilt.split_off(rebuilt.len() - shape.argument_count);
                let mut arguments = arguments.into_iter();
                let rebuild_instances =
                    |instances: Box<[(EffectId, usize)]>,
                     arguments: &mut std::vec::IntoIter<IterativeTypeOwner>| {
                        instances
                            .into_vec()
                            .into_iter()
                            .map(|(effect, count)| {
                                EffectInstance::new(
                                    effect,
                                    arguments
                                        .by_ref()
                                        .take(count)
                                        .map(IterativeTypeOwner::into_inner)
                                        .collect::<Vec<_>>()
                                        .into_boxed_slice(),
                                )
                            })
                            .collect::<Vec<_>>()
                    };
                let known = rebuild_instances(shape.known, &mut arguments);
                let tail = shape
                    .tail
                    .map(|(variable, lacks)| (variable, rebuild_instances(lacks, &mut arguments)));
                debug_assert!(arguments.next().is_none());
                let effects = effect_row_from_owned_parts_with_budget_and_failure(
                    known,
                    tail,
                    charge,
                    |_| allocation_error(),
                )?;
                let effects = if let Some((target, replacement)) = shape.replacement {
                    let substituted = if replacement.known.is_empty()
                        && replacement
                            .tail
                            .as_ref()
                            .is_some_and(|tail| tail.variable == target)
                    {
                        rebuild_effect_row_with_budget_and_failure(
                            effects.known.iter(),
                            Some(target),
                            effects
                                .tail
                                .iter()
                                .flat_map(|tail| tail.lacks.iter())
                                .chain(replacement.tail.iter().flat_map(|tail| tail.lacks.iter())),
                            |argument, budget| clone_type_with_budget(argument, budget),
                            charge,
                            |_| allocation_error(),
                        )
                        .map(Ok)?
                    } else {
                        effects.substitute_tail_once_with_budget_and_failure(
                            target,
                            replacement,
                            charge,
                            |_| allocation_error(),
                        )?
                    };
                    match substituted {
                        Ok(effects) => effects,
                        Err(error) => return Ok(Err(error)),
                    }
                } else {
                    effects
                };
                let codomain = rebuilt
                    .pop()
                    .expect("type reconstruction codomain")
                    .into_inner();
                let domain = rebuilt
                    .pop()
                    .expect("type reconstruction domain")
                    .into_inner();
                rebuilt.push(IterativeTypeOwner::new(Type::function_computation(
                    domain,
                    ComputationType::new(codomain, effects),
                )));
            }
            Task::FinishForall(parameters) => {
                let body = rebuilt
                    .pop()
                    .expect("type reconstruction scheme body")
                    .into_inner();
                rebuilt.push(IterativeTypeOwner::new(Type::Forall(
                    parameters,
                    Box::new(body),
                )));
            }
        }
    }
    debug_assert!(active_shadows.values().all(|count| *count == 0));
    Ok(Ok(rebuilt
        .pop()
        .expect("one reconstructed type")
        .into_inner()))
}

/// The internal kind language used to check type constructors.
pub enum Kind {
    /// The kind of every source-admitted value type.
    Type,
    /// The kind of computation effect rows.
    EffectRow,
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

/// Clones borrowed arrow domains and folds them over one owned result Kind.
///
/// The budget charges exactly the nodes retained in the returned Kind: every
/// result node, every cloned domain node, and one new Arrow per domain.
pub(crate) fn clone_arrows_with_budget<'a>(
    domains: impl DoubleEndedIterator<Item = &'a Kind>,
    result: Kind,
    budget: &mut TypeWorkBudget,
) -> Result<Kind, ()> {
    charge_kind_nodes(&result, budget)?;
    let mut kind = result;
    for domain in domains.rev() {
        let domain = clone_kind_with_budget(domain, budget)?;
        budget.charge(1)?;
        kind = Kind::Arrow(Box::new(domain), Box::new(kind));
    }
    Ok(kind)
}

#[cfg(test)]
thread_local! {
    static KIND_NODE_CHARGE_VISITS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
    static KIND_RENDER_MAX_LIVE_STATES: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
    // 0 is idle, 1 arms the next root, 2 observes that root's iterative
    // teardown, and 3 suppresses the sentinel field drops that follow it.
    static KIND_DISCARD_STATE: std::cell::Cell<u8> = const { std::cell::Cell::new(0) };
    static KIND_DISCARD_VISITS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
    static KIND_DISCARD_PENDING: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
    static KIND_DISCARD_PENDING_PEAK: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
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

#[cfg(test)]
fn reset_kind_discard_observation() {
    KIND_DISCARD_VISITS.set(0);
    KIND_DISCARD_PENDING.set(0);
    KIND_DISCARD_PENDING_PEAK.set(0);
    KIND_DISCARD_STATE.set(1);
}

#[cfg(test)]
fn begin_kind_discard_observation() -> bool {
    if KIND_DISCARD_STATE.get() == 1 {
        KIND_DISCARD_STATE.set(2);
        KIND_DISCARD_PENDING.set(1);
        KIND_DISCARD_PENDING_PEAK.set(1);
        true
    } else {
        false
    }
}

#[cfg(test)]
fn finish_kind_discard_observation() {
    assert_eq!(KIND_DISCARD_PENDING.get(), 0);
    KIND_DISCARD_STATE.set(3);
}

#[cfg(test)]
fn observe_kind_discard_visit(children: usize) {
    KIND_DISCARD_VISITS.set(KIND_DISCARD_VISITS.get() + 1);
    let pending = KIND_DISCARD_PENDING
        .get()
        .checked_sub(1)
        .and_then(|pending| pending.checked_add(children))
        .expect("a visited Kind node must be pending exactly once");
    KIND_DISCARD_PENDING.set(pending);
    KIND_DISCARD_PENDING_PEAK.set(KIND_DISCARD_PENDING_PEAK.get().max(pending));
}

#[cfg(test)]
fn kind_discard_visits() -> usize {
    KIND_DISCARD_VISITS.get()
}

#[cfg(test)]
fn kind_discard_pending() -> usize {
    KIND_DISCARD_PENDING.get()
}

#[cfg(test)]
fn kind_discard_pending_peak() -> usize {
    KIND_DISCARD_PENDING_PEAK.get()
}

pub(crate) fn charge_kind_nodes<B: TypeWorkMeter>(
    kind: &Kind,
    budget: &mut B,
) -> Result<(), B::Error> {
    charge_kind_with_charge(kind, || budget.charge(1))
}

pub(crate) fn charge_kind_with_charge<E>(
    kind: &Kind,
    mut charge: impl FnMut() -> Result<(), E>,
) -> Result<(), E> {
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
        Kind::Type | Kind::EffectRow => Ok(()),
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
            Task::Visit(Kind::EffectRow) => rebuilt.push(Kind::EffectRow),
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
            (Kind::Type, Kind::Type) | (Kind::EffectRow, Kind::EffectRow) => {}
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
            Kind::EffectRow => 1_u8.hash(state),
            Kind::Arrow(domain, codomain) => {
                2_u8.hash(state);
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
                Kind::EffectRow => {
                    formatter.write_str("EffectRow")?;
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
        if crate::eval::disposal::failure().is_some() {
            std::mem::forget(std::mem::replace(self, Self::Type));
            return;
        }
        #[cfg(test)]
        let observing = begin_kind_discard_observation();

        let Self::Arrow(domain, codomain) = self else {
            #[cfg(test)]
            if observing {
                observe_kind_discard_visit(0);
                finish_kind_discard_observation();
            }
            return;
        };
        #[cfg(test)]
        if observing {
            observe_kind_discard_visit(2);
        }
        if matches!(domain.as_ref(), Self::Type) && matches!(codomain.as_ref(), Self::Type) {
            #[cfg(test)]
            if observing {
                observe_kind_discard_visit(0);
                observe_kind_discard_visit(0);
                finish_kind_discard_observation();
            }
            return;
        }

        let mut work =
            crate::eval::disposal::Pending::new(crate::eval::RuntimeResource::KindDisposal);
        work.push(std::mem::replace(codomain.as_mut(), Self::Type));
        work.push(std::mem::replace(domain.as_mut(), Self::Type));
        while let Some(mut kind) = work.pop() {
            #[cfg(test)]
            if observing {
                observe_kind_discard_visit(usize::from(matches!(&kind, Self::Arrow(_, _))) * 2);
            }
            if let Self::Arrow(domain, codomain) = &mut kind {
                work.push(std::mem::replace(codomain.as_mut(), Self::Type));
                work.push(std::mem::replace(domain.as_mut(), Self::Type));
            }
        }
        #[cfg(test)]
        if observing {
            finish_kind_discard_observation();
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
    fn left_heavy_kind_operations_have_exact_late_failure_boundaries() {
        const DEPTH: usize = 32_768;
        // D left-heavy Arrows retain one right Type each plus the base Type.
        const KIND_NODES: usize = 2 * DEPTH + 1;

        fn left_heavy(depth: usize) -> Kind {
            let mut kind = Kind::Type;
            for _ in 0..depth {
                kind = Kind::Arrow(Box::new(kind), Box::new(Kind::Type));
            }
            kind
        }

        fn assert_left_heavy(kind: &Kind, depth: usize) {
            let mut current = kind;
            for level in 0..depth {
                let Kind::Arrow(domain, codomain) = current else {
                    panic!("left-heavy Arrow level {level} is missing");
                };
                assert!(matches!(codomain.as_ref(), Kind::Type));
                current = domain;
            }
            assert!(matches!(current, Kind::Type));
        }

        // The equal left subtree contains 2(D-1)+1 nodes. Its owning Arrow
        // and the final mismatched codomain pair make the comparison consume
        // exactly 2D+1 pairs before returning false.
        fn late_mismatch(depth: usize) -> Kind {
            Kind::Arrow(
                Box::new(left_heavy(depth - 1)),
                Box::new(Kind::Arrow(Box::new(Kind::Type), Box::new(Kind::Type))),
            )
        }

        std::thread::Builder::new()
            .name("left-heavy-kind-operations".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let kind = left_heavy(DEPTH);

                let mut clone_short = TypeWorkBudget::with_limit(KIND_NODES - 1);
                assert_eq!(clone_kind_with_budget(&kind, &mut clone_short), Err(()));
                assert_eq!(clone_short.used(), KIND_NODES - 1);
                let mut clone_exact = TypeWorkBudget::with_limit(KIND_NODES);
                let cloned = clone_kind_with_budget(&kind, &mut clone_exact)
                    .expect("the exact K-node left-heavy clone should fit");
                assert_eq!(clone_exact.used(), KIND_NODES);

                let mut equality_short = TypeWorkBudget::with_limit(KIND_NODES - 1);
                assert_eq!(
                    same_kind_with_budget(&kind, &cloned, &mut equality_short),
                    Err(()),
                );
                assert_eq!(equality_short.used(), KIND_NODES - 1);
                let mut equality_exact = TypeWorkBudget::with_limit(KIND_NODES);
                assert_eq!(
                    same_kind_with_budget(&kind, &cloned, &mut equality_exact),
                    Ok(true),
                );
                assert_eq!(equality_exact.used(), KIND_NODES);

                let mut short_hasher = DefaultHasher::new();
                17_u8.hash(&mut short_hasher);
                let untouched_hash = short_hasher.finish();
                let mut hash_short = TypeWorkBudget::with_limit(KIND_NODES - 1);
                assert_eq!(
                    hash_kind_with_budget(&kind, &mut short_hasher, &mut hash_short),
                    Err(()),
                );
                assert_eq!(hash_short.used(), KIND_NODES - 1);
                assert_eq!(short_hasher.finish(), untouched_hash);
                let mut exact_hasher = DefaultHasher::new();
                let mut hash_exact = TypeWorkBudget::with_limit(KIND_NODES);
                assert_eq!(
                    hash_kind_with_budget(&kind, &mut exact_hasher, &mut hash_exact),
                    Ok(()),
                );
                assert_eq!(hash_exact.used(), KIND_NODES);
                let mut cloned_hasher = DefaultHasher::new();
                cloned.hash(&mut cloned_hasher);
                assert_eq!(exact_hasher.finish(), cloned_hasher.finish());

                let mismatch = late_mismatch(DEPTH);
                let mut mismatch_short = TypeWorkBudget::with_limit(KIND_NODES - 1);
                assert_eq!(
                    same_kind_with_budget(&kind, &mismatch, &mut mismatch_short),
                    Err(()),
                    "one short must fail before the final mismatched pair",
                );
                assert_eq!(mismatch_short.used(), KIND_NODES - 1);
                let mut mismatch_exact = TypeWorkBudget::with_limit(KIND_NODES);
                assert_eq!(
                    same_kind_with_budget(&kind, &mismatch, &mut mismatch_exact),
                    Ok(false),
                );
                assert_eq!(mismatch_exact.used(), KIND_NODES);
                assert_left_heavy(&kind, DEPTH);
                assert_left_heavy(&cloned, DEPTH);
                let Kind::Arrow(mismatch_domain, mismatch_codomain) = &mismatch else {
                    panic!("the late mismatch root must remain an Arrow");
                };
                assert_left_heavy(mismatch_domain, DEPTH - 1);
                assert!(matches!(
                    mismatch_codomain.as_ref(),
                    Kind::Arrow(domain, codomain)
                        if matches!(domain.as_ref(), Kind::Type)
                            && matches!(codomain.as_ref(), Kind::Type)
                ));

                reset_kind_discard_observation();
                drop(cloned);
                assert_eq!(kind_discard_visits(), KIND_NODES);
                assert_eq!(kind_discard_pending(), 0);
                assert_eq!(kind_discard_pending_peak(), DEPTH + 1);
                drop(mismatch);
                drop(kind);
            })
            .expect("the left-heavy Kind thread should start")
            .join()
            .expect("all exact, one-short, mismatch, and teardown paths should fit 256 KiB");
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
    fn type_and_kind_disposal_have_exact_visits_and_bounded_pending_ownership() {
        const DEPTH: usize = 32_768;
        const WIDTH: usize = 32_768;
        // One nominal plus D Applications and D scalar arguments.
        const TYPE_APPLICATION_NODES: usize = 2 * DEPTH + 1;
        // One tuple wrapper plus W scalar elements.
        const TYPE_TUPLE_NODES: usize = WIDTH + 1;
        // D left-heavy Arrows plus D right Types and one base Type.
        const KIND_NODES: usize = 2 * DEPTH + 1;

        fn deep_application(depth: usize) -> Type {
            let owner = NominalTypeId::new(ModuleId::new(0), 0);
            Type::apply_arguments(Type::Nominal(owner), vec![Type::Unit; depth])
        }

        fn left_heavy_kind(depth: usize) -> Kind {
            let mut kind = Kind::Type;
            for _ in 0..depth {
                kind = Kind::Arrow(Box::new(kind), Box::new(Kind::Type));
            }
            kind
        }

        fn reject_owned_type(ty: Type) -> Result<(), ()> {
            let _partial = IterativeTypeOwner::new(ty);
            Err(())
        }

        fn reject_owned_kind(kind: Kind) -> Result<(), ()> {
            let _partial = kind;
            Err(())
        }

        std::thread::Builder::new()
            .name("exact-structural-disposal".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                reset_type_discard_observation();
                discard_type_iteratively(deep_application(DEPTH));
                assert_eq!(type_discard_visits(), TYPE_APPLICATION_NODES);
                assert_eq!(type_discard_pending(), 0);
                // Each visited left-spine Application leaves its argument pending.
                assert_eq!(type_discard_pending_peak(), DEPTH + 1);

                reset_type_discard_observation();
                discard_type_iteratively(Type::Tuple(vec![Type::Int; WIDTH].into_boxed_slice()));
                assert_eq!(type_discard_visits(), TYPE_TUPLE_NODES);
                assert_eq!(type_discard_pending(), 0);
                // The sequence iterator owns all W elements after consuming the wrapper.
                assert_eq!(type_discard_pending_peak(), WIDTH);

                reset_type_discard_observation();
                assert_eq!(reject_owned_type(deep_application(DEPTH)), Err(()));
                assert_eq!(type_discard_visits(), TYPE_APPLICATION_NODES);
                assert_eq!(type_discard_pending(), 0);
                assert_eq!(type_discard_pending_peak(), DEPTH + 1);

                reset_type_discard_observation();
                assert_eq!(
                    reject_owned_type(Type::Tuple(vec![Type::Int; WIDTH].into_boxed_slice())),
                    Err(()),
                );
                assert_eq!(type_discard_visits(), TYPE_TUPLE_NODES);
                assert_eq!(type_discard_pending(), 0);
                assert_eq!(type_discard_pending_peak(), WIDTH);

                reset_kind_discard_observation();
                drop(left_heavy_kind(DEPTH));
                assert_eq!(kind_discard_visits(), KIND_NODES);
                assert_eq!(kind_discard_pending(), 0);
                assert_eq!(kind_discard_pending_peak(), DEPTH + 1);

                reset_kind_discard_observation();
                assert_eq!(reject_owned_kind(left_heavy_kind(DEPTH)), Err(()));
                assert_eq!(kind_discard_visits(), KIND_NODES);
                assert_eq!(kind_discard_pending(), 0);
                assert_eq!(kind_discard_pending_peak(), DEPTH + 1);
            })
            .expect("the exact disposal thread should start")
            .join()
            .expect("accepted and rejected structural owners should dispose on 256 KiB");
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
        // One application plus two expanded scalar replacements.
        let mut exact = 3usize;
        let mut short = 2usize;

        let rebuilt = substitute_type_variables_with(
            &application,
            &replacements,
            |cells| {
                exact = exact.checked_sub(cells).ok_or(())?;
                Ok::<(), ()>(())
            },
            || (),
        )
        .expect("the exact rebuilt application should fit");
        assert_eq!(
            rebuilt,
            Type::Application(Box::new(Type::Nominal(owner)), Box::new(Type::Bool)),
        );
        assert_eq!(exact, 0);
        assert_eq!(
            substitute_type_variables_with(
                &application,
                &replacements,
                |cells| {
                    short = short.checked_sub(cells).ok_or(())?;
                    Ok::<(), ()>(())
                },
                || ()
            ),
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

        let result = substitute_type_variables_with(
            &source,
            &replacements,
            |cells| {
                remaining = remaining.checked_sub(cells).ok_or(())?;
                Ok(())
            },
            || (),
        );

        assert_eq!(result, Err(()));
        assert_eq!(remaining, 0);
    }

    #[test]
    fn nested_forall_substitution_uses_linear_active_shadow_counts() {
        const DEPTH: usize = 2_048;
        const WIDTH: usize = 2_048;
        // One overlapping replacement-key shadow-map record; D retained forall nodes,
        // binder records, and Kind nodes; enter and exit transitions for the
        // shadowed key at every depth; one tuple, one directly shadowed
        // variable, and W non-recursive replacement variables.
        const EXACT_WORK: usize = 1 + (3 * DEPTH) + (2 * DEPTH) + 1 + 1 + WIDTH;

        std::thread::Builder::new()
            .name("nested-forall-substitution-shadow-counts".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let shadowed = TypeVariableId::new(0);
                let substituted = TypeVariableId::new(1);
                let mut body = Type::Tuple(
                    std::iter::once(Type::Variable(shadowed))
                        .chain(std::iter::repeat_n(Type::Variable(substituted), WIDTH))
                        .collect::<Vec<_>>()
                        .into_boxed_slice(),
                );
                for _ in 0..DEPTH {
                    body = Type::Forall(Box::new([(shadowed, Kind::Type)]), Box::new(body));
                }
                let replacements = HashMap::from([
                    (shadowed, Type::Unit),
                    (substituted, Type::Variable(shadowed)),
                ]);

                let mut short = EXACT_WORK - 1;
                let short_result = substitute_type_variables_with(
                    &body,
                    &replacements,
                    |cells| {
                        short = short.checked_sub(cells).ok_or(())?;
                        Ok::<(), ()>(())
                    },
                    || (),
                );
                if let Ok(rebuilt) = short_result {
                    discard_type_iteratively(rebuilt);
                    panic!("the one-short source-plus-expansion budget unexpectedly fit");
                }
                assert_eq!(short, 0);

                for attempt in 0..2 {
                    let mut exact = EXACT_WORK;
                    let rebuilt = substitute_type_variables_with(
                        &body,
                        &replacements,
                        |cells| {
                            exact = exact.checked_sub(cells).ok_or(())?;
                            Ok::<(), ()>(())
                        },
                        || (),
                    )
                    .unwrap_or_else(|()| {
                        panic!("linear nested-forall attempt {attempt} should fit")
                    });
                    assert_eq!(exact, 0);
                    let mut current = &rebuilt;
                    for depth in 0..DEPTH {
                        let Type::Forall(parameters, inner) = current else {
                            panic!("forall layer {depth} is missing");
                        };
                        assert_eq!(parameters.as_ref(), [(shadowed, Kind::Type)]);
                        current = inner;
                    }
                    let Type::Tuple(elements) = current else {
                        panic!("the rebuilt nested body must remain a tuple");
                    };
                    assert_eq!(elements.len(), WIDTH + 1);
                    assert!(elements.iter().all(
                        |element| matches!(element, Type::Variable(found) if *found == shadowed)
                    ));
                    discard_type_iteratively(rebuilt);
                }
                discard_type_iteratively(body);
            })
            .expect("the nested-forall substitution thread should start")
            .join()
            .expect("nested-forall substitution should tear down on 256 KiB");
    }

    #[test]
    fn wide_unrelated_forall_parameter_inspection_is_exact_and_retryable() {
        const WIDTH: usize = 2_048;
        // One forall node, W binder records and W Kind nodes, and one scalar
        // replacement visit. Unrelated binders retain no shadow state.
        const EXACT_WORK: usize = 1 + (2 * WIDTH) + 1;

        let substituted = TypeVariableId::new(0);
        let source = Type::Forall(
            (0..WIDTH)
                .map(|index| {
                    (
                        TypeVariableId::new(
                            u32::try_from(index + 1).expect("the test width fits in u32"),
                        ),
                        Kind::Type,
                    )
                })
                .collect::<Vec<_>>()
                .into_boxed_slice(),
            Box::new(Type::Variable(substituted)),
        );
        let replacements = HashMap::from([(substituted, Type::Unit)]);

        let mut short = EXACT_WORK - 1;
        let short_result = substitute_type_variables_with(
            &source,
            &replacements,
            |cells| {
                short = short.checked_sub(cells).ok_or(())?;
                Ok::<(), ()>(())
            },
            || (),
        );
        if let Ok(rebuilt) = short_result {
            discard_type_iteratively(rebuilt);
            panic!("the one-short unrelated-binder inspection budget unexpectedly fit");
        }
        assert_eq!(short, 0);

        for attempt in 0..2 {
            let mut exact = EXACT_WORK;
            let rebuilt = substitute_type_variables_with(
                &source,
                &replacements,
                |cells| {
                    exact = exact.checked_sub(cells).ok_or(())?;
                    Ok::<(), ()>(())
                },
                || (),
            )
            .unwrap_or_else(|()| panic!("exact unrelated-binder attempt {attempt} should fit"));
            assert_eq!(exact, 0);
            assert!(matches!(
                &rebuilt,
                Type::Forall(parameters, body)
                    if parameters.len() == WIDTH && matches!(body.as_ref(), Type::Unit)
            ));
            discard_type_iteratively(rebuilt);
        }
        discard_type_iteratively(source);
    }

    #[test]
    fn deep_and_wide_substitution_resource_boundaries_are_exact_and_reusable() {
        const DEPTH: usize = 32_768;
        const WIDTH: usize = 32_768;
        // Replacing the sole source variable retains every node of a left-deep
        // unary application: one nominal, D applications, and D arguments.
        const DEEP_RESULT_CELLS: usize = 2 * DEPTH + 1;
        // The tuple plus one scalar replacement per source element.
        const WIDE_RESULT_CELLS: usize = 1 + WIDTH;

        fn assert_deep_application(ty: &Type, depth: usize, owner: NominalTypeId) {
            let mut current = ty;
            for argument_index in (0..depth).rev() {
                let Type::Application(function, argument) = current else {
                    panic!("application argument {argument_index} is missing");
                };
                assert!(
                    matches!(argument.as_ref(), Type::Unit),
                    "application argument {argument_index} must remain Unit",
                );
                current = function;
            }
            assert!(
                matches!(current, Type::Nominal(found) if *found == owner),
                "the application spine must end at its original nominal",
            );
        }

        std::thread::Builder::new()
            .name("deep-wide-substitution-budget".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let parameter = TypeVariableId::new(0);
                let owner = NominalTypeId::new(ModuleId::new(0), 0);
                let source = Type::Variable(parameter);
                let mut replacements = HashMap::from([(
                    parameter,
                    Type::apply_arguments(Type::Nominal(owner), vec![Type::Unit; DEPTH]),
                )]);

                let mut deep_short = DEEP_RESULT_CELLS - 1;
                assert_eq!(
                    substitute_type_variables_with(&source, &replacements, |cells| {
                        deep_short = deep_short.checked_sub(cells).ok_or(())?;
                        Ok::<(), ()>(())
                    }, || ()),
                    Err(()),
                );
                assert_eq!(deep_short, 0);
                assert_deep_application(
                    replacements
                        .get(&parameter)
                        .expect("one-short substitution must retain its borrowed replacement"),
                    DEPTH,
                    owner,
                );

                let mut deep_exact = DEEP_RESULT_CELLS;
                let rebuilt = substitute_type_variables_with(
                    &source,
                    &replacements,
                    |cells| {
                        deep_exact = deep_exact.checked_sub(cells).ok_or(())?;
                        Ok::<(), ()>(())
                    },
                    || (),
                )
                .expect("the exact deep expanded-result budget should fit");
                assert_eq!(deep_exact, 0);
                assert_deep_application(&rebuilt, DEPTH, owner);
                discard_type_iteratively(rebuilt);
                discard_type_iteratively(
                    replacements
                        .remove(&parameter)
                        .expect("the reusable deep replacement should remain immutable"),
                );

                let wide_source = Type::Tuple(
                    vec![Type::Variable(parameter); WIDTH].into_boxed_slice(),
                );
                let wide_replacements = HashMap::from([(parameter, Type::Int)]);
                let mut wide_short = WIDE_RESULT_CELLS - 1;
                assert_eq!(
                    substitute_type_variables_with(&wide_source, &wide_replacements, |cells| {
                        wide_short = wide_short.checked_sub(cells).ok_or(())?;
                        Ok::<(), ()>(())
                    }, || ()),
                    Err(()),
                );
                assert_eq!(wide_short, 0);
                assert!(matches!(
                    &wide_source,
                    Type::Tuple(elements)
                        if elements.len() == WIDTH
                            && matches!(elements.first(), Some(Type::Variable(found)) if *found == parameter)
                ));

                let mut wide_exact = WIDE_RESULT_CELLS;
                let rebuilt = substitute_type_variables_with(
                    &wide_source,
                    &wide_replacements,
                    |cells| {
                        wide_exact = wide_exact.checked_sub(cells).ok_or(())?;
                        Ok::<(), ()>(())
                    },
                    || (),
                )
                .expect("the exact wide expanded-result budget should fit");
                assert_eq!(wide_exact, 0);
                assert!(matches!(
                    &rebuilt,
                    Type::Tuple(elements)
                        if elements.len() == WIDTH
                            && elements.iter().all(|element| matches!(element, Type::Int))
                ));
                discard_type_iteratively(rebuilt);
            })
            .expect("the deep/wide substitution thread should start")
            .join()
            .expect("partial and complete substitution results should tear down on 256 KiB");
    }

    #[test]
    fn effect_row_and_computation_clone_are_exact_atomic_and_retryable() {
        const ROW_CELLS: usize = 5;
        const COMPUTATION_CELLS: usize = 7;
        let member = EffectInstance::new(
            EffectId::new(ModuleId::new(0), 0),
            Box::new([Type::Tuple(Box::new([Type::Int, Type::Bool]))]),
        );
        let row = EffectRow::singleton(member);

        let mut row_short = TypeWorkBudget::with_limit(ROW_CELLS - 1);
        assert_eq!(clone_effect_row_with_budget(&row, &mut row_short), Err(()));
        assert_eq!(row.known().len(), 1);
        let mut row_exact = TypeWorkBudget::with_limit(ROW_CELLS);
        assert_eq!(
            clone_effect_row_with_budget(&row, &mut row_exact),
            Ok(row.clone()),
        );

        let computation = ComputationType::new(Type::Unit, row);
        let mut computation_short = TypeWorkBudget::with_limit(COMPUTATION_CELLS - 1);
        assert_eq!(
            clone_computation_type_with_budget(&computation, &mut computation_short),
            Err(()),
        );
        assert_eq!(computation.value(), &Type::Unit);
        let mut computation_exact = TypeWorkBudget::with_limit(COMPUTATION_CELLS);
        assert_eq!(
            clone_computation_type_with_budget(&computation, &mut computation_exact),
            Ok(computation),
        );
    }

    #[test]
    fn effect_row_equality_is_exact_retryable_and_deep() {
        fn row(depth: usize) -> EffectRow {
            let mut argument = Type::Unit;
            for _ in 0..depth {
                argument = Type::Application(Box::new(Type::Int), Box::new(argument));
            }
            EffectRow::open(
                EffectRowVariable::rigid(TypeVariableId::generated(0)),
                Box::new([EffectInstance::new(
                    EffectId::new(ModuleId::new(0), 0),
                    Box::new([argument]),
                )]),
            )
        }

        std::thread::Builder::new()
            .name("effect-row-equality-deep".to_owned())
            .stack_size(64 * 1024)
            .spawn(|| {
                let left = row(4_096);
                let right = row(4_096);
                let mut measured = TypeWorkBudget::unbounded();
                assert_eq!(
                    same_effect_rows_with_budget(&left, &right, &mut measured),
                    Ok(true),
                );
                let exact_work = measured.used();
                let mut short = TypeWorkBudget::with_limit(exact_work - 1);
                assert_eq!(
                    same_effect_rows_with_budget(&left, &right, &mut short),
                    Err(()),
                );
                for _ in 0..2 {
                    let mut exact = TypeWorkBudget::with_limit(exact_work);
                    assert_eq!(
                        same_effect_rows_with_budget(&left, &right, &mut exact),
                        Ok(true),
                    );
                    assert_eq!(exact.used(), exact_work);
                }
            })
            .expect("deep row-equality worker")
            .join()
            .expect("row equality must stay iterative");
    }

    #[test]
    fn row_algebra_owners_are_exact_atomic_and_retryable() {
        let effect = EffectId::new(ModuleId::new(0), 0);
        let left_member = EffectInstance::new(effect, Box::new([Type::Int]));
        let right_member = EffectInstance::new(effect, Box::new([Type::Bool]));
        let tail = EffectRowVariable::rigid(TypeVariableId::new(0));
        let left = EffectRow::with_tail(Box::new([left_member.clone()]), tail, Box::new([]));
        let right = EffectRow::with_tail(Box::new([right_member.clone()]), tail, Box::new([]));

        let mut union_measure = TypeWorkBudget::unbounded();
        let expected_union = left
            .union_with_budget(&right, &mut union_measure)
            .expect("the measured union should fit")
            .expect("the shared tail supplies both lacks facts");
        let union_work = union_measure.used();
        let mut union_short = TypeWorkBudget::with_limit(union_work - 1);
        assert_eq!(left.union_with_budget(&right, &mut union_short), Err(()));
        assert_eq!(left.known(), std::slice::from_ref(&left_member));
        let mut union_exact = TypeWorkBudget::with_limit(union_work);
        let union = left
            .union_with_budget(&right, &mut union_exact)
            .expect("the exact union budget should fit")
            .expect("the shared tail supplies both lacks facts");
        assert_eq!(union, expected_union);
        assert_eq!(union_exact.used(), union_work);

        let mut removal_measure = TypeWorkBudget::unbounded();
        let expected_removal = union
            .remove_exact_with_budget(&left_member, &mut removal_measure)
            .expect("the measured removal should fit");
        let removal_work = removal_measure.used();
        let mut removal_short = TypeWorkBudget::with_limit(removal_work - 1);
        assert_eq!(
            union.remove_exact_with_budget(&left_member, &mut removal_short),
            Err(()),
        );
        let mut removal_exact = TypeWorkBudget::with_limit(removal_work);
        let removed = EffectRow::with_tail(
            Box::new([right_member.clone()]),
            tail,
            Box::new([left_member.clone(), right_member]),
        );
        assert_eq!(
            union
                .remove_exact_with_budget(&left_member, &mut removal_exact)
                .expect("the exact removal budget should fit"),
            Ok(removed.clone()),
        );
        assert_eq!(expected_removal, Ok(removed));
        assert_eq!(removal_exact.used(), removal_work);

        let open = EffectRow::open(tail, Box::new([]));
        let replacement = EffectRow::singleton(left_member.clone());
        let mut tail_measure = TypeWorkBudget::unbounded();
        let expected_tail = open
            .substitute_tail_once_with_budget(tail, &replacement, &mut tail_measure)
            .expect("the measured tail substitution should fit");
        let tail_work = tail_measure.used();
        let mut tail_short = TypeWorkBudget::with_limit(tail_work - 1);
        assert_eq!(
            open.substitute_tail_once_with_budget(tail, &replacement, &mut tail_short),
            Err(()),
        );
        let mut tail_exact = TypeWorkBudget::with_limit(tail_work);
        assert_eq!(
            open.substitute_tail_once_with_budget(tail, &replacement, &mut tail_exact),
            Ok(Ok(replacement.clone())),
        );
        assert_eq!(expected_tail, Ok(replacement.clone()));
        assert_eq!(tail_exact.used(), tail_work);

        let mut map_measure = TypeWorkBudget::unbounded();
        replacement
            .map_type_arguments_with_budget(clone_type_with_budget, &mut map_measure)
            .expect("the measured row-argument map should fit");
        let map_work = map_measure.used();
        let mut map_short = TypeWorkBudget::with_limit(map_work - 1);
        assert_eq!(
            replacement.map_type_arguments_with_budget(clone_type_with_budget, &mut map_short,),
            Err(()),
        );
        let mut map_exact = TypeWorkBudget::with_limit(map_work);
        assert_eq!(
            replacement.map_type_arguments_with_budget(clone_type_with_budget, &mut map_exact,),
            Ok(replacement),
        );
        assert_eq!(map_exact.used(), map_work);

        let substituted = EffectRow::singleton(EffectInstance::new(
            effect,
            Box::new([Type::Variable(TypeVariableId::new(1))]),
        ));
        let replacements = HashMap::from([(TypeVariableId::new(1), Type::Bool)]);
        let mut substitution_measure = TypeWorkBudget::unbounded();
        substituted
            .substitute_type_variables_with_budget(&replacements, &mut substitution_measure)
            .expect("the measured row substitution should fit");
        let substitution_work = substitution_measure.used();
        let mut substitution_short = TypeWorkBudget::with_limit(substitution_work - 1);
        assert_eq!(
            substituted
                .substitute_type_variables_with_budget(&replacements, &mut substitution_short,),
            Err(()),
        );
        assert!(matches!(
            substituted.known()[0].arguments(),
            [Type::Variable(_)]
        ));
        let mut substitution_exact = TypeWorkBudget::with_limit(substitution_work);
        assert_eq!(
            substituted
                .substitute_type_variables_with_budget(&replacements, &mut substitution_exact,),
            Ok(EffectRow::singleton(EffectInstance::new(
                effect,
                Box::new([Type::Bool]),
            ))),
        );
        assert_eq!(substitution_exact.used(), substitution_work);
    }

    #[test]
    fn row_union_charges_pending_membership_and_canonical_comparisons() {
        let effect = EffectId::new(ModuleId::new(0), 0);
        let member = EffectInstance::new(effect, Box::new([Type::Int]));
        let tail = EffectRowVariable::rigid(TypeVariableId::new(0));
        let left = EffectRow::with_tail(Box::new([member.clone()]), tail, Box::new([]));
        let right = EffectRow::with_tail(Box::new([member.clone()]), tail, Box::new([]));

        let mut measured = TypeWorkBudget::unbounded();
        let union = left
            .union_with_budget(&right, &mut measured)
            .expect("the measured union should fit")
            .expect("equal closed members have a principal union");
        let exact = measured.used();
        assert!(
            exact > 5,
            "the row, two candidate members, and their arguments cost five cells before membership and canonical comparisons"
        );
        assert_eq!(union, left);

        let mut one_short = TypeWorkBudget::with_limit(exact - 1);
        assert_eq!(left.union_with_budget(&right, &mut one_short), Err(()));
        assert_eq!(left.known(), std::slice::from_ref(&member));

        let mut retry = TypeWorkBudget::with_limit(exact);
        assert_eq!(left.union_with_budget(&right, &mut retry), Ok(Ok(left)));
        assert_eq!(retry.used(), exact);
    }

    #[test]
    fn effectful_function_closed_operations_share_one_exact_cell_formula() {
        const CELLS: usize = 7;
        let ty = Type::function_computation(
            Type::Unit,
            ComputationType::new(
                Type::Bool,
                EffectRow::singleton(EffectInstance::new(
                    EffectId::new(ModuleId::new(0), 0),
                    Box::new([Type::Int]),
                )),
            ),
        );

        let mut clone_short = TypeWorkBudget::with_limit(CELLS - 1);
        assert_eq!(clone_type_with_budget(&ty, &mut clone_short), Err(()));
        let mut clone_exact = TypeWorkBudget::with_limit(CELLS);
        assert_eq!(
            clone_type_with_budget(&ty, &mut clone_exact),
            Ok(ty.clone())
        );

        let mut equality_short = TypeWorkBudget::with_limit(CELLS - 1);
        assert_eq!(
            same_type_with_budget(&ty, &ty, &mut equality_short),
            Err(()),
        );
        let mut equality_exact = TypeWorkBudget::with_limit(CELLS);
        assert_eq!(
            same_type_with_budget(&ty, &ty, &mut equality_exact),
            Ok(true),
        );

        let mut render_short = TypeWorkBudget::with_limit(CELLS - 1);
        assert_eq!(render_type_with_budget(&ty, &mut render_short), Err(()));
        let mut render_exact = TypeWorkBudget::with_limit(CELLS);
        assert!(render_type_with_budget(&ty, &mut render_exact).is_ok());

        let mut hash_short = TypeWorkBudget::with_limit(CELLS - 1);
        let mut short_hasher = DefaultHasher::new();
        assert_eq!(
            hash_type_with_budget(&ty, &mut short_hasher, &mut hash_short),
            Err(()),
        );
        let mut hash_exact = TypeWorkBudget::with_limit(CELLS);
        let mut exact_hasher = DefaultHasher::new();
        assert_eq!(
            hash_type_with_budget(&ty, &mut exact_hasher, &mut hash_exact),
            Ok(()),
        );
    }

    #[test]
    fn nested_row_arguments_clone_and_substitute_on_a_small_stack() {
        const DEPTH: usize = 8_192;

        std::thread::Builder::new()
            .name("nested-row-operations".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let parameter = TypeVariableId::new(0);
                let effect = EffectId::new(ModuleId::new(0), 0);
                let mut nested = Type::Variable(parameter);
                for _ in 0..DEPTH {
                    nested = Type::function_computation(
                        Type::Unit,
                        ComputationType::new(
                            Type::Unit,
                            EffectRow::singleton(EffectInstance::new(effect, Box::new([nested]))),
                        ),
                    );
                }
                let row = EffectRow::singleton(EffectInstance::new(effect, Box::new([nested])));

                let mut budget = TypeWorkBudget::default();
                let cloned = clone_effect_row_with_budget(&row, &mut budget)
                    .expect("the nested row clone should stay iterative");
                assert_eq!(cloned, row);

                let substituted =
                    row.substitute_type_variables(&HashMap::from([(parameter, Type::Int)]));
                assert_ne!(substituted, row);
                drop(substituted);
                drop(cloned);
                drop(row);
            })
            .expect("the nested-row test thread should start")
            .join()
            .expect("row clone, substitution, and disposal should fit a 256 KiB stack");
    }

    #[test]
    fn effectful_substitution_preflights_known_row_argument_work() {
        assert_effectful_substitution_preflights_row_arguments(false);
    }

    #[test]
    fn effectful_substitution_preflights_lacks_row_argument_work() {
        assert_effectful_substitution_preflights_row_arguments(true);
    }

    fn assert_effectful_substitution_preflights_row_arguments(lacks: bool) {
        for width in [16, 4_096] {
            let parameter = TypeVariableId::new(0);
            let instance = EffectInstance::new(
                EffectId::new(ModuleId::new(0), 0),
                vec![Type::Unit; width].into_boxed_slice(),
            );
            let row = if lacks {
                EffectRow::open(EffectRowVariable::rigid(parameter), Box::new([instance]))
            } else {
                EffectRow::singleton(instance)
            };
            let source =
                Type::function_computation(Type::Unit, ComputationType::new(Type::Unit, row));
            let mut work = TypeWorkBudget::with_limit(if lacks { 5 } else { 4 });
            let mut charges = Vec::new();
            assert_eq!(
                substitute_type_and_row_variables_with(
                    &source,
                    &HashMap::from([(parameter, Type::Bool)]),
                    &HashMap::new(),
                    |cells| {
                        charges.push(cells);
                        work.charge(cells)
                    },
                    || (),
                ),
                Err(()),
            );
            assert_eq!(
                charges,
                if lacks {
                    vec![3, 0, 1, 1, width]
                } else {
                    vec![3, 1, width]
                },
                "the complete argument queue must be admitted before any argument traversal",
            );
        }
    }

    #[test]
    fn effectful_substitution_row_queue_is_exact_simultaneous_and_drops_deep_failure() {
        std::thread::Builder::new()
            .name("effectful-substitution-row-queue".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                const DEPTH: usize = 32_000;
                let first = TypeVariableId::new(0);
                let second = TypeVariableId::new(1);
                let row_parameter = TypeVariableId::new(2);
                let mut deep = Type::Unit;
                for _ in 0..DEPTH {
                    deep = Type::Application(Box::new(Type::Unit), Box::new(deep));
                }
                let row = EffectRow::with_tail(
                    Box::new([EffectInstance::new(
                        EffectId::new(ModuleId::new(0), 0),
                        Box::new([deep, Type::Variable(first)]),
                    )]),
                    EffectRowVariable::rigid(row_parameter),
                    Box::new([EffectInstance::new(
                        EffectId::new(ModuleId::new(0), 1),
                        Box::new([Type::Variable(second)]),
                    )]),
                );
                let source = IterativeTypeOwner::new(Type::function_computation(
                    Type::Unit,
                    ComputationType::new(Type::Unit, row),
                ));
                let replacements =
                    HashMap::from([(first, Type::Variable(second)), (second, Type::Bool)]);
                let substitute = |work: &mut TypeWorkBudget| {
                    substitute_type_and_row_variables_with(
                        &source,
                        &replacements,
                        &HashMap::new(),
                        |cells| work.charge(cells),
                        || (),
                    )
                };
                // Seven shape cells, five queued arguments, two function children,
                // and the first deep argument are retained before the next failure.
                let mut partial = TypeWorkBudget::with_limit(2 * DEPTH + 15);
                assert_eq!(substitute(&mut partial), Err(()));
                assert_eq!(partial.used(), 2 * DEPTH + 15);
                let mut measured = TypeWorkBudget::unbounded();
                discard_type_iteratively(substitute(&mut measured).unwrap().unwrap());
                assert_eq!(
                    substitute(&mut TypeWorkBudget::with_limit(measured.used() - 1)),
                    Err(()),
                );
                for _ in 0..2 {
                    let mut exact = TypeWorkBudget::with_limit(measured.used());
                    let substituted =
                        IterativeTypeOwner::new(substitute(&mut exact).unwrap().unwrap());
                    assert_eq!(exact.used(), measured.used());
                    let Type::EffectfulFunction(_, computation) = &*substituted else {
                        panic!("the open row remains effectful");
                    };
                    assert_eq!(
                        computation.effects.known[0].arguments[1],
                        Type::Variable(second),
                        "replacement values must not be substituted a second time",
                    );
                    let tail = computation.effects.tail.as_ref().unwrap();
                    assert_eq!(tail.lacks[1].arguments[0], Type::Bool);
                }
            })
            .expect("the row-queue thread should start")
            .join()
            .expect("partial row-queue reconstruction must be disposed iteratively");
    }

    #[test]
    fn row_identity_substitution_adds_exclusions_without_admitting_recursion() {
        let binder = TypeVariableId::new(0);
        let variable = EffectRowVariable::rigid(binder);
        let member = EffectInstance::new(EffectId::new(ModuleId::new(0), 0), Box::new([Type::Int]));
        let row = EffectRow::open(variable, Box::new([]));
        let source =
            Type::function_computation(Type::Unit, ComputationType::new(Type::Int, row.clone()));
        let replacement = EffectRow::open(variable, Box::new([member.clone()]));
        let substituted = substitute_type_and_row_variables_with(
            &source,
            &HashMap::new(),
            &HashMap::from([(binder, replacement.clone())]),
            |_| Ok::<(), ()>(()),
            || (),
        )
        .unwrap()
        .unwrap();
        assert_eq!(
            substituted.function_view().unwrap().effects().unwrap(),
            &replacement
        );
        let recursive = effect_row_from_owned_parts_with_budget(
            vec![member],
            Some((variable, Vec::new())),
            &mut TypeWorkBudget::unbounded(),
        )
        .unwrap();
        assert_eq!(
            row.substitute_tail_once_with_budget(
                variable,
                &recursive,
                &mut TypeWorkBudget::unbounded()
            ),
            Ok(Err(EffectRowError::Infinite))
        );
        assert_eq!(
            substitute_type_and_row_variables_with(
                &source,
                &HashMap::new(),
                &HashMap::from([(binder, recursive)]),
                |_| Ok::<(), ()>(()),
                || (),
            ),
            Ok(Err(EffectRowError::Infinite))
        );
    }

    #[test]
    fn type_substitution_replaces_one_row_binder_with_complete_rows() {
        let binder = TypeVariableId::new(0);
        let effect = EffectId::new(ModuleId::new(0), 0);
        let member = EffectInstance::new(effect, Box::new([Type::Int]));
        let source = Type::function_computation(
            Type::Unit,
            ComputationType::new(
                Type::Bool,
                EffectRow::open(EffectRowVariable::rigid(binder), Box::new([member.clone()])),
            ),
        );
        assert_eq!(
            substitute_type_and_row_variables_with(
                &source,
                &HashMap::new(),
                &HashMap::from([(binder, EffectRow::singleton(member.clone()))]),
                |_| Ok::<(), ()>(()),
                || (),
            ),
            Ok(Err(EffectRowError::Missing)),
        );
        let replacement = EffectRow::open(
            EffectRowVariable::rigid(TypeVariableId::new(1)),
            Box::new([member]),
        );
        let substituted = substitute_type_and_row_variables_with(
            &source,
            &HashMap::new(),
            &HashMap::from([(binder, replacement.clone())]),
            |_| Ok::<(), ()>(()),
            || (),
        )
        .unwrap()
        .unwrap();
        let Type::EffectfulFunction(_, computation) = substituted else {
            panic!()
        };
        assert_eq!(computation.effects(), &replacement);

        let replacements = HashMap::from([(binder, replacement)]);
        let mut measured = TypeWorkBudget::default();
        substitute_type_and_row_variables_with(
            &source,
            &HashMap::new(),
            &replacements,
            |cells| measured.charge(cells),
            || (),
        )
        .unwrap()
        .unwrap();
        let exact = measured.used();
        let mut short = TypeWorkBudget::with_limit(exact - 1);
        assert!(
            substitute_type_and_row_variables_with(
                &source,
                &HashMap::new(),
                &replacements,
                |cells| short.charge(cells),
                || (),
            )
            .is_err()
        );
        for _ in 0..2 {
            let mut retry = TypeWorkBudget::with_limit(exact);
            substitute_type_and_row_variables_with(
                &source,
                &HashMap::new(),
                &replacements,
                |cells| retry.charge(cells),
                || (),
            )
            .unwrap()
            .unwrap();
            assert_eq!(retry.used(), exact);
        }

        let deep = || {
            (0..1_024).fold(Type::Unit, |ty, _| {
                Type::Application(Box::new(Type::Unit), Box::new(ty))
            })
        };
        let instance = |ordinal| {
            EffectInstance::new(EffectId::new(ModuleId::new(0), ordinal), Box::new([deep()]))
        };
        let deep_source = Type::function_computation(
            Type::Unit,
            ComputationType::new(
                Type::Bool,
                EffectRow::with_tail(
                    Box::new([instance(1), instance(2)]),
                    EffectRowVariable::rigid(binder),
                    Box::new([instance(3), instance(4)]),
                ),
            ),
        );
        let mut prefix = TypeWorkBudget::default();
        charge_type_cells(&deep_source, &mut prefix).unwrap();
        let mut short = TypeWorkBudget::with_limit(prefix.used());
        let mut rejected = None;
        assert!(
            substitute_type_and_row_variables_with(
                &deep_source,
                &HashMap::new(),
                &HashMap::from([(
                    binder,
                    EffectRow::open(EffectRowVariable::rigid(binder), Box::new([])),
                )]),
                |cells| {
                    if short.charge(cells).is_err() {
                        rejected = Some(cells);
                        Err(())
                    } else {
                        Ok(())
                    }
                },
                || (),
            )
            .is_err()
        );
        assert_eq!(rejected, Some(1), "failure must interrupt row work");

        let deep_replacements = HashMap::from([(binder, EffectRow::empty())]);
        let mut measured = TypeWorkBudget::default();
        substitute_type_and_row_variables_with(
            &deep_source,
            &HashMap::new(),
            &deep_replacements,
            |cells| measured.charge(cells),
            || (),
        )
        .unwrap()
        .unwrap();
        for _ in 0..2 {
            let mut retry = TypeWorkBudget::with_limit(measured.used());
            substitute_type_and_row_variables_with(
                &deep_source,
                &HashMap::new(),
                &deep_replacements,
                |cells| retry.charge(cells),
                || (),
            )
            .unwrap()
            .unwrap();
            assert_eq!(retry.used(), measured.used());
        }
    }

    #[test]
    fn charged_row_rebuild_failure_discards_staged_arguments_on_a_small_stack() {
        const DEPTH: usize = 4_096;
        const FIRST_ARGUMENT_WORK: usize = 2 * DEPTH + 1;

        std::thread::Builder::new()
            .name("failed-row-rebuild".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let mut deep = Type::Unit;
                for _ in 0..DEPTH {
                    deep = Type::Application(Box::new(Type::Unit), Box::new(deep));
                }
                let row = EffectRow::singleton(EffectInstance::new(
                    EffectId::new(ModuleId::new(0), 0),
                    Box::new([deep, Type::Bool]),
                ));
                let mut short = TypeWorkBudget::with_limit(2 + FIRST_ARGUMENT_WORK);
                assert_eq!(
                    row.map_type_arguments_with_budget(clone_type_with_budget, &mut short,),
                    Err(()),
                );
                drop(row);
            })
            .expect("the failed row-rebuild thread should start")
            .join()
            .expect("a partial row rebuild should dismantle staged arguments iteratively");
    }
}
