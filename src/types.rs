//! Structural types shared by elaboration and Core.

use std::{
    borrow::Borrow,
    cmp::Ordering,
    collections::HashMap,
    fmt,
    hash::{Hash, Hasher},
};

use crate::module::ModuleId;

mod owner_arguments;
pub(crate) use owner_arguments::{
    IterativeArgumentOwner, clone_kinded_argument_with_budget, clone_kinded_arguments_with_budget,
    discard_kinded_argument_iteratively, extend_owner_type_children_with_charge,
    extend_owner_type_pairs_with_charge, map_kinded_argument_types_with_budget,
    type_arguments_to_kinded_with_budget, visit_owner_components_with_charge,
    visit_owner_type_children_with_charge, visit_owner_type_pairs_with_charge,
};
use owner_arguments::{
    StructuralRoot, StructuralValue, charge_structural, clone_kind_precharged, clone_structural,
    clone_structural_with_failure, discard_row_iteratively,
};

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
            limit: crate::calibration::limit(
                TYPE_WORK_LIMIT,
                crate::calibration::DiagnosticOwner::Structural,
            ),
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

    pub(crate) const fn limit(&self) -> usize {
        self.limit
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

    // A bounded sizing phase may admit an input-derived TOTAL. Every sizing
    // charge remains in that total; this never resets or adds spent work.
    pub(crate) fn finish_sizing(&mut self, total: usize) -> Result<(), ()> {
        if self.used > total {
            return Err(());
        }
        self.limit = total;
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

pub(crate) fn allocation_error<B: TypeWorkMeter>(budget: &mut B) -> B::Error {
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
    charge_structural(StructuralRoot::Type(ty), budget)
}

pub(crate) fn charge_kinded_argument_with_budget<B: TypeWorkMeter>(
    argument: &KindedArgument,
    budget: &mut B,
) -> Result<(), B::Error> {
    charge_structural(StructuralRoot::Argument(argument), budget)
}

pub(crate) fn charge_effect_row_cells<B: TypeWorkMeter>(
    row: &EffectRow,
    budget: &mut B,
) -> Result<(), B::Error> {
    charge_structural(StructuralRoot::Row(row), budget)
}

pub(crate) fn clone_effect_row_with_budget<B: TypeWorkMeter>(
    row: &EffectRow,
    budget: &mut B,
) -> Result<EffectRow, B::Error> {
    clone_effect_row_with_budget_and_failure(row, budget, allocation_error)
}

pub(crate) fn clone_effect_row_with_budget_and_failure<B: TypeWorkMeter>(
    row: &EffectRow,
    budget: &mut B,
    mut storage_error: impl FnMut(&mut B) -> B::Error,
) -> Result<EffectRow, B::Error> {
    Ok(
        clone_structural_with_failure(StructuralRoot::Row(row), budget, &mut storage_error)?
            .into_row()
            .expect("row root shape"),
    )
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
    Ok(clone_structural(StructuralRoot::Type(ty), budget)?
        .into_type()
        .expect("type root shape"))
}

fn clone_type(ty: &Type) -> Type {
    let mut unbounded = TypeWorkBudget::unbounded();
    match clone_type_with_budget(ty, &mut unbounded) {
        Ok(cloned) => cloned,
        Err(()) => unreachable!("an in-memory type cannot exceed the address-space work bound"),
    }
}

#[derive(Clone, Copy)]
pub(crate) enum TypeStructureNode<'a> {
    Type(&'a Type),
    Tail(&'a EffectRowTail),
}

/// Visits all Type payloads and row tails, including recursively nested owner
/// arguments and lacks members, without recursing on the Rust stack.
pub(crate) fn visit_type_structure_with_budget<B: TypeWorkMeter>(
    root: &Type,
    budget: &mut B,
    visit: impl FnMut(TypeStructureNode<'_>, &mut B) -> Result<bool, B::Error>,
) -> Result<bool, B::Error> {
    visit_structural_components(StructuralRoot::Type(root), budget, visit, |_, _| Ok(false))
}

pub(crate) fn visit_argument_structure_with_budget<B: TypeWorkMeter>(
    root: &KindedArgument,
    budget: &mut B,
    visit: impl FnMut(TypeStructureNode<'_>, &mut B) -> Result<bool, B::Error>,
) -> Result<bool, B::Error> {
    visit_structural_components(StructuralRoot::Argument(root), budget, visit, |_, _| {
        Ok(false)
    })
}

/// Includes each complete effect identity inside known and lacks rows, even
/// when those rows occur only as owner arguments. Uses the same paid worklist.
pub(crate) fn visit_type_structure_and_instances_with_budget<B: TypeWorkMeter>(
    root: &Type,
    budget: &mut B,
    visit: impl FnMut(TypeStructureNode<'_>, &mut B) -> Result<bool, B::Error>,
    visit_instance: impl FnMut(&EffectInstance, &mut B) -> Result<bool, B::Error>,
) -> Result<bool, B::Error> {
    visit_structural_components(StructuralRoot::Type(root), budget, visit, visit_instance)
}

fn visit_structural_components<B: TypeWorkMeter>(
    root: StructuralRoot<'_>,
    budget: &mut B,
    mut visit: impl FnMut(TypeStructureNode<'_>, &mut B) -> Result<bool, B::Error>,
    mut visit_instance: impl FnMut(&EffectInstance, &mut B) -> Result<bool, B::Error>,
) -> Result<bool, B::Error> {
    let mut pending = Vec::new();
    fn push<'a, B: TypeWorkMeter>(
        pending: &mut Vec<StructuralRoot<'a>>,
        root: StructuralRoot<'a>,
        budget: &mut B,
    ) -> Result<(), B::Error> {
        budget.charge(1)?;
        pending
            .try_reserve(1)
            .map_err(|_| allocation_error(budget))?;
        pending.push(root);
        Ok(())
    }
    push(&mut pending, root, budget)?;
    while let Some(root) = pending.pop() {
        match root {
            StructuralRoot::Type(ty) => {
                if visit(TypeStructureNode::Type(ty), budget)? {
                    return Ok(true);
                }
                match ty {
                    Type::Tuple(elements) => {
                        for ty in elements.iter().rev() {
                            push(&mut pending, StructuralRoot::Type(ty), budget)?;
                        }
                    }
                    Type::ResourceApply(_, arguments) | Type::ForeignOwnerApply(_, arguments) => {
                        for argument in arguments.iter().rev() {
                            push(&mut pending, StructuralRoot::Argument(argument), budget)?;
                        }
                    }
                    Type::Application(left, right) | Type::Function(left, right) => {
                        push(&mut pending, StructuralRoot::Type(right), budget)?;
                        push(&mut pending, StructuralRoot::Type(left), budget)?;
                    }
                    Type::EffectfulFunction(domain, codomain) => {
                        push(
                            &mut pending,
                            StructuralRoot::Row(codomain.effects()),
                            budget,
                        )?;
                        push(&mut pending, StructuralRoot::Type(codomain.value()), budget)?;
                        push(&mut pending, StructuralRoot::Type(domain), budget)?;
                    }
                    Type::Forall(parameters, body) => {
                        charge_kinded_type_parameters(parameters, budget)?;
                        push(&mut pending, StructuralRoot::Type(body), budget)?;
                    }
                    Type::Bytes
                    | Type::String
                    | Type::Int
                    | Type::Bool
                    | Type::Unit
                    | Type::Nominal(_)
                    | Type::Variable(_)
                    | Type::Inference(_) => {}
                }
            }
            StructuralRoot::Argument(KindedArgument::TypeArg(ty)) => {
                push(&mut pending, StructuralRoot::Type(ty), budget)?
            }
            StructuralRoot::Argument(KindedArgument::RowArg(row)) => {
                push(&mut pending, StructuralRoot::Row(row), budget)?
            }
            StructuralRoot::Instance(instance) => {
                if visit_instance(instance, budget)? {
                    return Ok(true);
                }
                for argument in instance.arguments().iter().rev() {
                    push(&mut pending, StructuralRoot::Argument(argument), budget)?;
                }
            }
            StructuralRoot::Row(row) => {
                if let Some(tail) = row.tail() {
                    budget.charge(1)?;
                    if visit(TypeStructureNode::Tail(tail), budget)? {
                        return Ok(true);
                    }
                    for instance in tail.lacks().iter().rev() {
                        push(&mut pending, StructuralRoot::Instance(instance), budget)?;
                    }
                }
                for instance in row.known().iter().rev() {
                    push(&mut pending, StructuralRoot::Instance(instance), budget)?;
                }
            }
        }
    }
    Ok(false)
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

/// Defining identity of an experimental source resource assembly.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ResourceDefinitionId {
    module: ModuleId,
    ordinal: u32,
}

impl ResourceDefinitionId {
    /// Constructs a module-owned declaration identity.
    #[must_use]
    pub const fn new(module: ModuleId, ordinal: u32) -> Self {
        Self { module, ordinal }
    }
    /// Returns the defining module identity.
    #[must_use]
    pub const fn module(self) -> ModuleId {
        self.module
    }
    /// Returns the category-local declaration ordinal.
    #[must_use]
    pub const fn ordinal(self) -> u32 {
        self.ordinal
    }
}

/// One complete owner argument in declaration order. Rows are not value types.
pub enum KindedArgument {
    /// An ordinary value or constructor-kinded type argument.
    TypeArg(Type),
    /// One complete row, including its exact members, tail and lacks facts.
    RowArg(EffectRow),
}

impl fmt::Debug for KindedArgument {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write_structural_debug(StructuralRoot::Argument(self), formatter)
    }
}

impl fmt::Debug for EffectInstance {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write_structural_debug(StructuralRoot::Instance(self), formatter)
    }
}

impl fmt::Debug for Type {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write_structural_debug(StructuralRoot::Type(self), formatter)
    }
}

impl KindedArgument {
    pub(crate) fn outer_nominal(&self) -> Option<NominalTypeId> {
        match self {
            Self::TypeArg(ty) => ty.outer_nominal(),
            Self::RowArg(_) => None,
        }
    }
    pub(crate) fn is_bare_variable(&self) -> bool {
        match self {
            Self::TypeArg(Type::Variable(_)) => true,
            Self::RowArg(row) => {
                row.known().is_empty()
                    && matches!(
                        row.tail().map(|tail| tail.variable()),
                        Some(EffectRowVariable::Rigid(_))
                    )
            }
            _ => false,
        }
    }
}

impl Clone for KindedArgument {
    fn clone(&self) -> Self {
        clone_kinded_argument_with_budget(self, &mut TypeWorkBudget::unbounded())
            .expect("an in-memory argument fits the address-space work bound")
    }
}

impl PartialEq for KindedArgument {
    fn eq(&self, other: &Self) -> bool {
        compare_kinded_arguments_with_budget(self, other, &mut TypeWorkBudget::unbounded())
            .expect("an in-memory argument comparison fits the address-space work bound")
            == Ordering::Equal
    }
}
impl Eq for KindedArgument {}

impl Hash for KindedArgument {
    fn hash<H: Hasher>(&self, state: &mut H) {
        hash_type_or_effect_row(TypeHashTask::Argument(self), state);
    }
}

impl fmt::Display for KindedArgument {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write_structural(StructuralRoot::Argument(self), formatter)
    }
}

/// One exact effect application in a computation row.
#[derive(Clone, Eq, Hash, PartialEq)]
pub struct EffectInstance {
    effect: EffectId,
    arguments: Box<[KindedArgument]>,
}

impl EffectInstance {
    pub(crate) fn from_type_arguments_with_budget<B: TypeWorkMeter>(
        effect: EffectId,
        arguments: Box<[Type]>,
        budget: &mut B,
    ) -> Result<Self, B::Error> {
        Ok(Self::new_kinded(
            effect,
            type_arguments_to_kinded_with_budget(arguments, budget)?,
        ))
    }

    /// Creates one exact effect instance from its stable identity and arguments.
    #[must_use]
    pub fn new(effect: EffectId, arguments: Box<[Type]>) -> Self {
        // Public Type-only construction. Compiler-owned copies use the charged
        // argument-buffer path rather than this convenience adapter.
        let arguments = arguments
            .into_vec()
            .into_iter()
            .map(KindedArgument::TypeArg)
            .collect();
        Self { effect, arguments }
    }

    /// Creates an exact application with complete tagged owner arguments.
    #[must_use]
    pub const fn new_kinded(effect: EffectId, arguments: Box<[KindedArgument]>) -> Self {
        Self { effect, arguments }
    }

    /// Returns the stable effect declaration identity.
    #[must_use]
    pub const fn effect(&self) -> EffectId {
        self.effect
    }

    /// Borrows the complete ordered type arguments.
    #[must_use]
    pub const fn arguments(&self) -> &[KindedArgument] {
        &self.arguments
    }

    pub(crate) fn into_parts(mut self) -> (EffectId, Box<[KindedArgument]>) {
        (self.effect, std::mem::take(&mut self.arguments))
    }
}

impl Drop for EffectInstance {
    fn drop(&mut self) {
        for argument in std::mem::take(&mut self.arguments).into_vec() {
            discard_kinded_argument_iteratively(argument);
        }
    }
}

pub(crate) fn clone_effect_instance_with_budget(
    instance: &EffectInstance,
    budget: &mut TypeWorkBudget,
) -> Result<EffectInstance, ()> {
    clone_structural(StructuralRoot::Instance(instance), budget)?.into_instance()
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

    pub(crate) fn substitute_type_variables_borrowed_with_budget(
        &self,
        replacements: &HashMap<TypeVariableId, &Type>,
        budget: &mut TypeWorkBudget,
    ) -> Result<Self, ()> {
        rebuild_effect_row_with_budget(
            self.known.iter(),
            self.tail.as_ref().map(|tail| tail.variable),
            self.tail.iter().flat_map(|tail| tail.lacks.iter()),
            |argument, budget| {
                substitute_type_variables_borrowed_with(
                    argument,
                    replacements,
                    |cells| budget.charge(cells),
                    || (),
                )
            },
            budget,
        )
    }

    /// Consumes a freshly reconstructed row. Only the borrowed replacement
    /// needs cloning; all original members stay owned through canonicalization.
    fn substitute_owned_tail_for_reconstruction<B: TypeWorkMeter>(
        self,
        target: EffectRowVariable,
        replacement: &Self,
        budget: &mut B,
        mut storage_error: impl FnMut(&mut B) -> B::Error,
    ) -> Result<Result<Self, EffectRowError>, B::Error> {
        budget.charge(1)?;
        let Some(tail) = &self.tail else {
            return Ok(Ok(self));
        };
        if tail.variable != target {
            return Ok(Ok(self));
        }
        let identity = replacement.known.is_empty()
            && replacement
                .tail
                .as_ref()
                .is_some_and(|tail| tail.variable == target);
        if !identity {
            if replacement
                .tail
                .as_ref()
                .is_some_and(|tail| tail.variable == target)
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
        }
        let (known, tail) = self.into_parts();
        fn append<B: TypeWorkMeter>(
            mut owned: Vec<EffectInstance>,
            extra: &[EffectInstance],
            site: RowReservationSite,
            budget: &mut B,
            storage_error: &mut impl FnMut(&mut B) -> B::Error,
        ) -> Result<Vec<EffectInstance>, B::Error> {
            if !extra.is_empty() {
                // Reservation can relocate the original prefix. Existing members
                // keep their arguments; only the borrowed suffix is rebuilt.
                let count = owned
                    .len()
                    .checked_add(extra.len())
                    .ok_or_else(|| storage_error(budget))?;
                budget.charge(count)?;
                reserve_row(&mut owned, extra.len(), site).map_err(|_| storage_error(budget))?;
                let mut clone = clone_type_with_budget::<B>;
                for instance in extra {
                    owned.push(rebuild_effect_instance_with_budget_and_failure(
                        instance,
                        &mut clone,
                        budget,
                        storage_error,
                    )?);
                }
            }
            Ok(owned)
        }
        let known = append(
            known.into_vec(),
            &replacement.known,
            RowReservationSite::RebuildMembers,
            budget,
            &mut storage_error,
        )?;
        let tail = if let Some(replacement_tail) = &replacement.tail {
            let (_, original_lacks) = tail.expect("matched reconstructed tail");
            Some((
                replacement_tail.variable,
                append(
                    original_lacks.into_vec(),
                    &replacement_tail.lacks,
                    RowReservationSite::RebuildLacks,
                    budget,
                    &mut storage_error,
                )?,
            ))
        } else {
            None
        };
        effect_row_from_owned_parts_with_budget_and_failure(known, tail, budget, storage_error)
            .map(Ok)
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

    #[cfg(test)]
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

fn rebuild_effect_instance_with_budget_and_failure<E, B: TypeWorkMeter>(
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
        let argument = IterativeArgumentOwner::new(map_kinded_argument_types_with_budget(
            argument,
            map,
            budget,
            storage_error,
        )?);
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
    retained.extend(
        arguments
            .into_iter()
            .map(IterativeArgumentOwner::into_inner),
    );
    Ok(EffectInstance::new_kinded(
        instance.effect,
        retained.into_boxed_slice(),
    ))
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
    let mut rebuilt_known = Vec::new();
    for instance in known {
        let instance = rebuild_effect_instance_with_budget_and_failure(
            instance,
            &mut map,
            budget,
            &mut storage_error,
        )?;
        budget.charge(1).map_err(E::from)?;
        reserve_row(&mut rebuilt_known, 1, RowReservationSite::RebuildMembers)
            .map_err(|_| E::from(storage_error(budget)))?;
        rebuilt_known.push(instance);
    }
    let rebuilt_tail = if let Some(variable) = tail {
        let mut rebuilt_lacks = Vec::new();
        for instance in lacks {
            let instance = rebuild_effect_instance_with_budget_and_failure(
                instance,
                &mut map,
                budget,
                &mut storage_error,
            )?;
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
        let ordering = compare_structural_with_charge(
            StructuralRoot::Argument(left),
            StructuralRoot::Argument(right),
            charge,
            storage_error,
        )?;
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

pub(crate) fn same_kinded_argument_with_budget(
    left: &KindedArgument,
    right: &KindedArgument,
    budget: &mut TypeWorkBudget,
) -> Result<bool, ()> {
    compare_kinded_arguments_with_budget(left, right, budget)
        .map(|ordering| ordering == Ordering::Equal)
}

fn compare_kinded_arguments_with_budget(
    left: &KindedArgument,
    right: &KindedArgument,
    budget: &mut TypeWorkBudget,
) -> Result<Ordering, ()> {
    compare_structural_with_charge(
        StructuralRoot::Argument(left),
        StructuralRoot::Argument(right),
        budget,
        &mut allocation_error,
    )
}

pub(crate) fn compare_types_with_charge<B: TypeWorkMeter>(
    left: &Type,
    right: &Type,
    charge: &mut B,
    storage_error: &mut impl FnMut(&mut B) -> B::Error,
) -> Result<Ordering, B::Error> {
    compare_structural_with_charge(
        StructuralRoot::Type(left),
        StructuralRoot::Type(right),
        charge,
        storage_error,
    )
}

fn compare_structural_with_charge<B: TypeWorkMeter>(
    left: StructuralRoot<'_>,
    right: StructuralRoot<'_>,
    charge: &mut B,
    storage_error: &mut impl FnMut(&mut B) -> B::Error,
) -> Result<Ordering, B::Error> {
    enum Task<'a> {
        Types(&'a Type, &'a Type),
        Arguments(&'a KindedArgument, &'a KindedArgument),
        Kinds(&'a Kind, &'a Kind),
        Rows(&'a EffectRow, &'a EffectRow),
        Instances(&'a EffectInstance, &'a EffectInstance),
        KnownOrdering(Ordering),
    }

    fn type_tag(ty: &Type) -> u8 {
        match ty {
            Type::Bytes => 11,
            Type::String => 12,
            Type::Int => 0,
            Type::Bool => 1,
            Type::Unit => 2,
            Type::Tuple(_) => 3,
            Type::Nominal(_) => 4,
            Type::Variable(_) => 5,
            Type::Inference(_) => 6,
            Type::Application(_, _) => 7,
            Type::ResourceApply(_, _) => 10,
            Type::ForeignOwnerApply(_, _) => 13,
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
    match (left, right) {
        (StructuralRoot::Type(left), StructuralRoot::Type(right)) => {
            schedule!(Task::Types(left, right))
        }
        (StructuralRoot::Argument(left), StructuralRoot::Argument(right)) => {
            schedule!(Task::Arguments(left, right))
        }
        (StructuralRoot::Row(left), StructuralRoot::Row(right)) => {
            schedule!(Task::Rows(left, right))
        }
        (StructuralRoot::Instance(left), StructuralRoot::Instance(right)) => {
            schedule!(Task::Instances(left, right))
        }
        _ => unreachable!("comparison roots have the same structural category"),
    }
    while let Some(task) = work.pop() {
        let ordering = match task {
            Task::KnownOrdering(ordering) => ordering,
            Task::Arguments(left, right) => match (left, right) {
                (KindedArgument::TypeArg(left), KindedArgument::TypeArg(right)) => {
                    schedule!(Task::Types(left, right));
                    Ordering::Equal
                }
                (KindedArgument::RowArg(left), KindedArgument::RowArg(right)) => {
                    schedule!(Task::Rows(left, right));
                    Ordering::Equal
                }
                (KindedArgument::TypeArg(_), KindedArgument::RowArg(_)) => Ordering::Less,
                (KindedArgument::RowArg(_), KindedArgument::TypeArg(_)) => Ordering::Greater,
            },
            Task::Types(left, right) => {
                let tags = type_tag(left).cmp(&type_tag(right));
                if tags != Ordering::Equal {
                    tags
                } else {
                    match (left, right) {
                        (Type::Bytes, Type::Bytes)
                        | (Type::String, Type::String)
                        | (Type::Int, Type::Int)
                        | (Type::Bool, Type::Bool)
                        | (Type::Unit, Type::Unit) => Ordering::Equal,
                        (Type::Nominal(left), Type::Nominal(right)) => left.cmp(right),
                        (Type::Variable(left), Type::Variable(right)) => left.cmp(right),
                        (
                            Type::ForeignOwnerApply(left_id, left),
                            Type::ForeignOwnerApply(right_id, right),
                        ) => {
                            let identity = left_id.cmp(right_id);
                            if identity != Ordering::Equal {
                                return Ok(identity);
                            }
                            let lengths = left.len().cmp(&right.len());
                            if lengths == Ordering::Equal {
                                for (left, right) in left.iter().zip(right).rev() {
                                    schedule!(Task::Arguments(left, right));
                                }
                            }
                            lengths
                        }
                        (
                            Type::ResourceApply(left_id, left),
                            Type::ResourceApply(right_id, right),
                        ) => {
                            let identity = left_id.cmp(right_id);
                            if identity != Ordering::Equal {
                                return Ok(identity);
                            }
                            let lengths = left.len().cmp(&right.len());
                            if lengths == Ordering::Equal {
                                for (left, right) in left.iter().zip(right).rev() {
                                    schedule!(Task::Arguments(left, right));
                                }
                            }
                            lengths
                        }
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
                            Type::Function(_, _) | Type::EffectfulFunction(_, _),
                            Type::Function(_, _) | Type::EffectfulFunction(_, _),
                        ) => {
                            let left = left.function_view().expect("matched function family");
                            let right = right.function_view().expect("matched function family");
                            // Compare semantic function components in the same
                            // order for every representation. The latent-row
                            // decision must wait until domain and value work.
                            match (left.effects(), right.effects()) {
                                (Some(left), Some(right)) => schedule!(Task::Rows(left, right)),
                                (None, Some(_)) => schedule!(Task::KnownOrdering(Ordering::Less)),
                                (Some(_), None) => {
                                    schedule!(Task::KnownOrdering(Ordering::Greater))
                                }
                                (None, None) => {}
                            }
                            schedule!(Task::Types(left.value(), right.value()));
                            schedule!(Task::Types(left.domain(), right.domain()));
                            Ordering::Equal
                        }
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
                            schedule!(Task::Arguments(left, right));
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
        clone_effect_row_with_budget(self, &mut TypeWorkBudget::unbounded())
            .expect("an in-memory row fits the address-space work bound")
    }
}

impl PartialEq for EffectRow {
    fn eq(&self, other: &Self) -> bool {
        compare_structural_with_charge(
            StructuralRoot::Row(self),
            StructuralRoot::Row(other),
            &mut TypeWorkBudget::unbounded(),
            &mut allocation_error,
        )
        .expect("an in-memory row comparison fits the address-space work bound")
            == Ordering::Equal
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
        if self.known.is_empty() && self.tail.is_none() {
            return;
        }
        let row = EffectRow {
            known: std::mem::take(&mut self.known),
            tail: self.tail.take(),
        };
        discard_row_iteratively(row);
    }
}

impl fmt::Display for EffectRow {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write_structural(StructuralRoot::Row(self), formatter)
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

    pub(crate) fn effect_arguments(&self) -> impl DoubleEndedIterator<Item = &KindedArgument> {
        self.effects
            .known
            .iter()
            .chain(self.effects.tail.iter().flat_map(|tail| tail.lacks.iter()))
            .flat_map(|instance| instance.arguments.iter())
    }

    pub(crate) fn effect_argument_count(&self) -> usize {
        self.effect_arguments().count()
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
pub enum Type {
    /// Immutable packed arbitrary bytes.
    Bytes,
    /// Immutable packed valid UTF-8.
    String,
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
    /// One saturated row-bearing resource owner application.
    ResourceApply(ResourceDefinitionId, Box<[KindedArgument]>),
    /// One saturated row-bearing source foreign State or checked Access application.
    ForeignOwnerApply(NominalTypeId, Box<[KindedArgument]>),
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
                Self::Nominal(identity) | Self::ForeignOwnerApply(identity, _) => {
                    return Some(*identity);
                }
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

#[cfg(test)]
fn argument_type_child_count(arguments: &[KindedArgument]) -> usize {
    let mut pending: Vec<_> = arguments.iter().collect();
    let mut count = 0;
    while let Some(argument) = pending.pop() {
        match argument {
            KindedArgument::TypeArg(_) => count += 1,
            KindedArgument::RowArg(row) => {
                for instance in row
                    .known
                    .iter()
                    .chain(row.tail.iter().flat_map(|tail| tail.lacks.iter()))
                {
                    pending.extend(instance.arguments.iter());
                }
            }
        }
    }
    count
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
        Arguments(std::vec::IntoIter<KindedArgument>),
        Argument(KindedArgument),
        Row(EffectRow),
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
                Type::ResourceApply(_, arguments) | Type::ForeignOwnerApply(_, arguments) => {
                    argument_type_child_count(arguments)
                }
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
                        .map(|instance| argument_type_child_count(&instance.arguments))
                        .sum::<usize>()
                }
                Type::Forall(_, _) => 1,
                Type::Bytes
                | Type::String
                | Type::Int
                | Type::Bool
                | Type::Unit
                | Type::Nominal(_)
                | Type::Variable(_)
                | Type::Inference(_) => 0,
            };
            observe_type_discard_visit(children);
        }
        match task {
            Task::Visit(
                Type::ResourceApply(_, arguments) | Type::ForeignOwnerApply(_, arguments),
            ) => {
                work.push(Task::Arguments(arguments.into_vec().into_iter()));
            }
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
                Type::Bytes
                | Type::String
                | Type::Int
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
            Task::Arguments(mut remaining) => {
                if let Some(argument) = remaining.next() {
                    work.push(Task::Arguments(remaining));
                    work.push(Task::Argument(argument));
                }
            }
            Task::Argument(KindedArgument::TypeArg(ty)) => work.push(Task::Visit(ty)),
            Task::Argument(KindedArgument::RowArg(row)) => work.push(Task::Row(row)),
            Task::Row(mut row) => {
                let known = std::mem::take(&mut row.known).into_vec().into_iter();
                if let Some(tail) = row.tail.take() {
                    work.push(Task::EffectInstances(tail.lacks.into_vec().into_iter()));
                }
                work.push(Task::EffectInstances(known));
            }
            Task::EffectInstances(mut remaining) => {
                if let Some(mut instance) = remaining.next() {
                    let arguments = std::mem::take(&mut instance.arguments)
                        .into_vec()
                        .into_iter();
                    drop(instance);
                    work.push(Task::EffectInstances(remaining));
                    work.push(Task::Arguments(arguments));
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
    write_structural(StructuralRoot::Type(ty), formatter)
}

fn write_structural(root: StructuralRoot<'_>, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
    write_structural_inner(root, formatter, false)
}

fn write_structural_debug(
    root: StructuralRoot<'_>,
    formatter: &mut fmt::Formatter<'_>,
) -> fmt::Result {
    write_structural_inner(root, formatter, true)
}

fn write_structural_inner(
    root: StructuralRoot<'_>,
    formatter: &mut fmt::Formatter<'_>,
    include_lacks: bool,
) -> fmt::Result {
    enum Task<'a> {
        Visit(&'a Type),
        Argument(&'a KindedArgument),
        Arguments(std::slice::Iter<'a, KindedArgument>),
        ApplicationSpine(&'a Type),
        EffectRow(&'a EffectRow),
        EffectInstances(std::slice::Iter<'a, EffectInstance>),
        EffectInstance(&'a EffectInstance),
        EffectRowTail(&'a EffectRowTail, bool),
        Text(&'static str),
        Sequence(std::slice::Iter<'a, Type>),
    }

    let initial = match root {
        StructuralRoot::Type(ty) => Task::Visit(ty),
        StructuralRoot::Argument(arg) => Task::Argument(arg),
        StructuralRoot::Row(row) => Task::EffectRow(row),
        StructuralRoot::Instance(instance) => Task::EffectInstance(instance),
    };
    let mut work = vec![initial];
    while let Some(task) = work.pop() {
        match task {
            Task::Argument(KindedArgument::TypeArg(ty)) => work.push(Task::Visit(ty)),
            Task::Argument(KindedArgument::RowArg(row)) => work.push(Task::EffectRow(row)),
            Task::Arguments(mut remaining) => {
                if let Some(next) = remaining.next() {
                    if !remaining.as_slice().is_empty() {
                        work.push(Task::Arguments(remaining));
                        work.push(Task::Text(", "));
                    }
                    work.push(Task::Argument(next));
                }
            }
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
                    work.push(Task::Arguments(instance.arguments.iter()));
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
                if include_lacks && !tail.lacks.is_empty() {
                    formatter.write_str(" lacks [")?;
                    work.push(Task::Text("]"));
                    work.push(Task::EffectInstances(tail.lacks.iter()));
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
            Task::Visit(Type::Bytes) => formatter.write_str("Bytes")?,
            Task::Visit(Type::String) => formatter.write_str("String")?,
            Task::Visit(Type::Int) => formatter.write_str("Int")?,
            Task::Visit(Type::Bool) => formatter.write_str("Bool")?,
            Task::Visit(Type::Unit) => formatter.write_str("Unit")?,
            Task::Visit(Type::Tuple(elements)) => {
                work.push(Task::Text(")"));
                work.push(Task::Sequence(elements.iter()));
                work.push(Task::Text("("));
            }
            Task::Visit(Type::ResourceApply(id, arguments)) => {
                write!(formatter, "<resource:{}:{}>", id.module(), id.ordinal())?;
                work.push(Task::Text(">"));
                work.push(Task::Arguments(arguments.iter()));
                work.push(Task::Text("<"));
            }
            Task::Visit(Type::ForeignOwnerApply(id, arguments)) => {
                write!(
                    formatter,
                    "<foreign-owner:{}:{}>",
                    id.module(),
                    id.declaration()
                )?;
                work.push(Task::Text(">"));
                work.push(Task::Arguments(arguments.iter()));
                work.push(Task::Text("<"));
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
        CompareArguments(&'a KindedArgument, &'a KindedArgument),
        ArgumentSequence(
            std::iter::Zip<
                std::slice::Iter<'a, KindedArgument>,
                std::slice::Iter<'a, KindedArgument>,
            >,
        ),
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
                Task::CompareArguments(left, right) => match (left, right) {
                    (KindedArgument::TypeArg(left), KindedArgument::TypeArg(right)) => {
                        pending.push(Task::Compare(left, right))
                    }
                    (KindedArgument::RowArg(left), KindedArgument::RowArg(right)) => {
                        pending.push(Task::CompareRows(left, right))
                    }
                    _ => return false,
                },
                Task::ArgumentSequence(mut remaining) => {
                    if let Some((left, right)) = remaining.next() {
                        pending.push(Task::ArgumentSequence(remaining));
                        pending.push(Task::CompareArguments(left, right));
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
                        pending.push(Task::ArgumentSequence(
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
                                pending.push(Task::ArgumentSequence(
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
            (Type::Bytes, Type::Bytes)
            | (Type::String, Type::String)
            | (Type::Int, Type::Int)
            | (Type::Bool, Type::Bool)
            | (Type::Unit, Type::Unit) => {}
            (Type::Nominal(left), Type::Nominal(right)) if left == right => {}
            (Type::Variable(left), Type::Variable(right)) if left == right => {}
            (Type::ForeignOwnerApply(left_id, left), Type::ForeignOwnerApply(right_id, right))
                if left_id == right_id && left.len() == right.len() =>
            {
                pending.push(Task::ArgumentSequence(left.iter().zip(right.iter())));
            }
            (Type::ResourceApply(left_id, left), Type::ResourceApply(right_id, right))
                if left_id == right_id && left.len() == right.len() =>
            {
                pending.push(Task::ArgumentSequence(left.iter().zip(right.iter())));
            }
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
        ArgumentSequence(
            std::iter::Zip<
                std::slice::Iter<'a, KindedArgument>,
                std::slice::Iter<'a, KindedArgument>,
            >,
        ),
        Sequence(std::iter::Zip<std::slice::Iter<'a, Type>, std::slice::Iter<'a, Type>>),
    }

    fn push_type<'a>(
        pending: &mut Vec<Task<'a>>,
        left: &'a Type,
        right: &'a Type,
        budget: &mut TypeWorkBudget,
    ) -> Result<(), ()> {
        budget.charge(1)?;
        reserve_row(pending, 1, RowReservationSite::ComparisonWork).map_err(|_| ())?;
        pending.push(Task::Compare(left, right));
        Ok(())
    }
    fn push_row<'a>(
        pending: &mut Vec<Task<'a>>,
        left: &'a EffectRow,
        right: &'a EffectRow,
        budget: &mut TypeWorkBudget,
    ) -> Result<(), ()> {
        budget.charge(1)?;
        reserve_row(pending, 1, RowReservationSite::ComparisonWork).map_err(|_| ())?;
        pending.push(Task::CompareRows(left, right));
        Ok(())
    }
    fn push_argument<'a>(
        pending: &mut Vec<Task<'a>>,
        left: &'a KindedArgument,
        right: &'a KindedArgument,
        budget: &mut TypeWorkBudget,
    ) -> Result<bool, ()> {
        match (left, right) {
            (KindedArgument::TypeArg(left), KindedArgument::TypeArg(right)) => {
                push_type(pending, left, right, budget)?
            }
            (KindedArgument::RowArg(left), KindedArgument::RowArg(right)) => {
                push_row(pending, left, right, budget)?
            }
            _ => return Ok(false),
        }
        Ok(true)
    }
    let mut pending = Vec::new();
    push_type(&mut pending, left, right, budget)?;
    while let Some(task) = pending.pop() {
        let Task::Compare(left, right) = task else {
            match task {
                Task::Sequence(mut remaining) => {
                    if let Some((left, right)) = remaining.next() {
                        // The container token remains admitted while its next child gets its own cell.
                        reserve_row(&mut pending, 1, RowReservationSite::ComparisonWork)
                            .map_err(|_| ())?;
                        pending.push(Task::Sequence(remaining));
                        push_type(&mut pending, left, right, budget)?;
                    }
                }
                Task::ArgumentSequence(mut remaining) => {
                    if let Some((left, right)) = remaining.next() {
                        reserve_row(&mut pending, 1, RowReservationSite::ComparisonWork)
                            .map_err(|_| ())?;
                        pending.push(Task::ArgumentSequence(remaining));
                        if !push_argument(&mut pending, left, right, budget)? {
                            return Ok(false);
                        }
                    }
                }
                Task::CompareRows(left, right) => {
                    if left.known.len() != right.known.len() {
                        return Ok(false);
                    }
                    budget.charge(left.known.len())?;
                    reserve_row(
                        &mut pending,
                        left.known.len(),
                        RowReservationSite::ComparisonWork,
                    )
                    .map_err(|_| ())?;
                    for (left, right) in left.known.iter().zip(right.known.iter()) {
                        if left.effect != right.effect
                            || left.arguments.len() != right.arguments.len()
                        {
                            return Ok(false);
                        }
                        pending.push(Task::ArgumentSequence(
                            left.arguments.iter().zip(right.arguments.iter()),
                        ));
                    }
                    match (&left.tail, &right.tail) {
                        (None, None) => {}
                        (Some(left), Some(right))
                            if left.variable == right.variable
                                && left.lacks.len() == right.lacks.len() =>
                        {
                            budget.charge(left.lacks.len().checked_add(1).ok_or(())?)?;
                            reserve_row(
                                &mut pending,
                                left.lacks.len(),
                                RowReservationSite::ComparisonWork,
                            )
                            .map_err(|_| ())?;
                            for (left, right) in left.lacks.iter().zip(right.lacks.iter()) {
                                if left.effect != right.effect
                                    || left.arguments.len() != right.arguments.len()
                                {
                                    return Ok(false);
                                }
                                pending.push(Task::ArgumentSequence(
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
        match (left, right) {
            (Type::Bytes, Type::Bytes)
            | (Type::String, Type::String)
            | (Type::Int, Type::Int)
            | (Type::Bool, Type::Bool)
            | (Type::Unit, Type::Unit) => {}
            (Type::Nominal(left), Type::Nominal(right)) if left == right => {}
            (Type::Variable(left), Type::Variable(right)) if left == right => {}
            (Type::ForeignOwnerApply(left_id, left), Type::ForeignOwnerApply(right_id, right))
                if left_id == right_id && left.len() == right.len() =>
            {
                reserve_row(&mut pending, 1, RowReservationSite::ComparisonWork).map_err(|_| ())?;
                pending.push(Task::ArgumentSequence(left.iter().zip(right.iter())));
            }
            (Type::ResourceApply(left_id, left), Type::ResourceApply(right_id, right))
                if left_id == right_id && left.len() == right.len() =>
            {
                reserve_row(&mut pending, 1, RowReservationSite::ComparisonWork).map_err(|_| ())?;
                pending.push(Task::ArgumentSequence(left.iter().zip(right.iter())));
            }
            (Type::Inference(left), Type::Inference(right)) if left == right => {}
            (
                Type::Application(left_function, left_argument),
                Type::Application(right_function, right_argument),
            ) => {
                push_type(&mut pending, left_argument, right_argument, budget)?;
                push_type(&mut pending, left_function, right_function, budget)?;
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
                push_type(&mut pending, left, right, budget)?;
            }
            (Type::Tuple(left), Type::Tuple(right)) if left.len() == right.len() => {
                reserve_row(&mut pending, 1, RowReservationSite::ComparisonWork).map_err(|_| ())?;
                pending.push(Task::Sequence(left.iter().zip(right.iter())));
            }
            (
                Type::Function(left_domain, left_codomain),
                Type::Function(right_domain, right_codomain),
            ) => {
                push_type(&mut pending, left_codomain, right_codomain, budget)?;
                push_type(&mut pending, left_domain, right_domain, budget)?;
            }
            (
                Type::EffectfulFunction(left_domain, left_codomain),
                Type::EffectfulFunction(right_domain, right_codomain),
            ) => {
                budget.charge(1)?;
                push_row(
                    &mut pending,
                    &left_codomain.effects,
                    &right_codomain.effects,
                    budget,
                )?;
                push_type(
                    &mut pending,
                    &left_codomain.value,
                    &right_codomain.value,
                    budget,
                )?;
                push_type(&mut pending, left_domain, right_domain, budget)?;
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
                push_type(&mut pending, left_codomain, &right_codomain.value, budget)?;
                push_type(&mut pending, left_domain, right_domain, budget)?;
            }
            _ => return Ok(false),
        }
    }
    Ok(true)
}

enum TypeHashTask<'a> {
    Visit(&'a Type),
    Argument(&'a KindedArgument),
    Arguments(std::slice::Iter<'a, KindedArgument>),
    EffectRow(&'a EffectRow),
    Instances(std::slice::Iter<'a, EffectInstance>),
    Instance(&'a EffectInstance),
    Sequence(std::slice::Iter<'a, Type>),
    Parameters(std::slice::Iter<'a, (TypeVariableId, Kind)>),
    Parameter(&'a (TypeVariableId, Kind)),
    Kind(&'a Kind),
}

fn hash_type<H: Hasher>(ty: &Type, state: &mut H) {
    hash_type_or_effect_row(TypeHashTask::Visit(ty), state);
}

fn hash_type_or_effect_row<H: Hasher>(root: TypeHashTask<'_>, state: &mut H) {
    hash_type_or_effect_row_with_reservation(root, state, |_, _| Ok(()))
        .expect("ordinary type hashing has no fallible admission");
}

fn hash_type_or_effect_row_with_reservation<'a, H: Hasher>(
    root: TypeHashTask<'a>,
    state: &mut H,
    mut reserve: impl FnMut(&mut Vec<TypeHashTask<'a>>, &TypeHashTask<'a>) -> Result<(), ()>,
) -> Result<(), ()> {
    let mut work = Vec::new();
    reserve(&mut work, &root)?;
    work.push(root);
    macro_rules! push {
        ($task:expr) => {{
            let task = $task;
            reserve(&mut work, &task)?;
            work.push(task);
        }};
    }
    while let Some(task) = work.pop() {
        match task {
            TypeHashTask::Parameters(mut remaining) => {
                if let Some(parameter) = remaining.next() {
                    push!(TypeHashTask::Parameters(remaining));
                    push!(TypeHashTask::Parameter(parameter));
                }
            }
            TypeHashTask::Parameter((identity, kind)) => {
                identity.hash(state);
                push!(TypeHashTask::Kind(kind));
            }
            TypeHashTask::Kind(kind) => match kind {
                Kind::Type => 0_u8.hash(state),
                Kind::EffectRow => 1_u8.hash(state),
                Kind::Arrow(domain, codomain) => {
                    2_u8.hash(state);
                    push!(TypeHashTask::Kind(codomain));
                    push!(TypeHashTask::Kind(domain));
                }
            },
            TypeHashTask::Argument(KindedArgument::TypeArg(ty)) => {
                0_u8.hash(state);
                push!(TypeHashTask::Visit(ty));
            }
            TypeHashTask::Argument(KindedArgument::RowArg(row)) => {
                1_u8.hash(state);
                push!(TypeHashTask::EffectRow(row));
            }
            TypeHashTask::Arguments(mut remaining) => {
                if let Some(next) = remaining.next() {
                    push!(TypeHashTask::Arguments(remaining));
                    push!(TypeHashTask::Argument(next));
                }
            }
            TypeHashTask::Sequence(mut remaining) => {
                if let Some(next) = remaining.next() {
                    push!(TypeHashTask::Sequence(remaining));
                    push!(TypeHashTask::Visit(next));
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
                        push!(TypeHashTask::Instances(tail.lacks.iter()));
                    }
                }
                push!(TypeHashTask::Instances(row.known.iter()));
            }
            TypeHashTask::Instances(mut remaining) => {
                if let Some(next) = remaining.next() {
                    push!(TypeHashTask::Instances(remaining));
                    push!(TypeHashTask::Instance(next));
                }
            }
            TypeHashTask::Instance(instance) => {
                instance.effect.hash(state);
                instance.arguments.len().hash(state);
                push!(TypeHashTask::Arguments(instance.arguments.iter()));
            }
            TypeHashTask::Visit(Type::Bytes) => 11_u8.hash(state),
            TypeHashTask::Visit(Type::String) => 12_u8.hash(state),
            TypeHashTask::Visit(Type::Int) => 0_u8.hash(state),
            TypeHashTask::Visit(Type::Bool) => 1_u8.hash(state),
            TypeHashTask::Visit(Type::Unit) => 2_u8.hash(state),
            TypeHashTask::Visit(Type::Tuple(elements)) => {
                3_u8.hash(state);
                elements.len().hash(state);
                push!(TypeHashTask::Sequence(elements.iter()));
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
            TypeHashTask::Visit(Type::ResourceApply(id, arguments)) => {
                10_u8.hash(state);
                id.hash(state);
                arguments.len().hash(state);
                push!(TypeHashTask::Arguments(arguments.iter()));
            }
            TypeHashTask::Visit(Type::ForeignOwnerApply(id, arguments)) => {
                13_u8.hash(state);
                id.hash(state);
                arguments.len().hash(state);
                push!(TypeHashTask::Arguments(arguments.iter()));
            }
            TypeHashTask::Visit(Type::Application(function, argument)) => {
                7_u8.hash(state);
                push!(TypeHashTask::Visit(argument));
                push!(TypeHashTask::Visit(function));
            }
            TypeHashTask::Visit(Type::Forall(parameters, body)) => {
                8_u8.hash(state);
                parameters.len().hash(state);
                push!(TypeHashTask::Visit(body));
                push!(TypeHashTask::Parameters(parameters.iter()));
            }
            TypeHashTask::Visit(Type::Function(domain, codomain)) => {
                9_u8.hash(state);
                10_u8.hash(state);
                0_usize.hash(state);
                0_u8.hash(state);
                push!(TypeHashTask::Visit(codomain));
                push!(TypeHashTask::Visit(domain));
            }
            TypeHashTask::Visit(Type::EffectfulFunction(domain, codomain)) => {
                9_u8.hash(state);
                push!(TypeHashTask::Visit(&codomain.value));
                push!(TypeHashTask::Visit(domain));
                push!(TypeHashTask::EffectRow(&codomain.effects));
            }
        }
    }
    Ok(())
}

pub(crate) fn hash_type_with_budget<H: Hasher>(
    ty: &Type,
    state: &mut H,
    budget: &mut TypeWorkBudget,
) -> Result<(), ()> {
    hash_type_or_effect_row_with_reservation(TypeHashTask::Visit(ty), state, |work, task| {
        // The same complete cells as structural admission, paid before scratch retention.
        // Iterator continuations reuse their admitted container and child cells.
        let cells = match task {
            TypeHashTask::Visit(Type::EffectfulFunction(_, _)) => 2,
            TypeHashTask::Visit(_)
            | TypeHashTask::Instance(_)
            | TypeHashTask::Parameter(_)
            | TypeHashTask::Kind(_) => 1,
            TypeHashTask::EffectRow(row) => 1 + usize::from(row.tail.is_some()),
            TypeHashTask::Argument(_)
            | TypeHashTask::Arguments(_)
            | TypeHashTask::Instances(_)
            | TypeHashTask::Sequence(_)
            | TypeHashTask::Parameters(_) => 0,
        };
        budget.charge(cells)?;
        work.try_reserve(1).map_err(|_| ())
    })
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

pub(crate) fn substitute_type_variables_borrowed_with<E>(
    ty: &Type,
    replacements: &HashMap<TypeVariableId, &Type>,
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

pub(crate) fn substitute_type_and_row_variables_borrowed_with<E>(
    ty: &Type,
    replacements: &HashMap<TypeVariableId, &Type>,
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

pub(crate) fn substitute_effect_and_template_rows_with<E>(
    row: &EffectRow,
    replacements: &HashMap<TypeVariableId, Type>,
    row_replacements: &HashMap<TypeVariableId, EffectRow>,
    inference_rows: &HashMap<InferenceVariableId, EffectRow>,
    mut charge: impl FnMut(usize) -> Result<(), E>,
    mut allocation_error: impl FnMut() -> E,
) -> Result<Result<EffectRow, EffectRowError>, E> {
    substitute_structural_type_and_row_variables(
        SubstitutionRoot::Row(row),
        replacements,
        row_replacements,
        Some(TemplateRowReplacements {
            inference_rows,
            renaming: None,
        }),
        &mut charge,
        &mut allocation_error,
        None,
    )
    .map(|result| result.map(|value| value.into_row().expect("row substitution root")))
}

pub(crate) fn substitute_argument_and_template_rows_with<E>(
    argument: &KindedArgument,
    replacements: &HashMap<TypeVariableId, Type>,
    row_replacements: &HashMap<TypeVariableId, EffectRow>,
    inference_rows: &HashMap<InferenceVariableId, EffectRow>,
    mut charge: impl FnMut(usize) -> Result<(), E>,
    mut allocation_error: impl FnMut() -> E,
) -> Result<Result<KindedArgument, EffectRowError>, E> {
    substitute_structural_type_and_row_variables(
        SubstitutionRoot::Argument(argument),
        replacements,
        row_replacements,
        Some(TemplateRowReplacements {
            inference_rows,
            renaming: None,
        }),
        &mut charge,
        &mut allocation_error,
        None,
    )
    .map(|result| result.map(|value| value.into_argument().expect("argument substitution root")))
}

/// Renames copied local declarations, including binders underneath `forall`.
/// Canonical external declarations and actual substitution payloads retain
/// their identities. These maps express a claim; Core checks their freshness.
pub(crate) struct TemplateIdentityRenaming<'a> {
    pub(crate) nominals: &'a HashMap<NominalTypeId, NominalTypeId>,
    pub(crate) variables: &'a HashMap<TypeVariableId, TypeVariableId>,
}

#[derive(Clone, Copy)]
struct TemplateRowReplacements<'a> {
    inference_rows: &'a HashMap<InferenceVariableId, EffectRow>,
    renaming: Option<&'a TemplateIdentityRenaming<'a>>,
}

pub(crate) fn substitute_type_for_template_with<E>(
    ty: &Type,
    replacements: &HashMap<TypeVariableId, Type>,
    row_replacements: &HashMap<TypeVariableId, EffectRow>,
    inference_rows: &HashMap<InferenceVariableId, EffectRow>,
    renaming: &TemplateIdentityRenaming<'_>,
    mut charge: impl FnMut(usize) -> Result<(), E>,
    mut allocation_error: impl FnMut() -> E,
) -> Result<Result<Type, EffectRowError>, E> {
    substitute_structural_type_and_row_variables(
        SubstitutionRoot::Type(ty),
        replacements,
        row_replacements,
        Some(TemplateRowReplacements {
            inference_rows,
            renaming: Some(renaming),
        }),
        &mut charge,
        &mut allocation_error,
        None,
    )
    .map(|result| result.map(StructuralValue::into_inner))
}

pub(crate) fn substitute_row_for_template_with<E>(
    row: &EffectRow,
    replacements: &HashMap<TypeVariableId, Type>,
    row_replacements: &HashMap<TypeVariableId, EffectRow>,
    inference_rows: &HashMap<InferenceVariableId, EffectRow>,
    renaming: &TemplateIdentityRenaming<'_>,
    mut charge: impl FnMut(usize) -> Result<(), E>,
    mut allocation_error: impl FnMut() -> E,
) -> Result<Result<EffectRow, EffectRowError>, E> {
    substitute_structural_type_and_row_variables(
        SubstitutionRoot::Row(row),
        replacements,
        row_replacements,
        Some(TemplateRowReplacements {
            inference_rows,
            renaming: Some(renaming),
        }),
        &mut charge,
        &mut allocation_error,
        None,
    )
    .map(|result| result.map(|value| value.into_row().expect("row substitution root")))
}

pub(crate) fn substitute_argument_for_template_with<E>(
    argument: &KindedArgument,
    replacements: &HashMap<TypeVariableId, Type>,
    row_replacements: &HashMap<TypeVariableId, EffectRow>,
    inference_rows: &HashMap<InferenceVariableId, EffectRow>,
    renaming: &TemplateIdentityRenaming<'_>,
    mut charge: impl FnMut(usize) -> Result<(), E>,
    mut allocation_error: impl FnMut() -> E,
) -> Result<Result<KindedArgument, EffectRowError>, E> {
    substitute_structural_type_and_row_variables(
        SubstitutionRoot::Argument(argument),
        replacements,
        row_replacements,
        Some(TemplateRowReplacements {
            inference_rows,
            renaming: Some(renaming),
        }),
        &mut charge,
        &mut allocation_error,
        None,
    )
    .map(|result| result.map(|value| value.into_argument().expect("argument substitution root")))
}

/// Substitute an implementation's complete source type after requiring every
/// free source binder to have a checked replacement. Replacement values retain
/// the caller's scope. Missing bindings fail inside the shared reconstruction,
/// so already rebuilt fragments remain protected by iterative owners.
#[cfg(test)]
pub(crate) fn substitute_type_and_row_variables_strict_source_with<E>(
    ty: &Type,
    replacements: &HashMap<TypeVariableId, Type>,
    row_replacements: &HashMap<TypeVariableId, EffectRow>,
    mut charge: impl FnMut(usize) -> Result<(), E>,
    mut allocation_error: impl FnMut() -> E,
    mut invalid_source: impl FnMut() -> E,
) -> Result<Result<Type, EffectRowError>, E> {
    substitute_structural_type_and_row_variables(
        SubstitutionRoot::Type(ty),
        replacements,
        row_replacements,
        None,
        &mut charge,
        &mut allocation_error,
        Some(&mut invalid_source),
    )
    .map(|result| result.map(StructuralValue::into_inner))
}

/// The same strict source policy for an ordered owner argument, including
/// nested row payloads; replacement bodies remain caller-scoped.
pub(crate) fn substitute_kinded_argument_strict_source_with<E>(
    argument: &KindedArgument,
    replacements: &HashMap<TypeVariableId, Type>,
    row_replacements: &HashMap<TypeVariableId, EffectRow>,
    mut charge: impl FnMut(usize) -> Result<(), E>,
    mut allocation_error: impl FnMut() -> E,
    mut invalid_source: impl FnMut() -> E,
) -> Result<Result<KindedArgument, EffectRowError>, E> {
    substitute_structural_type_and_row_variables(
        SubstitutionRoot::Argument(argument),
        replacements,
        row_replacements,
        None,
        &mut charge,
        &mut allocation_error,
        Some(&mut invalid_source),
    )
    .map(|result| result.map(|value| value.into_argument().expect("argument substitution root")))
}

enum SubstitutionRoot<'a> {
    Row(&'a EffectRow),
    Type(&'a Type),
    Argument(&'a KindedArgument),
}

/// Applies existing facts from a rigid expected row to matching occurrences
/// throughout one complete owner argument. The caller authenticates that row;
/// this operation neither infers exclusions nor changes other tail identities.
/// No replacement means the original argument needs no qualification.
pub(crate) fn qualify_kinded_argument_with_expected_row_with_budget(
    argument: &KindedArgument,
    expected: Option<&EffectRow>,
    budget: &mut TypeWorkBudget,
) -> Result<Result<Option<KindedArgument>, EffectRowError>, ()> {
    let Some(expected) = expected else {
        return Ok(Ok(None));
    };
    let Some(tail) = expected.tail() else {
        return Ok(Ok(None));
    };
    let EffectRowVariable::Rigid(binder) = tail.variable() else {
        return Ok(Ok(None));
    };
    if tail.lacks().is_empty() && expected.known().is_empty() {
        return Ok(Ok(None));
    }
    let qualified = rebuild_effect_row_with_budget(
        std::iter::empty(),
        Some(tail.variable()),
        tail.lacks().iter().chain(expected.known()),
        clone_type_with_budget,
        budget,
    )?;
    budget.charge(1)?;
    let mut rows = HashMap::new();
    rows.try_reserve(1).map_err(|_| ())?;
    rows.insert(binder, qualified);
    substitute_kinded_argument_with(argument, &HashMap::new(), &rows, |cells| {
        budget.charge(cells)
    })
    .map(|result| result.map(Some))
}

/// Qualifies a complete argument with independently authenticated enclosing
/// declaration facts. Structural substitution preserves nested binder scope.
pub(crate) fn qualify_kinded_argument_with_row_contexts_with_budget<'a>(
    argument: &KindedArgument,
    contexts: impl IntoIterator<Item = &'a HashMap<TypeVariableId, EffectRow>>,
    budget: &mut TypeWorkBudget,
) -> Result<Result<Option<KindedArgument>, EffectRowError>, ()> {
    let mut qualified: Option<IterativeArgumentOwner> = None;
    for rows in contexts {
        if rows.is_empty() {
            continue;
        }
        let original = qualified.as_deref().unwrap_or(argument);
        let value =
            match substitute_kinded_argument_with(original, &HashMap::new(), rows, |cells| {
                budget.charge(cells)
            })? {
                Ok(value) => value,
                Err(error) => return Ok(Err(error)),
            };
        qualified = Some(IterativeArgumentOwner::new(value));
    }
    Ok(Ok(qualified.map(IterativeArgumentOwner::into_inner)))
}

/// A paid structural gate for lazy reconstruction of original ambient facts.
/// It includes latent function rows and rows in complete effect owner payloads.
pub(crate) fn kinded_arguments_have_rigid_rows_with_budget<'a>(
    arguments: impl IntoIterator<Item = &'a KindedArgument>,
    budget: &mut TypeWorkBudget,
) -> Result<bool, ()> {
    enum Task<'a> {
        Type(&'a Type),
        Argument(&'a KindedArgument),
        Row(&'a EffectRow),
    }
    let mut pending = Vec::new();
    let mut found = false;
    for argument in arguments {
        budget.charge(1)?;
        pending.try_reserve(1).map_err(|_| ())?;
        pending.push(Task::Argument(argument));
    }
    while let Some(task) = pending.pop() {
        budget.charge(1)?;
        if let Task::Row(row) = &task {
            let labels = row
                .known()
                .len()
                .checked_add(row.tail().map_or(0, |tail| tail.lacks().len()))
                .ok_or(())?;
            budget.charge(labels)?;
        }
        let mut push = |task| -> Result<(), ()> {
            budget.charge(1)?;
            pending.try_reserve(1).map_err(|_| ())?;
            pending.push(task);
            Ok(())
        };
        match task {
            Task::Argument(KindedArgument::TypeArg(ty)) => push(Task::Type(ty))?,
            Task::Argument(KindedArgument::RowArg(row)) => push(Task::Row(row))?,
            Task::Type(Type::Application(left, right) | Type::Function(left, right)) => {
                push(Task::Type(left))?;
                push(Task::Type(right))?;
            }
            Task::Type(Type::EffectfulFunction(domain, codomain)) => {
                push(Task::Type(domain))?;
                push(Task::Type(&codomain.value))?;
                push(Task::Row(&codomain.effects))?;
            }
            Task::Type(Type::Tuple(elements)) => {
                for ty in elements {
                    push(Task::Type(ty))?;
                }
            }
            Task::Type(
                Type::ResourceApply(_, arguments) | Type::ForeignOwnerApply(_, arguments),
            ) => {
                for argument in arguments {
                    push(Task::Argument(argument))?;
                }
            }
            Task::Type(Type::Forall(_, body)) => push(Task::Type(body))?,
            Task::Row(row) => {
                found |= matches!(
                    row.tail().map(|tail| tail.variable()),
                    Some(EffectRowVariable::Rigid(_))
                );
                for instance in row
                    .known()
                    .iter()
                    .chain(row.tail().into_iter().flat_map(|tail| tail.lacks()))
                {
                    for argument in instance.arguments() {
                        push(Task::Argument(argument))?;
                    }
                }
            }
            Task::Type(
                Type::Bytes
                | Type::String
                | Type::Int
                | Type::Bool
                | Type::Unit
                | Type::Nominal(_)
                | Type::Variable(_)
                | Type::Inference(_),
            ) => {}
        }
    }
    Ok(found)
}

pub(crate) fn substitute_kinded_argument_with(
    argument: &KindedArgument,
    replacements: &HashMap<TypeVariableId, Type>,
    row_replacements: &HashMap<TypeVariableId, EffectRow>,
    mut charge: impl FnMut(usize) -> Result<(), ()>,
) -> Result<Result<KindedArgument, EffectRowError>, ()> {
    substitute_structural_type_and_row_variables(
        SubstitutionRoot::Argument(argument),
        replacements,
        row_replacements,
        None,
        &mut charge,
        &mut || (),
        None,
    )
    .map(|result| result.map(|value| value.into_argument().expect("argument substitution root")))
}

pub(crate) fn substitute_kinded_argument_borrowed_with(
    argument: &KindedArgument,
    replacements: &HashMap<TypeVariableId, &Type>,
    row_replacements: &HashMap<TypeVariableId, EffectRow>,
    mut charge: impl FnMut(usize) -> Result<(), ()>,
) -> Result<Result<KindedArgument, EffectRowError>, ()> {
    substitute_structural_type_and_row_variables(
        SubstitutionRoot::Argument(argument),
        replacements,
        row_replacements,
        None,
        &mut charge,
        &mut || (),
        None,
    )
    .map(|result| result.map(|value| value.into_argument().expect("argument substitution root")))
}

pub(crate) fn substitute_effect_row_with(
    row: &EffectRow,
    replacements: &HashMap<TypeVariableId, Type>,
    row_replacements: &HashMap<TypeVariableId, EffectRow>,
    mut charge: impl FnMut(usize) -> Result<(), ()>,
) -> Result<Result<EffectRow, EffectRowError>, ()> {
    substitute_structural_type_and_row_variables(
        SubstitutionRoot::Row(row),
        replacements,
        row_replacements,
        None,
        &mut charge,
        &mut || (),
        None,
    )
    .map(|result| result.map(|value| value.into_row().expect("row substitution root")))
}

fn substitute_type_and_row_variables<E, R: Borrow<Type>>(
    ty: &Type,
    replacements: &HashMap<TypeVariableId, R>,
    row_replacements: &HashMap<TypeVariableId, EffectRow>,
    charge: &mut impl FnMut(usize) -> Result<(), E>,
    allocation_error: &mut impl FnMut() -> E,
) -> Result<Result<Type, EffectRowError>, E> {
    substitute_structural_type_and_row_variables(
        SubstitutionRoot::Type(ty),
        replacements,
        row_replacements,
        None,
        charge,
        allocation_error,
        None,
    )
    .map(|result| result.map(StructuralValue::into_inner))
}

#[allow(
    clippy::type_complexity,
    reason = "the local traversal shape mirrors substitution state without a module-level alias"
)]
fn substitute_structural_type_and_row_variables<E, R: Borrow<Type>>(
    root: SubstitutionRoot<'_>,
    replacements: &HashMap<TypeVariableId, R>,
    row_replacements: &HashMap<TypeVariableId, EffectRow>,
    template: Option<TemplateRowReplacements<'_>>,
    charge: &mut impl FnMut(usize) -> Result<(), E>,
    allocation_error: &mut impl FnMut() -> E,
    mut invalid_source: Option<&mut dyn FnMut() -> E>,
) -> Result<Result<StructuralValue, EffectRowError>, E> {
    struct RowShape<'a> {
        known: Box<[(EffectId, usize)]>,
        tail: Option<(EffectRowVariable, Box<[(EffectId, usize)]>)>,
        argument_count: usize,
        replacement: Option<(EffectRowVariable, &'a EffectRow)>,
    }

    enum Task<'a> {
        Visit(&'a Type, bool),
        VisitArgument(&'a KindedArgument, bool),
        VisitRow(&'a EffectRow, bool),
        FinishTypeArgument,
        FinishRowArgument,
        FinishResource(ResourceDefinitionId, usize),
        FinishForeignOwner(NominalTypeId, usize),
        FinishRow(RowShape<'a>),
        Sequence(std::slice::Iter<'a, Type>, bool),
        EnterForall(&'a [(TypeVariableId, Kind)]),
        ExitForall(&'a [(TypeVariableId, Kind)]),
        FinishTuple(usize),
        FinishApplication,
        FinishFunction,
        FinishEffectfulFunction,
        FinishForall(Box<[(TypeVariableId, Kind)]>),
    }

    let mut active_shadows = HashMap::new();
    let mut work = Vec::new();
    charge(1)?;
    work.try_reserve_exact(1).map_err(|_| allocation_error())?;
    work.push(match root {
        SubstitutionRoot::Row(row) => Task::VisitRow(row, true),
        SubstitutionRoot::Type(ty) => Task::Visit(ty, true),
        SubstitutionRoot::Argument(argument) => Task::VisitArgument(argument, true),
    });
    let mut rebuilt: Vec<StructuralValue> = Vec::new();
    while let Some(task) = work.pop() {
        work.try_reserve(4).map_err(|_| allocation_error())?;
        rebuilt.try_reserve(1).map_err(|_| allocation_error())?;
        match task {
            Task::Visit(Type::Variable(identity), true) => {
                if let Some(renamed) = template
                    .and_then(|template| template.renaming)
                    .and_then(|renaming| renaming.variables.get(identity))
                {
                    charge(1)?;
                    rebuilt.push(StructuralValue::type_value(Type::Variable(*renamed)));
                } else if active_shadows
                    .get(identity)
                    .is_some_and(|count| *count != 0)
                {
                    charge(1)?;
                    rebuilt.push(StructuralValue::type_value(Type::Variable(*identity)));
                } else if let Some(replacement) = replacements.get(identity) {
                    work.push(Task::Visit(replacement.borrow(), false));
                } else if let Some(invalid_source) = invalid_source.as_mut() {
                    return Err(invalid_source());
                } else {
                    charge(1)?;
                    rebuilt.push(StructuralValue::type_value(Type::Variable(*identity)));
                }
            }
            Task::Visit(Type::Nominal(identity), true) => {
                charge(1)?;
                let identity = template
                    .and_then(|template| template.renaming)
                    .and_then(|renaming| renaming.nominals.get(identity))
                    .unwrap_or(identity);
                rebuilt.push(StructuralValue::type_value(Type::Nominal(*identity)));
            }
            Task::Visit(Type::Inference(_) | Type::Forall(_, _), true)
                if invalid_source.is_some() =>
            {
                return Err(invalid_source.as_mut().expect("strict source policy")());
            }
            Task::Visit(
                ty @ (Type::Bytes
                | Type::String
                | Type::Int
                | Type::Bool
                | Type::Unit
                | Type::Nominal(_)
                | Type::Variable(_)
                | Type::Inference(_)),
                _,
            ) => {
                charge(1)?;
                rebuilt.push(StructuralValue::type_value(clone_type(ty)));
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
                charge(2)?;
                work.try_reserve(4).map_err(|_| allocation_error())?;
                work.push(Task::FinishEffectfulFunction);
                work.push(Task::VisitRow(&codomain.effects, substitute));
                work.push(Task::Visit(&codomain.value, substitute));
                work.push(Task::Visit(domain, substitute));
            }
            Task::Visit(Type::ResourceApply(definition, arguments), substitute) => {
                charge(1)?;
                charge(arguments.len())?;
                work.try_reserve(
                    arguments
                        .len()
                        .checked_add(1)
                        .ok_or_else(&mut *allocation_error)?,
                )
                .map_err(|_| allocation_error())?;
                work.push(Task::FinishResource(*definition, arguments.len()));
                for argument in arguments.iter().rev() {
                    work.push(Task::VisitArgument(argument, substitute));
                }
            }
            Task::Visit(Type::ForeignOwnerApply(definition, arguments), substitute) => {
                charge(1)?;
                charge(arguments.len())?;
                work.try_reserve(
                    arguments
                        .len()
                        .checked_add(1)
                        .ok_or_else(&mut *allocation_error)?,
                )
                .map_err(|_| allocation_error())?;
                work.push(Task::FinishForeignOwner(*definition, arguments.len()));
                for argument in arguments.iter().rev() {
                    work.push(Task::VisitArgument(argument, substitute));
                }
            }
            Task::VisitArgument(KindedArgument::TypeArg(ty), substitute) => {
                work.try_reserve(2).map_err(|_| allocation_error())?;
                work.push(Task::FinishTypeArgument);
                work.push(Task::Visit(ty, substitute));
            }
            Task::VisitArgument(KindedArgument::RowArg(row), substitute) => {
                work.try_reserve(2).map_err(|_| allocation_error())?;
                work.push(Task::FinishRowArgument);
                work.push(Task::VisitRow(row, substitute));
            }
            Task::VisitRow(row, substitute) => {
                if substitute
                    && let Some(invalid_source) = invalid_source.as_mut()
                    && let Some(tail) = &row.tail
                {
                    match tail.variable {
                        EffectRowVariable::Rigid(identity)
                            if row_replacements.contains_key(&identity) => {}
                        _ => return Err(invalid_source()),
                    }
                }
                charge(1)?;
                charge(row.known.len())?;
                if let Some(tail) = &row.tail {
                    charge(1)?;
                    charge(tail.lacks.len())?;
                }
                let instances = row
                    .known
                    .iter()
                    .chain(row.tail.iter().flat_map(|tail| tail.lacks.iter()));
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
                    .try_reserve(row.known.len())
                    .map_err(|_| allocation_error())?;
                known.extend(
                    row.known
                        .iter()
                        .map(|instance| (instance.effect, instance.arguments.len())),
                );
                let replacement = row.tail.as_ref().and_then(|tail| match tail.variable {
                    EffectRowVariable::Rigid(identity)
                        if substitute
                            && template.and_then(|template| template.renaming).is_none_or(
                                |renaming| !renaming.variables.contains_key(&identity),
                            )
                            && !active_shadows
                                .get(&identity)
                                .is_some_and(|count| *count != 0) =>
                    {
                        row_replacements
                            .get(&identity)
                            .map(|row| (tail.variable, row))
                    }
                    EffectRowVariable::Inference(identity) if substitute => template
                        .and_then(|template| template.inference_rows.get(&identity))
                        .map(|row| (tail.variable, row)),
                    _ => None,
                });
                let tail = if let Some(tail) = &row.tail {
                    let mut lacks = Vec::new();
                    lacks
                        .try_reserve(tail.lacks.len())
                        .map_err(|_| allocation_error())?;
                    lacks.extend(
                        tail.lacks
                            .iter()
                            .map(|instance| (instance.effect, instance.arguments.len())),
                    );
                    let variable = if substitute {
                        match tail.variable {
                            EffectRowVariable::Rigid(identity) => template
                                .and_then(|template| template.renaming)
                                .and_then(|renaming| renaming.variables.get(&identity))
                                .map_or(tail.variable, |identity| {
                                    EffectRowVariable::Rigid(*identity)
                                }),
                            _ => tail.variable,
                        }
                    } else {
                        tail.variable
                    };
                    Some((variable, lacks.into_boxed_slice()))
                } else {
                    None
                };
                work.push(Task::FinishRow(RowShape {
                    known: known.into_boxed_slice(),
                    tail,
                    argument_count,
                    replacement,
                }));
                for instance in instances.rev() {
                    for argument in instance.arguments.iter().rev() {
                        work.push(Task::VisitArgument(argument, substitute));
                    }
                }
            }
            Task::Visit(Type::Forall(parameters, body), substitute) => {
                charge(1)?;
                charge(parameters.len())?;
                for (_, kind) in parameters {
                    charge_kind_with_charge(kind, || charge(1))?;
                }
                let mut retained = Vec::new();
                retained
                    .try_reserve_exact(parameters.len())
                    .map_err(|_| allocation_error())?;
                for (identity, kind) in parameters {
                    let identity = if substitute {
                        template
                            .and_then(|template| template.renaming)
                            .and_then(|renaming| renaming.variables.get(identity))
                            .unwrap_or(identity)
                    } else {
                        identity
                    };
                    retained.push((
                        *identity,
                        clone_kind_precharged(kind, charge, &mut |_| allocation_error())?,
                    ));
                }
                work.push(Task::FinishForall(retained.into_boxed_slice()));
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
                charge(count)?;
                let mut elements = Vec::new();
                elements
                    .try_reserve_exact(count)
                    .map_err(|_| allocation_error())?;
                for value in rebuilt.drain(rebuilt.len() - count..) {
                    elements.push(value.into_inner());
                }
                rebuilt.push(StructuralValue::type_value(Type::Tuple(
                    elements.into_boxed_slice(),
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
                rebuilt.push(StructuralValue::type_value(Type::Application(
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
                rebuilt.push(StructuralValue::type_value(Type::function(
                    domain, codomain,
                )));
            }
            Task::FinishEffectfulFunction => {
                let row = rebuilt
                    .pop()
                    .expect("function row")
                    .into_row()
                    .expect("row shape");
                let codomain = rebuilt.pop().expect("function value").into_inner();
                let domain = rebuilt.pop().expect("function domain").into_inner();
                rebuilt.push(StructuralValue::type_value(Type::function_computation(
                    domain,
                    ComputationType::new(codomain, row),
                )));
            }
            Task::FinishTypeArgument => {
                let ty = rebuilt.pop().expect("Type argument").into_inner();
                rebuilt.push(StructuralValue::argument_value(KindedArgument::TypeArg(ty)));
            }
            Task::FinishRowArgument => {
                let row = rebuilt
                    .pop()
                    .expect("row argument")
                    .into_row()
                    .expect("row shape");
                rebuilt.push(StructuralValue::argument_value(KindedArgument::RowArg(row)));
            }
            Task::FinishResource(definition, count) => {
                charge(count)?;
                let mut arguments = Vec::new();
                arguments
                    .try_reserve_exact(count)
                    .map_err(|_| allocation_error())?;
                for value in rebuilt.drain(rebuilt.len() - count..) {
                    arguments.push(value.into_argument_inner());
                }
                rebuilt.push(StructuralValue::type_value(Type::ResourceApply(
                    definition,
                    arguments.into_boxed_slice(),
                )));
            }
            Task::FinishForeignOwner(definition, count) => {
                charge(count)?;
                let mut arguments = Vec::new();
                arguments
                    .try_reserve_exact(count)
                    .map_err(|_| allocation_error())?;
                for value in rebuilt.drain(rebuilt.len() - count..) {
                    arguments.push(value.into_argument_inner());
                }
                rebuilt.push(StructuralValue::type_value(Type::ForeignOwnerApply(
                    definition,
                    arguments.into_boxed_slice(),
                )));
            }
            Task::FinishRow(shape) => {
                charge(shape.argument_count)?;
                let mut suffix = Vec::new();
                suffix
                    .try_reserve_exact(shape.argument_count)
                    .map_err(|_| allocation_error())?;
                suffix.extend(rebuilt.drain(rebuilt.len() - shape.argument_count..));
                let mut arguments = suffix.into_iter();
                fn rebuild_instances<E>(
                    shapes: Box<[(EffectId, usize)]>,
                    arguments: &mut std::vec::IntoIter<StructuralValue>,
                    charge: &mut impl FnMut(usize) -> Result<(), E>,
                    allocation_error: &mut impl FnMut() -> E,
                ) -> Result<Vec<EffectInstance>, E> {
                    charge(shapes.len())?;
                    let mut instances = Vec::new();
                    instances
                        .try_reserve_exact(shapes.len())
                        .map_err(|_| allocation_error())?;
                    for (effect, count) in shapes.into_vec() {
                        charge(count)?;
                        let mut actuals = Vec::new();
                        actuals
                            .try_reserve_exact(count)
                            .map_err(|_| allocation_error())?;
                        for _ in 0..count {
                            actuals.push(
                                arguments
                                    .next()
                                    .expect("counted row argument")
                                    .into_argument_inner(),
                            );
                        }
                        instances.push(EffectInstance::new_kinded(
                            effect,
                            actuals.into_boxed_slice(),
                        ));
                    }
                    Ok(instances)
                }
                let known =
                    rebuild_instances(shape.known, &mut arguments, charge, allocation_error)?;
                let tail = if let Some((variable, lacks)) = shape.tail {
                    Some((
                        variable,
                        rebuild_instances(lacks, &mut arguments, charge, allocation_error)?,
                    ))
                } else {
                    None
                };
                debug_assert!(arguments.next().is_none());
                let effects = effect_row_from_owned_parts_with_budget_and_failure(
                    known,
                    tail,
                    charge,
                    |_| allocation_error(),
                )?;
                let effects = if let Some((target, replacement)) = shape.replacement {
                    let substituted = effects.substitute_owned_tail_for_reconstruction(
                        target,
                        replacement,
                        charge,
                        |_| allocation_error(),
                    )?;
                    match substituted {
                        Ok(effects) => effects,
                        Err(error) => return Ok(Err(error)),
                    }
                } else {
                    effects
                };
                rebuilt.push(StructuralValue::row_value(effects));
            }
            Task::FinishForall(parameters) => {
                let body = rebuilt
                    .pop()
                    .expect("type reconstruction scheme body")
                    .into_inner();
                rebuilt.push(StructuralValue::type_value(Type::Forall(
                    parameters,
                    Box::new(body),
                )));
            }
        }
    }
    debug_assert!(active_shadows.values().all(|count| *count == 0));
    Ok(Ok(rebuilt
        .pop()
        .expect("one reconstructed substitution root")))
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
mod row_comparator_tests;

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
    fn copied_templates_freshen_local_schemes_and_solve_nested_owner_rows_once() {
        let module = ModuleId::new(71);
        let formal = TypeVariableId::resolved(module, 0);
        let local = TypeVariableId::resolved(module, 1);
        let local_row = TypeVariableId::resolved(module, 2);
        let fresh = TypeVariableId::generated(91);
        let fresh_row = TypeVariableId::generated(92);
        let pending = InferenceVariableId::new(3);
        let nominal = NominalTypeId::new(module, 0);
        let copied_nominal = NominalTypeId::new(module, 1);
        let effect = EffectId::new(module, 0);
        let excluded = EffectId::new(module, 1);
        let instance = |id, argument| EffectInstance::new(id, vec![argument].into_boxed_slice());
        let source = IterativeTypeOwner::new(Type::Forall(
            vec![(local, Kind::Type), (local_row, Kind::EffectRow)].into_boxed_slice(),
            Box::new(Type::Tuple(
                vec![
                    Type::Variable(local),
                    Type::Nominal(nominal),
                    Type::ResourceApply(
                        ResourceDefinitionId::new(module, 0),
                        vec![
                            KindedArgument::TypeArg(Type::Variable(formal)),
                            KindedArgument::RowArg(EffectRow::with_tail(
                                Box::new([]),
                                EffectRowVariable::Inference(pending),
                                vec![instance(excluded, Type::Variable(formal))].into_boxed_slice(),
                            )),
                            KindedArgument::RowArg(EffectRow::with_tail(
                                Box::new([]),
                                EffectRowVariable::Rigid(local_row),
                                vec![instance(excluded, Type::Variable(local))].into_boxed_slice(),
                            )),
                        ]
                        .into_boxed_slice(),
                    ),
                ]
                .into_boxed_slice(),
            )),
        ));
        let types = HashMap::from([(formal, Type::Nominal(nominal))]);
        let rows = HashMap::new();
        let solved = HashMap::from([(
            pending,
            EffectRow::singleton(instance(effect, Type::Variable(formal))),
        )]);
        let nominals = HashMap::from([(nominal, copied_nominal)]);
        let variables = HashMap::from([(local, fresh), (local_row, fresh_row)]);
        let renaming = TemplateIdentityRenaming {
            nominals: &nominals,
            variables: &variables,
        };
        let mut work = TypeWorkBudget::unbounded();
        let copied = IterativeTypeOwner::new(
            substitute_type_for_template_with(
                &source,
                &types,
                &rows,
                &solved,
                &renaming,
                |units| work.charge(units),
                || (),
            )
            .unwrap()
            .unwrap(),
        );
        let Type::Forall(parameters, body) = &*copied else {
            panic!("scheme preserved")
        };
        assert_eq!(
            parameters.as_ref(),
            &[(fresh, Kind::Type), (fresh_row, Kind::EffectRow)]
        );
        let Type::Tuple(fields) = &**body else {
            panic!("tuple preserved")
        };
        assert_eq!(fields[0], Type::Variable(fresh));
        assert_eq!(fields[1], Type::Nominal(copied_nominal));
        let Type::ResourceApply(_, arguments) = &fields[2] else {
            panic!("owner application preserved")
        };
        assert_eq!(
            arguments[0],
            KindedArgument::TypeArg(Type::Nominal(nominal))
        );
        let KindedArgument::RowArg(solved_row) = &arguments[1] else {
            panic!("row tag preserved")
        };
        assert_eq!(
            solved_row.known(),
            &[instance(effect, Type::Variable(formal))]
        );
        assert!(solved_row.tail().is_none());
        let KindedArgument::RowArg(bound_row) = &arguments[2] else {
            panic!("bound row tag preserved")
        };
        let tail = bound_row.tail().unwrap();
        assert_eq!(tail.variable(), EffectRowVariable::Rigid(fresh_row));
        assert_eq!(tail.lacks(), &[instance(excluded, Type::Variable(fresh))]);
        let mut short = TypeWorkBudget::with_limit(work.used() - 1);
        assert!(
            substitute_type_for_template_with(
                &source,
                &types,
                &rows,
                &solved,
                &renaming,
                |units| short.charge(units),
                || (),
            )
            .is_err()
        );
        let forbidden = HashMap::from([(
            pending,
            EffectRow::singleton(instance(excluded, Type::Nominal(nominal))),
        )]);
        assert!(
            substitute_type_for_template_with(
                &source,
                &types,
                &rows,
                &forbidden,
                &renaming,
                |units| work.charge(units),
                || (),
            )
            .unwrap()
            .is_err()
        );
    }

    #[test]
    fn direct_owner_row_substitution_is_simultaneous_and_checks_substituted_lacks() {
        let source = crate::source::SourceFile::new("owner-row-sigma.ash", "owner").unwrap();
        let module = ModuleId::from(source.id());
        let ty = TypeVariableId::resolved(module, 0);
        let row = TypeVariableId::resolved(module, 1);
        let h = EffectId::new(module, 0);
        let g = EffectId::new(module, 1);
        let excluded = EffectId::new(module, 2);
        let instance = |effect, argument| {
            EffectInstance::new_kinded(
                effect,
                vec![KindedArgument::TypeArg(argument)].into_boxed_slice(),
            )
        };
        let original = KindedArgument::RowArg(EffectRow::with_tail(
            vec![instance(h, Type::Variable(ty))].into_boxed_slice(),
            EffectRowVariable::Rigid(row),
            vec![instance(excluded, Type::Variable(ty))].into_boxed_slice(),
        ));
        let types = HashMap::from([(ty, Type::Int)]);
        let rows = HashMap::from([(row, EffectRow::singleton(instance(g, Type::Variable(ty))))]);
        let mut work = TypeWorkBudget::unbounded();
        let substituted =
            substitute_kinded_argument_with(&original, &types, &rows, |units| work.charge(units))
                .unwrap()
                .unwrap();
        let KindedArgument::RowArg(result) = substituted else {
            panic!("row tag retained")
        };
        assert!(result.tail().is_none());
        assert!(result.known().contains(&instance(h, Type::Int)));
        // The replacement is inserted once; its own free Type variable is not
        // rewritten by the simultaneously applied Type replacement.
        assert!(result.known().contains(&instance(g, Type::Variable(ty))));
        let forbidden = HashMap::from([(row, EffectRow::singleton(instance(excluded, Type::Int)))]);
        assert!(
            substitute_kinded_argument_with(&original, &types, &forbidden, |units| work
                .charge(units))
            .unwrap()
            .is_err()
        );
        assert!(
            substitute_kinded_argument_with(&original, &types, &rows, |units| {
                TypeWorkBudget::with_limit(0).charge(units)
            })
            .is_err()
        );
    }

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
    fn complete_budgeted_type_hash_preserves_rows_kinds_and_pure_function_equivalence() {
        let module = ModuleId::new(0);
        let variable = TypeVariableId::new(0);
        let owner = ResourceDefinitionId::new(module, 0);
        let effect = EffectId::new(module, 0);
        let row = EffectRow::with_tail(
            Box::new([EffectInstance::new_kinded(
                effect,
                Box::new([
                    KindedArgument::RowArg(EffectRow::empty()),
                    KindedArgument::TypeArg(Type::Bytes),
                ]),
            )]),
            EffectRowVariable::rigid(variable),
            Box::new([EffectInstance::new(EffectId::new(module, 1), Box::new([]))]),
        );
        let complete = Type::Forall(
            Box::new([(
                variable,
                Kind::Arrow(Box::new(Kind::EffectRow), Box::new(Kind::Type)),
            )]),
            Box::new(Type::EffectfulFunction(
                Box::new(Type::ResourceApply(
                    owner,
                    Box::new([
                        KindedArgument::RowArg(row),
                        KindedArgument::TypeArg(Type::String),
                    ]),
                )),
                Box::new(ComputationType::new(Type::Int, EffectRow::empty())),
            )),
        );
        let mut admission = TypeWorkBudget::unbounded();
        charge_type_cells(&complete, &mut admission).unwrap();
        let mut raw = DefaultHasher::new();
        complete.hash(&mut raw);
        for prefix in [0, 9] {
            let mut exact = TypeWorkBudget::with_limit(prefix + admission.used());
            exact.charge(prefix).unwrap();
            let mut hashed = DefaultHasher::new();
            hash_type_with_budget(&complete, &mut hashed, &mut exact).unwrap();
            assert_eq!(exact.used(), prefix + admission.used());
            assert_eq!(hashed.finish(), raw.finish());
            let mut short = TypeWorkBudget::with_limit(prefix + admission.used() - 1);
            short.charge(prefix).unwrap();
            assert_eq!(
                hash_type_with_budget(&complete, &mut DefaultHasher::new(), &mut short,),
                Err(())
            );
        }
        let pure = Type::function(Type::Unit, Type::Int);
        let empty_effectful = Type::EffectfulFunction(
            Box::new(Type::Unit),
            Box::new(ComputationType::new(Type::Int, EffectRow::empty())),
        );
        assert!(
            same_type_with_budget(&pure, &empty_effectful, &mut TypeWorkBudget::unbounded(),)
                .unwrap()
        );
        let mut left = DefaultHasher::new();
        let mut right = DefaultHasher::new();
        hash_type_with_budget(&pure, &mut left, &mut TypeWorkBudget::unbounded()).unwrap();
        hash_type_with_budget(
            &empty_effectful,
            &mut right,
            &mut TypeWorkBudget::unbounded(),
        )
        .unwrap();
        assert_eq!(left.finish(), right.finish());
        discard_type_iteratively(complete);
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
    fn borrowed_replacement_transport_keeps_shadowing_rows_and_owned_results() {
        let shadowed = TypeVariableId::new(81);
        let actual = TypeVariableId::new(82);
        let nested = TypeVariableId::new(83);
        let row_variable = TypeVariableId::new(84);
        let effect = EffectId::new(ModuleId::new(81), 0);
        let excluded = EffectId::new(ModuleId::new(81), 1);
        // Deliberately noncanonical empty-effect Function input. The old
        // transport clones it before substitution; the borrowed route must
        // produce exactly the same final canonical result without that clone.
        let replacement = Type::EffectfulFunction(
            Box::new(Type::Variable(nested)),
            Box::new(ComputationType::new(
                Type::Variable(shadowed),
                EffectRow::empty(),
            )),
        );
        let originals = HashMap::from([
            (shadowed, Type::Bool),
            (actual, replacement),
            (nested, Type::Int),
        ]);
        let borrowed: HashMap<_, _> = originals.iter().map(|(id, ty)| (*id, ty)).collect();
        let mut owned = HashMap::new();
        let mut setup = TypeWorkBudget::unbounded();
        for (id, ty) in &originals {
            owned.insert(*id, clone_type_with_budget(ty, &mut setup).unwrap());
        }
        let row = effect_row_from_owned_parts_with_budget(
            vec![EffectInstance::new(
                effect,
                Box::new([Type::Variable(actual)]),
            )],
            Some((
                EffectRowVariable::rigid(row_variable),
                vec![EffectInstance::new(
                    excluded,
                    Box::new([Type::Variable(actual)]),
                )],
            )),
            &mut setup,
        )
        .unwrap();
        let source = Type::Forall(
            Box::new([(shadowed, Kind::Type)]),
            Box::new(Type::Tuple(Box::new([
                Type::Variable(shadowed),
                Type::Variable(actual),
                Type::function_computation(
                    Type::Unit,
                    ComputationType::new(Type::Variable(actual), row.clone()),
                ),
            ]))),
        );
        let rows = HashMap::new();
        let expected = substitute_type_and_row_variables_with(
            &source,
            &owned,
            &rows,
            |units| setup.charge(units),
            || (),
        )
        .unwrap()
        .unwrap();
        let mut measured = TypeWorkBudget::unbounded();
        let result = substitute_type_and_row_variables_borrowed_with(
            &source,
            &borrowed,
            &rows,
            |units| measured.charge(units),
            || (),
        )
        .unwrap()
        .unwrap();
        assert_eq!(result, expected);
        let Type::Forall(_, body) = &result else {
            panic!("forall retained")
        };
        let Type::Tuple(items) = body.as_ref() else {
            panic!("tuple retained")
        };
        assert_eq!(items[0], Type::Variable(shadowed));
        assert_eq!(
            items[1],
            Type::Function(
                Box::new(Type::Variable(nested)),
                Box::new(Type::Variable(shadowed)),
            )
        );
        let expected_row = row
            .substitute_type_variables_with_budget(&owned, &mut setup)
            .unwrap();
        let actual_row = row
            .substitute_type_variables_borrowed_with_budget(&borrowed, &mut setup)
            .unwrap();
        assert_eq!(actual_row, expected_row);
        let argument = KindedArgument::RowArg(row);
        let expected_argument =
            substitute_kinded_argument_with(&argument, &owned, &rows, |units| setup.charge(units))
                .unwrap()
                .unwrap();
        let actual_argument =
            substitute_kinded_argument_borrowed_with(&argument, &borrowed, &rows, |units| {
                setup.charge(units)
            })
            .unwrap()
            .unwrap();
        assert_eq!(actual_argument, expected_argument);
        let required = measured.used();
        for available in 0..required {
            let mut short = TypeWorkBudget::with_limit(available);
            assert!(
                substitute_type_and_row_variables_borrowed_with(
                    &source,
                    &borrowed,
                    &rows,
                    |units| short.charge(units),
                    || (),
                )
                .is_err()
            );
            let mut retry = TypeWorkBudget::with_limit(required);
            assert_eq!(
                substitute_type_and_row_variables_borrowed_with(
                    &source,
                    &borrowed,
                    &rows,
                    |units| retry.charge(units),
                    || (),
                )
                .unwrap()
                .unwrap(),
                expected
            );
            assert_eq!(retry.used(), required);
        }
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
        // One initial work slot, an application and two expanded scalars.
        let mut exact = 4usize;
        let mut short = 3usize;

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
        // The final retained tuple reservation charges all 16 slots atomically.
        assert_eq!(remaining, 10);
    }

    #[test]
    fn nested_forall_substitution_uses_linear_active_shadow_counts() {
        const DEPTH: usize = 2_048;
        const WIDTH: usize = 2_048;
        // One initial work slot and one overlapping replacement-key shadow-map record; D retained forall nodes,
        // binder records, and Kind nodes; enter and exit transitions for the
        // shadowed key at every depth; one tuple, one directly shadowed
        // variable, and W non-recursive replacement variables.
        // The tuple retains WIDTH + 1 element slots in addition to its nodes.
        const EXACT_WORK: usize = 2 + (3 * DEPTH) + (2 * DEPTH) + 1 + 1 + WIDTH + WIDTH + 1;

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
                let body = IterativeTypeOwner::new(body);
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
                    let rebuilt = IterativeTypeOwner::new(rebuilt);
                    assert_eq!(exact, 0);
                    let mut current = &*rebuilt;
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
                    drop(rebuilt);
                }
                drop(body);
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
        const EXACT_WORK: usize = 1 + 1 + (2 * WIDTH) + 1;

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
        // Include the initial work slot in both boundaries.
        const DEEP_RESULT_CELLS: usize = 2 * DEPTH + 2;
        // The tuple, one scalar per element and the retained element slots.
        const WIDE_RESULT_CELLS: usize = 2 + 2 * WIDTH;

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
                struct Replacements(HashMap<TypeVariableId, Type>);
                impl Drop for Replacements {
                    fn drop(&mut self) {
                        for (_, ty) in self.0.drain() {
                            discard_type_iteratively(ty);
                        }
                    }
                }
                let parameter = TypeVariableId::new(0);
                let owner = NominalTypeId::new(ModuleId::new(0), 0);
                let source = Type::Variable(parameter);
                let mut replacements = Replacements(HashMap::from([(
                    parameter,
                    Type::apply_arguments(Type::Nominal(owner), vec![Type::Unit; DEPTH]),
                )]));

                let mut deep_short = DEEP_RESULT_CELLS - 1;
                assert_eq!(
                    substitute_type_variables_with(&source, &replacements.0, |cells| {
                        deep_short = deep_short.checked_sub(cells).ok_or(())?;
                        Ok::<(), ()>(())
                    }, || ()),
                    Err(()),
                );
                assert_eq!(deep_short, 0);
                assert_deep_application(
                    replacements
                        .0
                        .get(&parameter)
                        .expect("one-short substitution must retain its borrowed replacement"),
                    DEPTH,
                    owner,
                );

                let mut deep_exact = DEEP_RESULT_CELLS;
                let rebuilt = substitute_type_variables_with(
                    &source,
                    &replacements.0,
                    |cells| {
                        deep_exact = deep_exact.checked_sub(cells).ok_or(())?;
                        Ok::<(), ()>(())
                    },
                    || (),
                )
                .expect("the exact deep expanded-result budget should fit");
                let rebuilt = IterativeTypeOwner::new(rebuilt);
                assert_eq!(deep_exact, 0);
                assert_deep_application(&rebuilt, DEPTH, owner);
                drop(rebuilt);
                discard_type_iteratively(
                    replacements
                        .0
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
                assert_eq!(wide_short, WIDTH - 1);
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
            [KindedArgument::TypeArg(Type::Variable(_))]
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
            let mut work = TypeWorkBudget::with_limit(if lacks { 8 } else { 7 });
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
                    vec![1, 2, 1, 1, 1, 0, 1, 1, width]
                } else {
                    vec![1, 2, 1, 1, 1, 1, width]
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
                        KindedArgument::TypeArg(Type::Variable(second)),
                        "replacement values must not be substituted a second time",
                    );
                    let tail = computation.effects.tail.as_ref().unwrap();
                    assert_eq!(
                        tail.lacks[1].arguments[0],
                        KindedArgument::TypeArg(Type::Bool)
                    );
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

    #[test]
    fn mixed_owner_structural_budget_and_partial_storage_refusal_use_small_stack() {
        std::thread::Builder::new()
            .stack_size(256 * 1024)
            .spawn(|| {
                let module = ModuleId::new(0);
                let resource = ResourceDefinitionId::new(module, 0);
                let effect = EffectId::new(module, 0);
                // Raw graph ownership evidence, not a well-kinded resource application.
                let mut ty = Type::Unit;
                for _ in 0..4_096 {
                    ty = Type::ResourceApply(
                        resource,
                        Box::new([KindedArgument::RowArg(EffectRow::singleton(
                            EffectInstance::new_kinded(
                                effect,
                                Box::new([KindedArgument::TypeArg(ty)]),
                            ),
                        ))]),
                    );
                }
                let source = IterativeTypeOwner::new(ty);
                let mut measured = TypeWorkBudget::unbounded();
                assert_eq!(
                    same_type_with_budget(&source, &source, &mut measured),
                    Ok(true)
                );
                assert_eq!(
                    same_type_with_budget(
                        &source,
                        &source,
                        &mut TypeWorkBudget::with_limit(measured.used() - 1)
                    ),
                    Err(())
                );
                assert_eq!(
                    same_type_with_budget(
                        &source,
                        &source,
                        &mut TypeWorkBudget::with_limit(measured.used())
                    ),
                    Ok(true)
                );
                {
                    let _fault =
                        row_reservation_fault::fail(RowReservationSite::ComparisonWork, 32);
                    assert_eq!(
                        same_type_with_budget(&source, &source, &mut TypeWorkBudget::unbounded()),
                        Err(())
                    );
                    assert_eq!(row_reservation_fault::hits(), 33);
                }
                {
                    // Fail after complete inner alternating fragments were staged.
                    let _fault =
                        row_reservation_fault::fail(RowReservationSite::CloneArguments, 1_024);
                    assert_eq!(
                        clone_type_with_budget(&source, &mut TypeWorkBudget::unbounded()),
                        Err(())
                    );
                    assert_eq!(row_reservation_fault::hits(), 1_025);
                }
                let mut copied_work = TypeWorkBudget::unbounded();
                let copied = IterativeTypeOwner::new(
                    clone_type_with_budget(&source, &mut copied_work).unwrap(),
                );
                assert_eq!(&*source, &*copied);
                assert_eq!(
                    clone_type_with_budget(
                        &source,
                        &mut TypeWorkBudget::with_limit(copied_work.used() - 1)
                    ),
                    Err(())
                );
                let _exact = IterativeTypeOwner::new(
                    clone_type_with_budget(
                        &source,
                        &mut TypeWorkBudget::with_limit(copied_work.used()),
                    )
                    .unwrap(),
                );
            })
            .expect("the mixed structural refusal thread starts")
            .join()
            .expect("staged mixed owners drain within the predecessor stack bound");
    }
}

/// Checks existing rigid-tail absence authority without strengthening any row.
/// Both source checking and final original reconstruction supply independently
/// derived outer environments. Nested forall ownership was already shielded by
/// the ordinary complete-type collector. This comparison does not strengthen a
/// rigid binder or change its identity.
pub(crate) fn rigid_row_requirements_entailed_with_budget(
    required: &HashMap<TypeVariableId, EffectRow>,
    contexts: &[HashMap<TypeVariableId, EffectRow>],
    budget: &mut TypeWorkBudget,
) -> Result<bool, ()> {
    for (binder, row) in required {
        budget.charge(1)?;
        let Some(tail) = row.tail() else {
            return Ok(false);
        };
        if !row.known().is_empty() || tail.variable() != EffectRowVariable::rigid(*binder) {
            return Ok(false);
        }
        for instance in tail.lacks() {
            budget.charge(1)?;
            let mut found = false;
            for context in contexts {
                budget.charge(1)?;
                let Some(existing) = context.get(binder) else {
                    continue;
                };
                let Some(existing_tail) = existing.tail() else {
                    return Ok(false);
                };
                if !existing.known().is_empty()
                    || existing_tail.variable() != EffectRowVariable::rigid(*binder)
                {
                    return Ok(false);
                }
                for established in existing_tail.lacks() {
                    if compare_effect_instances_with_budget(instance, established, budget)?
                        == std::cmp::Ordering::Equal
                    {
                        found = true;
                        break;
                    }
                }
                if found {
                    break;
                }
            }
            if !found {
                return Ok(false);
            }
        }
    }
    Ok(true)
}

/// Collects the row exclusions required by an effectful Core scheme.
/// Nested schemes own their variables; callers qualify one scheme body.
pub(crate) fn qualify_scheme_row_replacements_with_budget(
    ty: &Type,
    replacements: &std::collections::HashMap<TypeVariableId, Type>,
    row_replacements: &mut std::collections::HashMap<TypeVariableId, EffectRow>,
    include_free: bool,
    budget: &mut TypeWorkBudget,
) -> Result<(), ()> {
    // The common first-order pure arrow has no row contract to collect.
    // This fixed-size shape check avoids a second work queue for it.
    let atomic = |ty: &Type| {
        matches!(
            ty,
            Type::Bytes
                | Type::String
                | Type::Int
                | Type::Bool
                | Type::Unit
                | Type::Nominal(_)
                | Type::Variable(_)
                | Type::Inference(_)
        )
    };
    if atomic(ty)
        || matches!(ty, Type::Function(domain, codomain) if atomic(domain) && atomic(codomain))
    {
        return Ok(());
    }
    enum Task<'a> {
        Type(&'a Type),
        Argument(&'a KindedArgument),
        Row(&'a EffectRow),
    }
    fn push<'a>(
        pending: &mut Vec<Task<'a>>,
        budget: &mut TypeWorkBudget,
        task: Task<'a>,
    ) -> Result<(), ()> {
        budget.charge(1)?;
        pending.try_reserve(1).map_err(|_| ())?;
        pending.push(task);
        Ok(())
    }
    let mut exclusions: std::collections::HashMap<_, Vec<_>> = std::collections::HashMap::new();
    let mut pending = Vec::new();
    budget.charge(1)?;
    pending.try_reserve(1).map_err(|_| ())?;
    pending.push(Task::Type(ty));
    while let Some(task) = pending.pop() {
        match task {
            Task::Type(Type::Tuple(elements)) => {
                for element in elements {
                    push(&mut pending, budget, Task::Type(element))?;
                }
            }
            Task::Type(Type::Application(left, right) | Type::Function(left, right)) => {
                push(&mut pending, budget, Task::Type(left))?;
                push(&mut pending, budget, Task::Type(right))?;
            }
            Task::Type(
                Type::ResourceApply(_, arguments) | Type::ForeignOwnerApply(_, arguments),
            ) => {
                for argument in arguments {
                    push(&mut pending, budget, Task::Argument(argument))?;
                }
            }
            Task::Type(Type::EffectfulFunction(domain, codomain)) => {
                push(&mut pending, budget, Task::Type(domain))?;
                push(&mut pending, budget, Task::Type(&codomain.value))?;
                push(&mut pending, budget, Task::Row(&codomain.effects))?;
            }
            Task::Argument(KindedArgument::TypeArg(ty)) => {
                push(&mut pending, budget, Task::Type(ty))?
            }
            Task::Argument(KindedArgument::RowArg(row)) => {
                push(&mut pending, budget, Task::Row(row))?
            }
            Task::Row(row) => {
                let count = row
                    .known()
                    .len()
                    .checked_add(row.tail().map_or(0, |tail| tail.lacks().len()))
                    .ok_or(())?;
                budget.charge(count)?;
                for instance in row
                    .known()
                    .iter()
                    .chain(row.tail().into_iter().flat_map(|tail| tail.lacks()))
                {
                    for argument in instance.arguments() {
                        push(&mut pending, budget, Task::Argument(argument))?;
                    }
                }
                if let Some(tail) = row.tail()
                    && !tail.lacks().is_empty()
                    && let EffectRowVariable::Rigid(binder) = tail.variable()
                    && (include_free || row_replacements.contains_key(&binder))
                {
                    budget.charge(tail.lacks().len().checked_add(1).ok_or(())?)?;
                    exclusions.try_reserve(1).map_err(|_| ())?;
                    let retained = exclusions.entry(binder).or_default();
                    retained.try_reserve(tail.lacks().len()).map_err(|_| ())?;
                    retained.extend(tail.lacks());
                }
            }
            // Nested schemes bind their own variables.
            Task::Type(
                Type::Forall(_, _)
                | Type::Bytes
                | Type::String
                | Type::Int
                | Type::Bool
                | Type::Unit
                | Type::Nominal(_)
                | Type::Variable(_)
                | Type::Inference(_),
            ) => {}
        }
    }
    let mut qualified = Vec::new();
    budget.charge(exclusions.len())?;
    qualified.try_reserve(exclusions.len()).map_err(|_| ())?;
    for (binder, lacks) in exclusions {
        let variable = row_replacements
            .get(&binder)
            .and_then(EffectRow::tail)
            .map_or(EffectRowVariable::rigid(binder), |tail| tail.variable());
        let row = rebuild_effect_row_with_budget(
            std::iter::empty(),
            Some(variable),
            lacks,
            |argument, budget| {
                substitute_type_and_row_variables_with(
                    argument,
                    replacements,
                    row_replacements,
                    |cells| budget.charge(cells),
                    || (),
                )?
                .map_err(|_| ())
            },
            budget,
        )?;
        qualified.push((binder, row));
    }
    for (binder, row) in qualified {
        budget.charge(1)?;
        row_replacements.try_reserve(1).map_err(|_| ())?;
        row_replacements.insert(binder, row);
    }
    Ok(())
}

#[cfg(test)]
mod lexical_row_context_tests {
    use super::*;

    #[test]
    fn enclosing_row_facts_reach_nested_owner_payloads_without_crossing_forall() {
        let file = crate::source::SourceFile::new("lexical-row-context.ash", "owner").unwrap();
        let module = ModuleId::from(file.id());
        let delta = TypeVariableId::resolved(module, 0);
        let epsilon = TypeVariableId::resolved(module, 1);
        let h = EffectInstance::new(EffectId::new(module, 0), Box::new([]));
        let g = EffectInstance::new(EffectId::new(module, 1), Box::new([]));
        let plain = |binder| EffectRow::open(EffectRowVariable::Rigid(binder), Box::new([]));
        let qualified = |binder, effect: EffectInstance| {
            EffectRow::open(EffectRowVariable::Rigid(binder), Box::new([effect]))
        };
        let function =
            |row| Type::function_computation(Type::Unit, ComputationType::new(Type::Unit, row));
        let argument = KindedArgument::TypeArg(Type::Tuple(Box::new([
            function(plain(delta)),
            Type::Forall(
                Box::new([(delta, Kind::EffectRow)]),
                Box::new(function(plain(delta))),
            ),
            function(EffectRow::singleton(EffectInstance::new_kinded(
                EffectId::new(module, 2),
                Box::new([KindedArgument::RowArg(plain(epsilon))]),
            ))),
        ])));
        let expected = KindedArgument::TypeArg(Type::Tuple(Box::new([
            function(qualified(delta, h.clone())),
            Type::Forall(
                Box::new([(delta, Kind::EffectRow)]),
                Box::new(function(plain(delta))),
            ),
            function(EffectRow::singleton(EffectInstance::new_kinded(
                EffectId::new(module, 2),
                Box::new([KindedArgument::RowArg(qualified(epsilon, g.clone()))]),
            ))),
        ])));
        let contexts = [
            HashMap::from([(delta, qualified(delta, h))]),
            HashMap::from([(epsilon, qualified(epsilon, g))]),
        ];
        let mut measured = TypeWorkBudget::default();
        assert_eq!(
            qualify_kinded_argument_with_row_contexts_with_budget(
                &argument,
                contexts.iter(),
                &mut measured
            )
            .unwrap()
            .unwrap()
            .unwrap(),
            expected
        );
        let exact = measured.used();
        for prefix in [0, 7] {
            for limit in [exact - 1, exact, exact] {
                let mut work = TypeWorkBudget::with_limit(prefix + limit);
                work.charge(prefix).unwrap();
                let result = qualify_kinded_argument_with_row_contexts_with_budget(
                    &argument,
                    contexts.iter(),
                    &mut work,
                );
                if limit < exact {
                    assert!(result.is_err());
                } else {
                    assert_eq!(result.unwrap().unwrap().unwrap(), expected);
                    assert_eq!(work.used(), prefix + exact);
                }
            }
        }
        // Zero-argument known/lacks labels still contribute actual visits.
        let label_only = KindedArgument::TypeArg(function(EffectRow::singleton(
            EffectInstance::new(EffectId::new(module, 3), Box::new([])),
        )));
        for (root, has_rigid) in [(&argument, true), (&label_only, false)] {
            let mut measured = TypeWorkBudget::default();
            assert_eq!(
                kinded_arguments_have_rigid_rows_with_budget(std::iter::once(root), &mut measured)
                    .unwrap(),
                has_rigid
            );
            let exact = measured.used();
            for prefix in [0, 7] {
                for limit in [exact - 1, exact, exact] {
                    let mut work = TypeWorkBudget::with_limit(prefix + limit);
                    work.charge(prefix).unwrap();
                    let result = kinded_arguments_have_rigid_rows_with_budget(
                        std::iter::once(root),
                        &mut work,
                    );
                    if limit < exact {
                        assert!(result.is_err());
                    } else {
                        assert_eq!(result.unwrap(), has_rigid);
                        assert_eq!(work.used(), prefix + exact);
                    }
                }
            }
        }
    }
}

#[cfg(test)]
mod owned_tail_reconstruction_tests {
    use super::*;
    use crate::module::ModuleId;

    fn member(local: u32) -> EffectInstance {
        EffectInstance::new_kinded(
            EffectId::new(ModuleId::new(0), local),
            Box::new([
                KindedArgument::TypeArg(Type::Tuple(Box::new([Type::Int, Type::Bool]))),
                KindedArgument::RowArg(EffectRow::singleton(EffectInstance::new(
                    EffectId::new(ModuleId::new(0), 9),
                    Box::new([Type::String]),
                ))),
            ]),
        )
    }
    fn source() -> EffectRow {
        EffectRow::with_tail(
            Box::new([member(0)]),
            EffectRowVariable::rigid(TypeVariableId::new(0)),
            Box::new([member(1)]),
        )
    }
    fn old_template(
        row: &EffectRow,
        replacement: &EffectRow,
        work: &mut TypeWorkBudget,
    ) -> Result<Result<EffectRow, EffectRowError>, ()> {
        let target = EffectRowVariable::rigid(TypeVariableId::new(0));
        if replacement.known.is_empty()
            && replacement
                .tail
                .as_ref()
                .is_some_and(|tail| tail.variable == target)
        {
            rebuild_effect_row_with_budget(
                row.known.iter(),
                Some(target),
                row.tail
                    .iter()
                    .flat_map(|tail| tail.lacks.iter())
                    .chain(replacement.tail.iter().flat_map(|tail| tail.lacks.iter())),
                clone_type_with_budget,
                work,
            )
            .map(Ok)
        } else {
            row.substitute_tail_once_with_budget(target, replacement, work)
        }
    }
    fn run(
        replacement: &EffectRow,
        work: &mut TypeWorkBudget,
    ) -> Result<Result<EffectRow, EffectRowError>, ()> {
        source().substitute_owned_tail_for_reconstruction(
            EffectRowVariable::rigid(TypeVariableId::new(0)),
            replacement,
            work,
            allocation_error,
        )
    }
    #[test]
    fn owned_tail_reconstruction_matches_full_kinded_rows_and_failures() {
        let target = EffectRowVariable::rigid(TypeVariableId::new(0));
        let other = EffectRowVariable::rigid(TypeVariableId::new(1));
        let replacements = [
            EffectRow::closed(Box::new([member(2), member(3)])),
            EffectRow::with_tail(Box::new([member(2)]), other, Box::new([member(3)])),
            EffectRow::open(target, Box::new([member(1), member(3)])),
            EffectRow::singleton(member(1)),
            EffectRow::with_tail(Box::new([member(2)]), target, Box::new([])),
            EffectRow::singleton(member(0)),
        ];
        for replacement in &replacements {
            let before = replacement.clone();
            let expected =
                old_template(&source(), replacement, &mut TypeWorkBudget::default()).unwrap();
            assert_eq!(
                run(replacement, &mut TypeWorkBudget::default()).unwrap(),
                expected
            );
            assert_eq!(*replacement, before);
            let actual = substitute_row_for_template_with(
                &source(),
                &HashMap::new(),
                &HashMap::from([(TypeVariableId::new(0), replacement.clone())]),
                &HashMap::new(),
                &TemplateIdentityRenaming {
                    variables: &HashMap::new(),
                    nominals: &HashMap::new(),
                },
                |_: usize| Ok::<_, ()>(()),
                || (),
            )
            .unwrap();
            assert_eq!(actual, expected);
        }
        assert_eq!(
            run(&replacements[3], &mut TypeWorkBudget::default()),
            Ok(Err(EffectRowError::Missing))
        );
        assert_eq!(
            run(&replacements[4], &mut TypeWorkBudget::default()),
            Ok(Err(EffectRowError::Infinite))
        );
        assert_eq!(
            run(&replacements[5], &mut TypeWorkBudget::default()),
            Ok(Err(EffectRowError::Missing))
        );
        let mut old = TypeWorkBudget::default();
        old_template(&source(), &replacements[0], &mut old)
            .unwrap()
            .unwrap();
        let mut owned = TypeWorkBudget::default();
        run(&replacements[0], &mut owned).unwrap().unwrap();
        assert!(owned.used() < old.used());
    }
    #[test]
    fn owned_tail_reconstruction_pays_exact_prefix_short_spent_and_storage() {
        let replacement = EffectRow::closed(Box::new([member(2), member(3)]));
        let mut measured = TypeWorkBudget::default();
        let expected = run(&replacement, &mut measured).unwrap().unwrap();
        let cost = measured.used();
        for prefix in [0, 7] {
            let mut short = TypeWorkBudget::with_limit(prefix + cost - 1);
            short.charge(prefix).unwrap();
            assert_eq!(run(&replacement, &mut short), Err(()));
            for _ in 0..2 {
                let mut exact = TypeWorkBudget::with_limit(prefix + cost);
                exact.charge(prefix).unwrap();
                assert_eq!(run(&replacement, &mut exact), Ok(Ok(expected.clone())));
                assert_eq!(exact.used(), prefix + cost);
                assert_eq!(run(&replacement, &mut exact), Err(()));
                assert_eq!(exact.used(), prefix + cost);
            }
        }
        for site in [
            RowReservationSite::RebuildMembers,
            RowReservationSite::CanonicalMembers,
        ] {
            let input = source();
            let _fault = row_reservation_fault::fail(site, 0);
            let mut work = TypeWorkBudget::default();
            assert_eq!(
                input.substitute_owned_tail_for_reconstruction(
                    EffectRowVariable::rigid(TypeVariableId::new(0)),
                    &replacement,
                    &mut work,
                    allocation_error,
                ),
                Err(())
            );
            assert!(work.used() > 0);
        }
    }
}
