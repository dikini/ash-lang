//! Iterative ownership and copies for alternating Type and complete owner rows.

use super::{
    ComputationType, EffectId, EffectInstance, EffectRow, EffectRowTail, EffectRowVariable,
    IterativeTypeOwner, Kind, KindedArgument, ResourceDefinitionId, RowReservationSite, Type,
    TypeVariableId, TypeWorkMeter, allocation_error, charge_kinded_type_parameters,
    discard_type_iteratively, effect_row_from_owned_parts_with_budget_and_failure, reserve_row,
};

#[derive(Clone, Copy)]
pub(super) enum StructuralRoot<'a> {
    Type(&'a Type),
    Argument(&'a KindedArgument),
    Row(&'a EffectRow),
    Instance(&'a EffectInstance),
}

enum StructuralOwned {
    Type(Type),
    Argument(KindedArgument),
    Row(EffectRow),
    Instance(EffectInstance),
}

pub(super) struct StructuralValue(Option<StructuralOwned>);

impl StructuralValue {
    fn new(value: StructuralOwned) -> Self {
        Self(Some(value))
    }
    pub(super) fn type_value(ty: Type) -> Self {
        Self::new(StructuralOwned::Type(ty))
    }
    pub(super) fn argument_value(argument: KindedArgument) -> Self {
        Self::new(StructuralOwned::Argument(argument))
    }
    pub(super) fn row_value(row: EffectRow) -> Self {
        Self::new(StructuralOwned::Row(row))
    }
    pub(super) fn into_inner(self) -> Type {
        self.into_type()
            .expect("a Type reconstruction value has Type shape")
    }
    pub(super) fn into_argument_inner(self) -> KindedArgument {
        self.into_argument()
            .expect("an argument reconstruction value has argument shape")
    }
    pub(super) fn into_type(mut self) -> Result<Type, ()> {
        match self.0.take().expect("a structural value is consumed once") {
            StructuralOwned::Type(value) => Ok(value),
            other => {
                discard_owned(other);
                Err(())
            }
        }
    }
    pub(super) fn into_argument(mut self) -> Result<KindedArgument, ()> {
        match self.0.take().expect("a structural value is consumed once") {
            StructuralOwned::Argument(value) => Ok(value),
            other => {
                discard_owned(other);
                Err(())
            }
        }
    }
    pub(super) fn into_row(mut self) -> Result<EffectRow, ()> {
        match self.0.take().expect("a structural value is consumed once") {
            StructuralOwned::Row(value) => Ok(value),
            other => {
                discard_owned(other);
                Err(())
            }
        }
    }
    pub(super) fn into_instance(mut self) -> Result<EffectInstance, ()> {
        match self.0.take().expect("a structural value is consumed once") {
            StructuralOwned::Instance(value) => Ok(value),
            other => {
                discard_owned(other);
                Err(())
            }
        }
    }
}

impl Drop for StructuralValue {
    fn drop(&mut self) {
        if let Some(value) = self.0.take() {
            discard_owned(value);
        }
    }
}

fn discard_owned(value: StructuralOwned) {
    match value {
        StructuralOwned::Type(value) => discard_type_iteratively(value),
        StructuralOwned::Argument(value) => discard_kinded_argument_iteratively(value),
        StructuralOwned::Row(value) => discard_row_iteratively(value),
        StructuralOwned::Instance(mut value) => {
            for argument in std::mem::take(&mut value.arguments).into_vec() {
                discard_kinded_argument_iteratively(argument);
            }
        }
    }
}

pub(super) fn charge_structural<B: TypeWorkMeter>(
    root: StructuralRoot<'_>,
    budget: &mut B,
) -> Result<(), B::Error> {
    fn schedule<'a, B: TypeWorkMeter>(
        pending: &mut Vec<StructuralRoot<'a>>,
        root: StructuralRoot<'a>,
        budget: &mut B,
    ) -> Result<(), B::Error> {
        let root = match root {
            StructuralRoot::Argument(KindedArgument::TypeArg(ty)) => StructuralRoot::Type(ty),
            StructuralRoot::Argument(KindedArgument::RowArg(row)) => StructuralRoot::Row(row),
            root => root,
        };
        // The existing node charge covers its pending record; admit it before
        // reserving or retaining that record, rather than charging at pop.
        budget.charge(1)?;
        pending
            .try_reserve(1)
            .map_err(|_| allocation_error(budget))?;
        pending.push(root);
        Ok(())
    }
    let mut pending = Vec::new();
    schedule(&mut pending, root, budget)?;
    while let Some(root) = pending.pop() {
        match root {
            StructuralRoot::Type(ty) => match ty {
                Type::Tuple(elements) => {
                    for element in elements {
                        schedule(&mut pending, StructuralRoot::Type(element), budget)?;
                    }
                }
                Type::Application(left, right) | Type::Function(left, right) => {
                    schedule(&mut pending, StructuralRoot::Type(left), budget)?;
                    schedule(&mut pending, StructuralRoot::Type(right), budget)?;
                }
                Type::ResourceApply(_, arguments) => {
                    for argument in arguments {
                        schedule(&mut pending, StructuralRoot::Argument(argument), budget)?;
                    }
                }
                Type::EffectfulFunction(domain, codomain) => {
                    budget.charge(1)?;
                    schedule(&mut pending, StructuralRoot::Type(domain), budget)?;
                    schedule(&mut pending, StructuralRoot::Type(&codomain.value), budget)?;
                    schedule(&mut pending, StructuralRoot::Row(&codomain.effects), budget)?;
                }
                Type::Forall(parameters, body) => {
                    charge_kinded_type_parameters(parameters, budget)?;
                    schedule(&mut pending, StructuralRoot::Type(body), budget)?;
                }
                Type::Int
                | Type::Bool
                | Type::Unit
                | Type::Nominal(_)
                | Type::Variable(_)
                | Type::Inference(_) => {}
            },
            StructuralRoot::Argument(_) => {
                unreachable!("argument tags are normalized before retention")
            }
            StructuralRoot::Instance(instance) => {
                for argument in &instance.arguments {
                    schedule(&mut pending, StructuralRoot::Argument(argument), budget)?;
                }
            }
            StructuralRoot::Row(row) => {
                for instance in &row.known {
                    schedule(&mut pending, StructuralRoot::Instance(instance), budget)?;
                }
                if let Some(tail) = &row.tail {
                    budget.charge(1)?;
                    for instance in &tail.lacks {
                        schedule(&mut pending, StructuralRoot::Instance(instance), budget)?;
                    }
                }
            }
        }
    }
    Ok(())
}

pub(super) fn clone_structural<B: TypeWorkMeter>(
    root: StructuralRoot<'_>,
    budget: &mut B,
) -> Result<StructuralValue, B::Error> {
    clone_structural_with_failure(root, budget, &mut allocation_error)
}

pub(super) fn clone_structural_with_failure<B: TypeWorkMeter>(
    root: StructuralRoot<'_>,
    budget: &mut B,
    storage_error: &mut impl FnMut(&mut B) -> B::Error,
) -> Result<StructuralValue, B::Error> {
    // Leaf copies need no reconstruction storage. Keep their frame separate
    // from the compound worklist: callers such as pattern admission already
    // have large bounded frames on the predecessor's small stack.
    if let StructuralRoot::Type(ty) = root {
        let leaf = match ty {
            Type::Int => Some(Type::Int),
            Type::Bool => Some(Type::Bool),
            Type::Unit => Some(Type::Unit),
            Type::Nominal(id) => Some(Type::Nominal(*id)),
            Type::Variable(id) => Some(Type::Variable(*id)),
            Type::Inference(id) => Some(Type::Inference(*id)),
            _ => None,
        };
        if let Some(leaf) = leaf {
            budget.charge(1)?;
            return Ok(StructuralValue::type_value(leaf));
        }
    }
    clone_compound_structural_with_failure(root, budget, storage_error)
}

#[inline(never)]
fn clone_compound_structural_with_failure<B: TypeWorkMeter>(
    root: StructuralRoot<'_>,
    budget: &mut B,
    storage_error: &mut impl FnMut(&mut B) -> B::Error,
) -> Result<StructuralValue, B::Error> {
    enum Task<'a> {
        Visit(StructuralRoot<'a>),
        Tuple(usize),
        Application,
        Resource(ResourceDefinitionId, usize),
        Function,
        EffectfulFunction,
        Forall(Box<[(TypeVariableId, Kind)]>),
        TypeArgument,
        RowArgument,
        Instance(EffectId, usize),
        Row(usize, Option<(EffectRowVariable, usize)>),
    }
    charge_structural(root, budget)?;
    let mut pending = Vec::new();
    pending.try_reserve(1).map_err(|_| storage_error(budget))?;
    pending.push(Task::Visit(root));
    let mut values: Vec<StructuralValue> = Vec::new();
    while let Some(task) = pending.pop() {
        // The preceding whole-graph charge admits these proportional records.
        pending.try_reserve(3).map_err(|_| storage_error(budget))?;
        values.try_reserve(1).map_err(|_| storage_error(budget))?;
        match task {
            Task::Visit(StructuralRoot::Type(ty)) => match ty {
                Type::Int => values.push(StructuralValue::new(StructuralOwned::Type(Type::Int))),
                Type::Bool => values.push(StructuralValue::new(StructuralOwned::Type(Type::Bool))),
                Type::Unit => values.push(StructuralValue::new(StructuralOwned::Type(Type::Unit))),
                Type::Nominal(id) => values.push(StructuralValue::new(StructuralOwned::Type(
                    Type::Nominal(*id),
                ))),
                Type::Variable(id) => values.push(StructuralValue::new(StructuralOwned::Type(
                    Type::Variable(*id),
                ))),
                Type::Inference(id) => values.push(StructuralValue::new(StructuralOwned::Type(
                    Type::Inference(*id),
                ))),
                Type::Tuple(elements) => {
                    pending
                        .try_reserve(
                            elements
                                .len()
                                .checked_add(1)
                                .ok_or_else(|| storage_error(budget))?,
                        )
                        .map_err(|_| storage_error(budget))?;
                    pending.push(Task::Tuple(elements.len()));
                    pending.extend(
                        elements
                            .iter()
                            .rev()
                            .map(|ty| Task::Visit(StructuralRoot::Type(ty))),
                    );
                }
                Type::ResourceApply(id, arguments) => {
                    pending
                        .try_reserve(
                            arguments
                                .len()
                                .checked_add(1)
                                .ok_or_else(|| storage_error(budget))?,
                        )
                        .map_err(|_| storage_error(budget))?;
                    pending.push(Task::Resource(*id, arguments.len()));
                    pending.extend(
                        arguments
                            .iter()
                            .rev()
                            .map(|arg| Task::Visit(StructuralRoot::Argument(arg))),
                    );
                }
                Type::Application(left, right) => {
                    pending.push(Task::Application);
                    pending.push(Task::Visit(StructuralRoot::Type(right)));
                    pending.push(Task::Visit(StructuralRoot::Type(left)));
                }
                Type::Function(left, right) => {
                    pending.push(Task::Function);
                    pending.push(Task::Visit(StructuralRoot::Type(right)));
                    pending.push(Task::Visit(StructuralRoot::Type(left)));
                }
                Type::EffectfulFunction(domain, codomain) => {
                    pending.try_reserve(4).map_err(|_| storage_error(budget))?;
                    pending.push(Task::EffectfulFunction);
                    pending.push(Task::Visit(StructuralRoot::Row(&codomain.effects)));
                    pending.push(Task::Visit(StructuralRoot::Type(&codomain.value)));
                    pending.push(Task::Visit(StructuralRoot::Type(domain)));
                }
                Type::Forall(parameters, body) => {
                    let mut copied = Vec::new();
                    copied
                        .try_reserve_exact(parameters.len())
                        .map_err(|_| storage_error(budget))?;
                    for (id, kind) in parameters {
                        copied.push((*id, clone_kind_precharged(kind, budget, storage_error)?));
                    }
                    pending.push(Task::Forall(copied.into_boxed_slice()));
                    pending.push(Task::Visit(StructuralRoot::Type(body)));
                }
            },
            Task::Visit(StructuralRoot::Argument(argument)) => match argument {
                KindedArgument::TypeArg(ty) => {
                    pending.push(Task::TypeArgument);
                    pending.push(Task::Visit(StructuralRoot::Type(ty)));
                }
                KindedArgument::RowArg(row) => {
                    pending.push(Task::RowArgument);
                    pending.push(Task::Visit(StructuralRoot::Row(row)));
                }
            },
            Task::Visit(StructuralRoot::Instance(instance)) => {
                pending
                    .try_reserve(
                        instance
                            .arguments
                            .len()
                            .checked_add(1)
                            .ok_or_else(|| storage_error(budget))?,
                    )
                    .map_err(|_| storage_error(budget))?;
                pending.push(Task::Instance(instance.effect, instance.arguments.len()));
                pending.extend(
                    instance
                        .arguments
                        .iter()
                        .rev()
                        .map(|arg| Task::Visit(StructuralRoot::Argument(arg))),
                );
            }
            Task::Visit(StructuralRoot::Row(row)) => {
                let count = row
                    .known
                    .len()
                    .checked_add(row.tail.as_ref().map_or(0, |tail| tail.lacks.len()))
                    .ok_or_else(|| storage_error(budget))?;
                reserve_row(
                    &mut pending,
                    count.checked_add(1).ok_or_else(|| storage_error(budget))?,
                    RowReservationSite::CloneMembers,
                )
                .map_err(|_| storage_error(budget))?;
                if let Some(tail) = &row.tail {
                    reserve_row(
                        &mut pending,
                        tail.lacks.len(),
                        RowReservationSite::CloneLacks,
                    )
                    .map_err(|_| storage_error(budget))?;
                }
                pending.push(Task::Row(
                    row.known.len(),
                    row.tail
                        .as_ref()
                        .map(|tail| (tail.variable, tail.lacks.len())),
                ));
                if let Some(tail) = &row.tail {
                    pending.extend(
                        tail.lacks
                            .iter()
                            .rev()
                            .map(|instance| Task::Visit(StructuralRoot::Instance(instance))),
                    );
                }
                pending.extend(
                    row.known
                        .iter()
                        .rev()
                        .map(|instance| Task::Visit(StructuralRoot::Instance(instance))),
                );
            }
            Task::Tuple(count) => {
                let mut children = Vec::new();
                reserve_row(&mut children, count, RowReservationSite::CloneArguments)
                    .map_err(|_| storage_error(budget))?;
                for value in values.drain(values.len() - count..) {
                    children.push(value.into_type().expect("tuple children have Type shape"));
                }
                values.push(StructuralValue::new(StructuralOwned::Type(Type::Tuple(
                    children.into_boxed_slice(),
                ))));
            }
            Task::Resource(id, count) => {
                let mut children = Vec::new();
                reserve_row(&mut children, count, RowReservationSite::CloneArguments)
                    .map_err(|_| storage_error(budget))?;
                for value in values.drain(values.len() - count..) {
                    children.push(
                        value
                            .into_argument()
                            .expect("resource children have argument shape"),
                    );
                }
                values.push(StructuralValue::new(StructuralOwned::Type(
                    Type::ResourceApply(id, children.into_boxed_slice()),
                )));
            }
            Task::Instance(id, count) => {
                let mut children = Vec::new();
                reserve_row(&mut children, count, RowReservationSite::CloneArguments)
                    .map_err(|_| storage_error(budget))?;
                for value in values.drain(values.len() - count..) {
                    children.push(
                        value
                            .into_argument()
                            .expect("instance children have argument shape"),
                    );
                }
                values.push(StructuralValue::new(StructuralOwned::Instance(
                    EffectInstance::new_kinded(id, children.into_boxed_slice()),
                )));
            }
            Task::Application | Task::Function => {
                let right = values
                    .pop()
                    .expect("binary right child")
                    .into_type()
                    .expect("binary child Type");
                let left = values
                    .pop()
                    .expect("binary left child")
                    .into_type()
                    .expect("binary child Type");
                let ty = if matches!(task, Task::Application) {
                    Type::Application(Box::new(left), Box::new(right))
                } else {
                    Type::function(left, right)
                };
                values.push(StructuralValue::new(StructuralOwned::Type(ty)));
            }
            Task::EffectfulFunction => {
                let row = values
                    .pop()
                    .expect("computation row")
                    .into_row()
                    .expect("row shape");
                let value = values
                    .pop()
                    .expect("computation value")
                    .into_type()
                    .expect("value Type");
                let domain = values
                    .pop()
                    .expect("function domain")
                    .into_type()
                    .expect("domain Type");
                values.push(StructuralValue::new(StructuralOwned::Type(
                    Type::function_computation(domain, ComputationType::new(value, row)),
                )));
            }
            Task::Forall(parameters) => {
                let body = values
                    .pop()
                    .expect("scheme body")
                    .into_type()
                    .expect("body Type");
                values.push(StructuralValue::new(StructuralOwned::Type(Type::Forall(
                    parameters,
                    Box::new(body),
                ))));
            }
            Task::TypeArgument => {
                let ty = values
                    .pop()
                    .expect("argument child")
                    .into_type()
                    .expect("Type argument child");
                values.push(StructuralValue::new(StructuralOwned::Argument(
                    KindedArgument::TypeArg(ty),
                )));
            }
            Task::RowArgument => {
                let row = values
                    .pop()
                    .expect("argument child")
                    .into_row()
                    .expect("row argument child");
                values.push(StructuralValue::new(StructuralOwned::Argument(
                    KindedArgument::RowArg(row),
                )));
            }
            Task::Row(known_count, tail) => {
                let lacks_count = tail.map_or(0, |(_, count)| count);
                let count = known_count
                    .checked_add(lacks_count)
                    .ok_or_else(|| storage_error(budget))?;
                let mut instances = Vec::new();
                let mut lacks = Vec::new();
                instances
                    .try_reserve_exact(known_count)
                    .map_err(|_| storage_error(budget))?;
                lacks
                    .try_reserve_exact(lacks_count)
                    .map_err(|_| storage_error(budget))?;
                for (position, value) in values.drain(values.len() - count..).enumerate() {
                    let instance = value.into_instance().expect("row instance shape");
                    if position < known_count {
                        instances.push(instance);
                    } else {
                        lacks.push(instance);
                    }
                }
                let row = EffectRow {
                    known: instances.into_boxed_slice(),
                    tail: tail.map(|(variable, _)| EffectRowTail {
                        variable,
                        lacks: lacks.into_boxed_slice(),
                    }),
                };
                values.push(StructuralValue::new(StructuralOwned::Row(row)));
            }
        }
    }
    Ok(values.pop().expect("one structural root was rebuilt"))
}

pub(super) fn clone_kind_precharged<B: TypeWorkMeter>(
    kind: &Kind,
    budget: &mut B,
    storage_error: &mut impl FnMut(&mut B) -> B::Error,
) -> Result<Kind, B::Error> {
    enum Task<'a> {
        Visit(&'a Kind),
        Arrow,
    }
    let mut pending = Vec::new();
    pending.try_reserve(1).map_err(|_| storage_error(budget))?;
    pending.push(Task::Visit(kind));
    let mut values = Vec::new();
    while let Some(task) = pending.pop() {
        pending.try_reserve(3).map_err(|_| storage_error(budget))?;
        values.try_reserve(1).map_err(|_| storage_error(budget))?;
        match task {
            Task::Visit(Kind::Type) => values.push(Kind::Type),
            Task::Visit(Kind::EffectRow) => values.push(Kind::EffectRow),
            Task::Visit(Kind::Arrow(domain, codomain)) => {
                pending.push(Task::Arrow);
                pending.push(Task::Visit(codomain));
                pending.push(Task::Visit(domain));
            }
            Task::Arrow => {
                let right = values.pop().expect("kind codomain");
                let left = values.pop().expect("kind domain");
                values.push(Kind::Arrow(Box::new(left), Box::new(right)));
            }
        }
    }
    Ok(values.pop().expect("one kind root"))
}

pub(crate) fn clone_kinded_argument_with_budget<B: TypeWorkMeter>(
    argument: &KindedArgument,
    budget: &mut B,
) -> Result<KindedArgument, B::Error> {
    Ok(
        clone_structural(StructuralRoot::Argument(argument), budget)?
            .into_argument()
            .expect("argument root shape"),
    )
}

pub(crate) fn discard_kinded_argument_iteratively(argument: KindedArgument) {
    match argument {
        KindedArgument::TypeArg(ty) => discard_type_iteratively(ty),
        KindedArgument::RowArg(row) => discard_row_iteratively(row),
    }
}

pub(super) fn discard_row_iteratively(mut row: EffectRow) {
    let known = std::mem::take(&mut row.known);
    let tail = row.tail.take();
    // One wrapper hands every nested argument to the same iterative Type drain.
    let effects = EffectRow { known, tail };
    discard_type_iteratively(Type::EffectfulFunction(
        Box::new(Type::Unit),
        Box::new(ComputationType {
            value: Type::Unit,
            effects,
        }),
    ));
}

/// Rebuilds nested row arguments while keeping the callback on ordinary Type leaves.
pub(crate) fn map_kinded_argument_types_with_budget<E, B: TypeWorkMeter>(
    argument: &KindedArgument,
    map: &mut impl FnMut(&Type, &mut B) -> Result<Type, E>,
    budget: &mut B,
    storage_error: &mut impl FnMut(&mut B) -> B::Error,
) -> Result<KindedArgument, E>
where
    E: From<B::Error>,
{
    enum Task<'a> {
        Argument(&'a KindedArgument),
        Row(&'a EffectRow),
        Instance(&'a EffectInstance),
        FinishArgument,
        FinishInstance(EffectId, usize),
        FinishRow(usize, Option<(EffectRowVariable, usize)>),
    }
    let mut pending = Vec::new();
    pending
        .try_reserve(1)
        .map_err(|_| E::from(storage_error(budget)))?;
    pending.push(Task::Argument(argument));
    let mut values: Vec<StructuralValue> = Vec::new();
    while let Some(task) = pending.pop() {
        pending
            .try_reserve(2)
            .map_err(|_| E::from(storage_error(budget)))?;
        values
            .try_reserve(1)
            .map_err(|_| E::from(storage_error(budget)))?;
        match task {
            Task::Argument(KindedArgument::TypeArg(ty)) => {
                let ty = map(ty, budget)?;
                values.push(StructuralValue::argument_value(KindedArgument::TypeArg(ty)));
            }
            Task::Argument(KindedArgument::RowArg(row)) => {
                budget.charge(1).map_err(E::from)?;
                pending.push(Task::FinishArgument);
                pending.push(Task::Row(row));
            }
            Task::Instance(instance) => {
                budget.charge(instance.arguments.len()).map_err(E::from)?;
                pending
                    .try_reserve(
                        instance
                            .arguments
                            .len()
                            .checked_add(1)
                            .ok_or_else(|| E::from(storage_error(budget)))?,
                    )
                    .map_err(|_| E::from(storage_error(budget)))?;
                pending.push(Task::FinishInstance(
                    instance.effect,
                    instance.arguments.len(),
                ));
                pending.extend(instance.arguments.iter().rev().map(Task::Argument));
            }
            Task::Row(row) => {
                let count = row
                    .known
                    .len()
                    .checked_add(row.tail.as_ref().map_or(0, |tail| tail.lacks.len()))
                    .ok_or_else(|| E::from(storage_error(budget)))?;
                budget.charge(count).map_err(E::from)?;
                if row.tail.is_some() {
                    budget.charge(1).map_err(E::from)?;
                }
                pending
                    .try_reserve(
                        count
                            .checked_add(1)
                            .ok_or_else(|| E::from(storage_error(budget)))?,
                    )
                    .map_err(|_| E::from(storage_error(budget)))?;
                pending.push(Task::FinishRow(
                    row.known.len(),
                    row.tail
                        .as_ref()
                        .map(|tail| (tail.variable, tail.lacks.len())),
                ));
                if let Some(tail) = &row.tail {
                    pending.extend(tail.lacks.iter().rev().map(Task::Instance));
                }
                pending.extend(row.known.iter().rev().map(Task::Instance));
            }
            Task::FinishArgument => {
                let row = values
                    .pop()
                    .expect("mapped argument row")
                    .into_row()
                    .expect("row shape");
                values.push(StructuralValue::argument_value(KindedArgument::RowArg(row)));
            }
            Task::FinishInstance(id, count) => {
                budget.charge(count).map_err(E::from)?;
                let mut arguments = Vec::new();
                reserve_row(&mut arguments, count, RowReservationSite::RebuildRetained)
                    .map_err(|_| E::from(storage_error(budget)))?;
                for value in values.drain(values.len() - count..) {
                    arguments.push(value.into_argument_inner());
                }
                values.push(StructuralValue::new(StructuralOwned::Instance(
                    EffectInstance::new_kinded(id, arguments.into_boxed_slice()),
                )));
            }
            Task::FinishRow(known_count, tail) => {
                let lacks_count = tail.map_or(0, |(_, count)| count);
                let count = known_count
                    .checked_add(lacks_count)
                    .ok_or_else(|| E::from(storage_error(budget)))?;
                let mut instances = Vec::new();
                let mut lacks = Vec::new();
                instances
                    .try_reserve_exact(known_count)
                    .map_err(|_| E::from(storage_error(budget)))?;
                lacks
                    .try_reserve_exact(lacks_count)
                    .map_err(|_| E::from(storage_error(budget)))?;
                for (position, value) in values.drain(values.len() - count..).enumerate() {
                    let instance = value.into_instance().expect("mapped row instance");
                    if position < known_count {
                        instances.push(instance);
                    } else {
                        lacks.push(instance);
                    }
                }
                let row = effect_row_from_owned_parts_with_budget_and_failure(
                    instances,
                    tail.map(|(variable, _)| (variable, lacks)),
                    budget,
                    &mut *storage_error,
                )
                .map_err(E::from)?;
                values.push(StructuralValue::row_value(row));
            }
        }
    }
    Ok(values
        .pop()
        .expect("mapped owner argument root")
        .into_argument_inner())
}

pub(crate) struct IterativeArgumentOwner(Option<KindedArgument>);
impl IterativeArgumentOwner {
    pub(crate) fn new(argument: KindedArgument) -> Self {
        Self(Some(argument))
    }
    pub(crate) fn as_ref(&self) -> &KindedArgument {
        self.0
            .as_ref()
            .expect("an argument owner retains its value until consumed")
    }
    pub(crate) fn into_inner(mut self) -> KindedArgument {
        self.0.take().expect("an argument owner is consumed once")
    }
}
impl std::ops::Deref for IterativeArgumentOwner {
    type Target = KindedArgument;
    fn deref(&self) -> &Self::Target {
        self.as_ref()
    }
}
impl Drop for IterativeArgumentOwner {
    fn drop(&mut self) {
        if let Some(argument) = self.0.take() {
            discard_kinded_argument_iteratively(argument);
        }
    }
}

/// Schedules ordinary Type children through complete owner rows for structural
/// analyses. This is not a native argument projection: row structure is visited
/// and charged, and the caller still owns validation of each owner signature.
pub(crate) fn extend_owner_type_children_with_charge<'a, B: TypeWorkMeter, I>(
    arguments: I,
    output: &mut Vec<&'a Type>,
    budget: &mut B,
) -> Result<bool, B::Error>
where
    I: IntoIterator<Item = &'a KindedArgument>,
    I::IntoIter: DoubleEndedIterator,
{
    visit_owner_type_children_with_charge(arguments, budget, |ty, budget| {
        output
            .try_reserve(1)
            .map_err(|_| allocation_error(budget))?;
        output.push(ty);
        Ok(())
    })
}

pub(crate) fn visit_owner_type_children_with_charge<'a, B: TypeWorkMeter, I>(
    arguments: I,
    budget: &mut B,
    mut emit: impl FnMut(&'a Type, &mut B) -> Result<(), B::Error>,
) -> Result<bool, B::Error>
where
    I: IntoIterator<Item = &'a KindedArgument>,
    I::IntoIter: DoubleEndedIterator,
{
    let mut has_row_variable = false;
    visit_owner_components_with_charge(arguments, budget, &mut emit, |_, _| {
        has_row_variable = true;
        Ok(())
    })?;
    Ok(has_row_variable)
}

pub(crate) fn visit_owner_components_with_charge<'a, B: TypeWorkMeter, I>(
    arguments: I,
    budget: &mut B,
    mut emit: impl FnMut(&'a Type, &mut B) -> Result<(), B::Error>,
    mut emit_tail: impl FnMut(&'a EffectRowTail, &mut B) -> Result<(), B::Error>,
) -> Result<(), B::Error>
where
    I: IntoIterator<Item = &'a KindedArgument>,
    I::IntoIter: DoubleEndedIterator,
{
    let mut pending = Vec::new();
    for argument in arguments.into_iter().rev() {
        budget.charge(1)?;
        pending
            .try_reserve(1)
            .map_err(|_| allocation_error(budget))?;
        pending.push(argument);
    }
    while let Some(argument) = pending.pop() {
        match argument {
            KindedArgument::TypeArg(ty) => {
                emit(ty, budget)?;
            }
            KindedArgument::RowArg(row) => {
                budget.charge(1)?;
                let count = row
                    .known
                    .len()
                    .checked_add(row.tail.as_ref().map_or(0, |tail| tail.lacks.len()))
                    .ok_or_else(|| allocation_error(budget))?;
                budget.charge(count)?;
                if let Some(tail) = &row.tail {
                    budget.charge(1)?;
                    emit_tail(tail, budget)?;
                }
                for instance in row
                    .known
                    .iter()
                    .chain(row.tail.iter().flat_map(|tail| tail.lacks.iter()))
                    .rev()
                {
                    budget.charge(instance.arguments.len())?;
                    pending
                        .try_reserve(instance.arguments.len())
                        .map_err(|_| allocation_error(budget))?;
                    pending.extend(instance.arguments.iter().rev());
                }
            }
        }
    }
    Ok(())
}

/// Checks owner slot tags and complete row identity while scheduling ordinary
/// Type pairs for a caller's structural matching relation.
pub(crate) fn extend_owner_type_pairs_with_charge<'a, B: TypeWorkMeter>(
    left: &'a [KindedArgument],
    right: &'a [KindedArgument],
    output: &mut Vec<(&'a Type, &'a Type)>,
    budget: &mut B,
) -> Result<bool, B::Error> {
    visit_owner_type_pairs_with_charge(left, right, budget, |left, right, budget| {
        output
            .try_reserve(1)
            .map_err(|_| allocation_error(budget))?;
        output.push((left, right));
        Ok(())
    })
}

pub(crate) fn visit_owner_type_pairs_with_charge<'a, B: TypeWorkMeter>(
    left: &'a [KindedArgument],
    right: &'a [KindedArgument],
    budget: &mut B,
    mut emit: impl FnMut(&'a Type, &'a Type, &mut B) -> Result<(), B::Error>,
) -> Result<bool, B::Error> {
    if left.len() != right.len() {
        return Ok(false);
    }
    let mut pending = Vec::new();
    budget.charge(left.len())?;
    pending
        .try_reserve(left.len())
        .map_err(|_| allocation_error(budget))?;
    pending.extend(left.iter().zip(right));
    while let Some((left, right)) = pending.pop() {
        match (left, right) {
            (KindedArgument::TypeArg(left), KindedArgument::TypeArg(right)) => {
                emit(left, right, budget)?;
            }
            (KindedArgument::RowArg(left), KindedArgument::RowArg(right)) => {
                budget.charge(1)?;
                if left.known.len() != right.known.len()
                    || match (&left.tail, &right.tail) {
                        (None, None) => false,
                        (Some(left), Some(right)) => {
                            left.variable != right.variable || left.lacks.len() != right.lacks.len()
                        }
                        _ => true,
                    }
                {
                    return Ok(false);
                }
                let members = left
                    .known
                    .iter()
                    .chain(left.tail.iter().flat_map(|tail| tail.lacks.iter()))
                    .zip(
                        right
                            .known
                            .iter()
                            .chain(right.tail.iter().flat_map(|tail| tail.lacks.iter())),
                    );
                for (left, right) in members {
                    budget.charge(1)?;
                    if left.effect != right.effect || left.arguments.len() != right.arguments.len()
                    {
                        return Ok(false);
                    }
                    budget.charge(left.arguments.len())?;
                    pending
                        .try_reserve(left.arguments.len())
                        .map_err(|_| allocation_error(budget))?;
                    pending.extend(left.arguments.iter().zip(right.arguments.iter()));
                }
            }
            _ => return Ok(false),
        }
    }
    Ok(true)
}

/// Tags an already owned Type-only constructor buffer through its existing
/// compiler work meter. The input owner protects a failed admission/allocation.
pub(crate) fn type_arguments_to_kinded_with_budget<B: TypeWorkMeter>(
    arguments: Box<[Type]>,
    budget: &mut B,
) -> Result<Box<[KindedArgument]>, B::Error> {
    let owned = IterativeTypeOwner::new(Type::Tuple(arguments));
    let Type::Tuple(arguments) = &*owned else {
        unreachable!()
    };
    let count = arguments.len();
    budget.charge(count)?;
    let mut tagged = Vec::new();
    tagged
        .try_reserve_exact(count)
        .map_err(|_| allocation_error(budget))?;
    let Type::Tuple(arguments) = owned.into_inner() else {
        unreachable!()
    };
    for argument in arguments.into_vec() {
        tagged.push(KindedArgument::TypeArg(argument));
    }
    Ok(tagged.into_boxed_slice())
}

pub(crate) fn clone_kinded_arguments_with_budget<'a, B: TypeWorkMeter>(
    arguments: impl ExactSizeIterator<Item = &'a KindedArgument>,
    budget: &mut B,
) -> Result<Box<[KindedArgument]>, B::Error> {
    let count = arguments.len();
    let charge = count
        .checked_mul(2)
        .ok_or_else(|| allocation_error(budget))?;
    budget.charge(charge)?;
    let mut staged = Vec::new();
    staged
        .try_reserve_exact(count)
        .map_err(|_| allocation_error(budget))?;
    for argument in arguments {
        staged.push(IterativeArgumentOwner::new(
            clone_kinded_argument_with_budget(argument, budget)?,
        ));
    }
    let mut retained = Vec::new();
    retained
        .try_reserve_exact(count)
        .map_err(|_| allocation_error(budget))?;
    retained.extend(staged.into_iter().map(IterativeArgumentOwner::into_inner));
    Ok(retained.into_boxed_slice())
}
