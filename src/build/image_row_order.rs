//! Portable order keys for unordered row partitions, before structural interning.
use super::*;
use crate::types::{EffectInstance, EffectRow, EffectRowVariable, Kind, KindedArgument};
use std::cmp::Ordering;

#[derive(Clone, Copy)]
enum Input<'a> {
    Structural(StructuralInput<'a>),
    Kind(&'a Kind),
    Variable(crate::types::TypeVariableId),
    EmptyRow,
}

// Every node is framed by its tag, scalar-prefix length and ordered child count;
// each child is length-prefixed. Tokens never contain process-local coordinates.
type Key = Vec<u64>;

fn compare(
    left: &[u64],
    right: &[u64],
    work: &mut TypeWorkBudget,
) -> Result<Ordering, ImageFailure> {
    charge(work, 1)?;
    for (left, right) in left.iter().zip(right) {
        charge(work, 2)?;
        let order = left.cmp(right);
        if order != Ordering::Equal {
            return Ok(order);
        }
    }
    Ok(left.len().cmp(&right.len()))
}

fn order(keys: &[Key], work: &mut TypeWorkBudget) -> Result<Vec<usize>, ImageFailure> {
    let count = keys.len();
    charge(work, count.checked_mul(2).ok_or(ImageFailure::Resource)?)?;
    let mut indices = Vec::new();
    let mut scratch = Vec::new();
    indices
        .try_reserve_exact(count)
        .map_err(|_| ImageFailure::Resource)?;
    scratch
        .try_reserve_exact(count)
        .map_err(|_| ImageFailure::Resource)?;
    indices.extend(0..count);
    scratch.resize(count, 0);
    let mut width = 1usize;
    while width < count {
        let mut start = 0;
        while start < count {
            let middle = start.saturating_add(width).min(count);
            let end = middle.saturating_add(width).min(count);
            let (mut left, mut right) = (start, middle);
            for output in &mut scratch[start..end] {
                charge(work, 1)?;
                if left < middle
                    && (right == end
                        || compare(&keys[indices[left]], &keys[indices[right]], work)?
                            != Ordering::Greater)
                {
                    *output = indices[left];
                    left += 1;
                } else {
                    *output = indices[right];
                    right += 1;
                }
            }
            start = end;
        }
        charge(work, count)?;
        indices.copy_from_slice(&scratch);
        width = width.checked_mul(2).unwrap_or(count);
    }
    for pair in indices.windows(2) {
        if compare(&keys[pair[0]], &keys[pair[1]], work)? == Ordering::Equal {
            return Err(ImageFailure::InvalidRecord);
        }
    }
    Ok(indices)
}

impl Encoder<'_> {
    pub(super) fn row_order_key(
        &mut self,
        root: StructuralInput<'_>,
        depth: usize,
    ) -> Result<Key, ImageFailure> {
        enum Task<'a> {
            Visit(Input<'a>, usize),
            Finish {
                prefix: Key,
                count: usize,
                row: Option<(usize, usize)>,
            },
        }
        let mut tasks = Vec::new();
        let mut results: Vec<Key> = Vec::new();
        push(
            &mut tasks,
            Task::Visit(Input::Structural(root), depth),
            self.work,
        )?;
        while let Some(task) = tasks.pop() {
            charge(self.work, 1)?;
            match task {
                Task::Visit(input, depth) => {
                    if depth > crate::core::CORE_PAYLOAD_DEPTH_LIMIT {
                        return Err(ImageFailure::Resource);
                    }
                    let mut prefix = Vec::new();
                    let mut children = Vec::new();
                    let mut row_partition = None;
                    macro_rules! scalar {
                        ($value:expr) => {{
                            push(&mut prefix, u64::from($value), self.work)?;
                        }};
                    }
                    macro_rules! child {
                        ($value:expr, $depth:expr) => {{
                            push(&mut children, ($value, $depth), self.work)?;
                        }};
                    }
                    match input {
                        Input::Variable(id) => {
                            scalar!(40u32);
                            match self.type_variable(id)? {
                                TypeVariableIdentity::Resolved { module, local } => {
                                    scalar!(0u32);
                                    scalar!(module);
                                    scalar!(local);
                                }
                                TypeVariableIdentity::Generated(local) => {
                                    scalar!(1u32);
                                    scalar!(local);
                                }
                            }
                        }
                        Input::Kind(kind) => match kind {
                            Kind::Type => scalar!(41u32),
                            Kind::EffectRow => scalar!(42u32),
                            Kind::Arrow(domain, codomain) => {
                                scalar!(43u32);
                                child!(Input::Kind(domain), depth + 1);
                                child!(Input::Kind(codomain), depth + 1);
                            }
                        },
                        Input::EmptyRow => {
                            scalar!(30u32);
                            scalar!(0u32);
                            scalar!(0u32);
                            scalar!(0u32);
                        }
                        Input::Structural(StructuralInput::Type(ty)) => {
                            if let Some(function) = ty.function_view() {
                                scalar!(10u32);
                                child!(
                                    Input::Structural(StructuralInput::Type(function.domain())),
                                    depth + 1
                                );
                                child!(
                                    Input::Structural(StructuralInput::Type(function.value())),
                                    depth + 1
                                );
                                child!(
                                    function.effects().map_or(Input::EmptyRow, |row| {
                                        Input::Structural(StructuralInput::Row(row))
                                    }),
                                    depth + 1
                                );
                            } else {
                                match ty {
                                    Type::Int => scalar!(0u32),
                                    Type::Bool => scalar!(1u32),
                                    Type::Unit => scalar!(2u32),
                                    Type::Bytes => scalar!(3u32),
                                    Type::String => scalar!(4u32),
                                    Type::Nominal(id) => {
                                        scalar!(5u32);
                                        let id = self.nominal(*id)?;
                                        scalar!(id.module);
                                        scalar!(id.local);
                                    }
                                    Type::Variable(id) => {
                                        scalar!(6u32);
                                        child!(Input::Variable(*id), depth);
                                    }
                                    Type::Application(function, argument) => {
                                        scalar!(7u32);
                                        child!(
                                            Input::Structural(StructuralInput::Type(function)),
                                            depth
                                        );
                                        child!(
                                            Input::Structural(StructuralInput::Type(argument)),
                                            depth + 1
                                        );
                                    }
                                    Type::Tuple(elements) => {
                                        scalar!(8u32);
                                        for element in elements {
                                            child!(
                                                Input::Structural(StructuralInput::Type(element)),
                                                depth + 1
                                            );
                                        }
                                    }
                                    Type::Forall(parameters, body) => {
                                        scalar!(9u32);
                                        scalar!(index(parameters.len())?);
                                        for (id, kind) in parameters {
                                            child!(Input::Variable(*id), depth);
                                            child!(Input::Kind(kind), 0);
                                        }
                                        child!(
                                            Input::Structural(StructuralInput::Type(body)),
                                            depth + 1
                                        );
                                    }
                                    Type::ResourceApply(id, arguments) => {
                                        scalar!(11u32);
                                        let id = self.resource_identity(*id)?;
                                        scalar!(id.module);
                                        scalar!(id.local);
                                        for argument in arguments {
                                            child!(
                                                Input::Structural(StructuralInput::Argument(
                                                    argument
                                                )),
                                                depth + 1
                                            );
                                        }
                                    }
                                    Type::ForeignOwnerApply(id, arguments) => {
                                        scalar!(12u32);
                                        let id = self.nominal(*id)?;
                                        scalar!(id.module);
                                        scalar!(id.local);
                                        for argument in arguments {
                                            child!(
                                                Input::Structural(StructuralInput::Argument(
                                                    argument
                                                )),
                                                depth + 1
                                            );
                                        }
                                    }
                                    Type::Inference(_)
                                    | Type::Function(_, _)
                                    | Type::EffectfulFunction(_, _) => {
                                        return Err(ImageFailure::Unsupported(Unsupported::Type));
                                    }
                                }
                            }
                        }
                        Input::Structural(StructuralInput::Argument(argument)) => match argument {
                            KindedArgument::TypeArg(ty) => {
                                scalar!(20u32);
                                child!(Input::Structural(StructuralInput::Type(ty)), depth);
                            }
                            KindedArgument::RowArg(row) => {
                                scalar!(21u32);
                                child!(Input::Structural(StructuralInput::Row(row)), depth);
                            }
                        },
                        Input::Structural(StructuralInput::Instance(instance)) => {
                            scalar!(22u32);
                            let id = self.effect_identity(instance.effect())?;
                            scalar!(id.module);
                            scalar!(id.local);
                            for argument in instance.arguments() {
                                child!(
                                    Input::Structural(StructuralInput::Argument(argument)),
                                    depth
                                );
                            }
                        }
                        Input::Structural(StructuralInput::Row(row)) => {
                            scalar!(30u32);
                            scalar!(index(row.known().len())?);
                            let lacks = row.tail().map_or(0, |tail| tail.lacks().len());
                            scalar!(index(lacks)?);
                            match row.tail() {
                                None => scalar!(0u32),
                                Some(tail) => match tail.variable() {
                                    EffectRowVariable::Rigid(id) => {
                                        scalar!(1u32);
                                        child!(Input::Variable(id), depth);
                                    }
                                    EffectRowVariable::Inference(id)
                                        if self.source_pending_rows.contains(&id) =>
                                    {
                                        scalar!(2u32);
                                        scalar!(id.value());
                                    }
                                    _ => return Err(ImageFailure::Unsupported(Unsupported::Type)),
                                },
                            }
                            // Keep a rigid tail child before the two unordered partitions.
                            row_partition = Some((children.len(), row.known().len()));
                            for instance in row.known() {
                                child!(
                                    Input::Structural(StructuralInput::Instance(instance)),
                                    depth
                                );
                            }
                            if let Some(tail) = row.tail() {
                                for instance in tail.lacks() {
                                    child!(
                                        Input::Structural(StructuralInput::Instance(instance)),
                                        depth
                                    );
                                }
                            }
                        }
                    }
                    let count = children.len();
                    push(
                        &mut tasks,
                        Task::Finish {
                            prefix,
                            count,
                            row: row_partition,
                        },
                        self.work,
                    )?;
                    for (input, depth) in children.into_iter().rev() {
                        push(&mut tasks, Task::Visit(input, depth), self.work)?;
                    }
                }
                Task::Finish { prefix, count, row } => {
                    let start = results
                        .len()
                        .checked_sub(count)
                        .ok_or(ImageFailure::InvalidRecord)?;
                    let children = &results[start..];
                    let mut indices = Vec::new();
                    charge(self.work, count)?;
                    indices
                        .try_reserve_exact(count)
                        .map_err(|_| ImageFailure::Resource)?;
                    if let Some((offset, known)) = row {
                        indices.extend(0..offset);
                        for i in order(&children[offset..offset + known], self.work)? {
                            indices.push(offset + i);
                        }
                        for i in order(&children[offset + known..], self.work)? {
                            indices.push(offset + known + i);
                        }
                    } else {
                        indices.extend(0..count);
                    }
                    charge(self.work, count)?;
                    let size = children.iter().try_fold(
                        prefix.len().checked_add(2).ok_or(ImageFailure::Resource)?,
                        |size, child| {
                            size.checked_add(child.len())
                                .and_then(|n| n.checked_add(1))
                                .ok_or(ImageFailure::Resource)
                        },
                    )?;
                    charge(self.work, size)?;
                    let mut key = Vec::new();
                    key.try_reserve_exact(size)
                        .map_err(|_| ImageFailure::Resource)?;
                    key.push(u64::from(index(prefix.len())?));
                    key.extend_from_slice(&prefix);
                    key.push(u64::from(index(count)?));
                    for i in indices {
                        key.push(u64::from(index(children[i].len())?));
                        key.extend_from_slice(&children[i]);
                    }
                    results.truncate(start);
                    push(&mut results, key, self.work)?;
                }
            }
        }
        results
            .pop()
            .filter(|_| results.is_empty())
            .ok_or(ImageFailure::InvalidRecord)
    }

    pub(super) fn portable_row_members<'a>(
        &mut self,
        row: &'a EffectRow,
        depth: usize,
    ) -> Result<Vec<&'a EffectInstance>, ImageFailure> {
        let mut result = Vec::new();
        let count = row
            .known()
            .len()
            .checked_add(row.tail().map_or(0, |tail| tail.lacks().len()))
            .ok_or(ImageFailure::Resource)?;
        charge(self.work, count)?;
        result
            .try_reserve_exact(count)
            .map_err(|_| ImageFailure::Resource)?;
        for partition in [row.known(), row.tail().map_or(&[][..], |tail| tail.lacks())] {
            let mut keys = Vec::new();
            for instance in partition {
                let key = self.row_order_key(StructuralInput::Instance(instance), depth)?;
                push(&mut keys, key, self.work)?;
            }
            for i in order(&keys, self.work)? {
                charge(self.work, 1)?;
                result.push(&partition[i]);
            }
        }
        Ok(result)
    }
}
