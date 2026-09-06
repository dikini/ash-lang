//! Immutable, lexical instantiation of validated effect metadata.

use std::{collections::HashMap, sync::Arc};

use super::RuntimeFailure;
use crate::types::{
    ComputationType, EffectInstance, EffectRow, IterativeTypeOwner, Kind, Type, TypeVariableId,
    TypeWorkBudget, clone_effect_row_with_budget, clone_type_with_budget, discard_type_iteratively,
    substitute_type_and_row_variables_with,
};

#[derive(Clone, Default)]
pub(super) struct Instantiation(Option<Arc<Bindings>>);

#[derive(Default)]
struct Bindings {
    types: HashMap<TypeVariableId, Type>,
    rows: HashMap<TypeVariableId, EffectRow>,
}

impl Bindings {
    fn insert_type(&mut self, parameter: TypeVariableId, ty: Type) {
        if let Some(previous) = self.types.insert(parameter, ty) {
            discard_type_iteratively(previous);
        }
    }

    fn insert_row(&mut self, parameter: TypeVariableId, row: EffectRow) {
        // EffectRow owns iterative destruction of its retained arguments.
        self.rows.insert(parameter, row);
    }
}

impl Drop for Bindings {
    fn drop(&mut self) {
        for (_, ty) in self.types.drain() {
            discard_type_iteratively(ty);
        }
    }
}

impl std::fmt::Debug for Instantiation {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("Instantiation")
            .field(
                "bindings",
                &self
                    .0
                    .as_ref()
                    .map_or(0, |bindings| bindings.types.len() + bindings.rows.len()),
            )
            .finish()
    }
}

fn capacity(_: ()) -> RuntimeFailure {
    RuntimeFailure::EnvironmentCapacity
}

impl Instantiation {
    pub(super) fn apply(
        &self,
        caller: &Self,
        parameters: &[(TypeVariableId, Kind)],
        arguments: &[Type],
        row_arguments: &[EffectRow],
        work: &mut TypeWorkBudget,
    ) -> Result<Self, RuntimeFailure> {
        let mut bindings = Bindings::default();
        let previous = self.0.as_deref();
        let type_count = previous
            .map_or(0, |bindings| bindings.types.len())
            .checked_add(arguments.len())
            .ok_or(RuntimeFailure::EnvironmentCapacity)?;
        let row_count = previous
            .map_or(0, |bindings| bindings.rows.len())
            .checked_add(row_arguments.len())
            .ok_or(RuntimeFailure::EnvironmentCapacity)?;
        work.charge(
            type_count
                .checked_add(row_count)
                .ok_or(RuntimeFailure::EnvironmentCapacity)?,
        )
        .map_err(capacity)?;
        bindings
            .types
            .try_reserve(type_count)
            .map_err(|_| RuntimeFailure::EnvironmentCapacity)?;
        bindings
            .rows
            .try_reserve(row_count)
            .map_err(|_| RuntimeFailure::EnvironmentCapacity)?;
        if let Some(previous) = previous {
            for (parameter, ty) in &previous.types {
                bindings.insert_type(
                    *parameter,
                    clone_type_with_budget(ty, work).map_err(capacity)?,
                );
            }
            for (parameter, row) in &previous.rows {
                bindings.insert_row(
                    *parameter,
                    clone_effect_row_with_budget(row, work).map_err(capacity)?,
                );
            }
        }
        let mut arguments = arguments.iter();
        let mut rows = row_arguments.iter();
        for (parameter, kind) in parameters {
            work.charge(1).map_err(capacity)?;
            if matches!(kind, Kind::EffectRow) {
                let row = rows.next().ok_or(RuntimeFailure::InvalidControlState)?;
                bindings.insert_row(*parameter, caller.row(row, work)?);
            } else {
                let argument = arguments
                    .next()
                    .ok_or(RuntimeFailure::InvalidControlState)?;
                let replacement = caller.ty(argument, work)?;
                bindings.insert_type(*parameter, replacement);
            }
        }
        if arguments.next().is_some() || rows.next().is_some() {
            return Err(RuntimeFailure::InvalidControlState);
        }
        Ok(Self(Some(Arc::new(bindings))))
    }

    pub(super) fn ty(&self, ty: &Type, work: &mut TypeWorkBudget) -> Result<Type, RuntimeFailure> {
        let Some(bindings) = &self.0 else {
            return clone_type_with_budget(ty, work).map_err(capacity);
        };
        substitute_type_and_row_variables_with(
            ty,
            &bindings.types,
            &bindings.rows,
            |cells| work.charge(cells).map_err(capacity),
            || RuntimeFailure::EnvironmentCapacity,
        )?
        .map_err(|_| RuntimeFailure::InvalidControlState)
    }

    fn row(&self, row: &EffectRow, work: &mut TypeWorkBudget) -> Result<EffectRow, RuntimeFailure> {
        let row = clone_effect_row_with_budget(row, work).map_err(capacity)?;
        let wrapper = IterativeTypeOwner::new(Type::function_computation(
            Type::Unit,
            ComputationType::new(Type::Unit, row),
        ));
        let substituted = self.ty(&wrapper, work)?;
        match substituted {
            Type::Function(_, _) => Ok(EffectRow::empty()),
            Type::EffectfulFunction(_, mut computation) => {
                Ok(std::mem::take(&mut computation.effects))
            }
            other => {
                discard_type_iteratively(other);
                Err(RuntimeFailure::InvalidControlState)
            }
        }
    }

    pub(super) fn effect(
        &self,
        effect: &EffectInstance,
        work: &mut TypeWorkBudget,
    ) -> Result<EffectInstance, RuntimeFailure> {
        work.charge(
            effect
                .arguments()
                .len()
                .checked_mul(2)
                .ok_or(RuntimeFailure::EnvironmentCapacity)?,
        )
        .map_err(capacity)?;
        let mut arguments = Vec::new();
        arguments
            .try_reserve(effect.arguments().len())
            .map_err(|_| RuntimeFailure::EnvironmentCapacity)?;
        for argument in effect.arguments() {
            arguments.push(IterativeTypeOwner::new(self.ty(argument, work)?));
        }
        // Admit the final owner before moving individually guarded types.
        let mut retained = Vec::new();
        retained
            .try_reserve(arguments.len())
            .map_err(|_| RuntimeFailure::EnvironmentCapacity)?;
        retained.extend(arguments.into_iter().map(IterativeTypeOwner::into_inner));
        Ok(EffectInstance::new(
            effect.effect(),
            retained.into_boxed_slice(),
        ))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn instantiation_is_simultaneous_exact_atomic_and_retryable() {
        let empty = Instantiation::default();
        let parameter = TypeVariableId::generated(0);
        let parameters = [(parameter, Kind::Type)];
        let mut short = TypeWorkBudget::with_limit(2);
        assert!(matches!(
            empty.apply(&empty, &parameters, &[Type::Int], &[], &mut short),
            Err(RuntimeFailure::EnvironmentCapacity)
        ));
        assert!(empty.0.is_none());
        for _ in 0..2 {
            let mut exact = TypeWorkBudget::with_limit(3);
            let context = empty
                .apply(&empty, &parameters, &[Type::Int], &[], &mut exact)
                .unwrap();
            assert_eq!(exact.used(), 3); // one retained binding, one parameter, one Type cell
            assert_eq!(
                context
                    .ty(&Type::Variable(parameter), &mut TypeWorkBudget::unbounded())
                    .unwrap(),
                Type::Int
            );
        }

        let second = TypeVariableId::generated(1);
        let parameters = [(parameter, Kind::Type), (second, Kind::Type)];
        let caller = empty
            .apply(
                &empty,
                &parameters,
                &[Type::Int, Type::Bool],
                &[],
                &mut TypeWorkBudget::unbounded(),
            )
            .unwrap();
        let swapped = empty
            .apply(
                &caller,
                &parameters,
                &[Type::Variable(second), Type::Variable(parameter)],
                &[],
                &mut TypeWorkBudget::unbounded(),
            )
            .unwrap();
        assert_eq!(
            swapped
                .ty(&Type::Variable(parameter), &mut TypeWorkBudget::unbounded())
                .unwrap(),
            Type::Bool
        );
        assert_eq!(
            swapped
                .ty(&Type::Variable(second), &mut TypeWorkBudget::unbounded())
                .unwrap(),
            Type::Int
        );
    }

    #[test]
    fn retained_context_bounds_known_and_lacks_argument_queues() {
        use crate::{
            module::ModuleId,
            types::{EffectId, EffectRowVariable},
        };

        let empty = Instantiation::default();
        let parameter = TypeVariableId::generated(0);
        let context = empty
            .apply(
                &empty,
                &[(parameter, Kind::Type)],
                &[Type::Bool],
                &[],
                &mut TypeWorkBudget::unbounded(),
            )
            .unwrap();
        for lacks in [false, true] {
            for width in [16, 4_096] {
                let instance = EffectInstance::new(
                    EffectId::new(ModuleId::new(0), 0),
                    vec![Type::Variable(parameter); width].into_boxed_slice(),
                );
                let row = if lacks {
                    EffectRow::open(
                        EffectRowVariable::rigid(TypeVariableId::generated(1)),
                        Box::new([instance]),
                    )
                } else {
                    EffectRow::singleton(instance)
                };
                let source = IterativeTypeOwner::new(Type::function_computation(
                    Type::Unit,
                    ComputationType::new(Type::Unit, row),
                ));
                let mut preflight = TypeWorkBudget::with_limit(if lacks { 5 } else { 4 });
                assert!(matches!(
                    context.ty(&source, &mut preflight),
                    Err(RuntimeFailure::EnvironmentCapacity),
                ));
                let mut measured = TypeWorkBudget::unbounded();
                discard_type_iteratively(context.ty(&source, &mut measured).unwrap());
                assert!(matches!(
                    context.ty(
                        &source,
                        &mut TypeWorkBudget::with_limit(measured.used() - 1)
                    ),
                    Err(RuntimeFailure::EnvironmentCapacity),
                ));
                for _ in 0..2 {
                    let mut exact = TypeWorkBudget::with_limit(measured.used());
                    let substituted =
                        IterativeTypeOwner::new(context.ty(&source, &mut exact).unwrap());
                    assert_eq!(exact.used(), measured.used());
                    let Type::EffectfulFunction(_, computation) = &*substituted else {
                        panic!("the nonempty row remains effectful");
                    };
                    let instances = if lacks {
                        computation.effects().tail().unwrap().lacks()
                    } else {
                        computation.effects().known()
                    };
                    assert!(instances[0].arguments().iter().all(|ty| *ty == Type::Bool));
                }
            }
        }
    }

    #[test]
    fn deep_instantiation_owns_success_and_partial_failure_iteratively() {
        std::thread::Builder::new()
            .stack_size(256 * 1024)
            .spawn(|| {
                const DEPTH: usize = 32_000;
                let deep = IterativeTypeOwner::new((0..DEPTH).fold(Type::Unit, |ty, _| {
                    Type::Application(Box::new(ty), Box::new(Type::Unit))
                }));
                let empty = Instantiation::default();
                let parameter = TypeVariableId::generated(0);
                let parameters = [(parameter, Kind::Type)];
                let arguments = std::slice::from_ref(&*deep);
                let required = 2 * DEPTH + 3;
                assert!(matches!(
                    empty.apply(
                        &empty,
                        &parameters,
                        arguments,
                        &[],
                        &mut TypeWorkBudget::with_limit(required - 1)
                    ),
                    Err(RuntimeFailure::EnvironmentCapacity)
                ));
                let context = empty
                    .apply(
                        &empty,
                        &parameters,
                        arguments,
                        &[],
                        &mut TypeWorkBudget::with_limit(required),
                    )
                    .unwrap();
                let mut measured = TypeWorkBudget::unbounded();
                let cloned = context
                    .apply(
                        &empty,
                        &[(TypeVariableId::generated(1), Kind::Type)],
                        &[Type::Bool],
                        &[],
                        &mut measured,
                    )
                    .unwrap();
                drop(cloned);
                assert!(matches!(
                    context.apply(
                        &empty,
                        &[(TypeVariableId::generated(1), Kind::Type)],
                        &[Type::Bool],
                        &[],
                        &mut TypeWorkBudget::with_limit(measured.used() - 1)
                    ),
                    Err(RuntimeFailure::EnvironmentCapacity)
                ));
                let retry = context
                    .apply(
                        &empty,
                        &[(TypeVariableId::generated(1), Kind::Type)],
                        &[Type::Bool],
                        &[],
                        &mut TypeWorkBudget::with_limit(measured.used()),
                    )
                    .unwrap();
                drop(retry);
                let replaced = context
                    .apply(
                        &empty,
                        &parameters,
                        &[Type::Bool],
                        &[],
                        &mut TypeWorkBudget::with_limit(measured.used()),
                    )
                    .unwrap();
                assert_eq!(
                    replaced
                        .ty(&Type::Variable(parameter), &mut TypeWorkBudget::unbounded())
                        .unwrap(),
                    Type::Bool,
                );
                assert!(matches!(
                    context.0.as_ref().unwrap().types.get(&parameter),
                    Some(Type::Application(_, _)),
                ));
                drop(replaced);
                drop(context);
            })
            .unwrap()
            .join()
            .unwrap();
    }
}
