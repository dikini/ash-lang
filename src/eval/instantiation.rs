//! Immutable, lexical instantiation of validated effect metadata.

use std::{collections::HashMap, sync::Arc};

use super::super::value::ActivationKey;
use super::RuntimeFailure;
use super::{ResourceFailureCause, RuntimePhase, RuntimeResource};
use crate::types::{
    ComputationType, EffectInstance, EffectRow, IterativeTypeOwner, Kind, Type, TypeVariableId,
    TypeWorkBudget, clone_effect_row_with_budget_and_failure, clone_type_with_budget,
    discard_type_iteratively, substitute_type_and_row_variables_with,
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

fn metadata_failure(
    phase: Option<RuntimePhase>,
    cause: ResourceFailureCause,
    requested: Option<usize>,
    available: Option<usize>,
) -> RuntimeFailure {
    RuntimeFailure::EnvironmentCapacity.with_resource_details(super::super::ResourceFailure::new(
        cause,
        phase.unwrap_or(RuntimePhase::Evaluation),
        if cause == ResourceFailureCause::WorkBudgetExhausted {
            RuntimeResource::WorkUnits
        } else {
            RuntimeResource::InstantiationStorage
        },
        requested,
        available,
    ))
}

fn admission_failure(
    phase: Option<RuntimePhase>,
    cause: ResourceFailureCause,
    requested: Option<usize>,
    available: Option<usize>,
) -> RuntimeFailure {
    let resource = if cause == ResourceFailureCause::WorkBudgetExhausted {
        RuntimeResource::WorkUnits
    } else {
        RuntimeResource::InstantiationEntries
    };
    RuntimeFailure::EnvironmentCapacity.with_resource_details(super::super::ResourceFailure::new(
        cause,
        phase.unwrap_or(RuntimePhase::Evaluation),
        resource,
        requested,
        available,
    ))
}

fn clone_row(
    row: &EffectRow,
    work: &mut TypeWorkBudget,
    phase: Option<RuntimePhase>,
) -> Result<EffectRow, RuntimeFailure> {
    let mut charge = |cells| {
        work.charge(cells).map_err(|()| {
            metadata_failure(
                phase,
                ResourceFailureCause::WorkBudgetExhausted,
                Some(cells),
                Some(work.remaining()),
            )
        })
    };
    clone_effect_row_with_budget_and_failure(row, &mut charge, |_| {
        metadata_failure(
            phase,
            ResourceFailureCause::StorageReservationFailed,
            None,
            None,
        )
    })
}

impl Instantiation {
    // Validated Core contains no inference variables. Within this private
    // runtime context only, that disjoint leaf namespace encodes activation
    // atoms. Substitution and exact equality treat them opaquely; runtime
    // metadata never goes through unification or back into checked Core.
    pub(super) fn acquire(
        &self,
        identity: TypeVariableId,
        key: ActivationKey,
        work: &mut TypeWorkBudget,
        phase: Option<RuntimePhase>,
    ) -> Result<Self, RuntimeFailure> {
        self.apply_in_phase(
            &Self::default(),
            &[(identity, Kind::Type)],
            &[Type::Inference(crate::types::InferenceVariableId::new(
                key.0,
            ))],
            &[],
            work,
            Some(phase.unwrap_or(RuntimePhase::Acquisition)),
        )
    }

    pub(super) fn activation(effect: &EffectInstance) -> Option<ActivationKey> {
        match effect.arguments() {
            [crate::types::KindedArgument::TypeArg(Type::Inference(identity))] => {
                Some(ActivationKey(identity.value()))
            }
            _ => None,
        }
    }

    pub(super) fn activation_at(effect: &EffectInstance, position: usize) -> Option<ActivationKey> {
        match effect.arguments().get(position) {
            Some(crate::types::KindedArgument::TypeArg(Type::Inference(identity))) => {
                Some(ActivationKey(identity.value()))
            }
            _ => None,
        }
    }

    pub(super) fn apply(
        &self,
        caller: &Self,
        parameters: &[(TypeVariableId, Kind)],
        arguments: &[Type],
        row_arguments: &[EffectRow],
        work: &mut TypeWorkBudget,
    ) -> Result<Self, RuntimeFailure> {
        self.apply_in_phase(caller, parameters, arguments, row_arguments, work, None)
    }

    #[allow(clippy::too_many_arguments)]
    fn apply_in_phase(
        &self,
        caller: &Self,
        parameters: &[(TypeVariableId, Kind)],
        arguments: &[Type],
        row_arguments: &[EffectRow],
        work: &mut TypeWorkBudget,
        phase: Option<RuntimePhase>,
    ) -> Result<Self, RuntimeFailure> {
        let mut bindings = Bindings::default();
        let previous = self.0.as_deref();
        let type_count = previous
            .map_or(0, |bindings| bindings.types.len())
            .checked_add(arguments.len())
            .ok_or_else(|| {
                admission_failure(phase, ResourceFailureCause::ConfiguredCapacity, None, None)
            })?;
        let row_count = previous
            .map_or(0, |bindings| bindings.rows.len())
            .checked_add(row_arguments.len())
            .ok_or_else(|| {
                admission_failure(phase, ResourceFailureCause::ConfiguredCapacity, None, None)
            })?;
        let requested = type_count.checked_add(row_count).ok_or_else(|| {
            admission_failure(phase, ResourceFailureCause::ConfiguredCapacity, None, None)
        })?;
        work.charge(requested).map_err(|()| {
            admission_failure(
                phase,
                ResourceFailureCause::WorkBudgetExhausted,
                Some(requested),
                Some(work.remaining()),
            )
        })?;
        bindings.types.try_reserve(type_count).map_err(|_| {
            admission_failure(
                phase,
                ResourceFailureCause::StorageReservationFailed,
                Some(type_count),
                None,
            )
        })?;
        bindings.rows.try_reserve(row_count).map_err(|_| {
            admission_failure(
                phase,
                ResourceFailureCause::StorageReservationFailed,
                Some(row_count),
                None,
            )
        })?;
        if let Some(previous) = previous {
            for (parameter, ty) in &previous.types {
                bindings.insert_type(
                    *parameter,
                    clone_type_with_budget(ty, work).map_err(|()| {
                        admission_failure(
                            phase,
                            ResourceFailureCause::WorkBudgetExhausted,
                            None,
                            Some(work.remaining()),
                        )
                    })?,
                );
            }
            for (parameter, row) in &previous.rows {
                bindings.insert_row(*parameter, clone_row(row, work, phase)?);
            }
        }
        let mut arguments = arguments.iter();
        let mut rows = row_arguments.iter();
        for (parameter, kind) in parameters {
            work.charge(1).map_err(|()| {
                admission_failure(
                    phase,
                    ResourceFailureCause::WorkBudgetExhausted,
                    Some(1),
                    Some(work.remaining()),
                )
            })?;
            if matches!(kind, Kind::EffectRow) {
                let row = rows.next().ok_or(RuntimeFailure::InvalidControlState)?;
                bindings.insert_row(*parameter, caller.row(row, work)?);
            } else {
                let argument = arguments
                    .next()
                    .ok_or(RuntimeFailure::InvalidControlState)?;
                let replacement = caller.ty_in_phase(argument, work, phase)?;
                bindings.insert_type(*parameter, replacement);
            }
        }
        if arguments.next().is_some() || rows.next().is_some() {
            return Err(RuntimeFailure::InvalidControlState);
        }
        Ok(Self(Some(Arc::new(bindings))))
    }

    pub(super) fn argument(
        &self,
        argument: &crate::types::KindedArgument,
        work: &mut TypeWorkBudget,
    ) -> Result<crate::types::IterativeArgumentOwner, RuntimeFailure> {
        work.charge(1).map_err(|()| {
            metadata_failure(
                Some(RuntimePhase::Access),
                ResourceFailureCause::WorkBudgetExhausted,
                Some(1),
                Some(work.remaining()),
            )
        })?;
        let argument = match argument {
            crate::types::KindedArgument::TypeArg(ty) => {
                crate::types::KindedArgument::TypeArg(self.ty(ty, work)?)
            }
            crate::types::KindedArgument::RowArg(row) => {
                crate::types::KindedArgument::RowArg(self.row(row, work)?)
            }
        };
        Ok(crate::types::IterativeArgumentOwner::new(argument))
    }

    pub(super) fn ty(&self, ty: &Type, work: &mut TypeWorkBudget) -> Result<Type, RuntimeFailure> {
        self.ty_in_phase(ty, work, None)
    }

    fn ty_in_phase(
        &self,
        ty: &Type,
        work: &mut TypeWorkBudget,
        phase: Option<RuntimePhase>,
    ) -> Result<Type, RuntimeFailure> {
        let Some(bindings) = &self.0 else {
            return clone_type_with_budget(ty, work).map_err(|()| {
                metadata_failure(
                    phase,
                    ResourceFailureCause::WorkBudgetExhausted,
                    None,
                    Some(work.remaining()),
                )
            });
        };
        substitute_type_and_row_variables_with(
            ty,
            &bindings.types,
            &bindings.rows,
            |cells| {
                work.charge(cells).map_err(|()| {
                    metadata_failure(
                        phase,
                        ResourceFailureCause::WorkBudgetExhausted,
                        Some(cells),
                        Some(work.remaining()),
                    )
                })
            },
            || {
                metadata_failure(
                    phase,
                    ResourceFailureCause::StorageReservationFailed,
                    None,
                    None,
                )
            },
        )?
        .map_err(|_| RuntimeFailure::InvalidControlState)
    }

    fn row(&self, row: &EffectRow, work: &mut TypeWorkBudget) -> Result<EffectRow, RuntimeFailure> {
        let row = clone_row(row, work, None)?;
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
        phase: Option<RuntimePhase>,
    ) -> Result<EffectInstance, RuntimeFailure> {
        let requested = effect.arguments().len().checked_mul(2).ok_or_else(|| {
            metadata_failure(phase, ResourceFailureCause::ConfiguredCapacity, None, None)
        })?;
        work.charge(requested).map_err(|()| {
            metadata_failure(
                phase,
                ResourceFailureCause::WorkBudgetExhausted,
                Some(requested),
                Some(work.remaining()),
            )
        })?;
        let mut arguments = Vec::new();
        arguments
            .try_reserve(effect.arguments().len())
            .map_err(|_| {
                metadata_failure(
                    phase,
                    ResourceFailureCause::StorageReservationFailed,
                    Some(effect.arguments().len()),
                    None,
                )
            })?;
        for argument in effect.arguments() {
            let substituted = match argument {
                crate::types::KindedArgument::TypeArg(ty) => {
                    crate::types::KindedArgument::TypeArg(self.ty_in_phase(ty, work, phase)?)
                }
                crate::types::KindedArgument::RowArg(row) => {
                    crate::types::KindedArgument::RowArg(self.row(row, work)?)
                }
            };
            arguments.push(crate::types::IterativeArgumentOwner::new(substituted));
        }
        // Admit the final owner before moving individually guarded types.
        let mut retained = Vec::new();
        retained.try_reserve(arguments.len()).map_err(|_| {
            metadata_failure(
                phase,
                ResourceFailureCause::StorageReservationFailed,
                Some(arguments.len()),
                None,
            )
        })?;
        retained.extend(
            arguments
                .into_iter()
                .map(crate::types::IterativeArgumentOwner::into_inner),
        );
        Ok(EffectInstance::new_kinded(
            effect.effect(),
            retained.into_boxed_slice(),
        ))
    }
}

#[cfg(test)]
mod tests {
    use super::super::tests::is_work_exhaustion;
    use super::*;

    fn fault_row(tail: TypeVariableId, offset: u32) -> EffectRow {
        use crate::types::{EffectId, EffectRowVariable, effect_row_from_owned_parts_with_budget};
        let module = crate::module::ModuleId::new(700);
        effect_row_from_owned_parts_with_budget(
            vec![EffectInstance::new(
                EffectId::new(module, offset),
                Box::new([Type::Int]),
            )],
            Some((
                EffectRowVariable::rigid(tail),
                vec![EffectInstance::new(
                    EffectId::new(module, offset + 1),
                    Box::new([Type::Bool]),
                )],
            )),
            &mut TypeWorkBudget::unbounded(),
        )
        .unwrap()
    }

    fn is_storage_failure(
        result: Result<Result<impl Sized, RuntimeFailure>, Box<dyn std::any::Any + Send>>,
    ) -> bool {
        matches!(result, Ok(Err(RuntimeFailure::Report(report)))
            if report.primary.reason_code() == "runtime.environment-capacity"
            && report.primary.resource().is_some_and(|details|
                details.cause == ResourceFailureCause::StorageReservationFailed
                && details.resource == RuntimeResource::InstantiationStorage
                && details.phase == RuntimePhase::Evaluation
                && details.requested != Some(usize::MAX)))
    }

    #[test]
    fn runtime_row_comparison_reservation_failures_are_not_work_charges() {
        use crate::{
            module::ModuleId,
            types::{EffectId, EffectRowVariable, RowReservationSite, row_reservation_fault},
        };
        let empty = Instantiation::default();
        let parameter = TypeVariableId::generated(700);
        let effect = EffectId::new(ModuleId::new(700), 0);
        let instance = |argument| EffectInstance::new(effect, Box::new([argument]));
        let context = empty
            .apply(
                &empty,
                &[(parameter, Kind::EffectRow)],
                &[],
                &[EffectRow::singleton(instance(Type::Int))],
                &mut TypeWorkBudget::unbounded(),
            )
            .unwrap();
        let canonical = crate::types::effect_row_from_owned_parts_with_budget(
            vec![instance(Type::Int), instance(Type::Bool)],
            None,
            &mut TypeWorkBudget::unbounded(),
        )
        .unwrap();
        let membership = EffectRow::open(
            EffectRowVariable::rigid(parameter),
            Box::new([instance(Type::Bool)]),
        );
        let mut failures = Vec::new();
        for (name, row) in [("canonical", canonical), ("tail membership", membership)] {
            let source = IterativeTypeOwner::new(Type::function_computation(
                Type::Unit,
                ComputationType::new(Type::Int, row),
            ));
            let _fault = row_reservation_fault::fail(RowReservationSite::ComparisonWork, 0);
            let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                context
                    .ty(&source, &mut TypeWorkBudget::unbounded())
                    .map(IterativeTypeOwner::new)
            }));
            if !is_storage_failure(result) {
                failures.push(name);
            }
            assert_eq!(row_reservation_fault::hits(), 1);
        }
        assert!(
            failures.is_empty(),
            "comparison storage refusal misclassified: {failures:?}"
        );
    }

    #[test]
    fn runtime_row_clone_reservation_failures_are_reports_not_panics() {
        use crate::types::{RowReservationSite, row_reservation_fault};
        let empty = Instantiation::default();
        let parameter = TypeVariableId::generated(700);
        let row = fault_row(parameter, 0);
        let previous = empty
            .apply(
                &empty,
                &[(parameter, Kind::EffectRow)],
                &[],
                std::slice::from_ref(&row),
                &mut TypeWorkBudget::unbounded(),
            )
            .unwrap();
        let mut failures = Vec::new();
        for retained in [false, true] {
            for site in [
                RowReservationSite::CloneMembers,
                RowReservationSite::CloneArguments,
                RowReservationSite::CloneLacks,
            ] {
                let _fault = row_reservation_fault::fail(site, 0);
                let mut work = TypeWorkBudget::unbounded();
                let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                    if retained {
                        previous.apply(&empty, &[], &[], &[], &mut work).map(drop)
                    } else {
                        empty.row(&row, &mut work).map(drop)
                    }
                }));
                if !is_storage_failure(result) {
                    failures.push((retained, site));
                }
                assert_eq!(row_reservation_fault::hits(), 1);
            }
        }
        assert!(
            failures.is_empty(),
            "row clone did not report storage refusal: {failures:?}"
        );
    }

    #[test]
    fn runtime_row_canonicalization_and_tail_reservation_failures_are_not_work_charges() {
        use crate::types::{RowReservationSite, row_reservation_fault};
        let empty = Instantiation::default();
        let parameter = TypeVariableId::generated(700);
        let replacement = fault_row(TypeVariableId::generated(701), 2);
        let context = empty
            .apply(
                &empty,
                &[(parameter, Kind::EffectRow)],
                &[],
                &[replacement],
                &mut TypeWorkBudget::unbounded(),
            )
            .unwrap();
        // The replacement sorts before the source member, forcing the real
        // canonicalization allocation rather than the append-only fast path.
        let source = IterativeTypeOwner::new(Type::function_computation(
            Type::Unit,
            ComputationType::new(Type::Int, fault_row(parameter, 4)),
        ));
        let mut failures = Vec::new();
        for (site, skip) in [
            (RowReservationSite::CanonicalMembers, 0),
            (RowReservationSite::CanonicalMembers, 2),
            (RowReservationSite::RebuildArguments, 0),
            (RowReservationSite::RebuildRetained, 0),
            (RowReservationSite::RebuildMembers, 0),
            (RowReservationSite::RebuildLacks, 0),
        ] {
            let _fault = row_reservation_fault::fail(site, skip);
            let mut work = TypeWorkBudget::unbounded();
            let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                context.ty(&source, &mut work).map(IterativeTypeOwner::new)
            }));
            if !is_storage_failure(result) {
                failures.push((site, skip));
            }
            assert_eq!(
                row_reservation_fault::hits(),
                skip + 1,
                "{site:?} skip={skip}"
            );
        }
        assert!(
            failures.is_empty(),
            "row storage refusal was lost or misclassified: {failures:?}"
        );
    }

    #[test]
    fn activation_atoms_survive_generic_and_row_substitution_without_rebinding_outer_context() {
        use crate::{
            module::ModuleId,
            types::{EffectId, EffectRowVariable},
        };
        let empty = Instantiation::default();
        let identity = TypeVariableId::generated(0);
        let parameter = TypeVariableId::generated(1);
        let row_parameter = TypeVariableId::generated(2);
        let effect = EffectId::new(ModuleId::new(0), 0);
        let instance = |id| EffectInstance::new(effect, Box::new([Type::Variable(id)]));
        let mut work = TypeWorkBudget::unbounded();
        let outer = empty
            .acquire(identity, ActivationKey(7), &mut work, None)
            .unwrap();
        let inner = outer
            .acquire(identity, ActivationKey(8), &mut work, None)
            .unwrap();
        for (caller, key) in [(&outer, ActivationKey(7)), (&inner, ActivationKey(8))] {
            let applied = empty
                .apply(
                    caller,
                    &[(parameter, Kind::Type), (row_parameter, Kind::EffectRow)],
                    &[Type::Variable(identity)],
                    &[EffectRow::singleton(instance(identity))],
                    &mut work,
                )
                .unwrap();
            assert_eq!(
                Instantiation::activation(
                    &applied
                        .effect(&instance(parameter), &mut work, None)
                        .unwrap()
                ),
                Some(key)
            );
            let row = EffectRow::open(EffectRowVariable::rigid(row_parameter), Box::new([]));
            let row = applied.row(&row, &mut work).unwrap();
            assert_eq!(row.known().len(), 1);
            assert_eq!(Instantiation::activation(&row.known()[0]), Some(key));
        }
        assert_eq!(
            Instantiation::activation(&outer.effect(&instance(identity), &mut work, None).unwrap()),
            Some(ActivationKey(7))
        );
        assert!(empty.0.is_none());
        assert_eq!(Instantiation::activation(&instance(identity)), None);
    }

    #[test]
    fn instantiation_is_simultaneous_exact_atomic_and_retryable() {
        let empty = Instantiation::default();
        let parameter = TypeVariableId::generated(0);
        let parameters = [(parameter, Kind::Type)];
        let mut short = TypeWorkBudget::with_limit(2);
        assert!(matches!(
            empty.apply(&empty, &parameters, &[Type::Int], &[], &mut short),
            Err(failure) if is_work_exhaustion(failure)
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
                    Err(failure) if is_work_exhaustion(failure)
                ));
                let mut measured = TypeWorkBudget::unbounded();
                discard_type_iteratively(context.ty(&source, &mut measured).unwrap());
                assert!(matches!(
                    context.ty(
                        &source,
                        &mut TypeWorkBudget::with_limit(measured.used() - 1)
                    ),
                    Err(failure) if is_work_exhaustion(failure)
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
                    assert!(
                        instances[0]
                            .arguments()
                            .iter()
                            .all(|ty| *ty == crate::types::KindedArgument::TypeArg(Type::Bool))
                    );
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
                    Err(failure) if is_work_exhaustion(failure)
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
                    Err(failure) if is_work_exhaustion(failure)
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
