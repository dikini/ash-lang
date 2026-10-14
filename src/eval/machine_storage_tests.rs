use super::machine_test_hooks as native;
use super::*;

fn assert_resource_failure(
    failure: RuntimeFailure,
    cause: ResourceFailureCause,
    phase: RuntimePhase,
) {
    let RuntimeFailure::Report(report) = failure else {
        panic!("expected resource report: {failure:?}")
    };
    let resource = report.primary.resource().unwrap();
    assert_eq!(resource.cause, cause);
    assert_eq!(resource.phase, phase);
    assert_eq!(report.cleanup, super::super::CleanupStatus::Unknown);
    assert!(report.teardown.is_none());
}

#[test]
fn type_row_and_kind_error_temporaries_preserve_primary_without_retry() {
    use crate::types::{EffectId, EffectRow, IterativeTypeOwner, Kind, Type};
    enum Temporary {
        Type(IterativeTypeOwner),
        Row(EffectRow),
        Kind(Kind),
    }
    fn fail(value: Temporary) -> Result<(), RuntimeFailure> {
        // Keep the temporary's destruction after the primary error is chosen.
        let result = Err(RuntimeFailure::MissingBinding);
        match value {
            Temporary::Type(value) => drop(value),
            Temporary::Row(value) => drop(value),
            Temporary::Kind(value) => drop(value),
        }
        result
    }
    for case in 0..3 {
        let mut ty = Type::Int;
        for _ in 0..32 {
            ty = Type::function(ty, Type::Int);
        }
        let temporary = match case {
            0 => Temporary::Type(IterativeTypeOwner::new(ty)),
            1 => Temporary::Row(EffectRow::singleton(EffectInstance::new(
                EffectId::new(crate::module::ModuleId::new(700), 0),
                vec![ty].into_boxed_slice(),
            ))),
            _ => {
                crate::types::discard_type_iteratively(ty);
                let mut kind = Kind::Type;
                for _ in 0..32 {
                    kind = Kind::Arrow(Box::new(kind), Box::new(Kind::Type));
                }
                Temporary::Kind(kind)
            }
        };
        native::reset();
        let scope = super::super::disposal::Scope::enter();
        super::super::disposal::reset_growth_attempts();
        native::FAIL_DISPOSAL_GROWTH.set(true);
        let RuntimeFailure::Report(report) = scope.finish(fail(temporary)).unwrap_err() else {
            panic!("secondary disposal failure")
        };
        assert_eq!(report.primary.reason_code(), "runtime.missing-binding");
        assert_eq!(
            report.teardown.unwrap().resource,
            if case == 2 {
                RuntimeResource::KindDisposal
            } else {
                RuntimeResource::TypeDisposal
            }
        );
        assert_eq!(report.cleanup, super::super::CleanupStatus::Incomplete);
        assert_eq!(super::super::disposal::growth_attempts(), 1);
    }
}

#[test]
fn control_storage_representation_bound_precedes_reservation() {
    native::reset();
    native::FAIL_CONTROL_RESERVATION.set(Some(ResourceFailureCause::AllocatorRefused));
    let mut storage = Vec::<usize>::new();
    let failure = reserve_control(
        &mut storage,
        usize::MAX,
        RuntimeResource::CaptureInspection,
        true,
    )
    .unwrap_err();
    assert_resource_failure(
        failure,
        ResourceFailureCause::ConfiguredCapacity,
        RuntimePhase::Capture,
    );
    assert_eq!(
        native::FAIL_CONTROL_RESERVATION.get(),
        Some(ResourceFailureCause::AllocatorRefused)
    );
    assert!(storage.is_empty());
    assert_eq!(storage.capacity(), 0);
    native::reset();
}

#[test]
fn registration_validation_reports_work_before_scanning() {
    native::reset();
    let program = super::tests::effect_program(
        "import @builtin.cell as Cell\nmain : Unit -> Int\nmain () = resource cell<R> c = 4 {\nCell.read c\n}\n",
    );
    let mut machine = Machine::new_effect(&program);
    machine
        .acquire_resource(
            super::tests::resource_node(&program),
            Environment::new(),
            super::tests::integer("4"),
        )
        .unwrap();
    machine.instantiation_work = TypeWorkBudget::with_limit(0);
    let failure = machine
        .registration_owner_index(RegistrationKey(0), 0, false)
        .unwrap_err();
    assert_eq!(failure.reason_code(), "runtime.environment-capacity");
    assert_resource_failure(
        failure,
        ResourceFailureCause::WorkBudgetExhausted,
        RuntimePhase::Capture,
    );
    let RuntimeFailure::Report(report) = failure else {
        unreachable!()
    };
    assert_eq!(report.primary.resource().unwrap().requested, Some(1));
    assert_eq!(report.primary.resource().unwrap().available, Some(0));
    assert_eq!(machine.live_resources, 1);
    drop(machine);
}
