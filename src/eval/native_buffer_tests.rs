use super::native_buffer::tests as native;
use super::tests::{effect_program, integer, resource_node};
use super::*;

fn program() -> ValidatedEffectProgram {
    effect_program(
        "import @builtin.native_buffer as Buffer\nmain : Unit -> Buffer.Outcome<Int>\nmain () = resource native_buffer<R> b = 4 {\nBuffer.length b\n}\n",
    )
}

fn assert_no_authority(machine: &Machine) {
    assert_eq!(machine.live_resources, 0);
    assert_eq!(machine.next_activation, 0);
    assert!(machine.frames.is_empty());
    assert!(
        !machine
            .effect_trace
            .as_ref()
            .unwrap()
            .iter()
            .any(|event| matches!(event, EffectTraceEvent::ResourceAcquired(_)))
    );
}

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
fn native_admission_reports_distinct_resource_causes() {
    let program = program();
    let node = resource_node(&program);
    for (limit, work, inject, expected) in [
        (0, 100, false, "runtime.capacity-exhausted"),
        (1, 0, false, "runtime.work-budget-exhausted"),
        (1, 100, true, "runtime.allocator-refused"),
    ] {
        native::reset();
        native::FAIL_PUBLICATION.set(inject);
        let mut machine = Machine::new_effect(&program);
        machine.resource_limit = limit;
        machine.instantiation_work = TypeWorkBudget::with_limit(work);
        let failure = machine
            .acquire_resource(node, Environment::new(), integer("4"))
            .unwrap_err();
        assert_eq!(failure.reason_code(), expected);
        assert!(failure.to_string().contains("acquisition"));
        assert_no_authority(&machine);
    }
}

#[test]
fn native_preflight_work_is_proportional_exact_and_precedes_adapter_calls() {
    let program = program();
    let node = resource_node(&program);
    let mut measured = Machine::new_effect(&program);
    measured
        .acquire_resource(node, Environment::new(), integer("4"))
        .unwrap();
    let work = measured.instantiation_work.used();
    drop(measured);
    for available in [work - 1, work, work] {
        native::reset();
        let mut machine = Machine::new_effect(&program);
        machine.instantiation_work = TypeWorkBudget::with_limit(available);
        let result = machine.acquire_resource(node, Environment::new(), integer("4"));
        if available < work {
            assert_resource_failure(
                result.unwrap_err(),
                ResourceFailureCause::WorkBudgetExhausted,
                RuntimePhase::Acquisition,
            );
            assert_no_authority(&machine);
            assert_eq!(native::ATTEMPTS.get(), 0);
            assert_eq!(native::ADAPTER_CALLS.get(), 0);
        } else {
            result.unwrap();
            assert_eq!(native::ADAPTER_CALLS.get(), 1);
            assert_eq!(machine.instantiation_work.used(), work);
        }
        drop(machine);
        assert_eq!(native::OWNERS.get(), native::RELEASES.get());
    }
    native::reset();
    let mut larger = Machine::new_effect(&program);
    larger
        .acquire_resource(node, Environment::new(), integer("12"))
        .unwrap();
    assert_eq!(larger.instantiation_work.used(), work + 8);
    drop(larger);
    assert_eq!(native::RELEASES.get(), 1);
    for (limit, key, environment, expected) in [
        (0, 0, Environment::new(), RuntimeResource::ResourceOwners),
        (
            1,
            u32::MAX,
            Environment::new(),
            RuntimeResource::ActivationKeys,
        ),
        (
            1,
            0,
            Environment {
                len: usize::MAX,
                ..Environment::new()
            },
            RuntimeResource::EnvironmentBindings,
        ),
    ] {
        native::reset();
        let mut machine = Machine::new_effect(&program);
        machine.resource_limit = limit;
        machine.next_activation = key;
        let failure = machine
            .acquire_resource(node, environment, integer("4"))
            .unwrap_err();
        assert_resource_failure(
            failure,
            ResourceFailureCause::ConfiguredCapacity,
            RuntimePhase::Acquisition,
        );
        let RuntimeFailure::Report(report) = failure else {
            panic!("resource report")
        };
        let details = report.primary.resource().unwrap();
        assert_eq!(details.resource, expected);
        assert_eq!(details.requested, Some(1));
        assert_eq!(details.available, Some(0));
        assert_eq!(machine.live_resources, 0);
        assert_eq!(machine.next_activation, key);
        assert_eq!(native::ADAPTER_CALLS.get(), 0);
    }
}

#[test]
fn native_invalid_length_and_injected_null_publish_only_typed_failure() {
    let program = program();
    let node = resource_node(&program);
    for (length, inject, expected) in [
        ("0", false, "Failure(InvalidLength)"),
        ("184467440737095516160", false, "Failure(InvalidLength)"),
        ("4", true, "Failure(AllocationFailed)"),
    ] {
        native::reset();
        native::FAIL_ALLOCATION.set(inject);
        let mut machine = Machine::new_effect(&program);
        machine
            .acquire_resource(node, Environment::new(), integer(length))
            .unwrap();
        assert_no_authority(&machine);
        assert_eq!(native::ATTEMPTS.get(), usize::from(inject));
        assert_eq!(native::ADAPTER_CALLS.get(), 0);
        assert_eq!(native::OWNERS.get(), 0);
        assert_eq!(machine.run().unwrap().value.to_string(), expected);
        assert_eq!(native::RELEASES.get(), 0);
    }
}

#[test]
fn native_refusal_preserves_initializer_effects_without_entering_body() {
    let program = effect_program(
        "import @builtin.cell as Cell\nimport @builtin.native_buffer as Buffer\nmain : Unit -> (Int, Buffer.Outcome<Int>)\nmain () = resource cell<C> trace = 0 {\nlet initialize : Unit -> Int ! {Cell.Ops<C>} = fn(ignored) {\nlet _ = Cell.write (trace, 7)\n1\n}\nlet result = resource native_buffer<R> b = (initialize ()) {\nlet _ = Cell.write (trace, 9)\nBuffer.length b\n}\n(Cell.read trace, result)\n}\n",
    );
    native::reset();
    native::FAIL_ALLOCATION.set(true);
    let result = Machine::new_effect(&program).run().unwrap();
    assert_eq!(result.value.to_string(), "(7, Failure(AllocationFailed))");
    assert_eq!(native::ATTEMPTS.get(), 1);
    assert_eq!(native::ADAPTER_CALLS.get(), 0);
    assert_eq!(native::OWNERS.get(), 0);
    assert_eq!(
        result
            .effect_trace()
            .iter()
            .filter(|event| matches!(event, EffectTraceEvent::ResourceAcquired(_)))
            .count(),
        1
    );
    assert_eq!(
        result
            .effect_trace()
            .iter()
            .filter(|event| matches!(event, EffectTraceEvent::ResourceWritten(_)))
            .count(),
        1
    );
}

#[test]
fn native_refusal_does_not_allocate_to_discard_prepared_environment() {
    let program = program();
    let node = resource_node(&program);
    let mut machine = Machine::new_effect(&program);
    let binding = machine.resource(node).unwrap().acquisition.handle;
    let environment = Environment::new().extend(binding, Value::Unit).unwrap();
    native::reset();
    native::FAIL_ALLOCATION.set(true);
    native::PROBE_REFUSAL.set(true);
    machine
        .acquire_resource(node, environment, integer("4"))
        .unwrap();
    native::REFUSAL_PROBE_ACTIVE.set(false);
    assert_eq!(
        (
            native::REFUSAL_ENV_GROWTH.get(),
            super::super::disposal::growth_attempts()
        ),
        (0, 0),
        "failure delivery attempted to grow a disposal worklist"
    );
    assert_no_authority(&machine);
}

#[test]
fn native_refusal_discards_generic_type_and_row_bindings_without_growth() {
    use crate::types::{EffectId, EffectRow, Kind, Type, TypeVariableId};
    let program = program();
    let mut machine = Machine::new_effect(&program);
    let mut work = TypeWorkBudget::unbounded();
    let environment = Environment {
        instantiation: Instantiation::default()
            .apply(
                &Instantiation::default(),
                &[
                    (TypeVariableId::generated(700), Kind::Type),
                    (TypeVariableId::generated(701), Kind::EffectRow),
                ],
                &[Type::function(
                    Type::Tuple(vec![Type::Int, Type::Bool].into_boxed_slice()),
                    Type::Int,
                )],
                &[EffectRow::singleton(EffectInstance::new(
                    EffectId::new(crate::module::ModuleId::new(700), 0),
                    vec![Type::function(Type::Int, Type::Unit)].into_boxed_slice(),
                ))],
                &mut work,
            )
            .unwrap(),
        ..Environment::new()
    };
    native::reset();
    native::FAIL_ALLOCATION.set(true);
    native::PROBE_REFUSAL.set(true);
    machine
        .acquire_resource(resource_node(&program), environment, integer("4"))
        .unwrap();
    native::REFUSAL_PROBE_ACTIVE.set(false);
    assert_eq!(super::super::disposal::growth_attempts(), 0);
    assert_eq!(
        machine.run().unwrap().value.to_string(),
        "Failure(AllocationFailed)"
    );
}

#[test]
fn teardown_failure_in_handler_selection_stops_source_clause_suffix_and_cleanup() {
    let mut ty = String::from("Int");
    for _ in 0..32 {
        ty = format!("({ty} -> Int)");
    }
    let source = format!(
        "import @builtin.native_buffer as Buffer\neffect Mark<T> {{\npublish : Int -> Int\n}}\nmain : Unit -> Buffer.Outcome<Int>\nmain () = resource native_buffer<R> b = 1 {{\nlet action : Unit -> Unit ! {{Buffer.Ops<R>}} = fn(ignored) {{\nlet _ = Buffer.write (b, 0, 99)\n()\n}}\ncleanup action {{\nlet value = handle (hook Mark<{ty}> {{\nperform Mark<Unit>.publish 1\n}}) with Mark<Unit> {{\npublish ignored => {{\nlet _ = Buffer.write (b, 0, 7)\nresume 42\n}}\n}}\nlet _ = Buffer.write (b, 0, 11)\nvalue\n}}\n}}\n"
    );
    let program = effect_program(&source);
    native::reset();
    native::FAIL_DISPOSAL_GROWTH.set(true);
    super::super::disposal::reset_growth_attempts();
    let failure = Machine::new_effect(&program).run().unwrap_err();
    let RuntimeFailure::Report(report) = failure else {
        panic!("resource failure: {failure:?}")
    };
    assert_eq!(
        report.primary.resource().unwrap().resource,
        RuntimeResource::TypeDisposal
    );
    assert_eq!(report.cleanup, super::super::CleanupStatus::Incomplete);
    assert_eq!(
        native::WRITES.get(),
        0,
        "clause, suffix and source cleanup must not run"
    );
    assert_eq!(super::super::disposal::growth_attempts(), 1);
}

fn deep_type_environment() -> Environment {
    use crate::types::{Kind, Type, TypeVariableId};
    let mut ty = Type::Int;
    for _ in 0..32 {
        ty = Type::function(ty, Type::Int);
    }
    Environment {
        instantiation: Instantiation::default()
            .apply(
                &Instantiation::default(),
                &[(TypeVariableId::generated(700), Kind::Type)],
                &[ty],
                &[],
                &mut TypeWorkBudget::unbounded(),
            )
            .unwrap(),
        ..Environment::new()
    }
}

#[test]
fn native_preparation_drop_failure_stops_before_the_native_attempt() {
    let program = program();
    let environment = deep_type_environment();
    let mut machine = Machine::new_effect(&program);
    native::reset();
    let scope = super::super::disposal::Scope::enter();
    native::FAIL_DISPOSAL_GROWTH.set(true);
    let result = machine.acquire_resource(resource_node(&program), environment, integer("4"));
    drop(machine);
    assert!(scope.finish(result).is_err());
    assert_eq!(native::ATTEMPTS.get(), 0);
}

#[test]
fn native_refusal_inline_disposal_shortage_is_terminal_without_heap_growth() {
    let program = program();
    let environment = deep_type_environment();
    let mut machine = Machine::new_effect(&program);
    native::reset();
    let scope = super::super::disposal::Scope::enter();
    native::FAIL_ALLOCATION.set(true);
    native::PROBE_REFUSAL.set(true);
    let result = machine.acquire_resource(resource_node(&program), environment, integer("4"));
    native::REFUSAL_PROBE_ACTIVE.set(false);
    drop(machine);
    let RuntimeFailure::Report(report) = scope.finish(result).unwrap_err() else {
        panic!("terminal refusal disposal")
    };
    let resource = report.primary.resource().unwrap();
    assert_eq!(resource.resource, RuntimeResource::TypeDisposal);
    assert_eq!(resource.cause, ResourceFailureCause::ConfiguredCapacity);
    assert_eq!(resource.available, Some(0));
    assert_eq!(report.cleanup, super::super::CleanupStatus::Incomplete);
    assert_eq!(super::super::disposal::growth_attempts(), 0);
    assert_eq!(native::ATTEMPTS.get(), 1);
    assert_eq!(native::ADAPTER_CALLS.get(), 0);
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
fn native_post_success_publication_failure_releases_unpublished_real_owner_once() {
    let program = program();
    native::reset();
    native::FAIL_PUBLICATION.set(true);
    let mut machine = Machine::new_effect(&program);
    assert_resource_failure(
        machine
            .acquire_resource(resource_node(&program), Environment::new(), integer("4"))
            .unwrap_err(),
        ResourceFailureCause::AllocatorRefused,
        RuntimePhase::Acquisition,
    );
    assert_no_authority(&machine);
    assert_eq!(native::ATTEMPTS.get(), 1);
    assert_eq!(native::ADAPTER_CALLS.get(), 1);
    assert_eq!(native::OWNERS.get(), 1);
    assert_eq!(native::RELEASES.get(), 1);
    drop(machine);
    assert_eq!(native::RELEASES.get(), 1);
}

fn operand(machine: &mut Machine, key: u32, index: &str, byte: Option<&str>) -> Value {
    let mut values = vec![Value::ResourceHandle(ActivationKey(key)), integer(index)];
    if let Some(byte) = byte {
        values.push(integer(byte));
    }
    Value::Location(
        allocate_heap(
            &mut machine.heap,
            HeapCell::Tuple(values.into_boxed_slice()),
        )
        .unwrap(),
    )
}

#[test]
fn native_write_validation_and_result_preparation_are_atomic() {
    let program = program();
    native::reset();
    let mut machine = Machine::new_effect(&program);
    let node = resource_node(&program);
    machine
        .acquire_resource(node, Environment::new(), integer("4"))
        .unwrap();
    let api = machine.resource(node).unwrap().acquisition.api().unwrap();
    let write = OperationId::new(api.ops(), 2);
    let value = operand(&mut machine, 0, "0", Some("42"));
    let before = machine.instantiation_work.used();
    machine.interpret_native_buffer(0, write, value).unwrap();
    let work = machine.instantiation_work.used() - before;
    assert_eq!(native::WRITES.get(), 1);
    for (index, byte) in [("4", "256"), ("0", "256"), ("184467440737095516160", "42")] {
        let value = operand(&mut machine, 0, index, Some(byte));
        machine.interpret_native_buffer(0, write, value).unwrap();
    }
    assert_eq!(native::WRITES.get(), 1);
    for inject in [false, true] {
        let value = operand(&mut machine, 0, "0", Some("99"));
        machine.instantiation_work =
            TypeWorkBudget::with_limit(if inject { work } else { work - 1 });
        native::FAIL_WRITE_RESULT.set(inject);
        assert_resource_failure(
            machine
                .interpret_native_buffer(0, write, value)
                .unwrap_err(),
            if inject {
                ResourceFailureCause::AllocatorRefused
            } else {
                ResourceFailureCause::WorkBudgetExhausted
            },
            RuntimePhase::Access,
        );
        assert_eq!(native::WRITES.get(), 1);
        let Frame::ResourceBoundary {
            payload: ResourcePayload::NativeBuffer { owner, .. },
            ..
        } = &machine.frames[0]
        else {
            panic!("native owner")
        };
        assert_eq!(owner.read(0), Some(42));
    }
    for _ in 0..2 {
        machine.instantiation_work = TypeWorkBudget::with_limit(work);
        let value = operand(&mut machine, 0, "0", Some("99"));
        machine.interpret_native_buffer(0, write, value).unwrap();
        assert_eq!(machine.instantiation_work.used(), work);
    }
    assert_eq!(native::WRITES.get(), 3);
}

#[test]
fn native_operand_alias_traversal_charges_before_access() {
    let program = program();
    native::reset();
    let mut machine = Machine::new_effect(&program);
    let node = resource_node(&program);
    machine
        .acquire_resource(node, Environment::new(), integer("4"))
        .unwrap();
    let api = machine.resource(node).unwrap().acquisition.api().unwrap();
    let read = OperationId::new(api.ops(), 1);
    let value = operand(&mut machine, 0, "0", None);
    let before = machine.instantiation_work.used();
    machine
        .interpret_native_buffer(0, read, value.clone())
        .unwrap();
    let work = machine.instantiation_work.used() - before;
    let Value::Location(mut location) = value else {
        panic!("tuple")
    };
    for _ in 0..16 {
        location = allocate_heap(&mut machine.heap, HeapCell::Alias(location)).unwrap();
    }
    machine.instantiation_work = TypeWorkBudget::with_limit(work + 15);
    assert_resource_failure(
        machine
            .interpret_native_buffer(0, read, Value::Location(location))
            .unwrap_err(),
        ResourceFailureCause::WorkBudgetExhausted,
        RuntimePhase::Access,
    );
    assert_eq!(native::READS.get(), 1);
    for _ in 0..2 {
        machine.instantiation_work = TypeWorkBudget::with_limit(work + 16);
        machine
            .interpret_native_buffer(0, read, Value::Location(location))
            .unwrap();
        assert_eq!(machine.instantiation_work.used(), work + 16);
    }
}

#[test]
fn native_wrong_and_retired_activations_fail_before_memory_access() {
    let program = program();
    native::reset();
    let mut machine = Machine::new_effect(&program);
    let node = resource_node(&program);
    machine
        .acquire_resource(node, Environment::new(), integer("4"))
        .unwrap();
    let frame = machine.frames.pop().unwrap();
    machine.return_from(frame, Value::Unit).unwrap();
    machine
        .acquire_resource(node, Environment::new(), integer("4"))
        .unwrap();
    let api = machine.resource(node).unwrap().acquisition.api().unwrap();
    for ordinal in [0, 1, 2, 3] {
        let value = if ordinal == 0 {
            Value::ResourceHandle(ActivationKey(0))
        } else {
            operand(&mut machine, 0, "0", (ordinal == 2).then_some("42"))
        };
        assert_eq!(
            machine.interpret_native_buffer(0, OperationId::new(api.ops(), ordinal), value),
            Err(RuntimeFailure::InvalidControlState)
        );
    }
    let value = operand(&mut machine, 1, "0", None);
    let other = crate::types::EffectId::new(crate::module::ModuleId::new(999), 0);
    assert_eq!(
        machine.interpret_native_buffer(0, OperationId::new(other, 1), value),
        Err(RuntimeFailure::InvalidControlState)
    );
    assert_eq!(native::READS.get(), 0);
    assert_eq!(native::WRITES.get(), 0);
    assert_eq!(machine.next_activation, 2);
    drop(machine);
    assert_eq!(native::OWNERS.get(), 2);
    assert_eq!(native::RELEASES.get(), 2);
}

#[test]
fn native_outer_row_storage_refusal_reports_and_stops_source_effects() {
    use crate::types::{RowReservationSite, row_reservation_fault};
    let program = effect_program(
        "import @builtin.native_buffer as Buffer\nscoped<E : EffectRow> : (Unit -> Unit ! {| E}) -> Int ! {| E}\nscoped action = cleanup action {\n42\n}\nmain : Unit -> Buffer.Outcome<Int>\nmain () = resource native_buffer<R> b = 1 {\nlet action : Unit -> Unit ! {Buffer.Ops<R>} = fn(ignored) {\nlet _ = Buffer.write (b, 0, 99)\n()\n}\nlet value = scoped action\nlet _ = Buffer.write (b, 0, 7)\nvalue\n}\n",
    );
    for site in [
        RowReservationSite::CloneMembers,
        RowReservationSite::CloneArguments,
        RowReservationSite::CanonicalMembers,
    ] {
        native::reset();
        let _fault = row_reservation_fault::fail(site, 0);
        let failure = Machine::new_effect(&program).run().unwrap_err();
        let RuntimeFailure::Report(report) = failure else {
            panic!("row storage report: {failure:?}")
        };
        assert_eq!(report.primary.reason_code(), "runtime.environment-capacity");
        let details = report.primary.resource().unwrap();
        assert_eq!(
            details.cause,
            ResourceFailureCause::StorageReservationFailed
        );
        assert_eq!(details.phase, RuntimePhase::Evaluation);
        assert_eq!(details.resource, RuntimeResource::InstantiationStorage);
        assert_eq!(details.requested, None);
        assert_eq!(report.cleanup, super::super::CleanupStatus::Complete);
        assert!(report.teardown.is_none());
        assert_eq!(native::OWNERS.get(), 1);
        assert_eq!(native::RELEASES.get(), 1);
        assert_eq!(native::WRITES.get(), 0);
        assert_eq!(row_reservation_fault::hits(), 1);
    }
}

#[test]
fn native_outer_cleanup_registration_and_generic_work_failure_stops_source_effects() {
    for (case, definitions, body) in [
        (
            0,
            "",
            "cleanup fn(ignored) {\nlet _ = Buffer.write (b, 0, 99)\n()\n} {\nlet _ = Buffer.write (b, 0, 7)\n42\n}",
        ),
        (
            1,
            "effect Adjust {\npublish : Int -> Int\n}\n",
            "hook Adjust {\nregister Adjust (fn(value) {\nvalue + 1\n}) {\nlet _ = Buffer.write (b, 0, 7)\n42\n}\n}",
        ),
        (
            2,
            "identity<T> : T -> T\nidentity value = value\n",
            "let value = identity 42\nlet _ = Buffer.write (b, 0, 7)\nvalue",
        ),
        (
            3,
            "",
            "let value = cleanup fn(ignored) {\nlet _ = Buffer.write (b, 0, 99)\n()\n} {\n7001\n}\nlet _ = Buffer.write (b, 0, 7)\nvalue",
        ),
    ] {
        let source = format!(
            "import @builtin.native_buffer as Buffer\n{definitions}main : Unit -> Buffer.Outcome<Int>\nmain () = resource native_buffer<R> b = 1 {{\n{body}\n}}\n"
        );
        let program = effect_program(&source);
        let trace = Arc::new(std::sync::Mutex::new(Vec::new()));
        let mut measured = Machine::new_effect(&program);
        measured.work_trace = Some(Arc::clone(&trace));
        measured.run().unwrap();
        let limit = trace
            .lock()
            .unwrap()
            .iter()
            .find_map(|(node, work)| {
                let kind = &program.node(*node).unwrap().kind;
                match (case, kind) {
                    (0, EffectExprKind::Operation(EffectOperation::Cleanup(_)))
                    | (1, EffectExprKind::Operation(EffectOperation::Registration(_)))
                    | (
                        2,
                        EffectExprKind::Pure(PureExprKind::Computation(
                            PureComputation::TypeApplication(_),
                        )),
                    ) => Some(*work),
                    (3, EffectExprKind::Pure(PureExprKind::Value(PureValue::Integer(value))))
                        if value.value().to_string() == "7001" =>
                    {
                        Some(*work)
                    }
                    _ => None,
                }
            })
            .unwrap();
        native::reset();
        let mut machine = Machine::new_effect(&program);
        machine.instantiation_work = TypeWorkBudget::with_limit(limit);
        let failure = machine.run().unwrap_err();
        assert_eq!(failure.reason_code(), "runtime.environment-capacity");
        let RuntimeFailure::Report(report) = failure else {
            panic!("native-outer case {case} lost resource details: {failure:?}")
        };
        let details = report.primary.resource().unwrap();
        assert_eq!(details.cause, ResourceFailureCause::WorkBudgetExhausted);
        assert_eq!(details.resource, RuntimeResource::WorkUnits);
        assert_eq!(
            details.phase,
            match case {
                2 => RuntimePhase::Evaluation,
                3 => RuntimePhase::Cleanup,
                _ => RuntimePhase::Acquisition,
            }
        );
        assert_eq!(report.cleanup, super::super::CleanupStatus::Complete);
        assert_eq!(native::OWNERS.get(), 1);
        assert_eq!(native::RELEASES.get(), 1);
        assert_eq!(
            native::WRITES.get(),
            0,
            "body, suffix and source cleanup must not continue"
        );
    }
}

#[test]
fn native_outer_mixed_owner_capacity_failure_stops_source_effects() {
    for (case, definitions, body, resource) in [
        (
            0,
            "",
            "cleanup fn(ignored) {\nlet _ = Buffer.write (b, 0, 99)\n()\n} {\nlet _ = Buffer.write (b, 0, 7)\n42\n}",
            RuntimeResource::CleanupOwners,
        ),
        (
            1,
            "effect Adjust {\npublish : Int -> Int\n}\n",
            "hook Adjust {\nregister Adjust (fn(value) {\nvalue + 1\n}) {\nlet _ = Buffer.write (b, 0, 7)\n42\n}\n}",
            RuntimeResource::RegistrationOwners,
        ),
        (
            2,
            "",
            "resource cell<C> c = 42 {\nlet _ = Buffer.write (b, 0, 7)\nCell.read c\n}",
            RuntimeResource::ResourceOwners,
        ),
    ] {
        let source = format!(
            "import @builtin.native_buffer as Buffer\nimport @builtin.cell as Cell\n{definitions}main : Unit -> Buffer.Outcome<Int>\nmain () = resource native_buffer<R> b = 1 {{\n{body}\n}}\n"
        );
        let program = effect_program(&source);
        native::reset();
        let mut machine = Machine::new_effect(&program);
        match case {
            0 => machine.cleanup_limit = 0,
            1 => machine.registration_limit = 0,
            _ => machine.resource_limit = 1,
        };
        let failure = machine.run().unwrap_err();
        assert_eq!(failure.reason_code(), "runtime.resource-capacity");
        let RuntimeFailure::Report(report) = failure else {
            panic!("mixed-owner capacity report")
        };
        assert_eq!(
            report.primary.resource(),
            Some(super::super::ResourceFailure::new(
                ResourceFailureCause::ConfiguredCapacity,
                RuntimePhase::Acquisition,
                resource,
                Some(1),
                Some(0)
            ))
        );
        assert_eq!(report.cleanup, super::super::CleanupStatus::Complete);
        assert_eq!(native::RELEASES.get(), 1);
        assert_eq!(native::WRITES.get(), 0);
    }
}

#[test]
fn native_outer_representation_boundaries_report_heap_and_environment_units() {
    for heap in [false, true] {
        let program = program();
        native::reset();
        let mut machine = Machine::new_effect(&program);
        machine
            .acquire_resource(resource_node(&program), Environment::new(), integer("1"))
            .unwrap();
        let scope = super::super::disposal::Scope::enter();
        let result = if heap {
            admit_heap_cell(usize::MAX)
        } else {
            checked_environment_len(usize::MAX, 1, RuntimePhase::Evaluation).map(|_| ())
        };
        drop(machine);
        let failure = scope.finish(result).unwrap_err();
        assert_eq!(
            failure.reason_code(),
            if heap {
                "runtime.heap-capacity"
            } else {
                "runtime.environment-capacity"
            }
        );
        let RuntimeFailure::Report(report) = failure else {
            panic!("representation report")
        };
        assert_eq!(
            report.primary.resource(),
            Some(super::super::ResourceFailure::new(
                ResourceFailureCause::ConfiguredCapacity,
                RuntimePhase::Evaluation,
                if heap {
                    RuntimeResource::HeapCells
                } else {
                    RuntimeResource::EnvironmentBindings
                },
                Some(1),
                Some(0)
            ))
        );
        assert_eq!(report.cleanup, super::super::CleanupStatus::Complete);
        assert_eq!(native::RELEASES.get(), 1);
    }
}

#[test]
fn native_bearing_registration_validation_reports_work_before_scanning() {
    native::reset();
    let program = program();
    let mut machine = Machine::new_effect(&program);
    machine
        .acquire_resource(resource_node(&program), Environment::new(), integer("4"))
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
    assert_eq!(native::RELEASES.get(), 0);
    drop(machine);
    assert_eq!(native::RELEASES.get(), 1);
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
fn native_resume_and_discard_reservation_refusal_preserves_capture() {
    let program = effect_program(
        "import @builtin.native_buffer as Buffer\neffect Pause {\nask : Unit -> Unit\n}\nmain : Unit -> Buffer.Outcome<Int>\nmain () = handle (resource native_buffer<R> b = 1 {\nlet _ = perform Pause.ask ()\nBuffer.length b\n}) with Pause {\nask ignored => resume ()\n}\n",
    );
    let mut pending = vec![program.root()];
    let mut resume = None;
    while let Some(node) = pending.pop() {
        let expression = program.node(node).unwrap();
        if let EffectExprKind::Operation(EffectOperation::Resume(found)) = &expression.kind {
            resume = Some((node, found.handler(), found.owner()));
        }
        pending.extend(
            (0..expression.kind.child_count()).filter_map(|index| expression.kind.child_at(index)),
        );
    }
    let (resume, handler, owner) = resume.unwrap();
    for discard in [false, true] {
        native::reset();
        let mut machine = Machine::new_effect(&program);
        machine
            .acquire_resource(resource_node(&program), Environment::new(), integer("1"))
            .unwrap();
        let capture = machine.capture_from(0).unwrap();
        machine.frames.push(Frame::ClauseBoundary {
            handler,
            owner,
            continuation: Some(capture),
            registration: None,
        });
        native::FAIL_CONTROL_RESERVATION.set(Some(ResourceFailureCause::AllocatorRefused));
        let failure = if discard {
            machine.discard(handler, owner)
        } else {
            machine.return_resume(resume, Value::Unit)
        }
        .unwrap_err();
        assert_eq!(failure.reason_code(), "runtime.captured-control-capacity");
        assert_resource_failure(
            failure,
            ResourceFailureCause::AllocatorRefused,
            RuntimePhase::Capture,
        );
        assert_eq!(machine.captured_cells, 1);
        assert_eq!(native::RELEASES.get(), 0);
        assert!(matches!(
            &machine.frames[0],
            Frame::ClauseBoundary {
                continuation: Some(_),
                ..
            }
        ));
        assert_eq!(native::FAIL_CONTROL_RESERVATION.get(), None);
        drop(machine);
        assert_eq!(native::RELEASES.get(), 1);
    }
}

#[test]
fn native_capture_reservation_reports_known_and_undetermined_refusal() {
    for cause in [
        ResourceFailureCause::AllocatorRefused,
        ResourceFailureCause::StorageReservationFailed,
    ] {
        native::reset();
        let program = program();
        let mut machine = Machine::new_effect(&program);
        machine
            .acquire_resource(resource_node(&program), Environment::new(), integer("4"))
            .unwrap();
        native::FAIL_CONTROL_RESERVATION.set(Some(cause));
        let failure = machine.capture_from(0).unwrap_err();
        assert_eq!(failure.reason_code(), "runtime.captured-control-capacity");
        assert_resource_failure(failure, cause, RuntimePhase::Capture);
        let RuntimeFailure::Report(report) = failure else {
            unreachable!()
        };
        assert_eq!(report.primary.resource().unwrap().requested, Some(1));
        assert_eq!(report.primary.resource().unwrap().available, None);
        assert_eq!(machine.frames.len(), 1);
        assert_eq!(machine.captured_cells, 0);
        assert_eq!(native::FAIL_CONTROL_RESERVATION.get(), None);
        drop(machine);
        assert_eq!(native::RELEASES.get(), 1);
    }
}

#[test]
fn native_capture_reports_exact_capacity_and_preserves_primary_during_teardown() {
    for (limit, fail_teardown) in [(0, false), (1, false), (0, true)] {
        native::reset();
        let program = program();
        let mut machine = Machine::new_effect(&program);
        machine
            .acquire_resource(resource_node(&program), Environment::new(), integer("4"))
            .unwrap();
        machine.capture_limit = limit;
        if fail_teardown {
            machine.control = Some(Control::Evaluate(program.root(), deep_type_environment()));
        }
        let scope = super::super::disposal::Scope::enter();
        native::FAIL_DISPOSAL_GROWTH.set(fail_teardown);
        super::super::disposal::reset_growth_attempts();
        let result = machine.capture_from(0);
        assert_eq!(machine.frames.len(), usize::from(limit == 0));
        assert_eq!(machine.captured_cells, usize::from(limit == 1));
        let result = result.map(drop);
        drop(machine);
        if limit == 1 {
            scope.finish(result).unwrap();
        } else {
            let failure = scope.finish(result).unwrap_err();
            assert_eq!(failure.reason_code(), "runtime.captured-control-capacity");
            let RuntimeFailure::Report(report) = failure else {
                panic!("capture must supply a bounded report: {failure:?}")
            };
            let details = report.primary.resource().unwrap();
            assert_eq!(details.cause, ResourceFailureCause::ConfiguredCapacity);
            assert_eq!(details.phase, RuntimePhase::Capture);
            assert_eq!(details.resource, RuntimeResource::FrameStorage);
            assert_eq!(details.requested, Some(1));
            assert_eq!(details.available, Some(0));
            assert_eq!(report.teardown.is_some(), fail_teardown);
            assert_eq!(
                report.cleanup,
                if fail_teardown {
                    super::super::CleanupStatus::Incomplete
                } else {
                    super::super::CleanupStatus::Complete
                }
            );
        }
        assert_eq!(native::WRITES.get(), 0);
        assert_eq!(native::RELEASES.get(), 1);
        assert_eq!(
            super::super::disposal::growth_attempts(),
            usize::from(fail_teardown)
        );
    }
}

#[test]
fn native_capture_capacity_reuse_and_discard_keep_one_real_owner() {
    let program = program();
    let node = resource_node(&program);
    for discard in [false, true] {
        native::reset();
        let mut machine = Machine::new_effect(&program);
        machine.resource_limit = 1;
        machine
            .acquire_resource(node, Environment::new(), integer("4"))
            .unwrap();
        let captured = machine.capture_from(0).unwrap();
        assert_eq!(machine.live_resources, 1);
        assert_eq!(native::RELEASES.get(), 0);
        assert_resource_failure(
            machine
                .acquire_resource(node, Environment::new(), integer("4"))
                .unwrap_err(),
            ResourceFailureCause::ConfiguredCapacity,
            RuntimePhase::Acquisition,
        );
        assert_eq!(native::ADAPTER_CALLS.get(), 1);
        let handler = HandlerId::new(0);
        let owner = ResumeId::new(0);
        machine.frames.push(Frame::ClauseBoundary {
            handler,
            owner,
            continuation: Some(captured),
            registration: None,
        });
        if discard {
            machine.discard(handler, owner).unwrap();
        } else {
            let Frame::ClauseBoundary {
                continuation: Some(mut capture),
                ..
            } = machine.frames.pop().unwrap()
            else {
                panic!("capture")
            };
            machine.frames.append(&mut capture.frames);
            machine.captured_cells = 0;
        }
        // Exhaustion after acquisition cannot prevent the fixed release or
        // normal wrapper: its heap slot and fixed work were already retained.
        machine.instantiation_work = TypeWorkBudget::with_limit(0);
        let frame = machine.frames.pop().unwrap();
        machine
            .return_from(frame, if discard { Value::Unit } else { integer("42") })
            .unwrap();
        assert_eq!(native::RELEASES.get(), 1);
        assert_eq!(machine.live_resources, 0);
        if discard {
            assert!(matches!(
                machine.control,
                Some(Control::Return(Value::Unit))
            ));
        } else {
            let Some(Control::Return(Value::Location(location))) = &machine.control else {
                panic!("normal wrapper")
            };
            assert!(
                matches!(&machine.heap[*location], HeapCell::Constructor(_, Some(Value::Integer(value))) if value.to_string() == "42")
            );
        }
        machine.instantiation_work = TypeWorkBudget::unbounded();
        machine
            .acquire_resource(node, Environment::new(), integer("4"))
            .unwrap();
        assert_eq!(machine.next_activation, 2);
        drop(machine);
        assert_eq!(native::RELEASES.get(), 2);
    }
}

#[test]
fn native_request_selection_work_exhaustion_precedes_access() {
    use crate::types::Type;
    let program = program();
    let trace = Arc::new(std::sync::Mutex::new(Vec::new()));
    let mut measured = Machine::new_effect(&program);
    measured.work_trace = Some(Arc::clone(&trace));
    measured.run().unwrap();
    let request_node = trace
        .lock()
        .unwrap()
        .iter()
        .find_map(|(node, _)| {
            matches!(
                program.node(*node).unwrap().kind,
                EffectExprKind::Operation(EffectOperation::Request(_))
            )
            .then_some(*node)
        })
        .unwrap();
    let EffectExprKind::Operation(EffectOperation::Request(request)) =
        &program.node(request_node).unwrap().kind
    else {
        unreachable!()
    };
    let [crate::types::KindedArgument::TypeArg(Type::Variable(identity))] =
        request.effect().arguments()
    else {
        panic!("native request identity")
    };
    let instantiation = Instantiation::default()
        .acquire(
            *identity,
            ActivationKey(0),
            &mut TypeWorkBudget::unbounded(),
            None,
        )
        .unwrap();
    let mut metadata_work = TypeWorkBudget::unbounded();
    instantiation
        .effect(
            request.effect(),
            &mut metadata_work,
            Some(RuntimePhase::Access),
        )
        .unwrap();
    native::reset();
    let mut machine = Machine::new_effect(&program);
    machine
        .acquire_resource(resource_node(&program), Environment::new(), integer("4"))
        .unwrap();
    machine.instantiation_work = TypeWorkBudget::with_limit(metadata_work.used());
    let failure = machine
        .return_request(
            request_node,
            &instantiation,
            Value::ResourceHandle(ActivationKey(0)),
        )
        .unwrap_err();
    assert_eq!(failure.reason_code(), "runtime.environment-capacity");
    assert_resource_failure(
        failure,
        ResourceFailureCause::WorkBudgetExhausted,
        RuntimePhase::Access,
    );
    let RuntimeFailure::Report(report) = failure else {
        unreachable!()
    };
    assert_eq!(report.primary.resource().unwrap().requested, Some(1));
    assert_eq!(report.primary.resource().unwrap().available, Some(0));
    assert!(
        !machine
            .effect_trace
            .as_ref()
            .unwrap()
            .iter()
            .any(|event| matches!(event, EffectTraceEvent::Request(_)))
    );
    assert_eq!(native::READS.get(), 0);
    assert_eq!(native::WRITES.get(), 0);
    drop(machine);
    assert_eq!(native::RELEASES.get(), 1);
}

#[test]
fn native_typed_body_failure_and_internal_teardown_release_without_source_cleanup() {
    for fail in [false, true] {
        let program = effect_program(
            "import @builtin.native_buffer as Buffer\nmain : Unit -> Buffer.Outcome<Buffer.Outcome<Int>>\nmain () = resource native_buffer<R> b = 4 {\nlet action : Unit -> Unit ! {Buffer.Ops<R>} = fn(ignored) {\nlet _ = Buffer.write (b, 0, 99)\n()\n}\ncleanup action {\nBuffer.read (b, 4)\n}\n}\n",
        );
        native::reset();
        let mut machine = Machine::new_effect(&program);
        if fail {
            machine.work_trace = Some(Arc::new(std::sync::Mutex::new(Vec::new())));
            let measured = machine.run().unwrap();
            let body_work = measured.work_trace.as_ref().unwrap().iter().find_map(|(node, work)| {
                matches!(&program.node(*node).unwrap().kind, EffectExprKind::Operation(EffectOperation::Request(request)) if request.operation().operation() == 1).then_some(*work)
            }).unwrap();
            native::reset();
            let mut machine = Machine::new_effect(&program);
            machine.instantiation_work = TypeWorkBudget::with_limit(body_work);
            let failure = machine.run().unwrap_err();
            assert_eq!(failure.reason_code(), "runtime.environment-capacity");
            let RuntimeFailure::Report(report) = failure else {
                panic!("request selection must supply a bounded report: {failure:?}")
            };
            let details = report.primary.resource().unwrap();
            assert_eq!(details.cause, ResourceFailureCause::WorkBudgetExhausted);
            assert_eq!(details.phase, RuntimePhase::Access);
            assert_eq!(details.resource, RuntimeResource::WorkUnits);
            assert_eq!(details.available, Some(0));
            assert_eq!(report.cleanup, super::super::CleanupStatus::Complete);
            assert_eq!(native::WRITES.get(), 0);
        } else {
            let result = machine.run().unwrap();
            assert_eq!(result.value.to_string(), "Success(Failure(InvalidIndex))");
            assert_eq!(native::WRITES.get(), 1);
        }
        assert_eq!(native::ADAPTER_CALLS.get(), 1);
        assert_eq!(native::OWNERS.get(), 1);
        assert_eq!(native::RELEASES.get(), 1);
    }
}

#[test]
fn native_deep_normal_completion_and_nested_capture_teardown_use_a_small_stack() {
    let program = program();
    std::thread::Builder::new()
        .stack_size(256 * 1024)
        .spawn(move || {
            const DEPTH: usize = 8_192;
            let node = resource_node(&program);
            native::reset();
            let mut normal = Machine::new_effect(&program);
            for _ in 0..DEPTH {
                normal
                    .acquire_resource(node, Environment::new(), integer("1"))
                    .unwrap();
            }
            normal.instantiation_work = TypeWorkBudget::with_limit(0);
            normal.control = Some(Control::Return(Value::Unit));
            let result = normal.run().unwrap();
            assert_eq!(native::OWNERS.get(), DEPTH);
            assert_eq!(native::RELEASES.get(), DEPTH);
            assert_eq!(
                result
                    .effect_trace()
                    .iter()
                    .filter(|event| matches!(event, EffectTraceEvent::ResourceReleased(_)))
                    .count(),
                DEPTH
            );
            drop(result);
            native::reset();
            for discard in [false, true] {
                let mut failure = Machine::new_effect(&program);
                let mut nested = CapturedContinuation { frames: Vec::new() };
                for _ in 0..DEPTH {
                    failure
                        .acquire_resource(node, Environment::new(), integer("1"))
                        .unwrap();
                    let frame = failure.frames.pop().unwrap();
                    nested = CapturedContinuation {
                        frames: vec![
                            frame,
                            Frame::ClauseBoundary {
                                handler: HandlerId::new(0),
                                owner: ResumeId::new(0),
                                continuation: Some(nested),
                                registration: None,
                            },
                        ],
                    };
                }
                failure.frames.push(Frame::ClauseBoundary {
                    handler: HandlerId::new(0),
                    owner: ResumeId::new(0),
                    continuation: Some(nested),
                    registration: None,
                });
                failure.captured_cells = DEPTH * 2;
                if discard {
                    failure
                        .discard(HandlerId::new(0), ResumeId::new(0))
                        .unwrap();
                }
                failure.instantiation_work = TypeWorkBudget::with_limit(0);
                failure.control = Some(Control::Return(Value::Unit));
                if discard {
                    assert!(matches!(failure.run().unwrap().value, Value::Unit));
                } else {
                    assert!(matches!(
                        failure.run(),
                        Err(RuntimeFailure::InvalidControlState)
                    ));
                }
                assert_eq!(
                    native::OWNERS.get(),
                    if discard { 2 * DEPTH } else { DEPTH }
                );
                assert_eq!(native::RELEASES.get(), native::OWNERS.get());
                assert_eq!(native::WRITES.get(), 0);
            }
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn captured_native_teardown_exhaustion_preserves_primary_and_marks_incomplete() {
    let program = program();
    let node = resource_node(&program);
    native::reset();
    let mut machine = Machine::new_effect(&program);
    let mut children = Vec::new();
    for _ in 0..32 {
        machine
            .acquire_resource(node, Environment::new(), integer("1"))
            .unwrap();
        children.push(machine.frames.pop().unwrap());
    }
    let captured = CapturedContinuation {
        frames: vec![Frame::ClauseBoundary {
            handler: HandlerId::new(0),
            owner: ResumeId::new(0),
            registration: None,
            continuation: Some(CapturedContinuation { frames: children }),
        }],
    };
    machine.frames.push(Frame::ClauseBoundary {
        handler: HandlerId::new(0),
        owner: ResumeId::new(0),
        registration: None,
        continuation: Some(captured),
    });
    machine.control = None;
    native::FAIL_DISPOSAL_GROWTH.set(true);
    super::super::disposal::reset_growth_attempts();
    let failure = machine.run().unwrap_err();
    let RuntimeFailure::Report(report) = failure else {
        panic!("missing teardown report: {failure:?}")
    };
    assert_eq!(
        report.primary.reason_code(),
        "runtime.invalid-control-state"
    );
    assert_eq!(report.cleanup, super::super::CleanupStatus::Incomplete);
    assert!(report.teardown.is_some());
    assert_eq!(native::OWNERS.get(), 32);
    assert!(native::RELEASES.get() < 32);
    assert_eq!(native::WRITES.get(), 0);
    assert_eq!(super::super::disposal::growth_attempts(), 1);
}
