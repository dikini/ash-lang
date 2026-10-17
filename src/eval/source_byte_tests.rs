//! Injected entry/authentication witnesses; these callbacks never dereference C memory.

use super::*;
use crate::{
    driver::{CompiledProgram, RunConfiguration, compile_path},
    foreign::source_runtime::{NativeByteCallbacks, NativeOwnerGuardReady},
    module::ModuleRoots,
    types::{Kind, Type},
};
use std::{
    cell::Cell,
    fs,
    path::PathBuf,
    sync::atomic::{AtomicU64, Ordering},
};

thread_local! {
    static READS: Cell<usize> = const { Cell::new(0) };
    static WRITES: Cell<usize> = const { Cell::new(0) };
    static RELEASES: Cell<usize> = const { Cell::new(0) };
    static BYTE: Cell<u8> = const { Cell::new(5) };
}

fn read(address: *mut core::ffi::c_void, index: usize) -> u8 {
    assert_eq!(address, std::ptr::NonNull::<u8>::dangling().as_ptr().cast());
    assert_eq!(index, 0);
    READS.set(READS.get() + 1);
    BYTE.get()
}
fn write(address: *mut core::ffi::c_void, index: usize, byte: u8) {
    assert_eq!(address, std::ptr::NonNull::<u8>::dangling().as_ptr().cast());
    assert_eq!(index, 0);
    WRITES.set(WRITES.get() + 1);
    BYTE.set(byte);
}
fn release(arguments: &[crate::foreign::source_runtime::NativeOwnerOperand]) {
    assert!(matches!(
        arguments,
        [crate::foreign::source_runtime::NativeOwnerOperand::Address(
            _
        )]
    ));
    RELEASES.set(RELEASES.get() + 1);
}

struct Fixture {
    directory: PathBuf,
    compiled: CompiledProgram,
    scope: NodeId,
}
impl Fixture {
    fn new() -> Self {
        Self::compile(
            include_str!("../../tests/fixtures/source-owner/byte_owner.ash"),
            include_str!("../../tests/fixtures/source-owner/byte_entry.ash"),
        )
    }
    fn data() -> Self {
        let owner = include_str!("../../tests/fixtures/source-owner/byte_owner.ash")
            .replace(
                "read : (Access, Int) -> Foreign.Call<Int>",
                "read : Access -> Int",
            )
            .replace(
                "write : (Access, Int, Int) -> Foreign.Call<Unit>",
                "write : (Access, Int) -> Unit",
            );
        let start = owner.find("    handlers (state, data) {").unwrap();
        let owner = format!(
            "{}    handlers (state, data) {{\n        read access => resume Foreign.data_of state\n        write (access, replacement) => resume Foreign.replace_data (state, replacement)\n    }}\n}}\n",
            &owner[..start]
        );
        Self::compile(
            &owner,
            "import owner as Owner\nmain : Unit -> Owner.Scope<Unit, Unit, Int>\nmain () = resource Owner.Probe<{}, Fresh, {}> owner = (42, 7) {\n    let _ = Owner.write (owner, 7)\n    Owner.read owner\n}\n",
        )
    }
    fn compile(owner: &str, entry: &str) -> Self {
        static IDS: AtomicU64 = AtomicU64::new(0);
        let directory = std::env::temp_dir().join(format!(
            "ash-byte-entry-{}-{}",
            std::process::id(),
            IDS.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&directory).unwrap();
        fs::write(directory.join("owner.ash"), owner).unwrap();
        fs::write(directory.join("entry.ash"), entry).unwrap();
        let compiled = compile_path(RunConfiguration {
            entry: directory.join("entry.ash"),
            roots: ModuleRoots::empty(),
        })
        .unwrap();
        let (program, _) = compiled.effect_build_input().unwrap();
        let mut pending = vec![program.root()];
        let scope = loop {
            let id = pending
                .pop()
                .expect("an admitted source scope is reachable");
            let node = program.node(id).unwrap();
            if matches!(
                node.kind,
                EffectExprKind::Operation(EffectOperation::SourceResourceScope(_))
            ) {
                break id;
            }
            pending
                .extend((0..node.kind.child_count()).filter_map(|index| node.kind.child_at(index)));
        };
        Self {
            directory,
            compiled,
            scope,
        }
    }
    fn program(&self) -> &ValidatedEffectProgram {
        self.compiled.effect_build_input().unwrap().0
    }
    fn machine(&self, initialized: bool) -> (Machine<'_>, ActivationKey) {
        let mut machine = Machine::new_effect(self.program());
        let input = machine
            .foreign_tuple(&[integer(42), integer(7)], RuntimePhase::Acquisition)
            .unwrap();
        machine
            .enter_source_resource(self.scope, Environment::new(), input)
            .unwrap();
        let Some(Frame::SourceResourceBoundary(mut boundary)) = machine.frames.pop() else {
            unreachable!()
        };
        let key = boundary.key;
        let scope = machine.source_resource_scope(self.scope).unwrap();
        let acquired = scope.header().codec.acquire[0];
        let mut ready = NativeOwnerGuardReady::new(Arc::clone(&scope.header().owner), release);
        ready.prepare_initialized_bytes(initialized.then_some(7));
        ready.prepare_byte_callbacks(NativeByteCallbacks { read, write });
        boundary.owner = ready
            .returned(std::ptr::NonNull::<u8>::dangling().as_ptr().cast())
            .record()
            .into_guard();
        let pair = machine
            .foreign_tuple(
                &[Value::NativeStateView(key), integer(42)],
                RuntimePhase::Acquisition,
            )
            .unwrap();
        let report = machine
            .foreign_constructor(acquired, Some(pair), RuntimePhase::Acquisition)
            .unwrap();
        machine.return_source_resource(boundary, report).unwrap();
        machine.control = None;
        machine.instantiation_work = TypeWorkBudget::unbounded();
        (machine, key)
    }
    fn call(
        &self,
        machine: &Machine<'_>,
        write: bool,
    ) -> (NodeId, SourceByteCallable, Instantiation) {
        self.call_role(
            machine,
            if write {
                crate::foreign::scalar_preflight::ForeignScalarPreflightRole::ByteWrite
            } else {
                crate::foreign::scalar_preflight::ForeignScalarPreflightRole::ByteRead
            },
        )
    }
    fn call_role(
        &self,
        machine: &Machine<'_>,
        role: crate::foreign::scalar_preflight::ForeignScalarPreflightRole,
    ) -> (NodeId, SourceByteCallable, Instantiation) {
        let scope = machine.source_resource_scope(self.scope).unwrap();
        let mut selected = None;
        scope
            .visit_byte_calls(
                |call, _| {
                    if call.apply.is_some()
                        && self
                            .program()
                            .registry()
                            .scalar_preflight(call.function)
                            .unwrap()
                            .role()
                            == role
                    {
                        selected = Some(call);
                    }
                    Ok(())
                },
                &mut TypeWorkBudget::unbounded(),
            )
            .unwrap();
        let call = selected.unwrap();
        let intrinsic = self.program().nodes().iter().find_map(|node| match &node.kind {
            EffectExprKind::Pure(PureExprKind::Value(PureValue::Intrinsic(intrinsic))) if matches!(intrinsic.operation(), crate::core::packed::Intrinsic::ForeignByteRead {function} | crate::core::packed::Intrinsic::ForeignByteWrite {function} | crate::core::packed::Intrinsic::ForeignDataOf {function} | crate::core::packed::Intrinsic::ForeignReplaceData {function} if function == call.function) => Some(*intrinsic),
            _ => None,
        }).unwrap();
        let Frame::SourceResourceBoundary(boundary) = &machine.frames[0] else {
            unreachable!()
        };
        let caller = boundary.environment.instantiation.clone();
        let PureExprKind::Computation(PureComputation::TypeApplication(application)) =
            pure_expression(&machine.program, call.application).unwrap()
        else {
            unreachable!()
        };
        let mut parameters = vec![(
            role.state_parameter(intrinsic.module()).unwrap(),
            Kind::Type,
        )];
        if let Some(data) = role.data_parameter(intrinsic.module()) {
            parameters.push((data, Kind::Type));
        }
        let defining = Instantiation::default()
            .apply(
                &caller,
                &parameters,
                application.arguments(),
                application.row_arguments(),
                &mut TypeWorkBudget::unbounded(),
            )
            .unwrap();
        (
            call.apply.unwrap(),
            SourceByteCallable {
                intrinsic,
                application: call.application,
                caller: caller.clone(),
                defining,
            },
            caller,
        )
    }
}
impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.directory);
    }
}
fn integer(value: i64) -> Value {
    Value::Integer(crate::integer::Integer::from_i64(value))
}
fn operands(
    machine: &mut Machine<'_>,
    key: ActivationKey,
    write: bool,
    index: i64,
    byte: i64,
) -> Value {
    let mut values = vec![Value::NativeStateView(key), integer(index)];
    if write {
        values.push(integer(byte));
    }
    machine
        .foreign_tuple(&values, RuntimePhase::Access)
        .unwrap()
}

#[test]
fn byte_entry_authenticates_live_guard_and_original_call_before_callbacks() {
    let fixture = Fixture::new();
    READS.set(0);
    WRITES.set(0);
    RELEASES.set(0);
    for mutation in 0..6 {
        let (mut machine, key) = fixture.machine(mutation != 0);
        let (apply, mut callable, caller) = fixture.call(&machine, false);
        let actual_key = if mutation == 1 {
            ActivationKey(key.0 + 1)
        } else {
            key
        };
        let operand = operands(&mut machine, actual_key, false, 0, 0);
        if mutation == 2 {
            callable.application = apply;
        }
        if mutation == 3 {
            let scope = machine.source_resource_scope(fixture.scope).unwrap();
            callable.caller = caller
                .apply(
                    &caller,
                    &[(scope.identity(), Kind::Type)],
                    &[Type::Int],
                    &[],
                    &mut TypeWorkBudget::unbounded(),
                )
                .unwrap();
        }
        if mutation == 4 {
            let parameter = fixture
                .program()
                .registry()
                .scalar_preflight(match callable.intrinsic.operation() {
                    crate::core::packed::Intrinsic::ForeignByteRead { function } => function,
                    _ => unreachable!(),
                })
                .unwrap()
                .role()
                .byte_parameter(callable.intrinsic.module())
                .unwrap();
            callable.defining = caller
                .apply(
                    &caller,
                    &[(parameter, Kind::Type)],
                    &[Type::Int],
                    &[],
                    &mut TypeWorkBudget::unbounded(),
                )
                .unwrap();
        }
        if mutation == 5 {
            let Frame::SourceResourceBoundary(boundary) = &mut machine.frames[0] else {
                unreachable!()
            };
            boundary.consumed = true;
        }
        let heap = format!("{:?}", machine.heap);
        assert_eq!(
            machine.return_source_byte_call(apply, callable, caller, operand),
            Err(RuntimeFailure::ForeignBinding),
            "mutation {mutation}"
        );
        assert_eq!(format!("{:?}", machine.heap), heap);
        assert!(machine.control.is_none());
        assert_eq!((READS.get(), WRITES.get()), (0, 0));
        drop(machine);
        assert_eq!(RELEASES.get(), mutation + 1);
    }
}

#[test]
fn byte_entry_complete_admission_is_exact_atomic_and_retryable() {
    let fixture = Fixture::new();
    READS.set(0);
    WRITES.set(0);
    RELEASES.set(0);
    BYTE.set(5);
    for write in [false, true] {
        let (mut measure, key) = fixture.machine(true);
        let (apply, callable, caller) = fixture.call(&measure, write);
        let operand = operands(&mut measure, key, write, 0, 255);
        measure.instantiation_work = TypeWorkBudget::unbounded();
        measure
            .return_source_byte_call(apply, callable, caller, operand)
            .unwrap();
        let required = measure.instantiation_work.used();
        drop(measure);
        for prefix in [0, 5] {
            let (mut short, key) = fixture.machine(true);
            let (apply, callable, caller) = fixture.call(&short, write);
            let operand = operands(&mut short, key, write, 0, 255);
            short.instantiation_work = TypeWorkBudget::with_limit(prefix + required - 1);
            short.instantiation_work.charge(prefix).unwrap();
            let heap = format!("{:?}", short.heap);
            let counts = (READS.get(), WRITES.get());
            let byte = BYTE.get();
            assert!(
                short
                    .return_source_byte_call(apply, callable, caller, operand)
                    .is_err()
            );
            assert_eq!(format!("{:?}", short.heap), heap);
            assert_eq!((READS.get(), WRITES.get()), counts);
            assert_eq!(BYTE.get(), byte);
            drop(short);
            for _ in 0..2 {
                let (mut exact, key) = fixture.machine(true);
                let (apply, callable, caller) = fixture.call(&exact, write);
                let operand = operands(&mut exact, key, write, 0, 255);
                exact.instantiation_work = TypeWorkBudget::with_limit(prefix + required);
                exact.instantiation_work.charge(prefix).unwrap();
                exact
                    .return_source_byte_call(apply, callable, caller, operand)
                    .unwrap();
                assert_eq!(exact.instantiation_work.used(), prefix + required);
                assert!(matches!(
                    exact.control,
                    Some(Control::Return(Value::Location(_)))
                ));
            }
        }
        let (mut refused, key) = fixture.machine(true);
        let (apply, callable, caller) = fixture.call(&refused, write);
        let operand = operands(&mut refused, key, write, 0, 255);
        let counts = (READS.get(), WRITES.get());
        let heap = format!("{:?}", refused.heap);
        let _fault = super::source_byte_phases::report_reservation_fault::fail_next();
        assert!(
            refused
                .return_source_byte_call(apply, callable, caller, operand)
                .is_err()
        );
        assert_eq!((READS.get(), WRITES.get()), counts);
        assert_eq!(format!("{:?}", refused.heap), heap);
        println!("byte entry exact work: write={write}, work={required}");
    }
}

#[test]
fn byte_entry_bounds_refusal_precedes_large_byte_conversion_admission() {
    let fixture = Fixture::new();
    READS.set(0);
    WRITES.set(0);
    BYTE.set(5);
    let large =
        crate::integer::Integer::parse_decimal("18446744073709551616000000000000000000").unwrap();
    let argument = |machine: &mut Machine<'_>, key, index| {
        machine
            .foreign_tuple(
                &[
                    Value::NativeStateView(key),
                    integer(index),
                    Value::Integer(large.clone()),
                ],
                RuntimePhase::Access,
            )
            .unwrap()
    };
    let (mut measured, key) = fixture.machine(true);
    let (apply, callable, caller) = fixture.call(&measured, true);
    let operand = argument(&mut measured, key, 7);
    measured.instantiation_work = TypeWorkBudget::unbounded();
    measured
        .return_source_byte_call(apply, callable, caller, operand)
        .unwrap();
    let required = measured.instantiation_work.used();
    for _ in 0..2 {
        let (mut exact, key) = fixture.machine(true);
        let (apply, callable, caller) = fixture.call(&exact, true);
        let function = match callable.intrinsic.operation() {
            crate::core::packed::Intrinsic::ForeignByteWrite { function } => function,
            _ => unreachable!(),
        };
        let failed = fixture
            .program()
            .registry()
            .scalar_preflight(function)
            .unwrap()
            .call_codec()
            .ids()
            .conversion_failed;
        let operand = argument(&mut exact, key, 7);
        exact.instantiation_work = TypeWorkBudget::with_limit(required);
        exact
            .return_source_byte_call(apply, callable, caller, operand)
            .unwrap();
        assert_eq!(exact.instantiation_work.used(), required);
        let Some(Control::Return(Value::Location(location))) = exact.control else {
            unreachable!()
        };
        assert!(
            matches!(&exact.heap[location], HeapCell::Constructor(found, _) if *found == failed)
        );
    }
    let (mut byte_short, key) = fixture.machine(true);
    let (apply, callable, caller) = fixture.call(&byte_short, true);
    let operand = argument(&mut byte_short, key, 0);
    byte_short.instantiation_work = TypeWorkBudget::with_limit(required);
    let heap = format!("{:?}", byte_short.heap);
    let failure = byte_short
        .return_source_byte_call(apply, callable, caller, operand)
        .unwrap_err();
    assert_eq!(failure.reason_code(), "runtime.environment-capacity");
    let RuntimeFailure::Report(report) = failure else {
        unreachable!("the byte conversion refusal retains resource details")
    };
    assert_eq!(
        report.primary.resource().unwrap().cause,
        super::super::ResourceFailureCause::WorkBudgetExhausted
    );
    assert_eq!(format!("{:?}", byte_short.heap), heap);
    assert_eq!((READS.get(), WRITES.get(), BYTE.get()), (0, 0, 5));
    println!("byte entry bounds refusal before large-byte conversion: work={required}");
}

#[test]
fn forged_byte_specialization_and_guard_dispose_iteratively_on_small_stack() {
    let fixture = Fixture::new();
    std::thread::Builder::new()
        .stack_size(256 * 1024)
        .spawn(move || {
            let (mut machine, key) = fixture.machine(true);
            let (apply, mut callable, caller) = fixture.call(&machine, false);
            let function = match callable.intrinsic.operation() {
                crate::core::packed::Intrinsic::ForeignByteRead { function } => function,
                _ => unreachable!(),
            };
            let parameter = fixture
                .program()
                .registry()
                .scalar_preflight(function)
                .unwrap()
                .role()
                .byte_parameter(callable.intrinsic.module())
                .unwrap();
            let mut deep = crate::types::IterativeTypeOwner::new(Type::Unit);
            for _ in 0..32_768 {
                deep = crate::types::IterativeTypeOwner::new(Type::Tuple(Box::new([
                    deep.into_inner()
                ])));
            }
            callable.defining = Instantiation::default()
                .apply(
                    &caller,
                    &[(parameter, Kind::Type)],
                    std::slice::from_ref::<Type>(&deep),
                    &[],
                    &mut TypeWorkBudget::default(),
                )
                .unwrap();
            drop(deep);
            let operand = operands(&mut machine, key, false, 0, 0);
            assert_eq!(
                machine.return_source_byte_call(apply, callable, caller, operand),
                Err(RuntimeFailure::ForeignBinding)
            );
            assert_eq!((READS.get(), WRITES.get()), (0, 0));
            drop(machine);
            assert_eq!(RELEASES.get(), 1);
        })
        .unwrap()
        .join()
        .expect("forged specialization and last guard drain without recursive destruction");
}

#[test]
fn data_entry_exact_work_short_prefix_and_fresh_retry_preserve_payload() {
    use crate::foreign::{
        scalar_preflight::ForeignScalarPreflightRole as Role, source_bindings::SourceNativeBindings,
    };
    let fixture = Fixture::data();
    let bindings = SourceNativeBindings::default();
    for role in [Role::DataOf, Role::ReplaceData] {
        let setup = || {
            let (mut machine, key) = fixture.machine(true);
            machine.source_bindings = Some(&bindings);
            let operand = if role == Role::ReplaceData {
                machine
                    .foreign_tuple(
                        &[Value::NativeStateView(key), integer(7)],
                        RuntimePhase::Access,
                    )
                    .unwrap()
            } else {
                Value::NativeStateView(key)
            };
            // Operand construction is outside this entry-admission ledger.
            machine.instantiation_work = TypeWorkBudget::unbounded();
            (machine, operand)
        };
        let (mut measured, operand) = setup();
        let (apply, callable, caller) = fixture.call_role(&measured, role);
        measured
            .return_source_data_call(apply, callable, caller, operand)
            .unwrap();
        let required = measured.instantiation_work.used();
        drop(measured);
        for prefix in [0, 9] {
            let (mut short, operand) = setup();
            let (apply, callable, caller) = fixture.call_role(&short, role);
            let before = format!("{:?}", short.heap);
            short.instantiation_work = TypeWorkBudget::with_limit(prefix + required - 1);
            short.instantiation_work.charge(prefix).unwrap();
            assert!(
                short
                    .return_source_data_call(apply, callable, caller, operand)
                    .is_err()
            );
            assert_eq!(format!("{:?}", short.heap), before);
            let Frame::SourceResourceBoundary(boundary) = &short.frames[0] else {
                unreachable!()
            };
            assert!(
                matches!(&boundary.payload, Some(Value::Integer(value)) if *value == crate::integer::Integer::from_i64(42))
            );
            assert!(boundary.owner.is_some());
            assert!(short.control.is_none());
            drop(short);
            for _ in 0..2 {
                let (mut exact, operand) = setup();
                let (apply, callable, caller) = fixture.call_role(&exact, role);
                exact.instantiation_work = TypeWorkBudget::with_limit(prefix + required);
                exact.instantiation_work.charge(prefix).unwrap();
                exact
                    .return_source_data_call(apply, callable, caller, operand)
                    .unwrap();
                assert_eq!(exact.instantiation_work.used(), prefix + required);
                if role == Role::ReplaceData {
                    assert!(matches!(exact.control, Some(Control::Return(Value::Unit))));
                    let Frame::SourceResourceBoundary(boundary) = &exact.frames[0] else {
                        unreachable!()
                    };
                    assert!(
                        matches!(&boundary.payload, Some(Value::Integer(value)) if *value == crate::integer::Integer::from_i64(7))
                    );
                } else {
                    assert!(
                        matches!(exact.control, Some(Control::Return(Value::Integer(value))) if value == crate::integer::Integer::from_i64(42))
                    );
                }
            }
        }
        println!("Data admission exact work: role={role:?}, required={required}");
    }
}

#[test]
fn data_entry_rejects_forged_context_phase_and_state_payload_without_replacement() {
    use crate::foreign::{
        scalar_preflight::ForeignScalarPreflightRole as Role, source_bindings::SourceNativeBindings,
    };
    let fixture = Fixture::data();
    let bindings = SourceNativeBindings::default();
    for mutation in 0..8 {
        let (mut machine, key) = fixture.machine(true);
        machine.source_bindings = Some(&bindings);
        let (mut apply, mut callable, caller) = fixture.call_role(&machine, Role::ReplaceData);
        let operand = machine
            .foreign_tuple(
                &[
                    Value::NativeStateView(if mutation == 0 {
                        ActivationKey(key.0 + 1)
                    } else {
                        key
                    }),
                    if mutation == 7 {
                        Value::NativeStateView(key)
                    } else {
                        integer(7)
                    },
                ],
                RuntimePhase::Access,
            )
            .unwrap();
        if mutation == 1 {
            callable.application = apply;
        }
        if mutation == 2 || mutation == 3 {
            let role = Role::ReplaceData;
            let formal = if mutation == 2 {
                role.state_parameter(callable.intrinsic.module())
            } else {
                role.data_parameter(callable.intrinsic.module())
            }
            .unwrap();
            callable.defining = callable
                .defining
                .apply(
                    &caller,
                    &[(formal, Kind::Type)],
                    &[Type::Bool],
                    &[],
                    &mut TypeWorkBudget::unbounded(),
                )
                .unwrap();
        }
        if mutation == 4 {
            apply = callable.application;
        }
        if mutation == 5 || mutation == 6 {
            let Frame::SourceResourceBoundary(boundary) = &mut machine.frames[0] else {
                unreachable!()
            };
            if mutation == 5 {
                boundary.consumed = true;
            } else {
                boundary.phase = ProviderPhase::Acquire;
            }
        }
        let heap = format!("{:?}", machine.heap);
        assert!(
            machine
                .return_source_data_call(apply, callable, caller, operand)
                .is_err(),
            "mutation {mutation}"
        );
        assert_eq!(format!("{:?}", machine.heap), heap);
        let Frame::SourceResourceBoundary(boundary) = &machine.frames[0] else {
            unreachable!()
        };
        assert!(
            matches!(&boundary.payload, Some(Value::Integer(value)) if *value == crate::integer::Integer::from_i64(42))
        );
        assert!(boundary.owner.is_some());
        assert!(machine.control.is_none());
    }
}

#[test]
fn data_entry_independent_core_refuses_arbitrary_state_and_callable_wrappers() {
    let fixture = Fixture::data();
    for source in [
        "import @builtin.foreign as Foreign\nmain : Unit -> Int\nmain () = Foreign.data_of 7\n",
        "import @builtin.foreign as Foreign\nmain : Unit -> Unit\nmain () = Foreign.replace_data (7, 42)\n",
        "import @builtin.foreign as Foreign\nhelper<S, D> : S -> D\nhelper state = Foreign.data_of state\nmain : Unit -> Int\nmain () = 42\n",
        "import @builtin.foreign as Foreign\nhelper<S, D> : (S, D) -> Unit\nhelper value = Foreign.replace_data value\nmain : Unit -> Int\nmain () = 42\n",
    ] {
        let entry = fixture.directory.join("refused.ash");
        fs::write(&entry, source).unwrap();
        let failure = compile_path(RunConfiguration {
            entry,
            roots: ModuleRoots::empty(),
        })
        .unwrap_err();
        assert!(
            matches!(failure, crate::driver::FileFailure::Pipeline(ref diagnostic)
            if matches!(diagnostic.failure(), crate::driver::PipelineFailure::Validation(_))),
            "compatible S/D shapes and ordinary wrappers grant no descriptor authority: {failure:?}"
        );
    }
}
