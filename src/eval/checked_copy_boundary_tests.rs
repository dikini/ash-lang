//! Actual private evaluator phase with genuine Core and injected physical data.
//! The safe Rust reader observes initialized Rust storage, never C memory. No
//! executable admission, native binding, protected context or public startup.
use super::super::SourceResourceBoundary;
use super::*;
use crate::{
    core::{PureComputation, PureExprKind, PureValue},
    foreign::source_runtime::{NativeOwnerBoundary, NativeOwnerGuardReady, NativeOwnerOperand},
    types::{IterativeTypeOwner, Kind, TypeWorkBudget},
};
use std::cell::Cell;

const PATTERN: [u8; 8] = [5, 255, 0, 65, 66, 67, 0, 9];
thread_local! { static READS: Cell<usize> = const { Cell::new(0) }; }
fn read(address: *mut core::ffi::c_void, index: usize) -> u8 {
    assert_eq!(address, std::ptr::NonNull::<u8>::dangling().as_ptr().cast());
    READS.set(READS.get() + 1);
    PATTERN[index]
}

fn prepare_authority(
    program: &crate::core::ValidatedEffectProgram,
    scope_id: NodeId,
    state: &crate::types::Type,
    access: &crate::types::Type,
    mut ready: NativeOwnerGuardReady,
) -> NativeOwnerGuardReady {
    let EffectExprKind::Operation(EffectOperation::SourceResourceScope(scope)) =
        &program.node(scope_id).unwrap().kind
    else {
        unreachable!()
    };
    let mut work = TypeWorkBudget::default();
    let context = super::super::Instantiation::default()
        .acquire(scope.identity(), ActivationKey(111), &mut work, None)
        .unwrap();
    let state = IterativeTypeOwner::new(context.ty(state, &mut work).unwrap());
    let access = IterativeTypeOwner::new(context.ty(access, &mut work).unwrap());
    ready
        .prepare_authority(
            111,
            state,
            access,
            Vec::new(),
            vec![NativeOwnerOperand::Address(std::ptr::null_mut())],
            &mut work,
        )
        .unwrap();
    ready
}

fn with_case(
    test: impl FnOnce(
        &mut Machine<'_>,
        NodeId,
        super::super::SourceByteCallable,
        super::super::Instantiation,
        Value,
        &NativeOwnerBoundary,
    ),
) {
    crate::foreign::source_bindings::with_eight_byte_boundary_for_test(
        prepare_authority,
        |fixture| {
            let mut machine = Machine::new_effect(fixture.program);
            machine.instantiation_work = TypeWorkBudget::default();
            machine.control = None;
            machine.live_resources = 1;
            let EffectExprKind::Operation(EffectOperation::SourceResourceScope(scope)) =
                &fixture.program.node(fixture.scope).unwrap().kind
            else {
                unreachable!()
            };
            let mut environment = Environment::new();
            environment.instantiation = environment
                .instantiation
                .acquire(
                    scope.identity(),
                    ActivationKey(111),
                    &mut machine.instantiation_work,
                    None,
                )
                .unwrap();
            let Some(ExecutableNode::Effect(expression)) = machine.program.node(fixture.window)
            else {
                unreachable!()
            };
            let EffectExprKind::Operation(EffectOperation::SourceCopyWindow(window)) =
                &expression.kind
            else {
                unreachable!()
            };
            let mut window_environment = environment.clone();
            window_environment.instantiation = window_environment
                .instantiation
                .acquire(
                    window.identity(),
                    ActivationKey(112),
                    &mut machine.instantiation_work,
                    None,
                )
                .unwrap();
            let mut arguments = Vec::new();
            for argument in window.arguments() {
                arguments.push(
                    window_environment
                        .instantiation
                        .argument(argument, &mut machine.instantiation_work)
                        .unwrap()
                        .into_inner(),
                );
            }
            let intrinsic = fixture.program.nodes().iter().find_map(|node| match &node.kind {
                EffectExprKind::Pure(PureExprKind::Value(PureValue::Intrinsic(intrinsic)))
                    if matches!(intrinsic.operation(), crate::core::packed::Intrinsic::ForeignCopyBytes { function } if function == fixture.function) => Some(*intrinsic),
                _ => None,
            }).unwrap();
            let fact = fixture
                .program
                .registry()
                .scalar_preflight(fixture.function)
                .unwrap();
            let PureExprKind::Computation(PureComputation::TypeApplication(application)) =
                super::super::pure_expression(&machine.program, fixture.application).unwrap()
            else {
                unreachable!()
            };
            let caller = window_environment.instantiation.clone();
            let defining = super::super::Instantiation::default()
                .apply(
                    &caller,
                    &[
                        (
                            fact.role().host_parameter(fact.module()).unwrap(),
                            Kind::Type,
                        ),
                        (
                            fact.role().view_parameter(fact.module()).unwrap(),
                            Kind::Type,
                        ),
                    ],
                    application.arguments(),
                    application.row_arguments(),
                    &mut machine.instantiation_work,
                )
                .unwrap();
            let callable = super::super::SourceByteCallable {
                intrinsic,
                application: fixture.application,
                caller: caller.clone(),
                defining,
            };
            let operands = machine
                .foreign_tuple(
                    &[
                        Value::NativeStateView(ActivationKey(111)),
                        Value::Integer(crate::integer::Integer::from_i64(0)),
                    ],
                    RuntimePhase::Access,
                )
                .unwrap();
            let observer = fixture.boundary.prepaid_scope_observer();
            machine.frames.push(Frame::SourceResourceBoundary(Box::new(
                SourceResourceBoundary {
                    checked: Some(fixture.boundary),
                    report_slot: None,
                    node: fixture.scope,
                    key: ActivationKey(111),
                    environment,
                    owner: Some(fixture.guard),
                    dependencies: Vec::new(),
                    phase: ProviderPhase::Body,
                    payload: None,
                    saved: None,
                    consumed: false,
                    blocked: false,
                    discarded: false,
                },
            )));
            machine.frames.push(Frame::SourceWindowBoundary(Box::new(
                SourceWindowBoundary {
                    node: fixture.window,
                    key: ActivationKey(112),
                    provider: ActivationKey(111),
                    owner: ActivationKey(111),
                    environment: window_environment,
                    views: vec![WindowView {
                        raw: NativeViewReturned::new(
                            std::ptr::NonNull::<u8>::dangling().as_ptr().cast(),
                            read,
                        ),
                        symbol: fixture.view_symbol,
                        operands,
                    }],
                    arguments: WindowArguments(arguments),
                },
            )));
            let view = WindowViewKey {
                window: ActivationKey(112),
                slot: 0,
            };
            let operand = machine
                .foreign_tuple(
                    &[
                        Value::NativeWindowView(view),
                        Value::NativeWindowExtent(WindowExtentKey {
                            view,
                            length: PATTERN.len(),
                        }),
                    ],
                    RuntimePhase::Access,
                )
                .unwrap();
            READS.set(0);
            // Fixture preparation remains bounded and separate from the phase's
            // measured default/exact budgets. No unbounded work is introduced.
            machine.instantiation_work = TypeWorkBudget::default();
            test(
                &mut machine,
                fixture.apply,
                callable,
                caller,
                operand,
                &observer,
            );
            assert!(machine.source_bindings.is_none());
        },
    );
}

fn copied_bytes<'m>(machine: &'m Machine<'_>) -> &'m [u8] {
    let Some(Control::Return(Value::Location(location))) = &machine.control else {
        panic!("actual copy return")
    };
    let super::super::HeapCell::Constructor(_, Some(Value::Bytes(bytes))) =
        &machine.heap[*location]
    else {
        panic!("independent complete Bytes")
    };
    bytes
}

#[test]
fn checked_copy_real_phase_admission_observation_and_output_failure() {
    // Canonical real phase first, before any authority/metadata mutation.
    let mut required = 0;
    with_case(|machine, apply, callable, caller, operand, observed| {
        let before = observed.snapshot();
        assert_eq!(before.observations, 3);
        machine
            .return_source_view_call(apply, callable.clone(), caller.clone(), operand.clone())
            .unwrap();
        required = machine.instantiation_work.used();
        assert_eq!(copied_bytes(machine), PATTERN);
        assert_eq!(READS.get(), PATTERN.len());
        assert_eq!(observed.snapshot().observations, 4);
        let Frame::SourceWindowBoundary(window) = &machine.frames[1] else {
            unreachable!()
        };
        let crate::core::packed::Intrinsic::ForeignCopyBytes { function } =
            callable.intrinsic.operation()
        else {
            unreachable!()
        };
        assert_eq!(
            observed.snapshot().last_copy_coordinates(),
            Some((window.node, apply, callable.application, function))
        );
        assert!(!observed.snapshot().unresolved);
        // Repeating a genuine occurrence may not spend mandatory Finish space.
        assert!(
            machine
                .return_source_view_call(apply, callable, caller, operand)
                .is_err()
        );
        assert_eq!(READS.get(), PATTERN.len());
        assert_eq!(observed.snapshot().observations, 4);
    });
    for mutation in 0..3 {
        with_case(|machine, apply, mut callable, caller, operand, observed| {
            let before = observed.snapshot();
            if mutation < 2 {
                let Value::Location(location) = operand else {
                    unreachable!()
                };
                let super::super::HeapCell::Tuple(fields) = &mut machine.heap[location] else {
                    unreachable!()
                };
                if mutation == 0 {
                    fields[0] = Value::NativeWindowView(WindowViewKey {
                        window: ActivationKey(113),
                        slot: 0,
                    });
                } else {
                    fields[1] = Value::NativeWindowExtent(WindowExtentKey {
                        view: WindowViewKey {
                            window: ActivationKey(112),
                            slot: 1,
                        },
                        length: PATTERN.len(),
                    });
                }
            } else {
                let fact = machine
                    .program
                    .registry()
                    .scalar_preflight(match callable.intrinsic.operation() {
                        crate::core::packed::Intrinsic::ForeignCopyBytes { function } => function,
                        _ => unreachable!(),
                    })
                    .unwrap();
                callable.defining = callable
                    .defining
                    .apply(
                        &caller,
                        &[(
                            fact.role().host_parameter(fact.module()).unwrap(),
                            Kind::Type,
                        )],
                        &[crate::types::Type::Int],
                        &[],
                        &mut machine.instantiation_work,
                    )
                    .unwrap();
            }
            assert!(
                machine
                    .return_source_view_call(apply, callable, caller, operand)
                    .is_err()
            );
            assert_eq!(READS.get(), 0);
            assert_eq!(observed.snapshot(), before);
        });
    }
    // A genuine second program's physical slot cannot stand in for this scope.
    with_case(|machine, apply, callable, caller, operand, observed| {
        crate::foreign::source_bindings::with_eight_byte_boundary_for_test(
            prepare_authority,
            |donor| {
                let Frame::SourceResourceBoundary(boundary) = &mut machine.frames[0] else {
                    unreachable!()
                };
                boundary.owner = Some(donor.guard);
                let before = observed.snapshot();
                let donor_before = donor.boundary.snapshot();
                assert!(
                    machine
                        .return_source_view_call(apply, callable, caller, operand)
                        .is_err()
                );
                assert_eq!(READS.get(), 0);
                assert_eq!(observed.snapshot(), before);
                assert_eq!(donor.boundary.snapshot(), donor_before);
            },
        );
    });
    for prefix in [0, 5] {
        with_case(|machine, apply, callable, caller, operand, observed| {
            machine.instantiation_work = TypeWorkBudget::with_limit(prefix + required - 1);
            machine.instantiation_work.charge(prefix).unwrap();
            let before = observed.snapshot();
            assert!(
                machine
                    .return_source_view_call(
                        apply,
                        callable.clone(),
                        caller.clone(),
                        operand.clone()
                    )
                    .is_err()
            );
            assert_eq!(READS.get(), 0);
            assert_eq!(observed.snapshot(), before);
            assert!(
                machine
                    .return_source_view_call(
                        apply,
                        callable.clone(),
                        caller.clone(),
                        operand.clone()
                    )
                    .is_err()
            );
            machine.instantiation_work = TypeWorkBudget::with_limit(prefix + required);
            machine.instantiation_work.charge(prefix).unwrap();
            machine
                .return_source_view_call(apply, callable, caller, operand)
                .unwrap();
            assert_eq!(machine.instantiation_work.used(), prefix + required);
            assert_eq!(copied_bytes(machine), PATTERN);
            assert_eq!(READS.get(), PATTERN.len());
        });
    }
    with_case(|machine, apply, callable, caller, operand, observed| {
        machine
            .return_source_view_call(apply, callable, caller, operand)
            .unwrap();
        let copied = match &machine.control {
            Some(Control::Return(value)) => value.clone(),
            _ => unreachable!(),
        };
        machine.frames.pop(); // the finished lexical loan, not owner completion
        let Frame::SourceResourceBoundary(boundary) = machine.frames.pop().unwrap() else {
            unreachable!()
        };
        machine.instantiation_work = TypeWorkBudget::with_limit(0);
        assert!(machine.return_source_resource(boundary, copied).is_err());
        assert_eq!(READS.get(), PATTERN.len());
        let after = observed.snapshot();
        assert_eq!(after.observations, 4);
        assert!(after.last_copy_coordinates().is_some());
        assert!(after.terminal);
        assert_ne!(
            after.continuation,
            crate::foreign::source_runtime::CheckedOwnerContinuation::Completed
        );
    });
}
