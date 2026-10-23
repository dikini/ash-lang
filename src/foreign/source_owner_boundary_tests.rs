//! Unit-injected returns, never native/initialized-byte execution evidence.
use super::*;
use crate::foreign::source_runtime::{NativeOwnerGuardReady, NativeOwnerStorage};
use std::rc::Rc;

thread_local! { static DISPOSALS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) }; }
fn dispose(_: &[NativeOwnerOperand]) {
    DISPOSALS.set(DISPOSALS.get() + 1);
}

struct FixtureRequest {
    receipt: SourceOwnerScopeRequest,
    state: crate::types::IterativeTypeOwner,
    access: crate::types::IterativeTypeOwner,
}
impl std::ops::Deref for FixtureRequest {
    type Target = SourceOwnerScopeRequest;
    fn deref(&self) -> &Self::Target {
        &self.receipt
    }
}
impl std::ops::DerefMut for FixtureRequest {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.receipt
    }
}
impl FixtureRequest {
    fn new(
        receipt: SourceOwnerScopeRequest,
        scope: &crate::core::source_resource::SourceResourceScopeNode,
        work: &mut TypeWorkBudget,
    ) -> Self {
        let crate::types::Type::Tuple(fields) = scope.finish.parameter.ty() else {
            panic!("actual copied finish State/data")
        };
        Self {
            receipt,
            state: crate::types::IterativeTypeOwner::new(
                crate::types::clone_type_with_budget(&fields[0], work).unwrap(),
            ),
            access: crate::types::IterativeTypeOwner::new(
                crate::types::clone_type_with_budget(scope.handle.ty(), work).unwrap(),
            ),
        }
    }
}

fn nodes(program: &crate::core::ValidatedEffectProgram) -> Vec<crate::core::NodeId> {
    let mut work = TypeWorkBudget::default();
    let mut pending = vec![program.root()];
    let mut seen = std::collections::HashSet::new();
    let mut result = Vec::new();
    while let Some(id) = pending.pop() {
        work.charge(1).unwrap();
        if !seen.insert(id) {
            continue;
        }
        let node = program.node(id).unwrap();
        work.charge(node.kind.child_count() + 1).unwrap();
        for index in 0..node.kind.child_count() {
            pending.push(node.kind.child_at(index).unwrap());
        }
        result.push(id);
    }
    result
}

fn with_context(
    test: impl FnOnce(&crate::core::ValidatedEffectProgram, FixtureRequest, FixtureRequest),
) {
    let (program, _) = crate::elaborate::checked_owner_passive_program();
    let executable = crate::eval::ExecutableProgram::Effect(program.shared());
    let mut work = TypeWorkBudget::default();
    let ids = nodes(&program);
    for node_id in ids.iter().copied() {
        let node = program.node(node_id).unwrap();
        let EffectExprKind::Operation(EffectOperation::SourceResourceScope(scope)) = &node.kind
        else {
            continue;
        };
        let find = |phase: SourceOwnerPhase,
                    symbol: &Arc<CheckedForeignSymbol>,
                    work: &mut TypeWorkBudget| {
            ids.iter().copied().find_map(|request_id| {
                let request = program.node(request_id).unwrap();
                let EffectExprKind::Operation(EffectOperation::Request(call)) = &request.kind
                else {
                    return None;
                };
                if call.operation() != symbol.operation() {
                    return None;
                }
                SourceOwnerScopeRequest::admit(
                    &executable,
                    node_id,
                    request_id,
                    phase,
                    call.effect(),
                    symbol,
                    work,
                )
                .ok()
            })
        };
        if let (Some(acquire), Some(finish)) = (
            find(
                SourceOwnerPhase::Acquire,
                &scope.header().acquire,
                &mut work,
            ),
            find(
                SourceOwnerPhase::Finish,
                &scope.header().teardown,
                &mut work,
            ),
        ) {
            assert!(
                SourceOwnerScopeRequest::admit(
                    &executable,
                    node_id,
                    acquire._request,
                    SourceOwnerPhase::Acquire,
                    &acquire._instance,
                    &scope.header().teardown,
                    &mut work
                )
                .is_err(),
                "a different genuine operation cannot acquire this scope"
            );
            test(
                &program,
                FixtureRequest::new(acquire, scope, &mut work),
                FixtureRequest::new(finish, scope, &mut work),
            );
            return;
        }
    }
    panic!("genuine independent checked Core acquire and finish requests");
}
fn with_requests(test: impl FnOnce(FixtureRequest, FixtureRequest)) {
    with_context(|_, acquire, finish| test(acquire, finish));
}
fn with_request(test: impl FnOnce(FixtureRequest, Arc<CheckedForeignSymbol>)) {
    with_requests(|receipt, _| {
        let symbol = Arc::clone(&receipt._scope.header().acquire);
        test(receipt, symbol);
    });
}

fn limits() -> crate::foreign::source_runtime::CheckedOwnerLimits {
    crate::foreign::source_runtime::CheckedOwnerLimits {
        groups: 1,
        owners: 1,
        pending: 1,
        observations: 4,
        history: 5,
        continuations: 1,
    }
}
fn authority_guard(
    receipt: &FixtureRequest,
    activation: usize,
    work: &mut TypeWorkBudget,
) -> (NativeOwnerGuardReady, Rc<NativeOwnerStorage>) {
    let storage = Rc::new(NativeOwnerStorage::default());
    let mut ready = NativeOwnerGuardReady::in_storage(
        Arc::clone(&receipt._scope.header().owner),
        dispose,
        true,
        1,
        0,
        Rc::clone(&storage),
    )
    .unwrap();
    let state = crate::types::IterativeTypeOwner::new(
        crate::types::clone_type_with_budget(&receipt.state, work).unwrap(),
    );
    let access = crate::types::IterativeTypeOwner::new(
        crate::types::clone_type_with_budget(&receipt.access, work).unwrap(),
    );
    work.charge(1).unwrap();
    ready
        .prepare_authority(
            activation,
            state,
            access,
            Vec::new(),
            vec![NativeOwnerOperand::Address(std::ptr::null_mut())],
            work,
        )
        .unwrap();
    (ready, storage)
}
fn ready(
    receipt: &FixtureRequest,
    activation: usize,
    work: &mut TypeWorkBudget,
) -> (NativeOwnerGuardReady, Rc<NativeOwnerStorage>) {
    let (mut ready, storage) = authority_guard(receipt, activation, work);
    ready
        .prepare_checked_boundary(receipt, activation, Some(limits()), work)
        .unwrap();
    ready.begin_checked_acquire().unwrap();
    (ready, storage)
}

#[test]
fn checked_owner_boundary_record_survives_unpublished_output_failure() {
    with_request(|receipt, _| {
        let mut work = TypeWorkBudget::default();
        let (ready, _storage) = ready(&receipt, 71, &mut work);
        let handle = ready.checked_boundary(&mut work).unwrap().unwrap(); // prepaid bookkeeping, not invocation authority
        let returned = ready.returned(std::ptr::NonNull::<u8>::dangling().as_ptr().cast());
        let guard = returned.record().into_guard().unwrap();
        let state = handle.snapshot();
        assert_eq!(state.native, super::super::checked_control::Native::Owned);
        assert_eq!(state.k, super::super::checked_control::K::Absent);
        assert!(guard.ordinary_live());
        handle.output_failed();
        assert_eq!(
            handle.snapshot().k,
            super::super::checked_control::K::Absent
        );
        assert!(guard.completion_address().is_some());
        assert!(handle.publish(71, receipt._scope_node, &mut work).is_err());
        // Physical guard remains independently responsible for host disposal.
        drop(guard);
        assert_eq!(
            handle.snapshot().native,
            super::super::checked_control::Native::Owned
        );
    });
}

#[test]
fn checked_owner_boundary_reservation_is_exact_short_spent_and_fresh() {
    with_request(|receipt, _| {
        let callbacks_before = DISPOSALS.get();
        let mut measured = TypeWorkBudget::default();
        let (_ready, _) = ready(&receipt, 72, &mut measured);
        let required = measured.used();
        for prefix in [0, 9] {
            let mut exact = TypeWorkBudget::with_limit(prefix + required);
            exact.charge(prefix).unwrap();
            let (_ready, _) = ready(&receipt, 72, &mut exact);
            assert_eq!(exact.used(), prefix + required);
            let mut short = TypeWorkBudget::with_limit(prefix + required - 1);
            short.charge(prefix).unwrap();
            let (mut candidate, _) = authority_guard(&receipt, 72, &mut short);
            assert!(
                candidate
                    .prepare_checked_boundary(&receipt, 72, Some(limits()), &mut short)
                    .is_err()
            );
            assert!(
                candidate
                    .checked_boundary(&mut TypeWorkBudget::default())
                    .unwrap()
                    .is_none()
            );
            assert!(
                candidate
                    .prepare_checked_boundary(&receipt, 72, Some(limits()), &mut short)
                    .is_err()
            );
            let mut fresh = TypeWorkBudget::with_limit(required);
            let (_fresh, _) = ready(&receipt, 72, &mut fresh);
            assert_eq!(fresh.used(), required);
        }
        assert_eq!(DISPOSALS.get(), callbacks_before);
    });
}

#[test]
fn checked_owner_boundary_exact_activation_scope_and_independent_group() {
    with_request(|receipt, _| {
        let mut work = TypeWorkBudget::default();
        let (first, _first_storage) = ready(&receipt, 73, &mut work);
        let first_handle = first.checked_boundary(&mut work).unwrap().unwrap();
        let guard = first
            .returned(std::ptr::NonNull::<u8>::dangling().as_ptr().cast())
            .record()
            .into_guard()
            .unwrap();
        assert!(
            first_handle
                .publish(74, receipt._scope_node, &mut work)
                .is_err()
        );
        first_handle
            .publish(73, receipt._scope_node, &mut work)
            .unwrap();
        assert!(
            first_handle
                .publish(73, receipt._scope_node, &mut work)
                .is_err()
        );
        let (second, _second_storage) = ready(&receipt, 73, &mut work);
        let second_handle = second.checked_boundary(&mut work).unwrap().unwrap();
        assert_ne!(
            first_handle.snapshot().identity,
            second_handle.snapshot().identity
        );
        assert_eq!(
            second_handle.snapshot().k,
            super::super::checked_control::K::Absent
        );
        first_handle.output_failed();
        assert!(!second_handle.snapshot().terminal);
        drop(guard);
    });
}

#[test]
fn checked_owner_boundary_finish_commit_survives_output_failure_without_replay() {
    with_requests(|acquire, finish| {
        let mut work = TypeWorkBudget::default();
        let (ready, storage) = ready(&acquire, 81, &mut work);
        let handle = ready.checked_boundary(&mut work).unwrap().unwrap();
        let guard = ready
            .returned(std::ptr::NonNull::<u8>::dangling().as_ptr().cast())
            .record()
            .into_guard()
            .unwrap();
        handle.publish(81, acquire._scope_node, &mut work).unwrap();
        handle.closing(81, acquire._scope_node, &mut work).unwrap();
        guard
            .prepare_checked_finish(&finish, 81, false, &mut work)
            .unwrap();
        guard.begin_checked_finish().unwrap();
        // A Rust unit callback does not establish native free/ABI truth.
        let before_finish = DISPOSALS.get();
        let disposition = guard.finish(
            dispose,
            true,
            &[NativeOwnerOperand::Address(
                std::ptr::NonNull::<u8>::dangling().as_ptr().cast(),
            )],
            false,
        );
        assert!(!disposition.is_retained());
        let state = handle.snapshot();
        assert_eq!(
            state.native,
            super::super::checked_control::Native::Consumed
        );
        assert_eq!(state.k, super::super::checked_control::K::Discharged);
        assert_eq!(
            state.continuation,
            super::super::checked_control::Continuation::Required
        );
        handle.output_failed();
        assert!(handle.source_continued(81, acquire._scope_node).is_err());
        assert_eq!(
            handle.snapshot().continuation,
            super::super::checked_control::Continuation::Required
        );
        assert_eq!(
            handle.snapshot().k,
            super::super::checked_control::K::Discharged
        );
        // Host cleanup sees the physically consumed slot and cannot replay it.
        assert_eq!(DISPOSALS.get(), before_finish + 1);
        assert!(storage.close());
        assert_eq!(DISPOSALS.get(), before_finish + 1);
        assert_eq!(
            handle.snapshot().native,
            super::super::checked_control::Native::Consumed
        );
    });
}

#[test]
fn checked_owner_boundary_request_window_donor_and_operation_substitution_refuse() {
    with_requests(|acquire, mut finish| {
        let mut work = TypeWorkBudget::default();
        let (ready, _storage) = ready(&acquire, 82, &mut work);
        let handle = ready.checked_boundary(&mut work).unwrap().unwrap();
        let guard = ready
            .returned(std::ptr::NonNull::<u8>::dangling().as_ptr().cast())
            .record()
            .into_guard()
            .unwrap();
        handle.publish(82, acquire._scope_node, &mut work).unwrap();
        // Genuine positive first; only the private receipt coordinate changes.
        finish._window = Some(acquire._request);
        assert!(
            guard
                .prepare_checked_finish(&finish, 82, false, &mut work)
                .is_err()
        );
        finish._window = None;
        let correct_request = finish._request;
        finish._request = acquire._request;
        assert!(
            guard
                .prepare_checked_finish(&finish, 82, false, &mut work)
                .is_err()
        );
        finish._request = correct_request;
        assert!(
            guard
                .prepare_checked_finish(&finish, 83, false, &mut work)
                .is_err()
        );
        with_requests(|_, donor| {
            assert!(
                guard
                    .prepare_checked_finish(&donor, 82, false, &mut work)
                    .is_err()
            );
        });
        handle.closing(82, acquire._scope_node, &mut work).unwrap();
        guard
            .prepare_checked_finish(&finish, 82, false, &mut work)
            .unwrap();
        guard.begin_checked_finish().unwrap();
        assert!(guard.begin_checked_finish().is_err());
        drop(guard);
        assert!(handle.snapshot().unresolved); // no forged finish observation
        assert_eq!(
            handle.snapshot().native,
            super::super::checked_control::Native::Owned
        );
    });
}

#[test]
fn checked_owner_boundary_null_return_and_closed_public_admission_are_distinct() {
    with_request(|receipt, _| {
        let mut work = TypeWorkBudget::default();
        let (ready, _storage) = ready(&receipt, 84, &mut work);
        let handle = ready.checked_boundary(&mut work).unwrap().unwrap();
        assert!(
            ready
                .returned(std::ptr::null_mut())
                .record()
                .into_guard()
                .is_none()
        );
        assert_eq!(
            handle.snapshot().native,
            super::super::checked_control::Native::NoOwner
        );
        assert!(!handle.snapshot().unresolved);
        assert!(handle.publish(84, receipt._scope_node, &mut work).is_err());
    });
    let (program, _) = crate::elaborate::checked_owner_passive_program();
    assert!(
        admit_source_native_program(
            &program,
            &mut SourceNativeBindings::default(),
            &mut TypeWorkBudget::default()
        )
        .is_err()
    );
    // Still no initializer, callback, protected context or executable approval.
}

fn eight_byte_program() -> crate::core::ValidatedEffectProgram {
    crate::elaborate::checked_owner_passive_program_for_source(
        include_str!("../../tests/fixtures/checked-owner-runtime/owner.ash"),
        "import @builtin.foreign as Foreign\nimport producer as Producer\nmain : Unit -> Foreign.CheckedScope<Producer.CopyProbe, Unit, Unit>\nmain () = Producer.run ()\n",
    ).0
}
fn eight_byte_copy_request(
    program: &crate::core::ValidatedEffectProgram,
    work: &mut TypeWorkBudget,
) -> SourceOwnerCopyRequest {
    let executable = crate::eval::ExecutableProgram::Effect(program.shared());
    let ids = nodes(program);
    for scope_id in ids.iter().copied() {
        let EffectExprKind::Operation(EffectOperation::SourceResourceScope(scope)) =
            &program.node(scope_id).unwrap().kind
        else {
            continue;
        };
        let mut copied = None;
        scope.visit_byte_calls(|call, _| {
            if call.apply.is_some() && program.registry().scalar_preflight(call.function).is_some_and(|fact| fact.role() == super::super::scalar_preflight::ForeignScalarPreflightRole::CheckedCopyBytes) { copied = Some(call); }
            Ok(())
        }, work).unwrap();
        let Some(call) = copied else {
            continue;
        };
        for window in ids.iter().copied() {
            if let Ok(receipt) = SourceOwnerCopyRequest::admit(
                &executable,
                scope_id,
                window,
                call.apply.unwrap(),
                call.application,
                call.function,
                crate::core::source_resource::SourceResourcePhase::Handler,
                work,
            ) {
                return receipt;
            }
        }
    }
    panic!("genuine checked-copy original in its exact source window");
}

type EightByteFixture = (
    crate::core::ValidatedEffectProgram,
    FixtureRequest,
    SourceOwnerScopeRequest,
    Vec<(SourceOwnerScopeRequest, Arc<CheckedForeignSymbol>)>,
    SourceOwnerCopyRequest,
);

fn eight_byte_fixture() -> EightByteFixture {
    let program = eight_byte_program();
    let executable = crate::eval::ExecutableProgram::Effect(program.shared());
    let ids = nodes(&program);
    let mut work = TypeWorkBudget::default();
    let mut selected = None;
    for scope_id in ids.iter().copied() {
        let EffectExprKind::Operation(EffectOperation::SourceResourceScope(scope)) =
            &program.node(scope_id).unwrap().kind
        else {
            continue;
        };
        let mut acquire = None;
        let mut finish = None;
        let mut queries = Vec::new();
        for request_id in ids.iter().copied() {
            let EffectExprKind::Operation(EffectOperation::Request(call)) =
                &program.node(request_id).unwrap().kind
            else {
                continue;
            };
            let Some(symbol) = program.registry().native_symbol(call.operation()) else {
                continue;
            };
            if Arc::ptr_eq(symbol, &scope.header().acquire) {
                acquire = SourceOwnerScopeRequest::admit(
                    &executable,
                    scope_id,
                    request_id,
                    SourceOwnerPhase::Acquire,
                    call.effect(),
                    symbol,
                    &mut work,
                )
                .ok();
            } else if Arc::ptr_eq(symbol, &scope.header().teardown) {
                finish = SourceOwnerScopeRequest::admit(
                    &executable,
                    scope_id,
                    request_id,
                    SourceOwnerPhase::Finish,
                    call.effect(),
                    symbol,
                    &mut work,
                )
                .ok();
            } else {
                for window_id in ids.iter().copied() {
                    let EffectExprKind::Operation(EffectOperation::SourceCopyWindow(window)) =
                        &program.node(window_id).unwrap().kind
                    else {
                        continue;
                    };
                    if let Ok(receipt) = SourceOwnerScopeRequest::admit_window(
                        &executable,
                        scope_id,
                        window_id,
                        request_id,
                        crate::core::source_resource::SourceResourcePhase::Handler,
                        window.arguments(),
                        call.effect(),
                        symbol,
                        &mut work,
                    ) {
                        queries.push((receipt, Arc::clone(symbol)));
                        break;
                    }
                }
            }
        }
        if let (Some(acquire), Some(finish)) = (acquire, finish)
            && queries.len() == 2
        {
            selected = Some((
                FixtureRequest::new(acquire, scope, &mut work),
                finish,
                queries,
            ));
            break;
        }
    }
    let (acquire, finish, mut queries) =
        selected.expect("actual Allocate, QueryBytes, ByteLength and Free originals");
    queries.sort_by_key(|(_, symbol)| {
        usize::from(symbol.symbol().access_result().is_some_and(|result| {
            matches!(
                result,
                crate::foreign::source_contract::PreparedAccessResult::Extent { .. }
            )
        }))
    });
    assert!(matches!(
        queries[0].1.symbol().access_result(),
        Some(crate::foreign::source_contract::PreparedAccessResult::View { .. })
    ));
    assert!(matches!(
        queries[1].1.symbol().access_result(),
        Some(crate::foreign::source_contract::PreparedAccessResult::Extent { .. })
    ));
    assert_eq!(acquire._scope.header().original.interpreted.len(), 2);
    assert_eq!(acquire._window_calls, 2);
    assert_eq!(acquire._copy_calls, Some(1));
    let copy = eight_byte_copy_request(&program, &mut work);
    assert!(Arc::ptr_eq(&copy.scope, &acquire._scope));
    (program, acquire, finish, queries, copy)
}

/// Retained PR101 supplies genuine checked byte/Core PREPARATION. Native
/// returns and the copy completion below are injected, not native memory evidence.
#[test]
fn checked_owner_boundary_initialized_eight_byte_full_request_preparation() {
    let (program, acquire, finish, queries, copy) = eight_byte_fixture();
    let executable = crate::eval::ExecutableProgram::Effect(program.shared());
    let mut work = TypeWorkBudget::default();
    let donor_program = eight_byte_program();
    let donor = eight_byte_copy_request(&donor_program, &mut TypeWorkBudget::default());
    let policy = crate::foreign::source_runtime::CheckedOwnerLimits {
        observations: 5,
        history: 6,
        ..limits()
    };
    let mut one_short = policy;
    one_short.observations = 4;
    let (mut refused, _) = authority_guard(&acquire, 91, &mut work);
    assert!(
        refused
            .prepare_checked_boundary(&acquire, 91, Some(one_short), &mut work)
            .is_err()
    );
    assert!(refused.checked_boundary(&mut work).unwrap().is_none());
    let (mut ready, _storage) = authority_guard(&acquire, 91, &mut work);
    ready
        .prepare_checked_boundary(&acquire, 91, Some(policy), &mut work)
        .unwrap();
    ready.begin_checked_acquire().unwrap();
    let handle = ready.checked_boundary(&mut work).unwrap().unwrap();
    let guard = ready
        .returned(std::ptr::NonNull::<u8>::dangling().as_ptr().cast())
        .record()
        .into_guard()
        .unwrap();
    handle.publish(91, acquire._scope_node, &mut work).unwrap();
    for (mut receipt, symbol) in queries {
        let original_scope = receipt._scope_node;
        receipt._scope_node = receipt._request;
        assert!(
            guard
                .prepare_checked_borrow(&receipt, &symbol, 91, &mut work)
                .is_err()
        );
        receipt._scope_node = original_scope;
        let ticket = guard
            .prepare_checked_borrow(&receipt, &symbol, 91, &mut work)
            .unwrap()
            .unwrap();
        ticket.begin().unwrap();
        assert!(handle.snapshot().unresolved);
        let returned = ticket.returned(); // UNIT-INJECTED callback return only
        assert_eq!(
            returned.snapshot().native,
            super::super::checked_control::Native::Owned
        );
        assert!(!returned.snapshot().unresolved);
    }
    assert!(guard.prepare_checked_copy(&donor, 91, &mut work).is_err());
    assert!(guard.prepare_checked_copy(&copy, 92, &mut work).is_err());
    // Admission starts from the canonical receipt, then changes one actual
    // coordinate. No synthetic token or copied passive role record is admitted.
    assert!(
        SourceOwnerCopyRequest::admit(
            &executable,
            copy.scope_node,
            copy.identity.window,
            copy.identity.application,
            copy.identity.application,
            copy.identity.function,
            copy.phase,
            &mut work
        )
        .is_err()
    );
    assert!(
        SourceOwnerCopyRequest::admit(
            &executable,
            copy.scope_node,
            copy.scope_node,
            copy.identity.apply,
            copy.identity.application,
            copy.identity.function,
            copy.phase,
            &mut work
        )
        .is_err()
    );
    let before_copy = handle.snapshot();
    let mut measured = TypeWorkBudget::default();
    let _prepared = guard
        .prepare_checked_copy(&copy, 91, &mut measured)
        .unwrap();
    let required = measured.used();
    for prefix in [0, 7] {
        let mut exact = TypeWorkBudget::with_limit(prefix + required);
        exact.charge(prefix).unwrap();
        let _exact = guard.prepare_checked_copy(&copy, 91, &mut exact).unwrap();
        assert_eq!(exact.used(), prefix + required);
        let mut short = TypeWorkBudget::with_limit(prefix + required - 1);
        short.charge(prefix).unwrap();
        assert!(guard.prepare_checked_copy(&copy, 91, &mut short).is_err());
        assert!(guard.prepare_checked_copy(&copy, 91, &mut short).is_err());
        let mut fresh = TypeWorkBudget::with_limit(required);
        let _fresh = guard.prepare_checked_copy(&copy, 91, &mut fresh).unwrap();
        assert_eq!(fresh.used(), required);
    }
    assert_eq!(handle.snapshot(), before_copy);
    let mut stale = guard.prepare_checked_copy(&copy, 91, &mut work).unwrap();
    let mut ticket = guard.prepare_checked_copy(&copy, 91, &mut work).unwrap();
    ticket.begin().unwrap();
    assert!(handle.snapshot().unresolved);
    let observed = ticket.returned(); // UNIT-INJECTED observation, no memory read
    assert_eq!(observed.snapshot().last_copy, Some(copy.identity));
    assert_eq!(observed.snapshot().observations, 4);
    // A repeated source occurrence cannot spend the final mandatory Finish cell.
    assert!(guard.prepare_checked_copy(&copy, 91, &mut work).is_err());
    assert!(stale.begin().is_err());
    assert_eq!(observed.snapshot().observations, 4);
    handle.closing(91, acquire._scope_node, &mut work).unwrap();
    guard
        .prepare_checked_finish(&finish, 91, false, &mut work)
        .unwrap();
    guard.begin_checked_finish().unwrap();
    let _disposition = guard.finish(
        dispose,
        true,
        &[NativeOwnerOperand::Address(
            std::ptr::NonNull::<u8>::dangling().as_ptr().cast(),
        )],
        false,
    );
    assert_eq!(handle.snapshot().observations, 5);
    assert_eq!(handle.snapshot().history, 6);
    assert_eq!(
        handle.snapshot().continuation,
        super::super::checked_control::Continuation::Required
    );
    handle.source_continued(91, acquire._scope_node).unwrap(); // UNIT-INJECTED continuation, not an authored Trace execution
    assert_eq!(
        handle.snapshot().continuation,
        super::super::checked_control::Continuation::Completed
    );
    assert!(
        admit_source_native_program(
            &program,
            &mut SourceNativeBindings::default(),
            &mut TypeWorkBudget::default()
        )
        .is_err()
    );
}

#[test]
fn checked_owner_boundary_policy_data_is_not_approval_and_short_capacity_refuses() {
    with_request(|receipt, _| {
        let mut work = TypeWorkBudget::default();
        let (mut candidate, _) = authority_guard(&receipt, 92, &mut work);
        assert!(
            candidate
                .prepare_checked_boundary(&receipt, 92, None, &mut work)
                .is_err()
        );
        for field in 0..6 {
            let mut cap = limits();
            match field {
                0 => cap.groups = 0,
                1 => cap.owners = 0,
                2 => cap.pending = 0,
                3 => cap.observations = 1,
                4 => cap.history = 4,
                _ => cap.continuations = 0,
            }
            let (mut candidate, _) = authority_guard(&receipt, 92, &mut work);
            assert!(
                candidate
                    .prepare_checked_boundary(&receipt, 92, Some(cap), &mut work)
                    .is_err()
            );
            assert!(candidate.checked_boundary(&mut work).unwrap().is_none());
        }
        candidate
            .prepare_checked_boundary(&receipt, 92, Some(limits()), &mut work)
            .unwrap();
        assert_eq!(
            candidate
                .checked_boundary(&mut work)
                .unwrap()
                .unwrap()
                .snapshot()
                .native,
            super::super::checked_control::Native::NoOwner
        );
        // Numeric data alone has not entered any callback or armed an address.
    });
}

#[test]
fn checked_owner_boundary_requires_existing_exact_physical_slot_authority() {
    with_request(|receipt, _| {
        let mut work = TypeWorkBudget::default();
        let mut absent = NativeOwnerGuardReady::in_storage(
            Arc::clone(&receipt._scope.header().owner),
            dispose,
            true,
            1,
            0,
            Rc::new(NativeOwnerStorage::default()),
        )
        .unwrap();
        assert!(
            absent
                .prepare_checked_boundary(&receipt, 101, Some(limits()), &mut work)
                .is_err()
        );
        assert!(absent.checked_boundary(&mut work).unwrap().is_none());
        let (mut donor, _) = authority_guard(&receipt, 102, &mut work);
        assert!(
            donor
                .prepare_checked_boundary(&receipt, 101, Some(limits()), &mut work)
                .is_err()
        );
        assert!(donor.checked_boundary(&mut work).unwrap().is_none());
        donor
            .prepare_checked_boundary(&receipt, 102, Some(limits()), &mut work)
            .unwrap();
        assert_eq!(
            donor
                .checked_boundary(&mut work)
                .unwrap()
                .unwrap()
                .snapshot()
                .native,
            super::super::checked_control::Native::NoOwner
        );
    });
}

/// Supplies bookkeeping and the real validated Core only. It never supplies an
/// admitted executable, binding table, callback capability or protected context.
pub(crate) fn with_recorded_boundary_for_test(
    test: impl FnOnce(
        &crate::core::ValidatedEffectProgram,
        crate::core::NodeId,
        crate::foreign::source_runtime::NativeOwnerBoundary,
    ),
) {
    with_context(|program, acquire, finish| {
        let mut work = TypeWorkBudget::default();
        let (ready, _storage) = ready(&acquire, 111, &mut work);
        let handle = ready.checked_boundary(&mut work).unwrap().unwrap();
        let guard = ready
            .returned(std::ptr::NonNull::<u8>::dangling().as_ptr().cast())
            .record()
            .into_guard()
            .unwrap();
        handle.publish(111, acquire._scope_node, &mut work).unwrap();
        handle.closing(111, acquire._scope_node, &mut work).unwrap();
        guard
            .prepare_checked_finish(&finish, 111, false, &mut work)
            .unwrap();
        guard.begin_checked_finish().unwrap();
        let _disposition = guard.finish(
            dispose,
            true,
            &[NativeOwnerOperand::Address(
                std::ptr::NonNull::<u8>::dangling().as_ptr().cast(),
            )],
            false,
        );
        test(program, acquire._scope_node, handle);
    });
}

/// Genuine source/Core coordinates plus unit-injected physical observations.
/// This contains no executable admission, binding table or protected context.
pub(crate) struct EightByteBoundary<'p> {
    pub(crate) program: &'p crate::core::ValidatedEffectProgram,
    pub(crate) scope: crate::core::NodeId,
    pub(crate) window: crate::core::NodeId,
    pub(crate) apply: crate::core::NodeId,
    pub(crate) application: crate::core::NodeId,
    pub(crate) function: crate::resolved::BinderId,
    pub(crate) view_symbol: Arc<CheckedForeignSymbol>,
    pub(crate) guard: crate::foreign::source_runtime::NativeOwnerGuard,
    pub(crate) boundary: crate::foreign::source_runtime::NativeOwnerBoundary,
}

pub(crate) fn with_eight_byte_boundary_for_test(
    prepare: impl FnOnce(
        &crate::core::ValidatedEffectProgram,
        crate::core::NodeId,
        &crate::types::Type,
        &crate::types::Type,
        NativeOwnerGuardReady,
    ) -> NativeOwnerGuardReady,
    test: impl FnOnce(EightByteBoundary<'_>),
) {
    let (program, acquire, _finish, queries, copy) = eight_byte_fixture();
    let mut work = TypeWorkBudget::default();
    let storage = Rc::new(NativeOwnerStorage::default());
    let ready = NativeOwnerGuardReady::in_storage(
        Arc::clone(&acquire._scope.header().owner),
        dispose,
        true,
        1,
        0,
        Rc::clone(&storage),
    )
    .unwrap();
    let mut ready = prepare(
        &program,
        acquire._scope_node,
        &acquire.state,
        &acquire.access,
        ready,
    );
    // Injected producer contract observation for this unit, not a C allocation.
    ready.prepare_initialized_bytes(Some(8));
    let policy = crate::foreign::source_runtime::CheckedOwnerLimits {
        observations: 5,
        history: 6,
        ..limits()
    };
    ready
        .prepare_checked_boundary(&acquire, 111, Some(policy), &mut work)
        .unwrap();
    ready.begin_checked_acquire().unwrap();
    let boundary = ready.checked_boundary(&mut work).unwrap().unwrap();
    let guard = ready
        .returned(std::ptr::NonNull::<u8>::dangling().as_ptr().cast())
        .record()
        .into_guard()
        .unwrap();
    boundary
        .publish(111, acquire._scope_node, &mut work)
        .unwrap();
    let view_symbol = Arc::clone(&queries[0].1);
    for (receipt, symbol) in queries {
        let ticket = guard
            .prepare_checked_borrow(&receipt, &symbol, 111, &mut work)
            .unwrap()
            .unwrap();
        ticket.begin().unwrap();
        let _injected = ticket.returned();
    }
    test(EightByteBoundary {
        program: &program,
        scope: acquire._scope_node,
        window: copy.identity.window,
        apply: copy.identity.apply,
        application: copy.identity.application,
        function: copy.identity.function,
        view_symbol,
        guard,
        boundary,
    });
}
