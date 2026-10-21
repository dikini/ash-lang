//! Hostile mutations of genuine independently admitted checked lifecycle Core.
//! Caller supplies a fresh actual program for each mutation; no authority is minted.

use super::*;

#[derive(Clone, Copy, Debug)]
pub(crate) enum Mutation {
    HostActual,
    InterpretationActual,
    FinishContinuation,
}

fn selected(program: &UnvalidatedEffectProgram) -> (usize, NodeId) {
    let mut matching = program
        .nodes
        .iter()
        .enumerate()
        .filter_map(|(index, stored)| {
            let EffectExprKind::Operation(EffectOperation::SourceResourceScope(scope)) =
                &stored.kind
            else {
                return None;
            };
            matches!(
                scope.header().codec.report,
                SourceResourceReportCodec::CheckedScope { .. }
            )
            .then_some(index)
        });
    let index = matching
        .next()
        .expect("actual connected checked resource scope");
    assert!(
        matching.next().is_none(),
        "control fixture must select exactly one checked scope"
    );
    (
        index,
        NodeId::new(program.arena, u32::try_from(index).unwrap()),
    )
}

fn scope(program: &UnvalidatedEffectProgram, index: usize) -> &SourceResourceScopeNode {
    let EffectExprKind::Operation(EffectOperation::SourceResourceScope(scope)) =
        &program.nodes[index].kind
    else {
        panic!("selected checked scope remains present");
    };
    scope
}

pub(crate) fn mutate_and_authenticate(
    program: &mut UnvalidatedEffectProgram,
    mutation: Mutation,
) -> ValidationError {
    let (index, id) = selected(program);
    scope(program, index)
        .authenticate(id, program, &mut TypeWorkBudget::default())
        .expect("genuine canonical scope authenticates before hostile mutation");
    let template = Arc::clone(scope(program, index).original());
    let changed;
    match mutation {
        Mutation::HostActual => {
            let EffectExprKind::Operation(EffectOperation::SourceResourceScope(scope)) =
                &mut program.nodes[index].kind
            else {
                unreachable!()
            };
            let host = scope
                .header()
                .original
                .host
                .expect("original authored host selector")
                .position;
            let owned = scope.header().original.owned_position;
            assert_ne!(host, owned);
            let descriptor = Arc::get_mut(&mut scope.descriptor)
                .expect("fresh actual program owns the scope descriptor exclusively");
            assert!(matches!(
                descriptor.arguments[host],
                KindedArgument::TypeArg(Type::Variable(_))
            ));
            let original = std::mem::replace(
                &mut descriptor.arguments[host],
                KindedArgument::TypeArg(Type::Int),
            );
            crate::types::discard_kinded_argument_iteratively(original);
            assert!(
                matches!(descriptor.arguments[owned], KindedArgument::TypeArg(Type::Variable(actual)) if actual == descriptor.identity)
            );
            changed = true;
        }
        Mutation::InterpretationActual => {
            let EffectExprKind::Operation(EffectOperation::SourceResourceScope(scope)) =
                &mut program.nodes[index].kind
            else {
                unreachable!()
            };
            let descriptor = Arc::get_mut(&mut scope.descriptor)
                .expect("fresh actual program owns the scope descriptor exclusively");
            let interpretation = descriptor
                .interpretations
                .first_mut()
                .expect("actual native lifecycle interpretation");
            let symbol = interpretation.symbol();
            let contract = symbol.prepared().checked_contract().unwrap();
            let host = contract.symbols()[symbol.symbol_index()].host_parameter();
            let effect = interpretation.effect();
            assert!(matches!(
                effect.arguments()[host],
                KindedArgument::TypeArg(Type::Variable(_))
            ));
            let mut work = TypeWorkBudget::default();
            let mut arguments = effect
                .arguments()
                .iter()
                .map(|argument| {
                    crate::types::clone_kinded_argument_with_budget(argument, &mut work).unwrap()
                })
                .collect::<Vec<_>>();
            let original =
                std::mem::replace(&mut arguments[host], KindedArgument::TypeArg(Type::Int));
            crate::types::discard_kinded_argument_iteratively(original);
            let replacement = crate::types::EffectInstance::new_kinded(
                effect.effect(),
                arguments.into_boxed_slice(),
            );
            assert_eq!(replacement.arguments().len(), effect.arguments().len());
            interpretation.effect = replacement;
            changed = true;
        }
        Mutation::FinishContinuation => {
            let selected = scope(program, index);
            let original = &selected.original().finish;
            let mut free = None;
            let mut trace = None;
            for (position, stored) in original.nodes.iter().enumerate() {
                let EffectExprKind::Operation(EffectOperation::Request(request)) = &stored.kind
                else {
                    continue;
                };
                let original_id = NodeId::new(original.arena, u32::try_from(position).unwrap());
                if request.operation() == selected.header().teardown.operation() {
                    assert!(free.replace(original_id).is_none());
                } else if original
                    .registry
                    .effect(request.effect().effect())
                    .is_some_and(|effect| effect.spelling == "Trace")
                {
                    assert!(trace.replace(original_id).is_none());
                }
            }
            let free = free.expect("actual original native finish request");
            let trace = trace.expect("actual required original finish Trace request");
            let free_span = node(original, free)
                .unwrap()
                .origin
                .as_ref()
                .unwrap()
                .primary_span();
            let trace_span = node(original, trace)
                .unwrap()
                .origin
                .as_ref()
                .unwrap()
                .primary_span();
            assert_eq!(free_span.source(), trace_span.source());
            assert!(
                trace_span.range().start() >= free_span.range().end(),
                "selected Trace is the original post-request continuation"
            );
            let mut targets = selected.descriptor.copies[1]
                .nodes
                .iter()
                .filter_map(|(source, target)| (*source == trace).then_some(*target));
            let target = targets
                .next()
                .expect("exact copied finish Trace correspondence");
            assert!(targets.next().is_none());
            let target_index = node(program, target).unwrap();
            assert_eq!(target_index.ty, Type::Unit);
            let EffectExprKind::Operation(EffectOperation::Request(copied)) = &target_index.kind
            else {
                panic!("actual copied continuation request");
            };
            let EffectExprKind::Operation(EffectOperation::Request(original_request)) =
                &node(original, trace).unwrap().kind
            else {
                unreachable!()
            };
            assert_eq!(copied.operation(), original_request.operation());
            assert!(!target_index.effects.known().is_empty());
            // Keep NodeId, type, origin, claimed row, original/template and all
            // copy maps untouched. Only the executable continuation kind goes.
            program.nodes[target.index().unwrap()].kind = EffectExprKind::Pure(
                PureExprKind::Value(PureValue::Unit(crate::core::literal::UnitNode)),
            );
            changed = true;
        }
    }
    assert!(changed, "a real selected scope occurrence was mutated");
    let selected = scope(program, index);
    assert!(Arc::ptr_eq(selected.original(), &template));
    let error = selected
        .authenticate(id, program, &mut TypeWorkBudget::default())
        .expect_err("independent scope authentication must reject the actual hostile mutation");
    assert_eq!(
        error.reason(),
        ValidationReason::Registry,
        "mutation must refuse semantically before whole-Core checks, not exhaust a budget"
    );
    error
}

pub(crate) fn assert_budget_controls(program: &UnvalidatedEffectProgram) {
    let (index, id) = selected(program);
    let selected = scope(program, index);
    let template = Arc::clone(selected.original());
    let run = |work: &mut TypeWorkBudget| selected.authenticate(id, program, work);
    let mut measured = TypeWorkBudget::default();
    run(&mut measured)
        .expect("actual canonical scope authentication fits the unchanged default allowance");
    let cost = measured.used();
    assert!(cost > 0);
    for prefix in [0, 7] {
        let mut exact = TypeWorkBudget::with_limit(prefix + cost);
        exact.charge(prefix).unwrap();
        run(&mut exact).unwrap();
        assert_eq!(exact.used(), prefix + cost);
        assert_eq!(
            run(&mut exact).unwrap_err().reason(),
            ValidationReason::Resource
        );
        let mut short = TypeWorkBudget::with_limit(prefix + cost - 1);
        short.charge(prefix).unwrap();
        assert_eq!(
            run(&mut short).unwrap_err().reason(),
            ValidationReason::Resource
        );
    }
    for _ in 0..2 {
        let mut fresh = TypeWorkBudget::with_limit(cost);
        run(&mut fresh).unwrap();
        assert_eq!(fresh.used(), cost);
    }
    assert!(Arc::ptr_eq(selected.original(), &template));
    run(&mut TypeWorkBudget::default()).unwrap();
}

// Proposed addition to existing private core::source_resource checked tests.
// Caller validates genuine canonical Core first, gives a fresh identity copy,
// then independently requires whole-Core semantic/non-Resource rejection.
// This removes NativeHost<H> on the actual copied scope, not outer Trace.
pub(crate) fn erase_copied_completion_host_row(program: &mut UnvalidatedEffectProgram) {
    let (index, id) = selected(program);
    scope(program, index)
        .authenticate(id, program, &mut TypeWorkBudget::default())
        .expect("actual canonical selected checked scope before row erasure");
    let template = Arc::clone(scope(program, index).original());
    let header = scope(program, index).header();
    let position = header.original.host.unwrap().position;
    let KindedArgument::TypeArg(Type::Variable(host_id)) =
        scope(program, index).descriptor.arguments[position]
    else {
        panic!("actual copied scope retains exact lexical H");
    };
    let mut work = TypeWorkBudget::default();
    let row = crate::types::clone_effect_row_with_budget(&program.nodes[index].effects, &mut work)
        .unwrap();
    let matching = row.known().iter().filter(|instance| {
        instance.effect().module().is_builtin_foreign()
            && instance.effect().declaration() == crate::module::FOREIGN_NATIVE_HOST_LOCAL
            && matches!(instance.arguments(), [KindedArgument::TypeArg(Type::Variable(id))] if *id == host_id)
    }).collect::<Vec<_>>();
    assert_eq!(
        matching.len(),
        1,
        "actual completion row contains exact canonical NativeHost<H>"
    );
    let host =
        crate::core::effect::clone_effect_instance_with_budget(matching[0], &mut work).unwrap();
    let reduced = row
        .remove_exact_with_budget(&host, &mut work)
        .unwrap()
        .unwrap();
    // Change only the claimed copied scope row. Free/Trace operations, full
    // vectors, copied maps, state/result type, descriptor, registry and originals
    // remain intact. Do not recompute a replacement row from those nodes.
    program.nodes[index].effects = reduced;
    assert!(Arc::ptr_eq(scope(program, index).original(), &template));
}
