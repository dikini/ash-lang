//! Staged private Core tests: actual checked scalar Borrow, never native execution.
//! Caller supplies fresh identity Core after independent canonical validation.
use super::*;
use crate::types::EffectInstance;

#[derive(Clone, Copy, Debug)]
pub(crate) enum Mutation {
    InterpretationHost,
    InterpretationOwned,
    MissingInterpretation,
    CopiedReadHost,
    CopiedReadHostRow,
}

fn selected(program: &UnvalidatedEffectProgram) -> (usize, NodeId) {
    let mut candidates = program
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
    let index = candidates
        .next()
        .expect("actual canonical checked resource scope");
    assert!(
        candidates.next().is_none(),
        "one actual scope in direct Borrow fixture"
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
        panic!("selected actual scope remains present");
    };
    scope
}

fn replace_argument(
    instance: &EffectInstance,
    position: usize,
    replacement: Type,
) -> EffectInstance {
    let mut work = TypeWorkBudget::default();
    let mut arguments = instance
        .arguments()
        .iter()
        .map(|argument| {
            crate::types::clone_kinded_argument_with_budget(argument, &mut work).unwrap()
        })
        .collect::<Vec<_>>();
    assert!(matches!(
        arguments[position],
        KindedArgument::TypeArg(Type::Variable(_))
    ));
    let old = std::mem::replace(
        &mut arguments[position],
        KindedArgument::TypeArg(replacement),
    );
    crate::types::discard_kinded_argument_iteratively(old);
    EffectInstance::new_kinded(instance.effect(), arguments.into_boxed_slice())
}

pub(crate) fn mutate_and_authenticate(
    program: &mut UnvalidatedEffectProgram,
    mutation: Mutation,
) -> ValidationError {
    let (index, id) = selected(program);
    scope(program, index)
        .authenticate(id, program, &mut TypeWorkBudget::default())
        .expect("actual scalar Borrow scope authenticates before each independent mutation");
    let template = Arc::clone(scope(program, index).original());
    let read_index = {
        let selected = scope(program, index);
        let mut candidates = selected
            .descriptor
            .interpretations
            .iter()
            .enumerate()
            .filter_map(|(index, native)| {
                (native.symbol().symbol().name() == "Read"
                    && matches!(
                        native.symbol().symbol().owner_call(),
                        Some(PreparedOwnerCall::Borrow { .. })
                    ))
                .then_some(index)
            });
        let index = candidates
            .next()
            .expect("actual original Read Borrow interpretation");
        assert!(candidates.next().is_none());
        index
    };
    let read = Arc::clone(scope(program, index).descriptor.interpretations[read_index].symbol());
    assert!(Arc::ptr_eq(
        read.owner().unwrap(),
        &scope(program, index).header().owner
    ));
    let host_position =
        read.prepared().checked_contract().unwrap().symbols()[read.symbol_index()].host_parameter();
    let application = read.symbol().owner_call().unwrap().application();
    let owned_position = match application.arguments()[read.owner().unwrap().owned_parameter()] {
        crate::foreign::source_contract::PreparedOwnerArgument::Type(position) => position,
        _ => panic!("actual owner R must be Type-kind"),
    };
    assert_ne!(host_position, owned_position);

    match mutation {
        Mutation::InterpretationHost | Mutation::InterpretationOwned => {
            let selected = scope(program, index);
            let instance = selected.descriptor.interpretations[read_index].effect();
            let replacement = match mutation {
                Mutation::InterpretationHost => {
                    replace_argument(instance, host_position, Type::Int)
                }
                Mutation::InterpretationOwned => {
                    let KindedArgument::TypeArg(Type::Variable(host)) =
                        instance.arguments()[host_position]
                    else {
                        panic!("actual lexical H in Read full vector");
                    };
                    replace_argument(instance, owned_position, Type::Variable(host))
                }
                _ => unreachable!(),
            };
            let EffectExprKind::Operation(EffectOperation::SourceResourceScope(selected)) =
                &mut program.nodes[index].kind
            else {
                unreachable!()
            };
            let descriptor =
                Arc::get_mut(&mut selected.descriptor).expect("fresh identity owns descriptor");
            descriptor.interpretations[read_index].effect = replacement;
        }
        Mutation::MissingInterpretation => {
            let EffectExprKind::Operation(EffectOperation::SourceResourceScope(selected)) =
                &mut program.nodes[index].kind
            else {
                unreachable!()
            };
            let descriptor =
                Arc::get_mut(&mut selected.descriptor).expect("fresh identity owns descriptor");
            let mut interpretations = std::mem::take(&mut descriptor.interpretations).into_vec();
            let removed = interpretations.remove(read_index);
            assert!(Arc::ptr_eq(removed.symbol(), &read));
            descriptor.interpretations = interpretations.into_boxed_slice();
        }
        Mutation::CopiedReadHost | Mutation::CopiedReadHostRow => {
            let selected = scope(program, index);
            let original = template.original_handler();
            let mut originals =
                original
                    .nodes
                    .iter()
                    .enumerate()
                    .filter_map(|(position, stored)| {
                        let EffectExprKind::Operation(EffectOperation::Request(request)) =
                            &stored.kind
                        else {
                            return None;
                        };
                        (request.operation() == read.operation()).then_some(NodeId::new(
                            original.arena,
                            u32::try_from(position).unwrap(),
                        ))
                    });
            let source = originals
                .next()
                .expect("actual direct handler Read request");
            assert!(originals.next().is_none());
            let mut targets = selected.descriptor.copies[2]
                .nodes
                .iter()
                .filter_map(|(from, to)| (*from == source).then_some(*to));
            let target = targets
                .next()
                .expect("exact original-to-copied handler Read correspondence");
            assert!(targets.next().is_none());
            let stored = node(program, target).unwrap();
            let EffectExprKind::Operation(EffectOperation::Request(request)) = &stored.kind else {
                panic!("actual copied Read request");
            };
            assert_eq!(request.operation(), read.operation());
            match mutation {
                Mutation::CopiedReadHost => {
                    let replacement = replace_argument(request.effect(), host_position, Type::Int);
                    let EffectExprKind::Operation(EffectOperation::Request(request)) =
                        &mut program.nodes[target.index().unwrap()].kind
                    else {
                        unreachable!()
                    };
                    // Keep actual registered operation, State operand, result
                    // type/row/origin, interpretation and every map untouched.
                    request.effect = replacement;
                }
                Mutation::CopiedReadHostRow => {
                    let mut work = TypeWorkBudget::default();
                    let host = crate::foreign::checked_source::checked_host_instance(
                        &read,
                        request.effect(),
                        &mut work,
                    )
                    .unwrap()
                    .expect("actual checked Read H effect");
                    assert!(
                        stored
                            .effects
                            .known()
                            .iter()
                            .any(|effect| effect.effect() == read.effect()),
                        "claimed Read row retains original native instance"
                    );
                    let row =
                        crate::types::clone_effect_row_with_budget(&stored.effects, &mut work)
                            .unwrap();
                    let reduced = row
                        .remove_exact_with_budget(&host, &mut work)
                        .unwrap()
                        .unwrap();
                    // Only erase this request's exact NativeHost<H>, preserving
                    // its native instance and all completion/Trace rows elsewhere.
                    program.nodes[target.index().unwrap()].effects = reduced;
                }
                _ => unreachable!(),
            }
        }
    }
    assert!(Arc::ptr_eq(scope(program, index).original(), &template));
    let error = scope(program, index)
        .authenticate(id, program, &mut TypeWorkBudget::default())
        .expect_err(
            "actual hostile Read descriptor/copy must fail direct independent scope authentication",
        );
    assert_eq!(
        error.reason(),
        ValidationReason::Registry,
        "direct semantic refusal must not exhaust work"
    );
    error
}

/// Component evidence on the genuine admitted request, separate from source
/// provider/capture guards. Removing the BoundaryFailed alternative fails this
/// inventory even when earlier source checks would reject hostile branch code.
pub(crate) fn assert_original_borrow_outcomes(program: &UnvalidatedEffectProgram) {
    let (index, id) = selected(program);
    let scope = scope(program, index);
    scope
        .authenticate(id, program, &mut TypeWorkBudget::default())
        .unwrap();
    let header = scope.header();
    let original = scope.original().original_handler();
    let (request_id, request, symbol) = original
        .nodes
        .iter()
        .enumerate()
        .find_map(|(index, stored)| {
            let EffectExprKind::Operation(EffectOperation::Request(request)) = &stored.kind else {
                return None;
            };
            let symbol = original.registry.native_symbol(request.operation())?;
            (symbol.symbol().name() == "Read"
                && matches!(symbol.owner_role(), Some(PreparedOwnerCall::Borrow { .. })))
            .then_some((
                NodeId::new(original.arena, u32::try_from(index).unwrap()),
                request,
                symbol,
            ))
        })
        .expect("genuine original handler Read request");
    assert!(Arc::ptr_eq(symbol.owner().unwrap(), &header.owner));
    let EffectExprKind::Pure(PureExprKind::Variable(current)) =
        &node(original, request.operand()).unwrap().kind
    else {
        panic!("the direct State-only request uses its actual Current binder");
    };
    let call = symbol.call_codec().ids();
    for phase in [
        SourceResourcePhase::Handler,
        SourceResourcePhase::Acquire,
        SourceResourcePhase::Finish,
    ] {
        let mut work = TypeWorkBudget::default();
        let mut values = facts(&mut work).unwrap();
        let mut path = FlowPath::new(&mut work).unwrap();
        path.bind(current.binder(), 2, &mut work).unwrap();
        assert!(matches!(values.fact(2).unwrap(), FlowFact::Current));
        let result = eval_flow(
            original,
            header,
            request_id,
            phase,
            path,
            &mut values,
            0,
            &mut work,
        );
        if phase != SourceResourcePhase::Handler {
            let Err(error) = result else {
                panic!("checked Borrow is handler-only");
            };
            assert_eq!(error.reason(), ValidationReason::Registry);
            continue;
        }
        let results = result.unwrap();
        assert_eq!(
            results.len(),
            2,
            "actual scalar Borrow follows returned and independent boundary outcomes"
        );
        let mut returned = 0;
        let mut boundary = 0;
        for (value, path) in results {
            assert!(
                !path.attempted_teardown && !path.consumed && path.checked_finish_outcome.is_none()
            );
            let FlowFact::Constructor(constructor, Some(payload)) = values.fact(value).unwrap()
            else {
                panic!("only actual checked Borrow reply alternatives");
            };
            assert!(matches!(
                values.fact(*payload).unwrap(),
                FlowFact::Independent
            ));
            if *constructor == call.returned {
                returned += 1;
            } else if *constructor == ConstructorId::new(call.call, 2) {
                boundary += 1;
            } else {
                panic!("unrelated reply cannot become a Borrow outcome");
            }
        }
        assert_eq!((returned, boundary), (1, 1));
    }
}
