//! Canonical-first checked-byte/window authority mutation controls.
//! Caller supplies fresh identity-traversed canonical actual byte/window Core.
use super::*;

#[derive(Clone, Copy, Debug)]
pub(crate) enum Mutation {
    RequestHostActual,
    RequestHostRow,
    NativeOrder,
}

pub(crate) fn mutate(program: &mut UnvalidatedEffectProgram, mutation: Mutation) {
    let indices = program.nodes.iter().enumerate().filter_map(|(i, stored)| {
        matches!(&stored.kind, EffectExprKind::Operation(EffectOperation::SourceResourceScope(scope))
            if matches!(scope.header().codec.report, SourceResourceReportCodec::CheckedScope { .. }))
            .then_some(i)
    }).collect::<Vec<_>>();
    assert_eq!(indices.len(), 1);
    let index = indices[0];
    let id = NodeId::new(program.arena, u32::try_from(index).unwrap());
    let EffectExprKind::Operation(EffectOperation::SourceResourceScope(scope)) =
        &program.nodes[index].kind
    else {
        unreachable!()
    };
    scope
        .authenticate(id, program, &mut TypeWorkBudget::default())
        .expect("actual byte/window canonical scope first");
    let template = Arc::clone(scope.original());
    let mut copy_apply = None;
    scope
        .visit_byte_calls(
            |call, _| {
                if call.function.local() == 13 && call.apply.is_some() {
                    assert!(copy_apply
                        .replace(call.apply.expect("actual applied checked_copy_bytes"))
                        .is_none());
                }
                Ok(())
            },
            &mut TypeWorkBudget::default(),
        )
        .unwrap();
    let copy_apply = copy_apply.expect("actual copied checked_copy_bytes flow fact");
    let original = &template.handler;
    let query = original
        .nodes
        .iter()
        .enumerate()
        .find_map(|(i, stored)| {
            let EffectExprKind::Operation(EffectOperation::Request(request)) = &stored.kind else {
                return None;
            };
            original
                .registry
                .effect(request.effect().effect())
                .is_some_and(|e| e.spelling == "QueryBytes")
                .then_some(NodeId::new(original.arena, u32::try_from(i).unwrap()))
        })
        .expect("genuine original window QueryBytes request");
    let target = scope.descriptor.copies[2]
        .nodes
        .iter()
        .find_map(|(source, target)| (*source == query).then_some(*target))
        .expect("actual original-to-copied query mapping");
    match mutation {
        Mutation::RequestHostActual => {
            let stored = &mut program.nodes[target.index().unwrap()];
            let EffectExprKind::Operation(EffectOperation::Request(request)) = &stored.kind else {
                panic!("copied request");
            };
            let mut work = TypeWorkBudget::default();
            let mut arguments = request
                .effect()
                .arguments()
                .iter()
                .map(|a| crate::types::clone_kinded_argument_with_budget(a, &mut work).unwrap())
                .collect::<Vec<_>>();
            assert_eq!(arguments.len(), 3, "complete W,H,R vector");
            assert!(matches!(
                arguments[1],
                KindedArgument::TypeArg(Type::Variable(_))
            ));
            let old = std::mem::replace(&mut arguments[1], KindedArgument::TypeArg(Type::Int));
            crate::types::discard_kinded_argument_iteratively(old);
            let effect = crate::types::EffectInstance::new_kinded(
                request.effect().effect(),
                arguments.into_boxed_slice(),
            );
            stored.kind = EffectExprKind::Operation(EffectOperation::Request(
                crate::core::effect::RequestNode::new(
                    effect,
                    request.operation(),
                    request.operand(),
                ),
            ));
        }
        Mutation::RequestHostRow => {
            // The actual applied checked_copy_bytes row carries NativeHost<H>;
            // a raw QueryBytes request may instead claim its own native effect.
            let stored = &mut program.nodes[copy_apply.index().unwrap()];
            let mut work = TypeWorkBudget::default();
            let row =
                crate::types::clone_effect_row_with_budget(&stored.effects, &mut work).unwrap();
            let hosts = row
                .known()
                .iter()
                .filter(|e| {
                    e.effect().module().is_builtin_foreign()
                        && e.effect().declaration() == crate::module::FOREIGN_NATIVE_HOST_LOCAL
                })
                .collect::<Vec<_>>();
            assert_eq!(hosts.len(), 1, "actual request has exact Host row");
            let host = crate::core::effect::clone_effect_instance_with_budget(hosts[0], &mut work)
                .unwrap();
            stored.effects = row
                .remove_exact_with_budget(&host, &mut work)
                .unwrap()
                .unwrap();
        }
        Mutation::NativeOrder => {
            let EffectExprKind::Operation(EffectOperation::SourceResourceScope(scope)) =
                &mut program.nodes[index].kind
            else {
                unreachable!()
            };
            let descriptor = Arc::get_mut(&mut scope.descriptor).expect("fresh descriptor");
            assert_eq!(
                descriptor.interpretations.len(),
                2,
                "actual Allocate,Free inventory"
            );
            assert_eq!(
                descriptor.interpretations[0].symbol().symbol().name(),
                "Allocate"
            );
            assert_eq!(
                descriptor.interpretations[1].symbol().symbol().name(),
                "Free"
            );
            descriptor.interpretations.swap(0, 1);
        }
    }
    let EffectExprKind::Operation(EffectOperation::SourceResourceScope(scope)) =
        &program.nodes[index].kind
    else {
        unreachable!()
    };
    assert!(Arc::ptr_eq(scope.original(), &template));
    // Whole Core is the required rejecting boundary. A claimed request row need
    // not be rejected by scope-only authentication; never assert that phase.
}

/// Changes first H on the actual canonical primitive instantiation, not a
/// neighboring QueryBytes request. The immutable original and all S/V actuals,
/// copied node types, rows, operand, application and correspondence maps remain.
pub(crate) fn mutate_primitive_first_host(program: &mut UnvalidatedEffectProgram, local: u32) {
    assert!((11..=14).contains(&local));
    let (index, scope) = program.nodes.iter().enumerate().find_map(|(index, node)| {
        match &node.kind {
            EffectExprKind::Operation(EffectOperation::SourceResourceScope(scope))
                if matches!(scope.header().codec.report, SourceResourceReportCodec::CheckedScope { .. }) => Some((index, scope)),
            _ => None,
        }
    }).expect("actual checked resource scope");
    scope.authenticate(NodeId::new(program.arena, u32::try_from(index).unwrap()),
        program, &mut TypeWorkBudget::default()).expect("canonical scope before first-H mutation");
    let template = Arc::clone(scope.original());
    let mut application = None;
    scope.visit_byte_calls(|call, _| {
        if call.function.module().is_some_and(|module| module.is_builtin_foreign())
            && call.function.local() == local && call.apply.is_some() {
            assert!(application.replace(call.application).is_none(), "one genuine primitive application");
        }
        Ok(())
    }, &mut TypeWorkBudget::default()).unwrap();
    let application = application.expect("flow-proved copied canonical primitive type application");
    let stored = &mut program.nodes[application.index().unwrap()];
    let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::TypeApplication(node))) = &mut stored.kind else {
        panic!("actual checked primitive TypeApplication");
    };
    assert_eq!(node.arguments().len(), 2, "ordered H then complete S/V");
    assert!(matches!(node.arguments()[0], Type::Variable(_)));
    let mut work = TypeWorkBudget::default();
    let mut arguments = node.arguments().iter().map(|ty| {
        crate::types::clone_type_with_budget(ty, &mut work).unwrap()
    }).collect::<Vec<_>>();
    let old = std::mem::replace(&mut arguments[0], Type::Int);
    crate::types::discard_type_iteratively(old);
    let rows = node.row_arguments().iter().map(|row| {
        crate::types::clone_effect_row_with_budget(row, &mut work).unwrap()
    }).collect::<Vec<_>>();
    *node = crate::core::type_ops::TypeApplicationNode::new_with_row_arguments(node.function(), arguments, rows);
    let EffectExprKind::Operation(EffectOperation::SourceResourceScope(scope)) = &program.nodes[index].kind else {
        unreachable!()
    };
    assert!(Arc::ptr_eq(scope.original(), &template));
}
