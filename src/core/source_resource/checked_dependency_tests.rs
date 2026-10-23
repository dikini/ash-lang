//! Mutate real copied dependency descriptors after independent admission.
use super::*;

fn refused<T>(result: Result<T, ValidationError>) -> ValidationError {
    match result {
        Err(error) => error,
        Ok(_) => panic!("hostile or insufficient-budget Core must refuse"),
    }
}

pub(crate) fn assert_core_controls(
    core: &crate::core::ValidatedEffectProgram,
    provenance: &[(crate::module::ModuleId, Arc<crate::source::SourceFile>)],
    donor_required: bool,
) {
    let sources = provenance
        .iter()
        .map(|(_, s)| s.as_ref())
        .collect::<Vec<_>>();
    let modules = provenance
        .iter()
        .map(|(m, s)| (*m, s.id()))
        .collect::<Vec<_>>();
    let fresh = || crate::core::transform::identity_effect_traversal(core).unwrap();
    let mut measured = TypeWorkBudget::default();
    crate::core::validate::validate_effect_modules_with_work(
        fresh(),
        &sources,
        &modules,
        &mut measured,
    )
    .unwrap();
    let cost = measured.used();
    assert!(cost > 0);
    for prefix in [0, 7] {
        let mut short = TypeWorkBudget::with_limit(prefix + cost - 1);
        short.charge(prefix).unwrap();
        assert_eq!(
            refused(crate::core::validate::validate_effect_modules_with_work(
                fresh(),
                &sources,
                &modules,
                &mut short
            ))
            .reason(),
            ValidationReason::Resource
        );
        assert!(short.used() > prefix);
        for _ in 0..2 {
            let mut exact = TypeWorkBudget::with_limit(prefix + cost);
            exact.charge(prefix).unwrap();
            crate::core::validate::validate_effect_modules_with_work(
                fresh(),
                &sources,
                &modules,
                &mut exact,
            )
            .unwrap();
            assert_eq!(exact.used(), prefix + cost);
            assert_eq!(
                refused(crate::core::validate::validate_effect_modules_with_work(
                    fresh(),
                    &sources,
                    &modules,
                    &mut exact
                ))
                .reason(),
                ValidationReason::Resource
            );
        }
    }
    let canonical = fresh();
    let child = canonical
        .nodes
        .iter()
        .find_map(|n| match &n.kind {
            EffectExprKind::Operation(EffectOperation::SourceResourceScope(s))
                if !s.header().dependencies.is_empty() =>
            {
                Some(s)
            }
            _ => None,
        })
        .unwrap();
    let parent_actual = match &child.arguments()[child
        .header()
        .original
        .parameters
        .iter()
        .position(|p| p.id == child.header().dependencies[0])
        .unwrap()]
    {
        KindedArgument::TypeArg(Type::Variable(id)) => *id,
        _ => panic!("actual enclosing owner identity"),
    };
    let donor = canonical.nodes.iter().find_map(|n| match &n.kind {
        EffectExprKind::Operation(EffectOperation::SourceResourceScope(s))
            if s.header().original.spelling == "Parent" && s.identity() != parent_actual =>
        {
            Some(s.identity())
        }
        _ => None,
    });
    assert_eq!(donor.is_some(), donor_required);
    let row_positions = child
        .arguments()
        .iter()
        .enumerate()
        .filter_map(|(i, a)| match a {
            KindedArgument::RowArg(row) if !row.known().is_empty() => Some(i),
            _ => None,
        })
        .collect::<Vec<_>>();
    if !donor_required {
        assert_eq!(row_positions.len(), 2);
    }
    let cases = 6 + usize::from(donor.is_some()) + 2 * usize::from(!row_positions.is_empty());
    for change in 0..cases {
        let mut forged = fresh();
        let index = forged.nodes.iter().position(|n| matches!(&n.kind, EffectExprKind::Operation(EffectOperation::SourceResourceScope(s)) if !s.header().dependencies.is_empty())).unwrap();
        let id = NodeId::new(forged.arena, u32::try_from(index).unwrap());
        let EffectExprKind::Operation(EffectOperation::SourceResourceScope(scope)) =
            &mut forged.nodes[index].kind
        else {
            unreachable!()
        };
        let dependency = scope.header().dependencies[0];
        let position = scope
            .header()
            .original
            .parameters
            .iter()
            .position(|p| p.id == dependency)
            .unwrap();
        let host = scope.header().original.host.unwrap().position;
        let identity = scope.identity();
        let row_ids = row_positions
            .iter()
            .map(|i| scope.header().original.parameters[*i].id)
            .collect::<Vec<_>>();
        let descriptor = Arc::get_mut(&mut scope.descriptor).unwrap();
        match change {
            0 => {
                let old = std::mem::replace(
                    &mut descriptor.arguments[position],
                    KindedArgument::TypeArg(Type::Variable(identity)),
                );
                crate::types::discard_kinded_argument_iteratively(old);
            }
            1..=3 => crate::types::replace_type_iteratively(
                descriptor.copies[change - 1]
                    .types
                    .get_mut(&dependency)
                    .unwrap(),
                Type::Variable(identity),
            ),
            4 => {
                let old = std::mem::replace(
                    &mut descriptor.arguments[host],
                    KindedArgument::TypeArg(Type::Variable(identity)),
                );
                crate::types::discard_kinded_argument_iteratively(old);
            }
            5 => descriptor.arguments.swap(host, position),
            6 if donor.is_some() => {
                let old = std::mem::replace(
                    &mut descriptor.arguments[position],
                    KindedArgument::TypeArg(Type::Variable(donor.unwrap())),
                );
                crate::types::discard_kinded_argument_iteratively(old);
            }
            _ => {
                let row_case = change - 6 - usize::from(donor.is_some());
                let row_position = row_positions[row_case];
                if row_case == 0 {
                    *descriptor.copies[0].rows.get_mut(&row_ids[0]).unwrap() =
                        crate::types::EffectRow::empty();
                } else {
                    let old = std::mem::replace(
                        &mut descriptor.arguments[row_position],
                        KindedArgument::RowArg(crate::types::EffectRow::empty()),
                    );
                    crate::types::discard_kinded_argument_iteratively(old);
                }
            }
        }
        let EffectExprKind::Operation(EffectOperation::SourceResourceScope(scope)) =
            &forged.nodes[index].kind
        else {
            unreachable!()
        };
        assert_eq!(
            scope
                .authenticate(id, &forged, &mut TypeWorkBudget::default())
                .unwrap_err()
                .reason(),
            ValidationReason::Registry
        );
        let error = refused(crate::core::validate::validate_effect_modules_family(
            forged, &sources, &modules,
        ));
        assert_ne!(error.reason(), ValidationReason::Resource);
    }
    println!(
        "checked dependency Core work={cost}, hostile cases={cases}; exact/prefix/short/spent/two fresh"
    );
}
