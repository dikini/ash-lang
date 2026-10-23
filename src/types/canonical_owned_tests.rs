use super::*;
use crate::module::ModuleId;

fn member(type_local: u32, row_local: u32) -> EffectInstance {
    EffectInstance::new_kinded(
        EffectId::new(ModuleId::new(0), 0),
        Box::new([
            KindedArgument::TypeArg(Type::Tuple(Box::new([
                Type::Nominal(NominalTypeId::new(ModuleId::new(0), type_local)),
                Type::Bool,
            ]))),
            KindedArgument::RowArg(EffectRow::with_tail(
                Box::new([EffectInstance::new(
                    EffectId::new(ModuleId::new(0), 7),
                    Box::new([Type::String]),
                )]),
                EffectRowVariable::rigid(TypeVariableId::new(row_local)),
                Box::new([EffectInstance::new(
                    EffectId::new(ModuleId::new(0), 8),
                    Box::new([Type::Int]),
                )]),
            )),
        ]),
    )
}

fn canonical() -> Vec<EffectInstance> {
    vec![member(0, 0), member(1, 0), member(1, 1)]
}

fn unordered() -> Vec<EffectInstance> {
    vec![member(1, 1), member(0, 0), member(1, 0), member(1, 0)]
}

fn run(input: Vec<EffectInstance>, work: &mut TypeWorkBudget) -> Result<Vec<EffectInstance>, ()> {
    canonical_instances_with_budget(input, work, &mut allocation_error)
}

// The unchanged insertion algorithm is the behavioral reference, including
// which original representation survives a semantically equal duplicate.
fn insertion_reference(
    input: Vec<EffectInstance>,
    work: &mut TypeWorkBudget,
) -> Result<Vec<EffectInstance>, ()> {
    let mut result = Vec::new();
    for instance in input {
        let mut position = 0;
        let mut duplicate = false;
        while position < result.len() {
            match compare_effect_instances_with_charge(
                &result[position],
                &instance,
                work,
                &mut allocation_error,
            )? {
                Ordering::Less => position += 1,
                Ordering::Equal => {
                    duplicate = true;
                    break;
                }
                Ordering::Greater => break,
            }
        }
        if duplicate {
            continue;
        }
        work.charge(1)?;
        reserve_row(&mut result, 1, RowReservationSite::CanonicalMembers)
            .map_err(|_| allocation_error(work))?;
        result.insert(position, instance);
    }
    Ok(result)
}

fn raw_function(index: u8) -> EffectInstance {
    let ty = match index {
        0 => Type::function(Type::Unit, Type::Unit),
        1 => Type::EffectfulFunction(
            Box::new(Type::Int),
            Box::new(ComputationType::new(
                Type::Unit,
                EffectRow::singleton(EffectInstance::new(
                    EffectId::new(ModuleId::new(0), 9),
                    Box::new([]),
                )),
            )),
        ),
        2 => Type::EffectfulFunction(
            Box::new(Type::Bool),
            Box::new(ComputationType::pure(Type::Unit)),
        ),
        3 => Type::EffectfulFunction(
            Box::new(Type::Unit),
            Box::new(ComputationType::pure(Type::Unit)),
        ),
        _ => panic!("exact raw function fixture"),
    };
    EffectInstance::new(EffectId::new(ModuleId::new(0), 0), Box::new([ty]))
}

fn representation(input: &[EffectInstance]) -> Vec<u8> {
    input
        .iter()
        .map(|instance| match &instance.arguments()[0] {
            KindedArgument::TypeArg(Type::Function(_, _)) => 0,
            KindedArgument::TypeArg(Type::EffectfulFunction(_, computation))
                if computation.effects().is_empty() =>
            {
                1
            }
            KindedArgument::TypeArg(Type::EffectfulFunction(_, _)) => 2,
            _ => panic!("raw function result"),
        })
        .collect()
}

#[test]
fn canonical_owned_members_match_repaired_function_laws_and_reference() {
    for order in [
        vec![0, 1, 2],
        vec![0, 2, 1],
        vec![1, 0, 2],
        vec![1, 2, 0],
        vec![2, 0, 1],
        vec![2, 1, 0],
        vec![0, 2, 1, 0],
        vec![3, 2, 1, 0],
        vec![0, 1, 2, 3],
        vec![0, 3],
        vec![3, 0],
    ] {
        // Construct each use afresh: Clone would normalize the empty variant.
        let input = order.iter().copied().map(raw_function).collect::<Vec<_>>();
        for (index, instance) in order.iter().zip(&input) {
            if *index == 2 || *index == 3 {
                assert!(
                    matches!(&instance.arguments()[0], KindedArgument::TypeArg(Type::EffectfulFunction(_, computation)) if computation.effects().is_empty())
                );
            }
        }
        let expected = insertion_reference(
            order.iter().copied().map(raw_function).collect(),
            &mut TypeWorkBudget::default(),
        )
        .unwrap();
        let actual = run(input, &mut TypeWorkBudget::default()).unwrap();
        assert_eq!(actual, expected);
        assert_eq!(representation(&actual), representation(&expected));
        assert_eq!(actual.len(), if order.len() == 2 { 1 } else { 3 });
        assert_eq!(run(actual, &mut TypeWorkBudget::default()), Ok(expected));
    }
}

#[test]
fn canonical_owned_members_reuse_exact_allocation_and_full_kinded_order() {
    let mut reference_work = TypeWorkBudget::default();
    let expected = insertion_reference(canonical(), &mut reference_work).unwrap();
    let mut input = Vec::with_capacity(8);
    input.extend(canonical());
    let pointer = input.as_ptr();
    let capacity = input.capacity();
    let mut work = TypeWorkBudget::default();
    let result = {
        let _fault = row_reservation_fault::fail(RowReservationSite::CanonicalMembers, 0);
        let result = run(input, &mut work).unwrap();
        assert_eq!(row_reservation_fault::hits(), 0);
        result
    };
    assert_eq!(result, expected);
    assert_eq!(result.as_ptr(), pointer);
    assert_eq!(result.capacity(), capacity);
    // Identical comparisons; only the second vector's three stored slots vanish.
    assert_eq!(reference_work.used(), work.used() + result.len());
    let mut fallback_work = TypeWorkBudget::default();
    let fallback = run(unordered(), &mut fallback_work).unwrap();
    let mut old_work = TypeWorkBudget::default();
    assert_eq!(
        fallback,
        insertion_reference(unordered(), &mut old_work).unwrap()
    );
    assert!(
        fallback_work.used() > old_work.used(),
        "failed precheck remains paid"
    );
    for input in [Vec::new(), vec![member(1, 1)]] {
        let pointer = input.as_ptr();
        let result = run(input, &mut TypeWorkBudget::with_limit(0)).unwrap();
        assert_eq!(result.as_ptr(), pointer);
    }
}

#[test]
fn canonical_owned_members_preserve_work_storage_and_deep_refusals() {
    for make in [canonical, unordered] {
        let mut measured = TypeWorkBudget::default();
        let expected = run(make(), &mut measured).unwrap();
        let cost = measured.used();
        assert!(cost > 0);
        for cut in 0..cost {
            let mut work = TypeWorkBudget::with_limit(cut);
            assert_eq!(run(make(), &mut work), Err(()));
            assert!(work.used() <= cut);
        }
        for prefix in [0, 7] {
            for _ in 0..2 {
                let mut work = TypeWorkBudget::with_limit(prefix + cost);
                work.charge(prefix).unwrap();
                assert_eq!(run(make(), &mut work), Ok(expected.clone()));
                assert_eq!(work.used(), prefix + cost);
                assert_eq!(run(make(), &mut work), Err(()));
                assert_eq!(work.used(), prefix + cost);
            }
        }
    }
    for (site, input) in [
        (RowReservationSite::ComparisonWork, canonical()),
        (RowReservationSite::CanonicalMembers, unordered()),
    ] {
        let _fault = row_reservation_fault::fail(site, 0);
        let mut work = TypeWorkBudget::default();
        assert_eq!(run(input, &mut work), Err(()));
        assert!(row_reservation_fault::hits() > 0);
        assert!(work.used() > 0);
    }
    let deep = || {
        (0..2)
            .map(|local| {
                EffectInstance::new(
                    EffectId::new(ModuleId::new(0), 0),
                    Box::new([Type::apply_arguments(
                        Type::Nominal(NominalTypeId::new(ModuleId::new(0), local)),
                        vec![Type::Unit; 256],
                    )]),
                )
            })
            .collect::<Vec<_>>()
    };
    assert_eq!(run(deep(), &mut TypeWorkBudget::with_limit(64)), Err(()));
    let input = deep();
    let pointer = input.as_ptr();
    assert_eq!(
        run(input, &mut TypeWorkBudget::default()).unwrap().as_ptr(),
        pointer
    );
}
