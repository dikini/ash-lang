use super::*;
use crate::module::ModuleId;
use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};

fn instance(ty: Type) -> EffectInstance {
    EffectInstance::new(EffectId::new(ModuleId::new(0), 0), Box::new([ty]))
}

fn hash(value: &impl Hash) -> u64 {
    let mut hasher = DefaultHasher::new();
    value.hash(&mut hasher);
    hasher.finish()
}

fn member(index: u8) -> EffectInstance {
    // Fresh raw constructors are intentional: structural Clone normalizes an
    // empty EffectfulFunction and would erase the counterexample representation.
    instance(match index {
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
        _ => panic!("exact function representation fixture"),
    })
}

#[test]
fn effect_row_function_representations_are_unordered_and_idempotent() {
    let a = member(0);
    let b = member(1);
    let c = member(2);
    let empty_a = member(3);
    assert!(matches!(
        &a.arguments()[0],
        KindedArgument::TypeArg(Type::Function(_, _))
    ));
    assert!(
        matches!(&b.arguments()[0], KindedArgument::TypeArg(Type::EffectfulFunction(_, computation)) if !computation.effects().is_empty())
    );
    assert!(
        matches!(&c.arguments()[0], KindedArgument::TypeArg(Type::EffectfulFunction(domain, computation)) if matches!(domain.as_ref(), Type::Bool) && computation.effects().is_empty())
    );
    assert!(
        matches!(&empty_a.arguments()[0], KindedArgument::TypeArg(Type::EffectfulFunction(_, computation)) if computation.effects().is_empty())
    );
    // Establish existing equality/hash support on the ACTUAL raw variants.
    assert_eq!(a, empty_a);
    assert_eq!(hash(&a), hash(&empty_a));
    let (KindedArgument::TypeArg(pure), KindedArgument::TypeArg(empty)) =
        (&a.arguments()[0], &empty_a.arguments()[0])
    else {
        panic!("genuine Type arguments");
    };
    assert_eq!(pure, empty);
    assert_eq!(hash(pure), hash(empty));

    assert!(
        matches!(&c.arguments()[0], KindedArgument::TypeArg(Type::EffectfulFunction(_, computation)) if computation.effects().is_empty())
    );
    let expected = EffectRow::closed(Box::new([a, b, c]));
    assert_eq!(expected.known().len(), 3);
    for order in [
        [0, 1, 2],
        [0, 2, 1],
        [1, 0, 2],
        [1, 2, 0],
        [2, 0, 1],
        [2, 1, 0],
    ] {
        let row = EffectRow::closed(order.map(member).into());
        assert_eq!(row, expected, "source permutation {order:?}");
        assert_eq!(hash(&row), hash(&expected));
        // Consume the exact raw members rather than cloning/normalizing them.
        let (known, tail) = row.into_parts();
        assert!(tail.is_none());
        assert_eq!(
            EffectRow::closed(known),
            expected,
            "normalizing twice {order:?}"
        );
    }
    for order in [[0, 2, 1, 0], [3, 2, 1, 0], [0, 1, 2, 3]] {
        let row = EffectRow::closed(order.map(member).into());
        assert_eq!(row.known().len(), 3, "exact duplicate must be coalesced");
        assert_eq!(row, expected);
        assert_eq!(hash(&row), hash(&expected));
    }
}

fn function_type(index: u8) -> Type {
    match index {
        0..=3 => {
            let (_, arguments) = member(index).into_parts();
            let KindedArgument::TypeArg(ty) = arguments.into_vec().pop().unwrap() else {
                panic!("function fixture Type argument");
            };
            ty
        }
        4 => Type::function(Type::Unit, Type::Bool),
        5 => Type::EffectfulFunction(
            Box::new(Type::Unit),
            Box::new(ComputationType::new(
                Type::Int,
                EffectRow::singleton(EffectInstance::new(
                    EffectId::new(ModuleId::new(0), 9),
                    Box::new([]),
                )),
            )),
        ),
        6 => Type::EffectfulFunction(
            Box::new(Type::Unit),
            Box::new(ComputationType::new(
                Type::Unit,
                EffectRow::singleton(EffectInstance::new(
                    EffectId::new(ModuleId::new(0), 9),
                    Box::new([]),
                )),
            )),
        ),
        7 | 8 => Type::EffectfulFunction(
            Box::new(Type::Unit),
            Box::new(ComputationType::new(
                Type::Unit,
                if index == 7 {
                    EffectRow::open(
                        EffectRowVariable::rigid(TypeVariableId::new(0)),
                        Box::new([]),
                    )
                } else {
                    EffectRow::singleton(EffectInstance::new(
                        EffectId::new(ModuleId::new(0), 10),
                        Box::new([]),
                    ))
                },
            )),
        ),
        _ => panic!("bounded function fixture"),
    }
}

#[test]
fn function_row_comparator_obeys_semantic_equality_and_order_laws() {
    let compare = |a: &Type, b: &Type| {
        compare_types_with_charge(a, b, &mut TypeWorkBudget::default(), &mut allocation_error)
            .unwrap()
    };
    for left in 0..9 {
        for right in 0..9 {
            let a = function_type(left);
            let b = function_type(right);
            let ordering = compare(&a, &b);
            assert_eq!(ordering == Ordering::Equal, same_type(&a, &b));
            assert_eq!(ordering.reverse(), compare(&b, &a));
            if ordering == Ordering::Equal {
                assert_eq!(hash(&a), hash(&b));
            }
            for third in 0..9 {
                let c = function_type(third);
                if ordering == Ordering::Less && compare(&b, &c) == Ordering::Less {
                    assert_eq!(compare(&a, &c), Ordering::Less);
                }
            }
        }
    }
    for (left, right) in [(0, 6), (6, 0), (0, 7), (7, 0), (6, 8), (8, 6)] {
        let a = function_type(left);
        let b = function_type(right);
        assert_ne!(compare(&a, &b), Ordering::Equal);
        assert_eq!(compare(&a, &b).reverse(), compare(&b, &a));
    }
    // A latent-row distinction cannot decide before the result value.
    assert_eq!(
        compare(&function_type(4), &function_type(5)),
        Ordering::Greater
    );
}

#[test]
fn function_row_comparator_preserves_full_kinded_vectors_and_tails() {
    let row = |tail, absent| {
        EffectRow::with_tail(
            Box::new([]),
            EffectRowVariable::rigid(TypeVariableId::new(tail)),
            Box::new([EffectInstance::new(
                EffectId::new(ModuleId::new(0), absent),
                Box::new([]),
            )]),
        )
    };
    let full = |which| {
        let arguments: Box<[KindedArgument]> = match which {
            0 => Box::new([
                KindedArgument::TypeArg(function_type(0)),
                KindedArgument::RowArg(row(0, 7)),
            ]),
            1 => Box::new([
                KindedArgument::TypeArg(function_type(3)),
                KindedArgument::RowArg(row(0, 7)),
            ]),
            2 => Box::new([
                KindedArgument::TypeArg(function_type(0)),
                KindedArgument::RowArg(row(1, 7)),
            ]),
            3 => Box::new([
                KindedArgument::TypeArg(function_type(0)),
                KindedArgument::RowArg(row(0, 8)),
            ]),
            4 => Box::new([
                KindedArgument::RowArg(row(0, 7)),
                KindedArgument::TypeArg(function_type(0)),
            ]),
            _ => panic!("exact full-kind fixture"),
        };
        EffectInstance::new_kinded(EffectId::new(ModuleId::new(0), 0), arguments)
    };
    let expected = EffectRow::closed([0, 2, 3, 4].map(full).into());
    for order in [[0, 1, 2, 3, 4], [4, 3, 2, 1, 0], [2, 0, 4, 1, 3]] {
        let actual = EffectRow::closed(order.map(full).into());
        assert_eq!(actual.known().len(), 4);
        assert_eq!(actual, expected);
        assert_eq!(hash(&actual), hash(&expected));
    }
}

#[test]
fn function_row_comparator_keeps_paid_boundaries_storage_and_deep_iteration() {
    for (left, right, expected) in [
        (4, 5, Ordering::Greater),
        (0, 6, Ordering::Less),
        (6, 0, Ordering::Greater),
    ] {
        let compare = |work: &mut TypeWorkBudget| {
            compare_types_with_charge(
                &function_type(left),
                &function_type(right),
                work,
                &mut allocation_error,
            )
        };
        let mut measured = TypeWorkBudget::default();
        assert_eq!(compare(&mut measured), Ok(expected));
        let cost = measured.used();
        for cut in 0..cost {
            assert_eq!(compare(&mut TypeWorkBudget::with_limit(cut)), Err(()));
        }
        for prefix in [0, 7] {
            for _ in 0..2 {
                let mut work = TypeWorkBudget::with_limit(prefix + cost);
                work.charge(prefix).unwrap();
                assert_eq!(compare(&mut work), Ok(expected));
                assert_eq!(work.used(), prefix + cost);
                assert_eq!(compare(&mut work), Err(()));
                assert_eq!(work.used(), prefix + cost);
            }
        }
    }
    for skip in [0, 1] {
        let a = function_type(4);
        let b = function_type(5);
        let _fault = row_reservation_fault::fail(RowReservationSite::ComparisonWork, skip);
        let mut work = TypeWorkBudget::default();
        assert_eq!(
            compare_types_with_charge(&a, &b, &mut work, &mut allocation_error),
            Err(())
        );
        assert_eq!(row_reservation_fault::hits(), skip + 1);
        assert!(work.used() > 0);
    }
    std::thread::Builder::new()
        .stack_size(64 * 1024)
        .spawn(|| {
            let a = IterativeTypeOwner::new(Type::apply_arguments(
                function_type(0),
                vec![Type::Unit; 1024],
            ));
            let b = IterativeTypeOwner::new(Type::apply_arguments(
                function_type(3),
                vec![Type::Unit; 1024],
            ));
            assert_eq!(
                compare_types_with_charge(
                    &a,
                    &b,
                    &mut TypeWorkBudget::with_limit(64),
                    &mut allocation_error
                ),
                Err(())
            );
            assert_eq!(
                compare_types_with_charge(
                    &a,
                    &b,
                    &mut TypeWorkBudget::default(),
                    &mut allocation_error
                ),
                Ok(Ordering::Equal)
            );
        })
        .unwrap()
        .join()
        .unwrap();
}
