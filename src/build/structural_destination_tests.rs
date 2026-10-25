//! Final decoder allocations protect partial conversion without transit vectors.
use super::*;

fn record(image: &mut PureImage, tag: TypeTag, children: &[u32]) -> u32 {
    let start = image.type_children.len();
    image.type_children.extend_from_slice(children);
    let slot = index(image.types.len()).unwrap();
    image.types.push(TypeRecord {
        tag,
        children: Slice::of(&image.type_children, start).unwrap(),
    });
    slot
}

fn fixture(arm: u8, depth: usize, malformed: bool, empty: bool) -> (PureImage, u32) {
    let mut image = PureImage {
        effect_dialect: true,
        ..PureImage::default()
    };
    let unit = record(&mut image, TypeTag::Unit, &[]);
    let empty_row = record(
        &mut image,
        TypeTag::Row {
            known: 0,
            tail: None,
        },
        &[],
    );
    let mut value = unit;
    for _ in 0..depth {
        value = record(&mut image, TypeTag::Function, &[unit, value]);
    }
    let raw = record(
        &mut image,
        TypeTag::EffectfulFunction,
        &[unit, value, empty_row],
    );
    let ty = record(&mut image, TypeTag::ArgumentType, &[raw]);
    let member = record(
        &mut image,
        TypeTag::Instance(EffectIdentity {
            module: 0,
            local: 19,
        }),
        &[ty],
    );
    let row = record(
        &mut image,
        TypeTag::Row {
            known: 1,
            tail: Some(TypeVariableIdentity::Resolved {
                module: 0,
                local: 23,
            }),
        },
        &[member, member],
    );
    let row_arg = record(&mut image, TypeTag::ArgumentRow, &[row]);
    let tag = match arm {
        0 => TypeTag::Instance(EffectIdentity {
            module: 0,
            local: 7,
        }),
        1 => TypeTag::Resource(ResourceIdentity {
            module: 0,
            local: 8,
        }),
        2 => TypeTag::Application,
        3 => TypeTag::Tuple,
        _ => unreachable!(),
    };
    let nominal = record(
        &mut image,
        TypeTag::Nominal(NominalId {
            module: 0,
            local: 9,
        }),
        &[],
    );
    let mut children = if arm == 3 {
        vec![raw, unit]
    } else if arm == 2 {
        vec![nominal, raw]
    } else {
        vec![ty, row_arg]
    };
    if empty {
        children.clear();
    }
    if malformed {
        children.push(if arm == 3 { empty_row } else { unit });
    }
    let root = record(&mut image, tag, &children);
    (image, root)
}

fn decoder<'a>(image: &'a PureImage, work: &'a mut TypeWorkBudget) -> Decoder<'a> {
    Decoder {
        image,
        expected_fact_prefixes: None,
        sources: CoordinateStorage::Owned(Vec::new()),
        modules: CoordinateStorage::Owned(vec![ModuleId::new(601)]),
        source_declaration_catalogs: HashMap::new(),
        decoded_types: HashMap::new(),
        decoded_rows: HashMap::new(),
        work,
    }
}

fn arguments(value: &StructuralOwner) -> &[crate::types::KindedArgument] {
    match value {
        StructuralOwner::Instance(instance) => {
            assert_eq!(
                instance.effect(),
                crate::types::EffectId::new(ModuleId::new(601), 7)
            );
            instance.arguments()
        }
        StructuralOwner::Type(ty) => match &**ty {
            Type::ResourceApply(id, args) => {
                assert_eq!(
                    *id,
                    crate::types::ResourceDefinitionId::new(ModuleId::new(601), 8)
                );
                args
            }
            _ => panic!("expected exact kinded application"),
        },
        _ => panic!("expected typed final owner"),
    }
}

fn assert_value(value: &StructuralOwner, arm: u8) {
    if arm == 2 {
        let StructuralOwner::Type(ty) = value else {
            panic!("application owner");
        };
        let Type::Application(function, argument) = &**ty else {
            panic!("application shape");
        };
        assert_eq!(
            function.as_ref(),
            &Type::Nominal(NominalTypeId::new(ModuleId::new(601), 9))
        );
        assert!(
            matches!(argument.as_ref(), Type::EffectfulFunction(_, computation) if computation.effects().is_empty())
        );
        return;
    }

    if arm == 3 {
        let StructuralOwner::Type(ty) = value else {
            panic!("tuple owner")
        };
        let Type::Tuple(fields) = &**ty else {
            panic!("tuple shape")
        };
        assert_eq!(fields.len(), 2);
        assert!(
            matches!(&fields[0], Type::EffectfulFunction(_, computation) if computation.effects().is_empty())
        );
        assert!(matches!(&fields[1], Type::Unit));
        return;
    }
    let args = arguments(value);
    assert_eq!(args.len(), 2);
    assert!(
        matches!(&args[0], crate::types::KindedArgument::TypeArg(Type::EffectfulFunction(_, computation)) if computation.effects().is_empty())
    );
    let crate::types::KindedArgument::RowArg(row) = &args[1] else {
        panic!("full Row actual")
    };
    assert_eq!(row.known().len(), 1);
    assert_eq!(
        row.known()[0].effect(),
        crate::types::EffectId::new(ModuleId::new(601), 19)
    );
    assert!(
        matches!(&row.known()[0].arguments()[0], crate::types::KindedArgument::TypeArg(Type::EffectfulFunction(_, computation)) if computation.effects().is_empty())
    );
    let tail = row.tail().unwrap();
    assert_eq!(
        tail.variable(),
        crate::types::EffectRowVariable::Rigid(crate::types::TypeVariableId::resolved(
            ModuleId::new(601),
            23
        ))
    );
    assert_eq!(tail.lacks(), row.known());
}

#[test]
fn structural_destinations_preserve_full_kinds_order_and_raw_representations() {
    for arm in 0..4 {
        let (image, root) = fixture(arm, 2, false, false);
        let value = decoder(&image, &mut TypeWorkBudget::default())
            .structural(root)
            .unwrap();
        assert_value(&value, arm);
        if arm < 2 {
            let (image, root) = fixture(arm, 0, false, true);
            let value = decoder(&image, &mut TypeWorkBudget::default())
                .structural(root)
                .unwrap();
            assert!(arguments(&value).is_empty());
        }
    }
}

#[test]
fn structural_destinations_keep_exact_short_prefix_spent_and_fresh_work() {
    for arm in 0..4 {
        let (image, root) = fixture(arm, 3, false, false);
        let mut measured = TypeWorkBudget::default();
        let value = decoder(&image, &mut measured).structural(root).unwrap();
        assert_value(&value, arm);
        let cost = measured.used();
        for limit in 0..cost {
            let mut work = TypeWorkBudget::with_limit(limit);
            assert!(matches!(
                decoder(&image, &mut work).structural(root),
                Err(ImageFailure::Resource)
            ));
            assert!(work.used() <= limit);
        }
        for prefix in [0, 7] {
            let mut short = TypeWorkBudget::with_limit(prefix + cost - 1);
            short.charge(prefix).unwrap();
            assert!(matches!(
                decoder(&image, &mut short).structural(root),
                Err(ImageFailure::Resource)
            ));
            let spent = short.used();
            assert!(matches!(
                decoder(&image, &mut short).structural(root),
                Err(ImageFailure::Resource)
            ));
            assert!(short.used() >= spent);
            for _ in 0..2 {
                let mut exact = TypeWorkBudget::with_limit(prefix + cost);
                exact.charge(prefix).unwrap();
                let value = decoder(&image, &mut exact).structural(root).unwrap();
                assert_value(&value, arm);
                assert_eq!(exact.used(), prefix + cost);
            }
        }
    }
}

#[test]
fn structural_destinations_drop_malformed_later_children_and_deep_partial_values_iteratively() {
    std::thread::Builder::new()
        .stack_size(64 * 1024)
        .spawn(|| {
            for arm in 0..4 {
                let (valid, root) = fixture(arm, 80, false, false);
                let value = decoder(&valid, &mut TypeWorkBudget::default())
                    .structural(root)
                    .unwrap();
                assert_value(&value, arm);
                drop(value);
                let (invalid, root) = fixture(arm, 80, true, false);
                assert!(matches!(
                    decoder(&invalid, &mut TypeWorkBudget::default()).structural(root),
                    Err(ImageFailure::InvalidRecord)
                ));
            }
            // Direct aggregate-guard cleanup exceeds Core's independent payload
            // admission depth; it tests ownership cleanup, not expanded admission.
            let mut deep = Type::Unit;
            for _ in 0..4096 {
                deep = Type::Function(Box::new(Type::Unit), Box::new(deep));
            }
            let row = crate::types::EffectRow::closed(
                vec![crate::types::EffectInstance::new_kinded(
                    crate::types::EffectId::new(ModuleId::new(601), 19),
                    vec![crate::types::KindedArgument::TypeArg(deep)].into_boxed_slice(),
                )]
                .into_boxed_slice(),
            );
            drop(ArgumentBuffer(vec![crate::types::KindedArgument::RowArg(
                row,
            )]));
            let mut deep = Type::Unit;
            for _ in 0..4096 {
                deep = Type::Function(Box::new(Type::Unit), Box::new(deep));
            }
            drop(TypeBuffer(vec![deep]));
        })
        .unwrap()
        .join()
        .unwrap();
}
