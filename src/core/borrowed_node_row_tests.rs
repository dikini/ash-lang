//! A builder-local row loan compares data; it conveys no Core admission result.
use super::*;
use crate::{
    core::effect::EffectOperationFamily,
    source::{ByteRange, SourceFile},
    types::{ComputationType, EffectId, EffectInstance, KindedArgument, RowReservationSite},
};

type Builder = CoreBuilder<EffectOperationFamily>;

fn row(raw_empty: bool, depth: usize, donor: bool) -> EffectRow {
    let module = ModuleId::new(if donor { 702 } else { 701 });
    let mut value = Type::Unit;
    for _ in 0..depth {
        value = Type::Function(Box::new(Type::Unit), Box::new(value));
    }
    let function = if raw_empty {
        Type::EffectfulFunction(
            Box::new(Type::Unit),
            Box::new(ComputationType::new(value, EffectRow::empty())),
        )
    } else {
        Type::Function(Box::new(Type::Unit), Box::new(value))
    };
    let member = EffectInstance::new_kinded(
        EffectId::new(module, 7),
        vec![
            KindedArgument::TypeArg(function),
            KindedArgument::RowArg(EffectRow::singleton(EffectInstance::new(
                EffectId::new(module, 8),
                Box::new([]),
            ))),
        ]
        .into_boxed_slice(),
    );
    EffectRow::with_tail(
        Box::new([member]),
        EffectRowVariable::Rigid(TypeVariableId::resolved(module, 9)),
        Box::new([EffectInstance::new(EffectId::new(module, 10), Box::new([]))]),
    )
}

fn fixture(effects: EffectRow) -> (Builder, NodeId) {
    let file = SourceFile::new("borrowed-node-row.ash", "()").unwrap();
    let origin = Origin::Source(file.span(ByteRange::new(0, 2).unwrap()).unwrap());
    let mut builder = Builder::with_effect_registry(Arc::new(ResolvedRegistry::default()));
    let value = builder.unit(Type::Unit, origin.clone()).unwrap();
    // Explicit-row assembly pays full payload admission; this is a builder data
    // control, not a claim that an unchecked application passed final validation.
    let node = builder
        .application_with_effects(
            ApplicationNode::new(value, value),
            Type::Unit,
            effects,
            origin,
        )
        .unwrap();
    (builder, node)
}

fn reference(
    builder: &Builder,
    node: NodeId,
    expected: &EffectRow,
    work: &mut TypeWorkBudget,
) -> Result<Result<bool, ()>, BuildError> {
    let owned = builder.clone_node_effects_with_budget(node, work)?;
    // EffectRow's Drop disposes full Type/Row argument graphs iteratively.
    Ok(crate::types::same_effect_rows_with_budget(
        &owned, expected, work,
    ))
}

#[test]
fn borrowed_node_rows_match_owned_reference_full_kinds_and_raw_empty_functions() {
    for raw in [false, true] {
        let (builder, node) = fixture(row(raw, 3, false));
        let expected = row(false, 3, false);
        let mut old_work = TypeWorkBudget::default();
        let mut work = TypeWorkBudget::default();
        assert_eq!(
            reference(&builder, node, &expected, &mut old_work),
            Ok(Ok(true))
        );
        assert_eq!(
            builder.node_effects_match_with_budget(node, &expected, &mut work),
            Ok(Ok(true))
        );
        assert!(
            work.used() < old_work.used(),
            "only the throwaway clone is removed"
        );
        let mut clone_work = TypeWorkBudget::default();
        let owned = builder
            .clone_node_effects_with_budget(node, &mut clone_work)
            .unwrap();
        assert_eq!(owned.known().len(), 1);
        assert_eq!(owned.tail().unwrap().lacks().len(), 2);
        let stored =
            EffectOperationFamily::effect_row(&builder.nodes[node.value() as usize].effects);
        assert!(
            matches!(
                &stored.known()[0].arguments()[0],
                KindedArgument::TypeArg(Type::EffectfulFunction(_, _))
            ) == raw
        );
        for mismatch in [EffectRow::empty(), row(false, 3, true)] {
            assert_eq!(
                reference(&builder, node, &mismatch, &mut TypeWorkBudget::default()),
                Ok(Ok(false))
            );
            assert_eq!(
                builder.node_effects_match_with_budget(
                    node,
                    &mismatch,
                    &mut TypeWorkBudget::default()
                ),
                Ok(Ok(false))
            );
        }
        // A same-owner, differently tagged complete actual must still disagree.
        let wrong_tag = EffectRow::with_tail(
            Box::new([EffectInstance::new_kinded(
                EffectId::new(ModuleId::new(701), 7),
                vec![
                    KindedArgument::RowArg(EffectRow::empty()),
                    KindedArgument::TypeArg(Type::Unit),
                ]
                .into_boxed_slice(),
            )]),
            EffectRowVariable::Rigid(TypeVariableId::resolved(ModuleId::new(701), 9)),
            Box::new([EffectInstance::new(
                EffectId::new(ModuleId::new(701), 10),
                Box::new([]),
            )]),
        );
        assert_eq!(
            wrong_tag.tail().unwrap().variable(),
            expected.tail().unwrap().variable()
        );
        assert_eq!(wrong_tag.known().len(), expected.known().len());
        assert_eq!(
            wrong_tag.tail().unwrap().lacks().len(),
            expected.tail().unwrap().lacks().len()
        );
        for (actual, original) in wrong_tag
            .tail()
            .unwrap()
            .lacks()
            .iter()
            .zip(expected.tail().unwrap().lacks())
        {
            assert_eq!(actual.effect(), original.effect());
        }
        assert_eq!(&wrong_tag.tail().unwrap().lacks()[0], &wrong_tag.known()[0]);
        assert!(matches!(
            &wrong_tag.known()[0].arguments()[0],
            KindedArgument::RowArg(_)
        ));
        assert!(matches!(
            &expected.known()[0].arguments()[0],
            KindedArgument::TypeArg(_)
        ));
        assert_eq!(
            reference(&builder, node, &wrong_tag, &mut TypeWorkBudget::default()),
            Ok(Ok(false))
        );
        assert_eq!(
            builder.node_effects_match_with_budget(
                node,
                &wrong_tag,
                &mut TypeWorkBudget::default()
            ),
            Ok(Ok(false))
        );
    }
    let (builder, node) = fixture(EffectRow::empty());
    let mut old = TypeWorkBudget::default();
    let mut work = TypeWorkBudget::default();
    assert_eq!(
        reference(&builder, node, &EffectRow::empty(), &mut old),
        Ok(Ok(true))
    );
    assert_eq!(
        builder.node_effects_match_with_budget(node, &EffectRow::empty(), &mut work),
        Ok(Ok(true))
    );
    assert_eq!(old.used(), work.used() + 1, "empty Row clone visit");
}

#[test]
fn borrowed_node_rows_keep_guard_and_comparison_errors_exact_and_retryable() {
    let expected = row(false, 2, false);
    let (builder, node) = fixture(row(false, 2, false));
    let (donor, donor_node) = fixture(EffectRow::empty());
    assert_ne!(node.arena(), donor_node.arena());
    let missing = NodeId::new(node.arena(), u32::MAX);
    for invalid in [donor_node, missing] {
        let mut work = TypeWorkBudget::default();
        assert_eq!(
            builder.node_effects_match_with_budget(invalid, &expected, &mut work),
            Err(BuildError::InvalidNodeId)
        );
        assert_eq!(work.used(), 1);
        assert_eq!(
            reference(&builder, invalid, &expected, &mut TypeWorkBudget::default()),
            Err(BuildError::InvalidNodeId)
        );
    }
    drop(donor);
    assert_eq!(
        builder.node_effects_match_with_budget(node, &expected, &mut TypeWorkBudget::with_limit(0)),
        Err(BuildError::TypeWorkExceeded)
    );
    assert_eq!(
        builder.node_effects_match_with_budget(node, &expected, &mut TypeWorkBudget::with_limit(1)),
        Ok(Err(()))
    );
    let mut measured = TypeWorkBudget::default();
    assert_eq!(
        builder.node_effects_match_with_budget(node, &expected, &mut measured),
        Ok(Ok(true))
    );
    let cost = measured.used();
    for limit in 0..cost {
        let mut work = TypeWorkBudget::with_limit(limit);
        let result = builder.node_effects_match_with_budget(node, &expected, &mut work);
        assert_eq!(
            result,
            if limit == 0 {
                Err(BuildError::TypeWorkExceeded)
            } else {
                Ok(Err(()))
            }
        );
        assert!(work.used() <= limit);
    }
    for prefix in [0, 7] {
        let mut short = TypeWorkBudget::with_limit(prefix + cost - 1);
        short.charge(prefix).unwrap();
        assert_eq!(
            builder.node_effects_match_with_budget(node, &expected, &mut short),
            Ok(Err(()))
        );
        let spent = short.used();
        assert!(
            builder.node_effects_match_with_budget(node, &expected, &mut short) != Ok(Ok(true))
        );
        assert!(short.used() >= spent);
        for _ in 0..2 {
            let mut exact = TypeWorkBudget::with_limit(prefix + cost);
            exact.charge(prefix).unwrap();
            assert_eq!(
                builder.node_effects_match_with_budget(node, &expected, &mut exact),
                Ok(Ok(true))
            );
            assert_eq!(exact.used(), prefix + cost);
        }
    }
    let fault = crate::types::row_reservation_fault::fail(RowReservationSite::ComparisonWork, 0);
    assert_eq!(
        builder.node_effects_match_with_budget(node, &expected, &mut TypeWorkBudget::default()),
        Ok(Err(()))
    );
    drop(fault);
    assert_eq!(
        builder.node_effects_match_with_budget(node, &expected, &mut TypeWorkBudget::default()),
        Ok(Ok(true))
    );
}

#[test]
fn borrowed_node_rows_compare_and_drop_deep_owned_reference_on_small_stack() {
    let (builder, node) = fixture(row(true, 80, false));
    let expected = row(false, 80, false);
    std::thread::Builder::new()
        .stack_size(64 * 1024)
        .spawn(move || {
            let mut old = TypeWorkBudget::default();
            assert_eq!(reference(&builder, node, &expected, &mut old), Ok(Ok(true)));
            let mut work = TypeWorkBudget::default();
            assert_eq!(
                builder.node_effects_match_with_budget(node, &expected, &mut work),
                Ok(Ok(true))
            );
            assert!(work.used() < old.used());
            assert_eq!(
                builder.node_effects_match_with_budget(
                    node,
                    &expected,
                    &mut TypeWorkBudget::with_limit(64)
                ),
                Ok(Err(()))
            );
            drop(expected);
            drop(builder);
        })
        .unwrap()
        .join()
        .unwrap();
}
