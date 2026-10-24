//! Local inference-closure classification for partial elaboration rewrites.
//! Dialect operations remain conservative; this grants no Core admission.
use super::{
    BuildError, CoreOperationFamily, CorePattern, CorePatternKind, PureComputation, PureExprKind,
    PureValue, StoredNode, TypeAdmissionTask, scan_type_admission,
};
use crate::types::{EffectRow, EffectRowVariable, Type, TypeWorkBudget};

fn closed_type(ty: &Type, work: &mut TypeWorkBudget, allow: bool) -> Result<bool, BuildError> {
    let (inference, normalize) =
        scan_type_admission(TypeAdmissionTask::Visit(ty, 0), work, true, allow)?;
    Ok(!inference && !normalize)
}
fn closed_row(row: &EffectRow, work: &mut TypeWorkBudget, allow: bool) -> Result<bool, BuildError> {
    work.charge(1).map_err(|_| BuildError::TypeWorkExceeded)?;
    if matches!(
        row.tail().map(|tail| tail.variable()),
        Some(EffectRowVariable::Inference(_))
    ) {
        return Ok(false);
    }
    for instance in row
        .known()
        .iter()
        .chain(row.tail().into_iter().flat_map(|tail| tail.lacks()))
    {
        work.charge(1).map_err(|_| BuildError::TypeWorkExceeded)?;
        let (inference, normalize) = scan_type_admission(
            TypeAdmissionTask::Owner(instance.arguments(), 0),
            work,
            true,
            allow,
        )?;
        if inference || normalize {
            return Ok(false);
        }
    }
    Ok(true)
}
fn closed_pattern(
    pattern: &CorePattern,
    work: &mut TypeWorkBudget,
    allow: bool,
) -> Result<bool, BuildError> {
    let mut pending = Vec::new();
    work.charge(1).map_err(|_| BuildError::TypeWorkExceeded)?;
    pending
        .try_reserve(1)
        .map_err(|_| BuildError::TypeWorkExceeded)?;
    pending.push(pattern);
    while let Some(pattern) = pending.pop() {
        work.charge(1).map_err(|_| BuildError::TypeWorkExceeded)?;
        if !closed_type(&pattern.ty, work, allow)? {
            return Ok(false);
        }
        match &pattern.kind {
            CorePatternKind::Binder(binder) => {
                if !closed_type(binder.ty(), work, allow)? {
                    return Ok(false);
                }
            }
            CorePatternKind::Tuple(elements) => {
                work.charge(elements.len())
                    .map_err(|_| BuildError::TypeWorkExceeded)?;
                pending
                    .try_reserve(elements.len())
                    .map_err(|_| BuildError::TypeWorkExceeded)?;
                pending.extend(elements.iter());
            }
            CorePatternKind::Constructor {
                payload: Some(payload),
                ..
            } => {
                work.charge(1).map_err(|_| BuildError::TypeWorkExceeded)?;
                pending
                    .try_reserve(1)
                    .map_err(|_| BuildError::TypeWorkExceeded)?;
                pending.push(payload);
            }
            _ => {}
        }
    }
    Ok(true)
}
pub(super) fn fully_closed<F: CoreOperationFamily>(
    node: &StoredNode<F>,
    work: &mut TypeWorkBudget,
) -> Result<bool, BuildError> {
    work.charge(1).map_err(|_| BuildError::TypeWorkExceeded)?;
    // The initial bounded candidate retains no dialect-operation proof or metadata.
    let Some(kind) = F::pure(&node.kind) else {
        return Ok(false);
    };
    let allow = F::ALLOWS_EFFECTFUL_TYPES;
    if !closed_type(&node.ty, work, allow)?
        || !closed_row(F::effect_row(&node.effects), work, allow)?
    {
        return Ok(false);
    }
    match kind {
        PureExprKind::Value(PureValue::Function(function)) => {
            if !closed_type(function.parameter().ty(), work, allow)? {
                return Ok(false);
            }
        }
        PureExprKind::Computation(PureComputation::Bind(binding)) => {
            if !closed_type(binding.binder().ty(), work, allow)? {
                return Ok(false);
            }
        }
        PureExprKind::Computation(PureComputation::RecursiveBind(group)) => {
            for member in group.members() {
                if !closed_type(member.binder().ty(), work, allow)? {
                    return Ok(false);
                }
            }
        }
        PureExprKind::Computation(PureComputation::Match(expression)) => {
            for arm in expression.arms() {
                if !closed_pattern(arm.pattern(), work, allow)? {
                    return Ok(false);
                }
            }
        }
        PureExprKind::Computation(PureComputation::TypeApplication(application)) => {
            for ty in application.arguments() {
                if !closed_type(ty, work, allow)? {
                    return Ok(false);
                }
            }
            for row in application.row_arguments() {
                if !closed_row(row, work, allow)? {
                    return Ok(false);
                }
            }
        }
        _ => {}
    }
    Ok(true)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        core::{dialect::CoreBuilder, effect::EffectOperationFamily},
        module::ModuleId,
        resolved::ResolvedRegistry,
        source::{ByteRange, Origin, SourceFile},
        types::{EffectId, EffectInstance, InferenceVariableId, TypeVariableId},
    };
    use std::{cell::RefCell, sync::Arc};
    fn origin() -> Origin {
        let source = SourceFile::new("settled-zonk.ash", "()").unwrap();
        Origin::Source(source.span(ByteRange::new(0, 2).unwrap()).unwrap())
    }
    fn identity<F: CoreOperationFamily>(
        builder: &mut CoreBuilder<F>,
        budget: &mut TypeWorkBudget,
    ) -> Result<usize, BuildError> {
        let meter = RefCell::new(budget);
        let calls = std::cell::Cell::new(0);
        builder.zonk_types_and_rows(
            &meter,
            |ty| {
                calls.set(calls.get() + 1);
                crate::types::clone_type_with_budget(ty, &mut **meter.borrow_mut())
                    .map_err(|_| BuildError::TypeWorkExceeded)
            },
            |row| {
                crate::types::clone_effect_row_with_budget(row, &mut **meter.borrow_mut())
                    .map_err(|_| BuildError::TypeWorkExceeded)
            },
        )?;
        Ok(calls.get())
    }
    #[test]
    fn settled_zonk_retains_closed_metadata_but_generic_rewrites_stay_full() {
        let mut builder = CoreBuilder::new();
        let origin = origin();
        builder.unit(Type::Unit, origin).unwrap();
        let mut work = TypeWorkBudget::default();
        assert_eq!(identity(&mut builder, &mut work).unwrap(), 1);
        assert_eq!(identity(&mut builder, &mut work).unwrap(), 0);
        let mut visits = 0;
        builder
            .rewrite_types(|ty| {
                visits += 1;
                Ok(ty.clone())
            })
            .unwrap();
        assert_eq!(visits, 1);
        assert_eq!(identity(&mut builder, &mut work).unwrap(), 1);
        builder
            .rewrite_types_and_rows(
                None,
                |ty| {
                    visits += 1;
                    Ok(ty.clone())
                },
                |row| Ok(row.clone()),
            )
            .unwrap();
        assert_eq!(visits, 2);
        assert_eq!(identity(&mut builder, &mut work).unwrap(), 1);
    }
    #[test]
    fn settled_zonk_never_settles_a_late_type_solution() {
        let mut builder = CoreBuilder::new();
        let id = InferenceVariableId::new(7);
        let node = builder.unit(Type::Inference(id), origin()).unwrap();
        let mut work = TypeWorkBudget::default();
        assert_eq!(identity(&mut builder, &mut work).unwrap(), 1);
        assert_eq!(identity(&mut builder, &mut work).unwrap(), 1);
        {
            let meter = RefCell::new(&mut work);
            builder
                .zonk_types_and_rows(
                    &meter,
                    |ty| {
                        meter
                            .borrow_mut()
                            .charge(1)
                            .map_err(|_| BuildError::TypeWorkExceeded)?;
                        Ok(if *ty == Type::Inference(id) {
                            Type::Unit
                        } else {
                            ty.clone()
                        })
                    },
                    |row| Ok(row.clone()),
                )
                .unwrap();
        }
        assert_eq!(builder.nodes[node.index().unwrap()].ty, Type::Unit);
        assert_eq!(identity(&mut builder, &mut work).unwrap(), 0);
    }
    #[test]
    fn settled_zonk_checks_row_tails_lacks_and_type_application_metadata() {
        let id = InferenceVariableId::new(8);
        let mut work = TypeWorkBudget::default();
        let row = EffectRow::open(EffectRowVariable::inference(id), Box::new([]));
        assert!(!closed_row(&row, &mut work, true).unwrap());
        let lacks = EffectInstance::new(
            EffectId::new(ModuleId::new(0), 1),
            Box::new([Type::Inference(id)]),
        );
        let row = EffectRow::open(
            EffectRowVariable::rigid(TypeVariableId::new(2)),
            Box::new([lacks]),
        );
        assert!(!closed_row(&row, &mut work, true).unwrap());
        let mut builder = CoreBuilder::<EffectOperationFamily>::with_effect_registry(Arc::new(
            ResolvedRegistry::default(),
        ));
        let node = builder.unit(Type::Unit, origin()).unwrap();
        let applied = builder
            .type_application_with_row_arguments(node, Vec::new(), vec![row], Type::Unit, origin())
            .unwrap();
        assert!(!fully_closed(&builder.nodes[applied.index().unwrap()], &mut work).unwrap());
    }
    #[test]
    fn settled_zonk_checks_hidden_pattern_and_binder_inference() {
        let mut builder = CoreBuilder::new();
        let id = InferenceVariableId::new(9);
        let binder = builder.binder(Type::Inference(id), origin()).unwrap();
        let pattern = CorePattern::new(
            Type::Unit,
            origin(),
            CorePatternKind::Tuple(Box::new([CorePattern::new(
                Type::Unit,
                origin(),
                CorePatternKind::Binder(binder),
            )])),
        );
        assert!(!closed_pattern(&pattern, &mut TypeWorkBudget::default(), true).unwrap());
    }
    #[test]
    fn settled_zonk_invalidates_changed_rows_and_cleanup_equations() {
        let mut builder = CoreBuilder::<EffectOperationFamily>::with_effect_registry(Arc::new(
            ResolvedRegistry::default(),
        ));
        let node = builder.unit(Type::Unit, origin()).unwrap();
        let mut work = TypeWorkBudget::default();
        identity(&mut builder, &mut work).unwrap();
        assert!(builder.settled_zonk_nodes[0]);
        let id = InferenceVariableId::new(10);
        let index = node.index().unwrap();
        builder.nodes[index].effects =
            EffectRow::open(EffectRowVariable::inference(id), Box::new([]));
        builder
            .invalidate_settled_zonk_range(index..index + 1)
            .unwrap();
        assert!(!builder.settled_zonk_nodes[index]);
        identity(&mut builder, &mut work).unwrap();
        assert!(!builder.settled_zonk_nodes[0]);
        builder.nodes[index].effects = EffectRow::empty();
        builder
            .invalidate_settled_zonk_range(index..index + 1)
            .unwrap();
        identity(&mut builder, &mut work).unwrap();
        assert!(builder.settled_zonk_nodes[0]);
        builder.complete_cleanup_row(id);
        assert!(builder.settled_zonk_nodes.is_empty());
        assert_eq!(identity(&mut builder, &mut work).unwrap(), 1);
        builder.defer_cleanup_row(id).unwrap();
        assert_eq!(identity(&mut builder, &mut work).unwrap(), 1);
        assert!(builder.settled_zonk_nodes.is_empty());
    }
    #[test]
    fn settled_zonk_rollback_cannot_reuse_an_old_ordinal_marker() {
        let mut builder = CoreBuilder::new();
        let checkpoint = builder.checkpoint();
        let mut work = TypeWorkBudget::default();
        builder.unit(Type::Unit, origin()).unwrap();
        identity(&mut builder, &mut work).unwrap();
        assert!(builder.settled_zonk_nodes[0]);
        builder.rollback(checkpoint);
        assert!(builder.settled_zonk_nodes.is_empty());
        builder
            .unit(Type::Inference(InferenceVariableId::new(11)), origin())
            .unwrap();
        assert_eq!(identity(&mut builder, &mut work).unwrap(), 1);
        assert!(!builder.settled_zonk_nodes[0]);
    }
    #[test]
    fn settled_zonk_work_is_exact_prefix_preserving_and_fresh_retryable() {
        let make = || {
            let mut builder = CoreBuilder::new();
            builder.unit(Type::Unit, origin()).unwrap();
            builder.unit(Type::Unit, origin()).unwrap();
            builder
        };
        let mut measured = make();
        let mut budget = TypeWorkBudget::default();
        identity(&mut measured, &mut budget).unwrap();
        let used = budget.used();
        for prefix in [0, 11, 150] {
            let mut short = make();
            let mut budget = TypeWorkBudget::with_limit(prefix + used - 1);
            budget.charge(prefix).unwrap();
            assert_eq!(
                identity(&mut short, &mut budget),
                Err(BuildError::TypeWorkExceeded)
            );
            assert!(
                short.settled_zonk_nodes.is_empty(),
                "failed pass publishes no new marker"
            );
            for _ in 0..2 {
                let mut fresh = make();
                let mut budget = TypeWorkBudget::with_limit(prefix + used);
                budget.charge(prefix).unwrap();
                identity(&mut fresh, &mut budget).unwrap();
                assert_eq!(budget.used(), prefix + used);
            }
        }
    }
    #[test]
    fn settled_zonk_does_not_hide_new_input_depth_refusal() {
        let mut builder = CoreBuilder::new();
        builder.unit(Type::Unit, origin()).unwrap();
        let mut work = TypeWorkBudget::default();
        identity(&mut builder, &mut work).unwrap();
        let mut deep = Type::Unit;
        for _ in 0..256 {
            deep = Type::Function(Box::new(Type::Unit), Box::new(deep));
        }
        assert_eq!(
            builder.unit(deep, origin()),
            Err(BuildError::TypeDepthExceeded)
        );
        assert_eq!(builder.nodes.len(), 1);
    }
}
