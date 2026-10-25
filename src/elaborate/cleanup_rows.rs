//! Row obligations whose unknown input is owned cleanup at a discard.

use std::collections::{HashMap, HashSet};

use super::{
    CoreElaborator, CoreLoweringFamily, EffectRowCause, TypeError, TypeReason, TypedNode,
    TypedNodeOwner, UnificationFailure, capture_failure, effect_row_failure, inference_failure,
    invalid_state, type_resource, zonk_core_effect_row,
};
use crate::{
    core::{
        NodeId,
        effect::{HandlerId, clone_effect_instance_with_budget},
    },
    resolved::{BinderId, ResumeId},
    source::Span,
    types::{
        EffectInstance, EffectRow, EffectRowVariable, InferenceVariableId,
        clone_effect_row_with_budget, same_effect_rows_with_budget,
    },
};

#[derive(Debug)]
enum Equation {
    Discard(usize),
    Union(EffectRow, EffectRow),
    Remove(EffectRow, crate::types::EffectInstance, bool),
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        elaborate::EffectElaborator,
        types::{ComputationType, Type, TypeWorkBudget},
    };

    #[test]
    fn failed_unification_rolls_back_cleanup_row_obligations() {
        let source = crate::source::SourceFile::new("cleanup-rollback.ash", "()").unwrap();
        let span = source
            .span(crate::source::ByteRange::new(0, 2).unwrap())
            .unwrap();
        let mut elaborator = EffectElaborator::new();
        let pending = elaborator
            .defer_cleanup_equation(
                Equation::Union(EffectRow::empty(), EffectRow::empty()),
                span,
            )
            .unwrap();
        let candidate = elaborator.fresh_effect_row(span).unwrap();
        let left = Type::Tuple(Box::new([
            Type::function_computation(Type::Unit, ComputationType::new(Type::Unit, pending)),
            Type::Int,
        ]));
        let right = Type::Tuple(Box::new([
            Type::function_computation(Type::Unit, ComputationType::new(Type::Unit, candidate)),
            Type::Bool,
        ]));
        assert_eq!(
            elaborator.unify(&left, &right),
            Err(UnificationFailure::Mismatch)
        );
        assert_eq!(elaborator.cleanup_rows.equations.len(), 1);
        assert_eq!(elaborator.cleanup_rows.identities.len(), 1);
        assert!(elaborator.cleanup_rows.equalities.is_empty());
    }

    #[test]
    fn cyclic_cleanup_rows_reach_the_least_finite_solution_at_exact_work() {
        let source = crate::source::SourceFile::new("cyclic-cleanup-rows.ash", "()").unwrap();
        let span = source
            .span(crate::source::ByteRange::new(0, 2).unwrap())
            .unwrap();
        let run = |limit| {
            let mut elaborator = EffectElaborator::new();
            elaborator.type_work = TypeWorkBudget::with_limit(limit);
            let result = (|| {
                let first = elaborator.defer_cleanup_equation(
                    Equation::Union(EffectRow::empty(), EffectRow::empty()),
                    span,
                )?;
                let effect = EffectInstance::new(
                    crate::types::EffectId::new(crate::module::ModuleId::new(0), 0),
                    Box::new([]),
                );
                let seed = EffectRow::singleton(effect);
                let dependency = clone_effect_row_with_budget(&first, &mut elaborator.type_work)
                    .map_err(|_| type_resource())?;
                let second = elaborator.defer_cleanup_union(dependency, seed, span)?;
                let replacement = clone_effect_row_with_budget(&second, &mut elaborator.type_work)
                    .map_err(|_| type_resource())?;
                elaborator.cleanup_rows.equations[0].1 =
                    Equation::Union(replacement, EffectRow::empty());
                elaborator.solve_cleanup_rows(&[], &[], &[], &[])?;
                let first = elaborator.zonk_effect_row(&first)?;
                let second = elaborator.zonk_effect_row(&second)?;
                assert_eq!(first.known().len(), 1);
                assert!(first.tail().is_none());
                assert!(
                    same_effect_rows_with_budget(&first, &second, &mut elaborator.type_work)
                        .map_err(|_| type_resource())?
                );
                Ok::<(), TypeError>(())
            })();
            (result, elaborator.type_work.used())
        };
        let (result, exact) = run(usize::MAX);
        result.unwrap();
        assert_eq!(run(exact - 1).0, Err(type_resource()));
        assert_eq!(run(exact), (Ok(()), exact));
        assert_eq!(run(exact), (Ok(()), exact));
    }
}

#[derive(Debug, Default)]
pub(super) struct CleanupRows {
    equations: Vec<(InferenceVariableId, Equation, Span)>,
    identities: HashSet<InferenceVariableId>,
    equalities: Vec<(EffectRow, EffectRow, Span)>,
    recomputations: Vec<(std::ops::Range<usize>, EffectRow, HandlerId, ResumeId)>,
}

impl CleanupRows {
    pub(super) fn is_empty(&self) -> bool {
        self.equations.is_empty() && self.equalities.is_empty() && self.recomputations.is_empty()
    }
    pub(super) fn contains(&self, id: InferenceVariableId) -> bool {
        self.identities.contains(&id)
    }

    pub(super) fn checkpoint(&self) -> (usize, usize) {
        (self.equations.len(), self.equalities.len())
    }
}

impl<F: CoreLoweringFamily> CoreElaborator<F> {
    pub(super) fn rollback_cleanup_rows(&mut self, (equations, equalities): (usize, usize)) {
        for (id, _, _) in self.cleanup_rows.equations.drain(equations..) {
            self.cleanup_rows.identities.remove(&id);
            self.builder.forget_cleanup_row(id);
        }
        self.cleanup_rows.equalities.truncate(equalities);
    }
    pub(super) fn finish_standalone_cleanup_rows(
        &mut self,
        result: TypedNode,
    ) -> Result<TypedNode, TypeError> {
        let mut result = TypedNodeOwner::new(result);
        if !self.cleanup_rows.is_empty() {
            self.solve_cleanup_rows(&[], &[], &[], &[])?;
            result.replace_type(self.zonk(&result.ty)?);
            result.replace_effects(self.zonk_effect_row(&result.effects)?);
        }
        Ok(result.into_inner())
    }

    pub(super) fn solve_cleanup_rows(
        &mut self,
        roots: &[(BinderId, NodeId)],
        imports: &[(BinderId, &crate::core::capture::CaptureValueSummary)],
        methods: &[crate::core::capture::MethodUse],
        adapters: &[crate::core::capture::MethodAdapter],
    ) -> Result<(), TypeError> {
        if self.cleanup_rows.is_empty() {
            return Ok(());
        }
        self.zonk_builder_types_since(None, false)
            .map_err(TypeError::Internal)?;
        let requirements = crate::core::capture::infer_cleanup_rows(
            &self.builder,
            roots,
            imports,
            F::capture_operation,
            methods,
            adapters,
            &mut self.type_work,
        )
        .map_err(|failure| capture_failure(failure, &mut self.type_work))?;
        let pending = std::mem::take(&mut self.cleanup_rows);
        let mut solutions = HashMap::new();
        self.type_work
            .charge(pending.equations.len() + self.row_inference_solutions.len())
            .map_err(|_| type_resource())?;
        solutions
            .try_reserve(pending.equations.len() + self.row_inference_solutions.len())
            .map_err(|_| type_resource())?;
        for (id, row) in self.row_inference_solutions.iter() {
            solutions.insert(
                *id,
                clone_effect_row_with_budget(row, &mut self.type_work)
                    .map_err(|_| type_resource())?,
            );
        }
        for (id, _, _) in &pending.equations {
            solutions.insert(*id, EffectRow::empty());
        }
        // These equations are monotone unions and exact removals over the
        // finite action-row vocabulary. Work exhaustion publishes no solution.
        loop {
            let mut changed = false;
            let mut failure = None;
            for (id, equation, span) in &pending.equations {
                self.type_work.charge(1).map_err(|_| type_resource())?;
                let row = match equation {
                    Equation::Discard(node) => (|| {
                        let mut row = EffectRow::empty();
                        for requirement in &requirements {
                            self.type_work.charge(1).map_err(|_| type_resource())?;
                            if !requirement.local
                                || requirement.discard != *node
                                || requirement.context != 0
                            {
                                continue;
                            }
                            let mut next =
                                self.resolve_cleanup_row(&requirement.row, &solutions)?;
                            for effect in &requirement.retained {
                                next = self.cleanup_remove_resolved(next, effect, *span, true)?;
                            }
                            row = self.union_effects(&row, &next, *span)?;
                        }
                        Ok(row)
                    })(),
                    Equation::Union(left, right) => {
                        let left = self.resolve_cleanup_row(left, &solutions)?;
                        let right = self.resolve_cleanup_row(right, &solutions)?;
                        self.union_effects(&left, &right, *span)
                    }
                    Equation::Remove(row, effect, absent) => {
                        let row = self.resolve_cleanup_row(row, &solutions)?;
                        self.cleanup_remove_resolved(row, effect, *span, *absent)
                    }
                };
                match row {
                    Ok(row) => {
                        if !same_effect_rows_with_budget(
                            &row,
                            solutions.get(id).ok_or_else(invalid_state)?,
                            &mut self.type_work,
                        )
                        .map_err(|_| type_resource())?
                        {
                            solutions.insert(*id, row);
                            changed = true;
                        }
                    }
                    Err(error @ TypeError::Source(_)) => {
                        if failure.is_none() {
                            failure = Some(error);
                        }
                    }
                    Err(error) => return Err(error),
                }
            }
            if !changed {
                if let Some(error) = failure {
                    return Err(error);
                }
                break;
            }
        }
        let mut inserted = Vec::new();
        for (id, _, _) in &pending.equations {
            let row = solutions.remove(id).ok_or_else(invalid_state)?;
            self.solve_effect_row_variable(*id, &[], row, &mut inserted)
                .map_err(|failure| match failure {
                    UnificationFailure::Resource => type_resource(),
                    _ => invalid_state(),
                })?;
        }
        for (left, right, span) in &pending.equalities {
            self.unify_effect_rows(left, right)
                .map_err(|failure| match failure {
                    UnificationFailure::Resource => type_resource(),
                    _ => effect_row_failure(
                        EffectRowCause::CleanupRequirement,
                        *span,
                        "cleanup effects do not satisfy this row requirement",
                    ),
                })?;
        }
        self.check_deferred_local_nominal_escapes()?;
        self.check_deferred_resource_escapes()?;
        self.zonk_builder_types().map_err(TypeError::Internal)?;
        self.builder.finish_cleanup_rows();
        for (range, output, handler, owner) in &pending.recomputations {
            let output = self.zonk_effect_row(output)?;
            F::recompute_clause_effect_rows(
                &mut self.builder,
                range.clone(),
                &output,
                *handler,
                *owner,
            )?;
        }
        F::finish_cleanup_effect_rows(&mut self.builder)?;
        Ok(())
    }

    fn resolve_cleanup_row(
        &mut self,
        row: &EffectRow,
        solutions: &HashMap<InferenceVariableId, EffectRow>,
    ) -> Result<EffectRow, TypeError> {
        Ok(zonk_core_effect_row(
            row,
            &self.inference_solutions,
            solutions,
            &self.inference_variables,
            &self.authenticated_inference_solutions,
            &mut self.type_work,
            false,
        )?)
    }

    fn cleanup_remove_resolved(
        &mut self,
        row: EffectRow,
        effect: &EffectInstance,
        span: Span,
        absent: bool,
    ) -> Result<EffectRow, TypeError> {
        match row
            .remove_exact_with_budget(effect, &mut self.type_work)
            .map_err(|_| type_resource())?
        {
            Ok(row) => Ok(row),
            Err(crate::types::EffectRowError::Missing) if absent => Ok(row),
            Err(_) if absent => Err(effect_row_failure(
                EffectRowCause::Removal,
                span,
                "the handled computation does not request this exact effect instance",
            )),
            Err(_) => Err(inference_failure(
                TypeReason::MissingHandledEffect,
                span,
                "the handled computation does not request this exact effect instance",
            )),
        }
    }
    pub(super) fn cleanup_row_pending(&self, row: &EffectRow) -> bool {
        row.tail().is_some_and(|tail| match tail.variable() {
            EffectRowVariable::Inference(id) => self.cleanup_rows.identities.contains(&id),
            _ => false,
        })
    }

    fn defer_cleanup_equation(
        &mut self,
        equation: Equation,
        span: Span,
    ) -> Result<EffectRow, TypeError> {
        self.type_work.charge(3).map_err(|_| type_resource())?;
        self.cleanup_rows
            .equations
            .try_reserve(1)
            .map_err(|_| type_resource())?;
        self.cleanup_rows
            .identities
            .try_reserve(1)
            .map_err(|_| type_resource())?;
        let row = self.fresh_effect_row(span)?;
        let Some(tail) = row.tail() else {
            return Err(invalid_state());
        };
        let EffectRowVariable::Inference(id) = tail.variable() else {
            return Err(invalid_state());
        };
        self.builder.defer_cleanup_row(id)?;
        self.cleanup_rows.identities.insert(id);
        self.cleanup_rows.equations.push((id, equation, span));
        Ok(row)
    }

    pub(super) fn defer_cleanup_discard(
        &mut self,
        node: usize,
        span: Span,
    ) -> Result<EffectRow, TypeError> {
        self.defer_cleanup_equation(Equation::Discard(node), span)
    }

    pub(super) fn defer_cleanup_union(
        &mut self,
        left: EffectRow,
        right: EffectRow,
        span: Span,
    ) -> Result<EffectRow, TypeError> {
        if left.is_empty() {
            return Ok(right);
        }
        if right.is_empty() {
            return Ok(left);
        }
        self.defer_cleanup_equation(Equation::Union(left, right), span)
    }

    pub(super) fn defer_cleanup_equality(
        &mut self,
        left: &EffectRow,
        right: &EffectRow,
    ) -> Result<(), TypeError> {
        let span = self
            .cleanup_rows
            .equations
            .first()
            .ok_or_else(invalid_state)?
            .2;
        for (candidate, replacement) in [(left, right), (right, left)] {
            if candidate.known().is_empty()
                && let Some(tail) = candidate.tail()
                && let EffectRowVariable::Inference(id) = tail.variable()
                && !self.cleanup_rows.identities.contains(&id)
                && !self.row_inference_solutions.contains_key(&id)
            {
                let replacement = clone_effect_row_with_budget(replacement, &mut self.type_work)
                    .map_err(|_| type_resource())?;
                self.type_work.charge(3).map_err(|_| type_resource())?;
                self.cleanup_rows
                    .identities
                    .try_reserve(1)
                    .map_err(|_| type_resource())?;
                self.cleanup_rows
                    .equations
                    .try_reserve(1)
                    .map_err(|_| type_resource())?;
                self.builder.defer_cleanup_row(id)?;
                self.cleanup_rows.identities.insert(id);
                self.cleanup_rows.equations.push((
                    id,
                    Equation::Union(replacement, EffectRow::empty()),
                    span,
                ));
                return Ok(());
            }
        }
        let left =
            clone_effect_row_with_budget(left, &mut self.type_work).map_err(|_| type_resource())?;
        let right = clone_effect_row_with_budget(right, &mut self.type_work)
            .map_err(|_| type_resource())?;
        self.type_work.charge(3).map_err(|_| type_resource())?;
        self.cleanup_rows
            .equalities
            .try_reserve(1)
            .map_err(|_| type_resource())?;
        self.cleanup_rows.equalities.push((left, right, span));
        Ok(())
    }

    pub(super) fn remove_cleanup_effect(
        &mut self,
        row: &EffectRow,
        effect: &crate::types::EffectInstance,
        span: Span,
        absent: bool,
    ) -> Result<EffectRow, TypeError> {
        let row = self.qualify_effect_row(row)?;
        if self.cleanup_row_pending(&row) {
            let effect = clone_effect_instance_with_budget(effect, &mut self.type_work)?;
            return self.defer_cleanup_equation(Equation::Remove(row, effect, absent), span);
        }
        match row
            .remove_exact_with_budget(effect, &mut self.type_work)
            .map_err(|_| type_resource())?
        {
            Ok(row) => Ok(row),
            Err(crate::types::EffectRowError::Missing) if absent => Ok(row),
            Err(_) if absent => Err(effect_row_failure(
                EffectRowCause::Removal,
                span,
                "the handled computation does not request this exact effect instance",
            )),
            Err(_) => Err(inference_failure(
                TypeReason::MissingHandledEffect,
                span,
                "the handled computation does not request this exact effect instance",
            )),
        }
    }

    pub(super) fn recompute_cleanup_clause(
        &mut self,
        range: std::ops::Range<usize>,
        output: &EffectRow,
        handler: HandlerId,
        owner: ResumeId,
    ) -> Result<(), TypeError> {
        if self.cleanup_rows.equations.is_empty() {
            F::recompute_clause_effect_rows(&mut self.builder, range, output, handler, owner)?;
        } else {
            let output = clone_effect_row_with_budget(output, &mut self.type_work)
                .map_err(|_| type_resource())?;
            self.type_work.charge(4).map_err(|_| type_resource())?;
            self.cleanup_rows
                .recomputations
                .try_reserve(1)
                .map_err(|_| type_resource())?;
            self.cleanup_rows
                .recomputations
                .push((range, output, handler, owner));
        }
        Ok(())
    }
}
