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
    ProviderPending,
    InterpretNative(EffectRow, EffectInstance),
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
    fn deferred_source_row_completion_rolls_back_late_exclusion_work_at_exact_budget() {
        let source = crate::source::SourceFile::new("provider-row-budget.ash", "()").unwrap();
        let span = source
            .span(crate::source::ByteRange::new(0, 2).unwrap())
            .unwrap();
        let run = |limit: usize, prefill: usize| {
            let mut elaborator = EffectElaborator::new();
            let unrelated = elaborator.fresh_effect_row(span).unwrap();
            let EffectRowVariable::Inference(unrelated_id) = unrelated.tail().unwrap().variable()
            else {
                unreachable!()
            };
            // This existing obligation is revisited after the new solution
            // has been inserted, so one-short reaches the late failure seam.
            elaborator
                .row_inference_obligations
                .insert_unique(unrelated_id, unrelated)
                .unwrap();
            let pending = elaborator.defer_provider_row(span).unwrap();
            let EffectRowVariable::Inference(identity) = pending.tail().unwrap().variable() else {
                unreachable!()
            };
            elaborator.type_work = TypeWorkBudget::with_limit(limit);
            elaborator.type_work.charge(prefill).unwrap();
            let result = elaborator.complete_provider_row(identity, EffectRow::empty());
            let used = elaborator.type_work.used();
            assert!(
                elaborator
                    .row_inference_obligations
                    .values()
                    .next()
                    .is_some()
            );
            if result.is_err() {
                assert!(!elaborator.row_inference_solutions.contains_key(&identity));
                assert!(
                    !elaborator
                        .authenticated_inference_solutions
                        .contains(&identity)
                );
                assert!(elaborator.cleanup_rows.identities.contains(&identity));
                assert!(matches!(elaborator.cleanup_rows.equations.as_slice(),
                    [(actual, Equation::ProviderPending, _)] if *actual == identity));
                assert!(elaborator.builder.requires_type_rewrite());
                // Work is consumed on refusal; replenish only the work ledger
                // to retry this exact private equation and original identity.
                elaborator.type_work = TypeWorkBudget::with_limit(usize::MAX);
                elaborator
                    .complete_provider_row(identity, EffectRow::empty())
                    .unwrap();
            }
            assert!(elaborator.row_inference_solutions.contains_key(&identity));
            assert!(
                elaborator
                    .authenticated_inference_solutions
                    .contains(&identity)
            );
            assert!(!elaborator.cleanup_rows.identities.contains(&identity));
            assert!(elaborator.cleanup_rows.equations.is_empty());
            // Completion removed the last pending guard, but a committed row
            // still needs the same source rewrite before replay can use it.
            assert!(elaborator.builder.requires_type_rewrite());
            elaborator.zonk_builder_types_since(None, false).unwrap();
            assert!(!elaborator.builder.requires_type_rewrite());
            (result, used)
        };
        let (result, exact) = run(usize::MAX, 0);
        result.unwrap();
        assert_eq!(run(exact, 0), (Ok(()), exact));
        assert_eq!(run(exact, 0), (Ok(()), exact));
        assert_eq!(run(exact - 1, 0).0, Err(type_resource()));
        assert_eq!(run(exact + 7, 7), (Ok(()), exact + 7));
        assert_eq!(run(exact + 6, 7).0, Err(type_resource()));
    }

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
    pub(super) fn take_provider_pending<F: CoreLoweringFamily>(
        &mut self,
        builder: &crate::core::CoreBuilder<F>,
        root: NodeId,
        work: &mut crate::types::TypeWorkBudget,
    ) -> Result<crate::core::provider::HandlerPendingRows, TypeError> {
        use crate::core::provider::{
            HandlerPendingRows, PendingRowEquality, PendingRowEquation, PendingRowRecomputation,
            PendingRowRecord,
        };
        let mut result = HandlerPendingRows::default();
        work.charge(
            self.equations
                .len()
                .checked_mul(2)
                .and_then(|count| count.checked_add(self.equalities.len()))
                .and_then(|count| count.checked_add(self.recomputations.len()))
                .ok_or_else(type_resource)?,
        )
        .map_err(|()| type_resource())?;
        result
            .equations
            .try_reserve_exact(self.equations.len())
            .map_err(|_| type_resource())?;
        result
            .equalities
            .try_reserve_exact(self.equalities.len())
            .map_err(|_| type_resource())?;
        result
            .recomputations
            .try_reserve_exact(self.recomputations.len())
            .map_err(|_| type_resource())?;
        for (identity, equation, source) in self.equations.drain(..) {
            if !self.identities.remove(&identity) {
                return Err(invalid_state());
            }
            let equation = match equation {
                Equation::ProviderPending | Equation::InterpretNative(_, _) => {
                    return Err(invalid_state());
                }
                Equation::Discard(ordinal) => {
                    PendingRowEquation::Discard(builder.provider_node_at_ordinal(root, ordinal)?)
                }
                Equation::Union(left, right) => PendingRowEquation::Union(left, right),
                Equation::Remove(row, effect, absent) => {
                    PendingRowEquation::Remove(row, effect, absent)
                }
            };
            result.equations.push(PendingRowRecord {
                identity,
                equation,
                source,
            });
        }
        if !self.identities.is_empty() {
            return Err(invalid_state());
        }
        for (left, right, source) in self.equalities.drain(..) {
            result.equalities.push(PendingRowEquality {
                left,
                right,
                source,
            });
        }
        for (range, output, handler, resume) in self.recomputations.drain(..) {
            work.charge(range.len()).map_err(|()| type_resource())?;
            let mut nodes = Vec::new();
            nodes
                .try_reserve_exact(range.len())
                .map_err(|_| type_resource())?;
            for ordinal in range {
                nodes.push(builder.provider_node_at_ordinal(root, ordinal)?);
            }
            result.recomputations.push(PendingRowRecomputation {
                nodes,
                output,
                handler,
                resume,
            });
        }
        Ok(result)
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
                    Equation::ProviderPending => return Err(invalid_state()),
                    Equation::InterpretNative(row, native) => {
                        let row = self.resolve_cleanup_row(row, &solutions)?;
                        crate::core::provider::interpret_native_phase_row(
                            &row,
                            native,
                            &mut self.type_work,
                        )
                        .map_err(super::provider::contract_validation_failure)
                        .map_err(super::resolved_build_error)
                    }
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

    /// A genuine source row equation whose provider input is available only
    /// after ordinary evidence closure. It cannot enter cleanup realization.
    pub(super) fn defer_provider_row(&mut self, span: Span) -> Result<EffectRow, TypeError> {
        self.defer_cleanup_equation(Equation::ProviderPending, span)
    }

    pub(super) fn provider_native_phase_row(
        &mut self,
        row: &EffectRow,
        native: &EffectInstance,
        span: Span,
    ) -> Result<EffectRow, TypeError> {
        if self.cleanup_row_pending(row) {
            let row = clone_effect_row_with_budget(row, &mut self.type_work)
                .map_err(|()| type_resource())?;
            let native =
                crate::types::clone_effect_instance_with_budget(native, &mut self.type_work)
                    .map_err(|()| type_resource())?;
            self.defer_cleanup_equation(Equation::InterpretNative(row, native), span)
        } else {
            crate::core::provider::interpret_native_phase_row(row, native, &mut self.type_work)
                .map_err(super::provider::contract_validation_failure)
                .map_err(super::resolved_build_error)
        }
    }

    pub(super) fn complete_provider_row(
        &mut self,
        identity: InferenceVariableId,
        row: EffectRow,
    ) -> Result<(), TypeError> {
        self.type_work
            .charge(self.cleanup_rows.equations.len())
            .map_err(|()| type_resource())?;
        let index = self
            .cleanup_rows
            .equations
            .iter()
            .position(|(id, equation, _)| {
                *id == identity && matches!(equation, Equation::ProviderPending)
            })
            .ok_or_else(invalid_state)?;
        self.complete_ready_source_row(index, row)
    }

    fn complete_ready_source_row(&mut self, index: usize, row: EffectRow) -> Result<(), TypeError> {
        let (identity, _, _) = self
            .cleanup_rows
            .equations
            .get(index)
            .ok_or_else(invalid_state)?;
        let identity = *identity;
        if self.row_inference_solutions.contains_key(&identity)
            || !self.cleanup_rows.identities.contains(&identity)
        {
            return Err(invalid_state());
        }
        // Removal must be fully paid before a solution enters the ordinary
        // unifier. The solver's late exclusion check retains its rollback list.
        self.type_work
            .charge(self.cleanup_rows.equations.len() - index)
            .map_err(|()| type_resource())?;
        let mut inserted = Vec::new();
        if let Err(failure) = self.solve_effect_row_variable(identity, &[], row, &mut inserted) {
            // The ordinary solver validates prior row exclusions after its
            // insertion. Restore only this attempted solution on refusal.
            for variable in inserted.into_iter().rev() {
                self.row_inference_solutions.remove(variable);
                self.authenticated_inference_solutions.remove(&variable);
                self.row_inference_obligations.remove(variable);
            }
            return Err(match failure {
                UnificationFailure::Resource => type_resource(),
                _ => invalid_state(),
            });
        }
        self.cleanup_rows.equations.remove(index);
        let removed = self.cleanup_rows.identities.remove(&identity);
        debug_assert!(removed);
        self.builder.complete_cleanup_row(identity);
        Ok(())
    }

    /// Resolve only ordinary unions/removals whose complete inputs already
    /// exist. Discard and provider inputs remain blocked; no graph is guessed.
    pub(super) fn complete_ready_provider_row_equations(&mut self) -> Result<(), TypeError> {
        loop {
            let mut progressed = false;
            let mut index = 0;
            while index < self.cleanup_rows.equations.len() {
                self.type_work.charge(1).map_err(|()| type_resource())?;
                let (_, equation, span) = &self.cleanup_rows.equations[index];
                let span = *span;
                let equation = match equation {
                    Equation::ProviderPending | Equation::Discard(_) => {
                        index += 1;
                        continue;
                    }
                    Equation::InterpretNative(row, effect) => Equation::InterpretNative(
                        clone_effect_row_with_budget(row, &mut self.type_work)
                            .map_err(|()| type_resource())?,
                        crate::types::clone_effect_instance_with_budget(
                            effect,
                            &mut self.type_work,
                        )
                        .map_err(|()| type_resource())?,
                    ),
                    Equation::Union(left, right) => Equation::Union(
                        clone_effect_row_with_budget(left, &mut self.type_work)
                            .map_err(|()| type_resource())?,
                        clone_effect_row_with_budget(right, &mut self.type_work)
                            .map_err(|()| type_resource())?,
                    ),
                    Equation::Remove(row, effect, absent) => Equation::Remove(
                        clone_effect_row_with_budget(row, &mut self.type_work)
                            .map_err(|()| type_resource())?,
                        crate::types::clone_effect_instance_with_budget(
                            effect,
                            &mut self.type_work,
                        )
                        .map_err(|()| type_resource())?,
                        *absent,
                    ),
                };
                let ready = |row: &EffectRow| {
                    !matches!(
                        row.tail().map(|tail| tail.variable()),
                        Some(EffectRowVariable::Inference(_))
                    )
                };
                let solution = match equation {
                    Equation::Union(left, right) => {
                        let left = self.zonk_effect_row(&left)?;
                        let right = self.zonk_effect_row(&right)?;
                        if !ready(&left) || !ready(&right) {
                            index += 1;
                            continue;
                        }
                        self.union_effects(&left, &right, span)?
                    }
                    Equation::InterpretNative(row, effect) => {
                        let row = self.zonk_effect_row(&row)?;
                        if !ready(&row) {
                            index += 1;
                            continue;
                        }
                        crate::core::provider::interpret_native_phase_row(
                            &row,
                            &effect,
                            &mut self.type_work,
                        )
                        .map_err(super::provider::contract_validation_failure)
                        .map_err(super::resolved_build_error)?
                    }
                    Equation::Remove(row, effect, absent) => {
                        let row = self.zonk_effect_row(&row)?;
                        if !ready(&row) {
                            index += 1;
                            continue;
                        }
                        self.cleanup_remove_resolved(row, &effect, span, absent)?
                    }
                    _ => return Err(invalid_state()),
                };
                self.complete_ready_source_row(index, solution)?;
                progressed = true;
            }
            if !progressed {
                return Ok(());
            }
        }
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
