//! Symbolic direct demands reconstructed from the actual clause forest.
//!
//! Capture atoms remain unknown. Ordinary leaves use Ash's existing row
//! algebra; a nonprincipal leaf union remains an equation, never new lacks.

use super::{CaptureInputId, HandlerRowRecipeDraft, PendingRowEquation, RowEquationOperation};
use crate::{
    core::{
        EffectExprKind, EffectOperation, NodeId, PureExprKind, PureValue, ValidationError,
        provider::{charge, invalid, node, resource},
    },
    types::{
        EffectInstance, EffectRow, EffectRowError, EffectRowVariable, InferenceVariableId,
        TypeWorkBudget, clone_effect_instance_with_budget, clone_effect_row_with_budget,
        clone_type_with_budget, compare_effect_instances_with_budget,
        rebuild_effect_row_with_budget, same_effect_rows_with_budget,
    },
};
use std::{cmp::Ordering, collections::HashMap};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct DemandAtomId(usize);

#[derive(Debug)]
#[cfg_attr(test, derive(PartialEq))]
enum DemandAtom {
    Ordinary(EffectRow),
    Capture(CaptureInputId),
    Remove {
        input: DemandAtomId,
        effect: EffectInstance,
        absent: bool,
    },
}

#[derive(Debug, Default)]
#[cfg_attr(test, derive(PartialEq))]
struct DemandExpression {
    atoms: Vec<DemandAtomId>,
}

/// Retains the full direct graph demand rather than trusting a scalar D. This
/// owner alone is not conditional Core authority: annotation and completion
/// relations are checked separately before a template can be constructed.
#[derive(Debug)]
pub(super) struct DirectDemandProof {
    atoms: Vec<DemandAtom>,
    pending: Vec<DemandExpression>,
    nodes: Vec<DemandExpression>,
    direct: DemandExpression,
    projections: Vec<bool>,
    latents: Vec<bool>,
    function_constraints: Vec<bool>,
}

#[expect(
    clippy::too_many_arguments,
    reason = "recipe and body-free projections share one ordinary demand realizer with an explicit capture-domain obligation"
)]
fn realize_demands(
    terms: &[DemandAtom],
    direct_term: &DemandExpression,
    pending_terms: &[DemandExpression],
    types: &HashMap<crate::types::TypeVariableId, crate::types::Type>,
    rows: &HashMap<crate::types::TypeVariableId, EffectRow>,
    captures: &HashMap<CaptureInputId, EffectRow>,
    exact_domain: bool,
    work: &mut TypeWorkBudget,
) -> Result<(EffectRow, Vec<EffectRow>), ValidationError> {
    fn expression(
        expression: &DemandExpression,
        atoms: &[EffectRow],
        work: &mut TypeWorkBudget,
    ) -> Result<EffectRow, ValidationError> {
        let mut output = EffectRow::empty();
        for atom in &expression.atoms {
            charge(work, 1)?;
            let row = atoms.get(atom.0).ok_or_else(resource)?;
            output = output
                .union_with_budget(row, work)
                .map_err(|()| resource())?
                .map_err(|error| ValidationError::row_union_failure(error, None))?;
        }
        Ok(output)
    }
    charge(
        work,
        terms
            .len()
            .checked_add(pending_terms.len())
            .ok_or_else(resource)?,
    )?;
    let mut atoms = Vec::new();
    atoms
        .try_reserve_exact(terms.len())
        .map_err(|_| resource())?;
    let mut seen = std::collections::HashSet::new();
    for atom in terms {
        charge(work, 1)?;
        let actual = match atom {
            DemandAtom::Ordinary(row) => crate::types::substitute_effect_and_template_rows_with(
                row,
                types,
                rows,
                &HashMap::new(),
                |cells| work.charge(cells),
                || (),
            )
            .map_err(|()| resource())?
            .map_err(|_| ValidationError::new(crate::core::ValidationReason::EffectRow, None))?,
            DemandAtom::Capture(input) => {
                charge(work, 2)?;
                seen.try_reserve(1).map_err(|_| resource())?;
                seen.insert(*input);
                clone_effect_row_with_budget(
                    captures.get(input).ok_or_else(|| {
                        ValidationError::new(crate::core::ValidationReason::ResourceEscape, None)
                    })?,
                    work,
                )
                .map_err(|()| resource())?
            }
            DemandAtom::Remove {
                input,
                effect,
                absent,
            } => {
                let row: &EffectRow = atoms.get(input.0).ok_or_else(resource)?;
                let mut arguments = Vec::new();
                charge(
                    work,
                    effect
                        .arguments()
                        .len()
                        .checked_mul(2)
                        .ok_or_else(resource)?,
                )?;
                arguments
                    .try_reserve_exact(effect.arguments().len())
                    .map_err(|_| resource())?;
                for argument in effect.arguments() {
                    arguments.push(crate::types::IterativeArgumentOwner::new(
                        crate::types::substitute_kinded_argument_with(
                            argument,
                            types,
                            rows,
                            |cells| work.charge(cells),
                        )
                        .map_err(|()| resource())?
                        .map_err(|_| {
                            ValidationError::new(crate::core::ValidationReason::EffectRow, None)
                        })?,
                    ));
                }
                let mut actual = Vec::new();
                actual
                    .try_reserve_exact(arguments.len())
                    .map_err(|_| resource())?;
                actual.extend(
                    arguments
                        .into_iter()
                        .map(crate::types::IterativeArgumentOwner::into_inner),
                );
                let effect = EffectInstance::new_kinded(effect.effect(), actual.into_boxed_slice());
                match row
                    .remove_exact_with_budget(&effect, work)
                    .map_err(|()| resource())?
                {
                    Ok(row) => row,
                    Err(EffectRowError::Missing) if *absent => {
                        clone_effect_row_with_budget(row, work).map_err(|()| resource())?
                    }
                    Err(_) => {
                        return Err(ValidationError::new(
                            crate::core::ValidationReason::EffectRow,
                            None,
                        ));
                    }
                }
            }
        };
        atoms.push(actual);
    }
    charge(work, captures.len())?;
    if exact_domain
        && (seen.len() != captures.len() || captures.keys().any(|input| !seen.contains(input)))
    {
        return Err(ValidationError::new(
            crate::core::ValidationReason::ResourceEscape,
            None,
        ));
    }
    let direct = expression(direct_term, &atoms, work)?;
    let mut pending = Vec::new();
    pending
        .try_reserve_exact(pending_terms.len())
        .map_err(|_| resource())?;
    for row in pending_terms {
        pending.push(expression(row, &atoms, work)?);
    }
    Ok((direct, pending))
}

impl DirectDemandProof {
    /// Realizes the authenticated flat vocabulary. Capture inputs are explicit
    /// obligations, never guessed empty. The capture-independent case uses
    /// exactly this engine with an empty required input domain.
    pub(super) fn realize(
        &self,
        types: &HashMap<crate::types::TypeVariableId, crate::types::Type>,
        rows: &HashMap<crate::types::TypeVariableId, EffectRow>,
        captures: &HashMap<CaptureInputId, EffectRow>,
        work: &mut TypeWorkBudget,
    ) -> Result<(EffectRow, Vec<EffectRow>), ValidationError> {
        realize_demands(
            &self.atoms,
            &self.direct,
            &self.pending,
            types,
            rows,
            captures,
            true,
            work,
        )
    }
    fn intern(
        &mut self,
        atom: DemandAtom,
        work: &mut TypeWorkBudget,
    ) -> Result<DemandAtomId, ValidationError> {
        for (index, existing) in self.atoms.iter().enumerate() {
            charge(work, 1)?;
            let same = match (existing, &atom) {
                (DemandAtom::Ordinary(left), DemandAtom::Ordinary(right)) => {
                    same_effect_rows_with_budget(left, right, work).map_err(|()| resource())?
                }
                (DemandAtom::Capture(left), DemandAtom::Capture(right)) => left == right,
                (
                    DemandAtom::Remove {
                        input: left,
                        effect: a,
                        absent: x,
                    },
                    DemandAtom::Remove {
                        input: right,
                        effect: b,
                        absent: y,
                    },
                ) => {
                    left == right
                        && x == y
                        && compare_effect_instances_with_budget(a, b, work)
                            .map_err(|()| resource())?
                            == Ordering::Equal
                }
                _ => false,
            };
            if same {
                return Ok(DemandAtomId(index));
            }
        }
        charge(work, 1)?;
        self.atoms.try_reserve(1).map_err(|_| resource())?;
        let id = DemandAtomId(self.atoms.len());
        self.atoms.push(atom);
        Ok(id)
    }

    fn copy(
        expression: &DemandExpression,
        work: &mut TypeWorkBudget,
    ) -> Result<DemandExpression, ValidationError> {
        charge(work, expression.atoms.len())?;
        let mut atoms = Vec::new();
        atoms
            .try_reserve_exact(expression.atoms.len())
            .map_err(|_| resource())?;
        atoms.extend(expression.atoms.iter().copied());
        Ok(DemandExpression { atoms })
    }

    fn singleton(
        &mut self,
        atom: DemandAtom,
        work: &mut TypeWorkBudget,
    ) -> Result<DemandExpression, ValidationError> {
        let id = self.intern(atom, work)?;
        charge(work, 1)?;
        let mut atoms = Vec::new();
        atoms.try_reserve_exact(1).map_err(|_| resource())?;
        atoms.push(id);
        Ok(DemandExpression { atoms })
    }

    fn ordinary(
        &mut self,
        row: &EffectRow,
        work: &mut TypeWorkBudget,
    ) -> Result<DemandExpression, ValidationError> {
        if row.is_empty() {
            return Ok(DemandExpression::default());
        }
        let row = clone_effect_row_with_budget(row, work).map_err(|()| resource())?;
        self.singleton(DemandAtom::Ordinary(row), work)
    }

    fn union(
        &mut self,
        mut left: DemandExpression,
        right: &DemandExpression,
        work: &mut TypeWorkBudget,
    ) -> Result<DemandExpression, ValidationError> {
        charge(work, right.atoms.len())?;
        left.atoms
            .try_reserve(right.atoms.len())
            .map_err(|_| resource())?;
        for incoming in &right.atoms {
            charge(work, left.atoms.len())?;
            if !left.atoms.contains(incoming) {
                left.atoms.push(*incoming);
            }
        }
        // Coalesce ordinary leaves only when the existing one-tail kernel
        // derives their principal union. Unknown capture atoms remain separate.
        loop {
            let mut joined = None;
            'pairs: for a in 0..left.atoms.len() {
                charge(work, 1)?;
                for b in a + 1..left.atoms.len() {
                    charge(work, 1)?;
                    let (DemandAtom::Ordinary(x), DemandAtom::Ordinary(y)) =
                        (&self.atoms[left.atoms[a].0], &self.atoms[left.atoms[b].0])
                    else {
                        continue;
                    };
                    if let Ok(row) = x.union_with_budget(y, work).map_err(|()| resource())? {
                        joined = Some((a, b, row));
                        break 'pairs;
                    }
                }
            }
            let Some((a, b, row)) = joined else {
                break;
            };
            let atom = self.intern(DemandAtom::Ordinary(row), work)?;
            left.atoms.remove(b);
            left.atoms.remove(a);
            charge(work, left.atoms.len())?;
            if !left.atoms.contains(&atom) {
                left.atoms.push(atom);
            }
        }
        // Ordinals are flat scalar keys. Account comparisons before sorting.
        let comparisons = left
            .atoms
            .len()
            .checked_mul(left.atoms.len())
            .ok_or_else(resource)?;
        charge(work, comparisons)?;
        left.atoms.sort_unstable_by_key(|id| id.0);
        Ok(left)
    }

    fn remove(
        &mut self,
        row: &DemandExpression,
        effect: &EffectInstance,
        absent: bool,
        work: &mut TypeWorkBudget,
    ) -> Result<DemandExpression, ValidationError> {
        let mut result = DemandExpression::default();
        for input in &row.atoms {
            charge(work, 1)?;
            let reduced = match &self.atoms[input.0] {
                DemandAtom::Ordinary(row) => match row
                    .remove_exact_with_budget(effect, work)
                    .map_err(|()| resource())?
                {
                    Ok(row) => Some(DemandAtom::Ordinary(row)),
                    Err(EffectRowError::Missing) => Some(DemandAtom::Ordinary(
                        clone_effect_row_with_budget(row, work).map_err(|()| resource())?,
                    )),
                    Err(_) => None,
                },
                _ => None,
            };
            let expression = match reduced {
                Some(DemandAtom::Ordinary(row)) if row.is_empty() => DemandExpression::default(),
                Some(atom) => self.singleton(atom, work)?,
                None => {
                    // Exact removal is idempotent. Avoid growing a recursive
                    // pending equation into an unbounded nested term while
                    // retaining the original absence-policy constraints.
                    let mut cursor = *input;
                    let mut already_removed = false;
                    while let DemandAtom::Remove {
                        input: previous,
                        effect: existing,
                        absent: policy,
                    } = &self.atoms[cursor.0]
                    {
                        charge(work, 1)?;
                        if *policy == absent
                            && compare_effect_instances_with_budget(existing, effect, work)
                                .map_err(|()| resource())?
                                == Ordering::Equal
                        {
                            already_removed = true;
                            break;
                        }
                        cursor = *previous;
                    }
                    if already_removed {
                        charge(work, 1)?;
                        let mut atoms = Vec::new();
                        atoms.try_reserve_exact(1).map_err(|_| resource())?;
                        atoms.push(*input);
                        DemandExpression { atoms }
                    } else {
                        let effect = clone_effect_instance_with_budget(effect, work)
                            .map_err(|()| resource())?;
                        self.singleton(
                            DemandAtom::Remove {
                                input: *input,
                                effect,
                                absent,
                            },
                            work,
                        )?
                    }
                }
            };
            result = self.union(result, &expression, work)?;
        }
        Ok(result)
    }

    fn row(
        &mut self,
        row: &EffectRow,
        identities: &HashMap<InferenceVariableId, usize>,
        root: NodeId,
        work: &mut TypeWorkBudget,
    ) -> Result<DemandExpression, ValidationError> {
        let Some(tail) = row.tail() else {
            return self.ordinary(row, work);
        };
        let EffectRowVariable::Inference(identity) = tail.variable() else {
            return self.ordinary(row, work);
        };
        charge(work, 1)?;
        let index = *identities.get(&identity).ok_or_else(|| invalid(root))?;
        let pending = self.pending.get(index).ok_or_else(|| invalid(root))?;
        let expression = Self::copy(pending, work)?;
        // An inference identity cannot supply an exclusion. Such a restriction
        // needs its actual removal/constraint equation, not a tail annotation.
        if !tail.lacks().is_empty() {
            return Err(invalid(root));
        }
        let known = rebuild_effect_row_with_budget(
            row.known().iter(),
            None,
            std::iter::empty(),
            clone_type_with_budget,
            work,
        )
        .map_err(|()| resource())?;
        let known = self.ordinary(&known, work)?;
        self.union(expression, &known, work)
    }

    fn projection_matches(
        &self,
        claimed: &DemandExpression,
        actual: &DemandExpression,
        work: &mut TypeWorkBudget,
    ) -> Result<bool, ValidationError> {
        let conditional = |id: DemandAtomId| !matches!(self.atoms[id.0], DemandAtom::Ordinary(_));
        charge(
            work,
            claimed
                .atoms
                .len()
                .checked_add(actual.atoms.len())
                .ok_or_else(resource)?,
        )?;
        if !claimed
            .atoms
            .iter()
            .copied()
            .filter(|id| conditional(*id))
            .eq(actual.atoms.iter().copied().filter(|id| conditional(*id)))
        {
            return Ok(false);
        }
        for id in &claimed.atoms {
            charge(work, 1)?;
            let DemandAtom::Ordinary(claimed) = &self.atoms[id.0] else {
                continue;
            };
            let mut found = false;
            for id in &actual.atoms {
                charge(work, 1)?;
                let DemandAtom::Ordinary(actual) = &self.atoms[id.0] else {
                    continue;
                };
                if let Ok(union) = actual
                    .union_with_budget(claimed, work)
                    .map_err(|()| resource())?
                    && same_effect_rows_with_budget(&union, actual, work)
                        .map_err(|()| resource())?
                {
                    found = true;
                    break;
                }
            }
            if !found {
                return Ok(false);
            }
        }
        Ok(true)
    }

    fn authenticate_annotations(
        &mut self,
        recipe: &HandlerRowRecipeDraft,
        entry: &crate::core::provider::HandlerGraphView<'_>,
        identities: &HashMap<InferenceVariableId, usize>,
        work: &mut TypeWorkBudget,
    ) -> Result<(), ValidationError> {
        let entry = &entry.handler_graph();
        let program = &entry.draft.program;
        charge(
            work,
            recipe.nodes.len().checked_mul(3).ok_or_else(resource)?,
        )?;
        self.projections
            .try_reserve_exact(recipe.nodes.len())
            .map_err(|_| resource())?;
        self.latents
            .try_reserve_exact(recipe.nodes.len())
            .map_err(|_| resource())?;
        self.function_constraints
            .try_reserve_exact(recipe.nodes.len())
            .map_err(|_| resource())?;
        for (ordinal, equation) in recipe.nodes.iter().enumerate() {
            charge(work, 1)?;
            let stored = node(program, equation.node)?;
            let pending = stored
                .effects
                .tail()
                .is_some_and(|tail| matches!(tail.variable(), EffectRowVariable::Inference(_)));
            let mut owner_replay = false;
            if let super::RowEquationOperation::Resume { output } = equation.operation
                && let super::HandlerOutputOwner::Nested { node: handler, .. } =
                    recipe.outputs[output.0].owner
            {
                let handler_equation = recipe.node_equations
                    [handler.index().map_err(|_| invalid(handler))?]
                .ok_or_else(|| invalid(handler))?;
                let handler_row = &node(program, handler)?.effects;
                if handler_row
                    .tail()
                    .is_some_and(|tail| matches!(tail.variable(), EffectRowVariable::Inference(_)))
                {
                    let EffectExprKind::Operation(EffectOperation::Resume(resume)) = &stored.kind
                    else {
                        return Err(invalid(equation.node));
                    };
                    let operand = &node(program, resume.value())?.effects;
                    // Source replay was deferred before the clause was given
                    // its shared output. Authenticate this exact operand-only
                    // provisional position through its actual owner record.
                    charge(work, entry.draft.pending_rows.recomputations.len())?;
                    let replay = entry
                        .draft
                        .pending_rows
                        .recomputations
                        .iter()
                        .find(|record| {
                            record.handler == resume.handler() && record.resume == resume.owner()
                        })
                        .ok_or_else(|| invalid(equation.node))?;
                    charge(work, replay.nodes.len())?;
                    if !replay.nodes.contains(&equation.node) {
                        return Err(invalid(equation.node));
                    }
                    let claimed = self.row(&stored.effects, identities, equation.node, work)?;
                    let provisional = self.row(operand, identities, equation.node, work)?;
                    let complete = Self::copy(&self.nodes[handler_equation.0], work)?;
                    let complete = self.union(provisional, &complete, work)?;
                    let operand_matches =
                        same_effect_rows_with_budget(&stored.effects, operand, work)
                            .map_err(|()| resource())?;
                    charge(
                        work,
                        claimed
                            .atoms
                            .len()
                            .checked_add(complete.atoms.len())
                            .ok_or_else(resource)?,
                    )?;
                    if !operand_matches && claimed.atoms != complete.atoms {
                        return Err(invalid(equation.node));
                    }
                    owner_replay = true;
                }
            }
            if pending && !owner_replay {
                let claimed = self.row(&stored.effects, identities, equation.node, work)?;
                if !self.projection_matches(&claimed, &self.nodes[ordinal], work)? {
                    return Err(invalid(equation.node));
                }
            }
            self.projections.push(pending || owner_replay);
            let mut latent_position = false;
            if let Some(latent) = stored.ty.function_view().and_then(|view| view.effects())
                && latent
                    .tail()
                    .is_some_and(|tail| matches!(tail.variable(), EffectRowVariable::Inference(_)))
            {
                let claimed = self.row(latent, identities, equation.node, work)?;
                let mut actual = DemandExpression::default();
                for body in &recipe.latent_bodies[ordinal] {
                    let body = Self::copy(&self.nodes[body.0], work)?;
                    actual = self.union(actual, &body, work)?;
                }
                charge(
                    work,
                    actual
                        .atoms
                        .len()
                        .checked_add(claimed.atoms.len())
                        .ok_or_else(resource)?,
                )?;
                if actual.atoms != claimed.atoms {
                    return Err(invalid(equation.node));
                }
                latent_position = true;
            }
            self.latents.push(latent_position);
            let mut function_constraint = false;
            if let EffectExprKind::Pure(PureExprKind::Value(PureValue::Function(function))) =
                &stored.kind
            {
                let body = recipe.node_equations[function
                    .body()
                    .index()
                    .map_err(|_| invalid(equation.node))?]
                .ok_or_else(|| invalid(equation.node))?;
                charge(work, self.nodes[body.0].atoms.len())?;
                if self.nodes[body.0]
                    .atoms
                    .iter()
                    .any(|id| !matches!(self.atoms[id.0], DemandAtom::Ordinary(_)))
                {
                    // The actual body/codomain subset relation is retained. It
                    // is not solved by assuming the continuation capture empty.
                    function_constraint = true;
                }
            }
            self.function_constraints.push(function_constraint);
        }
        Ok(())
    }

    pub(super) fn node_projection(&self, equation: super::RowEquationId) -> bool {
        self.projections.get(equation.0).copied().unwrap_or(false)
    }

    pub(super) fn latent_projection(&self, equation: super::RowEquationId) -> bool {
        self.latents.get(equation.0).copied().unwrap_or(false)
    }

    pub(super) fn function_constraint(&self, equation: super::RowEquationId) -> bool {
        self.function_constraints
            .get(equation.0)
            .copied()
            .unwrap_or(false)
    }

    #[cfg(test)]
    pub(super) fn has_open_leaf(&self) -> bool {
        self.atoms.iter().any(|atom| matches!(atom, DemandAtom::Ordinary(row) if row.tail().is_some_and(|tail| matches!(tail.variable(), EffectRowVariable::Rigid(_)))))
    }

    fn authenticate_recomputations(
        &mut self,
        recipe: &HandlerRowRecipeDraft,
        entry: &crate::core::provider::HandlerGraphView<'_>,
        identities: &HashMap<InferenceVariableId, usize>,
        work: &mut TypeWorkBudget,
    ) -> Result<(), ValidationError> {
        let entry = &entry.handler_graph();
        use std::collections::HashSet;
        let program = &entry.draft.program;
        let mut replayed = HashSet::new();
        charge(work, entry.draft.pending_rows.recomputations.len())?;
        replayed
            .try_reserve(entry.draft.pending_rows.recomputations.len())
            .map_err(|_| resource())?;
        for record in &entry.draft.pending_rows.recomputations {
            charge(work, recipe.outputs.len())?;
            let handler_node = recipe
                .outputs
                .iter()
                .find_map(|output| match output.owner {
                    super::HandlerOutputOwner::Nested { handler, node }
                        if handler == record.handler =>
                    {
                        Some(node)
                    }
                    _ => None,
                })
                .ok_or_else(|| invalid(program.root))?;
            let handler = match &node(program, handler_node)?.kind {
                EffectExprKind::Operation(EffectOperation::Handler(handler)) => handler,
                EffectExprKind::Operation(EffectOperation::ProviderScope(scope)) => &scope.handler,
                _ => return Err(invalid(handler_node)),
            };
            charge(work, handler.clauses().len())?;
            let clause = handler
                .clauses()
                .iter()
                .find(|clause| clause.resume() == record.resume)
                .ok_or_else(|| invalid(handler_node))?;
            if !replayed.insert((record.handler, record.resume)) {
                return Err(invalid(handler_node));
            }
            let equation = recipe.node_equations
                [handler_node.index().map_err(|_| invalid(handler_node))?]
            .ok_or_else(|| invalid(handler_node))?;
            let claimed = self.row(&record.output, identities, handler_node, work)?;
            charge(
                work,
                claimed
                    .atoms
                    .len()
                    .checked_add(self.nodes[equation.0].atoms.len())
                    .ok_or_else(resource)?,
            )?;
            if claimed.atoms != self.nodes[equation.0].atoms {
                return Err(invalid(handler_node));
            }
            let mut descendants = HashSet::new();
            let mut stack = Vec::new();
            charge(work, 1)?;
            stack.try_reserve(1).map_err(|_| resource())?;
            stack.push(clause.body());
            while let Some(id) = stack.pop() {
                charge(work, 1)?;
                if descendants.contains(&id) {
                    continue;
                }
                descendants.try_reserve(1).map_err(|_| resource())?;
                descendants.insert(id);
                let stored = node(program, id)?;
                charge(work, stored.kind.child_count())?;
                stack
                    .try_reserve(stored.kind.child_count())
                    .map_err(|_| resource())?;
                for ordinal in 0..stored.kind.child_count() {
                    stack.push(stored.kind.child_at(ordinal).ok_or_else(|| invalid(id))?);
                }
            }
            let mut mapped = HashSet::new();
            charge(work, record.nodes.len())?;
            mapped
                .try_reserve(record.nodes.len())
                .map_err(|_| resource())?;
            for id in &record.nodes {
                if !descendants.contains(id) || !mapped.insert(*id) {
                    return Err(invalid(*id));
                }
            }
            if !mapped.contains(&clause.body()) {
                return Err(invalid(clause.body()));
            }
        }
        Ok(())
    }

    fn authenticate_source_equalities(
        &self,
        recipe: &HandlerRowRecipeDraft,
        entry: &crate::core::provider::HandlerGraphView<'_>,
        work: &mut TypeWorkBudget,
    ) -> Result<(), ValidationError> {
        let entry = &entry.handler_graph();
        let program = &entry.draft.program;
        // Scalar source equalities are diagnostic replay claims. Their actual
        // typing endpoints are reconstructed from immutable function bodies and
        // computation codomains, independently of the source's summary span.
        for equality in &entry.draft.pending_rows.equalities {
            charge(work, 1)?;
            if entry
                .draft
                .pending_rows
                .equations
                .first()
                .is_none_or(|record| record.source != equality.source)
            {
                return Err(invalid(program.root));
            }
            let pending = |row: &EffectRow| {
                row.tail()
                    .is_some_and(|tail| matches!(tail.variable(), EffectRowVariable::Inference(_)))
            };
            if !pending(&equality.left) && !pending(&equality.right) {
                return Err(invalid(program.root));
            }
            let mut matched = false;
            for equation in &recipe.nodes {
                charge(work, 1)?;
                let stored = node(program, equation.node)?;
                let EffectExprKind::Pure(PureExprKind::Value(PureValue::Function(function))) =
                    &stored.kind
                else {
                    continue;
                };
                let Some(view) = stored.ty.function_view() else {
                    continue;
                };
                let empty = EffectRow::empty();
                let latent = view.effects().unwrap_or(&empty);
                let body = &node(program, function.body())?.effects;
                if (same_effect_rows_with_budget(body, &equality.left, work)
                    .map_err(|()| resource())?
                    && same_effect_rows_with_budget(latent, &equality.right, work)
                        .map_err(|()| resource())?)
                    || (same_effect_rows_with_budget(body, &equality.right, work)
                        .map_err(|()| resource())?
                        && same_effect_rows_with_budget(latent, &equality.left, work)
                            .map_err(|()| resource())?)
                {
                    matched = true;
                    break;
                }
            }
            if !matched {
                return Err(invalid(program.root));
            }
        }
        Ok(())
    }

    pub(super) fn reconstruct(
        recipe: &HandlerRowRecipeDraft,
        entry: &crate::core::provider::HandlerGraphView<'_>,
        work: &mut TypeWorkBudget,
    ) -> Result<Self, ValidationError> {
        let entry = &entry.handler_graph();
        let program = &entry.draft.program;
        let records = &entry.draft.pending_rows.equations;
        let mut proof = Self {
            atoms: Vec::new(),
            pending: Vec::new(),
            nodes: Vec::new(),
            direct: DemandExpression::default(),
            projections: Vec::new(),
            latents: Vec::new(),
            function_constraints: Vec::new(),
        };
        let mut identities = HashMap::new();
        charge(work, records.len())?;
        identities
            .try_reserve(records.len())
            .map_err(|_| resource())?;
        for (index, record) in records.iter().enumerate() {
            identities.insert(record.identity, index);
        }
        // Pending union/removal references may be cyclic. Retain their actual
        // graph equations and derive a symbolic least fixed point over capture
        // inputs and ordinary leaves; no concrete capture row is assigned.
        charge(work, records.len())?;
        proof
            .pending
            .try_reserve_exact(records.len())
            .map_err(|_| resource())?;
        proof
            .pending
            .resize_with(records.len(), DemandExpression::default);
        loop {
            let mut changed = false;
            for (index, record) in records.iter().enumerate() {
                charge(work, 1)?;
                let expression = match &record.equation {
                    PendingRowEquation::Discard(id) => {
                        charge(work, recipe.discards.len())?;
                        let ordinal = recipe
                            .discards
                            .iter()
                            .position(|port| port.node == *id && port.pending == record.identity)
                            .ok_or_else(|| invalid(*id))?;
                        proof.singleton(DemandAtom::Capture(CaptureInputId(ordinal)), work)?
                    }
                    PendingRowEquation::Union(left, right) => {
                        let left = proof.row(left, &identities, program.root, work)?;
                        let right = proof.row(right, &identities, program.root, work)?;
                        proof.union(left, &right, work)?
                    }
                    PendingRowEquation::Remove(row, effect, absent) => {
                        let row = proof.row(row, &identities, program.root, work)?;
                        proof.remove(&row, effect, *absent, work)?
                    }
                };
                charge(
                    work,
                    expression
                        .atoms
                        .len()
                        .checked_add(proof.pending[index].atoms.len())
                        .ok_or_else(resource)?,
                )?;
                changed |= expression.atoms != proof.pending[index].atoms;
                proof.pending[index] = expression;
            }
            if !changed {
                break;
            }
        }
        charge(work, recipe.nodes.len())?;
        proof
            .nodes
            .try_reserve_exact(recipe.nodes.len())
            .map_err(|_| resource())?;
        for equation in &recipe.nodes {
            charge(work, 1)?;
            let stored = node(program, equation.node)?;
            let mut expression = DemandExpression::default();
            if !matches!(
                equation.operation,
                RowEquationOperation::Empty
                    | RowEquationOperation::Handler { .. }
                    | RowEquationOperation::ProviderScope { .. }
            ) {
                for input in &recipe.edges[equation.inputs.clone()] {
                    let input = Self::copy(&proof.nodes[input.0], work)?;
                    expression = proof.union(expression, &input, work)?;
                }
            }
            match &stored.kind {
                EffectExprKind::Operation(EffectOperation::Request(request)) => {
                    let row = rebuild_effect_row_with_budget(
                        std::iter::once(request.effect()),
                        None,
                        std::iter::empty(),
                        clone_type_with_budget,
                        work,
                    )
                    .map_err(|()| resource())?;
                    let requested = proof.ordinary(&row, work)?;
                    expression = proof.union(expression, &requested, work)?;
                }
                EffectExprKind::Operation(EffectOperation::NativeInterpret(boundary)) => {
                    charge(work, boundary.interpretations().len())?;
                    for interpretation in boundary.interpretations() {
                        expression =
                            proof.remove(&expression, interpretation.effect(), true, work)?;
                    }
                }
                EffectExprKind::Operation(EffectOperation::Discard(_)) => {
                    let RowEquationOperation::Discard { capture } = equation.operation else {
                        return Err(invalid(equation.node));
                    };
                    expression = proof.singleton(DemandAtom::Capture(capture), work)?;
                }
                EffectExprKind::Operation(EffectOperation::Handler(handler)) => {
                    let body = recipe.node_equations
                        [handler.body().index().map_err(|_| invalid(equation.node))?]
                    .ok_or_else(|| invalid(equation.node))?;
                    let body = Self::copy(&proof.nodes[body.0], work)?;
                    expression = proof.remove(
                        &body,
                        handler.effect(),
                        handler.hook_root().is_some() || handler.hook_registration.is_some(),
                        work,
                    )?;
                    for clause in handler.clauses() {
                        let clause = recipe.node_equations
                            [clause.body().index().map_err(|_| invalid(equation.node))?]
                        .ok_or_else(|| invalid(equation.node))?;
                        let clause = Self::copy(&proof.nodes[clause.0], work)?;
                        expression = proof.union(expression, &clause, work)?;
                    }
                }
                EffectExprKind::Operation(EffectOperation::ProviderScope(scope)) => {
                    let body = recipe.node_equations[scope
                        .handler
                        .body()
                        .index()
                        .map_err(|_| invalid(equation.node))?]
                    .ok_or_else(|| invalid(equation.node))?;
                    let body = Self::copy(&proof.nodes[body.0], work)?;
                    expression = proof.remove(&body, scope.handler.effect(), true, work)?;
                    for root in scope
                        .handler
                        .clauses()
                        .iter()
                        .map(|clause| clause.body())
                        .chain([scope.acquire.body, scope.finish.body])
                    {
                        let root = recipe.node_equations
                            [root.index().map_err(|_| invalid(equation.node))?]
                        .ok_or_else(|| invalid(equation.node))?;
                        let row = Self::copy(&proof.nodes[root.0], work)?;
                        expression = proof.union(expression, &row, work)?;
                    }
                    expression =
                        proof.remove(&expression, scope.descriptor.native_effect(), true, work)?;
                    let initializer = recipe.node_equations[scope
                        .initializer
                        .index()
                        .map_err(|_| invalid(equation.node))?]
                    .ok_or_else(|| invalid(equation.node))?;
                    let initializer = Self::copy(&proof.nodes[initializer.0], work)?;
                    expression = proof.union(expression, &initializer, work)?;
                }
                EffectExprKind::Operation(EffectOperation::Resource(scope)) => {
                    let api = scope
                        .acquisition
                        .api()
                        .ok_or_else(|| invalid(equation.node))?;
                    charge(work, 1)?;
                    let effect = EffectInstance::new(
                        api.ops(),
                        Box::new([crate::types::Type::Variable(scope.acquisition.identity)]),
                    );
                    let body = recipe.node_equations
                        [scope.body().index().map_err(|_| invalid(equation.node))?]
                    .ok_or_else(|| invalid(equation.node))?;
                    let body = Self::copy(&proof.nodes[body.0], work)?;
                    expression = proof.remove(&body, &effect, true, work)?;
                    let initializer = recipe.node_equations[scope
                        .initializer()
                        .index()
                        .map_err(|_| invalid(equation.node))?]
                    .ok_or_else(|| invalid(equation.node))?;
                    let initializer = Self::copy(&proof.nodes[initializer.0], work)?;
                    expression = proof.union(expression, &initializer, work)?;
                }
                _ => {}
            }
            if let RowEquationOperation::Union {
                callable: Some(function),
            } = equation.operation
            {
                let function = node(program, function)?;
                if let Some(latent) = function.ty.function_view().and_then(|view| view.effects()) {
                    let latent = proof.row(latent, &identities, equation.node, work)?;
                    expression = proof.union(expression, &latent, work)?;
                }
            }
            proof.nodes.push(expression);
        }
        // A pending callable annotation is backed by its real function body,
        // not merely by the row identity also appearing in an Apply annotation.
        for (ordinal, equation) in recipe.nodes.iter().enumerate() {
            charge(work, 1)?;
            if let RowEquationOperation::Union {
                callable: Some(function),
            } = equation.operation
            {
                let function = node(program, function)?;
                if let Some(latent) = function.ty.function_view().and_then(|view| view.effects())
                    && latent.tail().is_some_and(|tail| {
                        matches!(tail.variable(), EffectRowVariable::Inference(_))
                    })
                {
                    let claimed = proof.row(latent, &identities, equation.node, work)?;
                    let mut actual = DemandExpression::default();
                    for body in &recipe.callable_bodies[ordinal] {
                        let body = Self::copy(&proof.nodes[body.0], work)?;
                        actual = proof.union(actual, &body, work)?;
                    }
                    charge(
                        work,
                        claimed
                            .atoms
                            .len()
                            .checked_add(actual.atoms.len())
                            .ok_or_else(resource)?,
                    )?;
                    if claimed.atoms != actual.atoms {
                        return Err(invalid(equation.node));
                    }
                }
            }
            if let EffectExprKind::Pure(PureExprKind::Value(PureValue::Function(function))) =
                &node(program, equation.node)?.kind
                && let Some(latent) = node(program, equation.node)?
                    .ty
                    .function_view()
                    .and_then(|view| view.effects())
                && latent
                    .tail()
                    .is_some_and(|tail| matches!(tail.variable(), EffectRowVariable::Inference(_)))
            {
                let claimed = proof.row(latent, &identities, equation.node, work)?;
                let body = recipe.node_equations[function
                    .body()
                    .index()
                    .map_err(|_| invalid(equation.node))?]
                .ok_or_else(|| invalid(equation.node))?;
                charge(
                    work,
                    claimed
                        .atoms
                        .len()
                        .checked_add(proof.nodes[body.0].atoms.len())
                        .ok_or_else(resource)?,
                )?;
                if claimed.atoms != proof.nodes[body.0].atoms {
                    return Err(invalid(equation.node));
                }
            }
        }
        let mut direct = DemandExpression::default();
        for clause in entry.draft.clauses {
            let equation = recipe.node_equations
                [clause.body().index().map_err(|_| invalid(clause.body()))?]
            .ok_or_else(|| invalid(clause.body()))?;
            let clause = Self::copy(&proof.nodes[equation.0], work)?;
            direct = proof.union(direct, &clause, work)?;
        }
        let claimed = proof.row(entry.draft.direct_demands, &identities, program.root, work)?;
        charge(
            work,
            direct
                .atoms
                .len()
                .checked_add(claimed.atoms.len())
                .ok_or_else(resource)?,
        )?;
        if direct.atoms != claimed.atoms {
            return Err(invalid(program.root));
        }
        proof.authenticate_annotations(recipe, entry, &identities, work)?;
        proof.authenticate_recomputations(recipe, entry, &identities, work)?;
        proof.authenticate_source_equalities(recipe, entry, work)?;
        proof.direct = direct;
        Ok(proof)
    }
}

/// A flat body-free demand vocabulary with recipe-local capture coordinates.
/// It contains no Core root and supplies no interpretation or completion fact.
#[derive(Debug)]
pub(super) struct HandlerDemandContract {
    atoms: Vec<DemandAtom>,
    direct: DemandExpression,
}
impl HandlerDemandContract {
    pub(super) fn visit_semantic_type_variables(
        &self,
        uses: &mut crate::core::validate::semantic_type_variables::UnusedVariables<'_>,
    ) -> Result<(), ()> {
        visit_atom_type_variables(&self.atoms, uses)
    }
    pub(super) fn realize(
        &self,
        types: &HashMap<crate::types::TypeVariableId, crate::types::Type>,
        rows: &HashMap<crate::types::TypeVariableId, EffectRow>,
        captures: &HashMap<CaptureInputId, EffectRow>,
        work: &mut TypeWorkBudget,
    ) -> Result<EffectRow, ValidationError> {
        // The full original recipe authenticates the capture domain first;
        // this body-free projection retains only the atoms reachable from D.
        let (direct, pending) = realize_demands(
            &self.atoms,
            &self.direct,
            &[],
            types,
            rows,
            captures,
            false,
            work,
        )?;
        if !pending.is_empty() {
            return Err(resource());
        }
        Ok(direct)
    }
}

impl DirectDemandProof {
    pub(super) fn visit_semantic_type_variables(
        &self,
        uses: &mut crate::core::validate::semantic_type_variables::UnusedVariables<'_>,
    ) -> Result<(), ()> {
        visit_atom_type_variables(&self.atoms, uses)
    }
}

fn visit_atom_type_variables(
    atoms: &[DemandAtom],
    uses: &mut crate::core::validate::semantic_type_variables::UnusedVariables<'_>,
) -> Result<(), ()> {
    uses.charge(atoms.len())?;
    for atom in atoms {
        match atom {
            DemandAtom::Ordinary(row) => uses.row(row)?,
            DemandAtom::Remove { effect, .. } => uses.instance(effect)?,
            DemandAtom::Capture(_) => {}
        }
    }
    Ok(())
}
impl DirectDemandProof {
    pub(super) fn defining_contract(
        &self,
        work: &mut TypeWorkBudget,
    ) -> Result<HandlerDemandContract, ValidationError> {
        // Retain only terms reachable from defining D. Intermediate local
        // callable rows remain in code/recipe, not the body-free contract.
        charge(work, self.atoms.len().checked_mul(2).ok_or_else(resource)?)?;
        let mut needed = Vec::new();
        needed
            .try_reserve_exact(self.atoms.len())
            .map_err(|_| resource())?;
        needed.resize(self.atoms.len(), false);
        let mut remap = Vec::new();
        remap
            .try_reserve_exact(self.atoms.len())
            .map_err(|_| resource())?;
        remap.resize(self.atoms.len(), None);
        let mut stack = Vec::new();
        charge(work, self.direct.atoms.len())?;
        stack
            .try_reserve_exact(self.direct.atoms.len())
            .map_err(|_| resource())?;
        stack.extend_from_slice(&self.direct.atoms);
        while let Some(id) = stack.pop() {
            charge(work, 1)?;
            let slot = needed.get_mut(id.0).ok_or_else(resource)?;
            if std::mem::replace(slot, true) {
                continue;
            }
            if let DemandAtom::Remove { input, .. } = self.atoms.get(id.0).ok_or_else(resource)? {
                charge(work, 1)?;
                stack.try_reserve(1).map_err(|_| resource())?;
                stack.push(*input);
            }
        }
        let mut atoms = Vec::new();
        for (ordinal, atom) in self.atoms.iter().enumerate() {
            charge(work, 1)?;
            if !needed[ordinal] {
                continue;
            }
            charge(work, 1)?;
            atoms.try_reserve(1).map_err(|_| resource())?;
            let copied = match atom {
                DemandAtom::Ordinary(row) => DemandAtom::Ordinary(
                    clone_effect_row_with_budget(row, work).map_err(|()| resource())?,
                ),
                DemandAtom::Capture(input) => DemandAtom::Capture(*input),
                DemandAtom::Remove {
                    input,
                    effect,
                    absent,
                } => DemandAtom::Remove {
                    input: remap.get(input.0).copied().flatten().ok_or_else(resource)?,
                    effect: clone_effect_instance_with_budget(effect, work)
                        .map_err(|()| resource())?,
                    absent: *absent,
                },
            };
            remap[ordinal] = Some(DemandAtomId(atoms.len()));
            atoms.push(copied);
        }
        let mut direct = DemandExpression::default();
        charge(work, self.direct.atoms.len())?;
        direct
            .atoms
            .try_reserve_exact(self.direct.atoms.len())
            .map_err(|_| resource())?;
        for id in &self.direct.atoms {
            direct
                .atoms
                .push(remap.get(id.0).copied().flatten().ok_or_else(resource)?);
        }
        Ok(HandlerDemandContract { atoms, direct })
    }
}

#[cfg(test)]
impl DirectDemandProof {
    pub(super) fn assert_retained_contract(&self, contract: &HandlerDemandContract) {
        let expected = self
            .defining_contract(&mut TypeWorkBudget::unbounded())
            .unwrap();
        assert_eq!(contract.atoms, expected.atoms);
        assert_eq!(contract.direct, expected.direct);
    }
}
