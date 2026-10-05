//! Realization of the authenticated node and handler equations.
use super::{CaptureInputId, HandlerOutputOwner, HandlerRowRecipeDraft, RowEquationOperation};
use crate::core::{EffectExprKind, EffectOperation, HandlerId, NodeId};
use crate::types::{
    EffectInstance, EffectRow, EffectRowError, InferenceVariableId, Type, TypeVariableId,
    TypeWorkBudget, clone_effect_row_with_budget, same_effect_rows_with_budget,
};
use std::collections::HashMap;

pub(in crate::core) struct RealizedHandlerRows {
    pub(in crate::core) nodes: HashMap<NodeId, EffectRow>,
    pub(in crate::core) handlers: HashMap<HandlerId, EffectRow>,
}
fn union(
    left: &EffectRow,
    right: &EffectRow,
    work: &mut TypeWorkBudget,
) -> Result<EffectRow, super::super::ValidationError> {
    left.union_with_budget(right, work)
        .map_err(|()| super::super::resource())?
        .map_err(|_| {
            super::super::ValidationError::new(crate::core::ValidationReason::EffectRow, None)
        })
}
fn copy(
    row: &EffectRow,
    work: &mut TypeWorkBudget,
) -> Result<EffectRow, super::super::ValidationError> {
    clone_effect_row_with_budget(row, work).map_err(|()| super::super::resource())
}
fn remove(
    row: &EffectRow,
    effect: &EffectInstance,
    allow_absent: bool,
    work: &mut TypeWorkBudget,
) -> Result<EffectRow, super::super::ValidationError> {
    match row
        .remove_exact_with_budget(effect, work)
        .map_err(|()| super::super::resource())?
    {
        Ok(row) => Ok(row),
        Err(EffectRowError::Missing) if allow_absent => copy(row, work),
        Err(_) => Err(super::super::ValidationError::new(
            crate::core::ValidationReason::EffectRow,
            None,
        )),
    }
}
impl HandlerRowRecipeDraft {
    #[allow(clippy::too_many_arguments)] // Independent source, actual and work authorities stay explicit.
    pub(in crate::core) fn realize_nodes(
        &self,
        program: &super::super::UnvalidatedEffectProgram,
        types: &HashMap<TypeVariableId, Type>,
        rows: &HashMap<TypeVariableId, EffectRow>,
        pending: &HashMap<InferenceVariableId, EffectRow>,
        captures: &HashMap<CaptureInputId, EffectRow>,
        outer: &EffectRow,
        work: &mut TypeWorkBudget,
    ) -> Result<RealizedHandlerRows, super::super::ValidationError> {
        use super::super::{charge, invalid, node, resource};
        let instantiate = |row: &EffectRow, work: &mut TypeWorkBudget| {
            crate::types::substitute_effect_and_template_rows_with(
                row,
                types,
                rows,
                pending,
                |cells| work.charge(cells),
                || (),
            )
            .map_err(|()| resource())?
            .map_err(|_| invalid(program.root))
        };
        let instance = |effect: &EffectInstance, work: &mut TypeWorkBudget| {
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
                let actual = crate::types::substitute_argument_and_template_rows_with(
                    argument,
                    types,
                    rows,
                    pending,
                    |cells| work.charge(cells),
                    || (),
                )
                .map_err(|()| resource())?
                .map_err(|_| invalid(program.root))?;
                arguments.push(crate::types::IterativeArgumentOwner::new(actual));
            }
            let mut result = Vec::new();
            result
                .try_reserve_exact(arguments.len())
                .map_err(|_| resource())?;
            result.extend(
                arguments
                    .into_iter()
                    .map(crate::types::IterativeArgumentOwner::into_inner),
            );
            Ok::<_, super::super::ValidationError>(EffectInstance::new_kinded(
                effect.effect(),
                result.into_boxed_slice(),
            ))
        };
        charge(
            work,
            self.nodes
                .len()
                .checked_add(self.outputs.len())
                .ok_or_else(resource)?,
        )?;
        let mut values = Vec::new();
        values
            .try_reserve_exact(self.nodes.len())
            .map_err(|_| resource())?;
        values.resize_with(self.nodes.len(), EffectRow::empty);
        let mut outputs = Vec::new();
        outputs
            .try_reserve_exact(self.outputs.len())
            .map_err(|_| resource())?;
        for output in &self.outputs {
            outputs.push(match output.owner {
                HandlerOutputOwner::ProviderEntry { .. } => copy(outer, work)?,
                HandlerOutputOwner::Nested { .. } => EffectRow::empty(),
            });
        }
        loop {
            let mut changed = false;
            for (ordinal, equation) in self.nodes.iter().enumerate() {
                charge(work, 1)?;
                let stored = node(program, equation.node)?;
                let mut row = EffectRow::empty();
                if !matches!(
                    equation.operation,
                    RowEquationOperation::Empty
                        | RowEquationOperation::Handler { .. }
                        | RowEquationOperation::ProviderScope { .. }
                ) {
                    for input in &self.edges[equation.inputs.clone()] {
                        row = union(&row, &values[input.0], work)?;
                    }
                }
                match equation.operation {
                    RowEquationOperation::Resume { output } => {
                        row = union(&row, &outputs[output.0], work)?;
                    }
                    RowEquationOperation::Discard { capture } => {
                        row = copy(
                            captures
                                .get(&capture)
                                .ok_or_else(|| invalid(equation.node))?,
                            work,
                        )?;
                    }
                    RowEquationOperation::Request => {
                        let EffectExprKind::Operation(EffectOperation::Request(request)) =
                            &stored.kind
                        else {
                            return Err(invalid(equation.node));
                        };
                        let effect = instance(request.effect(), work)?;
                        let requested = crate::types::rebuild_effect_row_with_budget(
                            std::iter::once(&effect),
                            None,
                            std::iter::empty(),
                            crate::types::clone_type_with_budget,
                            work,
                        )
                        .map_err(|()| resource())?;
                        row = union(&row, &requested, work)?;
                    }
                    RowEquationOperation::Handler { output } => {
                        row = copy(&outputs[output.0], work)?;
                    }
                    RowEquationOperation::ProviderScope { .. } => {
                        return Err(invalid(equation.node));
                    }
                    RowEquationOperation::Resource => {
                        let EffectExprKind::Operation(EffectOperation::Resource(scope)) =
                            &stored.kind
                        else {
                            return Err(invalid(equation.node));
                        };
                        let api = scope
                            .acquisition
                            .api()
                            .ok_or_else(|| invalid(equation.node))?;
                        charge(work, 2)?;
                        let effect = EffectInstance::new(
                            api.ops(),
                            Box::new([Type::Variable(scope.acquisition.identity)]),
                        );
                        let body = self.node_equations
                            [scope.body.index().map_err(|_| invalid(equation.node))?]
                        .ok_or_else(|| invalid(equation.node))?;
                        let initializer = self.node_equations[scope
                            .initializer
                            .index()
                            .map_err(|_| invalid(equation.node))?]
                        .ok_or_else(|| invalid(equation.node))?;
                        row = union(
                            &remove(&values[body.0], &effect, true, work)?,
                            &values[initializer.0],
                            work,
                        )?;
                    }
                    RowEquationOperation::Union {
                        callable: Some(function),
                    } => {
                        if self.callable_bodies[ordinal].is_empty() {
                            if let Some(latent) = node(program, function)?
                                .ty
                                .function_view()
                                .and_then(|view| view.effects())
                            {
                                row = union(&row, &instantiate(latent, work)?, work)?;
                            }
                        } else {
                            for body in &self.callable_bodies[ordinal] {
                                row = union(&row, &values[body.0], work)?;
                            }
                        }
                    }
                    _ => {}
                }
                changed |= !same_effect_rows_with_budget(&row, &values[ordinal], work)
                    .map_err(|()| resource())?;
                values[ordinal] = row;
            }
            for (ordinal, output) in self.outputs.iter().enumerate() {
                let HandlerOutputOwner::Nested { node: id, .. } = output.owner else {
                    continue;
                };
                let EffectExprKind::Operation(EffectOperation::Handler(handler)) =
                    &node(program, id)?.kind
                else {
                    return Err(invalid(id));
                };
                let body = output.body.ok_or_else(|| invalid(id))?;
                let effect = instance(handler.effect(), work)?;
                let mut row = remove(
                    &values[body.0],
                    &effect,
                    handler.hook_root().is_some() || handler.hook_registration.is_some(),
                    work,
                )?;
                for clause in &output.clauses {
                    row = union(&row, &values[clause.0], work)?;
                }
                changed |= !same_effect_rows_with_budget(&row, &outputs[ordinal], work)
                    .map_err(|()| resource())?;
                outputs[ordinal] = row;
            }
            if !changed {
                break;
            }
        }
        // Each callable's stored latent row must correspond to its actual body.
        // A changed row needs an explicit metadata realization rather than an
        // unchecked row-only copy. Such metadata is never silently accepted.
        for (ordinal, equation) in self.nodes.iter().enumerate() {
            if self.latent_bodies[ordinal].is_empty() {
                continue;
            }
            let stored = node(program, equation.node)?;
            let Some(view) = stored.ty.function_view() else {
                return Err(invalid(equation.node));
            };
            let mut actual = EffectRow::empty();
            for body in &self.latent_bodies[ordinal] {
                actual = union(&actual, &values[body.0], work)?;
            }
            let claimed = match view.effects() {
                Some(row) => instantiate(row, work)?,
                None => EffectRow::empty(),
            };
            if !same_effect_rows_with_budget(&actual, &claimed, work).map_err(|()| resource())? {
                return Err(invalid(equation.node));
            }
        }
        charge(
            work,
            self.nodes
                .len()
                .checked_add(self.outputs.len())
                .ok_or_else(resource)?,
        )?;
        let mut nodes = HashMap::new();
        nodes
            .try_reserve(self.nodes.len())
            .map_err(|_| resource())?;
        for (equation, row) in self.nodes.iter().zip(values) {
            if nodes.insert(equation.node, row).is_some() {
                return Err(invalid(equation.node));
            }
        }
        let mut handlers = HashMap::new();
        handlers
            .try_reserve(self.outputs.len())
            .map_err(|_| resource())?;
        for (output, row) in self.outputs.iter().zip(outputs) {
            let handler = match output.owner {
                HandlerOutputOwner::ProviderEntry { handler, .. }
                | HandlerOutputOwner::Nested { handler, .. } => handler,
            };
            if handlers.insert(handler, row).is_some() {
                return Err(invalid(program.root));
            }
        }
        Ok(RealizedHandlerRows { nodes, handlers })
    }
}
