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
                        | RowEquationOperation::CopyWindow
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
                        charge(work, 1)?;
                        let host = program
                            .registry
                            .native_symbol(request.operation())
                            .map(|symbol| {
                                crate::foreign::checked_source::checked_host_instance(
                                    symbol, &effect, work,
                                )
                            })
                            .transpose()
                            .map_err(|failure| {
                                if failure.is_resource_exhaustion() {
                                    resource()
                                } else {
                                    invalid(equation.node)
                                }
                            })?
                            .flatten();
                        let requested = crate::types::rebuild_effect_row_with_budget(
                            std::iter::once(&effect).chain(host.iter()),
                            None,
                            std::iter::empty(),
                            crate::types::clone_type_with_budget,
                            work,
                        )
                        .map_err(|()| resource())?;
                        row = union(&row, &requested, work)?;
                    }
                    RowEquationOperation::CopyWindow => {
                        let EffectExprKind::Operation(EffectOperation::SourceCopyWindow(scope)) =
                            &stored.kind
                        else {
                            return Err(invalid(equation.node));
                        };
                        charge(
                            work,
                            scope
                                .interpretations()
                                .len()
                                .checked_add(2)
                                .ok_or_else(resource)?,
                        )?;
                        let body = self
                            .node_equations
                            .get(scope.body().index().map_err(|_| invalid(equation.node))?)
                            .copied()
                            .flatten()
                            .ok_or_else(|| invalid(equation.node))?;
                        let mut body = copy(&values[body.0], work)?;
                        for interpretation in scope.interpretations() {
                            let actual = instance(interpretation.effect(), work)?;
                            body = remove(&body, &actual, true, work)?;
                        }
                        if !body.is_empty() {
                            return Err(invalid(equation.node));
                        }
                        let state = self
                            .node_equations
                            .get(scope.state().index().map_err(|_| invalid(equation.node))?)
                            .copied()
                            .flatten()
                            .ok_or_else(|| invalid(equation.node))?;
                        row = copy(&values[state.0], work)?;
                    }
                    RowEquationOperation::NativeInterpret => {
                        let EffectExprKind::Operation(EffectOperation::NativeInterpret(boundary)) =
                            &stored.kind
                        else {
                            return Err(invalid(equation.node));
                        };
                        if boundary.host().is_some() {
                            return Err(invalid(equation.node));
                        }
                        charge(work, boundary.interpretations().len())?;
                        for interpretation in boundary.interpretations() {
                            let actual = instance(interpretation.effect(), work)?;
                            row = remove(&row, &actual, true, work)?;
                        }
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
                        let effect =
                            scope
                                .instance_with_budget(work)
                                .map_err(|error| match error {
                                    crate::core::BuildError::TypeWorkExceeded => {
                                        super::super::resource()
                                    }
                                    _ => invalid(equation.node),
                                })?;
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::core::{
        ResumeUse, ValidationReason,
        dialect::StoredNode,
        effect::DiscardNode,
        provider::row::{NodeRowEquation, RowEquationId},
    };
    use std::{fs, path::PathBuf, sync::Arc};

    struct Fixture(PathBuf);
    impl Drop for Fixture {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.0);
        }
    }

    #[test]
    fn source_control_copy_window_rows_keep_state_and_refuse_unhandled_body() {
        let fixture = Fixture(
            std::env::temp_dir().join(format!("ash-copy-window-row-{}", std::process::id())),
        );
        fs::create_dir(&fixture.0).unwrap();
        fs::write(
            fixture.0.join("owner.ash"),
            include_str!("../../../../libraries/sqlite.ash"),
        )
        .unwrap();
        fs::write(fixture.0.join("entry.ash"), "import owner as Sqlite\nmain : Unit -> Sqlite.Scope<Sqlite.OpenError, Sqlite.CloseError, Bool> ! {Sqlite.Initialize}\nmain () = resource Sqlite.Connection<C> connection = Sqlite.InMemory {\n    true\n}\n").unwrap();
        let compiled = crate::driver::compile_path(crate::driver::RunConfiguration {
            entry: fixture.0.join("entry.ash"),
            roots: crate::module::ModuleRoots::empty(),
        })
        .unwrap();
        let (checked, _) = compiled.effect_build_input().unwrap();
        let original = checked
            .nodes()
            .iter()
            .find_map(|node| match &node.kind {
                EffectExprKind::Operation(EffectOperation::SourceResourceScope(scope)) => {
                    Some(scope.original())
                }
                _ => None,
            })
            .unwrap();
        let source = original.original_handler();
        let (stored, window) = source
            .nodes
            .iter()
            .find_map(|node| match &node.kind {
                EffectExprKind::Operation(EffectOperation::SourceCopyWindow(window))
                    if !window.interpretations().is_empty() =>
                {
                    Some((node, window))
                }
                _ => None,
            })
            .unwrap();
        let native = window.interpretations()[0].effect();
        let mut work = TypeWorkBudget::default();
        let body = EffectRow::singleton(
            crate::types::clone_effect_instance_with_budget(native, &mut work).unwrap(),
        );
        let state = EffectRow::with_tail(
            Box::new([crate::types::clone_effect_instance_with_budget(native, &mut work).unwrap()]),
            crate::types::EffectRowVariable::rigid(original.handler_continuation()),
            Box::new([]),
        );
        let state_id = NodeId::new(source.arena, 0);
        let body_id = NodeId::new(source.arena, 1);
        let window_id = NodeId::new(source.arena, 2);
        let handler = original.original_handler_node();
        let leaf = || StoredNode {
            dialect: stored.dialect,
            ty: Type::Unit,
            effects: EffectRow::empty(),
            origin: stored.origin.clone(),
            kind: EffectExprKind::Operation(EffectOperation::Discard(DiscardNode::new(
                handler.id(),
                handler.clauses()[0].resume(),
                ResumeUse::Available,
            ))),
        };
        let mut window = window.clone();
        window.state = state_id;
        window.body = body_id;
        let program = crate::core::UnvalidatedEffectProgram {
            registry: Arc::clone(&source.registry),
            method_evidence: Arc::clone(&source.method_evidence),
            method_evidence_anchors: Box::new([]),
            arena: source.arena,
            nodes: vec![
                leaf(),
                leaf(),
                StoredNode {
                    dialect: stored.dialect,
                    ty: Type::Unit,
                    effects: EffectRow::empty(),
                    origin: stored.origin.clone(),
                    kind: EffectExprKind::Operation(EffectOperation::SourceCopyWindow(window)),
                },
            ],
            root: window_id,
        };
        // Isolate the row engine using two explicit actual capture inputs and
        // the descriptor from the admitted original. This arena is not offered
        // as executable Core or as a new source-window authority.
        let recipe = HandlerRowRecipeDraft {
            template: crate::resolved::ProviderTemplateId::new(original.header().original.id, 2),
            nodes: vec![
                NodeRowEquation {
                    node: state_id,
                    operation: RowEquationOperation::Discard {
                        capture: CaptureInputId(0),
                    },
                    inputs: 0..0,
                },
                NodeRowEquation {
                    node: body_id,
                    operation: RowEquationOperation::Discard {
                        capture: CaptureInputId(1),
                    },
                    inputs: 0..0,
                },
                NodeRowEquation {
                    node: window_id,
                    operation: RowEquationOperation::CopyWindow,
                    inputs: 0..2,
                },
            ],
            edges: vec![RowEquationId(0), RowEquationId(1)],
            outputs: Vec::new(),
            discards: Vec::new(),
            node_equations: vec![
                Some(RowEquationId(0)),
                Some(RowEquationId(1)),
                Some(RowEquationId(2)),
            ],
            positions: Vec::new(),
            callable_bodies: vec![Vec::new(), Vec::new(), Vec::new()],
            latent_bodies: vec![Vec::new(), Vec::new(), Vec::new()],
            direct: None,
        };
        let realize = |body: &EffectRow, work: &mut TypeWorkBudget| {
            let captures = HashMap::from([
                (
                    CaptureInputId(0),
                    copy(&state, &mut TypeWorkBudget::default()).unwrap(),
                ),
                (
                    CaptureInputId(1),
                    copy(body, &mut TypeWorkBudget::default()).unwrap(),
                ),
            ]);
            recipe.realize_nodes(
                &program,
                &HashMap::new(),
                &HashMap::new(),
                &HashMap::new(),
                &captures,
                &EffectRow::empty(),
                work,
            )
        };
        let realized = realize(&body, &mut work).unwrap();
        assert!(
            same_effect_rows_with_budget(&realized.nodes[&window_id], &state, &mut work).unwrap()
        );
        // A different native instance, an ordinary request and a rigid tail
        // cannot be hidden by the descriptor's one exact interpretation.
        let other_native = EffectRow::singleton(
            crate::types::clone_effect_instance_with_budget(
                &original.header().original.interpreted[0].instance,
                &mut work,
            )
            .unwrap(),
        );
        let ordinary = EffectRow::singleton(
            crate::types::clone_effect_instance_with_budget(
                &original.header().original.provided.instance,
                &mut work,
            )
            .unwrap(),
        );
        let open = EffectRow::with_tail(
            Box::new([crate::types::clone_effect_instance_with_budget(native, &mut work).unwrap()]),
            crate::types::EffectRowVariable::rigid(original.handler_continuation()),
            Box::new([]),
        );
        for invalid in [&other_native, &ordinary, &open] {
            let error = realize(invalid, &mut TypeWorkBudget::default())
                .err()
                .unwrap();
            assert_eq!(error.reason(), ValidationReason::ResourceEscape);
            assert_eq!(error.node(), Some(window_id));
        }
        let mut measured = TypeWorkBudget::default();
        realize(&body, &mut measured).unwrap();
        let cost = measured.used();
        for prefix in [0, 13] {
            let mut exact = TypeWorkBudget::with_limit(prefix + cost);
            exact.charge(prefix).unwrap();
            realize(&body, &mut exact).unwrap();
            assert_eq!(exact.used(), prefix + cost);
            let mut short = TypeWorkBudget::with_limit(prefix + cost - 1);
            short.charge(prefix).unwrap();
            assert_eq!(
                realize(&body, &mut short).err().unwrap().reason(),
                ValidationReason::Resource
            );
        }
    }
}
