//! Conditional rows of an immutable product source handler.
//!
//! Source inputs are claims. The complete clause graph and private callback
//! wrapper are reconstructed before any provisional position is admitted.

use super::{
    CheckedSourceResourceHeader, EffectExprKind, EffectOperation, Kind, NodeId, PureComputation,
    PureExprKind, PureValue, Type, TypeWorkBudget, TypedBinder, UnvalidatedEffectProgram,
    ValidationError, charge, entry, invalid, node, resource,
};
use crate::{
    core::provider::{
        HandlerGraph, HandlerGraphDraft, HandlerGraphView, HandlerPendingRows,
        HandlerRowRecipeDraft,
    },
    types::{EffectRow, TypeVariableId, same_effect_rows_with_budget},
};

#[derive(Debug)]
pub(crate) struct SourceHandlerRowInputs {
    pub(crate) direct: EffectRow,
    pub(crate) pending: HandlerPendingRows,
}

pub(super) struct SourceHandlerRows {
    pub(super) inputs: SourceHandlerRowInputs,
    pub(super) recipe: HandlerRowRecipeDraft,
    pub(super) capture: crate::core::capture::ConditionalCaptureGraph,
}

impl std::fmt::Debug for SourceHandlerRows {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("SourceHandlerRows")
            .field("inputs", &self.inputs)
            .field("recipe", &self.recipe)
            .finish_non_exhaustive()
    }
}

/// An authenticated original wrapper, still not executable Core authority.
pub(in crate::core) struct SourceHandlerGraph<'a> {
    program: &'a UnvalidatedEffectProgram,
    header: &'a CheckedSourceResourceHeader,
    inputs: &'a SourceHandlerRowInputs,
    state: TypedBinder,
    hidden: [(TypeVariableId, Kind); 2],
    roots: Vec<NodeId>,
    pattern_binders: Vec<crate::resolved::BinderId>,
    wrapper: NodeId,
    pub(super) recipe: Option<&'a HandlerRowRecipeDraft>,
}

impl<'a> SourceHandlerGraph<'a> {
    pub(super) fn reconstruct(
        program: &'a UnvalidatedEffectProgram,
        header: &'a CheckedSourceResourceHeader,
        inputs: &'a SourceHandlerRowInputs,
        work: &mut TypeWorkBudget,
    ) -> Result<Self, ValidationError> {
        if !program
            .registry
            .source_resource_fact(header.original.id)
            .is_some_and(|registered| std::sync::Arc::ptr_eq(registered, &header.original))
        {
            return Err(invalid());
        }
        let (state, answer_function) = entry(program, &header.original, true, work)?;
        let EffectExprKind::Pure(PureExprKind::Value(PureValue::Function(answer))) =
            &node(program, answer_function)?.kind
        else {
            return Err(invalid());
        };
        let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Match(matching))) =
            &node(program, answer.body())?.kind
        else {
            return Err(invalid());
        };
        if matching.arms().len() != 1 {
            return Err(invalid());
        }
        let wrapper = matching.arms()[0].body();
        let EffectExprKind::Operation(EffectOperation::Handler(handler)) =
            &node(program, wrapper)?.kind
        else {
            return Err(invalid());
        };
        let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Apply(application))) =
            &node(program, handler.body())?.kind
        else {
            return Err(invalid());
        };
        let EffectExprKind::Pure(PureExprKind::Variable(callback)) =
            &node(program, application.function())?.kind
        else {
            return Err(invalid());
        };
        let view = answer
            .parameter()
            .ty()
            .function_view()
            .ok_or_else(invalid)?;
        let callback_row = view.effects().ok_or_else(invalid)?;
        let continuation = super::CheckedSourceResourceTemplate::handler_continuation_in(program);
        if callback.binder() != answer.parameter().id()
            || !matches!(
                &node(program, application.argument())?.kind,
                EffectExprKind::Pure(PureExprKind::Value(PureValue::Unit(_)))
            )
            || !super::same(view.domain(), &Type::Unit, work)?
            || !super::variable(view.value(), header.original.answer.id)
            || handler.has_hook_contracts()
            || crate::types::compare_effect_instances_with_budget(
                handler.effect(),
                &header.original.provided.instance,
                work,
            )
            .map_err(|_| resource())?
                != std::cmp::Ordering::Equal
            || !callback_row.tail().is_some_and(|tail| {
                tail.variable() == crate::types::EffectRowVariable::rigid(continuation)
            })
        {
            return Err(invalid());
        }
        let residual = callback_row
            .remove_exact_with_budget(&header.original.provided.instance, work)
            .map_err(|_| resource())?
            .map_err(|_| invalid())?;
        if !residual.known().is_empty()
            || !same_effect_rows_with_budget(&residual, &node(program, wrapper)?.effects, work)
                .map_err(|_| resource())?
        {
            return Err(invalid());
        }
        let mut roots = Vec::new();
        charge(work, handler.clauses().len())?;
        roots
            .try_reserve_exact(handler.clauses().len())
            .map_err(|_| resource())?;
        roots.extend(
            handler
                .clauses()
                .iter()
                .map(crate::core::EffectClause::body),
        );
        if roots.is_empty() {
            return Err(invalid());
        }
        let mut pattern_binders = Vec::new();
        for binder in matching.arms()[0].pattern().binder_iter() {
            super::push(&mut pattern_binders, binder.id(), work)?;
        }
        Ok(Self {
            program,
            header,
            inputs,
            state,
            hidden: [
                (header.original.answer.id, Kind::Type),
                (continuation, Kind::EffectRow),
            ],
            roots,
            pattern_binders,
            wrapper,
            recipe: None,
        })
    }

    pub(in crate::core) fn authenticates(
        &self,
        program: &UnvalidatedEffectProgram,
        original: &std::sync::Arc<crate::resolved::SourceResourceTypeFact>,
    ) -> bool {
        std::ptr::eq(self.program, program)
            && std::sync::Arc::ptr_eq(&self.header.original, original)
            && self.recipe.is_some()
    }

    pub(in crate::core) fn wrapper(&self) -> NodeId {
        self.wrapper
    }
}

impl HandlerGraph for SourceHandlerGraph<'_> {
    fn handler_graph(&self) -> HandlerGraphView<'_> {
        let EffectExprKind::Operation(EffectOperation::Handler(handler)) =
            &self.program.nodes[self.wrapper.value() as usize].kind
        else {
            unreachable!("independently reconstructed source handler wrapper")
        };
        HandlerGraphView {
            draft: HandlerGraphDraft {
                program: self.program,
                template: crate::resolved::ProviderTemplateId::new(self.header.original.id, 2),
                handler: handler.id(),
                state: &self.state,
                hidden: &self.hidden,
                clauses: handler.clauses(),
                direct_demands: &self.inputs.direct,
                pending_rows: &self.inputs.pending,
            },
            canonical: &self.program.registry,
            row_recipe: self.recipe,
            roots: &self.roots,
            wrapper_root: Some(self.program.root),
            pattern_binders: &self.pattern_binders,
            provided: &self.header.original.provided.instance,
        }
    }
}

impl super::CheckedSourceResourceTemplate {
    #[cfg(test)]
    pub(in crate::core) fn reconstructed_handler_graph_for_test(
        &self,
        work: &mut TypeWorkBudget,
    ) -> Result<SourceHandlerGraph<'_>, ValidationError> {
        let rows = self.handler_rows.as_ref().ok_or_else(invalid)?;
        let mut graph =
            SourceHandlerGraph::reconstruct(&self.handler, &self.header, &rows.inputs, work)?;
        graph.recipe = Some(&rows.recipe);
        Ok(graph)
    }

    pub(crate) fn original_handler_inputs(&self) -> Option<&SourceHandlerRowInputs> {
        self.handler_rows.as_ref().map(|rows| &rows.inputs)
    }

    /// Passive image claims are subjected to the same complete independent
    /// request and row reconstruction as compiler-authored instance claims.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn restore_row_claim(
        &self,
        rows: [EffectRow; 4],
        pending: std::collections::HashMap<crate::types::InferenceVariableId, EffectRow>,
        node_rows: std::collections::HashMap<NodeId, EffectRow>,
        handler_outputs: std::collections::HashMap<crate::core::HandlerId, EffectRow>,
        captures: crate::core::capture::ActualCaptureInputs,
        work: &mut TypeWorkBudget,
    ) -> Result<crate::core::provider::ResolvedProviderHandlerRows, ValidationError> {
        let [direct, epsilon, output, residual] = rows;
        if !same_effect_rows_with_budget(&epsilon, &residual, work).map_err(|_| resource())? {
            return Err(invalid());
        }
        crate::core::provider::ResolvedProviderHandlerRows::from_source_solution(
            self.handler.arena,
            [direct, epsilon, output],
            pending,
            node_rows,
            handler_outputs,
            captures,
            work,
        )
    }

    pub(in crate::core) fn conditional_capture_graph(
        &self,
    ) -> Option<(
        &crate::core::capture::ConditionalCaptureGraph,
        &super::UnvalidatedEffectProgram,
    )> {
        self.handler_rows
            .as_ref()
            .map(|rows| (&rows.capture, &self.handler))
    }

    pub(crate) fn has_conditional_handler_rows(&self) -> bool {
        self.handler_rows.is_some()
    }

    pub(crate) fn handler_row_count(
        &self,
        work: &mut TypeWorkBudget,
    ) -> Result<usize, ValidationError> {
        let original = self.handler_rows.as_ref().ok_or_else(invalid)?;
        charge(work, 1)?;
        let (nodes, handlers) = original.recipe.deferred_copy_counts();
        original
            .inputs
            .pending
            .equations
            .len()
            .checked_add(nodes)
            .and_then(|n| n.checked_add(handlers))
            .and_then(|n| n.checked_add(2))
            .ok_or_else(resource)
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn prepare_instance_rows<F: crate::core::dialect::CoreOperationFamily>(
        &self,
        builder: &crate::core::CoreBuilder<F>,
        scope: NodeId,
        globals: &[(crate::resolved::BinderId, NodeId)],
        imports: &[(
            crate::resolved::BinderId,
            &crate::core::capture::CaptureValueSummary,
        )],
        methods: &[crate::core::capture::MethodUse],
        adapters: &[crate::core::capture::MethodAdapter],
        operation: fn(&F::Kind) -> Option<&EffectOperation>,
        types: &std::collections::HashMap<TypeVariableId, Type>,
        rows: &std::collections::HashMap<TypeVariableId, EffectRow>,
        answer: &Type,
        body: &EffectRow,
        provided: &crate::types::EffectInstance,
        work: &mut TypeWorkBudget,
    ) -> Result<crate::core::provider::ResolvedProviderHandlerRows, ValidationError> {
        let capture = crate::core::capture::prepare_actual_source_captures(
            builder, scope, globals, imports, methods, adapters, operation, work,
        )
        .map_err(|failure| match failure {
            crate::core::capture::Failure::Resource => resource(),
            _ => invalid(),
        })?;
        self.realize_handler_rows(types, rows, answer, body, provided, Some(capture), work)
    }

    /// Fresh source inference positions in the independently reconstructed
    /// original domain. Callers register every position in the existing owner.
    pub(crate) fn defer_handler_rows(
        &self,
        allocate: impl FnMut() -> Option<EffectRow>,
        work: &mut TypeWorkBudget,
    ) -> Result<crate::core::provider::DeferredProviderHandlerRows, ValidationError> {
        let original = self.handler_rows.as_ref().ok_or_else(invalid)?;
        let (nodes, handlers) = original.recipe.deferred_copy_domain(work)?;
        let mut pending = Vec::new();
        charge(work, original.inputs.pending.equations.len())?;
        pending
            .try_reserve_exact(original.inputs.pending.equations.len())
            .map_err(|_| resource())?;
        pending.extend(original.inputs.pending.identities());
        crate::core::provider::DeferredProviderHandlerRows::from_domain(
            self.handler.arena,
            &pending,
            &nodes,
            &handlers,
            allocate,
            work,
        )
    }

    /// Realizes the immutable original equations only after actual capture
    /// inputs and the completed client row are available. The returned rows
    /// remain compiler claims until independent copied-scope admission.
    #[allow(clippy::too_many_arguments)]
    pub(in crate::core) fn realize_handler_rows(
        &self,
        types: &std::collections::HashMap<TypeVariableId, Type>,
        rows: &std::collections::HashMap<TypeVariableId, EffectRow>,
        answer: &Type,
        body: &EffectRow,
        provided: &crate::types::EffectInstance,
        captures: Option<crate::core::capture::ActualCaptureInputs>,
        work: &mut TypeWorkBudget,
    ) -> Result<crate::core::provider::ResolvedProviderHandlerRows, ValidationError> {
        use std::collections::HashMap;
        let original = self.handler_rows.as_ref().ok_or_else(invalid)?;
        let template = crate::resolved::ProviderTemplateId::new(self.header.original.id, 2);
        if types.contains_key(&self.header.original.answer.id)
            || rows.contains_key(&self.handler_continuation())
        {
            return Err(invalid());
        }
        let captures = match captures {
            Some(captures) => captures,
            None if original.recipe.discards().is_empty() => {
                crate::core::capture::ActualCaptureInputs::empty(template)
            }
            None => return Err(invalid()),
        };
        charge(work, 1)?;
        if captures.template() != template
            || captures.rows().len() != original.recipe.discards().len()
        {
            return Err(invalid());
        }
        let (direct, solved) =
            original
                .recipe
                .realize_direct(types, rows, captures.rows(), work)?;
        if solved.len() != original.inputs.pending.equations.len() {
            return Err(invalid());
        }
        let mut pending = HashMap::new();
        charge(work, solved.len())?;
        pending.try_reserve(solved.len()).map_err(|_| resource())?;
        for (id, row) in original.inputs.pending.identities().zip(solved) {
            if pending.insert(id, row).is_some() {
                return Err(invalid());
            }
        }
        let expected_direct = crate::types::substitute_effect_and_template_rows_with(
            &original.inputs.direct,
            types,
            rows,
            &pending,
            |cells| charge(work, cells),
            resource,
        )?
        .map_err(|_| invalid())?;
        if !same_effect_rows_with_budget(&expected_direct, &direct, work).map_err(|_| resource())? {
            return Err(invalid());
        }
        let epsilon = match body
            .remove_exact_with_budget(provided, work)
            .map_err(|_| resource())?
        {
            Ok(row) => row,
            Err(crate::types::EffectRowError::Missing) => {
                crate::types::clone_effect_row_with_budget(body, work).map_err(|_| resource())?
            }
            Err(_) => return Err(invalid()),
        };
        let output = direct
            .union_with_budget(&epsilon, work)
            .map_err(|_| resource())?
            .map_err(|failure| ValidationError::row_union_failure(failure, None))?;
        let mut complete_types = super::TypesGuard(HashMap::new());
        charge(
            work,
            types
                .len()
                .checked_add(rows.len())
                .and_then(|count| count.checked_add(2))
                .ok_or_else(resource)?,
        )?;
        complete_types
            .0
            .try_reserve(types.len() + 1)
            .map_err(|_| resource())?;
        let mut complete_rows = HashMap::new();
        complete_rows
            .try_reserve(rows.len() + 1)
            .map_err(|_| resource())?;
        for (id, ty) in types {
            complete_types.insert(
                *id,
                crate::types::clone_type_with_budget(ty, work).map_err(|_| resource())?,
            );
        }
        for (id, row) in rows {
            complete_rows.insert(
                *id,
                crate::types::clone_effect_row_with_budget(row, work).map_err(|_| resource())?,
            );
        }
        complete_types.insert(
            self.header.original.answer.id,
            crate::types::clone_type_with_budget(answer, work).map_err(|_| resource())?,
        );
        complete_rows.insert(
            self.handler_continuation(),
            crate::types::clone_effect_row_with_budget(&epsilon, work).map_err(|_| resource())?,
        );
        let realized = original.recipe.realize_nodes(
            &self.handler,
            &complete_types.0,
            &complete_rows,
            &pending,
            captures.rows(),
            &output,
            work,
        )?;
        crate::core::provider::ResolvedProviderHandlerRows::from_source_solution(
            self.handler.arena,
            [direct, epsilon, output],
            pending,
            realized.nodes,
            realized.handlers,
            captures,
            work,
        )
    }
}
