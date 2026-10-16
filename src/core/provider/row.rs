//! Owned source row obligations for conditional provider fragments.
//!
//! These are untrusted inputs to independent recipe reconstruction. Retention
//! permits unfinished rows in a private forest, never ordinary Core admission.

use super::super::{
    BuildError, NodeId,
    dialect::{CoreBuilder, CoreOperationFamily, StoredNode},
    effect::{EffectExprKind, EffectOperation, HandlerId},
};
use crate::{
    resolved::{ProviderTemplateId, ResumeId},
    source::{Origin, Span},
    types::{EffectInstance, EffectRow, InferenceVariableId, TypeWorkBudget},
};

mod demand;
mod realize;

#[derive(Debug)]
pub(crate) enum PendingRowEquation {
    Discard(NodeId),
    Union(EffectRow, EffectRow),
    Remove(EffectRow, EffectInstance, bool),
}

#[derive(Debug)]
pub(crate) struct PendingRowRecord {
    pub identity: InferenceVariableId,
    pub equation: PendingRowEquation,
    pub source: Span,
}

#[derive(Debug)]
pub(crate) struct PendingRowEquality {
    pub left: EffectRow,
    pub right: EffectRow,
    pub source: Span,
}

#[derive(Debug)]
pub(crate) struct PendingRowRecomputation {
    pub nodes: Vec<NodeId>,
    pub output: EffectRow,
    pub handler: HandlerId,
    pub resume: ResumeId,
}

#[derive(Debug, Default)]
pub(crate) struct HandlerPendingRows {
    pub equations: Vec<PendingRowRecord>,
    pub equalities: Vec<PendingRowEquality>,
    pub recomputations: Vec<PendingRowRecomputation>,
}

impl HandlerPendingRows {
    pub(crate) fn identities(&self) -> impl Iterator<Item = InferenceVariableId> + '_ {
        self.equations.iter().map(|record| record.identity)
    }

    pub(in crate::core) fn check_source_nodes<F: CoreOperationFamily>(
        &self,
        nodes: &[StoredNode<F>],
        root: NodeId,
        operation: fn(&F::Kind) -> Option<&EffectOperation>,
        work: &mut TypeWorkBudget,
    ) -> Result<(), BuildError> {
        for record in &self.equations {
            work.charge(1).map_err(|()| BuildError::TypeWorkExceeded)?;
            if let PendingRowEquation::Discard(id) = record.equation {
                if id.arena() != root.arena() {
                    return Err(BuildError::InvalidNodeId);
                }
                let stored = nodes.get(id.index()?).ok_or(BuildError::InvalidNodeId)?;
                let origin = stored.origin.as_ref().ok_or(BuildError::InvalidPayload)?;
                let source = primary_span_with_work(origin, work)
                    .map_err(|()| BuildError::TypeWorkExceeded)?;
                if !matches!(operation(&stored.kind), Some(EffectOperation::Discard(_)))
                    || source != record.source
                {
                    return Err(BuildError::InvalidPayload);
                }
            }
        }
        Ok(())
    }

    pub(crate) fn relocate(
        mut self,
        source_root: NodeId,
        correspondence: &[Option<NodeId>],
        target_root: NodeId,
        work: &mut TypeWorkBudget,
    ) -> Result<Self, BuildError> {
        let map = |id: NodeId, work: &mut TypeWorkBudget| {
            work.charge(1).map_err(|()| BuildError::TypeWorkExceeded)?;
            if id.arena() != source_root.arena() {
                return Err(BuildError::InvalidNodeId);
            }
            let mapped = correspondence
                .get(id.index()?)
                .copied()
                .flatten()
                .ok_or(BuildError::InvalidNodeId)?;
            if mapped.arena() != target_root.arena() {
                return Err(BuildError::InvalidNodeId);
            }
            Ok(mapped)
        };
        for record in &mut self.equations {
            work.charge(1).map_err(|()| BuildError::TypeWorkExceeded)?;
            if let PendingRowEquation::Discard(id) = &mut record.equation {
                *id = map(*id, work)?;
            }
        }
        for record in &mut self.recomputations {
            work.charge(1).map_err(|()| BuildError::TypeWorkExceeded)?;
            for id in &mut record.nodes {
                *id = map(*id, work)?;
            }
        }
        Ok(self)
    }

    pub(crate) fn seed_builder(
        &self,
        builder: &mut CoreBuilder<super::super::effect::EffectOperationFamily>,
        work: &mut TypeWorkBudget,
    ) -> Result<(), BuildError> {
        super::super::transform::begin_provider_draft_work(builder, work.remaining());
        let result = (|| {
            for identity in self.identities() {
                builder.defer_cleanup_row(identity)?;
            }
            Ok(())
        })();
        super::super::transform::discharge_provider_draft_work(builder, work)?;
        result
    }
}

pub(in crate::core) fn effect_operation(kind: &EffectExprKind) -> Option<&EffectOperation> {
    match kind {
        EffectExprKind::Operation(operation) => Some(operation),
        EffectExprKind::Pure(_) => None,
    }
}

// Each ordinal is scoped to one retained recipe and is never an Ash row binder.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub(in crate::core) struct RowEquationId(usize);

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub(in crate::core) struct HandlerOutputId(usize);

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub(crate) struct CaptureInputId(usize);
impl CaptureInputId {
    pub(crate) const fn from_image_claim(value: usize) -> Self {
        Self(value)
    }
    pub(crate) const fn value(self) -> usize {
        self.0
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(in crate::core) enum HandlerOutputOwner {
    ProviderEntry {
        template: ProviderTemplateId,
        handler: HandlerId,
    },
    Nested {
        handler: HandlerId,
        node: NodeId,
    },
}

/// The operation selects existing ordinary row algebra at realization. Inputs
/// name actual graph equations; intrinsic rows stay in the immutable Core.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(in crate::core) enum RowEquationOperation {
    Empty,
    Union { callable: Option<NodeId> },
    Request,
    NativeInterpret,
    CopyWindow,
    StateAccess,
    Handler { output: HandlerOutputId },
    Resume { output: HandlerOutputId },
    Discard { capture: CaptureInputId },
    Cleanup,
    Resource,
    ProviderScope { output: HandlerOutputId },
    Registration,
}

#[derive(Debug)]
pub(in crate::core) struct NodeRowEquation {
    node: NodeId,
    operation: RowEquationOperation,
    inputs: std::ops::Range<usize>,
}

#[derive(Debug)]
pub(in crate::core) struct HandlerOutputEquation {
    owner: HandlerOutputOwner,
    body: Option<RowEquationId>,
    clauses: Vec<RowEquationId>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(in crate::core) struct ConditionalDiscardPort {
    pub(in crate::core) node: NodeId,
    pub(in crate::core) handler: HandlerId,
    pub(in crate::core) resume: ResumeId,
    pub(in crate::core) clause: NodeId,
    pub(in crate::core) output: HandlerOutputId,
    pub(in crate::core) pending: InferenceVariableId,
    pub(in crate::core) source: Span,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(in crate::core) struct DeferredRowPosition {
    node: NodeId,
    equation: RowEquationId,
    provisional: InferenceVariableId,
}

/// Independent graph reconstruction precedes contextual checking. This owner
/// grants no allowance until its annotation equations and capture inputs have
/// also been authenticated against that exact graph.
#[derive(Debug)]
pub(in crate::core) struct HandlerRowRecipeDraft {
    template: ProviderTemplateId,
    nodes: Vec<NodeRowEquation>,
    edges: Vec<RowEquationId>,
    outputs: Vec<HandlerOutputEquation>,
    discards: Vec<ConditionalDiscardPort>,
    node_equations: Vec<Option<RowEquationId>>,
    positions: Vec<DeferredRowPosition>,
    callable_bodies: Vec<Vec<RowEquationId>>,
    latent_bodies: Vec<Vec<RowEquationId>>,
    direct: Option<demand::DirectDemandProof>,
}

fn primary_span_with_work(origin: &Origin, work: &mut TypeWorkBudget) -> Result<Span, ()> {
    let mut origin = origin;
    loop {
        work.charge(1)?;
        origin = match origin {
            Origin::Source(span) => return Ok(*span),
            Origin::Generated { cause, .. } => cause,
            Origin::Related { primary, .. } => primary,
        };
    }
}

impl HandlerRowRecipeDraft {
    /// Scalar original equation domains; this supplies no row solution.
    pub(in crate::core) fn deferred_copy_counts(&self) -> (usize, usize) {
        (self.nodes.len(), self.outputs.len())
    }

    pub(in crate::core) fn deferred_copy_domain(
        &self,
        work: &mut TypeWorkBudget,
    ) -> Result<(Vec<NodeId>, Vec<HandlerId>), super::ValidationError> {
        super::charge(
            work,
            self.nodes
                .len()
                .checked_add(self.outputs.len())
                .ok_or_else(super::resource)?,
        )?;
        let mut nodes = Vec::new();
        nodes
            .try_reserve_exact(self.nodes.len())
            .map_err(|_| super::resource())?;
        nodes.extend(self.nodes.iter().map(|equation| equation.node));
        let mut handlers = Vec::new();
        handlers
            .try_reserve_exact(self.outputs.len())
            .map_err(|_| super::resource())?;
        handlers.extend(self.outputs.iter().map(|output| match output.owner {
            HandlerOutputOwner::ProviderEntry { handler, .. }
            | HandlerOutputOwner::Nested { handler, .. } => handler,
        }));
        Ok((nodes, handlers))
    }

    pub(in crate::core) fn realize_direct(
        &self,
        types: &std::collections::HashMap<crate::types::TypeVariableId, crate::types::Type>,
        rows: &std::collections::HashMap<crate::types::TypeVariableId, EffectRow>,
        captures: &std::collections::HashMap<CaptureInputId, EffectRow>,
        work: &mut TypeWorkBudget,
    ) -> Result<(EffectRow, Vec<EffectRow>), crate::core::ValidationError> {
        self.direct
            .as_ref()
            .ok_or_else(super::resource)?
            .realize(types, rows, captures, work)
    }

    pub(in crate::core) fn discards(&self) -> &[ConditionalDiscardPort] {
        &self.discards
    }
    pub(in crate::core) fn capture_input_for_discard(
        &self,
        node: NodeId,
    ) -> Option<CaptureInputId> {
        let equation = self
            .node_equations
            .get(node.index().ok()?)
            .copied()
            .flatten()?;
        match self.nodes.get(equation.0)?.operation {
            RowEquationOperation::Discard { capture } => Some(capture),
            _ => None,
        }
    }
    pub(in crate::core) fn reconstruct(
        entry: &super::HandlerGraphView<'_>,
        work: &mut TypeWorkBudget,
    ) -> Result<Self, super::ValidationError> {
        let entry = &entry.handler_graph();
        use super::{PureComputation, PureExprKind, charge, invalid, node, resource};
        use std::collections::{HashMap, HashSet};
        let program = &entry.draft.program;
        let failure = |failure| match failure {
            super::super::transform::TransformError::Build(BuildError::TypeWorkExceeded) => {
                resource()
            }
            _ => invalid(program.root),
        };
        let order = if let Some(root) = entry.wrapper_root {
            if root != program.root {
                return Err(invalid(program.root));
            }
            // Projecting clause equations never makes the retained wrappers or
            // unrelated nodes disappear from complete original validation.
            super::super::transform::provider_fragment_order(
                program,
                &[root],
                &HashSet::new(),
                work,
            )
            .map_err(failure)?;
            super::super::transform::provider_entry_forest_order(
                program,
                entry.roots(),
                &HashSet::new(),
                work,
            )
            .map_err(failure)?
        } else {
            super::super::transform::provider_fragment_order(
                program,
                entry.roots(),
                &HashSet::new(),
                work,
            )
            .map_err(failure)?
        };
        charge(
            work,
            program.nodes.len().checked_mul(3).ok_or_else(resource)?,
        )?;
        let mut recipe = Self {
            template: entry.draft.template,
            nodes: Vec::new(),
            edges: Vec::new(),
            outputs: Vec::new(),
            discards: Vec::new(),
            node_equations: Vec::new(),
            positions: Vec::new(),
            callable_bodies: Vec::new(),
            latent_bodies: Vec::new(),
            direct: None,
        };
        recipe
            .nodes
            .try_reserve_exact(program.nodes.len())
            .map_err(|_| resource())?;
        recipe
            .node_equations
            .try_reserve_exact(program.nodes.len())
            .map_err(|_| resource())?;
        recipe.node_equations.resize(program.nodes.len(), None);
        let mut owners = HashMap::new();
        let mut clauses = HashMap::new();
        charge(
            work,
            entry
                .draft
                .clauses
                .len()
                .checked_add(2)
                .ok_or_else(resource)?,
        )?;
        owners.try_reserve(1).map_err(|_| resource())?;
        recipe.outputs.try_reserve(1).map_err(|_| resource())?;
        owners.insert(entry.draft.handler, HandlerOutputId(0));
        recipe.outputs.push(HandlerOutputEquation {
            owner: HandlerOutputOwner::ProviderEntry {
                template: recipe.template,
                handler: entry.draft.handler,
            },
            body: None,
            clauses: Vec::new(),
        });
        clauses
            .try_reserve(entry.draft.clauses.len())
            .map_err(|_| resource())?;
        for clause in entry.draft.clauses {
            if clauses
                .insert(
                    (entry.draft.handler, clause.resume()),
                    (clause.body(), HandlerOutputId(0)),
                )
                .is_some()
            {
                return Err(invalid(clause.body()));
            }
        }
        // Enumerate every real owner before wiring references. An enclosing
        // resume in a nested body keeps its enclosing output identity.
        for id in &order {
            charge(work, 1)?;
            let handler = match &node(program, *id)?.kind {
                EffectExprKind::Operation(EffectOperation::Handler(handler)) => Some(handler),
                EffectExprKind::Operation(EffectOperation::ProviderScope(scope)) => {
                    Some(&scope.handler)
                }
                _ => None,
            };
            if let Some(handler) = handler {
                charge(
                    work,
                    handler
                        .clauses()
                        .len()
                        .checked_add(2)
                        .ok_or_else(resource)?,
                )?;
                owners.try_reserve(1).map_err(|_| resource())?;
                recipe.outputs.try_reserve(1).map_err(|_| resource())?;
                let output = HandlerOutputId(recipe.outputs.len());
                if owners.insert(handler.id(), output).is_some() {
                    return Err(invalid(*id));
                }
                recipe.outputs.push(HandlerOutputEquation {
                    owner: HandlerOutputOwner::Nested {
                        handler: handler.id(),
                        node: *id,
                    },
                    body: None,
                    clauses: Vec::new(),
                });
                clauses
                    .try_reserve(handler.clauses().len())
                    .map_err(|_| resource())?;
                for clause in handler.clauses() {
                    if clauses
                        .insert((handler.id(), clause.resume()), (clause.body(), output))
                        .is_some()
                    {
                        return Err(invalid(*id));
                    }
                }
            }
        }
        let mut discard_rows = HashMap::new();
        charge(work, entry.draft.pending_rows.equations.len())?;
        discard_rows
            .try_reserve(entry.draft.pending_rows.equations.len())
            .map_err(|_| resource())?;
        for record in &entry.draft.pending_rows.equations {
            if let PendingRowEquation::Discard(id) = record.equation
                && discard_rows.insert(id, record).is_some()
            {
                return Err(invalid(id));
            }
        }
        for id in order {
            charge(work, 1)?;
            let stored = node(program, id)?;
            let child_count = stored.kind.child_count();
            charge(work, child_count)?;
            recipe
                .edges
                .try_reserve(child_count)
                .map_err(|_| resource())?;
            let start = recipe.edges.len();
            for index in 0..child_count {
                let child = stored.kind.child_at(index).ok_or_else(|| invalid(id))?;
                let equation = recipe
                    .node_equations
                    .get(child.index().map_err(|_| invalid(id))?)
                    .copied()
                    .flatten()
                    .ok_or_else(|| invalid(child))?;
                recipe.edges.push(equation);
            }
            let operation = match &stored.kind {
                EffectExprKind::Operation(EffectOperation::SourceCopyWindow(_)) => {
                    RowEquationOperation::CopyWindow
                }
                EffectExprKind::Operation(EffectOperation::SourceResourceScope(_)) => {
                    return Err(invalid(id));
                }
                EffectExprKind::Pure(PureExprKind::Value(_) | PureExprKind::Variable(_)) => {
                    RowEquationOperation::Empty
                }
                EffectExprKind::Pure(PureExprKind::Computation(computation)) => {
                    RowEquationOperation::Union {
                        callable: match computation {
                            PureComputation::Apply(application) => Some(application.function()),
                            _ => None,
                        },
                    }
                }
                EffectExprKind::Operation(EffectOperation::NativeInterpret(_)) => {
                    RowEquationOperation::NativeInterpret
                }
                EffectExprKind::Operation(EffectOperation::Request(_)) => {
                    RowEquationOperation::Request
                }
                EffectExprKind::Operation(EffectOperation::ProviderStateAccess(_)) => {
                    RowEquationOperation::StateAccess
                }
                EffectExprKind::Operation(EffectOperation::Cleanup(_)) => {
                    RowEquationOperation::Cleanup
                }
                EffectExprKind::Operation(EffectOperation::Resource(_)) => {
                    RowEquationOperation::Resource
                }
                EffectExprKind::Operation(EffectOperation::ProviderScope(scope)) => {
                    RowEquationOperation::ProviderScope {
                        output: *owners.get(&scope.handler.id()).ok_or_else(|| invalid(id))?,
                    }
                }
                EffectExprKind::Operation(EffectOperation::Registration(_)) => {
                    RowEquationOperation::Registration
                }
                EffectExprKind::Operation(EffectOperation::Handler(handler)) => {
                    RowEquationOperation::Handler {
                        output: *owners.get(&handler.id()).ok_or_else(|| invalid(id))?,
                    }
                }
                EffectExprKind::Operation(EffectOperation::Resume(resume)) => {
                    let (_, output) = clauses
                        .get(&(resume.handler(), resume.owner()))
                        .ok_or_else(|| invalid(id))?;
                    RowEquationOperation::Resume { output: *output }
                }
                EffectExprKind::Operation(EffectOperation::Discard(discard)) => {
                    let (clause, output) = clauses
                        .get(&(discard.handler(), discard.owner()))
                        .ok_or_else(|| invalid(id))?;
                    let record = discard_rows.remove(&id).ok_or_else(|| invalid(id))?;
                    if !stored.effects.known().is_empty()
                        || stored.effects.tail().is_none_or(|tail| {
                            tail.variable()
                                != crate::types::EffectRowVariable::Inference(record.identity)
                                || !tail.lacks().is_empty()
                        })
                        || primary_span_with_work(
                            stored.origin.as_ref().ok_or_else(|| invalid(id))?,
                            work,
                        )
                        .map_err(|()| resource())?
                            != record.source
                    {
                        return Err(invalid(id));
                    }
                    charge(work, 1)?;
                    recipe.discards.try_reserve(1).map_err(|_| resource())?;
                    let capture = CaptureInputId(recipe.discards.len());
                    recipe.discards.push(ConditionalDiscardPort {
                        node: id,
                        handler: discard.handler(),
                        resume: discard.owner(),
                        clause: *clause,
                        output: *output,
                        pending: record.identity,
                        source: record.source,
                    });
                    RowEquationOperation::Discard { capture }
                }
            };
            let equation = RowEquationId(recipe.nodes.len());
            recipe.node_equations[id.index().map_err(|_| invalid(id))?] = Some(equation);
            recipe.nodes.push(NodeRowEquation {
                node: id,
                operation,
                inputs: start..recipe.edges.len(),
            });
        }
        if !discard_rows.is_empty() {
            return Err(invalid(program.root));
        }
        for output in &mut recipe.outputs {
            let roots: &[super::super::effect::EffectClause] = match output.owner {
                HandlerOutputOwner::ProviderEntry { .. } => entry.draft.clauses,
                HandlerOutputOwner::Nested { node: id, .. } => {
                    let handler = match &node(program, id)?.kind {
                        EffectExprKind::Operation(EffectOperation::Handler(handler)) => handler,
                        EffectExprKind::Operation(EffectOperation::ProviderScope(scope)) => {
                            &scope.handler
                        }
                        _ => return Err(invalid(id)),
                    };
                    output.body = Some(
                        recipe.node_equations[handler.body().index().map_err(|_| invalid(id))?]
                            .ok_or_else(|| invalid(id))?,
                    );
                    handler.clauses()
                }
            };
            charge(work, roots.len())?;
            output
                .clauses
                .try_reserve_exact(roots.len())
                .map_err(|_| resource())?;
            for clause in roots {
                output.clauses.push(
                    recipe.node_equations
                        [clause.body().index().map_err(|_| invalid(clause.body()))?]
                    .ok_or_else(|| invalid(clause.body()))?,
                );
            }
        }
        recipe.reconstruct_callable_bodies(entry, work)?;
        recipe.reconstruct_pending_positions(entry, work)?;
        recipe.direct = Some(demand::DirectDemandProof::reconstruct(
            &recipe, entry, work,
        )?);
        Ok(recipe)
    }

    fn equation_for(
        &self,
        entry: &super::HandlerGraphView<'_>,
        id: NodeId,
    ) -> Option<RowEquationId> {
        let entry = &entry.handler_graph();
        if self.template != entry.draft.template || id.arena() != entry.draft.program.arena {
            return None;
        }
        self.node_equations.get(id.index().ok()?).copied().flatten()
    }

    pub(in crate::core) fn deferred_node(
        &self,
        entry: &super::HandlerGraphView<'_>,
        id: NodeId,
        work: &mut TypeWorkBudget,
    ) -> Result<bool, super::ValidationError> {
        let entry = &entry.handler_graph();
        super::charge(work, 1)?;
        Ok(self
            .equation_for(entry, id)
            .zip(self.direct.as_ref())
            .is_some_and(|(equation, proof)| proof.node_projection(equation)))
    }

    pub(in crate::core) fn deferred_function(
        &self,
        entry: &super::HandlerGraphView<'_>,
        id: NodeId,
        work: &mut TypeWorkBudget,
    ) -> Result<bool, super::ValidationError> {
        let entry = &entry.handler_graph();
        super::charge(work, 1)?;
        Ok(self
            .equation_for(entry, id)
            .zip(self.direct.as_ref())
            .is_some_and(|(equation, proof)| proof.function_constraint(equation)))
    }

    pub(in crate::core) fn permits_row_position(
        &self,
        entry: &super::HandlerGraphView<'_>,
        id: NodeId,
        row: &EffectRow,
        work: &mut TypeWorkBudget,
    ) -> Result<bool, super::ValidationError> {
        let entry = &entry.handler_graph();
        use super::{PureComputation, PureExprKind, charge, node};
        charge(work, 1)?;
        let Some(equation) = self.equation_for(entry, id) else {
            return Ok(false);
        };
        let Some(proof) = self.direct.as_ref() else {
            return Ok(false);
        };
        let stored = node(entry.draft.program, id)?;
        if std::ptr::eq(row, &stored.effects) {
            return Ok(proof.node_projection(equation));
        }
        if stored
            .ty
            .function_view()
            .and_then(|view| view.effects())
            .is_some_and(|latent| std::ptr::eq(row, latent))
        {
            return Ok(proof.latent_projection(equation));
        }
        let initializer = match &stored.kind {
            EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Bind(binding))) => {
                binding
                    .binder()
                    .ty()
                    .function_view()
                    .and_then(|view| view.effects())
                    .is_some_and(|latent| std::ptr::eq(row, latent))
                    .then_some(binding.initializer())
            }
            EffectExprKind::Pure(PureExprKind::Computation(PureComputation::RecursiveBind(
                group,
            ))) => {
                charge(work, group.members().len())?;
                group.members().iter().find_map(|member| {
                    member
                        .binder()
                        .ty()
                        .function_view()
                        .and_then(|view| view.effects())
                        .is_some_and(|latent| std::ptr::eq(row, latent))
                        .then_some(member.initializer())
                })
            }
            _ => None,
        };
        Ok(initializer
            .and_then(|id| self.equation_for(entry, id))
            .is_some_and(|equation| proof.latent_projection(equation)))
    }

    pub(in crate::core) fn discard_port(
        &self,
        entry: &super::HandlerGraphView<'_>,
        id: NodeId,
        work: &mut TypeWorkBudget,
    ) -> Result<bool, super::ValidationError> {
        let entry = &entry.handler_graph();
        super::charge(work, 1)?;
        let Some(equation) = self.equation_for(entry, id) else {
            return Ok(false);
        };
        let RowEquationOperation::Discard { capture } = self.nodes[equation.0].operation else {
            return Ok(false);
        };
        Ok(self.direct.is_some()
            && self
                .discards
                .get(capture.0)
                .is_some_and(|port| port.node == id))
    }

    fn reconstruct_callable_bodies(
        &mut self,
        entry: &super::HandlerGraphView<'_>,
        work: &mut TypeWorkBudget,
    ) -> Result<(), super::ValidationError> {
        let entry = &entry.handler_graph();
        use super::{PureComputation, PureExprKind, charge, invalid, node, resource};
        use std::collections::HashMap;
        let program = &entry.draft.program;
        let mut bindings = HashMap::new();
        charge(work, program.nodes.len())?;
        bindings
            .try_reserve(program.nodes.len())
            .map_err(|_| resource())?;
        for stored in &program.nodes {
            charge(work, 1)?;
            let EffectExprKind::Pure(PureExprKind::Computation(computation)) = &stored.kind else {
                continue;
            };
            match computation {
                PureComputation::Bind(binding) => {
                    if bindings
                        .insert(binding.binder().id(), binding.initializer())
                        .is_some()
                    {
                        return Err(invalid(program.root));
                    }
                }
                PureComputation::RecursiveBind(group) => {
                    charge(work, group.members().len())?;
                    bindings
                        .try_reserve(group.members().len())
                        .map_err(|_| resource())?;
                    for member in group.members() {
                        if bindings
                            .insert(member.binder().id(), member.initializer())
                            .is_some()
                        {
                            return Err(invalid(program.root));
                        }
                    }
                }
                _ => {}
            }
        }
        charge(work, self.nodes.len().checked_mul(2).ok_or_else(resource)?)?;
        self.callable_bodies
            .try_reserve_exact(self.nodes.len())
            .map_err(|_| resource())?;
        self.latent_bodies
            .try_reserve_exact(self.nodes.len())
            .map_err(|_| resource())?;
        for equation in &self.nodes {
            let callable = if let RowEquationOperation::Union {
                callable: Some(function),
            } = equation.operation
            {
                self.resolve_callable_bodies(program, function, &bindings, work)?
            } else {
                Vec::new()
            };
            let latent = if node(program, equation.node)?.ty.function_view().is_some() {
                self.resolve_callable_bodies(program, equation.node, &bindings, work)?
            } else {
                Vec::new()
            };
            self.callable_bodies.push(callable);
            self.latent_bodies.push(latent);
        }
        Ok(())
    }

    fn resolve_callable_bodies(
        &self,
        program: &super::UnvalidatedEffectProgram,
        function: NodeId,
        bindings: &std::collections::HashMap<crate::resolved::BinderId, NodeId>,
        work: &mut TypeWorkBudget,
    ) -> Result<Vec<RowEquationId>, super::ValidationError> {
        use super::{PureComputation, PureExprKind, PureValue, charge, invalid, node, resource};
        use std::collections::HashSet;
        let mut bodies = Vec::new();
        let mut visited = HashSet::new();
        let mut stack = Vec::new();
        charge(work, 1)?;
        stack.try_reserve(1).map_err(|_| resource())?;
        stack.push(function);
        while let Some(id) = stack.pop() {
            charge(work, 1)?;
            if visited.contains(&id) {
                continue;
            }
            visited.try_reserve(1).map_err(|_| resource())?;
            visited.insert(id);
            let stored = node(program, id)?;
            let next = match &stored.kind {
                EffectExprKind::Pure(PureExprKind::Value(PureValue::Function(function))) => {
                    charge(work, 1)?;
                    bodies.try_reserve(1).map_err(|_| resource())?;
                    let body = self.node_equations
                        [function.body().index().map_err(|_| invalid(id))?]
                    .ok_or_else(|| invalid(id))?;
                    charge(work, bodies.len())?;
                    if !bodies.contains(&body) {
                        bodies.push(body);
                    }
                    None
                }
                EffectExprKind::Pure(PureExprKind::Variable(variable)) => {
                    bindings.get(&variable.binder()).copied()
                }
                EffectExprKind::Pure(PureExprKind::Computation(computation)) => match computation {
                    PureComputation::TypeApplication(application) => Some(application.function()),
                    PureComputation::TypeAbstraction(abstraction) => Some(abstraction.body()),
                    PureComputation::NewtypeConversion(conversion) => Some(conversion.child()),
                    PureComputation::LocalNominalScope(scope) => Some(scope.body()),
                    PureComputation::Bind(binding) => Some(binding.body()),
                    PureComputation::RecursiveBind(group) => Some(group.body()),
                    PureComputation::Match(selection) => {
                        charge(work, selection.arms().len())?;
                        stack
                            .try_reserve(selection.arms().len())
                            .map_err(|_| resource())?;
                        stack.extend(selection.arms().iter().map(|arm| arm.body()));
                        None
                    }
                    _ => None,
                },
                _ => None,
            };
            if let Some(next) = next {
                charge(work, 1)?;
                stack.try_reserve(1).map_err(|_| resource())?;
                stack.push(next);
            }
        }
        Ok(bodies)
    }

    fn reconstruct_pending_positions(
        &mut self,
        entry: &super::HandlerGraphView<'_>,
        work: &mut TypeWorkBudget,
    ) -> Result<(), super::ValidationError> {
        let entry = &entry.handler_graph();
        use super::{charge, invalid, resource};
        use crate::types::EffectRowVariable;
        use std::collections::{HashMap, HashSet};
        let pending = &entry.draft.pending_rows;
        let mut identities = HashMap::new();
        charge(work, pending.equations.len())?;
        identities
            .try_reserve(pending.equations.len())
            .map_err(|_| resource())?;
        for (index, record) in pending.equations.iter().enumerate() {
            if identities.insert(record.identity, index).is_some() {
                return Err(invalid(entry.draft.program.root));
            }
        }
        let mut references = Vec::new();
        charge(work, pending.equations.len())?;
        references
            .try_reserve_exact(pending.equations.len())
            .map_err(|_| resource())?;
        for record in &pending.equations {
            let mut next = Vec::new();
            let rows: &[&EffectRow] = match &record.equation {
                PendingRowEquation::Discard(_) => &[],
                PendingRowEquation::Union(left, right) => &[left, right],
                PendingRowEquation::Remove(row, _, _) => &[row],
            };
            charge(work, rows.len())?;
            next.try_reserve_exact(rows.len()).map_err(|_| resource())?;
            for row in rows {
                if let Some(tail) = row.tail()
                    && let EffectRowVariable::Inference(identity) = tail.variable()
                {
                    next.push(
                        *identities
                            .get(&identity)
                            .ok_or_else(|| invalid(entry.draft.program.root))?,
                    );
                }
            }
            references.push(next);
        }
        // Compute the source identities' actual capture dependencies, including
        // cyclic source union constraints, without assigning any concrete c.
        let mut pending_dependencies = Vec::new();
        charge(work, pending.equations.len())?;
        pending_dependencies
            .try_reserve_exact(pending.equations.len())
            .map_err(|_| resource())?;
        pending_dependencies.resize_with(pending.equations.len(), HashSet::new);
        for (index, record) in pending.equations.iter().enumerate() {
            if let PendingRowEquation::Discard(node) = record.equation {
                charge(
                    work,
                    self.discards.len().checked_add(1).ok_or_else(resource)?,
                )?;
                let capture = self
                    .discards
                    .iter()
                    .enumerate()
                    .find_map(|(ordinal, port)| {
                        (port.node == node && port.pending == record.identity)
                            .then_some(CaptureInputId(ordinal))
                    })
                    .ok_or_else(|| invalid(node))?;
                pending_dependencies[index]
                    .try_reserve(1)
                    .map_err(|_| resource())?;
                pending_dependencies[index].insert(capture);
            }
        }
        loop {
            let mut changed = false;
            for (index, inputs) in references.iter().enumerate() {
                charge(work, 1)?;
                for input in inputs {
                    let source = &pending_dependencies[*input];
                    charge(
                        work,
                        source
                            .len()
                            .checked_mul(2)
                            .and_then(|cells| cells.checked_add(1))
                            .ok_or_else(resource)?,
                    )?;
                    let mut incoming = Vec::new();
                    incoming
                        .try_reserve_exact(source.len())
                        .map_err(|_| resource())?;
                    incoming.extend(source.iter().copied());
                    pending_dependencies[index]
                        .try_reserve(incoming.len())
                        .map_err(|_| resource())?;
                    for capture in incoming {
                        changed |= pending_dependencies[index].insert(capture);
                    }
                }
            }
            if !changed {
                break;
            }
        }
        let mut node_dependencies: Vec<HashSet<CaptureInputId>> = Vec::new();
        charge(work, self.nodes.len())?;
        node_dependencies
            .try_reserve_exact(self.nodes.len())
            .map_err(|_| resource())?;
        node_dependencies.resize_with(self.nodes.len(), HashSet::new);
        for (ordinal, equation) in self.nodes.iter().enumerate() {
            if let RowEquationOperation::Discard { capture } = equation.operation {
                charge(work, 1)?;
                node_dependencies[ordinal]
                    .try_reserve(1)
                    .map_err(|_| resource())?;
                node_dependencies[ordinal].insert(capture);
            }
        }
        // Invocation edges are not syntax children of the Apply node. Follow
        // actual local callable bodies, including recursive aliases, to a least
        // dependency fixed point. Function creation itself stays pure.
        loop {
            let mut changed = false;
            for (ordinal, equation) in self.nodes.iter().enumerate() {
                charge(work, 1)?;
                if matches!(
                    equation.operation,
                    RowEquationOperation::Empty | RowEquationOperation::Discard { .. }
                ) {
                    continue;
                }
                let mut owner_input = None;
                if let RowEquationOperation::Resume { output } = equation.operation
                    && let HandlerOutputOwner::Nested { node, .. } = self.outputs[output.0].owner
                {
                    owner_input = self.node_equations[node.index().map_err(|_| invalid(node))?];
                }
                let inputs = self.edges[equation.inputs.clone()]
                    .iter()
                    .chain(self.callable_bodies[ordinal].iter())
                    .chain(owner_input.iter());
                for input in inputs {
                    let incoming = &node_dependencies[input.0];
                    charge(
                        work,
                        incoming
                            .len()
                            .checked_mul(2)
                            .and_then(|cells| cells.checked_add(1))
                            .ok_or_else(resource)?,
                    )?;
                    let mut copy = Vec::new();
                    copy.try_reserve_exact(incoming.len())
                        .map_err(|_| resource())?;
                    copy.extend(incoming.iter().copied());
                    node_dependencies[ordinal]
                        .try_reserve(copy.len())
                        .map_err(|_| resource())?;
                    for capture in copy {
                        changed |= node_dependencies[ordinal].insert(capture);
                    }
                }
            }
            if !changed {
                break;
            }
        }
        let mut observed = HashSet::new();
        charge(work, pending.equations.len())?;
        observed
            .try_reserve(pending.equations.len())
            .map_err(|_| resource())?;
        for equation in &self.nodes {
            let stored = super::node(entry.draft.program, equation.node)?;
            charge(work, 1)?;
            if let Some(tail) = stored.effects.tail()
                && let EffectRowVariable::Inference(identity) = tail.variable()
            {
                let index = *identities
                    .get(&identity)
                    .ok_or_else(|| invalid(equation.node))?;
                let equation_id = self.node_equations
                    [equation.node.index().map_err(|_| invalid(equation.node))?]
                .ok_or_else(|| invalid(equation.node))?;
                let required = &pending_dependencies[index];
                let actual = &node_dependencies[equation_id.0];
                charge(work, required.len().checked_add(1).ok_or_else(resource)?)?;
                if required.is_empty() || actual.is_empty() || !required.is_subset(actual) {
                    return Err(invalid(equation.node));
                }
                observed.insert(index);
                charge(work, 1)?;
                self.positions.try_reserve(1).map_err(|_| resource())?;
                self.positions.push(DeferredRowPosition {
                    node: equation.node,
                    equation: self.node_equations
                        [equation.node.index().map_err(|_| invalid(equation.node))?]
                    .ok_or_else(|| invalid(equation.node))?,
                    provisional: identity,
                });
            }
        }
        // An unused callable still owns its latent pending equations. Its
        // actual body authenticates that position below in DirectDemandProof;
        // absence of an invocation does not erase the retained equation.
        for equation in &self.nodes {
            charge(work, 1)?;
            let stored = super::node(entry.draft.program, equation.node)?;
            if let Some(tail) = stored
                .ty
                .function_view()
                .and_then(|view| view.effects())
                .and_then(EffectRow::tail)
                && let EffectRowVariable::Inference(identity) = tail.variable()
            {
                charge(work, 1)?;
                observed.insert(
                    *identities
                        .get(&identity)
                        .ok_or_else(|| invalid(equation.node))?,
                );
            }
        }
        if let Some(tail) = entry.draft.direct_demands.tail()
            && let EffectRowVariable::Inference(identity) = tail.variable()
        {
            charge(work, 1)?;
            observed.insert(
                *identities
                    .get(&identity)
                    .ok_or_else(|| invalid(entry.draft.program.root))?,
            );
        }
        // Reachability is not equation authority. It establishes that every
        // retained source identity belongs to a real position or its dependency.
        // Operator/annotation agreement is authenticated separately.
        let mut stack = Vec::new();
        charge(work, observed.len())?;
        stack
            .try_reserve_exact(observed.len())
            .map_err(|_| resource())?;
        stack.extend(observed.iter().copied());
        while let Some(index) = stack.pop() {
            charge(work, references[index].len())?;
            stack
                .try_reserve(references[index].len())
                .map_err(|_| resource())?;
            for reference in &references[index] {
                if observed.insert(*reference) {
                    stack.push(*reference);
                }
            }
        }
        if observed.len() != pending.equations.len() {
            return Err(invalid(entry.draft.program.root));
        }
        Ok(())
    }
}

#[cfg(test)]
pub(crate) fn pending_row_inventory_for_test(draft: &super::HandlerFragmentDraft) -> String {
    format!(
        "pending={:#?}\nnodes={:#?}",
        draft.pending_rows, draft.program.nodes
    )
}

#[cfg(test)]
pub(crate) fn reconstructed_row_inventory_for_test(
    draft: &super::HandlerFragmentDraft,
    module: &crate::resolved::ResolvedModule,
    work: &mut TypeWorkBudget,
) -> Result<(usize, usize, usize), super::ValidationError> {
    let entry = super::HandlerFragmentEntry::reconstruct(draft, module, work)
        .inspect_err(|error| eprintln!("row inventory entry boundary: {error:?}"))?;
    let recipe = HandlerRowRecipeDraft::reconstruct(&entry.handler_graph(), work)
        .inspect_err(|error| eprintln!("row inventory recipe boundary: {error:?}"))?;
    for port in &recipe.discards {
        let stored = super::node(&draft.program, port.node)?;
        assert!(
            matches!(&stored.kind, EffectExprKind::Operation(EffectOperation::Discard(discard)) if discard.handler() == port.handler && discard.owner() == port.resume)
        );
        assert!(draft.pending_rows.equations.iter().any(|record| record.identity == port.pending && matches!(record.equation, PendingRowEquation::Discard(id) if id == port.node)));
        assert!(
            recipe.outputs[port.output.0]
                .clauses
                .contains(&recipe.node_equations[port.clause.index().unwrap()].unwrap())
        );
    }
    Ok((
        recipe.nodes.len(),
        recipe.outputs.len(),
        recipe.discards.len(),
    ))
}

#[cfg(test)]
pub(crate) fn row_recipe_links_for_test(
    draft: &super::HandlerFragmentDraft,
    module: &crate::resolved::ResolvedModule,
    work: &mut TypeWorkBudget,
) -> Result<Vec<(NodeId, HandlerId, bool)>, super::ValidationError> {
    let entry = super::HandlerFragmentEntry::reconstruct(draft, module, work)?;
    let recipe = HandlerRowRecipeDraft::reconstruct(&entry.handler_graph(), work)?;
    let mut result = Vec::new();
    for equation in &recipe.nodes {
        if let RowEquationOperation::Resume { output } = equation.operation {
            let (handler, provider) = match recipe.outputs[output.0].owner {
                HandlerOutputOwner::ProviderEntry { handler, .. } => (handler, true),
                HandlerOutputOwner::Nested { handler, .. } => (handler, false),
            };
            result.push((equation.node, handler, provider));
        }
    }
    Ok(result)
}

#[cfg(test)]
pub(crate) fn put_pending_on_unrelated_unit_for_test(draft: &mut super::HandlerFragmentDraft) {
    let row = draft
        .program
        .nodes
        .iter()
        .find_map(|stored| match &stored.kind {
            EffectExprKind::Operation(EffectOperation::Discard(_)) => Some(&stored.effects),
            _ => None,
        })
        .unwrap();
    let row =
        crate::types::clone_effect_row_with_budget(row, &mut TypeWorkBudget::unbounded()).unwrap();
    let stored = draft
        .program
        .nodes
        .iter_mut()
        .find(|stored| {
            matches!(
                &stored.kind,
                EffectExprKind::Pure(super::PureExprKind::Value(super::PureValue::Unit(_)))
            )
        })
        .unwrap();
    stored.effects = row;
}

#[cfg(test)]
pub(crate) fn drop_native_from_pending_demands_for_test(draft: &mut super::HandlerFragmentDraft) {
    let index = draft
        .pending_rows
        .equations
        .iter()
        .position(|record| matches!(record.equation, PendingRowEquation::Union(_, _)))
        .unwrap();
    let record = draft.pending_rows.equations.remove(index);
    let PendingRowEquation::Union(left, right) = record.equation else {
        unreachable!()
    };
    assert!(!right.known().is_empty());
    draft.direct_demands = left;
}

#[cfg(test)]
pub(crate) fn wrong_pending_recomputation_owner_for_test(draft: &mut super::HandlerFragmentDraft) {
    let record = draft.pending_rows.recomputations.first_mut().unwrap();
    assert_ne!(record.handler, draft.handler);
    record.handler = draft.handler;
    record.resume = draft.clauses[0].resume();
}

#[cfg(test)]
pub(crate) fn add_unused_pending_equality_for_test(draft: &mut super::HandlerFragmentDraft) {
    let source = draft.pending_rows.equations[0].source;
    draft.pending_rows.equalities.push(PendingRowEquality {
        left: EffectRow::empty(),
        right: EffectRow::empty(),
        source,
    });
}

#[cfg(test)]
pub(crate) fn has_actual_open_equation_for_test(
    draft: &super::HandlerFragmentDraft,
    module: &crate::resolved::ResolvedModule,
    work: &mut TypeWorkBudget,
) -> Result<bool, super::ValidationError> {
    let entry = super::HandlerFragmentEntry::reconstruct(draft, module, work)?;
    let recipe = HandlerRowRecipeDraft::reconstruct(&entry.handler_graph(), work)?;
    Ok(recipe.direct.as_ref().unwrap().has_open_leaf())
}

/// Body-free defining coordinates. Clause roots and node equations belong to
/// the separately owned recipe/code link, never to this contract's authority.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct FullContinuationInputId(usize);

/// Ordinary principal union and exact known-member residual realization are
/// obligations over an actual future boundary, never a supplied row value.
struct HandlerSharedRowContract {
    continuation: FullContinuationInputId,
    output: HandlerOutputId,
    residual: crate::types::TypeVariableId,
}

pub(in crate::core) struct HandlerRowContract {
    shared: HandlerSharedRowContract,
    template: ProviderTemplateId,
    family: Option<super::ProviderFamilyIdentity>,
    handler: HandlerId,
    hidden: [(crate::types::TypeVariableId, crate::types::Kind); 2],
    formals: Box<[(crate::types::TypeVariableId, crate::types::Kind)]>,
    provided: EffectInstance,
    interpreted: EffectInstance,
    state: crate::types::IterativeTypeOwner,
    clauses: Vec<HandlerClauseRowContract>,
    demands: demand::HandlerDemandContract,
}
struct HandlerClauseRowContract {
    operation: crate::types::OperationId,
    resume: ResumeId,
    origin: super::external::RetainedHandlerOrigin,
}

impl HandlerRowContract {
    pub(in crate::core) fn realize_direct(
        &self,
        types: &std::collections::HashMap<crate::types::TypeVariableId, crate::types::Type>,
        rows: &std::collections::HashMap<crate::types::TypeVariableId, EffectRow>,
        captures: &std::collections::HashMap<CaptureInputId, EffectRow>,
        work: &mut TypeWorkBudget,
    ) -> Result<EffectRow, super::ValidationError> {
        self.demands.realize(types, rows, captures, work)
    }
}
impl HandlerRowRecipeDraft {
    pub(in crate::core) fn defining_contract(
        &self,
        entry: &super::HandlerFragmentEntry<'_>,
        work: &mut TypeWorkBudget,
    ) -> Result<HandlerRowContract, super::ValidationError> {
        use super::{charge, invalid, resource};
        let proof = self
            .direct
            .as_ref()
            .ok_or_else(|| invalid(entry.draft.program.root))?;
        let parameter_count = entry
            .definition
            .parameters
            .len()
            .checked_add(usize::from(entry.family_identity().is_some()))
            .ok_or_else(resource)?;
        charge(work, parameter_count)?;
        let mut formals = Vec::new();
        formals
            .try_reserve_exact(parameter_count)
            .map_err(|_| resource())?;
        for parameter in entry.parameters() {
            formals.push((
                parameter.id,
                crate::types::clone_kind_with_budget(&parameter.kind, work)
                    .map_err(|()| resource())?,
            ));
        }
        charge(work, entry.draft.clauses.len())?;
        let mut clauses = Vec::new();
        clauses
            .try_reserve_exact(entry.draft.clauses.len())
            .map_err(|_| resource())?;
        for clause in &entry.draft.clauses {
            clauses.push(HandlerClauseRowContract {
                operation: clause.operation(),
                resume: clause.resume(),
                origin: super::external::RetainedHandlerOrigin::copy(clause.origin(), work)?,
            });
        }
        Ok(HandlerRowContract {
            shared: HandlerSharedRowContract {
                continuation: FullContinuationInputId(0),
                output: HandlerOutputId(0),
                residual: entry.draft.hidden[1].0,
            },
            template: entry.draft.template,
            family: entry.family_identity(),
            handler: entry.draft.handler,
            hidden: [
                (
                    entry.draft.hidden[0].0,
                    crate::types::clone_kind_with_budget(&entry.draft.hidden[0].1, work)
                        .map_err(|()| resource())?,
                ),
                (
                    entry.draft.hidden[1].0,
                    crate::types::clone_kind_with_budget(&entry.draft.hidden[1].1, work)
                        .map_err(|()| resource())?,
                ),
            ],
            formals: formals.into_boxed_slice(),
            provided: crate::types::clone_effect_instance_with_budget(entry.provided(), work)
                .map_err(|()| resource())?,
            interpreted: crate::types::clone_effect_instance_with_budget(entry.interpreted(), work)
                .map_err(|()| resource())?,
            state: crate::types::IterativeTypeOwner::new(
                crate::types::clone_type_with_budget(&entry.definition.state.ty, work)
                    .map_err(|()| resource())?,
            ),
            clauses,
            demands: proof.defining_contract(work)?,
        })
    }
}

pub(in crate::core) fn authenticate_definition_contract(
    contract: &HandlerRowContract,
    fact: &crate::resolved::ResourceTypeFact,
    work: &mut TypeWorkBudget,
) -> Result<(), super::ValidationError> {
    use super::{charge, resource};
    // The original immutable certificate is required; this projection is no
    // constructor for a conditional proof and cannot authorize executable Core.
    let invalid_contract = || super::ValidationError::new(super::ValidationReason::NodeType, None);
    let family = match contract.family {
        None => None,
        Some(identity) => {
            let family = fact.family_template.as_ref().ok_or_else(invalid_contract)?;
            if identity.definition != fact.id || identity.parameter != family.parameter.id {
                return Err(invalid_contract());
            }
            Some(family)
        }
    };
    let provided = family.map_or(&fact.provided.instance, |family| &family.provided.instance);
    let interpreted = family.map_or(&fact.interpreted.instance, |family| {
        &family.interpreted.instance
    });
    charge(work, contract.formals.len())?;
    if contract.template != ProviderTemplateId::new(fact.id, if family.is_some() { 3 } else { 2 })
        || contract.formals.len()
            != fact
                .parameters
                .len()
                .checked_add(usize::from(family.is_some()))
                .ok_or_else(resource)?
        || contract.hidden[0].0 == contract.hidden[1].0
        || contract.hidden[0].1 != crate::types::Kind::Type
        || contract.hidden[1].1 != crate::types::Kind::EffectRow
    {
        return Err(invalid_contract());
    }
    for ((formal, kind), parameter) in contract.formals.iter().zip(
        fact.parameters
            .iter()
            .chain(family.map(|family| &family.parameter)),
    ) {
        if *formal != parameter.id
            || !crate::types::same_kind_with_budget(kind, &parameter.kind, work)
                .map_err(|()| resource())?
            || contract.hidden.iter().any(|(hidden, _)| hidden == formal)
        {
            return Err(invalid_contract());
        }
    }
    if !crate::types::same_type_with_budget(&contract.state, &fact.state.ty, work)
        .map_err(|()| resource())?
        || crate::types::compare_effect_instances_with_budget(&contract.provided, provided, work)
            .map_err(|()| resource())?
            != std::cmp::Ordering::Equal
        || crate::types::compare_effect_instances_with_budget(
            &contract.interpreted,
            interpreted,
            work,
        )
        .map_err(|()| resource())?
            != std::cmp::Ordering::Equal
    {
        return Err(invalid_contract());
    }
    Ok(())
}

pub(in crate::core) fn authenticate_owned_contract(
    contract: &HandlerRowContract,
    recipe: &HandlerRowRecipeDraft,
    draft: &super::HandlerFragmentDraft,
    fact: &crate::resolved::ResourceTypeFact,
    work: &mut TypeWorkBudget,
) -> Result<(), super::ValidationError> {
    use super::{charge, invalid, resource};
    let family = match contract.family {
        None => None,
        Some(identity) => {
            let family = fact
                .family_template
                .as_ref()
                .ok_or_else(|| invalid(draft.program.root))?;
            if identity.definition != fact.id || identity.parameter != family.parameter.id {
                return Err(invalid(draft.program.root));
            }
            Some(family)
        }
    };
    let provided = family.map_or(&fact.provided.instance, |family| &family.provided.instance);
    let interpreted = family.map_or(&fact.interpreted.instance, |family| {
        &family.interpreted.instance
    });
    charge(
        work,
        contract
            .formals
            .len()
            .checked_add(contract.clauses.len())
            .ok_or_else(resource)?,
    )?;
    if contract.template != ProviderTemplateId::new(fact.id, if family.is_some() { 3 } else { 2 })
        || contract.template != draft.template
        || contract.handler != draft.handler
        || recipe.template != draft.template
        || recipe.direct.is_none()
        || contract.shared.continuation != FullContinuationInputId(0)
        || contract.shared.output != HandlerOutputId(0)
        || contract.shared.residual != draft.hidden[1].0
        || contract.formals.len()
            != fact
                .parameters
                .len()
                .checked_add(usize::from(family.is_some()))
                .ok_or_else(resource)?
        || contract.clauses.len() != draft.clauses.len()
        || contract.hidden[0].0 == contract.hidden[1].0
        || contract.hidden[0].1 != crate::types::Kind::Type
        || contract.hidden[1].1 != crate::types::Kind::EffectRow
    {
        return Err(invalid(draft.program.root));
    }
    for ((retained, kind), (actual, actual_kind)) in contract.hidden.iter().zip(&draft.hidden) {
        if retained != actual
            || !crate::types::same_kind_with_budget(kind, actual_kind, work)
                .map_err(|()| resource())?
        {
            return Err(invalid(draft.program.root));
        }
    }
    for ((formal, kind), parameter) in contract.formals.iter().zip(
        fact.parameters
            .iter()
            .chain(family.map(|family| &family.parameter)),
    ) {
        if *formal != parameter.id
            || !crate::types::same_kind_with_budget(kind, &parameter.kind, work)
                .map_err(|()| resource())?
            || contract.hidden.iter().any(|(hidden, _)| hidden == formal)
        {
            return Err(invalid(draft.program.root));
        }
    }
    if !crate::types::same_type_with_budget(&contract.state, &fact.state.ty, work)
        .map_err(|()| resource())?
        || crate::types::compare_effect_instances_with_budget(&contract.provided, provided, work)
            .map_err(|()| resource())?
            != std::cmp::Ordering::Equal
        || crate::types::compare_effect_instances_with_budget(
            &contract.interpreted,
            interpreted,
            work,
        )
        .map_err(|()| resource())?
            != std::cmp::Ordering::Equal
    {
        return Err(invalid(draft.program.root));
    }
    for (retained, clause) in contract.clauses.iter().zip(&draft.clauses) {
        if retained.operation != clause.operation()
            || retained.resume != clause.resume()
            || retained.operation.owner() != provided.effect()
            || !crate::resolved::same_origin_with_budget(
                retained.origin.as_origin(),
                clause.origin(),
                work,
            )
            .map_err(|()| resource())?
        {
            return Err(invalid(clause.body()));
        }
        super::node(&draft.program, clause.body())?;
    }
    Ok(())
}

#[cfg(test)]
pub(in crate::core) fn owned_contract_links_for_test(
    contract: &HandlerRowContract,
    recipe: &HandlerRowRecipeDraft,
    draft: &super::HandlerFragmentDraft,
) -> Vec<(crate::types::OperationId, ResumeId)> {
    assert_eq!(
        (contract.template, contract.handler),
        (draft.template, draft.handler)
    );
    assert_eq!(contract.hidden, draft.hidden);
    assert_eq!(contract.shared.continuation, FullContinuationInputId(0));
    assert_eq!(contract.shared.output, HandlerOutputId(0));
    assert_eq!(contract.shared.residual, draft.hidden[1].0);
    assert_eq!(contract.clauses.len(), draft.clauses.len());
    assert_eq!(recipe.template, draft.template);
    recipe
        .direct
        .as_ref()
        .unwrap()
        .assert_retained_contract(&contract.demands);
    assert_eq!(&*contract.state, draft.state.ty());
    assert_eq!(
        contract.provided.effect(),
        draft.clauses[0].operation().owner()
    );
    assert_ne!(contract.provided.effect(), contract.interpreted.effect());
    assert_ne!(contract.hidden[0].0, contract.hidden[1].0);
    assert_eq!(contract.hidden[0].1, crate::types::Kind::Type);
    assert_eq!(contract.hidden[1].1, crate::types::Kind::EffectRow);
    for (formal, _) in &contract.formals {
        assert!(contract.hidden.iter().all(|(hidden, _)| hidden != formal));
    }
    for output in &recipe.outputs {
        for clause in &output.clauses {
            assert!(recipe.nodes.get(clause.0).is_some());
        }
    }
    contract
        .clauses
        .iter()
        .zip(draft.clauses.iter())
        .map(|(retained, clause)| {
            assert_eq!(
                (retained.operation, retained.resume),
                (clause.operation(), clause.resume())
            );
            (retained.operation, retained.resume)
        })
        .collect()
}

#[cfg(test)]
pub(crate) fn erase_pending_function_latent_for_test(draft: &mut super::HandlerFragmentDraft) {
    let stored = draft
        .program
        .nodes
        .iter_mut()
        .find(|stored| {
            matches!(
                &stored.kind,
                EffectExprKind::Pure(super::PureExprKind::Value(super::PureValue::Function(_)))
            ) && stored
                .ty
                .function_view()
                .and_then(|view| view.effects())
                .is_some_and(|row| {
                    row.tail().is_some_and(|tail| {
                        matches!(
                            tail.variable(),
                            crate::types::EffectRowVariable::Inference(_)
                        )
                    })
                })
        })
        .expect("actual pending source function");
    let view = stored.ty.function_view().unwrap();
    let domain =
        crate::types::clone_type_with_budget(view.domain(), &mut TypeWorkBudget::unbounded())
            .unwrap();
    let result =
        crate::types::clone_type_with_budget(view.value(), &mut TypeWorkBudget::unbounded())
            .unwrap();
    crate::types::discard_type_iteratively(std::mem::replace(
        &mut stored.ty,
        crate::types::Type::Function(Box::new(domain), Box::new(result)),
    ));
}
