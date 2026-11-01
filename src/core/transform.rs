//! Bounded transformations over independently validated pure Core.

use std::{
    collections::HashMap,
    error::Error,
    fmt,
    ops::{Deref, DerefMut},
    sync::Arc,
};

use super::{
    BuildError, CoreBuilder, CoreMatchArm, CorePattern, CorePatternKind, NodeId, Primitive,
    PureComputation, PureExprKind, PureValue, UnvalidatedProgram, ValidatedProgram,
    dialect::{
        CoreOperationFamily, CoreTypedExpr, PureOperationFamily, UnvalidatedCoreProgram,
        ValidatedCoreProgram,
    },
    effect::{EffectClause, EffectExprKind, EffectOperation, EffectOperationFamily},
};
use crate::{
    source::{GeneratedReason, Origin},
    types::{IterativeTypeOwner, Type, discard_type_iteratively},
};

trait RebuildFields {
    fn ty(&self) -> &Type;
    fn effects(&self) -> &crate::types::EffectRow;
    fn origin(&self) -> Result<&Origin, TransformError>;
}

trait RebuildExpression<F: CoreOperationFamily>: RebuildFields {
    fn kind(&self) -> &F::Kind;
}
impl<F: CoreOperationFamily> RebuildFields for CoreTypedExpr<F> {
    fn ty(&self) -> &Type {
        &self.ty
    }
    fn effects(&self) -> &crate::types::EffectRow {
        self.effects()
    }
    fn origin(&self) -> Result<&Origin, TransformError> {
        Ok(&self.origin)
    }
}
impl<F: CoreOperationFamily> RebuildExpression<F> for CoreTypedExpr<F> {
    fn kind(&self) -> &F::Kind {
        &self.kind
    }
}
impl<F: CoreOperationFamily> RebuildFields for super::dialect::StoredNode<F> {
    fn ty(&self) -> &Type {
        &self.ty
    }
    fn effects(&self) -> &crate::types::EffectRow {
        F::effect_row(&self.effects)
    }
    fn origin(&self) -> Result<&Origin, TransformError> {
        self.origin
            .as_ref()
            .ok_or(TransformError::InvalidValidatedInput)
    }
}
impl<F: CoreOperationFamily> RebuildExpression<F> for super::dialect::StoredNode<F> {
    fn kind(&self) -> &F::Kind {
        &self.kind
    }
}

/// State shared by the existing identity copier and checked-module relocation.
/// Identity rebuilding uses the builder directly and retains its current work
/// accounting; a fragment transfer will also supply explicit identity mappings.
struct RebuildContext<'a, F: CoreOperationFamily> {
    builder: &'a mut CoreBuilder<F>,
    identities: Option<FragmentIdentityView<'a>>,
}

/// One fragment's complete mapping into the assembled Core namespace.
/// Resolver-qualified identities remain stable; generated identities and
/// handler owners are mapped separately for each source arena.
#[derive(Debug, Default)]
pub(crate) struct FragmentIdentities {
    pub(crate) binders: HashMap<crate::resolved::BinderId, crate::resolved::BinderId>,
    pub(crate) variables: HashMap<crate::types::TypeVariableId, crate::types::TypeVariableId>,
    pub(crate) handlers: HashMap<super::HandlerId, super::HandlerId>,
}

/// A method may freshen its own source type binders without copying the
/// fragment-wide binder, handler and generated-type inventories.
#[derive(Clone, Copy)]
pub(crate) struct FragmentIdentityView<'a> {
    pub(crate) base: &'a FragmentIdentities,
    pub(crate) variables:
        Option<&'a HashMap<crate::types::TypeVariableId, crate::types::TypeVariableId>>,
    preserve_completed_metadata: bool,
}

impl<'a> FragmentIdentityView<'a> {
    pub(crate) const fn new(
        base: &'a FragmentIdentities,
        variables: Option<&'a HashMap<crate::types::TypeVariableId, crate::types::TypeVariableId>>,
    ) -> Self {
        Self {
            base,
            variables,
            preserve_completed_metadata: false,
        }
    }

    pub(crate) const fn completed(base: &'a FragmentIdentities) -> Self {
        Self {
            base,
            variables: None,
            preserve_completed_metadata: true,
        }
    }

    pub(crate) fn variable(
        self,
        identity: &crate::types::TypeVariableId,
    ) -> Option<crate::types::TypeVariableId> {
        self.variables
            .and_then(|overlay| overlay.get(identity))
            .copied()
            .or_else(|| self.base.variables.get(identity).copied())
    }
}

/// Reusable storage for each checked owner in one source arena.
pub(crate) struct FragmentWorkspace {
    nodes: Vec<Option<NodeId>>,
    visits: Vec<u8>,
    touched: Vec<usize>,
}

impl FragmentWorkspace {
    pub(crate) fn new<S: CoreOperationFamily, D: CoreOperationFamily>(
        source: &CoreBuilder<S>,
        destination: &mut CoreBuilder<D>,
    ) -> Result<Self, TransformError> {
        let count = source.nodes.len();
        destination
            .charge_rebuild_work(count.checked_mul(2).ok_or(BuildError::TypeWorkExceeded)?)?;
        let mut nodes = Vec::new();
        nodes
            .try_reserve_exact(count)
            .map_err(|_| BuildError::TypeWorkExceeded)?;
        let mut visits = Vec::new();
        visits
            .try_reserve_exact(count)
            .map_err(|_| BuildError::TypeWorkExceeded)?;
        nodes.resize(count, None);
        visits.resize(count, 0);
        Ok(Self {
            nodes,
            visits,
            touched: Vec::new(),
        })
    }
}

/// Relocates the reachable nodes for one checked owner and type mapping.
///
/// A separate map is needed for each effective method-owner substitution:
/// sharing a source node does not make the two substitutions interchangeable.
/// The caller controls traversal and may replace a whole evidence occurrence
/// before visiting its obsolete source children.
pub(crate) struct FragmentNodeMap<'a> {
    identities: FragmentIdentityView<'a>,
    source_arena: super::dialect::ArenaId,
    destination_anchor: Option<NodeId>,
    workspace: &'a mut FragmentWorkspace,
}

impl<'a> FragmentNodeMap<'a> {
    pub(crate) fn new<S: CoreOperationFamily, D: CoreOperationFamily>(
        workspace: &'a mut FragmentWorkspace,
        source: &CoreBuilder<S>,
        source_root: NodeId,
        destination: &mut CoreBuilder<D>,
        identities: FragmentIdentityView<'a>,
    ) -> Result<Self, TransformError> {
        let root_index = node_index(source_root)?;
        source.node_at_ordinal(source_root, root_index)?;
        if source.nodes.len() != workspace.nodes.len() {
            return Err(BuildError::InvalidPayload.into());
        }
        destination.charge_rebuild_work(
            workspace
                .touched
                .len()
                .checked_mul(2)
                .and_then(|work| work.checked_add(1))
                .ok_or(BuildError::TypeWorkExceeded)?,
        )?;
        for index in workspace.touched.drain(..) {
            workspace.nodes[index] = None;
            workspace.visits[index] = 0;
        }
        Ok(Self {
            identities,
            source_arena: source_root.arena(),
            destination_anchor: None,
            workspace,
        })
    }

    /// Starts a node once for this owner; a back-edge fails closed.
    pub(crate) fn enter<S: CoreOperationFamily, D: CoreOperationFamily>(
        &mut self,
        source: &CoreBuilder<S>,
        original: NodeId,
        destination: &mut CoreBuilder<D>,
    ) -> Result<bool, TransformError> {
        destination.charge_rebuild_work(1)?;
        let index = self.source_index(source, original)?;
        self.check_destination_builder(destination)?;
        match self.workspace.visits[index] {
            0 => {
                self.track(index, destination)?;
                Ok(true)
            }
            2 => Ok(false),
            _ => Err(BuildError::InvalidPayload.into()),
        }
    }

    /// Publishes a complete replacement, without inspecting the old children.
    pub(crate) fn replace<S: CoreOperationFamily, D: CoreOperationFamily>(
        &mut self,
        source: &CoreBuilder<S>,
        original: NodeId,
        destination: &mut CoreBuilder<D>,
        replacement: NodeId,
    ) -> Result<(), TransformError> {
        destination.charge_rebuild_work(1)?;
        let index = self.check_source(source, original)?;
        self.check_destination(destination, replacement)?;
        self.track(index, destination)?;
        self.publish(index, replacement);
        Ok(())
    }

    pub(crate) fn copy_effect(
        &mut self,
        source: &CoreBuilder<EffectOperationFamily>,
        original: NodeId,
        destination: &mut CoreBuilder<EffectOperationFamily>,
    ) -> Result<NodeId, TransformError> {
        self.check_destination_builder(destination)?;
        let expression = self.checked_children(source, original, destination)?;
        let index = node_index(original)?;
        self.track(index, destination)?;
        let mut context = RebuildContext {
            builder: destination,
            identities: Some(self.identities),
        };
        let rebuilt = rebuild_nonfold_node(&mut context, &self.workspace.nodes, expression)?;
        self.publish(index, rebuilt);
        Ok(rebuilt)
    }

    pub(crate) fn copy_pure(
        &mut self,
        source: &CoreBuilder<PureOperationFamily>,
        original: NodeId,
        destination: &mut CoreBuilder<PureOperationFamily>,
    ) -> Result<NodeId, TransformError> {
        self.check_destination_builder(destination)?;
        let expression = self.checked_children(source, original, destination)?;
        let index = node_index(original)?;
        self.track(index, destination)?;
        let mut context = RebuildContext {
            builder: destination,
            identities: Some(self.identities),
        };
        let rebuilt = rebuild_nonfold_node(&mut context, &self.workspace.nodes, expression)?;
        self.publish(index, rebuilt);
        Ok(rebuilt)
    }

    /// Lifts only the compiler-owned Foreign primitives whose checked Pure
    /// representation is unchanged in Effect Core. Other pure expressions
    /// may require Effect-specific region lowering and are not lifted here.
    pub(crate) fn copy_foreign_pure_as_effect(
        &mut self,
        source: &CoreBuilder<PureOperationFamily>,
        original: NodeId,
        destination: &mut CoreBuilder<EffectOperationFamily>,
    ) -> Result<NodeId, TransformError> {
        self.check_destination_builder(destination)?;
        let expression = self.checked_children(source, original, destination)?;
        match &expression.kind {
            PureExprKind::Value(PureValue::Intrinsic(node))
                if node.module().is_builtin_foreign()
                    && matches!(
                        node.operation(),
                        super::packed::Intrinsic::AddressNull
                            | super::packed::Intrinsic::AddressIsNull
                            | super::packed::Intrinsic::AddressEqual
                    ) => {}
            PureExprKind::Computation(PureComputation::TypeAbstraction(_)) => {}
            _ => return Err(BuildError::InvalidPayload.into()),
        }
        let index = node_index(original)?;
        self.track(index, destination)?;
        let mut context = RebuildContext {
            builder: destination,
            identities: Some(self.identities),
        };
        let rebuilt = rebuild_pure_node(
            &mut context,
            &self.workspace.nodes,
            expression,
            &expression.kind,
        )?;
        self.publish(index, rebuilt);
        Ok(rebuilt)
    }

    pub(crate) fn mapped(&self, original: NodeId) -> Result<NodeId, TransformError> {
        if original.arena() != self.source_arena {
            return Err(BuildError::InvalidNodeId.into());
        }
        remap(&self.workspace.nodes, original)
    }

    fn source_index<S: CoreOperationFamily>(
        &self,
        source: &CoreBuilder<S>,
        original: NodeId,
    ) -> Result<usize, TransformError> {
        let index = node_index(original)?;
        if original.arena() != self.source_arena {
            return Err(BuildError::InvalidNodeId.into());
        }
        source.node_at_ordinal(original, index)?;
        if self.workspace.nodes.get(index).is_none() {
            return Err(BuildError::InvalidNodeId.into());
        }
        Ok(index)
    }

    fn check_source<S: CoreOperationFamily>(
        &self,
        source: &CoreBuilder<S>,
        original: NodeId,
    ) -> Result<usize, TransformError> {
        let index = self.source_index(source, original)?;
        if self.workspace.nodes[index].is_some() {
            return Err(BuildError::InvalidPayload.into());
        }
        Ok(index)
    }

    fn check_destination<D: CoreOperationFamily>(
        &self,
        destination: &CoreBuilder<D>,
        node: NodeId,
    ) -> Result<(), TransformError> {
        if self
            .destination_anchor
            .is_some_and(|anchor| anchor.arena() != node.arena())
        {
            return Err(BuildError::InvalidNodeId.into());
        }
        destination.node_at_ordinal(node, node_index(node)?)?;
        Ok(())
    }

    fn check_destination_builder<D: CoreOperationFamily>(
        &self,
        destination: &CoreBuilder<D>,
    ) -> Result<(), TransformError> {
        if let Some(anchor) = self.destination_anchor {
            self.check_destination(destination, anchor)?;
        }
        Ok(())
    }

    fn checked_children<'s, S: CoreOperationFamily, D: CoreOperationFamily>(
        &self,
        source: &'s CoreBuilder<S>,
        original: NodeId,
        destination: &mut CoreBuilder<D>,
    ) -> Result<&'s super::dialect::StoredNode<S>, TransformError> {
        let index = self.check_source(source, original)?;
        let expression = source.nodes.get(index).ok_or(BuildError::InvalidNodeId)?;
        let child_count = S::child_count(&expression.kind);
        destination.charge_rebuild_work(child_count)?;
        let capture_count =
            S::region_closure(&expression.kind).map_or(0, |closure| closure.captures.len());
        for child_index in 0..child_count {
            if !self.identities.preserve_completed_metadata
                && (1..=capture_count).contains(&child_index)
            {
                continue;
            }
            let child =
                S::child_at(&expression.kind, child_index).ok_or(BuildError::InvalidPayload)?;
            if child.arena() != self.source_arena {
                return Err(BuildError::InvalidNodeId.into());
            }
            let mapped = self.mapped(child)?;
            self.check_destination(destination, mapped)?;
        }
        Ok(expression)
    }

    fn track<D: CoreOperationFamily>(
        &mut self,
        index: usize,
        destination: &mut CoreBuilder<D>,
    ) -> Result<(), TransformError> {
        match self.workspace.visits[index] {
            0 => {
                destination.charge_rebuild_work(1)?;
                self.workspace
                    .touched
                    .try_reserve(1)
                    .map_err(|_| BuildError::TypeWorkExceeded)?;
                self.workspace.touched.push(index);
                self.workspace.visits[index] = 1;
            }
            1 => {}
            _ => return Err(BuildError::InvalidPayload.into()),
        }
        Ok(())
    }

    fn publish(&mut self, index: usize, replacement: NodeId) {
        debug_assert_eq!(self.workspace.visits[index], 1);
        debug_assert!(self.workspace.nodes[index].is_none());
        debug_assert!(
            self.destination_anchor
                .is_none_or(|anchor| anchor.arena() == replacement.arena())
        );
        self.destination_anchor.get_or_insert(replacement);
        self.workspace.nodes[index] = Some(replacement);
        self.workspace.visits[index] = 2;
    }
}

impl<F: CoreOperationFamily> Deref for RebuildContext<'_, F> {
    type Target = CoreBuilder<F>;

    fn deref(&self) -> &Self::Target {
        self.builder
    }
}

impl<F: CoreOperationFamily> DerefMut for RebuildContext<'_, F> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.builder
    }
}

trait TransformFamily: CoreOperationFamily {
    fn collect_operation_binders(
        kind: &Self::Kind,
        binders: &mut Vec<crate::resolved::BinderId>,
        builder: &mut CoreBuilder<Self>,
    ) -> Result<(), TransformError>;
    fn rebuild_operation(
        builder: &mut RebuildContext<'_, Self>,
        remapped: &[Option<NodeId>],
        expression: &impl RebuildExpression<Self>,
    ) -> Result<NodeId, TransformError>;
}

impl TransformFamily for PureOperationFamily {
    fn collect_operation_binders(
        _: &Self::Kind,
        _: &mut Vec<crate::resolved::BinderId>,
        _: &mut CoreBuilder<Self>,
    ) -> Result<(), TransformError> {
        Ok(())
    }
    fn rebuild_operation(
        _: &mut RebuildContext<'_, Self>,
        _: &[Option<NodeId>],
        _: &impl RebuildExpression<Self>,
    ) -> Result<NodeId, TransformError> {
        Err(TransformError::InvalidValidatedInput)
    }
}

impl TransformFamily for EffectOperationFamily {
    fn collect_operation_binders(
        kind: &Self::Kind,
        binders: &mut Vec<crate::resolved::BinderId>,
        _builder: &mut CoreBuilder<Self>,
    ) -> Result<(), TransformError> {
        if let EffectExprKind::Operation(EffectOperation::Resource(resource)) = kind {
            binders.push(resource.handle.id());
        }
        if let EffectExprKind::Operation(EffectOperation::Store(store)) = kind {
            binders.push(store.handle.id());
        }
        if let EffectExprKind::Operation(EffectOperation::Continue(continuation)) = kind {
            binders.push(continuation.adapter.answer.id());
        }
        if let EffectExprKind::Operation(EffectOperation::Region(scope)) = kind {
            binders.push(scope.access.id());
        }
        if let EffectExprKind::Operation(EffectOperation::RegionClosure(closure)) = kind
            && let Some(function) = closure.code.function()
        {
            binders.push(function.parameter().id());
        }
        let handler = match kind {
            EffectExprKind::Operation(EffectOperation::Handler(handler)) => handler,
            _ => return Ok(()),
        };
        for clause in handler.clauses() {
            binders.extend(clause.pattern().binder_iter().map(|binder| binder.id()));
        }
        Ok(())
    }

    fn rebuild_operation(
        builder: &mut RebuildContext<'_, Self>,
        remapped: &[Option<NodeId>],
        expression: &impl RebuildExpression<Self>,
    ) -> Result<NodeId, TransformError> {
        let EffectExprKind::Operation(operation) = expression.kind() else {
            return Err(TransformError::InvalidValidatedInput);
        };
        let ty = IterativeTypeOwner::new(copy_type(builder, expression.ty())?);
        let effects = copy_expression_row(builder, expression)?;
        let origin = copy_origin(builder, expression.origin()?)?;
        match operation {
            EffectOperation::Network(network) => {
                if builder.identities.is_none() || network.linked_result.is_some() {
                    return Err(TransformError::InvalidValidatedInput);
                }
                let handle_type = copy_type(builder, network.handle.ty())?;
                let handle_id = copy_binder_id(builder, network.handle.id())?;
                let handle_origin = copy_origin(builder, network.handle.origin())?;
                let handle = builder.resolved_binder(handle_id, handle_type, handle_origin)?;
                let mut acquisition = network.acquisition;
                acquisition.identity = copy_variable_id(builder, acquisition.identity)?;
                acquisition.handle = copy_binder_id(builder, acquisition.handle)?;
                let entries = [
                    copy_binder_id(builder, network.entries[0])?,
                    copy_binder_id(builder, network.entries[1])?,
                ];
                builder.charge_effect_metadata(1)?;
                builder.network_scope(
                    Box::new(super::effect::NetworkScopeNode::new(
                        acquisition,
                        handle,
                        entries,
                        remap(remapped, network.capacity)?,
                        [
                            remap(remapped, network.inputs[0])?,
                            remap(remapped, network.inputs[1])?,
                        ],
                        remap(remapped, network.body)?,
                    )),
                    ty.into_inner(),
                    effects,
                    origin,
                )
            }
            EffectOperation::RegionValueRequest(request) => builder.region_operation(
                EffectOperation::RegionValueRequest(request.clone()),
                ty.into_inner(),
                effects,
                origin,
            ),
            EffectOperation::RegionBuffer(buffer) => {
                use super::region::RegionBufferOperation;
                let operation = match &buffer.operation {
                    RegionBufferOperation::Network { effect, operation } => {
                        if builder.identities.is_none() {
                            return Err(TransformError::InvalidValidatedInput);
                        }
                        RegionBufferOperation::Network {
                            effect: copy_effect_instance(builder, effect)?,
                            operation: *operation,
                        }
                    }
                    RegionBufferOperation::Intrinsic(intrinsic) if builder.identities.is_some() => {
                        RegionBufferOperation::Intrinsic(super::packed::IntrinsicNode::new(
                            copy_intrinsic(builder, intrinsic.operation())?,
                            intrinsic.module(),
                        ))
                    }
                    operation => operation.clone(),
                };
                builder.region_operation(
                    EffectOperation::RegionBuffer(super::region::RegionBufferNode {
                        api: buffer.api,
                        context: remap(remapped, buffer.context)?,
                        operand: buffer.operand.map(|id| remap(remapped, id)).transpose()?,
                        right: buffer.right.map(|id| remap(remapped, id)).transpose()?,
                        operation,
                    }),
                    ty.into_inner(),
                    effects,
                    origin,
                )
            }
            EffectOperation::RegionTuple(tuple) => {
                let mut fields = Vec::new();
                builder.charge_effect_metadata(tuple.fields.len())?;
                fields
                    .try_reserve_exact(tuple.fields.len())
                    .map_err(|_| BuildError::TypeWorkExceeded)?;
                for field in &tuple.fields {
                    fields.push(remap(remapped, *field)?);
                }
                builder.region_operation(
                    EffectOperation::RegionTuple(super::region::RegionTupleNode {
                        constructor: tuple.constructor,
                        api: tuple.api,
                        context: remap(remapped, tuple.context)?,
                        storage: remap(remapped, tuple.storage)?,
                        fields: fields.into_boxed_slice(),
                    }),
                    ty.into_inner(),
                    effects,
                    origin,
                )
            }
            EffectOperation::RegionClosure(closure) => {
                let code = if let Some(function) = closure.code.function() {
                    let parameter = function.parameter();
                    let parameter_type = copy_type(builder, parameter.ty())?;
                    let parameter_id = copy_binder_id(builder, parameter.id())?;
                    let parameter_origin = copy_origin(builder, parameter.origin())?;
                    let parameter =
                        builder.resolved_binder(parameter_id, parameter_type, parameter_origin)?;
                    super::region::RegionClosureCode::Function(super::function::FunctionNode::new(
                        parameter,
                        remap(remapped, closure.code.body())?,
                    ))
                } else {
                    super::region::RegionClosureCode::Adapter {
                        body: remap(remapped, closure.code.body())?,
                    }
                };
                let mut captures = Vec::new();
                if builder
                    .identities
                    .is_none_or(|identities| identities.preserve_completed_metadata)
                {
                    builder.charge_effect_metadata(closure.captures.len())?;
                    captures
                        .try_reserve_exact(closure.captures.len())
                        .map_err(|_| BuildError::TypeWorkExceeded)?;
                    for capture in &closure.captures {
                        captures.push(remap(remapped, *capture)?);
                    }
                }
                builder.region_operation(
                    EffectOperation::RegionClosure(super::region::RegionClosureNode {
                        api: closure.api,
                        context: remap(remapped, closure.context)?,
                        storage: remap(remapped, closure.storage)?,
                        captures: captures.into_boxed_slice(),
                        code,
                    }),
                    ty.into_inner(),
                    effects,
                    origin,
                )
            }
            EffectOperation::Region(scope) => {
                let access_type = copy_type(builder, scope.access.ty())?;
                let access_id = copy_binder_id(builder, scope.access.id())?;
                let access_origin = copy_origin(builder, scope.access.origin())?;
                let access = builder.resolved_binder(access_id, access_type, access_origin)?;
                let identity = copy_variable_id(builder, scope.identity)?;
                builder.region_operation(
                    EffectOperation::Region(Box::new(super::region::RegionScopeNode {
                        entry: scope.entry,
                        api: scope.api,
                        identity,
                        access,
                        preceding: remap(remapped, scope.preceding)?,
                        provider: remap(remapped, scope.provider)?,
                        body: remap(remapped, scope.body)?,
                    })),
                    ty.into_inner(),
                    effects,
                    origin,
                )
            }
            EffectOperation::RegionAllocate(allocation) => builder.region_operation(
                EffectOperation::RegionAllocate(super::region::RegionAllocateNode {
                    api: allocation.api,
                    context: remap(remapped, allocation.context)?,
                    request: remap(remapped, allocation.request)?,
                }),
                ty.into_inner(),
                effects,
                origin,
            ),
            EffectOperation::Cleanup(scope) => {
                let callback = copy_binder_id(builder, scope.callback)?;
                builder.cleanup_scope(
                    super::effect::CleanupScopeNode {
                        callback,
                        body: remap(remapped, scope.body)?,
                        action: remap(remapped, scope.action)?,
                        ..*scope
                    },
                    ty.into_inner(),
                    effects,
                    origin,
                )
            }
            EffectOperation::Registration(scope) => {
                let callback = copy_binder_id(builder, scope.callback)?;
                let handler = copy_handler_id(builder, scope.handler)?;
                builder.registration_scope(
                    super::effect::RegistrationScopeNode {
                        callback,
                        handler,
                        body: remap(remapped, scope.body)?,
                        ..*scope
                    },
                    ty.into_inner(),
                    effects,
                    origin,
                )
            }
            EffectOperation::Resource(resource) => {
                let handle_type =
                    IterativeTypeOwner::new(copy_type(builder, resource.handle.ty())?);
                let handle_id = copy_binder_id(builder, resource.handle.id())?;
                let handle_origin = copy_origin(builder, resource.handle.origin())?;
                let handle =
                    builder.resolved_binder(handle_id, handle_type.into_inner(), handle_origin)?;
                let mut acquisition = resource.acquisition;
                acquisition.identity = copy_variable_id(builder, acquisition.identity)?;
                acquisition.handle = copy_binder_id(builder, acquisition.handle)?;
                acquisition.provider = copy_lexical_id(builder, acquisition.provider)?;
                builder.resource_scope(
                    Box::new(super::effect::ResourceScopeNode {
                        acquisition,
                        handle,
                        initializer: remap(remapped, resource.initializer)?,
                        body: remap(remapped, resource.body)?,
                    }),
                    ty.into_inner(),
                    effects,
                    origin,
                )
            }
            EffectOperation::Store(store) => {
                let handle_type = IterativeTypeOwner::new(copy_type(builder, store.handle.ty())?);
                let handle_id = copy_binder_id(builder, store.handle.id())?;
                let handle_origin = copy_origin(builder, store.handle.origin())?;
                let handle =
                    builder.resolved_binder(handle_id, handle_type.into_inner(), handle_origin)?;
                let mut acquisition = store.acquisition;
                acquisition.identity = copy_variable_id(builder, acquisition.identity)?;
                acquisition.handle = copy_binder_id(builder, acquisition.handle)?;
                builder.store_scope(
                    Box::new(super::effect::StoreScopeNode::new(
                        acquisition,
                        handle,
                        remap(remapped, store.initializer)?,
                        remap(remapped, store.body)?,
                    )),
                    ty.into_inner(),
                    effects,
                    origin,
                )
            }
            EffectOperation::Continue(continuation) => {
                let answer = &continuation.adapter.answer;
                let answer_type = IterativeTypeOwner::new(copy_type(builder, answer.ty())?);
                let answer_id = copy_binder_id(builder, answer.id())?;
                let answer_origin = copy_origin(builder, answer.origin())?;
                let answer =
                    builder.resolved_binder(answer_id, answer_type.into_inner(), answer_origin)?;
                builder.continue_control(
                    super::effect::ContinueNode {
                        store: remap(remapped, continuation.store)?,
                        key: remap(remapped, continuation.key)?,
                        adapter: Box::new(super::effect::ContinueAdapter {
                            answer,
                            some: remap(remapped, continuation.adapter.some)?,
                            none: remap(remapped, continuation.adapter.none)?,
                        }),
                    },
                    ty.into_inner(),
                    effects,
                    origin,
                )
            }
            EffectOperation::RetainedRoot(root) => builder.retained_root(
                super::effect::RetainedRootNode {
                    store: remap(remapped, root.store)?,
                    handler: remap(remapped, root.handler)?,
                },
                ty.into_inner(),
                effects,
                origin,
            ),
            EffectOperation::Retain(retain) => {
                let handler = copy_handler_id(builder, retain.handler)?;
                let owner = copy_resume_id(builder, retain.owner)?;
                builder.retain_control(
                    super::effect::RetainNode { handler, owner },
                    ty.into_inner(),
                    effects,
                    origin,
                )
            }

            EffectOperation::NativeInterpret(boundary) => {
                let copied = (|| -> Result<_, TransformError> {
                    builder.charge_effect_metadata(boundary.interpretations().len())?;
                    let mut interpretations = Vec::new();
                    interpretations
                        .try_reserve_exact(boundary.interpretations().len())
                        .map_err(|_| BuildError::TypeWorkExceeded)?;
                    for interpretation in boundary.interpretations() {
                        let effect = copy_effect_instance(builder, interpretation.effect())?;
                        interpretations.push(super::effect::NativeInterpretation::new(
                            effect,
                            Arc::clone(interpretation.symbol()),
                        ));
                    }
                    let body = remap(remapped, boundary.body())?;
                    Ok((body, interpretations.into_boxed_slice()))
                })();
                let (body, interpretations) = match copied {
                    Ok(copied) => copied,
                    Err(error) => {
                        crate::source::discard_origin_iteratively(origin);
                        return Err(error);
                    }
                };
                builder.native_interpret(body, interpretations, ty.into_inner(), effects, origin)
            }
            EffectOperation::Request(node) => {
                let effect = copy_effect_instance(builder, node.effect())?;
                builder.request(
                    effect,
                    node.operation(),
                    remap(remapped, node.operand())?,
                    ty.into_inner(),
                    effects,
                    origin,
                )
            }
            EffectOperation::Resume(node) => {
                let handler = copy_handler_id(builder, node.handler())?;
                let owner = copy_resume_id(builder, node.owner())?;
                builder.resume(
                    handler,
                    owner,
                    node.use_state(),
                    remap(remapped, node.value())?,
                    ty.into_inner(),
                    effects,
                    origin,
                )
            }
            EffectOperation::Discard(node) => {
                let handler = copy_handler_id(builder, node.handler())?;
                let owner = copy_resume_id(builder, node.owner())?;
                builder.discard(
                    handler,
                    owner,
                    node.use_state(),
                    ty.into_inner(),
                    effects,
                    origin,
                )
            }
            EffectOperation::Handler(node) => {
                let registration = node
                    .hook_registration
                    .as_ref()
                    .map(|registration| {
                        builder.charge_effect_metadata(1)?;
                        let mut copied = registration
                            .with_target(copy_effect_instance(builder, &registration.target)?);
                        copied.callback = copy_binder_id(builder, copied.callback)?;
                        copied.input = copy_binder_id(builder, copied.input)?;
                        copied.previous = copy_binder_id(builder, copied.previous)?;
                        copied.next = copy_binder_id(builder, copied.next)?;
                        copied.resume = copy_resume_id(builder, copied.resume)?;
                        Ok::<_, TransformError>(Box::new(copied))
                    })
                    .transpose()?;
                let effect = copy_effect_instance(builder, node.effect())?;
                let root = node
                    .hook_root()
                    .map(|root| {
                        builder.charge_effect_metadata(1)?;
                        let mut copied =
                            root.with_target(copy_effect_instance(builder, &root.target)?);
                        copied.input = copy_binder_id(builder, copied.input)?;
                        copied.resume = copy_resume_id(builder, copied.resume)?;
                        Ok::<_, TransformError>(copied)
                    })
                    .transpose()?;
                let body = remap(remapped, node.body())?;
                let mut clauses = Vec::new();
                builder.charge_effect_metadata(node.clauses().len())?;
                clauses
                    .try_reserve_exact(node.clauses().len())
                    .map_err(|_| TransformError::Build(BuildError::TypeWorkExceeded))?;
                for clause in node.clauses() {
                    let clause_body = remap(remapped, clause.body())?;
                    let resume = copy_resume_id(builder, clause.resume())?;
                    let clause_origin = copy_origin(builder, clause.origin())?;
                    clauses.push(EffectClause::new(
                        clause.operation(),
                        resume,
                        CoreMatchArm::new(
                            rebuild_pattern_in_context(builder, clause.pattern())?,
                            clause_body,
                            clause_origin,
                        ),
                    ));
                }
                let handler_id = copy_handler_id(builder, node.id())?;
                builder.handler_with_contracts(
                    handler_id,
                    body,
                    effect,
                    clauses,
                    ty.into_inner(),
                    effects,
                    origin,
                    root,
                    registration,
                )
            }
        }
        .map_err(TransformError::from)
    }
}

// Keep scope construction temporaries off the shared operation frame: ordinary
// handlers must still rebuild on the established small stack. This moves the
// existing charged/fallible copies without adding allocation or changing order.

fn clone_effect_instance<F: CoreOperationFamily>(
    builder: &mut RebuildContext<'_, F>,
    instance: &crate::types::EffectInstance,
) -> Result<crate::types::EffectInstance, TransformError> {
    super::effect::clone_effect_instance_with_budget(instance, &mut builder.type_work)
        .map_err(TransformError::from)
}

fn copy_type<F: CoreOperationFamily>(
    builder: &mut RebuildContext<'_, F>,
    ty: &Type,
) -> Result<Type, BuildError> {
    let Some(identities) = builder.identities else {
        return builder.clone_type_for_rebuild(ty);
    };
    crate::types::rename_fragment_type_with(
        ty,
        &identities.base.variables,
        identities.variables,
        |units| builder.charge_rebuild_work(units),
        || BuildError::TypeWorkExceeded,
    )?
    .map_err(|_| BuildError::InvalidPayload)
}
fn copy_row<F: CoreOperationFamily>(
    builder: &mut RebuildContext<'_, F>,
    row: &crate::types::EffectRow,
) -> Result<crate::types::EffectRow, BuildError> {
    let Some(identities) = builder.identities else {
        return builder.clone_effect_row_for_rebuild(row);
    };
    crate::types::rename_fragment_row_with(
        row,
        &identities.base.variables,
        identities.variables,
        |units| builder.charge_rebuild_work(units),
        || BuildError::TypeWorkExceeded,
    )?
    .map_err(|_| BuildError::InvalidPayload)
}
fn copy_expression_row<F: CoreOperationFamily>(
    builder: &mut RebuildContext<'_, F>,
    expression: &impl RebuildFields,
) -> Result<crate::types::EffectRow, BuildError> {
    copy_row(builder, expression.effects())
}
fn copy_effect_instance<F: CoreOperationFamily>(
    builder: &mut RebuildContext<'_, F>,
    instance: &crate::types::EffectInstance,
) -> Result<crate::types::EffectInstance, TransformError> {
    let Some(identities) = builder.identities else {
        return clone_effect_instance(builder, instance);
    };
    builder.charge_effect_metadata(instance.arguments().len())?;
    let mut arguments = IterativeArgumentBuffer(Vec::new());
    arguments
        .0
        .try_reserve_exact(instance.arguments().len())
        .map_err(|_| BuildError::TypeWorkExceeded)?;
    for argument in instance.arguments() {
        let copied = crate::types::rename_fragment_argument_with(
            argument,
            &identities.base.variables,
            identities.variables,
            |units| builder.charge_rebuild_work(units),
            || BuildError::TypeWorkExceeded,
        )?
        .map_err(|_| BuildError::InvalidPayload)?;
        arguments.0.push(copied);
    }
    Ok(crate::types::EffectInstance::new_kinded(
        instance.effect(),
        arguments.into_boxed_slice(),
    ))
}
fn copy_origin<F: CoreOperationFamily>(
    _builder: &mut RebuildContext<'_, F>,
    origin: &Origin,
) -> Result<Origin, TransformError> {
    Ok(origin.clone())
}
macro_rules! copy_identity {
    ($function:ident,$method:ident,$identity:ty) => {
        fn $function<F: CoreOperationFamily>(
            _builder: &mut RebuildContext<'_, F>,
            identity: $identity,
        ) -> Result<$identity, BuildError> {
            Ok(identity)
        }
    };
}
fn copy_binder_id<F: CoreOperationFamily>(
    builder: &mut RebuildContext<'_, F>,
    identity: crate::resolved::BinderId,
) -> Result<crate::resolved::BinderId, BuildError> {
    let Some(identities) = builder.identities else {
        return Ok(identity);
    };
    builder.charge_rebuild_work(1)?;
    match identity {
        crate::resolved::BinderId::Generated(_) => identities
            .base
            .binders
            .get(&identity)
            .copied()
            .ok_or(BuildError::InvalidPayload),
        crate::resolved::BinderId::Resolved { .. } => Ok(identity),
    }
}

fn copy_variable_id<F: CoreOperationFamily>(
    builder: &mut RebuildContext<'_, F>,
    identity: crate::types::TypeVariableId,
) -> Result<crate::types::TypeVariableId, BuildError> {
    let Some(identities) = builder.identities else {
        return Ok(identity);
    };
    builder.charge_rebuild_work(1)?;
    if identities.variables.is_some() {
        builder.charge_rebuild_work(1)?;
    }
    match identities.variable(&identity) {
        Some(mapped) => Ok(mapped),
        None if matches!(identity, crate::types::TypeVariableId::Resolved { .. }) => Ok(identity),
        None => Err(BuildError::InvalidPayload),
    }
}

fn copy_handler_id<F: CoreOperationFamily>(
    builder: &mut RebuildContext<'_, F>,
    identity: super::HandlerId,
) -> Result<super::HandlerId, BuildError> {
    let Some(identities) = builder.identities else {
        return Ok(identity);
    };
    builder.charge_rebuild_work(1)?;
    identities
        .base
        .handlers
        .get(&identity)
        .copied()
        .ok_or(BuildError::InvalidPayload)
}
copy_identity!(copy_resume_id, resume, crate::resolved::ResumeId);
copy_identity!(copy_nominal_id, nominal, crate::types::NominalTypeId);
copy_identity!(
    copy_constructor_id,
    constructor,
    crate::types::ConstructorId
);
copy_identity!(
    copy_lexical_id,
    lexical,
    crate::interface::LexicalEvidenceId
);

fn copy_intrinsic<F: CoreOperationFamily>(
    builder: &mut RebuildContext<'_, F>,
    operation: super::packed::Intrinsic,
) -> Result<super::packed::Intrinsic, BuildError> {
    use super::packed::Intrinsic;
    Ok(match operation {
        Intrinsic::RegionHostAllocate {
            owner,
            configuration,
        } => Intrinsic::RegionHostAllocate {
            owner: copy_variable_id(builder, owner)?,
            configuration,
        },
        Intrinsic::RegionHostRelease {
            owner,
            configuration,
        } => Intrinsic::RegionHostRelease {
            owner: copy_variable_id(builder, owner)?,
            configuration,
        },
        Intrinsic::RegionFromBacking {
            owner,
            address_module,
        } => Intrinsic::RegionFromBacking {
            owner: copy_variable_id(builder, owner)?,
            address_module,
        },
        operation => operation,
    })
}

struct IterativeArgumentBuffer(Vec<crate::types::KindedArgument>);

impl IterativeArgumentBuffer {
    fn into_boxed_slice(mut self) -> Box<[crate::types::KindedArgument]> {
        std::mem::take(&mut self.0).into_boxed_slice()
    }
}

impl Drop for IterativeArgumentBuffer {
    fn drop(&mut self) {
        for argument in self.0.drain(..) {
            crate::types::discard_kinded_argument_iteratively(argument);
        }
    }
}

struct IterativeTypeBuffer(Vec<Type>);

impl IterativeTypeBuffer {
    fn push(&mut self, ty: Type) {
        self.0.push(ty);
    }

    fn try_reserve(&mut self, additional: usize) -> Result<(), std::collections::TryReserveError> {
        self.0.try_reserve(additional)
    }

    fn into_vec(mut self) -> Vec<Type> {
        std::mem::take(&mut self.0)
    }
}

impl Drop for IterativeTypeBuffer {
    fn drop(&mut self) {
        for ty in self.0.drain(..) {
            discard_type_iteratively(ty);
        }
    }
}

struct CorePatternOwner(Option<CorePattern>);

impl CorePatternOwner {
    const fn new(pattern: CorePattern) -> Self {
        Self(Some(pattern))
    }

    fn into_inner(mut self) -> CorePattern {
        self.0.take().expect("a Core pattern transfers once")
    }
}

impl Drop for CorePatternOwner {
    fn drop(&mut self) {
        if let Some(pattern) = self.0.take() {
            pattern.discard_iteratively();
        }
    }
}

struct CorePatternBuffer(Vec<CorePattern>);

impl CorePatternBuffer {
    fn push(&mut self, pattern: CorePattern) {
        self.0.push(pattern);
    }

    fn pop(&mut self) -> Option<CorePatternOwner> {
        self.0.pop().map(CorePatternOwner::new)
    }

    fn len(&self) -> usize {
        self.0.len()
    }

    fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    fn append_suffix_to(&mut self, start: usize, destination: &mut Self) {
        let destination_start = destination.len();
        while self.len() > start {
            if let Some(pattern) = self.pop() {
                destination.push(pattern.into_inner());
            }
        }
        destination.0[destination_start..].reverse();
    }

    fn into_boxed_slice(mut self) -> Box<[CorePattern]> {
        std::mem::take(&mut self.0).into_boxed_slice()
    }
}

impl Drop for CorePatternBuffer {
    fn drop(&mut self) {
        for pattern in self.0.drain(..) {
            pattern.discard_iteratively();
        }
    }
}

/// Why a validated Core traversal could not construct unchecked output.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum TransformError {
    /// The output builder could not represent a transformed payload.
    Build(BuildError),
    /// A supposedly validated graph did not satisfy a traversal invariant.
    InvalidValidatedInput,
}

impl fmt::Display for TransformError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Build(error) => write!(formatter, "Core transformation failed: {error}"),
            Self::InvalidValidatedInput => {
                formatter.write_str("validated Core transformation state is inconsistent")
            }
        }
    }
}

impl Error for TransformError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            Self::Build(error) => Some(error),
            Self::InvalidValidatedInput => None,
        }
    }
}

impl From<BuildError> for TransformError {
    fn from(error: BuildError) -> Self {
        Self::Build(error)
    }
}

/// Rebuilds a validated program without changing its typed structure or origins.
///
/// The result deliberately returns to the unchecked boundary and must pass
/// independent validation before another validated-only consumer may use it.
///
/// # Errors
///
/// Returns a typed failure when output construction cannot represent the
/// input or when a validated-input invariant is unexpectedly absent.
pub fn identity_traversal(
    program: &ValidatedProgram,
) -> Result<UnvalidatedProgram, TransformError> {
    rebuild(program, false)
}

/// Folds primitive addition and multiplication whose operands are literals.
///
/// Every folded literal keeps the operation's exact result type and records a
/// generated origin whose cause is the replaced operation. The result returns
/// to the unchecked boundary for independent validation.
///
/// # Errors
///
/// Returns a typed failure when output construction cannot represent the
/// transform or when a validated-input invariant is unexpectedly absent.
pub fn fold_literal_primitives(
    program: &ValidatedProgram,
) -> Result<UnvalidatedProgram, TransformError> {
    rebuild(program, true)
}

/// Rebuilds every family in validated effect Core.
pub fn identity_effect_traversal(
    program: &super::ValidatedEffectProgram,
) -> Result<super::UnvalidatedEffectProgram, TransformError> {
    rebuild(program, false)
}

/// Folds pure literal primitives inside validated effect Core.
pub fn fold_effect_literal_primitives(
    program: &super::ValidatedEffectProgram,
) -> Result<super::UnvalidatedEffectProgram, TransformError> {
    rebuild(program, true)
}

fn rebuild<F: TransformFamily>(
    program: &ValidatedCoreProgram<F>,
    fold_literal_primitives: bool,
) -> Result<UnvalidatedCoreProgram<F>, TransformError> {
    rebuild_with_initial_type_work(program, fold_literal_primitives, 0)
}

fn rebuild_with_initial_type_work<F: TransformFamily>(
    program: &ValidatedCoreProgram<F>,
    fold_literal_primitives: bool,
    initial_type_work: usize,
) -> Result<UnvalidatedCoreProgram<F>, TransformError> {
    let mut builder = CoreBuilder::<F>::with_registry_and_method_evidence(
        Arc::clone(program.registry()),
        Arc::clone(program.method_evidence()),
    )?;
    #[cfg(test)]
    builder.charge_type_work_for_test(initial_type_work)?;
    #[cfg(not(test))]
    debug_assert_eq!(initial_type_work, 0);
    let order = postorder(program, fold_literal_primitives, &mut builder)?;
    let mut binders = Vec::new();
    for id in &order {
        let expression = program
            .node(*id)
            .ok_or(TransformError::InvalidValidatedInput)?;
        builder.charge_effect_metadata(F::operation_extra_edge_count(&expression.kind))?;
        match F::pure(&expression.kind) {
            Some(PureExprKind::Value(PureValue::Function(function))) => {
                binders.push(function.parameter().id());
            }
            Some(PureExprKind::Computation(PureComputation::Bind(binding))) => {
                binders.push(binding.binder().id());
            }
            Some(PureExprKind::Computation(PureComputation::RecursiveBind(group))) => {
                binders.extend(group.members().iter().map(|member| member.binder().id()));
            }
            Some(PureExprKind::Computation(PureComputation::Match(match_node))) => {
                for arm in match_node.arms() {
                    let mut pattern_binders = Vec::new();
                    arm.pattern().binders(&mut pattern_binders);
                    binders.extend(pattern_binders.into_iter().map(|binder| binder.id()));
                }
            }
            Some(
                PureExprKind::Value(
                    PureValue::Integer(_)
                    | PureValue::String(_)
                    | PureValue::Intrinsic(_)
                    | PureValue::Boolean(_)
                    | PureValue::Unit(_)
                    | PureValue::Constructor(_),
                )
                | PureExprKind::Variable(_)
                | PureExprKind::Computation(
                    PureComputation::Apply(_)
                    | PureComputation::Primitive(_)
                    | PureComputation::Tuple(_)
                    | PureComputation::NewtypeConversion(_)
                    | PureComputation::LocalNominalScope(_)
                    | PureComputation::TypeAbstraction(_)
                    | PureComputation::TypeApplication(_),
                ),
            ) => {}
            None => F::collect_operation_binders(&expression.kind, &mut binders, &mut builder)?,
        }
    }
    builder.reserve_resolved_binders(binders)?;

    builder.charge_rebuild_work(program.node_count())?;
    let mut remapped = Vec::new();
    remapped
        .try_reserve_exact(program.node_count())
        .map_err(|_| TransformError::Build(BuildError::TypeWorkExceeded))?;
    remapped.resize(program.node_count(), None);
    for original in order {
        let expression = program
            .node(original)
            .ok_or(TransformError::InvalidValidatedInput)?;
        let transformed = rebuild_node(
            &mut builder,
            program,
            &remapped,
            expression,
            fold_literal_primitives,
        )?;
        let slot = remapped
            .get_mut(node_index(original)?)
            .ok_or(TransformError::InvalidValidatedInput)?;
        *slot = Some(transformed);
    }
    let root = remap(&remapped, program.root())?;
    builder.charge_rebuild_work(program.method_evidence_anchors().len())?;
    for anchor in program.method_evidence_anchors() {
        let node = remap(&remapped, anchor.node)?;
        let role = match anchor.role {
            super::dialect::MethodEvidenceAnchorRole::AdapterEdge {
                adapter,
                adapter_selection_node,
                ordinal,
                producer_node,
                producer_selection_node,
                producer_binder,
                producer,
            } => {
                builder.charge_rebuild_work(1)?;
                super::dialect::MethodEvidenceAnchorRole::AdapterEdge {
                    adapter,
                    adapter_selection_node,
                    ordinal,
                    producer_node: remap(&remapped, producer_node)?,
                    producer_selection_node,
                    producer_binder,
                    producer,
                }
            }
            role => role,
        };
        let application = builder.clone_interface_application_for_rebuild(&anchor.application)?;
        builder.authenticate_method_evidence(
            node,
            anchor.owner,
            anchor.requirement,
            anchor.method,
            application,
            role,
            anchor.occurrence,
        )?;
    }
    builder.finish(root).map_err(TransformError::from)
}

fn rebuild_node<F: TransformFamily>(
    builder: &mut CoreBuilder<F>,
    program: &ValidatedCoreProgram<F>,
    remapped: &[Option<NodeId>],
    expression: &CoreTypedExpr<F>,
    fold_literal_primitives: bool,
) -> Result<NodeId, TransformError> {
    if fold_literal_primitives
        && let Some(PureExprKind::Computation(PureComputation::Primitive(operation))) =
            F::pure(&expression.kind)
        && let Some(value) = folded_literal(program, *operation)
    {
        let ty = builder.clone_type_for_rebuild(&expression.ty)?;
        return builder
            .integer(
                value,
                ty,
                Origin::Generated {
                    cause: Box::new(expression.origin.clone()),
                    reason: GeneratedReason::ConstantFolding,
                },
            )
            .map_err(TransformError::from);
    }

    let mut context = RebuildContext {
        builder,
        identities: None,
    };
    rebuild_nonfold_node(&mut context, remapped, expression)
}

fn rebuild_nonfold_node<F: TransformFamily>(
    builder: &mut RebuildContext<'_, F>,
    remapped: &[Option<NodeId>],
    expression: &impl RebuildExpression<F>,
) -> Result<NodeId, TransformError> {
    let Some(kind) = F::pure(expression.kind()) else {
        return F::rebuild_operation(builder, remapped, expression);
    };
    rebuild_pure_node(builder, remapped, expression, kind)
}

fn rebuild_pure_node<F: TransformFamily>(
    builder: &mut RebuildContext<'_, F>,
    remapped: &[Option<NodeId>],
    expression: &impl RebuildFields,
    kind: &PureExprKind,
) -> Result<NodeId, TransformError> {
    let origin = copy_origin(builder, expression.origin()?)?;
    match kind {
        PureExprKind::Value(PureValue::String(node)) => {
            let ty = copy_type(builder, expression.ty())?;
            builder
                .string(Arc::clone(node.bytes()), ty, origin)
                .map_err(TransformError::from)
        }
        PureExprKind::Value(PureValue::Intrinsic(node)) => {
            let ty = copy_type(builder, expression.ty())?;
            let operation = copy_intrinsic(builder, node.operation())?;
            builder
                .intrinsic(operation, node.module(), ty, origin)
                .map_err(TransformError::from)
        }
        PureExprKind::Value(PureValue::Integer(node)) => {
            let ty = copy_type(builder, expression.ty())?;
            builder
                .integer(node.value().clone(), ty, origin)
                .map_err(TransformError::from)
        }
        PureExprKind::Value(PureValue::Boolean(node)) => {
            let ty = copy_type(builder, expression.ty())?;
            builder
                .boolean(node.value(), ty, origin)
                .map_err(TransformError::from)
        }
        PureExprKind::Value(PureValue::Unit(_)) => {
            let ty = copy_type(builder, expression.ty())?;
            builder.unit(ty, origin).map_err(TransformError::from)
        }
        PureExprKind::Value(PureValue::Constructor(node)) => {
            let ty = IterativeTypeOwner::new(copy_type(builder, expression.ty())?);
            let constructor = copy_constructor_id(builder, node.constructor())?;
            builder
                .constructor(constructor, ty.into_inner(), origin)
                .map_err(TransformError::from)
        }
        PureExprKind::Value(PureValue::Function(node)) => {
            let parameter_type =
                IterativeTypeOwner::new(copy_type(builder, node.parameter().ty())?);
            let parameter_id = copy_binder_id(builder, node.parameter().id())?;
            let parameter_origin = copy_origin(builder, node.parameter().origin())?;
            let parameter = builder.resolved_binder(
                parameter_id,
                parameter_type.into_inner(),
                parameter_origin,
            )?;
            let ty = IterativeTypeOwner::new(copy_type(builder, expression.ty())?);
            let body = remap(remapped, node.body())?;

            builder
                .function(parameter, body, ty.into_inner(), origin)
                .map_err(TransformError::from)
        }
        PureExprKind::Variable(node) => {
            let ty = IterativeTypeOwner::new(copy_type(builder, expression.ty())?);
            let binder = copy_binder_id(builder, node.binder())?;
            builder
                .variable(binder, ty.into_inner(), origin)
                .map_err(TransformError::from)
        }
        PureExprKind::Computation(PureComputation::Bind(node)) => {
            let binder_type = IterativeTypeOwner::new(copy_type(builder, node.binder().ty())?);
            let binder_id = copy_binder_id(builder, node.binder().id())?;
            let binder_origin = copy_origin(builder, node.binder().origin())?;
            let binder =
                builder.resolved_binder(binder_id, binder_type.into_inner(), binder_origin)?;
            let ty = IterativeTypeOwner::new(copy_type(builder, expression.ty())?);
            let initializer = remap(remapped, node.initializer())?;
            let body = remap(remapped, node.body())?;

            builder
                .binding(binder, initializer, body, ty.into_inner(), origin)
                .map_err(TransformError::from)
        }
        PureExprKind::Computation(PureComputation::RecursiveBind(node)) => {
            let mut members = Vec::new();
            members
                .try_reserve(node.members().len())
                .map_err(|_| TransformError::Build(BuildError::TypeWorkExceeded))?;
            for member in node.members() {
                let binder_type =
                    IterativeTypeOwner::new(copy_type(builder, member.binder().ty())?);
                let binder_id = copy_binder_id(builder, member.binder().id())?;
                let member_origin = copy_origin(builder, member.binder().origin())?;
                let binder =
                    builder.resolved_binder(binder_id, binder_type.into_inner(), member_origin)?;
                members.push((binder, remap(remapped, member.initializer())?));
            }
            let ty = IterativeTypeOwner::new(copy_type(builder, expression.ty())?);
            let body = remap(remapped, node.body())?;

            builder
                .recursive_binding(members, body, ty.into_inner(), origin)
                .map_err(TransformError::from)
        }
        PureExprKind::Computation(PureComputation::Apply(node)) => {
            let ty = IterativeTypeOwner::new(copy_type(builder, expression.ty())?);
            let function = remap(remapped, node.function())?;
            let argument = remap(remapped, node.argument())?;

            if !F::REQUIRES_EMPTY_ROWS
                && builder
                    .identities
                    .is_none_or(|identities| identities.preserve_completed_metadata)
            {
                let effects = copy_expression_row(builder, expression)?;
                return builder
                    .application_with_effects(
                        super::function::ApplicationNode::new(function, argument),
                        ty.into_inner(),
                        effects,
                        origin,
                    )
                    .map_err(TransformError::from);
            }
            builder
                .application(function, argument, ty.into_inner(), origin)
                .map_err(TransformError::from)
        }
        PureExprKind::Computation(PureComputation::Primitive(node)) => {
            let ty = IterativeTypeOwner::new(copy_type(builder, expression.ty())?);
            let left = remap(remapped, node.left())?;
            let right = remap(remapped, node.right())?;

            builder
                .primitive(node.primitive(), left, right, ty.into_inner(), origin)
                .map_err(TransformError::from)
        }
        PureExprKind::Computation(PureComputation::Tuple(node)) => {
            builder.charge_rebuild_work(node.elements().len())?;
            let mut elements = Vec::new();
            elements
                .try_reserve_exact(node.elements().len())
                .map_err(|_| BuildError::TypeWorkExceeded)?;
            for element in node.elements() {
                elements.push(remap(remapped, *element)?);
            }
            let ty = IterativeTypeOwner::new(copy_type(builder, expression.ty())?);

            builder
                .tuple(elements, ty.into_inner(), origin)
                .map_err(TransformError::from)
        }
        PureExprKind::Computation(PureComputation::Match(node)) => {
            builder.charge_rebuild_work(node.arms().len())?;
            let mut arms = Vec::new();
            arms.try_reserve_exact(node.arms().len())
                .map_err(|_| BuildError::TypeWorkExceeded)?;
            for arm in node.arms() {
                let pattern =
                    CorePatternOwner::new(rebuild_pattern_in_context(builder, arm.pattern())?);
                let body = remap(remapped, arm.body())?;
                let origin = copy_origin(builder, arm.origin())?;
                arms.push(CoreMatchArm::new(pattern.into_inner(), body, origin));
            }
            let ty = IterativeTypeOwner::new(copy_type(builder, expression.ty())?);
            let scrutinee = remap(remapped, node.scrutinee())?;

            builder
                .match_expression(scrutinee, arms, ty.into_inner(), origin)
                .map_err(TransformError::from)
        }
        PureExprKind::Computation(PureComputation::NewtypeConversion(node)) => {
            let ty = IterativeTypeOwner::new(copy_type(builder, expression.ty())?);
            let child = remap(remapped, node.child())?;

            let owner = copy_nominal_id(builder, node.owner())?;
            builder
                .newtype_conversion(owner, node.direction(), child, ty.into_inner(), origin)
                .map_err(TransformError::from)
        }
        PureExprKind::Computation(PureComputation::LocalNominalScope(node)) => {
            let ty = IterativeTypeOwner::new(copy_type(builder, expression.ty())?);
            let body = remap(remapped, node.body())?;
            let owner = copy_nominal_id(builder, node.owner())?;
            builder
                .local_nominal_scope(owner, body, ty.into_inner(), origin)
                .map_err(TransformError::from)
        }
        PureExprKind::Computation(PureComputation::TypeAbstraction(node)) => {
            let ty = IterativeTypeOwner::new(copy_type(builder, expression.ty())?);
            let body = remap(remapped, node.body())?;

            if builder.identities.is_some() {
                let mut parameters = crate::types::clone_kinded_type_parameters_with_budget(
                    node.parameters(),
                    &mut builder.type_work,
                )
                .map_err(|()| BuildError::TypeWorkExceeded)?;
                for (identity, _) in &mut parameters {
                    *identity = copy_variable_id(builder, *identity)?;
                }
                return builder
                    .type_abstraction_after_parameter_admission(
                        Ok(parameters),
                        body,
                        ty.into_inner(),
                        origin,
                    )
                    .map_err(TransformError::from);
            }
            builder
                .type_abstraction_from_borrowed(node.parameters(), body, ty.into_inner(), origin)
                .map_err(TransformError::from)
        }
        PureExprKind::Computation(PureComputation::TypeApplication(node)) => {
            let mut arguments = IterativeTypeBuffer(Vec::new());
            arguments
                .try_reserve(node.arguments().len())
                .map_err(|_| TransformError::Build(BuildError::TypeWorkExceeded))?;
            for argument in node.arguments() {
                arguments.push(copy_type(builder, argument)?);
            }
            builder.charge_effect_metadata(node.row_arguments().len())?;
            let mut row_arguments = Vec::new();
            row_arguments
                .try_reserve_exact(node.row_arguments().len())
                .map_err(|_| TransformError::Build(BuildError::TypeWorkExceeded))?;
            for row in node.row_arguments() {
                row_arguments.push(copy_row(builder, row)?);
            }
            let ty = IterativeTypeOwner::new(copy_type(builder, expression.ty())?);
            let function = remap(remapped, node.function())?;

            if !F::REQUIRES_EMPTY_ROWS
                && builder
                    .identities
                    .is_none_or(|identities| identities.preserve_completed_metadata)
            {
                let effects = copy_expression_row(builder, expression)?;
                return builder
                    .type_application_with_effects(
                        super::type_ops::TypeApplicationNode::new_with_row_arguments(
                            function,
                            arguments.into_vec(),
                            row_arguments,
                        ),
                        ty.into_inner(),
                        effects,
                        origin,
                    )
                    .map_err(TransformError::from);
            }
            builder
                .type_application_with_row_arguments(
                    function,
                    arguments.into_vec(),
                    row_arguments,
                    ty.into_inner(),
                    origin,
                )
                .map_err(TransformError::from)
        }
    }
}

#[cfg(test)]
fn rebuild_pattern<F: CoreOperationFamily>(
    builder: &mut CoreBuilder<F>,
    pattern: &CorePattern,
) -> Result<CorePattern, TransformError> {
    let mut context = RebuildContext {
        builder,
        identities: None,
    };
    rebuild_pattern_in_context(&mut context, pattern)
}

fn rebuild_pattern_in_context<F: CoreOperationFamily>(
    builder: &mut RebuildContext<'_, F>,
    pattern: &CorePattern,
) -> Result<CorePattern, TransformError> {
    let clone_origin = |_builder: &mut RebuildContext<'_, F>, origin: &Origin| {
        Ok::<_, TransformError>(origin.clone())
    };
    enum Task<'a> {
        Visit(&'a CorePattern),
        FinishTuple(&'a CorePattern, usize),
        FinishConstructor(&'a CorePattern, crate::types::ConstructorId, bool),
    }

    builder.charge_rebuild_work(1)?;
    let mut work = Vec::new();
    work.try_reserve(1)
        .map_err(|_| BuildError::TypeWorkExceeded)?;
    work.push(Task::Visit(pattern));
    let mut rebuilt = CorePatternBuffer(Vec::new());
    while let Some(task) = work.pop() {
        builder.charge_rebuild_work(1)?;
        rebuilt
            .0
            .try_reserve(1)
            .map_err(|_| BuildError::TypeWorkExceeded)?;
        match task {
            Task::Visit(pattern) => match &pattern.kind {
                CorePatternKind::Binder(binder) => {
                    let origin = clone_origin(builder, &pattern.origin)?;
                    let binder_origin = clone_origin(builder, binder.origin())?;
                    let binder_type = IterativeTypeOwner::new(copy_type(builder, binder.ty())?);
                    let binder_id = copy_binder_id(builder, binder.id())?;
                    let binder = builder.resolved_binder(
                        binder_id,
                        binder_type.into_inner(),
                        binder_origin,
                    )?;
                    let ty = copy_type(builder, &pattern.ty)?;
                    rebuilt.push(CorePattern::new(
                        ty,
                        origin,
                        CorePatternKind::Binder(binder),
                    ));
                }
                CorePatternKind::Wildcard => {
                    let origin = clone_origin(builder, &pattern.origin)?;
                    let ty = copy_type(builder, &pattern.ty)?;
                    rebuilt.push(CorePattern::new(ty, origin, CorePatternKind::Wildcard));
                }
                CorePatternKind::Boolean(value) => {
                    let origin = clone_origin(builder, &pattern.origin)?;
                    let ty = copy_type(builder, &pattern.ty)?;
                    rebuilt.push(CorePattern::new(
                        ty,
                        origin,
                        CorePatternKind::Boolean(*value),
                    ));
                }
                CorePatternKind::Unit => {
                    let origin = clone_origin(builder, &pattern.origin)?;
                    let ty = copy_type(builder, &pattern.ty)?;
                    rebuilt.push(CorePattern::new(ty, origin, CorePatternKind::Unit));
                }
                CorePatternKind::Tuple(elements) => {
                    builder.charge_rebuild_work(elements.len() + 1)?;
                    work.try_reserve(elements.len() + 1)
                        .map_err(|_| BuildError::TypeWorkExceeded)?;
                    work.push(Task::FinishTuple(pattern, elements.len()));
                    work.extend(elements.iter().rev().map(Task::Visit));
                }
                CorePatternKind::Constructor {
                    constructor,
                    payload,
                } => {
                    builder.charge_rebuild_work(2)?;
                    work.try_reserve(2)
                        .map_err(|_| BuildError::TypeWorkExceeded)?;
                    work.push(Task::FinishConstructor(
                        pattern,
                        copy_constructor_id(builder, *constructor)?,
                        payload.is_some(),
                    ));
                    if let Some(payload) = payload.as_deref() {
                        work.push(Task::Visit(payload));
                    }
                }
            },
            Task::FinishTuple(pattern, count) => {
                let origin = clone_origin(builder, &pattern.origin)?;
                if rebuilt.len() < count {
                    return Err(TransformError::InvalidValidatedInput);
                }
                builder.charge_rebuild_work(count)?;
                let mut elements = CorePatternBuffer(Vec::new());
                elements
                    .0
                    .try_reserve_exact(count)
                    .map_err(|_| BuildError::TypeWorkExceeded)?;
                let start = rebuilt.len() - count;
                rebuilt.append_suffix_to(start, &mut elements);
                let ty = IterativeTypeOwner::new(copy_type(builder, &pattern.ty)?);
                rebuilt.push(CorePattern::new(
                    ty.into_inner(),
                    origin,
                    CorePatternKind::Tuple(elements.into_boxed_slice()),
                ));
            }
            Task::FinishConstructor(pattern, constructor, has_payload) => {
                let origin = clone_origin(builder, &pattern.origin)?;
                let payload = if has_payload {
                    Some(rebuilt.pop().ok_or(TransformError::InvalidValidatedInput)?)
                } else {
                    None
                };
                let ty = IterativeTypeOwner::new(copy_type(builder, &pattern.ty)?);
                rebuilt.push(CorePattern::new(
                    ty.into_inner(),
                    origin,
                    CorePatternKind::Constructor {
                        constructor,
                        payload: payload.map(|payload| Box::new(payload.into_inner())),
                    },
                ));
            }
        }
    }
    let result = rebuilt.pop().ok_or(TransformError::InvalidValidatedInput)?;
    if rebuilt.is_empty() {
        Ok(result.into_inner())
    } else {
        Err(TransformError::InvalidValidatedInput)
    }
}

fn postorder<F: TransformFamily>(
    program: &ValidatedCoreProgram<F>,
    fold_literal_primitives: bool,
    builder: &mut CoreBuilder<F>,
) -> Result<Vec<NodeId>, TransformError> {
    enum Task {
        Enter(NodeId),
        Exit(NodeId),
    }

    let mut scheduled = vec![false; program.node_count()];
    let mut work = vec![Task::Enter(program.root())];
    let mut order = Vec::with_capacity(program.node_count());
    while let Some(task) = work.pop() {
        match task {
            Task::Enter(id) => {
                let index = node_index(id)?;
                let Some(was_scheduled) = scheduled.get_mut(index) else {
                    return Err(TransformError::InvalidValidatedInput);
                };
                if *was_scheduled {
                    continue;
                }
                *was_scheduled = true;
                let expression = program
                    .node(id)
                    .ok_or(TransformError::InvalidValidatedInput)?;
                let child_count = if fold_literal_primitives
                    && matches!(
                            F::pure(&expression.kind),
                            Some(PureExprKind::Computation(PureComputation::Primitive(operation)))
                                if is_foldable_literal(program, *operation)
                    ) {
                    0
                } else {
                    F::child_count(&expression.kind)
                };
                builder.charge_effect_metadata(F::operation_extra_edge_count(&expression.kind))?;
                work.try_reserve(
                    child_count
                        .checked_add(1)
                        .ok_or(BuildError::TypeWorkExceeded)?,
                )
                .map_err(|_| BuildError::TypeWorkExceeded)?;
                work.push(Task::Exit(id));
                for child_index in (0..child_count).rev() {
                    let child = F::child_at(&expression.kind, child_index)
                        .ok_or(TransformError::InvalidValidatedInput)?;
                    work.push(Task::Enter(child));
                }
            }
            Task::Exit(id) => order.push(id),
        }
    }
    Ok(order)
}

fn folded_literal<F: TransformFamily>(
    program: &ValidatedCoreProgram<F>,
    operation: super::primitive::PrimitiveNode,
) -> Option<crate::integer::Integer> {
    let Some(PureExprKind::Value(PureValue::Integer(left))) =
        F::pure(&program.node(operation.left())?.kind)
    else {
        return None;
    };
    let Some(PureExprKind::Value(PureValue::Integer(right))) =
        F::pure(&program.node(operation.right())?.kind)
    else {
        return None;
    };
    match operation.primitive() {
        Primitive::Add => Some(left.value() + right.value()),
        Primitive::Multiply => Some(left.value() * right.value()),
        Primitive::Equal => None,
    }
}

fn is_foldable_literal<F: TransformFamily>(
    program: &ValidatedCoreProgram<F>,
    operation: super::primitive::PrimitiveNode,
) -> bool {
    matches!(operation.primitive(), Primitive::Add | Primitive::Multiply)
        && matches!(
            program
                .node(operation.left())
                .and_then(|node| F::pure(&node.kind)),
            Some(PureExprKind::Value(PureValue::Integer(_)))
        )
        && matches!(
            program
                .node(operation.right())
                .and_then(|node| F::pure(&node.kind)),
            Some(PureExprKind::Value(PureValue::Integer(_)))
        )
}

fn remap(remapped: &[Option<NodeId>], original: NodeId) -> Result<NodeId, TransformError> {
    remapped
        .get(node_index(original)?)
        .copied()
        .flatten()
        .ok_or(TransformError::InvalidValidatedInput)
}

fn node_index(id: NodeId) -> Result<usize, TransformError> {
    usize::try_from(id.value()).map_err(|_| TransformError::InvalidValidatedInput)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        core::NewtypeConversionDirection,
        elaborate::{EffectElaborator, check_module, link_modules},
        module::{ModuleGraph, ModuleRoots, load_module_graph},
        resolve::{DependencyExports, resolve_module},
        resolved::{BinderId, CheckedModule, ResolvedRegistry},
        source::{ByteRange, SourceFile},
        types::{ConstructorId, Kind, NominalTypeId, TYPE_WORK_LIMIT, Type, TypeVariableId},
        validate_linked_facts_for_test,
    };
    use std::{
        fs,
        path::PathBuf,
        sync::atomic::{AtomicU64, Ordering},
    };

    static LINKED_TRANSFORM_TEMP_IDS: AtomicU64 = AtomicU64::new(0);

    struct LinkedTransformDirectory(PathBuf);

    impl LinkedTransformDirectory {
        fn create() -> Self {
            loop {
                let id = LINKED_TRANSFORM_TEMP_IDS.fetch_add(1, Ordering::Relaxed);
                let directory = std::env::temp_dir().join(format!(
                    "ash-linked-core-transform-{}-{id}",
                    std::process::id(),
                ));
                match fs::create_dir(&directory) {
                    Ok(()) => return Self(directory),
                    Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
                    Err(error) => panic!("linked transform fixture should be creatable: {error}"),
                }
            }
        }

        fn write(&self, name: &str, source: &str) -> PathBuf {
            let path = self.0.join(name);
            fs::write(&path, source).expect("linked transform fixture should be writable");
            path
        }
    }

    impl Drop for LinkedTransformDirectory {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.0);
        }
    }

    struct LinkedTransformFixture {
        _directory: LinkedTransformDirectory,
        graph: ModuleGraph,
        program: super::super::ValidatedEffectProgram,
        module_sources: Vec<(crate::module::ModuleId, crate::source::SourceId)>,
    }

    impl LinkedTransformFixture {
        fn sources(&self) -> Vec<&SourceFile> {
            self.graph
                .modules()
                .iter()
                .map(|module| module.source())
                .collect()
        }
    }

    fn checked_linked_transform_graph(graph: &ModuleGraph) -> Vec<CheckedModule> {
        let mut checked = Vec::new();
        for module in graph.modules() {
            let dependencies = module
                .dependencies()
                .iter()
                .map(|edge| {
                    let dependency = checked
                        .iter()
                        .find(|checked: &&CheckedModule| checked.module() == edge.target())
                        .expect("dependency order should check the target first");
                    DependencyExports::new(edge, dependency.exports())
                        .expect("linked transform dependency exports should authenticate")
                })
                .collect::<Vec<_>>();
            let resolved = resolve_module(module, &dependencies)
                .expect("the linked transform module should resolve");
            checked.push(
                check_module(resolved).expect("the linked transform module should type-check"),
            );
        }
        checked
    }

    fn linked_row_bearing_fold_fixture() -> LinkedTransformFixture {
        linked_transform_fixture(concat!(
            "pub fold<F : Type -> Type> : F<Int> -> Int\n",
            "fold value = 1 + 2\n\n",
            "main : Unit -> Int\n",
            "main () = 0\n",
        ))
    }

    fn linked_transform_fixture(text: &str) -> LinkedTransformFixture {
        let directory = LinkedTransformDirectory::create();
        let entry = directory.write("entry.ash", text);
        let graph = load_module_graph(&entry, &ModuleRoots::empty())
            .expect("the linked transform graph should load");
        let checked = checked_linked_transform_graph(&graph);
        let linked = link_modules(checked, graph.entry())
            .expect("the checked linked transform graph should link");
        let linked = validate_linked_facts_for_test(linked)
            .expect("the linked transform facts should authenticate");
        let mut elaborator = EffectElaborator::for_module_program(&linked)
            .expect("the linked transform binder namespace should fit");
        let typed = elaborator
            .synthesize_effect_module_program(&linked)
            .expect("the linked transform program should lower to Core");
        let unchecked = elaborator
            .finish(typed.node)
            .expect("the linked transform Core root should finish");
        let sources = graph
            .modules()
            .iter()
            .map(|module| module.source())
            .collect::<Vec<_>>();
        let module_sources = graph
            .modules()
            .iter()
            .map(|module| (module.id(), module.source().id()))
            .collect::<Vec<_>>();
        let program = super::super::validate_effect_modules(unchecked, &sources, &module_sources)
            .expect("the linked row-bearing transform Core should validate");
        LinkedTransformFixture {
            _directory: directory,
            graph,
            program,
            module_sources,
        }
    }

    fn linked_method_transform_fixture() -> LinkedTransformFixture {
        let directory = LinkedTransformDirectory::create();
        let entry = directory.write(
            "entry.ash",
            concat!(
                "type Wrap<A> = Wrap(A)\n\n",
                "interface Base<A> {\n",
                "base : A -> A\n",
                "}\n\n",
                "interface Convert<A> {\n",
                "convert<X> : (A, X) -> A\n",
                "}\n\n",
                "impl Base<Int> {\n",
                "base value = value\n",
                "}\n\n",
                "impl<A> Convert<Wrap<A>> where Base<A> {\n",
                "convert (Wrap(value), ignored) = Wrap(base(value))\n",
                "}\n\n",
                "main : Unit -> Wrap<Int>\n",
                "main () = convert((Wrap(42), true))\n",
            ),
        );
        let graph = load_module_graph(&entry, &ModuleRoots::empty())
            .expect("the linked method transform graph should load");
        let checked = checked_linked_transform_graph(&graph);
        let linked = link_modules(checked, graph.entry())
            .expect("the checked linked method transform graph should link");
        let linked = validate_linked_facts_for_test(linked)
            .expect("the linked method transform facts should authenticate");
        let mut elaborator = EffectElaborator::for_module_program(&linked)
            .expect("the linked method transform binder namespace should fit");
        let typed = elaborator
            .synthesize_effect_module_program(&linked)
            .expect("the linked method transform program should lower to Core");
        let unchecked = elaborator
            .finish(typed.node)
            .expect("the linked method transform Core root should finish");
        let sources = graph
            .modules()
            .iter()
            .map(|module| module.source())
            .collect::<Vec<_>>();
        let module_sources = graph
            .modules()
            .iter()
            .map(|module| (module.id(), module.source().id()))
            .collect::<Vec<_>>();
        let program = super::super::validate_effect_modules(unchecked, &sources, &module_sources)
            .expect("the linked method transform Core should validate");
        LinkedTransformFixture {
            _directory: directory,
            graph,
            program,
            module_sources,
        }
    }

    #[test]
    fn linked_method_transforms_have_exact_anchor_remap_and_arc_lifecycle_boundaries() {
        // Complete normal identity and folding rebuilds each consume 2,025
        // units. Their independently counted carriers (20), candidate visits
        // (5), and the explicit terms below leave a fixed 1,946-unit subtotal
        // for Effect reconstruction and structural application copies. This
        // whole-boundary subtotal is not a local anchor tariff; normal retries
        // retain it without measuring their own allowance.
        // Four complete applications add four vector-copy slots, four retained
        // argument slots, three non-edge envelopes, and five edge admissions.
        // All-method catalog lookup costs eight cells; concrete-source lookup
        // adds one cell per replay. Sidecar visits cost A=4 and the embedded
        // prerequisite producer remap costs G=1 before its NodeId lookup.
        const EFFECT_RECONSTRUCTION_AND_COPY_WORK: usize = 1_946;
        const CONCRETE_SOURCE_LOOKUP_WORK: usize = 4;
        const COMPLETE_APPLICATION_WORK: usize = 4 + 4 + 3 + 5;
        const ALL_METHOD_CATALOG_LOOKUP_WORK: usize = 8;
        const CORE_WORK: usize = EFFECT_RECONSTRUCTION_AND_COPY_WORK
            + COMPLETE_APPLICATION_WORK
            + ALL_METHOD_CATALOG_LOOKUP_WORK
            + CONCRETE_SOURCE_LOOKUP_WORK;
        const ANCHOR_REPLAY_WORK: usize = 4;
        const PRODUCER_REMAP_WORK: usize = 1;
        // Constructor admission reserves both the E=4 consumed bitmap and
        // the E=4 anchor carrier, adding the second E term to prior totals.
        const CONSTRUCTOR_SECOND_CARRIER_WORK: usize = 4;
        // Index construction adds two E-bounded tables plus one original
        // expectation visit and retained position per row. Authentication
        // replaces prior duplicate/whole-table scans with two key lookups,
        // one retained key, and exact shortlisted original-position visits.
        const CONSTRUCTOR_INDEX_WORK: usize = 4 * ANCHOR_REPLAY_WORK;
        const PRIOR_ANCHOR_DUPLICATE_SCAN_WORK: usize = 1 + 2 + 3;
        const PRIOR_EXPECTATION_SCAN_WORK: usize = 4 * ANCHOR_REPLAY_WORK;
        const INDEXED_ANCHOR_KEY_WORK: usize = 3 * ANCHOR_REPLAY_WORK;
        // Complete tags add four anchor-clone visits, four retained tag
        // admissions, and two additional selected-application comparisons.
        const COMPLETE_TAG_REPLAY_WORK: usize = 4 + 4 + 2;
        const IDENTITY_WORK: usize = CORE_WORK
            + COMPLETE_TAG_REPLAY_WORK
            + ANCHOR_REPLAY_WORK
            + PRODUCER_REMAP_WORK
            + CONSTRUCTOR_SECOND_CARRIER_WORK
            + 1; // exact selected producer matcher entry during anchor replay
        const FOLD_WORK: usize = IDENTITY_WORK;
        let fixture = linked_method_transform_fixture();
        assert_eq!(
            fixture.program.method_evidence_anchors().len(),
            ANCHOR_REPLAY_WORK,
        );
        assert_eq!(
            fixture
                .program
                .method_evidence_anchors()
                .iter()
                .filter(|anchor| matches!(
                    anchor.role,
                    super::super::dialect::MethodEvidenceAnchorRole::AdapterEdge { .. }
                ))
                .count(),
            PRODUCER_REMAP_WORK,
        );
        let expectations = fixture.program.method_evidence().expectations();
        assert_eq!(expectations.len(), ANCHOR_REPLAY_WORK);
        // The validated original anchor records its admitted expectation.
        // Replay keeps that immutable catalog and order. Every same-key
        // position through the admitted one is visited, including consumed
        // positions; unrelated keys and the untouched full predicate add no
        // new scan debit. Derive this count from coordinates, not measured
        // transform work or a larger allowance chosen after refusal.
        let mut indexed_candidate_work = 0;
        for anchor in fixture.program.method_evidence_anchors() {
            let expected = &expectations[anchor.expectation];
            assert_eq!(expected.occurrence, anchor.occurrence);
            assert_eq!(expected.method, anchor.method);
            indexed_candidate_work += expectations[..=anchor.expectation]
                .iter()
                .filter(|candidate| {
                    candidate.occurrence == anchor.occurrence && candidate.method == anchor.method
                })
                .count();
        }
        // Fallible tuple/match carriers now charge each copied edge. Pattern
        // rebuilding additionally charges its initial queue, every visited
        // pattern/finish carrier, and tuple/constructor pending storage.
        let mut payload_carrier_work = 0;
        for index in 0..fixture.program.node_count() {
            let kind = &fixture
                .program
                .node(NodeId::new(fixture.program.root().arena(), index as u32))
                .unwrap()
                .kind;
            match EffectOperationFamily::pure(kind) {
                Some(PureExprKind::Computation(PureComputation::Tuple(tuple))) => {
                    payload_carrier_work += tuple.elements().len()
                }
                Some(PureExprKind::Computation(PureComputation::Match(matching))) => {
                    payload_carrier_work += matching.arms().len();
                    for arm in matching.arms() {
                        let mut patterns = vec![arm.pattern()];
                        let (mut nodes, mut tuples, mut constructors, mut tuple_edges) =
                            (0, 0, 0, 0);
                        while let Some(pattern) = patterns.pop() {
                            nodes += 1;
                            match &pattern.kind {
                                CorePatternKind::Tuple(elements) => {
                                    tuples += 1;
                                    tuple_edges += elements.len();
                                    patterns.extend(elements.iter());
                                }
                                CorePatternKind::Constructor { payload, .. } => {
                                    constructors += 1;
                                    patterns.extend(payload.as_deref());
                                }
                                _ => {}
                            }
                        }
                        payload_carrier_work +=
                            1 + nodes + 2 * tuples + 3 * constructors + 2 * tuple_edges;
                    }
                }
                _ => {}
            }
        }
        let registry = Arc::clone(fixture.program.registry());
        let catalog = Arc::clone(fixture.program.method_evidence());
        let weak_registry = Arc::downgrade(&registry);
        let weak_catalog = Arc::downgrade(&catalog);
        let sources = fixture.sources();
        for (fold, exact_work) in [(false, IDENTITY_WORK), (true, FOLD_WORK)] {
            let exact_work = exact_work
                + payload_carrier_work
                + CONSTRUCTOR_INDEX_WORK
                + INDEXED_ANCHOR_KEY_WORK
                + indexed_candidate_work
                - PRIOR_ANCHOR_DUPLICATE_SCAN_WORK
                - PRIOR_EXPECTATION_SCAN_WORK;
            assert_eq!(
                rebuild_with_initial_type_work(
                    &fixture.program,
                    fold,
                    TYPE_WORK_LIMIT - (exact_work - 1),
                )
                .expect_err("one missing anchor-remap unit must reject the transform"),
                TransformError::Build(BuildError::TypeWorkExceeded),
            );
            let rebuilt = rebuild_with_initial_type_work(
                &fixture.program,
                fold,
                TYPE_WORK_LIMIT - exact_work,
            )
            .expect("the exact anchor-remap allowance should fit");
            assert!(Arc::ptr_eq(&rebuilt.registry, &registry));
            assert!(Arc::ptr_eq(&rebuilt.method_evidence, &catalog));
            super::super::validate_effect_modules(rebuilt, &sources, &fixture.module_sources)
                .expect("the exactly rebuilt anchors should freshly validate");
        }
        drop(sources);
        drop(registry);
        drop(catalog);
        drop(fixture);
        assert!(weak_registry.upgrade().is_none());
        assert!(weak_catalog.upgrade().is_none());
    }

    type GlobalRowShape = (BinderId, Vec<TypeVariableId>);

    fn global_row_shape(registry: &ResolvedRegistry) -> Vec<GlobalRowShape> {
        registry
            .global_parameter_rows()
            .iter()
            .map(|row| (row.owner(), row.parameters().to_vec()))
            .collect()
    }

    // Independent manual Pure contracts retain only their own ordinary
    // canonical fold/F metadata, not a Source Effect program's registry.
    fn isolated_pure_fold_registry(fixture: &LinkedTransformFixture) -> Arc<ResolvedRegistry> {
        let rows = fixture.program.registry().global_parameter_rows();
        let mut rows = rows
            .iter()
            .filter(|row| row.owner().module() == Some(fixture.graph.entry()));
        let row = rows.next().expect("entry fold row");
        assert!(rows.next().is_none());
        let [parameter] = row.parameters() else {
            panic!("fold F parameter")
        };
        let canonical = fixture
            .program
            .registry()
            .type_variable(*parameter)
            .unwrap()
            .clone();
        assert!(matches!(canonical.kind, Kind::Arrow(_, _)));
        Arc::new(
            ResolvedRegistry::default()
                .with_image_global_parameters(
                    vec![(row.owner(), vec![canonical])],
                    &mut crate::types::TypeWorkBudget::default(),
                )
                .unwrap(),
        )
    }

    fn has_constant_folded_literal<F: TransformFamily>(
        program: &UnvalidatedCoreProgram<F>,
    ) -> bool {
        program.nodes.iter().any(|node| {
            matches!(
                F::pure(&node.kind),
                Some(PureExprKind::Value(PureValue::Integer(_)))
            ) && node.origin.as_ref().is_some_and(|origin| {
                origin.generated_reason() == Some(GeneratedReason::ConstantFolding)
            })
        })
    }

    fn deep_origin(source: &SourceFile, depth: usize) -> Origin {
        let mut origin = Origin::Source(
            source
                .span(ByteRange::new(0, 1).expect("the deep origin range should be ordered"))
                .expect("the deep origin span should fit"),
        );
        for _ in 0..depth {
            origin = Origin::Generated {
                cause: Box::new(origin),
                reason: GeneratedReason::TypeChecking,
            };
        }
        origin
    }

    fn origin_depth(root: &Origin) -> usize {
        let mut depth = 0;
        let mut current = root;
        loop {
            match current {
                Origin::Source(_) => return depth,
                Origin::Generated { cause, .. } => current = cause,
                Origin::Related { primary, .. } => current = primary,
            }
            depth += 1;
        }
    }

    fn row_bearing_fold_program_with_initial_type_work(
        registry: Arc<ResolvedRegistry>,
        owner: BinderId,
        parameter: TypeVariableId,
        origin: Origin,
        initial_type_work: usize,
    ) -> Result<UnvalidatedProgram, BuildError> {
        let parameter_kind = registry
            .type_variable(parameter)
            .ok_or(BuildError::InvalidPayload)?
            .kind
            .clone();
        let mut builder = CoreBuilder::with_registry(registry);
        builder.charge_type_work_for_test(initial_type_work)?;
        builder.reserve_resolved_binders([owner])?;
        let left = builder.integer(
            crate::integer::Integer::parse_decimal("1").expect("the left literal should parse"),
            Type::Int,
            origin.clone(),
        )?;
        let right = builder.integer(
            crate::integer::Integer::parse_decimal("2").expect("the right literal should parse"),
            Type::Int,
            origin.clone(),
        )?;
        let body = builder.primitive(Primitive::Add, left, right, Type::Int, origin.clone())?;
        let parameter_binder = builder.binder(Type::Unit, origin.clone())?;
        let function_type = Type::Function(Box::new(Type::Unit), Box::new(Type::Int));
        let function = builder.function(
            parameter_binder,
            body,
            function_type.clone(),
            origin.clone(),
        )?;
        let scheme = Type::Forall(
            Box::new([(parameter, parameter_kind.clone())]),
            Box::new(function_type),
        );
        let abstraction = builder.type_abstraction(
            vec![(parameter, parameter_kind)],
            function,
            scheme.clone(),
            origin.clone(),
        )?;
        let global = builder.resolved_binder(owner, scheme, origin.clone())?;
        let group_body = builder.unit(Type::Unit, origin.clone())?;
        let root = builder.recursive_binding(
            vec![(global, abstraction)],
            group_body,
            Type::Unit,
            origin,
        )?;
        builder.finish(root)
    }

    fn application_type(depth: usize) -> Type {
        let mut result = Type::Unit;
        for _ in 0..depth {
            result = Type::Application(Box::new(result), Box::new(Type::Unit));
        }
        result
    }

    fn application_spine_depth(root: &Type) -> usize {
        let mut depth = 0;
        let mut current = root;
        loop {
            match current {
                Type::Application(function, argument) => {
                    assert!(matches!(argument.as_ref(), Type::Unit));
                    depth += 1;
                    current = function;
                }
                Type::Unit => return depth,
                _ => panic!("the deep transform payload must remain a Unit application spine"),
            }
        }
    }

    fn deep_arrow_kind(depth: usize) -> Kind {
        let mut result = Kind::Type;
        for _ in 0..depth {
            result = Kind::Arrow(Box::new(Kind::Type), Box::new(result));
        }
        result
    }

    fn arrow_kind_depth(root: &Kind) -> usize {
        let mut depth = 0;
        let mut current = root;
        loop {
            match current {
                Kind::Arrow(domain, codomain) => {
                    assert!(matches!(domain.as_ref(), Kind::Type));
                    depth += 1;
                    current = codomain;
                }
                Kind::Type | Kind::EffectRow => return depth,
            }
        }
    }

    #[test]
    fn source_identity_retains_opaque_region_metadata_under_exact_child_remapping() {
        use super::super::region::{RegionBufferOperation, RegionClosureCode};
        let mut seen = [false; 7];
        for text in [
            include_str!("../../tests/fixtures/first-stratum/valid/v008-mixed.ash"),
            "main : Unit -> Bool\nmain () = true\n",
            "main : Unit -> Unit\nmain () = ()\n",
            "main : Unit -> Bool\nmain () = 1 == 1\n",
        ] {
            let fixture = linked_transform_fixture(text);
            let after = super::super::validate_effect_modules(
                identity_effect_traversal(&fixture.program).unwrap(),
                &fixture.sources(),
                &fixture.module_sources,
            )
            .expect("the same Source identity should independently validate");
            let mut forward = std::collections::HashMap::new();
            let mut reverse = std::collections::HashMap::new();
            let mut pending = vec![(fixture.program.root(), after.root())];
            while let Some((left, right)) = pending.pop() {
                if let Some(previous) = forward.insert(left, right) {
                    assert_eq!(previous, right);
                    continue;
                }
                assert!(reverse.insert(right, left).is_none());
                let a = fixture.program.node(left).unwrap();
                let b = after.node(right).unwrap();
                assert_eq!(a.ty, b.ty);
                assert_eq!(a.effects, b.effects);
                assert_eq!(a.origin, b.origin);
                let binder = |value: &super::super::TypedBinder| {
                    (value.id(), value.ty().clone(), value.origin().clone())
                };
                match (&a.kind, &b.kind) {
                    (EffectExprKind::Pure(_), EffectExprKind::Pure(_)) => {} // Complete public comparison lives in semantics.rs.
                    (EffectExprKind::Operation(a), EffectExprKind::Operation(b)) => match (a, b) {
                        (EffectOperation::Region(a), EffectOperation::Region(b)) => {
                            seen[0] = true;
                            assert_eq!(a.entry, b.entry);
                            assert_eq!(a.api, b.api);
                            assert_eq!(a.identity, b.identity);
                            assert_eq!(binder(&a.access), binder(&b.access));
                        }
                        (
                            EffectOperation::RegionAllocate(a),
                            EffectOperation::RegionAllocate(b),
                        ) => {
                            seen[1] = true;
                            assert_eq!(a.api, b.api);
                        }
                        (
                            EffectOperation::RegionValueRequest(a),
                            EffectOperation::RegionValueRequest(b),
                        ) => {
                            seen[2] = true;
                            assert_eq!(a, b);
                        }
                        (EffectOperation::RegionBuffer(a), EffectOperation::RegionBuffer(b)) => {
                            assert_eq!(a.api, b.api);
                            assert_eq!(a.operation, b.operation);
                            assert_eq!(a.operand.is_some(), b.operand.is_some());
                            assert_eq!(a.right.is_some(), b.right.is_some());
                            if matches!(
                                a.operation,
                                RegionBufferOperation::IntegerArithmetic(Primitive::Add)
                            ) {
                                seen[3] = true;
                            }
                            if matches!(
                                a.operation,
                                RegionBufferOperation::IntegerArithmetic(Primitive::Multiply)
                            ) {
                                seen[4] = true;
                            }
                        }
                        (EffectOperation::RegionTuple(a), EffectOperation::RegionTuple(b)) => {
                            assert_eq!(a.api, b.api);
                            assert_eq!(a.constructor, b.constructor);
                            assert_eq!(a.fields.len(), b.fields.len());
                        }
                        (EffectOperation::RegionClosure(a), EffectOperation::RegionClosure(b)) => {
                            seen[5] = true;
                            assert_eq!(a.api, b.api);
                            assert_eq!(a.captures.len(), b.captures.len());
                            match (&a.code, &b.code) {
                                (
                                    RegionClosureCode::Function(a),
                                    RegionClosureCode::Function(b),
                                ) => assert_eq!(binder(a.parameter()), binder(b.parameter())),
                                (
                                    RegionClosureCode::Adapter { .. },
                                    RegionClosureCode::Adapter { .. },
                                ) => {}
                                _ => panic!("identity changed stored code kind"),
                            }
                        }
                        (EffectOperation::Request(a), EffectOperation::Request(b)) => {
                            seen[6] = true;
                            assert_eq!(a.effect(), b.effect());
                            assert_eq!(a.operation(), b.operation());
                        }
                        (EffectOperation::Handler(a), EffectOperation::Handler(b)) => {
                            assert_eq!(a.id(), b.id());
                            assert_eq!(a.effect(), b.effect());
                            assert_eq!(a.hook_root, b.hook_root);
                            assert_eq!(a.hook_registration, b.hook_registration);
                            assert_eq!(a.clauses().len(), b.clauses().len());
                            for (a, b) in a.clauses().iter().zip(b.clauses()) {
                                assert_eq!(a.operation(), b.operation());
                                assert_eq!(a.resume(), b.resume());
                                assert_eq!(a.pattern().ty, b.pattern().ty);
                                assert_eq!(a.pattern().origin, b.pattern().origin);
                                match (&a.pattern().kind, &b.pattern().kind) {
                                    (CorePatternKind::Binder(a), CorePatternKind::Binder(b)) => {
                                        assert_eq!(binder(a), binder(b))
                                    }
                                    _ => assert_eq!(a.pattern(), b.pattern()),
                                }
                                assert_eq!(a.origin(), b.origin());
                            }
                        }
                        (EffectOperation::Resume(a), EffectOperation::Resume(b)) => {
                            assert_eq!(a.handler(), b.handler());
                            assert_eq!(a.owner(), b.owner());
                            assert_eq!(a.use_state(), b.use_state());
                        }
                        (EffectOperation::Discard(a), EffectOperation::Discard(b)) => {
                            assert_eq!(a, b)
                        }
                        _ => panic!("unexpected or changed Effect operation in original Sources"),
                    },
                    _ => panic!("identity changed a Core family"),
                }
                assert_eq!(a.kind.child_count(), b.kind.child_count());
                pending.extend((0..a.kind.child_count()).map(|index| {
                    (
                        a.kind.child_at(index).unwrap(),
                        b.kind.child_at(index).unwrap(),
                    )
                }));
            }
            assert_eq!(forward.len(), fixture.program.node_count());
            assert_eq!(reverse.len(), after.node_count());
        }
        assert!(
            seen.into_iter().all(|present| present),
            "original Sources must reach region/allocation/request/closure/Add/Multiply controls"
        );
    }

    #[test]
    fn unchecked_transforms_share_the_exact_nonempty_global_row_registry() {
        let fixture = linked_row_bearing_fold_fixture();
        let registry = Arc::clone(fixture.program.registry());
        let rows = global_row_shape(&registry);
        let entry_rows = rows
            .iter()
            .filter(|(owner, _)| owner.module() == Some(fixture.graph.entry()))
            .collect::<Vec<_>>();
        assert_eq!(entry_rows.len(), 1);
        assert_eq!(entry_rows[0].1.len(), 1);
        assert!(matches!(
            &registry.type_variable(entry_rows[0].1[0]).unwrap().kind,
            Kind::Arrow(_, _)
        ));

        let identity = identity_effect_traversal(&fixture.program)
            .expect("the row-bearing identity traversal should rebuild");
        let folded = fold_effect_literal_primitives(&fixture.program)
            .expect("the row-bearing literal fold should rebuild independently");
        assert!(Arc::ptr_eq(&identity.registry, &registry));
        assert!(Arc::ptr_eq(&folded.registry, &registry));
        assert_eq!(global_row_shape(&identity.registry), rows);
        assert_eq!(global_row_shape(&folded.registry), rows);
        assert!(!has_constant_folded_literal(&identity));
        // Source arithmetic retains RegionBuffer/default-allocation effects;
        // the isolated Pure donor below proves actual scalar folding.
        assert!(!has_constant_folded_literal(&folded));
        let arithmetic = |nodes: &[super::super::dialect::StoredNode<EffectOperationFamily>]| {
            nodes.iter().filter(|node| matches!(&node.kind,
            EffectExprKind::Operation(EffectOperation::RegionBuffer(buffer))
                if matches!(buffer.operation, super::super::region::RegionBufferOperation::IntegerArithmetic(_)))).count()
        };
        assert!(arithmetic(&identity.nodes) > 0);
        assert_eq!(arithmetic(&folded.nodes), arithmetic(&identity.nodes));
        assert_ne!(identity.arena, fixture.program.root().arena());
        assert_ne!(folded.arena, fixture.program.root().arena());

        let sources = fixture.sources();
        let identity =
            super::super::validate_effect_modules(identity, &sources, &fixture.module_sources)
                .expect("the row-bearing identity traversal should independently revalidate");
        let folded =
            super::super::validate_effect_modules(folded, &sources, &fixture.module_sources)
                .expect("the row-bearing literal fold should independently revalidate");
        assert!(Arc::ptr_eq(identity.registry(), &registry));
        assert!(Arc::ptr_eq(folded.registry(), &registry));
        assert_eq!(global_row_shape(identity.registry()), rows);
        assert_eq!(global_row_shape(folded.registry()), rows);
    }

    #[test]
    fn row_bearing_construction_and_identity_have_exact_independent_type_work() {
        std::thread::Builder::new()
            .name("exact-row-bearing-construction-and-identity".into())
            .stack_size(256 * 1024)
            .spawn(|| {
                // Input literals and primitive: three admitted Int cells = 3.
                // Function: Unit binder 1 + three-cell function result = 4.
                // Abstraction: one record + three Arrow Kind nodes + eight-cell scheme = 12.
                // Recursive owner/root: eight-cell scheme binder + Unit result = 9.
                // Recursive body Unit = 1. The shared registry and its row add 0.
                const CONSTRUCTION_WORK: usize = 3 + 4 + 12 + 9 + 1;
                // Identity literals and primitive: three clone/admission pairs = 6.
                // Function: Unit binder clone/admission 2 + result clone/admission 6 = 8.
                // Abstraction: scheme clone/admission 16 + parameter record/Arrow Kind 4 = 20.
                // Recursive owner/root: scheme binder clone/admission 16 + Unit result 2 = 18.
                // Recursive body Unit clone/admission = 2. The shared row again adds 0.
                // Exact old-to-new NodeId remap slots = 7.
                const IDENTITY_WORK: usize = 6 + 8 + 20 + 18 + 2 + 7;

                let fixture = linked_row_bearing_fold_fixture();
                let registry = isolated_pure_fold_registry(&fixture);
                let rows = global_row_shape(&registry);
                let entry_rows = rows
                    .iter()
                    .filter(|(owner, _)| owner.module() == Some(fixture.graph.entry()))
                    .cloned()
                    .collect::<Vec<_>>();
                let [(owner, parameters)] = entry_rows.as_slice() else {
                    panic!("the exact construction fixture should retain one global row");
                };
                let [parameter] = parameters.as_slice() else {
                    panic!("the exact construction row should retain one parameter");
                };
                let source = fixture
                    .graph
                    .modules()
                    .iter()
                    .find(|module| module.id() == fixture.graph.entry())
                    .expect("the exact construction fixture should retain its entry module")
                    .source();
                let origin = deep_origin(source, super::super::CORE_PAYLOAD_DEPTH_LIMIT - 1);
                let mixed = row_bearing_fold_program_with_initial_type_work(
                    Arc::clone(fixture.program.registry()),
                    *owner,
                    *parameter,
                    Origin::Source(source.span(ByteRange::new(0, 1).unwrap()).unwrap()),
                    0,
                )
                .unwrap();
                assert_eq!(
                    super::super::validate::validate_modules(
                        mixed,
                        &fixture.sources(),
                        &fixture.module_sources,
                    )
                    .unwrap_err()
                    .reason(),
                    super::super::ValidationReason::Registry,
                    "Pure admission must reject the complete Source Effect registry"
                );
                let registry_owners_before = Arc::strong_count(&registry);

                let short = row_bearing_fold_program_with_initial_type_work(
                    Arc::clone(&registry),
                    *owner,
                    *parameter,
                    origin.clone(),
                    TYPE_WORK_LIMIT - (CONSTRUCTION_WORK - 1),
                )
                .expect_err("one-short construction must reject without publishing a program");
                assert_eq!(short, BuildError::TypeWorkExceeded);
                assert_eq!(Arc::strong_count(&registry), registry_owners_before);

                let unchecked = row_bearing_fold_program_with_initial_type_work(
                    Arc::clone(&registry),
                    *owner,
                    *parameter,
                    origin,
                    TYPE_WORK_LIMIT - CONSTRUCTION_WORK,
                )
                .expect("the exact construction allowance should succeed on a fresh retry");
                assert!(Arc::ptr_eq(&unchecked.registry, &registry));
                assert_eq!(global_row_shape(&unchecked.registry), rows);
                let sources = fixture.sources();
                let program = super::super::validate::validate_modules(
                    unchecked,
                    &sources,
                    &fixture.module_sources,
                )
                .expect("the exact constructed row-bearing Core should freshly validate");
                assert!(Arc::ptr_eq(program.registry(), &registry));
                assert_eq!(global_row_shape(program.registry()), rows);
                assert_eq!(program.node_count(), 7);

                let registry_owners_before = Arc::strong_count(&registry);
                let short = rebuild_with_initial_type_work(
                    &program,
                    false,
                    TYPE_WORK_LIMIT - (IDENTITY_WORK - 1),
                )
                .expect_err("one-short identity rebuild must publish no transformed program");
                assert_eq!(short, TransformError::Build(BuildError::TypeWorkExceeded));
                assert_eq!(Arc::strong_count(&registry), registry_owners_before);

                let identity = rebuild_with_initial_type_work(
                    &program,
                    false,
                    TYPE_WORK_LIMIT - IDENTITY_WORK,
                )
                .expect("the exact identity allowance should succeed on a fresh retry");
                assert!(Arc::ptr_eq(&identity.registry, &registry));
                assert_eq!(global_row_shape(&identity.registry), rows);
                let identity = super::super::validate::validate_modules(
                    identity,
                    &sources,
                    &fixture.module_sources,
                )
                .expect("the exact identity result should freshly validate");
                assert!(Arc::ptr_eq(identity.registry(), &registry));
                assert_eq!(global_row_shape(identity.registry()), rows);
                assert_eq!(identity.node_count(), 7);

                drop(identity);
                drop(program);
                drop(sources);
                drop(fixture);
                drop(registry);
            })
            .expect("the small-stack construction/identity worker should start")
            .join()
            .expect("accepted and rejected construction/identity states should dismantle");
    }

    #[test]
    fn folded_higher_kinded_transform_has_exact_independent_type_work() {
        std::thread::Builder::new()
            .name("exact-row-bearing-fold-transform".into())
            .stack_size(256 * 1024)
            .spawn(|| {
                // Folded Int result: one clone + one admission = 2.
                // Function: Unit binder clone/admission 2 + result clone/admission 6 = 8.
                // Outer Forall(F : Type -> Type). (Unit -> Int): 8 + 8 = 16.
                // Abstraction parameter: one record + three Arrow Kind nodes = 4.
                // Recursive owner: scheme binder clone/admission 16 + result Unit 2 = 18.
                // Recursive body Unit: one clone + one admission = 2.
                // The shared registry Arc and its nonempty resolved-global row add 0.
                // Exact old-to-new NodeId remap slots = 7.
                const EXACT_WORK: usize = 2 + 8 + 16 + 4 + 18 + 2 + 7;
                let fixture = linked_row_bearing_fold_fixture();
                let registry = isolated_pure_fold_registry(&fixture);
                let rows = global_row_shape(&registry);
                let entry_rows = rows
                    .iter()
                    .filter(|(owner, _)| owner.module() == Some(fixture.graph.entry()))
                    .cloned()
                    .collect::<Vec<_>>();
                let [(owner, parameters)] = entry_rows.as_slice() else {
                    panic!("the exact fold fixture should retain one global row");
                };
                let [parameter] = parameters.as_slice() else {
                    panic!("the exact fold row should retain one parameter");
                };
                assert!(owner.module().is_some());
                let canonical = registry
                    .type_variable(*parameter)
                    .expect("the retained row parameter should have one canonical record");
                assert!(matches!(canonical.kind, Kind::Arrow(_, _)));
                let source = fixture
                    .graph
                    .modules()
                    .iter()
                    .find(|module| module.id() == fixture.graph.entry())
                    .expect("the exact fold fixture should retain its entry module")
                    .source();
                let origin = deep_origin(source, super::super::CORE_PAYLOAD_DEPTH_LIMIT - 1);
                assert_eq!(
                    origin_depth(&origin),
                    super::super::CORE_PAYLOAD_DEPTH_LIMIT - 1,
                );
                let unchecked = row_bearing_fold_program_with_initial_type_work(
                    Arc::clone(&registry),
                    *owner,
                    *parameter,
                    origin,
                    0,
                )
                .expect("the row-bearing fold fixture should construct");
                assert!(Arc::ptr_eq(&unchecked.registry, &registry));
                assert_eq!(global_row_shape(&unchecked.registry), rows);
                assert_eq!(unchecked.nodes.len(), 7);
                assert!(unchecked.nodes.iter().any(|node| matches!(
                    node.kind,
                    PureExprKind::Computation(PureComputation::Primitive(_)),
                )));
                let sources = fixture.sources();
                let program = super::super::validate::validate_modules(
                    unchecked,
                    &sources,
                    &fixture.module_sources,
                )
                .expect("the row-bearing higher-kinded fold fixture should validate");
                assert!(Arc::ptr_eq(program.registry(), &registry));

                let registry_owners_before = Arc::strong_count(&registry);
                let short = rebuild_with_initial_type_work(
                    &program,
                    true,
                    TYPE_WORK_LIMIT - (EXACT_WORK - 1),
                )
                .expect_err("one-short folding must reject without publishing output");
                assert_eq!(short, TransformError::Build(BuildError::TypeWorkExceeded));
                assert_eq!(Arc::strong_count(&registry), registry_owners_before);

                let transformed =
                    rebuild_with_initial_type_work(&program, true, TYPE_WORK_LIMIT - EXACT_WORK)
                        .expect("the exact independent folding allowance should succeed on retry");
                assert!(Arc::ptr_eq(&transformed.registry, &registry));
                assert_eq!(global_row_shape(&transformed.registry), rows);
                assert_eq!(transformed.nodes.len(), 5);
                assert!(has_constant_folded_literal(&transformed));
                let (folded_value, folded_origin) = transformed
                    .nodes
                    .iter()
                    .find_map(|node| {
                        let PureExprKind::Value(PureValue::Integer(integer)) = &node.kind else {
                            return None;
                        };
                        let origin = node.origin.as_ref()?;
                        (origin.generated_reason() == Some(GeneratedReason::ConstantFolding))
                            .then_some((integer.value(), origin))
                    })
                    .expect("the exact transform should publish its folded literal");
                assert_eq!(folded_value.to_string(), "3");
                assert_eq!(
                    origin_depth(folded_origin),
                    super::super::CORE_PAYLOAD_DEPTH_LIMIT,
                );
                let transformed = super::super::validate::validate_modules(
                    transformed,
                    &sources,
                    &fixture.module_sources,
                )
                .expect("the exact folded result should independently validate");
                assert!(Arc::ptr_eq(transformed.registry(), &registry));
                assert_eq!(global_row_shape(transformed.registry()), rows);
                assert_eq!(
                    crate::eval::evaluate(&transformed)
                        .expect("the exact folded result should evaluate")
                        .value
                        .to_string(),
                    "()",
                );

                drop(transformed);
                drop(program);
                drop(sources);
                drop(fixture);
                drop(registry);
            })
            .expect("the small-stack exact fold worker should start")
            .join()
            .expect("accepted and rejected fold states should dismantle on the small stack");
    }

    #[test]
    fn generic_cell_core_builder_reconstruction_is_exact_and_fresh_retryable() {
        let (program, sources, relation) =
            crate::core::validate::generic_cell_source_fixture_for_test(
                "import @builtin.generic_cell as Cell\nmain : Unit -> Int\nmain () = resource Cell.Cell<R, Int> c = 41 {\nCell.read c + 1\n}\n",
                None,
            );
        let refs = sources.iter().collect::<Vec<_>>();
        for fold in [false, true] {
            // This is the CoreBuilder ledger, separate from source inference.
            // Find the exact smallest remaining allowance with fresh builders.
            let mut low = 0;
            let mut high = crate::types::TYPE_WORK_LIMIT;
            while low < high {
                let allowance = low + (high - low) / 2;
                match rebuild_with_initial_type_work(
                    &program,
                    fold,
                    crate::types::TYPE_WORK_LIMIT - allowance,
                ) {
                    Ok(output) => {
                        drop(output);
                        high = allowance;
                    }
                    Err(TransformError::Build(super::super::BuildError::TypeWorkExceeded)) => {
                        low = allowance + 1
                    }
                    Err(error) => panic!("unexpected builder refusal: {error:?}"),
                }
            }
            let exact = low;
            assert!(exact > 0);
            assert!(
                matches!(
                    rebuild_with_initial_type_work(
                        &program,
                        fold,
                        crate::types::TYPE_WORK_LIMIT - exact + 1
                    ),
                    Err(TransformError::Build(
                        super::super::BuildError::TypeWorkExceeded
                    ))
                ),
                "one-short publishes no Core output"
            );
            for _ in 0..2 {
                let output = rebuild_with_initial_type_work(
                    &program,
                    fold,
                    crate::types::TYPE_WORK_LIMIT - exact,
                )
                .unwrap();
                let admitted =
                    crate::core::validate_effect_modules(output, &refs, &relation).unwrap();
                assert_eq!(
                    crate::eval::evaluate_effect(&admitted)
                        .unwrap()
                        .value
                        .to_string(),
                    "42"
                );
            }
            println!(
                "generic CoreBuilder fold={fold} exactwork={exact}; one-short refused; two fresh retries42"
            );
        }
    }

    #[test]
    fn higher_kinded_transform_copies_have_an_exact_type_budget() {
        // Body: one retained clone + one admission visit = 2.
        // Abstraction scheme: six clone units and six admission units.
        // Abstraction parameters: one binder record + three Kind nodes = 4.
        // Exact old-to-new NodeId remap slots = 2.
        const EXACT_WORK: usize = 20;
        let source =
            SourceFile::new("transform-kinds.ash", "higher").expect("transform fixture source");
        let origin = Origin::Source(
            source
                .span(ByteRange::new(0, 6).expect("transform fixture range"))
                .expect("transform fixture span"),
        );
        let parameter = TypeVariableId::new(0);
        let kind = Kind::Arrow(Box::new(Kind::Type), Box::new(Kind::Type));
        let mut builder = CoreBuilder::new();
        let body = builder
            .unit(Type::Unit, origin.clone())
            .expect("fixture body");
        let root = builder
            .type_abstraction(
                vec![(parameter, kind.clone())],
                body,
                Type::Forall(
                    vec![(parameter, kind.clone())].into_boxed_slice(),
                    Box::new(Type::Unit),
                ),
                origin,
            )
            .expect("fixture abstraction");
        let program = super::super::validate::validate(
            builder.finish(root).expect("fixture root"),
            &[&source],
        )
        .expect("fixture validates");

        let short =
            rebuild_with_initial_type_work(&program, false, TYPE_WORK_LIMIT - (EXACT_WORK - 1))
                .expect_err("one-short transform must reject before publishing output");
        assert_eq!(short, TransformError::Build(BuildError::TypeWorkExceeded));

        let transformed =
            rebuild_with_initial_type_work(&program, false, TYPE_WORK_LIMIT - EXACT_WORK)
                .expect("the exact transform allowance fits");
        super::super::validate::validate(transformed, &[&source])
            .expect("the exact transform preserves canonical binder kinds");
    }

    #[test]
    fn discard_rebuild_preserves_owner_usage_and_empty_row_without_children() {
        use crate::{
            core::{DiscardNode, HandlerId, ResumeUse},
            resolved::ResumeId,
            types::EffectRow,
        };
        let source = SourceFile::new("discard-transform.ash", "discard").unwrap();
        let origin = Origin::Source(source.span(ByteRange::new(0, 7).unwrap()).unwrap());
        let expression = CoreTypedExpr {
            ty: Type::Unit,
            effects: EffectRow::empty(),
            origin,
            kind: EffectExprKind::Operation(EffectOperation::Discard(DiscardNode::new(
                HandlerId::new(7),
                ResumeId::new(9),
                ResumeUse::Consumed,
            ))),
        };
        let mut builder = CoreBuilder::<EffectOperationFamily>::with_effect_registry(Arc::new(
            ResolvedRegistry::default(),
        ));
        let root = EffectOperationFamily::rebuild_operation(
            &mut RebuildContext {
                builder: &mut builder,
                identities: None,
            },
            &[],
            &expression,
        )
        .unwrap();
        let rebuilt = &builder.nodes[root.index().unwrap()];
        assert_eq!(rebuilt.kind, expression.kind);
        assert_eq!(rebuilt.ty, Type::Unit);
        assert!(rebuilt.effects.is_empty());
        assert_eq!(rebuilt.origin.as_ref(), Some(&expression.origin));
        assert_eq!(
            crate::core::validate_effect(builder.finish(root).unwrap(), &[&source])
                .unwrap_err()
                .reason(),
            crate::core::ValidationReason::Resume
        );
    }

    #[test]
    fn checked_fragment_transfer_replaces_whole_node_before_copying_children() {
        let source_file = SourceFile::new("fragment-transfer.ash", "value").unwrap();
        let origin = Origin::Source(source_file.span(ByteRange::new(0, 5).unwrap()).unwrap());
        let mut source = CoreBuilder::<EffectOperationFamily>::with_effect_registry(Arc::new(
            ResolvedRegistry::default(),
        ));
        let thirteen = source
            .integer(
                crate::integer::Integer::from_i64(13),
                Type::Int,
                origin.clone(),
            )
            .unwrap();
        let twenty_seven = source
            .integer(
                crate::integer::Integer::from_i64(27),
                Type::Int,
                origin.clone(),
            )
            .unwrap();
        let obsolete = source
            .primitive(
                Primitive::Add,
                thirteen,
                twenty_seven,
                Type::Int,
                origin.clone(),
            )
            .unwrap();
        let two = source
            .integer(
                crate::integer::Integer::from_i64(2),
                Type::Int,
                origin.clone(),
            )
            .unwrap();
        let root = source
            .primitive(Primitive::Add, obsolete, two, Type::Int, origin.clone())
            .unwrap();
        let identities = FragmentIdentities::default();
        let mut destination = CoreBuilder::<EffectOperationFamily>::with_effect_registry(Arc::new(
            ResolvedRegistry::default(),
        ));
        let mut workspace = FragmentWorkspace::new(&source, &mut destination).unwrap();
        let mut transfer = FragmentNodeMap::new(
            &mut workspace,
            &source,
            root,
            &mut destination,
            FragmentIdentityView::new(&identities, None),
        )
        .expect("the source arena and map are admitted");

        assert!(
            transfer
                .copy_effect(&source, root, &mut destination)
                .is_err()
        );
        let replacement = destination
            .integer(crate::integer::Integer::from_i64(40), Type::Int, origin)
            .unwrap();
        transfer
            .replace(&source, obsolete, &mut destination, replacement)
            .expect("the complete evidence replacement is published");
        let mut wrong_destination = CoreBuilder::<EffectOperationFamily>::with_effect_registry(
            Arc::new(ResolvedRegistry::default()),
        );
        assert!(
            transfer
                .copy_effect(&source, two, &mut wrong_destination)
                .is_err()
        );
        assert!(wrong_destination.nodes.is_empty());
        assert!(transfer.mapped(thirteen).is_err());
        assert!(transfer.mapped(twenty_seven).is_err());
        assert!(
            transfer
                .replace(&source, obsolete, &mut destination, replacement)
                .is_err()
        );
        transfer
            .copy_effect(&source, two, &mut destination)
            .unwrap();
        let rebuilt = transfer
            .copy_effect(&source, root, &mut destination)
            .unwrap();
        assert_eq!(transfer.mapped(root).unwrap(), rebuilt);
        assert_eq!(
            destination.nodes.len(),
            3,
            "obsolete children were never copied"
        );
        let validated =
            super::super::validate_effect(destination.finish(rebuilt).unwrap(), &[&source_file])
                .expect("the newly assembled Core is independently validated");
        assert_eq!(
            crate::eval::evaluate_effect(&validated)
                .unwrap()
                .value
                .to_string(),
            "42"
        );
    }

    #[test]
    fn checked_fragment_maps_are_owner_scoped_and_require_exact_arena() {
        let source_file = SourceFile::new("fragment-owner.ash", "x").unwrap();
        let origin = Origin::Source(source_file.span(ByteRange::new(0, 1).unwrap()).unwrap());
        let variable = TypeVariableId::generated(0);
        let binder = BinderId::resolved(crate::module::ModuleId::new(0), 0);
        let mut source = CoreBuilder::<EffectOperationFamily>::with_effect_registry(Arc::new(
            ResolvedRegistry::default(),
        ));
        let root = source
            .variable(binder, Type::Variable(variable), origin.clone())
            .unwrap();
        let mut other_source = CoreBuilder::<EffectOperationFamily>::with_effect_registry(
            Arc::new(ResolvedRegistry::default()),
        );
        let unrelated = other_source
            .variable(binder, Type::Variable(variable), origin)
            .unwrap();
        let first = FragmentIdentities {
            variables: HashMap::from([(variable, TypeVariableId::generated(10))]),
            ..FragmentIdentities::default()
        };
        let second = FragmentIdentities {
            variables: HashMap::from([(variable, TypeVariableId::generated(20))]),
            ..FragmentIdentities::default()
        };
        for (identities, expected) in [(&first, 10), (&second, 20)] {
            let mut destination = CoreBuilder::<EffectOperationFamily>::with_effect_registry(
                Arc::new(ResolvedRegistry::default()),
            );
            let mut workspace = FragmentWorkspace::new(&source, &mut destination).unwrap();
            let mut transfer = FragmentNodeMap::new(
                &mut workspace,
                &source,
                root,
                &mut destination,
                FragmentIdentityView::new(identities, None),
            )
            .expect("owner-specific mapping");
            assert!(
                transfer
                    .copy_effect(&other_source, unrelated, &mut destination)
                    .is_err()
            );
            let copied = transfer
                .copy_effect(&source, root, &mut destination)
                .unwrap();
            assert_eq!(
                destination.nodes[copied.index().unwrap()].ty,
                Type::Variable(TypeVariableId::generated(expected))
            );
            let mut retry = CoreBuilder::<EffectOperationFamily>::with_effect_registry(Arc::new(
                ResolvedRegistry::default(),
            ));
            let other = if expected == 10 { &second } else { &first };
            let mut transfer = FragmentNodeMap::new(
                &mut workspace,
                &source,
                root,
                &mut retry,
                FragmentIdentityView::new(other, None),
            )
            .expect("the workspace resets only the previous owner's touched nodes");
            assert!(transfer.mapped(root).is_err());
            let copied = transfer.copy_effect(&source, root, &mut retry).unwrap();
            let new_owner = if expected == 10 { 20 } else { 10 };
            assert_eq!(
                retry.nodes[copied.index().unwrap()].ty,
                Type::Variable(TypeVariableId::generated(new_owner))
            );
        }

        let count = source.nodes.len();
        let work = count * 2 + 1;
        let mut short = CoreBuilder::<EffectOperationFamily>::with_effect_registry(Arc::new(
            ResolvedRegistry::default(),
        ));
        short
            .charge_type_work_for_test(TYPE_WORK_LIMIT - (work - 1))
            .unwrap();
        let mut workspace = FragmentWorkspace::new(&source, &mut short).unwrap();
        assert!(matches!(
            FragmentNodeMap::new(
                &mut workspace,
                &source,
                root,
                &mut short,
                FragmentIdentityView::new(&first, None)
            ),
            Err(TransformError::Build(BuildError::TypeWorkExceeded))
        ));
        for _ in 0..2 {
            let mut exact = CoreBuilder::<EffectOperationFamily>::with_effect_registry(Arc::new(
                ResolvedRegistry::default(),
            ));
            exact
                .charge_type_work_for_test(TYPE_WORK_LIMIT - work)
                .unwrap();
            let mut workspace = FragmentWorkspace::new(&source, &mut exact).unwrap();
            FragmentNodeMap::new(
                &mut workspace,
                &source,
                root,
                &mut exact,
                FragmentIdentityView::new(&first, None),
            )
            .expect("fresh exact allocation retries");
        }
    }

    #[test]
    fn fragment_handler_relocation_preserves_hook_coordinates_and_retries() {
        use crate::{
            core::effect::{HandlerId, HandlerNode},
            module::ModuleId,
            resolved::{HookRegistrationContract, HookRootContract, ResumeId},
            types::{EffectId, EffectInstance, EffectRow, OperationId},
        };

        let source = SourceFile::new("fragment-handler.ash", "handler").unwrap();
        let span = source.span(ByteRange::new(0, 7).unwrap()).unwrap();
        let origin = Origin::Source(span);
        let effect = EffectId::new(ModuleId::new(0), 0);
        let source_type = TypeVariableId::generated(0);
        let target_type = TypeVariableId::generated(10);
        let source_binders = [0, 1, 2, 3].map(BinderId::generated);
        let target_binders = [10, 11, 12, 13].map(BinderId::generated);
        let identities = FragmentIdentities {
            binders: source_binders.into_iter().zip(target_binders).collect(),
            variables: HashMap::from([(source_type, target_type)]),
            handlers: HashMap::from([(HandlerId::new(0), HandlerId::new(7))]),
        };
        let prepare = || {
            let mut builder = CoreBuilder::<EffectOperationFamily>::with_effect_registry(Arc::new(
                ResolvedRegistry::default(),
            ));
            let body = builder.unit(Type::Unit, origin.clone()).unwrap();
            let instance = || {
                EffectInstance::new(effect, vec![Type::Variable(source_type)].into_boxed_slice())
            };
            let handler = HandlerNode::new(HandlerId::new(0), body, instance(), Vec::new())
                .with_hook_registration(Some(HookRegistrationContract {
                    target: instance(),
                    span,
                    target_span: span,
                    operation: OperationId::new(effect, 0),
                    callback: source_binders[0],
                    input: source_binders[1],
                    previous: source_binders[2],
                    next: source_binders[3],
                    resume: ResumeId::new(3),
                }))
                .with_hook_root(Some(HookRootContract {
                    target: instance(),
                    span,
                    target_span: span,
                    operation: OperationId::new(effect, 0),
                    input: source_binders[1],
                    resume: ResumeId::new(4),
                }));
            let expression = CoreTypedExpr {
                ty: Type::Unit,
                effects: EffectRow::empty(),
                origin: origin.clone(),
                kind: EffectExprKind::Operation(EffectOperation::Handler(handler)),
            };
            (builder, vec![Some(body)], expression)
        };
        let (mut measured, remapped, expression) = prepare();
        let before = measured.type_work.used();
        let root = EffectOperationFamily::rebuild_operation(
            &mut RebuildContext {
                builder: &mut measured,
                identities: Some(FragmentIdentityView::new(&identities, None)),
            },
            &remapped,
            &expression,
        )
        .expect("the complete fragment mapping succeeds");
        let work = measured.type_work.used() - before;
        let EffectExprKind::Operation(EffectOperation::Handler(handler)) =
            &measured.nodes[root.index().unwrap()].kind
        else {
            panic!("the rebuilt operation remains a handler");
        };
        assert_eq!(handler.id(), HandlerId::new(7));
        let expected_target =
            EffectInstance::new(effect, vec![Type::Variable(target_type)].into_boxed_slice());
        assert_eq!(handler.effect(), &expected_target);
        let registration = handler.hook_registration().expect("registration retained");
        assert_eq!(registration.target, expected_target);
        assert_eq!(
            [
                registration.callback,
                registration.input,
                registration.previous,
                registration.next
            ],
            target_binders,
        );
        assert_eq!(registration.resume, ResumeId::new(3));
        let root_contract = handler.hook_root().expect("root retained");
        assert_eq!(root_contract.target, expected_target);
        assert_eq!(root_contract.input, target_binders[1]);
        assert_eq!(root_contract.resume, ResumeId::new(4));

        let (mut short, remapped, expression) = prepare();
        let retained = short.nodes.len();
        short
            .charge_type_work_for_test(TYPE_WORK_LIMIT - short.type_work.used() - (work - 1))
            .unwrap();
        assert_eq!(
            EffectOperationFamily::rebuild_operation(
                &mut RebuildContext {
                    builder: &mut short,
                    identities: Some(FragmentIdentityView::new(&identities, None)),
                },
                &remapped,
                &expression,
            ),
            Err(TransformError::Build(BuildError::TypeWorkExceeded)),
        );
        assert_eq!(short.nodes.len(), retained);
        for _ in 0..2 {
            let (mut retry, remapped, expression) = prepare();
            retry
                .charge_type_work_for_test(TYPE_WORK_LIMIT - retry.type_work.used() - work)
                .unwrap();
            EffectOperationFamily::rebuild_operation(
                &mut RebuildContext {
                    builder: &mut retry,
                    identities: Some(FragmentIdentityView::new(&identities, None)),
                },
                &remapped,
                &expression,
            )
            .expect("a fresh exact-work retry succeeds");
        }
        let (mut rejected, remapped, expression) = prepare();
        let mut incomplete = identities;
        incomplete.binders.remove(&source_binders[3]);
        assert_eq!(
            EffectOperationFamily::rebuild_operation(
                &mut RebuildContext {
                    builder: &mut rejected,
                    identities: Some(FragmentIdentityView::new(&incomplete, None)),
                },
                &remapped,
                &expression,
            ),
            Err(TransformError::Build(BuildError::InvalidPayload)),
        );
        assert_eq!(rejected.nodes.len(), 1);
    }

    #[test]
    fn fragment_network_relocation_defers_linked_result_until_assembly() {
        use crate::{
            core::effect::NetworkScopeNode, module::ModuleId, resolved::NetworkAcquisition,
            types::EffectRow,
        };

        let source = SourceFile::new("fragment-network.ash", "network").unwrap();
        let span = source.span(ByteRange::new(0, 7).unwrap()).unwrap();
        let origin = Origin::Source(span);
        let mut original = CoreBuilder::<EffectOperationFamily>::with_effect_registry(Arc::new(
            ResolvedRegistry::default(),
        ));
        let handle = original.binder(Type::Unit, origin.clone()).unwrap();
        let old_handle = handle.id();
        let old_inputs = [
            original.unit(Type::Unit, origin.clone()).unwrap(),
            original.unit(Type::Unit, origin.clone()).unwrap(),
            original.unit(Type::Unit, origin.clone()).unwrap(),
            original.unit(Type::Unit, origin.clone()).unwrap(),
        ];
        let old_type = TypeVariableId::generated(0);
        let old_entries = [BinderId::generated(1), BinderId::generated(2)];
        let expression = CoreTypedExpr {
            ty: Type::Unit,
            effects: EffectRow::empty(),
            origin: origin.clone(),
            kind: EffectExprKind::Operation(EffectOperation::Network(Box::new(
                NetworkScopeNode::new(
                    NetworkAcquisition {
                        builtin: ModuleId::new(0),
                        identity: old_type,
                        handle: old_handle,
                        span,
                    },
                    handle,
                    old_entries,
                    old_inputs[0],
                    [old_inputs[1], old_inputs[2]],
                    old_inputs[3],
                ),
            ))),
        };
        let new_handle = BinderId::generated(10);
        let new_entries = [BinderId::generated(11), BinderId::generated(12)];
        let new_type = TypeVariableId::generated(10);
        let identities = FragmentIdentities {
            binders: HashMap::from([
                (old_handle, new_handle),
                (old_entries[0], new_entries[0]),
                (old_entries[1], new_entries[1]),
            ]),
            variables: HashMap::from([(old_type, new_type)]),
            handlers: HashMap::new(),
        };
        let mut destination = CoreBuilder::<EffectOperationFamily>::with_effect_registry(Arc::new(
            ResolvedRegistry::default(),
        ));
        destination.reserve_resolved_binders([new_handle]).unwrap();
        let new_inputs = [
            destination.unit(Type::Unit, origin.clone()).unwrap(),
            destination.unit(Type::Unit, origin.clone()).unwrap(),
            destination.unit(Type::Unit, origin.clone()).unwrap(),
            destination.unit(Type::Unit, origin.clone()).unwrap(),
        ];
        let remapped: Vec<_> = new_inputs.into_iter().map(Some).collect();
        let relocated = EffectOperationFamily::rebuild_operation(
            &mut RebuildContext {
                builder: &mut destination,
                identities: Some(FragmentIdentityView::new(&identities, None)),
            },
            &remapped,
            &expression,
        )
        .expect("the network fragment relocates");
        let network = match &destination.nodes[relocated.index().unwrap()].kind {
            EffectExprKind::Operation(EffectOperation::Network(network)) => network,
            _ => panic!("the rebuilt operation remains a network"),
        };
        assert_eq!(network.acquisition.identity, new_type);
        assert_eq!(network.acquisition.handle, new_handle);
        assert_eq!(network.handle.id(), new_handle);
        assert_eq!(network.entries, new_entries);
        assert_eq!(network.capacity, new_inputs[0]);
        assert_eq!(network.inputs, [new_inputs[1], new_inputs[2]]);
        assert_eq!(network.body, new_inputs[3]);
        assert_eq!(network.linked_result, None);
        destination
            .set_network_linked_result(new_inputs[3])
            .unwrap();
        let EffectExprKind::Operation(EffectOperation::Network(network)) =
            &destination.nodes[relocated.index().unwrap()].kind
        else {
            unreachable!();
        };
        assert_eq!(network.linked_result, Some(new_inputs[3]));
    }

    #[test]
    fn effect_handler_rebuild_is_exact_retryable_and_deep_drop_safe() {
        std::thread::Builder::new()
            .stack_size(64 * 1024)
            .spawn(|| {
                use crate::{
                    core::effect::{HandlerId, HandlerNode},
                    resolved::ResumeId,
                    types::{EffectId, EffectInstance, EffectRow, OperationId},
                };
                let source = SourceFile::new("effect-transform.ash", "handler").unwrap();
                let origin = Origin::Source(source.span(ByteRange::new(0, 7).unwrap()).unwrap());
                let effect = EffectId::new(crate::module::ModuleId::new(0), 0);
                let prepare = |deep| {
                    let mut builder = CoreBuilder::<EffectOperationFamily>::with_effect_registry(
                        Arc::new(ResolvedRegistry::default()),
                    );
                    let body = builder.unit(Type::Unit, origin.clone()).unwrap();
                    let clauses = (0..4)
                        .map(|ordinal| {
                            EffectClause::new(
                                OperationId::new(effect, ordinal),
                                ResumeId::new(ordinal),
                                CoreMatchArm::new(
                                    CorePattern::new(
                                        Type::Unit,
                                        origin.clone(),
                                        CorePatternKind::Wildcard,
                                    ),
                                    body,
                                    origin.clone(),
                                ),
                            )
                        })
                        .collect();
                    let expression = CoreTypedExpr {
                        ty: Type::Unit,
                        effects: EffectRow::empty(),
                        origin: origin.clone(),
                        kind: EffectExprKind::Operation(EffectOperation::Handler(
                            HandlerNode::new(
                                HandlerId::new(0),
                                body,
                                EffectInstance::new(
                                    effect,
                                    vec![deep, Type::Unit].into_boxed_slice(),
                                ),
                                clauses,
                            ),
                        )),
                    };
                    (builder, vec![Some(body)], expression)
                };
                let admitted = || application_type(super::super::CORE_PAYLOAD_DEPTH_LIMIT - 2);
                let (mut measured, remapped, expression) = prepare(admitted());
                let before = measured.type_work.used();
                EffectOperationFamily::rebuild_operation(
                    &mut RebuildContext {
                        builder: &mut measured,
                        identities: None,
                    },
                    &remapped,
                    &expression,
                )
                .unwrap();
                let work = measured.type_work.used() - before;

                let (mut short, remapped, expression) = prepare(admitted());
                let retained = short.nodes.len();
                short
                    .charge_type_work_for_test(
                        TYPE_WORK_LIMIT - short.type_work.used() - (work - 1),
                    )
                    .unwrap();
                assert_eq!(
                    EffectOperationFamily::rebuild_operation(
                        &mut RebuildContext {
                            builder: &mut short,
                            identities: None
                        },
                        &remapped,
                        &expression,
                    ),
                    Err(TransformError::Build(BuildError::TypeWorkExceeded)),
                );
                assert_eq!(short.nodes.len(), retained);
                for _ in 0..2 {
                    let (mut retry, remapped, expression) = prepare(admitted());
                    retry
                        .charge_type_work_for_test(TYPE_WORK_LIMIT - retry.type_work.used() - work)
                        .unwrap();
                    EffectOperationFamily::rebuild_operation(
                        &mut RebuildContext {
                            builder: &mut retry,
                            identities: None,
                        },
                        &remapped,
                        &expression,
                    )
                    .expect("fresh exact retry");
                }
                let rejected_type = (0..32_768).fold(Type::Unit, |ty, _| {
                    Type::Function(Box::new(Type::Unit), Box::new(ty))
                });
                let (mut rejected, remapped, expression) = prepare(rejected_type);
                assert_eq!(
                    EffectOperationFamily::rebuild_operation(
                        &mut RebuildContext {
                            builder: &mut rejected,
                            identities: None
                        },
                        &remapped,
                        &expression,
                    ),
                    Err(TransformError::Build(BuildError::TypeDepthExceeded)),
                );
                expression.discard_iteratively();
            })
            .unwrap()
            .join()
            .expect("deep effect metadata teardown stays on the small stack");
    }

    #[test]
    fn row_bearing_deep_abstraction_failure_dismantles_integrated_transform_state() {
        std::thread::Builder::new()
            .name("integrated-row-bearing-transform-owner".into())
            .stack_size(256 * 1024)
            .spawn(|| {
                const TYPE_DEPTH: usize = 32_768;
                const KIND_DEPTH: usize = 16_384;
                const KIND_NODES: usize = 2 * KIND_DEPTH + 1;
                const TYPE_CELLS: usize = 2 * TYPE_DEPTH + 1;
                // Forall root + binder record + binder Kind + body Type.
                const SCHEME_WORK: usize = 1 + 1 + KIND_NODES + TYPE_CELLS;
                // The abstraction payload independently clones its binder
                // record and Kind after the body remap succeeds.
                const PARAMETER_WORK: usize = 1 + KIND_NODES;
                const REBUILD_WORK: usize = SCHEME_WORK + PARAMETER_WORK + SCHEME_WORK;
                const BODY_WORK: usize = 1;

                let fixture = linked_row_bearing_fold_fixture();
                let registry = isolated_pure_fold_registry(&fixture);
                let rows = global_row_shape(&registry);
                let entry_rows = rows
                    .iter()
                    .filter(|(owner, _)| owner.module() == Some(fixture.graph.entry()))
                    .cloned()
                    .collect::<Vec<_>>();
                let [(owner, parameters)] = entry_rows.as_slice() else {
                    panic!("the integrated transform fixture must retain one global row");
                };
                let [resolved_parameter] = parameters.as_slice() else {
                    panic!("the integrated transform row must retain one parameter");
                };
                assert!(owner.module().is_some());
                assert!(matches!(
                    registry
                        .type_variable(*resolved_parameter)
                        .expect("the row parameter must retain its canonical record")
                        .kind,
                    Kind::Arrow(_, _),
                ));

                let source = fixture
                    .graph
                    .modules()
                    .iter()
                    .find(|module| module.id() == fixture.graph.entry())
                    .expect("the integrated fixture must retain its source")
                    .source();
                let span = source
                    .span(ByteRange::new(0, 1).expect("the integrated range is ordered"))
                    .expect("the integrated span belongs to its source");
                let pure = row_bearing_fold_program_with_initial_type_work(
                    Arc::clone(&registry),
                    *owner,
                    *resolved_parameter,
                    Origin::Source(span),
                    0,
                )
                .unwrap();
                let pure = super::super::validate::validate_modules(
                    pure,
                    &fixture.sources(),
                    &fixture.module_sources,
                )
                .unwrap();
                let generated_parameter = TypeVariableId::generated(90_001);
                let parameter_kind = deep_arrow_kind(KIND_DEPTH);
                let expression = super::super::TypedExpr {
                    effects: (),
                    ty: Type::Forall(
                        Box::new([(generated_parameter, parameter_kind.clone())]),
                        Box::new(application_type(TYPE_DEPTH)),
                    ),
                    origin: deep_origin(source, super::super::CORE_PAYLOAD_DEPTH_LIMIT),
                    kind: PureExprKind::Computation(PureComputation::TypeAbstraction(
                        super::super::type_ops::TypeAbstractionNode::new(
                            vec![(generated_parameter, parameter_kind)],
                            pure.root(),
                        ),
                    )),
                };

                let Type::Forall(scheme_parameters, scheme_body) = &expression.ty else {
                    panic!("the integrated input must retain its deep scheme");
                };
                assert_eq!(scheme_parameters[0].0, generated_parameter);
                assert_eq!(arrow_kind_depth(&scheme_parameters[0].1), KIND_DEPTH);
                assert_eq!(application_spine_depth(scheme_body), TYPE_DEPTH);
                let PureExprKind::Computation(PureComputation::TypeAbstraction(abstraction)) =
                    &expression.kind
                else {
                    panic!("the integrated input must remain a type abstraction");
                };
                assert_eq!(abstraction.body(), pure.root());
                assert_eq!(abstraction.parameters()[0].0, generated_parameter);
                assert_eq!(arrow_kind_depth(&abstraction.parameters()[0].1), KIND_DEPTH);
                assert_eq!(
                    origin_depth(&expression.origin),
                    super::super::CORE_PAYLOAD_DEPTH_LIMIT,
                );
                const { assert!(BODY_WORK + REBUILD_WORK < TYPE_WORK_LIMIT) };

                let owners_before = Arc::strong_count(&registry);
                let mut output = CoreBuilder::with_registry(Arc::clone(&registry));
                let body = output
                    .unit(Type::Unit, Origin::Source(span))
                    .expect("the mapped output body must fit");
                let mut remapped = vec![None; pure.node_count()];
                remapped[node_index(pure.root()).expect("the root index must fit")] = Some(body);
                output
                    .charge_type_work_for_test(TYPE_WORK_LIMIT - BODY_WORK - (REBUILD_WORK - 1))
                    .expect("the late one-short allowance must fit");
                let error = rebuild_node(&mut output, &pure, &remapped, &expression, false)
                    .expect_err(
                        "one missing final admission cell must reject the rebuilt abstraction",
                    );
                assert_eq!(error, TransformError::Build(BuildError::TypeWorkExceeded));
                drop(output);
                assert_eq!(Arc::strong_count(&registry), owners_before);
                assert_eq!(global_row_shape(&registry), rows);

                let mut exact_output = CoreBuilder::with_registry(Arc::clone(&registry));
                let exact_body = exact_output
                    .unit(Type::Unit, Origin::Source(span))
                    .expect("the exact mapped output body must fit");
                let mut exact_remapped = vec![None; pure.node_count()];
                exact_remapped[node_index(pure.root()).expect("the exact root index must fit")] =
                    Some(exact_body);
                exact_output
                    .charge_type_work_for_test(TYPE_WORK_LIMIT - BODY_WORK - REBUILD_WORK)
                    .expect("the exact integrated allowance must fit");
                let rebuilt = rebuild_node(
                    &mut exact_output,
                    &pure,
                    &exact_remapped,
                    &expression,
                    false,
                )
                .expect("the exact integrated allowance must rebuild the abstraction");
                let exact = exact_output
                    .finish(rebuilt)
                    .expect("the exact integrated output must finish unchecked");
                assert!(Arc::ptr_eq(&exact.registry, &registry));
                assert_eq!(global_row_shape(&exact.registry), rows);
                exact.discard_iteratively();
                assert_eq!(Arc::strong_count(&registry), owners_before);

                expression.discard_iteratively();
                drop(fixture);
                drop(registry);
            })
            .expect("the integrated transform worker must start")
            .join()
            .expect("integrated rejected and exact transform state must dismantle on 256 KiB");
    }

    #[test]
    fn late_pattern_rebuild_failure_discards_completed_patterns_iteratively() {
        std::thread::Builder::new()
            .name("late-pattern-transform-owner".into())
            .stack_size(256 * 1024)
            .spawn(|| {
                const DEPTH: usize = 32_000;
                let source =
                    SourceFile::new("transform-owner.ash", "()").expect("the fixture should fit");
                let origin = Origin::Source(
                    source
                        .span(ByteRange::new(0, 2).expect("ordered range"))
                        .expect("fixture span"),
                );
                let binder_id = BinderId::new(0);
                let mut builder = CoreBuilder::new();
                builder
                    .reserve_resolved_binders([binder_id])
                    .expect("the test binder is reserved");
                let binder = builder
                    .resolved_binder(binder_id, Type::Unit, origin.clone())
                    .expect("the first materialization succeeds");
                let pattern = CorePattern::new(
                    Type::Tuple(vec![application_type(DEPTH), Type::Unit].into_boxed_slice()),
                    origin.clone(),
                    CorePatternKind::Tuple(
                        vec![
                            CorePattern::new(
                                application_type(DEPTH),
                                origin.clone(),
                                CorePatternKind::Wildcard,
                            ),
                            CorePattern::new(Type::Unit, origin, CorePatternKind::Binder(binder)),
                        ]
                        .into_boxed_slice(),
                    ),
                );

                let error = rebuild_pattern(&mut builder, &pattern)
                    .expect_err("the duplicate binder materialization is rejected");
                assert_eq!(
                    error,
                    TransformError::Build(BuildError::DuplicateResolvedBinder)
                );
                pattern.discard_iteratively();
                drop(builder);
            })
            .expect("small-stack transform thread should start")
            .join()
            .expect("late pattern-transform teardown must fit the small stack");
    }

    #[test]
    fn deep_type_application_arguments_survive_a_late_missing_remap() {
        std::thread::Builder::new()
            .name("transform-type-argument-owner".into())
            .stack_size(256 * 1024)
            .spawn(|| {
                const DEPTH: usize = 32_768;
                let source = SourceFile::new("transform-argument.ash", "()").expect("test source");
                let origin = Origin::Source(
                    source
                        .span(ByteRange::new(0, 2).expect("ordered range"))
                        .expect("test span"),
                );
                let mut input = CoreBuilder::new();
                let input_root = input.unit(Type::Unit, origin.clone()).expect("input root");
                let program = super::super::validate::validate(
                    input.finish(input_root).expect("input program"),
                    &[&source],
                )
                .expect("input validates");
                let expression = super::super::TypedExpr {
                    effects: (),
                    ty: Type::Unit,
                    origin: origin.clone(),
                    kind: PureExprKind::Computation(PureComputation::TypeApplication(
                        super::super::type_ops::TypeApplicationNode::new(
                            program.root(),
                            vec![application_type(DEPTH)],
                        ),
                    )),
                };
                let mut output = CoreBuilder::new();
                let remapped = vec![None; program.node_count()];

                let error = rebuild_node(&mut output, &program, &remapped, &expression, false)
                    .expect_err("the deliberately absent function remap is an invariant failure");
                assert_eq!(error, TransformError::InvalidValidatedInput);

                expression.discard_iteratively();
            })
            .expect("small-stack argument-owner thread should start")
            .join()
            .expect("late missing-remap teardown must fit the small stack");
    }

    #[test]
    fn accumulated_type_arguments_survive_one_short_result_clone() {
        std::thread::Builder::new()
            .name("transform-result-clone-owner".into())
            .stack_size(256 * 1024)
            .spawn(|| {
                const DEPTH: usize = 32_768;
                const DEEP_CELLS: usize = 2 * DEPTH + 1;
                const ARGUMENT_CELLS: usize = DEEP_CELLS + 1;
                let source = SourceFile::new("transform-result.ash", "()").expect("test source");
                let origin = Origin::Source(
                    source
                        .span(ByteRange::new(0, 2).expect("ordered range"))
                        .expect("test span"),
                );
                let mut input = CoreBuilder::new();
                let input_root = input.unit(Type::Unit, origin.clone()).expect("input root");
                let program = super::super::validate::validate(
                    input.finish(input_root).expect("input program"),
                    &[&source],
                )
                .expect("input validates");
                let expression = super::super::TypedExpr {
                    effects: (),
                    ty: Type::Unit,
                    origin,
                    kind: PureExprKind::Computation(PureComputation::TypeApplication(
                        super::super::type_ops::TypeApplicationNode::new(
                            program.root(),
                            vec![application_type(DEPTH), Type::Unit],
                        ),
                    )),
                };
                let mut output = CoreBuilder::new();
                output
                    .charge_type_work_for_test(TYPE_WORK_LIMIT - ARGUMENT_CELLS)
                    .expect("the exact argument-clone allowance remains");

                let error = rebuild_node(&mut output, &program, &[], &expression, false)
                    .expect_err("the one-short result clone must fail after both arguments");
                assert_eq!(error, TransformError::Build(BuildError::TypeWorkExceeded));

                expression.discard_iteratively();
            })
            .expect("small-stack result-owner thread should start")
            .join()
            .expect("late result-clone teardown must fit the small stack");
    }

    #[test]
    fn extracted_tuple_and_constructor_children_survive_parent_clone_failure() {
        std::thread::Builder::new()
            .name("transform-pattern-child-owner".into())
            .stack_size(256 * 1024)
            .spawn(|| {
                const DEPTH: usize = 32_768;
                const DEEP_CELLS: usize = 2 * DEPTH + 1;
                let source = SourceFile::new("transform-pattern.ash", "()").expect("test source");
                let origin = Origin::Source(
                    source
                        .span(ByteRange::new(0, 2).expect("ordered range"))
                        .expect("test span"),
                );

                let tuple = CorePattern::new(
                    Type::Unit,
                    origin.clone(),
                    CorePatternKind::Tuple(
                        vec![
                            CorePattern::new(
                                application_type(DEPTH),
                                origin.clone(),
                                CorePatternKind::Wildcard,
                            ),
                            CorePattern::new(Type::Unit, origin.clone(), CorePatternKind::Wildcard),
                        ]
                        .into_boxed_slice(),
                    ),
                );
                let mut tuple_builder = CoreBuilder::new();
                tuple_builder
                    .charge_type_work_for_test(TYPE_WORK_LIMIT - (DEEP_CELLS + 1))
                    .expect("the exact tuple-child allowance remains");
                assert_eq!(
                    rebuild_pattern(&mut tuple_builder, &tuple),
                    Err(TransformError::Build(BuildError::TypeWorkExceeded))
                );
                tuple.discard_iteratively();

                let constructor = CorePattern::new(
                    Type::Unit,
                    origin.clone(),
                    CorePatternKind::Constructor {
                        constructor: ConstructorId::new(NominalTypeId::new(source.id(), 0), 0),
                        payload: Some(Box::new(CorePattern::new(
                            application_type(DEPTH),
                            origin,
                            CorePatternKind::Wildcard,
                        ))),
                    },
                );
                let mut constructor_builder = CoreBuilder::new();
                constructor_builder
                    .charge_type_work_for_test(TYPE_WORK_LIMIT - DEEP_CELLS)
                    .expect("the exact constructor-child allowance remains");
                assert_eq!(
                    rebuild_pattern(&mut constructor_builder, &constructor),
                    Err(TransformError::Build(BuildError::TypeWorkExceeded))
                );
                constructor.discard_iteratively();
            })
            .expect("small-stack pattern-child thread should start")
            .join()
            .expect("extracted pattern-child teardown must fit the small stack");
    }

    #[test]
    fn rebuilt_deep_match_pattern_survives_missing_body_remap() {
        std::thread::Builder::new()
            .name("transform-match-pattern-owner".into())
            .stack_size(256 * 1024)
            .spawn(|| {
                const DEPTH: usize = 32_768;
                let source = SourceFile::new("transform-match.ash", "()").expect("test source");
                let origin = Origin::Source(
                    source
                        .span(ByteRange::new(0, 2).expect("ordered range"))
                        .expect("test span"),
                );
                let mut input = CoreBuilder::new();
                let input_root = input.unit(Type::Unit, origin.clone()).expect("input root");
                let program = super::super::validate::validate(
                    input.finish(input_root).expect("input program"),
                    &[&source],
                )
                .expect("input validates");
                let pattern = CorePattern::new(
                    application_type(DEPTH),
                    origin.clone(),
                    CorePatternKind::Wildcard,
                );
                let expression = super::super::TypedExpr {
                    effects: (),
                    ty: Type::Unit,
                    origin: origin.clone(),
                    kind: PureExprKind::Computation(PureComputation::Match(
                        super::super::MatchNode::new(
                            program.root(),
                            vec![CoreMatchArm::new(pattern, program.root(), origin)],
                        ),
                    )),
                };
                let mut output = CoreBuilder::new();
                let remapped = vec![None; program.node_count()];

                let error = rebuild_node(&mut output, &program, &remapped, &expression, false)
                    .expect_err("the deliberately absent arm-body remap is an invariant failure");
                assert_eq!(error, TransformError::InvalidValidatedInput);

                expression.discard_iteratively();
            })
            .expect("small-stack match-pattern thread should start")
            .join()
            .expect("missing-remap pattern teardown must fit the small stack");
    }

    #[test]
    fn transforms_rebuild_validated_newtype_conversions() {
        const REMAP_WORK: usize = 2; // one slot per input node
        const CHILD_COPY_WORK: usize = 2; // clone + admit `Unit`
        const CONVERSION_COPY_WORK: usize = 2; // clone + admit `Unit`
        const EXACT_WORK: usize = REMAP_WORK + CHILD_COPY_WORK + CONVERSION_COPY_WORK;
        let source = SourceFile::new("transform-conversion.ash", "()").expect("test source");
        let origin = Origin::Source(
            source
                .span(ByteRange::new(0, 2).expect("ordered range"))
                .expect("source span"),
        );
        let owner = NominalTypeId::new(source.id(), 0);
        let mut builder = CoreBuilder::new();
        let child = builder
            .unit(Type::Unit, origin.clone())
            .expect("the conversion child should fit");
        let root = builder
            .newtype_conversion(
                owner,
                NewtypeConversionDirection::Wrap,
                child,
                Type::Unit,
                origin,
            )
            .expect("the conversion carrier should fit");
        let program = super::super::dialect::forge_validated_for_test(
            builder.finish(root).expect("the conversion should finish"),
        );

        let identity = identity_traversal(&program).expect("identity must rebuild the conversion");
        let folded =
            fold_literal_primitives(&program).expect("folding must rebuild the conversion");
        for rebuilt in [&identity, &folded] {
            assert!(matches!(
                rebuilt.expression_kinds_for_test().nth(1),
                Some(PureExprKind::Computation(PureComputation::NewtypeConversion(
                    conversion,
                ))) if conversion.owner() == owner
                    && conversion.direction() == NewtypeConversionDirection::Wrap
            ));
        }
        for fold_literal_primitives in [false, true] {
            assert_eq!(
                rebuild_with_initial_type_work(
                    &program,
                    fold_literal_primitives,
                    TYPE_WORK_LIMIT - (EXACT_WORK - 1),
                )
                .expect_err("one-short newtype transform must reject"),
                TransformError::Build(BuildError::TypeWorkExceeded),
            );
            for _ in 0..2 {
                let rebuilt = rebuild_with_initial_type_work(
                    &program,
                    fold_literal_primitives,
                    TYPE_WORK_LIMIT - EXACT_WORK,
                )
                .expect("exact newtype transform should retry");
                assert_eq!(rebuilt.expression_kinds_for_test().count(), 2);
                drop(rebuilt);
            }
        }
    }

    #[test]
    fn transform_conversion_rebuild_and_teardown_fit_a_small_stack() {
        const DEPTH: usize = 32_768;

        std::thread::Builder::new()
            .name("transform-newtype-conversion-rebuild".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let source =
                    SourceFile::new("transform-conversion-chain.ash", "()").expect("test source");
                let origin = Origin::Source(
                    source
                        .span(ByteRange::new(0, 2).expect("ordered range"))
                        .expect("source span"),
                );
                let owner = NominalTypeId::new(source.id(), 0);
                let mut builder = CoreBuilder::new();
                let mut root = builder
                    .unit(Type::Unit, origin.clone())
                    .expect("the conversion leaf should fit");
                for index in 0..DEPTH {
                    root = builder
                        .newtype_conversion(
                            owner,
                            if index % 2 == 0 {
                                NewtypeConversionDirection::Wrap
                            } else {
                                NewtypeConversionDirection::Unwrap
                            },
                            root,
                            Type::Unit,
                            origin.clone(),
                        )
                        .expect("the conversion chain should fit");
                }
                let program = super::super::dialect::forge_validated_for_test(
                    builder.finish(root).expect("the conversion should finish"),
                );
                let identity = identity_traversal(&program)
                    .expect("identity must rebuild the conversion chain");
                let folded = fold_literal_primitives(&program)
                    .expect("folding must rebuild the conversion chain");
                drop(identity);
                drop(folded);
            })
            .expect("the transform rebuild thread should start")
            .join()
            .expect("transform conversion rebuilding must fit a small stack");
    }
}
