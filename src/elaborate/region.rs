//! Lower lexical owners and selections to explicit provider pairs and handlers.

use super::*;
use crate::module::ModuleId;
use crate::{
    core::{
        packed::Intrinsic,
        region::{HostRegionConfiguration, RegionAllocateNode, RegionScopeNode},
    },
    resolved::{RegionApi, ResolvedRegionExpr, ResolvedRegionSelectionExpr},
};

pub(super) struct RegionProgress<'a> {
    pub source: &'a ResolvedRegionExpr,
    pub span: Span,
    pub provider: TypedNodeOwner,
    pub access: TypedBinder,
    pub provider_rows: EffectRow,
}

pub(super) struct SelectionProgress {
    pub span: Span,
    pub operand: TypedNodeOwner,
    pub selected: TypedBinder,
}

impl<F: CoreLoweringFamily> CoreElaborator<F> {
    pub(super) fn active_region_api(&mut self) -> Result<Option<RegionApi>, TypeError> {
        self.type_work
            .charge(self.registry.effects().len())
            .map_err(|()| type_resource())?;
        Ok(self
            .registry
            .effects()
            .iter()
            .find_map(|effect| RegionApi::for_module(effect.id.module())))
    }

    pub(super) fn saved_region_context(
        &mut self,
        api: RegionApi,
        span: Span,
    ) -> Result<(TypedBinder, NodeId, NodeId), TypeError> {
        let context = self
            .builder
            .binder(Type::Nominal(api.region_view()), Origin::Source(span))?;
        let context_value = self.builder.variable(
            context.id(),
            Type::Nominal(api.region_view()),
            Origin::Source(span),
        )?;
        let unit = self.builder.unit(Type::Unit, Origin::Source(span))?;
        let instance = EffectInstance::new(api.default_alloc(), Box::new([]));
        let row = self.core_effect_row(&EffectRow::singleton(instance.clone()))?;
        let query = self.push_effect_core(
            Type::Nominal(api.region_view()),
            row,
            Origin::Source(span),
            EffectOperation::Request(RequestNode::new(
                instance,
                crate::types::OperationId::new(api.default_alloc(), 1),
                unit,
            )),
        )?;
        Ok((context, context_value, query))
    }

    pub(super) fn construct_function(
        &mut self,
        parameter: TypedBinder,
        body: NodeId,
        ty: Type,
        origin: Origin,
    ) -> Result<NodeId, TypeError> {
        if !F::EFFECTS || self.active_region_api()?.is_none() {
            return Ok(self.builder.function(parameter, body, ty, origin)?);
        }
        self.construct_closure_code(
            crate::core::region::RegionClosureCode::Function(
                crate::core::function::FunctionNode::new(parameter, body),
            ),
            ty,
            origin,
        )
    }

    pub(super) fn construct_adapter_captures(
        &mut self,
        body: NodeId,
        ty: Type,
        origin: Origin,
    ) -> Result<NodeId, TypeError> {
        if !F::EFFECTS || self.active_region_api()?.is_none() {
            return Ok(body);
        }
        self.construct_closure_code(
            crate::core::region::RegionClosureCode::Adapter { body },
            ty,
            origin,
        )
    }

    fn construct_closure_code(
        &mut self,
        code: crate::core::region::RegionClosureCode,
        ty: Type,
        origin: Origin,
    ) -> Result<NodeId, TypeError> {
        let span = origin.primary_span();
        let api = self.region_api_at(span)?;
        let (context, context_value, query) = self.saved_region_context(api, span)?;
        let row = EffectRow::singleton(EffectInstance::new(api.default_alloc(), Box::new([])));
        let request = self.push_effect_core(
            Type::Nominal(api.request()),
            EffectRow::empty(),
            Origin::Source(span),
            EffectOperation::RegionValueRequest(crate::core::region::RegionValueRequestNode {
                api: api.module(),
                fields: 1,
            }),
        )?;
        let allocation_row = self.core_effect_row(&row)?;
        let storage = self.push_effect_core(
            Type::Nominal(api.storage_view()),
            allocation_row,
            Origin::Source(span),
            EffectOperation::RegionAllocate(RegionAllocateNode {
                api: api.module(),
                context: context_value,
                request,
            }),
        )?;
        let result_type = self.clone_type(&ty)?;
        let creation_row = self.core_effect_row(&row)?;
        self.type_work.charge(1).map_err(|()| type_resource())?;
        self.pending_region_closures
            .try_reserve(1)
            .map_err(|_| type_resource())?;
        let closure = self.push_effect_core(
            ty,
            creation_row,
            origin,
            EffectOperation::RegionClosure(crate::core::region::RegionClosureNode {
                api: api.module(),
                context: context_value,
                captures: Box::new([]),
                storage,
                code,
            }),
        )?;
        self.pending_region_closures.push((closure, request));
        Ok(self
            .builder
            .binding(context, query, closure, result_type, Origin::Source(span))?)
    }

    pub(super) fn prepare_region_closures(
        &mut self,
        methods: &[crate::core::capture::MethodUse],
        roots: &[(BinderId, NodeId)],
    ) -> Result<(), TypeError> {
        let Some(builder) = F::effect_builder(&mut self.builder) else {
            return Ok(());
        };
        for &(node, request) in &self.pending_region_closures {
            crate::core::capture::prepare_region_closure(
                builder,
                node,
                request,
                methods,
                roots,
                &mut self.type_work,
            )
            .map_err(|failure| capture_failure(failure, &mut self.type_work))?;
        }
        self.pending_region_closures.clear();
        Ok(())
    }

    pub(super) fn initialize_region_buffer(
        &mut self,
        operation: crate::core::region::RegionBufferOperation,
        operand: Option<NodeId>,
        right: Option<NodeId>,
        ty: &Type,
        effects: &EffectRow,
        span: Span,
    ) -> Result<NodeId, TypeError> {
        let api = self.region_api_at(span)?;
        let (context, context_value, query) = self.saved_region_context(api, span)?;
        let row = self.core_effect_row(effects)?;
        let result = self.clone_type(ty)?;
        let node = self.push_effect_core(
            result,
            row,
            Origin::Source(span),
            EffectOperation::RegionBuffer(crate::core::region::RegionBufferNode {
                api: api.module(),
                context: context_value,
                operand,
                right,
                operation,
            }),
        )?;
        let result = self.clone_type(ty)?;
        Ok(self
            .builder
            .binding(context, query, node, result, Origin::Source(span))?)
    }

    pub(super) fn lower_buffer_intrinsic(
        &mut self,
        intrinsic: Intrinsic,
        module: ModuleId,
        ty: &Type,
        span: Span,
    ) -> Result<NodeId, TypeError> {
        let function = ty.function_view().ok_or_else(invalid_state)?;
        let domain = self.clone_type(function.domain())?;
        let parameter = self.builder.binder(domain, Origin::Source(span))?;
        let domain = self.clone_type(function.domain())?;
        let operand = self
            .builder
            .variable(parameter.id(), domain, Origin::Source(span))?;
        let body = self.initialize_region_buffer(
            crate::core::region::RegionBufferOperation::Intrinsic(
                crate::core::packed::IntrinsicNode::new(intrinsic, module),
            ),
            Some(operand),
            None,
            function.value(),
            function.effects().ok_or_else(invalid_state)?,
            span,
        )?;
        let ty = self.clone_type(ty)?;
        self.construct_function(parameter, body, ty, Origin::Source(span))
    }

    pub(super) fn initialize_region_tuple(
        &mut self,
        operands: Vec<NodeId>,
        ty: &Type,
        effects: &EffectRow,
        span: Span,
    ) -> Result<NodeId, TypeError> {
        self.initialize_region_record(None, operands, ty, effects, span)
    }

    pub(super) fn initialize_region_record(
        &mut self,
        constructor: Option<crate::types::ConstructorId>,
        operands: Vec<NodeId>,
        ty: &Type,
        effects: &EffectRow,
        span: Span,
    ) -> Result<NodeId, TypeError> {
        use crate::core::region::{RegionTupleNode, RegionValueRequestNode};
        let api = self.region_api_at(span)?;
        if constructor.is_none()
            && !matches!(ty, Type::Tuple(types) if types.len() == operands.len())
        {
            return Err(invalid_state());
        }
        self.type_work
            .charge(operands.len())
            .map_err(|()| type_resource())?;
        let (context, context_value, query) = self.saved_region_context(api, span)?;
        let default_row =
            EffectRow::singleton(EffectInstance::new(api.default_alloc(), Box::new([])));
        let request = self.push_effect_core(
            Type::Nominal(api.request()),
            EffectRow::empty(),
            Origin::Source(span),
            EffectOperation::RegionValueRequest(RegionValueRequestNode {
                api: api.module(),
                fields: operands.len() + usize::from(constructor.is_some()),
            }),
        )?;
        let allocate_row = self.core_effect_row(&default_row)?;
        let allocated = self.push_effect_core(
            Type::Nominal(api.storage_view()),
            allocate_row,
            Origin::Source(span),
            EffectOperation::RegionAllocate(RegionAllocateNode {
                api: api.module(),
                context: context_value,
                request,
            }),
        )?;
        let result_type = self.clone_type(ty)?;
        let initialized_effects = self.core_effect_row(effects)?;
        let initialized = self.push_effect_core(
            result_type,
            initialized_effects,
            Origin::Source(span),
            EffectOperation::RegionTuple(RegionTupleNode {
                constructor,
                api: api.module(),
                context: context_value,
                storage: allocated,
                fields: operands.into_boxed_slice(),
            }),
        )?;
        let result_type = self.clone_type(ty)?;
        Ok(self.builder.binding(
            context,
            query,
            initialized,
            result_type,
            Origin::Source(span),
        )?)
    }

    pub(super) fn wrap_region_entry(&mut self, body: TypedNode) -> Result<TypedNode, TypeError> {
        let body = TypedNodeOwner::new(body);
        let span = body.provenance.span().ok_or_else(invalid_state)?;
        let api = self.region_api_at(span)?;
        let identity = TypeVariableId::generated(self.next_generated_type_variable);
        self.next_generated_type_variable = self
            .next_generated_type_variable
            .checked_sub(1)
            .ok_or_else(invalid_state)?;
        let access = self
            .builder
            .binder(Type::Nominal(api.region_view()), Origin::Source(span))?;
        let provider = self.host_pair(api, identity, span)?;
        let body = TypedNodeOwner::new(self.forward_default(body, &access, api, span)?);
        let preceding = self.builder.unit(Type::Unit, Origin::Source(span))?;
        let default = EffectInstance::new(api.default_alloc(), Box::new([]));
        let effects = self.remove_cleanup_effect(&body.effects, &default, span, true)?;
        let result_type = self.clone_type(&body.ty)?;
        let core_effects = self.core_effect_row(&effects)?;
        let node = self.push_effect_core(
            result_type,
            core_effects,
            Origin::Source(span),
            EffectOperation::Region(Box::new(RegionScopeNode {
                entry: true,
                api: api.module(),
                identity,
                access,
                preceding,
                provider: provider.node,
                body: body.node,
            })),
        )?;
        Ok(TypedNode {
            node,
            ty: self.clone_type(&body.ty)?,
            effects,
            provenance: self.at_span_provenance(&body.ty, span)?,
        })
    }

    fn region_api_at(&mut self, _span: Span) -> Result<RegionApi, TypeError> {
        self.type_work
            .charge(self.registry.effects().len())
            .map_err(|()| type_resource())?;
        let mut candidates = self
            .registry
            .effects()
            .iter()
            .filter_map(|effect| RegionApi::for_module(effect.id.module()));
        let api = candidates.next().ok_or_else(invalid_state)?;
        if candidates.next().is_some() {
            return Err(invalid_state());
        }
        Ok(api)
    }

    pub(super) fn schedule_region<'a>(
        &mut self,
        source: &'a ResolvedRegionExpr,
        span: Span,
        tasks: &mut ElaborationTaskBuffer<'a>,
    ) -> Result<(), TypeError> {
        self.type_work.charge(2).map_err(|()| type_resource())?;
        tasks.0.try_reserve(2).map_err(|_| type_resource())?;
        tasks.push(ElaborationTask::RegionBody { source, span });
        if let Some(provider) = &source.provider {
            tasks.push(ElaborationTask::Synthesize {
                expression: provider,
                cause: None,
            });
        }
        Ok(())
    }

    fn host_pair(
        &mut self,
        api: RegionApi,
        owner: TypeVariableId,
        span: Span,
    ) -> Result<TypedNodeOwner, TypeError> {
        self.type_work.charge(12).map_err(|()| type_resource())?;
        let allocate_type = Type::Function(
            Box::new(Type::Nominal(api.request())),
            Box::new(Type::Application(
                Box::new(Type::Nominal(api.storage())),
                Box::new(Type::Variable(owner)),
            )),
        );
        let release_type = Type::Function(Box::new(Type::Unit), Box::new(Type::Unit));
        let allocate_core_type = self.clone_type(&allocate_type)?;
        let allocate = self.builder.intrinsic(
            Intrinsic::RegionHostAllocate {
                owner,
                configuration: HostRegionConfiguration::System,
            },
            api.module(),
            allocate_core_type,
            Origin::Source(span),
        )?;
        let release_core_type = self.clone_type(&release_type)?;
        let release = self.builder.intrinsic(
            Intrinsic::RegionHostRelease {
                owner,
                configuration: HostRegionConfiguration::System,
            },
            api.module(),
            release_core_type,
            Origin::Source(span),
        )?;
        let ty = Type::Tuple(Box::new([allocate_type, release_type]));
        let core_type = self.clone_type(&ty)?;
        let node = self
            .builder
            .tuple(vec![allocate, release], core_type, Origin::Source(span))?;
        Ok(TypedNodeOwner::new(TypedNode {
            node,
            ty,
            effects: EffectRow::empty(),
            provenance: TypeProvenance::atom(Some(span)),
        }))
    }

    fn pair_rows(
        &mut self,
        api: RegionApi,
        owner: TypeVariableId,
        pair: &Type,
        span: Span,
    ) -> Result<EffectRow, TypeError> {
        let pair = IterativeTypeOwner::new(self.zonk(pair)?);
        let Type::Tuple(members) = &*pair else {
            return Err(pattern_mismatch(span, &pair, &self.registry));
        };
        let [allocate, release] = members.as_ref() else {
            return Err(pattern_mismatch(span, &pair, &self.registry));
        };
        let allocate = allocate
            .function_view()
            .ok_or_else(|| pattern_mismatch(span, &pair, &self.registry))?;
        let release = release
            .function_view()
            .ok_or_else(|| pattern_mismatch(span, &pair, &self.registry))?;
        self.refine_pattern_expected(allocate.domain(), &Type::Nominal(api.request()), span)?;
        self.refine_pattern_expected(
            allocate.value(),
            &Type::Application(
                Box::new(Type::Nominal(api.storage())),
                Box::new(Type::Variable(owner)),
            ),
            span,
        )?;
        self.refine_pattern_expected(release.domain(), &Type::Unit, span)?;
        self.refine_pattern_expected(release.value(), &Type::Unit, span)?;
        let allocate_row = match allocate.effects() {
            Some(row) => clone_effect_row_with_budget(row, &mut self.type_work)
                .map_err(|()| type_resource())?,
            None => EffectRow::empty(),
        };
        let release_row = match release.effects() {
            Some(row) => clone_effect_row_with_budget(row, &mut self.type_work)
                .map_err(|()| type_resource())?,
            None => EffectRow::empty(),
        };
        self.union_effects(&allocate_row, &release_row, span)
    }

    pub(super) fn region_body<'a>(
        &mut self,
        source: &'a ResolvedRegionExpr,
        span: Span,
        context: &mut TypeContext,
        tasks: &mut ElaborationTaskBuffer<'a>,
        values: &mut TypedNodeBuffer,
    ) -> Result<(), TypeError> {
        let api = self.region_api_at(span)?;
        let provider = if source.provider.is_some() {
            values.pop().ok_or_else(invalid_state)?
        } else {
            self.host_pair(api, source.identity.id, span)?
        };
        let provider_rows = self.pair_rows(api, source.identity.id, &provider.ty, span)?;
        let view_type = Type::Nominal(api.region_view());
        let provenance =
            self.at_span_provenance(&view_type, source.handle.origin.primary_span())?;
        context
            .binders
            .try_reserve(1)
            .map_err(|_| type_resource())?;
        if context.insert_with_provenance(
            source.handle.id,
            self.clone_type(&view_type)?,
            provenance,
        )? {
            return Err(invalid_state());
        }
        let access = self.builder.resolved_binder(
            source.handle.id,
            view_type,
            source.handle.origin.clone(),
        )?;
        self.type_work.charge(2).map_err(|()| type_resource())?;
        tasks.0.try_reserve(2).map_err(|_| type_resource())?;
        tasks.push(ElaborationTask::FinishRegion(Box::new(RegionProgress {
            source,
            span,
            provider,
            access,
            provider_rows,
        })));
        tasks.push(ElaborationTask::Synthesize {
            expression: &source.body,
            cause: None,
        });
        Ok(())
    }

    /// Both clauses are ordinary Core clauses. Allocation is always directed to
    /// the explicitly saved view; context never transports an action payload.
    fn forward_default(
        &mut self,
        body: TypedNodeOwner,
        view: &TypedBinder,
        api: RegionApi,
        span: Span,
    ) -> Result<TypedNode, TypeError> {
        if body.effects.tail().is_none()
            && !body
                .effects
                .known()
                .iter()
                .any(|instance| instance.effect() == api.default_alloc())
        {
            return Ok(body.into_inner());
        }
        let default = EffectInstance::new(api.default_alloc(), Box::new([]));
        let required = EffectRow::singleton(EffectInstance::new(api.default_alloc(), Box::new([])));
        let output = self.union_effects(&body.effects, &required, span)?;
        self.type_work.charge(16).map_err(|()| type_resource())?;
        let handler = HandlerId::new(self.next_handler);
        self.next_handler = self.next_handler.checked_add(1).ok_or_else(invalid_state)?;
        let mut clauses = Vec::new();
        clauses.try_reserve_exact(2).map_err(|_| type_resource())?;
        for ordinal in 0..2 {
            let input_type = if ordinal == 0 {
                Type::Nominal(api.request())
            } else {
                Type::Unit
            };
            let core_input_type = self.clone_type(&input_type)?;
            let input = self.builder.binder(core_input_type, Origin::Source(span))?;
            let view_value = self.builder.variable(
                view.id(),
                Type::Nominal(api.region_view()),
                Origin::Source(span),
            )?;
            let response = if ordinal == 0 {
                let request = self.builder.variable(
                    input.id(),
                    Type::Nominal(api.request()),
                    Origin::Source(span),
                )?;
                let core_required = self.core_effect_row(&required)?;
                self.push_effect_core(
                    Type::Nominal(api.storage_view()),
                    core_required,
                    Origin::Source(span),
                    EffectOperation::RegionAllocate(RegionAllocateNode {
                        api: api.module(),
                        context: view_value,
                        request,
                    }),
                )?
            } else {
                view_value
            };
            let owner = crate::resolved::ResumeId::new(
                handler
                    .value()
                    .checked_mul(2)
                    .and_then(|base| base.checked_add(ordinal))
                    .ok_or_else(invalid_state)?,
            );
            let resume_type = self.clone_type(&body.ty)?;
            let resume_effects = self.core_effect_row(&output)?;
            let resumed = self.push_effect_core(
                resume_type,
                resume_effects,
                Origin::Source(span),
                EffectOperation::Resume(ResumeNode::new(
                    handler,
                    owner,
                    ResumeUse::Consumed,
                    response,
                )),
            )?;
            clauses.push(EffectClause::new(
                crate::types::OperationId::new(api.default_alloc(), ordinal),
                owner,
                CoreMatchArm::new(
                    CorePattern::new(
                        input_type,
                        Origin::Source(span),
                        CorePatternKind::Binder(input),
                    ),
                    resumed,
                    Origin::Source(span),
                ),
            ));
        }
        let handler_type = self.clone_type(&body.ty)?;
        let handler_effects = self.core_effect_row(&output)?;
        let node = self.push_effect_core(
            handler_type,
            handler_effects,
            Origin::Source(span),
            EffectOperation::Handler(HandlerNode::new(handler, body.node, default, clauses)),
        )?;
        Ok(TypedNode {
            node,
            ty: self.clone_type(&body.ty)?,
            effects: output,
            provenance: self.at_span_provenance(&body.ty, span)?,
        })
    }

    fn provider_adapter(
        &mut self,
        callee: &TypedBinder,
        preceding: &TypedBinder,
        api: RegionApi,
        span: Span,
    ) -> Result<(NodeId, Type), TypeError> {
        let signature = IterativeTypeOwner::new(self.zonk(callee.ty())?);
        let function = signature.function_view().ok_or_else(invalid_state)?;
        let domain = self.clone_type(function.domain())?;
        let result = self.clone_type(function.value())?;
        let row = match function.effects() {
            Some(row) => clone_effect_row_with_budget(row, &mut self.type_work)
                .map_err(|()| type_resource())?,
            None => EffectRow::empty(),
        };
        let parameter_type = self.clone_type(&domain)?;
        let parameter = self.builder.binder(parameter_type, Origin::Source(span))?;
        let callee_type = self.clone_type(&signature)?;
        let function = self
            .builder
            .variable(callee.id(), callee_type, Origin::Source(span))?;
        let argument_type = self.clone_type(&domain)?;
        let argument =
            self.builder
                .variable(parameter.id(), argument_type, Origin::Source(span))?;
        let call_type = self.clone_type(&result)?;
        let call_effects = self.core_effect_row(&row)?;
        let call = F::push_application(
            &mut self.builder,
            ApplicationNode::new(function, argument),
            call_type,
            call_effects,
            Origin::Source(span),
        )?;
        let call = TypedNodeOwner::new(TypedNode {
            node: call,
            ty: result,
            effects: row,
            provenance: TypeProvenance::atom(Some(span)),
        });
        let body = TypedNodeOwner::new(self.forward_default(call, preceding, api, span)?);
        let result = self.clone_type(&body.ty)?;
        let row = clone_effect_row_with_budget(&body.effects, &mut self.type_work)
            .map_err(|()| type_resource())?;
        let signature =
            Type::function_computation(domain, crate::types::ComputationType::new(result, row));
        let core_type = self.clone_type(&signature)?;
        let node =
            self.construct_function(parameter, body.node, core_type, Origin::Source(span))?;
        Ok((node, signature))
    }

    /// The callback adapters use ordinary Core handlers over a bound preceding
    /// view, so invoking a member never performs ambient default selection.
    fn adapt_provider(
        &mut self,
        provider: &TypedNodeOwner,
        preceding: &TypedBinder,
        api: RegionApi,
        span: Span,
    ) -> Result<NodeId, TypeError> {
        let signature = IterativeTypeOwner::new(self.zonk(&provider.ty)?);
        let Type::Tuple(members) = &*signature else {
            return Err(invalid_state());
        };
        let [allocate, release] = members.as_ref() else {
            return Err(invalid_state());
        };
        let allocate_type = self.clone_type(allocate)?;
        let allocate = self.builder.binder(allocate_type, Origin::Source(span))?;
        let release_type = self.clone_type(release)?;
        let release = self.builder.binder(release_type, Origin::Source(span))?;
        let (allocate_node, allocate_signature) =
            self.provider_adapter(&allocate, preceding, api, span)?;
        let (release_node, release_signature) =
            self.provider_adapter(&release, preceding, api, span)?;
        let pair_type = IterativeTypeOwner::new(Type::Tuple(Box::new([
            allocate_signature,
            release_signature,
        ])));
        let core_type = self.clone_type(&pair_type)?;
        let pair = self.builder.tuple(
            vec![allocate_node, release_node],
            core_type,
            Origin::Source(span),
        )?;
        let allocate_type = self.clone_type(allocate.ty())?;
        let release_type = self.clone_type(release.ty())?;
        let pattern_type = self.clone_type(&signature)?;
        let pattern = CorePattern::new(
            pattern_type,
            Origin::Source(span),
            CorePatternKind::Tuple(
                vec![
                    CorePattern::new(
                        allocate_type,
                        Origin::Source(span),
                        CorePatternKind::Binder(allocate),
                    ),
                    CorePattern::new(
                        release_type,
                        Origin::Source(span),
                        CorePatternKind::Binder(release),
                    ),
                ]
                .into_boxed_slice(),
            ),
        );
        let core_type = self.clone_type(&pair_type)?;
        self.builder
            .match_expression(
                provider.node,
                vec![CoreMatchArm::new(pattern, pair, Origin::Source(span))],
                core_type,
                Origin::Source(span),
            )
            .map_err(TypeError::from)
    }

    pub(super) fn finish_region(
        &mut self,
        progress: RegionProgress<'_>,
        context: &mut TypeContext,
        values: &mut TypedNodeBuffer,
    ) -> Result<(), TypeError> {
        let body = values.pop().ok_or_else(invalid_state)?;
        let api = self.region_api_at(progress.span)?;
        let body = TypedNodeOwner::new(self.forward_default(
            body,
            &progress.access,
            api,
            progress.span,
        )?);
        context.remove_and_discard(progress.source.handle.id);
        let default = EffectInstance::new(api.default_alloc(), Box::new([]));
        let outward = self.remove_cleanup_effect(&body.effects, &default, progress.span, true)?;
        let rows = self.union_effects(&outward, &progress.provider_rows, progress.span)?;
        let rows = self.union_effects(&rows, &progress.provider.effects, progress.span)?;
        let unit = self
            .builder
            .unit(Type::Unit, Origin::Source(progress.span))?;
        let preceding_row =
            EffectRow::singleton(EffectInstance::new(api.default_alloc(), Box::new([])));
        let preceding_effects = self.core_effect_row(&preceding_row)?;
        let preceding = self.push_effect_core(
            Type::Nominal(api.region_view()),
            preceding_effects,
            Origin::Source(progress.span),
            EffectOperation::Request(RequestNode::new(
                EffectInstance::new(api.default_alloc(), Box::new([])),
                crate::types::OperationId::new(api.default_alloc(), 1),
                unit,
            )),
        )?;
        let mut scope_rows = clone_effect_row_with_budget(&rows, &mut self.type_work)
            .map_err(|()| type_resource())?;
        let rows = self.union_effects(&rows, &preceding_row, progress.span)?;
        let preceding_binder = self.builder.binder(
            Type::Nominal(api.region_view()),
            Origin::Source(progress.span),
        )?;
        let preceding_value = self.builder.variable(
            preceding_binder.id(),
            Type::Nominal(api.region_view()),
            Origin::Source(progress.span),
        )?;
        let provider =
            self.adapt_provider(&progress.provider, &preceding_binder, api, progress.span)?;
        let adapter_effects = self
            .builder
            .clone_node_effects_with_budget(provider, &mut self.type_work)?;
        scope_rows = self.union_effects(&scope_rows, &adapter_effects, progress.span)?;
        let rows = self.union_effects(&rows, &adapter_effects, progress.span)?;
        let owner_type = self.clone_type(&body.ty)?;
        let owner_effects = self.core_effect_row(&scope_rows)?;
        let node = self.push_effect_core(
            owner_type,
            owner_effects,
            Origin::Source(progress.span),
            EffectOperation::Region(Box::new(RegionScopeNode {
                entry: false,
                api: api.module(),
                identity: progress.source.identity.id,
                access: progress.access,
                preceding: preceding_value,
                provider,
                body: body.node,
            })),
        )?;
        let result_type = self.clone_type(&body.ty)?;
        let node = self.builder.binding(
            preceding_binder,
            preceding,
            node,
            result_type,
            Origin::Source(progress.span),
        )?;
        values.push(TypedNode {
            node,
            ty: self.clone_type(&body.ty)?,
            effects: rows,
            provenance: self.at_span_provenance(&body.ty, progress.span)?,
        });
        Ok(())
    }

    pub(super) fn schedule_selection<'a>(
        &mut self,
        source: &'a ResolvedRegionSelectionExpr,
        span: Span,
        tasks: &mut ElaborationTaskBuffer<'a>,
    ) -> Result<(), TypeError> {
        self.type_work.charge(2).map_err(|()| type_resource())?;
        tasks.0.try_reserve(2).map_err(|_| type_resource())?;
        tasks.push(ElaborationTask::SelectionBody { source, span });
        tasks.push(ElaborationTask::Synthesize {
            expression: &source.region,
            cause: None,
        });
        Ok(())
    }

    pub(super) fn selection_body<'a>(
        &mut self,
        source: &'a ResolvedRegionSelectionExpr,
        span: Span,
        tasks: &mut ElaborationTaskBuffer<'a>,
        values: &mut TypedNodeBuffer,
    ) -> Result<(), TypeError> {
        let operand = values.pop().ok_or_else(invalid_state)?;
        let api = self.region_api_at(span)?;
        self.refine_pattern_expected(
            &operand.ty,
            &Type::Nominal(api.region_view()),
            source.region.span,
        )?;
        let selected = self.builder.binder(
            Type::Nominal(api.region_view()),
            Origin::Source(source.region.span),
        )?;
        self.type_work.charge(2).map_err(|()| type_resource())?;
        tasks.0.try_reserve(2).map_err(|_| type_resource())?;
        tasks.push(ElaborationTask::FinishSelection(Box::new(
            SelectionProgress {
                span,
                operand,
                selected,
            },
        )));
        tasks.push(ElaborationTask::Synthesize {
            expression: &source.body,
            cause: None,
        });
        Ok(())
    }

    pub(super) fn finish_selection(
        &mut self,
        progress: SelectionProgress,
        values: &mut TypedNodeBuffer,
    ) -> Result<(), TypeError> {
        let body = values.pop().ok_or_else(invalid_state)?;
        let api = self.region_api_at(progress.span)?;
        let body = TypedNodeOwner::new(self.forward_default(
            body,
            &progress.selected,
            api,
            progress.span,
        )?);
        let effects =
            self.union_effects(&progress.operand.effects, &body.effects, progress.span)?;
        let binding_type = self.clone_type(&body.ty)?;
        let node = self.builder.binding(
            progress.selected,
            progress.operand.node,
            body.node,
            binding_type,
            Origin::Source(progress.span),
        )?;
        values.push(TypedNode {
            node,
            ty: self.clone_type(&body.ty)?,
            effects,
            provenance: self.at_span_provenance(&body.ty, progress.span)?,
        });
        Ok(())
    }
}
