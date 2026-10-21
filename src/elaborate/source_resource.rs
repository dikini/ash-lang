//! Original product resource compilation. Immutable checked programs are
//! compiled once; instance specialization only copies their typed forests.

use std::{collections::HashMap, sync::Arc};

use super::{
    BorrowedOwnerArgument, CheckKind, CheckedPattern, CoreElaborator, CoreLoweringFamily,
    CorePatternBuffer, CorePatternMatrixBuffer, CorePatternOwner, ElaborationTask,
    ElaborationTaskBuffer, OwnerReplacementBuffer, ProvenancedType, TypeContext, TypeError,
    TypeReason, TypedNode, TypedNodeOwner, constraint_resource, inference_failure, invalid_state,
    provider, provider_instance, type_resource, unsupported_provider_resource,
};
use crate::{
    core::{
        CoreBuilder, CoreMatchArm, EffectClause, EffectOperation, HandlerNode, NodeId, TypedBinder,
        dialect::MethodEvidenceCatalog,
        effect::{EffectOperationFamily, clone_effect_instance_with_budget},
        source_resource::{
            CheckedSourceResourceHeader, CheckedSourceResourceTemplate,
            CheckedSourceResourceTemplates,
        },
    },
    interface::InterfaceConstraintBudget,
    pattern::{UsefulnessBudget, missing_witness_for_types_with_budget},
    resolved::{
        BinderId, ResolvedBlock, ResolvedDefinitionKind, ResolvedExpr, ResolvedExprKind,
        ResolvedLocalDeclaration, ResolvedModule, ResolvedPattern, ResolvedRegistry,
        ResolvedSourceResourceDefinition, SharedCheckedInterfaceFact, SourceResourceTypeFact,
    },
    source::{GeneratedReason, Origin, Span},
    types::{
        ComputationType, EffectInstance, EffectRow, IterativeTypeOwner, Kind, KindedArgument, Type,
        TypeVariableId, TypeWorkBudget, clone_effect_row_with_budget, clone_kind_with_budget,
        clone_kinded_type_parameters_with_budget,
    },
};

struct SourceArguments(Vec<KindedArgument>);
impl SourceArguments {
    fn into_boxed_slice(mut self) -> Box<[KindedArgument]> {
        std::mem::take(&mut self.0).into_boxed_slice()
    }
}
impl Drop for SourceArguments {
    fn drop(&mut self) {
        for argument in self.0.drain(..) {
            crate::types::discard_kinded_argument_iteratively(argument);
        }
    }
}

pub(super) struct SourceResourceProgress<'a> {
    resource: &'a crate::resolved::ResolvedProviderResourceExpr,
    span: Span,
    initializer: TypedNodeOwner,
    handle: Option<TypedBinder>,
    template: Arc<CheckedSourceResourceTemplate>,
    arguments: SourceArguments,
    replacements: OwnerReplacementBuffer,
    forwarding: provider_instance::ProviderForwardings,
    members: Vec<(TypedBinder, NodeId)>,
    previous: Option<usize>,
}

pub(super) struct DeferredSourceResourceInstance {
    scope: NodeId,
    body: NodeId,
    answer: IterativeTypeOwner,
    body_effects: EffectRow,
    template: Arc<CheckedSourceResourceTemplate>,
    arguments: SourceArguments,
    rows: crate::core::provider::DeferredProviderHandlerRows,
    copies: [provider_instance::PreparedPhaseCopy; 3],
    provided: EffectInstance,
    marker: Option<crate::evidence::PendingObligationMarker>,
}
impl std::fmt::Debug for DeferredSourceResourceInstance {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("DeferredSourceResourceInstance")
            .field("scope", &self.scope)
            .field("body", &self.body)
            .finish_non_exhaustive()
    }
}

pub(super) struct PreparedSourceResource<'a> {
    pub(super) resource: &'a crate::resolved::ResolvedProviderResourceExpr,
    span: Span,
    template: Arc<CheckedSourceResourceTemplate>,
    arguments: SourceArguments,
    replacements: OwnerReplacementBuffer,
}

impl<F: CoreLoweringFamily> CoreElaborator<F> {
    fn source_template(
        &mut self,
        resource: &crate::resolved::ResolvedProviderResourceExpr,
    ) -> Result<Arc<CheckedSourceResourceTemplate>, TypeError> {
        if !F::EFFECTS {
            return Err(unsupported_provider_resource());
        }
        let fact = self
            .registry
            .source_resource_fact(resource.definition)
            .ok_or_else(invalid_state)?;
        let code = self
            .provider_codes
            .source_code(resource.definition.module(), &mut self.type_work)?
            .ok_or_else(invalid_state)?;
        for (index, header) in code.headers().enumerate() {
            self.type_work.charge(1).map_err(|_| type_resource())?;
            if header.original.id == resource.definition {
                if !Arc::ptr_eq(&header.original, fact) || header.original.family != resource.family
                {
                    return Err(invalid_state());
                }
                return code
                    .resource(index)
                    .map(Arc::clone)
                    .ok_or_else(invalid_state);
            }
        }
        Err(invalid_state())
    }

    fn source_actuals(
        &mut self,
        resource: &crate::resolved::ResolvedProviderResourceExpr,
        header: &SourceResourceTypeFact,
    ) -> Result<(SourceArguments, OwnerReplacementBuffer), TypeError> {
        let remaining = resource.arguments.as_ref().ok_or_else(invalid_state)?;
        if remaining.len().checked_add(1) != Some(header.parameters.len()) {
            return Err(invalid_state());
        }
        self.type_work
            .charge(header.parameters.len())
            .map_err(|_| type_resource())?;
        let mut arguments = SourceArguments(Vec::new());
        arguments
            .0
            .try_reserve_exact(header.parameters.len())
            .map_err(|_| type_resource())?;
        let mut replacements = OwnerReplacementBuffer::new();
        let mut written = remaining.iter();
        for (position, formal) in header.parameters.iter().enumerate() {
            let argument = if position == header.owned_position {
                if formal.kind != Kind::Type {
                    return Err(invalid_state());
                }
                KindedArgument::TypeArg(Type::Variable(resource.identity.id))
            } else {
                let written = &written.next().ok_or_else(invalid_state)?.ty;
                let qualified =
                    crate::types::qualify_kinded_argument_with_expected_row_with_budget(
                        written,
                        self.expected_effect_rows.last(),
                        &mut self.type_work,
                    )
                    .map_err(|()| type_resource())?
                    .map_err(|_| invalid_state())?
                    .map(crate::types::IterativeArgumentOwner::new);
                if let Some(qualified) = qualified {
                    qualified.into_inner()
                } else {
                    crate::types::clone_kinded_argument_with_budget(written, &mut self.type_work)
                        .map_err(|()| type_resource())?
                }
            };
            let argument = crate::types::IterativeArgumentOwner::new(argument);
            if matches!(
                (&formal.kind, &*argument),
                (Kind::EffectRow, KindedArgument::TypeArg(_))
            ) || !matches!(&formal.kind, Kind::EffectRow)
                && matches!(&*argument, KindedArgument::RowArg(_))
            {
                return Err(invalid_state());
            }
            replacements.insert_cloned(formal.id, &argument, &mut self.type_work)?;
            arguments.0.push(argument.into_inner());
        }
        Ok((arguments, replacements))
    }

    pub(super) fn schedule_source_resource_instance<'a>(
        &mut self,
        resource: &'a crate::resolved::ResolvedProviderResourceExpr,
        span: Span,
        tasks: &mut ElaborationTaskBuffer<'a>,
    ) -> Result<(), TypeError> {
        let template = self.source_template(resource)?;
        let (arguments, replacements) =
            self.source_actuals(resource, &template.header().original)?;
        let input = IterativeTypeOwner::new(
            replacements.substitute(&template.header().original.input.ty, &mut self.type_work)?,
        );
        let provenance = self.at_span_provenance(&input, resource.initializer.span)?;
        self.type_work.charge(3).map_err(|_| type_resource())?;
        tasks.0.try_reserve(2).map_err(|_| type_resource())?;
        tasks.push(ElaborationTask::SourceResourceBody(Box::new(
            PreparedSourceResource {
                resource,
                span,
                template,
                arguments,
                replacements,
            },
        )));
        tasks.push(ElaborationTask::Check {
            expression: &resource.initializer,
            expected: ProvenancedType {
                ty: input.into_inner(),
                provenance,
            },
            kind: CheckKind::General,
        });
        Ok(())
    }

    fn prepare_source_forwardings(
        &mut self,
        resource: &crate::resolved::ResolvedProviderResourceExpr,
        template: &CheckedSourceResourceTemplate,
        replacements: &OwnerReplacementBuffer,
    ) -> Result<provider_instance::ProviderForwardings, TypeError> {
        let header = &template.header().original;
        let mut arguments = SourceArguments(Vec::new());
        self.type_work
            .charge(header.provider.arguments.len())
            .map_err(|_| type_resource())?;
        arguments
            .0
            .try_reserve_exact(header.provider.arguments.len())
            .map_err(|_| type_resource())?;
        for argument in &header.provider.arguments {
            arguments.0.push(
                crate::types::substitute_kinded_argument_with(
                    &argument.ty,
                    replacements.types.as_map(),
                    &replacements.rows,
                    |cells| self.type_work.charge(cells),
                )
                .map_err(|_| type_resource())?
                .map_err(|_| invalid_state())?,
            );
        }
        let application = crate::interface::InterfaceApplication::new_kinded(
            header.provider.interface.id,
            arguments.into_boxed_slice(),
        );
        let row = replacements.substitute_row(
            &EffectRow::singleton(
                clone_effect_instance_with_budget(&header.provided.instance, &mut self.type_work)
                    .map_err(|_| type_resource())?,
            ),
            &mut self.type_work,
        )?;
        if row.tail().is_some()
            || row.known().len() != 1
            || template.methods().len() != resource.forwarding.len()
        {
            return Err(invalid_state());
        }
        let effect = clone_effect_instance_with_budget(&row.known()[0], &mut self.type_work)
            .map_err(|_| type_resource())?;
        self.type_work
            .charge(template.methods().len())
            .map_err(|_| type_resource())?;
        let mut methods = Vec::new();
        methods
            .try_reserve_exact(template.methods().len())
            .map_err(|_| type_resource())?;
        for ((method, operation), source) in template.methods().iter().zip(&resource.forwarding) {
            if *method != source.method || operation.owner() != effect.effect() {
                return Err(invalid_state());
            }
            let (domain, value) =
                self.operation_signature(&effect, *operation, resource.origin.primary_span())?;
            let domain = IterativeTypeOwner::new(domain);
            let value = IterativeTypeOwner::new(value);
            let effects = EffectRow::singleton(
                clone_effect_instance_with_budget(&effect, &mut self.type_work)
                    .map_err(|_| type_resource())?,
            );
            methods.push(provider_instance::ProviderForwarding {
                method: *method,
                operation: *operation,
                binder: source.binder.id,
                ty: IterativeTypeOwner::new(Type::function_computation(
                    domain.into_inner(),
                    ComputationType::new(value.into_inner(), effects),
                )),
            });
        }
        Ok(provider_instance::ProviderForwardings {
            application,
            effect,
            methods,
        })
    }

    pub(super) fn enter_source_resource_body<'a>(
        &mut self,
        prepared: PreparedSourceResource<'a>,
        initializer: TypedNodeOwner,
        context: &mut TypeContext,
    ) -> Result<SourceResourceProgress<'a>, TypeError> {
        let PreparedSourceResource {
            resource,
            span,
            template,
            arguments,
            replacements,
        } = prepared;
        let access = IterativeTypeOwner::new(
            template
                .header()
                .access_type(&arguments.0, &mut self.type_work)
                .map_err(validation)?,
        );
        let forwarding = self.prepare_source_forwardings(resource, &template, &replacements)?;
        let members = self.lower_resource_forwardings(resource, &forwarding)?;
        let (handle, previous) =
            self.enter_resource_forwarding_body(resource, access, &forwarding, context)?;
        Ok(SourceResourceProgress {
            resource,
            span,
            initializer,
            handle: Some(handle),
            forwarding,
            members,
            previous,
            template,
            arguments,
            replacements,
        })
    }

    pub(super) fn finish_source_resource_instance(
        &mut self,
        mut progress: SourceResourceProgress<'_>,
        body: TypedNodeOwner,
        context: &mut TypeContext,
    ) -> Result<TypedNode, TypeError> {
        self.leave_provider_instance_body(progress.resource, progress.previous, context)?;
        let header = &progress.template.header().original;
        let mut associated = SourceArguments(Vec::new());
        self.type_work
            .charge(header.provided.instance.arguments().len())
            .map_err(|_| type_resource())?;
        associated
            .0
            .try_reserve_exact(header.provided.instance.arguments().len())
            .map_err(|_| type_resource())?;
        for argument in header.provided.instance.arguments() {
            associated.0.push(
                crate::types::substitute_kinded_argument_with(
                    argument,
                    progress.replacements.types.as_map(),
                    &progress.replacements.rows,
                    |cells| self.type_work.charge(cells),
                )
                .map_err(|_| type_resource())?
                .map_err(|_| invalid_state())?,
            );
        }
        let provided = EffectInstance::new_kinded(
            header.provided.instance.effect(),
            associated.into_boxed_slice(),
        );
        let body_row = self.zonk_effect_row(&body.effects)?;
        let client_residual =
            self.remove_cleanup_effect(&body_row, &provided, progress.span, true)?;
        let deferred = if progress.template.has_conditional_handler_rows() {
            let count = progress
                .template
                .handler_row_count(&mut self.type_work)
                .map_err(validation)?;
            let mut fresh = Vec::new();
            self.type_work.charge(count).map_err(|_| type_resource())?;
            fresh
                .try_reserve_exact(count)
                .map_err(|_| type_resource())?;
            for _ in 0..count {
                fresh.push(self.defer_provider_row(progress.span)?);
            }
            let mut fresh = fresh.into_iter();
            Some(
                progress
                    .template
                    .defer_handler_rows(|| fresh.next(), &mut self.type_work)
                    .map_err(validation)?,
            )
        } else {
            None
        };
        let residual = if let Some(deferred) = &deferred {
            clone_effect_row_with_budget(deferred.output(), &mut self.type_work)
                .map_err(|_| type_resource())?
        } else {
            let direct = progress
                .template
                .handler_direct_row(&mut self.type_work)
                .map_err(validation)?;
            let direct = progress
                .replacements
                .substitute_row(&direct, &mut self.type_work)?;
            self.union_effects(&client_residual, &direct, progress.span)?
        };

        self.zonk_builder_types_since(None, false)
            .map_err(TypeError::Internal)?;
        let body_type = IterativeTypeOwner::new(self.zonk(&body.ty)?);
        progress.replacements.insert_borrowed(
            header.answer.id,
            BorrowedOwnerArgument::TypeArg(&body_type),
            &mut self.type_work,
        )?;
        let report = IterativeTypeOwner::new(
            progress
                .replacements
                .substitute(&header.result.ty, &mut self.type_work)?,
        );
        let mut outward_handler = clone_effect_row_with_budget(&residual, &mut self.type_work)
            .map_err(|_| type_resource())?;
        for interpretation in &header.interpreted {
            let interpreted = progress.replacements.substitute_row(
                &EffectRow::singleton(
                    clone_effect_instance_with_budget(
                        &interpretation.instance,
                        &mut self.type_work,
                    )
                    .map_err(|_| type_resource())?,
                ),
                &mut self.type_work,
            )?;
            outward_handler = self.provider_native_phase_row(
                &outward_handler,
                interpreted.known().first().ok_or_else(invalid_state)?,
                progress.span,
            )?;
        }
        let mut effects = self.union_effects(
            &progress.initializer.effects,
            &outward_handler,
            progress.span,
        )?;
        for acquire in [true, false] {
            let original = progress
                .template
                .lifecycle_row(acquire, &mut self.type_work)
                .map_err(validation)?;
            let mut outward = progress
                .replacements
                .substitute_row(&original, &mut self.type_work)?;
            for interpretation in &header.interpreted {
                let original = clone_effect_instance_with_budget(
                    &interpretation.instance,
                    &mut self.type_work,
                )
                .map_err(|_| type_resource())?;
                let interpreted = progress
                    .replacements
                    .substitute_row(&EffectRow::singleton(original), &mut self.type_work)?;
                let effect = interpreted.known().first().ok_or_else(invalid_state)?;
                outward = self.provider_native_phase_row(&outward, effect, progress.span)?;
            }
            effects = self.union_effects(&effects, &outward, progress.span)?;
        }
        self.check_provider_instance_escape(
            progress.resource,
            &report,
            &effects,
            context,
            progress.span,
        )?;
        let output = ComputationType::new(
            self.clone_type(&body_type)?,
            clone_effect_row_with_budget(&residual, &mut self.type_work)
                .map_err(|_| type_resource())?,
        );
        let empty_pending = HashMap::new();
        let empty_nodes = HashMap::new();
        let phases = self.prepare_source_resource_copies(
            &progress.template,
            &progress.arguments.0,
            &output,
            provider_instance::copy::ProviderScopeCopyRows {
                residual: deferred
                    .as_ref()
                    .map_or(&client_residual, |rows| rows.residual()),
                pending: deferred
                    .as_ref()
                    .map_or(&empty_pending, |rows| rows.pending()),
                nodes: deferred
                    .as_ref()
                    .map_or(&empty_nodes, |rows| rows.node_rows()),
            },
            progress
                .resource
                .identity
                .id
                .module()
                .unwrap_or(progress.resource.definition.module()),
            progress.span,
        )?;
        let mut body_node = body.node;
        while let Some((binder, function)) = progress.members.pop() {
            let binder_id = binder.id();
            let ty = self.clone_type(&body_type)?;
            body_node = self.builder.binding(
                binder,
                function,
                body_node,
                ty,
                Origin::Source(progress.span),
            )?;
            if self.purpose == super::ElaborationPurpose::FinalSynthesis {
                self.type_work
                    .charge(progress.forwarding.methods.len())
                    .map_err(|_| type_resource())?;
                let method = progress
                    .forwarding
                    .methods
                    .iter()
                    .find(|method| method.binder == binder_id)
                    .ok_or_else(invalid_state)?;
                let application = progress
                    .forwarding
                    .application
                    .clone_with_budget(&mut self.type_work)
                    .map_err(|_| type_resource())?;
                self.builder.authenticate_method_evidence(
                    body_node,
                    None,
                    None,
                    method.method,
                    application,
                    crate::core::dialect::MethodEvidenceAnchorRole::LexicalOwner {
                        source: progress.resource.provider,
                        binder: binder_id,
                    },
                    None,
                )?;
            }
        }
        self.type_work
            .charge(progress.forwarding.methods.len())
            .map_err(|_| type_resource())?;
        let mut forwardings = Vec::new();
        forwardings
            .try_reserve_exact(progress.forwarding.methods.len())
            .map_err(|_| type_resource())?;
        for method in &progress.forwarding.methods {
            forwardings.push(crate::core::provider::ProviderForwardingMethod {
                method: method.method,
                binder: method.binder,
            });
        }
        let builder = F::effect_builder(&mut self.builder).ok_or_else(invalid_state)?;
        let copied = lower_source_copies(
            builder,
            &progress.template,
            &phases,
            body_node,
            &mut self.type_work,
        )?;
        let claims =
            std::array::from_fn(
                |index| crate::core::source_resource::SourceResourceCopyClaim {
                    nodes: &copied.forests[index].nodes,
                    freshening: phases[index].freshening(),
                    substitution: phases[index].substitution(),
                    node_rows: phases[index].node_rows(),
                },
            );
        let deferred_arguments = if deferred.is_some() {
            Some(SourceArguments(
                crate::types::clone_kinded_arguments_with_budget(
                    progress.arguments.0.iter(),
                    &mut self.type_work,
                )
                .map_err(|_| type_resource())?
                .into_vec(),
            ))
        } else {
            None
        };
        let handle = progress.handle.take().ok_or_else(invalid_state)?;
        let scope = crate::core::source_resource::SourceResourceScopeNode::new(
            Arc::clone(&progress.template),
            progress.arguments.into_boxed_slice(),
            progress.resource.identity.id,
            progress.initializer.node,
            copied.acquire,
            copied.finish,
            copied.state,
            copied.pattern.into_inner(),
            handle,
            copied.handler,
            output,
            progress.resource.provider,
            forwardings.into_boxed_slice(),
            claims,
            &mut self.type_work,
        )
        .map_err(validation)?;
        let core_type = self.clone_type(&report)?;
        let core_effects = self.core_effect_row(&effects)?;
        let provenance = self.at_span_provenance(&report, progress.span)?;
        let node = self
            .push_effect_core(
                core_type,
                core_effects,
                Origin::Source(progress.span),
                EffectOperation::SourceResourceScope(Box::new(scope)),
            )
            .map_err(TypeError::from)?;
        if let Some(rows) = deferred {
            self.type_work.charge(1).map_err(|_| type_resource())?;
            self.deferred_source_resources
                .try_reserve(1)
                .map_err(|_| type_resource())?;
            let marker = if self.purpose == super::ElaborationPurpose::ModuleCheck {
                Some(self.evidence_marker()?)
            } else {
                None
            };
            let answer = IterativeTypeOwner::new(self.clone_type(&body_type)?);
            self.deferred_source_resources
                .push(DeferredSourceResourceInstance {
                    scope: node,
                    body: body_node,
                    answer,
                    body_effects: body_row,
                    template: progress.template,
                    arguments: deferred_arguments.ok_or_else(invalid_state)?,
                    rows,
                    copies: phases,
                    provided,
                    marker,
                });
        }
        Ok(TypedNode {
            node,
            ty: report.into_inner(),
            effects,
            provenance,
        })
    }
    pub(super) fn complete_deferred_source_resources(
        &mut self,
        marker: Option<crate::evidence::PendingObligationMarker>,
        owner: NodeId,
    ) -> Result<(), TypeError> {
        if self.deferred_source_resources.is_empty() {
            return Ok(());
        }
        if matches!(self.purpose, super::ElaborationPurpose::ModuleCheck) != marker.is_some() {
            return Err(invalid_state());
        }
        let mut stack = Vec::new();
        let mut reachable = std::collections::HashSet::new();
        self.type_work.charge(1).map_err(|_| type_resource())?;
        stack.try_reserve(1).map_err(|_| type_resource())?;
        stack.push(owner);
        while let Some(node) = stack.pop() {
            self.type_work.charge(1).map_err(|_| type_resource())?;
            reachable.try_reserve(1).map_err(|_| type_resource())?;
            if !reachable.insert(node) {
                continue;
            }
            let kind = self.builder.compiler_node_kind(node)?;
            self.type_work
                .charge(F::child_count(kind))
                .map_err(|_| type_resource())?;
            stack
                .try_reserve(F::child_count(kind))
                .map_err(|_| type_resource())?;
            for ordinal in 0..F::child_count(kind) {
                stack.push(F::child_at(kind, ordinal).ok_or_else(invalid_state)?);
            }
        }
        let count = self.deferred_source_resources.len();
        self.type_work.charge(count).map_err(|_| type_resource())?;
        let mut retained = Vec::new();
        retained
            .try_reserve_exact(count)
            .map_err(|_| type_resource())?;
        let pending = std::mem::replace(&mut self.deferred_source_resources, retained);
        for instance in pending {
            let covered = match (marker, instance.marker) {
                (Some(owner), Some(child)) => owner.covers(child),
                (None, None) => true,
                _ => false,
            };
            if !covered || !reachable.contains(&instance.scope) {
                self.deferred_source_resources.push(instance);
                continue;
            }
            self.complete_deferred_source_resource(instance)?;
        }
        Ok(())
    }

    fn complete_deferred_source_resource(
        &mut self,
        instance: DeferredSourceResourceInstance,
    ) -> Result<(), TypeError> {
        self.complete_ready_provider_row_equations()?;
        self.zonk_builder_types_since(None, false)
            .map_err(TypeError::Internal)?;
        let answer = IterativeTypeOwner::new(self.zonk(&instance.answer)?);
        let body_row = self.zonk_effect_row(&instance.body_effects)?;
        let mut replacements = OwnerReplacementBuffer::new();
        for (formal, argument) in instance
            .template
            .header()
            .original
            .parameters
            .iter()
            .zip(&instance.arguments.0)
        {
            let argument =
                crate::types::IterativeArgumentOwner::new(self.zonk_owner_argument(argument)?);
            replacements.insert_cloned(formal.id, &argument, &mut self.type_work)?;
        }
        let completed = self.provider_completed_roots.as_deref().unwrap_or(&[]);
        self.type_work
            .charge(completed.len())
            .map_err(|_| type_resource())?;
        let mut roots = Vec::new();
        roots
            .try_reserve_exact(completed.len())
            .map_err(|_| type_resource())?;
        roots.extend_from_slice(completed);
        let (methods, adapters) = if self.purpose == super::ElaborationPurpose::ModuleCheck {
            self.capture_provider_actual_routes(instance.scope, &roots)?
        } else {
            (Vec::new(), Vec::new())
        };
        let provided = self.zonk_effect_row(&EffectRow::singleton(instance.provided))?;
        let imported = self.provider_imported_captures.as_deref().unwrap_or(&[]);
        self.type_work
            .charge(imported.len())
            .map_err(|_| type_resource())?;
        let mut imports = Vec::new();
        imports
            .try_reserve_exact(imported.len())
            .map_err(|_| type_resource())?;
        imports.extend(imported.iter().map(|(binder, summary)| (*binder, summary)));
        let actual = instance
            .template
            .prepare_instance_rows(
                &self.builder,
                instance.scope,
                &roots,
                &imports,
                &methods,
                &adapters,
                F::capture_operation,
                replacements.types.as_map(),
                &replacements.rows,
                &answer,
                &body_row,
                provided.known().first().ok_or_else(invalid_state)?,
                &mut self.type_work,
            )
            .map_err(validation)?;
        let completion = instance
            .rows
            .completion(&actual, &mut self.type_work)
            .map_err(validation)?;
        for (position, identity, row) in completion {
            use crate::core::provider::DeferredProviderRowPosition as Position;
            let row = match position {
                Position::Node(_) | Position::Pending(_) | Position::Handler(_) => instance.copies
                    [2]
                .context()
                .realized_row(row, &mut self.type_work)
                .map_err(|error| TypeError::Internal(error.into()))?,
                Position::Output | Position::Residual => {
                    clone_effect_row_with_budget(row, &mut self.type_work)
                        .map_err(|_| type_resource())?
                }
            };
            self.complete_provider_row(identity, row)?;
        }
        self.complete_ready_provider_row_equations()?;
        self.zonk_builder_types_since(None, false)
            .map_err(TypeError::Internal)?;
        F::effect_builder(&mut self.builder)
            .ok_or_else(invalid_state)?
            .with_caller_type_work(&mut self.type_work, |builder| {
                builder.retain_source_resource_rows(instance.scope, Arc::new(actual))
            })?;
        Ok(())
    }
}

struct SourceCopied {
    acquire: crate::core::source_resource::SourceResourceLifecycleEntry,
    finish: crate::core::source_resource::SourceResourceLifecycleEntry,
    state: TypedBinder,
    pattern: CorePatternOwner,
    handler: HandlerNode,
    forests: [crate::core::provider::ProviderCopiedForest; 3],
}

fn lower_source_copies(
    builder: &mut crate::core::EffectCoreBuilder,
    template: &CheckedSourceResourceTemplate,
    phases: &[provider_instance::PreparedPhaseCopy; 3],
    body: NodeId,
    work: &mut TypeWorkBudget,
) -> Result<SourceCopied, TypeError> {
    use crate::core::{provider::copy_prepared_provider_forest, transform};
    fn failure(error: transform::TransformError) -> TypeError {
        match error {
            transform::TransformError::Build(error) => error.into(),
            _ => invalid_state(),
        }
    }
    builder.with_caller_type_work(work, |builder| {
        let replacements = HashMap::new();
        let acquire = copy_prepared_provider_forest(
            builder,
            template.original_acquire(),
            &[template.acquire_entry().1],
            &replacements,
            &phases[0].context(),
        )
        .map_err(failure)?;
        let finish = copy_prepared_provider_forest(
            builder,
            template.original_finish(),
            &[template.finish_entry().1],
            &replacements,
            &phases[1].context(),
        )
        .map_err(failure)?;
        let original_handler = template.original_handler_node();
        builder.charge_rebuild_work(original_handler.clauses().len().saturating_mul(2))?;
        let mut roots = Vec::new();
        roots
            .try_reserve_exact(original_handler.clauses().len())
            .map_err(|_| type_resource())?;
        roots.extend(original_handler.clauses().iter().map(EffectClause::body));
        let handler = copy_prepared_provider_forest(
            builder,
            template.original_handler(),
            &roots,
            &replacements,
            &phases[2].context(),
        )
        .map_err(failure)?;
        let acquire_parameter = transform::rebuild_provider_fragment_binder_with_context(
            builder,
            template.acquire_entry().0,
            &phases[0].context(),
        )
        .map_err(failure)?;
        let finish_parameter = transform::rebuild_provider_fragment_binder_with_context(
            builder,
            template.finish_entry().0,
            &phases[1].context(),
        )
        .map_err(failure)?;
        let state = transform::rebuild_provider_fragment_binder_with_context(
            builder,
            template.handler_entry().0,
            &phases[2].context(),
        )
        .map_err(failure)?;
        let pattern = CorePatternOwner::new(Some(
            transform::rebuild_provider_fragment_pattern_with_context(
                builder,
                template.handler_pattern(),
                &phases[2].context(),
            )
            .map_err(failure)?,
        ));
        let context = phases[2].context();
        let mut clauses = Vec::new();
        clauses
            .try_reserve_exact(original_handler.clauses().len())
            .map_err(|_| type_resource())?;
        for (original, copied_body) in original_handler.clauses().iter().zip(&handler.roots) {
            let pattern = CorePatternOwner::new(Some(
                transform::rebuild_provider_fragment_pattern_with_context(
                    builder,
                    original.pattern(),
                    &context,
                )
                .map_err(failure)?,
            ));
            let origin = transform::rebuild_provider_fragment_origin(builder, original.origin())
                .map_err(failure)?;
            clauses.push(EffectClause::new(
                original.operation(),
                *context
                    .resumes
                    .get(&original.resume())
                    .ok_or_else(invalid_state)?,
                CoreMatchArm::new(pattern.into_inner(), *copied_body, origin),
            ));
        }
        let mut effect_arguments = SourceArguments(Vec::new());
        builder.charge_rebuild_work(original_handler.effect().arguments().len())?;
        effect_arguments
            .0
            .try_reserve_exact(original_handler.effect().arguments().len())
            .map_err(|_| type_resource())?;
        for argument in original_handler.effect().arguments() {
            effect_arguments
                .0
                .push(builder.with_rebuild_type_work(|work| context.argument(argument, work))?);
        }
        let effect = EffectInstance::new_kinded(
            original_handler.effect().effect(),
            effect_arguments.into_boxed_slice(),
        );
        let handler_node = HandlerNode::new(
            *context
                .handlers
                .get(&original_handler.id())
                .ok_or_else(invalid_state)?,
            body,
            effect,
            clauses,
        );
        Ok(SourceCopied {
            acquire: crate::core::source_resource::SourceResourceLifecycleEntry {
                parameter: acquire_parameter,
                body: *acquire.roots.first().ok_or_else(invalid_state)?,
            },
            finish: crate::core::source_resource::SourceResourceLifecycleEntry {
                parameter: finish_parameter,
                body: *finish.roots.first().ok_or_else(invalid_state)?,
            },
            state,
            pattern,
            handler: handler_node,
            forests: [acquire, finish, handler],
        })
    })
}

fn validation(error: crate::core::ValidationError) -> TypeError {
    match error.reason() {
        crate::core::ValidationReason::Resource => type_resource(),
        _ => invalid_state(),
    }
}

fn header_validation(error: crate::core::ValidationError, span: Span) -> TypeError {
    match error.reason() {
        crate::core::ValidationReason::Resource => type_resource(),
        _ => inference_failure(
            TypeReason::Argument,
            span,
            "source resource header requires matching owned state, lifecycle symbols, and scope codecs",
        ),
    }
}

fn template_validation(error: crate::core::ValidationError, span: Span) -> TypeError {
    match error.reason() {
        crate::core::ValidationReason::Resource => type_resource(),
        _ => inference_failure(
            TypeReason::Argument,
            span,
            "source resource lifecycle and handlers must preserve the admitted owner flow",
        ),
    }
}

enum SourceBinderNode<'a> {
    Definition(&'a ResolvedDefinitionKind),
    Equation(&'a crate::resolved::ResolvedEquation),
    Method(&'a crate::resolved::ResolvedImplementationMethodGroup),
    Declaration(&'a ResolvedLocalDeclaration),
    Block(&'a ResolvedBlock),
    Pattern(&'a crate::resolved::ResolvedPattern),
    Expression(&'a ResolvedExpr),
}

struct SourceBinderInventory<'a, 'work> {
    binders: Vec<BinderId>,
    pending: Vec<SourceBinderNode<'a>>,
    work: &'work mut TypeWorkBudget,
}

impl<'a> SourceBinderInventory<'a, '_> {
    fn push(
        &mut self,
        nodes: impl IntoIterator<Item = SourceBinderNode<'a>, IntoIter: ExactSizeIterator>,
    ) -> Result<(), TypeError> {
        let nodes = nodes.into_iter();
        self.work.charge(nodes.len()).map_err(|_| type_resource())?;
        self.pending
            .try_reserve(nodes.len())
            .map_err(|_| type_resource())?;
        self.pending.extend(nodes);
        Ok(())
    }

    fn binder(&mut self, id: BinderId) -> Result<(), TypeError> {
        self.work.charge(1).map_err(|_| type_resource())?;
        self.binders.try_reserve(1).map_err(|_| type_resource())?;
        self.binders.push(id);
        Ok(())
    }

    fn clauses(
        &mut self,
        clauses: &'a [crate::resolved::ResolvedHandlerClause],
    ) -> Result<(), TypeError> {
        for clause in clauses {
            self.push([
                SourceBinderNode::Pattern(&clause.pattern),
                SourceBinderNode::Expression(&clause.body),
            ])?;
        }
        Ok(())
    }

    fn finish(mut self) -> Result<Vec<BinderId>, TypeError> {
        use SourceBinderNode as Node;
        while let Some(node) = self.pending.pop() {
            self.work.charge(1).map_err(|_| type_resource())?;
            match node {
                Node::Definition(
                    ResolvedDefinitionKind::Equational(definition)
                    | ResolvedDefinitionKind::ForeignConstant(definition),
                ) => {
                    self.binder(definition.interface.name.id)?;
                    self.push(definition.equations.iter().map(Node::Equation))?;
                }
                Node::Definition(ResolvedDefinitionKind::InlineOperational(definition)) => {
                    self.binder(definition.header.name.id)?;
                    self.push(
                        definition
                            .header
                            .parameters
                            .iter()
                            .map(|parameter| Node::Pattern(&parameter.pattern)),
                    )?;
                    self.push([Node::Block(&definition.body)])?;
                }
                Node::Equation(equation) => {
                    self.push(equation.patterns.iter().map(Node::Pattern))?;
                    self.push([Node::Expression(&equation.body)])?;
                }
                Node::Method(method) => {
                    self.binder(method.binder.id)?;
                    self.push(method.equations.iter().map(Node::Equation))?;
                }
                Node::Declaration(ResolvedLocalDeclaration::Evidence(evidence)) => {
                    self.push(evidence.method_groups.iter().map(Node::Method))?;
                }
                Node::Declaration(ResolvedLocalDeclaration::Binding(binding)) => {
                    self.push([
                        Node::Pattern(&binding.pattern),
                        Node::Expression(&binding.initializer),
                    ])?;
                }
                Node::Declaration(ResolvedLocalDeclaration::Recursive(group)) => {
                    for member in &group.members {
                        self.binder(member.binder.id)?;
                        self.push([Node::Expression(&member.initializer)])?;
                    }
                }
                Node::Declaration(ResolvedLocalDeclaration::Newtype(_)) => {}
                Node::Block(block) => {
                    self.push(block.declarations.iter().map(Node::Declaration))?;
                    self.push([Node::Expression(&block.result)])?;
                }
                Node::Pattern(pattern) => match &pattern.kind {
                    crate::resolved::ResolvedPatternKind::Binder(binder) => {
                        self.binder(binder.id)?;
                    }
                    crate::resolved::ResolvedPatternKind::Tuple(elements) => {
                        self.push(elements.iter().map(Node::Pattern))?;
                    }
                    crate::resolved::ResolvedPatternKind::Constructor {
                        payload: Some(payload),
                        ..
                    } => self.push([Node::Pattern(payload)])?,
                    crate::resolved::ResolvedPatternKind::Constructor { payload: None, .. }
                    | crate::resolved::ResolvedPatternKind::Wildcard
                    | crate::resolved::ResolvedPatternKind::Boolean(_)
                    | crate::resolved::ResolvedPatternKind::Unit => {}
                },
                Node::Expression(expression) => match &expression.kind {
                    ResolvedExprKind::Apply(application) => self.push([
                        Node::Expression(&application.argument),
                        Node::Expression(&application.function),
                    ])?,
                    ResolvedExprKind::Add(binary)
                    | ResolvedExprKind::Multiply(binary)
                    | ResolvedExprKind::Equal(binary) => self.push([
                        Node::Expression(&binary.left),
                        Node::Expression(&binary.right),
                    ])?,
                    ResolvedExprKind::Block(block) => self.push([Node::Block(block)])?,
                    ResolvedExprKind::Function(function) => self.push([
                        Node::Pattern(&function.pattern),
                        Node::Block(&function.body),
                    ])?,
                    ResolvedExprKind::Tuple(elements) => {
                        self.push(elements.iter().map(Node::Expression))?;
                    }
                    ResolvedExprKind::Match(expression) => {
                        self.push([Node::Expression(&expression.scrutinee)])?;
                        for arm in &expression.arms {
                            self.push([Node::Pattern(&arm.pattern), Node::Expression(&arm.body)])?;
                        }
                    }
                    ResolvedExprKind::ForeignHost(host) => {
                        self.push([Node::Expression(&host.body)])?;
                    }
                    ResolvedExprKind::CopyWindow(window) => {
                        self.push([
                            Node::Expression(&window.state),
                            Node::Expression(&window.body),
                        ])?;
                    }
                    ResolvedExprKind::ProviderResource(resource) => {
                        for method in &resource.forwarding {
                            self.binder(method.binder.id)?;
                            self.binder(method.parameter.id)?;
                        }
                        self.binder(resource.handle.id)?;
                        self.push([
                            Node::Expression(&resource.body),
                            Node::Expression(&resource.initializer),
                        ])?;
                    }
                    ResolvedExprKind::Resource(resource) => {
                        self.binder(resource.handle.id)?;
                        self.push([
                            Node::Expression(&resource.body),
                            Node::Expression(&resource.initializer),
                        ])?;
                    }
                    ResolvedExprKind::Cleanup(cleanup) => self.push([
                        Node::Expression(&cleanup.body),
                        Node::Expression(&cleanup.action),
                    ])?,
                    ResolvedExprKind::Perform(request) => {
                        self.push([Node::Expression(&request.operand)])?;
                    }
                    ResolvedExprKind::Handle(handler) => {
                        self.push([Node::Expression(&handler.body)])?;
                        self.clauses(&handler.clauses)?;
                    }
                    ResolvedExprKind::Resume(resume) => {
                        self.push([Node::Expression(&resume.value)])?;
                    }
                    ResolvedExprKind::Discard(_)
                    | ResolvedExprKind::String(_)
                    | ResolvedExprKind::Integer(_)
                    | ResolvedExprKind::Boolean(_)
                    | ResolvedExprKind::Unit
                    | ResolvedExprKind::Occurrence(_)
                    | ResolvedExprKind::Constructor(_) => {}
                },
            }
        }
        Ok(self.binders)
    }
}

/// Scan source binder identities once. Each independently built template forest
/// reserves this immutable inventory before allocating any generated binders.
fn source_module_binders(
    module: &ResolvedModule,
    work: &mut TypeWorkBudget,
) -> Result<Vec<BinderId>, TypeError> {
    use SourceBinderNode as Node;
    let mut inventory = SourceBinderInventory {
        binders: Vec::new(),
        pending: Vec::new(),
        work,
    };
    for resource in module.resources() {
        inventory.work.charge(1).map_err(|_| type_resource())?;
        inventory.binder(resource.acquire_binder.id)?;
        inventory.binder(resource.finish_binder.id)?;
        inventory.binder(resource.handlers_binder.id)?;
        inventory.push([
            Node::Expression(&resource.acquire),
            Node::Expression(&resource.finish),
        ])?;
        inventory.clauses(&resource.handlers)?;
        if let Some(family) = &resource.family_template {
            inventory.binder(family.handlers_binder.id)?;
            inventory.clauses(&family.handlers)?;
        }
    }
    for resource in module.source_resources() {
        inventory.work.charge(1).map_err(|_| type_resource())?;
        inventory.push([
            Node::Pattern(&resource.acquire_pattern),
            Node::Pattern(&resource.finish_pattern),
            Node::Pattern(&resource.handlers_pattern),
            Node::Expression(&resource.acquire),
            Node::Expression(&resource.finish),
        ])?;
        inventory.clauses(&resource.handlers)?;
    }
    inventory.push(
        module
            .definitions()
            .iter()
            .map(|definition| Node::Definition(&definition.kind)),
    )?;
    for implementation in module.implementations() {
        inventory.work.charge(1).map_err(|_| type_resource())?;
        inventory.push(implementation.method_groups.iter().map(Node::Method))?;
    }
    inventory.finish()
}

/// Transfers the caller's cumulative meter into one ordinary effect checker.
/// Both successful and refused compilation return the consumed meter.
#[allow(clippy::too_many_arguments)]
pub(super) fn compile(
    module: &ResolvedModule,
    registry: &Arc<ResolvedRegistry>,
    interfaces: &[SharedCheckedInterfaceFact],
    schemes: &[crate::resolved::CheckedGlobalScheme],
    work: &mut TypeWorkBudget,
    coverage: &mut UsefulnessBudget,
    constraints: &mut InterfaceConstraintBudget,
    original_provider: Option<&provider::SourceOriginalProviderContext<'_>>,
    rewrite_work_limit: usize,
) -> Result<Option<Arc<CheckedSourceResourceTemplates>>, TypeError> {
    if module.source_resources().is_empty() {
        return Ok(None);
    }
    let binders = source_module_binders(module, work)?;
    let catalog = Arc::new(
        crate::evidence_validation::build_source_resource_method_evidence_catalog(
            module,
            interfaces,
            registry,
            constraints,
            work,
        )
        .map_err(|error| match error.reason() {
            crate::evidence_validation::EvidenceValidationReason::TypeResourceExhausted => {
                type_resource()
            }
            crate::evidence_validation::EvidenceValidationReason::ConstraintResourceExhausted => {
                constraint_resource()
            }
            _ => invalid_state(),
        })?,
    );
    let mut compiler = CoreElaborator::<EffectOperationFamily>::for_source_module_with_work(
        module,
        Arc::clone(registry),
        work,
        coverage.clone(),
        TypeWorkBudget::with_limit(rewrite_work_limit),
    )?;
    let result = (|| {
        // These original declaration headers were checked by the caller.
        // Their bodies still cross the ordinary callable barrier separately.
        // No unused Core binders are allocated just to seed this type context.
        // Refusal stays inside the transaction that returns the consumed meter.
        for scheme in schemes {
            compiler.type_work.charge(1).map_err(|_| type_resource())?;
            let parameters = clone_kinded_type_parameters_with_budget(
                &scheme.scheme.type_parameters,
                &mut compiler.type_work,
            )
            .map_err(|_| type_resource())?
            .into_boxed_slice();
            let body = IterativeTypeOwner::new(
                crate::types::clone_type_with_budget(
                    &scheme.scheme.value_type,
                    &mut compiler.type_work,
                )
                .map_err(|_| type_resource())?,
            );
            let provenance = super::at_span_provenance_with_budget(
                &body,
                scheme.origin.primary_span(),
                &mut compiler.type_work,
            )
            .map_err(|_| type_resource())?;
            if compiler.base_context.insert_with_provenance(
                scheme.binder,
                body.into_inner(),
                provenance,
            )? {
                return Err(invalid_state());
            }
            compiler
                .base_context
                .set_quantified(scheme.binder, parameters)?;
        }
        let globals = Arc::new(compiler.source_global_schemes(module)?);
        compiler
            .type_work
            .charge(
                module
                    .defining_sources()
                    .len()
                    .saturating_mul(2)
                    .saturating_add(module.source_resources().len()),
            )
            .map_err(|_| type_resource())?;
        let mut sources = Vec::new();
        let mut module_sources = Vec::new();
        let mut records = Vec::new();
        sources
            .try_reserve_exact(module.defining_sources().len())
            .map_err(|_| type_resource())?;
        module_sources
            .try_reserve_exact(module.defining_sources().len())
            .map_err(|_| type_resource())?;
        records
            .try_reserve_exact(module.source_resources().len())
            .map_err(|_| type_resource())?;
        for (owner, source) in module.defining_sources() {
            sources.push(source.as_ref());
            module_sources.push((*owner, source.id()));
        }
        for definition in module.source_resources() {
            let header = Arc::new(
                CheckedSourceResourceHeader::admit(
                    &definition.header,
                    registry,
                    &mut compiler.type_work,
                )
                .map_err(|error| header_validation(error, definition.span))?,
            );
            let acquire = compiler.compile_source_lifecycle(
                &binders,
                &catalog,
                definition,
                &header,
                provider::Phase::Acquire,
            )?;
            let finish = compiler.compile_source_lifecycle(
                &binders,
                &catalog,
                definition,
                &header,
                provider::Phase::Finish,
            )?;
            let (handler, handler_inputs) =
                compiler.compile_source_handler(&binders, &catalog, definition, &header)?;
            records.push(Arc::new(
                CheckedSourceResourceTemplate::admit_with_globals(
                    header,
                    acquire,
                    finish,
                    handler,
                    handler_inputs,
                    Arc::clone(&globals),
                    &sources,
                    &module_sources,
                    &mut compiler.type_work,
                    &mut crate::core::validate::SourceResourceStructureSession::with_original_provider(original_provider),
                )
                .map_err(|error| template_validation(error, definition.span))?,
            ));
        }
        CheckedSourceResourceTemplates::new(records, &mut compiler.type_work)
            .map(Arc::new)
            .map(Some)
            .map_err(validation)
    })();
    *work = std::mem::take(&mut compiler.type_work);
    *coverage = std::mem::take(&mut compiler.coverage_work);
    result
}

impl CoreElaborator<EffectOperationFamily> {
    fn for_source_module_with_work(
        module: &ResolvedModule,
        registry: Arc<ResolvedRegistry>,
        work: &mut TypeWorkBudget,
        coverage: UsefulnessBudget,
        rewrite_work: TypeWorkBudget,
    ) -> Result<Self, TypeError> {
        let builder =
            CoreBuilder::with_registry_and_rewrite_work(Arc::clone(&registry), rewrite_work);
        Self::for_module_with_prepared_builder(module, registry, work, coverage, builder)
    }

    fn source_global_schemes(
        &mut self,
        module: &ResolvedModule,
    ) -> Result<crate::core::source_resource::SourceResourceGlobals, TypeError> {
        let mut globals = crate::core::source_resource::SourceResourceGlobals::new();
        for binder in module
            .imported_facts()
            .globals()
            .map(|fact| fact.binder)
            .chain(
                module
                    .definitions()
                    .iter()
                    .map(|definition| match &definition.kind {
                        ResolvedDefinitionKind::Equational(definition)
                        | ResolvedDefinitionKind::ForeignConstant(definition) => {
                            definition.interface.name.id
                        }
                        ResolvedDefinitionKind::InlineOperational(definition) => {
                            definition.header.name.id
                        }
                    }),
            )
        {
            self.type_work.charge(1).map_err(|_| type_resource())?;
            if self.registry.scalar_preflight(binder).is_some() {
                continue;
            }
            let fact = self.base_context.fact(binder).ok_or_else(invalid_state)?;
            let ty = IterativeTypeOwner::new(
                crate::types::clone_type_with_budget(&fact.ty, &mut self.type_work)
                    .map_err(|_| type_resource())?,
            );
            let parameters =
                clone_kinded_type_parameters_with_budget(&fact.quantified, &mut self.type_work)
                    .map_err(|_| type_resource())?;
            let mut ty = IterativeTypeOwner::new(self.pure_core_type(&ty)?);
            if !parameters.is_empty() {
                self.type_work.charge(1).map_err(|_| type_resource())?;
                ty = IterativeTypeOwner::new(Type::Forall(
                    parameters.into_boxed_slice(),
                    Box::new(ty.into_inner()),
                ));
            }
            globals.try_reserve(1).map_err(|_| type_resource())?;
            if globals.insert(binder, ty).is_some() {
                return Err(invalid_state());
            }
        }
        Ok(globals)
    }

    fn begin_source_program(
        &mut self,
        binders: &[BinderId],
        catalog: &Arc<MethodEvidenceCatalog>,
    ) -> Result<(), TypeError> {
        // Source association supplies method declarations only. The constructor
        // has no expectation work; each forest's work ledger is installed below.
        if catalog.occurrence_count() != 0
            || catalog.implementation_owner_count() != 0
            || !catalog.expectations().is_empty()
        {
            return Err(invalid_state());
        }
        self.builder = CoreBuilder::with_registry_method_evidence_and_rewrite_work(
            Arc::clone(&self.registry),
            Arc::clone(catalog),
            TypeWorkBudget::with_limit(self.builder.rewrite_work_limit()),
        )?;
        self.builder
            .reserve_provider_draft_binders(binders, &mut self.type_work)?;
        crate::core::transform::begin_provider_draft_work(
            &mut self.builder,
            self.type_work.remaining(),
        );
        Ok(())
    }

    fn source_parameters(
        &mut self,
        header: &SourceResourceTypeFact,
        answer: bool,
    ) -> Result<Vec<(TypeVariableId, Kind)>, TypeError> {
        let count = header
            .parameters
            .len()
            .checked_add(usize::from(answer))
            .ok_or_else(type_resource)?;
        self.type_work.charge(count).map_err(|_| type_resource())?;
        let mut parameters = Vec::new();
        parameters
            .try_reserve_exact(count)
            .map_err(|_| type_resource())?;
        for formal in &header.parameters {
            parameters.push((
                formal.id,
                clone_kind_with_budget(&formal.kind, &mut self.type_work)
                    .map_err(|_| type_resource())?,
            ));
        }
        if answer {
            parameters.push((header.answer.id, Kind::Type));
        }
        Ok(parameters)
    }

    fn source_state_data(
        &mut self,
        header: &SourceResourceTypeFact,
    ) -> Result<IterativeTypeOwner, TypeError> {
        let state = IterativeTypeOwner::new(self.clone_type(&header.state.ty)?);
        let data = IterativeTypeOwner::new(self.clone_type(&header.data.ty)?);
        self.type_work.charge(2).map_err(|_| type_resource())?;
        let mut fields = Vec::new();
        fields.try_reserve_exact(2).map_err(|_| type_resource())?;
        fields.extend([state.into_inner(), data.into_inner()]);
        Ok(IterativeTypeOwner::new(Type::Tuple(
            fields.into_boxed_slice(),
        )))
    }

    fn source_pattern(
        &mut self,
        pattern: &ResolvedPattern,
        input: &Type,
        context: &mut TypeContext,
    ) -> Result<(CheckedPattern, Vec<BinderId>), TypeError> {
        let mut binders = Vec::new();
        let checked = self.check_core_pattern(
            pattern,
            input,
            context,
            &mut binders,
            GeneratedReason::BindingLowering,
        )?;
        let CheckedPattern {
            pattern: checked_pattern,
            inference_changed,
            contains_newtype,
            pattern_count,
        } = checked;
        let mut checked_pattern = CorePatternOwner::new(Some(checked_pattern));
        let mut row = CorePatternBuffer(Vec::new());
        self.type_work.charge(1).map_err(|_| type_resource())?;
        row.try_reserve(1).map_err(|_| type_resource())?;
        row.push(checked_pattern.take().ok_or_else(invalid_state)?);
        let mut matrix_storage = Vec::new();
        matrix_storage
            .try_reserve_exact(1)
            .map_err(|_| type_resource())?;
        let mut matrix = CorePatternMatrixBuffer(matrix_storage);
        matrix.push(row.into_vec());
        if missing_witness_for_types_with_budget(
            &matrix,
            std::slice::from_ref(input),
            &self.registry,
            &mut self.coverage_work,
        )?
        .is_some()
        {
            return Err(inference_failure(
                TypeReason::RefutableHandlerPattern,
                pattern.span,
                "a resource lifecycle or access pattern must cover every value",
            ));
        }
        let mut row = matrix.pop().ok_or_else(invalid_state)?;
        let pattern = row.0.pop().ok_or_else(invalid_state)?;
        Ok((
            CheckedPattern {
                pattern,
                inference_changed,
                contains_newtype,
                pattern_count,
            },
            binders,
        ))
    }

    fn finish_source_program(
        &mut self,
        function: NodeId,
        function_type: &Type,
        header: &SourceResourceTypeFact,
        continuation: Option<TypeVariableId>,
    ) -> Result<crate::core::UnvalidatedEffectProgram, TypeError> {
        self.zonk_builder_types().map_err(TypeError::Internal)?;
        let mut parameters = self.source_parameters(header, continuation.is_some())?;
        if let Some(row) = continuation {
            self.type_work.charge(1).map_err(|_| type_resource())?;
            parameters.try_reserve(1).map_err(|_| type_resource())?;
            parameters.push((row, Kind::EffectRow));
        }
        let scheme_parameters =
            clone_kinded_type_parameters_with_budget(&parameters, &mut self.type_work)
                .map_err(|_| type_resource())?
                .into_boxed_slice();
        let function_type = IterativeTypeOwner::new(self.zonk(function_type)?);
        let scheme = Type::Forall(scheme_parameters, Box::new(function_type.into_inner()));
        let root =
            self.builder
                .type_abstraction(parameters, function, scheme, header.origin.clone())?;
        crate::core::transform::discharge_provider_draft_work(&self.builder, &mut self.type_work)?;
        let replacement = CoreBuilder::with_registry_and_rewrite_work(
            Arc::clone(&self.registry),
            TypeWorkBudget::with_limit(self.builder.rewrite_work_limit()),
        );
        std::mem::replace(&mut self.builder, replacement)
            .finish(root)
            .map_err(Into::into)
    }

    fn compile_source_lifecycle(
        &mut self,
        binders: &[BinderId],
        catalog: &Arc<MethodEvidenceCatalog>,
        definition: &ResolvedSourceResourceDefinition,
        header: &Arc<CheckedSourceResourceHeader>,
        phase: provider::Phase,
    ) -> Result<crate::core::UnvalidatedEffectProgram, TypeError> {
        let mut context = std::mem::take(&mut self.base_context);
        let result = (|| {
            self.begin_source_program(binders, catalog)?;
            let (pattern, expression, input, output) = match phase {
                provider::Phase::Acquire => (
                    &definition.acquire_pattern,
                    &definition.acquire,
                    IterativeTypeOwner::new(self.clone_type(&definition.input.ty)?),
                    &definition.acquisition.ty,
                ),
                provider::Phase::Finish => (
                    &definition.finish_pattern,
                    &definition.finish,
                    self.source_state_data(definition)?,
                    &definition.completion.ty,
                ),
                provider::Phase::Handler => return Err(invalid_state()),
            };
            self.provider_context = Some(provider::CheckingContext::source(
                Arc::clone(header),
                phase,
                &mut self.type_work,
            )?);
            self.provider_occurrence_template = Some(crate::resolved::ProviderTemplateId::new(
                definition.id,
                u32::from(phase == provider::Phase::Finish),
            ));
            let (checked, binders) = self.source_pattern(pattern, &input, &mut context)?;
            let pattern_owner = CorePatternOwner::new(Some(checked.pattern));
            let parameter_type = self.clone_type(&input)?;
            let parameter = self
                .builder
                .binder(parameter_type, Origin::Source(pattern.span))?;
            let scrutinee_type = self.clone_type(&input)?;
            let scrutinee = self.builder.variable(
                parameter.id(),
                scrutinee_type,
                Origin::Source(pattern.span),
            )?;
            let expected_type = self.clone_type(output)?;
            let expected_provenance = self.at_span_provenance(output, expression.span)?;
            let typed = self.elaborate_expression_with_context(
                ElaborationTask::Check {
                    expression,
                    expected: ProvenancedType {
                        ty: expected_type,
                        provenance: expected_provenance,
                    },
                    kind: CheckKind::General,
                },
                &mut context,
            );
            let cleanup = self.remove_pattern_binders(&mut context, &binders);
            let typed = TypedNodeOwner::new(typed?);
            cleanup?;
            let result_type = self.clone_type(&typed.ty)?;
            let mut pattern_owner = pattern_owner;
            let arm = CoreMatchArm::new(
                pattern_owner.take().ok_or_else(invalid_state)?,
                typed.node,
                Origin::Source(pattern.span),
            );
            let matched = self.lower_match_expression(
                scrutinee,
                vec![arm],
                result_type,
                Origin::Source(expression.span),
                checked.contains_newtype,
                checked.pattern_count,
            )?;
            let function_type = IterativeTypeOwner::new(Type::function_computation(
                self.clone_type(&input)?,
                ComputationType::new(
                    self.clone_type(&typed.ty)?,
                    clone_effect_row_with_budget(&typed.effects, &mut self.type_work)
                        .map_err(|_| type_resource())?,
                ),
            ));
            let core_type = self.clone_type(&function_type)?;
            let function = self.builder.function(
                parameter,
                matched,
                core_type,
                Origin::Source(definition.span),
            )?;
            self.finish_source_program(function, &function_type, definition, None)
        })();
        self.base_context = context;
        self.provider_context = None;
        self.provider_occurrence_template = None;
        if result.is_err() {
            crate::core::transform::discharge_provider_draft_work(
                &self.builder,
                &mut self.type_work,
            )?;
        }
        result
    }

    fn compile_source_handler(
        &mut self,
        binders: &[BinderId],
        catalog: &Arc<MethodEvidenceCatalog>,
        definition: &ResolvedSourceResourceDefinition,
        header: &Arc<CheckedSourceResourceHeader>,
    ) -> Result<
        (
            crate::core::UnvalidatedEffectProgram,
            Option<crate::core::source_resource::SourceHandlerRowInputs>,
        ),
        TypeError,
    > {
        let mut context = std::mem::take(&mut self.base_context);
        let result = (|| {
            self.begin_source_program(binders, catalog)?;
            self.provider_context = Some(provider::CheckingContext::source(
                Arc::clone(header),
                provider::Phase::Handler,
                &mut self.type_work,
            )?);
            self.provider_occurrence_template =
                Some(crate::resolved::ProviderTemplateId::new(definition.id, 2));
            let input = self.source_state_data(definition)?;
            let (checked, binders) =
                self.source_pattern(&definition.handlers_pattern, &input, &mut context)?;
            let mut pattern_owner = CorePatternOwner::new(Some(checked.pattern));
            let input_type = self.clone_type(&input)?;
            let state_data = self
                .builder
                .binder(input_type, Origin::Source(definition.handlers_pattern.span))?;
            let input_type = self.clone_type(&input)?;
            let scrutinee = self.builder.variable(
                state_data.id(),
                input_type,
                Origin::Source(definition.handlers_pattern.span),
            )?;
            let answer_type = Type::Variable(definition.answer.id);
            let continuation = self.fresh_type_variable(&Kind::EffectRow, definition.span)?;
            let handled = self.check_effect_clauses(
                &definition.provided.instance,
                &definition.handlers,
                definition.span,
                &mut context,
                &answer_type,
                EffectRow::empty(),
            );
            let cleanup = self.remove_pattern_binders(&mut context, &binders);
            let (handler, demands, checked_clauses) = handled?;
            cleanup?;
            let direct = self.zonk_effect_row(&demands)?;
            let conditional = !direct.is_empty()
                || !self.cleanup_rows.is_empty()
                || checked_clauses.iter().any(|clause| {
                    clause
                        .pattern
                        .binder_iter()
                        .any(|binder| binder.ty().function_view().is_some())
                });
            let demands = clone_effect_row_with_budget(&direct, &mut self.type_work)
                .map_err(|_| type_resource())?;
            let placeholder_effect = clone_effect_instance_with_budget(
                &definition.provided.instance,
                &mut self.type_work,
            )
            .map_err(|_| type_resource())?;
            let residual = crate::types::rebuild_effect_row_with_budget(
                std::iter::empty(),
                Some(crate::types::EffectRowVariable::rigid(continuation)),
                demands
                    .known()
                    .iter()
                    .filter(|_| !conditional)
                    .chain(std::iter::once(&placeholder_effect)),
                crate::types::clone_type_with_budget,
                &mut self.type_work,
            )
            .map_err(|_| type_resource())?;
            let demands = if conditional {
                residual
            } else {
                self.union_effects(&demands, &residual, definition.span)?
            };
            // The original thunk carries the complete ordinary continuation row.
            // At specialization its private residual is solved from the client's
            // least output, while direct clause demands remain explicit.
            let callback_row = self.union_effects(
                &EffectRow::singleton(placeholder_effect),
                &demands,
                definition.span,
            )?;
            let callback_type = IterativeTypeOwner::new(Type::function_computation(
                Type::Unit,
                ComputationType::new(Type::Variable(definition.answer.id), callback_row),
            ));
            let callback_binder_type = self.clone_type(&callback_type)?;
            let answer = self
                .builder
                .binder(callback_binder_type, Origin::Source(definition.span))?;
            let callback_value_type = self.clone_type(&callback_type)?;
            let callback = self.builder.variable(
                answer.id(),
                callback_value_type,
                Origin::Source(definition.span),
            )?;
            let unit = self
                .builder
                .unit(Type::Unit, Origin::Source(definition.span))?;
            let placeholder = self.builder.application(
                callback,
                unit,
                Type::Variable(definition.answer.id),
                Origin::Source(definition.span),
            )?;
            self.type_work
                .charge(checked_clauses.len())
                .map_err(|_| type_resource())?;
            let mut clauses = Vec::new();
            clauses
                .try_reserve_exact(checked_clauses.len())
                .map_err(|_| type_resource())?;
            for clause in checked_clauses {
                if !conditional {
                    self.recompute_cleanup_clause(clause.range, &demands, handler, clause.resume)?;
                }
                clauses.push(EffectClause::new(
                    clause.operation,
                    clause.resume,
                    CoreMatchArm::new(clause.pattern.into_inner(), clause.body, clause.origin),
                ));
            }
            let effect = clone_effect_instance_with_budget(
                &definition.provided.instance,
                &mut self.type_work,
            )
            .map_err(|_| type_resource())?;
            let row = clone_effect_row_with_budget(&demands, &mut self.type_work)
                .map_err(|_| type_resource())?;
            let handled = self.builder.handler(
                handler,
                placeholder,
                effect,
                clauses,
                Type::Variable(definition.answer.id),
                row,
                Origin::Source(definition.span),
            )?;
            let matched = self.lower_match_expression(
                scrutinee,
                vec![CoreMatchArm::new(
                    pattern_owner.take().ok_or_else(invalid_state)?,
                    handled,
                    Origin::Source(definition.handlers_pattern.span),
                )],
                Type::Variable(definition.answer.id),
                Origin::Source(definition.span),
                checked.contains_newtype,
                checked.pattern_count,
            )?;
            let answer_function_row = clone_effect_row_with_budget(&demands, &mut self.type_work)
                .map_err(|_| type_resource())?;
            let answer_function_type = IterativeTypeOwner::new(Type::function_computation(
                callback_type.into_inner(),
                ComputationType::new(Type::Variable(definition.answer.id), answer_function_row),
            ));
            let answer_function_core_type = self.clone_type(&answer_function_type)?;
            let answer_function = self.builder.function(
                answer,
                matched,
                answer_function_core_type,
                Origin::Source(definition.span),
            )?;
            let function_type = IterativeTypeOwner::new(Type::function_computation(
                self.clone_type(&input)?,
                ComputationType::pure(answer_function_type.into_inner()),
            ));
            let core_type = self.clone_type(&function_type)?;
            let function = self.builder.function(
                state_data,
                answer_function,
                core_type,
                Origin::Source(definition.span),
            )?;
            if conditional {
                self.zonk_builder_types_since(None, false)
                    .map_err(TypeError::Internal)?;
                let mut parameters = self.source_parameters(definition, true)?;
                self.type_work.charge(1).map_err(|_| type_resource())?;
                parameters.try_reserve(1).map_err(|_| type_resource())?;
                parameters.push((continuation, Kind::EffectRow));
                let quantified =
                    clone_kinded_type_parameters_with_budget(&parameters, &mut self.type_work)
                        .map_err(|_| type_resource())?
                        .into_boxed_slice();
                let ty = IterativeTypeOwner::new(self.zonk(&function_type)?);
                let root = self.builder.type_abstraction(
                    parameters,
                    function,
                    Type::Forall(quantified, Box::new(ty.into_inner())),
                    definition.origin.clone(),
                )?;
                let pending = self.cleanup_rows.take_provider_pending(
                    &self.builder,
                    root,
                    &mut self.type_work,
                )?;
                crate::core::transform::discharge_provider_draft_work(
                    &self.builder,
                    &mut self.type_work,
                )?;
                let replacement = CoreBuilder::with_registry_and_rewrite_work(
                    Arc::clone(&self.registry),
                    TypeWorkBudget::with_limit(self.builder.rewrite_work_limit()),
                );
                let (program, pending) = std::mem::replace(&mut self.builder, replacement)
                    .finish_provider_conditional_draft(root, pending, &mut self.type_work)?;
                Ok((
                    program,
                    Some(crate::core::source_resource::SourceHandlerRowInputs { direct, pending }),
                ))
            } else {
                self.finish_source_program(function, &function_type, definition, Some(continuation))
                    .map(|program| (program, None))
            }
        })();
        self.base_context = context;
        self.provider_context = None;
        self.provider_occurrence_template = None;
        if result.is_err() {
            crate::core::transform::discharge_provider_draft_work(
                &self.builder,
                &mut self.type_work,
            )?;
        }
        result
    }
}
