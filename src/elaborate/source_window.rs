//! Direct source-phase candidates; independent Core reconstructs their authority.
use super::{
    Arc, CheckKind, CoreElaborator, CoreLoweringFamily, EffectOperation, ElaborationTask,
    ElaborationTaskBuffer, IterativeTypeOwner, Origin, ProvenancedType, Span, Type, TypeError,
    TypeReason, TypeVariableId, TypedNode, TypedNodeBuffer, TypedNodeOwner,
    clone_effect_instance_with_budget, inference_failure, invalid_state, type_resource,
};
use crate::foreign::source_access::CheckedForeignAccess;

#[derive(Debug)]
pub(super) struct WindowArguments(pub(super) Box<[crate::types::KindedArgument]>);
impl WindowArguments {
    fn take(&mut self) -> Box<[crate::types::KindedArgument]> {
        std::mem::take(&mut self.0)
    }
}
impl Drop for WindowArguments {
    fn drop(&mut self) {
        for argument in self.take().into_vec() {
            crate::types::discard_kinded_argument_iteratively(argument);
        }
    }
}
#[derive(Debug)]
pub(super) struct CheckingWindow {
    pub(super) family: Arc<CheckedForeignAccess>,
    pub(super) arguments: WindowArguments,
    identity: TypeVariableId,
}
pub(super) struct WindowProgress<'a> {
    source: &'a crate::resolved::ResolvedCopyWindowExpr,
    span: Span,
    family: Arc<CheckedForeignAccess>,
    arguments: WindowArguments,
    state: Option<TypedNodeOwner>,
}
impl<F: CoreLoweringFamily> CoreElaborator<F> {
    pub(super) fn schedule_copy_window<'a>(
        &mut self,
        source: &'a crate::resolved::ResolvedCopyWindowExpr,
        span: Span,
        tasks: &mut ElaborationTaskBuffer<'a>,
    ) -> Result<(), TypeError> {
        if !F::EFFECTS || !self.source_window_context() {
            return Err(inference_failure(
                TypeReason::Argument,
                span,
                "copy windows require an original direct provider phase",
            ));
        }
        self.type_work
            .charge(self.registry.source_foreign_nominal_count())
            .map_err(|()| type_resource())?;
        let family = self
            .registry
            .source_accesses()
            .find(|access| access.nominal() == source.family)
            .map(Arc::clone)
            .ok_or_else(invalid_state)?;
        let arguments = WindowArguments(
            crate::types::clone_kinded_arguments_with_budget(
                source.arguments.iter().map(|argument| &argument.ty),
                &mut self.type_work,
            )
            .map_err(|()| type_resource())?,
        );
        let (_, expected) = crate::foreign::source_access::window_state_type(
            &family,
            arguments.0.iter(),
            source.identity.id,
            &self.registry,
            &mut self.type_work,
        )
        .map_err(|failure| {
            if failure.is_resource_exhaustion() {
                type_resource()
            } else {
                invalid_state()
            }
        })?;
        self.type_work.charge(3).map_err(|()| type_resource())?;
        tasks.0.try_reserve(2).map_err(|_| type_resource())?;
        tasks.push(ElaborationTask::CopyWindowBody(Box::new(WindowProgress {
            source,
            span,
            family,
            arguments,
            state: None,
        })));
        let provenance = self.at_span_provenance(&expected, source.state.span)?;
        tasks.push(ElaborationTask::Check {
            expression: &source.state,
            expected: ProvenancedType {
                ty: expected.into_inner(),
                provenance,
            },
            kind: CheckKind::General,
        });
        Ok(())
    }
    pub(super) fn step_copy_window_body<'a>(
        &mut self,
        mut progress: Box<WindowProgress<'a>>,
        tasks: &mut ElaborationTaskBuffer<'a>,
        values: &mut TypedNodeBuffer,
    ) -> Result<(), TypeError> {
        progress.state = Some(values.pop().ok_or_else(invalid_state)?);
        let arguments = WindowArguments(
            crate::types::clone_kinded_arguments_with_budget(
                progress.arguments.0.iter(),
                &mut self.type_work,
            )
            .map_err(|()| type_resource())?,
        );
        self.type_work.charge(3).map_err(|()| type_resource())?;
        let context = self.provider_context.as_mut().ok_or_else(invalid_state)?;
        context
            .windows
            .try_reserve(1)
            .map_err(|_| type_resource())?;
        context.windows.push(CheckingWindow {
            family: Arc::clone(&progress.family),
            arguments,
            identity: progress.source.identity.id,
        });
        let body = &progress.source.body;
        tasks.0.try_reserve(2).map_err(|_| type_resource())?;
        tasks.push(ElaborationTask::FinishCopyWindow(progress));
        tasks.push(ElaborationTask::Synthesize {
            expression: body,
            cause: None,
        });
        Ok(())
    }
    #[expect(
        clippy::boxed_local,
        reason = "keep the already-boxed phase payload off ordinary reentrant work frames"
    )]
    pub(super) fn finish_copy_window(
        &mut self,
        mut progress: Box<WindowProgress<'_>>,
        values: &mut TypedNodeBuffer,
    ) -> Result<(), TypeError> {
        let body = values.pop().ok_or_else(invalid_state)?;
        let active = self
            .provider_context
            .as_mut()
            .and_then(|context| context.windows.pop())
            .ok_or_else(invalid_state)?;
        if active.identity != progress.source.identity.id
            || !Arc::ptr_eq(&active.family, &progress.family)
        {
            return Err(invalid_state());
        }
        let row = self.zonk_effect_row(&body.effects)?;
        if row.tail().is_some() {
            return Err(inference_failure(
                TypeReason::Argument,
                progress.span,
                "an open copy window cannot suspend",
            ));
        }
        let host = crate::foreign::source_access::checked_window_host_instance(
            &progress.family,
            &progress.arguments.0,
            &self.registry,
            &mut self.type_work,
        )
        .map_err(|error| {
            if error.is_resource_exhaustion() {
                type_resource()
            } else {
                invalid_state()
            }
        })?;
        let mut retained_host = false;
        let mut interpretations = Vec::new();
        self.type_work
            .charge(row.known().len())
            .map_err(|()| type_resource())?;
        interpretations
            .try_reserve_exact(row.known().len())
            .map_err(|_| type_resource())?;
        for effect in row.known() {
            if let Some(host) = &host
                && crate::types::compare_effect_instances_with_budget(
                    effect,
                    host,
                    &mut self.type_work,
                )
                .map_err(|_| type_resource())?
                    == std::cmp::Ordering::Equal
            {
                retained_host = true;
                // The exact sealed Host obligation is retained, never
                // interpreted as a native operation by this window.
                continue;
            }
            let symbol = self
                .registry
                .native_symbol(crate::types::OperationId::new(effect.effect(), 0))
                .map(Arc::clone)
                .ok_or_else(|| {
                    inference_failure(
                        TypeReason::Argument,
                        progress.span,
                        "an open copy window cannot suspend",
                    )
                })?;
            let interpretation = crate::core::NativeInterpretation::new(
                clone_effect_instance_with_budget(effect, &mut self.type_work)?,
                symbol,
            );
            if !crate::foreign::source_access::window_interpretation_matches(
                &progress.family,
                &progress.arguments.0,
                &interpretation,
                &self.registry,
                &mut self.type_work,
            )
            .map_err(|failure| {
                if failure.is_resource_exhaustion() {
                    type_resource()
                } else {
                    invalid_state()
                }
            })? {
                return Err(inference_failure(
                    TypeReason::Argument,
                    progress.span,
                    "operation does not preserve the exact copy-window family",
                ));
            }
            interpretations.push(interpretation);
        }
        let state = progress.state.take().ok_or_else(invalid_state)?;
        let ty = IterativeTypeOwner::new(self.zonk(&body.ty)?);
        if crate::types::visit_type_structure_with_budget(&ty, &mut self.type_work, |node, _| {
            Ok(matches!(node, crate::types::TypeStructureNode::Type(Type::Variable(id)) if *id == progress.source.identity.id))
        }).map_err(|()| type_resource())? {
            return Err(inference_failure(TypeReason::Argument, progress.span, "copy-window identity escapes in the result"));
        }
        let provenance = self.at_span_provenance(&ty, progress.span)?;
        let host_row = if let Some(host) = host.filter(|_| retained_host) {
            self.type_work.charge(1).map_err(|_| type_resource())?;
            crate::types::EffectRow::singleton(host)
        } else {
            crate::types::EffectRow::empty()
        };
        let effects = self.union_effects(&state.effects, &host_row, progress.span)?;
        let node_ty = self.clone_type(&ty)?;
        let node_effects = self.core_effect_row(&effects)?;
        self.type_work.charge(2).map_err(|()| type_resource())?;
        let window = crate::core::source_window::SourceCopyWindowNode::new(
            Arc::clone(&progress.family),
            progress.arguments.take(),
            progress.source.identity.id,
            interpretations.into_boxed_slice(),
            state.node,
            body.node,
        );
        let node = self.push_effect_core(
            node_ty,
            node_effects,
            Origin::Source(progress.span),
            EffectOperation::SourceCopyWindow(Box::new(window)),
        )?;
        values.push(TypedNode {
            node,
            ty: ty.into_inner(),
            effects,
            provenance,
        });
        Ok(())
    }
}
