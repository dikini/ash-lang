//! Static checked host introduction and exact native interpretation.
use super::*;
use crate::types::OperationId;

impl<F: CoreLoweringFamily> CoreElaborator<F> {
    pub(super) fn schedule_foreign_host<'a>(
        &mut self,
        source: &'a crate::resolved::ResolvedForeignHostExpr,
        span: Span,
        tasks: &mut ElaborationTaskBuffer<'a>,
    ) -> Result<(), TypeError> {
        if !F::EFFECTS {
            return Err(foreign_privilege_unavailable());
        }
        let effect = self
            .registry
            .effect(source.effect)
            .ok_or_else(invalid_state)?;
        if source.identity.kind != Kind::Type
            || !crate::foreign::checked_builtins::is_canonical_native_host(
                effect,
                &self.registry,
                &mut self.type_work,
            )
            .map_err(|failure| {
                if failure.is_resource_exhaustion() {
                    type_resource()
                } else {
                    invalid_state()
                }
            })?
        {
            return Err(invalid_state());
        }
        self.type_work.charge(2).map_err(|()| type_resource())?;
        tasks.0.try_reserve(2).map_err(|_| type_resource())?;
        tasks.push(ElaborationTask::FinishForeignHost { source, span });
        tasks.push(ElaborationTask::Synthesize {
            expression: &source.body,
            cause: None,
        });
        Ok(())
    }

    pub(super) fn finish_foreign_host(
        &mut self,
        source: &crate::resolved::ResolvedForeignHostExpr,
        span: Span,
        values: &mut TypedNodeBuffer,
    ) -> Result<(), TypeError> {
        #[cfg(test)]
        eprintln!("checked lifecycle host finish entered");
        let body = values.pop().ok_or_else(invalid_state)?;
        let row = self.zonk_effect_row(&body.effects)?;
        let ty = IterativeTypeOwner::new(self.zonk(&body.ty)?);
        let host = crate::core::effect::ForeignHostIdentity {
            identity: source.identity.id,
            effect: source.effect,
        };
        self.type_work
            .charge(row.known().len())
            .map_err(|()| type_resource())?;
        let mut interpretations = Vec::new();
        interpretations
            .try_reserve_exact(row.known().len())
            .map_err(|_| type_resource())?;
        for instance in row.known() {
            let Some(symbol) = self
                .registry
                .native_symbol(OperationId::new(instance.effect(), 0))
            else {
                continue;
            };
            let selected = crate::foreign::checked_source::checked_host_instance(
                symbol,
                instance,
                &mut self.type_work,
            )
            .map_err(|failure| {
                if failure.is_resource_exhaustion() {
                    type_resource()
                } else {
                    invalid_state()
                }
            })?;
            let Some(selected) = selected else {
                return Err(inference_failure(
                    TypeReason::Argument,
                    span,
                    "a checked host cannot admit a legacy native contract",
                ));
            };
            if !matches!(selected.arguments(), [crate::types::KindedArgument::TypeArg(Type::Variable(id))] if *id == host.identity())
                || selected.effect() != host.effect()
            {
                continue;
            }
            if symbol.owner().is_some()
                || !matches!(
                    symbol.symbol().call(),
                    crate::foreign::source_contract::PreparedForeignCall::Scalar { .. }
                )
            {
                return Err(inference_failure(
                    TypeReason::Argument,
                    span,
                    "checked owner lifecycle admission is not yet available",
                ));
            }
            interpretations.push(crate::core::NativeInterpretation::new(
                clone_effect_instance_with_budget(instance, &mut self.type_work)?,
                Arc::clone(symbol),
            ));
        }
        #[cfg(test)]
        eprintln!("checked lifecycle host interpretations={}", interpretations.len());
        let effects = crate::core::effect::foreign_host_outward_row(
            &row,
            &interpretations,
            Some(host),
            &mut self.type_work,
        )?;
        let row_type = IterativeTypeOwner::new(Type::function_computation(
            Type::Unit,
            crate::types::ComputationType::new(
                self.clone_type(&ty)?,
                clone_effect_row_with_budget(&effects, &mut self.type_work)
                    .map_err(|()| type_resource())?,
            ),
        ));
        if crate::types::visit_type_structure_with_budget(&row_type, &mut self.type_work, |node, _| {
            Ok(matches!(node, crate::types::TypeStructureNode::Type(Type::Variable(id)) if *id == host.identity()))
        }).map_err(|()| type_resource())? {
            return Err(inference_failure(TypeReason::Argument, span, "checked host identity escapes in the result or outward row"));
        }
        let provenance = self.at_span_provenance(&ty, span)?;
        let core_ty = self.pure_core_type(&ty)?;
        let core_effects = self.core_effect_row(&effects)?;
        let boundary =
            crate::core::NativeInterpretNode::new(body.node, interpretations.into_boxed_slice())
                .with_host(host);
        let node = self.push_effect_core(
            core_ty,
            core_effects,
            Origin::Source(span),
            EffectOperation::NativeInterpret(boundary),
        )?;
        #[cfg(test)]
        eprintln!("checked lifecycle host finish complete");
        values.push(TypedNode {
            node,
            ty: ty.into_inner(),
            effects,
            provenance,
        });
        Ok(())
    }
}
