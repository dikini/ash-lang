//! Exact original declarations for conservative checked-group denial.

use super::*;
use crate::types::{EffectId, KindedArgument, NominalTypeId};

impl CheckedForeignScalarPreflight {
    pub(super) fn authenticate_checked_violation_annotation(
        &self,
        work: &mut TypeWorkBudget,
    ) -> Result<(), ForeignAdmissionError> {
        let invalid = || failure(ForeignAdmissionReason::InvalidSignature, self.source);
        charge(work, 20, self.source)?;
        let host = self
            .role
            .host_parameter(self.module())
            .ok_or_else(invalid)?;
        let cause = NominalTypeId::new(
            self.module(),
            crate::module::ForeignCheckedNominalRole::ViolationCause.local(),
        );
        let Type::EffectfulFunction(domain, computation) = self.signature() else {
            return Err(invalid());
        };
        let quarantine = self.role == ForeignScalarPreflightRole::CheckedQuarantine;
        if quarantine {
            let state = self
                .role
                .state_parameter(self.module())
                .ok_or_else(invalid)?;
            if !matches!(domain.as_ref(), Type::Tuple(fields)
                if matches!(fields.as_ref(), [Type::Variable(actual), Type::Nominal(found)]
                    if *actual == state && *found == cause))
            {
                return Err(invalid());
            }
        } else if self.role != ForeignScalarPreflightRole::CheckedRejectAcquisition
            || !matches!(domain.as_ref(), Type::Nominal(found) if *found == cause)
        {
            return Err(invalid());
        }
        if self.call_codec.ids().call != NominalTypeId::new(self.module(), 12)
            || !matches!(computation.value(), Type::Application(call, result)
                if matches!(call.as_ref(), Type::Nominal(found) if *found == self.call_codec.ids().call)
                    && matches!(result.as_ref(), Type::Unit))
            || computation.effects().tail().is_some()
            || !matches!(computation.effects().known(), [instance]
                if instance.effect() == EffectId::new(self.module(), crate::module::FOREIGN_NATIVE_HOST_LOCAL)
                    && matches!(instance.arguments(), [KindedArgument::TypeArg(Type::Variable(found))] if *found == host))
        {
            return Err(invalid());
        }
        let text = if quarantine {
            "(S, ViolationCause) -> CheckedCall<Unit> ! {NativeHost<H>}"
        } else {
            "ViolationCause -> CheckedCall<Unit> ! {NativeHost<H>}"
        };
        let start = self.annotation.span.range().start();
        let exact = |span: Span, offset: usize, length: usize| {
            span.source() == self.source.source()
                && span.range().start() == start + offset as u32
                && span.range().end() == start + (offset + length) as u32
        };
        let nodes = self.annotation.provenance.nodes();
        charge(work, nodes.len(), self.source)?;
        let fact = |id, offset, length| {
            matches!(nodes.get(id),
            Some(ResolvedTypeProvenanceNode::Fact(span)) if exact(*span, offset, length))
        };
        let Some(ResolvedTypeProvenanceNode::Function {
            span,
            domain,
            codomain,
            effect_arguments,
        }) = nodes.get(self.annotation.provenance.root())
        else {
            return Err(invalid());
        };
        if !exact(*span, 0, text.len()) || *span != self.annotation.span {
            return Err(invalid());
        }
        if quarantine {
            let Some(ResolvedTypeProvenanceNode::Tuple { span, elements }) = nodes.get(*domain)
            else {
                return Err(invalid());
            };
            if !exact(*span, 0, text.find(" ->").expect("fixed annotation"))
                || elements.len() != 2
                || !fact(elements[0], 1, 1)
                || !fact(elements[1], 4, "ViolationCause".len())
            {
                return Err(invalid());
            }
        } else if !fact(*domain, 0, "ViolationCause".len()) {
            return Err(invalid());
        }
        let call_start = text.find("CheckedCall").expect("fixed annotation");
        let Some(ResolvedTypeProvenanceNode::Application {
            span,
            function,
            argument,
            argument_span,
        }) = nodes.get(*codomain)
        else {
            return Err(invalid());
        };
        if !exact(*span, call_start, "CheckedCall<Unit>".len())
            || !fact(*function, call_start, "CheckedCall".len())
            || !fact(*argument, call_start + "CheckedCall<".len(), "Unit".len())
            || !exact(
                *argument_span,
                call_start + "CheckedCall<".len(),
                "Unit".len(),
            )
            || effect_arguments.len() != 1
            || !fact(effect_arguments[0], text.rfind('H').expect("fixed host"), 1)
        {
            return Err(invalid());
        }
        Ok(())
    }
}
