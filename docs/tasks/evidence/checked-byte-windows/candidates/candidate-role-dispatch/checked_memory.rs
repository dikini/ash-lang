//! Exact checked primitive annotation shapes within the existing builtin fact.

use super::*;
use crate::types::{EffectId, KindedArgument, NominalTypeId};

impl CheckedForeignScalarPreflight {
    pub(super) fn authenticate_checked_memory_annotation(
        &self,
        work: &mut TypeWorkBudget,
    ) -> Result<(), ForeignAdmissionError> {
        let invalid = || failure(ForeignAdmissionReason::InvalidSignature, self.source);
        charge(work, 32, self.source)?;
        let host = self
            .role
            .host_parameter(self.module())
            .ok_or_else(invalid)?;
        let borrowed = self
            .role
            .borrowed_parameter(self.module())
            .ok_or_else(invalid)?;
        let role = self.role.operation_role();
        let bytes = role == ForeignScalarPreflightRole::CopyBytes;
        let copy = matches!(
            role,
            ForeignScalarPreflightRole::CopyBytes | ForeignScalarPreflightRole::CopyNul
        );
        let write = role == ForeignScalarPreflightRole::ByteWrite;
        if self.call_codec.ids().call != NominalTypeId::new(self.module(), 12) {
            return Err(invalid());
        }
        let Type::EffectfulFunction(domain, computation) = self.signature() else {
            return Err(invalid());
        };
        let Type::Tuple(fields) = domain.as_ref() else {
            return Err(invalid());
        };
        if fields.len() != 2 + usize::from(write)
            || !matches!(fields.first(), Some(Type::Variable(id)) if *id == borrowed)
        {
            return Err(invalid());
        }
        if bytes {
            if !matches!(&fields[1], Type::Application(head, argument)
                if matches!(head.as_ref(), Type::Nominal(id) if *id == NominalTypeId::new(self.module(), 5))
                && matches!(argument.as_ref(), Type::Variable(id) if *id == borrowed))
            {
                return Err(invalid());
            }
        } else if fields[1..].iter().any(|field| !matches!(field, Type::Int)) {
            return Err(invalid());
        }
        let Type::Application(call, result) = computation.value() else {
            return Err(invalid());
        };
        if !matches!(call.as_ref(), Type::Nominal(id) if *id == self.call_codec.ids().call)
            || if copy {
                !matches!(result.as_ref(), Type::Bytes)
            } else if write {
                !matches!(result.as_ref(), Type::Unit)
            } else {
                !matches!(result.as_ref(), Type::Int)
            }
        {
            return Err(invalid());
        }
        if computation.effects().tail().is_some() {
            return Err(invalid());
        }
        let [instance] = computation.effects().known() else {
            return Err(invalid());
        };
        if instance.effect()
            != EffectId::new(self.module(), crate::module::FOREIGN_NATIVE_HOST_LOCAL)
            || !matches!(instance.arguments(), [KindedArgument::TypeArg(Type::Variable(id))] if *id == host)
        {
            return Err(invalid());
        }

        // Provenance is checked against the exact immutable annotation, including
        // its Host argument occurrence. Matching semantic type shape alone is
        // insufficient to authenticate a compiler-owned role.
        let text = match role {
            ForeignScalarPreflightRole::ByteRead => {
                "(S, Int) -> CheckedCall<Int> ! {NativeHost<H>}"
            }
            ForeignScalarPreflightRole::ByteWrite => {
                "(S, Int, Int) -> CheckedCall<Unit> ! {NativeHost<H>}"
            }
            ForeignScalarPreflightRole::CopyBytes => {
                "(V, Extent<V>) -> CheckedCall<Bytes> ! {NativeHost<H>}"
            }
            ForeignScalarPreflightRole::CopyNul => {
                "(V, Int) -> CheckedCall<Bytes> ! {NativeHost<H>}"
            }
            _ => return Err(invalid()),
        };
        let start = self.annotation.span.range().start();
        let exact = |span: Span, offset: usize, length: usize| {
            span.source() == self.source.source()
                && span.range().start() == start + offset as u32
                && span.range().end() == start + (offset + length) as u32
        };
        let nodes = self.annotation.provenance.nodes();
        charge(work, nodes.len(), self.source)?;
        let fact = |id, offset, length| matches!(nodes.get(id), Some(ResolvedTypeProvenanceNode::Fact(span)) if exact(*span, offset, length));
        let application = |id, offset, name_length, argument_length| {
            matches!(nodes.get(id), Some(ResolvedTypeProvenanceNode::Application {span, function, argument, argument_span})
                if exact(*span, offset, name_length + argument_length + 2)
                && fact(*function, offset, name_length)
                && fact(*argument, offset + name_length + 1, argument_length)
                && exact(*argument_span, offset + name_length + 1, argument_length))
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
        let Some(ResolvedTypeProvenanceNode::Tuple {
            span: tuple,
            elements,
        }) = nodes.get(*domain)
        else {
            return Err(invalid());
        };
        let call_start = text
            .find("CheckedCall")
            .expect("fixed canonical annotation");
        let tuple_length = text.find(" ->").expect("fixed canonical annotation");
        let host_start = text.rfind('H').expect("fixed canonical Host argument");
        if *span != self.annotation.span
            || !exact(*span, 0, text.len())
            || !exact(*tuple, 0, tuple_length)
            || elements.len() != fields.len()
            || !fact(elements[0], 1, 1)
            || if bytes {
                !application(elements[1], 4, 6, 1)
            } else {
                !fact(elements[1], 4, 3)
            }
            || write && !fact(elements[2], 9, 3)
            || !application(
                *codomain,
                call_start,
                11,
                if copy {
                    5
                } else if write {
                    4
                } else {
                    3
                },
            )
            || effect_arguments.len() != 1
            || !fact(effect_arguments[0], host_start, 1)
        {
            return Err(invalid());
        }
        Ok(())
    }
}
