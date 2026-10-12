//! Original compiler-owned scalar checks and sealed byte declarations.
//! A declaration fact grants no live native access or owner authority.

use std::sync::Arc;

use super::checked_source::{
    CheckedForeignCallCodec, ForeignAdmissionError, ForeignAdmissionReason, charge, failure,
};
use crate::{
    module::ModuleId,
    resolved::{BinderId, ResolvedRegistry, ResolvedType, ResolvedTypeProvenanceNode},
    source::{Origin, Span, discard_origin_iteratively},
    types::{ConstructorId, Kind, Type, TypeVariableId, TypeWorkBudget, discard_type_iteratively},
};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum ForeignScalarPreflightRole {
    I64,
    SizeT,
    ByteRead,
    ByteWrite,
}

impl ForeignScalarPreflightRole {
    pub(crate) const fn local(self) -> u32 {
        match self {
            Self::I64 => 0,
            Self::SizeT => 1,
            Self::ByteRead => 2,
            Self::ByteWrite => 3,
        }
    }

    pub(crate) const fn byte_parameter(self, module: ModuleId) -> Option<TypeVariableId> {
        match self {
            // The four preceding canonical nominal declarations each bind T.
            Self::ByteRead => Some(TypeVariableId::resolved(module, 4)),
            Self::ByteWrite => Some(TypeVariableId::resolved(module, 5)),
            _ => None,
        }
    }
}

pub(crate) struct CheckedForeignScalarPreflight {
    function: BinderId,
    role: ForeignScalarPreflightRole,
    source: Span,
    origin: Origin,
    annotation: ResolvedType,
    core_signature: Option<Type>,
    call_codec: Arc<CheckedForeignCallCodec>,
}

impl std::fmt::Debug for CheckedForeignScalarPreflight {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("CheckedForeignScalarPreflight")
            .field("function", &self.function)
            .field("role", &self.role)
            .field("source", &self.source)
            .field("annotation", &self.annotation)
            .finish_non_exhaustive()
    }
}

impl PartialEq for CheckedForeignScalarPreflight {
    fn eq(&self, other: &Self) -> bool {
        self.function == other.function
            && self.role == other.role
            && self.source == other.source
            && self.origin == other.origin
            && self.annotation == other.annotation
            && Arc::ptr_eq(&self.call_codec, &other.call_codec)
    }
}
impl Eq for CheckedForeignScalarPreflight {}

impl Drop for CheckedForeignScalarPreflight {
    fn drop(&mut self) {
        discard_type_iteratively(std::mem::replace(&mut self.annotation.ty, Type::Unit));
        if let Some(signature) = self.core_signature.take() {
            discard_type_iteratively(signature);
        }
        discard_origin_iteratively(std::mem::replace(
            &mut self.annotation.origin,
            Origin::Source(self.source),
        ));
        discard_origin_iteratively(std::mem::replace(
            &mut self.origin,
            Origin::Source(self.source),
        ));
    }
}

impl CheckedForeignScalarPreflight {
    pub(crate) fn from_original(
        role: ForeignScalarPreflightRole,
        source: Span,
        origin: &Origin,
        annotation: &ResolvedType,
        call_codec: Arc<CheckedForeignCallCodec>,
        work: &mut TypeWorkBudget,
    ) -> Result<Self, ForeignAdmissionError> {
        charge(work, 2, source)?;
        let (Origin::Source(origin), Origin::Source(annotation_origin)) =
            (origin, &annotation.origin)
        else {
            return Err(failure(ForeignAdmissionReason::InvalidSignature, source));
        };
        let ty = crate::types::IterativeTypeOwner::new(
            crate::types::clone_type_with_budget(&annotation.ty, work)
                .map_err(|()| failure(ForeignAdmissionReason::WorkExhausted, source))?,
        );
        charge(work, 1, source)?;
        let annotation = ResolvedType {
            ty: ty.into_inner(),
            provenance: annotation.provenance.clone(),
            origin: Origin::Source(*annotation_origin),
            span: annotation.span,
        };
        Self::from_image_records(
            BinderId::resolved(call_codec.module(), role.local()),
            role,
            source,
            Origin::Source(*origin),
            annotation,
            call_codec,
            work,
        )
    }
    /// Takes decoded original records; independent registry admission follows.
    pub(crate) fn from_image_records(
        function: BinderId,
        role: ForeignScalarPreflightRole,
        source: Span,
        origin: Origin,
        annotation: ResolvedType,
        call_codec: Arc<CheckedForeignCallCodec>,
        work: &mut TypeWorkBudget,
    ) -> Result<Self, ForeignAdmissionError> {
        let core_signature = if let Some(parameter) = role.byte_parameter(call_codec.module()) {
            let body = crate::types::IterativeTypeOwner::new(
                crate::types::clone_type_with_budget(&annotation.ty, work)
                    .map_err(|()| failure(ForeignAdmissionReason::WorkExhausted, source))?,
            );
            charge(work, 3, source)?;
            let mut parameters = Vec::new();
            parameters
                .try_reserve_exact(1)
                .map_err(|_| failure(ForeignAdmissionReason::WorkExhausted, source))?;
            parameters.push((parameter, Kind::Type));
            Some(Type::Forall(
                parameters.into_boxed_slice(),
                Box::new(body.into_inner()),
            ))
        } else {
            None
        };
        let fact = Self {
            function,
            role,
            source,
            origin,
            annotation,
            core_signature,
            call_codec,
        };
        charge(work, 1, source)?;
        fact.authenticate_original(work)?;
        Ok(fact)
    }

    pub(crate) const fn function(&self) -> BinderId {
        self.function
    }
    pub(crate) const fn role(&self) -> ForeignScalarPreflightRole {
        self.role
    }
    pub(crate) fn module(&self) -> ModuleId {
        self.call_codec.module()
    }
    pub(crate) const fn source(&self) -> Span {
        self.source
    }
    pub(crate) fn origin(&self) -> &Origin {
        &self.origin
    }
    pub(crate) fn annotation(&self) -> &ResolvedType {
        &self.annotation
    }
    pub(crate) fn signature(&self) -> &Type {
        &self.annotation.ty
    }
    pub(crate) fn core_signature(&self) -> &Type {
        self.core_signature.as_ref().unwrap_or(&self.annotation.ty)
    }
    pub(crate) fn matches_parameters(&self, parameters: &[(TypeVariableId, Kind)]) -> bool {
        match self.role.byte_parameter(self.module()) {
            Some(parameter) => parameters == [(parameter, Kind::Type)],
            None => parameters.is_empty(),
        }
    }
    pub(crate) fn call_codec(&self) -> &Arc<CheckedForeignCallCodec> {
        &self.call_codec
    }
    pub(crate) fn conversion_error_constructor(&self) -> Option<ConstructorId> {
        Some(ConstructorId::new(
            self.call_codec.ids().conversion_error,
            0,
        ))
    }

    /// Checks exact builtin records without relying on exported display names.
    pub(crate) fn authenticate_original(
        &self,
        work: &mut TypeWorkBudget,
    ) -> Result<(), ForeignAdmissionError> {
        charge(work, 12, self.source)?;
        let invalid = || failure(ForeignAdmissionReason::InvalidSignature, self.source);
        let module = self.module();
        if !module.is_builtin_foreign()
            || self.function != BinderId::resolved(module, self.role.local())
            || self.source != self.call_codec.source()
        {
            return Err(invalid());
        }
        let (name, annotation) =
            crate::module::foreign_scalar_preflight_ranges(self.source, self.role.local())
                .ok_or_else(invalid)?;
        let exact_span = |span: Span, start: u32, end: u32| {
            span.source() == self.source.source()
                && span.range().start() == start
                && span.range().end() == end
        };
        if !matches!(&self.origin, Origin::Source(span) if span.source() == self.source.source() && span.range() == name)
            || self.annotation.span.source() != self.source.source()
            || self.annotation.span.range() != annotation
            || !matches!(&self.annotation.origin, Origin::Source(span) if *span == self.annotation.span)
        {
            return Err(invalid());
        }
        if self.role.byte_parameter(module).is_some() {
            return self.authenticate_byte_annotation(work);
        }
        let Type::Function(domain, codomain) = &self.annotation.ty else {
            return Err(invalid());
        };
        let Type::Application(call, argument) = codomain.as_ref() else {
            return Err(invalid());
        };
        if **domain != Type::Int
            || **argument != Type::Int
            || !matches!(call.as_ref(), Type::Nominal(id) if *id == self.call_codec.ids().call)
        {
            return Err(invalid());
        }
        let start = annotation.start();
        let nodes = self.annotation.provenance.nodes();
        charge(work, 5, self.source)?;
        let Some(ResolvedTypeProvenanceNode::Function {
            span: function,
            domain,
            codomain,
            effect_arguments,
        }) = nodes.get(self.annotation.provenance.root())
        else {
            return Err(invalid());
        };
        let Some(ResolvedTypeProvenanceNode::Fact(domain)) = nodes.get(*domain) else {
            return Err(invalid());
        };
        let Some(ResolvedTypeProvenanceNode::Application {
            span: application,
            function: call,
            argument,
            argument_span,
        }) = nodes.get(*codomain)
        else {
            return Err(invalid());
        };
        let Some(ResolvedTypeProvenanceNode::Fact(call)) = nodes.get(*call) else {
            return Err(invalid());
        };
        let Some(ResolvedTypeProvenanceNode::Fact(argument)) = nodes.get(*argument) else {
            return Err(invalid());
        };
        if !effect_arguments.is_empty()
            || !exact_span(*domain, start, start + 3)
            || !exact_span(*argument, start + 12, start + 15)
            || !exact_span(*call, start + 7, start + 11)
            || !exact_span(*application, start + 7, start + 16)
            || *argument_span != *argument
            || *function != self.annotation.span
        {
            return Err(invalid());
        }
        Ok(())
    }

    fn authenticate_byte_annotation(
        &self,
        work: &mut TypeWorkBudget,
    ) -> Result<(), ForeignAdmissionError> {
        let invalid = || failure(ForeignAdmissionReason::InvalidSignature, self.source);
        let parameter = self
            .role
            .byte_parameter(self.module())
            .ok_or_else(invalid)?;
        let write = self.role == ForeignScalarPreflightRole::ByteWrite;
        let Type::Function(domain, result) = self.signature() else {
            return Err(invalid());
        };
        let Type::Tuple(fields) = domain.as_ref() else {
            return Err(invalid());
        };
        let Type::Application(call, output) = result.as_ref() else {
            return Err(invalid());
        };
        charge(work, 10 + fields.len(), self.source)?;
        if fields.len() != 2 + usize::from(write)
            || fields[0] != Type::Variable(parameter)
            || fields[1..].iter().any(|field| *field != Type::Int)
            || !matches!(call.as_ref(), Type::Nominal(id) if *id == self.call_codec.ids().call)
            || **output != if write { Type::Unit } else { Type::Int }
        {
            return Err(invalid());
        }
        let start = self.annotation.span.range().start();
        let exact = |span: Span, offset: u32, length: u32| {
            span.source() == self.source.source()
                && span.range().start() == start + offset
                && span.range().end() == start + offset + length
        };
        let nodes = self.annotation.provenance.nodes();
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
        let Some(ResolvedTypeProvenanceNode::Application {
            span: application,
            function,
            argument,
            argument_span,
        }) = nodes.get(*codomain)
        else {
            return Err(invalid());
        };
        let offset = if write { 17 } else { 12 };
        if *span != self.annotation.span
            || !effect_arguments.is_empty()
            || !exact(*tuple, 0, if write { 13 } else { 8 })
            || elements.len() != fields.len()
            || !exact(*application, offset, if write { 10 } else { 9 })
            || !matches!(nodes.get(*function), Some(ResolvedTypeProvenanceNode::Fact(span)) if exact(*span,offset,4))
            || !matches!(nodes.get(*argument), Some(ResolvedTypeProvenanceNode::Fact(span)) if exact(*span,offset+5,if write {4} else {3}) && *span == *argument_span)
        {
            return Err(invalid());
        }
        for (index, element) in elements.iter().enumerate() {
            let (offset, length) = if index == 0 {
                (1, 1)
            } else if index == 1 {
                (4, 3)
            } else {
                (9, 3)
            };
            if !matches!(nodes.get(*element), Some(ResolvedTypeProvenanceNode::Fact(span)) if exact(*span,offset,length))
            {
                return Err(invalid());
            }
        }
        Ok(())
    }

    pub(crate) fn authenticate(
        &self,
        registry: &ResolvedRegistry,
        work: &mut TypeWorkBudget,
    ) -> Result<(), ForeignAdmissionError> {
        self.authenticate_original(work)?;
        CheckedForeignCallCodec::authenticate(
            self.module(),
            self.source,
            self.call_codec.ids(),
            registry,
            work,
        )?;
        charge(work, 2, self.source)?;
        let id = self
            .conversion_error_constructor()
            .expect("the canonical error role is fixed");
        if let Some(error) = registry.nominal(id.owner()) {
            if error.constructors.as_ref() != [id] {
                return Err(failure(ForeignAdmissionReason::InvalidCodec, self.source));
            }
            let constructor = registry
                .constructor(id)
                .ok_or_else(|| failure(ForeignAdmissionReason::InvalidCodec, self.source))?;
            if constructor.id != id
                || constructor.owner != id.owner()
                || constructor.payload.is_some()
                || !super::checked_source::origin_within(self.source, &constructor.origin, work)?
            {
                return Err(failure(ForeignAdmissionReason::InvalidCodec, self.source));
            }
        } else if registry.constructor(id).is_some() {
            return Err(failure(ForeignAdmissionReason::InvalidCodec, self.source));
        }
        Ok(())
    }
}
