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
    Nul,
    DataOf,
    ReplaceData,
    CopyBytes,
    CopyNul,
    ExtentValue,
    CheckedByteRead,
    CheckedByteWrite,
    CheckedCopyBytes,
    CheckedCopyNul,
}

impl ForeignScalarPreflightRole {
    pub(crate) const fn local(self) -> u32 {
        match self {
            Self::I64 => 0,
            Self::SizeT => 1,
            Self::ByteRead => 2,
            Self::ByteWrite => 3,
            Self::Nul => 4,
            Self::DataOf => 5,
            Self::ReplaceData => 6,
            Self::CopyBytes => 7,
            Self::CopyNul => 8,
            Self::ExtentValue => 9,
            Self::CheckedByteRead => 11,
            Self::CheckedByteWrite => 12,
            Self::CheckedCopyBytes => 13,
            Self::CheckedCopyNul => 14,
        }
    }

    pub(crate) const fn checked_memory_local(local: u32) -> Option<Self> {
        match local {
            11 => Some(Self::CheckedByteRead),
            12 => Some(Self::CheckedByteWrite),
            13 => Some(Self::CheckedCopyBytes),
            14 => Some(Self::CheckedCopyNul),
            _ => None,
        }
    }

    pub(crate) const fn host_parameter(self, module: ModuleId) -> Option<TypeVariableId> {
        let local = match self {
            Self::CheckedByteRead => 23,
            Self::CheckedByteWrite => 25,
            Self::CheckedCopyBytes => 27,
            Self::CheckedCopyNul => 29,
            _ => return None,
        };
        Some(TypeVariableId::resolved(module, local))
    }

    pub(crate) const fn operation_role(self) -> Self {
        match self {
            Self::CheckedByteRead => Self::ByteRead,
            Self::CheckedByteWrite => Self::ByteWrite,
            Self::CheckedCopyBytes => Self::CopyBytes,
            Self::CheckedCopyNul => Self::CopyNul,
            other => other,
        }
    }

    pub(crate) const fn byte_parameter(self, module: ModuleId) -> Option<TypeVariableId> {
        match self {
            // Five preceding canonical nominal declarations bind one Type formal each.
            Self::ByteRead => Some(TypeVariableId::resolved(module, 5)),
            Self::ByteWrite => Some(TypeVariableId::resolved(module, 6)),
            Self::CheckedByteRead => Some(TypeVariableId::resolved(module, 24)),
            Self::CheckedByteWrite => Some(TypeVariableId::resolved(module, 26)),
            _ => None,
        }
    }

    pub(crate) const fn state_parameter(self, module: ModuleId) -> Option<TypeVariableId> {
        match self {
            Self::DataOf => Some(TypeVariableId::resolved(module, 7)),
            Self::ReplaceData => Some(TypeVariableId::resolved(module, 9)),
            _ => self.byte_parameter(module),
        }
    }

    pub(crate) const fn data_parameter(self, module: ModuleId) -> Option<TypeVariableId> {
        match self {
            Self::DataOf => Some(TypeVariableId::resolved(module, 8)),
            Self::ReplaceData => Some(TypeVariableId::resolved(module, 10)),
            _ => None,
        }
    }

    pub(crate) const fn view_parameter(self, module: ModuleId) -> Option<TypeVariableId> {
        match self {
            Self::CopyBytes => Some(TypeVariableId::resolved(module, 11)),
            Self::CopyNul => Some(TypeVariableId::resolved(module, 12)),
            Self::ExtentValue => Some(TypeVariableId::resolved(module, 13)),
            Self::CheckedCopyBytes => Some(TypeVariableId::resolved(module, 28)),
            Self::CheckedCopyNul => Some(TypeVariableId::resolved(module, 30)),
            _ => None,
        }
    }
    /// Shared quantifier inventory only; State and view permission stay distinct.
    pub(crate) fn borrowed_parameter(self, module: ModuleId) -> Option<TypeVariableId> {
        self.state_parameter(module)
            .or_else(|| self.view_parameter(module))
    }

    pub(crate) fn matches_parameters(
        self,
        module: ModuleId,
        parameters: &[(TypeVariableId, Kind)],
    ) -> bool {
        if let Some(host) = self.host_parameter(module) {
            return self.borrowed_parameter(module).is_some_and(|borrowed| {
                parameters == [(host, Kind::Type), (borrowed, Kind::Type)]
            });
        }
        match (self.borrowed_parameter(module), self.data_parameter(module)) {
            (Some(state), Some(data)) => parameters == [(state, Kind::Type), (data, Kind::Type)],
            (Some(state), None) => parameters == [(state, Kind::Type)],
            _ => parameters.is_empty(),
        }
    }

    pub(crate) fn matches_parameter_ids(
        self,
        module: ModuleId,
        parameters: &[TypeVariableId],
    ) -> bool {
        if let Some(host) = self.host_parameter(module) {
            return self
                .borrowed_parameter(module)
                .is_some_and(|borrowed| parameters == [host, borrowed]);
        }
        match (self.borrowed_parameter(module), self.data_parameter(module)) {
            (Some(state), Some(data)) => parameters == [state, data],
            (Some(state), None) => parameters == [state],
            _ => parameters.is_empty(),
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
        let core_signature = if let Some(parameter) = role.borrowed_parameter(call_codec.module()) {
            let body = crate::types::IterativeTypeOwner::new(
                crate::types::clone_type_with_budget(&annotation.ty, work)
                    .map_err(|()| failure(ForeignAdmissionReason::WorkExhausted, source))?,
            );
            let data = role.data_parameter(call_codec.module());
            let host = role.host_parameter(call_codec.module());
            let count = 1 + usize::from(data.is_some()) + usize::from(host.is_some());
            charge(work, 2 + count, source)?;
            let mut parameters = Vec::new();
            parameters
                .try_reserve_exact(count)
                .map_err(|_| failure(ForeignAdmissionReason::WorkExhausted, source))?;
            if let Some(host) = host {
                parameters.push((host, Kind::Type));
            }
            parameters.push((parameter, Kind::Type));
            if let Some(data) = data {
                parameters.push((data, Kind::Type));
            }
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
        self.role.matches_parameters(self.module(), parameters)
    }
    /// Scheme-kind lookup only: callers must still enforce lexical type scope.
    pub(crate) fn parameter_kind_with_charge<E>(
        &self,
        identity: TypeVariableId,
        mut charge: impl FnMut(usize) -> Result<(), E>,
    ) -> Result<Option<&Kind>, E> {
        let Type::Forall(parameters, _) = self.core_signature() else {
            return Ok(None);
        };
        charge(parameters.len())?;
        // The sealed fact retains its exact defining role, module and complete
        // ordered formals. Never infer kind authority from a builtin namespace.
        if !self.matches_parameters(parameters) {
            return Ok(None);
        }
        Ok(parameters
            .iter()
            .find(|(parameter, _)| *parameter == identity)
            .map(|(_, kind)| kind))
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
        if self.role.host_parameter(module).is_some() {
            return self.authenticate_checked_memory_annotation(work);
        }
        if self.role.view_parameter(module).is_some() {
            return self.authenticate_view_annotation(work);
        }
        if self.role.data_parameter(module).is_some() {
            return self.authenticate_data_annotation(work);
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
        let nul = self.role == ForeignScalarPreflightRole::Nul;
        if **domain != if nul { Type::String } else { Type::Int }
            || **argument != if nul { Type::Unit } else { Type::Int }
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
        let call_offset = if nul { 10 } else { 7 };
        let argument_length = if nul { 4 } else { 3 };
        if !effect_arguments.is_empty()
            || !exact_span(*domain, start, start + if nul { 6 } else { 3 })
            || !exact_span(
                *argument,
                start + call_offset + 5,
                start + call_offset + 5 + argument_length,
            )
            || !exact_span(*call, start + call_offset, start + call_offset + 4)
            || !exact_span(
                *application,
                start + call_offset,
                start + call_offset + 6 + argument_length,
            )
            || *argument_span != *argument
            || *function != self.annotation.span
        {
            return Err(invalid());
        }
        Ok(())
    }

    fn authenticate_view_annotation(
        &self,
        work: &mut TypeWorkBudget,
    ) -> Result<(), ForeignAdmissionError> {
        let invalid = || failure(ForeignAdmissionReason::InvalidSignature, self.source);
        let parameter = self
            .role
            .view_parameter(self.module())
            .ok_or_else(invalid)?;
        let extent = crate::types::NominalTypeId::new(self.module(), 5);
        let is_extent = |ty: &Type| matches!(ty, Type::Application(head, argument) if **head == Type::Nominal(extent) && **argument == Type::Variable(parameter));
        let Type::Function(domain, output) = self.signature() else {
            return Err(invalid());
        };
        charge(work, 15, self.source)?;
        let value = self.role == ForeignScalarPreflightRole::ExtentValue;
        let bytes = self.role == ForeignScalarPreflightRole::CopyBytes;
        if value {
            if !is_extent(domain) || **output != Type::Int {
                return Err(invalid());
            }
        } else {
            let Type::Tuple(fields) = domain.as_ref() else {
                return Err(invalid());
            };
            if fields.len() != 2
                || fields[0] != Type::Variable(parameter)
                || if bytes {
                    !is_extent(&fields[1])
                } else {
                    fields[1] != Type::Int
                }
                || !matches!(output.as_ref(), Type::Application(call, payload) if **call == Type::Nominal(self.call_codec.ids().call) && **payload == Type::Bytes)
            {
                return Err(invalid());
            }
        }
        let start = self.annotation.span.range().start();
        let exact = |span: Span, offset: u32, length: u32| {
            span.source() == self.source.source()
                && span.range().start() == start + offset
                && span.range().end() == start + offset + length
        };
        let nodes = self.annotation.provenance.nodes();
        let fact = |id: usize, offset, length| matches!(nodes.get(id), Some(ResolvedTypeProvenanceNode::Fact(span)) if exact(*span, offset, length));
        let application = |id: usize, offset, name_length, argument_length| {
            matches!(nodes.get(id), Some(ResolvedTypeProvenanceNode::Application { span, function, argument, argument_span })
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
        if *span != self.annotation.span || !effect_arguments.is_empty() {
            return Err(invalid());
        }
        if value {
            if !application(*domain, 0, 6, 1) || !fact(*codomain, 13, 3) {
                return Err(invalid());
            }
        } else {
            let Some(ResolvedTypeProvenanceNode::Tuple { span, elements }) = nodes.get(*domain)
            else {
                return Err(invalid());
            };
            if !exact(*span, 0, if bytes { 14 } else { 8 })
                || elements.len() != 2
                || !fact(elements[0], 1, 1)
                || if bytes {
                    !application(elements[1], 4, 6, 1)
                } else {
                    !fact(elements[1], 4, 3)
                }
                || !application(*codomain, if bytes { 18 } else { 12 }, 4, 5)
            {
                return Err(invalid());
            }
        }
        Ok(())
    }

    fn authenticate_data_annotation(
        &self,
        work: &mut TypeWorkBudget,
    ) -> Result<(), ForeignAdmissionError> {
        let invalid = || failure(ForeignAdmissionReason::InvalidSignature, self.source);
        let state = self
            .role
            .state_parameter(self.module())
            .ok_or_else(invalid)?;
        let data = self
            .role
            .data_parameter(self.module())
            .ok_or_else(invalid)?;
        let replace = self.role == ForeignScalarPreflightRole::ReplaceData;
        let Type::Function(domain, output) = self.signature() else {
            return Err(invalid());
        };
        charge(work, 8, self.source)?;
        if replace {
            if !matches!(domain.as_ref(), Type::Tuple(fields) if fields.as_ref() == [Type::Variable(state), Type::Variable(data)])
                || **output != Type::Unit
            {
                return Err(invalid());
            }
        } else if **domain != Type::Variable(state) || **output != Type::Variable(data) {
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
        if *span != self.annotation.span
            || !effect_arguments.is_empty()
            || !matches!(nodes.get(*codomain), Some(ResolvedTypeProvenanceNode::Fact(span)) if exact(*span, if replace {10} else {5}, if replace {4} else {1}))
        {
            return Err(invalid());
        }
        if replace {
            let Some(ResolvedTypeProvenanceNode::Tuple { span, elements }) = nodes.get(*domain)
            else {
                return Err(invalid());
            };
            if !exact(*span, 0, 6) || elements.len() != 2 {
                return Err(invalid());
            }
            for (index, element) in elements.iter().enumerate() {
                if !matches!(nodes.get(*element), Some(ResolvedTypeProvenanceNode::Fact(span)) if exact(*span, if index == 0 {1} else {4}, 1))
                {
                    return Err(invalid());
                }
            }
        } else if !matches!(nodes.get(*domain), Some(ResolvedTypeProvenanceNode::Fact(span)) if exact(*span,0,1))
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
        self.authenticate_registry_projection(registry, work)
    }

    // Only the whole-table entry below shares a codec proof. Standalone fact
    // admission above always reconstructs that proof in the actual registry.
    fn authenticate_registry_projection(
        &self,
        registry: &ResolvedRegistry,
        work: &mut TypeWorkBudget,
    ) -> Result<(), ForeignAdmissionError> {
        if self.role.host_parameter(self.module()).is_some() {
            charge(work, 1, self.source)?;
            let host = registry
                .effect(crate::types::EffectId::new(
                    self.module(),
                    crate::module::FOREIGN_NATIVE_HOST_LOCAL,
                ))
                .ok_or_else(|| failure(ForeignAdmissionReason::InvalidSignature, self.source))?;
            // The fresh checked codec proof above (or this table's identical
            // family proof) already authenticated the full builtin inventory.
            // Recheck this row's Host declaration/formal projection without
            // repeating that same complete inventory walk.
            if !super::checked_builtins::host_matches(
                host,
                registry,
                self.module(),
                self.source,
                work,
            )? {
                return Err(failure(
                    ForeignAdmissionReason::InvalidSignature,
                    self.source,
                ));
            }
        }
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

/// Authenticate this immutable registry table, sharing only identical codec
/// reconstruction within this call. No completed proof escapes the operation.
pub(crate) fn authenticate_registry_families(
    registry: &ResolvedRegistry,
    work: &mut TypeWorkBudget,
) -> Result<(), ForeignAdmissionError> {
    let mut proved = Vec::<BinderId>::new();
    for (function, fact) in registry.scalar_preflights() {
        charge(work, 1, fact.source)?;
        if function != fact.function() {
            return Err(failure(
                ForeignAdmissionReason::InvalidSignature,
                fact.source,
            ));
        }
        fact.authenticate_original(work)?;
        let anchor = BinderId::resolved(
            fact.module(),
            if fact.role.host_parameter(fact.module()).is_some() {
                11
            } else {
                0
            },
        );
        charge(work, 1, fact.source)?;
        let common = registry
            .scalar_preflight(anchor)
            .ok_or_else(|| failure(ForeignAdmissionReason::InvalidSignature, fact.source))?;
        if common.function() != anchor || !Arc::ptr_eq(common.call_codec(), fact.call_codec()) {
            return Err(failure(
                ForeignAdmissionReason::InvalidSignature,
                fact.source,
            ));
        }
        charge(work, proved.len(), fact.source)?;
        let fresh = !proved.contains(&anchor);
        if fresh {
            CheckedForeignCallCodec::authenticate(
                fact.module(),
                fact.source,
                fact.call_codec.ids(),
                registry,
                work,
            )?;
        }
        // Every row still authenticates its own Host and ConversionError
        // projections; the common codec proof alone is shared.
        fact.authenticate_registry_projection(registry, work)?;
        if fresh {
            charge(work, 1, fact.source)?;
            proved
                .try_reserve(1)
                .map_err(|_| failure(ForeignAdmissionReason::StorageRefused, fact.source))?;
            proved.push(anchor);
        }
    }
    Ok(())
}

mod checked_memory;
