//! Canonical source owner facts; these do not grant an executable activation.

use std::{collections::HashSet, sync::Arc};

use super::{
    checked_source::{
        CheckedForeignCallCodec, ForeignAdmissionError, ForeignAdmissionReason, NativeLibraryId,
        charge, check_domain, check_source_path, failure, names_match, origin_within, primary_span,
    },
    source_contract::{
        PreparedAbiResult, PreparedForeignLibrary, PreparedForeignOwner, PreparedForeignSymbol,
        PreparedOperandSource, PreparedOwnerApplication, PreparedOwnerArgument, PreparedOwnerCall,
        PreparedRepresentation,
    },
};
use crate::{
    module::ModuleId,
    resolved::{
        CanonicalNominalKind, ResolvedEffectDeclaration, ResolvedNominalDeclarationKind,
        ResolvedRegistry, ResolvedTypeVariable, SharedOwnerParameters,
        clone_resolved_type_variables_with_budget, same_origin_with_budget,
    },
    source::Span,
    types::{ConstructorId, Kind, NominalTypeId, Type, TypeVariableId, TypeWorkBudget},
};

/// Immutable owner identity and original authored assumptions, without runtime permission.
#[derive(Debug)]
pub struct CheckedForeignOwner {
    library: NativeLibraryId,
    prepared: Arc<PreparedForeignLibrary>,
    owner_index: usize,
    nominal: NominalTypeId,
    parameter_ids: Box<[TypeVariableId]>,
    parameters: SharedOwnerParameters,
}

impl PartialEq for CheckedForeignOwner {
    fn eq(&self, other: &Self) -> bool {
        self.library == other.library
            && self.owner_index == other.owner_index
            && self.nominal == other.nominal
            && self.parameter_ids == other.parameter_ids
            && Arc::ptr_eq(&self.prepared, &other.prepared)
    }
}
impl Eq for CheckedForeignOwner {}

impl CheckedForeignOwner {
    pub(crate) const fn library(&self) -> NativeLibraryId {
        self.library
    }
    pub(crate) fn prepared(&self) -> &Arc<PreparedForeignLibrary> {
        &self.prepared
    }
    pub(crate) const fn owner_index(&self) -> usize {
        self.owner_index
    }
    pub(crate) fn owner(&self) -> &PreparedForeignOwner {
        &self.prepared.owners()[self.owner_index]
    }
    pub(crate) const fn nominal(&self) -> NominalTypeId {
        self.nominal
    }
    pub(crate) fn parameter_ids(&self) -> &[TypeVariableId] {
        &self.parameter_ids
    }
    pub(crate) fn parameters(&self) -> &SharedOwnerParameters {
        &self.parameters
    }
    pub(crate) fn owned_parameter(&self) -> usize {
        self.owner().owned_parameter()
    }
}

/// Checks the original owner declaration against its constructor-free canonical nominal.
///
/// This checkpoint admits Type-only owner families. Row-bearing owner preparation
/// remains passive; a row must not be erased to make an ordinary Type application.
pub(crate) fn bind_foreign_owner(
    library: NativeLibraryId,
    prepared: Arc<PreparedForeignLibrary>,
    owner_index: usize,
    nominal: NominalTypeId,
    parameters: &[ResolvedTypeVariable],
    registry: &ResolvedRegistry,
    work: &mut TypeWorkBudget,
) -> Result<CheckedForeignOwner, ForeignAdmissionError> {
    let (ids, span) = owner_parameter_ids(
        library.module(),
        &prepared,
        owner_index,
        nominal,
        parameters,
        registry,
        work,
    )?;
    let parameters = clone_resolved_type_variables_with_budget(parameters, work)
        .map_err(|()| failure(ForeignAdmissionReason::WorkExhausted, span))?;
    let parameters =
        SharedOwnerParameters::from_boxed_with_budget(parameters.into_boxed_slice(), work)
            .map_err(|_| failure(ForeignAdmissionReason::WorkExhausted, span))?;
    Ok(CheckedForeignOwner {
        library,
        prepared,
        owner_index,
        nominal,
        parameter_ids: ids.into_boxed_slice(),
        parameters,
    })
}

/// Independently checks a passive original owner candidate without creating an
/// executable owner, library identity or native symbol receipt.
pub(crate) fn authenticate_source_owner_candidate(
    prepared: &PreparedForeignLibrary,
    owner_index: usize,
    nominal: NominalTypeId,
    parameters: &[ResolvedTypeVariable],
    registry: &ResolvedRegistry,
    work: &mut TypeWorkBudget,
) -> Result<(), ForeignAdmissionError> {
    owner_parameter_ids(
        prepared.module(),
        prepared,
        owner_index,
        nominal,
        parameters,
        registry,
        work,
    )?;
    Ok(())
}

fn owner_parameter_ids(
    library_module: ModuleId,
    prepared: &PreparedForeignLibrary,
    owner_index: usize,
    nominal: NominalTypeId,
    parameters: &[ResolvedTypeVariable],
    registry: &ResolvedRegistry,
    work: &mut TypeWorkBudget,
) -> Result<(Vec<TypeVariableId>, Span), ForeignAdmissionError> {
    let span = primary_span(prepared.origin(), work, prepared.origin().primary_span())?;
    charge(work, 4, span)?;
    let owner = prepared
        .owners()
        .get(owner_index)
        .ok_or_else(|| failure(ForeignAdmissionReason::InvalidLibrary, span))?;
    let span = primary_span(owner.origin(), work, span)?;
    if library_module != prepared.module()
        || nominal.module() != prepared.module()
        || parameters.len() != owner.parameters().len()
        || owner.owned_parameter() >= parameters.len()
    {
        return Err(failure(ForeignAdmissionReason::InvalidParameters, span));
    }
    let original = registry
        .nominal(nominal)
        .ok_or_else(|| failure(ForeignAdmissionReason::InvalidSignature, span))?;
    charge(work, original.constructors.len().saturating_add(3), span)?;
    if original.declaration_kind != ResolvedNominalDeclarationKind::Data
        || !original.constructors.is_empty()
        || original.representation.is_some()
        || original.representation_provenance.is_some()
        || !same_origin_with_budget(&original.origin, owner.origin(), work)
            .map_err(|()| failure(ForeignAdmissionReason::WorkExhausted, span))?
        || !names_match(&original.spelling, owner.name(), work, span)?
    {
        return Err(failure(ForeignAdmissionReason::InvalidSignature, span));
    }
    let Some(CanonicalNominalKind::Parameters {
        parameters: canonical,
        ..
    }) = registry.nominal_kind(nominal)
    else {
        return Err(failure(ForeignAdmissionReason::InvalidParameters, span));
    };
    if canonical.len() != parameters.len() {
        return Err(failure(ForeignAdmissionReason::InvalidParameters, span));
    }
    charge(
        work,
        parameters
            .len()
            .checked_mul(2)
            .ok_or_else(|| failure(ForeignAdmissionReason::WorkExhausted, span))?,
        span,
    )?;
    let mut ids = Vec::new();
    ids.try_reserve_exact(parameters.len())
        .map_err(|_| failure(ForeignAdmissionReason::StorageRefused, span))?;
    let mut seen = HashSet::new();
    seen.try_reserve(parameters.len())
        .map_err(|_| failure(ForeignAdmissionReason::StorageRefused, span))?;
    for ((parameter, canonical), source) in parameters.iter().zip(canonical).zip(owner.parameters())
    {
        charge(work, 3, span)?;
        let parameter_span = primary_span(source.origin(), work, span)?;
        if source.kind() != &Kind::Type
            || parameter.kind != Kind::Type
            || parameter.id != canonical.id
            || canonical.kind != Kind::Type
            || parameter.id.module() != Some(nominal.module())
            || !seen.insert(parameter.id)
            || !names_match(&parameter.spelling, source.name(), work, parameter_span)?
            || !same_origin_with_budget(&parameter.origin, &canonical.origin, work)
                .map_err(|()| failure(ForeignAdmissionReason::WorkExhausted, span))?
            || !origin_within(parameter_span, &parameter.origin, work)?
        {
            return Err(failure(
                ForeignAdmissionReason::InvalidParameters,
                parameter_span,
            ));
        }
        ids.push(parameter.id);
    }
    Ok((ids, span))
}

/// Exact common owner-result roles from the original compiler-owned module.
#[derive(Debug, Eq, PartialEq)]
pub(crate) struct CheckedForeignOwnerCodec {
    output: NominalTypeId,
    nullable: NominalTypeId,
    disposition: NominalTypeId,
    output_constructors: [ConstructorId; 2],
    nullable_constructors: [ConstructorId; 2],
    disposition_constructors: [ConstructorId; 3],
}

impl CheckedForeignOwnerCodec {
    pub(crate) const fn output_constructors(&self) -> &[ConstructorId; 2] {
        &self.output_constructors
    }
    pub(crate) const fn nullable_constructors(&self) -> &[ConstructorId; 2] {
        &self.nullable_constructors
    }
    pub(crate) const fn disposition_constructors(&self) -> &[ConstructorId; 3] {
        &self.disposition_constructors
    }

    pub(crate) fn authenticate(
        module: ModuleId,
        source: Span,
        registry: &ResolvedRegistry,
        work: &mut TypeWorkBudget,
    ) -> Result<Self, ForeignAdmissionError> {
        if !module.is_builtin_foreign() {
            return Err(failure(ForeignAdmissionReason::InvalidCodec, source));
        }
        for (ordinal, payloads) in [
            (2, &[false, true][..]),
            (3, &[false, true][..]),
            (4, &[true, true, false][..]),
        ] {
            let id = NominalTypeId::new(module, ordinal);
            charge(work, payloads.len().saturating_add(3), source)?;
            let invalid = || failure(ForeignAdmissionReason::InvalidCodec, source);
            let nominal = registry.nominal(id).ok_or_else(invalid)?;
            let [parameter] = registry.nominal_parameters(id).ok_or_else(invalid)? else {
                return Err(invalid());
            };
            if nominal.declaration_kind != ResolvedNominalDeclarationKind::Data
                || nominal.representation.is_some()
                || nominal.representation_provenance.is_some()
                || nominal.constructors.len() != payloads.len()
                || parameter.kind != Kind::Type
                || !origin_within(source, &nominal.origin, work)?
                || !origin_within(source, &parameter.origin, work)?
            {
                return Err(invalid());
            }
            for (position, has_payload) in payloads.iter().enumerate() {
                let constructor = ConstructorId::new(id, position as u32);
                let original = registry.constructor(constructor).ok_or_else(invalid)?;
                if nominal.constructors[position] != constructor
                    || original.owner != id
                    || !origin_within(source, &original.origin, work)?
                    || match original.payload.as_ref() {
                        Some(Type::Variable(variable)) => !has_payload || *variable != parameter.id,
                        None => *has_payload,
                        _ => true,
                    }
                {
                    return Err(invalid());
                }
            }
        }
        let output = NominalTypeId::new(module, 2);
        let nullable = NominalTypeId::new(module, 3);
        let disposition = NominalTypeId::new(module, 4);
        Ok(Self {
            output,
            nullable,
            disposition,
            output_constructors: [ConstructorId::new(output, 0), ConstructorId::new(output, 1)],
            nullable_constructors: [
                ConstructorId::new(nullable, 0),
                ConstructorId::new(nullable, 1),
            ],
            disposition_constructors: [
                ConstructorId::new(disposition, 0),
                ConstructorId::new(disposition, 1),
                ConstructorId::new(disposition, 2),
            ],
        })
    }
}

fn unary_payload<'a>(
    ty: &'a Type,
    nominal: NominalTypeId,
    span: Span,
    work: &mut TypeWorkBudget,
) -> Result<&'a Type, ForeignAdmissionError> {
    charge(work, 2, span)?;
    match ty {
        Type::Application(head, payload) if matches!(head.as_ref(), Type::Nominal(id) if *id == nominal) => {
            Ok(payload)
        }
        _ => Err(failure(ForeignAdmissionReason::InvalidSignature, span)),
    }
}

fn check_state_application(
    state: &Type,
    owner: &CheckedForeignOwner,
    application: &PreparedOwnerApplication,
    effect: &ResolvedEffectDeclaration,
    work: &mut TypeWorkBudget,
) -> Result<(), ForeignAdmissionError> {
    let span = application.span();
    charge(work, application.arguments().len().saturating_add(2), span)?;
    if application.owner() != owner.owner_index()
        || application.arguments().len() != owner.parameter_ids().len()
    {
        return Err(failure(ForeignAdmissionReason::InvalidParameters, span));
    }
    let mut remaining = state;
    for argument in application.arguments().iter().rev() {
        let PreparedOwnerArgument::Type(position) = argument else {
            return Err(failure(ForeignAdmissionReason::InvalidParameters, span));
        };
        let parameter = effect
            .parameters
            .get(*position)
            .ok_or_else(|| failure(ForeignAdmissionReason::InvalidParameters, span))?;
        let Type::Application(head, actual) = remaining else {
            return Err(failure(ForeignAdmissionReason::InvalidSignature, span));
        };
        if parameter.kind != Kind::Type || actual.as_ref() != &Type::Variable(parameter.id) {
            return Err(failure(ForeignAdmissionReason::InvalidParameters, span));
        }
        remaining = head;
    }
    if remaining != &Type::Nominal(owner.nominal()) {
        return Err(failure(ForeignAdmissionReason::InvalidSignature, span));
    }
    Ok(())
}

fn source_leaf<'a>(
    domain: &'a Type,
    path: &[usize],
    span: Span,
    work: &mut TypeWorkBudget,
) -> Result<&'a Type, ForeignAdmissionError> {
    charge(work, path.len().saturating_add(1), span)?;
    let invalid = || failure(ForeignAdmissionReason::InvalidSourcePosition, span);
    let (first, rest) = path.split_first().ok_or_else(invalid)?;
    let mut selected = match domain {
        Type::Tuple(fields) => fields.get(*first),
        _ if *first == 0 => Some(domain),
        _ => None,
    }
    .ok_or_else(invalid)?;
    for position in rest {
        selected = match selected {
            Type::Tuple(fields) => fields.get(*position),
            _ => None,
        }
        .ok_or_else(invalid)?;
    }
    Ok(selected)
}

/// Authenticate a nonowning enclosing state against its original constructor-
/// free declaration and this output owner's explicit retained identity roles.
/// Compatible nominal shapes or an ordinary Type variable do not grant a borrow.
pub(crate) fn enclosing_identity(
    state: &Type,
    owner: &CheckedForeignOwner,
    application: &PreparedOwnerApplication,
    effect: &ResolvedEffectDeclaration,
    registry: &ResolvedRegistry,
    span: Span,
    work: &mut TypeWorkBudget,
) -> Result<TypeVariableId, ForeignAdmissionError> {
    let mut arguments = Vec::new();
    let mut head = state;
    while let Type::Application(function, argument) = head {
        charge(work, 1, span)?;
        arguments
            .try_reserve(1)
            .map_err(|_| failure(ForeignAdmissionReason::StorageRefused, span))?;
        arguments.push(argument.as_ref());
        head = function;
    }
    arguments.reverse();
    let Type::Nominal(nominal) = head else {
        return Err(failure(ForeignAdmissionReason::InvalidSignature, span));
    };
    charge(work, registry.source_owner_candidate_count(), span)?;
    let (prepared, index, _, parameters) = registry
        .source_owner_candidates()
        .find(|(_, _, candidate, _)| candidate == nominal)
        .ok_or_else(|| failure(ForeignAdmissionReason::InvalidSignature, span))?;
    authenticate_source_owner_candidate(prepared, index, *nominal, parameters, registry, work)?;
    let enclosing = &prepared.owners()[index];
    if arguments.len() != parameters.len() {
        return Err(failure(ForeignAdmissionReason::InvalidParameters, span));
    }
    let Some(Type::Variable(identity)) = arguments.get(enclosing.owned_parameter()).copied() else {
        return Err(failure(ForeignAdmissionReason::InvalidParameters, span));
    };
    charge(work, owner.owner().retained_parameters().len(), span)?;
    for retained in owner.owner().retained_parameters() {
        let Some(PreparedOwnerArgument::Type(position)) = application.arguments().get(*retained)
        else {
            return Err(failure(ForeignAdmissionReason::InvalidParameters, span));
        };
        let parameter = effect
            .parameters
            .get(*position)
            .ok_or_else(|| failure(ForeignAdmissionReason::InvalidParameters, span))?;
        if parameter.kind == Kind::Type && parameter.id == *identity {
            return Ok(*identity);
        }
    }
    Err(failure(ForeignAdmissionReason::InvalidParameters, span))
}

#[allow(
    clippy::too_many_arguments,
    reason = "original owner, application and full declaration actuals remain separate from domain traversal"
)]
fn owner_domain(
    domain: &Type,
    current: Option<&Type>,
    owner: &CheckedForeignOwner,
    application: &PreparedOwnerApplication,
    effect: &ResolvedEffectDeclaration,
    parameters: &HashSet<TypeVariableId>,
    registry: &ResolvedRegistry,
    span: Span,
    work: &mut TypeWorkBudget,
) -> Result<(), ForeignAdmissionError> {
    let mut pending = Vec::new();
    charge(work, 1, span)?;
    pending
        .try_reserve(1)
        .map_err(|_| failure(ForeignAdmissionReason::StorageRefused, span))?;
    pending.push(domain);
    while let Some(ty) = pending.pop() {
        charge(work, 1, span)?;
        if current.is_some_and(|current| std::ptr::eq(ty, current)) {
            continue;
        }
        if let Type::Tuple(fields) = ty {
            if fields.len() < 2 {
                return Err(failure(ForeignAdmissionReason::InvalidSignature, span));
            }
            charge(work, fields.len(), span)?;
            pending
                .try_reserve(fields.len())
                .map_err(|_| failure(ForeignAdmissionReason::StorageRefused, span))?;
            pending.extend(fields.iter());
        } else if matches!(ty, Type::Application(_, _)) {
            enclosing_identity(ty, owner, application, effect, registry, span, work)?;
        } else {
            check_domain(ty, parameters, registry, work, span)?;
        }
    }
    Ok(())
}

/// Reconstructs canonical native owner replies and every mapped source leaf.
// The owner, reply codecs and original registry are independently checked inputs.
#[allow(clippy::too_many_arguments)]
pub(super) fn validate_owner_symbol(
    library: NativeLibraryId,
    prepared: &PreparedForeignLibrary,
    symbol: &PreparedForeignSymbol,
    effect: &ResolvedEffectDeclaration,
    owner: &CheckedForeignOwner,
    codec: &CheckedForeignOwnerCodec,
    call_codec: &CheckedForeignCallCodec,
    registry: &ResolvedRegistry,
    work: &mut TypeWorkBudget,
) -> Result<(), ForeignAdmissionError> {
    let span = effect.span;
    charge(work, 3, span)?;
    if library != owner.library() || !std::ptr::eq(prepared, owner.prepared().as_ref()) {
        return Err(failure(ForeignAdmissionReason::InvalidLibrary, span));
    }
    let canonical_codec = CheckedForeignOwnerCodec::authenticate(
        call_codec.module(),
        call_codec.source(),
        registry,
        work,
    )?;
    if codec != &canonical_codec {
        return Err(failure(ForeignAdmissionReason::InvalidCodec, span));
    }
    // Owner candidates preserve the defining binder vector through checker views.
    charge(work, registry.source_owner_candidate_count(), span)?;
    let (nominal, parameters) = registry
        .source_owner_candidate(owner.prepared(), owner.owner_index())
        .ok_or_else(|| failure(ForeignAdmissionReason::InvalidParameters, span))?;
    if nominal != owner.nominal() || parameters.len() != owner.parameter_ids().len() {
        return Err(failure(ForeignAdmissionReason::InvalidParameters, span));
    }
    charge(work, parameters.len(), span)?;
    for ((parameter, id), original) in parameters
        .iter()
        .zip(owner.parameter_ids())
        .zip(owner.owner().parameters())
    {
        let parameter_span = primary_span(original.origin(), work, span)?;
        if parameter.id != *id
            || parameter.kind != Kind::Type
            || original.kind() != &Kind::Type
            || !names_match(&parameter.spelling, original.name(), work, parameter_span)?
            || !origin_within(parameter_span, &parameter.origin, work)?
        {
            return Err(failure(ForeignAdmissionReason::InvalidParameters, span));
        }
    }
    charge(work, 1, span)?;
    let owner_span = primary_span(owner.owner().origin(), work, span)?;
    match registry.nominal_kind(owner.nominal()) {
        Some(CanonicalNominalKind::Parameters {
            parameters: current,
            origin,
        }) if origin == owner_span && current.len() == parameters.len() => {
            charge(work, current.len(), span)?;
            if current
                .iter()
                .zip(parameters)
                .any(|(left, right)| left.id != right.id || left.kind != Kind::Type)
            {
                return Err(failure(ForeignAdmissionReason::InvalidParameters, span));
            }
            let nominal = registry
                .nominal(owner.nominal())
                .ok_or_else(|| failure(ForeignAdmissionReason::InvalidSignature, span))?;
            if nominal.declaration_kind != ResolvedNominalDeclarationKind::Data
                || !nominal.constructors.is_empty()
                || nominal.representation.is_some()
                || nominal.representation_provenance.is_some()
            {
                return Err(failure(ForeignAdmissionReason::InvalidSignature, span));
            }
        }
        Some(CanonicalNominalKind::Frozen { kind, origin }) if origin == owner_span => {
            // Import opacity retains kind and original declaration provenance;
            // the canonical owner fact supplies the defining formal records.
            charge(work, parameters.len().saturating_add(1), span)?;
            let mut remaining = kind;
            for _ in parameters {
                let Kind::Arrow(argument, result) = remaining else {
                    return Err(failure(ForeignAdmissionReason::InvalidParameters, span));
                };
                if argument.as_ref() != &Kind::Type {
                    return Err(failure(ForeignAdmissionReason::InvalidParameters, span));
                }
                remaining = result;
            }
            if remaining != &Kind::Type {
                return Err(failure(ForeignAdmissionReason::InvalidParameters, span));
            }
        }
        _ => return Err(failure(ForeignAdmissionReason::InvalidParameters, span)),
    }
    let Type::Function(domain, codomain) = &effect.operations[0].annotation.ty else {
        return Err(failure(ForeignAdmissionReason::InvalidSignature, span));
    };
    let payload = unary_payload(codomain, call_codec.ids().call, span, work)?;
    let mut formal_ids = HashSet::new();
    charge(work, effect.parameters.len(), span)?;
    formal_ids
        .try_reserve(effect.parameters.len())
        .map_err(|_| failure(ForeignAdmissionReason::StorageRefused, span))?;
    formal_ids.extend(effect.parameters.iter().map(|parameter| parameter.id));
    let current = match symbol
        .owner_call()
        .ok_or_else(|| failure(ForeignAdmissionReason::InvalidSignature, span))?
    {
        PreparedOwnerCall::Acquire {
            application,
            initialized_bytes,
            ..
        } => {
            if symbol.result() != PreparedAbiResult::Address(owner.owner().representation()) {
                return Err(failure(ForeignAdmissionReason::InvalidSignature, span));
            }
            let output = unary_payload(payload, codec.output, span, work)?;
            let state = unary_payload(output, codec.nullable, span, work)?;
            check_state_application(state, owner, application, effect, work)?;
            owner_domain(
                domain,
                None,
                owner,
                application,
                effect,
                &formal_ids,
                registry,
                span,
                work,
            )?;
            if let Some(initialized) = initialized_bytes {
                check_source_path(domain, initialized.extent(), work, initialized.span())?;
            }
            None
        }
        PreparedOwnerCall::Teardown {
            application,
            current_operand,
            ..
        } => {
            if symbol.result() != PreparedAbiResult::Void
                || unary_payload(payload, codec.disposition, span, work)? != &Type::Unit
            {
                return Err(failure(ForeignAdmissionReason::InvalidSignature, span));
            }
            let operand = symbol
                .operands()
                .get(*current_operand)
                .ok_or_else(|| failure(ForeignAdmissionReason::InvalidSourcePosition, span))?;
            let PreparedOperandSource::Current(path) = operand.source() else {
                return Err(failure(ForeignAdmissionReason::InvalidSourcePosition, span));
            };
            let state = source_leaf(domain, path, span, work)?;
            check_state_application(state, owner, application, effect, work)?;
            owner_domain(
                domain,
                Some(state),
                owner,
                application,
                effect,
                &formal_ids,
                registry,
                span,
                work,
            )?;
            Some(*current_operand)
        }
    };
    charge(work, symbol.operands().len(), span)?;
    for (index, operand) in symbol.operands().iter().enumerate() {
        match (operand.source(), operand.representation()) {
            (PreparedOperandSource::Source(path), PreparedRepresentation::Scalar(_)) => {
                check_source_path(domain, path, work, span)?
            }
            (
                PreparedOperandSource::Enclosing(path),
                PreparedRepresentation::Address(representation),
            ) => {
                let state = source_leaf(domain, path, span, work)?;
                let application = match symbol.owner_call().expect("checked owner role") {
                    PreparedOwnerCall::Acquire { application, .. }
                    | PreparedOwnerCall::Teardown { application, .. } => application,
                };
                enclosing_identity(state, owner, application, effect, registry, span, work)?;
                let mut head = state;
                while let Type::Application(function, _) = head {
                    charge(work, 1, span)?;
                    head = function;
                }
                let Type::Nominal(nominal) = head else {
                    return Err(failure(ForeignAdmissionReason::InvalidSignature, span));
                };
                charge(work, registry.source_owner_candidate_count(), span)?;
                let (prepared, index, _, _) = registry
                    .source_owner_candidates()
                    .find(|(_, _, candidate, _)| candidate == nominal)
                    .ok_or_else(|| failure(ForeignAdmissionReason::InvalidSignature, span))?;
                if representation != prepared.owners()[index].representation() {
                    return Err(failure(ForeignAdmissionReason::InvalidSignature, span));
                }
            }
            (
                PreparedOperandSource::Current(_),
                PreparedRepresentation::Address(representation),
            ) if current == Some(index) && representation == owner.owner().representation() => {}
            _ => return Err(failure(ForeignAdmissionReason::InvalidSignature, span)),
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::bind_foreign_owner;
    use crate::{
        foreign::{checked_source::NativeLibraryId, source_contract::PreparedForeignLibrary},
        module::ModuleId,
        resolved::{ResolvedRegistry, ResolvedTypeVariable},
        types::{Kind, NominalTypeId, TypeVariableId, TypeWorkBudget},
    };
    use crate::{
        lexer::lex,
        parser::{parse, project_module},
        resolved::{ResolvedNominalDeclarationKind, ResolvedNominalType},
        source::{Origin, SourceFile},
    };
    use std::sync::Arc;

    const SOURCE: &str = r#"foreign library Memory {
        profile "x86_64-unknown-linux-gnu"
        repr Size = size_t
        repr Address = opaque
        owner State<T, R> {
            representation Address
            owned R
            teardown Free
        }
        symbol Allocate<Delta : EffectRow, R, T> : Int -> Foreign.Call<Foreign.Output<Foreign.Nullable<State<T, R>>>> {
            name "malloc"
            abi (Size) -> pointer(Address)
            operand 0 from 0 scalar
            output result as owner(State<T, R>)
            outcome result nonnull { readable result }
            outcome otherwise { readable result }
        }
        symbol Free<T, Delta : EffectRow, R> : State<T, R> -> Foreign.Call<Foreign.Disposition<Unit>> {
            name "free"
            abi (pointer(Address)) -> void
            operand 0 from 0 current
            retained_dependents block
            outcome otherwise { consumed 0 }
        }
    }
"#;

    fn fixture() -> (Arc<PreparedForeignLibrary>, NominalTypeId, ResolvedRegistry) {
        let source = SourceFile::new("source-owner.ash", SOURCE).unwrap();
        let module = project_module(&source, &parse(lex(&source).unwrap())).unwrap();
        let id = ModuleId::from(source.id());
        let prepared = Arc::new(
            super::super::source_contract::prepare_foreign_library(
                id,
                &module.foreign_libraries[0],
            )
            .unwrap(),
        );
        let owner = &module.foreign_libraries[0].members[3];
        let crate::surface::SurfaceForeignMember::Owner(owner) = owner else {
            panic!("owner")
        };
        let nominal = NominalTypeId::new(id, 0);
        let parameters = owner
            .parameters
            .iter()
            .enumerate()
            .map(|(index, parameter)| ResolvedTypeVariable {
                id: TypeVariableId::resolved(id, index as u32),
                spelling: parameter.name.text.clone(),
                kind: Kind::Type,
                origin: Origin::Source(parameter.name.span),
            })
            .collect::<Vec<_>>();
        let registry = ResolvedRegistry::new(
            vec![ResolvedNominalType {
                id: nominal,
                declaration_kind: ResolvedNominalDeclarationKind::Data,
                spelling: owner.name.text.clone(),
                constructors: Box::new([]),
                representation: None,
                representation_provenance: None,
                origin: Origin::Source(owner.span),
            }],
            vec![],
        )
        .with_type_parameters(vec![(nominal, parameters)]);
        (prepared, nominal, registry)
    }

    #[test]
    fn owner_admission_preserves_original_member_and_nonfirst_owned_position() {
        let (prepared, nominal, registry) = fixture();
        let mut work = TypeWorkBudget::default();
        let bound = bind_foreign_owner(
            NativeLibraryId::new(prepared.module(), 0),
            Arc::clone(&prepared),
            0,
            nominal,
            registry.nominal_parameters(nominal).unwrap(),
            &registry,
            &mut work,
        )
        .unwrap();
        assert!(Arc::ptr_eq(bound.prepared(), &prepared));
        assert_eq!(bound.nominal(), nominal);
        assert_eq!(bound.owner().member_index(), 3);
        assert_eq!(bound.owned_parameter(), 1);
        assert_eq!(bound.owner().teardown_member(), 5);
        assert_eq!(bound.parameter_ids().len(), 2);
        let exact = work.used();
        assert!(
            bind_foreign_owner(
                bound.library(),
                Arc::clone(&prepared),
                0,
                nominal,
                registry.nominal_parameters(nominal).unwrap(),
                &registry,
                &mut TypeWorkBudget::with_limit(exact - 1),
            )
            .is_err()
        );
        assert!(
            bind_foreign_owner(
                bound.library(),
                prepared,
                0,
                nominal,
                registry.nominal_parameters(nominal).unwrap(),
                &registry,
                &mut TypeWorkBudget::with_limit(exact),
            )
            .is_ok()
        );
    }

    #[test]
    fn owner_admission_rejects_wrong_nominal_and_substituted_formal_origin() {
        let (prepared, nominal, registry) = fixture();
        let mut parameters = registry.nominal_parameters(nominal).unwrap().to_vec();
        parameters[0].origin = parameters[1].origin.clone();
        assert!(
            bind_foreign_owner(
                NativeLibraryId::new(prepared.module(), 0),
                Arc::clone(&prepared),
                0,
                nominal,
                &parameters,
                &registry,
                &mut TypeWorkBudget::default(),
            )
            .is_err()
        );
        assert!(
            bind_foreign_owner(
                NativeLibraryId::new(prepared.module(), 0),
                prepared,
                0,
                NominalTypeId::new(nominal.module(), 1),
                registry.nominal_parameters(nominal).unwrap(),
                &registry,
                &mut TypeWorkBudget::default(),
            )
            .is_err()
        );
    }
}
