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
    types::{
        ConstructorId, Kind, KindedArgument, NominalTypeId, Type, TypeVariableId, TypeWorkBudget,
    },
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
/// Owner families retain their complete Type/EffectRow formals. Only the
/// explicitly owned position introduces a Type-kind identity.
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

/// Reconstructs the exact original row-bearing State declaration. The tag is
/// canonical only for an Owner whose full defining vector contains a Row.
pub(crate) fn row_owner_parameters<'a>(
    nominal: NominalTypeId,
    registry: &'a ResolvedRegistry,
    span: Span,
    work: &mut TypeWorkBudget,
) -> Result<&'a [ResolvedTypeVariable], ForeignAdmissionError> {
    charge(work, registry.source_owner_candidate_count(), span)?;
    let (prepared, index, _, parameters) = registry
        .source_owner_candidates()
        .find(|(_, _, candidate, _)| *candidate == nominal)
        .ok_or_else(|| failure(ForeignAdmissionReason::InvalidSignature, span))?;
    authenticate_source_owner_candidate(prepared, index, nominal, parameters, registry, work)?;
    charge(work, parameters.len(), span)?;
    if !parameters
        .iter()
        .any(|parameter| parameter.kind == Kind::EffectRow)
    {
        return Err(failure(ForeignAdmissionReason::InvalidParameters, span));
    }
    Ok(parameters)
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
    let canonical = match registry.nominal_kind(nominal) {
        Some(CanonicalNominalKind::Parameters {
            parameters: canonical,
            origin,
        }) if origin == span => {
            let original = registry
                .nominal(nominal)
                .ok_or_else(|| failure(ForeignAdmissionReason::InvalidSignature, span))?;
            charge(work, original.constructors.len().saturating_add(3), span)?;
            if original.declaration_kind != ResolvedNominalDeclarationKind::Data
                || !original.constructors.is_empty()
                || original.representation.is_some()
                || original.representation_provenance.is_some()
                || !same_origin_with_budget(&original.origin, owner.origin(), work)
                    .map_err(|_| failure(ForeignAdmissionReason::WorkExhausted, span))?
                || !names_match(&original.spelling, owner.name(), work, span)?
                || canonical.len() != parameters.len()
            {
                return Err(failure(ForeignAdmissionReason::InvalidSignature, span));
            }
            Some(canonical)
        }
        Some(CanonicalNominalKind::Frozen { kind, origin })
            if origin == span && registry.nominal(nominal).is_none() =>
        {
            // The original prepared Owner and full retained defining records
            // authenticate import opacity; a frozen arrow shape alone does not.
            charge(work, parameters.len().saturating_add(2), span)?;
            let mut remaining = kind;
            for parameter in parameters {
                let Kind::Arrow(argument, result) = remaining else {
                    return Err(failure(ForeignAdmissionReason::InvalidParameters, span));
                };
                if argument.as_ref() != &parameter.kind {
                    return Err(failure(ForeignAdmissionReason::InvalidParameters, span));
                }
                remaining = result;
            }
            if remaining != &Kind::Type {
                return Err(failure(ForeignAdmissionReason::InvalidParameters, span));
            }
            None
        }
        _ => return Err(failure(ForeignAdmissionReason::InvalidParameters, span)),
    };
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
    for (position, (parameter, source)) in parameters.iter().zip(owner.parameters()).enumerate() {
        let canonical = canonical
            .and_then(|canonical| canonical.get(position))
            .or_else(|| registry.type_variable(parameter.id))
            .ok_or_else(|| failure(ForeignAdmissionReason::InvalidParameters, span))?;
        charge(work, 3, span)?;
        let parameter_span = primary_span(source.origin(), work, span)?;
        if !matches!(source.kind(), Kind::Type | Kind::EffectRow)
            || &parameter.kind != source.kind()
            || parameter.id != canonical.id
            || canonical.kind != parameter.kind
            || (position == owner.owned_parameter() && parameter.kind != Kind::Type)
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

pub(super) fn unary_payload<'a>(
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

/// Borrowed actuals preserve their Type/Row tag without creating authority.
pub(crate) enum StateArgument<'a> {
    Type(&'a Type),
    EffectRow(&'a crate::types::EffectRow),
}

/// Reads one complete canonical State vector after its caller has authenticated
/// the original Owner. Type-only owners keep the ordinary application encoding.
pub(crate) fn state_arguments<'a>(
    state: &'a Type,
    nominal: NominalTypeId,
    parameters: &[ResolvedTypeVariable],
    span: Span,
    work: &mut TypeWorkBudget,
) -> Result<Vec<StateArgument<'a>>, ForeignAdmissionError> {
    charge(work, parameters.len().saturating_add(1), span)?;
    let has_row = parameters
        .iter()
        .any(|parameter| parameter.kind == Kind::EffectRow);
    let mut arguments = Vec::new();
    if let Type::ForeignOwnerApply(head, actuals) = state {
        if *head != nominal || !has_row || actuals.len() != parameters.len() {
            return Err(failure(ForeignAdmissionReason::InvalidSignature, span));
        }
        charge(work, actuals.len(), span)?;
        arguments
            .try_reserve_exact(actuals.len())
            .map_err(|_| failure(ForeignAdmissionReason::StorageRefused, span))?;
        for (argument, parameter) in actuals.iter().zip(parameters) {
            arguments.push(match (argument, &parameter.kind) {
                (KindedArgument::TypeArg(ty), Kind::Type) => StateArgument::Type(ty),
                (KindedArgument::RowArg(row), Kind::EffectRow) => StateArgument::EffectRow(row),
                _ => return Err(failure(ForeignAdmissionReason::InvalidParameters, span)),
            });
        }
    } else {
        if has_row {
            return Err(failure(ForeignAdmissionReason::InvalidSignature, span));
        }
        let mut head = state;
        while let Type::Application(function, argument) = head {
            charge(work, 1, span)?;
            arguments
                .try_reserve(1)
                .map_err(|_| failure(ForeignAdmissionReason::StorageRefused, span))?;
            arguments.push(StateArgument::Type(argument));
            head = function;
        }
        if !matches!(head, Type::Nominal(id) if *id == nominal)
            || arguments.len() != parameters.len()
        {
            return Err(failure(ForeignAdmissionReason::InvalidSignature, span));
        }
        arguments.reverse();
    }
    Ok(arguments)
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
    let actuals = state_arguments(state, owner.nominal(), owner.parameters(), span, work)?;
    for (argument, actual) in application.arguments().iter().zip(actuals) {
        let position = match argument {
            PreparedOwnerArgument::Type(position) | PreparedOwnerArgument::EffectRow(position) => {
                *position
            }
        };
        let parameter = effect
            .parameters
            .get(position)
            .ok_or_else(|| failure(ForeignAdmissionReason::InvalidParameters, span))?;
        let valid = match (argument, actual, &parameter.kind) {
            (
                PreparedOwnerArgument::Type(_),
                StateArgument::Type(Type::Variable(id)),
                Kind::Type,
            ) => *id == parameter.id,
            (
                PreparedOwnerArgument::EffectRow(_),
                StateArgument::EffectRow(row),
                Kind::EffectRow,
            ) => {
                row.known().is_empty()
                    && row.tail().is_some_and(|tail| {
                        tail.variable() == crate::types::EffectRowVariable::rigid(parameter.id)
                            && tail.lacks().is_empty()
                    })
            }
            _ => false,
        };
        if !valid {
            return Err(failure(ForeignAdmissionReason::InvalidParameters, span));
        }
    }
    Ok(())
}

pub(super) fn source_leaf<'a>(
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
    let nominal = state
        .outer_nominal()
        .ok_or_else(|| failure(ForeignAdmissionReason::InvalidSignature, span))?;
    charge(work, registry.source_owner_candidate_count(), span)?;
    let (prepared, index, _, parameters) = registry
        .source_owner_candidates()
        .find(|(_, _, candidate, _)| *candidate == nominal)
        .ok_or_else(|| failure(ForeignAdmissionReason::InvalidSignature, span))?;
    authenticate_source_owner_candidate(prepared, index, nominal, parameters, registry, work)?;
    let enclosing = &prepared.owners()[index];
    let arguments = state_arguments(state, nominal, parameters, span, work)?;
    let Some(StateArgument::Type(Type::Variable(identity))) =
        arguments.get(enclosing.owned_parameter())
    else {
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
    view: Option<&Type>,
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
        if current.is_some_and(|current| std::ptr::eq(ty, current))
            || view.is_some_and(|view| std::ptr::eq(ty, view))
        {
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
        } else if matches!(ty, Type::Application(_, _) | Type::ForeignOwnerApply(_, _)) {
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
            || !matches!(original.kind(), Kind::Type | Kind::EffectRow)
            || &parameter.kind != original.kind()
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
                .any(|(left, right)| left.id != right.id || left.kind != right.kind)
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
            for parameter in parameters {
                let Kind::Arrow(argument, result) = remaining else {
                    return Err(failure(ForeignAdmissionReason::InvalidParameters, span));
                };
                if argument.as_ref() != &parameter.kind {
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
        PreparedOwnerCall::Borrow {
            application,
            current_operand,
            ..
        } => {
            let view = if let Some(access) = symbol.access_result() {
                super::source_access::validate_result_signature(
                    owner.prepared(),
                    symbol,
                    access,
                    effect,
                    payload,
                    codec.output,
                    codec.nullable,
                    call_codec,
                    registry,
                    work,
                )?
            } else {
                if payload != &Type::Int || !matches!(symbol.result(), PreparedAbiResult::Scalar(_))
                {
                    return Err(failure(ForeignAdmissionReason::InvalidSignature, span));
                }
                None
            };
            let Some(PreparedOperandSource::Current(path)) = symbol
                .operands()
                .get(*current_operand)
                .map(|operand| operand.source())
            else {
                return Err(failure(ForeignAdmissionReason::InvalidSignature, span));
            };
            let current = source_leaf(domain, path, span, work)?;
            check_state_application(current, owner, application, effect, work)?;
            owner_domain(
                domain,
                Some(current),
                view,
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
        PreparedOwnerCall::OutputAcquire {
            application,
            output_operand,
            offset,
            ..
        } => {
            let Type::Tuple(fields) = payload else {
                return Err(failure(ForeignAdmissionReason::InvalidSignature, span));
            };
            if fields.len() != 2 + usize::from(offset.is_some())
                || fields[0] != Type::Int
                || !matches!(symbol.result(), PreparedAbiResult::Scalar(_))
                || owner.owner().representation()
                    != super::source_contract::PreparedAddressRepresentation::Opaque
                || !symbol
                    .operands()
                    .get(*output_operand)
                    .is_some_and(|operand| {
                        matches!(operand.source(), PreparedOperandSource::OwnerOutput)
                    })
            {
                return Err(failure(ForeignAdmissionReason::InvalidSignature, span));
            }
            let output = unary_payload(&fields[1], codec.output, span, work)?;
            let state = unary_payload(output, codec.nullable, span, work)?;
            check_state_application(state, owner, application, effect, work)?;
            if offset.is_some() {
                let output = unary_payload(&fields[2], codec.output, span, work)?;
                if unary_payload(output, codec.nullable, span, work)? != &Type::Int {
                    return Err(failure(ForeignAdmissionReason::InvalidSignature, span));
                }
            }
            owner_domain(
                domain,
                None,
                None,
                owner,
                application,
                effect,
                &formal_ids,
                registry,
                span,
                work,
            )?;
            None
        }
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
        }
        | PreparedOwnerCall::StatusTeardown {
            application,
            current_operand,
            ..
        } => {
            let expected_payload = match symbol.owner_call() {
                Some(PreparedOwnerCall::Teardown { .. })
                    if symbol.result() == PreparedAbiResult::Void =>
                {
                    &Type::Unit
                }
                Some(PreparedOwnerCall::StatusTeardown { .. })
                    if matches!(symbol.result(), PreparedAbiResult::Scalar(_)) =>
                {
                    &Type::Int
                }
                _ => return Err(failure(ForeignAdmissionReason::InvalidSignature, span)),
            };
            if unary_payload(payload, codec.disposition, span, work)? != expected_payload {
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
                None,
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
            (
                PreparedOperandSource::Bytes { path, extent, .. },
                PreparedRepresentation::Address(
                    super::source_contract::PreparedAddressRepresentation::Bytes,
                ),
            ) if matches!(symbol.owner_call(), Some(PreparedOwnerCall::Borrow { .. })) => {
                if !matches!(
                    source_leaf(domain, path, span, work)?,
                    Type::Bytes | Type::String
                ) || source_leaf(domain, extent, span, work)? != &Type::Int
                {
                    return Err(failure(ForeignAdmissionReason::InvalidSourcePosition, span));
                }
            }
            (
                PreparedOperandSource::Nul(path),
                PreparedRepresentation::Address(
                    super::source_contract::PreparedAddressRepresentation::Bytes,
                ),
            ) if matches!(
                symbol.owner_call(),
                Some(PreparedOwnerCall::OutputAcquire { .. })
            ) =>
            {
                if source_leaf(domain, path, span, work)? != &Type::String {
                    return Err(failure(ForeignAdmissionReason::InvalidSourcePosition, span));
                }
            }
            (PreparedOperandSource::Null, PreparedRepresentation::Address(_))
                if matches!(
                    symbol.owner_call(),
                    Some(PreparedOwnerCall::OutputAcquire { .. })
                ) => {}
            (
                PreparedOperandSource::OwnerOutput,
                PreparedRepresentation::Address(representation),
            ) if representation == owner.owner().representation()
                && matches!(symbol.owner_call(), Some(PreparedOwnerCall::OutputAcquire { output_operand, .. }) if *output_operand == index) =>
                {}
            (
                PreparedOperandSource::OffsetOutput,
                PreparedRepresentation::Address(
                    super::source_contract::PreparedAddressRepresentation::Bytes,
                ),
            ) if matches!(symbol.owner_call(), Some(PreparedOwnerCall::OutputAcquire { offset: Some(offset), .. }) if offset.operand == index) =>
                {}
            (
                PreparedOperandSource::Constant(position),
                PreparedRepresentation::Scalar(representation),
            ) if owner
                .prepared()
                .constants()
                .get(*position)
                .is_some_and(|constant| constant.representation() == representation) => {}
            (
                PreparedOperandSource::Sentinel(position),
                PreparedRepresentation::FunctionAddressSentinel,
            ) if owner
                .prepared()
                .sentinels()
                .get(*position)
                .is_some_and(|sentinel| {
                    owner
                        .prepared()
                        .representations()
                        .get(sentinel.representation_index())
                        .is_some_and(|value| {
                            value.representation()
                                == PreparedRepresentation::FunctionAddressSentinel
                        })
                }) => {}
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
                    | PreparedOwnerCall::Borrow { application, .. }
                    | PreparedOwnerCall::OutputAcquire { application, .. }
                    | PreparedOwnerCall::Teardown { application, .. }
                    | PreparedOwnerCall::StatusTeardown { application, .. } => application,
                };
                enclosing_identity(state, owner, application, effect, registry, span, work)?;
                let mut head = state;
                while let Type::Application(function, _) = head {
                    charge(work, 1, span)?;
                    head = function;
                }
                let nominal = match head {
                    Type::Nominal(nominal) | Type::ForeignOwnerApply(nominal, _) => nominal,
                    _ => return Err(failure(ForeignAdmissionReason::InvalidSignature, span)),
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
        fixture_from(SOURCE)
    }

    fn fixture_from(text: &str) -> (Arc<PreparedForeignLibrary>, NominalTypeId, ResolvedRegistry) {
        let source = SourceFile::new("source-owner.ash", text).unwrap();
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
                kind: prepared.owners()[0].parameters()[index].kind().clone(),
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
    fn inherited_row_owner_kind_authority_preserves_exact_formals_tags_and_work() {
        use crate::{
            kind::{KindEnvironments, KindFailure},
            types::{EffectRow, IterativeTypeOwner, KindedArgument, Type},
        };

        let text = SOURCE
            .replace("owner State<T, R>", "owner State<T : EffectRow, R>")
            .replace("State<T, R>", "State<{| T}, R>")
            .replace("R, T>", "R, T : EffectRow>")
            .replace("symbol Free<T,", "symbol Free<T : EffectRow,");
        let (prepared, nominal, registry) = fixture_from(&text);
        let parameters = registry.nominal_parameters(nominal).unwrap();
        let bound = bind_foreign_owner(
            NativeLibraryId::new(prepared.module(), 0),
            Arc::clone(&prepared),
            0,
            nominal,
            parameters,
            &registry,
            &mut TypeWorkBudget::default(),
        )
        .unwrap();
        assert_eq!(bound.owned_parameter(), 1);
        assert_eq!(parameters[0].kind, Kind::EffectRow);
        assert_eq!(parameters[1].kind, Kind::Type);
        let span = prepared.origin().primary_span();
        let state = IterativeTypeOwner::new(Type::ForeignOwnerApply(
            nominal,
            vec![
                KindedArgument::RowArg(EffectRow::empty()),
                KindedArgument::TypeArg(Type::Int),
            ]
            .into_boxed_slice(),
        ));
        let check = |mirror: &[ResolvedTypeVariable], work: &mut TypeWorkBudget| {
            let mut kinds = KindEnvironments::new();
            kinds.insert_source_owner_nominal(&bound, mirror, span, work)?;
            kinds.expect_body_free_value_type_with_ledger(&state, span, work)
        };
        let mut measured = TypeWorkBudget::default();
        check(parameters, &mut measured).unwrap();
        let cost = measured.used();
        for prefix in [0, 13] {
            let mut short = TypeWorkBudget::with_limit(prefix + cost - 1);
            short.charge(prefix).unwrap();
            assert!(
                check(parameters, &mut short)
                    .unwrap_err()
                    .is_resource_exhaustion()
            );
            for _ in 0..2 {
                let mut exact = TypeWorkBudget::with_limit(prefix + cost);
                exact.charge(prefix).unwrap();
                check(parameters, &mut exact).unwrap();
                assert_eq!(exact.used(), prefix + cost);
            }
            check(parameters, &mut TypeWorkBudget::default()).unwrap();
        }
        for change in 0..4 {
            let mut mirror = parameters.to_vec();
            match change {
                0 => mirror[0].id = parameters[1].id,
                1 => mirror[0].origin = parameters[1].origin.clone(),
                2 => mirror[0].kind = Kind::Type,
                _ => mirror.swap(0, 1),
            }
            assert!(matches!(
                check(&mirror, &mut TypeWorkBudget::default()),
                Err(KindFailure::Internal(_))
            ));
        }
        let (_, donor_nominal, donor) = fixture_from(&text);
        assert_ne!(nominal, donor_nominal);
        assert!(matches!(
            check(
                donor.nominal_parameters(donor_nominal).unwrap(),
                &mut TypeWorkBudget::default()
            ),
            Err(KindFailure::Internal(_))
        ));

        let mut ordinary = KindEnvironments::new();
        ordinary
            .insert_nominal(nominal, parameters, span, &mut TypeWorkBudget::default())
            .unwrap();
        assert!(matches!(
            ordinary.expect_body_free_value_type_with_ledger(
                &state,
                span,
                &mut TypeWorkBudget::default()
            ),
            Err(KindFailure::Internal(_))
        ));
        for (head, arguments) in [
            (
                donor_nominal,
                vec![
                    KindedArgument::RowArg(EffectRow::empty()),
                    KindedArgument::TypeArg(Type::Int),
                ],
            ),
            (
                nominal,
                vec![
                    KindedArgument::TypeArg(Type::Unit),
                    KindedArgument::TypeArg(Type::Int),
                ],
            ),
            (
                nominal,
                vec![
                    KindedArgument::RowArg(EffectRow::empty()),
                    KindedArgument::RowArg(EffectRow::empty()),
                ],
            ),
            (nominal, vec![KindedArgument::RowArg(EffectRow::empty())]),
        ] {
            let forged = IterativeTypeOwner::new(Type::ForeignOwnerApply(
                head,
                arguments.into_boxed_slice(),
            ));
            let mut kinds = KindEnvironments::new();
            kinds
                .insert_source_owner_nominal(
                    &bound,
                    parameters,
                    span,
                    &mut TypeWorkBudget::default(),
                )
                .unwrap();
            assert!(
                kinds
                    .expect_body_free_value_type_with_ledger(
                        &forged,
                        span,
                        &mut TypeWorkBudget::default()
                    )
                    .is_err()
            );
        }
        let ordinary_state = IterativeTypeOwner::new(Type::Application(
            Box::new(Type::Nominal(nominal)),
            Box::new(Type::Int),
        ));
        assert!(
            super::state_arguments(
                &ordinary_state,
                nominal,
                parameters,
                span,
                &mut TypeWorkBudget::default()
            )
            .is_err()
        );

        let (plain, plain_nominal, plain_registry) = fixture();
        let tagged_plain = IterativeTypeOwner::new(Type::ForeignOwnerApply(
            plain_nominal,
            vec![
                KindedArgument::TypeArg(Type::Unit),
                KindedArgument::TypeArg(Type::Int),
            ]
            .into_boxed_slice(),
        ));
        assert!(
            super::state_arguments(
                &tagged_plain,
                plain_nominal,
                plain_registry.nominal_parameters(plain_nominal).unwrap(),
                plain.origin().primary_span(),
                &mut TypeWorkBudget::default()
            )
            .is_err()
        );
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
