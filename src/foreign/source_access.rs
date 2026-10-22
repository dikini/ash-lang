//! Exact original access-family type facts, without an active native window.

use std::sync::Arc;

use super::{
    checked_source::{
        ForeignAdmissionError, ForeignAdmissionReason, NativeLibraryId, charge, failure,
        names_match, origin_within, primary_span,
    },
    source_contract::{
        PreparedForeignLibrary, PreparedForeignNominalRole, PreparedForeignParameter,
    },
    source_owner::CheckedForeignOwner,
};
use crate::{
    resolved::{
        CanonicalNominalKind, ResolvedNominalDeclarationKind, ResolvedRegistry,
        ResolvedTypeVariable, SharedOwnerParameters, clone_resolved_type_variables_with_budget,
        same_origin_with_budget,
    },
    source::Origin,
    types::{Kind, NominalTypeId, TypeWorkBudget, same_kind_with_budget},
};

/// A declaration identity and its complete defining formal vector. It supplies
/// neither a native address nor a live owner/window/key relation.
#[derive(Debug)]
pub(crate) struct CheckedForeignAccess {
    library: NativeLibraryId,
    prepared: Arc<PreparedForeignLibrary>,
    index: usize,
    nominal: NominalTypeId,
    parameters: SharedOwnerParameters,
}
impl PartialEq for CheckedForeignAccess {
    fn eq(&self, other: &Self) -> bool {
        self.library == other.library
            && Arc::ptr_eq(&self.prepared, &other.prepared)
            && self.index == other.index
            && self.nominal == other.nominal
            && self.parameters == other.parameters
    }
}
impl Eq for CheckedForeignAccess {}
impl CheckedForeignAccess {
    pub(crate) const fn library(&self) -> NativeLibraryId {
        self.library
    }
    pub(crate) const fn prepared(&self) -> &Arc<PreparedForeignLibrary> {
        &self.prepared
    }
    pub(crate) const fn index(&self) -> usize {
        self.index
    }
    pub(crate) const fn nominal(&self) -> NominalTypeId {
        self.nominal
    }
    pub(crate) fn parameters(&self) -> &SharedOwnerParameters {
        &self.parameters
    }
    pub(crate) fn declaration(&self) -> &super::source_contract::PreparedForeignAccess {
        &self.prepared.accesses()[self.index]
    }
}

/// Constructor-free source categories share nominal transport, while preserving
/// their separate authority. In particular an Access is never a native State.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum CheckedForeignNominal {
    Owner(Arc<CheckedForeignOwner>),
    Access(Arc<CheckedForeignAccess>),
}
impl CheckedForeignNominal {
    pub(crate) fn nominal(&self) -> NominalTypeId {
        match self {
            Self::Owner(v) => v.nominal(),
            Self::Access(v) => v.nominal(),
        }
    }
    pub(crate) fn library(&self) -> NativeLibraryId {
        match self {
            Self::Owner(v) => v.library(),
            Self::Access(v) => v.library(),
        }
    }
    pub(crate) fn prepared(&self) -> &Arc<PreparedForeignLibrary> {
        match self {
            Self::Owner(v) => v.prepared(),
            Self::Access(v) => v.prepared(),
        }
    }
    pub(crate) fn role(&self) -> PreparedForeignNominalRole {
        match self {
            Self::Owner(v) => PreparedForeignNominalRole::Owner(v.owner_index()),
            Self::Access(v) => PreparedForeignNominalRole::Access(v.index()),
        }
    }
    pub(crate) fn parameters(&self) -> &SharedOwnerParameters {
        match self {
            Self::Owner(v) => v.parameters(),
            Self::Access(v) => v.parameters(),
        }
    }
    pub(crate) fn original_parameters(&self) -> &[PreparedForeignParameter] {
        match self {
            Self::Owner(v) => v.owner().parameters(),
            Self::Access(v) => v.declaration().parameters(),
        }
    }
    pub(crate) fn origin(&self) -> &Origin {
        match self {
            Self::Owner(v) => v.owner().origin(),
            Self::Access(v) => v.declaration().origin(),
        }
    }
    pub(crate) fn same_original(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Owner(a), Self::Owner(b)) => Arc::ptr_eq(a, b),
            (Self::Access(a), Self::Access(b)) => Arc::ptr_eq(a, b),
            _ => false,
        }
    }
}

pub(crate) fn bind_foreign_access(
    library: NativeLibraryId,
    prepared: Arc<PreparedForeignLibrary>,
    index: usize,
    nominal: NominalTypeId,
    parameters: &[ResolvedTypeVariable],
    registry: &ResolvedRegistry,
    work: &mut TypeWorkBudget,
) -> Result<CheckedForeignAccess, ForeignAdmissionError> {
    let span = prepared.origin().primary_span();
    if library.module() != prepared.module() {
        return Err(failure(ForeignAdmissionReason::InvalidLibrary, span));
    }
    authenticate_source_access_candidate(&prepared, index, nominal, parameters, registry, work)?;
    let parameters = clone_resolved_type_variables_with_budget(parameters, work)
        .map_err(|()| failure(ForeignAdmissionReason::WorkExhausted, span))?;
    let parameters =
        SharedOwnerParameters::from_boxed_with_budget(parameters.into_boxed_slice(), work)
            .map_err(|_| failure(ForeignAdmissionReason::StorageRefused, span))?;
    Ok(CheckedForeignAccess {
        library,
        prepared,
        index,
        nominal,
        parameters,
    })
}

pub(crate) fn authenticate_source_access_candidate(
    prepared: &PreparedForeignLibrary,
    index: usize,
    nominal: NominalTypeId,
    parameters: &[ResolvedTypeVariable],
    registry: &ResolvedRegistry,
    work: &mut TypeWorkBudget,
) -> Result<(), ForeignAdmissionError> {
    let span = prepared.origin().primary_span();
    charge(work, 4, span)?;
    let access = prepared
        .accesses()
        .get(index)
        .ok_or_else(|| failure(ForeignAdmissionReason::InvalidLibrary, span))?;
    let span = primary_span(access.origin(), work, span)?;
    let invalid = || failure(ForeignAdmissionReason::InvalidParameters, span);
    if nominal.module() != prepared.module()
        || parameters.len() != access.parameters().len()
        || access.window_parameter() >= parameters.len()
        || access.parameters()[access.window_parameter()].kind() != &Kind::Type
    {
        return Err(invalid());
    }
    let canonical = match registry.nominal_kind(nominal) {
        Some(CanonicalNominalKind::Parameters {
            parameters: canonical,
            origin,
        }) => {
            let original = registry.nominal(nominal).ok_or_else(invalid)?;
            if origin != span
                || canonical.len() != parameters.len()
                || original.declaration_kind != ResolvedNominalDeclarationKind::Data
                || !original.constructors.is_empty()
                || original.representation.is_some()
                || original.representation_provenance.is_some()
                || !same_origin_with_budget(&original.origin, access.origin(), work)
                    .map_err(|()| failure(ForeignAdmissionReason::WorkExhausted, span))?
                || !names_match(&original.spelling, access.name(), work, span)?
            {
                return Err(invalid());
            }
            canonical
        }
        Some(CanonicalNominalKind::Frozen { kind, origin })
            if origin == span && registry.nominal(nominal).is_none() =>
        {
            charge(work, registry.source_foreign_nominal_count(), span)?;
            let retained = registry
                .source_accesses()
                .find(|fact| {
                    fact.nominal() == nominal
                        && fact.index() == index
                        && std::ptr::eq(fact.prepared().as_ref(), prepared)
                })
                .ok_or_else(invalid)?;
            if retained.parameters().len() != parameters.len() {
                return Err(invalid());
            }
            let mut remaining = kind;
            for parameter in parameters {
                charge(work, 1, span)?;
                let Kind::Arrow(argument, result) = remaining else {
                    return Err(invalid());
                };
                if !same_kind_with_budget(argument, &parameter.kind, work)
                    .map_err(|()| failure(ForeignAdmissionReason::WorkExhausted, span))?
                {
                    return Err(invalid());
                }
                remaining = result;
            }
            if remaining != &Kind::Type {
                return Err(invalid());
            }
            retained.parameters().as_ref()
        }
        _ => return Err(invalid()),
    };
    let mut seen = std::collections::HashSet::new();
    charge(work, parameters.len(), span)?;
    seen.try_reserve(parameters.len())
        .map_err(|_| failure(ForeignAdmissionReason::StorageRefused, span))?;
    for ((actual, canonical), expected) in parameters.iter().zip(canonical).zip(access.parameters())
    {
        let expected_span = primary_span(expected.origin(), work, span)?;
        charge(work, 3, expected_span)?;
        if actual.id.module() != Some(nominal.module())
            || actual.id != canonical.id
            || !seen.insert(actual.id)
            || !same_kind_with_budget(&actual.kind, expected.kind(), work)
                .map_err(|()| failure(ForeignAdmissionReason::WorkExhausted, span))?
            || !same_kind_with_budget(&canonical.kind, expected.kind(), work)
                .map_err(|()| failure(ForeignAdmissionReason::WorkExhausted, span))?
            || !names_match(&actual.spelling, expected.name(), work, expected_span)?
            || !same_origin_with_budget(&actual.origin, &canonical.origin, work)
                .map_err(|()| failure(ForeignAdmissionReason::WorkExhausted, span))?
            || !origin_within(expected_span, &actual.origin, work)?
        {
            return Err(invalid());
        }
    }
    Ok(())
}

/// Reconstruct the exact state projection of one fresh window application.
/// This authenticates passive identities and kinds only; a direct provider's
/// original graph and the selected live guard must still prove the state loan.
pub(crate) fn window_state_type<'a>(
    access: &Arc<CheckedForeignAccess>,
    arguments: impl ExactSizeIterator<Item = &'a crate::types::KindedArgument>,
    window: crate::types::TypeVariableId,
    registry: &ResolvedRegistry,
    work: &mut TypeWorkBudget,
) -> Result<(Arc<CheckedForeignOwner>, crate::types::IterativeTypeOwner), ForeignAdmissionError> {
    use super::source_contract::PreparedOwnerArgument;
    use crate::types::{IterativeTypeOwner, KindedArgument, Type, TypeStructureNode};
    let span = primary_span(
        access.declaration().origin(),
        work,
        access.prepared().origin().primary_span(),
    )?;
    let invalid = || failure(ForeignAdmissionReason::InvalidParameters, span);
    charge(work, registry.source_foreign_nominal_count(), span)?;
    if !registry
        .source_accesses()
        .any(|original| Arc::ptr_eq(original, access))
    {
        return Err(invalid());
    }
    let count = arguments.len();
    charge(work, count, span)?;
    if count != access.parameters().len() {
        return Err(invalid());
    }
    let mut actuals = Vec::new();
    actuals
        .try_reserve_exact(count)
        .map_err(|_| failure(ForeignAdmissionReason::StorageRefused, span))?;
    actuals.extend(arguments);
    for (position, (argument, parameter)) in
        actuals.iter().zip(access.parameters().iter()).enumerate()
    {
        charge(work, 1, span)?;
        if !matches!(
            (argument, &parameter.kind),
            (KindedArgument::TypeArg(_), Kind::Type) | (KindedArgument::RowArg(_), Kind::EffectRow)
        ) {
            return Err(invalid());
        }
        if position == access.declaration().window_parameter() {
            if !matches!(argument, KindedArgument::TypeArg(Type::Variable(id)) if *id == window) {
                return Err(invalid());
            }
        } else if crate::types::visit_argument_structure_with_budget(argument, work, |node, _| {
            Ok(matches!(node, TypeStructureNode::Type(Type::Variable(id)) if *id == window))
        })
        .map_err(|()| failure(ForeignAdmissionReason::WorkExhausted, span))?
        {
            // No inherited argument can refer to a binder introduced later.
            return Err(invalid());
        }
    }
    // Recover the same checked owner allocation from the independently sealed
    // native table. A same-shaped or same-spelled owner is insufficient.
    charge(work, registry.effects().len(), span)?;
    let mut owner = None;
    for effect in registry.effects() {
        let Some(symbol) = registry.native_symbol(crate::types::OperationId::new(effect.id, 0))
        else {
            continue;
        };
        let Some(candidate) = symbol.owner() else {
            continue;
        };
        if candidate.library() != access.library()
            || !Arc::ptr_eq(candidate.prepared(), access.prepared())
            || candidate.owner_index() != access.declaration().owner().owner()
        {
            continue;
        }
        if owner
            .as_ref()
            .is_some_and(|old| !Arc::ptr_eq(old, candidate))
        {
            return Err(invalid());
        }
        owner = Some(Arc::clone(candidate));
    }
    let owner = owner.ok_or_else(invalid)?;
    let projection = access.declaration().owner().arguments();
    charge(work, projection.len(), span)?;
    if projection.len() != owner.parameters().len() {
        return Err(invalid());
    }
    let mut arguments = Vec::new();
    arguments
        .try_reserve_exact(projection.len())
        .map_err(|_| failure(ForeignAdmissionReason::StorageRefused, span))?;
    let mut has_row = false;
    for (argument, parameter) in projection.iter().zip(owner.parameters().iter()) {
        let (position, row) = match argument {
            PreparedOwnerArgument::Type(position) => (*position, false),
            PreparedOwnerArgument::EffectRow(position) => (*position, true),
        };
        let actual = actuals.get(position).copied().ok_or_else(invalid)?;
        if row != (parameter.kind == Kind::EffectRow)
            || row != matches!(actual, KindedArgument::RowArg(_))
        {
            return Err(invalid());
        }
        has_row |= row;
        arguments.push(crate::types::IterativeArgumentOwner::new(
            crate::types::clone_kinded_argument_with_budget(actual, work)
                .map_err(|_| failure(ForeignAdmissionReason::WorkExhausted, span))?,
        ));
    }
    let state = if has_row {
        charge(work, arguments.len(), span)?;
        let mut actuals = Vec::new();
        actuals
            .try_reserve_exact(arguments.len())
            .map_err(|_| failure(ForeignAdmissionReason::StorageRefused, span))?;
        actuals.extend(
            arguments
                .into_iter()
                .map(crate::types::IterativeArgumentOwner::into_inner),
        );
        IterativeTypeOwner::new(Type::ForeignOwnerApply(
            owner.nominal(),
            actuals.into_boxed_slice(),
        ))
    } else {
        let mut state = IterativeTypeOwner::new(Type::Nominal(owner.nominal()));
        for argument in arguments {
            charge(work, 1, span)?;
            let KindedArgument::TypeArg(argument) = argument.into_inner() else {
                unreachable!("the complete projection checked each Type tag")
            };
            state = IterativeTypeOwner::new(Type::Application(
                Box::new(state.into_inner()),
                Box::new(argument),
            ));
        }
        state
    };
    Ok((owner, state))
}

/// Reconstruct one original operation's complete instantiation at this window.
/// This relation is passive: the direct phase and selected runtime guard remain
/// independent obligations. No member spelling or compatible function grants it.
pub(crate) fn window_interpretation_matches(
    access: &Arc<CheckedForeignAccess>,
    arguments: &[crate::types::KindedArgument],
    interpretation: &crate::core::NativeInterpretation,
    registry: &ResolvedRegistry,
    work: &mut TypeWorkBudget,
) -> Result<bool, ForeignAdmissionError> {
    window_operation_matches(
        access,
        arguments,
        interpretation.symbol(),
        interpretation.effect(),
        registry,
        work,
    )
}

pub(crate) fn window_operation_matches(
    access: &Arc<CheckedForeignAccess>,
    arguments: &[crate::types::KindedArgument],
    symbol: &Arc<super::checked_source::CheckedForeignSymbol>,
    instance: &crate::types::EffectInstance,
    registry: &ResolvedRegistry,
    work: &mut TypeWorkBudget,
) -> Result<bool, ForeignAdmissionError> {
    use super::source_contract::{PreparedOwnerArgument, PreparedOwnerCall};
    use crate::types::same_kinded_argument_with_budget;
    let span = access.declaration().origin().primary_span();
    charge(
        work,
        access.declaration().preserving_members().len() + 3,
        span,
    )?;
    if symbol.library() != access.library()
        || !Arc::ptr_eq(symbol.prepared(), access.prepared())
        || !registry
            .native_symbol(symbol.operation())
            .is_some_and(|registered| Arc::ptr_eq(registered, symbol))
        || instance.effect() != symbol.effect()
        || !access
            .declaration()
            .preserving_members()
            .iter()
            .any(|(member, _)| *member == symbol.symbol().member_index())
    {
        return Ok(false);
    }
    let effect = registry
        .effect(instance.effect())
        .ok_or_else(|| failure(ForeignAdmissionReason::InvalidParameters, span))?;
    charge(work, effect.parameters.len(), span)?;
    if effect.parameters.len() != instance.arguments().len()
        || effect.parameters.len() != symbol.parameter_ids().len()
        || arguments.len() != access.parameters().len()
    {
        return Ok(false);
    }
    for ((formal, id), actual) in effect
        .parameters
        .iter()
        .zip(symbol.parameter_ids())
        .zip(instance.arguments())
    {
        if formal.id != *id
            || !matches!(
                (&formal.kind, actual),
                (Kind::Type, crate::types::KindedArgument::TypeArg(_))
                    | (Kind::EffectRow, crate::types::KindedArgument::RowArg(_))
            )
        {
            return Ok(false);
        }
    }
    let same_projection = |projection: &[PreparedOwnerArgument],
                           expected: &[&crate::types::KindedArgument],
                           work: &mut TypeWorkBudget| {
        charge(work, projection.len(), span)?;
        if projection.len() != expected.len() {
            return Ok(false);
        }
        for (projection, expected) in projection.iter().zip(expected) {
            let Some(actual) = instance.arguments().get(projection.parameter()) else {
                return Ok(false);
            };
            if !matches!(
                (projection, actual),
                (
                    PreparedOwnerArgument::Type(_),
                    crate::types::KindedArgument::TypeArg(_)
                ) | (
                    PreparedOwnerArgument::EffectRow(_),
                    crate::types::KindedArgument::RowArg(_)
                )
            ) || !same_kinded_argument_with_budget(actual, expected, work)
                .map_err(|()| failure(ForeignAdmissionReason::WorkExhausted, span))?
            {
                return Ok(false);
            }
        }
        Ok(true)
    };
    if let Some(result) = symbol.symbol().access_result() {
        let application = result.application();
        charge(work, arguments.len(), span)?;
        let mut expected = Vec::new();
        expected
            .try_reserve_exact(arguments.len())
            .map_err(|_| failure(ForeignAdmissionReason::StorageRefused, span))?;
        expected.extend(arguments.iter());
        return if application.family() == access.index() {
            same_projection(application.arguments(), &expected, work)
        } else {
            Ok(false)
        };
    }
    // Preserving scalar borrows still require the exact owner projection. They
    // may neither create nor consume a guard while the window remains open.
    let Some(PreparedOwnerCall::Borrow { application, .. }) = symbol.owner_role() else {
        return Ok(false);
    };
    if application.owner() != access.declaration().owner().owner() {
        return Ok(false);
    }
    charge(work, access.declaration().owner().arguments().len(), span)?;
    let mut expected = Vec::new();
    expected
        .try_reserve_exact(access.declaration().owner().arguments().len())
        .map_err(|_| failure(ForeignAdmissionReason::StorageRefused, span))?;
    for projection in access.declaration().owner().arguments() {
        let Some(argument) = arguments.get(projection.parameter()) else {
            return Ok(false);
        };
        expected.push(argument);
    }
    same_projection(application.arguments(), &expected, work)
}

/// Independent category reconstruction; constructor-free membership alone grants nothing.
pub(crate) fn authenticate_source_foreign_nominal_candidate(
    prepared: &PreparedForeignLibrary,
    role: PreparedForeignNominalRole,
    nominal: NominalTypeId,
    parameters: &[ResolvedTypeVariable],
    registry: &ResolvedRegistry,
    work: &mut TypeWorkBudget,
) -> Result<(), ForeignAdmissionError> {
    match role {
        PreparedForeignNominalRole::Owner(index) => {
            super::source_owner::authenticate_source_owner_candidate(
                prepared, index, nominal, parameters, registry, work,
            )
        }
        PreparedForeignNominalRole::Access(index) => authenticate_source_access_candidate(
            prepared, index, nominal, parameters, registry, work,
        ),
    }
}

fn check_view_application(
    ty: &crate::types::Type,
    nominal: NominalTypeId,
    application: &super::source_contract::PreparedAccessApplication,
    effect: &crate::resolved::ResolvedEffectDeclaration,
    work: &mut TypeWorkBudget,
) -> Result<(), ForeignAdmissionError> {
    use super::source_contract::PreparedOwnerArgument;
    use crate::types::Type;
    let span = application.span();
    let mut head = ty;
    for argument in application.arguments().iter().rev() {
        charge(work, 2, span)?;
        let PreparedOwnerArgument::Type(index) = argument else {
            return Err(failure(ForeignAdmissionReason::InvalidParameters, span));
        };
        let formal = effect
            .parameters
            .get(*index)
            .ok_or_else(|| failure(ForeignAdmissionReason::InvalidParameters, span))?;
        let Type::Application(function, value) = head else {
            return Err(failure(ForeignAdmissionReason::InvalidSignature, span));
        };
        if formal.kind != Kind::Type || value.as_ref() != &Type::Variable(formal.id) {
            return Err(failure(ForeignAdmissionReason::InvalidParameters, span));
        }
        head = function;
    }
    if head != &Type::Nominal(nominal) {
        return Err(failure(ForeignAdmissionReason::InvalidSignature, span));
    }
    Ok(())
}

/// Reconstruct the common opaque Extent kind from the original builtin module;
/// a user nominal with the same shape or spelling supplies no such role.
pub(crate) fn extent_nominal(
    codec: &super::checked_source::CheckedForeignCallCodec,
    registry: &ResolvedRegistry,
    work: &mut TypeWorkBudget,
) -> Result<NominalTypeId, ForeignAdmissionError> {
    let span = codec.source();
    let id = NominalTypeId::new(codec.module(), 5);
    charge(work, 4, span)?;
    if !codec.module().is_builtin_foreign() {
        return Err(failure(ForeignAdmissionReason::InvalidCodec, span));
    }
    let (declaration_range, formal_range) = crate::module::foreign_extent_ranges(span)
        .ok_or_else(|| failure(ForeignAdmissionReason::InvalidCodec, span))?;
    let invalid = || failure(ForeignAdmissionReason::InvalidCodec, span);
    let origin = match registry.nominal_kind(id) {
        Some(CanonicalNominalKind::Parameters {
            parameters: [parameter],
            origin,
        }) => {
            let expected = crate::types::TypeVariableId::resolved(codec.module(), 4);
            let canonical = registry.type_variable(expected).ok_or_else(invalid)?;
            charge(work, 5, span)?;
            if parameter.id != expected
                || parameter.kind != Kind::Type
                || canonical.kind != Kind::Type
                || parameter.origin.primary_span().source() != span.source()
                || parameter.origin.primary_span().range() != formal_range
                || !same_origin_with_budget(&parameter.origin, &canonical.origin, work)
                    .map_err(|()| failure(ForeignAdmissionReason::WorkExhausted, span))?
            {
                return Err(invalid());
            }
            origin
        }
        Some(CanonicalNominalKind::Frozen {
            kind: Kind::Arrow(argument, result),
            origin,
        }) if argument.as_ref() == &Kind::Type && result.as_ref() == &Kind::Type => origin,
        _ => return Err(invalid()),
    };
    if origin.source() != span.source() || origin.range() != declaration_range {
        return Err(invalid());
    }
    if let Some(original) = registry.nominal(id) {
        let constructor = crate::types::ConstructorId::new(id, 0);
        charge(work, 4, span)?;
        if original.declaration_kind != ResolvedNominalDeclarationKind::Data
            || original.representation.is_some()
            || original.representation_provenance.is_some()
            || original.constructors.as_ref() != [constructor]
            || !origin_within(span, &original.origin, work)?
            || registry
                .constructor(constructor)
                .is_none_or(|value| value.owner != id || value.payload.is_some())
        {
            return Err(invalid());
        }
    }
    Ok(id)
}

/// Authenticate a passive symbol's exact view/extent result and extra view
/// input. Returning its input reference merely marks that already-checked leaf
/// for domain traversal; it creates no executable reading permission.
#[allow(clippy::too_many_arguments)]
pub(super) fn validate_result_signature<'a>(
    prepared: &Arc<PreparedForeignLibrary>,
    symbol: &super::source_contract::PreparedForeignSymbol,
    result: &super::source_contract::PreparedAccessResult,
    effect: &'a crate::resolved::ResolvedEffectDeclaration,
    payload: &crate::types::Type,
    output: NominalTypeId,
    nullable: NominalTypeId,
    codec: &super::checked_source::CheckedForeignCallCodec,
    registry: &ResolvedRegistry,
    work: &mut TypeWorkBudget,
) -> Result<Option<&'a crate::types::Type>, ForeignAdmissionError> {
    use super::{
        source_contract::{PreparedAccessResult, PreparedOwnerCall},
        source_owner::{source_leaf, unary_payload},
    };
    use crate::types::Type;
    let span = result.span();
    let application = result.application();
    charge(work, registry.source_foreign_nominal_count(), span)?;
    let (nominal, parameters) = registry
        .source_access_candidate(prepared, application.family())
        .ok_or_else(|| failure(ForeignAdmissionReason::InvalidSignature, span))?;
    authenticate_source_access_candidate(
        prepared,
        application.family(),
        nominal,
        parameters,
        registry,
        work,
    )?;
    let (owner, arguments) = prepared
        .access_result_owner(application, work)
        .map_err(|error| {
            failure(
                if error.is_resource_exhaustion() {
                    ForeignAdmissionReason::WorkExhausted
                } else {
                    ForeignAdmissionReason::InvalidSignature
                },
                error.span(),
            )
        })?;
    if !matches!(symbol.owner_call(), Some(PreparedOwnerCall::Borrow { application, .. })
        if application.owner() == owner && application.arguments() == arguments)
    {
        return Err(failure(ForeignAdmissionReason::InvalidSignature, span));
    }
    let Type::Function(domain, _) = &effect.operations[0].annotation.ty else {
        return Err(failure(ForeignAdmissionReason::InvalidSignature, span));
    };
    let (view, keys) = match result {
        PreparedAccessResult::View { keys, .. } => {
            let view = unary_payload(
                unary_payload(payload, output, span, work)?,
                nullable,
                span,
                work,
            )?;
            check_view_application(view, nominal, application, effect, work)?;
            (None, keys)
        }
        PreparedAccessResult::Extent { view, keys, .. } => {
            let extent = extent_nominal(codec, registry, work)?;
            check_view_application(
                unary_payload(payload, extent, span, work)?,
                nominal,
                application,
                effect,
                work,
            )?;
            let view = source_leaf(domain, view, span, work)?;
            check_view_application(view, nominal, application, effect, work)?;
            (Some(view), keys)
        }
    };
    for key in keys {
        super::checked_source::check_source_path(domain, key, work, span)?;
    }
    Ok(view)
}

/// Reconstruct the checked window's exact Host from its original owner selector
/// and complete family actuals. This does not supply a native interpretation.
pub(crate) fn checked_window_host_instance(
    access: &CheckedForeignAccess,
    arguments: &[crate::types::KindedArgument],
    registry: &ResolvedRegistry,
    work: &mut TypeWorkBudget,
) -> Result<Option<crate::types::EffectInstance>, ForeignAdmissionError> {
    use super::source_contract::PreparedOwnerArgument;
    use crate::types::{EffectId, EffectInstance, KindedArgument};
    let span = primary_span(
        access.declaration().origin(),
        work,
        access.prepared().origin().primary_span(),
    )?;
    charge(work, 5 + arguments.len(), span)?;
    let Some(contract) = access.prepared().checked_contract() else {
        return Ok(None);
    };
    let invalid = || failure(ForeignAdmissionReason::InvalidParameters, span);
    let application = access.declaration().owner();
    let owner = access
        .prepared()
        .owners()
        .get(application.owner())
        .ok_or_else(invalid)?;
    let selected = contract
        .owners()
        .get(application.owner())
        .ok_or_else(invalid)?;
    if selected.member_index() != owner.member_index()
        || arguments.len() != access.parameters().len()
    {
        return Err(invalid());
    }
    let Some(PreparedOwnerArgument::Type(position)) =
        application.arguments().get(selected.host_parameter())
    else {
        return Err(invalid());
    };
    let Some(KindedArgument::TypeArg(host)) = arguments.get(*position) else {
        return Err(invalid());
    };
    charge(work, registry.effects().len(), span)?;
    let declaration = registry
        .effects()
        .iter()
        .find(|effect| {
            effect.id.module().is_builtin_foreign()
                && effect.id.declaration() == crate::module::FOREIGN_NATIVE_HOST_LOCAL
        })
        .ok_or_else(invalid)?;
    if !super::checked_builtins::is_canonical_native_host(declaration, registry, work)? {
        return Err(invalid());
    }
    let host = crate::types::clone_type_with_budget(host, work)
        .map_err(|_| failure(ForeignAdmissionReason::WorkExhausted, span))?;
    charge(work, 2, span)?;
    Ok(Some(EffectInstance::new(
        EffectId::new(
            declaration.id.module(),
            crate::module::FOREIGN_NATIVE_HOST_LOCAL,
        ),
        Box::new([host]),
    )))
}
