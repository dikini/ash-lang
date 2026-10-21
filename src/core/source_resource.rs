//! Independently checked source resource headers. Header admission does not
//! admit lifecycle code, a specialized scope, a native binding or an activation.

use std::{collections::HashMap, sync::Arc};

mod checked_codec;
mod handler_rows;
pub(in crate::core) use handler_rows::SourceHandlerGraph;
pub(crate) use handler_rows::SourceHandlerRowInputs;
use handler_rows::SourceHandlerRows;

use crate::{
    foreign::{
        checked_source::CheckedForeignSymbol, source_contract::PreparedOwnerCall,
        source_owner::CheckedForeignOwner,
    },
    resolved::{ResolvedRegistry, SourceResourceTypeFact},
    surface::SurfaceResourceReportCodecKind,
    types::{
        ConstructorId, Kind, KindedArgument, NominalTypeId, OperationId, Type, TypeWorkBudget,
        same_type_with_budget,
    },
};

use super::{
    CorePattern, CorePatternKind, EffectExprKind, EffectOperation, NodeId, PureComputation,
    PureExprKind, PureValue, TypedBinder, UnvalidatedEffectProgram, ValidationError,
    ValidationReason,
};

fn invalid() -> ValidationError {
    ValidationError::new(ValidationReason::Registry, None)
}

fn resource() -> ValidationError {
    ValidationError::new(ValidationReason::Resource, None)
}

struct TypesGuard(HashMap<crate::types::TypeVariableId, Type>);
impl TypesGuard {
    fn insert(&mut self, id: crate::types::TypeVariableId, ty: Type) {
        if let Some(displaced) = self.0.insert(id, ty) {
            crate::types::discard_type_iteratively(displaced);
        }
    }

    fn into_map(mut self) -> HashMap<crate::types::TypeVariableId, Type> {
        std::mem::take(&mut self.0)
    }
}
impl Drop for TypesGuard {
    fn drop(&mut self) {
        for (_, ty) in std::mem::take(&mut self.0) {
            crate::types::discard_type_iteratively(ty);
        }
    }
}
struct PatternGuard(Option<CorePattern>);
impl Drop for PatternGuard {
    fn drop(&mut self) {
        if let Some(pattern) = self.0.take() {
            pattern.discard_iteratively();
        }
    }
}
struct ArgumentsGuard(Vec<KindedArgument>);
impl ArgumentsGuard {
    fn into_boxed_slice(mut self) -> Box<[KindedArgument]> {
        std::mem::take(&mut self.0).into_boxed_slice()
    }
}
impl Drop for ArgumentsGuard {
    fn drop(&mut self) {
        for argument in std::mem::take(&mut self.0) {
            crate::types::discard_kinded_argument_iteratively(argument);
        }
    }
}

fn finalized_arguments(
    arguments: &[KindedArgument],
    rewrite: &mut dyn FnMut(&Type) -> Result<Type, super::BuildError>,
    rewrite_row: &mut dyn FnMut(
        &crate::types::EffectRow,
    ) -> Result<crate::types::EffectRow, super::BuildError>,
    work: &mut TypeWorkBudget,
) -> Result<Box<[KindedArgument]>, super::BuildError> {
    let exhausted = || super::BuildError::TypeWorkExceeded;
    work.charge(arguments.len()).map_err(|_| exhausted())?;
    let mut staged = ArgumentsGuard(Vec::new());
    staged
        .0
        .try_reserve_exact(arguments.len())
        .map_err(|_| exhausted())?;
    for argument in arguments {
        staged.0.push(match argument {
            KindedArgument::TypeArg(ty) => KindedArgument::TypeArg(rewrite(ty)?),
            KindedArgument::RowArg(row) => KindedArgument::RowArg(rewrite_row(row)?),
        });
    }
    Ok(staged.into_boxed_slice())
}

pub(super) fn finalize_arguments(
    arguments: &mut Box<[KindedArgument]>,
    rewrite: &mut dyn FnMut(&Type) -> Result<Type, super::BuildError>,
    rewrite_row: &mut dyn FnMut(
        &crate::types::EffectRow,
    ) -> Result<crate::types::EffectRow, super::BuildError>,
    work: &mut TypeWorkBudget,
) -> Result<(), super::BuildError> {
    let replacement = finalized_arguments(arguments, rewrite, rewrite_row, work)?;
    for argument in std::mem::replace(arguments, replacement).into_vec() {
        crate::types::discard_kinded_argument_iteratively(argument);
    }
    Ok(())
}

pub(super) fn finalize_instance(
    instance: &mut crate::types::EffectInstance,
    rewrite: &mut dyn FnMut(&Type) -> Result<Type, super::BuildError>,
    rewrite_row: &mut dyn FnMut(
        &crate::types::EffectRow,
    ) -> Result<crate::types::EffectRow, super::BuildError>,
    work: &mut TypeWorkBudget,
) -> Result<(), super::BuildError> {
    let arguments = finalized_arguments(instance.arguments(), rewrite, rewrite_row, work)?;
    *instance = crate::types::EffectInstance::new_kinded(instance.effect(), arguments);
    Ok(())
}

fn charge(work: &mut TypeWorkBudget, count: usize) -> Result<(), ValidationError> {
    work.charge(count).map_err(|()| resource())
}

/// Exact library ADT roles, separate from ordinary constructor spellings.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct SourceResourceCodec {
    pub(crate) acquire: [ConstructorId; 2],
    pub(crate) finish: [ConstructorId; 3],
    pub(crate) report: SourceResourceReportCodec,
}

/// Checked report roles retain defining identities, including their field order.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum SourceResourceReportCodec {
    CheckedScope {
        report: [ConstructorId; 2],
        completion: [ConstructorId; 3],
    },
    Scope {
        report: [ConstructorId; 2],
        completion: [ConstructorId; 3],
    },
    AcquiredOnly {
        report: [ConstructorId; 2],
    },
}

impl SourceResourceReportCodec {
    pub(crate) fn refusal(self) -> ConstructorId {
        match self {
            Self::Scope { report, .. } | Self::CheckedScope { report, .. } => report[0],
            Self::AcquiredOnly { report } => report[1],
        }
    }
}

/// A completed header phase, retaining original immutable source authority.
/// Only lifecycle and final-scope validation can supply execution permission.
#[derive(Debug)]
pub(crate) struct CheckedSourceResourceHeader {
    pub(crate) original: Arc<SourceResourceTypeFact>,
    pub(crate) owner: Arc<CheckedForeignOwner>,
    pub(crate) acquire: Arc<CheckedForeignSymbol>,
    pub(crate) teardown: Arc<CheckedForeignSymbol>,
    pub(crate) dependencies: Box<[crate::types::TypeVariableId]>,
    pub(crate) codec: SourceResourceCodec,
}

/// Borrows an ordinary result-codec application without copying its types.
fn application<'a>(
    ty: &'a Type,
    work: &mut TypeWorkBudget,
) -> Result<(NominalTypeId, Vec<&'a Type>), ValidationError> {
    let mut arguments = Vec::new();
    let mut head = ty;
    loop {
        charge(work, 1)?;
        match head {
            Type::Application(function, argument) => {
                arguments.try_reserve(1).map_err(|_| resource())?;
                arguments.push(argument.as_ref());
                head = function;
            }
            Type::Nominal(nominal) => {
                arguments.reverse();
                return Ok((*nominal, arguments));
            }
            _ => return Err(invalid()),
        }
    }
}

fn same(left: &Type, right: &Type, work: &mut TypeWorkBudget) -> Result<bool, ValidationError> {
    same_type_with_budget(left, right, work).map_err(|()| resource())
}

fn constructors<const N: usize>(
    nominal: NominalTypeId,
    parameter_count: usize,
    registry: &ResolvedRegistry,
    work: &mut TypeWorkBudget,
) -> Result<[ConstructorId; N], ValidationError> {
    charge(work, parameter_count.checked_add(N).ok_or_else(resource)?)?;
    let declaration = registry.nominal(nominal).ok_or_else(invalid)?;
    let parameters = registry.nominal_parameters(nominal).ok_or_else(invalid)?;
    if declaration.declaration_kind != crate::resolved::ResolvedNominalDeclarationKind::Data
        || parameters.len() != parameter_count
        || parameters
            .iter()
            .any(|parameter| parameter.kind != Kind::Type)
        || declaration.constructors.len() != N
    {
        return Err(invalid());
    }
    let mut ids = [ConstructorId::new(nominal, 0); N];
    for (index, id) in ids.iter_mut().enumerate() {
        let expected = ConstructorId::new(nominal, u32::try_from(index).map_err(|_| invalid())?);
        if declaration.constructors[index] != expected {
            return Err(invalid());
        }
        let constructor = registry.constructor(expected).ok_or_else(invalid)?;
        if constructor.owner != nominal || constructor.id != expected {
            return Err(invalid());
        }
        *id = expected;
    }
    Ok(ids)
}

fn payload(
    id: ConstructorId,
    registry: &ResolvedRegistry,
) -> Result<Option<&Type>, ValidationError> {
    Ok(registry
        .constructor(id)
        .ok_or_else(invalid)?
        .payload
        .as_ref())
}

fn variable(ty: &Type, id: crate::types::TypeVariableId) -> bool {
    matches!(ty, Type::Variable(actual) if *actual == id)
}

fn acquire_codec(
    nominal: NominalTypeId,
    registry: &ResolvedRegistry,
    work: &mut TypeWorkBudget,
) -> Result<[ConstructorId; 2], ValidationError> {
    let ids = constructors::<2>(nominal, 3, registry, work)?;
    let parameters = registry.nominal_parameters(nominal).ok_or_else(invalid)?;
    let Some(Type::Tuple(fields)) = payload(ids[0], registry)? else {
        return Err(invalid());
    };
    if fields.len() != 2
        || !variable(&fields[0], parameters[0].id)
        || !variable(&fields[1], parameters[1].id)
        || !payload(ids[1], registry)?.is_some_and(|ty| variable(ty, parameters[2].id))
    {
        return Err(invalid());
    }
    Ok(ids)
}

fn finish_codec(
    nominal: NominalTypeId,
    registry: &ResolvedRegistry,
    work: &mut TypeWorkBudget,
) -> Result<[ConstructorId; 3], ValidationError> {
    let ids = constructors::<3>(nominal, 2, registry, work)?;
    let parameters = registry.nominal_parameters(nominal).ok_or_else(invalid)?;
    let Some(Type::Tuple(fields)) = payload(ids[2], registry)? else {
        return Err(invalid());
    };
    if payload(ids[0], registry)?.is_some()
        || !payload(ids[1], registry)?.is_some_and(|ty| variable(ty, parameters[1].id))
        || fields.len() != 2
        || !variable(&fields[0], parameters[0].id)
        || !variable(&fields[1], parameters[1].id)
    {
        return Err(invalid());
    }
    Ok(ids)
}

fn report_codec(
    nominal: NominalTypeId,
    registry: &ResolvedRegistry,
    work: &mut TypeWorkBudget,
) -> Result<([ConstructorId; 2], [ConstructorId; 3]), ValidationError> {
    let ids = constructors::<2>(nominal, 3, registry, work)?;
    let parameters = registry.nominal_parameters(nominal).ok_or_else(invalid)?;
    let Some(Type::Tuple(fields)) = payload(ids[1], registry)? else {
        return Err(invalid());
    };
    if fields.len() != 2
        || !variable(&fields[0], parameters[2].id)
        || !payload(ids[0], registry)?.is_some_and(|ty| variable(ty, parameters[0].id))
    {
        return Err(invalid());
    }
    let (completion, arguments) = application(&fields[1], work)?;
    if arguments.len() != 1 || !variable(arguments[0], parameters[1].id) {
        return Err(invalid());
    }
    let completion_ids = constructors::<3>(completion, 1, registry, work)?;
    let error = registry
        .nominal_parameters(completion)
        .ok_or_else(invalid)?[0]
        .id;
    if payload(completion_ids[0], registry)?.is_some()
        || !payload(completion_ids[1], registry)?.is_some_and(|ty| variable(ty, error))
        || !payload(completion_ids[2], registry)?.is_some_and(|ty| variable(ty, error))
    {
        return Err(invalid());
    }
    Ok((ids, completion_ids))
}

fn acquired_only_codec(
    nominal: NominalTypeId,
    arguments: &[&Type],
    answer: crate::types::TypeVariableId,
    refusal: &Type,
    registry: &ResolvedRegistry,
    work: &mut TypeWorkBudget,
) -> Result<[ConstructorId; 2], ValidationError> {
    let ids = constructors::<2>(nominal, arguments.len(), registry, work)?;
    let parameters = registry.nominal_parameters(nominal).ok_or_else(invalid)?;
    let mut replacements = HashMap::new();
    charge(work, parameters.len())?;
    replacements
        .try_reserve(parameters.len())
        .map_err(|_| resource())?;
    for (parameter, argument) in parameters.iter().zip(arguments) {
        replacements.insert(parameter.id, *argument);
    }
    // Authenticate instantiated payloads rather than inventing an arity or
    // parameter order. Outcome<T> with a concrete error preserves builtin shape.
    for (index, id) in ids.iter().enumerate() {
        let ty = payload(*id, registry)?.ok_or_else(invalid)?;
        let instantiated = crate::types::IterativeTypeOwner::new(
            crate::types::substitute_type_variables_borrowed_with(
                ty,
                &replacements,
                |cells| charge(work, cells),
                resource,
            )?,
        );
        let valid = if index == 0 {
            variable(&instantiated, answer)
        } else {
            same(&instantiated, refusal, work)?
        };
        if !valid {
            return Err(invalid());
        }
    }
    Ok(ids)
}

fn dependency_state_identity(
    ty: &Type,
    registry: &ResolvedRegistry,
    work: &mut TypeWorkBudget,
) -> Result<Option<crate::types::TypeVariableId>, ValidationError> {
    if let Type::ResourceApply(id, arguments) = ty {
        let Some(header) = registry.source_resource_fact(*id) else {
            return Ok(None);
        };
        if arguments.len() != header.parameters.len() {
            return Err(invalid());
        }
        charge(work, arguments.len())?;
        for (argument, parameter) in arguments.iter().zip(&header.parameters) {
            if !matches!((argument, &parameter.kind), (KindedArgument::TypeArg(_), kind) if *kind != Kind::EffectRow)
                && !matches!(
                    (argument, &parameter.kind),
                    (KindedArgument::RowArg(_), Kind::EffectRow)
                )
            {
                return Err(invalid());
            }
        }
        let Some(KindedArgument::TypeArg(Type::Variable(identity))) =
            arguments.get(header.owned_position)
        else {
            return Err(invalid());
        };
        return Ok(Some(*identity));
    }
    if let Type::ForeignOwnerApply(nominal, _) = ty {
        let span = match registry.nominal_kind(*nominal).ok_or_else(invalid)? {
            crate::resolved::CanonicalNominalKind::Parameters { origin, .. }
            | crate::resolved::CanonicalNominalKind::Frozen { origin, .. }
            | crate::resolved::CanonicalNominalKind::RowBearingResource { origin, .. } => origin,
        };
        let map = |error: crate::foreign::checked_source::ForeignAdmissionError| {
            if error.is_resource_exhaustion() {
                resource()
            } else {
                invalid()
            }
        };
        let parameters =
            crate::foreign::source_owner::row_owner_parameters(*nominal, registry, span, work)
                .map_err(map)?;
        let arguments =
            crate::foreign::source_owner::state_arguments(ty, *nominal, parameters, span, work)
                .map_err(map)?;
        charge(work, registry.source_owner_candidate_count())?;
        let (prepared, index, _, _) = registry
            .source_owner_candidates()
            .find(|(_, _, id, _)| id == nominal)
            .ok_or_else(invalid)?;
        let Some(crate::foreign::source_owner::StateArgument::Type(Type::Variable(identity))) =
            arguments.get(prepared.owners()[index].owned_parameter())
        else {
            return Err(invalid());
        };
        return Ok(Some(*identity));
    }
    let mut head = ty;
    let mut arguments = Vec::new();
    while let Type::Application(function, argument) = head {
        push(&mut arguments, argument.as_ref(), work)?;
        head = function;
    }
    let Type::Nominal(nominal) = head else {
        return Ok(None);
    };
    charge(work, registry.source_resource_facts().count())?;
    if let Some(header) = registry
        .source_resource_facts()
        .find(|header| header.family == *nominal)
    {
        if arguments.len() != header.parameters.len() {
            // A structural walk also visits the partial application heads of
            // a fully saturated multi-parameter access type. Only the complete
            // value application has an owner identity; ordinary kind admission
            // independently rejects an unsaturated value type.
            return Ok(None);
        }
        arguments.reverse();
        let Some(Type::Variable(identity)) = arguments.get(header.owned_position).copied() else {
            return Err(invalid());
        };
        return Ok(Some(*identity));
    }
    charge(work, registry.source_owner_candidate_count())?;
    let Some((prepared, index, _, parameters)) = registry
        .source_owner_candidates()
        .find(|(_, _, candidate, _)| candidate == nominal)
    else {
        return Ok(None);
    };
    if arguments.len() != parameters.len() {
        return Ok(None);
    }
    crate::foreign::source_owner::authenticate_source_owner_candidate(
        prepared, index, *nominal, parameters, registry, work,
    )
    .map_err(|error| {
        if error.is_resource_exhaustion() {
            resource()
        } else {
            invalid()
        }
    })?;
    arguments.reverse();
    let Some(Type::Variable(identity)) = arguments
        .get(prepared.owners()[index].owned_parameter())
        .copied()
    else {
        return Err(invalid());
    };
    Ok(Some(*identity))
}

fn admit_private_data(
    ty: &Type,
    registry: &ResolvedRegistry,
    work: &mut TypeWorkBudget,
) -> Result<(), ValidationError> {
    // Candidate identity is sufficient for rejection, never native permission.
    // Walk arguments and defining constructor payloads: a nominal with a fixed
    // State or native-view field must not hide it merely because no constructor runs here.
    // Each declaration is visited once, so recursive ordinary ADTs terminate.
    // Their actual arguments are already visited in the enclosing type walk.
    let candidates = registry.source_foreign_nominal_count();
    let mut pending = one(ty, work)?;
    let mut visited = std::collections::HashSet::new();
    while let Some(ty) = pending.pop() {
        let mut nominals = Vec::new();
        let forbidden = crate::types::visit_type_structure_with_budget(ty, work, |node, work| {
            if let crate::types::TypeStructureNode::Type(
                Type::Nominal(nominal) | Type::ForeignOwnerApply(nominal, _),
            ) = node
            {
                work.charge(candidates)?;
                if registry.source_foreign_nominal(*nominal) {
                    return Ok(true);
                }
                work.charge(1)?;
                nominals.try_reserve(1).map_err(|_| ())?;
                nominals.push(*nominal);
            }
            Ok(false)
        })
        .map_err(|_| resource())?;
        if forbidden {
            return Err(invalid());
        }
        for nominal in nominals {
            charge(work, 1)?;
            visited.try_reserve(1).map_err(|_| resource())?;
            if !visited.insert(nominal) {
                continue;
            }
            charge(work, registry.source_resource_facts().count())?;
            if registry
                .source_resource_facts()
                .any(|header| header.family == nominal)
            {
                // Resource access has a distinct declaration category and no
                // ordinary constructor payload. Its complete arguments were
                // visited above; it is not its owner's native State family.
                continue;
            }
            let declaration = registry.nominal(nominal).ok_or_else(invalid)?;
            charge(work, declaration.constructors.len())?;
            for constructor in &declaration.constructors {
                if let Some(payload) = payload(*constructor, registry)? {
                    push(&mut pending, payload, work)?;
                }
            }
        }
    }
    Ok(())
}

impl CheckedSourceResourceHeader {
    pub(crate) fn admit(
        header: &Arc<SourceResourceTypeFact>,
        registry: &ResolvedRegistry,
        work: &mut TypeWorkBudget,
    ) -> Result<Self, ValidationError> {
        charge(work, 6)?;
        if !registry
            .source_resource_fact(header.id)
            .is_some_and(|original| Arc::ptr_eq(original, header))
            || header
                .parameters
                .get(header.owned_position)
                .is_none_or(|parameter| parameter.kind != Kind::Type)
        {
            return Err(invalid());
        }
        for other in registry.source_resource_facts() {
            charge(work, 1)?;
            if other.id != header.id && other.provider.interface.id == header.provider.interface.id
            {
                return Err(invalid());
            }
        }
        charge(work, header.parameters.len())?;
        if header
            .parameters
            .iter()
            .any(|parameter| !matches!(parameter.kind, Kind::Type | Kind::EffectRow))
        {
            return Err(invalid());
        }
        let state = header.state.ty.outer_nominal().ok_or_else(invalid)?;
        charge(work, registry.source_owner_candidate_count())?;
        let (prepared, index, _, parameters) = registry
            .source_owner_candidates()
            .find(|(_, _, id, _)| *id == state)
            .ok_or_else(invalid)?;
        let checked = prepared.checked_contract().is_some();
        charge(work, 1)?;
        if checked
            != matches!(
                header.codec.kind,
                SurfaceResourceReportCodecKind::CheckedScope
            )
            || checked != header.host.is_some()
        {
            return Err(invalid());
        }
        let host_identity = if let Some(host) = header.host {
            charge(work, 1)?;
            let parameter = header.parameters.get(host.position).ok_or_else(invalid)?;
            if host.position == header.owned_position
                || parameter.kind != Kind::Type
                || host.span.source() != header.owned_origin.primary_span().source()
            {
                return Err(invalid());
            }
            Some(parameter.id)
        } else {
            None
        };
        crate::foreign::source_owner::authenticate_source_owner_candidate(
            prepared, index, state, parameters, registry, work,
        )
        .map_err(|error| {
            if error.is_resource_exhaustion() {
                resource()
            } else {
                invalid()
            }
        })?;
        let state_arguments = crate::foreign::source_owner::state_arguments(
            &header.state.ty,
            state,
            parameters,
            header.state.span,
            work,
        )
        .map_err(|error| {
            if error.is_resource_exhaustion() {
                resource()
            } else {
                invalid()
            }
        })?;
        let (acquire_codec, finish_codec, report) = if checked {
            let codec = checked_codec::authenticate(header, registry, work)?;
            (codec.acquire, codec.finish, codec.report)
        } else {
            let (acquisition, acquisition_arguments) = application(&header.acquisition.ty, work)?;
            let (finish, finish_arguments) = application(&header.completion.ty, work)?;
            let (scope, scope_arguments) = application(&header.result.ty, work)?;
            if acquisition_arguments.len() != 3
                || finish_arguments.len() != 2
                || !same(acquisition_arguments[0], &header.state.ty, work)?
                || !same(acquisition_arguments[1], &header.data.ty, work)?
                || !same(finish_arguments[0], &header.state.ty, work)?
            {
                return Err(invalid());
            }
            let acquire_codec = acquire_codec(acquisition, registry, work)?;
            let finish_codec = finish_codec(finish, registry, work)?;
            let report = match header.codec.kind {
                SurfaceResourceReportCodecKind::CheckedScope => return Err(invalid()),
                SurfaceResourceReportCodecKind::Scope => {
                    if scope_arguments.len() != 3
                        || !same(acquisition_arguments[2], scope_arguments[0], work)?
                        || !same(finish_arguments[1], scope_arguments[1], work)?
                        || !variable(scope_arguments[2], header.answer.id)
                    {
                        return Err(invalid());
                    }
                    let (report, completion) = report_codec(scope, registry, work)?;
                    SourceResourceReportCodec::Scope { report, completion }
                }
                SurfaceResourceReportCodecKind::AcquiredOnly => {
                    let report = acquired_only_codec(
                        scope,
                        &scope_arguments,
                        header.answer.id,
                        acquisition_arguments[2],
                        registry,
                        work,
                    )?;
                    SourceResourceReportCodec::AcquiredOnly { report }
                }
            };
            (acquire_codec, finish_codec, report)
        };
        let mut acquiring = None;
        let mut tearing_down = None;
        charge(work, header.interpreted.len())?;
        for effect in &header.interpreted {
            let operation = OperationId::new(effect.instance.effect(), 0);
            let symbol = registry.native_symbol(operation).ok_or_else(invalid)?;
            let owner = symbol.owner().ok_or_else(invalid)?;
            if let Some(host_identity) = host_identity {
                let contract = owner.prepared().checked_contract().ok_or_else(invalid)?;
                charge(work, contract.owners().len())?;
                let selection = contract
                    .owners()
                    .iter()
                    .find(|selection| selection.member_index() == owner.owner().member_index())
                    .ok_or_else(invalid)?;
                if state_arguments.get(selection.host_parameter()).is_none_or(|argument|
                    !matches!(argument, crate::foreign::source_owner::StateArgument::Type(ty) if variable(ty, host_identity)))
                { return Err(invalid()); }
                let instance = crate::foreign::checked_source::checked_host_instance(
                    symbol,
                    &effect.instance,
                    work,
                )
                .map_err(|error| {
                    if error.is_resource_exhaustion() {
                        resource()
                    } else {
                        invalid()
                    }
                })?
                .ok_or_else(invalid)?;
                if !matches!(instance.arguments(), [KindedArgument::TypeArg(Type::Variable(id))] if *id == host_identity)
                {
                    return Err(invalid());
                }
            } else if symbol.prepared().checked_contract().is_some() {
                return Err(invalid());
            }
            if owner.nominal() != state
                || owner.parameter_ids().len() != state_arguments.len()
                || state_arguments
                    .get(owner.owned_parameter())
                    .is_none_or(|argument| !matches!(argument, crate::foreign::source_owner::StateArgument::Type(ty) if variable(ty, header.parameters[header.owned_position].id)))
            {
                return Err(invalid());
            }
            let crate::foreign::source_contract::PreparedForeignCall::Owner(role) =
                symbol.symbol().call()
            else {
                return Err(invalid());
            };
            let arguments = match role {
                PreparedOwnerCall::Acquire { application, .. }
                | PreparedOwnerCall::Borrow { application, .. }
                | PreparedOwnerCall::OutputAcquire { application, .. }
                | PreparedOwnerCall::Teardown { application, .. }
                | PreparedOwnerCall::StatusTeardown { application, .. } => application.arguments(),
            };
            charge(work, arguments.len())?;
            if arguments.len() != state_arguments.len() {
                return Err(invalid());
            }
            for (mapping, state_argument) in arguments.iter().zip(&state_arguments) {
                use crate::foreign::{
                    source_contract::PreparedOwnerArgument, source_owner::StateArgument,
                };
                let position = match mapping {
                    PreparedOwnerArgument::Type(position)
                    | PreparedOwnerArgument::EffectRow(position) => *position,
                };
                let actual = effect
                    .instance
                    .arguments()
                    .get(position)
                    .ok_or_else(invalid)?;
                let valid = match (mapping, state_argument, actual) {
                    (
                        PreparedOwnerArgument::Type(_),
                        StateArgument::Type(expected),
                        KindedArgument::TypeArg(actual),
                    ) => same(actual, expected, work)?,
                    (
                        PreparedOwnerArgument::EffectRow(_),
                        StateArgument::EffectRow(expected),
                        KindedArgument::RowArg(actual),
                    ) => crate::types::same_effect_rows_with_budget(actual, expected, work)
                        .map_err(|_| resource())?,
                    _ => false,
                };
                if !valid {
                    return Err(invalid());
                }
            }
            match role {
                PreparedOwnerCall::Borrow { .. } => {}
                PreparedOwnerCall::Acquire { .. } | PreparedOwnerCall::OutputAcquire { .. }
                    if acquiring.is_none() =>
                {
                    acquiring = Some(Arc::clone(symbol))
                }
                PreparedOwnerCall::Teardown { .. } | PreparedOwnerCall::StatusTeardown { .. }
                    if tearing_down.is_none() =>
                {
                    tearing_down = Some(Arc::clone(symbol))
                }
                _ => return Err(invalid()),
            }
        }
        let acquire = acquiring.ok_or_else(invalid)?;
        let teardown = tearing_down.ok_or_else(invalid)?;
        let owner = acquire.owner().ok_or_else(invalid)?;
        if !teardown
            .owner()
            .is_some_and(|other| Arc::ptr_eq(owner, other))
        {
            return Err(invalid());
        }
        use crate::foreign::source_contract::PreparedAddressRepresentation;
        if !matches!(
            (owner.owner().representation(), acquire.owner_role()),
            (
                PreparedAddressRepresentation::Opaque,
                Some(PreparedOwnerCall::Acquire {
                    initialized_bytes: None,
                    ..
                })
            ) | (
                PreparedAddressRepresentation::Opaque,
                Some(PreparedOwnerCall::OutputAcquire { .. })
            ) | (
                PreparedAddressRepresentation::Bytes,
                Some(PreparedOwnerCall::Acquire {
                    initialized_bytes: Some(_),
                    ..
                })
            )
        ) || !matches!(
            (teardown.owner_role(), teardown.symbol().result()),
            (
                Some(PreparedOwnerCall::Teardown { .. }),
                crate::foreign::source_contract::PreparedAbiResult::Void
            ) | (
                Some(PreparedOwnerCall::StatusTeardown { .. }),
                crate::foreign::source_contract::PreparedAbiResult::Scalar(_)
            )
        ) {
            return Err(invalid());
        }
        if checked
            && (!owner.owner().retained_parameters().is_empty()
                || !matches!(
                    owner.owner().representation(),
                    PreparedAddressRepresentation::Opaque
                )
                || !matches!(
                    acquire.owner_role(),
                    Some(PreparedOwnerCall::Acquire {
                        initialized_bytes: None,
                        ..
                    })
                )
                || !matches!(
                    teardown.owner_role(),
                    Some(PreparedOwnerCall::Teardown { .. })
                )
                || !matches!(
                    teardown.symbol().result(),
                    crate::foreign::source_contract::PreparedAbiResult::Void
                )
                || teardown.symbol().operands().len() != 1)
        {
            return Err(invalid());
        }
        let owned = header.parameters[header.owned_position].id;
        let mut dependencies = Vec::new();
        charge(work, owner.owner().retained_parameters().len())?;
        dependencies
            .try_reserve_exact(owner.owner().retained_parameters().len())
            .map_err(|_| resource())?;
        for position in owner.owner().retained_parameters() {
            let Some(crate::foreign::source_owner::StateArgument::Type(Type::Variable(identity))) =
                state_arguments.get(*position)
            else {
                return Err(invalid());
            };
            charge(work, header.parameters.len())?;
            if *identity == owned
                || !header
                    .parameters
                    .iter()
                    .any(|parameter| parameter.id == *identity && parameter.kind == Kind::Type)
            {
                return Err(invalid());
            }
            dependencies.push(*identity);
        }
        admit_private_data(&header.data.ty, registry, work)?;
        for ty in [&header.input.ty, &header.data.ty] {
            let mut role_failure = None;
            let forbidden =
                crate::types::visit_type_structure_with_budget(ty, work, |node, work| match node {
                    crate::types::TypeStructureNode::Type(Type::Variable(id)) => Ok(*id == owned),
                    crate::types::TypeStructureNode::Type(
                        ty @ (Type::Application(_, _)
                        | Type::ResourceApply(_, _)
                        | Type::ForeignOwnerApply(_, _)),
                    ) => {
                        let identity = match dependency_state_identity(ty, registry, work) {
                            Ok(identity) => identity,
                            Err(error) => {
                                role_failure = Some(error);
                                return Ok(true);
                            }
                        };
                        work.charge(dependencies.len())?;
                        Ok(identity.is_some_and(|identity| !dependencies.contains(&identity)))
                    }
                    _ => Ok(false),
                })
                .map_err(|_| resource())?;
            if let Some(failure) = role_failure {
                return Err(failure);
            }
            if forbidden {
                return Err(invalid());
            }
        }
        charge(work, 1)?;
        Ok(Self {
            original: Arc::clone(header),
            owner: Arc::clone(owner),
            acquire,
            teardown,
            dependencies: dependencies.into_boxed_slice(),
            codec: SourceResourceCodec {
                acquire: acquire_codec,
                finish: finish_codec,
                report,
            },
        })
    }
    /// Constructs the ordinary value type for the admitted family category.
    /// The complete tagged instance remains separate in the scope descriptor.
    pub(crate) fn access_type(
        &self,
        arguments: &[KindedArgument],
        work: &mut TypeWorkBudget,
    ) -> Result<Type, ValidationError> {
        charge(work, self.original.parameters.len() + arguments.len())?;
        if self.original.parameters.len() != arguments.len() {
            return Err(invalid());
        }
        let mut has_row = false;
        for (formal, actual) in self.original.parameters.iter().zip(arguments) {
            match (&formal.kind, actual) {
                (Kind::Type, KindedArgument::TypeArg(_)) => {}
                (Kind::EffectRow, KindedArgument::RowArg(_)) => has_row = true,
                _ => return Err(invalid()),
            }
        }
        if has_row {
            let arguments =
                crate::types::clone_kinded_arguments_with_budget(arguments.iter(), work)
                    .map_err(|_| resource())?;
            return Ok(Type::ResourceApply(self.original.id, arguments));
        }
        let mut access = crate::types::IterativeTypeOwner::new(Type::Nominal(self.original.family));
        for argument in arguments {
            let KindedArgument::TypeArg(argument) = argument else {
                return Err(invalid());
            };
            let argument = crate::types::IterativeTypeOwner::new(
                crate::types::clone_type_with_budget(argument, work).map_err(|_| resource())?,
            );
            charge(work, 1)?;
            access = crate::types::IterativeTypeOwner::new(Type::Application(
                Box::new(access.into_inner()),
                Box::new(argument.into_inner()),
            ));
        }
        Ok(access.into_inner())
    }
}

/// Ordinary global scheme loans. Final Core must close every loan with its
/// actual lexical global binder; this table grants no lifecycle permission.
#[derive(Default)]
pub(crate) struct SourceResourceGlobals {
    types: HashMap<crate::resolved::BinderId, crate::types::IterativeTypeOwner>,
}
impl SourceResourceGlobals {
    pub(crate) fn new() -> Self {
        Self::default()
    }
}
impl std::fmt::Debug for SourceResourceGlobals {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("SourceResourceGlobals")
            .field("schemes", &self.types.len())
            .finish()
    }
}
impl std::ops::Deref for SourceResourceGlobals {
    type Target = HashMap<crate::resolved::BinderId, crate::types::IterativeTypeOwner>;
    fn deref(&self) -> &Self::Target {
        &self.types
    }
}
impl std::ops::DerefMut for SourceResourceGlobals {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.types
    }
}

/// Immutable defining forests. This certificate grants compiler copying input,
/// and cannot be converted to a validated executable program.
#[derive(Debug)]
pub(crate) struct CheckedSourceResourceTemplate {
    header: Arc<CheckedSourceResourceHeader>,
    module_sources: Box<[(crate::module::ModuleId, crate::source::SourceId)]>,
    globals: Arc<SourceResourceGlobals>,
    acquire: UnvalidatedEffectProgram,
    finish: UnvalidatedEffectProgram,
    handler: UnvalidatedEffectProgram,
    handler_rows: Option<SourceHandlerRows>,
    acquire_entry: (TypedBinder, NodeId),
    finish_entry: (TypedBinder, NodeId),
    handler_entry: (TypedBinder, NodeId),
    methods: Box<[(crate::interface::MethodId, crate::types::OperationId)]>,
    byte_calls: [Box<[SourceByteCall]>; 3],
    window_calls: [Box<[SourceWindowCall]>; 3],
}

impl CheckedSourceResourceTemplate {
    pub(in crate::core) fn visit_semantic_type_variables(
        &self,
        uses: &mut crate::core::validate::semantic_type_variables::UnusedVariables<'_>,
    ) -> Result<(), ()> {
        uses.source_header(&self.header.original)?;
        uses.charge(self.globals.len())?;
        for ty in self.globals.values() {
            uses.ty(ty)?;
        }
        for (entry, _) in [&self.acquire_entry, &self.finish_entry, &self.handler_entry] {
            uses.ty(entry.ty())?;
        }
        if let Some(rows) = &self.handler_rows {
            uses.row(&rows.inputs.direct)?;
            uses.pending_rows(&rows.inputs.pending)?;
            rows.recipe.visit_semantic_type_variables(uses)?;
            rows.capture.visit_semantic_type_variables(uses)?;
        }
        Ok(())
    }
}

#[derive(Debug)]
pub(crate) struct CheckedSourceResourceTemplates {
    records: Box<[Arc<CheckedSourceResourceTemplate>]>,
}
impl CheckedSourceResourceTemplates {
    pub(crate) fn new(
        records: Vec<Arc<CheckedSourceResourceTemplate>>,
        work: &mut TypeWorkBudget,
    ) -> Result<Self, ValidationError> {
        charge(work, records.len())?;
        let mut identities = std::collections::HashSet::new();
        identities
            .try_reserve(records.len())
            .map_err(|_| resource())?;
        for record in &records {
            charge(work, 1)?;
            if !identities.insert(record.header.original.id) {
                return Err(invalid());
            }
        }
        Ok(Self {
            records: records.into_boxed_slice(),
        })
    }
    pub(crate) fn len(&self) -> usize {
        self.records.len()
    }
    pub(crate) fn resource(&self, index: usize) -> Option<&Arc<CheckedSourceResourceTemplate>> {
        self.records.get(index)
    }
    pub(crate) fn headers(&self) -> impl Iterator<Item = &Arc<CheckedSourceResourceHeader>> {
        self.records.iter().map(|record| &record.header)
    }
}

fn node(
    program: &UnvalidatedEffectProgram,
    id: NodeId,
) -> Result<&super::dialect::StoredNode<super::EffectOperationFamily>, ValidationError> {
    if id.arena() != program.arena {
        return Err(invalid());
    }
    program
        .nodes
        .get(id.index().map_err(|_| invalid())?)
        .ok_or_else(invalid)
}

fn pure(node: &super::dialect::StoredNode<super::EffectOperationFamily>) -> Option<&PureExprKind> {
    match &node.kind {
        EffectExprKind::Pure(pure) => Some(pure),
        _ => None,
    }
}

fn entry(
    program: &UnvalidatedEffectProgram,
    header: &SourceResourceTypeFact,
    answer: bool,
    work: &mut TypeWorkBudget,
) -> Result<(TypedBinder, NodeId), ValidationError> {
    let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::TypeAbstraction(
        abstraction,
    ))) = &node(program, program.root)?.kind
    else {
        return Err(invalid());
    };
    charge(work, abstraction.parameters().len())?;
    if abstraction.parameters().len() != header.parameters.len() + 2 * usize::from(answer) {
        return Err(invalid());
    }
    for ((id, kind), formal) in abstraction.parameters().iter().zip(&header.parameters) {
        if *id != formal.id || *kind != formal.kind {
            return Err(invalid());
        }
    }
    if answer
        && (abstraction.parameters().get(header.parameters.len())
            != Some(&(header.answer.id, Kind::Type))
            || !matches!(
                abstraction.parameters().last(),
                Some((crate::types::TypeVariableId::Generated(_), Kind::EffectRow))
            ))
    {
        return Err(invalid());
    }
    let EffectExprKind::Pure(PureExprKind::Value(PureValue::Function(function))) =
        &node(program, abstraction.body())?.kind
    else {
        return Err(invalid());
    };
    charge(work, 1)?;
    let parameter = function.parameter();
    let ty = crate::types::IterativeTypeOwner::new(
        crate::types::clone_type_with_budget(parameter.ty(), work).map_err(|_| resource())?,
    );
    let origin = crate::resolved::clone_effect_origin_with_budget(parameter.origin(), work)
        .map_err(|_| resource())?;
    let retained = TypedBinder::new(program.arena, parameter.id(), ty.into_inner(), origin);
    Ok((retained, function.body()))
}

/// Declaration categories never stand in for a graph's lexical binding proof.
/// Match the complete original phase inventory before any registry admission.
fn check_original_window_declarations(
    declarations: &[crate::resolved::SourceWindowDeclaration],
    acquire: &UnvalidatedEffectProgram,
    finish: &UnvalidatedEffectProgram,
    handler: &UnvalidatedEffectProgram,
    work: &mut TypeWorkBudget,
) -> Result<(), ValidationError> {
    use crate::resolved::SourceWindowPhase;
    charge(work, declarations.len())?;
    let mut seen = Vec::new();
    seen.try_reserve_exact(declarations.len())
        .map_err(|_| resource())?;
    seen.resize(declarations.len(), false);
    for (phase, program) in [
        (SourceWindowPhase::Acquire, acquire),
        (SourceWindowPhase::Finish, finish),
        (SourceWindowPhase::Handler, handler),
    ] {
        for node in &program.nodes {
            charge(work, 1)?;
            if let EffectExprKind::Operation(EffectOperation::SourceCopyWindow(window)) = &node.kind
            {
                charge(work, declarations.len())?;
                let index = declarations
                    .iter()
                    .position(|declaration| declaration.identity == window.identity())
                    .ok_or_else(invalid)?;
                let declaration = &declarations[index];
                let parameter = program
                    .registry
                    .type_variable(declaration.identity)
                    .ok_or_else(invalid)?;
                if std::mem::replace(&mut seen[index], true)
                    || declaration.phase != phase
                    || declaration.family != window.family().nominal()
                    || node
                        .origin
                        .as_ref()
                        .map(crate::source::Origin::primary_span)
                        != Some(declaration.span)
                    || declaration.identity_span != parameter.origin.primary_span()
                    || parameter.kind != Kind::Type
                {
                    return Err(invalid());
                }
            }
        }
    }
    charge(work, seen.len())?;
    if seen.iter().any(|seen| !seen) {
        return Err(invalid());
    }
    Ok(())
}

impl CheckedSourceResourceTemplate {
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn admit_with_globals(
        header: Arc<CheckedSourceResourceHeader>,
        acquire: UnvalidatedEffectProgram,
        finish: UnvalidatedEffectProgram,
        handler: UnvalidatedEffectProgram,
        handler_inputs: Option<SourceHandlerRowInputs>,
        globals: Arc<SourceResourceGlobals>,
        sources: &[&crate::source::SourceFile],
        module_sources: &[(crate::module::ModuleId, crate::source::SourceId)],
        work: &mut TypeWorkBudget,
        session: &mut super::validate::SourceResourceStructureSession<'_>,
    ) -> Result<Self, ValidationError> {
        check_original_window_declarations(
            &header.original.windows,
            &acquire,
            &finish,
            &handler,
            work,
        )?;
        // Retain only loans actually referenced by these original forests.
        // Their caller/definition Type and Row vectors remain on ordinary Core
        // variable/application nodes and close again against final globals.
        let mut used = HashMap::new();
        for program in [&acquire, &finish, &handler]
            .into_iter()
            .filter(|_| !globals.is_empty())
        {
            for stored in &program.nodes {
                charge(work, 1)?;
                if let EffectExprKind::Pure(PureExprKind::Variable(variable)) = &stored.kind
                    && let Some(ty) = globals.get(&variable.binder())
                    && !used.contains_key(&variable.binder())
                {
                    if variable.binder().module().is_none()
                        || program
                            .registry
                            .scalar_preflight(variable.binder())
                            .is_some()
                    {
                        return Err(invalid());
                    }
                    let ty = crate::types::IterativeTypeOwner::new(
                        crate::types::clone_type_with_budget(ty, work).map_err(|_| resource())?,
                    );
                    used.try_reserve(1).map_err(|_| resource())?;
                    used.insert(variable.binder(), ty);
                }
            }
        }
        let globals = Arc::new(SourceResourceGlobals { types: used });
        let mut handler_graph = handler_inputs
            .as_ref()
            .map(|inputs| SourceHandlerGraph::reconstruct(&handler, &header, inputs, work))
            .transpose()?;
        let recipe = handler_graph
            .as_ref()
            .map(|graph| {
                super::provider::HandlerRowRecipeDraft::reconstruct(&graph.handler_graph(), work)
            })
            .transpose()?;
        if let Some(graph) = &mut handler_graph {
            graph.recipe = recipe.as_ref();
        }
        let capture = handler_graph
            .as_ref()
            .map(|graph| {
                charge(work, handler.nodes.len())?;
                let mut correspondence = Vec::new();
                correspondence
                    .try_reserve_exact(handler.nodes.len())
                    .map_err(|_| resource())?;
                for ordinal in 0..handler.nodes.len() {
                    correspondence.push(Some(NodeId::new(
                        handler.arena,
                        u32::try_from(ordinal).map_err(|_| resource())?,
                    )));
                }
                super::capture::reconstruct_conditional_handler_capture(
                    &graph.handler_graph(),
                    &handler.nodes,
                    handler.arena,
                    &correspondence,
                    &[],
                    &[],
                    &[],
                    &[],
                    &[],
                    None,
                    work,
                )
                .map_err(|failure| match failure {
                    super::capture::Failure::Resource => resource(),
                    _ => invalid(),
                })
            })
            .transpose()?;
        // Ordinary graph, kind, scope, effect, registry and provenance checking
        // precedes the resource-specific phase and owner-lineage proof.
        for (program, answer) in [(&acquire, false), (&finish, false), (&handler, true)] {
            if !Arc::ptr_eq(&program.registry, &acquire.registry) {
                return Err(invalid());
            }
            let diagnostic = session.check_with_handler_graph(
                program,
                &header.original,
                answer,
                sources,
                module_sources,
                &globals,
                if answer { handler_graph.as_ref() } else { None },
                work,
            );
            #[cfg(test)]
            eprintln!("checked lifecycle original structure answer={answer}: {diagnostic:?}");
            diagnostic?;
        }
        let canonical =
            CheckedSourceResourceHeader::admit(&header.original, &acquire.registry, work)?;
        charge(work, header.dependencies.len().saturating_add(3))?;
        if !Arc::ptr_eq(&canonical.owner, &header.owner)
            || !Arc::ptr_eq(&canonical.acquire, &header.acquire)
            || !Arc::ptr_eq(&canonical.teardown, &header.teardown)
            || canonical.dependencies != header.dependencies
            || canonical.codec != header.codec
        {
            return Err(invalid());
        }
        #[cfg(test)]
        eprintln!("checked lifecycle header complete");
        let methods = check_provider_association(&header, &handler, work)?;
        #[cfg(test)]
        eprintln!("checked lifecycle association complete");
        let acquire_entry = entry(&acquire, &header.original, false, work)?;
        let finish_entry = entry(&finish, &header.original, false, work)?;
        let handler_entry = entry(&handler, &header.original, true, work)?;
        charge(work, 2)?;
        let mut state_data_fields = Vec::new();
        state_data_fields
            .try_reserve_exact(2)
            .map_err(|_| resource())?;
        let state = crate::types::IterativeTypeOwner::new(
            crate::types::clone_type_with_budget(&header.original.state.ty, work)
                .map_err(|_| resource())?,
        );
        let data = crate::types::IterativeTypeOwner::new(
            crate::types::clone_type_with_budget(&header.original.data.ty, work)
                .map_err(|_| resource())?,
        );
        state_data_fields.push(state.into_inner());
        state_data_fields.push(data.into_inner());
        let state_data = crate::types::IterativeTypeOwner::new(Type::Tuple(
            state_data_fields.into_boxed_slice(),
        ));
        if !same(acquire_entry.0.ty(), &header.original.input.ty, work)?
            || !same(finish_entry.0.ty(), &state_data, work)?
            || !same(handler_entry.0.ty(), &state_data, work)?
            || !same(
                &node(&acquire, acquire_entry.1)?.ty,
                &header.original.acquisition.ty,
                work,
            )?
            || !same(
                &node(&finish, finish_entry.1)?.ty,
                &header.original.completion.ty,
                work,
            )?
        {
            return Err(invalid());
        }
        let EffectExprKind::Pure(PureExprKind::Value(PureValue::Function(answer))) =
            &node(&handler, handler_entry.1)?.kind
        else {
            return Err(invalid());
        };
        let Type::EffectfulFunction(domain, codomain) = answer.parameter().ty() else {
            return Err(invalid());
        };
        if !same(domain, &Type::Unit, work)?
            || !variable(codomain.value(), header.original.answer.id)
            || !codomain.effects().tail().is_some_and(|tail| {
                tail.variable()
                    == crate::types::EffectRowVariable::rigid(Self::handler_continuation_in(
                        &handler,
                    ))
            })
            || !codomain
                .effects()
                .known()
                .iter()
                .any(|effect| effect.effect() == header.original.provided.instance.effect())
        {
            return Err(invalid());
        }
        let residual = codomain
            .effects()
            .remove_exact_with_budget(&header.original.provided.instance, work)
            .map_err(|_| resource())?
            .map_err(|_| invalid())?;
        if !crate::types::same_effect_rows_with_budget(
            &residual,
            &node(&handler, answer.body())?.effects,
            work,
        )
        .map_err(|_| resource())?
        {
            return Err(invalid());
        }
        let handler_body = answer.body();
        #[cfg(test)]
        eprintln!("checked lifecycle entries complete");
        let acquire_calls = check_flow(
            &acquire,
            &header,
            &acquire_entry,
            SourceResourcePhase::Acquire,
            &globals,
            work,
        )?;
        let finish_calls = check_flow(
            &finish,
            &header,
            &finish_entry,
            SourceResourcePhase::Finish,
            &globals,
            work,
        )?;
        let handler_calls = check_handler(
            &handler,
            &header,
            &handler_entry.0,
            answer,
            &globals,
            handler_graph.as_ref(),
            work,
        )?;
        charge(work, module_sources.len())?;
        let mut retained_sources = Vec::new();
        retained_sources
            .try_reserve_exact(module_sources.len())
            .map_err(|_| resource())?;
        retained_sources.extend_from_slice(module_sources);
        drop(handler_graph);
        let handler_rows = match (handler_inputs, recipe, capture) {
            (Some(inputs), Some(recipe), Some(capture)) => Some(SourceHandlerRows {
                inputs,
                recipe,
                capture,
            }),
            (None, None, None) => None,
            _ => return Err(invalid()),
        };
        Ok(Self {
            header,
            module_sources: retained_sources.into_boxed_slice(),
            globals,
            acquire,
            finish,
            handler,
            handler_rows,
            acquire_entry,
            finish_entry,
            handler_entry: (handler_entry.0, handler_body),
            methods,
            byte_calls: [
                acquire_calls.byte_calls,
                finish_calls.byte_calls,
                handler_calls.byte_calls,
            ],
            window_calls: [
                acquire_calls.window_calls,
                finish_calls.window_calls,
                handler_calls.window_calls,
            ],
        })
    }
    pub(crate) fn header(&self) -> &Arc<CheckedSourceResourceHeader> {
        &self.header
    }
    pub(crate) fn module_sources(&self) -> &[(crate::module::ModuleId, crate::source::SourceId)] {
        &self.module_sources
    }
    pub(crate) fn original_registry(&self) -> &Arc<ResolvedRegistry> {
        &self.acquire.registry
    }
    pub(crate) fn globals(&self) -> &SourceResourceGlobals {
        &self.globals
    }
    pub(crate) fn methods(&self) -> &[(crate::interface::MethodId, crate::types::OperationId)] {
        &self.methods
    }
    pub(crate) fn original_acquire(&self) -> &UnvalidatedEffectProgram {
        &self.acquire
    }
    pub(crate) fn original_finish(&self) -> &UnvalidatedEffectProgram {
        &self.finish
    }
    pub(crate) fn original_handler(&self) -> &UnvalidatedEffectProgram {
        &self.handler
    }
    pub(crate) fn acquire_entry(&self) -> (&TypedBinder, NodeId) {
        (&self.acquire_entry.0, self.acquire_entry.1)
    }
    pub(crate) fn finish_entry(&self) -> (&TypedBinder, NodeId) {
        (&self.finish_entry.0, self.finish_entry.1)
    }
    pub(crate) fn handler_entry(&self) -> (&TypedBinder, NodeId) {
        (&self.handler_entry.0, self.handler_entry.1)
    }
    fn handler_continuation_in(program: &UnvalidatedEffectProgram) -> crate::types::TypeVariableId {
        let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::TypeAbstraction(
            abstraction,
        ))) = &node(program, program.root)
            .expect("checked source handler root")
            .kind
        else {
            unreachable!("checked source handler abstraction")
        };
        abstraction
            .parameters()
            .last()
            .expect("checked source continuation parameter")
            .0
    }
    pub(crate) fn handler_continuation(&self) -> crate::types::TypeVariableId {
        Self::handler_continuation_in(&self.handler)
    }
    pub(crate) fn handler_direct_row(
        &self,
        work: &mut TypeWorkBudget,
    ) -> Result<crate::types::EffectRow, ValidationError> {
        if let Some(rows) = &self.handler_rows {
            return crate::types::clone_effect_row_with_budget(&rows.inputs.direct, work)
                .map_err(|_| resource());
        }
        crate::types::rebuild_effect_row_with_budget(
            node(&self.handler, self.handler_entry.1)?
                .effects
                .known()
                .iter(),
            None,
            std::iter::empty(),
            crate::types::clone_type_with_budget,
            work,
        )
        .map_err(|_| resource())
    }
    pub(crate) fn lifecycle_row(
        &self,
        acquire: bool,
        work: &mut TypeWorkBudget,
    ) -> Result<crate::types::EffectRow, ValidationError> {
        let (program, root) = if acquire {
            (&self.acquire, self.acquire_entry.1)
        } else {
            (&self.finish, self.finish_entry.1)
        };
        crate::types::clone_effect_row_with_budget(&node(program, root)?.effects, work)
            .map_err(|_| resource())
    }
    pub(crate) fn handler_pattern(&self) -> &CorePattern {
        let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Match(matching))) =
            &node(&self.handler, self.handler_entry.1)
                .expect("checked source handler pattern")
                .kind
        else {
            unreachable!("checked source handler match")
        };
        matching.arms()[0].pattern()
    }
    /// Original, independently checked lexical window binders for the linked
    /// registry inventory. This exposes no mutable graph or admission bypass.
    pub(crate) fn original_window_binders(
        &self,
        work: &mut TypeWorkBudget,
    ) -> Result<Vec<(NodeId, &crate::resolved::ResolvedTypeVariable)>, ValidationError> {
        let mut result = Vec::new();
        for original in [
            self.original_acquire(),
            self.original_finish(),
            self.original_handler(),
        ] {
            charge(work, original.nodes.len())?;
            for (index, node) in original.nodes.iter().enumerate() {
                if let EffectExprKind::Operation(EffectOperation::SourceCopyWindow(window)) =
                    &node.kind
                {
                    let canonical = original
                        .registry
                        .type_variable(window.identity())
                        .ok_or_else(invalid)?;
                    let id = NodeId::new(
                        original.arena,
                        u32::try_from(index).map_err(|_| resource())?,
                    );
                    push(&mut result, (id, canonical), work)?;
                }
            }
        }
        Ok(result)
    }

    pub(crate) fn original_handler_node(&self) -> &super::HandlerNode {
        let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Match(matching))) =
            &node(&self.handler, self.handler_entry.1)
                .expect("checked source handler pattern")
                .kind
        else {
            unreachable!("checked source handler match")
        };
        let EffectExprKind::Operation(EffectOperation::Handler(handler)) =
            &node(&self.handler, matching.arms()[0].body())
                .expect("checked source handler")
                .kind
        else {
            unreachable!("checked source handler")
        };
        handler
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum SourceResourcePhase {
    Acquire,
    Finish,
    Handler,
}
// Flat symbolic records: tuples and constructors retain scalar indices only.
// No symbolic value, failure path or arena disposal recurses through host heaps.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct SourceByteCall {
    pub(crate) apply: Option<NodeId>,
    pub(crate) application: NodeId,
    pub(crate) function: crate::resolved::BinderId,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct SourceWindowCall {
    request: NodeId,
    window: NodeId,
}
struct SourcePhaseCalls {
    byte_calls: Box<[SourceByteCall]>,
    window_calls: Box<[SourceWindowCall]>,
}
#[derive(Debug)]
enum FlowFact<'a> {
    Independent,
    // Only the exact admitted checked finish request can mint this payload.
    FinishBoundary(NodeId),
    ScalarLiteral(&'a crate::integer::Integer),
    Fresh,
    Current,
    Enclosing(crate::types::TypeVariableId),
    WindowView {
        window: NodeId,
        producer: NodeId,
        keys: Box<[usize]>,
    },
    WindowExtent {
        view: usize,
    },
    // A typed but constructor-unknown ordinary input. The original forest owns
    // the Type; narrowing a checked constructor pattern preserves its payload
    // roles without manufacturing an enclosing state or cloning Type storage.
    InputNominal(&'a Type, Box<[crate::types::TypeVariableId]>),
    Tuple(Box<[usize]>),
    Constructor(ConstructorId, Option<usize>),
    Callable(ConstructorId),
    ScalarPreflight,
    PayloadCallable,
    // This invocation fact comes only from an exact original operation input.
    // Ordinary transport retains its separate prior value fact; invocation
    // itself supplies neither independence nor a native operand.
    HandlerInputCallable {
        original: &'a SourceResourceTypeFact,
        operation: OperationId,
        pattern: &'a CorePattern,
        binder: &'a TypedBinder,
        value_type: &'a Type,
        value: Option<usize>,
    },
    ByteCallable(crate::resolved::BinderId, Option<NodeId>),
    ViewCallable(crate::resolved::BinderId, Option<NodeId>),
}
#[derive(Default)]
struct FlowFacts<'a> {
    globals: Option<&'a SourceResourceGlobals>,
    handler_graph: Option<super::provider::HandlerGraphView<'a>>,
    values: Vec<FlowFact<'a>>,
    byte_calls: Vec<SourceByteCall>,
    window_calls: Vec<SourceWindowCall>,
}
fn push<T>(
    values: &mut Vec<T>,
    value: T,
    work: &mut TypeWorkBudget,
) -> Result<(), ValidationError> {
    charge(work, 1)?;
    values.try_reserve(1).map_err(|_| resource())?;
    values.push(value);
    Ok(())
}
fn one<T>(value: T, work: &mut TypeWorkBudget) -> Result<Vec<T>, ValidationError> {
    let mut values = Vec::new();
    push(&mut values, value, work)?;
    Ok(values)
}
impl<'a> FlowFacts<'a> {
    fn add(
        &mut self,
        value: FlowFact<'a>,
        work: &mut TypeWorkBudget,
    ) -> Result<usize, ValidationError> {
        let id = self.values.len();
        push(&mut self.values, value, work)?;
        Ok(id)
    }
    fn fact(&self, id: usize) -> Result<&FlowFact<'a>, ValidationError> {
        self.values.get(id).ok_or_else(invalid)
    }
    fn independent(&self, id: usize, work: &mut TypeWorkBudget) -> Result<bool, ValidationError> {
        let mut pending = one(id, work)?;
        while let Some(id) = pending.pop() {
            charge(work, 1)?;
            match self.fact(id)? {
                FlowFact::Independent
                | FlowFact::FinishBoundary(_)
                | FlowFact::PayloadCallable
                | FlowFact::ScalarLiteral(_) => {}
                FlowFact::InputNominal(_, identities) if identities.is_empty() => {}
                FlowFact::Tuple(fields) => {
                    charge(work, fields.len())?;
                    pending.try_reserve(fields.len()).map_err(|_| resource())?;
                    pending.extend_from_slice(fields);
                }
                FlowFact::Constructor(_, Some(payload)) => push(&mut pending, *payload, work)?,
                FlowFact::Constructor(_, None) => {}
                FlowFact::HandlerInputCallable {
                    value: Some(value), ..
                } => push(&mut pending, *value, work)?,
                _ => return Ok(false),
            }
        }
        Ok(true)
    }
    fn borrowed(
        &self,
        id: usize,
        current: bool,
        header: &CheckedSourceResourceHeader,
        work: &mut TypeWorkBudget,
    ) -> Result<bool, ValidationError> {
        let mut pending = one(id, work)?;
        while let Some(id) = pending.pop() {
            charge(work, 1)?;
            match self.fact(id)? {
                FlowFact::Independent
                | FlowFact::FinishBoundary(_)
                | FlowFact::ScalarLiteral(_)
                | FlowFact::Constructor(_, None) => {}
                FlowFact::Current if current => {}
                FlowFact::InputNominal(_, identities) => {
                    for identity in identities {
                        charge(work, header.dependencies.len())?;
                        if !header.dependencies.contains(identity) {
                            return Ok(false);
                        }
                    }
                }
                FlowFact::Enclosing(identity) => {
                    charge(work, header.dependencies.len())?;
                    if !header.dependencies.contains(identity) {
                        return Ok(false);
                    }
                }
                FlowFact::Tuple(fields) => {
                    charge(work, fields.len())?;
                    pending.try_reserve(fields.len()).map_err(|_| resource())?;
                    pending.extend_from_slice(fields);
                }
                FlowFact::Constructor(_, Some(payload)) => push(&mut pending, *payload, work)?,
                FlowFact::HandlerInputCallable {
                    value: Some(value), ..
                } => push(&mut pending, *value, work)?,
                _ => return Ok(false),
            }
        }
        Ok(true)
    }

    fn input(
        &mut self,
        ty: &'a Type,
        registry: &ResolvedRegistry,
        work: &mut TypeWorkBudget,
    ) -> Result<usize, ValidationError> {
        enum Task<'a> {
            Visit(&'a Type),
            Tuple(usize),
        }
        let mut pending = one(Task::Visit(ty), work)?;
        let mut values = Vec::new();
        while let Some(task) = pending.pop() {
            charge(work, 1)?;
            match task {
                Task::Visit(Type::Tuple(fields)) => {
                    push(&mut pending, Task::Tuple(fields.len()), work)?;
                    charge(work, fields.len())?;
                    pending.try_reserve(fields.len()).map_err(|_| resource())?;
                    pending.extend(fields.iter().rev().map(Task::Visit));
                }
                Task::Visit(ty) => {
                    let fact = if let Some(identity) =
                        dependency_state_identity(ty, registry, work)?
                    {
                        self.add(FlowFact::Enclosing(identity), work)?
                    } else if matches!(ty, Type::Nominal(_) | Type::Application(_, _)) {
                        let mut identities = Vec::new();
                        let mut pending = one(ty, work)?;
                        while let Some(part) = pending.pop() {
                            charge(work, 1)?;
                            if let Some(identity) = dependency_state_identity(part, registry, work)?
                            {
                                push(&mut identities, identity, work)?;
                                continue;
                            }
                            match part {
                                Type::Application(function, argument) => {
                                    push(&mut pending, function.as_ref(), work)?;
                                    push(&mut pending, argument.as_ref(), work)?;
                                }
                                Type::Tuple(fields) => {
                                    charge(work, fields.len())?;
                                    pending.try_reserve(fields.len()).map_err(|_| resource())?;
                                    pending.extend(fields.iter());
                                }
                                _ => {}
                            }
                        }
                        self.add(
                            FlowFact::InputNominal(ty, identities.into_boxed_slice()),
                            work,
                        )?
                    } else {
                        0
                    };
                    push(&mut values, fact, work)?;
                }
                Task::Tuple(count) => {
                    let start = values.len().checked_sub(count).ok_or_else(invalid)?;
                    let mut fields = Vec::new();
                    charge(work, count)?;
                    fields.try_reserve_exact(count).map_err(|_| resource())?;
                    fields.extend_from_slice(&values[start..]);
                    values.truncate(start);
                    let fact = self.add(FlowFact::Tuple(fields.into_boxed_slice()), work)?;
                    push(&mut values, fact, work)?;
                }
            }
        }
        if values.len() != 1 {
            return Err(invalid());
        }
        values.pop().ok_or_else(invalid)
    }

    fn wrapped(
        &mut self,
        id: ConstructorId,
        payload: usize,
        work: &mut TypeWorkBudget,
    ) -> Result<usize, ValidationError> {
        self.add(FlowFact::Constructor(id, Some(payload)), work)
    }
    fn selected(
        &self,
        value: usize,
        path: &[usize],
        work: &mut TypeWorkBudget,
    ) -> Result<usize, ValidationError> {
        charge(work, path.len() + 1)?;
        let (first, rest) = path.split_first().ok_or_else(invalid)?;
        let mut selected = match self.fact(value)? {
            FlowFact::Tuple(values) => *values.get(*first).ok_or_else(invalid)?,
            _ if *first == 0 => value,
            _ => return Err(invalid()),
        };
        for position in rest {
            let FlowFact::Tuple(values) = self.fact(selected)? else {
                return Err(invalid());
            };
            selected = *values.get(*position).ok_or_else(invalid)?;
        }
        Ok(selected)
    }
}
#[derive(Clone, Copy, Debug)]
enum CheckedFinishOutcome {
    Consumed(NodeId),
    Retained(NodeId),
    Boundary(NodeId),
}
impl CheckedFinishOutcome {
    fn request(self) -> NodeId {
        match self {
            Self::Consumed(request) | Self::Retained(request) | Self::Boundary(request) => request,
        }
    }
}

struct FlowPath {
    locals: HashMap<crate::resolved::BinderId, usize>,
    acquired: bool,
    consumed: bool,
    attempted_teardown: bool,
    checked_finish_outcome: Option<CheckedFinishOutcome>,
    blocked: bool,
    windows: Vec<(NodeId, usize)>,
    ordinary_owners: Vec<(super::HandlerId, crate::resolved::ResumeId)>,
}
impl FlowPath {
    fn new(work: &mut TypeWorkBudget) -> Result<Self, ValidationError> {
        charge(work, 1)?;
        Ok(Self {
            locals: HashMap::new(),
            acquired: false,
            consumed: false,
            attempted_teardown: false,
            checked_finish_outcome: None,
            blocked: false,
            windows: Vec::new(),
            ordinary_owners: Vec::new(),
        })
    }
    fn bind(
        &mut self,
        id: crate::resolved::BinderId,
        value: usize,
        work: &mut TypeWorkBudget,
    ) -> Result<(), ValidationError> {
        charge(work, 1)?;
        self.locals.try_reserve(1).map_err(|_| resource())?;
        self.locals.insert(id, value);
        Ok(())
    }
    fn copy(&self, work: &mut TypeWorkBudget) -> Result<Self, ValidationError> {
        charge(work, self.locals.len() + 1)?;
        let mut locals = HashMap::new();
        locals
            .try_reserve(self.locals.len())
            .map_err(|_| resource())?;
        locals.extend(self.locals.iter().map(|(id, value)| (*id, *value)));
        let mut windows = Vec::new();
        charge(work, self.windows.len())?;
        windows
            .try_reserve_exact(self.windows.len())
            .map_err(|_| resource())?;
        windows.extend_from_slice(&self.windows);
        let mut ordinary_owners = Vec::new();
        charge(work, self.ordinary_owners.len())?;
        ordinary_owners
            .try_reserve_exact(self.ordinary_owners.len())
            .map_err(|_| resource())?;
        ordinary_owners.extend_from_slice(&self.ordinary_owners);
        Ok(Self {
            locals,
            acquired: self.acquired,
            consumed: self.consumed,
            attempted_teardown: self.attempted_teardown,
            checked_finish_outcome: self.checked_finish_outcome,
            blocked: self.blocked,
            windows,
            ordinary_owners,
        })
    }
}
/// Symbolic admission separates a compatible pattern from one which is certain
/// to match. Independent values retain no constructor/boolean choice; an owner
/// beside them does not make that choice known.
#[derive(Clone, Copy, Eq, PartialEq)]
enum PatternMatch {
    Impossible,
    Possible,
    Certain,
}
impl PatternMatch {
    fn and(self, other: Self) -> Self {
        match (self, other) {
            (Self::Impossible, _) | (_, Self::Impossible) => Self::Impossible,
            (Self::Possible, _) | (_, Self::Possible) => Self::Possible,
            _ => Self::Certain,
        }
    }
}
fn bind_pattern<'a>(
    pattern: &'a CorePattern,
    value: usize,
    path: &mut FlowPath,
    facts: &mut FlowFacts<'a>,
    registry: &ResolvedRegistry,
    depth: usize,
    work: &mut TypeWorkBudget,
) -> Result<PatternMatch, ValidationError> {
    use PatternMatch::{Certain, Impossible, Possible};
    charge(work, 1)?;
    if depth > 64 {
        return Err(resource());
    }
    if let FlowFact::InputNominal(ty, _) = facts.fact(value)? {
        let ty = *ty;
        if !same(ty, &pattern.ty, work)? {
            return Err(invalid());
        }
        if let CorePatternKind::Constructor {
            constructor,
            payload: pattern_payload,
        } = &pattern.kind
        {
            let (nominal, arguments) = application(ty, work)?;
            if constructor.owner() != nominal {
                return Err(invalid());
            }
            let declaration = registry.constructor(*constructor).ok_or_else(invalid)?;
            match (&declaration.payload, pattern_payload) {
                (None, None) => return Ok(Possible),
                (Some(expected), Some(pattern)) => {
                    let parameters = registry.nominal_parameters(nominal).ok_or_else(invalid)?;
                    if parameters.len() != arguments.len() {
                        return Err(invalid());
                    }
                    let mut replacements = HashMap::new();
                    charge(work, parameters.len())?;
                    replacements
                        .try_reserve(parameters.len())
                        .map_err(|_| resource())?;
                    for (parameter, argument) in parameters.iter().zip(arguments) {
                        if parameter.kind == Kind::EffectRow {
                            return Err(invalid());
                        }
                        replacements.insert(parameter.id, argument);
                    }
                    let expected = crate::types::IterativeTypeOwner::new(
                        crate::types::substitute_type_variables_borrowed_with(
                            expected,
                            &replacements,
                            |cells| charge(work, cells),
                            resource,
                        )?,
                    );
                    if !same(&expected, &pattern.ty, work)? {
                        return Err(invalid());
                    }
                    let value = facts.input(&pattern.ty, registry, work)?;
                    return Ok(Possible.and(bind_pattern(
                        pattern,
                        value,
                        path,
                        facts,
                        registry,
                        depth + 1,
                        work,
                    )?));
                }
                _ => return Err(invalid()),
            }
        }
    }
    Ok(match &pattern.kind {
        CorePatternKind::Binder(binder) => {
            path.bind(binder.id(), value, work)?;
            Certain
        }
        CorePatternKind::Wildcard => Certain,
        CorePatternKind::Unit => {
            if facts.independent(value, work)? {
                Certain
            } else {
                Impossible
            }
        }
        CorePatternKind::Boolean(_) => {
            if facts.independent(value, work)? {
                Possible
            } else {
                Impossible
            }
        }
        CorePatternKind::Tuple(patterns) => match facts.fact(value)? {
            FlowFact::Tuple(values) => {
                if values.len() != patterns.len() {
                    Impossible
                } else {
                    let mut matches = Certain;
                    charge(work, values.len())?;
                    let mut copied = Vec::new();
                    copied
                        .try_reserve_exact(values.len())
                        .map_err(|_| resource())?;
                    copied.extend_from_slice(values);
                    for (pattern, value) in patterns.iter().zip(&copied) {
                        matches = matches.and(bind_pattern(
                            pattern,
                            *value,
                            path,
                            facts,
                            registry,
                            depth + 1,
                            work,
                        )?);
                    }
                    matches
                }
            }
            FlowFact::Independent => {
                let mut matches = Certain;
                for pattern in patterns {
                    matches = matches.and(bind_pattern(
                        pattern,
                        value,
                        path,
                        facts,
                        registry,
                        depth + 1,
                        work,
                    )?);
                }
                matches
            }
            _ => Impossible,
        },
        CorePatternKind::Constructor {
            constructor,
            payload,
        } => match facts.fact(value)? {
            FlowFact::Constructor(actual, value) if actual == constructor => {
                match (payload.as_deref(), value) {
                    (Some(pattern), Some(value)) => {
                        let value = *value;
                        bind_pattern(pattern, value, path, facts, registry, depth + 1, work)?
                    }
                    (None, None) => Certain,
                    _ => Impossible,
                }
            }
            FlowFact::Independent => {
                if let Some(payload) = payload {
                    Possible.and(bind_pattern(
                        payload,
                        value,
                        path,
                        facts,
                        registry,
                        depth + 1,
                        work,
                    )?)
                } else {
                    Possible
                }
            }
            _ => Impossible,
        },
    })
}
fn extend<T>(
    values: &mut Vec<T>,
    next: Vec<T>,
    work: &mut TypeWorkBudget,
) -> Result<(), ValidationError> {
    charge(work, next.len())?;
    values.try_reserve(next.len()).map_err(|_| resource())?;
    values.extend(next);
    Ok(())
}
#[allow(
    clippy::too_many_arguments,
    reason = "the phase proof keeps its original graph, lineage, path, facts, depth and work dependencies explicit"
)]
fn eval_flow<'a>(
    program: &'a UnvalidatedEffectProgram,
    header: &'a CheckedSourceResourceHeader,
    id: NodeId,
    phase: SourceResourcePhase,
    path: FlowPath,
    facts: &mut FlowFacts<'a>,
    depth: usize,
    work: &mut TypeWorkBudget,
) -> Result<Vec<(usize, FlowPath)>, ValidationError> {
    charge(work, 1)?;
    if depth > 64 {
        return Err(resource());
    }
    let stored = node(program, id)?;
    match &stored.kind {
        EffectExprKind::Pure(PureExprKind::Variable(local)) => {
            charge(work, 1)?;
            let value = if let Some(value) = path.locals.get(&local.binder()) {
                *value
            } else if let Some(ty) = facts
                .globals
                .and_then(|globals| globals.get(&local.binder()))
            {
                if !same(&stored.ty, ty, work)? {
                    return Err(invalid());
                }
                if matches!(&stored.ty, Type::Forall(_, _)) || stored.ty.function_view().is_some() {
                    facts.add(FlowFact::PayloadCallable, work)?
                } else {
                    let value = facts.input(&stored.ty, &program.registry, work)?;
                    if !facts.independent(value, work)? {
                        return Err(invalid());
                    }
                    value
                }
            } else {
                // A completed compiler-owned scalar fact admits only this pure
                // callable. It does not open the ordinary helper barrier.
                charge(work, 1)?;
                let fact = program
                    .registry
                    .scalar_preflight(local.binder())
                    .ok_or_else(invalid)?;
                if !same(&stored.ty, fact.core_signature(), work)? {
                    return Err(invalid());
                }
                facts.add(
                    if fact.role().view_parameter(fact.module()).is_some() {
                        FlowFact::ViewCallable(fact.function(), None)
                    } else if fact.role().state_parameter(fact.module()).is_some() {
                        FlowFact::ByteCallable(fact.function(), None)
                    } else {
                        FlowFact::ScalarPreflight
                    },
                    work,
                )?
            };
            one((value, path), work)
        }
        EffectExprKind::Pure(PureExprKind::Value(value)) => match value {
            PureValue::Constructor(constructor) => {
                let id = constructor.constructor();
                let declaration = program.registry.constructor(id).ok_or_else(invalid)?;
                let value = facts.add(
                    if declaration.payload.is_some() {
                        FlowFact::Callable(id)
                    } else {
                        FlowFact::Constructor(id, None)
                    },
                    work,
                )?;
                one((value, path), work)
            }
            PureValue::Integer(value) => {
                let value = facts.add(FlowFact::ScalarLiteral(value.value()), work)?;
                one((value, path), work)
            }
            PureValue::Function(_) => Err(invalid()),
            PureValue::Intrinsic(intrinsic) => {
                use super::packed::Intrinsic;
                use crate::foreign::scalar_preflight::ForeignScalarPreflightRole;
                let (function, role) = match intrinsic.operation() {
                    Intrinsic::ForeignCheckedI64 { function } => {
                        (function, ForeignScalarPreflightRole::I64)
                    }
                    Intrinsic::ForeignCheckedSizeT { function } => {
                        (function, ForeignScalarPreflightRole::SizeT)
                    }
                    Intrinsic::ForeignCheckedNul { function } => {
                        (function, ForeignScalarPreflightRole::Nul)
                    }
                    Intrinsic::ForeignDataOf { function } => {
                        (function, ForeignScalarPreflightRole::DataOf)
                    }
                    Intrinsic::ForeignReplaceData { function } => {
                        (function, ForeignScalarPreflightRole::ReplaceData)
                    }
                    Intrinsic::ForeignCopyBytes { function } => {
                        (function, ForeignScalarPreflightRole::CopyBytes)
                    }
                    Intrinsic::ForeignCopyNul { function } => {
                        (function, ForeignScalarPreflightRole::CopyNul)
                    }
                    Intrinsic::ForeignExtentValue { function } => {
                        (function, ForeignScalarPreflightRole::ExtentValue)
                    }
                    Intrinsic::ForeignByteRead { function } => {
                        (function, ForeignScalarPreflightRole::ByteRead)
                    }
                    Intrinsic::ForeignByteWrite { function } => {
                        (function, ForeignScalarPreflightRole::ByteWrite)
                    }
                    _ => return Err(invalid()),
                };
                charge(work, 1)?;
                let fact = program
                    .registry
                    .scalar_preflight(function)
                    .ok_or_else(invalid)?;
                if fact.function() != function
                    || fact.role() != role
                    || fact.module() != intrinsic.module()
                    || !same(&stored.ty, fact.signature(), work)?
                {
                    return Err(invalid());
                }
                let value = facts.add(
                    if role.view_parameter(fact.module()).is_some() {
                        FlowFact::ViewCallable(function, None)
                    } else if role.state_parameter(fact.module()).is_some() {
                        FlowFact::ByteCallable(function, None)
                    } else {
                        FlowFact::ScalarPreflight
                    },
                    work,
                )?;
                one((value, path), work)
            }
            _ => one((0, path), work),
        },
        EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Bind(binding))) => {
            let mut results = Vec::new();
            for (value, mut path) in eval_flow(
                program,
                header,
                binding.initializer(),
                phase,
                path,
                facts,
                depth + 1,
                work,
            )? {
                path.bind(binding.binder().id(), value, work)?;
                let next = eval_flow(
                    program,
                    header,
                    binding.body(),
                    phase,
                    path,
                    facts,
                    depth + 1,
                    work,
                )?;
                extend(&mut results, next, work)?;
            }
            Ok(results)
        }
        EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Tuple(tuple))) => {
            let mut paths = one((Vec::<usize>::new(), path), work)?;
            for element in tuple.elements() {
                let mut next = Vec::new();
                for (values, path) in paths {
                    for (value, path) in eval_flow(
                        program,
                        header,
                        *element,
                        phase,
                        path,
                        facts,
                        depth + 1,
                        work,
                    )? {
                        charge(work, values.len())?;
                        let mut fields = Vec::new();
                        fields
                            .try_reserve_exact(values.len() + 1)
                            .map_err(|_| resource())?;
                        fields.extend_from_slice(&values);
                        push(&mut fields, value, work)?;
                        push(&mut next, (fields, path), work)?;
                    }
                }
                paths = next;
            }
            let mut results = Vec::new();
            for (values, path) in paths {
                let value = facts.add(FlowFact::Tuple(values.into_boxed_slice()), work)?;
                push(&mut results, (value, path), work)?;
            }
            Ok(results)
        }
        EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Apply(application))) => {
            let mut results = Vec::new();
            for (function, path) in eval_flow(
                program,
                header,
                application.function(),
                phase,
                path,
                facts,
                depth + 1,
                work,
            )? {
                let constructor = match facts.fact(function)? {
                    FlowFact::Callable(constructor) => Some(*constructor),
                    FlowFact::ScalarPreflight
                    | FlowFact::PayloadCallable
                    | FlowFact::HandlerInputCallable { .. }
                    | FlowFact::ByteCallable(_, Some(_))
                    | FlowFact::ViewCallable(_, Some(_)) => None,
                    _ => return Err(invalid()),
                };
                for (argument, path) in eval_flow(
                    program,
                    header,
                    application.argument(),
                    phase,
                    path,
                    facts,
                    depth + 1,
                    work,
                )? {
                    let value = if let Some(constructor) = constructor {
                        facts.wrapped(constructor, argument, work)?
                    } else if let FlowFact::ViewCallable(canonical, Some(selected_application)) =
                        facts.fact(function)?
                    {
                        let canonical = *canonical;
                        let selected_application = *selected_application;
                        admit_view_primitive(program, canonical, argument, &path, facts, work)?;
                        push(
                            &mut facts.byte_calls,
                            SourceByteCall {
                                apply: Some(id),
                                application: selected_application,
                                function: canonical,
                            },
                            work,
                        )?;
                        0
                    } else if let FlowFact::HandlerInputCallable {
                        original,
                        operation,
                        pattern,
                        binder,
                        value_type,
                        ..
                    } = facts.fact(function)?
                    {
                        let (original, operation, pattern, binder, value_type) =
                            (*original, *operation, *pattern, *binder, *value_type);
                        let graph = facts.handler_graph.as_ref().ok_or_else(invalid)?;
                        charge(work, graph.draft.clauses.len())?;
                        let clause = graph
                            .draft
                            .clauses
                            .iter()
                            .find(|clause| {
                                clause.operation() == operation
                                    && std::ptr::eq(clause.pattern(), pattern)
                            })
                            .ok_or_else(invalid)?;
                        charge(work, clause.pattern().binder_iter().count())?;
                        if phase != SourceResourcePhase::Handler
                            || !std::ptr::eq(original, &*header.original)
                            || !clause
                                .pattern()
                                .binder_iter()
                                .any(|candidate| std::ptr::eq(candidate, binder))
                            || !same(&node(program, application.function())?.ty, value_type, work)?
                            || !facts.independent(argument, work)?
                        {
                            return Err(invalid());
                        }
                        let signature = value_type.function_view().ok_or_else(invalid)?;
                        if !same(signature.value(), &stored.ty, work)? {
                            return Err(invalid());
                        }
                        if signature.value().function_view().is_some() {
                            facts.add(
                                FlowFact::HandlerInputCallable {
                                    original,
                                    operation,
                                    pattern,
                                    binder,
                                    value_type: signature.value(),
                                    value: None,
                                },
                                work,
                            )?
                        } else {
                            let value = facts.input(&stored.ty, &program.registry, work)?;
                            if !facts.independent(value, work)? {
                                return Err(invalid());
                            }
                            value
                        }
                    } else if matches!(facts.fact(function)?, FlowFact::PayloadCallable) {
                        let callable = node(program, application.function())?;
                        let signature = callable.ty.function_view().ok_or_else(invalid)?;
                        if signature.effects().is_some_and(|row| !row.is_empty())
                            || !facts.independent(argument, work)?
                        {
                            return Err(invalid());
                        }
                        if stored.ty.function_view().is_some() {
                            facts.add(FlowFact::PayloadCallable, work)?
                        } else {
                            let value = facts.input(&stored.ty, &program.registry, work)?;
                            if !facts.independent(value, work)? {
                                return Err(invalid());
                            }
                            value
                        }
                    } else {
                        if let FlowFact::ByteCallable(function, Some(application)) =
                            facts.fact(function)?
                        {
                            if !path.windows.is_empty() {
                                return Err(invalid());
                            }
                            let function = *function;
                            let selected_application = *application;
                            let fact = program
                                .registry
                                .scalar_preflight(function)
                                .ok_or_else(invalid)?;
                            if fact.role().data_parameter(fact.module()).is_some() {
                                if phase == SourceResourcePhase::Acquire
                                    || path.consumed
                                    || path.checked_finish_outcome.is_some()
                                {
                                    return Err(invalid());
                                }
                                let replace = fact.role() == crate::foreign::scalar_preflight::ForeignScalarPreflightRole::ReplaceData;
                                let state = if replace {
                                    let FlowFact::Tuple(fields) = facts.fact(argument)? else {
                                        return Err(invalid());
                                    };
                                    if fields.len() != 2
                                        || !facts.borrowed(fields[1], false, header, work)?
                                    {
                                        return Err(invalid());
                                    }
                                    fields[0]
                                } else {
                                    argument
                                };
                                if !matches!(facts.fact(state)?, FlowFact::Current) {
                                    return Err(invalid());
                                }
                                push(
                                    &mut facts.byte_calls,
                                    SourceByteCall {
                                        apply: Some(id),
                                        application: selected_application,
                                        function,
                                    },
                                    work,
                                )?;
                                let result = if replace {
                                    0
                                } else {
                                    facts.input(
                                        &header.original.data.ty,
                                        &program.registry,
                                        work,
                                    )?
                                };
                                push(&mut results, (result, path), work)?;
                                continue;
                            }
                            let FlowFact::Tuple(fields) = facts.fact(argument)? else {
                                return Err(invalid());
                            };
                            let write = fact.role() == crate::foreign::scalar_preflight::ForeignScalarPreflightRole::ByteWrite;
                            if fields.len() != 2 + usize::from(write) || path.consumed || path.attempted_teardown
                                || header.owner.owner().representation() != crate::foreign::source_contract::PreparedAddressRepresentation::Bytes
                                || !matches!(header.acquire.owner_role(), Some(PreparedOwnerCall::Acquire {initialized_bytes:Some(_), ..}))
                                || !matches!(facts.fact(fields[0])?, FlowFact::Fresh if phase == SourceResourcePhase::Acquire && path.acquired)
                                    && !matches!(facts.fact(fields[0])?, FlowFact::Current if phase != SourceResourcePhase::Acquire)
                            { return Err(invalid()); }
                            for field in &fields[1..] {
                                if !facts.independent(*field, work)? {
                                    return Err(invalid());
                                }
                            }
                            push(
                                &mut facts.byte_calls,
                                SourceByteCall {
                                    apply: Some(id),
                                    application: selected_application,
                                    function,
                                },
                                work,
                            )?;
                        } else if !facts.independent(argument, work)? {
                            return Err(invalid());
                        }
                        // Both scalar-check alternatives contain independent
                        // values and preserve the same ownership path. Keeping
                        // that common fact avoids a Cartesian branch expansion.
                        0
                    };
                    push(&mut results, (value, path), work)?;
                }
            }
            Ok(results)
        }
        EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Primitive(primitive))) => {
            let mut results = Vec::new();
            for (left, path) in eval_flow(
                program,
                header,
                primitive.left(),
                phase,
                path,
                facts,
                depth + 1,
                work,
            )? {
                if !facts.independent(left, work)? {
                    return Err(invalid());
                }
                for (right, path) in eval_flow(
                    program,
                    header,
                    primitive.right(),
                    phase,
                    path,
                    facts,
                    depth + 1,
                    work,
                )? {
                    if !facts.independent(right, work)? {
                        return Err(invalid());
                    }
                    push(&mut results, (0, path), work)?;
                }
            }
            Ok(results)
        }
        EffectExprKind::Pure(PureExprKind::Computation(PureComputation::TypeApplication(
            application,
        ))) => {
            let mut results = Vec::new();
            for (value, path) in eval_flow(
                program,
                header,
                application.function(),
                phase,
                path,
                facts,
                depth + 1,
                work,
            )? {
                let value = if let FlowFact::ViewCallable(function, None) = facts.fact(value)? {
                    let function = *function;
                    let (window, _) = path.windows.last().copied().ok_or_else(invalid)?;
                    let EffectExprKind::Operation(EffectOperation::SourceCopyWindow(window)) =
                        &node(program, window)?.kind
                    else {
                        return Err(invalid());
                    };
                    if application.arguments().len() != 1
                        || !application.row_arguments().is_empty()
                        || !window
                            .matches_view_type(&application.arguments()[0], work)
                            .map_err(|()| resource())?
                    {
                        return Err(invalid());
                    }
                    push(
                        &mut facts.byte_calls,
                        SourceByteCall {
                            apply: None,
                            application: id,
                            function,
                        },
                        work,
                    )?;
                    facts.add(FlowFact::ViewCallable(function, Some(id)), work)?
                } else if let FlowFact::ByteCallable(function, None) = facts.fact(value)? {
                    let function = *function;
                    let fact = program
                        .registry
                        .scalar_preflight(function)
                        .ok_or_else(invalid)?;
                    let data = fact.role().data_parameter(fact.module()).is_some();
                    if application.arguments().len() != 1 + usize::from(data)
                        || !application.row_arguments().is_empty()
                        || !same(&application.arguments()[0], &header.original.state.ty, work)?
                        || data
                            && !same(&application.arguments()[1], &header.original.data.ty, work)?
                    {
                        return Err(invalid());
                    }
                    push(
                        &mut facts.byte_calls,
                        SourceByteCall {
                            apply: None,
                            application: id,
                            function,
                        },
                        work,
                    )?;
                    facts.add(FlowFact::ByteCallable(function, Some(id)), work)?
                } else {
                    value
                };
                push(&mut results, (value, path), work)?;
            }
            Ok(results)
        }
        EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Match(matching))) => {
            let mut results = Vec::new();
            for (value, path) in eval_flow(
                program,
                header,
                matching.scrutinee(),
                phase,
                path,
                facts,
                depth + 1,
                work,
            )? {
                let mut matched = false;
                for arm in matching.arms() {
                    let mut candidate = path.copy(work)?;
                    let certainty = bind_pattern(
                        arm.pattern(),
                        value,
                        &mut candidate,
                        facts,
                        &program.registry,
                        0,
                        work,
                    )?;
                    if certainty != PatternMatch::Impossible {
                        matched = true;
                        let next = eval_flow(
                            program,
                            header,
                            arm.body(),
                            phase,
                            candidate,
                            facts,
                            depth + 1,
                            work,
                        )?;
                        extend(&mut results, next, work)?;
                        if certainty == PatternMatch::Certain {
                            break;
                        }
                    }
                }
                if !matched {
                    return Err(invalid());
                }
            }
            Ok(results)
        }
        EffectExprKind::Operation(EffectOperation::SourceCopyWindow(window)) => {
            let mut results = Vec::new();
            for (state, mut path) in eval_flow(
                program,
                header,
                window.state(),
                phase,
                path,
                facts,
                depth + 1,
                work,
            )? {
                let allowed = match facts.fact(state)? {
                    FlowFact::Fresh => {
                        phase == SourceResourcePhase::Acquire
                            && path.acquired
                            && !path.consumed
                            && !path.blocked
                    }
                    FlowFact::Current => {
                        phase != SourceResourcePhase::Acquire
                            && !path.consumed
                            && !path.blocked
                            && path.checked_finish_outcome.is_none()
                    }
                    FlowFact::Enclosing(identity) => {
                        charge(work, header.dependencies.len())?;
                        header.dependencies.contains(identity)
                    }
                    _ => false,
                };
                if !allowed {
                    return Err(invalid());
                }
                push(&mut path.windows, (id, state), work)?;
                for (value, mut path) in eval_flow(
                    program,
                    header,
                    window.body(),
                    phase,
                    path,
                    facts,
                    depth + 1,
                    work,
                )? {
                    if path.windows.pop() != Some((id, state)) || !facts.independent(value, work)? {
                        return Err(invalid());
                    }
                    push(&mut results, (value, path), work)?;
                }
            }
            Ok(results)
        }
        EffectExprKind::Operation(EffectOperation::Request(request)) => {
            if !path.windows.is_empty() {
                return eval_window_request(
                    program, header, id, request, phase, path, facts, depth, work,
                );
            }
            if program
                .registry
                .native_symbol(request.operation())
                .is_some_and(|symbol| symbol.symbol().access_result().is_some())
            {
                return Err(invalid());
            }
            charge(work, header.original.interpreted.len())?;
            let controlled_native = header
                .original
                .interpreted
                .iter()
                .any(|effect| effect.instance.effect() == request.effect().effect());
            if !controlled_native {
                let mut results = Vec::new();
                for (operand, path) in eval_flow(
                    program,
                    header,
                    request.operand(),
                    phase,
                    path,
                    facts,
                    depth + 1,
                    work,
                )? {
                    // An ordinary outward operation cannot transport this
                    // phase's controlled native state or synthesize its lineage.
                    if !facts.borrowed(operand, false, header, work)? {
                        return Err(invalid());
                    }
                    let value = facts.input(&stored.ty, &program.registry, work)?;
                    push(&mut results, (value, path), work)?;
                }
                return Ok(results);
            }
            let borrowed = program
                .registry
                .native_symbol(request.operation())
                .filter(|symbol| {
                    matches!(symbol.owner_role(), Some(PreparedOwnerCall::Borrow { .. }))
                        && symbol
                            .owner()
                            .is_some_and(|owner| Arc::ptr_eq(owner, &header.owner))
                });
            if phase == SourceResourcePhase::Handler && borrowed.is_none() {
                return Err(invalid());
            }
            let expected = if let Some(borrowed) = borrowed {
                borrowed
            } else if phase == SourceResourcePhase::Acquire {
                &header.acquire
            } else {
                &header.teardown
            };
            if request.operation() != expected.operation() {
                return Err(invalid());
            }
            let mut exact = false;
            for effect in &header.original.interpreted {
                if crate::types::compare_effect_instances_with_budget(
                    &effect.instance,
                    request.effect(),
                    work,
                )
                .map_err(|_| resource())?
                    == std::cmp::Ordering::Equal
                {
                    exact = true;
                    break;
                }
            }
            if !exact {
                return Err(invalid());
            }
            let codec = expected.owner_codec().ok_or_else(invalid)?;
            let call = expected.call_codec().ids();
            let mut results = Vec::new();
            for (operand, mut path) in eval_flow(
                program,
                header,
                request.operand(),
                phase,
                path,
                facts,
                depth + 1,
                work,
            )? {
                for mapped in expected.symbol().operands() {
                    if let crate::foreign::source_contract::PreparedOperandSource::Enclosing(
                        selection,
                    ) = mapped.source()
                    {
                        let selected = facts.selected(operand, selection, work)?;
                        if !matches!(facts.fact(selected)?, FlowFact::Enclosing(_))
                            || !facts.borrowed(selected, false, header, work)?
                        {
                            return Err(invalid());
                        }
                    }
                }
                if let Some(PreparedOwnerCall::Borrow {
                    current_operand, ..
                }) = expected.owner_role()
                {
                    if path.consumed || path.blocked || path.checked_finish_outcome.is_some() {
                        return Err(invalid());
                    }
                    let crate::foreign::source_contract::PreparedOperandSource::Current(selection) =
                        expected.symbol().operands()[*current_operand].source()
                    else {
                        return Err(invalid());
                    };
                    let selected = facts.selected(operand, selection, work)?;
                    if !matches!(facts.fact(selected)?, FlowFact::Fresh if phase == SourceResourcePhase::Acquire && path.acquired)
                        && !matches!(facts.fact(selected)?, FlowFact::Current if phase != SourceResourcePhase::Acquire)
                    {
                        return Err(invalid());
                    }
                    if expected.symbol().operands().iter().any(|operand| {
                        matches!(
                            operand.source(),
                            crate::foreign::source_contract::PreparedOperandSource::Source(_)
                        )
                    }) {
                        let refusal = facts.wrapped(call.conversion_failed, 0, work)?;
                        push(&mut results, (refusal, path.copy(work)?), work)?;
                    }
                    let returned = facts.wrapped(call.returned, 0, work)?;
                    push(&mut results, (returned, path), work)?;
                    continue;
                }
                if phase == SourceResourcePhase::Acquire {
                    if path.acquired || !facts.borrowed(operand, false, header, work)? {
                        return Err(invalid());
                    }
                    let refusal = facts.wrapped(call.conversion_failed, 0, work)?;
                    push(&mut results, (refusal, path.copy(work)?), work)?;
                    if matches!(
                        header.codec.report,
                        SourceResourceReportCodec::CheckedScope { .. }
                    ) {
                        charge(work, 1)?;
                        let failed = ConstructorId::new(call.call, 2);
                        let outcome = facts.wrapped(failed, 0, work)?;
                        push(&mut results, (outcome, path.copy(work)?), work)?;
                    }
                    let null = facts.add(
                        FlowFact::Constructor(codec.nullable_constructors()[0], None),
                        work,
                    )?;
                    let readable = facts.wrapped(codec.output_constructors()[1], null, work)?;
                    let output = if let Some(role @ PreparedOwnerCall::OutputAcquire { .. }) =
                        expected.owner_role()
                    {
                        let (owner_field, offset_field) =
                            role.output_field_positions().ok_or_else(invalid)?;
                        let mut fields = Vec::new();
                        push(&mut fields, 0, work)?;
                        push(&mut fields, readable, work)?;
                        if let Some(offset_field) = offset_field {
                            let Type::Application(_, payload) = &stored.ty else {
                                return Err(invalid());
                            };
                            let Type::Tuple(types) = payload.as_ref() else {
                                return Err(invalid());
                            };
                            let tail = facts.input(
                                types.get(offset_field).ok_or_else(invalid)?,
                                &program.registry,
                                work,
                            )?;
                            push(&mut fields, tail, work)?;
                            fields.swap(1, owner_field);
                        }
                        facts.add(FlowFact::Tuple(fields.into_boxed_slice()), work)?
                    } else {
                        readable
                    };
                    let returned = facts.wrapped(call.returned, output, work)?;
                    push(&mut results, (returned, path.copy(work)?), work)?;
                    path.acquired = true;
                    let nonnull = facts.wrapped(codec.nullable_constructors()[1], 1, work)?;
                    let readable = facts.wrapped(codec.output_constructors()[1], nonnull, work)?;
                    let output = if let Some(role @ PreparedOwnerCall::OutputAcquire { .. }) =
                        expected.owner_role()
                    {
                        let (owner_field, offset_field) =
                            role.output_field_positions().ok_or_else(invalid)?;
                        let mut fields = Vec::new();
                        push(&mut fields, 0, work)?;
                        push(&mut fields, readable, work)?;
                        if let Some(offset_field) = offset_field {
                            let Type::Application(_, payload) = &stored.ty else {
                                return Err(invalid());
                            };
                            let Type::Tuple(types) = payload.as_ref() else {
                                return Err(invalid());
                            };
                            let tail = facts.input(
                                types.get(offset_field).ok_or_else(invalid)?,
                                &program.registry,
                                work,
                            )?;
                            push(&mut fields, tail, work)?;
                            fields.swap(1, owner_field);
                        }
                        facts.add(FlowFact::Tuple(fields.into_boxed_slice()), work)?
                    } else {
                        readable
                    };
                    let returned = facts.wrapped(call.returned, output, work)?;
                    push(&mut results, (returned, path), work)?;
                } else {
                    if path.consumed || path.attempted_teardown {
                        return Err(invalid());
                    }
                    let role = expected.owner_role().ok_or_else(invalid)?;
                    let current_operand = role.current_operand().ok_or_else(invalid)?;
                    let Some(crate::foreign::source_contract::PreparedOperandSource::Current(
                        selection,
                    )) = expected
                        .symbol()
                        .operands()
                        .get(current_operand)
                        .map(|operand| operand.source())
                    else {
                        return Err(invalid());
                    };
                    if !matches!(
                        facts.fact(facts.selected(operand, selection, work)?)?,
                        FlowFact::Current
                    ) {
                        return Err(invalid());
                    }
                    path.attempted_teardown = true;
                    if matches!(
                        header.codec.report,
                        SourceResourceReportCodec::CheckedScope { .. }
                    ) {
                        // This signature has only authenticated Current and a void
                        // result. It has no fallible scalar/result conversion.
                        // Source arms remain typed/exhaustive; impossible generic
                        // codec alternatives supply no path or finish witness.
                        if expected.symbol().operands().len() != 1
                            || !matches!(
                                expected.symbol().result(),
                                crate::foreign::source_contract::PreparedAbiResult::Void
                            )
                        {
                            return Err(invalid());
                        }
                        let PreparedOwnerCall::Teardown { consumes, .. } = role else {
                            return Err(invalid());
                        };
                        charge(work, 1)?;
                        path.checked_finish_outcome = Some(CheckedFinishOutcome::Boundary(id));
                        let boundary = facts.add(FlowFact::FinishBoundary(id), work)?;
                        let outcome =
                            facts.wrapped(ConstructorId::new(call.call, 2), boundary, work)?;
                        push(&mut results, (outcome, path.copy(work)?), work)?;
                        path.consumed = *consumes;
                        path.checked_finish_outcome = Some(if *consumes {
                            CheckedFinishOutcome::Consumed(id)
                        } else {
                            CheckedFinishOutcome::Retained(id)
                        });
                        let disposition = facts.wrapped(
                            codec.disposition_constructors()[usize::from(!consumes)],
                            0,
                            work,
                        )?;
                        let outcome = facts.wrapped(call.returned, disposition, work)?;
                        push(&mut results, (outcome, path), work)?;
                        continue;
                    }
                    // Current/Enclosing are authenticated guarded addresses.
                    // Their refusal is terminal, not ordinary scalar conversion.
                    // Preserve the existing void profile's flow/accounting.
                    if matches!(role, PreparedOwnerCall::Teardown { .. })
                        || expected.symbol().operands().iter().any(|operand| {
                            matches!(
                                operand.source(),
                                crate::foreign::source_contract::PreparedOperandSource::Source(_)
                            )
                        })
                    {
                        let refusal = facts.wrapped(call.conversion_failed, 0, work)?;
                        push(&mut results, (refusal, path.copy(work)?), work)?;
                    }
                    let blocked = facts.add(
                        FlowFact::Constructor(codec.disposition_constructors()[2], None),
                        work,
                    )?;
                    let blocked = facts.wrapped(call.returned, blocked, work)?;
                    let mut blocked_path = path.copy(work)?;
                    // A blocked close preserves ownership but revokes native
                    // access until the dependent closure has been resolved.
                    blocked_path.blocked = true;
                    push(&mut results, (blocked, blocked_path), work)?;
                    if let PreparedOwnerCall::Teardown { consumes, .. } = role {
                        path.consumed = *consumes;
                        let disposition = facts.wrapped(
                            codec.disposition_constructors()[usize::from(!consumes)],
                            0,
                            work,
                        )?;
                        let returned = facts.wrapped(call.returned, disposition, work)?;
                        push(&mut results, (returned, path), work)?;
                        continue;
                    }
                    for (consumes, readable) in role.dispositions() {
                        if !readable {
                            return Err(invalid());
                        }
                        let mut recorded = path.copy(work)?;
                        recorded.consumed = consumes;
                        let disposition = facts.wrapped(
                            codec.disposition_constructors()[usize::from(!consumes)],
                            0,
                            work,
                        )?;
                        let returned = facts.wrapped(call.returned, disposition, work)?;
                        push(&mut results, (returned, recorded), work)?;
                    }
                }
            }
            Ok(results)
        }
        EffectExprKind::Operation(EffectOperation::Handler(handler))
            if phase == SourceResourcePhase::Handler && facts.handler_graph.is_some() =>
        {
            if handler.has_hook_contracts() {
                return Err(invalid());
            }
            let mut results = eval_flow(
                program,
                header,
                handler.body(),
                phase,
                path.copy(work)?,
                facts,
                depth + 1,
                work,
            )?;
            for clause in handler.clauses() {
                let mut branch = path.copy(work)?;
                push(
                    &mut branch.ordinary_owners,
                    (handler.id(), clause.resume()),
                    work,
                )?;
                bind_pattern(
                    clause.pattern(),
                    0,
                    &mut branch,
                    facts,
                    &program.registry,
                    depth + 1,
                    work,
                )?;
                let completed = eval_flow(
                    program,
                    header,
                    clause.body(),
                    phase,
                    branch,
                    facts,
                    depth + 1,
                    work,
                )?;
                for (value, mut branch) in completed {
                    if !facts.independent(value, work)? {
                        return Err(invalid());
                    }
                    if branch.ordinary_owners.pop() != Some((handler.id(), clause.resume())) {
                        return Err(invalid());
                    }
                    push(&mut results, (value, branch), work)?;
                }
            }
            Ok(results)
        }
        EffectExprKind::Operation(EffectOperation::Discard(discard))
            if phase == SourceResourcePhase::Handler =>
        {
            let graph = facts.handler_graph.as_ref().ok_or_else(invalid)?;
            let recipe = graph.row_recipe.ok_or_else(invalid)?;
            charge(work, path.ordinary_owners.len())?;
            if !path
                .ordinary_owners
                .contains(&(discard.handler(), discard.owner()))
                || !recipe.discard_port(graph, id, work)?
                || !same(&stored.ty, &Type::Unit, work)?
            {
                return Err(invalid());
            }
            // This is the checked Discard expression's Unit result, not a
            // resumed client return or a native-consumption witness. Its actual
            // capture and cleanup remain in the conditional control graph.
            one((0, path), work)
        }
        EffectExprKind::Operation(EffectOperation::Resume(resume))
            if phase == SourceResourcePhase::Handler =>
        {
            let mut results = Vec::new();
            for (value, path) in eval_flow(
                program,
                header,
                resume.value(),
                phase,
                path,
                facts,
                depth + 1,
                work,
            )? {
                if !facts.borrowed(value, true, header, work)? {
                    return Err(invalid());
                }
                push(&mut results, (0, path), work)?;
            }
            Ok(results)
        }
        _ => Err(invalid()),
    }
}
fn admit_view_primitive(
    program: &UnvalidatedEffectProgram,
    function: crate::resolved::BinderId,
    argument: usize,
    path: &FlowPath,
    facts: &FlowFacts<'_>,
    work: &mut TypeWorkBudget,
) -> Result<(), ValidationError> {
    use crate::foreign::scalar_preflight::ForeignScalarPreflightRole as Role;
    let fact = program
        .registry
        .scalar_preflight(function)
        .ok_or_else(invalid)?;
    let (window, _) = path.windows.last().copied().ok_or_else(invalid)?;
    let (view, extent) = if fact.role() == Role::ExtentValue {
        let FlowFact::WindowExtent { view } = facts.fact(argument)? else {
            return Err(invalid());
        };
        (*view, None)
    } else {
        let FlowFact::Tuple(fields) = facts.fact(argument)? else {
            return Err(invalid());
        };
        if fields.len() != 2 {
            return Err(invalid());
        }
        match fact.role() {
            Role::CopyBytes => {
                let FlowFact::WindowExtent { view } = facts.fact(fields[1])? else {
                    return Err(invalid());
                };
                if *view != fields[0] {
                    return Err(invalid());
                }
                (
                    fields[0],
                    Some(crate::foreign::source_contract::PreparedForeignExtent::Bytes),
                )
            }
            Role::CopyNul => {
                if !facts.independent(fields[1], work)? {
                    return Err(invalid());
                }
                (
                    fields[0],
                    Some(crate::foreign::source_contract::PreparedForeignExtent::Nul),
                )
            }
            _ => return Err(invalid()),
        }
    };
    let FlowFact::WindowView {
        window: original, ..
    } = facts.fact(view)?
    else {
        return Err(invalid());
    };
    if *original != window {
        return Err(invalid());
    }
    let EffectExprKind::Operation(EffectOperation::SourceCopyWindow(scope)) =
        &node(program, window)?.kind
    else {
        return Err(invalid());
    };
    if extent.is_some_and(|extent| scope.family().declaration().extent() != extent) {
        return Err(invalid());
    }
    Ok(())
}

#[inline(never)]
#[allow(clippy::too_many_arguments)]
fn eval_window_request<'a>(
    program: &'a UnvalidatedEffectProgram,
    header: &'a CheckedSourceResourceHeader,
    id: NodeId,
    request: &'a super::RequestNode,
    phase: SourceResourcePhase,
    path: FlowPath,
    facts: &mut FlowFacts<'a>,
    depth: usize,
    work: &mut TypeWorkBudget,
) -> Result<Vec<(usize, FlowPath)>, ValidationError> {
    use crate::foreign::source_contract::{PreparedAccessResult, PreparedOperandSource};
    let symbol = program
        .registry
        .native_symbol(request.operation())
        .ok_or_else(invalid)?;
    let &(window_id, state) = path.windows.last().ok_or_else(invalid)?;
    for (window, _) in &path.windows {
        let EffectExprKind::Operation(EffectOperation::SourceCopyWindow(window)) =
            &node(program, *window)?.kind
        else {
            return Err(invalid());
        };
        if !crate::foreign::source_access::window_operation_matches(
            window.family(),
            window.arguments(),
            symbol,
            request.effect(),
            &program.registry,
            work,
        )
        .map_err(|error| {
            if error.is_resource_exhaustion() {
                resource()
            } else {
                invalid()
            }
        })? {
            return Err(invalid());
        }
    }
    let Some(PreparedOwnerCall::Borrow {
        current_operand, ..
    }) = symbol.owner_role()
    else {
        return Err(invalid());
    };
    let PreparedOperandSource::Current(current) = symbol
        .symbol()
        .operands()
        .get(*current_operand)
        .ok_or_else(invalid)?
        .source()
    else {
        return Err(invalid());
    };
    let codec = symbol.owner_codec().ok_or_else(invalid)?;
    let call = symbol.call_codec().ids();
    let mut results = Vec::new();
    for (operand, path) in eval_flow(
        program,
        header,
        request.operand(),
        phase,
        path,
        facts,
        depth + 1,
        work,
    )? {
        if facts.selected(operand, current, work)? != state {
            return Err(invalid());
        }
        for declared in symbol.symbol().operands() {
            if let PreparedOperandSource::Source(path) | PreparedOperandSource::Nul(path) =
                declared.source()
            {
                let selected = facts.selected(operand, path, work)?;
                if !facts.independent(selected, work)? {
                    return Err(invalid());
                }
            }
        }
        push(
            &mut facts.window_calls,
            SourceWindowCall {
                request: id,
                window: window_id,
            },
            work,
        )?;
        if symbol.symbol().operands().iter().any(|operand| {
            matches!(
                operand.source(),
                PreparedOperandSource::Source(_) | PreparedOperandSource::Nul(_)
            )
        }) {
            let refusal = facts.wrapped(call.conversion_failed, 0, work)?;
            push(&mut results, (refusal, path.copy(work)?), work)?;
        }
        let output = match symbol.symbol().access_result() {
            Some(PreparedAccessResult::View { keys, .. }) => {
                let mut selected = Vec::new();
                charge(work, keys.len())?;
                selected
                    .try_reserve_exact(keys.len())
                    .map_err(|_| resource())?;
                for key in keys {
                    let key = facts.selected(operand, key, work)?;
                    if !facts.independent(key, work)? {
                        return Err(invalid());
                    }
                    selected.push(key);
                }
                let view = facts.add(
                    FlowFact::WindowView {
                        window: window_id,
                        producer: id,
                        keys: selected.into_boxed_slice(),
                    },
                    work,
                )?;
                let null = facts.add(
                    FlowFact::Constructor(codec.nullable_constructors()[0], None),
                    work,
                )?;
                let nullable = facts.wrapped(codec.output_constructors()[1], null, work)?;
                let returned = facts.wrapped(call.returned, nullable, work)?;
                push(&mut results, (returned, path.copy(work)?), work)?;
                let nonnull = facts.wrapped(codec.nullable_constructors()[1], view, work)?;
                facts.wrapped(codec.output_constructors()[1], nonnull, work)?
            }
            Some(PreparedAccessResult::Extent { view, keys, .. }) => {
                let selected_view = facts.selected(operand, view, work)?;
                let FlowFact::WindowView {
                    window,
                    producer,
                    keys: produced_keys,
                } = facts.fact(selected_view)?
                else {
                    return Err(invalid());
                };
                if *window != window_id || keys.len() != produced_keys.len() {
                    return Err(invalid());
                }
                charge(work, facts.window_calls.len() + keys.len())?;
                if !facts
                    .window_calls
                    .iter()
                    .any(|call| call.request == *producer && call.window == window_id)
                {
                    return Err(invalid());
                }
                // Unknown keys retain mandatory exact dynamic comparison before
                // native entry. This flow never certifies unknown keys equal.
                for (query, produced) in keys.iter().zip(produced_keys) {
                    let query = facts.selected(operand, query, work)?;
                    if !facts.independent(query, work)? {
                        return Err(invalid());
                    }
                    if let (FlowFact::ScalarLiteral(left), FlowFact::ScalarLiteral(right)) =
                        (facts.fact(query)?, facts.fact(*produced)?)
                    {
                        let bytes = left
                            .magnitude_byte_length()
                            .checked_add(right.magnitude_byte_length())
                            .ok_or_else(resource)?;
                        charge(
                            work,
                            usize::try_from(bytes)
                                .map_err(|_| resource())?
                                .checked_add(1)
                                .ok_or_else(resource)?,
                        )?;
                        if left != right {
                            return Err(invalid());
                        }
                    }
                }
                facts.add(
                    FlowFact::WindowExtent {
                        view: selected_view,
                    },
                    work,
                )?
            }
            None => 0,
        };
        let returned = facts.wrapped(call.returned, output, work)?;
        push(&mut results, (returned, path), work)?;
    }
    Ok(results)
}

fn facts<'a>(work: &mut TypeWorkBudget) -> Result<FlowFacts<'a>, ValidationError> {
    let mut facts = FlowFacts::default();
    for value in [FlowFact::Independent, FlowFact::Fresh, FlowFact::Current] {
        facts.add(value, work)?;
    }
    Ok(facts)
}
fn state_data<'a>(
    facts: &mut FlowFacts<'a>,
    header: &'a CheckedSourceResourceHeader,
    registry: &ResolvedRegistry,
    work: &mut TypeWorkBudget,
) -> Result<usize, ValidationError> {
    let data = facts.input(&header.original.data.ty, registry, work)?;
    let mut fields = Vec::new();
    push(&mut fields, 2, work)?;
    push(&mut fields, data, work)?;
    facts.add(FlowFact::Tuple(fields.into_boxed_slice()), work)
}
fn check_flow(
    program: &UnvalidatedEffectProgram,
    header: &CheckedSourceResourceHeader,
    entry: &(TypedBinder, NodeId),
    phase: SourceResourcePhase,
    globals: &SourceResourceGlobals,
    work: &mut TypeWorkBudget,
) -> Result<SourcePhaseCalls, ValidationError> {
    let mut facts = facts(work)?;
    facts.globals = Some(globals);
    let value = if phase == SourceResourcePhase::Acquire {
        facts.input(&header.original.input.ty, &program.registry, work)?
    } else {
        state_data(&mut facts, header, &program.registry, work)?
    };
    let mut path = FlowPath::new(work)?;
    path.bind(entry.0.id(), value, work)?;
    let results = eval_flow(program, header, entry.1, phase, path, &mut facts, 0, work)?;
    if results.is_empty() {
        return Err(invalid());
    }
    #[cfg(test)]
    if matches!(
        header.codec.report,
        SourceResourceReportCodec::CheckedScope { .. }
    ) {
        eprintln!("checked lifecycle flow {phase:?} results={}", results.len());
    }
    for (value, path) in results {
        #[cfg(test)]
        if matches!(
            header.codec.report,
            SourceResourceReportCodec::CheckedScope { .. }
        ) {
            eprintln!(
                "checked lifecycle result {phase:?} acquired={} consumed={} request={:?} value={:?}",
                path.acquired,
                path.consumed,
                path.checked_finish_outcome,
                facts.fact(value)?
            );
        }
        if phase == SourceResourcePhase::Finish
            && matches!(
                header.codec.report,
                SourceResourceReportCodec::CheckedScope { .. }
            )
        {
            let outcome = path.checked_finish_outcome.ok_or_else(invalid)?;
            let request = outcome.request();
            let FlowFact::Constructor(constructor, Some(payload)) = facts.fact(value)? else {
                return Err(invalid());
            };
            if *constructor == header.codec.finish[0] {
                if !matches!(outcome, CheckedFinishOutcome::Consumed(_))
                    || !path.consumed
                    || !facts.independent(*payload, work)?
                {
                    return Err(invalid());
                }
            } else if *constructor == header.codec.finish[1] {
                let FlowFact::Tuple(fields) = facts.fact(*payload)? else {
                    return Err(invalid());
                };
                if !matches!(outcome, CheckedFinishOutcome::Retained(_))
                    || path.consumed
                    || fields.len() != 2
                    || !matches!(facts.fact(fields[0])?, FlowFact::Current)
                    || !facts.independent(fields[1], work)?
                {
                    return Err(invalid());
                }
            } else if *constructor == header.codec.finish[2] {
                if !matches!(outcome, CheckedFinishOutcome::Boundary(_))
                    || path.consumed
                    || !matches!(facts.fact(*payload)?, FlowFact::FinishBoundary(original) if *original == request)
                {
                    return Err(invalid());
                }
            } else {
                return Err(invalid());
            }
            continue;
        }
        match (phase, facts.fact(value)?) {
            (SourceResourcePhase::Acquire, FlowFact::Constructor(id, Some(payload)))
                if *id == header.codec.acquire[0] =>
            {
                let FlowFact::Tuple(fields) = facts.fact(*payload)? else {
                    return Err(invalid());
                };
                if !path.acquired
                    || fields.len() != 2
                    || !matches!(facts.fact(fields[0])?, FlowFact::Fresh)
                    || !facts.borrowed(fields[1], false, header, work)?
                {
                    return Err(invalid());
                }
            }
            (SourceResourcePhase::Acquire, FlowFact::Constructor(id, payload))
                if *id == header.codec.acquire[1] =>
            {
                // Refusal may abandon a provisional fresh owner; the runtime
                // guard remains pending and runs fallback cleanup on this path.
                if let Some(value) = payload
                    && !facts.independent(*value, work)?
                {
                    return Err(invalid());
                }
            }
            (SourceResourcePhase::Finish, FlowFact::Constructor(id, None))
                if *id == header.codec.finish[0] =>
            {
                if !path.consumed {
                    return Err(invalid());
                }
            }
            (SourceResourcePhase::Finish, FlowFact::Constructor(id, Some(payload)))
                if *id == header.codec.finish[1] =>
            {
                if !path.consumed || !facts.independent(*payload, work)? {
                    return Err(invalid());
                }
            }
            (SourceResourcePhase::Finish, FlowFact::Constructor(id, Some(payload)))
                if *id == header.codec.finish[2] =>
            {
                let FlowFact::Tuple(fields) = facts.fact(*payload)? else {
                    return Err(invalid());
                };
                if !path.attempted_teardown
                    || path.consumed
                    || fields.len() != 2
                    || !matches!(facts.fact(fields[0])?, FlowFact::Current)
                    || !facts.independent(fields[1], work)?
                {
                    return Err(invalid());
                }
            }
            _ => return Err(invalid()),
        }
    }
    Ok(SourcePhaseCalls {
        byte_calls: facts.byte_calls.into_boxed_slice(),
        window_calls: facts.window_calls.into_boxed_slice(),
    })
}
fn check_handler(
    program: &UnvalidatedEffectProgram,
    header: &CheckedSourceResourceHeader,
    state: &TypedBinder,
    callback: &super::function::FunctionNode,
    globals: &SourceResourceGlobals,
    graph: Option<&SourceHandlerGraph<'_>>,
    work: &mut TypeWorkBudget,
) -> Result<SourcePhaseCalls, ValidationError> {
    let body = callback.body();
    let answer = callback.parameter().id();
    let mut facts = facts(work)?;
    facts.globals = Some(globals);
    facts.handler_graph = graph.map(|graph| graph.handler_graph());
    let mut path = FlowPath::new(work)?;
    path.bind(
        state.id(),
        state_data(&mut facts, header, &program.registry, work)?,
        work,
    )?;
    path.bind(answer, 0, work)?;
    let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Match(matching))) =
        &node(program, body)?.kind
    else {
        return Err(invalid());
    };
    if matching.arms().len() != 1 {
        return Err(invalid());
    }
    let values = eval_flow(
        program,
        header,
        matching.scrutinee(),
        SourceResourcePhase::Handler,
        path,
        &mut facts,
        0,
        work,
    )?;
    if values.len() != 1 {
        return Err(invalid());
    }
    let (value, mut path) = values.into_iter().next().ok_or_else(invalid)?;
    let arm = &matching.arms()[0];
    if bind_pattern(
        arm.pattern(),
        value,
        &mut path,
        &mut facts,
        &program.registry,
        0,
        work,
    )? == PatternMatch::Impossible
    {
        return Err(invalid());
    }
    let EffectExprKind::Operation(EffectOperation::Handler(handler)) =
        &node(program, arm.body())?.kind
    else {
        return Err(invalid());
    };
    if crate::types::compare_effect_instances_with_budget(
        handler.effect(),
        &header.original.provided.instance,
        work,
    )
    .map_err(|_| resource())?
        != std::cmp::Ordering::Equal
        || handler.has_hook_contracts()
    {
        return Err(invalid());
    }
    // The synthetic callback supplies the exact provided computation row to
    // ordinary handler validation. Final specialization supplies the actual
    // client body; this callback is never copied into an executable scope.
    let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Apply(application))) =
        &node(program, handler.body())?.kind
    else {
        return Err(invalid());
    };
    let EffectExprKind::Pure(PureExprKind::Variable(placeholder)) =
        &node(program, application.function())?.kind
    else {
        return Err(invalid());
    };
    if placeholder.binder() != answer
        || !matches!(
            &node(program, application.argument())?.kind,
            EffectExprKind::Pure(PureExprKind::Value(PureValue::Unit(_)))
        )
    {
        return Err(invalid());
    }
    for clause in handler.clauses() {
        let mut clause_path = path.copy(work)?;
        bind_pattern(
            clause.pattern(),
            0,
            &mut clause_path,
            &mut facts,
            &program.registry,
            0,
            work,
        )?;
        push(
            &mut clause_path.ordinary_owners,
            (handler.id(), clause.resume()),
            work,
        )?;
        if facts.handler_graph.is_some() {
            for binder in clause.pattern().binder_iter() {
                charge(work, 1)?;
                if binder.ty().function_view().is_some() {
                    let prior = *clause_path.locals.get(&binder.id()).ok_or_else(invalid)?;
                    let value = facts.add(
                        FlowFact::HandlerInputCallable {
                            original: &header.original,
                            operation: clause.operation(),
                            pattern: clause.pattern(),
                            binder,
                            value_type: binder.ty(),
                            value: Some(prior),
                        },
                        work,
                    )?;
                    clause_path.bind(binder.id(), value, work)?;
                }
            }
        }
        for (value, _) in eval_flow(
            program,
            header,
            clause.body(),
            SourceResourcePhase::Handler,
            clause_path,
            &mut facts,
            0,
            work,
        )? {
            if !facts.independent(value, work)? {
                return Err(invalid());
            }
        }
    }
    Ok(SourcePhaseCalls {
        byte_calls: facts.byte_calls.into_boxed_slice(),
        window_calls: facts.window_calls.into_boxed_slice(),
    })
}

/// Complete compiler claim for one immutable defining forest. This is not an
/// executable receipt; final Core reconstructs the relation independently.
pub(crate) struct SourceResourceCopyClaim<'a> {
    pub(crate) nodes: &'a [(NodeId, NodeId)],
    pub(crate) freshening: super::provider::ProviderFreshening<'a>,
    pub(crate) substitution: super::provider::ProviderTemplateSubstitution<'a>,
    pub(crate) node_rows: &'a HashMap<NodeId, crate::types::EffectRow>,
}
#[derive(Debug)]
struct SourceResourceCopy {
    nodes: Box<[(NodeId, NodeId)]>,
    binders: Box<[(crate::resolved::BinderId, crate::resolved::BinderId)]>,
    variables: Box<
        [(
            crate::types::TypeVariableId,
            crate::types::TypeVariableId,
            Kind,
        )],
    >,
    handlers: Box<[(super::HandlerId, super::HandlerId)]>,
    resumes: Box<[(crate::resolved::ResumeId, crate::resolved::ResumeId)]>,
    types: HashMap<crate::types::TypeVariableId, Type>,
    rows: HashMap<crate::types::TypeVariableId, crate::types::EffectRow>,
    pending: HashMap<crate::types::InferenceVariableId, crate::types::EffectRow>,
    node_rows: HashMap<NodeId, crate::types::EffectRow>,
}
impl Drop for SourceResourceCopy {
    fn drop(&mut self) {
        for (_, ty) in std::mem::take(&mut self.types) {
            crate::types::discard_type_iteratively(ty);
        }
        drop(std::mem::take(&mut self.rows));
    }
}
impl SourceResourceCopy {
    fn retain(
        claim: SourceResourceCopyClaim<'_>,
        work: &mut TypeWorkBudget,
    ) -> Result<Self, ValidationError> {
        claim.freshening.authenticate(work)?;
        if !claim.freshening.nominals.is_empty() || !claim.freshening.lexicals.is_empty() {
            return Err(invalid());
        }
        fn pairs<T: Copy>(
            input: &[T],
            work: &mut TypeWorkBudget,
        ) -> Result<Box<[T]>, ValidationError> {
            charge(work, input.len())?;
            let mut output = Vec::new();
            output
                .try_reserve_exact(input.len())
                .map_err(|_| resource())?;
            output.extend_from_slice(input);
            Ok(output.into_boxed_slice())
        }
        let mut variables = Vec::new();
        charge(work, claim.freshening.types.len())?;
        variables
            .try_reserve_exact(claim.freshening.types.len())
            .map_err(|_| resource())?;
        for (source, target, kind) in claim.freshening.types {
            variables.push((
                *source,
                *target,
                crate::types::clone_kind_with_budget(kind, work).map_err(|_| resource())?,
            ));
        }
        let mut types = TypesGuard(HashMap::new());
        charge(work, claim.substitution.types.len())?;
        types
            .0
            .try_reserve(claim.substitution.types.len())
            .map_err(|_| resource())?;
        for (id, ty) in claim.substitution.types {
            types.insert(
                *id,
                crate::types::clone_type_with_budget(ty, work).map_err(|_| resource())?,
            );
        }
        let mut rows = HashMap::new();
        charge(work, claim.substitution.rows.len())?;
        rows.try_reserve(claim.substitution.rows.len())
            .map_err(|_| resource())?;
        for (id, row) in claim.substitution.rows {
            rows.insert(
                *id,
                crate::types::clone_effect_row_with_budget(row, work).map_err(|_| resource())?,
            );
        }
        fn row_map<K: Copy + Eq + std::hash::Hash>(
            input: &HashMap<K, crate::types::EffectRow>,
            work: &mut TypeWorkBudget,
        ) -> Result<HashMap<K, crate::types::EffectRow>, ValidationError> {
            charge(work, input.len())?;
            let mut output = HashMap::new();
            output.try_reserve(input.len()).map_err(|_| resource())?;
            for (id, row) in input {
                output.insert(
                    *id,
                    crate::types::clone_effect_row_with_budget(row, work)
                        .map_err(|_| resource())?,
                );
            }
            Ok(output)
        }
        let pending = row_map(claim.substitution.pending, work)?;
        let node_rows = row_map(claim.node_rows, work)?;
        Ok(Self {
            nodes: pairs(claim.nodes, work)?,
            binders: pairs(claim.freshening.binders, work)?,
            variables: variables.into_boxed_slice(),
            handlers: pairs(claim.freshening.handlers, work)?,
            resumes: pairs(claim.freshening.resumes, work)?,
            types: types.into_map(),
            rows,
            pending,
            node_rows,
        })
    }
    fn fresh(&self) -> super::provider::ProviderFreshening<'_> {
        super::provider::ProviderFreshening {
            binders: &self.binders,
            types: &self.variables,
            handlers: &self.handlers,
            resumes: &self.resumes,
            nominals: &[],
            lexicals: &[],
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct SourceResourceLifecycleEntry {
    pub(crate) parameter: TypedBinder,
    pub(crate) body: NodeId,
}

#[derive(Debug)]
struct SourceResourceScopeDescriptor {
    template: Arc<CheckedSourceResourceTemplate>,
    arguments: Box<[KindedArgument]>,
    identity: crate::types::TypeVariableId,
    interpretations: Box<[super::NativeInterpretation]>,
    copies: [SourceResourceCopy; 3],
    handler_rows: Option<Arc<super::provider::ResolvedProviderHandlerRows>>,
}
impl Drop for SourceResourceScopeDescriptor {
    fn drop(&mut self) {
        for argument in std::mem::take(&mut self.arguments).into_vec() {
            crate::types::discard_kinded_argument_iteratively(argument);
        }
    }
}
impl PartialEq for SourceResourceScopeDescriptor {
    fn eq(&self, other: &Self) -> bool {
        std::ptr::eq(self, other)
    }
}
impl Eq for SourceResourceScopeDescriptor {}

/// A source scope has no experimental manifest and no unchecked execution bit.
/// The ordinary validated-program boundary authenticates its retained originals,
/// complete substitutions, fresh identities and actual copied forests.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SourceResourceScopeNode {
    descriptor: Arc<SourceResourceScopeDescriptor>,
    pub(crate) initializer: NodeId,
    pub(crate) acquire: SourceResourceLifecycleEntry,
    pub(crate) finish: SourceResourceLifecycleEntry,
    pub(crate) handler_state: TypedBinder,
    pub(crate) handler_pattern: CorePattern,
    pub(crate) handle: TypedBinder,
    pub(crate) handler: super::HandlerNode,
    pub(crate) handler_output: crate::types::ComputationType,
    pub(crate) lexical: crate::interface::LexicalEvidenceId,
    pub(crate) forwardings: Box<[super::provider::ProviderForwardingMethod]>,
}
impl Drop for SourceResourceScopeNode {
    fn drop(&mut self) {
        crate::types::discard_type_iteratively(std::mem::replace(
            &mut self.handler_output.value,
            Type::Unit,
        ));
        let placeholder = CorePattern::new(
            Type::Unit,
            crate::source::Origin::Source(self.handler_pattern.origin.primary_span()),
            CorePatternKind::Wildcard,
        );
        std::mem::replace(&mut self.handler_pattern, placeholder).discard_iteratively();
    }
}
impl SourceResourceScopeNode {
    pub(in crate::core) fn visit_semantic_type_variables(
        &self,
        uses: &mut crate::core::validate::semantic_type_variables::UnusedVariables<'_>,
    ) -> Result<(), ()> {
        uses.source_header(&self.header().original)?;
        // Operation metadata already visits the ordered arguments and every
        // interpretation. This additional walk covers retained copy/original
        // correspondence and conditional row/capture claims.
        for copy in self.copy_claims() {
            uses.charge(copy.freshening.types.len())?;
            for (original, copied, _) in copy.freshening.types {
                uses.id(*original)?;
                uses.id(*copied)?;
            }
            uses.charge(
                copy.substitution.types.len()
                    + copy.substitution.rows.len()
                    + copy.substitution.pending.len()
                    + copy.node_rows.len(),
            )?;
            for (id, ty) in copy.substitution.types {
                uses.id(*id)?;
                uses.ty(ty)?;
            }
            for (id, row) in copy.substitution.rows {
                uses.id(*id)?;
                uses.row(row)?;
            }
            for row in copy
                .substitution
                .pending
                .values()
                .chain(copy.node_rows.values())
            {
                uses.row(row)?;
            }
        }
        if let Some(rows) = self.handler_row_claim() {
            rows.visit_semantic_type_variables(uses)?;
        }
        self.original().visit_semantic_type_variables(uses)
    }
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn new(
        template: Arc<CheckedSourceResourceTemplate>,
        arguments: Box<[KindedArgument]>,
        identity: crate::types::TypeVariableId,
        initializer: NodeId,
        acquire: SourceResourceLifecycleEntry,
        finish: SourceResourceLifecycleEntry,
        handler_state: TypedBinder,
        handler_pattern: CorePattern,
        handle: TypedBinder,
        handler: super::HandlerNode,
        mut handler_output: crate::types::ComputationType,
        lexical: crate::interface::LexicalEvidenceId,
        forwardings: Box<[super::provider::ProviderForwardingMethod]>,
        copies: [SourceResourceCopyClaim<'_>; 3],
        work: &mut TypeWorkBudget,
    ) -> Result<Self, ValidationError> {
        let mut handler_pattern = PatternGuard(Some(handler_pattern));
        let output = crate::types::IterativeTypeOwner::new(std::mem::replace(
            &mut handler_output.value,
            Type::Unit,
        ));
        let arguments = ArgumentsGuard(arguments.into_vec());
        charge(work, arguments.0.len())?;
        let [acquire_copy, finish_copy, handler_copy] = copies;
        let copies = [
            SourceResourceCopy::retain(acquire_copy, work)?,
            SourceResourceCopy::retain(finish_copy, work)?,
            SourceResourceCopy::retain(handler_copy, work)?,
        ];
        if copies[..2]
            .iter()
            .any(|copy| !copy.pending.is_empty() || !copy.node_rows.is_empty())
        {
            return Err(invalid());
        }
        if let Some(original) = &template.handler_rows {
            let (nodes, _) = original.recipe.deferred_copy_domain(work)?;
            charge(
                work,
                nodes
                    .len()
                    .checked_add(original.inputs.pending.equations.len())
                    .ok_or_else(resource)?,
            )?;
            if copies[2].node_rows.len() != nodes.len()
                || nodes.iter().any(|id| !copies[2].node_rows.contains_key(id))
                || copies[2].pending.len() != original.inputs.pending.equations.len()
                || original
                    .inputs
                    .pending
                    .identities()
                    .any(|id| !copies[2].pending.contains_key(&id))
            {
                return Err(invalid());
            }
        } else if !copies[2].pending.is_empty() || !copies[2].node_rows.is_empty() {
            return Err(invalid());
        }

        let mut interpretations = Vec::new();
        charge(work, template.header.original.interpreted.len())?;
        interpretations
            .try_reserve_exact(template.header.original.interpreted.len())
            .map_err(|_| resource())?;
        for effect in &template.header.original.interpreted {
            let mut actuals = ArgumentsGuard(Vec::new());
            charge(work, effect.instance.arguments().len())?;
            actuals
                .0
                .try_reserve_exact(effect.instance.arguments().len())
                .map_err(|_| resource())?;
            for argument in effect.instance.arguments() {
                actuals.0.push(
                    crate::types::substitute_argument_for_template_with(
                        argument,
                        &copies[0].types,
                        &copies[0].rows,
                        &HashMap::new(),
                        &crate::types::TemplateIdentityRenaming {
                            nominals: &HashMap::new(),
                            variables: &HashMap::new(),
                        },
                        |cells| work.charge(cells).map_err(|_| resource()),
                        resource,
                    )?
                    .map_err(|_| invalid())?,
                );
            }
            let instance = crate::types::EffectInstance::new_kinded(
                effect.instance.effect(),
                actuals.into_boxed_slice(),
            );
            let symbol = Arc::clone(
                template
                    .original_acquire()
                    .registry
                    .native_symbol(OperationId::new(effect.instance.effect(), 0))
                    .ok_or_else(invalid)?,
            );
            interpretations.push(super::NativeInterpretation::new(instance, symbol));
        }
        handler_output.value = output.into_inner();
        Ok(Self {
            descriptor: Arc::new(SourceResourceScopeDescriptor {
                template,
                arguments: arguments.into_boxed_slice(),
                identity,
                interpretations: interpretations.into_boxed_slice(),
                copies,
                handler_rows: None,
            }),
            initializer,
            acquire,
            finish,
            handler_state,
            handler_pattern: handler_pattern
                .0
                .take()
                .expect("retained source handler pattern"),
            handle,
            handler,
            handler_output,
            lexical,
            forwardings,
        })
    }
    /// Finishes only an instance's solved Type/Row specialization. The defining
    /// template, identity/freshening maps and copied forest stay immutable; final
    /// Core still reconstructs and compares the complete correspondence.
    pub(crate) fn finalize_instantiation(
        &mut self,
        rewrite: &mut dyn FnMut(&Type) -> Result<Type, super::BuildError>,
        rewrite_row: &mut dyn FnMut(
            &crate::types::EffectRow,
        ) -> Result<crate::types::EffectRow, super::BuildError>,
        work: &mut TypeWorkBudget,
    ) -> Result<(), super::BuildError> {
        let exhausted = || super::BuildError::TypeWorkExceeded;
        let retain_error = |error: ValidationError| {
            if error.reason() == ValidationReason::Resource {
                exhausted()
            } else {
                super::BuildError::InvalidPayload
            }
        };
        // A transformed or cloned scope must not rewrite another scope's claim.
        // Retain a private descriptor before touching any shared specialization.
        if Arc::get_mut(&mut self.descriptor).is_none() {
            let [first, second, third] = self.copy_claims();
            let copies = [
                SourceResourceCopy::retain(first, work).map_err(retain_error)?,
                SourceResourceCopy::retain(second, work).map_err(retain_error)?,
                SourceResourceCopy::retain(third, work).map_err(retain_error)?,
            ];
            let arguments = ArgumentsGuard(
                crate::types::clone_kinded_arguments_with_budget(self.arguments().iter(), work)
                    .map_err(|_| exhausted())?
                    .into_vec(),
            );
            let interpretations = super::effect::copy_native_interpretations_with_budget(
                self.native_interpretations(),
                work,
            )?;
            self.descriptor = Arc::new(SourceResourceScopeDescriptor {
                template: Arc::clone(self.original()),
                arguments: arguments.into_boxed_slice(),
                identity: self.identity(),
                interpretations,
                copies,
                handler_rows: self.descriptor.handler_rows.as_ref().map(Arc::clone),
            });
        }
        let descriptor =
            Arc::get_mut(&mut self.descriptor).ok_or(super::BuildError::InvalidPayload)?;
        finalize_arguments(&mut descriptor.arguments, rewrite, rewrite_row, work)?;
        for copy in &mut descriptor.copies {
            work.charge(
                copy.types
                    .len()
                    .checked_add(copy.rows.len())
                    .and_then(|count| count.checked_add(copy.pending.len()))
                    .and_then(|count| count.checked_add(copy.node_rows.len()))
                    .ok_or_else(exhausted)?,
            )
            .map_err(|_| exhausted())?;
            for actual in copy.types.values_mut() {
                let replacement = rewrite(actual)?;
                crate::types::replace_type_iteratively(actual, replacement);
            }
            for actual in copy
                .rows
                .values_mut()
                .chain(copy.pending.values_mut())
                .chain(copy.node_rows.values_mut())
            {
                *actual = rewrite_row(actual)?;
            }
        }
        if let Some(rows) = &descriptor.handler_rows {
            descriptor.handler_rows = Some(Arc::new(rows.rewrite_source_claim(rewrite_row, work)?));
        }
        work.charge(descriptor.interpretations.len())
            .map_err(|_| exhausted())?;
        for interpretation in &mut descriptor.interpretations {
            finalize_instance(&mut interpretation.effect, rewrite, rewrite_row, work)?;
        }
        work.charge(4).map_err(|_| exhausted())?;
        for binder in [
            &mut self.acquire.parameter,
            &mut self.finish.parameter,
            &mut self.handler_state,
            &mut self.handle,
        ] {
            binder.rewrite_type(&mut |ty| rewrite(ty))?;
        }
        self.handler_pattern.rewrite_types(&mut |ty| rewrite(ty))?;
        let output = rewrite(self.handler_output.value())?;
        crate::types::replace_type_iteratively(&mut self.handler_output.value, output);
        self.handler_output.effects = rewrite_row(self.handler_output.effects())?;
        finalize_instance(&mut self.handler.effect, rewrite, rewrite_row, work)?;
        work.charge(self.handler.clauses.len())
            .map_err(|_| exhausted())?;
        for clause in &mut self.handler.clauses {
            clause
                .arm
                .pattern_mut()
                .rewrite_types(&mut |ty| rewrite(ty))?;
        }
        Ok(())
    }

    pub(crate) fn retain_handler_rows(
        &mut self,
        rows: Arc<super::provider::ResolvedProviderHandlerRows>,
        work: &mut TypeWorkBudget,
    ) -> Result<(), super::BuildError> {
        work.charge(1)
            .map_err(|_| super::BuildError::TypeWorkExceeded)?;
        if !self.original().has_conditional_handler_rows() || self.descriptor.handler_rows.is_some()
        {
            return Err(super::BuildError::InvalidPayload);
        }
        Arc::get_mut(&mut self.descriptor)
            .ok_or(super::BuildError::InvalidPayload)?
            .handler_rows = Some(rows);
        Ok(())
    }

    pub(in crate::core) fn retain_handler_rows_from(
        &mut self,
        original: &Self,
        work: &mut TypeWorkBudget,
    ) -> Result<(), super::BuildError> {
        work.charge(1)
            .map_err(|_| super::BuildError::TypeWorkExceeded)?;
        if !Arc::ptr_eq(self.original(), original.original())
            || self.descriptor.handler_rows.is_some()
        {
            return Err(super::BuildError::InvalidPayload);
        }
        Arc::get_mut(&mut self.descriptor)
            .ok_or(super::BuildError::InvalidPayload)?
            .handler_rows = original.descriptor.handler_rows.as_ref().map(Arc::clone);
        Ok(())
    }

    pub(crate) fn handler_row_claim(
        &self,
    ) -> Option<&super::provider::ResolvedProviderHandlerRows> {
        self.descriptor.handler_rows.as_deref()
    }

    pub(crate) fn original(&self) -> &Arc<CheckedSourceResourceTemplate> {
        &self.descriptor.template
    }
    pub(crate) fn header(&self) -> &Arc<CheckedSourceResourceHeader> {
        self.original().header()
    }
    pub(crate) fn arguments(&self) -> &[KindedArgument] {
        &self.descriptor.arguments
    }
    pub(crate) fn identity(&self) -> crate::types::TypeVariableId {
        self.descriptor.identity
    }
    pub(crate) fn native_interpretations(&self) -> &[super::NativeInterpretation] {
        &self.descriptor.interpretations
    }
    pub(crate) fn copy_claims(&self) -> [SourceResourceCopyClaim<'_>; 3] {
        std::array::from_fn(|index| {
            let copy = &self.descriptor.copies[index];
            SourceResourceCopyClaim {
                nodes: &copy.nodes,
                freshening: copy.fresh(),
                substitution: super::provider::ProviderTemplateSubstitution {
                    types: &copy.types,
                    rows: &copy.rows,
                    pending: &copy.pending,
                },
                node_rows: &copy.node_rows,
            }
        })
    }

    pub(crate) fn child_count(&self) -> usize {
        4 + self.handler.clauses().len()
    }
    pub(crate) fn child_at(&self, index: usize) -> Option<NodeId> {
        match index {
            0 => Some(self.initializer),
            1 => Some(self.acquire.body),
            2 => Some(self.finish.body),
            3 => Some(self.handler.body()),
            4.. => self
                .handler
                .clauses()
                .get(index - 4)
                .map(super::EffectClause::body),
        }
    }
    pub(crate) fn contains_phase_request(
        &self,
        program: &super::dialect::CoreProgram<super::EffectOperationFamily>,
        request: NodeId,
        phase: SourceResourcePhase,
        work: &mut TypeWorkBudget,
    ) -> Result<bool, ValidationError> {
        let index = match phase {
            SourceResourcePhase::Acquire => 0,
            SourceResourcePhase::Finish => 1,
            SourceResourcePhase::Handler => 2,
        };
        let copy = &self.descriptor.copies[index];
        charge(work, copy.nodes.len())?;
        if !copy.nodes.iter().any(|(_, actual)| *actual == request) {
            return Ok(false);
        }
        let Some(node) = program.node(request) else {
            return Ok(false);
        };
        let EffectExprKind::Operation(EffectOperation::Request(call)) = &node.kind else {
            return Ok(false);
        };
        let Some(symbol) = program.registry().native_symbol(call.operation()) else {
            return Ok(false);
        };
        let expected = match phase {
            SourceResourcePhase::Acquire => Some(&self.header().acquire),
            SourceResourcePhase::Finish => Some(&self.header().teardown),
            SourceResourcePhase::Handler => None,
        };
        if !expected.is_some_and(|expected| Arc::ptr_eq(expected, symbol))
            && !(matches!(symbol.owner_role(), Some(PreparedOwnerCall::Borrow { .. }))
                && symbol
                    .owner()
                    .is_some_and(|owner| Arc::ptr_eq(owner, &self.header().owner)))
        {
            return Ok(false);
        }
        for interpretation in self.native_interpretations() {
            if Arc::ptr_eq(interpretation.symbol(), symbol)
                && crate::types::compare_effect_instances_with_budget(
                    interpretation.effect(),
                    call.effect(),
                    work,
                )
                .map_err(|_| resource())?
                    == std::cmp::Ordering::Equal
            {
                return Ok(true);
            }
        }
        Ok(false)
    }

    pub(crate) fn visit_windows(
        &self,
        mut visit: impl FnMut(NodeId, &mut TypeWorkBudget) -> Result<(), ValidationError>,
        work: &mut TypeWorkBudget,
    ) -> Result<(), ValidationError> {
        for (phase, copy) in self.descriptor.copies.iter().enumerate() {
            let original = match phase {
                0 => self.original().original_acquire(),
                1 => self.original().original_finish(),
                _ => self.original().original_handler(),
            };
            for (source, target) in &copy.nodes {
                charge(work, 1)?;
                if matches!(
                    node(original, *source)?.kind,
                    EffectExprKind::Operation(EffectOperation::SourceCopyWindow(_))
                ) {
                    visit(*target, work)?;
                }
            }
        }
        Ok(())
    }

    /// Exact mapped window occurrence in one defining lifecycle phase. The
    /// final independent specialization check owns this map; runtime activation
    /// and selected guard remain separate obligations.
    pub(crate) fn contains_phase_window(
        &self,
        phase: SourceResourcePhase,
        window: NodeId,
        work: &mut TypeWorkBudget,
    ) -> Result<bool, ValidationError> {
        let index = match phase {
            SourceResourcePhase::Acquire => 0,
            SourceResourcePhase::Finish => 1,
            SourceResourcePhase::Handler => 2,
        };
        let original = match index {
            0 => self.original().original_acquire(),
            1 => self.original().original_finish(),
            _ => self.original().original_handler(),
        };
        let copy = &self.descriptor.copies[index];
        charge(work, copy.nodes.len())?;
        for (source, target) in &copy.nodes {
            if *target == window {
                return Ok(matches!(
                    node(original, *source)?.kind,
                    EffectExprKind::Operation(EffectOperation::SourceCopyWindow(_))
                ));
            }
        }
        Ok(false)
    }

    /// An original flow-authenticated request under this particular window,
    /// mapped through the same complete checked lifecycle copy.
    pub(crate) fn contains_window_request(
        &self,
        phase: SourceResourcePhase,
        window: NodeId,
        request: NodeId,
        symbol: &Arc<CheckedForeignSymbol>,
        work: &mut TypeWorkBudget,
    ) -> Result<bool, ValidationError> {
        let index = match phase {
            SourceResourcePhase::Acquire => 0,
            SourceResourcePhase::Finish => 1,
            SourceResourcePhase::Handler => 2,
        };
        let original = match index {
            0 => self.original().original_acquire(),
            1 => self.original().original_finish(),
            _ => self.original().original_handler(),
        };
        let copy = &self.descriptor.copies[index];
        charge(work, copy.nodes.len())?;
        let source_window = copy
            .nodes
            .iter()
            .find_map(|(source, target)| (*target == window).then_some(*source));
        let source_request = copy
            .nodes
            .iter()
            .find_map(|(source, target)| (*target == request).then_some(*source));
        let (Some(window), Some(request)) = (source_window, source_request) else {
            return Ok(false);
        };
        charge(work, self.original().window_calls[index].len())?;
        if !self.original().window_calls[index]
            .iter()
            .any(|call| call.window == window && call.request == request)
        {
            return Ok(false);
        }
        let EffectExprKind::Operation(EffectOperation::Request(call)) =
            &node(original, request)?.kind
        else {
            return Err(invalid());
        };
        Ok(original
            .registry
            .native_symbol(call.operation())
            .is_some_and(|original| Arc::ptr_eq(original, symbol)))
    }

    /// Exposes only original window requests mapped through this scope's
    /// independently authenticated specialization forest. It is representation
    /// lineage for capture analysis, not permission to execute a native call.
    pub(in crate::core) fn visit_window_calls(
        &self,
        mut visit: impl FnMut(
            NodeId,
            NodeId,
            &CheckedForeignSymbol,
            &mut TypeWorkBudget,
        ) -> Result<(), ValidationError>,
        work: &mut TypeWorkBudget,
    ) -> Result<(), ValidationError> {
        for (phase, copy) in self.descriptor.copies.iter().enumerate() {
            let original = match phase {
                0 => self.original().original_acquire(),
                1 => self.original().original_finish(),
                _ => self.original().original_handler(),
            };
            charge(work, self.original().window_calls[phase].len())?;
            for relation in &self.original().window_calls[phase] {
                let EffectExprKind::Operation(EffectOperation::Request(call)) =
                    &node(original, relation.request)?.kind
                else {
                    return Err(invalid());
                };
                let symbol = original
                    .registry
                    .native_symbol(call.operation())
                    .ok_or_else(invalid)?;
                let mut request = None;
                let mut window = None;
                charge(work, copy.nodes.len())?;
                for (source, target) in &copy.nodes {
                    if *source == relation.request {
                        request = Some(*target);
                    }
                    if *source == relation.window {
                        window = Some(*target);
                    }
                }
                visit(
                    request.ok_or_else(invalid)?,
                    window.ok_or_else(invalid)?,
                    symbol,
                    work,
                )?;
            }
        }
        Ok(())
    }

    /// Maps a flow-proved original call and its selected canonical type
    /// application through the independently authenticated specialization forest.
    pub(crate) fn visit_byte_calls(
        &self,
        mut visit: impl FnMut(SourceByteCall, &mut TypeWorkBudget) -> Result<(), ValidationError>,
        work: &mut TypeWorkBudget,
    ) -> Result<(), ValidationError> {
        for phase in [
            SourceResourcePhase::Acquire,
            SourceResourcePhase::Finish,
            SourceResourcePhase::Handler,
        ] {
            self.visit_phase_byte_calls(phase, &mut visit, work)?;
        }
        Ok(())
    }

    fn visit_phase_byte_calls(
        &self,
        phase: SourceResourcePhase,
        mut visit: impl FnMut(SourceByteCall, &mut TypeWorkBudget) -> Result<(), ValidationError>,
        work: &mut TypeWorkBudget,
    ) -> Result<(), ValidationError> {
        let index = match phase {
            SourceResourcePhase::Acquire => 0,
            SourceResourcePhase::Finish => 1,
            SourceResourcePhase::Handler => 2,
        };
        let copy = &self.descriptor.copies[index];
        for call in &self.original().byte_calls[index] {
            charge(work, copy.nodes.len())?;
            let map = |original| {
                copy.nodes
                    .iter()
                    .find_map(|(source, target)| (*source == original).then_some(*target))
            };
            visit(
                SourceByteCall {
                    apply: call
                        .apply
                        .map(|apply| map(apply).ok_or_else(invalid))
                        .transpose()?,
                    application: map(call.application).ok_or_else(invalid)?,
                    function: call.function,
                },
                work,
            )?;
        }
        Ok(())
    }

    pub(crate) fn contains_byte_call(
        &self,
        phase: SourceResourcePhase,
        apply: NodeId,
        application: NodeId,
        function: crate::resolved::BinderId,
        work: &mut TypeWorkBudget,
    ) -> Result<bool, ValidationError> {
        let mut found = false;
        self.visit_phase_byte_calls(
            phase,
            |call, _| {
                found |= call
                    == SourceByteCall {
                        apply: Some(apply),
                        application,
                        function,
                    };
                Ok(())
            },
            work,
        )?;
        Ok(found)
    }

    /// Enumerates only original checked lifecycle requests whose exact copied
    /// occurrences and full instances belong to this independently checked
    /// scope. A caller cannot turn a general native request into phase code.
    pub(in crate::core) fn visit_phase_requests(
        &self,
        program: &UnvalidatedEffectProgram,
        mut visit: impl FnMut(NodeId, &mut TypeWorkBudget) -> Result<(), ValidationError>,
        work: &mut TypeWorkBudget,
    ) -> Result<(), ValidationError> {
        for (phase, original, expected) in [
            (
                0,
                self.original().original_acquire(),
                Some(&self.header().acquire),
            ),
            (
                1,
                self.original().original_finish(),
                Some(&self.header().teardown),
            ),
            (2, self.original().original_handler(), None),
        ] {
            let copy = &self.descriptor.copies[phase];
            charge(work, copy.nodes.len())?;
            for (source, target) in &copy.nodes {
                let EffectExprKind::Operation(EffectOperation::Request(original_call)) =
                    &node(original, *source)?.kind
                else {
                    continue;
                };
                // Ordinary outward requests keep their checked effect rows and
                // are not permissions for the native owner interpreter. Their
                // copied correspondence was authenticated with the whole forest.
                charge(work, 1)?;
                if original
                    .registry
                    .native_symbol(original_call.operation())
                    .is_none_or(|symbol| symbol.owner().is_none())
                {
                    continue;
                }
                let EffectExprKind::Operation(EffectOperation::Request(call)) =
                    &node(program, *target)?.kind
                else {
                    return Err(invalid());
                };
                let symbol = original
                    .registry
                    .native_symbol(original_call.operation())
                    .ok_or_else(invalid)?;
                charge(work, self.original().window_calls[phase].len())?;
                if let Some(window_call) = self.original().window_calls[phase]
                    .iter()
                    .find(|record| record.request == *source)
                {
                    let window = copy
                        .nodes
                        .iter()
                        .find_map(|(original, actual)| {
                            (*original == window_call.window).then_some(*actual)
                        })
                        .ok_or_else(invalid)?;
                    let EffectExprKind::Operation(EffectOperation::SourceCopyWindow(window)) =
                        &node(program, window)?.kind
                    else {
                        return Err(invalid());
                    };
                    let actual = program
                        .registry
                        .native_symbol(call.operation())
                        .ok_or_else(invalid)?;
                    if !Arc::ptr_eq(symbol, actual)
                        || !crate::foreign::source_access::window_operation_matches(
                            window.family(),
                            window.arguments(),
                            actual,
                            call.effect(),
                            &program.registry,
                            work,
                        )
                        .map_err(|error| {
                            if error.is_resource_exhaustion() {
                                resource()
                            } else {
                                invalid()
                            }
                        })?
                    {
                        return Err(invalid());
                    }
                    visit(*target, work)?;
                    continue;
                }
                if original_call.operation() != call.operation()
                    || !(expected.is_some_and(|expected| Arc::ptr_eq(expected, symbol))
                        || matches!(symbol.owner_role(), Some(PreparedOwnerCall::Borrow { .. }))
                            && symbol
                                .owner()
                                .is_some_and(|owner| Arc::ptr_eq(owner, &self.header().owner)))
                {
                    return Err(invalid());
                }
                let mut covered = false;
                for interpretation in self.native_interpretations() {
                    charge(work, 1)?;
                    if Arc::ptr_eq(interpretation.symbol(), symbol)
                        && crate::types::compare_effect_instances_with_budget(
                            interpretation.effect(),
                            call.effect(),
                            work,
                        )
                        .map_err(|_| resource())?
                            == std::cmp::Ordering::Equal
                    {
                        covered = true;
                        break;
                    }
                }
                if !covered {
                    return Err(invalid());
                }
                visit(*target, work)?;
            }
        }
        Ok(())
    }
}

impl SourceResourceScopeNode {
    /// Independently reconstructs immutable originals and complete specialization.
    /// Caller-authored maps supply claims only; every copied occurrence is paid
    /// for and compared against its exact defining node and provenance.
    pub(in crate::core) fn authenticate(
        &self,
        id: NodeId,
        program: &UnvalidatedEffectProgram,
        work: &mut TypeWorkBudget,
    ) -> Result<(), ValidationError> {
        let template = self.original();
        if template.has_conditional_handler_rows() && self.descriptor.handler_rows.is_none() {
            return Err(invalid());
        }
        let header =
            CheckedSourceResourceHeader::admit(&template.header.original, &program.registry, work)?;
        charge(work, template.header.dependencies.len().saturating_add(3))?;
        if !Arc::ptr_eq(&header.owner, &template.header.owner)
            || !Arc::ptr_eq(&header.acquire, &template.header.acquire)
            || !Arc::ptr_eq(&header.teardown, &template.header.teardown)
            || header.dependencies != template.header.dependencies
            || header.codec != template.header.codec
        {
            return Err(invalid());
        }
        for (position, argument) in self.arguments().iter().enumerate() {
            if position == template.header.original.owned_position {
                continue;
            }
            if crate::types::visit_argument_structure_with_budget(argument, work, |node, _| {
                Ok(match node {
                    crate::types::TypeStructureNode::Type(Type::Variable(id)) => {
                        *id == self.identity()
                    }
                    crate::types::TypeStructureNode::Tail(tail) => {
                        tail.variable() == crate::types::EffectRowVariable::Rigid(self.identity())
                    }
                    _ => false,
                })
            })
            .map_err(|_| resource())?
            {
                return Err(invalid());
            }
        }
        let formals = &template.header.original.parameters;
        if formals.len() != self.arguments().len()
            || !matches!(self.arguments().get(template.header.original.owned_position),Some(KindedArgument::TypeArg(Type::Variable(identity))) if *identity==self.identity())
        {
            return Err(invalid());
        }
        let realized = if template.has_conditional_handler_rows() {
            let mut types = TypesGuard(HashMap::new());
            let mut rows = HashMap::new();
            charge(work, formals.len())?;
            types.0.try_reserve(formals.len()).map_err(|_| resource())?;
            rows.try_reserve(formals.len()).map_err(|_| resource())?;
            for (formal, argument) in formals.iter().zip(self.arguments()) {
                match (&formal.kind, argument) {
                    (Kind::Type, KindedArgument::TypeArg(ty)) => types.insert(
                        formal.id,
                        crate::types::clone_type_with_budget(ty, work).map_err(|_| resource())?,
                    ),
                    (Kind::EffectRow, KindedArgument::RowArg(row)) => {
                        rows.insert(
                            formal.id,
                            crate::types::clone_effect_row_with_budget(row, work)
                                .map_err(|_| resource())?,
                        );
                    }
                    _ => return Err(invalid()),
                }
            }
            let root_bindings =
                crate::core::capture::source_root_bindings(program, work).map_err(|failure| {
                    match failure {
                        crate::core::capture::Failure::Resource => resource(),
                        _ => invalid(),
                    }
                })?;
            let captures = crate::core::capture::reconstruct_source_captures(
                &program.nodes,
                program.arena,
                id,
                &root_bindings,
                &[],
                &[],
                &[],
                super::provider::row_effect_operation,
                work,
            )
            .map_err(|failure| match failure {
                crate::core::capture::Failure::Resource => resource(),
                _ => invalid(),
            })?;
            let actual = template.realize_handler_rows(
                &types.0,
                &rows,
                &node(program, self.handler.body())?.ty,
                &node(program, self.handler.body())?.effects,
                self.handler.effect(),
                Some(captures),
                work,
            )?;
            if !self
                .descriptor
                .handler_rows
                .as_ref()
                .ok_or_else(invalid)?
                .same_actual_captures(&actual, work)?
            {
                return Err(invalid());
            }
            Some(actual)
        } else {
            if self.descriptor.handler_rows.is_some() {
                return Err(invalid());
            }
            None
        };
        let forests = [
            source_inventory(template, 0, &self.descriptor.copies[0], work)?,
            source_inventory(template, 1, &self.descriptor.copies[1], work)?,
            source_inventory(template, 2, &self.descriptor.copies[2], work)?,
        ];
        let mut original_binders = std::collections::HashSet::new();
        let mut original_types = std::collections::HashSet::new();
        let mut original_handlers = std::collections::HashSet::new();
        let mut original_resumes = std::collections::HashSet::new();
        for forest in &forests {
            let inventory = &forest.inventory;
            if !inventory.nominals.is_empty() || !inventory.lexicals.is_empty() {
                return Err(invalid());
            }
            retain_set(
                &mut original_binders,
                inventory.binders.iter().copied(),
                work,
            )?;
            retain_set(
                &mut original_types,
                inventory.types.iter().map(|(id, _)| *id),
                work,
            )?;
            retain_set(
                &mut original_handlers,
                inventory.handlers.iter().copied(),
                work,
            )?;
            retain_set(
                &mut original_resumes,
                inventory.resumes.iter().copied(),
                work,
            )?;
        }
        let mut target_binders = std::collections::HashSet::new();
        let mut target_types = std::collections::HashSet::new();
        let mut target_handlers = std::collections::HashSet::new();
        let mut target_resumes = std::collections::HashSet::new();
        let mut copied_targets = std::collections::HashSet::new();
        for (phase, copy) in self.descriptor.copies.iter().enumerate() {
            let inventory = &forests[phase].inventory;
            exact_fresh_pairs(
                &inventory.binders,
                &copy.binders,
                &original_binders,
                &mut target_binders,
                work,
            )?;
            exact_fresh_pairs(
                &inventory.handlers,
                &copy.handlers,
                &original_handlers,
                &mut target_handlers,
                work,
            )?;
            exact_fresh_pairs(
                &inventory.resumes,
                &copy.resumes,
                &original_resumes,
                &mut target_resumes,
                work,
            )?;
            charge(work, inventory.types.len() + copy.variables.len())?;
            if inventory.types.len() != copy.variables.len() {
                return Err(invalid());
            }
            let mut kinds = HashMap::new();
            kinds
                .try_reserve(inventory.types.len())
                .map_err(|_| resource())?;
            for (id, kind) in &inventory.types {
                kinds.insert(*id, kind);
            }
            target_types
                .try_reserve(copy.variables.len())
                .map_err(|_| resource())?;
            for (source, target, kind) in &copy.variables {
                let original_kind = kinds.remove(source).ok_or_else(invalid)?;
                if !crate::types::same_kind_with_budget(original_kind, kind, work)
                    .map_err(|_| resource())?
                    || original_types.contains(target)
                    || !target_types.insert(*target)
                {
                    return Err(invalid());
                }
            }
            let original = match phase {
                0 => &template.acquire,
                1 => &template.finish,
                _ => &template.handler,
            };
            let root = match phase {
                0 => template.acquire_entry.1,
                1 => template.finish_entry.1,
                _ => template.handler_entry.1,
            };
            charge(
                work,
                copy.types.len() + copy.rows.len() + copy.nodes.len() + formals.len(),
            )?;
            if copy.types.len() + copy.rows.len() != formals.len() + 2 * usize::from(phase == 2) {
                return Err(invalid());
            }
            for (formal, argument) in formals.iter().zip(self.arguments()) {
                match (&formal.kind, argument) {
                    (Kind::Type, KindedArgument::TypeArg(actual)) => {
                        if !same(
                            copy.types.get(&formal.id).ok_or_else(invalid)?,
                            actual,
                            work,
                        )? {
                            return Err(invalid());
                        }
                    }
                    (Kind::EffectRow, KindedArgument::RowArg(actual)) => {
                        if !crate::types::same_effect_rows_with_budget(
                            copy.rows.get(&formal.id).ok_or_else(invalid)?,
                            actual,
                            work,
                        )
                        .map_err(|_| resource())?
                        {
                            return Err(invalid());
                        }
                    }
                    _ => return Err(invalid()),
                }
            }
            if phase == 2
                && !same(
                    copy.types
                        .get(&template.header.original.answer.id)
                        .ok_or_else(invalid)?,
                    &node(program, self.handler.body())?.ty,
                    work,
                )?
            {
                return Err(invalid());
            }
            if phase == 2 {
                let expected = if let Some(rows) = &realized {
                    if !crate::types::same_effect_rows_with_budget(
                        self.handler_output.effects(),
                        rows.output(),
                        work,
                    )
                    .map_err(|_| resource())?
                    {
                        return Err(invalid());
                    }
                    crate::types::clone_effect_row_with_budget(rows.residual(), work)
                        .map_err(|_| resource())?
                } else {
                    let body = &node(program, self.handler.body())?.effects;
                    match body
                        .remove_exact_with_budget(self.handler.effect(), work)
                        .map_err(|_| resource())?
                    {
                        Ok(row) => row,
                        Err(crate::types::EffectRowError::Missing) => {
                            crate::types::clone_effect_row_with_budget(body, work)
                                .map_err(|_| resource())?
                        }
                        Err(_) => return Err(invalid()),
                    }
                };
                if !crate::types::same_effect_rows_with_budget(
                    copy.rows
                        .get(&template.handler_continuation())
                        .ok_or_else(invalid)?,
                    &expected,
                    work,
                )
                .map_err(|_| resource())?
                {
                    return Err(invalid());
                }
            }
            if phase == 0 {
                // The retained native list is an ordered specialization claim,
                // just like the copied forests. Authenticate every original
                // instance and exact symbol before it can cover a request.
                let interpreted = &template.header.original.interpreted;
                charge(
                    work,
                    interpreted.len() + self.native_interpretations().len(),
                )?;
                if interpreted.len() != self.native_interpretations().len() {
                    return Err(invalid());
                }
                let empty = HashMap::new();
                let renaming = crate::types::TemplateIdentityRenaming {
                    variables: &empty,
                    nominals: &HashMap::new(),
                };
                for (original, actual) in interpreted.iter().zip(self.native_interpretations()) {
                    let expected_symbol = template
                        .original_acquire()
                        .registry
                        .native_symbol(OperationId::new(original.instance.effect(), 0))
                        .ok_or_else(invalid)?;
                    if original.instance.effect() != actual.effect().effect()
                        || !Arc::ptr_eq(expected_symbol, actual.symbol())
                        || original.instance.arguments().len() != actual.effect().arguments().len()
                    {
                        return Err(invalid());
                    }
                    for (argument, actual) in original
                        .instance
                        .arguments()
                        .iter()
                        .zip(actual.effect().arguments())
                    {
                        let mut expected = ArgumentsGuard(Vec::new());
                        charge(work, 1)?;
                        expected.0.try_reserve_exact(1).map_err(|_| resource())?;
                        expected.0.push(
                            crate::types::substitute_argument_for_template_with(
                                argument,
                                &copy.types,
                                &copy.rows,
                                &HashMap::new(),
                                &renaming,
                                |cells| work.charge(cells).map_err(|_| resource()),
                                resource,
                            )?
                            .map_err(|_| invalid())?,
                        );
                        if !crate::types::same_kinded_argument_with_budget(
                            &expected.0[0],
                            actual,
                            work,
                        )
                        .map_err(|_| resource())?
                        {
                            return Err(invalid());
                        }
                    }
                }
            }
            // Exact original IDs/projections were collected while deriving
            // this phase's sigma-dependent inventory. Reuse that invocation-
            // local representation rather than walking/projecting it again.
            let originals = &forests[phase].projections;
            if originals.len() != copy.nodes.len() {
                return Err(invalid());
            }
            let mut mappings = HashMap::new();
            mappings
                .try_reserve(copy.nodes.len() + 2)
                .map_err(|_| resource())?;
            copied_targets
                .try_reserve(copy.nodes.len())
                .map_err(|_| resource())?;
            for (source, target) in &copy.nodes {
                charge(work, 1)?;
                if !originals.contains_key(source) {
                    return Err(invalid());
                }
                node(original, *source)?;
                node(program, *target)?;
                if mappings.insert(*source, *target).is_some() || !copied_targets.insert(*target) {
                    return Err(invalid());
                }
            }
            let mut variables = HashMap::new();
            charge(work, copy.variables.len())?;
            variables
                .try_reserve(copy.variables.len())
                .map_err(|_| resource())?;
            for (source, target, _) in &copy.variables {
                variables.insert(*source, *target);
            }
            let nominals = HashMap::new();
            let pending = &copy.pending;
            let renaming = crate::types::TemplateIdentityRenaming {
                variables: &variables,
                nominals: &nominals,
            };
            let substitution = super::provider::ProviderTemplateSubstitution {
                types: &copy.types,
                rows: &copy.rows,
                pending,
            };
            if phase == 2
                && let Some(realized) = &realized
            {
                charge(
                    work,
                    realized
                        .pending()
                        .len()
                        .checked_add(realized.node_rows().len())
                        .ok_or_else(resource)?,
                )?;
                if copy.pending.len() != realized.pending().len()
                    || copy.node_rows.len() != realized.node_rows().len()
                {
                    return Err(invalid());
                }
                for (source, actual) in realized.pending() {
                    let expected = crate::types::substitute_row_for_template_with(
                        actual,
                        &HashMap::new(),
                        &HashMap::new(),
                        &HashMap::new(),
                        &renaming,
                        |cells| work.charge(cells).map_err(|_| resource()),
                        resource,
                    )?
                    .map_err(|_| invalid())?;
                    if !crate::types::same_effect_rows_with_budget(
                        copy.pending.get(source).ok_or_else(invalid)?,
                        &expected,
                        work,
                    )
                    .map_err(|_| resource())?
                    {
                        return Err(invalid());
                    }
                }
                for (source, actual) in realized.node_rows() {
                    let expected = crate::types::substitute_row_for_template_with(
                        actual,
                        &HashMap::new(),
                        &HashMap::new(),
                        &HashMap::new(),
                        &renaming,
                        |cells| work.charge(cells).map_err(|_| resource()),
                        resource,
                    )?
                    .map_err(|_| invalid())?;
                    if !crate::types::same_effect_rows_with_budget(
                        copy.node_rows.get(source).ok_or_else(invalid)?,
                        &expected,
                        work,
                    )
                    .map_err(|_| resource())?
                    {
                        return Err(invalid());
                    }
                }
            } else if !copy.pending.is_empty() || !copy.node_rows.is_empty() {
                return Err(invalid());
            }
            let fresh = copy.fresh();
            fresh.authenticate(work)?;
            let fresh_lookup = super::provider::specialization::SourceScopeFreshening::new(
                &fresh, &variables, work,
            )?;
            for (source, target) in &copy.nodes {
                let expected = originals.get(source).ok_or_else(invalid)?;
                let mut expected = super::provider::specialization::specialize_source_projection(
                    expected,
                    &mappings,
                    &fresh_lookup,
                    &substitution,
                    &renaming,
                    work,
                )?;
                if let Some(row) = copy.node_rows.get(source) {
                    expected.replace_effects(
                        crate::types::clone_effect_row_with_budget(row, work)
                            .map_err(|_| resource())?,
                    )?;
                }
                let actual = super::provider::projection::project_borrowed(
                    *target,
                    node(program, *target)?,
                    work,
                )?;
                if !expected.same_borrowed(&actual, work)? {
                    return Err(invalid());
                }
            }
            let (parameter, actual, actual_root) = match phase {
                0 => (
                    &template.acquire_entry.0,
                    &self.acquire.parameter,
                    self.acquire.body,
                ),
                1 => (
                    &template.finish_entry.0,
                    &self.finish.parameter,
                    self.finish.body,
                ),
                _ => (&template.handler_entry.0, &self.handler_state, id),
            };
            if phase < 2 && mappings.get(&root) != Some(&actual_root) {
                return Err(invalid());
            }
            mappings.insert(root, actual_root);
            let expected = super::provider::projection::project_binder(root, parameter, work)?;
            let expected = super::provider::specialization::specialize_source_projection(
                &expected,
                &mappings,
                &fresh_lookup,
                &substitution,
                &renaming,
                work,
            )?;
            let actual = super::provider::projection::project_binder(actual_root, actual, work)?;
            if !expected.same(&actual, work)? {
                return Err(invalid());
            }
            if phase == 2 {
                let expected = super::provider::projection::project_pattern(
                    root,
                    template.handler_pattern(),
                    work,
                )?;
                let expected = super::provider::specialization::specialize_source_projection(
                    &expected,
                    &mappings,
                    &fresh_lookup,
                    &substitution,
                    &renaming,
                    work,
                )?;
                if !expected.same(
                    &super::provider::projection::project_pattern(id, &self.handler_pattern, work)?,
                    work,
                )? {
                    return Err(invalid());
                }
                let original_handler = template.original_handler_node();
                charge(work, copy.handlers.len())?;
                if copy
                    .handlers
                    .iter()
                    .find(|(original, _)| *original == original_handler.id())
                    .map(|(_, actual)| *actual)
                    != Some(self.handler.id())
                    || self.handler.clauses().len() != original_handler.clauses().len()
                {
                    return Err(invalid());
                }
                let mut actuals = ArgumentsGuard(Vec::new());
                charge(work, original_handler.effect().arguments().len())?;
                actuals
                    .0
                    .try_reserve_exact(original_handler.effect().arguments().len())
                    .map_err(|_| resource())?;
                for argument in original_handler.effect().arguments() {
                    actuals.0.push(
                        crate::types::substitute_argument_for_template_with(
                            argument,
                            &copy.types,
                            &copy.rows,
                            pending,
                            &renaming,
                            |cells| work.charge(cells).map_err(|_| resource()),
                            resource,
                        )?
                        .map_err(|_| invalid())?,
                    );
                }
                let effect = crate::types::EffectInstance::new_kinded(
                    original_handler.effect().effect(),
                    actuals.into_boxed_slice(),
                );
                if crate::types::compare_effect_instances_with_budget(
                    &effect,
                    self.handler.effect(),
                    work,
                )
                .map_err(|_| resource())?
                    != std::cmp::Ordering::Equal
                {
                    return Err(invalid());
                }
                for (original, actual) in original_handler
                    .clauses()
                    .iter()
                    .zip(self.handler.clauses())
                {
                    let expected = super::provider::specialization::specialize_source_projection(
                        &super::provider::projection::project_clause(original, work)?,
                        &mappings,
                        &fresh_lookup,
                        &substitution,
                        &renaming,
                        work,
                    )?;
                    if !expected.same(
                        &super::provider::projection::project_clause(actual, work)?,
                        work,
                    )? {
                        return Err(invalid());
                    }
                }
            }
        }
        let sigma = &self.descriptor.copies[2];
        let empty = HashMap::new();
        let variables = HashMap::new();
        let nominals = HashMap::new();
        let rename = crate::types::TemplateIdentityRenaming {
            variables: &variables,
            nominals: &nominals,
        };
        let specialized = |ty: &Type, work: &mut TypeWorkBudget| {
            crate::types::substitute_type_for_template_with(
                ty,
                &sigma.types,
                &sigma.rows,
                &empty,
                &rename,
                |cells| work.charge(cells).map_err(|_| resource()),
                resource,
            )?
            .map_err(|_| invalid())
        };
        if self.lexical.module() != self.identity().module().ok_or_else(invalid)?
            || self.forwardings.len() != template.methods().len()
        {
            return Err(invalid());
        }
        let mut current = self.handler.body();
        let mut used = std::collections::HashSet::new();
        charge(work, 1 + self.forwardings.len())?;
        used.try_reserve(1 + self.forwardings.len())
            .map_err(|_| resource())?;
        used.insert(self.handle.id());
        for ((method, operation), forwarding) in template.methods().iter().zip(&self.forwardings) {
            if forwarding.method != *method || !used.insert(forwarding.binder) {
                return Err(invalid());
            }
            let Some(PureExprKind::Computation(PureComputation::Bind(binding))) =
                pure(node(program, current)?)
            else {
                return Err(invalid());
            };
            if binding.binder().id() != forwarding.binder {
                return Err(invalid());
            }
            let Some(PureExprKind::Value(PureValue::Function(function))) =
                pure(node(program, binding.initializer())?)
            else {
                return Err(invalid());
            };
            let EffectExprKind::Operation(EffectOperation::Request(request)) =
                &node(program, function.body())?.kind
            else {
                return Err(invalid());
            };
            let Some(PureExprKind::Variable(operand)) = pure(node(program, request.operand())?)
            else {
                return Err(invalid());
            };
            if request.operation() != *operation
                || operand.binder() != function.parameter().id()
                || crate::types::compare_effect_instances_with_budget(
                    request.effect(),
                    self.handler.effect(),
                    work,
                )
                .map_err(|_| resource())?
                    != std::cmp::Ordering::Equal
            {
                return Err(invalid());
            }
            let effect_declaration = template
                .original_handler()
                .registry
                .effect(operation.owner())
                .ok_or_else(invalid)?;
            let original = effect_declaration
                .operations
                .iter()
                .find(|candidate| candidate.id == *operation)
                .ok_or_else(invalid)?;
            if effect_declaration.parameters.len() != self.handler.effect().arguments().len() {
                return Err(invalid());
            }
            let mut operation_types = TypesGuard(HashMap::new());
            let mut operation_rows = HashMap::new();
            charge(work, effect_declaration.parameters.len().saturating_mul(2))?;
            operation_types
                .0
                .try_reserve(effect_declaration.parameters.len())
                .map_err(|_| resource())?;
            operation_rows
                .try_reserve(effect_declaration.parameters.len())
                .map_err(|_| resource())?;
            for (formal, actual) in effect_declaration
                .parameters
                .iter()
                .zip(self.handler.effect().arguments())
            {
                match actual {
                    KindedArgument::TypeArg(ty) => operation_types.insert(
                        formal.id,
                        crate::types::clone_type_with_budget(ty, work).map_err(|_| resource())?,
                    ),
                    KindedArgument::RowArg(row) => {
                        operation_rows.insert(
                            formal.id,
                            crate::types::clone_effect_row_with_budget(row, work)
                                .map_err(|_| resource())?,
                        );
                    }
                }
            }
            let operation_type = crate::types::IterativeTypeOwner::new(
                crate::types::substitute_type_for_template_with(
                    &original.annotation.ty,
                    &operation_types.0,
                    &operation_rows,
                    &empty,
                    &rename,
                    |cells| work.charge(cells).map_err(|_| resource()),
                    resource,
                )?
                .map_err(|_| invalid())?,
            );
            let operation_type = operation_type.function_view().ok_or_else(invalid)?;
            if !same(function.parameter().ty(), operation_type.domain(), work)? {
                return Err(invalid());
            }
            let expected = crate::types::IterativeTypeOwner::new(Type::function_computation(
                crate::types::clone_type_with_budget(operation_type.domain(), work)
                    .map_err(|_| resource())?,
                crate::types::ComputationType::new(
                    crate::types::clone_type_with_budget(operation_type.value(), work)
                        .map_err(|_| resource())?,
                    crate::types::EffectRow::singleton(
                        crate::types::clone_effect_instance_with_budget(
                            self.handler.effect(),
                            work,
                        )
                        .map_err(|_| resource())?,
                    ),
                ),
            ));
            if !same(binding.binder().ty(), &expected, work)?
                || !same(&node(program, binding.initializer())?.ty, &expected, work)?
            {
                return Err(invalid());
            }
            let owner = program
                .method_evidence
                .lexical_owner(self.lexical, *method)
                .ok_or_else(invalid)?;
            if owner.binder != forwarding.binder
                || owner.application.interface() != template.header.original.provider.interface.id
                || owner.application.arguments().len()
                    != template.header.original.provider.arguments.len()
            {
                return Err(invalid());
            }
            for (original, actual) in template
                .header
                .original
                .provider
                .arguments
                .iter()
                .zip(owner.application.arguments())
            {
                let expected = crate::types::IterativeArgumentOwner::new(
                    crate::types::substitute_argument_for_template_with(
                        &original.ty,
                        &sigma.types,
                        &sigma.rows,
                        &empty,
                        &rename,
                        |cells| work.charge(cells).map_err(|_| resource()),
                        resource,
                    )?
                    .map_err(|_| invalid())?,
                );
                if !crate::types::same_kinded_argument_with_budget(&expected, actual, work)
                    .map_err(|_| resource())?
                {
                    return Err(invalid());
                }
            }
            let mut definitions = 0usize;
            charge(work, program.nodes.len())?;
            for stored in &program.nodes {
                if let Some(PureExprKind::Computation(PureComputation::Bind(candidate))) =
                    pure(stored)
                    && candidate.binder().id() == forwarding.binder
                {
                    definitions += 1;
                }
            }
            if definitions != 1 {
                return Err(invalid());
            }
            current = binding.body();
        }
        let input = crate::types::IterativeTypeOwner::new(specialized(
            &template.header.original.input.ty,
            work,
        )?);
        let data = crate::types::IterativeTypeOwner::new(specialized(
            &template.header.original.data.ty,
            work,
        )?);
        // A defining generic D may be independent until its complete Type/Row
        // application is known. Copy correspondence cannot authorize storing a
        // native State introduced by that otherwise kind-correct application.
        admit_private_data(&data, &program.registry, work)?;
        let acquisition = crate::types::IterativeTypeOwner::new(specialized(
            &template.header.original.acquisition.ty,
            work,
        )?);
        let completion = crate::types::IterativeTypeOwner::new(specialized(
            &template.header.original.completion.ty,
            work,
        )?);
        let result = crate::types::IterativeTypeOwner::new(specialized(
            &template.header.original.result.ty,
            work,
        )?);
        if !same(&node(program, self.initializer)?.ty, &input, work)?
            || !same(&node(program, self.acquire.body)?.ty, &acquisition, work)?
            || !same(&node(program, self.finish.body)?.ty, &completion, work)?
            || !same(&node(program, id)?.ty, &result, work)?
            || !same(
                self.handler_output.value(),
                &node(program, self.handler.body())?.ty,
                work,
            )?
        {
            return Err(invalid());
        }
        let access = crate::types::IterativeTypeOwner::new(
            template.header.access_type(self.arguments(), work)?,
        );
        if !same(self.handle.ty(), &access, work)? || self.handler.has_hook_contracts() {
            return Err(invalid());
        }
        // Original forest projections imply the phase flow proof for each exact
        // copied instance. Initializer and client answer cannot expose the fresh
        // identity; ordinary type-scope validation checks that boundary.
        // The ordinary handler checker independently reconstructs its least
        // residual row, and the scope checker removes only the listed native
        // instances. Ordinary outward requests retain their capture demands.
        Ok(())
    }
}

/// Authenticate the complete name/type/row relation independently of method
/// and operation declaration order before generating lexical forwarding.
fn check_provider_association(
    checked_header: &CheckedSourceResourceHeader,
    program: &UnvalidatedEffectProgram,
    work: &mut TypeWorkBudget,
) -> Result<Box<[(crate::interface::MethodId, crate::types::OperationId)]>, ValidationError> {
    use crate::resolved::OwnerId;
    let header = &checked_header.original;
    let interface = header.provider.interface.id;
    let signature = program
        .registry
        .owner_signature(OwnerId::Interface(interface))
        .ok_or_else(invalid)?;
    if signature.parameters.len() != header.provider.arguments.len() {
        return Err(invalid());
    }
    let effect = program
        .registry
        .effect(header.provided.instance.effect())
        .ok_or_else(invalid)?;
    if effect.operations.is_empty()
        || effect.parameters.len() != header.provided.instance.arguments().len()
    {
        return Err(invalid());
    }
    let catalog = program.method_evidence.methods();
    charge(work, catalog.len())?;
    let method_count = catalog
        .iter()
        .filter(|method| method.id.interface() == interface)
        .count();
    if method_count != effect.operations.len() {
        return Err(invalid());
    }
    let mut types = TypesGuard(HashMap::new());
    let mut rows = HashMap::new();
    charge(work, signature.parameters.len() + effect.parameters.len())?;
    types
        .0
        .try_reserve(signature.parameters.len() + effect.parameters.len())
        .map_err(|_| resource())?;
    rows.try_reserve(signature.parameters.len() + effect.parameters.len())
        .map_err(|_| resource())?;
    // Borrowed source payloads are cloned through the shared iterative copier.
    for (id, argument) in signature.parameters.iter().zip(&header.provider.arguments) {
        let formal = program.registry.type_variable(*id).ok_or_else(invalid)?;
        match (&formal.kind, &argument.ty) {
            (Kind::Type, KindedArgument::TypeArg(ty)) => {
                types.insert(
                    *id,
                    crate::types::clone_type_with_budget(ty, work).map_err(|_| resource())?,
                );
            }
            (Kind::EffectRow, KindedArgument::RowArg(row)) => {
                rows.insert(
                    *id,
                    crate::types::clone_effect_row_with_budget(row, work)
                        .map_err(|_| resource())?,
                );
            }
            _ => return Err(invalid()),
        }
    }
    for (formal, argument) in effect
        .parameters
        .iter()
        .zip(header.provided.instance.arguments())
    {
        match (&formal.kind, argument) {
            (Kind::Type, KindedArgument::TypeArg(ty)) => {
                types.insert(
                    formal.id,
                    crate::types::clone_type_with_budget(ty, work).map_err(|_| resource())?,
                );
            }
            (Kind::EffectRow, KindedArgument::RowArg(row)) => {
                rows.insert(
                    formal.id,
                    crate::types::clone_effect_row_with_budget(row, work)
                        .map_err(|_| resource())?,
                );
            }
            _ => return Err(invalid()),
        }
    }
    let empty = HashMap::new();
    let variables = HashMap::new();
    let nominals = HashMap::new();
    let rename = crate::types::TemplateIdentityRenaming {
        variables: &variables,
        nominals: &nominals,
    };
    let specialized = |ty: &Type, work: &mut TypeWorkBudget| {
        crate::types::substitute_type_for_template_with(
            ty,
            &types.0,
            &rows,
            &empty,
            &rename,
            |cells| work.charge(cells).map_err(|_| resource()),
            resource,
        )?
        .map_err(|_| invalid())
    };
    let mut associations = Vec::new();
    charge(work, method_count)?;
    associations
        .try_reserve_exact(method_count)
        .map_err(|_| resource())?;
    for method in catalog
        .iter()
        .filter(|method| method.id.interface() == interface)
    {
        if !method.parameters.is_empty()
            || method.interface_parameters.as_ref() != signature.parameters.as_ref()
        {
            return Err(invalid());
        }
        let mut selected = None;
        for operation in &effect.operations {
            charge(work, 1 + method.spelling.len() + operation.spelling.len())?;
            if method.spelling.as_ref() == operation.spelling
                && selected.replace(operation).is_some()
            {
                return Err(invalid());
            }
        }
        let operation = selected.ok_or_else(invalid)?;
        charge(work, associations.len())?;
        if associations.iter().any(|(_, id)| *id == operation.id) {
            return Err(invalid());
        }
        let method_type =
            crate::types::IterativeTypeOwner::new(specialized(&method.value_type, work)?);
        let operation_type =
            crate::types::IterativeTypeOwner::new(specialized(&operation.annotation.ty, work)?);
        let method_function = method_type.function_view().ok_or_else(invalid)?;
        let operation_function = operation_type.function_view().ok_or_else(invalid)?;
        if operation_function.effects().is_some()
            || !same(method_function.domain(), operation_function.domain(), work)?
            || !same(method_function.value(), operation_function.value(), work)?
        {
            return Err(invalid());
        }
        let row = method_function.effects().ok_or_else(invalid)?;
        let expected = crate::types::EffectRow::singleton(
            crate::types::clone_effect_instance_with_budget(&header.provided.instance, work)
                .map_err(|_| resource())?,
        );
        if !crate::types::same_effect_rows_with_budget(row, &expected, work)
            .map_err(|_| resource())?
        {
            return Err(invalid());
        }
        associations.push((method.id, operation.id));
    }
    Ok(associations.into_boxed_slice())
}

fn retain_set<T: Copy + Eq + std::hash::Hash>(
    set: &mut std::collections::HashSet<T>,
    values: impl Iterator<Item = T>,
    work: &mut TypeWorkBudget,
) -> Result<(), ValidationError> {
    for value in values {
        charge(work, 1)?;
        set.try_reserve(1).map_err(|_| resource())?;
        set.insert(value);
    }
    Ok(())
}
fn exact_fresh_pairs<T: Copy + Eq + std::hash::Hash>(
    originals: &[T],
    pairs: &[(T, T)],
    all_originals: &std::collections::HashSet<T>,
    targets: &mut std::collections::HashSet<T>,
    work: &mut TypeWorkBudget,
) -> Result<(), ValidationError> {
    charge(work, originals.len() + pairs.len())?;
    if originals.len() != pairs.len() {
        return Err(invalid());
    }
    let mut remaining = std::collections::HashSet::new();
    remaining
        .try_reserve(originals.len())
        .map_err(|_| resource())?;
    remaining.extend(originals.iter().copied());
    targets.try_reserve(pairs.len()).map_err(|_| resource())?;
    for (source, target) in pairs {
        if !remaining.remove(source) || all_originals.contains(target) || !targets.insert(*target) {
            return Err(invalid());
        }
    }
    Ok(())
}
fn source_inventory<'a>(
    template: &'a CheckedSourceResourceTemplate,
    phase: usize,
    copy: &SourceResourceCopy,
    work: &mut TypeWorkBudget,
) -> Result<super::provider::specialization::SourceResourceOriginalForest<'a>, ValidationError> {
    let (program, parameter, root) = match phase {
        0 => (
            &template.acquire,
            &template.acquire_entry.0,
            template.acquire_entry.1,
        ),
        1 => (
            &template.finish,
            &template.finish_entry.0,
            template.finish_entry.1,
        ),
        _ => (
            &template.handler,
            &template.handler_entry.0,
            template.handler_entry.1,
        ),
    };
    let mut roots = Vec::new();
    if phase < 2 {
        push(&mut roots, root, work)?;
    } else {
        for clause in template.original_handler_node().clauses() {
            push(&mut roots, clause.body(), work)?;
        }
    }
    let sigma = super::provider::ProviderTemplateSubstitution {
        types: &copy.types,
        rows: &copy.rows,
        pending: &copy.pending,
    };
    let handler_patterns = [template.handler_pattern()];
    super::provider::specialization::source_resource_original_forest(
        program,
        &roots,
        &[parameter],
        if phase == 2 { &handler_patterns } else { &[] },
        if phase == 2 {
            Some(template.original_handler_node())
        } else {
            None
        },
        &sigma,
        work,
    )
}

#[cfg(test)]
mod tests {
    use crate::{
        core::{EffectExprKind, EffectOperation, NodeId, ValidationReason},
        types::{KindedArgument, Type, TypeWorkBudget},
    };
    use std::sync::Arc;
    use std::{
        fs,
        path::PathBuf,
        sync::atomic::{AtomicU64, Ordering},
    };

    struct Fixture(PathBuf);
    impl Fixture {
        fn new() -> Self {
            static IDS: AtomicU64 = AtomicU64::new(0);
            let directory = std::env::temp_dir().join(format!(
                "ash-source-core-{}-{}",
                std::process::id(),
                IDS.fetch_add(1, Ordering::Relaxed)
            ));
            fs::create_dir(&directory).unwrap();
            fs::write(
                directory.join("owner.ash"),
                include_str!("../../tests/fixtures/source-owner/owner.ash"),
            )
            .unwrap();
            fs::write(
                directory.join("entry.ash"),
                include_str!("../../tests/fixtures/source-owner/entry.ash"),
            )
            .unwrap();
            Self(directory)
        }
        fn compile(&self) -> crate::driver::CompiledProgram {
            crate::driver::compile_path(crate::driver::RunConfiguration {
                entry: self.0.join("entry.ash"),
                roots: crate::module::ModuleRoots::empty(),
            })
            .expect("connected source scope fixture")
        }
    }
    impl Drop for Fixture {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.0);
        }
    }

    #[test]
    fn lexical_window_declarations_match_exact_original_phase_inventory_and_budget() {
        let fixture = Fixture::new();
        fs::write(
            fixture.0.join("owner.ash"),
            include_str!("../../libraries/sqlite.ash"),
        )
        .unwrap();
        fs::write(fixture.0.join("entry.ash"), "import owner as Sqlite\nmain : Unit -> Sqlite.Scope<Sqlite.OpenError, Sqlite.CloseError, Bool> ! {Sqlite.Initialize}\nmain () = resource Sqlite.Connection<C> connection = Sqlite.InMemory {\n    true\n}\n").unwrap();
        let compiled = fixture.compile();
        let (program, _) = compiled.effect_build_input().unwrap();
        let original = program
            .nodes()
            .iter()
            .find_map(|node| match &node.kind {
                EffectExprKind::Operation(EffectOperation::SourceResourceScope(scope)) => {
                    Some(scope.original())
                }
                _ => None,
            })
            .unwrap();
        let declarations = &original.header().original.windows;
        assert_eq!(declarations.len(), 1);
        assert_eq!(
            declarations[0].phase,
            crate::resolved::SourceWindowPhase::Handler
        );
        let check = |declarations: &[_], work: &mut TypeWorkBudget| {
            super::check_original_window_declarations(
                declarations,
                original.original_acquire(),
                original.original_finish(),
                original.original_handler(),
                work,
            )
        };
        let mut measured = TypeWorkBudget::default();
        check(declarations, &mut measured).unwrap();
        let cost = measured.used();
        for prefix in [0, 17] {
            for _ in 0..2 {
                let mut exact = TypeWorkBudget::with_limit(prefix + cost);
                exact.charge(prefix).unwrap();
                check(declarations, &mut exact).unwrap();
                assert_eq!(exact.used(), prefix + cost);
                let mut short = TypeWorkBudget::with_limit(prefix + cost - 1);
                short.charge(prefix).unwrap();
                assert_eq!(
                    check(declarations, &mut short).unwrap_err().reason(),
                    ValidationReason::Resource
                );
            }
            check(declarations, &mut TypeWorkBudget::default()).unwrap();
        }
        let mut phase = declarations.to_vec();
        phase[0].phase = crate::resolved::SourceWindowPhase::Acquire;
        let mut family = declarations.to_vec();
        family[0].family = original.header().original.family;
        let mut identity = declarations.to_vec();
        identity[0].identity = original.header().original.answer.id;
        let mut span = declarations.to_vec();
        span[0].span = span[0].identity_span;
        let donor = original
            .original_registry()
            .source_resource_facts()
            .find(|header| header.id != original.header().original.id && !header.windows.is_empty())
            .unwrap()
            .windows[0];
        for invalid in [
            Vec::new(),
            vec![declarations[0], declarations[0]],
            phase,
            family,
            identity,
            span,
            vec![donor],
        ] {
            assert_eq!(
                check(&invalid, &mut TypeWorkBudget::default())
                    .unwrap_err()
                    .reason(),
                ValidationReason::Registry
            );
        }
    }

    #[test]
    fn source_control_copy_window_recipe_keeps_state_and_exact_direct_claim() {
        let fixture = Fixture::new();
        let library = include_str!("../../libraries/sqlite.ash");
        let direct_clause =
            "error_code access => resume (column_int_result (perform ErrorCode<C>.call state))";
        let direct_prefix = "let code = column_int_result (perform ErrorCode<C>.call state)";
        let window_prefix = "copy_window DiagnosticView<W, C> from state {";
        for exact in [direct_clause, direct_prefix, window_prefix] {
            assert_eq!(library.matches(exact).count(), 1);
        }
        // Make the state prefix the only ErrorCode request in this handler.
        // The actual body still requests the separate window-local ErrorMessage.
        let library = library
            .replace(direct_clause, "error_code access => resume (Ok 14)")
            .replace(direct_prefix, "let code = Ok 14")
            .replace(window_prefix, "copy_window DiagnosticView<W, C> from ({\n                        let _ = perform ErrorCode<C>.call state\n                        state\n                    }) {");
        fs::write(fixture.0.join("owner.ash"), library).unwrap();
        fs::write(fixture.0.join("entry.ash"), "import owner as Sqlite\nmain : Unit -> Sqlite.Scope<Sqlite.OpenError, Sqlite.CloseError, Bool> ! {Sqlite.Initialize}\nmain () = resource Sqlite.Connection<C> connection = Sqlite.InMemory {\n    true\n}\n").unwrap();
        let compiled = fixture.compile();
        let (checked, _) = compiled.effect_build_input().unwrap();
        let original = checked
            .nodes()
            .iter()
            .find_map(|node| match &node.kind {
                EffectExprKind::Operation(EffectOperation::SourceResourceScope(scope)) => {
                    Some(scope.original())
                }
                _ => None,
            })
            .unwrap();
        let program = original.original_handler();
        let window = program
            .nodes
            .iter()
            .find_map(|stored| match &stored.kind {
                EffectExprKind::Operation(EffectOperation::SourceCopyWindow(window)) => {
                    Some(window)
                }
                _ => None,
            })
            .unwrap();
        let state = &program.nodes[window.state().index().unwrap()].effects;
        let body = &program.nodes[window.body().index().unwrap()].effects;
        let inputs = original.original_handler_inputs().unwrap();
        assert_eq!(state.known().len(), 1);
        assert!(state.tail().is_none());
        assert_eq!(body.known().len(), 1);
        assert!(body.tail().is_none());
        assert_ne!(state.known()[0].effect(), body.known()[0].effect());
        let mut work = TypeWorkBudget::default();
        assert!(
            crate::types::same_effect_rows_with_budget(state, &inputs.direct, &mut work).unwrap()
        );
        let graph = original
            .reconstructed_handler_graph_for_test(&mut work)
            .unwrap();
        let view = graph.handler_graph();
        let recipe =
            super::super::provider::HandlerRowRecipeDraft::reconstruct(&view, &mut work).unwrap();
        let (direct, pending) = recipe
            .realize_direct(
                &std::collections::HashMap::new(),
                &std::collections::HashMap::new(),
                &std::collections::HashMap::new(),
                &mut work,
            )
            .unwrap();
        assert_eq!(pending.len(), inputs.pending.equations.len());
        assert!(crate::types::same_effect_rows_with_budget(&direct, state, &mut work).unwrap());
        let leaked = state.union_with_budget(body, &mut work).unwrap().unwrap();
        for wrong in [crate::types::EffectRow::empty(), leaked] {
            let mut changed = view;
            changed.draft.direct_demands = &wrong;
            let error = super::super::provider::HandlerRowRecipeDraft::reconstruct(
                &changed,
                &mut TypeWorkBudget::default(),
            )
            .unwrap_err();
            assert_eq!(error.reason(), ValidationReason::ResourceEscape);
            assert_eq!(error.node(), Some(program.root));
        }
    }

    #[test]
    fn source_control_handler_call_proof_preserves_prior_value_flow() {
        let fixture = Fixture::new();
        fs::write(
            fixture.0.join("owner.ash"),
            include_str!("../../tests/fixtures/source-owner/replaced_payload_owner.ash"),
        )
        .unwrap();
        fs::write(fixture.0.join("entry.ash"), "import owner as Owner\ninitial : Unit -> Int\ninitial () = 7\nmain : Unit -> Owner.Scope<Unit, Unit -> Int, Unit>\nmain () = resource Owner.Probe<{}, Fresh, {}> owner = initial {\n    let replacement : Unit -> Int = fn(ignored) {\n        let retained = 1\n        42\n    }\n    Owner.store (owner, replacement)\n}\n").unwrap();
        let compiled = fixture.compile();
        let (program, _) = compiled.effect_build_input().unwrap();
        let original = program
            .nodes()
            .iter()
            .find_map(|node| match &node.kind {
                EffectExprKind::Operation(EffectOperation::SourceResourceScope(scope)) => {
                    Some(scope.original())
                }
                _ => None,
            })
            .unwrap();
        let (clause, binder) = original
            .original_handler_node()
            .clauses()
            .iter()
            .find_map(|clause| {
                clause
                    .pattern()
                    .binder_iter()
                    .find(|binder| binder.ty().function_view().is_some())
                    .map(|binder| (clause, binder))
            })
            .unwrap();
        let mut work = TypeWorkBudget::default();
        let mut facts = super::facts(&mut work).unwrap();
        let current = facts.add(super::FlowFact::Current, &mut work).unwrap();
        for (prior, expected) in [(None, false), (Some(current), false), (Some(0), true)] {
            let value = facts
                .add(
                    super::FlowFact::HandlerInputCallable {
                        original: &original.header().original,
                        operation: clause.operation(),
                        pattern: clause.pattern(),
                        binder,
                        value_type: binder.ty(),
                        value: prior,
                    },
                    &mut work,
                )
                .unwrap();
            assert_eq!(facts.independent(value, &mut work).unwrap(), expected);
            assert_eq!(
                facts
                    .borrowed(value, false, original.header(), &mut work)
                    .unwrap(),
                expected,
            );
        }
    }

    #[test]
    fn source_control_core_retains_exact_continuation_rows_and_budget() {
        let fixture = Fixture::new();
        fs::write(fixture.0.join("entry.ash"),
            "import owner as Owner\neffect Pause {\n    pause : Unit -> Unit\n}\nmain : Unit -> Owner.Scope<Unit, Unit, Int>\nmain () = handle (resource Owner.Probe<{}, R, {}> owner = 42 {\n    let paused = perform Pause.pause ()\n    Owner.read owner\n}) with Pause {\n    pause ignored => resume ()\n}\n").unwrap();
        let compiled = fixture.compile();
        let (checked, provenance) = compiled.effect_build_input().unwrap();
        let sources = provenance
            .iter()
            .map(|(_, source)| source.as_ref())
            .collect::<Vec<_>>();
        let modules = provenance
            .iter()
            .map(|(module, source)| (*module, source.id()))
            .collect::<Vec<_>>();
        let validate = |program, work: &mut TypeWorkBudget| {
            super::super::validate::validate_effect_modules_with_work(
                program, &sources, &modules, work,
            )
        };
        let fresh = || super::super::transform::identity_effect_traversal(checked).unwrap();
        let mut normal = TypeWorkBudget::with_limit(
            crate::compiler_work::CompilationPhase::IndependentCore.budget(),
        );
        validate(fresh(), &mut normal).unwrap();
        let cost = normal.used();
        for prefix in [0, 5] {
            let mut short = TypeWorkBudget::with_limit(prefix + cost - 1);
            short.charge(prefix).unwrap();
            assert_eq!(
                validate(fresh(), &mut short).unwrap_err().reason(),
                ValidationReason::Resource
            );
            for _ in 0..2 {
                let mut exact = TypeWorkBudget::with_limit(prefix + cost);
                exact.charge(prefix).unwrap();
                validate(fresh(), &mut exact).unwrap();
                assert_eq!(exact.used(), prefix + cost);
            }
        }
        // Every mutation is kind-correct. The existing body, forest, original
        // header and template remain intact, so each altered claim must fail.
        for mutation in 0..3 {
            let mut forged = fresh();
            let scope_index = forged
                .nodes
                .iter()
                .position(|node| {
                    matches!(
                        &node.kind,
                        EffectExprKind::Operation(EffectOperation::SourceResourceScope(_))
                    )
                })
                .unwrap();
            let scope_id = NodeId::new(forged.arena, scope_index as u32);
            let EffectExprKind::Operation(EffectOperation::SourceResourceScope(scope)) =
                &mut forged.nodes[scope_index].kind
            else {
                unreachable!()
            };
            let continuation = scope.original().handler_continuation();
            assert_eq!(scope.handler_output.effects().known().len(), 1);
            assert!(scope.handler_output.effects().tail().is_none());
            match mutation {
                0 => {
                    let descriptor = Arc::get_mut(&mut scope.descriptor).unwrap();
                    *descriptor.copies[2].rows.get_mut(&continuation).unwrap() =
                        crate::types::EffectRow::empty();
                }
                1 => scope.handler_output.effects = crate::types::EffectRow::empty(),
                _ => Arc::get_mut(&mut scope.descriptor)
                    .unwrap()
                    .interpretations
                    .swap(0, 1),
            }
            let error = validate(forged, &mut TypeWorkBudget::default()).unwrap_err();
            if mutation == 1 {
                // The intact client residual now exposes output erasure at the
                // ordinary handler check before original-copy correspondence.
                assert_eq!(error.reason(), ValidationReason::EffectRow);
                assert_eq!(error.cause_name(), Some("handler-body-effects"));
                assert_eq!(error.node(), Some(scope_id));
            } else {
                assert_eq!(
                    error.reason(),
                    ValidationReason::Registry,
                    "mutation {mutation}: {error:?}"
                );
            }
        }
        println!(
            "source control independent Core work={cost}; exact/one-short/prefix/two fresh retries and three original-claim refusals"
        );
    }

    #[test]
    fn source_control_complete_client_residual_is_distinct_from_direct_demand() {
        use crate::types::{EffectRow, clone_effect_row_with_budget, same_effect_rows_with_budget};
        for overlap in [false, true] {
            let fixture = Fixture::new();
            let helper = include_str!("../../tests/fixtures/source-owner/control_capture.ash");
            let helper = if overlap {
                helper.replace("    let first = probe (connection, with_owner)", "    let overlap = perform H.op ()\n    let first = probe (connection, with_owner)")
            } else {
                helper.to_owned()
            };
            fs::write(fixture.0.join("helpers.ash"), helper).unwrap();
            fs::write(
                fixture.0.join("entry.ash"),
                include_str!("../../tests/fixtures/source-owner/control_capture_entry.ash"),
            )
            .unwrap();
            let compiled = fixture.compile();
            let (checked, provenance) = compiled.effect_build_input().unwrap();
            let sources = provenance
                .iter()
                .map(|(_, source)| source.as_ref())
                .collect::<Vec<_>>();
            let modules = provenance
                .iter()
                .map(|(module, source)| (*module, source.id()))
                .collect::<Vec<_>>();
            let fresh = || super::super::transform::identity_effect_traversal(checked).unwrap();
            let validate = |program| {
                super::super::validate::validate_effect_modules_family(program, &sources, &modules)
            };
            let normal = fresh();
            let index = normal.nodes.iter().position(|stored| matches!(&stored.kind,
                EffectExprKind::Operation(EffectOperation::SourceResourceScope(scope)) if scope.handler_row_claim().is_some()
            )).unwrap();
            let EffectExprKind::Operation(EffectOperation::SourceResourceScope(scope)) =
                &normal.nodes[index].kind
            else {
                unreachable!()
            };
            let claims = scope.handler_row_claim().unwrap();
            let [direct, epsilon, output, residual] = claims.source_rows();
            assert_eq!(direct.known().len(), 1);
            assert!(direct.tail().is_none());
            assert_eq!(epsilon.is_empty(), !overlap);
            let mut work = TypeWorkBudget::default();
            assert!(same_effect_rows_with_budget(epsilon, residual, &mut work).unwrap());
            assert!(same_effect_rows_with_budget(direct, output, &mut work).unwrap());
            if overlap {
                assert!(
                    same_effect_rows_with_budget(direct, epsilon, &mut work).unwrap(),
                    "overlapping client H remains in epsilon"
                );
            } else {
                claims.assert_distinct_actual_captures_for_test(direct.known()[0].effect());
            }
            super::super::validate::assert_source_wrapper_coordinate_for_test(
                scope.original(),
                &sources,
                &modules,
            );
            let continuation = scope.original().handler_continuation();
            assert!(
                same_effect_rows_with_budget(
                    &scope.descriptor.copies[2].rows[&continuation],
                    epsilon,
                    &mut work
                )
                .unwrap()
            );
            let wrong_row = if overlap {
                EffectRow::empty()
            } else {
                clone_effect_row_with_budget(direct, &mut work).unwrap()
            };
            let donor = normal
                .nodes
                .iter()
                .find_map(|stored| match &stored.kind {
                    EffectExprKind::Operation(EffectOperation::SourceResourceScope(other))
                        if !Arc::ptr_eq(scope.original(), other.original()) =>
                    {
                        other
                            .header()
                            .original
                            .parameters
                            .iter()
                            .find(|parameter| parameter.kind == crate::types::Kind::EffectRow)
                            .map(|parameter| parameter.id)
                    }
                    _ => None,
                })
                .unwrap();
            validate(normal).unwrap();
            for mutation in 0..3 {
                let mut forged = fresh();
                let id = NodeId::new(forged.arena, index as u32);
                let EffectExprKind::Operation(EffectOperation::SourceResourceScope(scope)) =
                    &mut forged.nodes[index].kind
                else {
                    unreachable!()
                };
                let descriptor = Arc::get_mut(&mut scope.descriptor).unwrap();
                match mutation {
                    0 => {
                        *descriptor.copies[2].rows.get_mut(&continuation).unwrap() =
                            clone_effect_row_with_budget(&wrong_row, &mut TypeWorkBudget::default())
                                .unwrap()
                    }
                    1 => {
                        let row = descriptor.copies[2].rows.remove(&continuation).unwrap();
                        assert!(descriptor.copies[2].rows.insert(donor, row).is_none());
                    }
                    _ => {
                        let row = clone_effect_row_with_budget(
                            &descriptor.copies[2].rows[&continuation],
                            &mut TypeWorkBudget::default(),
                        )
                        .unwrap();
                        assert!(
                            descriptor.copies[0]
                                .rows
                                .insert(continuation, row)
                                .is_none()
                        );
                    }
                }
                let EffectExprKind::Operation(EffectOperation::SourceResourceScope(scope)) =
                    &forged.nodes[index].kind
                else {
                    unreachable!()
                };
                let direct_error = scope
                    .authenticate(id, &forged, &mut TypeWorkBudget::default())
                    .unwrap_err();
                assert_eq!(
                    direct_error.reason(),
                    ValidationReason::Registry,
                    "overlap={overlap} mutation={mutation}: {direct_error:?}"
                );
                let whole_error = validate(forged).unwrap_err();
                assert_eq!(
                    whole_error.reason(),
                    ValidationReason::Registry,
                    "overlap={overlap} mutation={mutation}: {whole_error:?}"
                );
            }
        }
    }

    #[test]
    fn ordinary_header_payloads_pay_for_all_passive_owner_candidates_and_retry_exactly() {
        let original = include_str!("../../tests/fixtures/source-owner/owner.ash");
        let library = &original[original.find("pub foreign library Memory").unwrap()
            ..original.find("pub type Acquire").unwrap()];
        let mut costs = Vec::new();
        for extra_owners in [0, 7] {
            let fixture = Fixture::new();
            let mut owner = original
                .replace(
                    "pub type Acquire",
                    "pub type Payload = Payload\npub type Acquire",
                )
                .replace("input Int", "input (Payload, Payload)")
                .replace("data Int", "data (Payload, Payload)")
                .replace(
                    "Acquire<State<R>, Int, Unit>",
                    "Acquire<State<R>, (Payload, Payload), Unit>",
                )
                .replace(".call size {", ".call 42 {")
                .replace("match size == 9 {", "match false {")
                .replace("read access => resume data", "read access => resume 42");
            for index in 0..extra_owners {
                // These contracts are independently admitted but unused by Probe.
                // Native operation selection must not stand in for the owner table.
                let passive = library
                    .replace("Memory", &format!("Passive{index}"))
                    .replace("Size", &format!("PassiveSize{index}"))
                    .replace("Address", &format!("PassiveAddress{index}"))
                    .replace("State", &format!("PassiveState{index}"))
                    .replace("Allocate", &format!("PassiveAllocate{index}"))
                    .replace("Free", &format!("PassiveFree{index}"));
                owner.push_str(&passive);
            }
            fs::write(fixture.0.join("owner.ash"), owner).unwrap();
            fs::write(
                fixture.0.join("entry.ash"),
                "import owner as Owner\nmain : Unit -> Int\nmain () = 42\n",
            )
            .unwrap();
            let compiled = fixture.compile();
            // The associated interface's exact effectful value types select
            // the existing Effect dialect even when no resource is executed.
            let (checked, _) = compiled
                .effect_build_input()
                .expect("unused passive headers remain independently admitted");
            let registry = checked.registry();
            assert_eq!(registry.source_owner_candidate_count(), extra_owners + 1);
            let header = registry
                .source_resource_facts()
                .find(|fact| fact.spelling == "Probe")
                .expect("the original checked source header is retained");
            assert_eq!(header.interpreted.len(), 2);
            for payload in [&header.input.ty, &header.data.ty] {
                let Type::Tuple(fields) = payload else {
                    panic!("the independent payload retains its ordinary nominal tuple")
                };
                assert_eq!(fields.len(), 2);
                assert!(fields.iter().all(|field| matches!(
                    field,
                    Type::Nominal(nominal) if !registry.source_foreign_nominal(*nominal)
                )));
            }
            let mut measured = TypeWorkBudget::unbounded();
            super::CheckedSourceResourceHeader::admit(header, registry, &mut measured)
                .expect("independent nominal input and private data are admissible");
            let cost = measured.used();
            if let Some((_, smaller_cost)) = costs.first() {
                let mut smaller_table_budget = TypeWorkBudget::with_limit(*smaller_cost);
                let failure = super::CheckedSourceResourceHeader::admit(
                    header,
                    registry,
                    &mut smaller_table_budget,
                )
                .expect_err("work sufficient for one owner cannot admit the wider passive table");
                assert_eq!(failure.reason(), ValidationReason::Resource);
            }
            costs.push((registry.source_owner_candidate_count(), cost));
            for prefix in [0, 19] {
                let mut short = TypeWorkBudget::with_limit(prefix + cost - 1);
                short.charge(prefix).unwrap();
                let failure =
                    super::CheckedSourceResourceHeader::admit(header, registry, &mut short)
                        .expect_err("one-short header work refuses without publishing authority");
                assert_eq!(failure.reason(), ValidationReason::Resource);
                for _ in 0..2 {
                    let mut exact = TypeWorkBudget::with_limit(prefix + cost);
                    exact.charge(prefix).unwrap();
                    let admitted =
                        super::CheckedSourceResourceHeader::admit(header, registry, &mut exact)
                            .expect("the same immutable header retries at its exact work boundary");
                    assert!(Arc::ptr_eq(&admitted.original, header));
                    assert_eq!(exact.used(), prefix + cost);
                }
            }
        }
        let [(small_count, small_cost), (large_count, large_cost)] = costs.as_slice() else {
            panic!("both passive owner table sizes were measured")
        };
        assert!(
            *large_cost >= *small_cost + 2 * (*large_count - *small_count),
            "both ordinary nominal D occurrences must inspect every passive owner: {costs:?}"
        );
    }

    #[test]
    fn final_core_rejects_owner_state_in_an_unused_ordinary_function() {
        let fixture = Fixture::new();
        let entry = fs::read_to_string(fixture.0.join("entry.ash")).unwrap();
        fs::write(
            fixture.0.join("entry.ash"),
            entry.replace(
                "main () = {",
                "main () = {\n    let ordinary : Int -> Int = fn(ignored) {\n        42\n    }",
            ),
        )
        .unwrap();
        let compiled = fixture.compile();
        let (checked, provenance) = compiled.effect_build_input().unwrap();
        let sources = provenance
            .iter()
            .map(|(_, source)| source.as_ref())
            .collect::<Vec<_>>();
        let module_sources = provenance
            .iter()
            .map(|(module, source)| (*module, source.id()))
            .collect::<Vec<_>>();
        let ordinary = Type::Function(Box::new(Type::Int), Box::new(Type::Int));
        let pristine = super::super::transform::identity_effect_traversal(checked).unwrap();
        let (binding_index, function_id) = pristine
            .nodes
            .iter()
            .enumerate()
            .find_map(|(index, node)| match &node.kind {
                EffectExprKind::Pure(super::super::PureExprKind::Computation(
                    super::super::PureComputation::Bind(binding),
                )) if binding.binder().ty() == &ordinary => Some((index, binding.initializer())),
                _ => None,
            })
            .expect("reachable unused ordinary constant function binding");
        let owner = pristine
            .registry
            .source_owner_candidates()
            .next()
            .expect("authenticated owner category")
            .2;
        super::super::validate::validate_effect_modules_family(pristine, &sources, &module_sources)
            .expect("the unused scalar function and all lifecycle copies validate");

        // Direct, nested tuple, and nested callable domains all retain a State
        // component. The body remains a closed Int constant in every case.
        for nesting in 0..3 {
            let mut transformed =
                super::super::transform::identity_effect_traversal(checked).unwrap();
            // Identity traversal preserves node order in its newly allocated arena.
            let current_function_id = NodeId::new(
                transformed.arena,
                u32::try_from(function_id.index().unwrap()).unwrap(),
            );
            let state = Type::Application(Box::new(Type::Nominal(owner)), Box::new(Type::Int));
            let domain = match nesting {
                0 => state,
                1 => Type::Tuple(vec![Type::Unit, state].into_boxed_slice()),
                _ => Type::Function(Box::new(state), Box::new(Type::Int)),
            };
            let callable = Type::Function(Box::new(domain.clone()), Box::new(Type::Int));
            let node = &mut transformed.nodes[function_id.index().unwrap()];
            let EffectExprKind::Pure(super::super::PureExprKind::Value(
                super::super::PureValue::Function(function),
            )) = &mut node.kind
            else {
                panic!("the selected initializer is the ordinary Function")
            };
            assert_eq!(function.parameter().ty(), &Type::Int);
            let parameter = function.parameter().id();
            function.parameter_mut().replace_type(domain);
            crate::types::replace_type_iteratively(&mut node.ty, callable.clone());
            let EffectExprKind::Pure(super::super::PureExprKind::Computation(
                super::super::PureComputation::Bind(binding),
            )) = &mut transformed.nodes[binding_index].kind
            else {
                panic!("the selected ordinary binding is retained")
            };
            binding.binder_mut().replace_type(callable);
            assert!(
                transformed.nodes.iter().all(|node| !matches!(
                    &node.kind,
                    EffectExprKind::Pure(super::super::PureExprKind::Variable(variable))
                        if variable.binder() == parameter
                )),
                "the changed parameter has no uses to invalidate ordinary type equations"
            );
            let failure = super::super::validate::validate_effect_modules_family(
                transformed,
                &sources,
                &module_sources,
            )
            .expect_err("ordinary callable state cannot acquire lifecycle permission");
            assert_eq!(failure.reason(), ValidationReason::ResourceEscape);
            assert_eq!(failure.node(), Some(current_function_id));
        }
    }

    #[test]
    fn private_data_rejects_native_state_after_substitution_with_exact_scan_budget() {
        let fixture = Fixture::new();
        fs::write(
            fixture.0.join("owner.ash"),
            format!(
                "{}\npub type Recursive<T> = End\n    | More(T, Recursive<T>)\n",
                include_str!("../../tests/fixtures/source-owner/dependent_owner.ash")
            ),
        )
        .unwrap();
        fs::write(
            fixture.0.join("entry.ash"),
            "import owner as Owner\nmain : Unit -> Int\nmain () = 42\n",
        )
        .unwrap();
        let compiled = fixture.compile();
        let (checked, _) = compiled.effect_build_input().unwrap();
        let registry = checked.registry();
        let parent = registry
            .source_resource_facts()
            .find(|fact| fact.spelling == "Parent")
            .unwrap();
        let child = registry
            .source_resource_facts()
            .find(|fact| fact.spelling == "Child")
            .unwrap();
        let generic = Type::Tuple(vec![Type::Variable(parent.parameters[0].id), Type::Int].into());
        super::admit_private_data(&generic, registry, &mut TypeWorkBudget::default()).unwrap();
        let mut replacements = std::collections::HashMap::new();
        replacements.insert(parent.parameters[0].id, &parent.state.ty);
        let specialized = crate::types::IterativeTypeOwner::new(
            crate::types::substitute_type_variables_borrowed_with(
                &generic,
                &replacements,
                |_| Ok(()),
                || (),
            )
            .unwrap(),
        );
        assert_eq!(
            super::admit_private_data(&specialized, registry, &mut TypeWorkBudget::default())
                .unwrap_err()
                .reason(),
            ValidationReason::Registry
        );
        let recursive = registry
            .nominals()
            .iter()
            .find(|nominal| nominal.spelling == "Recursive")
            .unwrap();
        let recursive_access = crate::types::IterativeTypeOwner::new(Type::Application(
            Box::new(Type::Nominal(recursive.id)),
            Box::new(
                crate::types::clone_type_with_budget(
                    &child.data.ty,
                    &mut TypeWorkBudget::default(),
                )
                .unwrap(),
            ),
        ));
        super::admit_private_data(&recursive_access, registry, &mut TypeWorkBudget::default())
            .expect("recursive ordinary access payloads are not native State storage");
        // The original access family is distinct from its owner's native State.
        let mut measured = TypeWorkBudget::default();
        super::admit_private_data(&child.data.ty, registry, &mut measured).unwrap();
        let cost = measured.used();
        assert!(cost > 0);
        for prefix in [0, 9] {
            let mut short = TypeWorkBudget::with_limit(prefix + cost - 1);
            short.charge(prefix).unwrap();
            assert_eq!(
                super::admit_private_data(&child.data.ty, registry, &mut short)
                    .unwrap_err()
                    .reason(),
                ValidationReason::Resource
            );
            assert!(short.used() < prefix + cost);
            for _ in 0..2 {
                let mut exact = TypeWorkBudget::with_limit(prefix + cost);
                exact.charge(prefix).unwrap();
                super::admit_private_data(&child.data.ty, registry, &mut exact).unwrap();
                assert_eq!(exact.used(), prefix + cost);
            }
        }
    }

    #[test]
    fn dependent_source_scope_rejects_current_identity_and_changed_copy_actuals() {
        let fixture = Fixture::new();
        let owner = include_str!("../../tests/fixtures/source-owner/dependent_owner.ash")
            .replace(
                "pub resource Parent<P>",
                "pub resource Parent<Before : EffectRow, P, After : EffectRow>",
            )
            .replace("Parent<P>", "Parent<{| Before}, P, {| After}>")
            .replace(
                "pub resource Child<P, R>",
                "pub resource Child<Before : EffectRow, P, R, After : EffectRow>",
            )
            .replace("Child<P, R>", "Child<{| Before}, P, R, {| After}>");
        fs::write(fixture.0.join("owner.ash"), owner).unwrap();
        fs::write(fixture.0.join("entry.ash"), "import owner as Owner\neffect Marker {\n    marker : Unit -> Unit\n}\nmain : Unit -> Owner.Scope<Unit, Unit, Owner.Scope<Unit, Unit, Int>>\nmain () = resource Owner.Parent<{Marker}, ParentFresh, {}> parent = 64 {\n    resource Owner.Child<{Marker}, ParentFresh, ChildFresh, {}> child = (parent, 4) {\n        Owner.child_read child\n    }\n}\n").unwrap();
        let compiled = fixture.compile();
        let (checked, provenance) = compiled.effect_build_input().unwrap();
        let sources = provenance
            .iter()
            .map(|(_, source)| source.as_ref())
            .collect::<Vec<_>>();
        let modules = provenance
            .iter()
            .map(|(module, source)| (*module, source.id()))
            .collect::<Vec<_>>();
        let fresh = || super::super::transform::identity_effect_traversal(checked).unwrap();
        super::super::validate::validate_effect_modules_family(fresh(), &sources, &modules)
            .unwrap();
        for change in 0..6 {
            let mut forged = fresh();
            let index = forged.nodes.iter().position(|node| matches!(&node.kind,
                EffectExprKind::Operation(EffectOperation::SourceResourceScope(scope)) if !scope.header().dependencies.is_empty()
            )).unwrap();
            let id = NodeId::new(forged.arena, u32::try_from(index).unwrap());
            let EffectExprKind::Operation(EffectOperation::SourceResourceScope(scope)) =
                &mut forged.nodes[index].kind
            else {
                panic!("dependent scope")
            };
            let identity = scope.identity();
            let dependency = scope.header().dependencies[0];
            let position = scope
                .header()
                .original
                .parameters
                .iter()
                .position(|parameter| parameter.id == dependency)
                .unwrap();
            let row_parameter = scope
                .header()
                .original
                .parameters
                .iter()
                .position(|parameter| matches!(parameter.kind, crate::types::Kind::EffectRow))
                .unwrap();
            let row_id = scope.header().original.parameters[row_parameter].id;
            let descriptor = Arc::get_mut(&mut scope.descriptor).unwrap();
            assert!(
                matches!(&descriptor.arguments[row_parameter], KindedArgument::RowArg(row) if !row.known().is_empty())
            );
            if change == 0 {
                let previous = std::mem::replace(
                    &mut descriptor.arguments[position],
                    KindedArgument::TypeArg(Type::Variable(identity)),
                );
                crate::types::discard_kinded_argument_iteratively(previous);
            } else if change <= 3 {
                let actual = descriptor.copies[change - 1]
                    .types
                    .get_mut(&dependency)
                    .expect("complete dependency substitution is retained in every phase");
                crate::types::replace_type_iteratively(actual, Type::Variable(identity));
            } else if change == 4 {
                let actual = descriptor.copies[0]
                    .rows
                    .get_mut(&row_id)
                    .expect("complete non-empty Row substitution is retained");
                *actual = crate::types::EffectRow::empty();
            } else {
                let previous = std::mem::replace(
                    &mut descriptor.arguments[row_parameter],
                    KindedArgument::RowArg(crate::types::EffectRow::empty()),
                );
                crate::types::discard_kinded_argument_iteratively(previous);
            }
            let EffectExprKind::Operation(EffectOperation::SourceResourceScope(scope)) =
                &forged.nodes[index].kind
            else {
                unreachable!()
            };
            let failure = scope.authenticate(id, &forged, &mut TypeWorkBudget::default()).expect_err("current identity cannot replace an enclosing dependency or its original copy actual");
            assert_eq!(
                failure.reason(),
                ValidationReason::Registry,
                "claim{change}"
            );
            assert!(
                super::super::validate::validate_effect_modules_family(forged, &sources, &modules)
                    .is_err()
            );
        }
    }

    #[test]
    fn inherited_row_owner_copies_preserve_phantom_order_identity_and_state_barriers() {
        let fixture = Fixture::new();
        let owner = include_str!("../../tests/fixtures/source-owner/owner.ash")
            .replace(
                "owner State<R>",
                "owner State<Before : EffectRow, R, After : EffectRow>",
            )
            .replace("State<R>", "State<{| Before}, R, {| After}>");
        fs::write(fixture.0.join("owner.ash"), owner).unwrap();
        fs::write(fixture.0.join("entry.ash"), "import owner as Owner\neffect First {\n    first : Unit -> Unit\n}\neffect Last {\n    last : Unit -> Unit\n}\nmain : Unit -> (Owner.Scope<Unit, Unit, Int>, Owner.Scope<Unit, Unit, Int>)\nmain () = (resource Owner.Probe<{First}, Fresh, {Last}> owner = 42 {\n    Owner.read owner\n}, resource Owner.Probe<{Last}, Donor, {First}> owner = 7 {\n    Owner.read owner\n})\n").unwrap();
        let compiled = fixture.compile();
        let (checked, provenance) = compiled.effect_build_input().unwrap();
        let sources = provenance
            .iter()
            .map(|(_, source)| source.as_ref())
            .collect::<Vec<_>>();
        let modules = provenance
            .iter()
            .map(|(module, source)| (*module, source.id()))
            .collect::<Vec<_>>();
        let fresh = || super::super::transform::identity_effect_traversal(checked).unwrap();
        let validate = |program, work: &mut TypeWorkBudget| {
            super::super::validate::validate_effect_modules_with_work(
                program, &sources, &modules, work,
            )
        };
        let original = fresh();
        let indices = source_forwarding_scope_indices(&original);
        assert_eq!(indices.len(), 2);
        let EffectExprKind::Operation(EffectOperation::SourceResourceScope(first)) =
            &original.nodes[indices[0]].kind
        else {
            unreachable!()
        };
        let EffectExprKind::Operation(EffectOperation::SourceResourceScope(donor)) =
            &original.nodes[indices[1]].kind
        else {
            unreachable!()
        };
        assert_ne!(first.identity(), donor.identity());
        let donor_identity = donor.identity();
        let Type::Tuple(state_data) = first.finish.parameter.ty() else {
            panic!("complete finish domain")
        };
        assert!(
            matches!(&state_data[0], Type::ForeignOwnerApply(_, arguments) if arguments.len() == 3 && matches!(&arguments[0], KindedArgument::RowArg(row) if !row.known().is_empty()) && matches!(&arguments[2], KindedArgument::RowArg(row) if !row.known().is_empty()))
        );
        let state = crate::types::IterativeTypeOwner::new(
            crate::types::clone_type_with_budget(&state_data[0], &mut TypeWorkBudget::default())
                .unwrap(),
        );
        assert_eq!(
            super::admit_private_data(&state, checked.registry(), &mut TypeWorkBudget::default())
                .unwrap_err()
                .reason(),
            ValidationReason::Registry
        );
        let nested_state = crate::types::IterativeTypeOwner::new(Type::Tuple(
            vec![
                Type::Int,
                crate::types::clone_type_with_budget(&state, &mut TypeWorkBudget::default())
                    .unwrap(),
            ]
            .into_boxed_slice(),
        ));
        assert_eq!(
            super::admit_private_data(
                &nested_state,
                checked.registry(),
                &mut TypeWorkBudget::default()
            )
            .unwrap_err()
            .reason(),
            ValidationReason::Registry
        );

        let mut measured = TypeWorkBudget::default();
        validate(fresh(), &mut measured).unwrap();
        let cost = measured.used();
        for prefix in [0, 7] {
            let mut short = TypeWorkBudget::with_limit(prefix + cost - 1);
            short.charge(prefix).unwrap();
            assert_eq!(
                validate(fresh(), &mut short).unwrap_err().reason(),
                ValidationReason::Resource
            );
            for _ in 0..2 {
                let mut exact = TypeWorkBudget::with_limit(prefix + cost);
                exact.charge(prefix).unwrap();
                validate(fresh(), &mut exact).unwrap();
                assert_eq!(exact.used(), prefix + cost);
            }
            validate(fresh(), &mut TypeWorkBudget::default()).unwrap();
        }
        for change in 0..6 {
            let mut changed = fresh();
            let index = indices[0];
            let node = NodeId::new(changed.arena, u32::try_from(index).unwrap());
            let EffectExprKind::Operation(EffectOperation::SourceResourceScope(scope)) =
                &mut changed.nodes[index].kind
            else {
                unreachable!()
            };
            let before = scope.header().original.parameters[0].id;
            let after = scope.header().original.parameters[2].id;
            let descriptor = Arc::get_mut(&mut scope.descriptor).unwrap();
            assert!(
                matches!(&descriptor.arguments[0], KindedArgument::RowArg(row) if !row.known().is_empty())
            );
            assert!(
                matches!(&descriptor.arguments[2], KindedArgument::RowArg(row) if !row.known().is_empty())
            );
            match change {
                0 => descriptor.arguments.swap(0, 2),
                1 => {
                    let old = std::mem::replace(
                        &mut descriptor.arguments[1],
                        KindedArgument::RowArg(crate::types::EffectRow::empty()),
                    );
                    crate::types::discard_kinded_argument_iteratively(old);
                }
                2..=4 => {
                    let copy = &mut descriptor.copies[change - 2];
                    let replacement = crate::types::clone_effect_row_with_budget(
                        copy.rows.get(&after).unwrap(),
                        &mut TypeWorkBudget::default(),
                    )
                    .unwrap();
                    let actual = copy.rows.get_mut(&before).unwrap();
                    assert!(*actual != replacement);
                    *actual = replacement;
                }
                _ => {
                    let old = std::mem::replace(
                        &mut descriptor.arguments[1],
                        KindedArgument::TypeArg(Type::Variable(donor_identity)),
                    );
                    crate::types::discard_kinded_argument_iteratively(old);
                }
            }
            let EffectExprKind::Operation(EffectOperation::SourceResourceScope(scope)) =
                &changed.nodes[index].kind
            else {
                unreachable!()
            };
            assert_eq!(
                scope
                    .authenticate(node, &changed, &mut TypeWorkBudget::default())
                    .unwrap_err()
                    .reason(),
                ValidationReason::Registry,
                "full owner Row/copy claim {change}"
            );
            assert!(validate(changed, &mut TypeWorkBudget::default()).is_err());
        }
    }

    #[test]
    fn status_owner_scope_copies_preserve_phantom_rows_and_reject_changed_original_claims() {
        let fixture = Fixture::new();
        fs::write(
            fixture.0.join("owner.ash"),
            include_str!("../../tests/fixtures/source-owner/status_owner.ash"),
        )
        .unwrap();
        fs::write(fixture.0.join("entry.ash"), "import owner as Owner\neffect Notice {\n    notice : Unit -> Unit\n}\nmain : Unit -> Owner.Scope<Unit, Int, Int>\nmain () = resource Owner.Probe<{Notice}, R, {}> owner = 42 {\n    Owner.read owner\n}\n").unwrap();
        check_independent_source_scope(&fixture);
        let compiled = fixture.compile();
        let (checked, provenance) = compiled.effect_build_input().unwrap();
        let sources = provenance
            .iter()
            .map(|(_, source)| source.as_ref())
            .collect::<Vec<_>>();
        let modules = provenance
            .iter()
            .map(|(module, source)| (*module, source.id()))
            .collect::<Vec<_>>();
        let fresh = || super::super::transform::identity_effect_traversal(checked).unwrap();
        let validate = |program, work: &mut TypeWorkBudget| {
            super::super::validate::validate_effect_modules_with_work(
                program, &sources, &modules, work,
            )
        };
        let mut measured = TypeWorkBudget::default();
        validate(fresh(), &mut measured).unwrap();
        let exact = measured.used();
        for prefix in [0, 7] {
            let mut short = TypeWorkBudget::with_limit(prefix + exact - 1);
            short.charge(prefix).unwrap();
            assert_eq!(
                validate(fresh(), &mut short).unwrap_err().reason(),
                ValidationReason::Resource
            );
            for _ in 0..2 {
                let mut work = TypeWorkBudget::with_limit(prefix + exact);
                work.charge(prefix).unwrap();
                validate(fresh(), &mut work).unwrap();
                assert_eq!(work.used(), prefix + exact);
            }
        }
        for change in 0..4 {
            let mut changed = fresh();
            let index = changed
                .nodes
                .iter()
                .position(|stored| {
                    matches!(
                        &stored.kind,
                        EffectExprKind::Operation(EffectOperation::SourceResourceScope(_))
                    )
                })
                .unwrap();
            let id = NodeId::new(changed.arena, u32::try_from(index).unwrap());
            let EffectExprKind::Operation(EffectOperation::SourceResourceScope(scope)) =
                &mut changed.nodes[index].kind
            else {
                unreachable!()
            };
            let before = scope.header().original.parameters[0].id;
            let descriptor = Arc::get_mut(&mut scope.descriptor).unwrap();
            assert!(
                matches!(&descriptor.arguments[0], KindedArgument::RowArg(row) if !row.known().is_empty())
            );
            assert!(
                matches!(&descriptor.arguments[2], KindedArgument::RowArg(row) if row.known().is_empty())
            );
            if change == 0 {
                let previous = std::mem::replace(
                    &mut descriptor.arguments[0],
                    KindedArgument::RowArg(crate::types::EffectRow::empty()),
                );
                crate::types::discard_kinded_argument_iteratively(previous);
            } else {
                *descriptor.copies[change - 1].rows.get_mut(&before).unwrap() =
                    crate::types::EffectRow::empty();
            }
            let EffectExprKind::Operation(EffectOperation::SourceResourceScope(scope)) =
                &changed.nodes[index].kind
            else {
                unreachable!()
            };
            assert_eq!(
                scope
                    .authenticate(id, &changed, &mut TypeWorkBudget::default())
                    .unwrap_err()
                    .reason(),
                ValidationReason::Registry,
                "well-kinded phantom row/copy change {change}"
            );
            assert!(validate(changed, &mut TypeWorkBudget::default()).is_err());
        }
    }

    #[test]
    fn independently_revalidated_source_scope_rejects_incomplete_or_forged_claims() {
        let fixture = Fixture::new();
        check_independent_source_scope(&fixture);
    }

    #[test]
    fn independently_revalidated_acquired_only_scope_rejects_incomplete_or_forged_claims() {
        let fixture = Fixture::new();
        fs::write(
            fixture.0.join("owner.ash"),
            include_str!("../../tests/fixtures/source-owner/acquired_only_owner.ash"),
        )
        .unwrap();
        fs::write(
            fixture.0.join("entry.ash"),
            include_str!("../../tests/fixtures/source-owner/acquired_only_entry.ash"),
        )
        .unwrap();
        check_independent_source_scope(&fixture);
    }

    fn initialized_byte_fixture(acquired_only: bool) -> Fixture {
        let fixture = Fixture::new();
        let (owner, entry) = if acquired_only {
            (
                include_str!("../../tests/fixtures/source-owner/acquired_only_owner.ash"),
                include_str!("../../tests/fixtures/source-owner/acquired_only_entry.ash"),
            )
        } else {
            (
                include_str!("../../tests/fixtures/source-owner/owner.ash"),
                include_str!("../../tests/fixtures/source-owner/entry.ash"),
            )
        };
        let owner = owner
            .replace("repr Address = opaque", "repr Address = bytes")
            .replace(
                ": Int -> Foreign.Call<Foreign.Output<Foreign.Nullable<State<R>>>>",
                ": (Int, Int) -> Foreign.Call<Foreign.Output<Foreign.Nullable<State<R>>>>",
            )
            .replace(
                "outcome result nonnull { readable result }",
                "outcome result nonnull { readable result, initialized_bytes result from 1 }",
            )
            .replace(".call size {", ".call (size, 7) {");
        fs::write(fixture.0.join("owner.ash"), owner).unwrap();
        fs::write(fixture.0.join("entry.ash"), entry).unwrap();
        fixture
    }

    fn byte_access_fixture(acquired_only: bool, generic_rows: bool) -> Fixture {
        let fixture = Fixture::new();
        let mut owner = include_str!("../../tests/fixtures/source-owner/byte_owner.ash").to_owned();
        let mut entry = if generic_rows {
            include_str!("../../tests/fixtures/source-owner/byte_generic_rows_entry.ash").to_owned()
        } else {
            include_str!("../../tests/fixtures/source-owner/byte_entry.ash").to_owned()
        };
        if generic_rows {
            owner = owner
                .replace(
                    "Before : EffectRow, R, After : EffectRow",
                    "Before : EffectRow, Phantom, R, After : EffectRow",
                )
                .replace(
                    "<{| Before}, R, {| After}>",
                    "<{| Before}, Phantom, R, {| After}>",
                );
            entry = entry
                .replace(
                    "Before : EffectRow, R, After : EffectRow",
                    "Before : EffectRow, Phantom, R, After : EffectRow",
                )
                .replace(
                    "<{| Before}, R, {| After}>",
                    "<{| Before}, Phantom, R, {| After}>",
                )
                .replace(
                    "<{| Before}, Inner, {| After}>",
                    "<{| Before}, Phantom, Inner, {| After}>",
                )
                .replace("<{Tag}, Outer, {}>", "<{Tag}, Int, Outer, {}>");
        }
        if acquired_only {
            owner = owner
                .replace(
                    "pub type Scope<I, E, T> = NotAcquired(I)\n    | Completed(T, Completion<E>)",
                    "pub type Outcome<T> = Success(T)\n    | Failure(Unit)",
                )
                .replace(
                    "result Scope<Unit, Unit, Answer> for <Answer>",
                    "result Outcome<Answer> for <Answer>",
                )
                .replace("codec scope", "codec acquired_only");
            entry = entry.replace("Owner.Scope<Unit, Unit, ", "Owner.Outcome<");
        }
        fs::write(fixture.0.join("owner.ash"), owner).unwrap();
        fs::write(fixture.0.join("entry.ash"), entry).unwrap();
        fixture
    }

    #[test]
    fn byte_access_original_copies_and_complete_rows_reject_independent_forgeries() {
        for acquired_only in [false, true] {
            let fixture = byte_access_fixture(acquired_only, true);
            check_independent_source_scope(&fixture);
            let compiled = fixture.compile();
            let (checked, provenance) = compiled.effect_build_input().unwrap();
            let sources = provenance
                .iter()
                .map(|(_, source)| source.as_ref())
                .collect::<Vec<_>>();
            let modules = provenance
                .iter()
                .map(|(module, source)| (*module, source.id()))
                .collect::<Vec<_>>();
            let original = super::super::transform::identity_effect_traversal(checked).unwrap();
            let index = source_forwarding_scope_indices(&original).into_iter().find(|index| {
                matches!(&original.nodes[*index].kind, EffectExprKind::Operation(EffectOperation::SourceResourceScope(scope))
                    if matches!(&scope.arguments()[0], KindedArgument::RowArg(row) if row.tail().is_some()))
            }).expect("the generic nested occurrence preserves its phantom Row actual");
            for changed in [0, 1, 3] {
                let mut forged =
                    super::super::transform::identity_effect_traversal(checked).unwrap();
                let EffectExprKind::Operation(EffectOperation::SourceResourceScope(scope)) =
                    &mut forged.nodes[index].kind
                else {
                    unreachable!()
                };
                let descriptor = Arc::get_mut(&mut scope.descriptor).unwrap();
                let old = &descriptor.arguments[changed];
                assert!(
                    matches!(old, KindedArgument::RowArg(row) if row.tail().is_some())
                        || matches!(old, KindedArgument::TypeArg(Type::Variable(_)))
                );
                // Before/After do not occur in the canonical byte value type S.
                // Change only the copied ordered Row actual, leaving every byte
                // Apply, type application, operand, original forest and type intact.
                let replacement = if changed == 1 {
                    KindedArgument::TypeArg(Type::Unit)
                } else {
                    KindedArgument::RowArg(crate::types::EffectRow::empty())
                };
                let old = std::mem::replace(&mut descriptor.arguments[changed], replacement);
                crate::types::discard_kinded_argument_iteratively(old);
                let EffectExprKind::Operation(EffectOperation::SourceResourceScope(scope)) =
                    &forged.nodes[index].kind
                else {
                    unreachable!()
                };
                let failure = scope
                    .authenticate(
                        NodeId::new(forged.arena, index as u32),
                        &forged,
                        &mut TypeWorkBudget::default(),
                    )
                    .unwrap_err();
                assert_eq!(failure.reason(), ValidationReason::Registry);
                assert!(
                    super::super::validate::validate_effect_modules_family(
                        forged, &sources, &modules
                    )
                    .is_err()
                );
            }
        }
    }

    #[test]
    fn byte_access_independent_core_has_exact_budget_prefix_and_fresh_retry() {
        let limit = crate::compiler_work::CompilationPhase::IndependentCore.hard_limit();
        for acquired_only in [false, true] {
            let fixture = byte_access_fixture(acquired_only, false);
            let compiled = fixture.compile();
            let (checked, provenance) = compiled.effect_build_input().unwrap();
            let sources = provenance
                .iter()
                .map(|(_, source)| source.as_ref())
                .collect::<Vec<_>>();
            let modules = provenance
                .iter()
                .map(|(module, source)| (*module, source.id()))
                .collect::<Vec<_>>();
            let mut measured = TypeWorkBudget::with_limit(limit);
            super::super::validate::validate_effect_modules_with_work(
                super::super::transform::identity_effect_traversal(checked).unwrap(),
                &sources,
                &modules,
                &mut measured,
            )
            .unwrap();
            let cost = measured.used();
            assert!(cost < crate::compiler_work::CompilationPhase::IndependentCore.budget());
            for prefix in [0, 5] {
                let mut short = TypeWorkBudget::with_limit(prefix + cost - 1);
                short.charge(prefix).unwrap();
                assert_eq!(
                    super::super::validate::validate_effect_modules_with_work(
                        super::super::transform::identity_effect_traversal(checked).unwrap(),
                        &sources,
                        &modules,
                        &mut short
                    )
                    .unwrap_err()
                    .reason(),
                    ValidationReason::Resource
                );
                for _ in 0..2 {
                    let mut exact = TypeWorkBudget::with_limit(prefix + cost);
                    exact.charge(prefix).unwrap();
                    super::super::validate::validate_effect_modules_with_work(
                        super::super::transform::identity_effect_traversal(checked).unwrap(),
                        &sources,
                        &modules,
                        &mut exact,
                    )
                    .unwrap();
                    assert_eq!(exact.used(), prefix + cost);
                }
            }
            println!("byte access independent Core: acquired_only={acquired_only}, work={cost}");
        }
    }

    #[test]
    fn initialized_byte_scope_revalidation_rejects_forged_claims_for_both_report_codecs() {
        for acquired_only in [false, true] {
            check_independent_source_scope(&initialized_byte_fixture(acquired_only));
        }
    }

    #[test]
    fn initialized_byte_header_admission_preserves_exact_budget_refusal_and_fresh_retry() {
        for acquired_only in [false, true] {
            let fixture = initialized_byte_fixture(acquired_only);
            let compiled = fixture.compile();
            let (checked, _) = compiled.effect_build_input().unwrap();
            let registry = checked.registry();
            let header = registry
                .source_resource_facts()
                .find(|header| header.spelling == "Probe")
                .unwrap();
            let mut measured = TypeWorkBudget::unbounded();
            super::CheckedSourceResourceHeader::admit(header, registry, &mut measured).unwrap();
            let cost = measured.used();
            let mut short = TypeWorkBudget::with_limit(cost - 1);
            assert_eq!(
                super::CheckedSourceResourceHeader::admit(header, registry, &mut short)
                    .unwrap_err()
                    .reason(),
                ValidationReason::Resource
            );
            for _ in 0..2 {
                let mut exact = TypeWorkBudget::with_limit(cost);
                super::CheckedSourceResourceHeader::admit(header, registry, &mut exact).unwrap();
                assert_eq!(exact.used(), cost);
            }
            println!(
                "initialized byte header admission: acquired_only={acquired_only}, work={cost}"
            );
        }
    }

    #[test]
    fn acquired_only_header_admission_preserves_exact_budget_refusal_and_fresh_retry() {
        let fixture = Fixture::new();
        fs::write(
            fixture.0.join("owner.ash"),
            include_str!("../../tests/fixtures/source-owner/acquired_only_owner.ash"),
        )
        .unwrap();
        fs::write(
            fixture.0.join("entry.ash"),
            include_str!("../../tests/fixtures/source-owner/acquired_only_entry.ash"),
        )
        .unwrap();
        let compiled = fixture.compile();
        let (checked, _) = compiled.effect_build_input().unwrap();
        let registry = checked.registry();
        let header = registry
            .source_resource_facts()
            .find(|header| header.spelling == "Probe")
            .unwrap();
        let mut measured = TypeWorkBudget::unbounded();
        super::CheckedSourceResourceHeader::admit(header, registry, &mut measured).unwrap();
        let cost = measured.used();
        let mut short = TypeWorkBudget::with_limit(cost - 1);
        assert_eq!(
            super::CheckedSourceResourceHeader::admit(header, registry, &mut short)
                .unwrap_err()
                .reason(),
            ValidationReason::Resource
        );
        for _ in 0..2 {
            let mut exact = TypeWorkBudget::with_limit(cost);
            let admitted =
                super::CheckedSourceResourceHeader::admit(header, registry, &mut exact).unwrap();
            assert!(matches!(
                admitted.codec.report,
                super::SourceResourceReportCodec::AcquiredOnly { .. }
            ));
            assert_eq!(exact.used(), cost);
        }
    }

    fn check_independent_source_scope(fixture: &Fixture) {
        let compiled = fixture.compile();
        let (checked, provenance) = compiled.effect_build_input().unwrap();
        let sources = provenance
            .iter()
            .map(|(_, source)| source.as_ref())
            .collect::<Vec<_>>();
        let module_sources = provenance
            .iter()
            .map(|(module, source)| (*module, source.id()))
            .collect::<Vec<_>>();
        let transformed = super::super::transform::identity_effect_traversal(checked)
            .expect("checked scope identity traversal");
        let original = transformed
            .nodes
            .iter()
            .find_map(|stored| match &stored.kind {
                EffectExprKind::Operation(EffectOperation::SourceResourceScope(scope)) => {
                    Some(Arc::clone(scope.original()))
                }
                _ => None,
            })
            .expect("checked scope retains immutable originals");
        super::super::validate::validate_effect_modules_family(
            transformed,
            &sources,
            &module_sources,
        )
        .expect("copied scope independently reconstructs original forests");
        let failure = super::super::check_ordinary_effect_modules_with_budget_for_test(
            original.original_acquire(),
            &sources,
            &module_sources,
            &mut TypeWorkBudget::default(),
        )
        .expect_err("an original owner acquisition forest is not an executable standalone program");
        assert_eq!(failure.reason(), ValidationReason::Registry);
        // This forest's registry is an OriginalTemplate projection. FinalProgram
        // admission can reject that registry before choosing a request node;
        // it must still refuse standalone execution semantically.

        for mutation in 0..4 {
            let mut transformed =
                super::super::transform::identity_effect_traversal(checked).unwrap();
            let scope = transformed
                .nodes
                .iter_mut()
                .find_map(|stored| match &mut stored.kind {
                    EffectExprKind::Operation(EffectOperation::SourceResourceScope(scope)) => {
                        Some(scope.as_mut())
                    }
                    _ => None,
                })
                .expect("public compilation retains source scope");
            match mutation {
                0 => {
                    let descriptor = Arc::get_mut(&mut scope.descriptor).unwrap();
                    let owned = descriptor.template.header.original.owned_position;
                    let previous = std::mem::replace(
                        &mut descriptor.arguments[owned],
                        KindedArgument::TypeArg(Type::Unit),
                    );
                    crate::types::discard_kinded_argument_iteratively(previous);
                }
                1 => {
                    let descriptor = Arc::get_mut(&mut scope.descriptor).unwrap();
                    let copy = &mut descriptor.copies[0];
                    assert!(!copy.binders.is_empty());
                    copy.binders = std::mem::take(&mut copy.binders)
                        .into_vec()
                        .into_iter()
                        .skip(1)
                        .collect::<Vec<_>>()
                        .into_boxed_slice();
                }
                2 => {
                    let descriptor = Arc::get_mut(&mut scope.descriptor).unwrap();
                    let copy = &mut descriptor.copies[0];
                    assert!(copy.nodes.len() > 1);
                    copy.nodes[1].1 = copy.nodes[0].1;
                }
                _ => {
                    scope.handler_output = crate::types::ComputationType::pure(Type::Unit);
                }
            }
            let failure = super::super::validate::validate_effect_modules_family(
                transformed,
                &sources,
                &module_sources,
            )
            .expect_err("scope claim mutation must fail independent admission");
            assert_ne!(
                failure.reason(),
                ValidationReason::Resource,
                "scope claim mutation {mutation} must fail semantically"
            );
        }
    }

    fn source_forwarding_fixture() -> Fixture {
        let fixture = Fixture::new();
        fs::write(
            fixture.0.join("owner.ash"),
            include_str!("../../tests/fixtures/source-owner/forwarding_owner.ash"),
        )
        .unwrap();
        fs::write(
            fixture.0.join("entry.ash"),
            r#"import owner as Owner

main : Unit -> Owner.Scope<Unit, Unit, (Int, Owner.Scope<Unit, Unit, (Int, Int)>, Int)>
main () = resource Owner.Probe<{}, Outer, {}> outer = 64 {
    let before = Owner.read outer
    let child = resource Owner.Probe<{}, Inner, {}> inner = 4 {
        (Owner.read inner, Owner.offset (inner, 3))
    }
    let after = Owner.read outer
    (before, child, after)
}
"#,
        )
        .unwrap();
        fixture
    }

    fn source_forwarding_scope_indices(program: &super::UnvalidatedEffectProgram) -> Vec<usize> {
        program
            .nodes
            .iter()
            .enumerate()
            .filter_map(|(index, stored)| {
                matches!(
                    &stored.kind,
                    EffectExprKind::Operation(EffectOperation::SourceResourceScope(_))
                )
                .then_some(index)
            })
            .collect()
    }

    fn source_forwarding_request_ids(
        program: &super::UnvalidatedEffectProgram,
        scope_index: usize,
    ) -> Vec<NodeId> {
        let EffectExprKind::Operation(EffectOperation::SourceResourceScope(scope)) =
            &program.nodes[scope_index].kind
        else {
            panic!("selected source forwarding scope")
        };
        let mut current = scope.handler.body();
        let mut requests = Vec::new();
        for _ in &scope.forwardings {
            let Some(super::PureExprKind::Computation(super::PureComputation::Bind(binding))) =
                super::pure(super::node(program, current).unwrap())
            else {
                panic!("generated forwarding binding")
            };
            let Some(super::PureExprKind::Value(super::PureValue::Function(function))) =
                super::pure(super::node(program, binding.initializer()).unwrap())
            else {
                panic!("generated forwarding function")
            };
            assert!(matches!(
                &super::node(program, function.body()).unwrap().kind,
                EffectExprKind::Operation(EffectOperation::Request(_))
            ));
            requests.push(function.body());
            current = binding.body();
        }
        requests
    }

    #[test]
    fn source_forwarding_borrowed_projection_preserves_fields_and_rejects_changed_type() {
        let fixture = source_forwarding_fixture();
        let compiled = fixture.compile();
        let (checked, _) = compiled.effect_build_input().unwrap();
        let mut program = super::super::transform::identity_effect_traversal(checked).unwrap();
        let mut compared = 0;
        let mut changed = 0;
        for ordinal in 0..program.nodes.len() {
            let id = NodeId::new(program.arena, u32::try_from(ordinal).unwrap());
            let owned = super::super::provider::projection::project(
                id,
                &program.nodes[ordinal],
                &mut TypeWorkBudget::with_limit(327680),
            );
            let borrowed = super::super::provider::projection::project_borrowed(
                id,
                &program.nodes[ordinal],
                &mut TypeWorkBudget::with_limit(327680),
            );
            match (owned, borrowed) {
                (Ok(expected), Ok(actual)) => {
                    assert!(
                        expected
                            .same_borrowed(&actual, &mut TypeWorkBudget::with_limit(327680))
                            .unwrap()
                    );
                    drop(actual);
                    compared += 1;
                    if program.nodes[ordinal].ty != Type::Unit {
                        let original =
                            std::mem::replace(&mut program.nodes[ordinal].ty, Type::Unit);
                        let altered = super::super::provider::projection::project_borrowed(
                            id,
                            &program.nodes[ordinal],
                            &mut TypeWorkBudget::with_limit(327680),
                        )
                        .unwrap();
                        assert!(
                            !expected
                                .same_borrowed(&altered, &mut TypeWorkBudget::with_limit(327680))
                                .unwrap()
                        );
                        drop(altered);
                        program.nodes[ordinal].ty = original;
                        changed += 1;
                    }
                }
                (Err(owned), Err(borrowed)) => assert_eq!(owned.reason(), borrowed.reason()),
                _ => panic!("owned and borrowed canonical emitters disagree"),
            }
        }
        assert!(compared > 20 && changed > 10);
    }

    #[test]
    fn source_forwarding_independent_core_has_exact_budget_and_fresh_retry() {
        let normal_limit = crate::compiler_work::CompilationPhase::IndependentCore.hard_limit();
        for acquired_only in [false, true] {
            let fixture = Fixture::new();
            let mut owner =
                include_str!("../../tests/fixtures/source-owner/forwarding_owner.ash").to_owned();
            let mut entry =
                include_str!("../../tests/fixtures/source-owner/forwarding_helper_entry.ash")
                    .to_owned();
            if acquired_only {
                owner = owner
                    .replace(
                        "pub type Scope<I, E, T> = NotAcquired(I)
    | Completed(T, Completion<E>)",
                        "pub type Outcome<T> = Success(T)
    | Failure(Unit)",
                    )
                    .replace(
                        "result Scope<Unit, Unit, Answer> for <Answer>",
                        "result Outcome<Answer> for <Answer>",
                    )
                    .replace("codec scope", "codec acquired_only");
                entry = entry.replace(
                    "Owner.Scope<Unit, Unit, (Int, Int)>",
                    "Owner.Outcome<(Int, Int)>",
                );
            }
            fs::write(fixture.0.join("owner.ash"), owner).unwrap();
            fs::write(fixture.0.join("entry.ash"), entry).unwrap();
            fs::write(
                fixture.0.join("helpers.ash"),
                include_str!("../../tests/fixtures/source-owner/forwarding_helpers.ash"),
            )
            .unwrap();
            let compiled = fixture.compile();
            let (checked, provenance) = compiled.effect_build_input().unwrap();
            let sources = provenance
                .iter()
                .map(|(_, source)| source.as_ref())
                .collect::<Vec<_>>();
            let module_sources = provenance
                .iter()
                .map(|(module, source)| (*module, source.id()))
                .collect::<Vec<_>>();
            let mut measured = TypeWorkBudget::with_limit(normal_limit);
            super::super::validate::validate_effect_modules_with_work(
                super::super::transform::identity_effect_traversal(checked).unwrap(),
                &sources,
                &module_sources,
                &mut measured,
            )
            .expect("independent Core uses the normal unchanged allowance");
            let required = measured.used();
            assert!(
                required > 0
                    && required < crate::compiler_work::CompilationPhase::IndependentCore.budget()
            );
            for prefix in [0, 5] {
                for available in [0, required - 1] {
                    let mut short = TypeWorkBudget::with_limit(prefix + available);
                    short.charge(prefix).unwrap();
                    assert_eq!(
                        super::super::validate::validate_effect_modules_with_work(
                            super::super::transform::identity_effect_traversal(checked).unwrap(),
                            &sources,
                            &module_sources,
                            &mut short,
                        )
                        .unwrap_err()
                        .reason(),
                        ValidationReason::Resource
                    );
                    for _ in 0..2 {
                        let mut exact = TypeWorkBudget::with_limit(prefix + required);
                        exact.charge(prefix).unwrap();
                        super::super::validate::validate_effect_modules_with_work(
                            super::super::transform::identity_effect_traversal(checked).unwrap(),
                            &sources,
                            &module_sources,
                            &mut exact,
                        )
                        .expect("a fresh exact allowance admits complete helper evidence");
                        assert_eq!(exact.used(), prefix + required);
                    }
                }
            }
            println!(
                "source forwarding independent Core: acquired_only={acquired_only}, work={required}"
            );
        }
    }

    #[test]
    fn source_forwarding_complete_row_metadata_is_frozen_before_late_normalization() {
        use super::super::dialect::CoreOperationFamily;
        let fixture = Fixture::new();
        fs::write(
            fixture.0.join("owner.ash"),
            include_str!("../../tests/fixtures/source-owner/forwarding_owner.ash"),
        )
        .unwrap();
        fs::write(
            fixture.0.join("entry.ash"),
            include_str!("../../tests/fixtures/source-owner/forwarding_generic_rows_entry.ash"),
        )
        .unwrap();
        let compiled = fixture.compile();
        let (checked, provenance) = compiled.effect_build_input().unwrap();
        let sources = provenance
            .iter()
            .map(|(_, source)| source.as_ref())
            .collect::<Vec<_>>();
        let module_sources = provenance
            .iter()
            .map(|(module, source)| (*module, source.id()))
            .collect::<Vec<_>>();
        let mut positive = super::super::transform::identity_effect_traversal(checked).unwrap();
        let indices = source_forwarding_scope_indices(&positive);
        assert_eq!(indices.len(), 2);
        let index = *indices.iter().find(|index| match &positive.nodes[**index].kind {
            EffectExprKind::Operation(EffectOperation::SourceResourceScope(scope)) => {
                matches!(&scope.descriptor.arguments[0], KindedArgument::RowArg(row) if row.tail().is_some())
            }
            _ => false,
        }).expect("generic helper's complete rigid Row argument");
        let descriptor = match &positive.nodes[index].kind {
            EffectExprKind::Operation(EffectOperation::SourceResourceScope(scope)) => {
                Arc::clone(&scope.descriptor)
            }
            _ => unreachable!(),
        };
        assert!(matches!(descriptor.arguments[0], KindedArgument::RowArg(_)));
        assert!(matches!(descriptor.arguments[2], KindedArgument::RowArg(_)));
        // A SourceScope is already admitted against normalized original copies.
        // An enclosing normalization must preserve this immutable certificate.
        super::super::EffectOperationFamily::rewrite_operation_type_metadata(
            &mut positive.nodes[index].kind,
            &mut |_| panic!("late normalization cannot rewrite a frozen source descriptor"),
            &mut |_| Ok(()),
        )
        .unwrap();
        let EffectExprKind::Operation(EffectOperation::SourceResourceScope(scope)) =
            &positive.nodes[index].kind
        else {
            unreachable!()
        };
        assert!(Arc::ptr_eq(&descriptor, &scope.descriptor));
        scope
            .authenticate(
                NodeId::new(positive.arena, index as u32),
                &positive,
                &mut TypeWorkBudget::default(),
            )
            .unwrap();
        drop(descriptor);
        super::super::validate::validate_effect_modules_family(positive, &sources, &module_sources)
            .unwrap();
        for unresolved in [false, true] {
            let mut forged = super::super::transform::identity_effect_traversal(checked).unwrap();
            let EffectExprKind::Operation(EffectOperation::SourceResourceScope(scope)) =
                &mut forged.nodes[index].kind
            else {
                unreachable!()
            };
            let descriptor = Arc::get_mut(&mut scope.descriptor).unwrap();
            let slot = if unresolved { 1 } else { 0 };
            let replacement = if unresolved {
                KindedArgument::TypeArg(Type::Inference(crate::types::InferenceVariableId::new(
                    u32::MAX,
                )))
            } else {
                KindedArgument::RowArg(crate::types::EffectRow::empty())
            };
            crate::types::discard_kinded_argument_iteratively(std::mem::replace(
                &mut descriptor.arguments[slot],
                replacement,
            ));
            // Preserving a certificate never grants altered or unresolved actuals.
            assert!(
                super::super::validate::validate_effect_modules_family(
                    forged,
                    &sources,
                    &module_sources
                )
                .is_err()
            );
        }
    }

    #[test]
    fn source_forwarding_scope_rejects_missing_duplicate_and_swapped_method_binder_claims() {
        #[derive(Clone, Copy, Debug)]
        enum Mutation {
            Missing,
            DuplicateMethod,
            DuplicateBinder,
            SwappedMethods,
            SwappedBinders,
        }

        let fixture = source_forwarding_fixture();
        // This also preserves the existing original-forest/freshening negatives
        // for a public fixture whose method and operation declaration orders differ.
        check_independent_source_scope(&fixture);
        let compiled = fixture.compile();
        let (checked, provenance) = compiled.effect_build_input().unwrap();
        let sources = provenance
            .iter()
            .map(|(_, source)| source.as_ref())
            .collect::<Vec<_>>();
        let module_sources = provenance
            .iter()
            .map(|(module, source)| (*module, source.id()))
            .collect::<Vec<_>>();
        for mutation in [
            Mutation::Missing,
            Mutation::DuplicateMethod,
            Mutation::DuplicateBinder,
            Mutation::SwappedMethods,
            Mutation::SwappedBinders,
        ] {
            let mut transformed =
                super::super::transform::identity_effect_traversal(checked).unwrap();
            let indices = source_forwarding_scope_indices(&transformed);
            assert_eq!(indices.len(), 2);
            let scope_index = indices[0];
            let scope_id = NodeId::new(transformed.arena, u32::try_from(scope_index).unwrap());
            let EffectExprKind::Operation(EffectOperation::SourceResourceScope(scope)) =
                &mut transformed.nodes[scope_index].kind
            else {
                panic!("selected forwarding scope")
            };
            assert_eq!(scope.forwardings.len(), 2);
            assert_ne!(scope.forwardings[0].method, scope.forwardings[1].method);
            assert_ne!(scope.forwardings[0].binder, scope.forwardings[1].binder);
            let first = scope.forwardings[0];
            let second = scope.forwardings[1];
            match mutation {
                Mutation::Missing => {
                    let mut methods = std::mem::take(&mut scope.forwardings).into_vec();
                    methods.pop().unwrap();
                    scope.forwardings = methods.into_boxed_slice();
                }
                Mutation::DuplicateMethod => scope.forwardings[1].method = first.method,
                Mutation::DuplicateBinder => scope.forwardings[1].binder = first.binder,
                Mutation::SwappedMethods => {
                    scope.forwardings[0].method = second.method;
                    scope.forwardings[1].method = first.method;
                }
                Mutation::SwappedBinders => {
                    scope.forwardings[0].binder = second.binder;
                    scope.forwardings[1].binder = first.binder;
                }
            }
            let EffectExprKind::Operation(EffectOperation::SourceResourceScope(scope)) =
                &transformed.nodes[scope_index].kind
            else {
                panic!("selected mutated forwarding scope")
            };
            let failure = scope
                .authenticate(scope_id, &transformed, &mut TypeWorkBudget::default())
                .expect_err("forwarding claims must authenticate independently");
            assert_eq!(failure.reason(), ValidationReason::Registry, "{mutation:?}");
            assert!(
                super::super::validate::validate_effect_modules_family(
                    transformed,
                    &sources,
                    &module_sources,
                )
                .is_err(),
                "{mutation:?} cannot publish independently checked Core"
            );
        }
    }

    #[test]
    fn source_forwarding_same_typed_application_cannot_donate_other_activation_authority() {
        let fixture = source_forwarding_fixture();
        let compiled = fixture.compile();
        let (checked, provenance) = compiled.effect_build_input().unwrap();
        let sources = provenance
            .iter()
            .map(|(_, source)| source.as_ref())
            .collect::<Vec<_>>();
        let module_sources = provenance
            .iter()
            .map(|(module, source)| (*module, source.id()))
            .collect::<Vec<_>>();
        let mut forged = super::super::transform::identity_effect_traversal(checked).unwrap();
        let indices = source_forwarding_scope_indices(&forged);
        let lexical = |index: usize| match &forged.nodes[index].kind {
            EffectExprKind::Operation(EffectOperation::SourceResourceScope(scope)) => scope.lexical,
            _ => unreachable!(),
        };
        let recipient = lexical(indices[0]);
        let donor = lexical(indices[1]);
        let mut catalog = (*forged.method_evidence).clone();
        let mut owners = catalog.lexical_owners().to_vec();
        let original = owners.clone();
        for owner in &mut owners {
            if owner.source != recipient {
                continue;
            }
            let donor = original
                .iter()
                .find(|row| row.source == donor && row.method == owner.method)
                .unwrap();
            let Some(crate::core::dialect::MethodEvidenceResourceOwner::Provider(recipient_owner)) =
                &owner.resource
            else {
                unreachable!()
            };
            let Some(crate::core::dialect::MethodEvidenceResourceOwner::Provider(donor_owner)) =
                &donor.resource
            else {
                unreachable!()
            };
            assert_ne!(recipient_owner.identity, donor_owner.identity);
            // Preserve exact binder, method and application. Only original
            // resource activation authority is taken from the other occurrence.
            owner.resource = donor.resource.clone();
        }
        catalog.set_lexical_owners(owners);
        forged.method_evidence = Arc::new(catalog);
        let EffectExprKind::Operation(EffectOperation::SourceResourceScope(scope)) =
            &forged.nodes[indices[0]].kind
        else {
            unreachable!()
        };
        scope
            .authenticate(
                NodeId::new(forged.arena, indices[0] as u32),
                &forged,
                &mut TypeWorkBudget::default(),
            )
            .expect("binder/application correspondence alone is unchanged");
        assert!(
            super::super::validate::validate_effect_modules_family(
                forged,
                &sources,
                &module_sources
            )
            .is_err(),
            "independent lexical resource-owner admission must reject donated activation authority"
        );
    }

    #[test]
    fn source_forwarding_scope_rejects_a_real_other_scope_lexical_source() {
        let fixture = source_forwarding_fixture();
        let compiled = fixture.compile();
        let (checked, provenance) = compiled.effect_build_input().unwrap();
        let sources = provenance
            .iter()
            .map(|(_, source)| source.as_ref())
            .collect::<Vec<_>>();
        let module_sources = provenance
            .iter()
            .map(|(module, source)| (*module, source.id()))
            .collect::<Vec<_>>();
        let positive = super::super::transform::identity_effect_traversal(checked).unwrap();
        super::super::validate::validate_effect_modules_family(positive, &sources, &module_sources)
            .expect("both real nested forwarding sources independently validate");

        let mut transformed = super::super::transform::identity_effect_traversal(checked).unwrap();
        let indices = source_forwarding_scope_indices(&transformed);
        assert_eq!(indices.len(), 2);
        let donor = match &transformed.nodes[indices[1]].kind {
            EffectExprKind::Operation(EffectOperation::SourceResourceScope(scope)) => scope.lexical,
            _ => unreachable!(),
        };
        let scope_index = indices[0];
        let scope_id = NodeId::new(transformed.arena, u32::try_from(scope_index).unwrap());
        let EffectExprKind::Operation(EffectOperation::SourceResourceScope(scope)) =
            &mut transformed.nodes[scope_index].kind
        else {
            panic!("selected recipient forwarding scope")
        };
        assert_ne!(scope.lexical, donor);
        scope.lexical = donor;
        let EffectExprKind::Operation(EffectOperation::SourceResourceScope(scope)) =
            &transformed.nodes[scope_index].kind
        else {
            unreachable!()
        };
        let failure = scope
            .authenticate(scope_id, &transformed, &mut TypeWorkBudget::default())
            .expect_err("another real source cannot authorize this forwarding binder");
        assert_eq!(failure.reason(), ValidationReason::Registry);
        assert!(
            super::super::validate::validate_effect_modules_family(
                transformed,
                &sources,
                &module_sources,
            )
            .is_err()
        );
    }

    #[test]
    fn source_forwarding_scope_rejects_changed_request_operand_effect_and_operation() {
        #[derive(Clone, Copy, Debug)]
        enum Mutation {
            Operand,
            Effect,
            Operation,
        }

        let fixture = source_forwarding_fixture();
        let owner = fs::read_to_string(fixture.0.join("owner.ash"))
            .unwrap()
            .replace("offset : (Access, Int) -> Int", "offset : Access -> Int")
            .replace(
                "offset (access, delta) => resume delta",
                "offset access => resume 11",
            );
        let entry = fs::read_to_string(fixture.0.join("entry.ash"))
            .unwrap()
            .replace("Owner.offset (inner, 3)", "Owner.offset inner");
        fs::write(fixture.0.join("owner.ash"), owner).unwrap();
        fs::write(fixture.0.join("entry.ash"), entry).unwrap();
        let compiled = fixture.compile();
        let (checked, provenance) = compiled.effect_build_input().unwrap();
        let sources = provenance
            .iter()
            .map(|(_, source)| source.as_ref())
            .collect::<Vec<_>>();
        let module_sources = provenance
            .iter()
            .map(|(module, source)| (*module, source.id()))
            .collect::<Vec<_>>();
        let positive = super::super::transform::identity_effect_traversal(checked).unwrap();
        super::super::validate::validate_effect_modules_family(positive, &sources, &module_sources)
            .expect("unchanged two-method forwarding requests independently validate");

        for mutation in [Mutation::Operand, Mutation::Effect, Mutation::Operation] {
            let mut transformed =
                super::super::transform::identity_effect_traversal(checked).unwrap();
            let indices = source_forwarding_scope_indices(&transformed);
            assert_eq!(indices.len(), 2);
            let scope_index = indices[0];
            let scope_id = NodeId::new(transformed.arena, u32::try_from(scope_index).unwrap());
            let requests = source_forwarding_request_ids(&transformed, scope_index);
            assert_eq!(requests.len(), 2);
            let request_id = requests[0];
            let request_index = request_id.index().unwrap();
            match mutation {
                Mutation::Operand => {
                    let EffectExprKind::Operation(EffectOperation::SourceResourceScope(scope)) =
                        &transformed.nodes[scope_index].kind
                    else {
                        unreachable!()
                    };
                    let handle = scope.handle.id();
                    let EffectExprKind::Operation(EffectOperation::Request(request)) =
                        &transformed.nodes[request_index].kind
                    else {
                        unreachable!()
                    };
                    let operand = request.operand();
                    let replacement_index = transformed
                        .nodes
                        .iter()
                        .position(|stored| {
                            matches!(super::pure(stored), Some(super::PureExprKind::Variable(variable))
                                if variable.binder() == handle)
                                && stored.ty == super::node(&transformed, operand).unwrap().ty
                        })
                        .expect("the client body contains a real same-typed access variable");
                    let replacement =
                        NodeId::new(transformed.arena, u32::try_from(replacement_index).unwrap());
                    assert_ne!(operand, replacement);
                    let Some(super::PureExprKind::Variable(original)) =
                        super::pure(super::node(&transformed, operand).unwrap())
                    else {
                        panic!("original forwarding operand is its parameter variable")
                    };
                    assert_ne!(original.binder(), handle);
                    // Both nodes have the exact same Access type. This mutation
                    // tests unchanged parameter transport, not a type mismatch.
                    let EffectExprKind::Operation(EffectOperation::Request(request)) =
                        &mut transformed.nodes[request_index].kind
                    else {
                        unreachable!()
                    };
                    request.operand = replacement;
                }
                Mutation::Effect => {
                    let EffectExprKind::Operation(EffectOperation::SourceResourceScope(donor)) =
                        &transformed.nodes[indices[1]].kind
                    else {
                        unreachable!()
                    };
                    let effect = crate::types::clone_effect_instance_with_budget(
                        donor.handler.effect(),
                        &mut TypeWorkBudget::default(),
                    )
                    .unwrap();
                    let EffectExprKind::Operation(EffectOperation::Request(request)) =
                        &mut transformed.nodes[request_index].kind
                    else {
                        unreachable!()
                    };
                    assert_eq!(request.effect.effect(), effect.effect());
                    assert_ne!(request.effect.arguments(), effect.arguments());
                    request.effect = effect;
                }
                Mutation::Operation => {
                    let EffectExprKind::Operation(EffectOperation::Request(sibling)) =
                        &super::node(&transformed, requests[1]).unwrap().kind
                    else {
                        unreachable!()
                    };
                    let operation = sibling.operation();
                    let EffectExprKind::Operation(EffectOperation::Request(request)) =
                        &transformed.nodes[request_index].kind
                    else {
                        unreachable!()
                    };
                    assert_ne!(request.operation(), operation);
                    let sibling_operand =
                        match &super::node(&transformed, requests[1]).unwrap().kind {
                            EffectExprKind::Operation(EffectOperation::Request(sibling)) => {
                                sibling.operand()
                            }
                            _ => unreachable!(),
                        };
                    let sibling_type = &super::node(&transformed, sibling_operand).unwrap().ty;
                    let operand_type = &super::node(&transformed, request.operand()).unwrap().ty;
                    assert!(
                        crate::types::same_type_with_budget(
                            sibling_type,
                            operand_type,
                            &mut TypeWorkBudget::default()
                        )
                        .unwrap()
                    );
                    // Same Access domain, Int result and provided effect. Only
                    // the exact associated operation identity changes.
                    let EffectExprKind::Operation(EffectOperation::Request(request)) =
                        &mut transformed.nodes[request_index].kind
                    else {
                        unreachable!()
                    };
                    request.operation = operation;
                }
            }
            let EffectExprKind::Operation(EffectOperation::SourceResourceScope(scope)) =
                &transformed.nodes[scope_index].kind
            else {
                unreachable!()
            };
            let failure = scope
                .authenticate(scope_id, &transformed, &mut TypeWorkBudget::default())
                .expect_err("generated forwarding requests retain exact original authority");
            assert_eq!(failure.reason(), ValidationReason::Registry, "{mutation:?}");
            assert!(
                super::super::validate::validate_effect_modules_family(
                    transformed,
                    &sources,
                    &module_sources,
                )
                .is_err(),
                "{mutation:?} cannot publish independently checked Core"
            );
        }
    }

    #[test]
    fn destruction_capture_copied_scope_keeps_exact_producer_and_full_row_originals() {
        let fixture = Fixture::new();
        let owner = include_str!("../../tests/fixtures/source-owner/owner.ash")
            .replace(
                "owner State<R>",
                "owner State<Before : EffectRow, R, After : EffectRow>",
            )
            .replace("State<R>", "State<{| Before}, R, {| After}>")
            .replace(
                "After : EffectRow> : Int ->",
                "After : EffectRow> : (Int, Int) ->",
            )
            .replace(
                "operand 0 from 0 scalar",
                "operand 0 from 0 scalar\n        destruction_operand 0 from 1 scalar",
            )
            .replace(
                "After : EffectRow> : State<{| Before}, R, {| After}> ->",
                "After : EffectRow> : (Int, State<{| Before}, R, {| After}>) ->",
            )
            .replace(
                "abi (pointer(Address)) -> void",
                "abi (Size, pointer(Address)) -> void",
            )
            .replace(
                "operand 0 from 0 current",
                "operand 0 from 0 scalar\n        operand 1 from 1 current",
            )
            .replace("consumed 0", "consumed 1")
            .replace(".call size {", ".call (size, 99) {")
            .replace(".call state {", ".call (data, state) {");
        let start = owner.find("    symbol Allocate<").unwrap();
        let end = owner.find("    symbol Free<").unwrap();
        let donor = owner[start..end]
            .replace("symbol Allocate<", "symbol AlternateAllocate<")
            .replace("ash_owner_acquire", "ash_owner_alternate_acquire")
            .replace(
                "destruction_operand 0 from 1 scalar",
                "destruction_operand 0 from 0 scalar",
            );
        let owner = format!("{}{donor}{}", &owner[..end], &owner[end..]);
        fs::write(fixture.0.join("owner.ash"), owner).unwrap();
        fs::write(fixture.0.join("entry.ash"), "import owner as Owner\neffect First {\n    first : Unit -> Unit\n}\neffect Last {\n    last : Unit -> Unit\n}\nmain : Unit -> Owner.Scope<Unit, Unit, Int>\nmain () = resource Owner.Probe<{First}, Fresh, {Last}> owner = 42 {\n    Owner.read owner\n}\n").unwrap();
        let compiled = fixture.compile();
        let (checked, provenance) = compiled.effect_build_input().unwrap();
        let sources = provenance
            .iter()
            .map(|(_, source)| source.as_ref())
            .collect::<Vec<_>>();
        let module_sources = provenance
            .iter()
            .map(|(module, source)| (*module, source.id()))
            .collect::<Vec<_>>();
        let donor = checked
            .registry()
            .effects()
            .iter()
            .find(|effect| effect.spelling == "AlternateAllocate")
            .unwrap()
            .native_contract
            .as_ref()
            .unwrap();
        let first = checked
            .registry()
            .effects()
            .iter()
            .find(|effect| effect.spelling == "First")
            .unwrap()
            .id;
        let last = checked
            .registry()
            .effects()
            .iter()
            .find(|effect| effect.spelling == "Last")
            .unwrap()
            .id;
        let transformed = super::super::transform::identity_effect_traversal(checked).unwrap();
        let index = transformed
            .nodes
            .iter()
            .position(|stored| {
                matches!(
                    stored.kind,
                    EffectExprKind::Operation(EffectOperation::SourceResourceScope(_))
                )
            })
            .unwrap();
        let EffectExprKind::Operation(EffectOperation::SourceResourceScope(scope)) =
            &transformed.nodes[index].kind
        else {
            unreachable!()
        };
        let producer = scope.header().acquire.operation();
        assert_eq!(
            scope.header().acquire.symbol().destruction_operands()[0].source(),
            &[1]
        );
        assert_eq!(donor.symbol().destruction_operands()[0].source(), &[0]);
        assert_ne!(producer, donor.operation());
        assert_eq!(
            scope.header().acquire.symbol().parameters().len(),
            donor.symbol().parameters().len()
        );
        assert!(
            scope
                .header()
                .acquire
                .symbol()
                .parameters()
                .iter()
                .zip(donor.symbol().parameters())
                .all(|(left, right)| left.kind() == right.kind())
        );
        super::super::validate::validate_effect_modules_family(
            transformed,
            &sources,
            &module_sources,
        )
        .unwrap();
        for mutation in 0..3 {
            let mut transformed =
                super::super::transform::identity_effect_traversal(checked).unwrap();
            let id = NodeId::new(transformed.arena, index as u32);
            if mutation == 0 {
                let request = transformed
                    .nodes
                    .iter_mut()
                    .find_map(|node| match &mut node.kind {
                        EffectExprKind::Operation(EffectOperation::Request(request))
                            if request.operation() == producer =>
                        {
                            Some(request)
                        }
                        _ => None,
                    })
                    .unwrap();
                let arguments = request
                    .effect
                    .arguments()
                    .iter()
                    .map(|argument| {
                        crate::types::clone_kinded_argument_with_budget(
                            argument,
                            &mut TypeWorkBudget::default(),
                        )
                        .unwrap()
                    })
                    .collect::<Vec<_>>();
                request.effect = crate::types::EffectInstance::new_kinded(
                    donor.effect(),
                    arguments.into_boxed_slice(),
                );
                request.operation = donor.operation();
            } else {
                let EffectExprKind::Operation(EffectOperation::SourceResourceScope(scope)) =
                    &mut transformed.nodes[index].kind
                else {
                    unreachable!()
                };
                let descriptor = Arc::get_mut(&mut scope.descriptor).unwrap();
                let copy = &mut descriptor.copies[0];
                if mutation == 1 {
                    assert!(copy.nodes.len() > 1);
                    copy.nodes[1].1 = copy.nodes[0].1;
                } else {
                    let before = *copy
                        .rows
                        .iter()
                        .find(|(_, row)| row.known().iter().any(|effect| effect.effect() == first))
                        .unwrap()
                        .0;
                    let after = copy
                        .rows
                        .iter()
                        .find(|(_, row)| row.known().iter().any(|effect| effect.effect() == last))
                        .unwrap()
                        .1;
                    let changed = crate::types::clone_effect_row_with_budget(
                        after,
                        &mut TypeWorkBudget::default(),
                    )
                    .unwrap();
                    assert_ne!(&copy.rows[&before], &changed);
                    copy.rows.insert(before, changed);
                }
            }
            let EffectExprKind::Operation(EffectOperation::SourceResourceScope(scope)) =
                &transformed.nodes[index].kind
            else {
                unreachable!()
            };
            let failure = scope
                .authenticate(id, &transformed, &mut TypeWorkBudget::default())
                .unwrap_err();
            assert_eq!(
                failure.reason(),
                ValidationReason::Registry,
                "copy/original mutation {mutation}"
            );
            let failure = super::super::validate::validate_effect_modules_family(
                transformed,
                &sources,
                &module_sources,
            )
            .unwrap_err();
            assert_eq!(
                failure.reason(),
                if mutation == 0 {
                    // The changed request retains the original stored row;
                    // ordinary whole-Core row checking rejects it first.
                    ValidationReason::EffectRow
                } else {
                    ValidationReason::Registry
                },
                "whole-Core copy/original mutation {mutation}"
            );
        }
    }

    #[test]
    fn final_source_scope_rejects_reordered_duplicate_or_missing_native_interpretations() {
        let fixture = Fixture::new();
        let compiled = fixture.compile();
        let (checked, provenance) = compiled.effect_build_input().unwrap();
        let sources = provenance
            .iter()
            .map(|(_, source)| source.as_ref())
            .collect::<Vec<_>>();
        let module_sources = provenance
            .iter()
            .map(|(module, source)| (*module, source.id()))
            .collect::<Vec<_>>();
        let transformed = super::super::transform::identity_effect_traversal(checked).unwrap();
        let index = transformed
            .nodes
            .iter()
            .position(|stored| {
                matches!(
                    stored.kind,
                    EffectExprKind::Operation(EffectOperation::SourceResourceScope(_))
                )
            })
            .expect("connected final source scope");
        let scope_id = NodeId::new(transformed.arena, u32::try_from(index).unwrap());
        let EffectExprKind::Operation(EffectOperation::SourceResourceScope(scope)) =
            &transformed.nodes[index].kind
        else {
            panic!("selected final source scope")
        };
        assert_eq!(scope.header().original.owned_position, 1);
        assert_eq!(scope.native_interpretations().len(), 2);
        for interpretation in scope.native_interpretations() {
            assert!(matches!(
                interpretation.effect().arguments(),
                [
                    KindedArgument::RowArg(_),
                    KindedArgument::TypeArg(_),
                    KindedArgument::RowArg(_)
                ]
            ));
        }
        scope
            .authenticate(scope_id, &transformed, &mut TypeWorkBudget::default())
            .expect("the final scope's complete specialized original list authenticates");
        super::super::validate::validate_effect_modules_family(
            transformed,
            &sources,
            &module_sources,
        )
        .expect("the unmodified final program independently validates");

        for mutation in 0..3 {
            let mut transformed =
                super::super::transform::identity_effect_traversal(checked).unwrap();
            let scope_id = NodeId::new(transformed.arena, u32::try_from(index).unwrap());
            let EffectExprKind::Operation(EffectOperation::SourceResourceScope(scope)) =
                &mut transformed.nodes[index].kind
            else {
                panic!("selected final source scope")
            };
            let descriptor = Arc::get_mut(&mut scope.descriptor).unwrap();
            match mutation {
                0 => descriptor.interpretations.swap(0, 1),
                1 => {
                    let mut interpretations =
                        std::mem::take(&mut descriptor.interpretations).into_vec();
                    interpretations.push(interpretations[0].clone());
                    descriptor.interpretations = interpretations.into_boxed_slice();
                }
                _ => {
                    let mut interpretations =
                        std::mem::take(&mut descriptor.interpretations).into_vec();
                    interpretations.pop().unwrap();
                    descriptor.interpretations = interpretations.into_boxed_slice();
                }
            }
            let EffectExprKind::Operation(EffectOperation::SourceResourceScope(scope)) =
                &transformed.nodes[index].kind
            else {
                panic!("selected final source scope")
            };
            let failure = scope
                .authenticate(scope_id, &transformed, &mut TypeWorkBudget::default())
                .expect_err("final scope metadata must reconstruct the ordered original list");
            assert_eq!(failure.reason(), ValidationReason::Registry);
            let failure = super::super::validate::validate_effect_modules_family(
                transformed,
                &sources,
                &module_sources,
            )
            .expect_err("malformed final interpretation metadata cannot publish checked Core");
            assert_eq!(failure.reason(), ValidationReason::Registry);
        }
    }

    fn payload_helper_fixture(polymorphic: bool) -> Fixture {
        let fixture = Fixture::new();
        let name = if polymorphic {
            "payload_copy"
        } else {
            "payload_mono"
        };
        let expression = if polymorphic {
            "false => {\n                let copy : Int -> Int = match size == 42 {\n                    true => payload_copy\n                    false => payload_copy\n                }\n                Acquired(state, copy size)\n            }".to_owned()
        } else {
            format!("false => Acquired(state, {name} size)")
        };
        let owner = include_str!("../../tests/fixtures/source-owner/owner.ash")
            .replace("false => Acquired(state, size)", &expression)
            + "\n"
            + include_str!("../../tests/fixtures/source-owner/payload_helpers.ash");
        fs::write(fixture.0.join("owner.ash"), owner).unwrap();
        fixture
    }

    #[test]
    fn payload_helper_complete_rows_and_core_budget_are_preserved() {
        use crate::core::{PureComputation, PureExprKind};
        let fixture = payload_helper_fixture(true);
        let compiled = fixture.compile();
        let (checked, provenance) = compiled.effect_build_input().unwrap();
        let sources = provenance
            .iter()
            .map(|(_, source)| source.as_ref())
            .collect::<Vec<_>>();
        let modules = provenance
            .iter()
            .map(|(module, source)| (*module, source.id()))
            .collect::<Vec<_>>();
        let fresh = || super::super::transform::identity_effect_traversal(checked).unwrap();
        let validate = |program, work: &mut TypeWorkBudget| {
            super::super::validate::validate_effect_modules_with_work(
                program, &sources, &modules, work,
            )
        };
        let mut measured = TypeWorkBudget::default();
        validate(fresh(), &mut measured).unwrap();
        let cost = measured.used();
        assert_eq!(
            validate(fresh(), &mut TypeWorkBudget::with_limit(cost - 1))
                .unwrap_err()
                .reason(),
            ValidationReason::Resource
        );
        for prefix in [0, 11] {
            for _ in 0..2 {
                let mut work = TypeWorkBudget::with_limit(prefix + cost);
                work.charge(prefix).unwrap();
                validate(fresh(), &mut work).unwrap();
                assert_eq!(work.used(), prefix + cost);
            }
        }
        let mut forged = fresh();
        let scope = forged
            .nodes
            .iter()
            .find_map(|node| match &node.kind {
                EffectExprKind::Operation(EffectOperation::SourceResourceScope(scope)) => {
                    Some(scope)
                }
                _ => None,
            })
            .unwrap();
        let provided = scope.handler.effect().clone();
        let copied = scope.copy_claims()[0].nodes.iter().find_map(|(_, copied)| {
            matches!(&forged.nodes[copied.index().unwrap()].kind,
                EffectExprKind::Pure(PureExprKind::Computation(PureComputation::TypeApplication(application)))
                if application.row_arguments().len() == 1).then_some(*copied)
        }).expect("complete ordered Row/Type helper application");
        let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::TypeApplication(
            application,
        ))) = &mut forged.nodes[copied.index().unwrap()].kind
        else {
            unreachable!()
        };
        let arguments = application.arguments().to_vec();
        let mut rows = application.row_arguments().to_vec();
        assert!(rows[0].is_empty());
        rows[0] = crate::types::EffectRow::singleton(provided);
        *application = crate::core::type_ops::TypeApplicationNode::new_with_row_arguments(
            application.function(),
            arguments,
            rows,
        );
        // Only the copied complete Row actual changes; the original remains.
        // Check correspondence directly before ordinary Core type validation.
        let (scope_id, scope) = forged
            .nodes
            .iter()
            .enumerate()
            .find_map(|(index, node)| match &node.kind {
                EffectExprKind::Operation(EffectOperation::SourceResourceScope(scope)) => {
                    Some((index, scope))
                }
                _ => None,
            })
            .unwrap();
        assert!(
            scope
                .authenticate(
                    NodeId::new(forged.arena, scope_id as u32),
                    &forged,
                    &mut TypeWorkBudget::default()
                )
                .is_err()
        );
        assert!(validate(forged, &mut TypeWorkBudget::default()).is_err());
        println!(
            "payload helper independent Core exact work={cost}; one-short, prefix, two fresh retries and copied Row refusal"
        );
    }

    #[test]
    fn payload_helper_same_type_donor_cannot_replace_a_copied_call() {
        use crate::core::{PureComputation, PureExprKind};
        let fixture = payload_helper_fixture(false);
        let compiled = fixture.compile();
        let (checked, provenance) = compiled.effect_build_input().unwrap();
        let sources = provenance
            .iter()
            .map(|(_, source)| source.as_ref())
            .collect::<Vec<_>>();
        let modules = provenance
            .iter()
            .map(|(module, source)| (*module, source.id()))
            .collect::<Vec<_>>();
        let mut forged = super::super::transform::identity_effect_traversal(checked).unwrap();
        let scope = forged
            .nodes
            .iter()
            .find_map(|node| match &node.kind {
                EffectExprKind::Operation(EffectOperation::SourceResourceScope(scope)) => {
                    Some(scope)
                }
                _ => None,
            })
            .unwrap();
        let (helper, signature) = scope.original().globals().iter().next().unwrap();
        let helper = *helper;
        let donor = forged
            .nodes
            .iter()
            .find_map(|node| match &node.kind {
                EffectExprKind::Pure(PureExprKind::Computation(
                    PureComputation::RecursiveBind(group),
                )) => group.members().iter().find_map(|member| {
                    (member.binder().id() != helper && member.binder().ty() == &**signature)
                        .then_some(member.binder().id())
                }),
                _ => None,
            })
            .expect("distinct ordinary same-type donor");
        let copied = scope.copy_claims()[0].nodes.iter().find_map(|(_, copied)| {
            matches!(&forged.nodes[copied.index().unwrap()].kind,
                EffectExprKind::Pure(PureExprKind::Variable(variable)) if variable.binder() == helper).then_some(*copied)
        }).unwrap();
        forged.nodes[copied.index().unwrap()].kind = EffectExprKind::Pure(PureExprKind::Variable(
            crate::core::variable::VariableNode::new(donor),
        ));
        assert!(
            super::super::validate::validate_effect_modules_with_work(
                forged,
                &sources,
                &modules,
                &mut TypeWorkBudget::default()
            )
            .is_err()
        );
    }

    #[test]
    fn payload_helper_registry_proof_is_bound_to_its_immutable_scheme_context() {
        let fixture = payload_helper_fixture(false);
        let compiled = fixture.compile();
        let (checked, provenance) = compiled.effect_build_input().unwrap();
        let sources = provenance
            .iter()
            .map(|(_, source)| source.as_ref())
            .collect::<Vec<_>>();
        let modules = provenance
            .iter()
            .map(|(module, source)| (*module, source.id()))
            .collect::<Vec<_>>();
        let program = super::super::transform::identity_effect_traversal(checked).unwrap();
        let original = program
            .nodes
            .iter()
            .find_map(|node| match &node.kind {
                EffectExprKind::Operation(EffectOperation::SourceResourceScope(scope)) => {
                    Some(Arc::clone(scope.original()))
                }
                _ => None,
            })
            .unwrap();
        let mut session = super::super::validate::SourceResourceStructureSession::default();
        let check = |session: &mut super::super::validate::SourceResourceStructureSession<'_>,
                     globals: &Arc<super::SourceResourceGlobals>,
                     work: &mut TypeWorkBudget| {
            session.check_with_globals(
                original.original_acquire(),
                &original.header.original,
                false,
                &sources,
                &modules,
                globals,
                work,
            )
        };
        let mut work = TypeWorkBudget::default();
        check(&mut session, &original.globals, &mut work).unwrap();
        let first = work.used();
        check(&mut session, &original.globals, &mut work).unwrap();
        let reused = work.used() - first;
        assert!(reused < first);
        let mut moved = super::SourceResourceGlobals::new();
        for (binder, ty) in original.globals.iter() {
            moved.insert(
                *binder,
                crate::types::IterativeTypeOwner::new(
                    crate::types::clone_type_with_budget(ty, &mut TypeWorkBudget::default())
                        .unwrap(),
                ),
            );
        }
        let moved = Arc::new(moved);
        let before = work.used();
        check(&mut session, &moved, &mut work).unwrap();
        let fresh_context = work.used() - before;
        assert!(
            fresh_context > reused,
            "a different immutable context must reauthenticate the registry"
        );
        let before = work.used();
        check(&mut session, &moved, &mut work).unwrap();
        assert_eq!(work.used() - before, reused);
        assert!(
            check(
                &mut session,
                &Arc::new(super::SourceResourceGlobals::new()),
                &mut TypeWorkBudget::default()
            )
            .is_err()
        );
        for _ in 0..2 {
            check(&mut session, &moved, &mut TypeWorkBudget::default()).unwrap();
        }
        println!(
            "payload helper registry context: first={first}, same={reused}, moved={fresh_context}; missing-loan refusal and two retries"
        );
    }
}

#[cfg(test)]
#[path = "source_resource/checked_owner_tests.rs"]
mod checked_owner_tests;
