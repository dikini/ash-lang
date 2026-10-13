//! Independently checked source resource headers. Header admission does not
//! admit lifecycle code, a specialized scope, a native binding or an activation.

use std::{collections::HashMap, sync::Arc};

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

fn finalize_arguments(
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

fn finalize_instance(
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
            Self::Scope { report, .. } => report[0],
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

/// Borrows a saturated ordinary nominal application without copying its types.
/// Row-bearing owner state families are refused by this bounded source profile.
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
    // State field must not hide it merely because no constructor runs here.
    // Each declaration is visited once, so recursive ordinary ADTs terminate.
    // Their actual arguments are already visited in the enclosing type walk.
    let candidates = registry.source_owner_candidate_count();
    let mut pending = one(ty, work)?;
    let mut visited = std::collections::HashSet::new();
    while let Some(ty) = pending.pop() {
        let mut nominals = Vec::new();
        let forbidden = crate::types::visit_type_structure_with_budget(ty, work, |node, work| {
            if let crate::types::TypeStructureNode::Type(Type::Nominal(nominal)) = node {
                work.charge(candidates)?;
                if registry.source_owner_nominal(*nominal) {
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
        let (state, state_arguments) = application(&header.state.ty, work)?;
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
        let mut acquiring = None;
        let mut tearing_down = None;
        charge(work, header.interpreted.len())?;
        for effect in &header.interpreted {
            let operation = OperationId::new(effect.instance.effect(), 0);
            let symbol = registry.native_symbol(operation).ok_or_else(invalid)?;
            let owner = symbol.owner().ok_or_else(invalid)?;
            if owner.nominal() != state
                || owner.parameter_ids().len() != state_arguments.len()
                || state_arguments
                    .get(owner.owned_parameter())
                    .is_none_or(|ty| !variable(ty, header.parameters[header.owned_position].id))
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
                | PreparedOwnerCall::Teardown { application, .. }
                | PreparedOwnerCall::StatusTeardown { application, .. } => application.arguments(),
            };
            charge(work, arguments.len())?;
            if arguments.len() != state_arguments.len() {
                return Err(invalid());
            }
            for (mapping, state_argument) in arguments.iter().zip(&state_arguments) {
                let crate::foreign::source_contract::PreparedOwnerArgument::Type(position) =
                    mapping
                else {
                    return Err(invalid());
                };
                let Some(KindedArgument::TypeArg(actual)) =
                    effect.instance.arguments().get(*position)
                else {
                    return Err(invalid());
                };
                if !same(actual, state_argument, work)? {
                    return Err(invalid());
                }
            }
            match role {
                PreparedOwnerCall::Acquire { .. } if acquiring.is_none() => {
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
        let owned = header.parameters[header.owned_position].id;
        let mut dependencies = Vec::new();
        charge(work, owner.owner().retained_parameters().len())?;
        dependencies
            .try_reserve_exact(owner.owner().retained_parameters().len())
            .map_err(|_| resource())?;
        for position in owner.owner().retained_parameters() {
            let Some(Type::Variable(identity)) = state_arguments.get(*position).copied() else {
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
                        ty @ (Type::Application(_, _) | Type::ResourceApply(_, _)),
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

/// Immutable defining forests. This certificate grants compiler copying input,
/// and cannot be converted to a validated executable program.
#[derive(Debug)]
pub(crate) struct CheckedSourceResourceTemplate {
    header: Arc<CheckedSourceResourceHeader>,
    acquire: UnvalidatedEffectProgram,
    finish: UnvalidatedEffectProgram,
    handler: UnvalidatedEffectProgram,
    acquire_entry: (TypedBinder, NodeId),
    finish_entry: (TypedBinder, NodeId),
    handler_entry: (TypedBinder, NodeId),
    methods: Box<[(crate::interface::MethodId, crate::types::OperationId)]>,
    byte_calls: [Box<[SourceByteCall]>; 3],
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

impl CheckedSourceResourceTemplate {
    pub(crate) fn admit(
        header: Arc<CheckedSourceResourceHeader>,
        acquire: UnvalidatedEffectProgram,
        finish: UnvalidatedEffectProgram,
        handler: UnvalidatedEffectProgram,
        sources: &[&crate::source::SourceFile],
        module_sources: &[(crate::module::ModuleId, crate::source::SourceId)],
        work: &mut TypeWorkBudget,
    ) -> Result<Self, ValidationError> {
        Self::admit_with_structure_session(
            header,
            acquire,
            finish,
            handler,
            sources,
            module_sources,
            work,
            &mut super::validate::SourceResourceStructureSession::default(),
        )
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn admit_with_structure_session(
        header: Arc<CheckedSourceResourceHeader>,
        acquire: UnvalidatedEffectProgram,
        finish: UnvalidatedEffectProgram,
        handler: UnvalidatedEffectProgram,
        sources: &[&crate::source::SourceFile],
        module_sources: &[(crate::module::ModuleId, crate::source::SourceId)],
        work: &mut TypeWorkBudget,
        session: &mut super::validate::SourceResourceStructureSession,
    ) -> Result<Self, ValidationError> {
        // Ordinary graph, kind, scope, effect, registry and provenance checking
        // precedes the resource-specific phase and owner-lineage proof.
        for (program, answer) in [(&acquire, false), (&finish, false), (&handler, true)] {
            if !Arc::ptr_eq(&program.registry, &acquire.registry) {
                return Err(invalid());
            }
            session.check(
                program,
                &header.original,
                answer,
                sources,
                module_sources,
                work,
            )?;
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
        let methods = check_provider_association(&header, &handler, work)?;
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
        let placeholder_binder = answer.parameter().id();
        let handler_body = answer.body();
        let acquire_calls = check_flow(
            &acquire,
            &header,
            &acquire_entry,
            SourceResourcePhase::Acquire,
            work,
        )?;
        let finish_calls = check_flow(
            &finish,
            &header,
            &finish_entry,
            SourceResourcePhase::Finish,
            work,
        )?;
        let handler_calls = check_handler(
            &handler,
            &header,
            &handler_entry.0,
            handler_body,
            placeholder_binder,
            work,
        )?;
        Ok(Self {
            header,
            acquire,
            finish,
            handler,
            acquire_entry,
            finish_entry,
            handler_entry: (handler_entry.0, handler_body),
            methods,
            byte_calls: [acquire_calls, finish_calls, handler_calls],
        })
    }
    pub(crate) fn header(&self) -> &Arc<CheckedSourceResourceHeader> {
        &self.header
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

#[derive(Debug)]
enum FlowFact<'a> {
    Independent,
    Fresh,
    Current,
    Enclosing(crate::types::TypeVariableId),
    // A typed but constructor-unknown ordinary input. The original forest owns
    // the Type; narrowing a checked constructor pattern preserves its payload
    // roles without manufacturing an enclosing state or cloning Type storage.
    InputNominal(&'a Type, Box<[crate::types::TypeVariableId]>),
    Tuple(Box<[usize]>),
    Constructor(ConstructorId, Option<usize>),
    Callable(ConstructorId),
    ScalarPreflight,
    ByteCallable(crate::resolved::BinderId, Option<NodeId>),
}
#[derive(Default)]
struct FlowFacts<'a> {
    values: Vec<FlowFact<'a>>,
    byte_calls: Vec<SourceByteCall>,
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
                FlowFact::Independent => {}
                FlowFact::InputNominal(_, identities) if identities.is_empty() => {}
                FlowFact::Tuple(fields) => {
                    charge(work, fields.len())?;
                    pending.try_reserve(fields.len()).map_err(|_| resource())?;
                    pending.extend_from_slice(fields);
                }
                FlowFact::Constructor(_, Some(payload)) => push(&mut pending, *payload, work)?,
                FlowFact::Constructor(_, None) => {}
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
                FlowFact::Independent | FlowFact::Constructor(_, None) => {}
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
struct FlowPath {
    locals: HashMap<crate::resolved::BinderId, usize>,
    acquired: bool,
    consumed: bool,
    attempted_teardown: bool,
}
impl FlowPath {
    fn new(work: &mut TypeWorkBudget) -> Result<Self, ValidationError> {
        charge(work, 1)?;
        Ok(Self {
            locals: HashMap::new(),
            acquired: false,
            consumed: false,
            attempted_teardown: false,
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
        Ok(Self {
            locals,
            acquired: self.acquired,
            consumed: self.consumed,
            attempted_teardown: self.attempted_teardown,
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
                    if fact.role().byte_parameter(fact.module()).is_some() {
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
                    if role.byte_parameter(fact.module()).is_some() {
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
                    FlowFact::ScalarPreflight | FlowFact::ByteCallable(_, Some(_)) => None,
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
                    } else {
                        if let FlowFact::ByteCallable(function, Some(application)) =
                            facts.fact(function)?
                        {
                            let function = *function;
                            let selected_application = *application;
                            let fact = program
                                .registry
                                .scalar_preflight(function)
                                .ok_or_else(invalid)?;
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
                let value = if let FlowFact::ByteCallable(function, None) = facts.fact(value)? {
                    let function = *function;
                    if application.arguments().len() != 1
                        || !application.row_arguments().is_empty()
                        || !same(&application.arguments()[0], &header.original.state.ty, work)?
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
        EffectExprKind::Operation(EffectOperation::Request(request)) => {
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
            if phase == SourceResourcePhase::Handler {
                return Err(invalid());
            }
            let expected = if phase == SourceResourcePhase::Acquire {
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
                if phase == SourceResourcePhase::Acquire {
                    if path.acquired || !facts.borrowed(operand, false, header, work)? {
                        return Err(invalid());
                    }
                    let refusal = facts.wrapped(call.conversion_failed, 0, work)?;
                    push(&mut results, (refusal, path.copy(work)?), work)?;
                    let null = facts.add(
                        FlowFact::Constructor(codec.nullable_constructors()[0], None),
                        work,
                    )?;
                    let readable = facts.wrapped(codec.output_constructors()[1], null, work)?;
                    let returned = facts.wrapped(call.returned, readable, work)?;
                    push(&mut results, (returned, path.copy(work)?), work)?;
                    path.acquired = true;
                    let nonnull = facts.wrapped(codec.nullable_constructors()[1], 1, work)?;
                    let readable = facts.wrapped(codec.output_constructors()[1], nonnull, work)?;
                    let returned = facts.wrapped(call.returned, readable, work)?;
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
                    push(&mut results, (blocked, path.copy(work)?), work)?;
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
                        let mut recorded = path.copy(work)?;
                        recorded.consumed = consumes;
                        if readable {
                            let disposition = facts.wrapped(
                                codec.disposition_constructors()[usize::from(!consumes)],
                                0,
                                work,
                            )?;
                            let returned = facts.wrapped(call.returned, disposition, work)?;
                            push(&mut results, (returned, recorded), work)?;
                        } else {
                            let refusal = facts.wrapped(call.conversion_failed, 0, work)?;
                            push(&mut results, (refusal, recorded), work)?;
                        }
                    }
                }
            }
            Ok(results)
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
    work: &mut TypeWorkBudget,
) -> Result<Box<[SourceByteCall]>, ValidationError> {
    let mut facts = facts(work)?;
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
    for (value, path) in results {
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
    Ok(facts.byte_calls.into_boxed_slice())
}
fn check_handler(
    program: &UnvalidatedEffectProgram,
    header: &CheckedSourceResourceHeader,
    state: &TypedBinder,
    body: NodeId,
    answer: crate::resolved::BinderId,
    work: &mut TypeWorkBudget,
) -> Result<Box<[SourceByteCall]>, ValidationError> {
    let mut facts = facts(work)?;
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
    Ok(facts.byte_calls.into_boxed_slice())
}

/// Complete compiler claim for one immutable defining forest. This is not an
/// executable receipt; final Core reconstructs the relation independently.
pub(crate) struct SourceResourceCopyClaim<'a> {
    pub(crate) nodes: &'a [(NodeId, NodeId)],
    pub(crate) freshening: super::provider::ProviderFreshening<'a>,
    pub(crate) substitution: super::provider::ProviderTemplateSubstitution<'a>,
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
        if !claim.freshening.nominals.is_empty()
            || !claim.freshening.lexicals.is_empty()
            || !claim.substitution.pending.is_empty()
        {
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
        Ok(Self {
            nodes: pairs(claim.nodes, work)?,
            binders: pairs(claim.freshening.binders, work)?,
            variables: variables.into_boxed_slice(),
            handlers: pairs(claim.freshening.handlers, work)?,
            resumes: pairs(claim.freshening.resumes, work)?,
            types: types.into_map(),
            rows,
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
            let symbol = if effect.instance.effect() == template.header.acquire.effect() {
                Arc::clone(&template.header.acquire)
            } else {
                Arc::clone(&template.header.teardown)
            };
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
                    .ok_or_else(exhausted)?,
            )
            .map_err(|_| exhausted())?;
            for actual in copy.types.values_mut() {
                let replacement = rewrite(actual)?;
                crate::types::replace_type_iteratively(actual, replacement);
            }
            for actual in copy.rows.values_mut() {
                *actual = rewrite_row(actual)?;
            }
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
        static PENDING: std::sync::OnceLock<
            HashMap<crate::types::InferenceVariableId, crate::types::EffectRow>,
        > = std::sync::OnceLock::new();
        let pending = PENDING.get_or_init(HashMap::new);
        std::array::from_fn(|index| {
            let copy = &self.descriptor.copies[index];
            SourceResourceCopyClaim {
                nodes: &copy.nodes,
                freshening: copy.fresh(),
                substitution: super::provider::ProviderTemplateSubstitution {
                    types: &copy.types,
                    rows: &copy.rows,
                    pending,
                },
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
        acquire: bool,
        work: &mut TypeWorkBudget,
    ) -> Result<bool, ValidationError> {
        let copy = &self.descriptor.copies[usize::from(!acquire)];
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
        let expected = if acquire {
            &self.header().acquire
        } else {
            &self.header().teardown
        };
        if call.operation() != expected.operation() {
            return Ok(false);
        }
        for interpretation in self.native_interpretations() {
            if Arc::ptr_eq(interpretation.symbol(), expected)
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
                &self.header().acquire,
            ),
            (
                1,
                self.original().original_finish(),
                &self.header().teardown,
            ),
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
                if original_call.operation() != expected.operation()
                    || call.operation() != expected.operation()
                {
                    return Err(invalid());
                }
                let mut covered = false;
                for interpretation in self.native_interpretations() {
                    charge(work, 1)?;
                    if Arc::ptr_eq(interpretation.symbol(), expected)
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
        let inventories = [
            source_inventory(template, 0, &self.descriptor.copies[0], work)?,
            source_inventory(template, 1, &self.descriptor.copies[1], work)?,
            source_inventory(template, 2, &self.descriptor.copies[2], work)?,
        ];
        let mut original_binders = std::collections::HashSet::new();
        let mut original_types = std::collections::HashSet::new();
        let mut original_handlers = std::collections::HashSet::new();
        let mut original_resumes = std::collections::HashSet::new();
        for inventory in &inventories {
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
            let inventory = &inventories[phase];
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
                let mut expected =
                    crate::types::clone_effect_row_with_budget(self.handler_output.effects(), work)
                        .map_err(|_| resource())?;
                let original_direct = template.handler_direct_row(work)?;
                let direct = crate::types::substitute_row_for_template_with(
                    &original_direct,
                    &copy.types,
                    &copy.rows,
                    &HashMap::new(),
                    &crate::types::TemplateIdentityRenaming {
                        variables: &HashMap::new(),
                        nominals: &HashMap::new(),
                    },
                    |cells| work.charge(cells).map_err(|_| resource()),
                    resource,
                )?
                .map_err(|_| invalid())?;
                for effect in direct.known() {
                    expected = expected
                        .remove_exact_with_budget(effect, work)
                        .map_err(|_| resource())?
                        .map_err(|_| invalid())?;
                }
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
                    let expected_symbol =
                        if original.instance.effect() == template.header.acquire.effect() {
                            &template.header.acquire
                        } else if original.instance.effect() == template.header.teardown.effect() {
                            &template.header.teardown
                        } else {
                            return Err(invalid());
                        };
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
            let mut reachable = std::collections::HashSet::new();
            let mut pending_nodes = Vec::new();
            if phase < 2 {
                push(&mut pending_nodes, root, work)?;
            } else {
                for clause in template.original_handler_node().clauses() {
                    push(&mut pending_nodes, clause.body(), work)?;
                }
            }
            while let Some(source) = pending_nodes.pop() {
                charge(work, 1)?;
                reachable.try_reserve(1).map_err(|_| resource())?;
                if !reachable.insert(source) {
                    continue;
                }
                let stored = node(original, source)?;
                for child in 0..stored.kind.child_count() {
                    push(
                        &mut pending_nodes,
                        stored.kind.child_at(child).ok_or_else(invalid)?,
                        work,
                    )?;
                }
            }
            if reachable.len() != copy.nodes.len() {
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
                if !reachable.contains(source) {
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
            let pending = HashMap::new();
            let renaming = crate::types::TemplateIdentityRenaming {
                variables: &variables,
                nominals: &nominals,
            };
            let substitution = super::provider::ProviderTemplateSubstitution {
                types: &copy.types,
                rows: &copy.rows,
                pending: &pending,
            };
            let fresh = copy.fresh();
            fresh.authenticate(work)?;
            for (source, target) in &copy.nodes {
                let expected =
                    super::provider::projection::project(*source, node(original, *source)?, work)?;
                let expected = super::provider::specialization::specialize_projection(
                    &expected,
                    &mappings,
                    &fresh,
                    &substitution,
                    &renaming,
                    work,
                )?;
                let actual =
                    super::provider::projection::project(*target, node(program, *target)?, work)?;
                if !expected.same(&actual, work)? {
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
            let expected = super::provider::specialization::specialize_projection(
                &expected,
                &mappings,
                &fresh,
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
                let expected = super::provider::specialization::specialize_projection(
                    &expected,
                    &mappings,
                    &fresh,
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
                            &pending,
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
                    let expected = super::provider::specialization::specialize_projection(
                        &super::provider::projection::project_clause(original, work)?,
                        &mappings,
                        &fresh,
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
fn source_inventory(
    template: &CheckedSourceResourceTemplate,
    phase: usize,
    copy: &SourceResourceCopy,
    work: &mut TypeWorkBudget,
) -> Result<super::provider::specialization::ProviderLocalInventory, ValidationError> {
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
    let pending = HashMap::new();
    let sigma = super::provider::ProviderTemplateSubstitution {
        types: &copy.types,
        rows: &copy.rows,
        pending: &pending,
    };
    let handler_patterns = [template.handler_pattern()];
    super::provider::source_resource_local_identities(
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
            let scope = forged
                .nodes
                .iter_mut()
                .find_map(|node| match &mut node.kind {
                    EffectExprKind::Operation(EffectOperation::SourceResourceScope(scope)) => {
                        Some(scope)
                    }
                    _ => None,
                })
                .unwrap();
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
            assert_eq!(
                error.reason(),
                ValidationReason::Registry,
                "mutation {mutation}: {error:?}"
            );
        }
        println!(
            "source control independent Core work={cost}; exact/one-short/prefix/two fresh retries and three original-claim refusals"
        );
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
                    Type::Nominal(nominal) if !registry.source_owner_nominal(*nominal)
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
        assert!(
            failure.node().is_some(),
            "standalone owner code must identify the refused Core boundary"
        );
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
            assert!(
                super::super::validate::validate_effect_modules_family(
                    transformed,
                    &sources,
                    &module_sources
                )
                .is_err(),
                "scope claim mutation {mutation} must fail independent admission"
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
}
