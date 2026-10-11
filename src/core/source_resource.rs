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

fn charge(work: &mut TypeWorkBudget, count: usize) -> Result<(), ValidationError> {
    work.charge(count).map_err(|()| resource())
}

/// Exact library ADT roles, separate from ordinary constructor spellings.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct SourceResourceCodec {
    pub(crate) acquire: [ConstructorId; 2],
    pub(crate) finish: [ConstructorId; 3],
    pub(crate) scope: [ConstructorId; 2],
    pub(crate) completion: [ConstructorId; 3],
}

/// A completed header phase, retaining original immutable source authority.
/// Only lifecycle and final-scope validation can supply execution permission.
#[derive(Debug)]
pub(crate) struct CheckedSourceResourceHeader {
    pub(crate) original: Arc<SourceResourceTypeFact>,
    pub(crate) owner: Arc<CheckedForeignOwner>,
    pub(crate) acquire: Arc<CheckedForeignSymbol>,
    pub(crate) teardown: Arc<CheckedForeignSymbol>,
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
            || header.codec.kind != SurfaceResourceReportCodecKind::Scope
            || header
                .parameters
                .get(header.owned_position)
                .is_none_or(|parameter| parameter.kind != Kind::Type)
        {
            return Err(invalid());
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
            || scope_arguments.len() != 3
            || !same(acquisition_arguments[0], &header.state.ty, work)?
            || !same(acquisition_arguments[1], &header.data.ty, work)?
            || !same(finish_arguments[0], &header.state.ty, work)?
            || !same(acquisition_arguments[2], scope_arguments[0], work)?
            || !same(finish_arguments[1], scope_arguments[1], work)?
            || !variable(scope_arguments[2], header.answer.id)
        {
            return Err(invalid());
        }
        let acquire_codec = acquire_codec(acquisition, registry, work)?;
        let finish_codec = finish_codec(finish, registry, work)?;
        let (scope_codec, completion_codec) = report_codec(scope, registry, work)?;
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
                | PreparedOwnerCall::Teardown { application, .. } => application.arguments(),
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
                PreparedOwnerCall::Teardown { .. } if tearing_down.is_none() => {
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
        if owner.owner().representation()
            != crate::foreign::source_contract::PreparedAddressRepresentation::Opaque
            || teardown.symbol().result()
                != crate::foreign::source_contract::PreparedAbiResult::Void
            || teardown.symbol().operands().len() != 1
        {
            return Err(invalid());
        }
        let owned = header.parameters[header.owned_position].id;
        for ty in [&header.input.ty, &header.data.ty] {
            if crate::types::visit_type_structure_with_budget(ty, work, |node, _| {
                Ok(match node {
                    crate::types::TypeStructureNode::Type(Type::Variable(id)) => *id == owned,
                    crate::types::TypeStructureNode::Type(Type::Nominal(id)) => {
                        registry.source_owner_nominal(*id)
                    }
                    _ => false,
                })
            })
            .map_err(|_| resource())?
            {
                return Err(invalid());
            }
        }
        charge(work, 1)?;
        Ok(Self {
            original: Arc::clone(header),
            owner: Arc::clone(owner),
            acquire,
            teardown,
            codec: SourceResourceCodec {
                acquire: acquire_codec,
                finish: finish_codec,
                scope: scope_codec,
                completion: completion_codec,
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
    if abstraction.parameters().len() != header.parameters.len() + usize::from(answer) {
        return Err(invalid());
    }
    for ((id, kind), formal) in abstraction.parameters().iter().zip(&header.parameters) {
        if *id != formal.id || *kind != formal.kind {
            return Err(invalid());
        }
    }
    if answer && abstraction.parameters().last() != Some(&(header.answer.id, Kind::Type)) {
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
        // Ordinary graph, kind, scope, effect, registry and provenance checking
        // precedes the resource-specific phase and owner-lineage proof.
        for (program, answer) in [(&acquire, false), (&finish, false), (&handler, true)] {
            if !Arc::ptr_eq(&program.registry, &acquire.registry) {
                return Err(invalid());
            }
            super::validate::check_source_resource_structure(
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
        if !Arc::ptr_eq(&canonical.owner, &header.owner) || canonical.codec != header.codec {
            return Err(invalid());
        }
        check_provider_association(&header, &handler, work)?;
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
            || codomain.effects().tail().is_some()
            || codomain.effects().known().len() != 1
            || crate::types::compare_effect_instances_with_budget(
                &codomain.effects().known()[0],
                &header.original.provided.instance,
                work,
            )
            .map_err(|_| resource())?
                != std::cmp::Ordering::Equal
        {
            return Err(invalid());
        }
        let placeholder_binder = answer.parameter().id();
        let handler_body = answer.body();
        check_flow(&acquire, &header, &acquire_entry, Phase::Acquire, work)?;
        check_flow(&finish, &header, &finish_entry, Phase::Finish, work)?;
        check_handler(
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
        })
    }
    pub(crate) fn header(&self) -> &Arc<CheckedSourceResourceHeader> {
        &self.header
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
enum Phase {
    Acquire,
    Finish,
    Handler,
}
// Flat symbolic records: tuples and constructors retain scalar indices only.
// No symbolic value, failure path or arena disposal recurses through host heaps.
#[derive(Debug)]
enum FlowFact {
    Independent,
    Fresh,
    Current,
    Tuple(Box<[usize]>),
    Constructor(ConstructorId, Option<usize>),
    Callable(ConstructorId),
}
#[derive(Default)]
struct FlowFacts {
    values: Vec<FlowFact>,
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
impl FlowFacts {
    fn add(
        &mut self,
        value: FlowFact,
        work: &mut TypeWorkBudget,
    ) -> Result<usize, ValidationError> {
        let id = self.values.len();
        push(&mut self.values, value, work)?;
        Ok(id)
    }
    fn fact(&self, id: usize) -> Result<&FlowFact, ValidationError> {
        self.values.get(id).ok_or_else(invalid)
    }
    fn independent(&self, id: usize, work: &mut TypeWorkBudget) -> Result<bool, ValidationError> {
        let mut pending = one(id, work)?;
        while let Some(id) = pending.pop() {
            charge(work, 1)?;
            match self.fact(id)? {
                FlowFact::Independent => {}
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
fn bind_pattern(
    pattern: &CorePattern,
    value: usize,
    path: &mut FlowPath,
    facts: &FlowFacts,
    depth: usize,
    work: &mut TypeWorkBudget,
) -> Result<bool, ValidationError> {
    charge(work, 1)?;
    if depth > 64 {
        return Err(resource());
    }
    Ok(match &pattern.kind {
        CorePatternKind::Binder(binder) => {
            path.bind(binder.id(), value, work)?;
            true
        }
        CorePatternKind::Wildcard => true,
        CorePatternKind::Unit | CorePatternKind::Boolean(_) => facts.independent(value, work)?,
        CorePatternKind::Tuple(patterns) => match facts.fact(value)? {
            FlowFact::Tuple(values) => {
                if values.len() != patterns.len() {
                    false
                } else {
                    let mut matches = true;
                    for (pattern, value) in patterns.iter().zip(values.iter()) {
                        matches &= bind_pattern(pattern, *value, path, facts, depth + 1, work)?;
                    }
                    matches
                }
            }
            FlowFact::Independent => {
                let mut matches = true;
                for pattern in patterns {
                    matches &= bind_pattern(pattern, value, path, facts, depth + 1, work)?;
                }
                matches
            }
            _ => false,
        },
        CorePatternKind::Constructor {
            constructor,
            payload,
        } => match facts.fact(value)? {
            FlowFact::Constructor(actual, value) if actual == constructor => {
                match (payload.as_deref(), value) {
                    (Some(pattern), Some(value)) => {
                        bind_pattern(pattern, *value, path, facts, depth + 1, work)?
                    }
                    (None, None) => true,
                    _ => false,
                }
            }
            FlowFact::Independent => {
                if let Some(payload) = payload {
                    bind_pattern(payload, value, path, facts, depth + 1, work)?
                } else {
                    true
                }
            }
            _ => false,
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
fn eval_flow(
    program: &UnvalidatedEffectProgram,
    header: &CheckedSourceResourceHeader,
    id: NodeId,
    phase: Phase,
    path: FlowPath,
    facts: &mut FlowFacts,
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
            let value = *path.locals.get(&local.binder()).ok_or_else(invalid)?;
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
                let FlowFact::Callable(constructor) = facts.fact(function)? else {
                    return Err(invalid());
                };
                let constructor = *constructor;
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
                    let value = facts.wrapped(constructor, argument, work)?;
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
        ))) => eval_flow(
            program,
            header,
            application.function(),
            phase,
            path,
            facts,
            depth + 1,
            work,
        ),
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
                    if bind_pattern(arm.pattern(), value, &mut candidate, facts, 0, work)? {
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
                        if !facts.independent(value, work)? {
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
            if phase == Phase::Handler {
                return Err(invalid());
            }
            let expected = if phase == Phase::Acquire {
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
                if phase == Phase::Acquire {
                    if path.acquired || !facts.independent(operand, work)? {
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
                    if path.consumed {
                        return Err(invalid());
                    }
                    let Some(PreparedOwnerCall::Teardown {
                        current_operand, ..
                    }) = expected.owner_role()
                    else {
                        return Err(invalid());
                    };
                    let Some(crate::foreign::source_contract::PreparedOperandSource::Current(
                        selection,
                    )) = expected
                        .symbol()
                        .operands()
                        .get(*current_operand)
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
                    let refusal = facts.wrapped(call.conversion_failed, 0, work)?;
                    push(&mut results, (refusal, path.copy(work)?), work)?;
                    path.consumed = true;
                    let consumed = facts.wrapped(codec.disposition_constructors()[0], 0, work)?;
                    let returned = facts.wrapped(call.returned, consumed, work)?;
                    push(&mut results, (returned, path), work)?;
                }
            }
            Ok(results)
        }
        EffectExprKind::Operation(EffectOperation::Resume(resume)) if phase == Phase::Handler => {
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
                if !facts.independent(value, work)? {
                    return Err(invalid());
                }
                push(&mut results, (0, path), work)?;
            }
            Ok(results)
        }
        _ => Err(invalid()),
    }
}
fn facts(work: &mut TypeWorkBudget) -> Result<FlowFacts, ValidationError> {
    let mut facts = FlowFacts::default();
    for value in [FlowFact::Independent, FlowFact::Fresh, FlowFact::Current] {
        facts.add(value, work)?;
    }
    Ok(facts)
}
fn state_data(facts: &mut FlowFacts, work: &mut TypeWorkBudget) -> Result<usize, ValidationError> {
    let mut fields = Vec::new();
    push(&mut fields, 2, work)?;
    push(&mut fields, 0, work)?;
    facts.add(FlowFact::Tuple(fields.into_boxed_slice()), work)
}
fn check_flow(
    program: &UnvalidatedEffectProgram,
    header: &CheckedSourceResourceHeader,
    entry: &(TypedBinder, NodeId),
    phase: Phase,
    work: &mut TypeWorkBudget,
) -> Result<(), ValidationError> {
    let mut facts = facts(work)?;
    let value = if phase == Phase::Acquire {
        0
    } else {
        state_data(&mut facts, work)?
    };
    let mut path = FlowPath::new(work)?;
    path.bind(entry.0.id(), value, work)?;
    let results = eval_flow(program, header, entry.1, phase, path, &mut facts, 0, work)?;
    if results.is_empty() {
        return Err(invalid());
    }
    for (value, path) in results {
        match (phase, facts.fact(value)?) {
            (Phase::Acquire, FlowFact::Constructor(id, Some(payload)))
                if *id == header.codec.acquire[0] =>
            {
                let FlowFact::Tuple(fields) = facts.fact(*payload)? else {
                    return Err(invalid());
                };
                if !path.acquired
                    || fields.len() != 2
                    || !matches!(facts.fact(fields[0])?, FlowFact::Fresh)
                    || !facts.independent(fields[1], work)?
                {
                    return Err(invalid());
                }
            }
            (Phase::Acquire, FlowFact::Constructor(id, payload))
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
            (Phase::Finish, FlowFact::Constructor(id, None)) if *id == header.codec.finish[0] => {
                if !path.consumed {
                    return Err(invalid());
                }
            }
            (Phase::Finish, FlowFact::Constructor(id, Some(payload)))
                if *id == header.codec.finish[1] =>
            {
                if !path.consumed || !facts.independent(*payload, work)? {
                    return Err(invalid());
                }
            }
            (Phase::Finish, FlowFact::Constructor(id, Some(payload)))
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
    Ok(())
}
fn check_handler(
    program: &UnvalidatedEffectProgram,
    header: &CheckedSourceResourceHeader,
    state: &TypedBinder,
    body: NodeId,
    answer: crate::resolved::BinderId,
    work: &mut TypeWorkBudget,
) -> Result<(), ValidationError> {
    let mut facts = facts(work)?;
    let mut path = FlowPath::new(work)?;
    path.bind(state.id(), state_data(&mut facts, work)?, work)?;
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
        Phase::Handler,
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
    if !bind_pattern(arm.pattern(), value, &mut path, &facts, 0, work)? {
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
        bind_pattern(clause.pattern(), 0, &mut clause_path, &facts, 0, work)?;
        for (value, _) in eval_flow(
            program,
            header,
            clause.body(),
            Phase::Handler,
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
    Ok(())
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
        })
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
        if !Arc::ptr_eq(&header.owner, &template.header.owner)
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
            if copy.types.len() + copy.rows.len() != formals.len() + usize::from(phase == 2) {
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
        let input = crate::types::IterativeTypeOwner::new(specialized(
            &template.header.original.input.ty,
            work,
        )?);
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
        if !self.handler_output.effects().is_empty() {
            return Err(invalid());
        }
        Ok(())
    }
}

/// The first executable source association has one Unit operation and one
/// monomorphic access method. Multi-operation forwarding and non-Unit operand
/// conventions need their own source-authenticated forwarding evidence.
fn check_provider_association(
    checked_header: &CheckedSourceResourceHeader,
    program: &UnvalidatedEffectProgram,
    work: &mut TypeWorkBudget,
) -> Result<(), ValidationError> {
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
    if effect.operations.len() != 1
        || effect.parameters.len() != header.provided.instance.arguments().len()
    {
        return Err(invalid());
    }
    let catalog = program.method_evidence.methods();
    charge(work, catalog.len())?;
    let mut methods = catalog
        .iter()
        .filter(|method| method.id.interface() == interface);
    let method = methods.next().ok_or_else(invalid)?;
    if methods.next().is_some()
        || !method.parameters.is_empty()
        || method.interface_parameters.as_ref() != signature.parameters.as_ref()
    {
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
    let method = crate::types::IterativeTypeOwner::new(specialized(&method.value_type, work)?);
    let operation = crate::types::IterativeTypeOwner::new(specialized(
        &effect.operations[0].annotation.ty,
        work,
    )?);
    let Some(method) = method.function_view() else {
        return Err(invalid());
    };
    let Some(operation) = operation.function_view() else {
        return Err(invalid());
    };
    if operation.domain() != &Type::Unit
        || operation.effects().is_some()
        || method.effects().is_some()
        || !same(method.value(), operation.value(), work)?
    {
        return Err(invalid());
    }
    let mut access = ArgumentsGuard(Vec::new());
    charge(work, header.parameters.len())?;
    access
        .0
        .try_reserve_exact(header.parameters.len())
        .map_err(|_| resource())?;
    for formal in &header.parameters {
        access.0.push(match formal.kind {
            Kind::Type => KindedArgument::TypeArg(Type::Variable(formal.id)),
            Kind::EffectRow => KindedArgument::RowArg(crate::types::EffectRow::open(
                crate::types::EffectRowVariable::Rigid(formal.id),
                Box::new([]),
            )),
            _ => return Err(invalid()),
        });
    }
    let access =
        crate::types::IterativeTypeOwner::new(checked_header.access_type(&access.0, work)?);
    if !same(method.domain(), &access, work)? {
        return Err(invalid());
    }
    Ok(())
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
    fn independently_revalidated_source_scope_rejects_incomplete_or_forged_claims() {
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
