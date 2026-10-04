//! Exact declaration entry for unpublished generic lifecycle code.
//!
//! The defining resolved declaration is supplied by the caller's local module
//! transaction. This proof grants no exported descriptor or runtime authority.

use super::super::NodeId;
use super::{
    BinderId, ConstructorId, EffectExprKind, ForeignResultFact, HashMap, HashSet, LifecyclePhase,
    NativeFacts, NominalTypeId, PureComputation, PureExprKind, PureValue, Type, TypeWorkBudget,
    UnvalidatedEffectProgram, ValidationError, charge, contains_state, invalid, node, resource,
    same_type_with_budget,
};
#[cfg(test)]
use super::{EffectInstance, EffectOperationFamily};
use crate::{
    resolved::{ProviderTemplateId, ResolvedResourceDefinition, same_origin_with_budget},
    types::{
        EffectRowVariable, IterativeTypeOwner, Kind, TypeVariableId, clone_effect_row_with_budget,
        clone_type_with_budget, same_kind_with_budget, same_kinded_type_parameters_with_budget,
        substitute_type_variables_with,
    },
};

#[cfg(test)]
pub(crate) enum EntryMutation {
    RootType,
    FunctionType,
    RootRow,
    FunctionRow,
    ErrorApplication,
    ParameterClass(Vec<(TypeVariableId, TypeVariableId)>),
}

#[cfg(test)]
pub(crate) fn mutate_entry_for_test(
    program: &mut UnvalidatedEffectProgram,
    mutation: EntryMutation,
) {
    let root_index = program.root.index().unwrap();
    let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::TypeAbstraction(
        abstraction,
    ))) = &program.nodes[root_index].kind
    else {
        unreachable!()
    };
    let function_index = abstraction.body().index().unwrap();
    let EffectExprKind::Pure(PureExprKind::Value(PureValue::Function(function))) =
        &program.nodes[function_index].kind
    else {
        unreachable!()
    };
    let body_index = function.body().index().unwrap();
    let row = crate::types::EffectRow::closed(Box::new([EffectInstance::new(
        crate::types::EffectId::new(crate::module::ModuleId::new(77), 0),
        Box::new([]),
    )]));
    match mutation {
        EntryMutation::RootType => program.nodes[root_index].ty = Type::Int,
        EntryMutation::FunctionType => program.nodes[function_index].ty = Type::Int,
        EntryMutation::RootRow => program.nodes[root_index].effects = row,
        EntryMutation::FunctionRow => program.nodes[function_index].effects = row,
        EntryMutation::ErrorApplication => {
            let Type::Application(_, error) = &mut program.nodes[body_index].ty else {
                unreachable!()
            };
            **error = Type::Application(Box::new((**error).clone()), Box::new(Type::Int));
            refresh_envelope_for_test(program, root_index, function_index, body_index);
        }
        EntryMutation::ParameterClass(mapping) => {
            let substitutions = mapping
                .iter()
                .map(|(source, actual)| (*source, Type::Variable(*actual)))
                .collect::<HashMap<_, _>>();
            let rewrite = |ty: &Type| {
                substitute_type_variables_with(ty, &substitutions, |_| Ok(()), || ()).unwrap()
            };
            for stored in &mut program.nodes {
                if !matches!(stored.ty, Type::Forall(_, _)) {
                    stored.ty = rewrite(&stored.ty);
                }
                stored.effects = stored
                    .effects
                    .substitute_type_variables_with_budget(
                        &substitutions,
                        &mut TypeWorkBudget::unbounded(),
                    )
                    .unwrap();
                <EffectOperationFamily as crate::core::dialect::CoreOperationFamily>::rewrite_operation_type_metadata(&mut stored.kind, &mut |ty| Ok(rewrite(ty)), &mut |_| Ok(())).unwrap();
                if let EffectExprKind::Pure(PureExprKind::Value(PureValue::Function(function))) =
                    &stored.kind
                {
                    let mut parameter = function.parameter().clone();
                    parameter.rewrite_type(&mut |ty| Ok(rewrite(ty))).unwrap();
                    stored.kind = EffectExprKind::Pure(PureExprKind::Value(PureValue::Function(
                        super::super::function::FunctionNode::new(parameter, function.body()),
                    )));
                }
            }
            let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::TypeAbstraction(
                abstraction,
            ))) = &program.nodes[root_index].kind
            else {
                unreachable!()
            };
            let parameters = abstraction
                .parameters()
                .iter()
                .map(|(id, kind)| {
                    (
                        mapping
                            .iter()
                            .find(|(source, _)| source == id)
                            .map_or(*id, |(_, actual)| *actual),
                        kind.clone(),
                    )
                })
                .collect();
            program.nodes[root_index].kind = EffectExprKind::Pure(PureExprKind::Computation(
                PureComputation::TypeAbstraction(super::super::type_ops::TypeAbstractionNode::new(
                    parameters,
                    abstraction.body(),
                )),
            ));
            refresh_envelope_for_test(program, root_index, function_index, body_index);
        }
    }
}

#[cfg(test)]
fn refresh_envelope_for_test(
    program: &mut UnvalidatedEffectProgram,
    root: usize,
    function: usize,
    body: usize,
) {
    let EffectExprKind::Pure(PureExprKind::Value(PureValue::Function(function_node))) =
        &program.nodes[function].kind
    else {
        unreachable!()
    };
    program.nodes[function].ty = Type::function_computation(
        function_node.parameter().ty().clone(),
        crate::types::ComputationType::new(
            program.nodes[body].ty.clone(),
            program.nodes[body].effects.clone(),
        ),
    );
    let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::TypeAbstraction(
        abstraction,
    ))) = &program.nodes[root].kind
    else {
        unreachable!()
    };
    program.nodes[root].ty = Type::Forall(
        abstraction.parameters().to_vec().into_boxed_slice(),
        Box::new(program.nodes[function].ty.clone()),
    );
}

/// Borrowed body-free declaration relation. Source admission and retained-proof
/// authentication provide this view through distinct constructors.
pub(crate) struct LifecycleDefinitionView<'a> {
    id: crate::resolved::ResourceDefinitionId,
    family: NominalTypeId,
    parameters: &'a [crate::resolved::ResolvedTypeVariable],
    answer: &'a crate::resolved::ResolvedTypeVariable,
    input: &'a crate::resolved::ResolvedType,
    state: &'a crate::resolved::ResolvedType,
    result: &'a crate::resolved::ResolvedType,
    interpreted: &'a crate::resolved::ResolvedEffectInstance,
    origin: &'a crate::source::Origin,
    parameter: BinderId,
    parameter_origin: &'a crate::source::Origin,
}
impl<'a> LifecycleDefinitionView<'a> {
    pub(crate) fn source(
        definition: &'a ResolvedResourceDefinition,
        phase: LifecyclePhase,
    ) -> Self {
        let parameter = match phase {
            LifecyclePhase::Acquire => &definition.acquire_binder,
            LifecyclePhase::Finish => &definition.finish_binder,
        };
        Self {
            id: definition.id,
            family: definition.family,
            parameters: &definition.parameters,
            answer: &definition.answer,
            input: &definition.input,
            state: &definition.state,
            result: &definition.result,
            interpreted: &definition.interpreted,
            origin: &definition.origin,
            parameter: parameter.id,
            parameter_origin: &parameter.origin,
        }
    }
    pub(crate) fn retained(
        fact: &'a crate::resolved::ResourceTypeFact,
        parameter: BinderId,
        parameter_origin: &'a crate::source::Origin,
    ) -> Self {
        Self {
            id: fact.id,
            family: fact.family,
            parameters: &fact.parameters,
            answer: &fact.answer,
            input: &fact.input,
            state: &fact.state,
            result: &fact.result,
            interpreted: &fact.interpreted,
            origin: &fact.origin,
            parameter,
            parameter_origin,
        }
    }
}

pub(crate) struct LifecycleEntryContext<'a> {
    pub definition: LifecycleDefinitionView<'a>,
    pub template: ProviderTemplateId,
    pub phase: LifecyclePhase,
    pub body: NodeId,
    pub parameter: BinderId,
    pub hidden_answer: TypeVariableId,
    pub hidden_row: EffectRowVariable,
    pub formal_parameters: &'a [(TypeVariableId, TypeVariableId, Kind)],
}

pub(crate) fn check_lifecycle_entry(
    program: &UnvalidatedEffectProgram,
    context: &LifecycleEntryContext<'_>,
    work: &mut TypeWorkBudget,
) -> Result<(), ValidationError> {
    let definition = &context.definition;
    charge(work, definition.parameters.len())?;
    if definition
        .parameters
        .iter()
        .any(|parameter| parameter.id == definition.answer.id)
    {
        return Err(invalid(program.root));
    }
    let (ordinal, input, error_position) = match context.phase {
        LifecyclePhase::Acquire => (0, &definition.input.ty, 0),
        LifecyclePhase::Finish => (1, &definition.state.ty, 1),
    };
    charge(work, 1)?;
    if context.template != ProviderTemplateId::new(definition.id, ordinal)
        || context.parameter != definition.parameter
        || definition.parameter.module() != Some(definition.id.module())
        || definition.family.module() != definition.id.module()
        || definition.parameters.len() != context.formal_parameters.len()
        || definition
            .parameters
            .first()
            .is_none_or(|parameter| parameter.kind != Kind::Type)
    {
        return Err(invalid(program.root));
    }
    let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::TypeAbstraction(
        abstraction,
    ))) = &node(program, program.root)?.kind
    else {
        return Err(invalid(program.root));
    };
    let parameters = abstraction.parameters();
    if parameters.len()
        != context
            .formal_parameters
            .len()
            .checked_add(2)
            .ok_or_else(resource)?
    {
        return Err(invalid(program.root));
    }
    let mut substitutions = HashMap::new();
    let mut generated = HashSet::new();
    charge(
        work,
        context
            .formal_parameters
            .len()
            .checked_mul(2)
            .and_then(|count| count.checked_add(2))
            .ok_or_else(resource)?,
    )?;
    substitutions
        .try_reserve(context.formal_parameters.len())
        .map_err(|_| resource())?;
    generated
        .try_reserve(parameters.len())
        .map_err(|_| resource())?;
    for ((source, actual, kind), (canonical, (binder, binder_kind))) in context
        .formal_parameters
        .iter()
        .zip(definition.parameters.iter().zip(parameters))
    {
        charge(work, 1)?;
        if *source != canonical.id
            || actual != binder
            || !matches!(actual, TypeVariableId::Generated(_))
            || !same_kind_with_budget(kind, &canonical.kind, work).map_err(|()| resource())?
            || !same_kind_with_budget(binder_kind, &canonical.kind, work)
                .map_err(|()| resource())?
            || !generated.insert(*actual)
            || substitutions
                .insert(*source, Type::Variable(*actual))
                .is_some()
        {
            return Err(invalid(program.root));
        }
    }
    let answer = &parameters[context.formal_parameters.len()];
    let row = &parameters[context.formal_parameters.len() + 1];
    if answer.0 != context.hidden_answer
        || !matches!(answer.0, TypeVariableId::Generated(_))
        || !matches!(row.0, TypeVariableId::Generated(_))
        || context.hidden_row != EffectRowVariable::rigid(row.0)
        || !same_kind_with_budget(&answer.1, &Kind::Type, work).map_err(|()| resource())?
        || !same_kind_with_budget(&row.1, &Kind::EffectRow, work).map_err(|()| resource())?
        || !generated.insert(answer.0)
        || !generated.insert(row.0)
    {
        return Err(invalid(program.root));
    }
    let EffectExprKind::Pure(PureExprKind::Value(PureValue::Function(function))) =
        &node(program, abstraction.body())?.kind
    else {
        return Err(invalid(abstraction.body()));
    };
    if function.body() != context.body || function.parameter().id() != context.parameter {
        return Err(invalid(context.body));
    }
    for (actual, canonical) in [
        (
            node(program, program.root)?.origin.as_ref(),
            definition.origin,
        ),
        (
            node(program, abstraction.body())?.origin.as_ref(),
            definition.origin,
        ),
        (
            Some(function.parameter().origin()),
            definition.parameter_origin,
        ),
    ] {
        if !same_origin_with_budget(
            actual.ok_or_else(|| invalid(program.root))?,
            canonical,
            work,
        )
        .map_err(|()| resource())?
        {
            return Err(invalid(program.root));
        }
    }
    let substitute = |ty: &Type, work: &mut TypeWorkBudget| {
        substitute_type_variables_with(ty, &substitutions, |cells| work.charge(cells), || ())
            .map(IterativeTypeOwner::new)
            .map_err(|()| resource())
    };
    let expected_input = substitute(input, work)?;
    if !same_type_with_budget(function.parameter().ty(), &expected_input, work)
        .map_err(|()| resource())?
    {
        return Err(invalid(context.body));
    }
    let body = node(program, context.body)?;
    let function_node = node(program, abstraction.body())?;
    let root = node(program, program.root)?;
    if !root.effects.is_empty() || !function_node.effects.is_empty() {
        return Err(invalid(program.root));
    }
    let result_type =
        IterativeTypeOwner::new(clone_type_with_budget(&body.ty, work).map_err(|()| resource())?);
    let effects = clone_effect_row_with_budget(&body.effects, work).map_err(|()| resource())?;
    charge(work, 1)?;
    let expected_function = IterativeTypeOwner::new(Type::function_computation(
        expected_input.into_inner(),
        crate::types::ComputationType::new(result_type.into_inner(), effects),
    ));
    if !same_type_with_budget(&function_node.ty, &expected_function, work)
        .map_err(|()| resource())?
    {
        return Err(invalid(abstraction.body()));
    }
    let Type::Forall(root_parameters, root_body) = &root.ty else {
        return Err(invalid(program.root));
    };
    if !same_kinded_type_parameters_with_budget(root_parameters, parameters, work)
        .map_err(|()| resource())?
        || !same_type_with_budget(root_body, &expected_function, work).map_err(|()| resource())?
    {
        return Err(invalid(program.root));
    }
    // The declaration codec's first two ordered arguments are the independent
    // initialization and completion error families. Its answer is separate.
    let Type::Application(scope, answer) = &definition.result.ty else {
        return Err(invalid(context.body));
    };
    if !same_type_with_budget(answer, &Type::Variable(definition.answer.id), work)
        .map_err(|()| resource())?
        || !same_kind_with_budget(&definition.answer.kind, &Kind::Type, work)
            .map_err(|()| resource())?
    {
        return Err(invalid(context.body));
    }
    let Type::Application(scope, completion_error) = scope.as_ref() else {
        return Err(invalid(context.body));
    };
    let Type::Application(scope, input_error) = scope.as_ref() else {
        return Err(invalid(context.body));
    };
    let Type::Nominal(scope) = scope.as_ref() else {
        return Err(invalid(context.body));
    };
    check_report_codec(program, *scope, context.body, work)?;
    let expected_error = substitute(
        if error_position == 0 {
            input_error
        } else {
            completion_error
        },
        work,
    )?;
    let state = substitute(&definition.state.ty, work)?;
    let native = NativeFacts::index(program, work)?;
    if contains_state(&native, &expected_error, work)? {
        return Err(invalid(context.body));
    }
    let body = node(program, context.body)?;
    let report = body
        .ty
        .outer_nominal()
        .ok_or_else(|| invalid(context.body))?;
    let declaration = program
        .registry
        .effect(definition.interpreted.instance.effect())
        .ok_or_else(|| invalid(context.body))?;
    let mut matched = false;
    for operation in &declaration.operations {
        charge(work, 1)?;
        let fact = native
            .operation(operation.id, work)?
            .ok_or_else(|| invalid(context.body))?;
        let (native_state, error, native_report) = match (&fact.result, context.phase) {
            (
                ForeignResultFact::Acquire {
                    state,
                    error,
                    report,
                    ..
                },
                LifecyclePhase::Acquire,
            )
            | (
                ForeignResultFact::Finish {
                    state,
                    error,
                    report,
                    ..
                },
                LifecyclePhase::Finish,
            ) => (state, error, report),
            _ => continue,
        };
        if Some(*native_state) == state.outer_nominal()
            && same_type_with_budget(&Type::Nominal(*error), &expected_error, work)
                .map_err(|()| resource())?
            && *native_report == report
        {
            matched = true;
        }
    }
    if !matched {
        return Err(invalid(context.body));
    }
    charge(work, 3)?;
    let expected = IterativeTypeOwner::new(Type::apply_arguments(
        Type::Nominal(report),
        [state.into_inner(), expected_error.into_inner()],
    ));
    if !same_type_with_budget(&body.ty, &expected, work).map_err(|()| resource())? {
        return Err(invalid(context.body));
    }
    Ok(())
}

fn check_report_codec(
    program: &UnvalidatedEffectProgram,
    scope: NominalTypeId,
    body: NodeId,
    work: &mut TypeWorkBudget,
) -> Result<(), ValidationError> {
    let registry = &program.registry;
    charge(work, registry.nominals().len())?;
    let nominal = registry
        .nominals()
        .iter()
        .find(|nominal| nominal.id == scope)
        .ok_or_else(|| invalid(body))?;
    let parameters = registry
        .nominal_parameters(scope)
        .ok_or_else(|| invalid(body))?;
    if nominal.declaration_kind != crate::resolved::ResolvedNominalDeclarationKind::Data
        || parameters.len() != 3
        || nominal.constructors.len() != 2
    {
        return Err(invalid(body));
    }
    for parameter in parameters {
        if !same_kind_with_budget(&parameter.kind, &Kind::Type, work).map_err(|()| resource())? {
            return Err(invalid(body));
        }
    }
    let payload = |ordinal: usize,
                   owner: NominalTypeId,
                   constructors: &[ConstructorId],
                   work: &mut TypeWorkBudget| {
        charge(work, 1)?;
        let id = *constructors.get(ordinal).ok_or_else(|| invalid(body))?;
        if id.owner() != owner
            || id.constructor() != u32::try_from(ordinal).map_err(|_| resource())?
        {
            return Err(invalid(body));
        }
        let constructor = registry.constructor(id).ok_or_else(|| invalid(body))?;
        if constructor.owner != owner {
            return Err(invalid(body));
        }
        Ok(constructor.payload.as_ref())
    };
    let failure = payload(0, scope, &nominal.constructors, work)?.ok_or_else(|| invalid(body))?;
    if !same_type_with_budget(failure, &Type::Variable(parameters[0].id), work)
        .map_err(|()| resource())?
    {
        return Err(invalid(body));
    }
    let Some(Type::Tuple(completed)) = payload(1, scope, &nominal.constructors, work)? else {
        return Err(invalid(body));
    };
    charge(work, completed.len())?;
    if completed.len() != 2
        || !same_type_with_budget(&completed[0], &Type::Variable(parameters[2].id), work)
            .map_err(|()| resource())?
    {
        return Err(invalid(body));
    }
    let Type::Application(completion, error) = &completed[1] else {
        return Err(invalid(body));
    };
    let Type::Nominal(completion) = completion.as_ref() else {
        return Err(invalid(body));
    };
    if !same_type_with_budget(error, &Type::Variable(parameters[1].id), work)
        .map_err(|()| resource())?
    {
        return Err(invalid(body));
    }
    charge(work, registry.nominals().len())?;
    let nominal = registry
        .nominals()
        .iter()
        .find(|nominal| nominal.id == *completion)
        .ok_or_else(|| invalid(body))?;
    let parameters = registry
        .nominal_parameters(*completion)
        .ok_or_else(|| invalid(body))?;
    if nominal.declaration_kind != crate::resolved::ResolvedNominalDeclarationKind::Data
        || parameters.len() != 1
        || nominal.constructors.len() != 3
        || !same_kind_with_budget(&parameters[0].kind, &Kind::Type, work)
            .map_err(|()| resource())?
    {
        return Err(invalid(body));
    }
    for ordinal in 0..3 {
        match payload(ordinal, *completion, &nominal.constructors, work)? {
            None if ordinal == 0 => {}
            Some(actual) if ordinal != 0 => {
                if !same_type_with_budget(actual, &Type::Variable(parameters[0].id), work)
                    .map_err(|()| resource())?
                {
                    return Err(invalid(body));
                }
            }
            _ => return Err(invalid(body)),
        }
    }
    Ok(())
}
