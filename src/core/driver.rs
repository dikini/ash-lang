//! Untrusted actual driver-call coordinates. This witness grants no fact.
use super::*;

pub(in crate::core) struct DriverNomination<'a> {
    pub(in crate::core) definition: DefinitionCandidate,
    pub(in crate::core) captures: &'a [BinderId],
    pub(in crate::core) call: NodeId,
    pub(in crate::core) arity: usize,
    pub(in crate::core) ledger_field: usize,
}

/// Exact source coordinates for an actual linked driver call and its Ledger
/// parameter. All normal-return/currentness/provider claims are separate.
pub(in crate::core) struct CheckedDriverCall<'a> {
    definition: CheckedStoredFunction<'a>,
    argument: CheckedPersistentTuple<'a>,
    call: NodeId,
    formal: BinderId,
    type_parameters: Vec<crate::types::TypeVariableId>,
    input_role: BinderId,
    field: usize,
}

pub(in crate::core) fn check_nominated_driver_call<'a>(
    program: &'a dyn LedgerArena,
    linked: &'a ValidatedInterfaceProgram,
    plan: &DriverNomination<'_>,
    work: &mut TypeWorkBudget,
) -> Result<CheckedDriverCall<'a>, Rejection> {
    if plan.arity == 0 || plan.ledger_field >= plan.arity {
        return Err(Rejection::Unsupported);
    }
    let initializer = linked_initializer(program, linked, plan.definition, work)?;
    reject_evidence(program, &[initializer], work)?;
    let mut inspect = CoreInspection { program, work };
    let mut body = initializer;
    let mut parameter_count = 0usize;
    let mut type_parameters = Vec::new();
    while let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::TypeAbstraction(
        abstraction,
    ))) = inspect.kind(body)?
    {
        inspect
            .work
            .charge(
                abstraction
                    .parameters()
                    .len()
                    .checked_add(1)
                    .ok_or(Rejection::Exhausted)?,
            )
            .map_err(|()| Rejection::Exhausted)?;
        parameter_count = parameter_count
            .checked_add(abstraction.parameters().len())
            .ok_or(Rejection::Exhausted)?;
        type_parameters
            .try_reserve(abstraction.parameters().len())
            .map_err(|_| Rejection::Exhausted)?;
        type_parameters.extend(
            abstraction
                .parameters()
                .iter()
                .map(|(parameter, _)| *parameter),
        );
        body = abstraction.body();
    }
    let definition = inspect.stored_function_witness(body, plan.captures)?;
    let branch = inspect.branch(definition.body)?;
    expect_variable(&mut inspect, branch.scrutinee(), definition.parameter)?;
    let [arm] = branch.arms() else {
        return Err(Rejection::Unsupported);
    };
    let super::super::CorePatternKind::Tuple(formals) = &arm.pattern().kind else {
        return Err(Rejection::Unsupported);
    };
    if formals.len() != plan.arity {
        return Err(Rejection::Unsupported);
    }
    let formal = binder_pattern(
        formals
            .get(plan.ledger_field)
            .ok_or(Rejection::Unsupported)?,
    )?;
    inspect
        .work
        .charge(formals.len())
        .map_err(|()| Rejection::Exhausted)?;
    let mut all = Vec::new();
    all.try_reserve(
        formals
            .len()
            .checked_add(plan.captures.len())
            .and_then(|n| n.checked_add(1))
            .ok_or(Rejection::Exhausted)?,
    )
    .map_err(|_| Rejection::Exhausted)?;
    for pattern in formals.iter() {
        all.push(binder_pattern(pattern)?);
    }
    inspect
        .work
        .charge(
            plan.captures
                .len()
                .checked_add(1)
                .ok_or(Rejection::Exhausted)?,
        )
        .map_err(|()| Rejection::Exhausted)?;
    all.push(definition.parameter);
    all.extend_from_slice(plan.captures);
    require_distinct(inspect.work, &all)?;
    check_registration_contexts(inspect.work, &[definition.context_binder], &all)?;
    let application = inspect.application(plan.call)?;
    let mut callee = application.function();
    let mut actual_count = 0usize;
    while let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::TypeApplication(
        applied,
    ))) = inspect.kind(callee)?
    {
        let count = applied
            .arguments()
            .len()
            .checked_add(applied.row_arguments().len())
            .ok_or(Rejection::Exhausted)?;
        inspect
            .work
            .charge(count.checked_add(1).ok_or(Rejection::Exhausted)?)
            .map_err(|()| Rejection::Exhausted)?;
        actual_count = actual_count
            .checked_add(count)
            .ok_or(Rejection::Exhausted)?;
        callee = applied.function();
    }
    if actual_count != parameter_count || inspect.variable(callee)? != plan.definition.binder {
        return Err(Rejection::Unsupported);
    }
    let argument = inspect.persistent_tuple(application.argument(), None)?;
    if argument.api != definition.api || argument.fields.len() != plan.arity {
        return Err(Rejection::Unsupported);
    }
    let input = *argument
        .fields
        .get(plan.ledger_field)
        .ok_or(Rejection::Unsupported)?;
    let input_role = inspect.variable(input)?;
    Ok(CheckedDriverCall {
        definition,
        argument,
        call: plan.call,
        formal,
        type_parameters,
        input_role,
        field: plan.ledger_field,
    })
}

impl CheckedDriverCall<'_> {
    pub(in crate::core) fn call(&self) -> NodeId {
        self.call
    }
    pub(in crate::core) fn closure(&self) -> NodeId {
        self.definition.closure
    }
    pub(in crate::core) fn formal(&self) -> BinderId {
        self.formal
    }
    pub(in crate::core) fn type_parameters(&self) -> &[crate::types::TypeVariableId] {
        &self.type_parameters
    }
    pub(in crate::core) fn captures(&self) -> &[NodeId] {
        self.definition.captures
    }
    pub(in crate::core) fn input_role(&self) -> BinderId {
        self.input_role
    }
    pub(in crate::core) fn parameter_match(&self) -> NodeId {
        self.definition.body
    }
    pub(in crate::core) fn binding(&self) -> NodeId {
        self.argument.root
    }
    pub(in crate::core) fn tuple(&self) -> NodeId {
        self.argument.tuple
    }
    pub(in crate::core) fn fields(&self) -> &[NodeId] {
        self.argument.fields
    }
    pub(in crate::core) fn field(&self) -> usize {
        self.field
    }
    pub(in crate::core) fn provider_api(&self) -> crate::module::ModuleId {
        self.definition.api
    }
}

impl CheckedDriverCall<'_> {
    pub(in crate::core) fn definition_query(&self) -> NodeId {
        self.definition.query
    }
    pub(in crate::core) fn definition_binding(&self) -> NodeId {
        self.definition.root
    }
    pub(in crate::core) fn definition_context(&self) -> NodeId {
        self.definition.context
    }
    pub(in crate::core) fn definition_root(&self) -> NodeId {
        self.definition.root
    }
    pub(in crate::core) fn argument_field(&self) -> NodeId {
        self.argument.fields[self.field]
    }
}

/// Untrusted actual call to the scoped receive function. Its selected worker,
/// event alternatives and successful return are checked in the same focus.
pub(in crate::core) struct ReceiveNomination {
    pub(in crate::core) definition: DefinitionCandidate,
    pub(in crate::core) call: NodeId,
}

pub(in crate::core) struct CheckedReceiveCall<'a> {
    definition: CheckedStoredFunction<'a>,
    type_parameters: Vec<crate::types::TypeVariableId>,
    call: NodeId,
}

pub(in crate::core) fn check_nominated_receive_call<'a>(
    program: &'a dyn LedgerArena,
    linked: &'a ValidatedInterfaceProgram,
    plan: &ReceiveNomination,
    work: &mut TypeWorkBudget,
) -> Result<CheckedReceiveCall<'a>, Rejection> {
    let initializer = linked_initializer(program, linked, plan.definition, work)?;
    let mut inspect = CoreInspection { program, work };
    let mut body = initializer;
    let mut parameters = 0usize;
    let mut type_parameters = Vec::new();
    while let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::TypeAbstraction(
        abstraction,
    ))) = inspect.kind(body)?
    {
        inspect
            .work
            .charge(
                abstraction
                    .parameters()
                    .len()
                    .checked_add(1)
                    .ok_or(Rejection::Exhausted)?,
            )
            .map_err(|()| Rejection::Exhausted)?;
        parameters = parameters
            .checked_add(abstraction.parameters().len())
            .ok_or(Rejection::Exhausted)?;
        type_parameters
            .try_reserve(abstraction.parameters().len())
            .map_err(|_| Rejection::Exhausted)?;
        type_parameters.extend(
            abstraction
                .parameters()
                .iter()
                .map(|(parameter, _)| *parameter),
        );
        body = abstraction.body();
    }
    let definition = inspect.stored_function_witness(body, &[])?;
    let application = inspect.application(plan.call)?;
    let mut callee = application.function();
    let mut arguments = 0usize;
    while let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::TypeApplication(
        applied,
    ))) = inspect.kind(callee)?
    {
        let count = applied
            .arguments()
            .len()
            .checked_add(applied.row_arguments().len())
            .ok_or(Rejection::Exhausted)?;
        inspect
            .work
            .charge(count.checked_add(1).ok_or(Rejection::Exhausted)?)
            .map_err(|()| Rejection::Exhausted)?;
        arguments = arguments.checked_add(count).ok_or(Rejection::Exhausted)?;
        callee = applied.function();
    }
    if arguments != parameters || inspect.variable(callee)? != plan.definition.binder {
        return Err(Rejection::Unsupported);
    }
    Ok(CheckedReceiveCall {
        definition,
        type_parameters,
        call: plan.call,
    })
}

impl CheckedReceiveCall<'_> {
    pub(in crate::core) fn call(&self) -> NodeId {
        self.call
    }
    pub(in crate::core) fn closure(&self) -> NodeId {
        self.definition.closure
    }
    pub(in crate::core) fn definition_query(&self) -> NodeId {
        self.definition.query
    }
    pub(in crate::core) fn definition_binding(&self) -> NodeId {
        self.definition.root
    }
    pub(in crate::core) fn definition_context(&self) -> NodeId {
        self.definition.context
    }
    pub(in crate::core) fn definition_body(&self) -> NodeId {
        self.definition.body
    }
    pub(in crate::core) fn type_parameters(&self) -> &[crate::types::TypeVariableId] {
        &self.type_parameters
    }
    pub(in crate::core) fn provider_api(&self) -> crate::module::ModuleId {
        self.definition.api
    }
}
