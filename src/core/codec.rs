//! Conditional reconstruction of linked network codec source.
//! These shape witnesses require independent provider and control checks and
//! do not by themselves issue codec or network authority.
use super::{
    BinderId, CheckedCounterIncrement, CheckedPersistentTuple, CheckedStoredFunction,
    CoreInspection, DefinitionCandidate, EffectExprKind, EffectOperation, LedgerArena, NodeId,
    PureComputation, PureExprKind, Rejection, TypeWorkBudget, ValidatedInterfaceProgram,
    acknowledgement, binder_pattern, bool_value, check_registration_contexts,
    checked_entry_default_handler, constructor_application, constructor_pattern, expect_variable,
    integer_equal, linked_initializer, nullary_constructor, reconstruct_counter_increment,
    registration_call, reject_evidence, require_distinct,
};
use crate::types::{ConstructorId, Type};

#[derive(Clone, Copy)]
pub(in crate::core) struct NaturalEndConstructors {
    pub(in crate::core) nat: ConstructorId,
    pub(in crate::core) invalid: ConstructorId,
}

/// A linked natural-reader end branch. This rule says only that the end
/// branch preserves the accumulated value and advances its cursor by one.
/// It does not establish a canonical scalar, byte input, or provider control.
pub(in crate::core) struct ConditionalNaturalEnd<'a> {
    arena: &'a dyn LedgerArena,
    definition: CheckedStoredFunction<'a>,
    empty_return: NodeId,
    nonzero_return: NodeId,
    invalid_return: NodeId,
    cursor_increments: [CheckedCounterIncrement<'a>; 2],
}

fn natural_return<'a>(
    inspect: &mut CoreInspection<'a, '_>,
    node: NodeId,
    nominal: ConstructorId,
    cursor: BinderId,
    value: BinderId,
    api: crate::module::ModuleId,
) -> Result<CheckedCounterIncrement<'a>, Rejection> {
    let result = constructor_application(inspect, node, nominal, 2, api)?;
    let [actual_value, actual_cursor] = result.arguments.fields else {
        return Err(Rejection::Unsupported);
    };
    expect_variable(inspect, *actual_value, value)?;
    reconstruct_counter_increment(inspect, *actual_cursor, cursor, api)
}

/// Requires the same live selected provider and nonreentry conditions as the
/// existing stored-function and allocation rules. All three actual branches
/// are checked; no input fact is accepted from the candidate's spelling.
pub(in crate::core) fn check_conditional_natural_end<'a>(
    program: &'a dyn LedgerArena,
    linked: &ValidatedInterfaceProgram,
    candidate: DefinitionCandidate,
    constructors: NaturalEndConstructors,
    work: &mut TypeWorkBudget,
) -> Result<ConditionalNaturalEnd<'a>, Rejection> {
    work.charge(2).map_err(|()| Rejection::Exhausted)?;
    if constructors.nat.owner() != constructors.invalid.owner()
        || constructors.nat == constructors.invalid
    {
        return Err(Rejection::Unsupported);
    }
    let nat = program
        .registry()
        .constructor(constructors.nat)
        .ok_or(Rejection::Unsupported)?;
    let invalid = program
        .registry()
        .constructor(constructors.invalid)
        .ok_or(Rejection::Unsupported)?;
    if !matches!(&nat.payload, Some(Type::Tuple(fields)) if matches!(fields.as_ref(), [Type::Int, Type::Int]))
        || invalid.payload.is_some()
    {
        return Err(Rejection::Unsupported);
    }
    let (definition, args, body) =
        acknowledgement::stage(program, linked, candidate, &[], 4, work)?;
    let [cursor, value, has_digit, last] = args.as_slice() else {
        return Err(Rejection::Unsupported);
    };
    let mut inspect = CoreInspection { program, work };
    let branch = inspect.branch(body)?;
    expect_variable(&mut inspect, branch.scrutinee(), *has_digit)?;
    let [empty, has] = branch.arms() else {
        return Err(Rejection::Unsupported);
    };
    if !matches!(
        empty.pattern().kind,
        super::super::CorePatternKind::Boolean(false)
    ) || !matches!(
        has.pattern().kind,
        super::super::CorePatternKind::Boolean(true)
    ) {
        return Err(Rejection::Unsupported);
    }
    let empty_increment = natural_return(
        &mut inspect,
        empty.body(),
        constructors.nat,
        *cursor,
        *value,
        definition.api,
    )?;
    let last_branch = inspect.branch(has.body())?;
    let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Primitive(equal))) =
        inspect.kind(last_branch.scrutinee())?
    else {
        return Err(Rejection::Unsupported);
    };
    if equal.primitive() != super::super::Primitive::Equal {
        return Err(Rejection::Unsupported);
    }
    expect_variable(&mut inspect, equal.left(), *last)?;
    let EffectExprKind::Pure(PureExprKind::Value(super::super::PureValue::Integer(zero))) =
        inspect.kind(equal.right())?
    else {
        return Err(Rejection::Unsupported);
    };
    let size =
        usize::try_from(zero.value().magnitude_byte_length()).map_err(|_| Rejection::Exhausted)?;
    inspect
        .work
        .charge(size.saturating_add(1))
        .map_err(|_| Rejection::Exhausted)?;
    if zero.value().to_i64() != Some(0) {
        return Err(Rejection::Unsupported);
    }
    let [invalid, nonzero] = last_branch.arms() else {
        return Err(Rejection::Unsupported);
    };
    if !matches!(
        invalid.pattern().kind,
        super::super::CorePatternKind::Boolean(true)
    ) || !matches!(
        nonzero.pattern().kind,
        super::super::CorePatternKind::Boolean(false)
    ) {
        return Err(Rejection::Unsupported);
    }
    nullary_constructor(
        &mut inspect,
        invalid.body(),
        constructors.invalid,
        definition.api,
    )?;
    let nonzero_increment = natural_return(
        &mut inspect,
        nonzero.body(),
        constructors.nat,
        *cursor,
        *value,
        definition.api,
    )?;
    Ok(ConditionalNaturalEnd {
        arena: program,
        definition,
        empty_return: empty.body(),
        nonzero_return: nonzero.body(),
        invalid_return: invalid.body(),
        cursor_increments: [empty_increment, nonzero_increment],
    })
}

#[derive(Clone, Copy)]
pub(super) enum CodecPrimitive {
    At,
    Append,
    Split,
    Empty,
}

/// Coordinates of a canonical linked primitive body. This shape witness does
/// not prove the call site's operands, selected provider, or normal return.
pub(super) struct PrimitiveWitness<'a> {
    definition: CheckedStoredFunction<'a>,
    query: NodeId,
    buffer: NodeId,
    operand: NodeId,
}

pub(super) fn reconstruct_primitive<'a>(
    program: &'a dyn LedgerArena,
    linked: &ValidatedInterfaceProgram,
    candidate: DefinitionCandidate,
    operation: CodecPrimitive,
    work: &mut TypeWorkBudget,
) -> Result<PrimitiveWitness<'a>, Rejection> {
    use super::super::{packed::Intrinsic, region::RegionBufferOperation};
    let initializer = linked_initializer(program, linked, candidate, work)?;
    let mut inspect = CoreInspection { program, work };
    let definition = inspect.stored_function_witness(initializer, &[])?;
    let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Bind(bind))) =
        inspect.kind(definition.body)?
    else {
        return Err(Rejection::Unsupported);
    };
    let EffectExprKind::Operation(EffectOperation::Request(query)) =
        inspect.kind(bind.initializer())?
    else {
        return Err(Rejection::Unsupported);
    };
    let EffectExprKind::Operation(EffectOperation::RegionBuffer(buffer)) =
        inspect.kind(bind.body())?
    else {
        return Err(Rejection::Unsupported);
    };
    let api = crate::resolved::RegionApi::for_module(buffer.api).ok_or(Rejection::Unsupported)?;
    let RegionBufferOperation::Intrinsic(intrinsic) = &buffer.operation else {
        return Err(Rejection::Unsupported);
    };
    let operand = buffer.operand.ok_or(Rejection::Unsupported)?;
    if buffer.api != definition.api
        || buffer.right.is_some()
        || query.effect().effect() != api.default_alloc()
        || !query.effect().arguments().is_empty()
        || query.operation() != crate::types::OperationId::new(api.default_alloc(), 1)
        || !matches!(
            inspect.kind(query.operand())?,
            EffectExprKind::Pure(PureExprKind::Value(super::super::PureValue::Unit(_)))
        )
        || inspect.variable(buffer.context)? != bind.binder().id()
        || inspect.variable(operand)? != definition.parameter
        || candidate.binder.module() != Some(intrinsic.module())
        || !intrinsic.authentic_module()
    {
        return Err(Rejection::Unsupported);
    }
    let module = intrinsic.module();
    let expected = match operation {
        CodecPrimitive::At if module.is_builtin_bytes() => {
            let owner = crate::types::NominalTypeId::new(module, 1);
            Intrinsic::BytesAt {
                found: ConstructorId::new(owner, 0),
                invalid: ConstructorId::new(owner, 1),
            }
        }
        CodecPrimitive::Append if module.is_builtin_bytes() => {
            let owner = crate::types::NominalTypeId::new(module, 0);
            Intrinsic::BytesAppendByte {
                appended: ConstructorId::new(owner, 0),
                invalid: ConstructorId::new(owner, 1),
            }
        }
        CodecPrimitive::Empty if module.is_builtin_bytes() => Intrinsic::BytesEmpty,
        CodecPrimitive::Split if module.is_builtin_integer() => {
            let owner = crate::types::NominalTypeId::new(module, 0);
            Intrinsic::IntegerSplit256 {
                parts: ConstructorId::new(owner, 0),
                negative: ConstructorId::new(owner, 1),
            }
        }
        _ => return Err(Rejection::Unsupported),
    };
    if intrinsic.operation() != expected {
        return Err(Rejection::Unsupported);
    }
    Ok(PrimitiveWitness {
        definition,
        query: bind.initializer(),
        buffer: bind.body(),
        operand,
    })
}

#[derive(Clone, Copy)]
pub(in crate::core) struct NaturalReaderDefinitions {
    pub(in crate::core) entry: DefinitionCandidate,
    pub(in crate::core) step: DefinitionCandidate,
    pub(in crate::core) digit: DefinitionCandidate,
    pub(in crate::core) end: DefinitionCandidate,
    pub(in crate::core) at: DefinitionCandidate,
}

#[derive(Clone, Copy)]
pub(in crate::core) struct NaturalReaderConstructors {
    pub(in crate::core) end: NaturalEndConstructors,
    pub(in crate::core) byte_at: ConstructorId,
    pub(in crate::core) invalid_index: ConstructorId,
}

/// Conditional shape witness. A caller must establish actual invocation,
/// finite input, allocation provider and nonreentry before using any reader law.
/// It does not establish complete-frame consumption or a protocol fact.
pub(super) struct ConditionalNaturalReader<'a> {
    arena: &'a dyn LedgerArena,
    entry: CheckedStoredFunction<'a>,
    step: CheckedStoredFunction<'a>,
    digit: CheckedStoredFunction<'a>,
    end: ConditionalNaturalEnd<'a>,
    at: PrimitiveWitness<'a>,
    initial_call: NodeId,
    marker_call: NodeId,
    digit_call: NodeId,
    recursive_call: NodeId,
    arithmetic_buffers: [NodeId; 5],
}

fn literal(
    inspect: &mut CoreInspection<'_, '_>,
    node: NodeId,
    expected: i64,
) -> Result<(), Rejection> {
    let EffectExprKind::Pure(PureExprKind::Value(super::super::PureValue::Integer(value))) =
        inspect.kind(node)?
    else {
        return Err(Rejection::Unsupported);
    };
    let size =
        usize::try_from(value.value().magnitude_byte_length()).map_err(|_| Rejection::Exhausted)?;
    inspect
        .work
        .charge(size.saturating_add(1))
        .map_err(|()| Rejection::Exhausted)?;
    if value.value().to_i64() != Some(expected) {
        return Err(Rejection::Unsupported);
    }
    Ok(())
}

fn arithmetic<'a>(
    inspect: &mut CoreInspection<'a, '_>,
    root: NodeId,
    operation: super::super::Primitive,
    expected_api: crate::module::ModuleId,
    live: &[BinderId],
) -> Result<(NodeId, NodeId, NodeId), Rejection> {
    use super::super::region::RegionBufferOperation;
    let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Bind(bind))) =
        inspect.kind(root)?
    else {
        return Err(Rejection::Unsupported);
    };
    let EffectExprKind::Operation(EffectOperation::Request(query)) =
        inspect.kind(bind.initializer())?
    else {
        return Err(Rejection::Unsupported);
    };
    let EffectExprKind::Operation(EffectOperation::RegionBuffer(buffer)) =
        inspect.kind(bind.body())?
    else {
        return Err(Rejection::Unsupported);
    };
    let api = crate::resolved::RegionApi::for_module(buffer.api).ok_or(Rejection::Unsupported)?;
    if buffer.api != expected_api
        || !matches!(&buffer.operation, RegionBufferOperation::IntegerArithmetic(op) if *op == operation)
        || query.effect().effect() != api.default_alloc()
        || !query.effect().arguments().is_empty()
        || query.operation() != crate::types::OperationId::new(api.default_alloc(), 1)
        || !matches!(
            inspect.kind(query.operand())?,
            EffectExprKind::Pure(PureExprKind::Value(super::super::PureValue::Unit(_)))
        )
        || inspect.variable(buffer.context)? != bind.binder().id()
    {
        return Err(Rejection::Unsupported);
    }
    check_registration_contexts(inspect.work, &[bind.binder().id()], live)?;
    Ok((
        buffer.operand.ok_or(Rejection::Unsupported)?,
        buffer.right.ok_or(Rejection::Unsupported)?,
        bind.body(),
    ))
}

fn equal_literal(
    inspect: &mut CoreInspection<'_, '_>,
    node: NodeId,
    actual: BinderId,
    constant: i64,
) -> Result<(), Rejection> {
    let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Primitive(op))) =
        inspect.kind(node)?
    else {
        return Err(Rejection::Unsupported);
    };
    if op.primitive() != super::super::Primitive::Equal {
        return Err(Rejection::Unsupported);
    }
    expect_variable(inspect, op.left(), actual)?;
    literal(inspect, op.right(), constant)
}

fn checked_call<'a>(
    inspect: &mut CoreInspection<'a, '_>,
    node: NodeId,
    binder: BinderId,
    arity: usize,
    api: crate::module::ModuleId,
    live: &[BinderId],
) -> Result<CheckedPersistentTuple<'a>, Rejection> {
    let args = registration_call(inspect, node, binder, arity, api)?;
    check_registration_contexts(inspect.work, &[args.context_binder], live)?;
    check_registration_contexts(inspect.work, &[args.context_binder], &[binder])?;
    Ok(args)
}

fn byte_result_arms<'a>(
    inspect: &mut CoreInspection<'a, '_>,
    node: NodeId,
    invalid: ConstructorId,
    found: ConstructorId,
) -> Result<
    (
        &'a super::super::CoreMatchArm,
        BinderId,
        &'a super::super::CoreMatchArm,
    ),
    Rejection,
> {
    let branch = inspect.branch(node)?;
    let [bad, good] = branch.arms() else {
        return Err(Rejection::Unsupported);
    };
    if constructor_pattern(bad.pattern(), invalid)?.is_some() {
        return Err(Rejection::Unsupported);
    }
    let payload = constructor_pattern(good.pattern(), found)?.ok_or(Rejection::Unsupported)?;
    Ok((bad, binder_pattern(payload)?, good))
}

/// Reconstruct the linked natural reader. A normal-return scalar derivation is
/// conditional on the invocation and provider premises documented above; the
/// fixed marker/digit progress and accumulator rules are checked below.
pub(super) fn check_conditional_natural_reader<'a>(
    program: &'a dyn LedgerArena,
    linked: &ValidatedInterfaceProgram,
    definitions: NaturalReaderDefinitions,
    constructors: NaturalReaderConstructors,
    work: &mut TypeWorkBudget,
) -> Result<ConditionalNaturalReader<'a>, Rejection> {
    let d = definitions;
    require_distinct(
        work,
        &[
            d.entry.binder,
            d.step.binder,
            d.digit.binder,
            d.end.binder,
            d.at.binder,
        ],
    )?;
    let at = reconstruct_primitive(program, linked, d.at, CodecPrimitive::At, work)?;
    let byte_module = d.at.binder.module().ok_or(Rejection::Unsupported)?;
    let byte_owner = crate::types::NominalTypeId::new(byte_module, 1);
    if constructors.byte_at != ConstructorId::new(byte_owner, 0)
        || constructors.invalid_index != ConstructorId::new(byte_owner, 1)
    {
        return Err(Rejection::Unsupported);
    }
    let end = check_conditional_natural_end(program, linked, d.end, constructors.end, work)?;
    let (entry, entry_args, entry_body) =
        acknowledgement::stage(program, linked, d.entry, &[d.step.binder], 2, work)?;
    let (step, step_args, step_body) = acknowledgement::stage(
        program,
        linked,
        d.step,
        &[d.at.binder, d.end.binder, d.digit.binder],
        6,
        work,
    )?;
    let (digit, digit_args, digit_body) = acknowledgement::stage(
        program,
        linked,
        d.digit,
        &[d.at.binder, d.step.binder],
        4,
        work,
    )?;
    if entry.api != step.api
        || entry.api != digit.api
        || entry.api != end.definition.api
        || entry.api != at.definition.api
    {
        return Err(Rejection::Unsupported);
    }
    let api = entry.api;
    let mut inspect = CoreInspection { program, work };
    let [entry_buffer, entry_cursor] = entry_args.as_slice() else {
        return Err(Rejection::Unsupported);
    };
    let initial = checked_call(&mut inspect, entry_body, d.step.binder, 6, api, &entry_args)?;
    let [buffer, cursor, value, power, has, last] = initial.fields else {
        return Err(Rejection::Unsupported);
    };
    expect_variable(&mut inspect, *buffer, *entry_buffer)?;
    expect_variable(&mut inspect, *cursor, *entry_cursor)?;
    literal(&mut inspect, *value, 0)?;
    literal(&mut inspect, *power, 1)?;
    bool_value(&mut inspect, *has, false)?;
    literal(&mut inspect, *last, 0)?;

    let [
        step_buffer,
        step_cursor,
        step_value,
        step_power,
        step_has,
        step_last,
    ] = step_args.as_slice()
    else {
        return Err(Rejection::Unsupported);
    };
    let branch = inspect.branch(step_body)?;
    let marker_call = branch.scrutinee();
    let marker_args = checked_call(&mut inspect, marker_call, d.at.binder, 2, api, &step_args)?;
    let [buffer, cursor] = marker_args.fields else {
        return Err(Rejection::Unsupported);
    };
    expect_variable(&mut inspect, *buffer, *step_buffer)?;
    expect_variable(&mut inspect, *cursor, *step_cursor)?;
    let (bad, marker, good) = byte_result_arms(
        &mut inspect,
        step_body,
        constructors.invalid_index,
        constructors.byte_at,
    )?;
    nullary_constructor(&mut inspect, bad.body(), constructors.end.invalid, api)?;
    let extra = [marker, d.at.binder, d.end.binder, d.digit.binder];
    inspect
        .work
        .charge(step_args.len().saturating_add(extra.len()))
        .map_err(|()| Rejection::Exhausted)?;
    let mut step_live = Vec::new();
    step_live
        .try_reserve(step_args.len().saturating_add(extra.len()))
        .map_err(|_| Rejection::Exhausted)?;
    step_live.extend_from_slice(&step_args);
    step_live.extend_from_slice(&extra);
    require_distinct(inspect.work, &step_live)?;
    let marker_branch = inspect.branch(good.body())?;
    equal_literal(&mut inspect, marker_branch.scrutinee(), marker, 0)?;
    let [zero, nonzero] = marker_branch.arms() else {
        return Err(Rejection::Unsupported);
    };
    if !matches!(
        zero.pattern().kind,
        super::super::CorePatternKind::Boolean(true)
    ) || !matches!(
        nonzero.pattern().kind,
        super::super::CorePatternKind::Boolean(false)
    ) {
        return Err(Rejection::Unsupported);
    }
    acknowledgement::call(
        &mut inspect,
        zero.body(),
        d.end.binder,
        &[*step_cursor, *step_value, *step_has, *step_last],
        api,
        &step_live,
    )?;
    let group_branch = inspect.branch(nonzero.body())?;
    equal_literal(&mut inspect, group_branch.scrutinee(), marker, 1)?;
    let [unknown, group] = group_branch.arms() else {
        return Err(Rejection::Unsupported);
    };
    if !matches!(
        unknown.pattern().kind,
        super::super::CorePatternKind::Boolean(false)
    ) || !matches!(
        group.pattern().kind,
        super::super::CorePatternKind::Boolean(true)
    ) {
        return Err(Rejection::Unsupported);
    }
    nullary_constructor(&mut inspect, unknown.body(), constructors.end.invalid, api)?;
    acknowledgement::call(
        &mut inspect,
        group.body(),
        d.digit.binder,
        &[*step_buffer, *step_cursor, *step_value, *step_power],
        api,
        &step_live,
    )?;

    let [digit_buffer, digit_cursor, digit_value, digit_power] = digit_args.as_slice() else {
        return Err(Rejection::Unsupported);
    };
    let branch = inspect.branch(digit_body)?;
    let digit_call = branch.scrutinee();
    let at_args = checked_call(&mut inspect, digit_call, d.at.binder, 2, api, &digit_args)?;
    let [buffer, index] = at_args.fields else {
        return Err(Rejection::Unsupported);
    };
    expect_variable(&mut inspect, *buffer, *digit_buffer)?;
    let (index_left, index_right, index_buffer) = arithmetic(
        &mut inspect,
        *index,
        super::super::Primitive::Add,
        api,
        &digit_args,
    )?;
    expect_variable(&mut inspect, index_left, *digit_cursor)?;
    literal(&mut inspect, index_right, 1)?;
    let (bad, byte, good) = byte_result_arms(
        &mut inspect,
        digit_body,
        constructors.invalid_index,
        constructors.byte_at,
    )?;
    nullary_constructor(&mut inspect, bad.body(), constructors.end.invalid, api)?;
    let recursive_call = good.body();
    inspect
        .work
        .charge(digit_args.len().saturating_add(3))
        .map_err(|()| Rejection::Exhausted)?;
    let mut live = Vec::new();
    live.try_reserve(digit_args.len().saturating_add(3))
        .map_err(|_| Rejection::Exhausted)?;
    live.extend_from_slice(&digit_args);
    live.extend_from_slice(&[byte, d.at.binder, d.step.binder]);
    require_distinct(inspect.work, &live)?;
    let next = checked_call(&mut inspect, recursive_call, d.step.binder, 6, api, &live)?;
    let [buffer, cursor, value, power, has, last] = next.fields else {
        return Err(Rejection::Unsupported);
    };
    expect_variable(&mut inspect, *buffer, *digit_buffer)?;
    let (left, right, cursor_buffer) = arithmetic(
        &mut inspect,
        *cursor,
        super::super::Primitive::Add,
        api,
        &live,
    )?;
    expect_variable(&mut inspect, left, *digit_cursor)?;
    literal(&mut inspect, right, 2)?;
    let (left, right, value_buffer) = arithmetic(
        &mut inspect,
        *value,
        super::super::Primitive::Add,
        api,
        &live,
    )?;
    expect_variable(&mut inspect, left, *digit_value)?;
    let (digit_node, power_node, digit_buffer_node) = arithmetic(
        &mut inspect,
        right,
        super::super::Primitive::Multiply,
        api,
        &live,
    )?;
    expect_variable(&mut inspect, digit_node, byte)?;
    expect_variable(&mut inspect, power_node, *digit_power)?;
    let (left, right, power_buffer) = arithmetic(
        &mut inspect,
        *power,
        super::super::Primitive::Multiply,
        api,
        &live,
    )?;
    expect_variable(&mut inspect, left, *digit_power)?;
    literal(&mut inspect, right, 256)?;
    bool_value(&mut inspect, *has, true)?;
    expect_variable(&mut inspect, *last, byte)?;
    Ok(ConditionalNaturalReader {
        arena: program,
        entry,
        step,
        digit,
        end,
        at,
        initial_call: entry_body,
        marker_call,
        digit_call,
        recursive_call,
        arithmetic_buffers: [
            index_buffer,
            cursor_buffer,
            value_buffer,
            digit_buffer_node,
            power_buffer,
        ],
    })
}

#[derive(Clone, Copy)]
pub(in crate::core) struct DecoderDefinitions {
    pub(in crate::core) reader: NaturalReaderDefinitions,
    pub(in crate::core) decode: DefinitionCandidate,
    pub(in crate::core) work: DefinitionCandidate,
    pub(in crate::core) ack: DefinitionCandidate,
    pub(in crate::core) finish_work: DefinitionCandidate,
    pub(in crate::core) payload: DefinitionCandidate,
    pub(in crate::core) address: DefinitionCandidate,
    pub(in crate::core) identity: DefinitionCandidate,
    pub(in crate::core) work_identity: DefinitionCandidate,
    pub(in crate::core) append: DefinitionCandidate,
    pub(in crate::core) append_byte: DefinitionCandidate,
    pub(in crate::core) empty: DefinitionCandidate,
    pub(in crate::core) length: DefinitionCandidate,
}

#[derive(Clone, Copy)]
pub(in crate::core) struct DecoderConstructors {
    pub(in crate::core) reader: NaturalReaderConstructors,
    pub(in crate::core) root: ConstructorId,
    pub(in crate::core) work_id: ConstructorId,
    pub(in crate::core) parent: ConstructorId,
    pub(in crate::core) identity: ConstructorId,
    pub(in crate::core) invalid_identity: ConstructorId,
    pub(in crate::core) address: ConstructorId,
    pub(in crate::core) invalid_address: ConstructorId,
    pub(in crate::core) payload: ConstructorId,
    pub(in crate::core) invalid_payload: ConstructorId,
    pub(in crate::core) encoded: ConstructorId,
    pub(in crate::core) encode_failed: ConstructorId,
    pub(in crate::core) work_decoded: ConstructorId,
    pub(in crate::core) ack_decoded: ConstructorId,
    pub(in crate::core) invalid_frame: ConstructorId,
}

/// An exact decoder shape witness, conditional on provider, control and the
/// natural reader's admitted-input premises. It is not a contextual message
/// or transport fact.
pub(super) struct ConditionalDecoder<'a> {
    reader: ConditionalNaturalReader<'a>,
    empty: PrimitiveWitness<'a>,
    append_byte: PrimitiveWitness<'a>,
    length: NodeId,
    definitions: [CheckedStoredFunction<'a>; 9],
    identity_buffers: [NodeId; 2],
    payload_buffers: [NodeId; 2],
}

fn match_pair<'a>(
    inspect: &mut CoreInspection<'a, '_>,
    node: NodeId,
    bad_id: ConstructorId,
    good_id: ConstructorId,
) -> Result<
    (
        &'a super::super::CoreMatchArm,
        [BinderId; 2],
        &'a super::super::CoreMatchArm,
    ),
    Rejection,
> {
    let branch = inspect.branch(node)?;
    let [bad, good] = branch.arms() else {
        return Err(Rejection::Unsupported);
    };
    if constructor_pattern(bad.pattern(), bad_id)?.is_some() {
        return Err(Rejection::Unsupported);
    }
    let fields = acknowledgement::pattern_fields::<2>(good.pattern(), good_id, inspect.work)?;
    Ok((bad, fields, good))
}

fn match_one<'a>(
    inspect: &mut CoreInspection<'a, '_>,
    node: NodeId,
    bad_id: ConstructorId,
    good_id: ConstructorId,
) -> Result<
    (
        &'a super::super::CoreMatchArm,
        BinderId,
        &'a super::super::CoreMatchArm,
    ),
    Rejection,
> {
    byte_result_arms(inspect, node, bad_id, good_id)
}

fn result_pair(
    inspect: &mut CoreInspection<'_, '_>,
    node: NodeId,
    constructor: ConstructorId,
    first: BinderId,
    second: BinderId,
    api: crate::module::ModuleId,
) -> Result<(), Rejection> {
    let result = constructor_application(inspect, node, constructor, 2, api)?;
    let [left, right] = result.arguments.fields else {
        return Err(Rejection::Unsupported);
    };
    expect_variable(inspect, *left, first)?;
    expect_variable(inspect, *right, second)
}

fn result_single(
    inspect: &mut CoreInspection<'_, '_>,
    node: NodeId,
    constructor: ConstructorId,
    expected: BinderId,
    api: crate::module::ModuleId,
) -> Result<(), Rejection> {
    let call = inspect.application(node)?;
    let closure = inspect.stored_function_witness(call.function(), &[])?;
    let value = inspect.persistent_tuple(closure.body, Some(constructor))?;
    let [payload] = value.fields else {
        return Err(Rejection::Unsupported);
    };
    if closure.api != api || value.api != api || inspect.variable(*payload)? != closure.parameter {
        return Err(Rejection::Unsupported);
    }
    expect_variable(inspect, call.argument(), expected)
}

fn invalid(
    inspect: &mut CoreInspection<'_, '_>,
    arm: &super::super::CoreMatchArm,
    constructor: ConstructorId,
    api: crate::module::ModuleId,
) -> Result<(), Rejection> {
    nullary_constructor(inspect, arm.body(), constructor, api).map(|_| ())
}

fn call_vars(
    inspect: &mut CoreInspection<'_, '_>,
    node: NodeId,
    target: BinderId,
    args: &[BinderId],
    api: crate::module::ModuleId,
    live: &[BinderId],
) -> Result<(), Rejection> {
    acknowledgement::call(inspect, node, target, args, api, live)
}

fn cursor_increment(
    inspect: &mut CoreInspection<'_, '_>,
    node: NodeId,
    cursor: BinderId,
    by: i64,
    api: crate::module::ModuleId,
    live: &[BinderId],
) -> Result<NodeId, Rejection> {
    let (left, right, buffer) = arithmetic(inspect, node, super::super::Primitive::Add, api, live)?;
    expect_variable(inspect, left, cursor)?;
    literal(inspect, right, by)?;
    Ok(buffer)
}

fn with_live(
    work: &mut TypeWorkBudget,
    base: &[BinderId],
    extra: &[BinderId],
) -> Result<Vec<BinderId>, Rejection> {
    let size = base
        .len()
        .checked_add(extra.len())
        .ok_or(Rejection::Exhausted)?;
    work.charge(size).map_err(|()| Rejection::Exhausted)?;
    let mut result = Vec::new();
    result.try_reserve(size).map_err(|_| Rejection::Exhausted)?;
    result.extend_from_slice(base);
    result.extend_from_slice(extra);
    require_distinct(work, &result)?;
    Ok(result)
}

fn checked_length(
    program: &dyn LedgerArena,
    linked: &ValidatedInterfaceProgram,
    candidate: DefinitionCandidate,
    work: &mut TypeWorkBudget,
) -> Result<NodeId, Rejection> {
    use super::super::packed::Intrinsic;
    let id = linked_initializer(program, linked, candidate, work)?;
    let mut inspect = CoreInspection { program, work };
    let EffectExprKind::Pure(PureExprKind::Value(super::super::PureValue::Intrinsic(intrinsic))) =
        inspect.kind(id)?
    else {
        return Err(Rejection::Unsupported);
    };
    if !intrinsic.authentic_module()
        || !intrinsic.module().is_builtin_bytes()
        || intrinsic.operation() != Intrinsic::BytesLength
        || candidate.binder.module() != Some(intrinsic.module())
    {
        return Err(Rejection::Unsupported);
    }
    Ok(id)
}

fn length_equality(
    inspect: &mut CoreInspection<'_, '_>,
    node: NodeId,
    cursor: BinderId,
    input: BinderId,
    length: BinderId,
) -> Result<(), Rejection> {
    let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Primitive(op))) =
        inspect.kind(node)?
    else {
        return Err(Rejection::Unsupported);
    };
    if op.primitive() != super::super::Primitive::Equal {
        return Err(Rejection::Unsupported);
    }
    expect_variable(inspect, op.left(), cursor)?;
    let call = inspect.application(op.right())?;
    expect_variable(inspect, call.function(), length)?;
    expect_variable(inspect, call.argument(), input)
}

fn expect_empty_call(
    inspect: &mut CoreInspection<'_, '_>,
    node: NodeId,
    empty: BinderId,
) -> Result<(), Rejection> {
    let call = inspect.application(node)?;
    expect_variable(inspect, call.function(), empty)?;
    if !matches!(
        inspect.kind(call.argument())?,
        EffectExprKind::Pure(PureExprKind::Value(super::super::PureValue::Unit(_)))
    ) {
        return Err(Rejection::Unsupported);
    }
    Ok(())
}

fn check_work_identity<'a>(
    program: &'a dyn LedgerArena,
    linked: &ValidatedInterfaceProgram,
    d: DecoderDefinitions,
    c: DecoderConstructors,
    work: &mut TypeWorkBudget,
) -> Result<CheckedStoredFunction<'a>, Rejection> {
    let (def, args, body) = acknowledgement::stage(
        program,
        linked,
        d.work_identity,
        &[d.reader.entry.binder],
        2,
        work,
    )?;
    let [buffer, cursor] = args.as_slice() else {
        return Err(Rejection::Unsupported);
    };
    let mut inspect = CoreInspection { program, work };
    let branch = inspect.branch(body)?;
    call_vars(
        &mut inspect,
        branch.scrutinee(),
        d.reader.entry.binder,
        &[*buffer, *cursor],
        def.api,
        &args,
    )?;
    let (bad, [owner, after_owner], good) =
        match_pair(&mut inspect, body, c.reader.end.invalid, c.reader.end.nat)?;
    invalid(&mut inspect, bad, c.invalid_identity, def.api)?;
    let live = with_live(
        inspect.work,
        &args,
        &[owner, after_owner, d.reader.entry.binder],
    )?;
    let branch = inspect.branch(good.body())?;
    call_vars(
        &mut inspect,
        branch.scrutinee(),
        d.reader.entry.binder,
        &[*buffer, after_owner],
        def.api,
        &live,
    )?;
    let (bad, [serial, after_serial], good) = match_pair(
        &mut inspect,
        good.body(),
        c.reader.end.invalid,
        c.reader.end.nat,
    )?;
    invalid(&mut inspect, bad, c.invalid_identity, def.api)?;
    let result = constructor_application(&mut inspect, good.body(), c.identity, 2, def.api)?;
    let [identity, cursor] = result.arguments.fields else {
        return Err(Rejection::Unsupported);
    };
    let work_id = constructor_application(&mut inspect, *identity, c.work_id, 2, def.api)?;
    let [actual_owner, actual_serial] = work_id.arguments.fields else {
        return Err(Rejection::Unsupported);
    };
    expect_variable(&mut inspect, *actual_owner, owner)?;
    expect_variable(&mut inspect, *actual_serial, serial)?;
    expect_variable(&mut inspect, *cursor, after_serial)?;
    Ok(def)
}

fn check_identity<'a>(
    program: &'a dyn LedgerArena,
    linked: &ValidatedInterfaceProgram,
    d: DecoderDefinitions,
    c: DecoderConstructors,
    work: &mut TypeWorkBudget,
) -> Result<(CheckedStoredFunction<'a>, [NodeId; 2]), Rejection> {
    let (def, args, body) = acknowledgement::stage(
        program,
        linked,
        d.identity,
        &[d.reader.at.binder, d.work_identity.binder],
        2,
        work,
    )?;
    let [buffer, cursor] = args.as_slice() else {
        return Err(Rejection::Unsupported);
    };
    let mut inspect = CoreInspection { program, work };
    let branch = inspect.branch(body)?;
    call_vars(
        &mut inspect,
        branch.scrutinee(),
        d.reader.at.binder,
        &[*buffer, *cursor],
        def.api,
        &args,
    )?;
    let (bad, tag, good) = match_one(&mut inspect, body, c.reader.invalid_index, c.reader.byte_at)?;
    invalid(&mut inspect, bad, c.invalid_identity, def.api)?;
    let live = with_live(
        inspect.work,
        &args,
        &[tag, d.reader.at.binder, d.work_identity.binder],
    )?;
    let branch = inspect.branch(good.body())?;
    equal_literal(&mut inspect, branch.scrutinee(), tag, 16)?;
    let [root, other] = branch.arms() else {
        return Err(Rejection::Unsupported);
    };
    if !matches!(
        root.pattern().kind,
        super::super::CorePatternKind::Boolean(true)
    ) || !matches!(
        other.pattern().kind,
        super::super::CorePatternKind::Boolean(false)
    ) {
        return Err(Rejection::Unsupported);
    }
    let result = constructor_application(&mut inspect, root.body(), c.identity, 2, def.api)?;
    let [identity, next] = result.arguments.fields else {
        return Err(Rejection::Unsupported);
    };
    nullary_constructor(&mut inspect, *identity, c.root, def.api)?;
    let root_increment = cursor_increment(&mut inspect, *next, *cursor, 1, def.api, &live)?;
    let branch = inspect.branch(other.body())?;
    equal_literal(&mut inspect, branch.scrutinee(), tag, 17)?;
    let [unknown, work_arm] = branch.arms() else {
        return Err(Rejection::Unsupported);
    };
    if !matches!(
        unknown.pattern().kind,
        super::super::CorePatternKind::Boolean(false)
    ) || !matches!(
        work_arm.pattern().kind,
        super::super::CorePatternKind::Boolean(true)
    ) {
        return Err(Rejection::Unsupported);
    }
    invalid(&mut inspect, unknown, c.invalid_identity, def.api)?;
    let args = checked_call(
        &mut inspect,
        work_arm.body(),
        d.work_identity.binder,
        2,
        def.api,
        &live,
    )?;
    let [actual_buffer, next] = args.fields else {
        return Err(Rejection::Unsupported);
    };
    expect_variable(&mut inspect, *actual_buffer, *buffer)?;
    let work_increment = cursor_increment(&mut inspect, *next, *cursor, 1, def.api, &live)?;
    Ok((def, [root_increment, work_increment]))
}

fn check_address<'a>(
    program: &'a dyn LedgerArena,
    linked: &ValidatedInterfaceProgram,
    d: DecoderDefinitions,
    c: DecoderConstructors,
    work: &mut TypeWorkBudget,
) -> Result<CheckedStoredFunction<'a>, Rejection> {
    let (def, args, body) = acknowledgement::stage(
        program,
        linked,
        d.address,
        &[d.reader.entry.binder, d.identity.binder],
        2,
        work,
    )?;
    let [buffer, cursor] = args.as_slice() else {
        return Err(Rejection::Unsupported);
    };
    let mut inspect = CoreInspection { program, work };
    let branch = inspect.branch(body)?;
    call_vars(
        &mut inspect,
        branch.scrutinee(),
        d.reader.entry.binder,
        &[*buffer, *cursor],
        def.api,
        &args,
    )?;
    let (bad, [owner, next], good) =
        match_pair(&mut inspect, body, c.reader.end.invalid, c.reader.end.nat)?;
    invalid(&mut inspect, bad, c.invalid_address, def.api)?;
    let live = with_live(
        inspect.work,
        &args,
        &[owner, next, d.reader.entry.binder, d.identity.binder],
    )?;
    let branch = inspect.branch(good.body())?;
    call_vars(
        &mut inspect,
        branch.scrutinee(),
        d.identity.binder,
        &[*buffer, next],
        def.api,
        &live,
    )?;
    let (bad, [identity, after], good) =
        match_pair(&mut inspect, good.body(), c.invalid_identity, c.identity)?;
    invalid(&mut inspect, bad, c.invalid_address, def.api)?;
    let result = constructor_application(&mut inspect, good.body(), c.address, 2, def.api)?;
    let [parent, cursor] = result.arguments.fields else {
        return Err(Rejection::Unsupported);
    };
    let parent = constructor_application(&mut inspect, *parent, c.parent, 2, def.api)?;
    let [actual_owner, actual_identity] = parent.arguments.fields else {
        return Err(Rejection::Unsupported);
    };
    expect_variable(&mut inspect, *actual_owner, owner)?;
    expect_variable(&mut inspect, *actual_identity, identity)?;
    expect_variable(&mut inspect, *cursor, after)?;
    Ok(def)
}

fn check_append<'a>(
    program: &'a dyn LedgerArena,
    linked: &ValidatedInterfaceProgram,
    append: DefinitionCandidate,
    append_byte: DefinitionCandidate,
    encoded: ConstructorId,
    encode_failed: ConstructorId,
    work: &mut TypeWorkBudget,
) -> Result<CheckedStoredFunction<'a>, Rejection> {
    let (def, args, body) =
        acknowledgement::stage(program, linked, append, &[append_byte.binder], 2, work)?;
    let [buffer, byte] = args.as_slice() else {
        return Err(Rejection::Unsupported);
    };
    let module = append_byte.binder.module().ok_or(Rejection::Unsupported)?;
    let owner = crate::types::NominalTypeId::new(module, 0);
    let appended = ConstructorId::new(owner, 0);
    let invalid_byte = ConstructorId::new(owner, 1);
    let mut inspect = CoreInspection { program, work };
    let branch = inspect.branch(body)?;
    call_vars(
        &mut inspect,
        branch.scrutinee(),
        append_byte.binder,
        &[*buffer, *byte],
        def.api,
        &args,
    )?;
    let branch = inspect.branch(body)?;
    let [good, bad] = branch.arms() else {
        return Err(Rejection::Unsupported);
    };
    let payload = constructor_pattern(good.pattern(), appended)?.ok_or(Rejection::Unsupported)?;
    let next = binder_pattern(payload)?;
    if constructor_pattern(bad.pattern(), invalid_byte)?.is_some() {
        return Err(Rejection::Unsupported);
    }
    result_single(&mut inspect, good.body(), encoded, next, def.api)?;
    invalid(&mut inspect, bad, encode_failed, def.api)?;
    Ok(def)
}

fn check_payload<'a>(
    program: &'a dyn LedgerArena,
    linked: &ValidatedInterfaceProgram,
    d: DecoderDefinitions,
    c: DecoderConstructors,
    work: &mut TypeWorkBudget,
) -> Result<(CheckedStoredFunction<'a>, [NodeId; 2]), Rejection> {
    let (def, args, body) = acknowledgement::stage(
        program,
        linked,
        d.payload,
        &[d.reader.at.binder, d.append.binder, d.payload.binder],
        5,
        work,
    )?;
    let [source, cursor, copied, length, destination] = args.as_slice() else {
        return Err(Rejection::Unsupported);
    };
    let mut inspect = CoreInspection { program, work };
    let branch = inspect.branch(body)?;
    integer_equal(&mut inspect, branch.scrutinee(), *copied, *length)?;
    let [done, remaining] = branch.arms() else {
        return Err(Rejection::Unsupported);
    };
    if !matches!(
        done.pattern().kind,
        super::super::CorePatternKind::Boolean(true)
    ) || !matches!(
        remaining.pattern().kind,
        super::super::CorePatternKind::Boolean(false)
    ) {
        return Err(Rejection::Unsupported);
    }
    result_pair(
        &mut inspect,
        done.body(),
        c.payload,
        *destination,
        *cursor,
        def.api,
    )?;
    let branch = inspect.branch(remaining.body())?;
    call_vars(
        &mut inspect,
        branch.scrutinee(),
        d.reader.at.binder,
        &[*source, *cursor],
        def.api,
        &args,
    )?;
    let (bad, byte, good) = match_one(
        &mut inspect,
        remaining.body(),
        c.reader.invalid_index,
        c.reader.byte_at,
    )?;
    invalid(&mut inspect, bad, c.invalid_payload, def.api)?;
    let live = with_live(
        inspect.work,
        &args,
        &[byte, d.reader.at.binder, d.append.binder, d.payload.binder],
    )?;
    let branch = inspect.branch(good.body())?;
    call_vars(
        &mut inspect,
        branch.scrutinee(),
        d.append.binder,
        &[*destination, byte],
        def.api,
        &live,
    )?;
    let (bad, next, good) = match_one(&mut inspect, good.body(), c.encode_failed, c.encoded)?;
    invalid(&mut inspect, bad, c.invalid_payload, def.api)?;
    let live = with_live(inspect.work, &live, &[next])?;
    let call = checked_call(
        &mut inspect,
        good.body(),
        d.payload.binder,
        5,
        def.api,
        &live,
    )?;
    let [
        actual_source,
        next_cursor,
        next_copied,
        actual_length,
        actual_destination,
    ] = call.fields
    else {
        return Err(Rejection::Unsupported);
    };
    expect_variable(&mut inspect, *actual_source, *source)?;
    let cursor_step = cursor_increment(&mut inspect, *next_cursor, *cursor, 1, def.api, &live)?;
    let copied_step = cursor_increment(&mut inspect, *next_copied, *copied, 1, def.api, &live)?;
    expect_variable(&mut inspect, *actual_length, *length)?;
    expect_variable(&mut inspect, *actual_destination, next)?;
    Ok((def, [cursor_step, copied_step]))
}

fn check_finish_work<'a>(
    program: &'a dyn LedgerArena,
    linked: &ValidatedInterfaceProgram,
    d: DecoderDefinitions,
    c: DecoderConstructors,
    work: &mut TypeWorkBudget,
) -> Result<CheckedStoredFunction<'a>, Rejection> {
    let (def, args, body) = acknowledgement::stage(
        program,
        linked,
        d.finish_work,
        &[d.payload.binder, d.empty.binder, d.length.binder],
        5,
        work,
    )?;
    let [buffer, child, parent, length, cursor] = args.as_slice() else {
        return Err(Rejection::Unsupported);
    };
    let mut inspect = CoreInspection { program, work };
    let branch = inspect.branch(body)?;
    let call = checked_call(
        &mut inspect,
        branch.scrutinee(),
        d.payload.binder,
        5,
        def.api,
        &args,
    )?;
    let [source, actual_cursor, copied, actual_length, destination] = call.fields else {
        return Err(Rejection::Unsupported);
    };
    expect_variable(&mut inspect, *source, *buffer)?;
    expect_variable(&mut inspect, *actual_cursor, *cursor)?;
    literal(&mut inspect, *copied, 0)?;
    expect_variable(&mut inspect, *actual_length, *length)?;
    expect_empty_call(&mut inspect, *destination, d.empty.binder)?;
    let (bad, [payload, after], good) =
        match_pair(&mut inspect, body, c.invalid_payload, c.payload)?;
    invalid(&mut inspect, bad, c.invalid_frame, def.api)?;
    let branch = inspect.branch(good.body())?;
    length_equality(
        &mut inspect,
        branch.scrutinee(),
        after,
        *buffer,
        d.length.binder,
    )?;
    let [complete, suffix] = branch.arms() else {
        return Err(Rejection::Unsupported);
    };
    if !matches!(
        complete.pattern().kind,
        super::super::CorePatternKind::Boolean(true)
    ) || !matches!(
        suffix.pattern().kind,
        super::super::CorePatternKind::Boolean(false)
    ) {
        return Err(Rejection::Unsupported);
    }
    let result =
        constructor_application(&mut inspect, complete.body(), c.work_decoded, 3, def.api)?;
    let [actual_child, actual_parent, actual_payload] = result.arguments.fields else {
        return Err(Rejection::Unsupported);
    };
    expect_variable(&mut inspect, *actual_child, *child)?;
    expect_variable(&mut inspect, *actual_parent, *parent)?;
    expect_variable(&mut inspect, *actual_payload, payload)?;
    invalid(&mut inspect, suffix, c.invalid_frame, def.api)?;
    Ok(def)
}

fn check_work<'a>(
    program: &'a dyn LedgerArena,
    linked: &ValidatedInterfaceProgram,
    d: DecoderDefinitions,
    c: DecoderConstructors,
    work: &mut TypeWorkBudget,
) -> Result<CheckedStoredFunction<'a>, Rejection> {
    let (def, args, body) = acknowledgement::stage(
        program,
        linked,
        d.work,
        &[
            d.identity.binder,
            d.address.binder,
            d.reader.entry.binder,
            d.finish_work.binder,
        ],
        2,
        work,
    )?;
    let [buffer, cursor] = args.as_slice() else {
        return Err(Rejection::Unsupported);
    };
    let mut inspect = CoreInspection { program, work };
    let branch = inspect.branch(body)?;
    call_vars(
        &mut inspect,
        branch.scrutinee(),
        d.identity.binder,
        &[*buffer, *cursor],
        def.api,
        &args,
    )?;
    let (bad, [child, after_child], good) =
        match_pair(&mut inspect, body, c.invalid_identity, c.identity)?;
    invalid(&mut inspect, bad, c.invalid_frame, def.api)?;
    let live = with_live(
        inspect.work,
        &args,
        &[
            child,
            after_child,
            d.identity.binder,
            d.address.binder,
            d.reader.entry.binder,
            d.finish_work.binder,
        ],
    )?;
    let branch = inspect.branch(good.body())?;
    call_vars(
        &mut inspect,
        branch.scrutinee(),
        d.address.binder,
        &[*buffer, after_child],
        def.api,
        &live,
    )?;
    let (bad, [parent, after_parent], good) =
        match_pair(&mut inspect, good.body(), c.invalid_address, c.address)?;
    invalid(&mut inspect, bad, c.invalid_frame, def.api)?;
    let live = with_live(inspect.work, &live, &[parent, after_parent])?;
    let branch = inspect.branch(good.body())?;
    call_vars(
        &mut inspect,
        branch.scrutinee(),
        d.reader.entry.binder,
        &[*buffer, after_parent],
        def.api,
        &live,
    )?;
    let (bad, [length, after_length], good) = match_pair(
        &mut inspect,
        good.body(),
        c.reader.end.invalid,
        c.reader.end.nat,
    )?;
    invalid(&mut inspect, bad, c.invalid_frame, def.api)?;
    let live = with_live(inspect.work, &live, &[length, after_length])?;
    call_vars(
        &mut inspect,
        good.body(),
        d.finish_work.binder,
        &[*buffer, child, parent, length, after_length],
        def.api,
        &live,
    )?;
    Ok(def)
}

fn check_ack<'a>(
    program: &'a dyn LedgerArena,
    linked: &ValidatedInterfaceProgram,
    d: DecoderDefinitions,
    c: DecoderConstructors,
    work: &mut TypeWorkBudget,
) -> Result<CheckedStoredFunction<'a>, Rejection> {
    let (def, args, body) = acknowledgement::stage(
        program,
        linked,
        d.ack,
        &[d.address.binder, d.identity.binder, d.length.binder],
        2,
        work,
    )?;
    let [buffer, cursor] = args.as_slice() else {
        return Err(Rejection::Unsupported);
    };
    let mut inspect = CoreInspection { program, work };
    let branch = inspect.branch(body)?;
    call_vars(
        &mut inspect,
        branch.scrutinee(),
        d.address.binder,
        &[*buffer, *cursor],
        def.api,
        &args,
    )?;
    let (bad, [parent, after_parent], good) =
        match_pair(&mut inspect, body, c.invalid_address, c.address)?;
    invalid(&mut inspect, bad, c.invalid_frame, def.api)?;
    let live = with_live(
        inspect.work,
        &args,
        &[
            parent,
            after_parent,
            d.address.binder,
            d.identity.binder,
            d.length.binder,
        ],
    )?;
    let branch = inspect.branch(good.body())?;
    call_vars(
        &mut inspect,
        branch.scrutinee(),
        d.identity.binder,
        &[*buffer, after_parent],
        def.api,
        &live,
    )?;
    let (bad, [child, after_child], good) =
        match_pair(&mut inspect, good.body(), c.invalid_identity, c.identity)?;
    invalid(&mut inspect, bad, c.invalid_frame, def.api)?;
    let branch = inspect.branch(good.body())?;
    length_equality(
        &mut inspect,
        branch.scrutinee(),
        after_child,
        *buffer,
        d.length.binder,
    )?;
    let [complete, suffix] = branch.arms() else {
        return Err(Rejection::Unsupported);
    };
    if !matches!(
        complete.pattern().kind,
        super::super::CorePatternKind::Boolean(true)
    ) || !matches!(
        suffix.pattern().kind,
        super::super::CorePatternKind::Boolean(false)
    ) {
        return Err(Rejection::Unsupported);
    }
    result_pair(
        &mut inspect,
        complete.body(),
        c.ack_decoded,
        parent,
        child,
        def.api,
    )?;
    invalid(&mut inspect, suffix, c.invalid_frame, def.api)?;
    Ok(def)
}

fn check_decode<'a>(
    program: &'a dyn LedgerArena,
    linked: &ValidatedInterfaceProgram,
    d: DecoderDefinitions,
    c: DecoderConstructors,
    work: &mut TypeWorkBudget,
) -> Result<CheckedStoredFunction<'a>, Rejection> {
    let id = linked_initializer(program, linked, d.decode, work)?;
    reject_evidence(program, &[id], work)?;
    let mut inspect = CoreInspection { program, work };
    let def =
        inspect.stored_function_witness(id, &[d.reader.at.binder, d.work.binder, d.ack.binder])?;
    let buffer = def.parameter;
    let live = [buffer, d.reader.at.binder, d.work.binder, d.ack.binder];
    require_distinct(inspect.work, &live)?;
    check_registration_contexts(inspect.work, &[def.context_binder], &live)?;
    let body = def.body;
    let branch = inspect.branch(body)?;
    let call = checked_call(
        &mut inspect,
        branch.scrutinee(),
        d.reader.at.binder,
        2,
        def.api,
        &live,
    )?;
    let [actual_buffer, index] = call.fields else {
        return Err(Rejection::Unsupported);
    };
    expect_variable(&mut inspect, *actual_buffer, buffer)?;
    literal(&mut inspect, *index, 0)?;
    let (bad, tag, good) = match_one(&mut inspect, body, c.reader.invalid_index, c.reader.byte_at)?;
    invalid(&mut inspect, bad, c.invalid_frame, def.api)?;
    let live = with_live(inspect.work, &live, &[tag])?;
    let branch = inspect.branch(good.body())?;
    equal_literal(&mut inspect, branch.scrutinee(), tag, 32)?;
    let [work_arm, other] = branch.arms() else {
        return Err(Rejection::Unsupported);
    };
    if !matches!(
        work_arm.pattern().kind,
        super::super::CorePatternKind::Boolean(true)
    ) || !matches!(
        other.pattern().kind,
        super::super::CorePatternKind::Boolean(false)
    ) {
        return Err(Rejection::Unsupported);
    }
    let call = checked_call(
        &mut inspect,
        work_arm.body(),
        d.work.binder,
        2,
        def.api,
        &live,
    )?;
    let [actual_buffer, cursor] = call.fields else {
        return Err(Rejection::Unsupported);
    };
    expect_variable(&mut inspect, *actual_buffer, buffer)?;
    literal(&mut inspect, *cursor, 1)?;
    let branch = inspect.branch(other.body())?;
    equal_literal(&mut inspect, branch.scrutinee(), tag, 33)?;
    let [ack_arm, unknown] = branch.arms() else {
        return Err(Rejection::Unsupported);
    };
    if !matches!(
        ack_arm.pattern().kind,
        super::super::CorePatternKind::Boolean(true)
    ) || !matches!(
        unknown.pattern().kind,
        super::super::CorePatternKind::Boolean(false)
    ) {
        return Err(Rejection::Unsupported);
    }
    let call = checked_call(
        &mut inspect,
        ack_arm.body(),
        d.ack.binder,
        2,
        def.api,
        &live,
    )?;
    let [actual_buffer, cursor] = call.fields else {
        return Err(Rejection::Unsupported);
    };
    expect_variable(&mut inspect, *actual_buffer, buffer)?;
    literal(&mut inspect, *cursor, 1)?;
    invalid(&mut inspect, unknown, c.invalid_frame, def.api)?;
    Ok(def)
}

/// Reconstructs every actual decoder helper and successful frame return. The
/// result is conditional on admitted input, selected provider and call/control
/// premises. It does not attach a receiver, peer, kind, or transport fact.
pub(super) fn check_conditional_decoder<'a>(
    program: &'a dyn LedgerArena,
    linked: &ValidatedInterfaceProgram,
    d: DecoderDefinitions,
    c: DecoderConstructors,
    work: &mut TypeWorkBudget,
) -> Result<ConditionalDecoder<'a>, Rejection> {
    require_distinct(
        work,
        &[
            d.reader.entry.binder,
            d.reader.step.binder,
            d.reader.digit.binder,
            d.reader.end.binder,
            d.reader.at.binder,
            d.decode.binder,
            d.work.binder,
            d.ack.binder,
            d.finish_work.binder,
            d.payload.binder,
            d.address.binder,
            d.identity.binder,
            d.work_identity.binder,
            d.append.binder,
            d.append_byte.binder,
            d.empty.binder,
            d.length.binder,
        ],
    )?;
    let pairs = [
        (c.reader.end.nat, c.reader.end.invalid),
        (c.root, c.work_id),
        (c.identity, c.invalid_identity),
        (c.address, c.invalid_address),
        (c.payload, c.invalid_payload),
        (c.encoded, c.encode_failed),
        (c.work_decoded, c.ack_decoded),
        (c.work_decoded, c.invalid_frame),
    ];
    work.charge(pairs.len())
        .map_err(|()| Rejection::Exhausted)?;
    for (left, right) in pairs {
        if left == right
            || left.owner() != right.owner()
            || program.registry().constructor(left).is_none()
            || program.registry().constructor(right).is_none()
        {
            return Err(Rejection::Unsupported);
        }
    }
    let reader = check_conditional_natural_reader(program, linked, d.reader, c.reader, work)?;
    let append_byte =
        reconstruct_primitive(program, linked, d.append_byte, CodecPrimitive::Append, work)?;
    let empty = reconstruct_primitive(program, linked, d.empty, CodecPrimitive::Empty, work)?;
    let length = checked_length(program, linked, d.length, work)?;
    let work_identity = check_work_identity(program, linked, d, c, work)?;
    let (identity, identity_buffers) = check_identity(program, linked, d, c, work)?;
    let address = check_address(program, linked, d, c, work)?;
    let append = check_append(
        program,
        linked,
        d.append,
        d.append_byte,
        c.encoded,
        c.encode_failed,
        work,
    )?;
    let (payload, payload_buffers) = check_payload(program, linked, d, c, work)?;
    let finish_work = check_finish_work(program, linked, d, c, work)?;
    let work_def = check_work(program, linked, d, c, work)?;
    let ack = check_ack(program, linked, d, c, work)?;
    let decode = check_decode(program, linked, d, c, work)?;
    let definitions = [
        work_identity,
        identity,
        address,
        append,
        payload,
        finish_work,
        work_def,
        ack,
        decode,
    ];
    work.charge(definitions.len())
        .map_err(|()| Rejection::Exhausted)?;
    if definitions.iter().any(|def| def.api != reader.entry.api)
        || append_byte.definition.api != reader.entry.api
        || empty.definition.api != reader.entry.api
    {
        return Err(Rejection::Unsupported);
    }
    Ok(ConditionalDecoder {
        reader,
        empty,
        append_byte,
        length,
        definitions,
        identity_buffers,
        payload_buffers,
    })
}

#[derive(Clone, Copy)]
pub(in crate::core) struct EncoderDefinitions {
    pub(in crate::core) encode: DefinitionCandidate,
    pub(in crate::core) work: DefinitionCandidate,
    pub(in crate::core) ack: DefinitionCandidate,
    pub(in crate::core) work_parent: DefinitionCandidate,
    pub(in crate::core) work_payload: DefinitionCandidate,
    pub(in crate::core) copy: DefinitionCandidate,
    pub(in crate::core) address: DefinitionCandidate,
    pub(in crate::core) identity: DefinitionCandidate,
    pub(in crate::core) nat: DefinitionCandidate,
    pub(in crate::core) digits: DefinitionCandidate,
    pub(in crate::core) append: DefinitionCandidate,
    pub(in crate::core) split: DefinitionCandidate,
    pub(in crate::core) append_byte: DefinitionCandidate,
    pub(in crate::core) empty: DefinitionCandidate,
    pub(in crate::core) length: DefinitionCandidate,
    pub(in crate::core) at: DefinitionCandidate,
}

#[derive(Clone, Copy)]
pub(in crate::core) struct EncoderConstructors {
    pub(in crate::core) root: ConstructorId,
    pub(in crate::core) work_id: ConstructorId,
    pub(in crate::core) no_parent: ConstructorId,
    pub(in crate::core) parent: ConstructorId,
    pub(in crate::core) work_out: ConstructorId,
    pub(in crate::core) ack_out: ConstructorId,
    pub(in crate::core) encoded: ConstructorId,
    pub(in crate::core) encode_failed: ConstructorId,
    pub(in crate::core) split_parts: ConstructorId,
    pub(in crate::core) split_negative: ConstructorId,
    pub(in crate::core) byte_at: ConstructorId,
    pub(in crate::core) invalid_index: ConstructorId,
}

/// Exact linked encoder shape. The result needs an actual admitted call,
/// provider and control premise before it supports a normal-return law. It
/// supplies no authenticated context or transport fact.
pub(super) struct ConditionalEncoder<'a> {
    split: PrimitiveWitness<'a>,
    append_byte: PrimitiveWitness<'a>,
    at: PrimitiveWitness<'a>,
    empty: PrimitiveWitness<'a>,
    length: NodeId,
    definitions: [CheckedStoredFunction<'a>; 11],
    copy_buffer: NodeId,
}

fn encode_append_constant(
    inspect: &mut CoreInspection<'_, '_>,
    node: NodeId,
    target: BinderId,
    buffer: BinderId,
    value: i64,
    api: crate::module::ModuleId,
    live: &[BinderId],
) -> Result<(), Rejection> {
    let call = checked_call(inspect, node, target, 2, api, live)?;
    let [actual_buffer, actual_value] = call.fields else {
        return Err(Rejection::Unsupported);
    };
    expect_variable(inspect, *actual_buffer, buffer)?;
    literal(inspect, *actual_value, value)
}

fn expect_length_call(
    inspect: &mut CoreInspection<'_, '_>,
    node: NodeId,
    length: BinderId,
    input: BinderId,
) -> Result<(), Rejection> {
    let call = inspect.application(node)?;
    expect_variable(inspect, call.function(), length)?;
    expect_variable(inspect, call.argument(), input)
}

fn check_nat_writer<'a>(
    program: &'a dyn LedgerArena,
    linked: &ValidatedInterfaceProgram,
    d: EncoderDefinitions,
    c: EncoderConstructors,
    work: &mut TypeWorkBudget,
) -> Result<CheckedStoredFunction<'a>, Rejection> {
    let (def, args, body) = acknowledgement::stage(
        program,
        linked,
        d.nat,
        &[d.append.binder, d.split.binder, d.digits.binder],
        2,
        work,
    )?;
    let [buffer, value] = args.as_slice() else {
        return Err(Rejection::Unsupported);
    };
    let mut inspect = CoreInspection { program, work };
    let branch = inspect.branch(body)?;
    equal_literal(&mut inspect, branch.scrutinee(), *value, 0)?;
    let [zero, nonzero] = branch.arms() else {
        return Err(Rejection::Unsupported);
    };
    if !matches!(
        zero.pattern().kind,
        super::super::CorePatternKind::Boolean(true)
    ) || !matches!(
        nonzero.pattern().kind,
        super::super::CorePatternKind::Boolean(false)
    ) {
        return Err(Rejection::Unsupported);
    }
    encode_append_constant(
        &mut inspect,
        zero.body(),
        d.append.binder,
        *buffer,
        0,
        def.api,
        &args,
    )?;
    let branch = inspect.branch(nonzero.body())?;
    let split = inspect.application(branch.scrutinee())?;
    expect_variable(&mut inspect, split.function(), d.split.binder)?;
    expect_variable(&mut inspect, split.argument(), *value)?;
    let (bad, [quotient, remainder], good) = match_pair(
        &mut inspect,
        nonzero.body(),
        c.split_negative,
        c.split_parts,
    )?;
    invalid(&mut inspect, bad, c.encode_failed, def.api)?;
    let live = with_live(
        inspect.work,
        &args,
        &[
            quotient,
            remainder,
            d.append.binder,
            d.split.binder,
            d.digits.binder,
        ],
    )?;
    call_vars(
        &mut inspect,
        good.body(),
        d.digits.binder,
        &[*buffer, quotient, remainder],
        def.api,
        &live,
    )?;
    Ok(def)
}

fn check_digits_writer<'a>(
    program: &'a dyn LedgerArena,
    linked: &ValidatedInterfaceProgram,
    d: EncoderDefinitions,
    c: EncoderConstructors,
    work: &mut TypeWorkBudget,
) -> Result<CheckedStoredFunction<'a>, Rejection> {
    let (def, args, body) = acknowledgement::stage(
        program,
        linked,
        d.digits,
        &[d.append.binder, d.nat.binder],
        3,
        work,
    )?;
    let [buffer, quotient, remainder] = args.as_slice() else {
        return Err(Rejection::Unsupported);
    };
    let mut inspect = CoreInspection { program, work };
    let branch = inspect.branch(body)?;
    encode_append_constant(
        &mut inspect,
        branch.scrutinee(),
        d.append.binder,
        *buffer,
        1,
        def.api,
        &args,
    )?;
    let (bad, marked, good) = match_one(&mut inspect, body, c.encode_failed, c.encoded)?;
    invalid(&mut inspect, bad, c.encode_failed, def.api)?;
    let live = with_live(
        inspect.work,
        &args,
        &[marked, d.append.binder, d.nat.binder],
    )?;
    let branch = inspect.branch(good.body())?;
    call_vars(
        &mut inspect,
        branch.scrutinee(),
        d.append.binder,
        &[marked, *remainder],
        def.api,
        &live,
    )?;
    let (bad, next, good) = match_one(&mut inspect, good.body(), c.encode_failed, c.encoded)?;
    invalid(&mut inspect, bad, c.encode_failed, def.api)?;
    let live = with_live(inspect.work, &live, &[next])?;
    call_vars(
        &mut inspect,
        good.body(),
        d.nat.binder,
        &[next, *quotient],
        def.api,
        &live,
    )?;
    Ok(def)
}

fn check_identity_writer<'a>(
    program: &'a dyn LedgerArena,
    linked: &ValidatedInterfaceProgram,
    d: EncoderDefinitions,
    c: EncoderConstructors,
    work: &mut TypeWorkBudget,
) -> Result<CheckedStoredFunction<'a>, Rejection> {
    let (def, args, body) = acknowledgement::stage(
        program,
        linked,
        d.identity,
        &[d.append.binder, d.nat.binder],
        2,
        work,
    )?;
    let [buffer, identity] = args.as_slice() else {
        return Err(Rejection::Unsupported);
    };
    let mut inspect = CoreInspection { program, work };
    let branch = inspect.branch(body)?;
    expect_variable(&mut inspect, branch.scrutinee(), *identity)?;
    let [root, work_arm] = branch.arms() else {
        return Err(Rejection::Unsupported);
    };
    if constructor_pattern(root.pattern(), c.root)?.is_some() {
        return Err(Rejection::Unsupported);
    }
    encode_append_constant(
        &mut inspect,
        root.body(),
        d.append.binder,
        *buffer,
        16,
        def.api,
        &args,
    )?;
    let [owner, serial] =
        acknowledgement::pattern_fields::<2>(work_arm.pattern(), c.work_id, inspect.work)?;
    let live = with_live(
        inspect.work,
        &args,
        &[owner, serial, d.append.binder, d.nat.binder],
    )?;
    let branch = inspect.branch(work_arm.body())?;
    encode_append_constant(
        &mut inspect,
        branch.scrutinee(),
        d.append.binder,
        *buffer,
        17,
        def.api,
        &live,
    )?;
    let (bad, tagged, good) = match_one(&mut inspect, work_arm.body(), c.encode_failed, c.encoded)?;
    invalid(&mut inspect, bad, c.encode_failed, def.api)?;
    let live = with_live(inspect.work, &live, &[tagged])?;
    let branch = inspect.branch(good.body())?;
    call_vars(
        &mut inspect,
        branch.scrutinee(),
        d.nat.binder,
        &[tagged, owner],
        def.api,
        &live,
    )?;
    let (bad, with_owner, good) = match_one(&mut inspect, good.body(), c.encode_failed, c.encoded)?;
    invalid(&mut inspect, bad, c.encode_failed, def.api)?;
    let live = with_live(inspect.work, &live, &[with_owner])?;
    call_vars(
        &mut inspect,
        good.body(),
        d.nat.binder,
        &[with_owner, serial],
        def.api,
        &live,
    )?;
    Ok(def)
}

fn check_address_writer<'a>(
    program: &'a dyn LedgerArena,
    linked: &ValidatedInterfaceProgram,
    d: EncoderDefinitions,
    c: EncoderConstructors,
    work: &mut TypeWorkBudget,
) -> Result<CheckedStoredFunction<'a>, Rejection> {
    let (def, args, body) = acknowledgement::stage(
        program,
        linked,
        d.address,
        &[d.nat.binder, d.identity.binder],
        2,
        work,
    )?;
    let [buffer, parent] = args.as_slice() else {
        return Err(Rejection::Unsupported);
    };
    let mut inspect = CoreInspection { program, work };
    let branch = inspect.branch(body)?;
    expect_variable(&mut inspect, branch.scrutinee(), *parent)?;
    let [none, some] = branch.arms() else {
        return Err(Rejection::Unsupported);
    };
    if constructor_pattern(none.pattern(), c.no_parent)?.is_some() {
        return Err(Rejection::Unsupported);
    }
    invalid(&mut inspect, none, c.encode_failed, def.api)?;
    let [owner, identity] =
        acknowledgement::pattern_fields::<2>(some.pattern(), c.parent, inspect.work)?;
    let live = with_live(
        inspect.work,
        &args,
        &[owner, identity, d.nat.binder, d.identity.binder],
    )?;
    let branch = inspect.branch(some.body())?;
    call_vars(
        &mut inspect,
        branch.scrutinee(),
        d.nat.binder,
        &[*buffer, owner],
        def.api,
        &live,
    )?;
    let (bad, written, good) = match_one(&mut inspect, some.body(), c.encode_failed, c.encoded)?;
    invalid(&mut inspect, bad, c.encode_failed, def.api)?;
    let live = with_live(inspect.work, &live, &[written])?;
    call_vars(
        &mut inspect,
        good.body(),
        d.identity.binder,
        &[written, identity],
        def.api,
        &live,
    )?;
    Ok(def)
}

fn check_copy_writer<'a>(
    program: &'a dyn LedgerArena,
    linked: &ValidatedInterfaceProgram,
    d: EncoderDefinitions,
    c: EncoderConstructors,
    work: &mut TypeWorkBudget,
) -> Result<(CheckedStoredFunction<'a>, NodeId), Rejection> {
    let (def, args, body) = acknowledgement::stage(
        program,
        linked,
        d.copy,
        &[d.at.binder, d.append.binder, d.copy.binder],
        4,
        work,
    )?;
    let [source, buffer, cursor, length] = args.as_slice() else {
        return Err(Rejection::Unsupported);
    };
    let mut inspect = CoreInspection { program, work };
    let branch = inspect.branch(body)?;
    integer_equal(&mut inspect, branch.scrutinee(), *cursor, *length)?;
    let [done, remaining] = branch.arms() else {
        return Err(Rejection::Unsupported);
    };
    if !matches!(
        done.pattern().kind,
        super::super::CorePatternKind::Boolean(true)
    ) || !matches!(
        remaining.pattern().kind,
        super::super::CorePatternKind::Boolean(false)
    ) {
        return Err(Rejection::Unsupported);
    }
    result_single(&mut inspect, done.body(), c.encoded, *buffer, def.api)?;
    let branch = inspect.branch(remaining.body())?;
    call_vars(
        &mut inspect,
        branch.scrutinee(),
        d.at.binder,
        &[*source, *cursor],
        def.api,
        &args,
    )?;
    let (bad, byte, good) = match_one(&mut inspect, remaining.body(), c.invalid_index, c.byte_at)?;
    invalid(&mut inspect, bad, c.encode_failed, def.api)?;
    let live = with_live(
        inspect.work,
        &args,
        &[byte, d.at.binder, d.append.binder, d.copy.binder],
    )?;
    let branch = inspect.branch(good.body())?;
    call_vars(
        &mut inspect,
        branch.scrutinee(),
        d.append.binder,
        &[*buffer, byte],
        def.api,
        &live,
    )?;
    let (bad, next, good) = match_one(&mut inspect, good.body(), c.encode_failed, c.encoded)?;
    invalid(&mut inspect, bad, c.encode_failed, def.api)?;
    let live = with_live(inspect.work, &live, &[next])?;
    let call = checked_call(&mut inspect, good.body(), d.copy.binder, 4, def.api, &live)?;
    let [actual_source, actual_buffer, next_cursor, actual_length] = call.fields else {
        return Err(Rejection::Unsupported);
    };
    expect_variable(&mut inspect, *actual_source, *source)?;
    expect_variable(&mut inspect, *actual_buffer, next)?;
    let cursor_step = cursor_increment(&mut inspect, *next_cursor, *cursor, 1, def.api, &live)?;
    expect_variable(&mut inspect, *actual_length, *length)?;
    Ok((def, cursor_step))
}

fn check_work_payload_writer<'a>(
    program: &'a dyn LedgerArena,
    linked: &ValidatedInterfaceProgram,
    d: EncoderDefinitions,
    c: EncoderConstructors,
    work: &mut TypeWorkBudget,
) -> Result<CheckedStoredFunction<'a>, Rejection> {
    let (def, args, body) = acknowledgement::stage(
        program,
        linked,
        d.work_payload,
        &[d.nat.binder, d.length.binder, d.copy.binder],
        2,
        work,
    )?;
    let [buffer, payload] = args.as_slice() else {
        return Err(Rejection::Unsupported);
    };
    let mut inspect = CoreInspection { program, work };
    let branch = inspect.branch(body)?;
    let call = checked_call(
        &mut inspect,
        branch.scrutinee(),
        d.nat.binder,
        2,
        def.api,
        &args,
    )?;
    let [actual_buffer, length] = call.fields else {
        return Err(Rejection::Unsupported);
    };
    expect_variable(&mut inspect, *actual_buffer, *buffer)?;
    expect_length_call(&mut inspect, *length, d.length.binder, *payload)?;
    let (bad, header, good) = match_one(&mut inspect, body, c.encode_failed, c.encoded)?;
    invalid(&mut inspect, bad, c.encode_failed, def.api)?;
    let live = with_live(
        inspect.work,
        &args,
        &[header, d.nat.binder, d.length.binder, d.copy.binder],
    )?;
    let call = checked_call(&mut inspect, good.body(), d.copy.binder, 4, def.api, &live)?;
    let [source, destination, cursor, length] = call.fields else {
        return Err(Rejection::Unsupported);
    };
    expect_variable(&mut inspect, *source, *payload)?;
    expect_variable(&mut inspect, *destination, header)?;
    literal(&mut inspect, *cursor, 0)?;
    expect_length_call(&mut inspect, *length, d.length.binder, *payload)?;
    Ok(def)
}

fn check_work_parent_writer<'a>(
    program: &'a dyn LedgerArena,
    linked: &ValidatedInterfaceProgram,
    d: EncoderDefinitions,
    c: EncoderConstructors,
    work: &mut TypeWorkBudget,
) -> Result<CheckedStoredFunction<'a>, Rejection> {
    let (def, args, body) = acknowledgement::stage(
        program,
        linked,
        d.work_parent,
        &[d.address.binder, d.work_payload.binder],
        3,
        work,
    )?;
    let [buffer, parent, payload] = args.as_slice() else {
        return Err(Rejection::Unsupported);
    };
    let mut inspect = CoreInspection { program, work };
    let branch = inspect.branch(body)?;
    call_vars(
        &mut inspect,
        branch.scrutinee(),
        d.address.binder,
        &[*buffer, *parent],
        def.api,
        &args,
    )?;
    let (bad, written, good) = match_one(&mut inspect, body, c.encode_failed, c.encoded)?;
    invalid(&mut inspect, bad, c.encode_failed, def.api)?;
    let live = with_live(
        inspect.work,
        &args,
        &[written, d.address.binder, d.work_payload.binder],
    )?;
    call_vars(
        &mut inspect,
        good.body(),
        d.work_payload.binder,
        &[written, *payload],
        def.api,
        &live,
    )?;
    Ok(def)
}

fn check_work_writer<'a>(
    program: &'a dyn LedgerArena,
    linked: &ValidatedInterfaceProgram,
    d: EncoderDefinitions,
    c: EncoderConstructors,
    work: &mut TypeWorkBudget,
) -> Result<CheckedStoredFunction<'a>, Rejection> {
    let (def, args, body) = acknowledgement::stage(
        program,
        linked,
        d.work,
        &[
            d.append.binder,
            d.empty.binder,
            d.identity.binder,
            d.work_parent.binder,
        ],
        3,
        work,
    )?;
    let [child, parent, payload] = args.as_slice() else {
        return Err(Rejection::Unsupported);
    };
    let mut inspect = CoreInspection { program, work };
    let branch = inspect.branch(body)?;
    let call = checked_call(
        &mut inspect,
        branch.scrutinee(),
        d.append.binder,
        2,
        def.api,
        &args,
    )?;
    let [empty, tag] = call.fields else {
        return Err(Rejection::Unsupported);
    };
    expect_empty_call(&mut inspect, *empty, d.empty.binder)?;
    literal(&mut inspect, *tag, 32)?;
    let (bad, tagged, good) = match_one(&mut inspect, body, c.encode_failed, c.encoded)?;
    invalid(&mut inspect, bad, c.encode_failed, def.api)?;
    let live = with_live(
        inspect.work,
        &args,
        &[
            tagged,
            d.append.binder,
            d.empty.binder,
            d.identity.binder,
            d.work_parent.binder,
        ],
    )?;
    let branch = inspect.branch(good.body())?;
    call_vars(
        &mut inspect,
        branch.scrutinee(),
        d.identity.binder,
        &[tagged, *child],
        def.api,
        &live,
    )?;
    let (bad, written, good) = match_one(&mut inspect, good.body(), c.encode_failed, c.encoded)?;
    invalid(&mut inspect, bad, c.encode_failed, def.api)?;
    let live = with_live(inspect.work, &live, &[written])?;
    call_vars(
        &mut inspect,
        good.body(),
        d.work_parent.binder,
        &[written, *parent, *payload],
        def.api,
        &live,
    )?;
    Ok(def)
}

fn check_ack_writer<'a>(
    program: &'a dyn LedgerArena,
    linked: &ValidatedInterfaceProgram,
    d: EncoderDefinitions,
    c: EncoderConstructors,
    work: &mut TypeWorkBudget,
) -> Result<CheckedStoredFunction<'a>, Rejection> {
    let (def, args, body) = acknowledgement::stage(
        program,
        linked,
        d.ack,
        &[
            d.append.binder,
            d.empty.binder,
            d.address.binder,
            d.identity.binder,
        ],
        2,
        work,
    )?;
    let [parent, child] = args.as_slice() else {
        return Err(Rejection::Unsupported);
    };
    let mut inspect = CoreInspection { program, work };
    let branch = inspect.branch(body)?;
    let call = checked_call(
        &mut inspect,
        branch.scrutinee(),
        d.append.binder,
        2,
        def.api,
        &args,
    )?;
    let [empty, tag] = call.fields else {
        return Err(Rejection::Unsupported);
    };
    expect_empty_call(&mut inspect, *empty, d.empty.binder)?;
    literal(&mut inspect, *tag, 33)?;
    let (bad, tagged, good) = match_one(&mut inspect, body, c.encode_failed, c.encoded)?;
    invalid(&mut inspect, bad, c.encode_failed, def.api)?;
    let live = with_live(
        inspect.work,
        &args,
        &[
            tagged,
            d.append.binder,
            d.empty.binder,
            d.address.binder,
            d.identity.binder,
        ],
    )?;
    let branch = inspect.branch(good.body())?;
    call_vars(
        &mut inspect,
        branch.scrutinee(),
        d.address.binder,
        &[tagged, *parent],
        def.api,
        &live,
    )?;
    let (bad, written, good) = match_one(&mut inspect, good.body(), c.encode_failed, c.encoded)?;
    invalid(&mut inspect, bad, c.encode_failed, def.api)?;
    let live = with_live(inspect.work, &live, &[written])?;
    call_vars(
        &mut inspect,
        good.body(),
        d.identity.binder,
        &[written, *child],
        def.api,
        &live,
    )?;
    Ok(def)
}

fn check_encode_entry<'a>(
    program: &'a dyn LedgerArena,
    linked: &ValidatedInterfaceProgram,
    d: EncoderDefinitions,
    c: EncoderConstructors,
    work: &mut TypeWorkBudget,
) -> Result<CheckedStoredFunction<'a>, Rejection> {
    let id = linked_initializer(program, linked, d.encode, work)?;
    reject_evidence(program, &[id], work)?;
    let mut inspect = CoreInspection { program, work };
    let def = inspect.stored_function_witness(id, &[d.work.binder, d.ack.binder])?;
    let input = def.parameter;
    let live = [input, d.work.binder, d.ack.binder];
    require_distinct(inspect.work, &live)?;
    check_registration_contexts(inspect.work, &[def.context_binder], &live)?;
    let branch = inspect.branch(def.body)?;
    expect_variable(&mut inspect, branch.scrutinee(), input)?;
    let [work_arm, ack_arm] = branch.arms() else {
        return Err(Rejection::Unsupported);
    };
    let [child, parent, destination, payload] =
        acknowledgement::pattern_fields::<4>(work_arm.pattern(), c.work_out, inspect.work)?;
    let work_live = with_live(inspect.work, &live, &[child, parent, destination, payload])?;
    call_vars(
        &mut inspect,
        work_arm.body(),
        d.work.binder,
        &[child, parent, payload],
        def.api,
        &work_live,
    )?;
    let [parent, child] =
        acknowledgement::pattern_fields::<2>(ack_arm.pattern(), c.ack_out, inspect.work)?;
    let ack_live = with_live(inspect.work, &live, &[parent, child])?;
    call_vars(
        &mut inspect,
        ack_arm.body(),
        d.ack.binder,
        &[parent, child],
        def.api,
        &ack_live,
    )?;
    Ok(def)
}

/// Reconstructs actual encoder helpers and success/failure branches. Any
/// canonical-wire law remains conditional on the actual call and provider;
/// Work destination is attached only from separately authenticated context.
pub(super) fn check_conditional_encoder<'a>(
    program: &'a dyn LedgerArena,
    linked: &ValidatedInterfaceProgram,
    d: EncoderDefinitions,
    c: EncoderConstructors,
    work: &mut TypeWorkBudget,
) -> Result<ConditionalEncoder<'a>, Rejection> {
    require_distinct(
        work,
        &[
            d.encode.binder,
            d.work.binder,
            d.ack.binder,
            d.work_parent.binder,
            d.work_payload.binder,
            d.copy.binder,
            d.address.binder,
            d.identity.binder,
            d.nat.binder,
            d.digits.binder,
            d.append.binder,
            d.split.binder,
            d.append_byte.binder,
            d.empty.binder,
            d.length.binder,
            d.at.binder,
        ],
    )?;
    let pairs = [
        (c.root, c.work_id),
        (c.no_parent, c.parent),
        (c.work_out, c.ack_out),
        (c.encoded, c.encode_failed),
        (c.split_parts, c.split_negative),
        (c.byte_at, c.invalid_index),
    ];
    work.charge(pairs.len())
        .map_err(|()| Rejection::Exhausted)?;
    for (left, right) in pairs {
        if left == right
            || left.owner() != right.owner()
            || program.registry().constructor(left).is_none()
            || program.registry().constructor(right).is_none()
        {
            return Err(Rejection::Unsupported);
        }
    }
    let split = reconstruct_primitive(program, linked, d.split, CodecPrimitive::Split, work)?;
    let append_byte =
        reconstruct_primitive(program, linked, d.append_byte, CodecPrimitive::Append, work)?;
    let at = reconstruct_primitive(program, linked, d.at, CodecPrimitive::At, work)?;
    let empty = reconstruct_primitive(program, linked, d.empty, CodecPrimitive::Empty, work)?;
    let length = checked_length(program, linked, d.length, work)?;
    let integer_module = d.split.binder.module().ok_or(Rejection::Unsupported)?;
    let split_owner = crate::types::NominalTypeId::new(integer_module, 0);
    let bytes_module = d.at.binder.module().ok_or(Rejection::Unsupported)?;
    let byte_owner = crate::types::NominalTypeId::new(bytes_module, 1);
    if c.split_parts != ConstructorId::new(split_owner, 0)
        || c.split_negative != ConstructorId::new(split_owner, 1)
        || c.byte_at != ConstructorId::new(byte_owner, 0)
        || c.invalid_index != ConstructorId::new(byte_owner, 1)
    {
        return Err(Rejection::Unsupported);
    }
    let append = check_append(
        program,
        linked,
        d.append,
        d.append_byte,
        c.encoded,
        c.encode_failed,
        work,
    )?;
    let nat = check_nat_writer(program, linked, d, c, work)?;
    let digits = check_digits_writer(program, linked, d, c, work)?;
    let identity = check_identity_writer(program, linked, d, c, work)?;
    let address = check_address_writer(program, linked, d, c, work)?;
    let (copy, copy_buffer) = check_copy_writer(program, linked, d, c, work)?;
    let work_payload = check_work_payload_writer(program, linked, d, c, work)?;
    let work_parent = check_work_parent_writer(program, linked, d, c, work)?;
    let work_def = check_work_writer(program, linked, d, c, work)?;
    let ack = check_ack_writer(program, linked, d, c, work)?;
    let encode = check_encode_entry(program, linked, d, c, work)?;
    let definitions = [
        append,
        nat,
        digits,
        identity,
        address,
        copy,
        work_payload,
        work_parent,
        work_def,
        ack,
        encode,
    ];
    work.charge(definitions.len())
        .map_err(|()| Rejection::Exhausted)?;
    if definitions.iter().any(|def| def.api != encode.api)
        || split.definition.api != encode.api
        || append_byte.definition.api != encode.api
        || at.definition.api != encode.api
        || empty.definition.api != encode.api
    {
        return Err(Rejection::Unsupported);
    }
    Ok(ConditionalEncoder {
        split,
        append_byte,
        at,
        empty,
        length,
        definitions,
        copy_buffer,
    })
}

/// Source coordinates for a nominated call. This is a shape witness only: the
/// owning worker focus must authenticate the entered closure, actual argument,
/// saved provider, every reachable helper and matching normal return.
pub(in crate::core) struct NominatedCodecCall<'a> {
    shape: CodecCallShape<'a>,
}

#[expect(
    clippy::large_enum_variant,
    reason = "keep checked witnesses inline without an uncharged allocation"
)]
enum CodecCallShape<'a> {
    Encode {
        definition: ConditionalEncoder<'a>,
        definitions: EncoderDefinitions,
        constructors: EncoderConstructors,
        call: NodeId,
        argument: NodeId,
    },
    Decode {
        definition: ConditionalDecoder<'a>,
        definitions: DecoderDefinitions,
        constructors: DecoderConstructors,
        call: NodeId,
        argument: NodeId,
    },
}

/// A catalog item records an already checked linked helper and, for a
/// canonical buffer intrinsic, the exact checked operation node.
#[derive(Clone, Copy)]
pub(in crate::core) struct CodecHelper {
    binder: BinderId,
    root: NodeId,
    query: NodeId,
    context: NodeId,
    closure: NodeId,
    primitive: Option<NodeId>,
}
impl CodecHelper {
    fn new(
        binder: BinderId,
        definition: CheckedStoredFunction<'_>,
        primitive: Option<NodeId>,
    ) -> Self {
        Self {
            binder,
            root: definition.root,
            query: definition.query,
            context: definition.context,
            closure: definition.closure,
            primitive,
        }
    }
    pub(in crate::core) fn binder(self) -> BinderId {
        self.binder
    }
    pub(in crate::core) fn root(self) -> NodeId {
        self.root
    }
    pub(in crate::core) fn query(self) -> NodeId {
        self.query
    }
    pub(in crate::core) fn context(self) -> NodeId {
        self.context
    }
    pub(in crate::core) fn closure(self) -> NodeId {
        self.closure
    }
    pub(in crate::core) fn primitive(self) -> Option<NodeId> {
        self.primitive
    }
}
impl NominatedCodecCall<'_> {
    pub(in crate::core) fn decoder_length(&self) -> Option<(BinderId, NodeId)> {
        match &self.shape {
            CodecCallShape::Decode {
                definition,
                definitions,
                ..
            } => Some((definitions.length.binder, definition.length)),
            CodecCallShape::Encode { .. } => None,
        }
    }

    pub(in crate::core) fn matches_source_root(&self, root: NodeId, kind: &EffectExprKind) -> bool {
        let arena = self.entry().arena;
        arena.root() == root
            && arena
                .kind_at(root)
                .is_some_and(|actual| std::ptr::eq(actual, kind))
    }

    /// Recheck the closed effect vocabulary of the actual reconstructed
    /// decoder bodies. This is only source evidence: the caller must still
    /// authenticate the live closures, captures and selected provider.
    pub(in crate::core) fn decoder_readonly_query(
        &self,
        work: &mut TypeWorkBudget,
    ) -> Result<(NodeId, NodeId), Rejection> {
        use super::super::{packed::Intrinsic, region::RegionBufferOperation};

        let CodecCallShape::Decode { definitions, .. } = &self.shape else {
            return Err(Rejection::Unsupported);
        };
        let helpers = self.helpers(work)?;
        let buffers = self.buffer_nodes(work)?;
        let arena = self.entry().arena;
        let default_handler = checked_entry_default_handler(arena, work)?;
        let api = self.provider_api();
        let region_api =
            crate::resolved::RegionApi::for_module(api).ok_or(Rejection::Unsupported)?;
        let mut inspect = CoreInspection {
            program: arena,
            work,
        };
        let mut pending = Vec::new();
        let mut visited = std::collections::HashSet::new();
        inspect
            .work
            .charge(helpers.len())
            .map_err(|()| Rejection::Exhausted)?;
        pending
            .try_reserve(helpers.len())
            .map_err(|_| Rejection::Exhausted)?;
        for helper in &helpers {
            let EffectExprKind::Operation(EffectOperation::RegionClosure(closure)) =
                inspect.kind(helper.closure)?
            else {
                return Err(Rejection::Unsupported);
            };
            if closure.api != api {
                return Err(Rejection::Unsupported);
            }
            pending.push(
                closure
                    .code
                    .function()
                    .ok_or(Rejection::Unsupported)?
                    .body(),
            );
        }
        let mut query = None;
        while let Some(id) = pending.pop() {
            inspect.work.charge(1).map_err(|()| Rejection::Exhausted)?;
            visited.try_reserve(1).map_err(|_| Rejection::Exhausted)?;
            if !visited.insert(id) {
                continue;
            }
            let kind = inspect.kind(id)?;
            match kind {
                EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Apply(call))) => {
                    match inspect.kind(call.function())? {
                        EffectExprKind::Pure(PureExprKind::Variable(variable)) => {
                            inspect
                                .work
                                .charge(helpers.len())
                                .map_err(|()| Rejection::Exhausted)?;
                            if variable.binder() != definitions.length.binder
                                && !helpers
                                    .iter()
                                    .any(|helper| helper.binder == variable.binder())
                            {
                                return Err(Rejection::Unsupported);
                            }
                        }
                        EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Bind(
                            _,
                        ))) => {
                            let constructor =
                                inspect.stored_function_witness(call.function(), &[])?;
                            if constructor.api != api {
                                return Err(Rejection::Unsupported);
                            }
                        }
                        _ => return Err(Rejection::Unsupported),
                    }
                }
                EffectExprKind::Pure(PureExprKind::Value(super::super::PureValue::Intrinsic(
                    intrinsic,
                ))) => {
                    if !intrinsic.authentic_module()
                        || !intrinsic.module().is_builtin_bytes()
                        || intrinsic.operation() != Intrinsic::BytesLength
                    {
                        return Err(Rejection::Unsupported);
                    }
                }
                EffectExprKind::Pure(PureExprKind::Value(super::super::PureValue::Function(_)))
                | EffectExprKind::Pure(PureExprKind::Computation(
                    PureComputation::RecursiveBind(_),
                )) => {
                    return Err(Rejection::Unsupported);
                }
                EffectExprKind::Pure(_) => {}
                EffectExprKind::Operation(EffectOperation::Request(request)) => {
                    if request.effect().effect() != region_api.default_alloc()
                        || !request.effect().arguments().is_empty()
                        || request.operation()
                            != crate::types::OperationId::new(region_api.default_alloc(), 1)
                        || !matches!(
                            inspect.kind(request.operand())?,
                            EffectExprKind::Pure(PureExprKind::Value(
                                super::super::PureValue::Unit(_)
                            ))
                        )
                    {
                        return Err(Rejection::Unsupported);
                    }
                    query.get_or_insert(id);
                }
                EffectExprKind::Operation(EffectOperation::RegionBuffer(buffer)) => {
                    inspect
                        .work
                        .charge(buffers.len())
                        .map_err(|()| Rejection::Exhausted)?;
                    if buffer.api != api
                        || !buffers.contains(&id)
                        || !matches!(
                            &buffer.operation,
                            RegionBufferOperation::Intrinsic(_)
                                | RegionBufferOperation::IntegerArithmetic(_)
                        )
                    {
                        return Err(Rejection::Unsupported);
                    }
                }
                EffectExprKind::Operation(EffectOperation::RegionAllocate(allocation)) => {
                    if allocation.api != api
                        || !matches!(inspect.kind(allocation.request)?, EffectExprKind::Operation(EffectOperation::RegionValueRequest(request)) if request.api == api)
                    {
                        return Err(Rejection::Unsupported);
                    }
                }
                EffectExprKind::Operation(EffectOperation::RegionValueRequest(request))
                    if request.api == api => {}
                EffectExprKind::Operation(EffectOperation::RegionTuple(tuple)) => {
                    let EffectExprKind::Operation(EffectOperation::RegionAllocate(allocation)) =
                        inspect.kind(tuple.storage)?
                    else {
                        return Err(Rejection::Unsupported);
                    };
                    if tuple.api != api
                        || allocation.api != api
                        || inspect.variable(allocation.context)?
                            != inspect.variable(tuple.context)?
                    {
                        return Err(Rejection::Unsupported);
                    }
                }
                EffectExprKind::Operation(EffectOperation::RegionClosure(closure)) => {
                    let EffectExprKind::Operation(EffectOperation::RegionAllocate(allocation)) =
                        inspect.kind(closure.storage)?
                    else {
                        return Err(Rejection::Unsupported);
                    };
                    if closure.api != api
                        || !closure.captures.is_empty()
                        || closure.code.function().is_none()
                        || allocation.api != api
                        || inspect.variable(allocation.context)?
                            != inspect.variable(closure.context)?
                    {
                        return Err(Rejection::Unsupported);
                    }
                }
                EffectExprKind::Operation(_) => return Err(Rejection::Unsupported),
            }
            let count = kind.child_count();
            inspect
                .work
                .charge(count)
                .map_err(|()| Rejection::Exhausted)?;
            pending
                .try_reserve(count)
                .map_err(|_| Rejection::Exhausted)?;
            for ordinal in 0..count {
                pending.push(kind.child_at(ordinal).ok_or(Rejection::Unsupported)?);
            }
        }
        inspect
            .work
            .charge(
                visited
                    .capacity()
                    .checked_add(pending.capacity())
                    .ok_or(Rejection::Exhausted)?,
            )
            .map_err(|()| Rejection::Exhausted)?;
        Ok((query.ok_or(Rejection::Unsupported)?, default_handler))
    }

    pub(in crate::core) fn call(&self) -> NodeId {
        match &self.shape {
            CodecCallShape::Encode { call, .. } | CodecCallShape::Decode { call, .. } => *call,
        }
    }

    pub(in crate::core) fn argument(&self) -> NodeId {
        match &self.shape {
            CodecCallShape::Encode { argument, .. } | CodecCallShape::Decode { argument, .. } => {
                *argument
            }
        }
    }

    fn entry(&self) -> &CheckedStoredFunction<'_> {
        match &self.shape {
            CodecCallShape::Encode { definition, .. } => &definition.definitions[10],
            CodecCallShape::Decode { definition, .. } => &definition.definitions[8],
        }
    }

    pub(in crate::core) fn closure(&self) -> NodeId {
        self.entry().closure
    }

    pub(in crate::core) fn definition_binding(&self) -> NodeId {
        self.entry().root
    }

    pub(in crate::core) fn definition_query(&self) -> NodeId {
        self.entry().query
    }

    pub(in crate::core) fn definition_context(&self) -> NodeId {
        self.entry().context
    }

    pub(in crate::core) fn provider_api(&self) -> crate::module::ModuleId {
        self.entry().api
    }

    /// The linked nominal identities already checked for this encoder.
    pub(in crate::core) fn encoder_constructors(&self) -> Option<EncoderConstructors> {
        match &self.shape {
            CodecCallShape::Encode { constructors, .. } => Some(*constructors),
            CodecCallShape::Decode { .. } => None,
        }
    }

    /// The already checked linked bytes-length intrinsic, when this is an encoder.
    pub(in crate::core) fn encoder_length(&self) -> Option<(BinderId, NodeId)> {
        match &self.shape {
            CodecCallShape::Encode {
                definition,
                definitions,
                ..
            } => Some((definitions.length.binder, definition.length)),
            CodecCallShape::Decode { .. } => None,
        }
    }

    /// Return only operation coordinates explicitly reconstructed by the
    /// primitive and arithmetic matchers. No descendant scan grants permission.
    pub(in crate::core) fn buffer_nodes(
        &self,
        work: &mut TypeWorkBudget,
    ) -> Result<Vec<NodeId>, Rejection> {
        let nodes: Vec<NodeId> = match &self.shape {
            CodecCallShape::Encode { definition: g, .. } => {
                work.charge(5).map_err(|()| Rejection::Exhausted)?;
                let mut nodes = Vec::new();
                nodes
                    .try_reserve_exact(5)
                    .map_err(|_| Rejection::Exhausted)?;
                nodes.extend([
                    g.split.buffer,
                    g.append_byte.buffer,
                    g.at.buffer,
                    g.empty.buffer,
                    g.copy_buffer,
                ]);
                nodes
            }
            CodecCallShape::Decode { definition: g, .. } => {
                let mut nodes = Vec::new();
                work.charge(14).map_err(|()| Rejection::Exhausted)?;
                nodes
                    .try_reserve_exact(14)
                    .map_err(|_| Rejection::Exhausted)?;
                nodes.extend([g.reader.at.buffer, g.append_byte.buffer, g.empty.buffer]);
                nodes.extend(g.reader.arithmetic_buffers);
                nodes.extend(
                    g.reader
                        .end
                        .cursor_increments
                        .map(|increment| increment.buffer),
                );
                nodes.extend(g.identity_buffers);
                nodes.extend(g.payload_buffers);
                nodes
            }
        };
        work.charge(nodes.len())
            .map_err(|()| Rejection::Exhausted)?;
        Ok(nodes)
    }

    /// Exact linked helpers for live-focus call/capture checks. The catalog is
    /// reconstructed from the checked definitions, not supplied by the caller.
    pub(in crate::core) fn helpers(
        &self,
        work: &mut TypeWorkBudget,
    ) -> Result<Vec<CodecHelper>, Rejection> {
        let mut helpers = Vec::new();
        let size = match &self.shape {
            CodecCallShape::Encode { .. } => 15,
            CodecCallShape::Decode { .. } => 16,
        };
        work.charge(size).map_err(|()| Rejection::Exhausted)?;
        helpers
            .try_reserve_exact(size)
            .map_err(|_| Rejection::Exhausted)?;
        match &self.shape {
            CodecCallShape::Encode {
                definition: g,
                definitions: d,
                ..
            } => {
                let candidates = [
                    d.append,
                    d.nat,
                    d.digits,
                    d.identity,
                    d.address,
                    d.copy,
                    d.work_payload,
                    d.work_parent,
                    d.work,
                    d.ack,
                    d.encode,
                ];
                for (candidate, def) in candidates.into_iter().zip(g.definitions) {
                    helpers.push(CodecHelper::new(candidate.binder, def, None));
                }
                for (candidate, primitive) in [
                    (d.split, &g.split),
                    (d.append_byte, &g.append_byte),
                    (d.at, &g.at),
                    (d.empty, &g.empty),
                ] {
                    helpers.push(CodecHelper::new(
                        candidate.binder,
                        primitive.definition,
                        Some(primitive.buffer),
                    ));
                }
            }
            CodecCallShape::Decode {
                definition: g,
                definitions: d,
                ..
            } => {
                let candidates = [
                    d.work_identity,
                    d.identity,
                    d.address,
                    d.append,
                    d.payload,
                    d.finish_work,
                    d.work,
                    d.ack,
                    d.decode,
                ];
                for (candidate, def) in candidates.into_iter().zip(g.definitions) {
                    helpers.push(CodecHelper::new(candidate.binder, def, None));
                }
                for (candidate, def) in [
                    (d.reader.entry, g.reader.entry),
                    (d.reader.step, g.reader.step),
                    (d.reader.digit, g.reader.digit),
                    (d.reader.end, g.reader.end.definition),
                ] {
                    helpers.push(CodecHelper::new(candidate.binder, def, None));
                }
                for (candidate, primitive) in [
                    (d.reader.at, &g.reader.at),
                    (d.append_byte, &g.append_byte),
                    (d.empty, &g.empty),
                ] {
                    helpers.push(CodecHelper::new(
                        candidate.binder,
                        primitive.definition,
                        Some(primitive.buffer),
                    ));
                }
            }
        }
        Ok(helpers)
    }
}

pub(in crate::core) fn nominate_encode_call<'a>(
    program: &'a dyn LedgerArena,
    linked: &ValidatedInterfaceProgram,
    call: NodeId,
    definitions: EncoderDefinitions,
    constructors: EncoderConstructors,
    work: &mut TypeWorkBudget,
) -> Result<NominatedCodecCall<'a>, Rejection> {
    let mut inspect = CoreInspection { program, work };
    let application = inspect.application(call)?;
    if inspect.variable(application.function())? != definitions.encode.binder {
        return Err(Rejection::Unsupported);
    }
    let argument = application.argument();
    let definition =
        check_conditional_encoder(program, linked, definitions, constructors, inspect.work)?;
    Ok(NominatedCodecCall {
        shape: CodecCallShape::Encode {
            definition,
            definitions,
            constructors,
            call,
            argument,
        },
    })
}

pub(super) fn nominate_decode_call<'a>(
    program: &'a dyn LedgerArena,
    linked: &ValidatedInterfaceProgram,
    call: NodeId,
    definitions: DecoderDefinitions,
    constructors: DecoderConstructors,
    work: &mut TypeWorkBudget,
) -> Result<NominatedCodecCall<'a>, Rejection> {
    let mut inspect = CoreInspection { program, work };
    let application = inspect.application(call)?;
    if inspect.variable(application.function())? != definitions.decode.binder {
        return Err(Rejection::Unsupported);
    }
    let argument = application.argument();
    let definition =
        check_conditional_decoder(program, linked, definitions, constructors, inspect.work)?;
    Ok(NominatedCodecCall {
        shape: CodecCallShape::Decode {
            definition,
            definitions,
            constructors,
            call,
            argument,
        },
    })
}

/// Source match coordinates; no arm is treated as reached by this witness.
pub(in crate::core) struct CodecResultMatch {
    call: NodeId,
    shape: CodecResultShape,
}

enum CodecResultShape {
    Encode {
        matching: NodeId,
        bytes: BinderId,
        success: NodeId,
        failure: NodeId,
    },
    Decode {
        matching: NodeId,
        child: BinderId,
        parent: BinderId,
        payload: BinderId,
        work_success: NodeId,
        ack_parent: BinderId,
        ack_child: BinderId,
        ack_success: NodeId,
        failure: NodeId,
    },
}

/// A source arm descriptor; it is not evidence that the arm was reached.
pub(in crate::core) enum CodecResultArm {
    Encoded { bytes: BinderId, body: NodeId },
    Work { fields: [BinderId; 3], body: NodeId },
    Ack { fields: [BinderId; 2], body: NodeId },
    Failure { body: NodeId },
}

impl CodecResultMatch {
    pub(in crate::core) fn call(&self) -> NodeId {
        self.call
    }
    pub(in crate::core) fn matching(&self) -> NodeId {
        match &self.shape {
            CodecResultShape::Encode { matching, .. }
            | CodecResultShape::Decode { matching, .. } => *matching,
        }
    }
    pub(in crate::core) fn arm(&self, ordinal: usize) -> Option<CodecResultArm> {
        match (&self.shape, ordinal) {
            (CodecResultShape::Encode { bytes, success, .. }, 0) => Some(CodecResultArm::Encoded {
                bytes: *bytes,
                body: *success,
            }),
            (CodecResultShape::Encode { failure, .. }, 1) => {
                Some(CodecResultArm::Failure { body: *failure })
            }
            (
                CodecResultShape::Decode {
                    child,
                    parent,
                    payload,
                    work_success,
                    ..
                },
                0,
            ) => Some(CodecResultArm::Work {
                fields: [*child, *parent, *payload],
                body: *work_success,
            }),
            (
                CodecResultShape::Decode {
                    ack_parent,
                    ack_child,
                    ack_success,
                    ..
                },
                1,
            ) => Some(CodecResultArm::Ack {
                fields: [*ack_parent, *ack_child],
                body: *ack_success,
            }),
            (CodecResultShape::Decode { failure, .. }, 2) => {
                Some(CodecResultArm::Failure { body: *failure })
            }
            _ => None,
        }
    }
}

pub(in crate::core) fn check_encode_result_match(
    program: &dyn LedgerArena,
    invocation: &NominatedCodecCall<'_>,
    matching: NodeId,
    work: &mut TypeWorkBudget,
) -> Result<CodecResultMatch, Rejection> {
    let CodecCallShape::Encode { constructors, .. } = &invocation.shape else {
        return Err(Rejection::Unsupported);
    };
    if !super::same_ledger_arena(program, invocation.entry().arena) {
        return Err(Rejection::Unsupported);
    }
    let mut inspect = CoreInspection { program, work };
    let branch = inspect.branch(matching)?;
    if branch.scrutinee() != invocation.call() {
        return Err(Rejection::Unsupported);
    }
    let [encoded, failed] = branch.arms() else {
        return Err(Rejection::Unsupported);
    };
    let bytes = constructor_pattern(encoded.pattern(), constructors.encoded)?
        .map(binder_pattern)
        .transpose()?
        .ok_or(Rejection::Unsupported)?;
    if constructor_pattern(failed.pattern(), constructors.encode_failed)?.is_some() {
        return Err(Rejection::Unsupported);
    }
    Ok(CodecResultMatch {
        call: invocation.call(),
        shape: CodecResultShape::Encode {
            matching,
            bytes,
            success: encoded.body(),
            failure: failed.body(),
        },
    })
}

pub(super) fn check_decode_result_match(
    program: &dyn LedgerArena,
    invocation: &NominatedCodecCall<'_>,
    matching: NodeId,
    work: &mut TypeWorkBudget,
) -> Result<CodecResultMatch, Rejection> {
    let CodecCallShape::Decode { constructors, .. } = &invocation.shape else {
        return Err(Rejection::Unsupported);
    };
    if !super::same_ledger_arena(program, invocation.entry().arena) {
        return Err(Rejection::Unsupported);
    }
    let mut inspect = CoreInspection { program, work };
    let branch = inspect.branch(matching)?;
    if branch.scrutinee() != invocation.call() {
        return Err(Rejection::Unsupported);
    }
    let [work_arm, ack_arm, failed] = branch.arms() else {
        return Err(Rejection::Unsupported);
    };
    let [child, parent, payload] = acknowledgement::pattern_fields::<3>(
        work_arm.pattern(),
        constructors.work_decoded,
        inspect.work,
    )?;
    let [ack_parent, ack_child] = acknowledgement::pattern_fields::<2>(
        ack_arm.pattern(),
        constructors.ack_decoded,
        inspect.work,
    )?;
    if constructor_pattern(failed.pattern(), constructors.invalid_frame)?.is_some() {
        return Err(Rejection::Unsupported);
    }
    Ok(CodecResultMatch {
        call: invocation.call(),
        shape: CodecResultShape::Decode {
            matching,
            child,
            parent,
            payload,
            work_success: work_arm.body(),
            ack_parent,
            ack_child,
            ack_success: ack_arm.body(),
            failure: failed.body(),
        },
    })
}

/// A checked driver call whose actual parameter is forwarded to the nominated
/// decoder and whose body matches that exact result. This records only source
/// coordinates; the selected closure, capture, payload and return still need
/// authentication in their owning live focus.
pub(in crate::core) struct ConditionalDecodeDriver<'a> {
    binder: BinderId,
    definition: CheckedStoredFunction<'a>,
    outer_call: NodeId,
    outer_argument: NodeId,
    invocation: NominatedCodecCall<'a>,
    result_match: CodecResultMatch,
}

impl ConditionalDecodeDriver<'_> {
    pub(in crate::core) fn helper(&self) -> CodecHelper {
        CodecHelper::new(self.binder, self.definition, None)
    }
    pub(in crate::core) fn captures(&self) -> &[NodeId] {
        self.definition.captures
    }
    pub(in crate::core) fn outer_call(&self) -> NodeId {
        self.outer_call
    }
    pub(in crate::core) fn outer_argument(&self) -> NodeId {
        self.outer_argument
    }
    pub(in crate::core) fn formal(&self) -> BinderId {
        self.definition.parameter
    }
    pub(in crate::core) fn closure(&self) -> NodeId {
        self.definition.closure
    }
    pub(in crate::core) fn definition_binding(&self) -> NodeId {
        self.definition.root
    }
    pub(in crate::core) fn definition_query(&self) -> NodeId {
        self.definition.query
    }
    pub(in crate::core) fn definition_context(&self) -> NodeId {
        self.definition.context
    }
    pub(in crate::core) fn provider_api(&self) -> crate::module::ModuleId {
        self.definition.api
    }
    pub(in crate::core) fn invocation(&self) -> &NominatedCodecCall<'_> {
        &self.invocation
    }
    pub(in crate::core) fn result_match(&self) -> &CodecResultMatch {
        &self.result_match
    }
}

pub(in crate::core) fn check_nominated_decode_driver<'a>(
    program: &'a dyn LedgerArena,
    linked: &ValidatedInterfaceProgram,
    driver: DefinitionCandidate,
    outer_call: NodeId,
    definitions: DecoderDefinitions,
    constructors: DecoderConstructors,
    work: &mut TypeWorkBudget,
) -> Result<ConditionalDecodeDriver<'a>, Rejection> {
    let initializer = linked_initializer(program, linked, driver, work)?;
    let mut inspect = CoreInspection { program, work };
    let definition = inspect.stored_function_witness(initializer, &[definitions.decode.binder])?;
    let outer = inspect.application(outer_call)?;
    if inspect.variable(outer.function())? != driver.binder {
        return Err(Rejection::Unsupported);
    }
    let outer_argument = outer.argument();
    let branch = inspect.branch(definition.body)?;
    let call = branch.scrutinee();
    let actual = inspect.application(call)?;
    if inspect.variable(actual.function())? != definitions.decode.binder
        || inspect.variable(actual.argument())? != definition.parameter
    {
        return Err(Rejection::Unsupported);
    }
    let invocation = nominate_decode_call(
        program,
        linked,
        call,
        definitions,
        constructors,
        inspect.work,
    )?;
    if definition.api != invocation.provider_api() {
        return Err(Rejection::Unsupported);
    }
    let result_match =
        check_decode_result_match(program, &invocation, definition.body, inspect.work)?;
    Ok(ConditionalDecodeDriver {
        binder: driver.binder,
        definition,
        outer_call,
        outer_argument,
        invocation,
        result_match,
    })
}

/// Source coordinates for a multi-field receipt helper. The actual worker,
/// current ledger, message origin, provider and reached arm are checked in
/// the owning live worker query; this witness grants none of those facts.
pub(in crate::core) struct ConditionalReceiptDecode<'a> {
    driver: super::driver::CheckedDriverCall<'a>,
    message_field: usize,
    message_formal: BinderId,
    invocation: NominatedCodecCall<'a>,
    result_match: CodecResultMatch,
}

impl ConditionalReceiptDecode<'_> {
    pub(in crate::core) fn driver(&self) -> &super::driver::CheckedDriverCall<'_> {
        &self.driver
    }

    pub(in crate::core) fn message_field(&self) -> usize {
        self.message_field
    }

    pub(in crate::core) fn message_formal(&self) -> BinderId {
        self.message_formal
    }

    pub(in crate::core) fn invocation(&self) -> &NominatedCodecCall<'_> {
        &self.invocation
    }

    pub(in crate::core) fn result_match(&self) -> &CodecResultMatch {
        &self.result_match
    }
}

/// Check the actual tuple argument/formals and the exact direct decoder match.
/// In particular, a caller-supplied DecodeResult or an unrelated message
/// field cannot substitute for the nominated source call.
pub(in crate::core) fn check_nominated_receipt_decode<'a>(
    program: &'a dyn LedgerArena,
    linked: &'a ValidatedInterfaceProgram,
    driver_plan: &super::driver::DriverNomination<'_>,
    message_field: usize,
    definitions: DecoderDefinitions,
    constructors: DecoderConstructors,
    work: &mut TypeWorkBudget,
) -> Result<ConditionalReceiptDecode<'a>, Rejection> {
    if message_field >= driver_plan.arity || message_field == driver_plan.ledger_field {
        return Err(Rejection::Unsupported);
    }
    let driver = super::driver::check_nominated_driver_call(program, linked, driver_plan, work)?;
    let mut inspect = CoreInspection { program, work };
    let parameters = inspect.branch(driver.parameter_match())?;
    let [arm] = parameters.arms() else {
        return Err(Rejection::Unsupported);
    };
    let super::super::CorePatternKind::Tuple(formals) = &arm.pattern().kind else {
        return Err(Rejection::Unsupported);
    };
    let message_formal = binder_pattern(formals.get(message_field).ok_or(Rejection::Unsupported)?)?;
    let matching = arm.body();
    let branch = inspect.branch(matching)?;
    let call = branch.scrutinee();
    let invocation = nominate_decode_call(
        program,
        linked,
        call,
        definitions,
        constructors,
        inspect.work,
    )?;
    expect_variable(&mut inspect, invocation.argument(), message_formal)?;
    if driver.provider_api() != invocation.provider_api() {
        return Err(Rejection::Unsupported);
    }
    let result_match = check_decode_result_match(program, &invocation, matching, inspect.work)?;
    Ok(ConditionalReceiptDecode {
        driver,
        message_field,
        message_formal,
        invocation,
        result_match,
    })
}
