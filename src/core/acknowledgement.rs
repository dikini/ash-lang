//! Draft acknowledgement analysis; this publishes no authority.
use super::*;
use crate::types::ConstructorId;

#[derive(Clone, Copy, Eq, PartialEq)]
pub(in crate::core) struct AcknowledgementDefinitions {
    pub(in crate::core) entry: DefinitionCandidate,
    pub(in crate::core) record: DefinitionCandidate,
    pub(in crate::core) child: DefinitionCandidate,
    pub(in crate::core) commit: DefinitionCandidate,
    pub(in crate::core) record_lookup: DefinitionCandidate,
    pub(in crate::core) child_lookup: DefinitionCandidate,
    pub(in crate::core) record_update: DefinitionCandidate,
    pub(in crate::core) child_removal: DefinitionCandidate,
    pub(in crate::core) comparison: DefinitionCandidate,
    pub(in crate::core) record_projection: DefinitionCandidate,
    pub(in crate::core) child_projection: DefinitionCandidate,
}

#[derive(Clone, Copy, Eq, PartialEq)]
pub(in crate::core) struct AcknowledgementConstructors {
    pub(in crate::core) state: InitializationConstructors,
    pub(in crate::core) child: ConstructorId,
    pub(in crate::core) no_record: ConstructorId,
    pub(in crate::core) has_record: ConstructorId,
    pub(in crate::core) no_child: ConstructorId,
    pub(in crate::core) has_child: ConstructorId,
    pub(in crate::core) removed: ConstructorId,
    pub(in crate::core) missing: ConstructorId,
}

/// Conditional on represented finite unique lists, actual captures,
/// faithfully selected allocation and an authenticated peer from the caller.
/// This witness conveys no currentness or network-release authority.
pub(in crate::core) struct ConditionalAcknowledgement<'a> {
    arena: &'a dyn LedgerArena,
    linked: &'a ValidatedInterfaceProgram,
    stages: [CheckedStoredFunction<'a>; 4],
    record_lookup: ConditionalRecordOperation<'a>,
    child_lookup: ConditionalLookup<'a>,
    record_update: ConditionalRecordOperation<'a>,
    child_removal: ConditionalRemoval<'a>,
    returns: [NodeId; 4],
    successor_fields: [NodeId; 3],
    replacement_fields: [NodeId; 4],
}

pub(super) fn stage<'a>(
    program: &'a dyn LedgerArena,
    linked: &ValidatedInterfaceProgram,
    candidate: DefinitionCandidate,
    captures: &[BinderId],
    arity: usize,
    work: &mut TypeWorkBudget,
) -> Result<(CheckedStoredFunction<'a>, Vec<BinderId>, NodeId), Rejection> {
    let id = linked_initializer(program, linked, candidate, work)?;
    reject_evidence(program, &[id], work)?;
    let mut inspect = CoreInspection { program, work };
    let function = inspect.stored_function_witness(id, captures)?;
    let branch = inspect.branch(function.body)?;
    expect_variable(&mut inspect, branch.scrutinee(), function.parameter)?;
    let [arm] = branch.arms() else {
        return Err(Rejection::Unsupported);
    };
    let super::super::CorePatternKind::Tuple(fields) = &arm.pattern().kind else {
        return Err(Rejection::Unsupported);
    };
    if fields.len() != arity {
        return Err(Rejection::Unsupported);
    }
    inspect
        .work
        .charge(arity)
        .map_err(|()| Rejection::Exhausted)?;
    let mut binders = Vec::new();
    binders
        .try_reserve(arity)
        .map_err(|_| Rejection::Exhausted)?;
    for field in fields.iter() {
        binders.push(binder_pattern(field)?);
    }
    inspect
        .work
        .charge(captures.len() + 1)
        .map_err(|()| Rejection::Exhausted)?;
    binders
        .try_reserve(captures.len() + 1)
        .map_err(|_| Rejection::Exhausted)?;
    binders.push(function.parameter);
    binders.extend_from_slice(captures);
    require_distinct(inspect.work, &binders)?;
    check_registration_contexts(inspect.work, &[function.context_binder], &binders)?;
    binders.truncate(arity);
    Ok((function, binders, arm.body()))
}

pub(super) fn pattern_fields<const N: usize>(
    pattern: &super::super::CorePattern,
    c: ConstructorId,
    work: &mut TypeWorkBudget,
) -> Result<[BinderId; N], Rejection> {
    let payload = constructor_pattern(pattern, c)?.ok_or(Rejection::Unsupported)?;
    let super::super::CorePatternKind::Tuple(fields) = &payload.kind else {
        return Err(Rejection::Unsupported);
    };
    if fields.len() != N {
        return Err(Rejection::Unsupported);
    }
    work.charge(N).map_err(|()| Rejection::Exhausted)?;
    let mut result = Vec::new();
    result.try_reserve(N).map_err(|_| Rejection::Exhausted)?;
    for field in fields.iter() {
        result.push(binder_pattern(field)?);
    }
    result.try_into().map_err(|_| Rejection::Unsupported)
}

pub(super) fn call<'a>(
    inspect: &mut CoreInspection<'a, '_>,
    node: NodeId,
    target: BinderId,
    args: &[BinderId],
    api: crate::module::ModuleId,
    live: &[BinderId],
) -> Result<(), Rejection> {
    let pair = registration_call(inspect, node, target, args.len(), api)?;
    for (field, binder) in pair.fields.iter().zip(args) {
        expect_variable(inspect, *field, *binder)?;
    }
    check_registration_contexts(inspect.work, &[pair.context_binder], live)?;
    check_registration_contexts(inspect.work, &[pair.context_binder], &[target])
}

pub(in crate::core) fn check_conditional_acknowledgement<'a>(
    program: &'a dyn LedgerArena,
    linked: &'a ValidatedInterfaceProgram,
    d: AcknowledgementDefinitions,
    c: AcknowledgementConstructors,
    work: &mut TypeWorkBudget,
) -> Result<ConditionalAcknowledgement<'a>, Rejection> {
    check_initialization_nominals(program, c.state, work)?;
    let names = [
        d.entry.binder,
        d.record.binder,
        d.child.binder,
        d.commit.binder,
        d.record_lookup.binder,
        d.child_lookup.binder,
        d.record_update.binder,
        d.child_removal.binder,
        d.comparison.binder,
        d.record_projection.binder,
        d.child_projection.binder,
    ];
    require_distinct(work, &names)?;
    let records = RecordListConstructors {
        root: c.state.root,
        work: c.state.work,
        record: c.state.record,
        empty: c.state.records_empty,
        more: c.state.records_more,
        absent: c.no_record,
        present: c.has_record,
    };
    let record_lookup = check_conditional_record_operation(
        program,
        linked,
        d.record_lookup,
        d.comparison,
        d.record_projection,
        records,
        RecordOperation::Lookup,
        work,
    )?;
    let record_update = check_conditional_record_operation(
        program,
        linked,
        d.record_update,
        d.comparison,
        d.record_projection,
        records,
        RecordOperation::Update,
        work,
    )?;
    let child_lookup = check_conditional_lookup(
        program,
        linked,
        d.child_lookup,
        LookupConstructors {
            root: c.state.root,
            work: c.state.work,
            child: c.child,
            empty: c.state.children_empty,
            more: c.state.children_more,
            absent: c.no_child,
            present: c.has_child,
        },
        RemovalDependencies {
            comparison: d.comparison,
            projection: d.child_projection,
        },
        work,
    )?;
    let child_removal = check_conditional_removal(
        program,
        linked,
        d.child_removal,
        RemovalConstructors {
            empty: c.state.children_empty,
            more: c.state.children_more,
            found: c.removed,
            missing: c.missing,
            root_id: c.state.root,
            work_id: c.state.work,
            entry: c.child,
        },
        RemovalDependencies {
            comparison: d.comparison,
            projection: d.child_projection,
        },
        work,
    )?;
    let (entry, a, entry_body) = stage(
        program,
        linked,
        d.entry,
        &[d.record_lookup.binder, d.record.binder],
        4,
        work,
    )?;
    let (record, b, record_body) = stage(
        program,
        linked,
        d.record,
        &[d.child_lookup.binder, d.child.binder],
        8,
        work,
    )?;
    let (child, x, child_body) = stage(program, linked, d.child, &[d.commit.binder], 12, work)?;
    let (commit, m, commit_body) = stage(
        program,
        linked,
        d.commit,
        &[d.child_removal.binder, d.record_update.binder],
        9,
        work,
    )?;
    let stages = [entry, record, child, commit];
    let api = entry.api;
    work.charge(8).map_err(|()| Rejection::Exhausted)?;
    if stages.iter().any(|s| s.api != api)
        || record_lookup.graph.definition.api != api
        || record_update.graph.definition.api != api
        || child_lookup.graph.provider_api != api
        || child_removal.graph.provider_api != api
    {
        return Err(Rejection::Unsupported);
    }
    let mut i = CoreInspection { program, work };

    let ledger = i.branch(entry_body)?;
    expect_variable(&mut i, ledger.scrutinee(), a[0])?;
    let [ledger_arm] = ledger.arms() else {
        return Err(Rejection::Unsupported);
    };
    let [next, records, outputs] =
        pattern_fields::<3>(ledger_arm.pattern(), c.state.ledger, i.work)?;
    let branch = i.branch(ledger_arm.body())?;
    let live = [
        a[0],
        a[1],
        a[2],
        a[3],
        next,
        records,
        outputs,
        d.record_lookup.binder,
        d.record.binder,
    ];
    require_distinct(i.work, &live)?;
    call(
        &mut i,
        branch.scrutinee(),
        d.record_lookup.binder,
        &[a[1], records],
        api,
        &live,
    )?;
    let [absent, present] = branch.arms() else {
        return Err(Rejection::Unsupported);
    };
    if constructor_pattern(absent.pattern(), c.no_record)?.is_some() {
        return Err(Rejection::Unsupported);
    }
    expect_variable(&mut i, absent.body(), a[0])?;
    let no_record_return = absent.body();
    let found = binder_pattern(
        constructor_pattern(present.pattern(), c.has_record)?.ok_or(Rejection::Unsupported)?,
    )?;
    let live = [
        a[0],
        a[1],
        a[2],
        a[3],
        next,
        records,
        outputs,
        found,
        d.record_lookup.binder,
        d.record.binder,
    ];
    require_distinct(i.work, &live)?;
    call(
        &mut i,
        present.body(),
        d.record.binder,
        &[found, a[0], next, a[1], a[2], a[3], records, outputs],
        api,
        &live,
    )?;

    let branch = i.branch(record_body)?;
    expect_variable(&mut i, branch.scrutinee(), b[0])?;
    let [arm] = branch.arms() else {
        return Err(Rejection::Unsupported);
    };
    let [actual, parent, phase, children] =
        pattern_fields::<4>(arm.pattern(), c.state.record, i.work)?;
    let live = [
        b[0],
        b[1],
        b[2],
        b[3],
        b[4],
        b[5],
        b[6],
        b[7],
        actual,
        parent,
        phase,
        children,
        d.child_lookup.binder,
        d.child.binder,
    ];
    require_distinct(i.work, &live)?;
    let branch = i.branch(arm.body())?;
    call(
        &mut i,
        branch.scrutinee(),
        d.child_lookup.binder,
        &[b[4], children],
        api,
        &live,
    )?;
    let [absent, present] = branch.arms() else {
        return Err(Rejection::Unsupported);
    };
    if constructor_pattern(absent.pattern(), c.no_child)?.is_some() {
        return Err(Rejection::Unsupported);
    }
    expect_variable(&mut i, absent.body(), b[1])?;
    let no_child_return = absent.body();
    let found = binder_pattern(
        constructor_pattern(present.pattern(), c.has_child)?.ok_or(Rejection::Unsupported)?,
    )?;
    let live = [
        b[0],
        b[1],
        b[2],
        b[3],
        b[4],
        b[5],
        b[6],
        b[7],
        actual,
        parent,
        phase,
        children,
        found,
        d.child_lookup.binder,
        d.child.binder,
    ];
    require_distinct(i.work, &live)?;
    call(
        &mut i,
        present.body(),
        d.child.binder,
        &[
            found, b[1], b[2], b[3], b[4], b[5], b[6], b[7], actual, parent, phase, children,
        ],
        api,
        &live,
    )?;

    let branch = i.branch(child_body)?;
    expect_variable(&mut i, branch.scrutinee(), x[0])?;
    let [arm] = branch.arms() else {
        return Err(Rejection::Unsupported);
    };
    let [id, destination] = pattern_fields::<2>(arm.pattern(), c.child, i.work)?;
    let live = [
        x[0],
        x[1],
        x[2],
        x[3],
        x[4],
        x[5],
        x[6],
        x[7],
        x[8],
        x[9],
        x[10],
        x[11],
        id,
        destination,
        d.commit.binder,
    ];
    require_distinct(i.work, &live)?;
    let branch = i.branch(arm.body())?;
    integer_equal(&mut i, branch.scrutinee(), destination, x[5])?;
    let [wrong, correct] = branch.arms() else {
        return Err(Rejection::Unsupported);
    };
    if !matches!(
        wrong.pattern().kind,
        super::super::CorePatternKind::Boolean(false)
    ) || !matches!(
        correct.pattern().kind,
        super::super::CorePatternKind::Boolean(true)
    ) {
        return Err(Rejection::Unsupported);
    }
    expect_variable(&mut i, wrong.body(), x[1])?;
    let wrong_peer_return = wrong.body();
    call(
        &mut i,
        correct.body(),
        d.commit.binder,
        &[x[2], x[3], x[4], x[6], x[7], x[8], x[9], x[10], x[11]],
        api,
        &live,
    )?;

    let branch = i.branch(commit_body)?;
    call(
        &mut i,
        branch.scrutinee(),
        d.child_removal.binder,
        &[m[2], m[8]],
        api,
        &m,
    )?;
    let [arm] = branch.arms() else {
        return Err(Rejection::Unsupported);
    };
    let (remaining, status) = pattern_pair(arm.pattern())?;
    let (remaining, status) = (binder_pattern(remaining)?, binder_pattern(status)?);
    let live = [
        m[0],
        m[1],
        m[2],
        m[3],
        m[4],
        m[5],
        m[6],
        m[7],
        m[8],
        remaining,
        status,
        d.record_update.binder,
    ];
    require_distinct(i.work, &live)?;
    let result = constructor_application(&mut i, arm.body(), c.state.ledger, 3, api)?;
    expect_variable(&mut i, result.arguments.fields[0], m[0])?;
    expect_variable(&mut i, result.arguments.fields[2], m[4])?;
    let updated = registration_call(
        &mut i,
        result.arguments.fields[1],
        d.record_update.binder,
        3,
        api,
    )?;
    expect_variable(&mut i, updated.fields[0], m[1])?;
    expect_variable(&mut i, updated.fields[2], m[3])?;
    let replacement = constructor_application(&mut i, updated.fields[1], c.state.record, 4, api)?;
    for (node, binder) in replacement
        .arguments
        .fields
        .iter()
        .zip([m[5], m[6], m[7], remaining])
    {
        expect_variable(&mut i, *node, binder)?;
    }
    check_registration_contexts(
        i.work,
        &[
            result.arguments.context_binder,
            updated.context_binder,
            replacement.arguments.context_binder,
        ],
        &live,
    )?;
    i.work.charge(11).map_err(|()| Rejection::Exhausted)?;
    let returns = [
        no_record_return,
        no_child_return,
        wrong_peer_return,
        arm.body(),
    ];
    let successor_fields = [
        result.arguments.fields[0],
        result.arguments.fields[1],
        result.arguments.fields[2],
    ];
    let replacement_fields = [
        replacement.arguments.fields[0],
        replacement.arguments.fields[1],
        replacement.arguments.fields[2],
        replacement.arguments.fields[3],
    ];
    Ok(ConditionalAcknowledgement {
        arena: program,
        linked,
        stages,
        record_lookup,
        child_lookup,
        record_update,
        child_removal,
        returns,
        successor_fields,
        replacement_fields,
    })
}

/// A call-bound conditional witness; the supplied peer still requires N4 authentication.
pub(in crate::core) struct ConditionalAcknowledgementCall<'a> {
    summary: ConditionalAcknowledgement<'a>,
    definitions: AcknowledgementDefinitions,
    constructors: AcknowledgementConstructors,
    call: NodeId,
    arguments: CheckedPersistentTuple<'a>,
}

impl ConditionalAcknowledgementCall<'_> {
    pub(in crate::core) fn same_definition(&self, other: &Self) -> bool {
        std::ptr::eq(self.summary.arena, other.summary.arena)
            && std::ptr::eq(self.summary.linked, other.summary.linked)
            && self.definitions == other.definitions
            && self.constructors == other.constructors
    }
    /// Optional exact capture-free Work constructor used as the child
    /// argument. Its provider and actual execution remain caller premises.
    pub(in crate::core) fn checked_work_argument(
        &self,
        work: &mut TypeWorkBudget,
    ) -> Result<(NodeId, NodeId), Rejection> {
        let mut inspect = CoreInspection {
            program: self.summary.arena,
            work,
        };
        let application = constructor_application(
            &mut inspect,
            self.arguments.fields[2],
            self.constructors.state.work,
            2,
            self.provider_api(),
        )?;
        for &operand in application.arguments.fields {
            if !matches!(
                inspect.kind(operand)?,
                EffectExprKind::Pure(PureExprKind::Value(super::super::PureValue::Integer(_)))
            ) {
                return Err(Rejection::Unsupported);
            }
        }
        Ok((application.call, application.closure.closure))
    }
    pub(in crate::core) fn call(&self) -> NodeId {
        self.call
    }
    pub(in crate::core) fn input(&self) -> NodeId {
        self.arguments.fields[0]
    }
    pub(in crate::core) fn arguments(&self) -> &[NodeId] {
        self.arguments.fields
    }
    pub(in crate::core) fn argument_binding(&self) -> NodeId {
        self.arguments.root
    }
    pub(in crate::core) fn argument_query(&self) -> NodeId {
        self.arguments.query
    }
    pub(in crate::core) fn argument_context(&self) -> NodeId {
        self.arguments.context
    }
    pub(in crate::core) fn closure(&self) -> NodeId {
        self.summary.stages[0].closure
    }
    pub(in crate::core) fn provider_api(&self) -> crate::module::ModuleId {
        self.summary.stages[0].api
    }
    pub(in crate::core) fn definition_query(&self) -> NodeId {
        self.summary.stages[0].query
    }
    pub(in crate::core) fn definition_binding(&self) -> NodeId {
        self.summary.stages[0].root
    }
    pub(in crate::core) fn definition_context(&self) -> NodeId {
        self.summary.stages[0].context
    }
    pub(in crate::core) fn entry_captures(&self) -> &[NodeId] {
        self.summary.stages[0].captures
    }
    pub(in crate::core) fn return_expressions(&self) -> [NodeId; 4] {
        self.summary.returns
    }
    /// Ordered Ledger and replacement-Record operands; no separate status is returned.
    pub(in crate::core) fn successor_fields(&self) -> [NodeId; 3] {
        self.summary.successor_fields
    }
    pub(in crate::core) fn replacement_fields(&self) -> [NodeId; 4] {
        self.summary.replacement_fields
    }
    pub(in crate::core) fn definition_roots(&self) -> [NodeId; 11] {
        let d = self.definitions;
        [
            d.entry.initializer,
            d.record.initializer,
            d.child.initializer,
            d.commit.initializer,
            d.record_lookup.initializer,
            d.child_lookup.initializer,
            d.record_update.initializer,
            d.child_removal.initializer,
            d.comparison.initializer,
            d.record_projection.initializer,
            d.child_projection.initializer,
        ]
    }
    pub(in crate::core) fn linked_helpers(&self) -> [(BinderId, NodeId); 11] {
        let d = self.definitions;
        let g = &self.summary;
        [
            (d.entry.binder, g.stages[0].closure),
            (d.record.binder, g.stages[1].closure),
            (d.child.binder, g.stages[2].closure),
            (d.commit.binder, g.stages[3].closure),
            (
                d.record_lookup.binder,
                g.record_lookup.graph.definition.closure,
            ),
            (
                d.child_lookup.binder,
                g.child_lookup.graph.definition.closure,
            ),
            (
                d.record_update.binder,
                g.record_update.graph.definition.closure,
            ),
            (
                d.child_removal.binder,
                g.child_removal.graph.definition.closure,
            ),
            (d.comparison.binder, g.child_lookup.graph.comparison.closure),
            (
                d.record_projection.binder,
                g.record_lookup.graph.projection.definition.closure,
            ),
            (
                d.child_projection.binder,
                g.child_lookup.graph.projection.closure,
            ),
        ]
    }
}

pub(in crate::core) fn check_nominated_acknowledgement_call<'a>(
    program: &'a dyn LedgerArena,
    linked: &'a ValidatedInterfaceProgram,
    call: NodeId,
    definitions: AcknowledgementDefinitions,
    constructors: AcknowledgementConstructors,
    work: &mut TypeWorkBudget,
) -> Result<ConditionalAcknowledgementCall<'a>, Rejection> {
    let mut inspect = CoreInspection { program, work };
    let application = inspect.application(call)?;
    if inspect.variable(application.function())? != definitions.entry.binder {
        return Err(Rejection::Unsupported);
    }
    let summary = check_conditional_acknowledgement(
        program,
        linked,
        definitions,
        constructors,
        inspect.work,
    )?;
    let arguments = registration_call(
        &mut inspect,
        call,
        definitions.entry.binder,
        4,
        summary.stages[0].api,
    )?;
    Ok(ConditionalAcknowledgementCall {
        summary,
        definitions,
        constructors,
        call,
        arguments,
    })
}
