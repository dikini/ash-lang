//! Draft child module for ledger_checker.rs. It publishes no currentness fact.
use super::*;
use crate::types::ConstructorId;

#[derive(Clone, Copy, Eq, PartialEq)]
pub(in crate::core) struct RetirementDefinitions {
    pub(in crate::core) entry: DefinitionCandidate,
    pub(in crate::core) work: DefinitionCandidate,
    pub(in crate::core) found: DefinitionCandidate,
    pub(in crate::core) parent: DefinitionCandidate,
    pub(in crate::core) phase: DefinitionCandidate,
    pub(in crate::core) children: DefinitionCandidate,
    pub(in crate::core) commit: DefinitionCandidate,
    pub(in crate::core) lookup: DefinitionCandidate,
    pub(in crate::core) removal: DefinitionCandidate,
    pub(in crate::core) append_output: DefinitionCandidate,
    pub(in crate::core) comparison: DefinitionCandidate,
    pub(in crate::core) projection: DefinitionCandidate,
}

#[derive(Clone, Copy, Eq, PartialEq)]
pub(in crate::core) struct RetirementConstructors {
    pub(in crate::core) state: InitializationConstructors,
    pub(in crate::core) no_record: ConstructorId,
    pub(in crate::core) has_record: ConstructorId,
    pub(in crate::core) found: ConstructorId,
    pub(in crate::core) missing: ConstructorId,
    pub(in crate::core) ack: ConstructorId,
}

/// All witnesses refer to one arena and linked program. This conditional law
/// assumes finite unique represented inputs, actual captures and faithful
/// selected allocation. It grants no currentness or network authority.
pub(in crate::core) struct ConditionalRetirement<'a> {
    arena: &'a dyn LedgerArena,
    linked: &'a ValidatedInterfaceProgram,
    stages: [CheckedStoredFunction<'a>; 7],
    lookup: ConditionalRecordOperation<'a>,
    removal: ConditionalRecordRemoval<'a>,
    append: ConditionalSpineInsertion<'a>,
    returns: [NodeId; 6],
    successor_fields: [NodeId; 3],
}

fn stage<'a>(
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

fn pattern_fields<const N: usize>(
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

fn call<'a>(
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

/// Reconstruct the linked fixture's complete transition. Dynamic captures and
/// actual selected provider are separate call-site premises.
pub(in crate::core) fn check_conditional_retirement<'a>(
    program: &'a dyn LedgerArena,
    linked: &'a ValidatedInterfaceProgram,
    d: RetirementDefinitions,
    c: RetirementConstructors,
    work: &mut TypeWorkBudget,
) -> Result<ConditionalRetirement<'a>, Rejection> {
    use crate::types::Type;
    check_initialization_nominals(program, c.state, work)?;
    exact_nominal_pair(program, c.no_record, c.has_record, work)?;
    exact_nominal_pair(program, c.found, c.missing, work)?;
    work.charge(3).map_err(|()| Rejection::Exhausted)?;
    let registry = program.registry();
    if registry
        .constructor(c.no_record)
        .ok_or(Rejection::Unsupported)?
        .payload
        .is_some()
        || !matches!(&registry.constructor(c.has_record).ok_or(Rejection::Unsupported)?.payload,
            Some(Type::Nominal(id)) if *id == c.state.record.owner())
        || !matches!(&registry.constructor(c.ack).ok_or(Rejection::Unsupported)?.payload,
            Some(Type::Tuple(fields)) if matches!(fields.as_ref(), [Type::Nominal(parent), Type::Nominal(id)]
                if *parent == c.state.parent.owner() && *id == c.state.root.owner()))
    {
        return Err(Rejection::Unsupported);
    }
    let names = [
        d.entry.binder,
        d.work.binder,
        d.found.binder,
        d.parent.binder,
        d.phase.binder,
        d.children.binder,
        d.commit.binder,
        d.lookup.binder,
        d.removal.binder,
        d.append_output.binder,
        d.comparison.binder,
        d.projection.binder,
    ];
    require_distinct(work, &names)?;
    let lookup = check_conditional_record_operation(
        program,
        linked,
        d.lookup,
        d.comparison,
        d.projection,
        RecordListConstructors {
            root: c.state.root,
            work: c.state.work,
            record: c.state.record,
            empty: c.state.records_empty,
            more: c.state.records_more,
            absent: c.no_record,
            present: c.has_record,
        },
        RecordOperation::Lookup,
        work,
    )?;
    let removal = check_conditional_record_removal(
        program,
        linked,
        d.removal,
        RemovalConstructors {
            empty: c.state.records_empty,
            more: c.state.records_more,
            found: c.found,
            missing: c.missing,
            root_id: c.state.root,
            work_id: c.state.work,
            entry: c.state.record,
        },
        RemovalDependencies {
            comparison: d.comparison,
            projection: d.projection,
        },
        work,
    )?;
    let append = check_conditional_spine_insertion(
        program,
        linked,
        d.append_output,
        InsertConstructors {
            entry: c.ack,
            empty: c.state.outputs_empty,
            more: c.state.outputs_more,
        },
        work,
    )?;
    let (entry, a, entry_body) = stage(program, linked, d.entry, &[d.work.binder], 2, work)?;
    let (worker, b, work_body) = stage(
        program,
        linked,
        d.work,
        &[d.lookup.binder, d.found.binder],
        5,
        work,
    )?;
    let (found, f, found_body) = stage(program, linked, d.found, &[d.parent.binder], 6, work)?;
    let (parent, p, parent_body) = stage(program, linked, d.parent, &[d.phase.binder], 8, work)?;
    let (phase, h, phase_body) = stage(program, linked, d.phase, &[d.children.binder], 8, work)?;
    let (children, k, children_body) =
        stage(program, linked, d.children, &[d.commit.binder], 7, work)?;
    let (commit, m, commit_body) = stage(
        program,
        linked,
        d.commit,
        &[d.removal.binder, d.append_output.binder],
        5,
        work,
    )?;
    let api = entry.api;
    let stages = [entry, worker, found, parent, phase, children, commit];
    work.charge(10).map_err(|()| Rejection::Exhausted)?;
    if stages.iter().any(|s| s.api != api)
        || lookup.graph.definition.api != api
        || removal.graph.provider_api != api
        || append.graph.provider_api != api
    {
        return Err(Rejection::Unsupported);
    }
    let mut i = CoreInspection { program, work };

    // Entry: decompose the actual input and forbid retirement of Root.
    let ledger = i.branch(entry_body)?;
    expect_variable(&mut i, ledger.scrutinee(), a[0])?;
    let [ledger_arm] = ledger.arms() else {
        return Err(Rejection::Unsupported);
    };
    let [next, records, outputs] =
        pattern_fields::<3>(ledger_arm.pattern(), c.state.ledger, i.work)?;
    let ids = i.branch(ledger_arm.body())?;
    expect_variable(&mut i, ids.scrutinee(), a[1])?;
    let [root, work_arm] = ids.arms() else {
        return Err(Rejection::Unsupported);
    };
    if constructor_pattern(root.pattern(), c.state.root)?.is_some() {
        return Err(Rejection::Unsupported);
    }
    let [owner, serial] = pattern_fields::<2>(work_arm.pattern(), c.state.work, i.work)?;
    expect_variable(&mut i, root.body(), a[0])?;
    let root_return = root.body();
    let live = [
        a[0],
        a[1],
        next,
        records,
        outputs,
        owner,
        serial,
        d.work.binder,
    ];
    require_distinct(i.work, &live)?;
    call(
        &mut i,
        work_arm.body(),
        d.work.binder,
        &[a[0], next, a[1], records, outputs],
        api,
        &live,
    )?;

    // Lookup is on the same ID and records; both branches are covered.
    let branch = i.branch(work_body)?;
    call(
        &mut i,
        branch.scrutinee(),
        d.lookup.binder,
        &[b[2], b[3]],
        api,
        &b,
    )?;
    let [missing, present] = branch.arms() else {
        return Err(Rejection::Unsupported);
    };
    if constructor_pattern(missing.pattern(), c.no_record)?.is_some() {
        return Err(Rejection::Unsupported);
    }
    expect_variable(&mut i, missing.body(), b[0])?;
    let missing_return = missing.body();
    let record = binder_pattern(
        constructor_pattern(present.pattern(), c.has_record)?.ok_or(Rejection::Unsupported)?,
    )?;
    require_distinct(
        i.work,
        &[b[0], b[1], b[2], b[3], b[4], record, d.found.binder],
    )?;
    call(
        &mut i,
        present.body(),
        d.found.binder,
        &[record, b[0], b[1], b[2], b[3], b[4]],
        api,
        &[b[0], b[1], b[2], b[3], b[4], record, d.found.binder],
    )?;

    let branch = i.branch(found_body)?;
    expect_variable(&mut i, branch.scrutinee(), f[0])?;
    let [arm] = branch.arms() else {
        return Err(Rejection::Unsupported);
    };
    let [actual, par, ph, ch] = pattern_fields::<4>(arm.pattern(), c.state.record, i.work)?;
    require_distinct(
        i.work,
        &[
            f[0],
            f[1],
            f[2],
            f[3],
            f[4],
            f[5],
            actual,
            par,
            ph,
            ch,
            d.parent.binder,
        ],
    )?;
    call(
        &mut i,
        arm.body(),
        d.parent.binder,
        &[par, ph, ch, f[1], f[2], f[3], f[4], f[5]],
        api,
        &[
            f[0],
            f[1],
            f[2],
            f[3],
            f[4],
            f[5],
            actual,
            par,
            ph,
            ch,
            d.parent.binder,
        ],
    )?;

    let branch = i.branch(parent_body)?;
    expect_variable(&mut i, branch.scrutinee(), p[0])?;
    let [none, some] = branch.arms() else {
        return Err(Rejection::Unsupported);
    };
    if constructor_pattern(none.pattern(), c.state.no_parent)?.is_some() {
        return Err(Rejection::Unsupported);
    }
    let [owner, id] = pattern_fields::<2>(some.pattern(), c.state.parent, i.work)?;
    require_distinct(
        i.work,
        &[
            p[0],
            p[1],
            p[2],
            p[3],
            p[4],
            p[5],
            p[6],
            p[7],
            owner,
            id,
            d.phase.binder,
        ],
    )?;
    expect_variable(&mut i, none.body(), p[3])?;
    let no_parent_return = none.body();
    call(
        &mut i,
        some.body(),
        d.phase.binder,
        &[p[1], p[2], p[3], p[4], p[5], p[6], p[7], p[0]],
        api,
        &[
            p[0],
            p[1],
            p[2],
            p[3],
            p[4],
            p[5],
            p[6],
            p[7],
            owner,
            id,
            d.phase.binder,
        ],
    )?;

    let branch = i.branch(phase_body)?;
    expect_variable(&mut i, branch.scrutinee(), h[0])?;
    let [open, closed] = branch.arms() else {
        return Err(Rejection::Unsupported);
    };
    if constructor_pattern(open.pattern(), c.state.open)?.is_some()
        || constructor_pattern(closed.pattern(), c.state.closed)?.is_some()
    {
        return Err(Rejection::Unsupported);
    }
    expect_variable(&mut i, open.body(), h[2])?;
    let open_return = open.body();
    call(
        &mut i,
        closed.body(),
        d.children.binder,
        &[h[1], h[2], h[3], h[4], h[5], h[6], h[7]],
        api,
        &[
            h[0],
            h[1],
            h[2],
            h[3],
            h[4],
            h[5],
            h[6],
            h[7],
            d.children.binder,
        ],
    )?;

    let branch = i.branch(children_body)?;
    expect_variable(&mut i, branch.scrutinee(), k[0])?;
    let [empty, more] = branch.arms() else {
        return Err(Rejection::Unsupported);
    };
    if constructor_pattern(empty.pattern(), c.state.children_empty)?.is_some() {
        return Err(Rejection::Unsupported);
    }
    let [child, tail] = pattern_fields::<2>(more.pattern(), c.state.children_more, i.work)?;
    require_distinct(
        i.work,
        &[
            k[0],
            k[1],
            k[2],
            k[3],
            k[4],
            k[5],
            k[6],
            child,
            tail,
            d.commit.binder,
        ],
    )?;
    expect_variable(&mut i, more.body(), k[1])?;
    let nonempty_return = more.body();
    call(
        &mut i,
        empty.body(),
        d.commit.binder,
        &[k[2], k[3], k[4], k[5], k[6]],
        api,
        &[
            k[0],
            k[1],
            k[2],
            k[3],
            k[4],
            k[5],
            k[6],
            child,
            tail,
            d.commit.binder,
        ],
    )?;

    let branch = i.branch(commit_body)?;
    call(
        &mut i,
        branch.scrutinee(),
        d.removal.binder,
        &[m[1], m[2]],
        api,
        &m,
    )?;
    let [arm] = branch.arms() else {
        return Err(Rejection::Unsupported);
    };
    let (remaining, status) = pattern_pair(arm.pattern())?;
    let (remaining, status) = (binder_pattern(remaining)?, binder_pattern(status)?);
    require_distinct(
        i.work,
        &[
            m[0],
            m[1],
            m[2],
            m[3],
            m[4],
            remaining,
            status,
            d.append_output.binder,
        ],
    )?;
    let result = constructor_application(&mut i, arm.body(), c.state.ledger, 3, api)?;
    expect_variable(&mut i, result.arguments.fields[0], m[0])?;
    expect_variable(&mut i, result.arguments.fields[1], remaining)?;
    let output = registration_call(
        &mut i,
        result.arguments.fields[2],
        d.append_output.binder,
        2,
        api,
    )?;
    expect_variable(&mut i, output.fields[1], m[3])?;
    let ack = constructor_application(&mut i, output.fields[0], c.ack, 2, api)?;
    expect_variable(&mut i, ack.arguments.fields[0], m[4])?;
    expect_variable(&mut i, ack.arguments.fields[1], m[1])?;
    let live = [
        m[0],
        m[1],
        m[2],
        m[3],
        m[4],
        remaining,
        status,
        d.append_output.binder,
    ];
    check_registration_contexts(
        i.work,
        &[
            result.arguments.context_binder,
            output.context_binder,
            ack.arguments.context_binder,
        ],
        &live,
    )?;
    i.work.charge(9).map_err(|()| Rejection::Exhausted)?;
    let returns = [
        root_return,
        missing_return,
        no_parent_return,
        open_return,
        nonempty_return,
        arm.body(),
    ];
    let successor_fields = [
        result.arguments.fields[0],
        result.arguments.fields[1],
        result.arguments.fields[2],
    ];
    Ok(ConditionalRetirement {
        arena: program,
        linked,
        stages,
        lookup,
        removal,
        append,
        returns,
        successor_fields,
    })
}

/// A call-bound conditional witness. The caller must still authenticate the
/// actual target/captures, provider, represented input and returned value.
pub(in crate::core) struct ConditionalRetirementCall<'a> {
    summary: ConditionalRetirement<'a>,
    definitions: RetirementDefinitions,
    constructors: RetirementConstructors,
    call: NodeId,
    arguments: CheckedPersistentTuple<'a>,
}

impl ConditionalRetirementCall<'_> {
    pub(in crate::core) fn same_definition(&self, other: &Self) -> bool {
        super::same_ledger_arena(self.summary.arena, other.summary.arena)
            && std::ptr::eq(self.summary.linked, other.summary.linked)
            && self.definitions == other.definitions
            && self.constructors == other.constructors
    }
    /// Optional exact capture-free Work constructor used as this call's
    /// second argument. This does not authenticate its runtime provider.
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
            self.arguments.fields[1],
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
    /// Return nodes are branch coordinates, not proof of a particular return.
    pub(in crate::core) fn return_expressions(&self) -> [NodeId; 6] {
        self.summary.returns
    }
    /// Ordered operands of the success Ledger constructor; no separate status is returned.
    pub(in crate::core) fn successor_fields(&self) -> [NodeId; 3] {
        self.summary.successor_fields
    }
    pub(in crate::core) fn definition_roots(&self) -> [NodeId; 12] {
        let d = self.definitions;
        [
            d.entry.initializer,
            d.work.initializer,
            d.found.initializer,
            d.parent.initializer,
            d.phase.initializer,
            d.children.initializer,
            d.commit.initializer,
            d.lookup.initializer,
            d.removal.initializer,
            d.append_output.initializer,
            d.comparison.initializer,
            d.projection.initializer,
        ]
    }
    pub(in crate::core) fn linked_helpers(&self) -> [(BinderId, NodeId); 12] {
        let d = self.definitions;
        let g = &self.summary;
        [
            (d.entry.binder, g.stages[0].closure),
            (d.work.binder, g.stages[1].closure),
            (d.found.binder, g.stages[2].closure),
            (d.parent.binder, g.stages[3].closure),
            (d.phase.binder, g.stages[4].closure),
            (d.children.binder, g.stages[5].closure),
            (d.commit.binder, g.stages[6].closure),
            (d.lookup.binder, g.lookup.graph.definition.closure),
            (d.removal.binder, g.removal.graph.definition.closure),
            (d.append_output.binder, g.append.graph.definition.closure),
            (d.comparison.binder, g.lookup.graph.comparison.closure),
            (
                d.projection.binder,
                g.lookup.graph.projection.definition.closure,
            ),
        ]
    }
}

pub(in crate::core) fn check_nominated_retirement_call<'a>(
    program: &'a dyn LedgerArena,
    linked: &'a ValidatedInterfaceProgram,
    call: NodeId,
    definitions: RetirementDefinitions,
    constructors: RetirementConstructors,
    work: &mut TypeWorkBudget,
) -> Result<ConditionalRetirementCall<'a>, Rejection> {
    let mut inspect = CoreInspection { program, work };
    let application = inspect.application(call)?;
    if inspect.variable(application.function())? != definitions.entry.binder {
        return Err(Rejection::Unsupported);
    }
    let summary =
        check_conditional_retirement(program, linked, definitions, constructors, inspect.work)?;
    let arguments = registration_call(
        &mut inspect,
        call,
        definitions.entry.binder,
        2,
        summary.stages[0].api,
    )?;
    Ok(ConditionalRetirementCall {
        summary,
        definitions,
        constructors,
        call,
        arguments,
    })
}
