//! Conditional reconstruction of a received Work installation.
//!
//! The witness establishes no current ledger, message origin or dispatch right.
use super::acknowledgement::{call, pattern_fields, stage};
use super::{
    BinderId, CheckedPersistentTuple, CheckedStoredFunction, ConditionalRecordOperation,
    CoreInspection, DefinitionCandidate, InitializationConstructors, InsertConstructors,
    InsertGraph, LedgerArena, NodeId, RecordListConstructors, RecordOperation, Rejection,
    TypeWorkBudget, ValidatedInterfaceProgram, binder_pattern, bool_value,
    check_conditional_record_operation, check_initialization_nominals, check_registration_contexts,
    constructor_application, constructor_pattern, expect_variable, nullary_constructor,
    reconstruct_insert_graph, registration_call, require_distinct,
};
use crate::types::ConstructorId;

#[derive(Clone, Copy, Eq, PartialEq)]
pub(in crate::core) struct InstallationDefinitions {
    pub(in crate::core) entry: DefinitionCandidate,
    pub(in crate::core) finish: DefinitionCandidate,
    pub(in crate::core) lookup: DefinitionCandidate,
    pub(in crate::core) insertion: DefinitionCandidate,
    pub(in crate::core) comparison: DefinitionCandidate,
    pub(in crate::core) projection: DefinitionCandidate,
}

#[derive(Clone, Copy, Eq, PartialEq)]
pub(in crate::core) struct InstallationConstructors {
    pub(in crate::core) state: InitializationConstructors,
    pub(in crate::core) no_record: ConstructorId,
    pub(in crate::core) has_record: ConstructorId,
}

/// Definition-bound result; the actual caller establishes finite represented
/// input, provider selection, decoded field origin and currentness.
pub(in crate::core) struct ConditionalInstallation<'a> {
    arena: &'a dyn LedgerArena,
    linked: &'a ValidatedInterfaceProgram,
    entry: CheckedStoredFunction<'a>,
    finish: CheckedStoredFunction<'a>,
    lookup: ConditionalRecordOperation<'a>,
    insertion: InsertGraph<'a>,
    returns: [NodeId; 4],
    successor_fields: [NodeId; 3],
    record_fields: [NodeId; 4],
}

fn rejected(
    inspect: &mut CoreInspection<'_, '_>,
    node: NodeId,
    ledger: BinderId,
    api: crate::module::ModuleId,
    live: &[BinderId],
) -> Result<(), Rejection> {
    let pair = inspect.persistent_tuple(node, None)?;
    let [actual, status] = pair.fields else {
        return Err(Rejection::Unsupported);
    };
    if pair.api != api {
        return Err(Rejection::Unsupported);
    }
    expect_variable(inspect, *actual, ledger)?;
    bool_value(inspect, *status, false)?;
    check_registration_contexts(inspect.work, &[pair.context_binder], live)
}

pub(in crate::core) fn check_conditional_installation<'a>(
    program: &'a dyn LedgerArena,
    linked: &'a ValidatedInterfaceProgram,
    d: InstallationDefinitions,
    c: InstallationConstructors,
    work: &mut TypeWorkBudget,
) -> Result<ConditionalInstallation<'a>, Rejection> {
    check_initialization_nominals(program, c.state, work)?;
    require_distinct(
        work,
        &[
            d.entry.binder,
            d.finish.binder,
            d.lookup.binder,
            d.insertion.binder,
            d.comparison.binder,
            d.projection.binder,
        ],
    )?;
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
    let insertion = reconstruct_insert_graph(
        program,
        linked,
        d.insertion,
        InsertConstructors {
            entry: c.state.record,
            empty: c.state.records_empty,
            more: c.state.records_more,
        },
        work,
    )?;
    let (entry, args, body) = stage(program, linked, d.entry, &[d.finish.binder], 3, work)?;
    let (finish, finish_args, finish_body) = stage(
        program,
        linked,
        d.finish,
        &[d.lookup.binder, d.insertion.binder],
        3,
        work,
    )?;
    let [finish_ledger, finish_child, finish_parent] = finish_args.as_slice() else {
        return Err(Rejection::Unsupported);
    };
    let [ledger, child, parent] = args.as_slice() else {
        return Err(Rejection::Unsupported);
    };
    let api = entry.api;
    if finish.api != api || lookup.graph.definition.api != api || insertion.provider_api != api {
        return Err(Rejection::Unsupported);
    }
    let mut inspect = CoreInspection { program, work };
    let branch = inspect.branch(body)?;
    expect_variable(&mut inspect, branch.scrutinee(), *child)?;
    let [root, work_arm] = branch.arms() else {
        return Err(Rejection::Unsupported);
    };
    if constructor_pattern(root.pattern(), c.state.root)?.is_some() {
        return Err(Rejection::Unsupported);
    }
    let [allocator, serial] = pattern_fields::<2>(work_arm.pattern(), c.state.work, inspect.work)?;
    let live = [*ledger, *child, *parent, allocator, serial, d.finish.binder];
    require_distinct(inspect.work, &live)?;
    rejected(&mut inspect, root.body(), *ledger, api, &live)?;

    let parents = inspect.branch(work_arm.body())?;
    expect_variable(&mut inspect, parents.scrutinee(), *parent)?;
    let [no_parent, parent_arm] = parents.arms() else {
        return Err(Rejection::Unsupported);
    };
    if constructor_pattern(no_parent.pattern(), c.state.no_parent)?.is_some() {
        return Err(Rejection::Unsupported);
    }
    let [owner, parent_id] =
        pattern_fields::<2>(parent_arm.pattern(), c.state.parent, inspect.work)?;
    let live = [
        *ledger,
        *child,
        *parent,
        allocator,
        serial,
        owner,
        parent_id,
        d.finish.binder,
    ];
    require_distinct(inspect.work, &live)?;
    rejected(&mut inspect, no_parent.body(), *ledger, api, &live)?;
    call(
        &mut inspect,
        parent_arm.body(),
        d.finish.binder,
        &[*ledger, *child, *parent],
        api,
        &live,
    )?;

    let ledger_match = inspect.branch(finish_body)?;
    expect_variable(&mut inspect, ledger_match.scrutinee(), *finish_ledger)?;
    let [ledger_arm] = ledger_match.arms() else {
        return Err(Rejection::Unsupported);
    };
    let [next, records, outputs] =
        pattern_fields::<3>(ledger_arm.pattern(), c.state.ledger, inspect.work)?;
    let live = [
        *finish_ledger,
        *finish_child,
        *finish_parent,
        next,
        records,
        outputs,
        d.lookup.binder,
        d.insertion.binder,
    ];
    require_distinct(inspect.work, &live)?;
    let found = inspect.branch(ledger_arm.body())?;
    call(
        &mut inspect,
        found.scrutinee(),
        d.lookup.binder,
        &[*finish_child, records],
        api,
        &live,
    )?;
    let [absent, present] = found.arms() else {
        return Err(Rejection::Unsupported);
    };
    if constructor_pattern(absent.pattern(), c.no_record)?.is_some() {
        return Err(Rejection::Unsupported);
    }
    let existing = binder_pattern(
        constructor_pattern(present.pattern(), c.has_record)?.ok_or(Rejection::Unsupported)?,
    )?;
    let present_live = [
        existing,
        *finish_ledger,
        *finish_child,
        *finish_parent,
        next,
        records,
        outputs,
        d.lookup.binder,
        d.insertion.binder,
    ];
    require_distinct(inspect.work, &present_live)?;
    rejected(
        &mut inspect,
        present.body(),
        *finish_ledger,
        api,
        &present_live,
    )?;

    let result = inspect.persistent_tuple(absent.body(), None)?;
    let [successor, status] = result.fields else {
        return Err(Rejection::Unsupported);
    };
    if result.api != api {
        return Err(Rejection::Unsupported);
    }
    bool_value(&mut inspect, *status, true)?;
    let successor = constructor_application(&mut inspect, *successor, c.state.ledger, 3, api)?;
    expect_variable(&mut inspect, successor.arguments.fields[0], next)?;
    expect_variable(&mut inspect, successor.arguments.fields[2], outputs)?;
    let append = registration_call(
        &mut inspect,
        successor.arguments.fields[1],
        d.insertion.binder,
        2,
        api,
    )?;
    expect_variable(&mut inspect, append.fields[1], records)?;
    let record = constructor_application(&mut inspect, append.fields[0], c.state.record, 4, api)?;
    expect_variable(&mut inspect, record.arguments.fields[0], *finish_child)?;
    expect_variable(&mut inspect, record.arguments.fields[1], *finish_parent)?;
    let open = nullary_constructor(&mut inspect, record.arguments.fields[2], c.state.open, api)?;
    let empty = nullary_constructor(
        &mut inspect,
        record.arguments.fields[3],
        c.state.children_empty,
        api,
    )?;
    check_registration_contexts(
        inspect.work,
        &[
            result.context_binder,
            successor.arguments.context_binder,
            append.context_binder,
            record.arguments.context_binder,
            open.context_binder,
            empty.context_binder,
        ],
        &live,
    )?;
    inspect.work.charge(8).map_err(|()| Rejection::Exhausted)?;
    Ok(ConditionalInstallation {
        arena: program,
        linked,
        entry,
        finish,
        lookup,
        insertion,
        returns: [root.body(), no_parent.body(), present.body(), absent.body()],
        successor_fields: [
            successor.arguments.fields[0],
            successor.arguments.fields[1],
            successor.arguments.fields[2],
        ],
        record_fields: [
            record.arguments.fields[0],
            record.arguments.fields[1],
            record.arguments.fields[2],
            record.arguments.fields[3],
        ],
    })
}

/// Nominated actual call; a consuming worker must establish its input and
/// decoded fields in the same live focus and verify its matched return.
pub(in crate::core) struct ConditionalInstallationCall<'a> {
    summary: ConditionalInstallation<'a>,
    definitions: InstallationDefinitions,
    constructors: InstallationConstructors,
    call: NodeId,
    arguments: CheckedPersistentTuple<'a>,
}

pub(in crate::core) fn check_nominated_installation_call<'a>(
    program: &'a dyn LedgerArena,
    linked: &'a ValidatedInterfaceProgram,
    call_node: NodeId,
    definitions: InstallationDefinitions,
    constructors: InstallationConstructors,
    work: &mut TypeWorkBudget,
) -> Result<ConditionalInstallationCall<'a>, Rejection> {
    let mut inspect = CoreInspection { program, work };
    let application = inspect.application(call_node)?;
    if inspect.variable(application.function())? != definitions.entry.binder {
        return Err(Rejection::Unsupported);
    }
    let summary =
        check_conditional_installation(program, linked, definitions, constructors, inspect.work)?;
    let arguments = registration_call(
        &mut inspect,
        call_node,
        definitions.entry.binder,
        3,
        summary.entry.api,
    )?;
    Ok(ConditionalInstallationCall {
        summary,
        definitions,
        constructors,
        call: call_node,
        arguments,
    })
}

impl ConditionalInstallationCall<'_> {
    pub(in crate::core) fn same_definition(&self, other: &Self) -> bool {
        super::same_ledger_arena(self.summary.arena, other.summary.arena)
            && std::ptr::eq(self.summary.linked, other.summary.linked)
            && self.definitions == other.definitions
            && self.constructors == other.constructors
    }

    pub(in crate::core) fn call(&self) -> NodeId {
        self.call
    }

    pub(in crate::core) fn input(&self) -> NodeId {
        self.arguments.fields[0]
    }

    pub(in crate::core) fn child(&self) -> NodeId {
        self.arguments.fields[1]
    }

    pub(in crate::core) fn parent(&self) -> NodeId {
        self.arguments.fields[2]
    }

    pub(in crate::core) fn closure(&self) -> NodeId {
        self.summary.entry.closure
    }

    pub(in crate::core) fn provider_api(&self) -> crate::module::ModuleId {
        self.summary.entry.api
    }

    pub(in crate::core) fn definition_query(&self) -> NodeId {
        self.summary.entry.query
    }

    pub(in crate::core) fn definition_binding(&self) -> NodeId {
        self.summary.entry.root
    }

    pub(in crate::core) fn definition_context(&self) -> NodeId {
        self.summary.entry.context
    }

    pub(in crate::core) fn return_expressions(&self) -> [NodeId; 4] {
        self.summary.returns
    }

    pub(in crate::core) fn successor_fields(&self) -> [NodeId; 3] {
        self.summary.successor_fields
    }

    pub(in crate::core) fn record_fields(&self) -> [NodeId; 4] {
        self.summary.record_fields
    }

    pub(in crate::core) fn definition_roots(&self) -> [NodeId; 6] {
        let d = self.definitions;
        [
            d.entry.initializer,
            d.finish.initializer,
            d.lookup.initializer,
            d.insertion.initializer,
            d.comparison.initializer,
            d.projection.initializer,
        ]
    }

    pub(in crate::core) fn linked_helpers(&self) -> [(BinderId, NodeId); 6] {
        let d = self.definitions;
        let s = &self.summary;
        [
            (d.entry.binder, s.entry.closure),
            (d.finish.binder, s.finish.closure),
            (d.lookup.binder, s.lookup.graph.definition.closure),
            (d.insertion.binder, s.insertion.definition.closure),
            (d.comparison.binder, s.lookup.graph.comparison.closure),
            (
                d.projection.binder,
                s.lookup.graph.projection.definition.closure,
            ),
        ]
    }
}

/// Source coordinates for the actual returned tuple and ordered Bool match.
/// The owning focus must still establish its returned ports and selected arm.
pub(in crate::core) struct InstallationResultMatch {
    pub(in crate::core) matching: NodeId,
    pub(in crate::core) ledger: BinderId,
    pub(in crate::core) status: BinderId,
    pub(in crate::core) status_match: NodeId,
    pub(in crate::core) installed: NodeId,
    pub(in crate::core) rejected: NodeId,
}

pub(in crate::core) fn check_installation_result_match(
    program: &dyn LedgerArena,
    installation: &ConditionalInstallationCall<'_>,
    matching: NodeId,
    work: &mut TypeWorkBudget,
) -> Result<InstallationResultMatch, Rejection> {
    if !super::same_ledger_arena(program, installation.summary.arena) {
        return Err(Rejection::Unsupported);
    }
    let mut inspect = CoreInspection { program, work };
    let branch = inspect.branch(matching)?;
    if branch.scrutinee() != installation.call {
        return Err(Rejection::Unsupported);
    }
    let [arm] = branch.arms() else {
        return Err(Rejection::Unsupported);
    };
    let super::super::CorePatternKind::Tuple(fields) = &arm.pattern().kind else {
        return Err(Rejection::Unsupported);
    };
    let [ledger, status] = fields.as_ref() else {
        return Err(Rejection::Unsupported);
    };
    let ledger = binder_pattern(ledger)?;
    let status = binder_pattern(status)?;
    require_distinct(inspect.work, &[ledger, status])?;
    let status_match = arm.body();
    let branch = inspect.branch(status_match)?;
    expect_variable(&mut inspect, branch.scrutinee(), status)?;
    let [installed, rejected] = branch.arms() else {
        return Err(Rejection::Unsupported);
    };
    if !matches!(
        installed.pattern().kind,
        super::super::CorePatternKind::Boolean(true)
    ) || !matches!(
        rejected.pattern().kind,
        super::super::CorePatternKind::Boolean(false)
    ) {
        return Err(Rejection::Unsupported);
    }
    Ok(InstallationResultMatch {
        matching,
        ledger,
        status,
        status_match,
        installed: installed.body(),
        rejected: rejected.body(),
    })
}
