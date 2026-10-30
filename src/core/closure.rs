//! Conditional, definition-bound ledger Close checking. No authority is published.
use super::acknowledgement::{call, pattern_fields, stage};
use super::*;
use crate::types::ConstructorId;

#[derive(Clone, Copy, Eq, PartialEq)]
pub(in crate::core) struct ClosureDefinitions {
    pub(in crate::core) entry: DefinitionCandidate,
    pub(in crate::core) finish: DefinitionCandidate,
    pub(in crate::core) lookup: DefinitionCandidate,
    pub(in crate::core) update: DefinitionCandidate,
    pub(in crate::core) comparison: DefinitionCandidate,
    pub(in crate::core) projection: DefinitionCandidate,
}

#[derive(Clone, Copy, Eq, PartialEq)]
pub(in crate::core) struct ClosureConstructors {
    pub(in crate::core) state: InitializationConstructors,
    pub(in crate::core) no_record: ConstructorId,
    pub(in crate::core) has_record: ConstructorId,
}

/// This binds a modeled Close body to actual definitions. Finite represented
/// input, captures, selected provider and currentness remain caller premises.
pub(in crate::core) struct ConditionalClosure<'a> {
    arena: &'a dyn LedgerArena,
    linked: &'a ValidatedInterfaceProgram,
    stages: [CheckedStoredFunction<'a>; 2],
    lookup: ConditionalRecordOperation<'a>,
    update: ConditionalRecordOperation<'a>,
    returns: [NodeId; 3],
    successor_fields: [NodeId; 3],
    replacement_fields: [NodeId; 4],
}

pub(in crate::core) fn check_conditional_closure<'a>(
    program: &'a dyn LedgerArena,
    linked: &'a ValidatedInterfaceProgram,
    d: ClosureDefinitions,
    c: ClosureConstructors,
    work: &mut TypeWorkBudget,
) -> Result<ConditionalClosure<'a>, Rejection> {
    check_initialization_nominals(program, c.state, work)?;
    require_distinct(
        work,
        &[
            d.entry.binder,
            d.finish.binder,
            d.lookup.binder,
            d.update.binder,
            d.comparison.binder,
            d.projection.binder,
        ],
    )?;
    let records = RecordListConstructors {
        root: c.state.root,
        work: c.state.work,
        record: c.state.record,
        empty: c.state.records_empty,
        more: c.state.records_more,
        absent: c.no_record,
        present: c.has_record,
    };
    let lookup = check_conditional_record_operation(
        program,
        linked,
        d.lookup,
        d.comparison,
        d.projection,
        records,
        RecordOperation::Lookup,
        work,
    )?;
    let update = check_conditional_record_operation(
        program,
        linked,
        d.update,
        d.comparison,
        d.projection,
        records,
        RecordOperation::Update,
        work,
    )?;
    let (entry, a, entry_body) = stage(
        program,
        linked,
        d.entry,
        &[d.lookup.binder, d.finish.binder],
        2,
        work,
    )?;
    let (finish, b, finish_body) = stage(program, linked, d.finish, &[d.update.binder], 6, work)?;
    let stages = [entry, finish];
    let api = entry.api;
    work.charge(4).map_err(|()| Rejection::Exhausted)?;
    if finish.api != api || lookup.graph.definition.api != api || update.graph.definition.api != api
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
    let live = [
        a[0],
        a[1],
        next,
        records,
        outputs,
        d.lookup.binder,
        d.finish.binder,
    ];
    require_distinct(i.work, &live)?;
    let branch = i.branch(ledger_arm.body())?;
    call(
        &mut i,
        branch.scrutinee(),
        d.lookup.binder,
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
    let found = binder_pattern(
        constructor_pattern(present.pattern(), c.has_record)?.ok_or(Rejection::Unsupported)?,
    )?;
    let live = [
        a[0],
        a[1],
        next,
        records,
        outputs,
        found,
        d.lookup.binder,
        d.finish.binder,
    ];
    require_distinct(i.work, &live)?;
    call(
        &mut i,
        present.body(),
        d.finish.binder,
        &[found, a[0], next, a[1], records, outputs],
        api,
        &live,
    )?;

    let record = i.branch(finish_body)?;
    expect_variable(&mut i, record.scrutinee(), b[0])?;
    let [arm] = record.arms() else {
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
        actual,
        parent,
        phase,
        children,
        d.update.binder,
    ];
    require_distinct(i.work, &live)?;
    let branch = i.branch(arm.body())?;
    expect_variable(&mut i, branch.scrutinee(), phase)?;
    let [open, closed] = branch.arms() else {
        return Err(Rejection::Unsupported);
    };
    if constructor_pattern(open.pattern(), c.state.open)?.is_some()
        || constructor_pattern(closed.pattern(), c.state.closed)?.is_some()
    {
        return Err(Rejection::Unsupported);
    }
    expect_variable(&mut i, closed.body(), b[1])?;
    let result = constructor_application(&mut i, open.body(), c.state.ledger, 3, api)?;
    expect_variable(&mut i, result.arguments.fields[0], b[2])?;
    expect_variable(&mut i, result.arguments.fields[2], b[5])?;
    let updated = registration_call(&mut i, result.arguments.fields[1], d.update.binder, 3, api)?;
    expect_variable(&mut i, updated.fields[0], b[3])?;
    expect_variable(&mut i, updated.fields[2], b[4])?;
    let replacement = constructor_application(&mut i, updated.fields[1], c.state.record, 4, api)?;
    expect_variable(&mut i, replacement.arguments.fields[0], actual)?;
    expect_variable(&mut i, replacement.arguments.fields[1], parent)?;
    let closed_value =
        nullary_constructor(&mut i, replacement.arguments.fields[2], c.state.closed, api)?;
    expect_variable(&mut i, replacement.arguments.fields[3], children)?;
    check_registration_contexts(
        i.work,
        &[
            result.arguments.context_binder,
            updated.context_binder,
            replacement.arguments.context_binder,
            closed_value.context_binder,
        ],
        &live,
    )?;
    i.work.charge(10).map_err(|()| Rejection::Exhausted)?;
    Ok(ConditionalClosure {
        arena: program,
        linked,
        stages,
        lookup,
        update,
        returns: [absent.body(), closed.body(), open.body()],
        successor_fields: [
            result.arguments.fields[0],
            result.arguments.fields[1],
            result.arguments.fields[2],
        ],
        replacement_fields: [
            replacement.arguments.fields[0],
            replacement.arguments.fields[1],
            replacement.arguments.fields[2],
            replacement.arguments.fields[3],
        ],
    })
}

/// Call-bound witness; actual entry, return, provider and currentness are
/// checked by the owning worker query.
pub(in crate::core) struct ConditionalClosureCall<'a> {
    summary: ConditionalClosure<'a>,
    definitions: ClosureDefinitions,
    constructors: ClosureConstructors,
    call: NodeId,
    arguments: CheckedPersistentTuple<'a>,
}

impl ConditionalClosureCall<'_> {
    pub(in crate::core) fn same_definition(&self, other: &Self) -> bool {
        super::same_ledger_arena(self.summary.arena, other.summary.arena)
            && std::ptr::eq(self.summary.linked, other.summary.linked)
            && self.definitions == other.definitions
            && self.constructors == other.constructors
    }
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
    pub(in crate::core) fn argument_binding(&self) -> NodeId {
        self.arguments.root
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
    pub(in crate::core) fn return_expressions(&self) -> [NodeId; 3] {
        self.summary.returns
    }
    pub(in crate::core) fn successor_fields(&self) -> [NodeId; 3] {
        self.summary.successor_fields
    }
    pub(in crate::core) fn replacement_fields(&self) -> [NodeId; 4] {
        self.summary.replacement_fields
    }
    pub(in crate::core) fn definition_roots(&self) -> [NodeId; 6] {
        let d = self.definitions;
        [
            d.entry.initializer,
            d.finish.initializer,
            d.lookup.initializer,
            d.update.initializer,
            d.comparison.initializer,
            d.projection.initializer,
        ]
    }
    pub(in crate::core) fn linked_helpers(&self) -> [(BinderId, NodeId); 6] {
        let d = self.definitions;
        let g = &self.summary;
        [
            (d.entry.binder, g.stages[0].closure),
            (d.finish.binder, g.stages[1].closure),
            (d.lookup.binder, g.lookup.graph.definition.closure),
            (d.update.binder, g.update.graph.definition.closure),
            (d.comparison.binder, g.lookup.graph.comparison.closure),
            (
                d.projection.binder,
                g.lookup.graph.projection.definition.closure,
            ),
        ]
    }
}

pub(in crate::core) fn check_nominated_closure_call<'a>(
    program: &'a dyn LedgerArena,
    linked: &'a ValidatedInterfaceProgram,
    call_node: NodeId,
    definitions: ClosureDefinitions,
    constructors: ClosureConstructors,
    work: &mut TypeWorkBudget,
) -> Result<ConditionalClosureCall<'a>, Rejection> {
    let mut inspect = CoreInspection { program, work };
    let application = inspect.application(call_node)?;
    if inspect.variable(application.function())? != definitions.entry.binder {
        return Err(Rejection::Unsupported);
    }
    let summary =
        check_conditional_closure(program, linked, definitions, constructors, inspect.work)?;
    let arguments = registration_call(
        &mut inspect,
        call_node,
        definitions.entry.binder,
        2,
        summary.stages[0].api,
    )?;
    Ok(ConditionalClosureCall {
        summary,
        definitions,
        constructors,
        call: call_node,
        arguments,
    })
}
