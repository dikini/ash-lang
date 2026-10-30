//! Independent post-link ledger analysis (under development).
//!
//! No ledger facts or network permissions are published by this module yet.

#[path = "driver.rs"]
pub(super) mod driver;
#[path = "plan.rs"]
pub(super) mod plan;

#[path = "acknowledgement.rs"]
pub(super) mod acknowledgement;
#[path = "closure.rs"]
pub(super) mod closure;
#[path = "retirement.rs"]
pub(super) mod retirement;

use std::sync::Arc;

use super::{
    EffectExprKind, EffectOperation, NodeId, PureComputation, PureExprKind, ValidatedEffectProgram,
};
use crate::{
    evidence_validation::ValidatedInterfaceProgram,
    resolved::{BinderId, ResolvedDeclarationIndex, ResolvedDefinitionKind},
    types::TypeWorkBudget,
};

/// Read-only access to one actual Core arena. A validator-stage view permits
/// reconstruction only; its provisional result is not an admission until the
/// entire enclosing validation succeeds.
pub(super) trait LedgerArena {
    fn kind_at(&self, id: NodeId) -> Option<&EffectExprKind>;
    fn root(&self) -> NodeId;
    fn registry(&self) -> &Arc<crate::resolved::ResolvedRegistry>;
    fn method_evidence(&self) -> &Arc<super::dialect::MethodEvidenceCatalog>;
    fn method_evidence_anchors(&self) -> &[super::dialect::MethodEvidenceAnchor];
}

impl LedgerArena for ValidatedEffectProgram {
    fn kind_at(&self, id: NodeId) -> Option<&EffectExprKind> {
        self.node(id).map(|node| &node.kind)
    }
    fn root(&self) -> NodeId {
        ValidatedEffectProgram::root(self)
    }
    fn registry(&self) -> &Arc<crate::resolved::ResolvedRegistry> {
        ValidatedEffectProgram::registry(self)
    }
    fn method_evidence(&self) -> &Arc<super::dialect::MethodEvidenceCatalog> {
        ValidatedEffectProgram::method_evidence(self)
    }
    fn method_evidence_anchors(&self) -> &[super::dialect::MethodEvidenceAnchor] {
        ValidatedEffectProgram::method_evidence_anchors(self)
    }
}

impl LedgerArena for super::UnvalidatedEffectProgram {
    fn kind_at(&self, id: NodeId) -> Option<&EffectExprKind> {
        if id.arena() != self.arena {
            return None;
        }
        self.nodes.get(id.index().ok()?).map(|node| &node.kind)
    }
    fn root(&self) -> NodeId {
        self.root
    }
    fn registry(&self) -> &Arc<crate::resolved::ResolvedRegistry> {
        &self.registry
    }
    fn method_evidence(&self) -> &Arc<super::dialect::MethodEvidenceCatalog> {
        &self.method_evidence
    }
    fn method_evidence_anchors(&self) -> &[super::dialect::MethodEvidenceAnchor] {
        &self.method_evidence_anchors
    }
}

/// A nomination selects a linked binder and its proposed initializer; neither
/// coordinate carries a semantic claim.
#[derive(Clone, Copy, Eq, PartialEq)]
pub(super) struct DefinitionCandidate {
    pub(super) binder: BinderId,
    pub(super) initializer: NodeId,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum Rejection {
    Unsupported,
    Exhausted,
}

/// Select one actual initializer from the complete linked global spine.
/// This is only an input to body checking: it does not establish a helper
/// postcondition or authenticate a region provider.
fn linked_initializer(
    program: &dyn LedgerArena,
    linked: &ValidatedInterfaceProgram,
    candidate: DefinitionCandidate,
    work: &mut TypeWorkBudget,
) -> Result<NodeId, Rejection> {
    linked_initializer_and_result(program, linked, candidate, work)
        .map(|(initializer, _)| initializer)
}

fn linked_initializer_and_result(
    program: &dyn LedgerArena,
    linked: &ValidatedInterfaceProgram,
    candidate: DefinitionCandidate,
    work: &mut TypeWorkBudget,
) -> Result<(NodeId, NodeId), Rejection> {
    let charge = |work: &mut TypeWorkBudget| work.charge(1).map_err(|()| Rejection::Exhausted);
    charge(work)?;
    if !Arc::ptr_eq(program.registry(), linked.registry())
        || !Arc::ptr_eq(program.method_evidence(), linked.method_evidence())
        || program.kind_at(candidate.initializer).is_none()
    {
        return Err(Rejection::Unsupported);
    }
    let node = |id: NodeId| program.kind_at(id).ok_or(Rejection::Unsupported);
    charge(work)?;
    let root = match node(program.root())? {
        EffectExprKind::Operation(EffectOperation::NativeInterpret(boundary)) => boundary.body(),
        _ => program.root(),
    };
    charge(work)?;
    let EffectExprKind::Operation(EffectOperation::Region(region)) = node(root)? else {
        return Err(Rejection::Unsupported);
    };
    if !region.entry {
        return Err(Rejection::Unsupported);
    }
    charge(work)?;
    let EffectExprKind::Operation(EffectOperation::Handler(handler)) = node(region.body)? else {
        return Err(Rejection::Unsupported);
    };
    let mut cursor = handler.body();
    let mut selected = None;
    for group in linked.groups() {
        // Foreign constants precede the single group of ordinary global
        // definitions in the linked lowering spine.
        for declaration in group.declaration_order() {
            charge(work)?;
            match *declaration {
                ResolvedDeclarationIndex::Global(index) => {
                    let definition = group
                        .definitions()
                        .get(index)
                        .ok_or(Rejection::Unsupported)?;
                    if matches!(
                        definition.kind(),
                        ResolvedDefinitionKind::ForeignConstant(_)
                    ) {
                        let scheme = group.schemes().get(index).ok_or(Rejection::Unsupported)?;
                        charge(work)?;
                        let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Bind(
                            binding,
                        ))) = node(cursor)?
                        else {
                            return Err(Rejection::Unsupported);
                        };
                        if binding.binder().id() != scheme.binder {
                            return Err(Rejection::Unsupported);
                        }
                        if scheme.binder == candidate.binder
                            && selected.replace(binding.initializer()).is_some()
                        {
                            return Err(Rejection::Unsupported);
                        }
                        cursor = binding.body();
                    }
                }
                ResolvedDeclarationIndex::Implementation(_)
                | ResolvedDeclarationIndex::Resource(_) => return Err(Rejection::Unsupported),
                _ => {}
            }
        }
        work.charge(group.declaration_order().len())
            .map_err(|()| Rejection::Exhausted)?;
        let mut expected = group
            .declaration_order()
            .iter()
            .filter_map(|declaration| {
                let ResolvedDeclarationIndex::Global(index) = *declaration else {
                    return None;
                };
                let definition = group.definitions().get(index)?;
                (!matches!(
                    definition.kind(),
                    ResolvedDefinitionKind::ForeignConstant(_)
                ))
                .then_some(index)
            })
            .peekable();
        charge(work)?;
        if expected.peek().is_some() {
            let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::RecursiveBind(
                binding,
            ))) = node(cursor)?
            else {
                return Err(Rejection::Unsupported);
            };
            for member in binding.members() {
                charge(work)?;
                let index = expected.next().ok_or(Rejection::Unsupported)?;
                let scheme = group.schemes().get(index).ok_or(Rejection::Unsupported)?;
                if member.binder().id() != scheme.binder {
                    return Err(Rejection::Unsupported);
                }
                if scheme.binder == candidate.binder
                    && selected.replace(member.initializer()).is_some()
                {
                    return Err(Rejection::Unsupported);
                }
            }
            if expected.next().is_some() {
                return Err(Rejection::Unsupported);
            }
            cursor = binding.body();
        }
    }
    match selected {
        Some(initializer) if initializer == candidate.initializer => Ok((initializer, cursor)),
        _ => Err(Rejection::Unsupported),
    }
}

/// The exact list and status constructors nominated for removal. These are
/// coordinates to check, not authority to issue a removal fact.
#[derive(Clone, Copy)]
struct RemovalConstructors {
    empty: crate::types::ConstructorId,
    more: crate::types::ConstructorId,
    found: crate::types::ConstructorId,
    missing: crate::types::ConstructorId,
    root_id: crate::types::ConstructorId,
    work_id: crate::types::ConstructorId,
    entry: crate::types::ConstructorId,
}

/// Arena-bound coordinates for a checked generated tuple. This is a shape
/// witness only: it says nothing about selected handlers or normal execution.
#[derive(Clone, Copy)]
struct CheckedPersistentTuple<'a> {
    arena: &'a dyn LedgerArena,
    root: NodeId,
    context_binder: BinderId,
    query: NodeId,
    unit: NodeId,
    tuple: NodeId,
    context: NodeId,
    storage: NodeId,
    storage_context: NodeId,
    request: NodeId,
    api: crate::module::ModuleId,
    constructor: Option<crate::types::ConstructorId>,
    fields: &'a [NodeId],
}

/// Exact linked nodes of one generated stored function. This is a shape
/// witness, not evidence of the active provider or a ledger fact.
#[derive(Clone, Copy)]
struct CheckedStoredFunction<'a> {
    arena: &'a dyn LedgerArena,
    root: NodeId,
    context_binder: BinderId,
    query: NodeId,
    unit: NodeId,
    closure: NodeId,
    context: NodeId,
    storage: NodeId,
    storage_context: NodeId,
    request: NodeId,
    api: crate::module::ModuleId,
    captures: &'a [NodeId],
    parameter: BinderId,
    body: NodeId,
}

struct CoreInspection<'a, 'w> {
    program: &'a dyn LedgerArena,
    work: &'w mut TypeWorkBudget,
}

impl<'a> CoreInspection<'a, '_> {
    fn kind(&mut self, id: NodeId) -> Result<&'a EffectExprKind, Rejection> {
        self.work.charge(1).map_err(|()| Rejection::Exhausted)?;
        self.work
            .charge(self.program.method_evidence_anchors().len())
            .map_err(|()| Rejection::Exhausted)?;
        if self
            .program
            .method_evidence_anchors()
            .iter()
            .any(|anchor| anchor.node == id)
        {
            return Err(Rejection::Unsupported);
        }
        self.program.kind_at(id).ok_or(Rejection::Unsupported)
    }

    fn variable(&mut self, id: NodeId) -> Result<BinderId, Rejection> {
        match self.kind(id)? {
            EffectExprKind::Pure(PureExprKind::Variable(variable)) => Ok(variable.binder()),
            _ => Err(Rejection::Unsupported),
        }
    }

    fn application(&mut self, id: NodeId) -> Result<super::function::ApplicationNode, Rejection> {
        match self.kind(id)? {
            EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Apply(
                application,
            ))) => Ok(*application),
            _ => Err(Rejection::Unsupported),
        }
    }

    fn stored_function(
        &mut self,
        id: NodeId,
        expected_captures: &[BinderId],
    ) -> Result<&'a super::function::FunctionNode, Rejection> {
        self.work.charge(8).map_err(|()| Rejection::Exhausted)?;
        let (_, closure) =
            super::region::closure_initializer::<super::EffectOperationFamily>(id, |id| {
                self.program.kind_at(id)
            })
            .ok_or(Rejection::Unsupported)?;
        let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Bind(bind))) =
            self.kind(id)?
        else {
            return Err(Rejection::Unsupported);
        };
        if closure.captures.len() != expected_captures.len()
            || self.variable(closure.context)? != bind.binder().id()
        {
            return Err(Rejection::Unsupported);
        }
        for expected in expected_captures {
            self.work
                .charge(closure.captures.len())
                .map_err(|()| Rejection::Exhausted)?;
            let mut count = 0;
            for capture in &closure.captures {
                if self.variable(*capture)? == *expected {
                    count += 1;
                }
            }
            if count != 1 {
                return Err(Rejection::Unsupported);
            }
        }
        let EffectExprKind::Operation(EffectOperation::RegionAllocate(storage)) =
            self.kind(closure.storage)?
        else {
            return Err(Rejection::Unsupported);
        };
        if storage.api != closure.api || self.variable(storage.context)? != bind.binder().id() {
            return Err(Rejection::Unsupported);
        }
        let EffectExprKind::Operation(EffectOperation::RegionValueRequest(layout)) =
            self.kind(storage.request)?
        else {
            return Err(Rejection::Unsupported);
        };
        if layout.api != closure.api || layout.fields != closure.captures.len() + 1 {
            return Err(Rejection::Unsupported);
        }
        closure.code.function().ok_or(Rejection::Unsupported)
    }

    /// Retain every actual node used by the modeled stored-closure rule.
    fn stored_function_witness(
        &mut self,
        id: NodeId,
        expected_captures: &[BinderId],
    ) -> Result<CheckedStoredFunction<'a>, Rejection> {
        let function = self.stored_function(id, expected_captures)?;
        self.work.charge(6).map_err(|()| Rejection::Exhausted)?;
        let (closure_id, closure) = super::region::closure_initializer::<
            super::EffectOperationFamily,
        >(id, |id| self.program.kind_at(id))
        .ok_or(Rejection::Unsupported)?;
        let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Bind(bind))) =
            self.kind(id)?
        else {
            return Err(Rejection::Unsupported);
        };
        let EffectExprKind::Operation(EffectOperation::Request(query)) =
            self.kind(bind.initializer())?
        else {
            return Err(Rejection::Unsupported);
        };
        let EffectExprKind::Operation(EffectOperation::RegionAllocate(storage)) =
            self.kind(closure.storage)?
        else {
            return Err(Rejection::Unsupported);
        };
        Ok(CheckedStoredFunction {
            arena: self.program,
            root: id,
            context_binder: bind.binder().id(),
            query: bind.initializer(),
            unit: query.operand(),
            closure: closure_id,
            context: closure.context,
            storage: closure.storage,
            storage_context: storage.context,
            request: storage.request,
            api: closure.api,
            captures: &closure.captures,
            parameter: function.parameter().id(),
            body: function.body(),
        })
    }

    fn branch(&mut self, id: NodeId) -> Result<&'a super::MatchNode, Rejection> {
        match self.kind(id)? {
            EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Match(branch))) => {
                Ok(branch)
            }
            _ => Err(Rejection::Unsupported),
        }
    }

    // Recognize the actual generated query, storage request and persistent
    // construction. This does not establish which handler/provider executes.
    fn persistent_tuple(
        &mut self,
        id: NodeId,
        expected: Option<crate::types::ConstructorId>,
    ) -> Result<CheckedPersistentTuple<'a>, Rejection> {
        let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Bind(bind))) =
            self.kind(id)?
        else {
            return Err(Rejection::Unsupported);
        };
        let EffectExprKind::Operation(EffectOperation::Request(query)) =
            self.kind(bind.initializer())?
        else {
            return Err(Rejection::Unsupported);
        };
        let EffectExprKind::Operation(EffectOperation::RegionTuple(tuple)) =
            self.kind(bind.body())?
        else {
            return Err(Rejection::Unsupported);
        };
        let api =
            crate::resolved::RegionApi::for_module(tuple.api).ok_or(Rejection::Unsupported)?;
        if tuple.constructor != expected
            || query.effect().effect() != api.default_alloc()
            || !query.effect().arguments().is_empty()
            || query.operation() != crate::types::OperationId::new(api.default_alloc(), 1)
            || !matches!(
                self.kind(query.operand())?,
                EffectExprKind::Pure(PureExprKind::Value(super::PureValue::Unit(_)))
            )
            || self.variable(tuple.context)? != bind.binder().id()
        {
            return Err(Rejection::Unsupported);
        }
        let EffectExprKind::Operation(EffectOperation::RegionAllocate(storage)) =
            self.kind(tuple.storage)?
        else {
            return Err(Rejection::Unsupported);
        };
        if storage.api != tuple.api || self.variable(storage.context)? != bind.binder().id() {
            return Err(Rejection::Unsupported);
        }
        let EffectExprKind::Operation(EffectOperation::RegionValueRequest(layout)) =
            self.kind(storage.request)?
        else {
            return Err(Rejection::Unsupported);
        };
        if layout.api != tuple.api
            || layout.fields != tuple.fields.len() + usize::from(expected.is_some())
        {
            return Err(Rejection::Unsupported);
        }
        Ok(CheckedPersistentTuple {
            arena: self.program,
            root: id,
            context_binder: bind.binder().id(),
            query: bind.initializer(),
            unit: query.operand(),
            tuple: bind.body(),
            context: tuple.context,
            storage: tuple.storage,
            storage_context: storage.context,
            request: storage.request,
            api: tuple.api,
            constructor: tuple.constructor,
            fields: &tuple.fields,
        })
    }
}

fn binder_pattern(pattern: &super::CorePattern) -> Result<BinderId, Rejection> {
    match &pattern.kind {
        super::CorePatternKind::Binder(binder) => Ok(binder.id()),
        _ => Err(Rejection::Unsupported),
    }
}

fn constructor_pattern(
    pattern: &super::CorePattern,
    expected: crate::types::ConstructorId,
) -> Result<Option<&super::CorePattern>, Rejection> {
    match &pattern.kind {
        super::CorePatternKind::Constructor {
            constructor,
            payload,
        } if *constructor == expected => Ok(payload.as_deref()),
        _ => Err(Rejection::Unsupported),
    }
}

// Reject selected method evidence anywhere in these actual body and capture
// graphs. The traversal checks every reachable child and charges before growth.
fn reject_evidence(
    program: &dyn LedgerArena,
    roots: &[NodeId],
    work: &mut TypeWorkBudget,
) -> Result<(), Rejection> {
    use std::collections::HashSet;
    let mut pending = Vec::new();
    let mut visited = HashSet::new();
    work.charge(roots.len())
        .map_err(|()| Rejection::Exhausted)?;
    pending
        .try_reserve(roots.len())
        .map_err(|_| Rejection::Exhausted)?;
    pending.extend_from_slice(roots);
    while let Some(id) = pending.pop() {
        work.charge(1).map_err(|()| Rejection::Exhausted)?;
        if visited.contains(&id) {
            continue;
        }
        visited.try_reserve(1).map_err(|_| Rejection::Exhausted)?;
        visited.insert(id);
        let node = program.kind_at(id).ok_or(Rejection::Unsupported)?;
        work.charge(program.method_evidence_anchors().len())
            .map_err(|()| Rejection::Exhausted)?;
        if program
            .method_evidence_anchors()
            .iter()
            .any(|anchor| anchor.node == id)
        {
            return Err(Rejection::Unsupported);
        }
        let count = node.child_count();
        work.charge(count).map_err(|()| Rejection::Exhausted)?;
        pending
            .try_reserve(count)
            .map_err(|_| Rejection::Exhausted)?;
        for index in 0..count {
            pending.push(node.child_at(index).ok_or(Rejection::Unsupported)?);
        }
    }
    Ok(())
}

/// Reconstruct the actual root host pair and its two forwarding clauses.
/// This establishes the root provider shape only. It does not rule out an
/// intervening local handler or reentrant caller on a function invocation.
fn check_root_default_provider(inspect: &mut CoreInspection<'_, '_>) -> Result<(), Rejection> {
    use super::{ResumeUse, packed::Intrinsic, region::HostRegionConfiguration};
    let root = inspect.program.root();
    let region_id = match inspect.kind(root)? {
        EffectExprKind::Operation(EffectOperation::NativeInterpret(boundary)) => boundary.body(),
        _ => root,
    };
    let EffectExprKind::Operation(EffectOperation::Region(region)) = inspect.kind(region_id)?
    else {
        return Err(Rejection::Unsupported);
    };
    if !region.entry {
        return Err(Rejection::Unsupported);
    }
    let api = crate::resolved::RegionApi::for_module(region.api).ok_or(Rejection::Unsupported)?;
    if !matches!(
        inspect.kind(region.preceding)?,
        EffectExprKind::Pure(PureExprKind::Value(super::PureValue::Unit(_)))
    ) {
        return Err(Rejection::Unsupported);
    }
    let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Tuple(provider))) =
        inspect.kind(region.provider)?
    else {
        return Err(Rejection::Unsupported);
    };
    let [allocate, release] = provider.elements() else {
        return Err(Rejection::Unsupported);
    };
    let EffectExprKind::Pure(PureExprKind::Value(super::PureValue::Intrinsic(allocate))) =
        inspect.kind(*allocate)?
    else {
        return Err(Rejection::Unsupported);
    };
    let EffectExprKind::Pure(PureExprKind::Value(super::PureValue::Intrinsic(release))) =
        inspect.kind(*release)?
    else {
        return Err(Rejection::Unsupported);
    };
    if allocate.module() != region.api
        || release.module() != region.api
        || allocate.operation()
            != (Intrinsic::RegionHostAllocate {
                owner: region.identity,
                configuration: HostRegionConfiguration::System,
            })
        || release.operation()
            != (Intrinsic::RegionHostRelease {
                owner: region.identity,
                configuration: HostRegionConfiguration::System,
            })
    {
        return Err(Rejection::Unsupported);
    }
    let EffectExprKind::Operation(EffectOperation::Handler(handler)) = inspect.kind(region.body)?
    else {
        return Err(Rejection::Unsupported);
    };
    if handler.effect().effect() != api.default_alloc()
        || !handler.effect().arguments().is_empty()
        || handler.hook_root().is_some()
        || handler.hook_registration().is_some()
    {
        return Err(Rejection::Unsupported);
    }
    let [allocation, context] = handler.clauses() else {
        return Err(Rejection::Unsupported);
    };
    if allocation.operation() != crate::types::OperationId::new(api.default_alloc(), 0)
        || context.operation() != crate::types::OperationId::new(api.default_alloc(), 1)
    {
        return Err(Rejection::Unsupported);
    }
    let request = binder_pattern(allocation.pattern())?;
    binder_pattern(context.pattern())?;
    let EffectExprKind::Operation(EffectOperation::Resume(allocation_resume)) =
        inspect.kind(allocation.body())?
    else {
        return Err(Rejection::Unsupported);
    };
    let EffectExprKind::Operation(EffectOperation::Resume(context_resume)) =
        inspect.kind(context.body())?
    else {
        return Err(Rejection::Unsupported);
    };
    for (clause, resume) in [(allocation, allocation_resume), (context, context_resume)] {
        if resume.handler() != handler.id()
            || resume.owner() != clause.resume()
            || resume.use_state() != ResumeUse::Consumed
        {
            return Err(Rejection::Unsupported);
        }
    }
    let EffectExprKind::Operation(EffectOperation::RegionAllocate(allocation)) =
        inspect.kind(allocation_resume.value())?
    else {
        return Err(Rejection::Unsupported);
    };
    if allocation.api != region.api
        || inspect.variable(allocation.context)? != region.access.id()
        || inspect.variable(allocation.request)? != request
        || inspect.variable(context_resume.value())? != region.access.id()
    {
        return Err(Rejection::Unsupported);
    }
    Ok(())
}

/// Verify the restricted direct entry invocation in the actual linked spine.
/// This initial control path admits a single direct call under the checked root
/// default provider. It issues no ledger fact; worker-driver paths need their
/// own complete caller, capture and reentry reconstruction.
fn check_root_entry_removal_call(
    program: &dyn LedgerArena,
    linked: &ValidatedInterfaceProgram,
    removal: DefinitionCandidate,
    caller: DefinitionCandidate,
    constructors: RemovalConstructors,
    work: &mut TypeWorkBudget,
) -> Result<NodeId, Rejection> {
    let (caller_initializer, linked_result) =
        linked_initializer_and_result(program, linked, caller, work)?;
    linked_initializer(program, linked, removal, work)?;
    reject_evidence(program, &[caller_initializer, linked_result], work)?;
    let mut inspect = CoreInspection { program, work };
    check_root_default_provider(&mut inspect)?;
    let root_call = inspect.application(linked_result)?;
    if inspect.variable(root_call.function())? != caller.binder
        || !matches!(
            inspect.kind(root_call.argument())?,
            EffectExprKind::Pure(PureExprKind::Value(super::PureValue::Unit(_)))
        )
    {
        return Err(Rejection::Unsupported);
    }
    let function = inspect.stored_function(caller_initializer, &[removal.binder])?;
    let outer = inspect.branch(function.body())?;
    if inspect.variable(outer.scrutinee())? != function.parameter().id() {
        return Err(Rejection::Unsupported);
    }
    let [arm] = outer.arms() else {
        return Err(Rejection::Unsupported);
    };
    if !matches!(arm.pattern().kind, super::CorePatternKind::Unit) {
        return Err(Rejection::Unsupported);
    }
    let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Bind(binding))) =
        inspect.kind(arm.body())?
    else {
        return Err(Rejection::Unsupported);
    };
    if !matches!(
        inspect.kind(binding.body())?,
        EffectExprKind::Pure(PureExprKind::Value(super::PureValue::Unit(_)))
    ) {
        return Err(Rejection::Unsupported);
    }
    let call = inspect.application(binding.initializer())?;
    if inspect.variable(call.function())? != removal.binder {
        return Err(Rejection::Unsupported);
    }
    let [query, list] = inspect.persistent_tuple(call.argument(), None)?.fields else {
        return Err(Rejection::Unsupported);
    };
    if !inspect
        .persistent_tuple(*query, Some(constructors.root_id))?
        .fields
        .is_empty()
        || !inspect
            .persistent_tuple(*list, Some(constructors.empty))?
            .fields
            .is_empty()
    {
        return Err(Rejection::Unsupported);
    }
    Ok(binding.initializer())
}

fn pattern_pair(
    pattern: &super::CorePattern,
) -> Result<(&super::CorePattern, &super::CorePattern), Rejection> {
    let super::CorePatternKind::Tuple(items) = &pattern.kind else {
        return Err(Rejection::Unsupported);
    };
    let [left, right] = items.as_ref() else {
        return Err(Rejection::Unsupported);
    };
    Ok((left, right))
}

fn exact_nominal_pair(
    program: &dyn LedgerArena,
    left: crate::types::ConstructorId,
    right: crate::types::ConstructorId,
    work: &mut TypeWorkBudget,
) -> Result<(), Rejection> {
    work.charge(3).map_err(|()| Rejection::Exhausted)?;
    if left == right || left.owner() != right.owner() {
        return Err(Rejection::Unsupported);
    }
    let nominal = program
        .registry()
        .nominal(left.owner())
        .ok_or(Rejection::Unsupported)?;
    if nominal.declaration_kind != crate::resolved::ResolvedNominalDeclarationKind::Data {
        return Err(Rejection::Unsupported);
    }
    let [first, second] = nominal.constructors.as_ref() else {
        return Err(Rejection::Unsupported);
    };
    if !((*first == left && *second == right) || (*first == right && *second == left)) {
        return Err(Rejection::Unsupported);
    }
    Ok(())
}

fn check_removal_nominals(
    program: &dyn LedgerArena,
    c: RemovalConstructors,
    work: &mut TypeWorkBudget,
) -> Result<(), Rejection> {
    check_removal_entry_nominals(program, c, false, work)
}

fn check_removal_entry_nominals(
    program: &dyn LedgerArena,
    c: RemovalConstructors,
    record: bool,
    work: &mut TypeWorkBudget,
) -> Result<(), Rejection> {
    use crate::types::Type;
    exact_nominal_pair(program, c.empty, c.more, work)?;
    exact_nominal_pair(program, c.found, c.missing, work)?;
    exact_nominal_pair(program, c.root_id, c.work_id, work)?;
    work.charge(7).map_err(|()| Rejection::Exhausted)?;
    let registry = program.registry();
    let get = |id| registry.constructor(id).ok_or(Rejection::Unsupported);
    if get(c.empty)?.payload.is_some()
        || get(c.found)?.payload.is_some()
        || get(c.missing)?.payload.is_some()
        || get(c.root_id)?.payload.is_some()
    {
        return Err(Rejection::Unsupported);
    }
    let Some(Type::Tuple(work_fields)) = &get(c.work_id)?.payload else {
        return Err(Rejection::Unsupported);
    };
    if !matches!(work_fields.as_ref(), [Type::Int, Type::Int]) {
        return Err(Rejection::Unsupported);
    }
    let Some(Type::Tuple(entry_fields)) = &get(c.entry)?.payload else {
        return Err(Rejection::Unsupported);
    };
    let valid_entry = if record {
        matches!(entry_fields.as_ref(), [Type::Nominal(id), Type::Nominal(_), Type::Nominal(_), Type::Nominal(_)] if *id == c.root_id.owner())
    } else {
        matches!(entry_fields.as_ref(), [Type::Nominal(id), Type::Int] if *id == c.root_id.owner())
    };
    if !valid_entry {
        return Err(Rejection::Unsupported);
    }
    let nominal = registry
        .nominal(c.entry.owner())
        .ok_or(Rejection::Unsupported)?;
    if nominal.declaration_kind != crate::resolved::ResolvedNominalDeclarationKind::Data
        || nominal.constructors.as_ref() != [c.entry]
    {
        return Err(Rejection::Unsupported);
    }
    let Some(Type::Tuple(list_fields)) = &get(c.more)?.payload else {
        return Err(Rejection::Unsupported);
    };
    if !matches!(list_fields.as_ref(), [Type::Nominal(entry), Type::Nominal(tail)] if *entry == c.entry.owner() && *tail == c.empty.owner())
    {
        return Err(Rejection::Unsupported);
    }
    Ok(())
}

fn check_projection(
    inspect: &mut CoreInspection<'_, '_>,
    initializer: NodeId,
    entry: crate::types::ConstructorId,
) -> Result<(), Rejection> {
    let function = inspect.stored_function(initializer, &[])?;
    let branch = inspect.branch(function.body())?;
    if inspect.variable(branch.scrutinee())? != function.parameter().id() {
        return Err(Rejection::Unsupported);
    }
    let [arm] = branch.arms() else {
        return Err(Rejection::Unsupported);
    };
    let payload = constructor_pattern(arm.pattern(), entry)?.ok_or(Rejection::Unsupported)?;
    let (key, destination) = pattern_pair(payload)?;
    let key = binder_pattern(key)?;
    binder_pattern(destination)?;
    if inspect.variable(arm.body())? != key {
        return Err(Rejection::Unsupported);
    }
    Ok(())
}

fn bool_value(
    inspect: &mut CoreInspection<'_, '_>,
    node: NodeId,
    expected: bool,
) -> Result<(), Rejection> {
    match inspect.kind(node)? {
        EffectExprKind::Pure(PureExprKind::Value(super::PureValue::Boolean(value)))
            if value.value() == expected =>
        {
            Ok(())
        }
        _ => Err(Rejection::Unsupported),
    }
}

fn integer_equal(
    inspect: &mut CoreInspection<'_, '_>,
    node: NodeId,
    left: BinderId,
    right: BinderId,
) -> Result<(), Rejection> {
    let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Primitive(operation))) =
        inspect.kind(node)?
    else {
        return Err(Rejection::Unsupported);
    };
    if operation.primitive() != super::Primitive::Equal
        || inspect.variable(operation.left())? != left
        || inspect.variable(operation.right())? != right
    {
        return Err(Rejection::Unsupported);
    }
    Ok(())
}

fn check_id_comparison(
    inspect: &mut CoreInspection<'_, '_>,
    initializer: NodeId,
    root: crate::types::ConstructorId,
    work: crate::types::ConstructorId,
) -> Result<(), Rejection> {
    let function = inspect.stored_function(initializer, &[])?;
    let arguments = inspect.branch(function.body())?;
    if inspect.variable(arguments.scrutinee())? != function.parameter().id() {
        return Err(Rejection::Unsupported);
    }
    let [argument_arm] = arguments.arms() else {
        return Err(Rejection::Unsupported);
    };
    let (left, right) = pattern_pair(argument_arm.pattern())?;
    let left = binder_pattern(left)?;
    let right = binder_pattern(right)?;
    let cases = inspect.branch(argument_arm.body())?;
    let [first, second] = inspect.persistent_tuple(cases.scrutinee(), None)?.fields else {
        return Err(Rejection::Unsupported);
    };
    if inspect.variable(*first)? != left || inspect.variable(*second)? != right {
        return Err(Rejection::Unsupported);
    }
    let [roots, works, mismatch] = cases.arms() else {
        return Err(Rejection::Unsupported);
    };
    let (a, b) = pattern_pair(roots.pattern())?;
    if constructor_pattern(a, root)?.is_some() || constructor_pattern(b, root)?.is_some() {
        return Err(Rejection::Unsupported);
    }
    bool_value(inspect, roots.body(), true)?;
    let (a, b) = pattern_pair(works.pattern())?;
    let a = constructor_pattern(a, work)?.ok_or(Rejection::Unsupported)?;
    let b = constructor_pattern(b, work)?.ok_or(Rejection::Unsupported)?;
    let (a_allocator, a_serial) = pattern_pair(a)?;
    let (b_allocator, b_serial) = pattern_pair(b)?;
    let (a_allocator, a_serial, b_allocator, b_serial) = (
        binder_pattern(a_allocator)?,
        binder_pattern(a_serial)?,
        binder_pattern(b_allocator)?,
        binder_pattern(b_serial)?,
    );
    let fields = inspect.branch(works.body())?;
    integer_equal(inspect, fields.scrutinee(), a_allocator, b_allocator)?;
    let [equal, unequal] = fields.arms() else {
        return Err(Rejection::Unsupported);
    };
    if !matches!(equal.pattern().kind, super::CorePatternKind::Boolean(true))
        || !matches!(
            unequal.pattern().kind,
            super::CorePatternKind::Boolean(false)
        )
        || !matches!(mismatch.pattern().kind, super::CorePatternKind::Wildcard)
    {
        return Err(Rejection::Unsupported);
    }
    integer_equal(inspect, equal.body(), a_serial, b_serial)?;
    bool_value(inspect, unequal.body(), false)?;
    bool_value(inspect, mismatch.body(), false)?;
    Ok(())
}

#[derive(Clone, Copy)]
struct RemovalDependencies {
    comparison: DefinitionCandidate,
    projection: DefinitionCandidate,
}

/// Coordinates reconstructed from the actual validated linked arena. The graph
/// is used for the modeled Remove correspondence; it is not a ledger fact.
struct RemovalGraph<'a> {
    arena: &'a dyn LedgerArena,
    candidate: DefinitionCandidate,
    dependencies: RemovalDependencies,
    definition: CheckedStoredFunction<'a>,
    comparison: CheckedStoredFunction<'a>,
    projection: CheckedStoredFunction<'a>,
    constructor: CheckedStoredFunction<'a>,
    constructors: RemovalConstructors,
    provider_api: crate::module::ModuleId,
    argument_match: NodeId,
    list_match: NodeId,
    comparison_match: NodeId,
    recursive_match: NodeId,
    comparison_call: NodeId,
    projection_call: NodeId,
    recursive_call: NodeId,
    rebuild_call: NodeId,
    wanted: BinderId,
    list: BinderId,
    entry: BinderId,
    tail: BinderId,
    remaining: BinderId,
    status: BinderId,
    comparison_left: BinderId,
    comparison_right: BinderId,
    work_fields: [BinderId; 4],
    projection_fields: Vec<BinderId>,
    empty_pair: CheckedPersistentTuple<'a>,
    empty_value: CheckedPersistentTuple<'a>,
    missing_value: CheckedPersistentTuple<'a>,
    comparison_pair: CheckedPersistentTuple<'a>,
    comparator_pair: CheckedPersistentTuple<'a>,
    hit_pair: CheckedPersistentTuple<'a>,
    found_value: CheckedPersistentTuple<'a>,
    recursive_pair: CheckedPersistentTuple<'a>,
    result_pair: CheckedPersistentTuple<'a>,
    constructor_pair: CheckedPersistentTuple<'a>,
    constructor_value: CheckedPersistentTuple<'a>,
}

fn require_distinct(work: &mut TypeWorkBudget, binders: &[BinderId]) -> Result<(), Rejection> {
    for (index, binder) in binders.iter().enumerate() {
        work.charge(index).map_err(|()| Rejection::Exhausted)?;
        if binders[..index].contains(binder) {
            return Err(Rejection::Unsupported);
        }
    }
    Ok(())
}

/// Reconstruct the actual branches and recursive call of one removal body.
/// Success is intermediate only: helper semantics and provider/control remain
/// unchecked, so this result is never exposed as a ledger fact.
fn check_removal_body_shape(
    program: &dyn LedgerArena,
    linked: &ValidatedInterfaceProgram,
    candidate: DefinitionCandidate,
    constructors: RemovalConstructors,
    dependencies: RemovalDependencies,
    record: bool,
    work: &mut TypeWorkBudget,
) -> Result<(), Rejection> {
    let initializer = linked_initializer(program, linked, candidate, work)?;
    let comparison = linked_initializer(program, linked, dependencies.comparison, work)?;
    let projection = linked_initializer(program, linked, dependencies.projection, work)?;
    check_removal_entry_nominals(program, constructors, record, work)?;
    if candidate.binder == dependencies.comparison.binder
        || candidate.binder == dependencies.projection.binder
        || dependencies.comparison.binder == dependencies.projection.binder
    {
        return Err(Rejection::Unsupported);
    }
    if constructors.empty == constructors.more
        || constructors.empty.owner() != constructors.more.owner()
        || constructors.found == constructors.missing
        || constructors.found.owner() != constructors.missing.owner()
    {
        return Err(Rejection::Unsupported);
    }
    for id in [
        constructors.empty,
        constructors.more,
        constructors.found,
        constructors.missing,
    ] {
        work.charge(1).map_err(|()| Rejection::Exhausted)?;
        program
            .registry()
            .constructor(id)
            .ok_or(Rejection::Unsupported)?;
    }
    reject_evidence(program, &[initializer, comparison, projection], work)?;
    let mut inspect = CoreInspection { program, work };
    let function = inspect.stored_function(
        initializer,
        &[
            candidate.binder,
            dependencies.comparison.binder,
            dependencies.projection.binder,
        ],
    )?;
    if record {
        // The projection checker establishes the exact first field of the
        // linked Record constructor; the second traversal below binds its nodes.
        reconstruct_record_projection(
            program,
            linked,
            dependencies.projection,
            constructors.entry,
            constructors.root_id,
            work,
        )?;
        inspect = CoreInspection { program, work };
    } else {
        check_projection(&mut inspect, projection, constructors.entry)?;
    }
    check_id_comparison(
        &mut inspect,
        comparison,
        constructors.root_id,
        constructors.work_id,
    )?;
    let arguments = inspect.branch(function.body())?;
    if inspect.variable(arguments.scrutinee())? != function.parameter().id() {
        return Err(Rejection::Unsupported);
    }
    let [argument_arm] = arguments.arms() else {
        return Err(Rejection::Unsupported);
    };
    let super::CorePatternKind::Tuple(arguments) = &argument_arm.pattern().kind else {
        return Err(Rejection::Unsupported);
    };
    let [wanted, list] = arguments.as_ref() else {
        return Err(Rejection::Unsupported);
    };
    let wanted = binder_pattern(wanted)?;
    let list = binder_pattern(list)?;
    let cases = inspect.branch(argument_arm.body())?;
    if inspect.variable(cases.scrutinee())? != list {
        return Err(Rejection::Unsupported);
    }
    let [empty, more] = cases.arms() else {
        return Err(Rejection::Unsupported);
    };
    if constructor_pattern(empty.pattern(), constructors.empty)?.is_some() {
        return Err(Rejection::Unsupported);
    }
    let more_pattern =
        constructor_pattern(more.pattern(), constructors.more)?.ok_or(Rejection::Unsupported)?;
    let super::CorePatternKind::Tuple(more_fields) = &more_pattern.kind else {
        return Err(Rejection::Unsupported);
    };
    let [entry, tail] = more_fields.as_ref() else {
        return Err(Rejection::Unsupported);
    };
    let entry = binder_pattern(entry)?;
    let tail = binder_pattern(tail)?;
    let [empty_list, missing] = inspect.persistent_tuple(empty.body(), None)?.fields else {
        return Err(Rejection::Unsupported);
    };
    if !inspect
        .persistent_tuple(*empty_list, Some(constructors.empty))?
        .fields
        .is_empty()
        || !inspect
            .persistent_tuple(*missing, Some(constructors.missing))?
            .fields
            .is_empty()
    {
        return Err(Rejection::Unsupported);
    }
    let compared = inspect.branch(more.body())?;
    let compare_call = inspect.application(compared.scrutinee())?;
    if inspect.variable(compare_call.function())? != dependencies.comparison.binder {
        return Err(Rejection::Unsupported);
    }
    let [key, query] = inspect
        .persistent_tuple(compare_call.argument(), None)?
        .fields
    else {
        return Err(Rejection::Unsupported);
    };
    if inspect.variable(*query)? != wanted {
        return Err(Rejection::Unsupported);
    }
    let projection = inspect.application(*key)?;
    if inspect.variable(projection.function())? != dependencies.projection.binder
        || inspect.variable(projection.argument())? != entry
    {
        return Err(Rejection::Unsupported);
    }
    let [hit, miss] = compared.arms() else {
        return Err(Rejection::Unsupported);
    };
    if !matches!(hit.pattern().kind, super::CorePatternKind::Boolean(true))
        || !matches!(miss.pattern().kind, super::CorePatternKind::Boolean(false))
    {
        return Err(Rejection::Unsupported);
    }
    let [returned_tail, found] = inspect.persistent_tuple(hit.body(), None)?.fields else {
        return Err(Rejection::Unsupported);
    };
    if inspect.variable(*returned_tail)? != tail
        || !inspect
            .persistent_tuple(*found, Some(constructors.found))?
            .fields
            .is_empty()
    {
        return Err(Rejection::Unsupported);
    }
    let recursive = inspect.branch(miss.body())?;
    let recursive_call = inspect.application(recursive.scrutinee())?;
    if inspect.variable(recursive_call.function())? != candidate.binder {
        return Err(Rejection::Unsupported);
    }
    let [recursive_query, recursive_tail] = inspect
        .persistent_tuple(recursive_call.argument(), None)?
        .fields
    else {
        return Err(Rejection::Unsupported);
    };
    if inspect.variable(*recursive_query)? != wanted || inspect.variable(*recursive_tail)? != tail {
        return Err(Rejection::Unsupported);
    }
    let [returned] = recursive.arms() else {
        return Err(Rejection::Unsupported);
    };
    let super::CorePatternKind::Tuple(return_pattern) = &returned.pattern().kind else {
        return Err(Rejection::Unsupported);
    };
    let [remaining, status] = return_pattern.as_ref() else {
        return Err(Rejection::Unsupported);
    };
    let remaining = binder_pattern(remaining)?;
    let status = binder_pattern(status)?;
    let [rebuilt, result_status] = inspect.persistent_tuple(returned.body(), None)?.fields else {
        return Err(Rejection::Unsupported);
    };
    if inspect.variable(*result_status)? != status {
        return Err(Rejection::Unsupported);
    }
    let construction = inspect.application(*rebuilt)?;
    let function = inspect.stored_function(construction.function(), &[])?;
    let [payload] = inspect
        .persistent_tuple(function.body(), Some(constructors.more))?
        .fields
    else {
        return Err(Rejection::Unsupported);
    };
    if inspect.variable(*payload)? != function.parameter().id() {
        return Err(Rejection::Unsupported);
    }
    let [original_entry, original_remaining] = inspect
        .persistent_tuple(construction.argument(), None)?
        .fields
    else {
        return Err(Rejection::Unsupported);
    };
    if inspect.variable(*original_entry)? != entry
        || inspect.variable(*original_remaining)? != remaining
    {
        return Err(Rejection::Unsupported);
    }
    Ok(())
}

/// Reconstruct the checked model's coordinates independently from the actual
/// linked nodes. No semantic fact is returned by this intermediate graph.
fn reconstruct_removal_graph<'a>(
    program: &'a dyn LedgerArena,
    linked: &ValidatedInterfaceProgram,
    candidate: DefinitionCandidate,
    constructors: RemovalConstructors,
    dependencies: RemovalDependencies,
    record: bool,
    work: &mut TypeWorkBudget,
) -> Result<RemovalGraph<'a>, Rejection> {
    check_removal_body_shape(
        program,
        linked,
        candidate,
        constructors,
        dependencies,
        record,
        work,
    )?;
    let initializer = linked_initializer(program, linked, candidate, work)?;
    let comparison_id = linked_initializer(program, linked, dependencies.comparison, work)?;
    let projection_id = linked_initializer(program, linked, dependencies.projection, work)?;
    let mut inspect = CoreInspection { program, work };
    let definition = inspect.stored_function_witness(
        initializer,
        &[
            candidate.binder,
            dependencies.comparison.binder,
            dependencies.projection.binder,
        ],
    )?;
    let provider_api = definition.api;
    let comparison = inspect.stored_function_witness(comparison_id, &[])?;
    let projection = inspect.stored_function_witness(projection_id, &[])?;

    let argument_match = definition.body;
    let argument_branch = inspect.branch(argument_match)?;
    let [argument_arm] = argument_branch.arms() else {
        return Err(Rejection::Unsupported);
    };
    let (wanted_pattern, list_pattern) = pattern_pair(argument_arm.pattern())?;
    let wanted = binder_pattern(wanted_pattern)?;
    let list = binder_pattern(list_pattern)?;
    let list_match = argument_arm.body();
    let list_branch = inspect.branch(list_match)?;
    let [empty_arm, more_arm] = list_branch.arms() else {
        return Err(Rejection::Unsupported);
    };
    let more_payload = constructor_pattern(more_arm.pattern(), constructors.more)?
        .ok_or(Rejection::Unsupported)?;
    let (entry_pattern, tail_pattern) = pattern_pair(more_payload)?;
    let entry = binder_pattern(entry_pattern)?;
    let tail = binder_pattern(tail_pattern)?;
    let empty_pair = inspect.persistent_tuple(empty_arm.body(), None)?;
    let [empty_id, missing_id] = empty_pair.fields else {
        return Err(Rejection::Unsupported);
    };
    let empty_value = inspect.persistent_tuple(*empty_id, Some(constructors.empty))?;
    let missing_value = inspect.persistent_tuple(*missing_id, Some(constructors.missing))?;

    let comparison_match = more_arm.body();
    let comparison_branch = inspect.branch(comparison_match)?;
    let comparison_call = comparison_branch.scrutinee();
    let compare_application = inspect.application(comparison_call)?;
    let comparison_pair = inspect.persistent_tuple(compare_application.argument(), None)?;
    let [projection_call, _] = comparison_pair.fields else {
        return Err(Rejection::Unsupported);
    };
    let [hit_arm, miss_arm] = comparison_branch.arms() else {
        return Err(Rejection::Unsupported);
    };
    let hit_pair = inspect.persistent_tuple(hit_arm.body(), None)?;
    let [_, found_id] = hit_pair.fields else {
        return Err(Rejection::Unsupported);
    };
    let found_value = inspect.persistent_tuple(*found_id, Some(constructors.found))?;
    let recursive_match = miss_arm.body();
    let recursive_branch = inspect.branch(recursive_match)?;
    let recursive_call = recursive_branch.scrutinee();
    let recursive_application = inspect.application(recursive_call)?;
    let recursive_pair = inspect.persistent_tuple(recursive_application.argument(), None)?;
    let [returned] = recursive_branch.arms() else {
        return Err(Rejection::Unsupported);
    };
    let (remaining_pattern, status_pattern) = pattern_pair(returned.pattern())?;
    let remaining = binder_pattern(remaining_pattern)?;
    let status = binder_pattern(status_pattern)?;
    let result_pair = inspect.persistent_tuple(returned.body(), None)?;
    let [rebuild_call, _] = result_pair.fields else {
        return Err(Rejection::Unsupported);
    };
    let rebuild_application = inspect.application(*rebuild_call)?;
    let constructor = inspect.stored_function_witness(rebuild_application.function(), &[])?;
    let constructor_pair = inspect.persistent_tuple(rebuild_application.argument(), None)?;
    let constructor_value = inspect.persistent_tuple(constructor.body, Some(constructors.more))?;

    let comparison_argument = inspect.branch(comparison.body)?;
    let [comparison_arm] = comparison_argument.arms() else {
        return Err(Rejection::Unsupported);
    };
    let (left_pattern, right_pattern) = pattern_pair(comparison_arm.pattern())?;
    let comparison_left = binder_pattern(left_pattern)?;
    let comparison_right = binder_pattern(right_pattern)?;
    let comparison_cases = inspect.branch(comparison_arm.body())?;
    let comparator_pair = inspect.persistent_tuple(comparison_cases.scrutinee(), None)?;
    let [_, work_arm, _] = comparison_cases.arms() else {
        return Err(Rejection::Unsupported);
    };
    let (left_work, right_work) = pattern_pair(work_arm.pattern())?;
    let left_work =
        constructor_pattern(left_work, constructors.work_id)?.ok_or(Rejection::Unsupported)?;
    let right_work =
        constructor_pattern(right_work, constructors.work_id)?.ok_or(Rejection::Unsupported)?;
    let (left_allocator, left_serial) = pattern_pair(left_work)?;
    let (right_allocator, right_serial) = pattern_pair(right_work)?;
    let work_fields = [
        binder_pattern(left_allocator)?,
        binder_pattern(left_serial)?,
        binder_pattern(right_allocator)?,
        binder_pattern(right_serial)?,
    ];
    let projection_branch = inspect.branch(projection.body)?;
    let [projection_arm] = projection_branch.arms() else {
        return Err(Rejection::Unsupported);
    };
    let projection_payload = constructor_pattern(projection_arm.pattern(), constructors.entry)?
        .ok_or(Rejection::Unsupported)?;
    let super::CorePatternKind::Tuple(patterns) = &projection_payload.kind else {
        return Err(Rejection::Unsupported);
    };
    if patterns.len() != if record { 4 } else { 2 } {
        return Err(Rejection::Unsupported);
    }
    inspect
        .work
        .charge(patterns.len())
        .map_err(|()| Rejection::Exhausted)?;
    let mut projection_fields = Vec::new();
    projection_fields
        .try_reserve(patterns.len())
        .map_err(|_| Rejection::Exhausted)?;
    for pattern in patterns.iter() {
        projection_fields.push(binder_pattern(pattern)?);
    }

    // The modeled host provider is the same actual Region API for every
    // query, closure and constructor in this graph. This still does not prove
    // dynamic selection or exclude an intervening local provider.
    let apis = [
        definition.api,
        comparison.api,
        projection.api,
        constructor.api,
        empty_pair.api,
        empty_value.api,
        missing_value.api,
        comparison_pair.api,
        comparator_pair.api,
        hit_pair.api,
        found_value.api,
        recursive_pair.api,
        result_pair.api,
        constructor_pair.api,
        constructor_value.api,
    ];
    inspect
        .work
        .charge(apis.len())
        .map_err(|()| Rejection::Exhausted)?;
    if apis.iter().any(|api| *api != provider_api) {
        return Err(Rejection::Unsupported);
    }

    // These distinctness conditions are the actual premises used by the
    // checked-node evaluator. Charge before each comparison; no fact is emitted.
    require_distinct(
        inspect.work,
        &[
            definition.parameter,
            wanted,
            list,
            entry,
            tail,
            candidate.binder,
            dependencies.comparison.binder,
            dependencies.projection.binder,
        ],
    )?;
    require_distinct(inspect.work, &[comparison_left, comparison_right])?;
    require_distinct(inspect.work, &work_fields)?;
    require_distinct(inspect.work, &projection_fields)?;
    require_distinct(inspect.work, &[entry, remaining, status])?;
    let freshness = [
        (
            dependencies.projection.binder,
            comparison_pair.context_binder,
        ),
        (entry, comparison_pair.context_binder),
        (wanted, comparison_pair.context_binder),
        (tail, hit_pair.context_binder),
        (wanted, recursive_pair.context_binder),
        (tail, recursive_pair.context_binder),
        (entry, constructor_pair.context_binder),
        (remaining, constructor_pair.context_binder),
        (entry, result_pair.context_binder),
        (remaining, result_pair.context_binder),
        (status, result_pair.context_binder),
        (constructor.parameter, constructor_value.context_binder),
        (comparison_left, comparator_pair.context_binder),
        (comparison_right, comparator_pair.context_binder),
    ];
    inspect
        .work
        .charge(freshness.len())
        .map_err(|()| Rejection::Exhausted)?;
    if freshness.iter().any(|(binder, context)| binder == context) {
        return Err(Rejection::Unsupported);
    }
    Ok(RemovalGraph {
        arena: program,
        candidate,
        dependencies,
        definition,
        comparison,
        projection,
        constructor,
        constructors,
        provider_api,
        argument_match,
        list_match,
        comparison_match,
        recursive_match,
        comparison_call,
        projection_call: *projection_call,
        recursive_call,
        rebuild_call: *rebuild_call,
        wanted,
        list,
        entry,
        tail,
        remaining,
        status,
        comparison_left,
        comparison_right,
        work_fields,
        projection_fields,
        empty_pair,
        empty_value,
        missing_value,
        comparison_pair,
        comparator_pair,
        hit_pair,
        found_value,
        recursive_pair,
        result_pair,
        constructor_pair,
        constructor_value,
    })
}

fn check_removal_body(
    program: &dyn LedgerArena,
    linked: &ValidatedInterfaceProgram,
    candidate: DefinitionCandidate,
    constructors: RemovalConstructors,
    dependencies: RemovalDependencies,
    work: &mut TypeWorkBudget,
) -> Result<(), Rejection> {
    reconstruct_removal_graph(
        program,
        linked,
        candidate,
        constructors,
        dependencies,
        false,
        work,
    )
    .map(|_| ())
}

/// Untrusted nominal coordinates for the ordinary finite ledger initialization.
#[derive(Clone, Copy, Eq, PartialEq)]
pub(super) struct InitializationConstructors {
    pub(super) ledger: crate::types::ConstructorId,
    pub(super) record: crate::types::ConstructorId,
    pub(super) root: crate::types::ConstructorId,
    pub(super) work: crate::types::ConstructorId,
    pub(super) no_parent: crate::types::ConstructorId,
    pub(super) parent: crate::types::ConstructorId,
    pub(super) open: crate::types::ConstructorId,
    pub(super) closed: crate::types::ConstructorId,
    pub(super) children_empty: crate::types::ConstructorId,
    pub(super) children_more: crate::types::ConstructorId,
    pub(super) records_empty: crate::types::ConstructorId,
    pub(super) records_more: crate::types::ConstructorId,
    pub(super) outputs_empty: crate::types::ConstructorId,
    pub(super) outputs_more: crate::types::ConstructorId,
}

#[derive(Clone, Copy)]
pub(super) enum InitializationRole {
    Root,
    Worker,
}

/// Actual capture-free constructor code and ordered argument tuple. This is
/// a checked node witness only; it does not establish the provider in control.
#[derive(Clone, Copy)]
struct ConstructorApplication<'a> {
    call: NodeId,
    closure: CheckedStoredFunction<'a>,
    arguments: CheckedPersistentTuple<'a>,
    value: CheckedPersistentTuple<'a>,
}

struct InitializationGraph<'a> {
    arena: &'a dyn LedgerArena,
    candidate: DefinitionCandidate,
    constructors: InitializationConstructors,
    initializer: CheckedStoredFunction<'a>,
    provider_api: crate::module::ModuleId,
    role: InitializationRole,
    ledger: ConstructorApplication<'a>,
    zero: NodeId,
    records_empty: CheckedPersistentTuple<'a>,
    outputs_empty: CheckedPersistentTuple<'a>,
    records_more: Option<ConstructorApplication<'a>>,
    root_record: Option<ConstructorApplication<'a>>,
    root: Option<CheckedPersistentTuple<'a>>,
    no_parent: Option<CheckedPersistentTuple<'a>>,
    open: Option<CheckedPersistentTuple<'a>>,
    children_empty: Option<CheckedPersistentTuple<'a>>,
}

/// Verify the selected singleton nominal and expose its actual payload type.
fn singleton_payload<'a>(
    program: &'a dyn LedgerArena,
    constructor: crate::types::ConstructorId,
    work: &mut TypeWorkBudget,
) -> Result<&'a crate::types::Type, Rejection> {
    work.charge(2).map_err(|()| Rejection::Exhausted)?;
    let registry = program.registry();
    let declaration = registry
        .constructor(constructor)
        .ok_or(Rejection::Unsupported)?;
    let nominal = registry
        .nominal(constructor.owner())
        .ok_or(Rejection::Unsupported)?;
    if nominal.declaration_kind != crate::resolved::ResolvedNominalDeclarationKind::Data
        || nominal.constructors.as_ref() != [constructor]
    {
        return Err(Rejection::Unsupported);
    }
    declaration.payload.as_ref().ok_or(Rejection::Unsupported)
}

fn check_initialization_nominals(
    program: &dyn LedgerArena,
    c: InitializationConstructors,
    work: &mut TypeWorkBudget,
) -> Result<(), Rejection> {
    use crate::types::Type;
    for (left, right) in [
        (c.root, c.work),
        (c.no_parent, c.parent),
        (c.open, c.closed),
        (c.children_empty, c.children_more),
        (c.records_empty, c.records_more),
        (c.outputs_empty, c.outputs_more),
    ] {
        exact_nominal_pair(program, left, right, work)?;
    }
    let ledger = singleton_payload(program, c.ledger, work)?;
    let record = singleton_payload(program, c.record, work)?;
    let Type::Tuple(ledger_fields) = ledger else {
        return Err(Rejection::Unsupported);
    };
    let Type::Tuple(record_fields) = record else {
        return Err(Rejection::Unsupported);
    };
    if !matches!(ledger_fields.as_ref(), [Type::Int, Type::Nominal(records), Type::Nominal(outputs)]
        if *records == c.records_empty.owner() && *outputs == c.outputs_empty.owner())
        || !matches!(record_fields.as_ref(), [Type::Nominal(identity), Type::Nominal(parent),
            Type::Nominal(phase), Type::Nominal(children)]
            if *identity == c.root.owner() && *parent == c.no_parent.owner()
                && *phase == c.open.owner() && *children == c.children_empty.owner())
    {
        return Err(Rejection::Unsupported);
    }
    work.charge(9).map_err(|()| Rejection::Exhausted)?;
    let registry = program.registry();
    for id in [
        c.root,
        c.no_parent,
        c.open,
        c.children_empty,
        c.records_empty,
        c.outputs_empty,
    ] {
        if registry
            .constructor(id)
            .ok_or(Rejection::Unsupported)?
            .payload
            .is_some()
        {
            return Err(Rejection::Unsupported);
        }
    }
    let Some(Type::Tuple(work_fields)) = &registry
        .constructor(c.work)
        .ok_or(Rejection::Unsupported)?
        .payload
    else {
        return Err(Rejection::Unsupported);
    };
    if !matches!(work_fields.as_ref(), [Type::Int, Type::Int]) {
        return Err(Rejection::Unsupported);
    }
    let Some(Type::Tuple(record_fields)) = &registry
        .constructor(c.records_more)
        .ok_or(Rejection::Unsupported)?
        .payload
    else {
        return Err(Rejection::Unsupported);
    };
    if !matches!(record_fields.as_ref(), [Type::Nominal(record), Type::Nominal(records)]
        if *record == c.record.owner() && *records == c.records_empty.owner())
    {
        return Err(Rejection::Unsupported);
    }
    let Some(Type::Tuple(output_fields)) = &registry
        .constructor(c.outputs_more)
        .ok_or(Rejection::Unsupported)?
        .payload
    else {
        return Err(Rejection::Unsupported);
    };
    if !matches!(output_fields.as_ref(), [Type::Nominal(_), Type::Nominal(outputs)]
        if *outputs == c.outputs_empty.owner())
    {
        return Err(Rejection::Unsupported);
    }
    Ok(())
}

fn constructor_application<'a>(
    inspect: &mut CoreInspection<'a, '_>,
    call: NodeId,
    nominal: crate::types::ConstructorId,
    arity: usize,
    provider_api: crate::module::ModuleId,
) -> Result<ConstructorApplication<'a>, Rejection> {
    let application = inspect.application(call)?;
    let closure = inspect.stored_function_witness(application.function(), &[])?;
    let value = inspect.persistent_tuple(closure.body, Some(nominal))?;
    let [payload] = value.fields else {
        return Err(Rejection::Unsupported);
    };
    if inspect.variable(*payload)? != closure.parameter || closure.parameter == value.context_binder
    {
        return Err(Rejection::Unsupported);
    }
    let arguments = inspect.persistent_tuple(application.argument(), None)?;
    if arguments.fields.len() != arity
        || closure.api != provider_api
        || value.api != provider_api
        || arguments.api != provider_api
    {
        return Err(Rejection::Unsupported);
    }
    Ok(ConstructorApplication {
        call,
        closure,
        arguments,
        value,
    })
}

fn nullary_constructor<'a>(
    inspect: &mut CoreInspection<'a, '_>,
    node: NodeId,
    nominal: crate::types::ConstructorId,
    provider_api: crate::module::ModuleId,
) -> Result<CheckedPersistentTuple<'a>, Rejection> {
    let value = inspect.persistent_tuple(node, Some(nominal))?;
    if !value.fields.is_empty() || value.api != provider_api {
        return Err(Rejection::Unsupported);
    }
    Ok(value)
}

/// Recover the exact ordinary constructor graph and zero counter. It confers
/// no current-state fact until the actual control/provider path is checked.
fn reconstruct_initialization_graph<'a>(
    program: &'a dyn LedgerArena,
    linked: &ValidatedInterfaceProgram,
    candidate: DefinitionCandidate,
    c: InitializationConstructors,
    role: InitializationRole,
    work: &mut TypeWorkBudget,
) -> Result<InitializationGraph<'a>, Rejection> {
    check_initialization_nominals(program, c, work)?;
    let initializer_id = linked_initializer(program, linked, candidate, work)?;
    reject_evidence(program, &[initializer_id], work)?;
    let mut inspect = CoreInspection { program, work };
    let initializer = inspect.stored_function_witness(initializer_id, &[])?;
    let provider_api = initializer.api;
    let argument_match = inspect.branch(initializer.body)?;
    if inspect.variable(argument_match.scrutinee())? != initializer.parameter {
        return Err(Rejection::Unsupported);
    }
    let [arm] = argument_match.arms() else {
        return Err(Rejection::Unsupported);
    };
    if !matches!(arm.pattern().kind, super::CorePatternKind::Unit) {
        return Err(Rejection::Unsupported);
    }
    let ledger = constructor_application(&mut inspect, arm.body(), c.ledger, 3, provider_api)?;
    let [zero, records, outputs] = ledger.arguments.fields else {
        return Err(Rejection::Unsupported);
    };
    let EffectExprKind::Pure(PureExprKind::Value(super::PureValue::Integer(integer))) =
        inspect.kind(*zero)?
    else {
        return Err(Rejection::Unsupported);
    };
    let bytes = usize::try_from(integer.value().magnitude_byte_length())
        .map_err(|_| Rejection::Exhausted)?;
    inspect
        .work
        .charge(bytes.saturating_add(1))
        .map_err(|()| Rejection::Exhausted)?;
    if integer.value().to_i64() != Some(0) {
        return Err(Rejection::Unsupported);
    }
    let outputs_empty = nullary_constructor(&mut inspect, *outputs, c.outputs_empty, provider_api)?;
    let (records_empty, records_more, root_record, root, no_parent, open, children_empty) =
        match role {
            InitializationRole::Worker => (
                nullary_constructor(&mut inspect, *records, c.records_empty, provider_api)?,
                None,
                None,
                None,
                None,
                None,
                None,
            ),
            InitializationRole::Root => {
                let more = constructor_application(
                    &mut inspect,
                    *records,
                    c.records_more,
                    2,
                    provider_api,
                )?;
                let [record_node, empty_node] = more.arguments.fields else {
                    return Err(Rejection::Unsupported);
                };
                let record =
                    constructor_application(&mut inspect, *record_node, c.record, 4, provider_api)?;
                let [root_node, parent_node, phase_node, children_node] = record.arguments.fields
                else {
                    return Err(Rejection::Unsupported);
                };
                (
                    nullary_constructor(&mut inspect, *empty_node, c.records_empty, provider_api)?,
                    Some(more),
                    Some(record),
                    Some(nullary_constructor(
                        &mut inspect,
                        *root_node,
                        c.root,
                        provider_api,
                    )?),
                    Some(nullary_constructor(
                        &mut inspect,
                        *parent_node,
                        c.no_parent,
                        provider_api,
                    )?),
                    Some(nullary_constructor(
                        &mut inspect,
                        *phase_node,
                        c.open,
                        provider_api,
                    )?),
                    Some(nullary_constructor(
                        &mut inspect,
                        *children_node,
                        c.children_empty,
                        provider_api,
                    )?),
                )
            }
        };
    Ok(InitializationGraph {
        arena: program,
        candidate,
        constructors: c,
        initializer,
        provider_api,
        role,
        ledger,
        zero: *zero,
        records_empty,
        outputs_empty,
        records_more,
        root_record,
        root,
        no_parent,
        open,
        children_empty,
    })
}

/// A definition-bound worker initialization law. A consuming call must
/// establish its Unit argument and faithfully selected default allocation.
/// This summary alone does not establish a current ledger or network right.
struct ConditionalWorkerInitialization<'a> {
    linked: &'a ValidatedInterfaceProgram,
    graph: InitializationGraph<'a>,
}

fn check_conditional_worker_initialization<'a>(
    program: &'a dyn LedgerArena,
    linked: &'a ValidatedInterfaceProgram,
    candidate: DefinitionCandidate,
    constructors: InitializationConstructors,
    work: &mut TypeWorkBudget,
) -> Result<ConditionalWorkerInitialization<'a>, Rejection> {
    let graph = reconstruct_initialization_graph(
        program,
        linked,
        candidate,
        constructors,
        InitializationRole::Worker,
        work,
    )?;
    Ok(ConditionalWorkerInitialization { linked, graph })
}

/// A definition-bound Root initialization law. A consuming call must
/// establish its Unit argument and faithfully selected default allocation.
/// This summary alone does not establish a current ledger or network right.
struct ConditionalRootInitialization<'a> {
    linked: &'a ValidatedInterfaceProgram,
    graph: InitializationGraph<'a>,
}

fn check_conditional_root_initialization<'a>(
    program: &'a dyn LedgerArena,
    linked: &'a ValidatedInterfaceProgram,
    candidate: DefinitionCandidate,
    constructors: InitializationConstructors,
    work: &mut TypeWorkBudget,
) -> Result<ConditionalRootInitialization<'a>, Rejection> {
    let graph = reconstruct_initialization_graph(
        program,
        linked,
        candidate,
        constructors,
        InitializationRole::Root,
        work,
    )?;
    Ok(ConditionalRootInitialization { linked, graph })
}

/// A nominated initialization call and its checked definition. The call is
/// provisional: only a matched normal return on the owning worker trace can
/// seed a current ledger, after its provider has also been checked.
pub(super) struct ConditionalInitializationCall<'a> {
    graph: InitializationGraph<'a>,
    call: NodeId,
    argument: NodeId,
}

impl ConditionalInitializationCall<'_> {
    pub(super) fn call(&self) -> NodeId {
        self.call
    }
    pub(super) fn argument(&self) -> NodeId {
        self.argument
    }
    pub(super) fn closure(&self) -> NodeId {
        self.graph.initializer.closure
    }
    pub(super) fn provider_api(&self) -> crate::module::ModuleId {
        self.graph.provider_api
    }
    pub(super) fn definition_query(&self) -> NodeId {
        self.graph.initializer.query
    }
    pub(super) fn definition_binding(&self) -> NodeId {
        self.graph.initializer.root
    }
    pub(super) fn definition_context(&self) -> NodeId {
        self.graph.initializer.context
    }
}

/// Authenticate the ordinary entry-region provider shape; dynamic selection
/// and its return are checked separately on the worker trace.
pub(super) fn checked_entry_default_handler(
    program: &dyn LedgerArena,
    work: &mut TypeWorkBudget,
) -> Result<NodeId, Rejection> {
    let mut inspect = CoreInspection { program, work };
    check_root_default_provider(&mut inspect)?;
    let root = program.root();
    let region = match inspect.kind(root)? {
        EffectExprKind::Operation(EffectOperation::NativeInterpret(boundary)) => boundary.body(),
        _ => root,
    };
    let EffectExprKind::Operation(EffectOperation::Region(region)) = inspect.kind(region)? else {
        return Err(Rejection::Unsupported);
    };
    Ok(region.body)
}

/// Check an actual call against the nominated initializer and its complete
/// linked definition, using the same allowance as the consuming query.
pub(super) fn check_nominated_initialization_call<'a>(
    program: &'a dyn LedgerArena,
    linked: &'a ValidatedInterfaceProgram,
    call: NodeId,
    candidate: DefinitionCandidate,
    constructors: InitializationConstructors,
    role: InitializationRole,
    work: &mut TypeWorkBudget,
) -> Result<ConditionalInitializationCall<'a>, Rejection> {
    let mut inspect = CoreInspection { program, work };
    let application = inspect.application(call)?;
    if inspect.variable(application.function())? != candidate.binder {
        return Err(Rejection::Unsupported);
    }
    let graph = reconstruct_initialization_graph(
        program,
        linked,
        candidate,
        constructors,
        role,
        inspect.work,
    )?;
    Ok(ConditionalInitializationCall {
        graph,
        call,
        argument: application.argument(),
    })
}

/// Exact saved-query and RegionBuffer Add coordinates, reconstructed from the
/// proposed successor counter field. This witness alone issues no ledger fact.
#[derive(Clone, Copy)]
struct CheckedCounterIncrement<'a> {
    arena: &'a dyn LedgerArena,
    root: NodeId,
    context_binder: BinderId,
    query: NodeId,
    unit: NodeId,
    buffer: NodeId,
    context: NodeId,
    left: NodeId,
    right: NodeId,
    counter: BinderId,
    api: crate::module::ModuleId,
}

/// Match the actual region-lowered `counter + 1`, retaining its selected API.
/// Callers must separately establish currentness and selected-provider control.
fn reconstruct_counter_increment<'a>(
    inspect: &mut CoreInspection<'a, '_>,
    root: NodeId,
    counter: BinderId,
    expected_api: crate::module::ModuleId,
) -> Result<CheckedCounterIncrement<'a>, Rejection> {
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
    let left = buffer.operand.ok_or(Rejection::Unsupported)?;
    let right = buffer.right.ok_or(Rejection::Unsupported)?;
    if buffer.api != expected_api
        || !matches!(
            &buffer.operation,
            super::region::RegionBufferOperation::IntegerArithmetic(super::Primitive::Add)
        )
        || query.effect().effect() != api.default_alloc()
        || !query.effect().arguments().is_empty()
        || query.operation() != crate::types::OperationId::new(api.default_alloc(), 1)
        || !matches!(
            inspect.kind(query.operand())?,
            EffectExprKind::Pure(PureExprKind::Value(super::PureValue::Unit(_)))
        )
        || inspect.variable(buffer.context)? != bind.binder().id()
        || inspect.variable(left)? != counter
        || counter == bind.binder().id()
    {
        return Err(Rejection::Unsupported);
    }
    let EffectExprKind::Pure(PureExprKind::Value(super::PureValue::Integer(one))) =
        inspect.kind(right)?
    else {
        return Err(Rejection::Unsupported);
    };
    let bytes =
        usize::try_from(one.value().magnitude_byte_length()).map_err(|_| Rejection::Exhausted)?;
    inspect
        .work
        .charge(bytes.saturating_add(1))
        .map_err(|()| Rejection::Exhausted)?;
    if one.value().to_i64() != Some(1) {
        return Err(Rejection::Unsupported);
    }
    Ok(CheckedCounterIncrement {
        arena: inspect.program,
        root,
        context_binder: bind.binder().id(),
        query: bind.initializer(),
        unit: query.operand(),
        buffer: bind.body(),
        context: buffer.context,
        left,
        right,
        counter,
        api: buffer.api,
    })
}

/// Intermediate coordinates for the actual returned registration successor.
/// The remaining registration branches, helper semantics, output operands,
/// currentness and freshness are not established by this witness.
struct RegistrationCounterGraph<'a> {
    arena: &'a dyn LedgerArena,
    candidate: DefinitionCandidate,
    definition: CheckedStoredFunction<'a>,
    argument_match: NodeId,
    successor: ConstructorApplication<'a>,
    result: CheckedPersistentTuple<'a>,
    status: NodeId,
    increment: CheckedCounterIncrement<'a>,
}

fn reconstruct_registration_counter<'a>(
    program: &'a dyn LedgerArena,
    linked: &ValidatedInterfaceProgram,
    candidate: DefinitionCandidate,
    captures: &[BinderId],
    ledger: crate::types::ConstructorId,
    work: &mut TypeWorkBudget,
) -> Result<RegistrationCounterGraph<'a>, Rejection> {
    let initializer = linked_initializer(program, linked, candidate, work)?;
    reject_evidence(program, &[initializer], work)?;
    let mut inspect = CoreInspection { program, work };
    let definition = inspect.stored_function_witness(initializer, captures)?;
    let arguments = inspect.branch(definition.body)?;
    if inspect.variable(arguments.scrutinee())? != definition.parameter {
        return Err(Rejection::Unsupported);
    }
    let [argument_arm] = arguments.arms() else {
        return Err(Rejection::Unsupported);
    };
    let super::CorePatternKind::Tuple(fields) = &argument_arm.pattern().kind else {
        return Err(Rejection::Unsupported);
    };
    let counter = binder_pattern(fields.first().ok_or(Rejection::Unsupported)?)?;
    let mut body = argument_arm.body();
    let result = loop {
        match inspect.persistent_tuple(body, None) {
            Ok(result) => break result,
            Err(Rejection::Exhausted) => return Err(Rejection::Exhausted),
            Err(Rejection::Unsupported) => {}
        }
        let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Bind(bind))) =
            inspect.kind(body)?
        else {
            return Err(Rejection::Unsupported);
        };
        body = bind.body();
    };
    let [successor_call, status] = result.fields else {
        return Err(Rejection::Unsupported);
    };
    if result.api != definition.api {
        return Err(Rejection::Unsupported);
    }
    let successor =
        constructor_application(&mut inspect, *successor_call, ledger, 3, definition.api)?;
    let [counter_field, _, _] = successor.arguments.fields else {
        return Err(Rejection::Unsupported);
    };
    let increment =
        reconstruct_counter_increment(&mut inspect, *counter_field, counter, definition.api)?;
    Ok(RegistrationCounterGraph {
        arena: program,
        candidate,
        definition,
        argument_match: definition.body,
        successor,
        result,
        status: *status,
        increment,
    })
}

#[derive(Clone, Copy)]
struct RegistrationSuccessConstructors {
    ledger: crate::types::ConstructorId,
    work: crate::types::ConstructorId,
    child: crate::types::ConstructorId,
    record: crate::types::ConstructorId,
    open: crate::types::ConstructorId,
    parent: crate::types::ConstructorId,
    work_out: crate::types::ConstructorId,
    registered: crate::types::ConstructorId,
}

/// Coordinates of the successful commit only. No fact is published: callers,
/// failure branches, helper semantics, finite inputs and currentness remain open.
struct RegistrationSuccessGraph<'a> {
    counter: RegistrationCounterGraph<'a>,
    work_value: ConstructorApplication<'a>,
    replacement: ConstructorApplication<'a>,
    child: ConstructorApplication<'a>,
    parent: ConstructorApplication<'a>,
    output: ConstructorApplication<'a>,
    helper_calls: [NodeId; 3],
    status_closure: CheckedStoredFunction<'a>,
}

fn registration_bind<'a>(
    inspect: &mut CoreInspection<'a, '_>,
    node: NodeId,
) -> Result<&'a super::binding::BindingNode, Rejection> {
    match inspect.kind(node)? {
        EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Bind(bind))) => Ok(bind),
        _ => Err(Rejection::Unsupported),
    }
}

fn check_registration_contexts(
    work: &mut TypeWorkBudget,
    contexts: &[BinderId],
    live: &[BinderId],
) -> Result<(), Rejection> {
    for context in contexts {
        work.charge(live.len()).map_err(|()| Rejection::Exhausted)?;
        if live.contains(context) {
            return Err(Rejection::Unsupported);
        }
    }
    Ok(())
}

fn registration_call<'a>(
    inspect: &mut CoreInspection<'a, '_>,
    node: NodeId,
    target: BinderId,
    count: usize,
    api: crate::module::ModuleId,
) -> Result<CheckedPersistentTuple<'a>, Rejection> {
    let call = inspect.application(node)?;
    if inspect.variable(call.function())? != target {
        return Err(Rejection::Unsupported);
    }
    let arguments = inspect.persistent_tuple(call.argument(), None)?;
    if arguments.api != api || arguments.fields.len() != count {
        return Err(Rejection::Unsupported);
    }
    Ok(arguments)
}

fn expect_variable(
    inspect: &mut CoreInspection<'_, '_>,
    node: NodeId,
    binder: BinderId,
) -> Result<(), Rejection> {
    if inspect.variable(node)? != binder {
        return Err(Rejection::Unsupported);
    }
    Ok(())
}

fn reconstruct_registration_success<'a>(
    program: &'a dyn LedgerArena,
    linked: &ValidatedInterfaceProgram,
    candidate: DefinitionCandidate,
    helpers: [DefinitionCandidate; 3],
    c: RegistrationSuccessConstructors,
    work: &mut TypeWorkBudget,
) -> Result<RegistrationSuccessGraph<'a>, Rejection> {
    let capture_names = [helpers[0].binder, helpers[1].binder, helpers[2].binder];
    for helper in helpers {
        linked_initializer(program, linked, helper, work)?;
    }
    let counter = reconstruct_registration_counter(
        program,
        linked,
        candidate,
        &capture_names,
        c.ledger,
        work,
    )?;
    let mut inspect = CoreInspection { program, work };
    let branch = inspect.branch(counter.argument_match)?;
    let [arm] = branch.arms() else {
        return Err(Rejection::Unsupported);
    };
    let super::CorePatternKind::Tuple(patterns) = &arm.pattern().kind else {
        return Err(Rejection::Unsupported);
    };
    let [
        next,
        owner,
        wanted,
        destination,
        payload,
        records,
        outputs,
        parent,
        children,
    ] = patterns.as_ref()
    else {
        return Err(Rejection::Unsupported);
    };
    let arguments = [
        binder_pattern(next)?,
        binder_pattern(owner)?,
        binder_pattern(wanted)?,
        binder_pattern(destination)?,
        binder_pattern(payload)?,
        binder_pattern(records)?,
        binder_pattern(outputs)?,
        binder_pattern(parent)?,
        binder_pattern(children)?,
    ];
    let [
        next,
        owner,
        wanted,
        destination,
        payload,
        records,
        outputs,
        parent,
        children,
    ] = arguments;
    let first = registration_bind(&mut inspect, arm.body())?;
    let second = registration_bind(&mut inspect, first.body())?;
    let third = registration_bind(&mut inspect, second.body())?;
    let fourth = registration_bind(&mut inspect, third.body())?;
    if fourth.body() != counter.result.root {
        return Err(Rejection::Unsupported);
    }
    let child_id = first.binder().id();
    let replacement_id = second.binder().id();
    let remaining_id = third.binder().id();
    let outgoing_id = fourth.binder().id();
    require_distinct(
        inspect.work,
        &[
            next,
            owner,
            wanted,
            destination,
            payload,
            records,
            outputs,
            parent,
            children,
            child_id,
            replacement_id,
            remaining_id,
            outgoing_id,
            capture_names[0],
            capture_names[1],
            capture_names[2],
        ],
    )?;
    let api = counter.definition.api;
    let work_value = constructor_application(&mut inspect, first.initializer(), c.work, 2, api)?;
    expect_variable(&mut inspect, work_value.arguments.fields[0], owner)?;
    expect_variable(&mut inspect, work_value.arguments.fields[1], next)?;
    let replacement =
        constructor_application(&mut inspect, second.initializer(), c.record, 4, api)?;
    expect_variable(&mut inspect, replacement.arguments.fields[0], wanted)?;
    expect_variable(&mut inspect, replacement.arguments.fields[1], parent)?;
    nullary_constructor(&mut inspect, replacement.arguments.fields[2], c.open, api)?;
    let child_append = replacement.arguments.fields[3];
    let child_args = registration_call(&mut inspect, child_append, capture_names[0], 2, api)?;
    let child = constructor_application(&mut inspect, child_args.fields[0], c.child, 2, api)?;
    expect_variable(&mut inspect, child.arguments.fields[0], child_id)?;
    expect_variable(&mut inspect, child.arguments.fields[1], destination)?;
    expect_variable(&mut inspect, child_args.fields[1], children)?;
    let update = registration_call(&mut inspect, third.initializer(), capture_names[1], 3, api)?;
    expect_variable(&mut inspect, update.fields[0], wanted)?;
    expect_variable(&mut inspect, update.fields[1], replacement_id)?;
    expect_variable(&mut inspect, update.fields[2], records)?;
    let output_args =
        registration_call(&mut inspect, fourth.initializer(), capture_names[2], 2, api)?;
    let output = constructor_application(&mut inspect, output_args.fields[0], c.work_out, 4, api)?;
    expect_variable(&mut inspect, output.arguments.fields[0], child_id)?;
    let parent_value =
        constructor_application(&mut inspect, output.arguments.fields[1], c.parent, 2, api)?;
    expect_variable(&mut inspect, parent_value.arguments.fields[0], owner)?;
    expect_variable(&mut inspect, parent_value.arguments.fields[1], wanted)?;
    expect_variable(&mut inspect, output.arguments.fields[2], destination)?;
    expect_variable(&mut inspect, output.arguments.fields[3], payload)?;
    expect_variable(&mut inspect, output_args.fields[1], outputs)?;
    expect_variable(
        &mut inspect,
        counter.successor.arguments.fields[1],
        remaining_id,
    )?;
    expect_variable(
        &mut inspect,
        counter.successor.arguments.fields[2],
        outgoing_id,
    )?;
    let status_call = inspect.application(counter.status)?;
    expect_variable(&mut inspect, status_call.argument(), child_id)?;
    let status_closure = inspect.stored_function_witness(status_call.function(), &[])?;
    let status_value = inspect.persistent_tuple(status_closure.body, Some(c.registered))?;
    let [status_field] = status_value.fields else {
        return Err(Rejection::Unsupported);
    };
    expect_variable(&mut inspect, *status_field, status_closure.parameter)?;
    if status_closure.api != api
        || status_value.api != api
        || status_closure.parameter == status_value.context_binder
    {
        return Err(Rejection::Unsupported);
    }
    let live = [
        next,
        owner,
        wanted,
        destination,
        payload,
        records,
        outputs,
        parent,
        children,
        child_id,
        replacement_id,
        remaining_id,
        outgoing_id,
        capture_names[0],
        capture_names[1],
        capture_names[2],
    ];
    check_registration_contexts(
        inspect.work,
        &[
            work_value.arguments.context_binder,
            replacement.arguments.context_binder,
            child_args.context_binder,
            child.arguments.context_binder,
            update.context_binder,
            output_args.context_binder,
            output.arguments.context_binder,
            parent_value.arguments.context_binder,
            counter.successor.arguments.context_binder,
            counter.increment.context_binder,
            counter.result.context_binder,
        ],
        &live,
    )?;
    Ok(RegistrationSuccessGraph {
        counter,
        work_value,
        replacement,
        child,
        parent: parent_value,
        output,
        helper_calls: [child_append, third.initializer(), fourth.initializer()],
        status_closure,
    })
}

#[derive(Clone, Copy)]
struct RegistrationFlowConstructors {
    ledger: crate::types::ConstructorId,
    record: crate::types::ConstructorId,
    no_record: crate::types::ConstructorId,
    has_record: crate::types::ConstructorId,
    closed: crate::types::ConstructorId,
    open: crate::types::ConstructorId,
    rejected: crate::types::ConstructorId,
}

/// The two rejecting branches return exactly the original ledger and Rejected.
fn registration_rejection<'a>(
    inspect: &mut CoreInspection<'a, '_>,
    node: NodeId,
    ledger: BinderId,
    rejected: crate::types::ConstructorId,
    api: crate::module::ModuleId,
) -> Result<CheckedPersistentTuple<'a>, Rejection> {
    let result = inspect.persistent_tuple(node, None)?;
    let [original, status] = result.fields else {
        return Err(Rejection::Unsupported);
    };
    if result.api != api {
        return Err(Rejection::Unsupported);
    }
    expect_variable(inspect, *original, ledger)?;
    nullary_constructor(inspect, *status, rejected, api)?;
    Ok(result)
}

struct RegistrationFlowGraph<'a> {
    arena: &'a dyn LedgerArena,
    linked: &'a ValidatedInterfaceProgram,
    entry: CheckedStoredFunction<'a>,
    finish: CheckedStoredFunction<'a>,
    missing_result: CheckedPersistentTuple<'a>,
    closed_result: CheckedPersistentTuple<'a>,
    find_call: NodeId,
    finish_call: NodeId,
    commit_call: NodeId,
}

/// Reconstruct every entry/finish branch and its exact forwarded arguments.
/// The successful commit and helper laws must still be composed before use.
#[expect(
    clippy::too_many_arguments,
    reason = "Linked definitions, constructors and the shared work budget are distinct inputs"
)]
fn reconstruct_registration_flow<'a>(
    program: &'a dyn LedgerArena,
    linked: &'a ValidatedInterfaceProgram,
    entry_candidate: DefinitionCandidate,
    find_candidate: DefinitionCandidate,
    finish_candidate: DefinitionCandidate,
    commit_candidate: DefinitionCandidate,
    c: RegistrationFlowConstructors,
    work: &mut TypeWorkBudget,
) -> Result<RegistrationFlowGraph<'a>, Rejection> {
    let entry_id = linked_initializer(program, linked, entry_candidate, work)?;
    let find_id = linked_initializer(program, linked, find_candidate, work)?;
    let finish_id = linked_initializer(program, linked, finish_candidate, work)?;
    let commit_id = linked_initializer(program, linked, commit_candidate, work)?;
    reject_evidence(program, &[entry_id, find_id, finish_id, commit_id], work)?;
    let mut inspect = CoreInspection { program, work };
    let entry = inspect
        .stored_function_witness(entry_id, &[find_candidate.binder, finish_candidate.binder])?;
    let finish = inspect.stored_function_witness(finish_id, &[commit_candidate.binder])?;
    let api = entry.api;
    if finish.api != api {
        return Err(Rejection::Unsupported);
    }
    let args = inspect.branch(entry.body)?;
    if inspect.variable(args.scrutinee())? != entry.parameter {
        return Err(Rejection::Unsupported);
    }
    let [args_arm] = args.arms() else {
        return Err(Rejection::Unsupported);
    };
    let super::CorePatternKind::Tuple(fields) = &args_arm.pattern().kind else {
        return Err(Rejection::Unsupported);
    };
    let [ledger, owner, wanted, destination, payload] = fields.as_ref() else {
        return Err(Rejection::Unsupported);
    };
    let [ledger, owner, wanted, destination, payload] = [
        binder_pattern(ledger)?,
        binder_pattern(owner)?,
        binder_pattern(wanted)?,
        binder_pattern(destination)?,
        binder_pattern(payload)?,
    ];
    let ledger_match = inspect.branch(args_arm.body())?;
    expect_variable(&mut inspect, ledger_match.scrutinee(), ledger)?;
    let [ledger_arm] = ledger_match.arms() else {
        return Err(Rejection::Unsupported);
    };
    let ledger_pattern =
        constructor_pattern(ledger_arm.pattern(), c.ledger)?.ok_or(Rejection::Unsupported)?;
    let super::CorePatternKind::Tuple(fields) = &ledger_pattern.kind else {
        return Err(Rejection::Unsupported);
    };
    let [next, records, outputs] = fields.as_ref() else {
        return Err(Rejection::Unsupported);
    };
    let [next, records, outputs] = [
        binder_pattern(next)?,
        binder_pattern(records)?,
        binder_pattern(outputs)?,
    ];
    let found_match = inspect.branch(ledger_arm.body())?;
    let find_call = found_match.scrutinee();
    let find_args = registration_call(&mut inspect, find_call, find_candidate.binder, 2, api)?;
    expect_variable(&mut inspect, find_args.fields[0], wanted)?;
    expect_variable(&mut inspect, find_args.fields[1], records)?;
    let [missing, found] = found_match.arms() else {
        return Err(Rejection::Unsupported);
    };
    if constructor_pattern(missing.pattern(), c.no_record)?.is_some() {
        return Err(Rejection::Unsupported);
    }
    let record = binder_pattern(
        constructor_pattern(found.pattern(), c.has_record)?.ok_or(Rejection::Unsupported)?,
    )?;
    let missing_result =
        registration_rejection(&mut inspect, missing.body(), ledger, c.rejected, api)?;
    let finish_call = found.body();
    let forwarded = registration_call(&mut inspect, finish_call, finish_candidate.binder, 9, api)?;
    for (field, binder) in forwarded.fields.iter().zip([
        record,
        ledger,
        next,
        owner,
        wanted,
        destination,
        payload,
        records,
        outputs,
    ]) {
        expect_variable(&mut inspect, *field, binder)?;
    }
    require_distinct(
        inspect.work,
        &[
            ledger,
            owner,
            wanted,
            destination,
            payload,
            next,
            records,
            outputs,
            record,
            find_candidate.binder,
            finish_candidate.binder,
        ],
    )?;
    check_registration_contexts(
        inspect.work,
        &[
            find_args.context_binder,
            missing_result.context_binder,
            forwarded.context_binder,
        ],
        &[
            ledger,
            owner,
            wanted,
            destination,
            payload,
            next,
            records,
            outputs,
            record,
            find_candidate.binder,
            finish_candidate.binder,
        ],
    )?;
    let finish_args = inspect.branch(finish.body)?;
    if inspect.variable(finish_args.scrutinee())? != finish.parameter {
        return Err(Rejection::Unsupported);
    }
    let [finish_arm] = finish_args.arms() else {
        return Err(Rejection::Unsupported);
    };
    let super::CorePatternKind::Tuple(fields) = &finish_arm.pattern().kind else {
        return Err(Rejection::Unsupported);
    };
    let [
        record,
        ledger,
        next,
        owner,
        wanted,
        destination,
        payload,
        records,
        outputs,
    ] = fields.as_ref()
    else {
        return Err(Rejection::Unsupported);
    };
    let [
        record,
        ledger,
        next,
        owner,
        wanted,
        destination,
        payload,
        records,
        outputs,
    ] = [
        binder_pattern(record)?,
        binder_pattern(ledger)?,
        binder_pattern(next)?,
        binder_pattern(owner)?,
        binder_pattern(wanted)?,
        binder_pattern(destination)?,
        binder_pattern(payload)?,
        binder_pattern(records)?,
        binder_pattern(outputs)?,
    ];
    let record_match = inspect.branch(finish_arm.body())?;
    expect_variable(&mut inspect, record_match.scrutinee(), record)?;
    let [record_arm] = record_match.arms() else {
        return Err(Rejection::Unsupported);
    };
    let record_pattern =
        constructor_pattern(record_arm.pattern(), c.record)?.ok_or(Rejection::Unsupported)?;
    let super::CorePatternKind::Tuple(fields) = &record_pattern.kind else {
        return Err(Rejection::Unsupported);
    };
    let [actual, parent, phase, children] = fields.as_ref() else {
        return Err(Rejection::Unsupported);
    };
    let [actual, parent, phase, children] = [
        binder_pattern(actual)?,
        binder_pattern(parent)?,
        binder_pattern(phase)?,
        binder_pattern(children)?,
    ];
    let phase_match = inspect.branch(record_arm.body())?;
    expect_variable(&mut inspect, phase_match.scrutinee(), phase)?;
    let [closed, open] = phase_match.arms() else {
        return Err(Rejection::Unsupported);
    };
    if constructor_pattern(closed.pattern(), c.closed)?.is_some()
        || constructor_pattern(open.pattern(), c.open)?.is_some()
    {
        return Err(Rejection::Unsupported);
    }
    let closed_result =
        registration_rejection(&mut inspect, closed.body(), ledger, c.rejected, api)?;
    let commit_call = open.body();
    let forwarded = registration_call(&mut inspect, commit_call, commit_candidate.binder, 9, api)?;
    for (field, binder) in forwarded.fields.iter().zip([
        next,
        owner,
        wanted,
        destination,
        payload,
        records,
        outputs,
        parent,
        children,
    ]) {
        expect_variable(&mut inspect, *field, binder)?;
    }
    require_distinct(
        inspect.work,
        &[
            record,
            ledger,
            next,
            owner,
            wanted,
            destination,
            payload,
            records,
            outputs,
            actual,
            parent,
            phase,
            children,
            commit_candidate.binder,
        ],
    )?;
    check_registration_contexts(
        inspect.work,
        &[closed_result.context_binder, forwarded.context_binder],
        &[
            record,
            ledger,
            next,
            owner,
            wanted,
            destination,
            payload,
            records,
            outputs,
            actual,
            parent,
            phase,
            children,
            commit_candidate.binder,
        ],
    )?;
    Ok(RegistrationFlowGraph {
        arena: program,
        linked,
        entry,
        finish,
        missing_result,
        closed_result,
        find_call,
        finish_call,
        commit_call,
    })
}

/// Exact linked capture-free Record key projection used by lookup and update.
/// Its shape is conditional on the represented record and provider at the call.
struct RecordProjectionGraph<'a> {
    arena: &'a dyn LedgerArena,
    linked: &'a ValidatedInterfaceProgram,
    candidate: DefinitionCandidate,
    definition: CheckedStoredFunction<'a>,
    record: crate::types::ConstructorId,
    scrutinee: NodeId,
    result: NodeId,
    fields: [BinderId; 4],
}

fn reconstruct_record_projection<'a>(
    program: &'a dyn LedgerArena,
    linked: &'a ValidatedInterfaceProgram,
    candidate: DefinitionCandidate,
    record: crate::types::ConstructorId,
    identity: crate::types::ConstructorId,
    work: &mut TypeWorkBudget,
) -> Result<RecordProjectionGraph<'a>, Rejection> {
    use crate::types::Type;
    work.charge(1).map_err(|()| Rejection::Exhausted)?;
    if program.registry().constructor(identity).is_none() {
        return Err(Rejection::Unsupported);
    }
    let Type::Tuple(payload) = singleton_payload(program, record, work)? else {
        return Err(Rejection::Unsupported);
    };
    if !matches!(payload.as_ref(), [Type::Nominal(id), Type::Nominal(_), Type::Nominal(_), Type::Nominal(_)] if *id == identity.owner())
    {
        return Err(Rejection::Unsupported);
    }
    let initializer = linked_initializer(program, linked, candidate, work)?;
    reject_evidence(program, &[initializer], work)?;
    let mut inspect = CoreInspection { program, work };
    let definition = inspect.stored_function_witness(initializer, &[])?;
    let branch = inspect.branch(definition.body)?;
    if inspect.variable(branch.scrutinee())? != definition.parameter {
        return Err(Rejection::Unsupported);
    }
    let [arm] = branch.arms() else {
        return Err(Rejection::Unsupported);
    };
    let payload = constructor_pattern(arm.pattern(), record)?.ok_or(Rejection::Unsupported)?;
    let super::CorePatternKind::Tuple(patterns) = &payload.kind else {
        return Err(Rejection::Unsupported);
    };
    let [key, parent, phase, children] = patterns.as_ref() else {
        return Err(Rejection::Unsupported);
    };
    let fields = [
        binder_pattern(key)?,
        binder_pattern(parent)?,
        binder_pattern(phase)?,
        binder_pattern(children)?,
    ];
    require_distinct(inspect.work, &fields)?;
    if inspect.variable(arm.body())? != fields[0] {
        return Err(Rejection::Unsupported);
    }
    Ok(RecordProjectionGraph {
        arena: program,
        linked,
        candidate,
        definition,
        record,
        scrutinee: branch.scrutinee(),
        result: arm.body(),
        fields,
    })
}

#[derive(Clone, Copy)]
struct RecordListConstructors {
    root: crate::types::ConstructorId,
    work: crate::types::ConstructorId,
    record: crate::types::ConstructorId,
    empty: crate::types::ConstructorId,
    more: crate::types::ConstructorId,
    absent: crate::types::ConstructorId,
    present: crate::types::ConstructorId,
}

#[derive(Clone, Copy)]
enum RecordOperation {
    Lookup,
    Update,
}

/// The exact checked result constructors of a Record-list operation.
#[expect(
    clippy::large_enum_variant,
    reason = "Keep checked branch witnesses inline without an uncharged allocation"
)]
enum RecordOperationBranches<'a> {
    Lookup {
        present_call: NodeId,
        present_closure: CheckedStoredFunction<'a>,
        present_value: CheckedPersistentTuple<'a>,
    },
    Update {
        replaced: ConstructorApplication<'a>,
        retained: ConstructorApplication<'a>,
    },
}

/// Actual nodes for one Record-list operation; no semantic fact is issued here.
struct RecordOperationGraph<'a> {
    arena: &'a dyn LedgerArena,
    linked: &'a ValidatedInterfaceProgram,
    candidate: DefinitionCandidate,
    constructors: RecordListConstructors,
    definition: CheckedStoredFunction<'a>,
    projection: RecordProjectionGraph<'a>,
    comparison: CheckedStoredFunction<'a>,
    argument_match: NodeId,
    list_match: NodeId,
    comparison_match: NodeId,
    comparison_call: NodeId,
    projection_call: NodeId,
    recursive_call: NodeId,
    wanted: BinderId,
    replacement: Option<BinderId>,
    list: BinderId,
    entry: BinderId,
    tail: BinderId,
    empty_result: CheckedPersistentTuple<'a>,
    comparator_pair: CheckedPersistentTuple<'a>,
    comparison_pair: CheckedPersistentTuple<'a>,
    recursive_pair: CheckedPersistentTuple<'a>,
    branches: RecordOperationBranches<'a>,
}

#[expect(
    clippy::too_many_arguments,
    reason = "Linked definitions, constructors and the shared work budget are distinct inputs"
)]
fn reconstruct_record_operation<'a>(
    program: &'a dyn LedgerArena,
    linked: &'a ValidatedInterfaceProgram,
    candidate: DefinitionCandidate,
    comparison: DefinitionCandidate,
    projection: DefinitionCandidate,
    c: RecordListConstructors,
    operation: RecordOperation,
    work: &mut TypeWorkBudget,
) -> Result<RecordOperationGraph<'a>, Rejection> {
    use crate::types::Type;
    exact_nominal_pair(program, c.root, c.work, work)?;
    exact_nominal_pair(program, c.empty, c.more, work)?;
    exact_nominal_pair(program, c.absent, c.present, work)?;
    let projection_graph =
        reconstruct_record_projection(program, linked, projection, c.record, c.root, work)?;
    work.charge(4).map_err(|()| Rejection::Exhausted)?;
    let registry = program.registry();
    if registry
        .constructor(c.root)
        .ok_or(Rejection::Unsupported)?
        .payload
        .is_some()
        || registry
            .constructor(c.empty)
            .ok_or(Rejection::Unsupported)?
            .payload
            .is_some()
        || registry
            .constructor(c.absent)
            .ok_or(Rejection::Unsupported)?
            .payload
            .is_some()
    {
        return Err(Rejection::Unsupported);
    }
    let Some(Type::Tuple(work_fields)) = &registry
        .constructor(c.work)
        .ok_or(Rejection::Unsupported)?
        .payload
    else {
        return Err(Rejection::Unsupported);
    };
    if !matches!(work_fields.as_ref(), [Type::Int, Type::Int]) {
        return Err(Rejection::Unsupported);
    }
    let Some(Type::Tuple(list_fields)) = &registry
        .constructor(c.more)
        .ok_or(Rejection::Unsupported)?
        .payload
    else {
        return Err(Rejection::Unsupported);
    };
    if !matches!(list_fields.as_ref(), [Type::Nominal(record), Type::Nominal(list)] if *record == c.record.owner() && *list == c.empty.owner())
    {
        return Err(Rejection::Unsupported);
    }
    if !matches!(&registry.constructor(c.present).ok_or(Rejection::Unsupported)?.payload, Some(Type::Nominal(record)) if *record == c.record.owner())
    {
        return Err(Rejection::Unsupported);
    }
    let initializer = linked_initializer(program, linked, candidate, work)?;
    let comparison_id = linked_initializer(program, linked, comparison, work)?;
    reject_evidence(program, &[initializer, comparison_id], work)?;
    let mut inspect = CoreInspection { program, work };
    let definition = inspect.stored_function_witness(
        initializer,
        &[candidate.binder, comparison.binder, projection.binder],
    )?;
    let comparison_function = inspect.stored_function_witness(comparison_id, &[])?;
    check_id_comparison(&mut inspect, comparison_id, c.root, c.work)?;
    let comparator_arguments = inspect.branch(comparison_function.body)?;
    let [comparator_arm] = comparator_arguments.arms() else {
        return Err(Rejection::Unsupported);
    };
    let (left, right) = pattern_pair(comparator_arm.pattern())?;
    let (left, right) = (binder_pattern(left)?, binder_pattern(right)?);
    let comparator_cases = inspect.branch(comparator_arm.body())?;
    let comparator_pair = inspect.persistent_tuple(comparator_cases.scrutinee(), None)?;
    let [_, work_arm, _] = comparator_cases.arms() else {
        return Err(Rejection::Unsupported);
    };
    let (left_work, right_work) = pattern_pair(work_arm.pattern())?;
    let left_work = constructor_pattern(left_work, c.work)?.ok_or(Rejection::Unsupported)?;
    let right_work = constructor_pattern(right_work, c.work)?.ok_or(Rejection::Unsupported)?;
    let (left_allocator, left_serial) = pattern_pair(left_work)?;
    let (right_allocator, right_serial) = pattern_pair(right_work)?;
    let comparator_fields = [
        binder_pattern(left_allocator)?,
        binder_pattern(left_serial)?,
        binder_pattern(right_allocator)?,
        binder_pattern(right_serial)?,
    ];
    require_distinct(inspect.work, &[left, right])?;
    require_distinct(inspect.work, &comparator_fields)?;
    if comparator_pair.context_binder == left || comparator_pair.context_binder == right {
        return Err(Rejection::Unsupported);
    }
    let api = definition.api;
    if comparator_pair.api != api {
        return Err(Rejection::Unsupported);
    }
    if projection_graph.definition.api != api || comparison_function.api != api {
        return Err(Rejection::Unsupported);
    }
    let arguments = inspect.branch(definition.body)?;
    expect_variable(&mut inspect, arguments.scrutinee(), definition.parameter)?;
    let [arm] = arguments.arms() else {
        return Err(Rejection::Unsupported);
    };
    let super::CorePatternKind::Tuple(fields) = &arm.pattern().kind else {
        return Err(Rejection::Unsupported);
    };
    let (wanted, replacement, list) = match (operation, fields.as_ref()) {
        (RecordOperation::Lookup, [wanted, list]) => {
            (binder_pattern(wanted)?, None, binder_pattern(list)?)
        }
        (RecordOperation::Update, [wanted, replacement, list]) => (
            binder_pattern(wanted)?,
            Some(binder_pattern(replacement)?),
            binder_pattern(list)?,
        ),
        _ => return Err(Rejection::Unsupported),
    };
    let list_cases = inspect.branch(arm.body())?;
    expect_variable(&mut inspect, list_cases.scrutinee(), list)?;
    let [empty, more] = list_cases.arms() else {
        return Err(Rejection::Unsupported);
    };
    if constructor_pattern(empty.pattern(), c.empty)?.is_some() {
        return Err(Rejection::Unsupported);
    }
    let payload = constructor_pattern(more.pattern(), c.more)?.ok_or(Rejection::Unsupported)?;
    let (entry, tail) = pattern_pair(payload)?;
    let (entry, tail) = (binder_pattern(entry)?, binder_pattern(tail)?);
    let empty_result = match operation {
        RecordOperation::Lookup => c.absent,
        RecordOperation::Update => c.empty,
    };
    let empty_value = nullary_constructor(&mut inspect, empty.body(), empty_result, api)?;
    let compared = inspect.branch(more.body())?;
    let comparison_call = compared.scrutinee();
    let comparison_pair =
        registration_call(&mut inspect, comparison_call, comparison.binder, 2, api)?;
    let projection_call = inspect.application(comparison_pair.fields[0])?;
    expect_variable(&mut inspect, projection_call.function(), projection.binder)?;
    expect_variable(&mut inspect, projection_call.argument(), entry)?;
    expect_variable(&mut inspect, comparison_pair.fields[1], wanted)?;
    let [hit, miss] = compared.arms() else {
        return Err(Rejection::Unsupported);
    };
    if !matches!(hit.pattern().kind, super::CorePatternKind::Boolean(true))
        || !matches!(miss.pattern().kind, super::CorePatternKind::Boolean(false))
    {
        return Err(Rejection::Unsupported);
    }
    let (recursive_call, branches) = match operation {
        RecordOperation::Lookup => {
            let present = inspect.application(hit.body())?;
            expect_variable(&mut inspect, present.argument(), entry)?;
            let closure = inspect.stored_function_witness(present.function(), &[])?;
            let value = inspect.persistent_tuple(closure.body, Some(c.present))?;
            let [field] = value.fields else {
                return Err(Rejection::Unsupported);
            };
            expect_variable(&mut inspect, *field, closure.parameter)?;
            if closure.api != api || value.api != api || closure.parameter == value.context_binder {
                return Err(Rejection::Unsupported);
            }
            (
                miss.body(),
                RecordOperationBranches::Lookup {
                    present_call: hit.body(),
                    present_closure: closure,
                    present_value: value,
                },
            )
        }
        RecordOperation::Update => {
            let replacement = replacement.ok_or(Rejection::Unsupported)?;
            let replaced = constructor_application(&mut inspect, hit.body(), c.more, 2, api)?;
            expect_variable(&mut inspect, replaced.arguments.fields[0], replacement)?;
            expect_variable(&mut inspect, replaced.arguments.fields[1], tail)?;
            let retained = constructor_application(&mut inspect, miss.body(), c.more, 2, api)?;
            expect_variable(&mut inspect, retained.arguments.fields[0], entry)?;
            check_registration_contexts(
                inspect.work,
                &[
                    replaced.arguments.context_binder,
                    retained.arguments.context_binder,
                ],
                &[wanted, replacement, list, entry, tail, candidate.binder],
            )?;
            (
                retained.arguments.fields[1],
                RecordOperationBranches::Update { replaced, retained },
            )
        }
    };
    let recursive_pair = registration_call(
        &mut inspect,
        recursive_call,
        candidate.binder,
        if replacement.is_some() { 3 } else { 2 },
        api,
    )?;
    expect_variable(&mut inspect, recursive_pair.fields[0], wanted)?;
    if let Some(replacement) = replacement {
        expect_variable(&mut inspect, recursive_pair.fields[1], replacement)?;
    }
    expect_variable(
        &mut inspect,
        *recursive_pair.fields.last().ok_or(Rejection::Unsupported)?,
        tail,
    )?;
    let binders = [
        definition.parameter,
        wanted,
        list,
        entry,
        tail,
        candidate.binder,
        comparison.binder,
        projection.binder,
    ];
    require_distinct(inspect.work, &binders)?;
    if let Some(replacement) = replacement {
        inspect
            .work
            .charge(binders.len())
            .map_err(|()| Rejection::Exhausted)?;
        if binders.contains(&replacement) {
            return Err(Rejection::Unsupported);
        }
    }
    if replacement == Some(recursive_pair.context_binder) {
        return Err(Rejection::Unsupported);
    }
    if [wanted, tail].contains(&recursive_pair.context_binder)
        || [wanted, entry, projection.binder].contains(&comparison_pair.context_binder)
    {
        return Err(Rejection::Unsupported);
    }
    Ok(RecordOperationGraph {
        arena: program,
        linked,
        candidate,
        constructors: c,
        definition,
        projection: projection_graph,
        comparison: comparison_function,
        argument_match: definition.body,
        list_match: arm.body(),
        comparison_match: more.body(),
        comparison_call,
        projection_call: comparison_pair.fields[0],
        recursive_call,
        wanted,
        replacement,
        list,
        entry,
        tail,
        empty_result: empty_value,
        comparator_pair,
        comparison_pair,
        recursive_pair,
        branches,
    })
}

/// A definition-bound Record-list law, conditional on the exact capture,
/// represented finite values and faithfully selected nonreentrant provider.
/// It conveys no current-state, freshness or network-release authority.
struct ConditionalRecordOperation<'a> {
    graph: RecordOperationGraph<'a>,
}

#[expect(
    clippy::too_many_arguments,
    reason = "Linked definitions, constructors and the shared work budget are distinct inputs"
)]
fn check_conditional_record_operation<'a>(
    program: &'a dyn LedgerArena,
    linked: &'a ValidatedInterfaceProgram,
    candidate: DefinitionCandidate,
    comparison: DefinitionCandidate,
    projection: DefinitionCandidate,
    constructors: RecordListConstructors,
    operation: RecordOperation,
    work: &mut TypeWorkBudget,
) -> Result<ConditionalRecordOperation<'a>, Rejection> {
    let graph = reconstruct_record_operation(
        program,
        linked,
        candidate,
        comparison,
        projection,
        constructors,
        operation,
        work,
    )?;
    Ok(ConditionalRecordOperation { graph })
}

#[derive(Clone, Copy, Eq, PartialEq)]
pub(super) struct RegistrationDefinitions {
    pub(super) entry: DefinitionCandidate,
    pub(super) find: DefinitionCandidate,
    pub(super) finish: DefinitionCandidate,
    pub(super) commit: DefinitionCandidate,
    pub(super) append_child: DefinitionCandidate,
    pub(super) update: DefinitionCandidate,
    pub(super) append_output: DefinitionCandidate,
    pub(super) comparison: DefinitionCandidate,
    pub(super) projection: DefinitionCandidate,
}

#[derive(Clone, Copy, Eq, PartialEq)]
pub(super) struct RegistrationConstructors {
    pub(super) state: InitializationConstructors,
    pub(super) no_record: crate::types::ConstructorId,
    pub(super) has_record: crate::types::ConstructorId,
    pub(super) rejected: crate::types::ConstructorId,
    pub(super) registered: crate::types::ConstructorId,
    pub(super) child: crate::types::ConstructorId,
    pub(super) work_out: crate::types::ConstructorId,
}

/// Complete bounded shape reconstruction. It confers no semantic fact until
/// the execution correspondence and consuming call premises are established.
struct CheckedRegistrationGraph<'a> {
    arena: &'a dyn LedgerArena,
    linked: &'a ValidatedInterfaceProgram,
    flow: RegistrationFlowGraph<'a>,
    success: RegistrationSuccessGraph<'a>,
    lookup: ConditionalRecordOperation<'a>,
    update: ConditionalRecordOperation<'a>,
    child_append: ConditionalSpineInsertion<'a>,
    output_append: ConditionalSpineInsertion<'a>,
}

fn reconstruct_registration<'a>(
    program: &'a dyn LedgerArena,
    linked: &'a ValidatedInterfaceProgram,
    d: RegistrationDefinitions,
    c: RegistrationConstructors,
    work: &mut TypeWorkBudget,
) -> Result<CheckedRegistrationGraph<'a>, Rejection> {
    use crate::types::Type;
    check_initialization_nominals(program, c.state, work)?;
    exact_nominal_pair(program, c.no_record, c.has_record, work)?;
    exact_nominal_pair(program, c.rejected, c.registered, work)?;
    require_distinct(
        work,
        &[
            d.entry.binder,
            d.find.binder,
            d.finish.binder,
            d.commit.binder,
            d.append_child.binder,
            d.update.binder,
            d.append_output.binder,
            d.comparison.binder,
            d.projection.binder,
        ],
    )?;
    work.charge(3).map_err(|()| Rejection::Exhausted)?;
    let registry = program.registry();
    if registry
        .constructor(c.rejected)
        .ok_or(Rejection::Unsupported)?
        .payload
        .is_some()
        || !matches!(&registry.constructor(c.registered).ok_or(Rejection::Unsupported)?.payload,
            Some(Type::Nominal(id)) if *id == c.state.root.owner())
    {
        return Err(Rejection::Unsupported);
    }
    let Some(Type::Tuple(output_fields)) = &registry
        .constructor(c.work_out)
        .ok_or(Rejection::Unsupported)?
        .payload
    else {
        return Err(Rejection::Unsupported);
    };
    if !matches!(output_fields.as_ref(), [Type::Nominal(id), Type::Nominal(parent), Type::Int, Type::Bytes]
        if *id == c.state.root.owner() && *parent == c.state.parent.owner())
    {
        return Err(Rejection::Unsupported);
    }
    let success = reconstruct_registration_success(
        program,
        linked,
        d.commit,
        [d.append_child, d.update, d.append_output],
        RegistrationSuccessConstructors {
            ledger: c.state.ledger,
            work: c.state.work,
            child: c.child,
            record: c.state.record,
            open: c.state.open,
            parent: c.state.parent,
            work_out: c.work_out,
            registered: c.registered,
        },
        work,
    )?;
    let flow = reconstruct_registration_flow(
        program,
        linked,
        d.entry,
        d.find,
        d.finish,
        d.commit,
        RegistrationFlowConstructors {
            ledger: c.state.ledger,
            record: c.state.record,
            no_record: c.no_record,
            has_record: c.has_record,
            closed: c.state.closed,
            open: c.state.open,
            rejected: c.rejected,
        },
        work,
    )?;
    let list = RecordListConstructors {
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
        d.find,
        d.comparison,
        d.projection,
        list,
        RecordOperation::Lookup,
        work,
    )?;
    let update = check_conditional_record_operation(
        program,
        linked,
        d.update,
        d.comparison,
        d.projection,
        list,
        RecordOperation::Update,
        work,
    )?;
    let child_append = check_conditional_spine_insertion(
        program,
        linked,
        d.append_child,
        InsertConstructors {
            entry: c.child,
            empty: c.state.children_empty,
            more: c.state.children_more,
        },
        work,
    )?;
    let output_append = check_conditional_spine_insertion(
        program,
        linked,
        d.append_output,
        InsertConstructors {
            entry: c.work_out,
            empty: c.state.outputs_empty,
            more: c.state.outputs_more,
        },
        work,
    )?;
    let api = flow.entry.api;
    work.charge(5).map_err(|()| Rejection::Exhausted)?;
    if [
        success.counter.definition.api,
        lookup.graph.definition.api,
        update.graph.definition.api,
        child_append.graph.provider_api,
        output_append.graph.provider_api,
    ]
    .iter()
    .any(|found| *found != api)
    {
        return Err(Rejection::Unsupported);
    }
    Ok(CheckedRegistrationGraph {
        arena: program,
        linked,
        flow,
        success,
        lookup,
        update,
        child_append,
        output_append,
    })
}

/// A definition-bound registration law for represented finite inputs. The
/// consumer establishes the checked closures and captures, faithful selected
/// provider, nonreentrancy and valid nonnegative allocator representation.
/// This does not confer current-state, freshness or network-release authority.
struct ConditionalRegistration<'a> {
    graph: CheckedRegistrationGraph<'a>,
}

/// Reconstruct every registration branch and dependency under one budget.
/// Refusal or exhaustion returns no summary.
fn check_conditional_registration<'a>(
    program: &'a dyn LedgerArena,
    linked: &'a ValidatedInterfaceProgram,
    definitions: RegistrationDefinitions,
    constructors: RegistrationConstructors,
    work: &mut TypeWorkBudget,
) -> Result<ConditionalRegistration<'a>, Rejection> {
    let graph = reconstruct_registration(program, linked, definitions, constructors, work)?;
    Ok(ConditionalRegistration { graph })
}

/// A provisional, arena-bound call witness. It proves the nominated call and
/// definition shapes only; the same worker focus must establish actual target,
/// initialization, provider, currentness and matched normal return.
pub(super) struct ConditionalRegistrationCall<'a> {
    summary: ConditionalRegistration<'a>,
    definitions: RegistrationDefinitions,
    constructors: RegistrationConstructors,
    call: NodeId,
    arguments: CheckedPersistentTuple<'a>,
}

impl ConditionalRegistrationCall<'_> {
    pub(super) fn same_definition(&self, other: &Self) -> bool {
        std::ptr::eq(self.summary.graph.arena, other.summary.graph.arena)
            && std::ptr::eq(self.summary.graph.linked, other.summary.graph.linked)
            && self.definitions == other.definitions
            && self.constructors == other.constructors
    }
    pub(super) fn call(&self) -> NodeId {
        self.call
    }

    pub(super) fn input(&self) -> NodeId {
        self.arguments.fields[0]
    }

    pub(super) fn allocator(&self) -> NodeId {
        self.arguments.fields[1]
    }
    pub(super) fn argument_binding(&self) -> NodeId {
        self.arguments.root
    }

    pub(super) fn closure(&self) -> NodeId {
        self.summary.graph.flow.entry.closure
    }

    pub(super) fn provider_api(&self) -> crate::module::ModuleId {
        self.summary.graph.flow.entry.api
    }
    pub(super) fn definition_query(&self) -> NodeId {
        self.summary.graph.flow.entry.query
    }
    pub(super) fn definition_binding(&self) -> NodeId {
        self.summary.graph.flow.entry.root
    }
    pub(super) fn definition_context(&self) -> NodeId {
        self.summary.graph.flow.entry.context
    }
    pub(super) fn linked_helpers(&self) -> [(BinderId, NodeId); 9] {
        let graph = &self.summary.graph;
        let d = self.definitions;
        [
            (d.entry.binder, graph.flow.entry.closure),
            (d.find.binder, graph.lookup.graph.definition.closure),
            (d.finish.binder, graph.flow.finish.closure),
            (d.commit.binder, graph.success.counter.definition.closure),
            (
                d.append_child.binder,
                graph.child_append.graph.definition.closure,
            ),
            (d.update.binder, graph.update.graph.definition.closure),
            (
                d.append_output.binder,
                graph.output_append.graph.definition.closure,
            ),
            (d.comparison.binder, graph.lookup.graph.comparison.closure),
            (
                d.projection.binder,
                graph.lookup.graph.projection.definition.closure,
            ),
        ]
    }
    pub(super) fn definition_roots(&self) -> [NodeId; 9] {
        let d = self.definitions;
        [
            d.entry.initializer,
            d.find.initializer,
            d.finish.initializer,
            d.commit.initializer,
            d.append_child.initializer,
            d.update.initializer,
            d.append_output.initializer,
            d.comparison.initializer,
            d.projection.initializer,
        ]
    }
}

/// Check an untrusted nominated call against its unique linked target and all
/// actual definition bodies. The result remains provisional inside validation.
pub(super) fn check_nominated_registration_call<'a>(
    program: &'a dyn LedgerArena,
    linked: &'a ValidatedInterfaceProgram,
    call: NodeId,
    definitions: RegistrationDefinitions,
    constructors: RegistrationConstructors,
    work: &mut TypeWorkBudget,
) -> Result<ConditionalRegistrationCall<'a>, Rejection> {
    let mut inspect = CoreInspection { program, work };
    let application = inspect.application(call)?;
    if inspect.variable(application.function())? != definitions.entry.binder {
        return Err(Rejection::Unsupported);
    }
    let summary =
        check_conditional_registration(program, linked, definitions, constructors, inspect.work)?;
    let arguments = registration_call(
        &mut inspect,
        call,
        definitions.entry.binder,
        5,
        summary.graph.flow.entry.api,
    )?;
    Ok(ConditionalRegistrationCall {
        summary,
        definitions,
        constructors,
        call,
        arguments,
    })
}

/// The actual destructuring of a checked registration result. These binders
/// are source coordinates only; the worker trace must establish the matched
/// normal return and its exact pattern-projection ports before they are used.
pub(super) struct RegistrationResultMatch {
    pub(super) matching: NodeId,
    pub(super) ledger: BinderId,
    pub(super) status: BinderId,
    pub(super) body: NodeId,
}

pub(super) fn check_registration_result_match(
    program: &dyn LedgerArena,
    registration: &ConditionalRegistrationCall<'_>,
    matching: NodeId,
    work: &mut TypeWorkBudget,
) -> Result<RegistrationResultMatch, Rejection> {
    let mut inspect = CoreInspection { program, work };
    if !std::ptr::eq(program, registration.summary.graph.arena) {
        return Err(Rejection::Unsupported);
    }
    let branch = inspect.branch(matching)?;
    if branch.scrutinee() != registration.call {
        return Err(Rejection::Unsupported);
    }
    let [arm] = branch.arms() else {
        return Err(Rejection::Unsupported);
    };
    let super::CorePatternKind::Tuple(fields) = &arm.pattern().kind else {
        return Err(Rejection::Unsupported);
    };
    let [ledger, status] = fields.as_ref() else {
        return Err(Rejection::Unsupported);
    };
    let ledger = binder_pattern(ledger)?;
    let status = binder_pattern(status)?;
    require_distinct(inspect.work, &[ledger, status])?;
    Ok(RegistrationResultMatch {
        matching,
        ledger,
        status,
        body: arm.body(),
    })
}

/// Untrusted nominal coordinates for an ordered child lookup.
#[derive(Clone, Copy)]
struct LookupConstructors {
    root: crate::types::ConstructorId,
    work: crate::types::ConstructorId,
    child: crate::types::ConstructorId,
    empty: crate::types::ConstructorId,
    more: crate::types::ConstructorId,
    absent: crate::types::ConstructorId,
    present: crate::types::ConstructorId,
}

struct LookupGraph<'a> {
    arena: &'a dyn LedgerArena,
    candidate: DefinitionCandidate,
    constructors: LookupConstructors,
    dependencies: RemovalDependencies,
    definition: CheckedStoredFunction<'a>,
    comparison: CheckedStoredFunction<'a>,
    projection: CheckedStoredFunction<'a>,
    present_constructor: CheckedStoredFunction<'a>,
    provider_api: crate::module::ModuleId,
    argument_match: NodeId,
    list_match: NodeId,
    comparison_match: NodeId,
    comparison_call: NodeId,
    projection_call: NodeId,
    recursive_call: NodeId,
    present_call: NodeId,
    wanted: BinderId,
    list: BinderId,
    entry: BinderId,
    tail: BinderId,
    absent: CheckedPersistentTuple<'a>,
    comparison_pair: CheckedPersistentTuple<'a>,
    comparator_pair: CheckedPersistentTuple<'a>,
    recursive_pair: CheckedPersistentTuple<'a>,
    present_value: CheckedPersistentTuple<'a>,
}

fn check_lookup_nominals(
    program: &dyn LedgerArena,
    c: LookupConstructors,
    work: &mut TypeWorkBudget,
) -> Result<(), Rejection> {
    use crate::types::Type;
    for (left, right) in [(c.root, c.work), (c.empty, c.more), (c.absent, c.present)] {
        exact_nominal_pair(program, left, right, work)?;
    }
    let child = singleton_payload(program, c.child, work)?;
    let Type::Tuple(child_fields) = child else {
        return Err(Rejection::Unsupported);
    };
    if !matches!(child_fields.as_ref(), [Type::Nominal(identity), Type::Int] if *identity == c.root.owner())
    {
        return Err(Rejection::Unsupported);
    }
    work.charge(5).map_err(|()| Rejection::Exhausted)?;
    let registry = program.registry();
    for id in [c.root, c.empty, c.absent] {
        if registry
            .constructor(id)
            .ok_or(Rejection::Unsupported)?
            .payload
            .is_some()
        {
            return Err(Rejection::Unsupported);
        }
    }
    let Some(Type::Tuple(work_fields)) = &registry
        .constructor(c.work)
        .ok_or(Rejection::Unsupported)?
        .payload
    else {
        return Err(Rejection::Unsupported);
    };
    if !matches!(work_fields.as_ref(), [Type::Int, Type::Int]) {
        return Err(Rejection::Unsupported);
    }
    let Some(Type::Tuple(more_fields)) = &registry
        .constructor(c.more)
        .ok_or(Rejection::Unsupported)?
        .payload
    else {
        return Err(Rejection::Unsupported);
    };
    if !matches!(more_fields.as_ref(), [Type::Nominal(child), Type::Nominal(list)]
        if *child == c.child.owner() && *list == c.empty.owner())
    {
        return Err(Rejection::Unsupported);
    }
    // Charge the final actual payload lookup separately before reading it.
    work.charge(1).map_err(|()| Rejection::Exhausted)?;
    if !matches!(&registry.constructor(c.present).ok_or(Rejection::Unsupported)?.payload,
        Some(Type::Nominal(child)) if *child == c.child.owner())
    {
        return Err(Rejection::Unsupported);
    }
    Ok(())
}

/// Reconstruct all reachable lookup branches and the actual proper-tail call.
/// This graph is intermediate: provider confinement and evaluation soundness
/// are required before any lookup fact can be issued.
fn reconstruct_lookup_graph<'a>(
    program: &'a dyn LedgerArena,
    linked: &ValidatedInterfaceProgram,
    candidate: DefinitionCandidate,
    c: LookupConstructors,
    dependencies: RemovalDependencies,
    work: &mut TypeWorkBudget,
) -> Result<LookupGraph<'a>, Rejection> {
    check_lookup_nominals(program, c, work)?;
    let initializer = linked_initializer(program, linked, candidate, work)?;
    let comparison_id = linked_initializer(program, linked, dependencies.comparison, work)?;
    let projection_id = linked_initializer(program, linked, dependencies.projection, work)?;
    reject_evidence(program, &[initializer, comparison_id, projection_id], work)?;
    let mut inspect = CoreInspection { program, work };
    let definition = inspect.stored_function_witness(
        initializer,
        &[
            candidate.binder,
            dependencies.comparison.binder,
            dependencies.projection.binder,
        ],
    )?;
    let provider_api = definition.api;
    let comparison = inspect.stored_function_witness(comparison_id, &[])?;
    let projection = inspect.stored_function_witness(projection_id, &[])?;
    check_id_comparison(&mut inspect, comparison_id, c.root, c.work)?;
    check_projection(&mut inspect, projection_id, c.child)?;

    let argument_match = definition.body;
    let arguments = inspect.branch(argument_match)?;
    if inspect.variable(arguments.scrutinee())? != definition.parameter {
        return Err(Rejection::Unsupported);
    }
    let [argument_arm] = arguments.arms() else {
        return Err(Rejection::Unsupported);
    };
    let (wanted, list) = pattern_pair(argument_arm.pattern())?;
    let wanted = binder_pattern(wanted)?;
    let list = binder_pattern(list)?;
    let list_match = argument_arm.body();
    let cases = inspect.branch(list_match)?;
    if inspect.variable(cases.scrutinee())? != list {
        return Err(Rejection::Unsupported);
    }
    let [empty_arm, more_arm] = cases.arms() else {
        return Err(Rejection::Unsupported);
    };
    if constructor_pattern(empty_arm.pattern(), c.empty)?.is_some() {
        return Err(Rejection::Unsupported);
    }
    let payload = constructor_pattern(more_arm.pattern(), c.more)?.ok_or(Rejection::Unsupported)?;
    let (entry, tail) = pattern_pair(payload)?;
    let entry = binder_pattern(entry)?;
    let tail = binder_pattern(tail)?;
    let absent = nullary_constructor(&mut inspect, empty_arm.body(), c.absent, provider_api)?;
    let comparison_match = more_arm.body();
    let compared = inspect.branch(comparison_match)?;
    let comparison_call = compared.scrutinee();
    let call = inspect.application(comparison_call)?;
    if inspect.variable(call.function())? != dependencies.comparison.binder {
        return Err(Rejection::Unsupported);
    }
    let comparison_pair = inspect.persistent_tuple(call.argument(), None)?;
    let [projection_call, actual_wanted] = comparison_pair.fields else {
        return Err(Rejection::Unsupported);
    };
    if inspect.variable(*actual_wanted)? != wanted {
        return Err(Rejection::Unsupported);
    }
    let key = inspect.application(*projection_call)?;
    if inspect.variable(key.function())? != dependencies.projection.binder
        || inspect.variable(key.argument())? != entry
    {
        return Err(Rejection::Unsupported);
    }
    let [hit, miss] = compared.arms() else {
        return Err(Rejection::Unsupported);
    };
    if !matches!(hit.pattern().kind, super::CorePatternKind::Boolean(true))
        || !matches!(miss.pattern().kind, super::CorePatternKind::Boolean(false))
    {
        return Err(Rejection::Unsupported);
    }
    let present_call = hit.body();
    let present_application = inspect.application(present_call)?;
    if inspect.variable(present_application.argument())? != entry {
        return Err(Rejection::Unsupported);
    }
    let present_constructor =
        inspect.stored_function_witness(present_application.function(), &[])?;
    let present_value = inspect.persistent_tuple(present_constructor.body, Some(c.present))?;
    let [present_payload] = present_value.fields else {
        return Err(Rejection::Unsupported);
    };
    if inspect.variable(*present_payload)? != present_constructor.parameter {
        return Err(Rejection::Unsupported);
    }
    let recursive_call = miss.body();
    let recursive = inspect.application(recursive_call)?;
    if inspect.variable(recursive.function())? != candidate.binder {
        return Err(Rejection::Unsupported);
    }
    let recursive_pair = inspect.persistent_tuple(recursive.argument(), None)?;
    let [recursive_wanted, recursive_tail] = recursive_pair.fields else {
        return Err(Rejection::Unsupported);
    };
    if inspect.variable(*recursive_wanted)? != wanted || inspect.variable(*recursive_tail)? != tail
    {
        return Err(Rejection::Unsupported);
    }
    let comparator_arguments = inspect.branch(comparison.body)?;
    let [comparator_arm] = comparator_arguments.arms() else {
        return Err(Rejection::Unsupported);
    };
    let (comparator_left, comparator_right) = pattern_pair(comparator_arm.pattern())?;
    let comparator_left = binder_pattern(comparator_left)?;
    let comparator_right = binder_pattern(comparator_right)?;
    let comparator_cases = inspect.branch(comparator_arm.body())?;
    let comparator_pair = inspect.persistent_tuple(comparator_cases.scrutinee(), None)?;
    let [_, work_arm, _] = comparator_cases.arms() else {
        return Err(Rejection::Unsupported);
    };
    let (left_work, right_work) = pattern_pair(work_arm.pattern())?;
    let left_work = constructor_pattern(left_work, c.work)?.ok_or(Rejection::Unsupported)?;
    let right_work = constructor_pattern(right_work, c.work)?.ok_or(Rejection::Unsupported)?;
    let (left_allocator, left_serial) = pattern_pair(left_work)?;
    let (right_allocator, right_serial) = pattern_pair(right_work)?;
    let work_fields = [
        binder_pattern(left_allocator)?,
        binder_pattern(left_serial)?,
        binder_pattern(right_allocator)?,
        binder_pattern(right_serial)?,
    ];
    let projection_branch = inspect.branch(projection.body)?;
    let [projection_arm] = projection_branch.arms() else {
        return Err(Rejection::Unsupported);
    };
    let projection_payload =
        constructor_pattern(projection_arm.pattern(), c.child)?.ok_or(Rejection::Unsupported)?;
    let (projection_key, projection_destination) = pattern_pair(projection_payload)?;
    let projection_fields = [
        binder_pattern(projection_key)?,
        binder_pattern(projection_destination)?,
    ];
    let apis = [
        definition.api,
        comparison.api,
        projection.api,
        present_constructor.api,
        absent.api,
        comparison_pair.api,
        comparator_pair.api,
        recursive_pair.api,
        present_value.api,
    ];
    inspect
        .work
        .charge(apis.len())
        .map_err(|()| Rejection::Exhausted)?;
    if apis.iter().any(|api| *api != provider_api) {
        return Err(Rejection::Unsupported);
    }
    require_distinct(
        inspect.work,
        &[
            definition.parameter,
            wanted,
            list,
            entry,
            tail,
            candidate.binder,
            dependencies.comparison.binder,
            dependencies.projection.binder,
        ],
    )?;
    require_distinct(inspect.work, &[comparator_left, comparator_right])?;
    require_distinct(inspect.work, &work_fields)?;
    require_distinct(inspect.work, &projection_fields)?;
    let freshness = [
        (
            dependencies.projection.binder,
            comparison_pair.context_binder,
        ),
        (entry, comparison_pair.context_binder),
        (wanted, comparison_pair.context_binder),
        (wanted, recursive_pair.context_binder),
        (tail, recursive_pair.context_binder),
        (present_constructor.parameter, present_value.context_binder),
        (comparator_left, comparator_pair.context_binder),
        (comparator_right, comparator_pair.context_binder),
    ];
    inspect
        .work
        .charge(freshness.len())
        .map_err(|()| Rejection::Exhausted)?;
    if freshness.iter().any(|(binder, context)| binder == context) {
        return Err(Rejection::Unsupported);
    }
    Ok(LookupGraph {
        arena: program,
        candidate,
        constructors: c,
        dependencies,
        definition,
        comparison,
        projection,
        present_constructor,
        provider_api,
        argument_match,
        list_match,
        comparison_match,
        comparison_call,
        projection_call: *projection_call,
        recursive_call,
        present_call,
        wanted,
        list,
        entry,
        tail,
        absent,
        comparison_pair,
        comparator_pair,
        recursive_pair,
        present_value,
    })
}

/// Untrusted constructor coordinates for the finite ordered insertion schema.
#[derive(Clone, Copy)]
struct InsertConstructors {
    entry: crate::types::ConstructorId,
    empty: crate::types::ConstructorId,
    more: crate::types::ConstructorId,
}

struct InsertGraph<'a> {
    arena: &'a dyn LedgerArena,
    candidate: DefinitionCandidate,
    constructors: InsertConstructors,
    definition: CheckedStoredFunction<'a>,
    provider_api: crate::module::ModuleId,
    argument_match: NodeId,
    argument_scrutinee: NodeId,
    list_match: NodeId,
    list_scrutinee: NodeId,
    recursive_call: NodeId,
    recursive_function: NodeId,
    new_entry: BinderId,
    list: BinderId,
    entry: BinderId,
    tail: BinderId,
    empty: CheckedPersistentTuple<'a>,
    singleton: ConstructorApplication<'a>,
    prepend: ConstructorApplication<'a>,
    recursive_pair: CheckedPersistentTuple<'a>,
}

/// Reconstruct the actual append-by-recursion implementation. The witness is
/// private and has no fact authority without control and evaluation checks.
fn reconstruct_insert_graph<'a>(
    program: &'a dyn LedgerArena,
    linked: &ValidatedInterfaceProgram,
    candidate: DefinitionCandidate,
    c: InsertConstructors,
    work: &mut TypeWorkBudget,
) -> Result<InsertGraph<'a>, Rejection> {
    reconstruct_insert_spine(program, linked, candidate, c, true, work)
}

/// Reconstruct append over a finite list whose entries are a data nominal.
/// This covers multi-constructor envelopes without treating any variant name
/// or payload as an authority for freshness or a registration fact.
fn reconstruct_insert_spine<'a>(
    program: &'a dyn LedgerArena,
    linked: &ValidatedInterfaceProgram,
    candidate: DefinitionCandidate,
    c: InsertConstructors,
    require_singleton: bool,
    work: &mut TypeWorkBudget,
) -> Result<InsertGraph<'a>, Rejection> {
    use crate::types::Type;
    exact_nominal_pair(program, c.empty, c.more, work)?;
    if require_singleton {
        singleton_payload(program, c.entry, work)?;
    } else {
        work.charge(2).map_err(|()| Rejection::Exhausted)?;
        let registry = program.registry();
        registry
            .constructor(c.entry)
            .ok_or(Rejection::Unsupported)?;
        let nominal = registry
            .nominal(c.entry.owner())
            .ok_or(Rejection::Unsupported)?;
        work.charge(nominal.constructors.len())
            .map_err(|()| Rejection::Exhausted)?;
        if nominal.declaration_kind != crate::resolved::ResolvedNominalDeclarationKind::Data
            || !nominal.constructors.contains(&c.entry)
        {
            return Err(Rejection::Unsupported);
        }
    }
    work.charge(2).map_err(|()| Rejection::Exhausted)?;
    let registry = program.registry();
    if registry
        .constructor(c.empty)
        .ok_or(Rejection::Unsupported)?
        .payload
        .is_some()
    {
        return Err(Rejection::Unsupported);
    }
    if !matches!(&registry.constructor(c.more).ok_or(Rejection::Unsupported)?.payload,
        Some(Type::Tuple(fields)) if matches!(fields.as_ref(), [Type::Nominal(entry), Type::Nominal(list)]
            if *entry == c.entry.owner() && *list == c.empty.owner()))
    {
        return Err(Rejection::Unsupported);
    }
    let initializer = linked_initializer(program, linked, candidate, work)?;
    reject_evidence(program, &[initializer], work)?;
    let mut inspect = CoreInspection { program, work };
    let definition = inspect.stored_function_witness(initializer, &[candidate.binder])?;
    // The definition binds one authenticated Region API. Selection of a
    // particular provider is a premise checked at each consuming call.
    let provider_api = definition.api;
    let argument_match = definition.body;
    let arguments = inspect.branch(argument_match)?;
    if inspect.variable(arguments.scrutinee())? != definition.parameter {
        return Err(Rejection::Unsupported);
    }
    let [argument_arm] = arguments.arms() else {
        return Err(Rejection::Unsupported);
    };
    let (new_entry, list) = pattern_pair(argument_arm.pattern())?;
    let new_entry = binder_pattern(new_entry)?;
    let list = binder_pattern(list)?;
    let list_match = argument_arm.body();
    let branches = inspect.branch(list_match)?;
    if inspect.variable(branches.scrutinee())? != list {
        return Err(Rejection::Unsupported);
    }
    let [empty_arm, more_arm] = branches.arms() else {
        return Err(Rejection::Unsupported);
    };
    if constructor_pattern(empty_arm.pattern(), c.empty)?.is_some() {
        return Err(Rejection::Unsupported);
    }
    let payload = constructor_pattern(more_arm.pattern(), c.more)?.ok_or(Rejection::Unsupported)?;
    let (entry, tail) = pattern_pair(payload)?;
    let entry = binder_pattern(entry)?;
    let tail = binder_pattern(tail)?;
    let singleton =
        constructor_application(&mut inspect, empty_arm.body(), c.more, 2, provider_api)?;
    let [singleton_entry, singleton_tail] = singleton.arguments.fields else {
        return Err(Rejection::Unsupported);
    };
    if inspect.variable(*singleton_entry)? != new_entry {
        return Err(Rejection::Unsupported);
    }
    let empty = nullary_constructor(&mut inspect, *singleton_tail, c.empty, provider_api)?;
    let prepend = constructor_application(&mut inspect, more_arm.body(), c.more, 2, provider_api)?;
    let [original_entry, recursive_call] = prepend.arguments.fields else {
        return Err(Rejection::Unsupported);
    };
    if inspect.variable(*original_entry)? != entry {
        return Err(Rejection::Unsupported);
    }
    let recursive = inspect.application(*recursive_call)?;
    if inspect.variable(recursive.function())? != candidate.binder {
        return Err(Rejection::Unsupported);
    }
    let recursive_pair = inspect.persistent_tuple(recursive.argument(), None)?;
    let [recursive_entry, recursive_tail] = recursive_pair.fields else {
        return Err(Rejection::Unsupported);
    };
    if inspect.variable(*recursive_entry)? != new_entry
        || inspect.variable(*recursive_tail)? != tail
        || recursive_pair.api != provider_api
    {
        return Err(Rejection::Unsupported);
    }
    require_distinct(
        inspect.work,
        &[
            definition.parameter,
            new_entry,
            list,
            entry,
            tail,
            candidate.binder,
        ],
    )?;
    let freshness = [
        (new_entry, singleton.arguments.context_binder),
        (entry, prepend.arguments.context_binder),
        (candidate.binder, prepend.arguments.context_binder),
        (new_entry, prepend.arguments.context_binder),
        (tail, prepend.arguments.context_binder),
        (new_entry, recursive_pair.context_binder),
        (tail, recursive_pair.context_binder),
    ];
    inspect
        .work
        .charge(freshness.len())
        .map_err(|()| Rejection::Exhausted)?;
    if freshness.iter().any(|(binder, context)| binder == context) {
        return Err(Rejection::Unsupported);
    }
    Ok(InsertGraph {
        arena: program,
        candidate,
        constructors: c,
        definition,
        provider_api,
        argument_match,
        argument_scrutinee: arguments.scrutinee(),
        list_match,
        list_scrutinee: branches.scrutinee(),
        recursive_call: *recursive_call,
        recursive_function: recursive.function(),
        new_entry,
        list,
        entry,
        tail,
        empty,
        singleton,
        prepend,
        recursive_pair,
    })
}

/// The finite CoreEval vocabulary needed by this exact insertion schema.
/// Identities remain the actual arena, binder and nominal identities until an
/// injective finite encoding is selected by the proof correspondence.
#[derive(Clone, Copy)]
enum InsertModelNode<'a> {
    Unit,
    Variable(BinderId),
    Bind {
        binder: BinderId,
        initializer: NodeId,
        body: NodeId,
    },
    Apply {
        function: NodeId,
        argument: NodeId,
    },
    ArgumentMatch {
        scrutinee: NodeId,
        first: BinderId,
        second: BinderId,
        body: NodeId,
    },
    ListMatch {
        scrutinee: NodeId,
        empty: crate::types::ConstructorId,
        more: crate::types::ConstructorId,
        entry: BinderId,
        tail: BinderId,
        empty_body: NodeId,
        more_body: NodeId,
    },
    Query {
        operand: NodeId,
    },
    Request {
        fields: usize,
    },
    Allocate {
        context: NodeId,
        request: NodeId,
    },
    Tuple {
        constructor: Option<crate::types::ConstructorId>,
        context: NodeId,
        fields: &'a [NodeId],
        storage: NodeId,
    },
    Closure {
        context: NodeId,
        captures: &'a [NodeId],
        storage: NodeId,
        parameter: BinderId,
        body: NodeId,
    },
}

struct InsertModelView<'a> {
    arena: &'a dyn LedgerArena,
    nodes: Vec<(NodeId, InsertModelNode<'a>)>,
    binders: Vec<BinderId>,
    constructors: Vec<crate::types::ConstructorId>,
}

/// Register an actual identity exactly once; index position is its model Nat.
fn intern_insert_identity<T: Copy + Eq>(
    values: &mut Vec<T>,
    value: T,
    work: &mut TypeWorkBudget,
) -> Result<(), Rejection> {
    work.charge(values.len())
        .map_err(|()| Rejection::Exhausted)?;
    if !values.contains(&value) {
        work.charge(1).map_err(|()| Rejection::Exhausted)?;
        values.try_reserve(1).map_err(|_| Rejection::Exhausted)?;
        values.push(value);
    }
    Ok(())
}

/// Project all nodes reachable from this checked linked insertion body. The
/// only accepted match forms are its already-checked argument and list matches.
/// Nothing here selects an allocation provider or issues a semantic fact.
fn insert_model_view<'a>(
    graph: &InsertGraph<'a>,
    semantics: RemovalConstructors,
    work: &mut TypeWorkBudget,
) -> Result<InsertModelView<'a>, Rejection> {
    use std::collections::HashSet;
    let program = graph.arena;
    if semantics.empty != graph.constructors.empty
        || semantics.more != graph.constructors.more
        || semantics.entry != graph.constructors.entry
    {
        return Err(Rejection::Unsupported);
    }
    check_removal_nominals(program, semantics, work)?;
    let mut inspect = CoreInspection { program, work };
    let mut nodes = Vec::new();
    let mut binders = Vec::new();
    let mut constructors = Vec::new();
    let mut pending = Vec::new();
    let mut visited = HashSet::new();
    for constructor in [
        semantics.root_id,
        semantics.work_id,
        semantics.entry,
        semantics.empty,
        semantics.more,
        semantics.found,
        semantics.missing,
    ] {
        intern_insert_identity(&mut constructors, constructor, inspect.work)?;
    }
    inspect.work.charge(1).map_err(|()| Rejection::Exhausted)?;
    pending.try_reserve(1).map_err(|_| Rejection::Exhausted)?;
    pending.push(graph.candidate.initializer);
    while let Some(id) = pending.pop() {
        inspect.work.charge(1).map_err(|()| Rejection::Exhausted)?;
        if visited.contains(&id) {
            continue;
        }
        inspect.work.charge(1).map_err(|()| Rejection::Exhausted)?;
        visited.try_reserve(1).map_err(|_| Rejection::Exhausted)?;
        visited.insert(id);
        let kind = inspect.kind(id)?;
        let node = match kind {
            EffectExprKind::Pure(PureExprKind::Value(super::PureValue::Unit(_))) => {
                InsertModelNode::Unit
            }
            EffectExprKind::Pure(PureExprKind::Variable(variable)) => {
                let binder = variable.binder();
                intern_insert_identity(&mut binders, binder, inspect.work)?;
                InsertModelNode::Variable(binder)
            }
            EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Bind(binding))) => {
                let binder = binding.binder().id();
                intern_insert_identity(&mut binders, binder, inspect.work)?;
                InsertModelNode::Bind {
                    binder,
                    initializer: binding.initializer(),
                    body: binding.body(),
                }
            }
            EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Apply(app))) => {
                InsertModelNode::Apply {
                    function: app.function(),
                    argument: app.argument(),
                }
            }
            EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Match(branch))) => {
                if id == graph.argument_match {
                    let [arm] = branch.arms() else {
                        return Err(Rejection::Unsupported);
                    };
                    let (first, second) = pattern_pair(arm.pattern())?;
                    let first = binder_pattern(first)?;
                    let second = binder_pattern(second)?;
                    intern_insert_identity(&mut binders, first, inspect.work)?;
                    intern_insert_identity(&mut binders, second, inspect.work)?;
                    InsertModelNode::ArgumentMatch {
                        scrutinee: branch.scrutinee(),
                        first,
                        second,
                        body: arm.body(),
                    }
                } else if id == graph.list_match {
                    let [empty_arm, more_arm] = branch.arms() else {
                        return Err(Rejection::Unsupported);
                    };
                    let empty = graph.constructors.empty;
                    let more = graph.constructors.more;
                    if constructor_pattern(empty_arm.pattern(), empty)?.is_some() {
                        return Err(Rejection::Unsupported);
                    }
                    let payload = constructor_pattern(more_arm.pattern(), more)?
                        .ok_or(Rejection::Unsupported)?;
                    let (entry, tail) = pattern_pair(payload)?;
                    let entry = binder_pattern(entry)?;
                    let tail = binder_pattern(tail)?;
                    intern_insert_identity(&mut binders, entry, inspect.work)?;
                    intern_insert_identity(&mut binders, tail, inspect.work)?;
                    intern_insert_identity(&mut constructors, empty, inspect.work)?;
                    intern_insert_identity(&mut constructors, more, inspect.work)?;
                    InsertModelNode::ListMatch {
                        scrutinee: branch.scrutinee(),
                        empty,
                        more,
                        entry,
                        tail,
                        empty_body: empty_arm.body(),
                        more_body: more_arm.body(),
                    }
                } else {
                    return Err(Rejection::Unsupported);
                }
            }
            EffectExprKind::Operation(EffectOperation::Request(request)) => {
                let api = crate::resolved::RegionApi::for_module(graph.provider_api)
                    .ok_or(Rejection::Unsupported)?;
                if request.effect().effect() != api.default_alloc()
                    || !request.effect().arguments().is_empty()
                    || request.operation() != crate::types::OperationId::new(api.default_alloc(), 1)
                {
                    return Err(Rejection::Unsupported);
                }
                InsertModelNode::Query {
                    operand: request.operand(),
                }
            }
            EffectExprKind::Operation(EffectOperation::RegionValueRequest(request))
                if request.api == graph.provider_api =>
            {
                InsertModelNode::Request {
                    fields: request.fields,
                }
            }
            EffectExprKind::Operation(EffectOperation::RegionAllocate(allocation))
                if allocation.api == graph.provider_api =>
            {
                InsertModelNode::Allocate {
                    context: allocation.context,
                    request: allocation.request,
                }
            }
            EffectExprKind::Operation(EffectOperation::RegionTuple(tuple))
                if tuple.api == graph.provider_api =>
            {
                if let Some(constructor) = tuple.constructor {
                    intern_insert_identity(&mut constructors, constructor, inspect.work)?;
                }
                InsertModelNode::Tuple {
                    constructor: tuple.constructor,
                    context: tuple.context,
                    fields: &tuple.fields,
                    storage: tuple.storage,
                }
            }
            EffectExprKind::Operation(EffectOperation::RegionClosure(closure))
                if closure.api == graph.provider_api =>
            {
                let function = closure.code.function().ok_or(Rejection::Unsupported)?;
                let parameter = function.parameter().id();
                intern_insert_identity(&mut binders, parameter, inspect.work)?;
                InsertModelNode::Closure {
                    context: closure.context,
                    captures: &closure.captures,
                    storage: closure.storage,
                    parameter,
                    body: function.body(),
                }
            }
            _ => return Err(Rejection::Unsupported),
        };
        let count = kind.child_count();
        inspect
            .work
            .charge(count)
            .map_err(|()| Rejection::Exhausted)?;
        pending
            .try_reserve(count)
            .map_err(|_| Rejection::Exhausted)?;
        for index in 0..count {
            pending.push(kind.child_at(index).ok_or(Rejection::Unsupported)?);
        }
        inspect.work.charge(1).map_err(|()| Rejection::Exhausted)?;
        nodes.try_reserve(1).map_err(|_| Rejection::Exhausted)?;
        nodes.push((id, node));
    }
    Ok(InsertModelView {
        arena: program,
        nodes,
        binders,
        constructors,
    })
}

/// A definition-bound whole-entry removal law. Consumers establish finite
/// input, exact captures and faithfully selected default allocation;
/// this summary carries no current-state or network-release authority.
struct ConditionalRemoval<'a> {
    linked: &'a ValidatedInterfaceProgram,
    graph: RemovalGraph<'a>,
}

/// All linked-body, helper and nominal checks share the caller's budget.
fn check_conditional_removal<'a>(
    program: &'a dyn LedgerArena,
    linked: &'a ValidatedInterfaceProgram,
    candidate: DefinitionCandidate,
    constructors: RemovalConstructors,
    dependencies: RemovalDependencies,
    work: &mut TypeWorkBudget,
) -> Result<ConditionalRemoval<'a>, Rejection> {
    let graph = reconstruct_removal_graph(
        program,
        linked,
        candidate,
        constructors,
        dependencies,
        false,
        work,
    )?;
    Ok(ConditionalRemoval { linked, graph })
}

/// Record removal is a separate conditional witness. It does not feed the
/// child-only removal model decoder or establish caller/provider premises.
struct ConditionalRecordRemoval<'a> {
    linked: &'a ValidatedInterfaceProgram,
    graph: RemovalGraph<'a>,
}

fn check_conditional_record_removal<'a>(
    program: &'a dyn LedgerArena,
    linked: &'a ValidatedInterfaceProgram,
    candidate: DefinitionCandidate,
    constructors: RemovalConstructors,
    dependencies: RemovalDependencies,
    work: &mut TypeWorkBudget,
) -> Result<ConditionalRecordRemoval<'a>, Rejection> {
    let graph = reconstruct_removal_graph(
        program,
        linked,
        candidate,
        constructors,
        dependencies,
        true,
        work,
    )?;
    Ok(ConditionalRecordRemoval { linked, graph })
}

/// A definition-bound first-match lookup law. Consumers establish finite
/// input, exact captures and faithfully selected default allocation; the
/// summary carries no current-state or network-release authority.
struct ConditionalLookup<'a> {
    linked: &'a ValidatedInterfaceProgram,
    graph: LookupGraph<'a>,
}

fn check_conditional_lookup<'a>(
    program: &'a dyn LedgerArena,
    linked: &'a ValidatedInterfaceProgram,
    candidate: DefinitionCandidate,
    constructors: LookupConstructors,
    dependencies: RemovalDependencies,
    work: &mut TypeWorkBudget,
) -> Result<ConditionalLookup<'a>, Rejection> {
    let graph =
        reconstruct_lookup_graph(program, linked, candidate, constructors, dependencies, work)?;
    Ok(ConditionalLookup { linked, graph })
}

/// A definition-bound insertion law, conditional on a represented finite
/// input, its actual closure and capture bindings, and faithful selection of
/// the canonical default provider. It grants no current-state, freshness,
/// uniqueness or network-release claim.
struct ConditionalInsertion<'a> {
    linked: &'a ValidatedInterfaceProgram,
    graph: InsertGraph<'a>,
    model: InsertModelView<'a>,
    semantics: RemovalConstructors,
}

/// A definition-bound append law for finite lists of located data values.
/// The caller establishes represented input and default-provider premises.
/// This does not establish a key, freshness, currentness or network fact.
struct ConditionalSpineInsertion<'a> {
    linked: &'a ValidatedInterfaceProgram,
    graph: InsertGraph<'a>,
}

fn check_conditional_spine_insertion<'a>(
    program: &'a dyn LedgerArena,
    linked: &'a ValidatedInterfaceProgram,
    candidate: DefinitionCandidate,
    constructors: InsertConstructors,
    work: &mut TypeWorkBudget,
) -> Result<ConditionalSpineInsertion<'a>, Rejection> {
    let graph = reconstruct_insert_spine(program, linked, candidate, constructors, false, work)?;
    Ok(ConditionalSpineInsertion { linked, graph })
}

/// Reconstruct the actual linked body and its complete insertion-only model
/// projection under one cumulative budget. A refusal publishes no summary.
fn check_conditional_insertion<'a>(
    program: &'a dyn LedgerArena,
    linked: &'a ValidatedInterfaceProgram,
    candidate: DefinitionCandidate,
    constructors: InsertConstructors,
    semantics: RemovalConstructors,
    work: &mut TypeWorkBudget,
) -> Result<ConditionalInsertion<'a>, Rejection> {
    let graph = reconstruct_insert_graph(program, linked, candidate, constructors, work)?;
    let model = insert_model_view(&graph, semantics, work)?;
    Ok(ConditionalInsertion {
        linked,
        graph,
        model,
        semantics,
    })
}

#[cfg(test)]
mod tests {
    use std::sync::atomic::{AtomicUsize, Ordering};

    use crate::{
        core::ValidatedEffectProgram,
        elaborate::{EffectElaborator, check_module, link_modules},
        evidence_validation::{ValidatedInterfaceProgram, validate_interface_evidence},
        module::{ModuleRoots, load_module_graph},
        resolve::{DependencyExports, resolve_module},
        resolved::CheckedModule,
        types::TypeWorkBudget,
    };

    // Private, ordinary source values. The names are fixture conveniences;
    // they must not authorize a checker fact.
    const ORDINARY_LEDGER: &str = r#"
type Identity =
    Root
    | Work(Int, Int)
type Child = Child(Identity, Int)
type Children =
    Empty
    | More(Child, Children)
type Parent =
    NoParent
    | Parent(Int, Identity)
type Phase =
    Open
    | Closed
type Record = Record(Identity, Parent, Phase, Children)
type Records =
    NoRecords
    | RecordCons(Record, Records)
type Envelope =
    WorkOut(Identity, Parent, Int, Bytes)
    | AckOut(Parent, Identity)
type Outputs =
    NoOutputs
    | OutputCons(Envelope, Outputs)
type Ledger = Ledger(Int, Records, Outputs)
type Removal =
    Found
    | Missing

same_id : (Identity, Identity) -> Bool
same_id (left, right) = match (left, right) {
    (Root, Root) => true
    (Work(a, b), Work(c, d)) => match a == c {
        true => b == d
        false => false
    }
    _ => false
}

child_id : Child -> Identity
child_id entry = match entry {
    Child(actual, destination) => actual
}

remove_child : (Identity, Children) -> (Children, Removal)
remove_child (wanted, children) = match children {
    Empty => (Empty, Missing)
    More(entry, tail) => match same_id (child_id entry, wanted) {
        true => (tail, Found)
        false => match remove_child (wanted, tail) {
            (remaining, status) => (More(entry, remaining), status)
        }
    }
}

initial : Unit -> Ledger
initial () = Ledger(0, RecordCons(Record(Root, NoParent, Open, Empty), NoRecords), NoOutputs)

main : Unit -> Unit
main () = {
    let ignored = remove_child (Root, Empty)
    ()
}
"#;

    struct FixtureDirectory(std::path::PathBuf);

    impl FixtureDirectory {
        fn create() -> Self {
            static NEXT: AtomicUsize = AtomicUsize::new(0);
            loop {
                let candidate = std::env::temp_dir().join(format!(
                    "ash-ledger-checker-{}-{}",
                    std::process::id(),
                    NEXT.fetch_add(1, Ordering::Relaxed)
                ));
                match std::fs::create_dir(&candidate) {
                    Ok(()) => return Self(candidate),
                    Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
                    Err(error) => panic!("create fixture directory: {error}"),
                }
            }
        }
    }

    impl Drop for FixtureDirectory {
        fn drop(&mut self) {
            let _ = std::fs::remove_dir_all(&self.0);
        }
    }

    fn ordinary_ledger(source: &str) -> (ValidatedEffectProgram, ValidatedInterfaceProgram) {
        ordinary_ledger_with_precheck(source, |_, _| {})
    }

    fn ordinary_ledger_with_precheck(
        source: &str,
        precheck: impl FnOnce(&crate::core::UnvalidatedEffectProgram, &ValidatedInterfaceProgram),
    ) -> (ValidatedEffectProgram, ValidatedInterfaceProgram) {
        let (program, linked, _) = ordinary_ledger_with_provenance(source, precheck);
        (program, linked)
    }

    fn ordinary_ledger_with_provenance(
        source: &str,
        precheck: impl FnOnce(&crate::core::UnvalidatedEffectProgram, &ValidatedInterfaceProgram),
    ) -> (
        ValidatedEffectProgram,
        ValidatedInterfaceProgram,
        Vec<(crate::module::ModuleId, crate::source::SourceFile)>,
    ) {
        let directory = FixtureDirectory::create();
        let path = directory.0.join("entry.ash");
        std::fs::write(&path, source).expect("write fixture source");
        let graph = load_module_graph(&path, &ModuleRoots::empty()).expect("load fixture modules");
        let mut checked: Vec<CheckedModule> = Vec::new();
        for module in graph.modules() {
            let dependencies = module
                .dependencies()
                .iter()
                .map(|edge| {
                    let dependency = checked
                        .iter()
                        .find(|candidate| candidate.module() == edge.target())
                        .expect("dependency checked first");
                    DependencyExports::new(edge, dependency.exports()).expect("dependency exports")
                })
                .collect::<Vec<_>>();
            let resolved = resolve_module(module, &dependencies).expect("resolve fixture module");
            checked.push(check_module(resolved).expect("check fixture module"));
        }
        let linked = validate_interface_evidence(
            link_modules(checked, graph.entry()).expect("link fixture modules"),
        )
        .expect("authenticate interface evidence");
        let mut elaborator = EffectElaborator::for_module_program(&linked).expect("elaborator");
        let root = elaborator
            .synthesize_effect_module_program(&linked)
            .expect("lower fixture to Effect Core");
        let program = elaborator.finish(root.node).expect("finish Effect Core");
        let sources = graph
            .modules()
            .iter()
            .map(|module| module.source())
            .collect::<Vec<_>>();
        let modules = graph
            .modules()
            .iter()
            .map(|module| (module.id(), module.source().id()))
            .collect::<Vec<_>>();
        precheck(&program, &linked);
        let validated = crate::core::validate::validate_effect_modules_linked_with_work(
            program,
            &sources,
            &modules,
            &linked,
            &mut TypeWorkBudget::default(),
        )
        .expect("independently validate linked Effect Core");
        let provenance = graph
            .modules()
            .iter()
            .map(|module| (module.id(), module.source().clone()))
            .collect();
        (validated, linked, provenance)
    }

    fn target_candidate(
        program: &ValidatedEffectProgram,
        linked: &ValidatedInterfaceProgram,
        name: &str,
    ) -> super::DefinitionCandidate {
        let binder = linked
            .groups()
            .iter()
            .flat_map(|group| group.definitions())
            .find_map(|definition| {
                let crate::resolved::ResolvedDefinitionKind::Equational(definition) =
                    definition.kind()
                else {
                    return None;
                };
                (definition.interface.name.spelling == name).then_some(definition.interface.name.id)
            })
            .expect("fixture target");
        let initializer = program
            .nodes()
            .iter()
            .find_map(|node| {
                let crate::core::EffectExprKind::Pure(crate::core::PureExprKind::Computation(
                    crate::core::PureComputation::RecursiveBind(group),
                )) = &node.kind
                else {
                    return None;
                };
                group
                    .members()
                    .iter()
                    .find(|member| member.binder().id() == binder)
                    .map(|member| member.initializer())
            })
            .expect("target initializer");
        super::DefinitionCandidate {
            binder,
            initializer,
        }
    }

    #[test]
    fn nominated_global_is_selected_from_the_actual_linked_spine() {
        let (program, linked) = ordinary_ledger(ORDINARY_LEDGER);
        let candidate = target_candidate(&program, &linked, "remove_child");
        let binder = candidate.binder;
        let initializer = candidate.initializer;
        let mut work = TypeWorkBudget::unbounded();
        assert_eq!(
            super::linked_initializer(&program, &linked, candidate, &mut work),
            Ok(initializer)
        );
        let used = work.used();
        let mut exact = TypeWorkBudget::with_limit(used);
        assert_eq!(
            super::linked_initializer(&program, &linked, candidate, &mut exact),
            Ok(initializer)
        );
        let mut short = TypeWorkBudget::with_limit(used - 1);
        assert_eq!(
            super::linked_initializer(&program, &linked, candidate, &mut short),
            Err(super::Rejection::Exhausted)
        );
        let wrong = super::DefinitionCandidate {
            binder,
            initializer: program.root(),
        };
        assert_eq!(
            super::linked_initializer(&program, &linked, wrong, &mut TypeWorkBudget::unbounded()),
            Err(super::Rejection::Unsupported)
        );
    }

    #[test]
    fn provisional_arena_reads_match_the_validated_linked_spine() {
        let mut provisional = None;
        let (program, linked) =
            ordinary_ledger_with_precheck(ORDINARY_LEDGER, |program, linked| {
                let binder = linked
                    .groups()
                    .iter()
                    .flat_map(|group| group.definitions())
                    .find_map(|definition| {
                        let crate::resolved::ResolvedDefinitionKind::Equational(definition) =
                            definition.kind()
                        else {
                            return None;
                        };
                        (definition.interface.name.spelling == "remove_child")
                            .then_some(definition.interface.name.id)
                    })
                    .expect("fixture target");
                let initializer = program
                    .nodes
                    .iter()
                    .find_map(|node| {
                        let crate::core::EffectExprKind::Pure(
                            crate::core::PureExprKind::Computation(
                                crate::core::PureComputation::RecursiveBind(group),
                            ),
                        ) = &node.kind
                        else {
                            return None;
                        };
                        group
                            .members()
                            .iter()
                            .find(|member| member.binder().id() == binder)
                            .map(|member| member.initializer())
                    })
                    .expect("linked initializer");
                let candidate = super::DefinitionCandidate {
                    binder,
                    initializer,
                };
                let mut work = TypeWorkBudget::unbounded();
                assert_eq!(
                    super::linked_initializer(program, linked, candidate, &mut work),
                    Ok(initializer)
                );
                provisional = Some((candidate, work.used()));
            });
        let (candidate, used) = provisional.expect("provisional linked result");
        let mut work = TypeWorkBudget::unbounded();
        assert_eq!(
            super::linked_initializer(&program, &linked, candidate, &mut work),
            Ok(candidate.initializer)
        );
        assert_eq!(work.used(), used);
        assert!(matches!(
            super::linked_initializer(
                &program,
                &linked,
                candidate,
                &mut TypeWorkBudget::with_limit(used - 1)
            ),
            Err(super::Rejection::Exhausted)
        ));
    }

    #[test]
    fn linked_initialization_reconstructs_root_worker_and_exact_budget() {
        fn inspect(source: &str, role: super::InitializationRole) -> Result<(), super::Rejection> {
            let (program, linked) = ordinary_ledger(source);
            let candidate = target_candidate(&program, &linked, "initial");
            let constructor = |name: &str| {
                program
                    .registry()
                    .constructors()
                    .iter()
                    .find(|item| item.spelling == name)
                    .expect("fixture constructor")
                    .id
            };
            let constructors = super::InitializationConstructors {
                ledger: constructor("Ledger"),
                record: constructor("Record"),
                root: constructor("Root"),
                work: constructor("Work"),
                no_parent: constructor("NoParent"),
                parent: constructor("Parent"),
                open: constructor("Open"),
                closed: constructor("Closed"),
                children_empty: constructor("Empty"),
                children_more: constructor("More"),
                records_empty: constructor("NoRecords"),
                records_more: constructor("RecordCons"),
                outputs_empty: constructor("NoOutputs"),
                outputs_more: constructor("OutputCons"),
            };
            let mut work = TypeWorkBudget::unbounded();
            let graph = match role {
                super::InitializationRole::Root => {
                    let summary = super::check_conditional_root_initialization(
                        &program,
                        &linked,
                        candidate,
                        constructors,
                        &mut work,
                    )?;
                    assert!(std::ptr::eq(summary.linked, &linked));
                    summary.graph
                }
                super::InitializationRole::Worker => {
                    let summary = super::check_conditional_worker_initialization(
                        &program,
                        &linked,
                        candidate,
                        constructors,
                        &mut work,
                    )?;
                    assert!(std::ptr::eq(summary.linked, &linked));
                    summary.graph
                }
            };
            fn assert_constructor_edge(
                program: &ValidatedEffectProgram,
                application: super::ConstructorApplication<'_>,
            ) {
                let node = program
                    .node(application.call)
                    .expect("constructor call node");
                let crate::core::EffectExprKind::Pure(crate::core::PureExprKind::Computation(
                    crate::core::PureComputation::Apply(actual),
                )) = &node.kind
                else {
                    panic!("constructor call is an application");
                };
                assert_eq!(actual.function(), application.closure.root);
                assert_eq!(actual.argument(), application.arguments.root);
                assert_eq!(application.closure.body, application.value.root);
                assert!(std::ptr::eq(application.closure.arena, program));
            }
            assert!(std::ptr::eq(graph.arena, &program));
            assert_eq!(graph.candidate.initializer, candidate.initializer);
            assert_eq!(graph.constructors.ledger, constructors.ledger);
            assert_eq!(graph.constructors.record, constructors.record);
            assert_constructor_edge(&program, graph.ledger);
            assert_eq!(graph.initializer.root, candidate.initializer);
            assert_eq!(graph.initializer.api, graph.provider_api);
            assert_eq!(graph.ledger.value.constructor, Some(constructors.ledger));
            assert_eq!(graph.ledger.arguments.fields[0], graph.zero);
            assert_eq!(
                graph.records_empty.constructor,
                Some(constructors.records_empty)
            );
            assert_eq!(
                graph.outputs_empty.constructor,
                Some(constructors.outputs_empty)
            );
            match graph.role {
                super::InitializationRole::Root => {
                    let records = graph.records_more.expect("root record list");
                    let record = graph.root_record.expect("root record");
                    assert_constructor_edge(&program, records);
                    assert_constructor_edge(&program, record);
                    assert_eq!(records.value.constructor, Some(constructors.records_more));
                    assert_eq!(record.value.constructor, Some(constructors.record));
                    assert_eq!(
                        graph.root.expect("root id").constructor,
                        Some(constructors.root)
                    );
                    assert_eq!(
                        graph.no_parent.expect("no parent").constructor,
                        Some(constructors.no_parent)
                    );
                    assert_eq!(
                        graph.open.expect("open phase").constructor,
                        Some(constructors.open)
                    );
                    assert_eq!(
                        graph.children_empty.expect("empty children").constructor,
                        Some(constructors.children_empty)
                    );
                }
                super::InitializationRole::Worker => {
                    assert!(
                        graph.records_more.is_none()
                            && graph.root_record.is_none()
                            && graph.root.is_none()
                            && graph.no_parent.is_none()
                            && graph.open.is_none()
                            && graph.children_empty.is_none()
                    );
                }
            }
            let used = work.used();
            let mut exact = TypeWorkBudget::with_limit(used);
            assert!(
                super::reconstruct_initialization_graph(
                    &program,
                    &linked,
                    candidate,
                    constructors,
                    role,
                    &mut exact,
                )
                .is_ok()
            );
            let mut short = TypeWorkBudget::with_limit(used - 1);
            assert!(matches!(
                super::reconstruct_initialization_graph(
                    &program,
                    &linked,
                    candidate,
                    constructors,
                    role,
                    &mut short,
                ),
                Err(super::Rejection::Exhausted)
            ));
            if matches!(role, super::InitializationRole::Worker) {
                let mut exact = TypeWorkBudget::with_limit(used);
                assert!(
                    super::check_conditional_worker_initialization(
                        &program,
                        &linked,
                        candidate,
                        constructors,
                        &mut exact,
                    )
                    .is_ok()
                );
                let mut short = TypeWorkBudget::with_limit(used - 1);
                assert!(matches!(
                    super::check_conditional_worker_initialization(
                        &program,
                        &linked,
                        candidate,
                        constructors,
                        &mut short,
                    ),
                    Err(super::Rejection::Exhausted)
                ));
            }
            if matches!(role, super::InitializationRole::Root) {
                let mut exact = TypeWorkBudget::with_limit(used);
                assert!(
                    super::check_conditional_root_initialization(
                        &program,
                        &linked,
                        candidate,
                        constructors,
                        &mut exact,
                    )
                    .is_ok()
                );
                let mut short = TypeWorkBudget::with_limit(used - 1);
                assert!(matches!(
                    super::check_conditional_root_initialization(
                        &program,
                        &linked,
                        candidate,
                        constructors,
                        &mut short,
                    ),
                    Err(super::Rejection::Exhausted)
                ));
            }
            let (other_program, other_linked) = ordinary_ledger(source);
            assert!(matches!(
                super::reconstruct_initialization_graph(
                    &other_program,
                    &other_linked,
                    candidate,
                    constructors,
                    role,
                    &mut TypeWorkBudget::unbounded(),
                ),
                Err(super::Rejection::Unsupported)
            ));
            if matches!(role, super::InitializationRole::Worker) {
                assert!(matches!(
                    super::check_conditional_worker_initialization(
                        &other_program,
                        &other_linked,
                        candidate,
                        constructors,
                        &mut TypeWorkBudget::unbounded(),
                    ),
                    Err(super::Rejection::Unsupported)
                ));
            }
            if matches!(role, super::InitializationRole::Root) {
                assert!(matches!(
                    super::check_conditional_root_initialization(
                        &other_program,
                        &other_linked,
                        candidate,
                        constructors,
                        &mut TypeWorkBudget::unbounded(),
                    ),
                    Err(super::Rejection::Unsupported)
                ));
            }
            let mut wrong_nominal = constructors;
            wrong_nominal.ledger = constructors.record;
            assert!(matches!(
                super::reconstruct_initialization_graph(
                    &program,
                    &linked,
                    candidate,
                    wrong_nominal,
                    role,
                    &mut TypeWorkBudget::unbounded(),
                ),
                Err(super::Rejection::Unsupported)
            ));
            if matches!(role, super::InitializationRole::Worker) {
                assert!(matches!(
                    super::check_conditional_worker_initialization(
                        &program,
                        &linked,
                        candidate,
                        wrong_nominal,
                        &mut TypeWorkBudget::unbounded(),
                    ),
                    Err(super::Rejection::Unsupported)
                ));
            }
            if matches!(role, super::InitializationRole::Root) {
                assert!(matches!(
                    super::check_conditional_root_initialization(
                        &program,
                        &linked,
                        candidate,
                        wrong_nominal,
                        &mut TypeWorkBudget::unbounded(),
                    ),
                    Err(super::Rejection::Unsupported)
                ));
            }
            Ok(())
        }
        use super::InitializationRole::{Root, Worker};
        assert_eq!(inspect(ORDINARY_LEDGER, Root), Ok(()));
        let worker = ORDINARY_LEDGER.replace(
            "Ledger(0, RecordCons(Record(Root, NoParent, Open, Empty), NoRecords), NoOutputs)",
            "Ledger(0, NoRecords, NoOutputs)",
        );
        assert_eq!(inspect(&worker, Worker), Ok(()));
        let nonzero = ORDINARY_LEDGER.replace("Ledger(0, RecordCons", "Ledger(1, RecordCons");
        assert_eq!(inspect(&nonzero, Root), Err(super::Rejection::Unsupported));
        let closed = ORDINARY_LEDGER.replace(
            "Record(Root, NoParent, Open, Empty)",
            "Record(Root, NoParent, Closed, Empty)",
        );
        assert_eq!(inspect(&closed, Root), Err(super::Rejection::Unsupported));
        let wrong_parent = ORDINARY_LEDGER.replace(
            "Record(Root, NoParent, Open, Empty)",
            "Record(Root, Parent(0, Root), Open, Empty)",
        );
        assert_eq!(
            inspect(&wrong_parent, Root),
            Err(super::Rejection::Unsupported)
        );
        let unexpected_output = ORDINARY_LEDGER.replace(
            "RecordCons(Record(Root, NoParent, Open, Empty), NoRecords), NoOutputs)",
            "RecordCons(Record(Root, NoParent, Open, Empty), NoRecords), OutputCons(AckOut(NoParent, Root), NoOutputs))",
        );
        assert_eq!(
            inspect(&unexpected_output, Root),
            Err(super::Rejection::Unsupported)
        );
        assert_eq!(inspect(&worker, Root), Err(super::Rejection::Unsupported));
        let worker_nonzero = worker.replace("Ledger(0, NoRecords", "Ledger(1, NoRecords");
        assert_eq!(
            inspect(&worker_nonzero, Worker),
            Err(super::Rejection::Unsupported)
        );
        assert_eq!(
            inspect(ORDINARY_LEDGER, Worker),
            Err(super::Rejection::Unsupported)
        );
    }

    #[test]
    fn linked_registration_counter_uses_the_returned_successor_field() {
        const REGISTER: &str = r#"
type RecordLookup =
    NoRecord
    | HasRecord(Record)
type Registration =
    Rejected
    | Registered(Identity)

record_id : Record -> Identity
record_id record = match record {
    Record(actual, parent, phase, children) => actual
}

find_record : (Identity, Records) -> RecordLookup
find_record (wanted, records) = match records {
    NoRecords => NoRecord
    RecordCons(record, tail) => match same_id (record_id record, wanted) {
        true => HasRecord(record)
        false => find_record (wanted, tail)
    }
}

update_record : (Identity, Record, Records) -> Records
update_record (wanted, replacement, records) = match records {
    NoRecords => NoRecords
    RecordCons(record, tail) => match same_id (record_id record, wanted) {
        true => RecordCons(replacement, tail)
        false => RecordCons(record, update_record (wanted, replacement, tail))
    }
}

append_child : (Child, Children) -> Children
append_child (added, children) = match children {
    Empty => More(added, Empty)
    More(child, tail) => More(child, append_child (added, tail))
}

append_output : (Envelope, Outputs) -> Outputs
append_output (added, outputs) = match outputs {
    NoOutputs => OutputCons(added, NoOutputs)
    OutputCons(output, tail) => OutputCons(output, append_output (added, tail))
}

commit_registration : (Int, Int, Identity, Int, Bytes, Records, Outputs, Parent, Children) -> (Ledger, Registration)
commit_registration (next, owner, wanted, destination, payload, records, outputs, parent, children) = {
    let child = Work(owner, next)
    let replacement = Record(wanted, parent, Open, append_child (Child(child, destination), children))
    let remaining = update_record (wanted, replacement, records)
    let outgoing = append_output (WorkOut(child, Parent(owner, wanted), destination, payload), outputs)
    (Ledger(next + 1, remaining, outgoing), Registered(child))
}

finish_registration : (Record, Ledger, Int, Int, Identity, Int, Bytes, Records, Outputs) -> (Ledger, Registration)
finish_registration (record, ledger, next, owner, wanted, destination, payload, records, outputs) = match record {
    Record(actual, parent, phase, children) => match phase {
        Closed => (ledger, Rejected)
        Open => commit_registration (next, owner, wanted, destination, payload, records, outputs, parent, children)
    }
}

reserve_job : (Ledger, Int, Identity, Int, Bytes) -> (Ledger, Registration)
reserve_job (ledger, owner, wanted, destination, payload) = match ledger {
    Ledger(next, records, outputs) => match find_record (wanted, records) {
        NoRecord => (ledger, Rejected)
        HasRecord(record) => finish_registration (record, ledger, next, owner, wanted, destination, payload, records, outputs)
    }
}
"#;
        fn inspect(extra: &str) -> Result<(), super::Rejection> {
            inspect_variant(extra, false)
        }
        fn inspect_variant(extra: &str, transform: bool) -> Result<(), super::Rejection> {
            let base = ORDINARY_LEDGER.replace(
                "let ignored = remove_child (Root, Empty)",
                "let ignored = match reserve_job (initial (), 0, Root, 0, B.empty ()) {\n        (successor, status) => successor\n    }",
            );
            let source = format!("import @builtin.bytes as B\n{base}\n{extra}");
            let (program, linked, provenance) = ordinary_ledger_with_provenance(&source, |_, _| {});
            let program = if transform {
                let old = target_candidate(&program, &linked, "commit_registration");
                let old_captures = [
                    target_candidate(&program, &linked, "append_child").binder,
                    target_candidate(&program, &linked, "update_record").binder,
                    target_candidate(&program, &linked, "append_output").binder,
                ];
                let ledger = program
                    .registry()
                    .constructors()
                    .iter()
                    .find(|item| item.spelling == "Ledger")
                    .expect("fixture ledger")
                    .id;
                let rebuilt = crate::core::transform::identity_effect_traversal(&program)
                    .expect("supported ledger Core transform");
                assert_ne!(old.initializer.arena(), rebuilt.root.arena());
                assert!(
                    matches!(
                        super::reconstruct_registration_counter(
                            &rebuilt,
                            &linked,
                            old,
                            &old_captures,
                            ledger,
                            &mut TypeWorkBudget::unbounded(),
                        ),
                        Err(super::Rejection::Unsupported)
                    ),
                    "old-arena nomination cannot authorize rebuilt Core"
                );
                let sources: Vec<_> = provenance.iter().map(|(_, source)| source).collect();
                let relations: Vec<_> = provenance
                    .iter()
                    .map(|(module, source)| (*module, source.id()))
                    .collect();
                crate::core::validate::validate_effect_modules_linked_with_work(
                    rebuilt,
                    &sources,
                    &relations,
                    &linked,
                    &mut TypeWorkBudget::unbounded(),
                )
                .expect("transformed ledger Core independently validates")
            } else {
                program
            };
            let candidate = target_candidate(&program, &linked, "commit_registration");
            let captures = [
                target_candidate(&program, &linked, "append_child").binder,
                target_candidate(&program, &linked, "update_record").binder,
                target_candidate(&program, &linked, "append_output").binder,
            ];
            let ledger = program
                .registry()
                .constructors()
                .iter()
                .find(|item| item.spelling == "Ledger")
                .expect("fixture ledger constructor")
                .id;
            let mut work = TypeWorkBudget::unbounded();
            let graph = super::reconstruct_registration_counter(
                &program, &linked, candidate, &captures, ledger, &mut work,
            )?;
            assert!(std::ptr::eq(graph.arena, &program));
            assert_eq!(graph.candidate.initializer, candidate.initializer);
            assert_eq!(graph.argument_match, graph.definition.body);
            assert_eq!(graph.result.fields[0], graph.successor.call);
            assert_eq!(graph.result.fields[1], graph.status);
            assert_eq!(graph.successor.arguments.fields[0], graph.increment.root);
            assert_eq!(graph.increment.api, graph.definition.api);
            assert!(std::ptr::eq(graph.increment.arena, &program));
            let output_candidate = target_candidate(&program, &linked, "append_output");
            let constructor = |name: &str| {
                program
                    .registry()
                    .constructors()
                    .iter()
                    .find(|item| item.spelling == name)
                    .expect("fixture output constructor")
                    .id
            };
            let helpers = [
                target_candidate(&program, &linked, "append_child"),
                target_candidate(&program, &linked, "update_record"),
                target_candidate(&program, &linked, "append_output"),
            ];
            let success_constructors = super::RegistrationSuccessConstructors {
                ledger,
                work: constructor("Work"),
                child: constructor("Child"),
                record: constructor("Record"),
                open: constructor("Open"),
                parent: constructor("Parent"),
                work_out: constructor("WorkOut"),
                registered: constructor("Registered"),
            };
            let mut success_work = TypeWorkBudget::unbounded();
            let success = super::reconstruct_registration_success(
                &program,
                &linked,
                candidate,
                helpers,
                success_constructors,
                &mut success_work,
            )?;
            assert_eq!(success.counter.successor.call, graph.successor.call);
            assert_eq!(success.work_value.arguments.fields.len(), 2);
            assert_eq!(success.replacement.arguments.fields.len(), 4);
            assert_eq!(success.child.arguments.fields.len(), 2);
            assert_eq!(success.parent.arguments.fields.len(), 2);
            assert_eq!(success.output.arguments.fields.len(), 4);
            assert_eq!(success.helper_calls.len(), 3);
            assert_eq!(success.status_closure.api, success.counter.definition.api);
            let success_used = success_work.used();
            assert!(
                super::reconstruct_registration_success(
                    &program,
                    &linked,
                    candidate,
                    helpers,
                    success_constructors,
                    &mut TypeWorkBudget::with_limit(success_used),
                )
                .is_ok()
            );
            assert!(matches!(
                super::reconstruct_registration_success(
                    &program,
                    &linked,
                    candidate,
                    helpers,
                    success_constructors,
                    &mut TypeWorkBudget::with_limit(success_used - 1),
                ),
                Err(super::Rejection::Exhausted)
            ));
            let output_constructors = super::InsertConstructors {
                entry: constructor("WorkOut"),
                empty: constructor("NoOutputs"),
                more: constructor("OutputCons"),
            };
            let entry_candidate = target_candidate(&program, &linked, "reserve_job");
            let find_candidate = target_candidate(&program, &linked, "find_record");
            let finish_candidate = target_candidate(&program, &linked, "finish_registration");
            let flow_constructors = super::RegistrationFlowConstructors {
                ledger,
                record: constructor("Record"),
                no_record: constructor("NoRecord"),
                has_record: constructor("HasRecord"),
                closed: constructor("Closed"),
                open: constructor("Open"),
                rejected: constructor("Rejected"),
            };
            let record_list = super::RecordListConstructors {
                root: constructor("Root"),
                work: constructor("Work"),
                record: constructor("Record"),
                empty: constructor("NoRecords"),
                more: constructor("RecordCons"),
                absent: constructor("NoRecord"),
                present: constructor("HasRecord"),
            };
            let equality = target_candidate(&program, &linked, "same_id");
            let key = target_candidate(&program, &linked, "record_id");
            for (operation, selected) in [
                (super::RecordOperation::Lookup, find_candidate),
                (super::RecordOperation::Update, helpers[1]),
            ] {
                let mut record_work = TypeWorkBudget::unbounded();
                let record_graph = super::reconstruct_record_operation(
                    &program,
                    &linked,
                    selected,
                    equality,
                    key,
                    record_list,
                    operation,
                    &mut record_work,
                )?;
                assert!(std::ptr::eq(record_graph.arena, &program));
                assert!(std::ptr::eq(record_graph.linked, &linked));
                assert_eq!(
                    record_graph.definition.api,
                    record_graph.projection.definition.api
                );
                assert_eq!(record_graph.comparison.api, record_graph.definition.api);
                assert_eq!(record_graph.comparison_pair.fields.len(), 2);
                assert_eq!(
                    record_graph.recursive_pair.fields.len(),
                    match operation {
                        super::RecordOperation::Lookup => 2,
                        super::RecordOperation::Update => 3,
                    }
                );
                assert_ne!(record_graph.comparison_call, record_graph.recursive_call);
                assert_eq!(record_graph.candidate.initializer, selected.initializer);
                assert_eq!(record_graph.constructors.record, constructor("Record"));
                assert_eq!(record_graph.argument_match, record_graph.definition.body);
                assert_ne!(record_graph.list_match, record_graph.comparison_match);
                assert_eq!(
                    record_graph.comparison_pair.fields[0],
                    record_graph.projection_call
                );
                assert_ne!(record_graph.wanted, record_graph.list);
                assert_ne!(record_graph.entry, record_graph.tail);
                assert_eq!(record_graph.empty_result.fields.len(), 0);
                assert_eq!(record_graph.comparator_pair.fields.len(), 2);
                match (&record_graph.branches, operation) {
                    (
                        super::RecordOperationBranches::Lookup {
                            present_call,
                            present_closure,
                            present_value,
                        },
                        super::RecordOperation::Lookup,
                    ) => {
                        assert_ne!(*present_call, record_graph.recursive_call);
                        assert_eq!(present_closure.api, present_value.api);
                        assert!(record_graph.replacement.is_none());
                    }
                    (
                        super::RecordOperationBranches::Update { replaced, retained },
                        super::RecordOperation::Update,
                    ) => {
                        assert_eq!(replaced.arguments.fields.len(), 2);
                        assert_eq!(retained.arguments.fields[1], record_graph.recursive_call);
                        assert!(record_graph.replacement.is_some());
                    }
                    _ => panic!("wrong record operation witness"),
                }
                let used = record_work.used();
                assert!(
                    super::reconstruct_record_operation(
                        &program,
                        &linked,
                        selected,
                        equality,
                        key,
                        record_list,
                        operation,
                        &mut TypeWorkBudget::with_limit(used),
                    )
                    .is_ok()
                );
                assert!(matches!(
                    super::reconstruct_record_operation(
                        &program,
                        &linked,
                        selected,
                        equality,
                        key,
                        record_list,
                        operation,
                        &mut TypeWorkBudget::with_limit(used - 1),
                    ),
                    Err(super::Rejection::Exhausted)
                ));
            }
            let definitions = super::RegistrationDefinitions {
                entry: entry_candidate,
                find: find_candidate,
                finish: finish_candidate,
                commit: candidate,
                append_child: helpers[0],
                update: helpers[1],
                append_output: helpers[2],
                comparison: equality,
                projection: key,
            };
            let registration_constructors = super::RegistrationConstructors {
                state: super::InitializationConstructors {
                    ledger,
                    record: constructor("Record"),
                    root: constructor("Root"),
                    work: constructor("Work"),
                    no_parent: constructor("NoParent"),
                    parent: constructor("Parent"),
                    open: constructor("Open"),
                    closed: constructor("Closed"),
                    children_empty: constructor("Empty"),
                    children_more: constructor("More"),
                    records_empty: constructor("NoRecords"),
                    records_more: constructor("RecordCons"),
                    outputs_empty: constructor("NoOutputs"),
                    outputs_more: constructor("OutputCons"),
                },
                no_record: constructor("NoRecord"),
                has_record: constructor("HasRecord"),
                rejected: constructor("Rejected"),
                registered: constructor("Registered"),
                child: constructor("Child"),
                work_out: constructor("WorkOut"),
            };
            // Locate the fixture's actual consuming call; production receives
            // the same arena-bound node as untrusted nomination metadata.
            let call = program
                .nodes()
                .iter()
                .enumerate()
                .find_map(|(index, node)| {
                    let crate::core::EffectExprKind::Pure(crate::core::PureExprKind::Computation(
                        crate::core::PureComputation::Apply(application),
                    )) = &node.kind
                    else {
                        return None;
                    };
                    let crate::core::EffectExprKind::Pure(crate::core::PureExprKind::Variable(
                        variable,
                    )) = &program.node(application.function())?.kind
                    else {
                        return None;
                    };
                    (variable.binder() == definitions.entry.binder).then(|| {
                        crate::core::NodeId::new(
                            program.root().arena(),
                            u32::try_from(index).unwrap(),
                        )
                    })
                })
                .expect("actual registration call");
            let mut call_work = TypeWorkBudget::unbounded();
            let call_summary = super::check_nominated_registration_call(
                &program,
                &linked,
                call,
                definitions,
                registration_constructors,
                &mut call_work,
            )?;
            assert_eq!(call_summary.call(), call);
            assert_eq!(
                call_summary.provider_api(),
                call_summary.summary.graph.flow.entry.api
            );
            assert_eq!(call_summary.input(), call_summary.arguments.fields[0]);
            let matching = program
                .nodes()
                .iter()
                .enumerate()
                .find_map(|(index, node)| {
                    let crate::core::EffectExprKind::Pure(crate::core::PureExprKind::Computation(
                        crate::core::PureComputation::Match(branch),
                    )) = &node.kind
                    else {
                        return None;
                    };
                    (branch.scrutinee() == call).then(|| {
                        crate::core::NodeId::new(
                            program.root().arena(),
                            u32::try_from(index).unwrap(),
                        )
                    })
                })
                .expect("actual registration result match");
            let result = super::check_registration_result_match(
                &program,
                &call_summary,
                matching,
                &mut TypeWorkBudget::unbounded(),
            )?;
            assert_eq!(result.matching, matching);
            assert_ne!(result.ledger, result.status);
            assert!(program.node(result.body).is_some());
            assert!(matches!(
                super::check_registration_result_match(
                    &program,
                    &call_summary,
                    call,
                    &mut TypeWorkBudget::unbounded(),
                ),
                Err(super::Rejection::Unsupported)
            ));
            let initializer = target_candidate(&program, &linked, "initial");
            let mut init_work = TypeWorkBudget::unbounded();
            let init = super::check_nominated_initialization_call(
                &program,
                &linked,
                call_summary.input(),
                initializer,
                registration_constructors.state,
                super::InitializationRole::Root,
                &mut init_work,
            )?;
            assert_eq!(init.call(), call_summary.input());
            assert_eq!(init.provider_api(), call_summary.provider_api());
            let init_used = init_work.used();
            assert!(matches!(
                super::check_nominated_initialization_call(
                    &program,
                    &linked,
                    call_summary.input(),
                    initializer,
                    registration_constructors.state,
                    super::InitializationRole::Root,
                    &mut TypeWorkBudget::with_limit(init_used - 1),
                ),
                Err(super::Rejection::Exhausted)
            ));
            assert!(matches!(
                super::check_nominated_initialization_call(
                    &program,
                    &linked,
                    call,
                    initializer,
                    registration_constructors.state,
                    super::InitializationRole::Root,
                    &mut TypeWorkBudget::unbounded(),
                ),
                Err(super::Rejection::Unsupported)
            ));
            let call_used = call_work.used();
            assert!(
                super::check_nominated_registration_call(
                    &program,
                    &linked,
                    call,
                    definitions,
                    registration_constructors,
                    &mut TypeWorkBudget::with_limit(call_used),
                )
                .is_ok()
            );
            assert!(matches!(
                super::check_nominated_registration_call(
                    &program,
                    &linked,
                    call,
                    definitions,
                    registration_constructors,
                    &mut TypeWorkBudget::with_limit(call_used - 1),
                ),
                Err(super::Rejection::Exhausted)
            ));
            assert!(matches!(
                super::check_nominated_registration_call(
                    &program,
                    &linked,
                    definitions.finish.initializer,
                    definitions,
                    registration_constructors,
                    &mut TypeWorkBudget::unbounded(),
                ),
                Err(super::Rejection::Unsupported)
            ));

            let mut registration_work = TypeWorkBudget::unbounded();
            let summary = super::check_conditional_registration(
                &program,
                &linked,
                definitions,
                registration_constructors,
                &mut registration_work,
            )?;
            let registration = &summary.graph;
            assert!(std::ptr::eq(registration.arena, &program));
            assert!(std::ptr::eq(registration.linked, &linked));
            assert_eq!(
                registration.flow.entry.api,
                registration.success.counter.definition.api
            );
            assert_eq!(
                registration.lookup.graph.definition.api,
                registration.update.graph.definition.api
            );
            assert_eq!(
                registration.child_append.graph.provider_api,
                registration.output_append.graph.provider_api
            );
            let registration_used = registration_work.used();
            assert!(
                super::check_conditional_registration(
                    &program,
                    &linked,
                    definitions,
                    registration_constructors,
                    &mut TypeWorkBudget::with_limit(registration_used),
                )
                .is_ok()
            );
            assert!(matches!(
                super::check_conditional_registration(
                    &program,
                    &linked,
                    definitions,
                    registration_constructors,
                    &mut TypeWorkBudget::with_limit(registration_used - 1),
                ),
                Err(super::Rejection::Exhausted)
            ));
            let mut flow_work = TypeWorkBudget::unbounded();
            let flow = super::reconstruct_registration_flow(
                &program,
                &linked,
                entry_candidate,
                find_candidate,
                finish_candidate,
                candidate,
                flow_constructors,
                &mut flow_work,
            )?;
            assert!(std::ptr::eq(flow.arena, &program));
            assert!(std::ptr::eq(flow.linked, &linked));
            assert_eq!(flow.entry.api, flow.finish.api);
            assert_eq!(flow.missing_result.fields.len(), 2);
            assert_eq!(flow.closed_result.fields.len(), 2);
            assert_ne!(flow.find_call, flow.finish_call);
            assert_ne!(flow.finish_call, flow.commit_call);
            let flow_used = flow_work.used();
            assert!(
                super::reconstruct_registration_flow(
                    &program,
                    &linked,
                    entry_candidate,
                    find_candidate,
                    finish_candidate,
                    candidate,
                    flow_constructors,
                    &mut TypeWorkBudget::with_limit(flow_used),
                )
                .is_ok()
            );
            assert!(matches!(
                super::reconstruct_registration_flow(
                    &program,
                    &linked,
                    entry_candidate,
                    find_candidate,
                    finish_candidate,
                    candidate,
                    flow_constructors,
                    &mut TypeWorkBudget::with_limit(flow_used - 1),
                ),
                Err(super::Rejection::Exhausted)
            ));
            let mut output_work = TypeWorkBudget::unbounded();
            let output = super::check_conditional_spine_insertion(
                &program,
                &linked,
                output_candidate,
                output_constructors,
                &mut output_work,
            )?;
            assert!(std::ptr::eq(output.linked, &linked));
            assert!(std::ptr::eq(output.graph.arena, &program));
            assert_eq!(
                output.graph.candidate.initializer,
                output_candidate.initializer
            );
            let projection_candidate = target_candidate(&program, &linked, "record_id");
            let mut projection_work = TypeWorkBudget::unbounded();
            let projection = super::reconstruct_record_projection(
                &program,
                &linked,
                projection_candidate,
                constructor("Record"),
                constructor("Root"),
                &mut projection_work,
            )?;
            assert!(std::ptr::eq(projection.arena, &program));
            assert!(std::ptr::eq(projection.linked, &linked));
            assert_eq!(
                projection.candidate.initializer,
                projection_candidate.initializer
            );
            assert_eq!(projection.record, constructor("Record"));
            assert!(matches!(
                &program.node(projection.definition.body).unwrap().kind,
                super::EffectExprKind::Pure(super::PureExprKind::Computation(
                    super::PureComputation::Match(_)
                ))
            ));
            assert_ne!(projection.scrutinee, projection.result);
            assert_ne!(projection.fields[0], projection.fields[1]);
            let projection_used = projection_work.used();
            assert!(
                super::reconstruct_record_projection(
                    &program,
                    &linked,
                    projection_candidate,
                    constructor("Record"),
                    constructor("Root"),
                    &mut TypeWorkBudget::with_limit(projection_used),
                )
                .is_ok()
            );
            assert!(matches!(
                super::reconstruct_record_projection(
                    &program,
                    &linked,
                    projection_candidate,
                    constructor("Record"),
                    constructor("Root"),
                    &mut TypeWorkBudget::with_limit(projection_used - 1),
                ),
                Err(super::Rejection::Exhausted)
            ));
            assert!(matches!(
                super::reconstruct_record_projection(
                    &program,
                    &linked,
                    projection_candidate,
                    constructor("Child"),
                    constructor("Root"),
                    &mut TypeWorkBudget::unbounded(),
                ),
                Err(super::Rejection::Unsupported)
            ));
            let output_used = output_work.used();
            let mut output_exact = TypeWorkBudget::with_limit(output_used);
            assert!(
                super::check_conditional_spine_insertion(
                    &program,
                    &linked,
                    output_candidate,
                    output_constructors,
                    &mut output_exact,
                )
                .is_ok()
            );
            let mut output_short = TypeWorkBudget::with_limit(output_used - 1);
            assert!(matches!(
                super::check_conditional_spine_insertion(
                    &program,
                    &linked,
                    output_candidate,
                    output_constructors,
                    &mut output_short,
                ),
                Err(super::Rejection::Exhausted)
            ));
            let mut wrong_output = output_constructors;
            wrong_output.entry = constructor("Child");
            assert!(matches!(
                super::check_conditional_spine_insertion(
                    &program,
                    &linked,
                    output_candidate,
                    wrong_output,
                    &mut TypeWorkBudget::unbounded(),
                ),
                Err(super::Rejection::Unsupported)
            ));
            let used = work.used();
            let mut exact = TypeWorkBudget::with_limit(used);
            assert!(
                super::reconstruct_registration_counter(
                    &program, &linked, candidate, &captures, ledger, &mut exact,
                )
                .is_ok()
            );
            let mut short = TypeWorkBudget::with_limit(used - 1);
            assert!(matches!(
                super::reconstruct_registration_counter(
                    &program, &linked, candidate, &captures, ledger, &mut short,
                ),
                Err(super::Rejection::Exhausted)
            ));
            Ok(())
        }
        assert_eq!(inspect(REGISTER), Ok(()));
        assert_eq!(inspect_variant(REGISTER, true), Ok(()));
        assert_eq!(
            inspect(&REGISTER.replace("true => HasRecord(record)", "true => NoRecord")),
            Err(super::Rejection::Unsupported)
        );
        assert_eq!(
            inspect(&REGISTER.replace(
                "false => find_record (wanted, tail)",
                "false => find_record (wanted, records)"
            )),
            Err(super::Rejection::Unsupported)
        );
        assert_eq!(
            inspect(&REGISTER.replace("RecordCons(replacement, tail)", "RecordCons(record, tail)")),
            Err(super::Rejection::Unsupported)
        );
        assert_eq!(
            inspect(&REGISTER.replace(
                "update_record (wanted, replacement, tail)",
                "update_record (wanted, replacement, records)"
            )),
            Err(super::Rejection::Unsupported)
        );
        assert_eq!(
            inspect(&REGISTER.replace(
                "NoRecord => (ledger, Rejected)",
                "NoRecord => (ledger, Registered(wanted))"
            )),
            Err(super::Rejection::Unsupported)
        );
        assert_eq!(
            inspect(&REGISTER.replace(
                "Closed => (ledger, Rejected)",
                "Closed => (ledger, Registered(wanted))"
            )),
            Err(super::Rejection::Unsupported)
        );
        assert_eq!(
            inspect(&REGISTER.replace("commit_registration (next, owner, wanted, destination, payload, records, outputs, parent, children)",
                "commit_registration (owner, next, wanted, destination, payload, records, outputs, parent, children)")),
            Err(super::Rejection::Unsupported)
        );
        assert_eq!(
            inspect(&REGISTER.replace(
                "Record(actual, parent, phase, children) => actual",
                "Record(actual, parent, phase, children) => Root",
            )),
            Err(super::Rejection::Unsupported)
        );
        assert_eq!(
            inspect(&REGISTER.replace(
                "let child = Work(owner, next)",
                "let child = Work(owner, owner)"
            )),
            Err(super::Rejection::Unsupported)
        );
        assert_eq!(
            inspect(&REGISTER.replace(
                "Parent(owner, wanted), destination, payload",
                "Parent(destination, wanted), destination, payload"
            )),
            Err(super::Rejection::Unsupported)
        );
        assert_eq!(
            inspect(&REGISTER.replace("Registered(child)", "Registered(wanted)")),
            Err(super::Rejection::Unsupported)
        );
        assert_eq!(
            inspect(&REGISTER.replace("next + 1", "next + 2")),
            Err(super::Rejection::Unsupported)
        );
        assert_eq!(
            inspect(&REGISTER.replace("next + 1", "1 + next")),
            Err(super::Rejection::Unsupported)
        );
        assert_eq!(
            inspect(&REGISTER.replace("next + 1", "owner + 1")),
            Err(super::Rejection::Unsupported)
        );
        assert_eq!(
            inspect(&REGISTER.replace("next + 1", "next")),
            Err(super::Rejection::Unsupported)
        );
        assert_eq!(
            inspect(&REGISTER.replace(
                "OutputCons(output, append_output (added, tail))",
                "append_output (added, tail)",
            )),
            Err(super::Rejection::Unsupported)
        );
    }

    // Search actual linked Core calls; names select candidates only.
    fn fixture_call(
        program: &ValidatedEffectProgram,
        binder: crate::resolved::BinderId,
    ) -> crate::core::NodeId {
        program
            .nodes()
            .iter()
            .enumerate()
            .find_map(|(index, node)| {
                let crate::core::EffectExprKind::Pure(crate::core::PureExprKind::Computation(
                    crate::core::PureComputation::Apply(application),
                )) = &node.kind
                else {
                    return None;
                };
                let crate::core::EffectExprKind::Pure(crate::core::PureExprKind::Variable(
                    variable,
                )) = &program.node(application.function())?.kind
                else {
                    return None;
                };
                (variable.binder() == binder).then(|| {
                    crate::core::NodeId::new(
                        program.root().arena(),
                        u32::try_from(index).expect("fixture node index"),
                    )
                })
            })
            .expect("fixture call")
    }

    #[test]
    fn closure_reconstructs_actual_branches_and_successor() {
        const CLOSE: &str = include_str!("closure.ash");
        const COMMON: &str = include_str!("acknowledgement.ash");
        fn inspect(close: &str) -> Result<(), super::Rejection> {
            use super::closure::{
                ClosureConstructors, ClosureDefinitions, check_conditional_closure,
                check_nominated_closure_call,
            };
            let source = ORDINARY_LEDGER.replace("main : Unit -> Unit",
                &format!("{COMMON}\n{close}\nmain : Unit -> Unit"))
                .replace("let ignored = remove_child (Root, Empty)",
                    "let ignored_close = close_record (initial (), Root)\n    let ignored = remove_child (Root, Empty)");
            let (program, linked) = ordinary_ledger(&source);
            let candidate = |name| target_candidate(&program, &linked, name);
            let constructor = |name: &str| {
                program
                    .registry()
                    .constructors()
                    .iter()
                    .find(|item| item.spelling == name)
                    .expect("fixture constructor")
                    .id
            };
            let d = ClosureDefinitions {
                entry: candidate("close_record"),
                finish: candidate("finish_close"),
                lookup: candidate("find_record"),
                update: candidate("update_record"),
                comparison: candidate("same_id"),
                projection: candidate("record_id"),
            };
            let c = ClosureConstructors {
                state: super::InitializationConstructors {
                    ledger: constructor("Ledger"),
                    record: constructor("Record"),
                    root: constructor("Root"),
                    work: constructor("Work"),
                    no_parent: constructor("NoParent"),
                    parent: constructor("Parent"),
                    open: constructor("Open"),
                    closed: constructor("Closed"),
                    children_empty: constructor("Empty"),
                    children_more: constructor("More"),
                    records_empty: constructor("NoRecords"),
                    records_more: constructor("RecordCons"),
                    outputs_empty: constructor("NoOutputs"),
                    outputs_more: constructor("OutputCons"),
                },
                no_record: constructor("NoRecord"),
                has_record: constructor("HasRecord"),
            };
            let call = fixture_call(&program, d.entry.binder);
            let wrong = fixture_call(&program, d.update.binder);
            let mut budget = TypeWorkBudget::unbounded();
            let witness = check_nominated_closure_call(&program, &linked, call, d, c, &mut budget)?;
            assert_eq!(witness.call(), call);
            assert_eq!(witness.return_expressions().len(), 3);
            assert_eq!(witness.successor_fields().len(), 3);
            assert_eq!(witness.replacement_fields().len(), 4);
            let used = budget.used();
            assert!(
                check_nominated_closure_call(
                    &program,
                    &linked,
                    call,
                    d,
                    c,
                    &mut TypeWorkBudget::with_limit(used)
                )
                .is_ok()
            );
            assert!(matches!(
                check_nominated_closure_call(
                    &program,
                    &linked,
                    call,
                    d,
                    c,
                    &mut TypeWorkBudget::with_limit(used - 1)
                ),
                Err(super::Rejection::Exhausted)
            ));
            assert!(matches!(
                check_nominated_closure_call(
                    &program,
                    &linked,
                    wrong,
                    d,
                    c,
                    &mut TypeWorkBudget::unbounded()
                ),
                Err(super::Rejection::Unsupported)
            ));
            check_conditional_closure(&program, &linked, d, c, &mut TypeWorkBudget::unbounded())?;
            Ok(())
        }
        inspect(CLOSE).expect("actual Close definition and call");
        for (before, after) in [
            (
                "NoRecord => ledger",
                "NoRecord => Ledger(next, records, outputs)",
            ),
            (
                "Record(actual, parent, Closed, children)",
                "Record(actual, parent, Open, children)",
            ),
            ("update_record (wanted,", "update_record (actual,"),
            (
                "Closed => ledger",
                "Closed => Ledger(next, records, outputs)",
            ),
        ] {
            let mutated = CLOSE.replace(before, after);
            assert_ne!(mutated, CLOSE);
            assert!(matches!(
                inspect(&mutated),
                Err(super::Rejection::Unsupported)
            ));
        }
    }

    #[test]
    fn acknowledgement_reconstructs_actual_peer_and_successor() {
        const ACK: &str = include_str!("acknowledgement.ash");
        fn inspect(extra: &str) -> Result<(), super::Rejection> {
            use super::acknowledgement::{
                AcknowledgementConstructors, AcknowledgementDefinitions,
                check_conditional_acknowledgement,
            };
            let source = ORDINARY_LEDGER.replace(
                "main : Unit -> Unit",
                &format!("{extra}\nmain : Unit -> Unit"),
            ).replace("let ignored = remove_child (Root, Empty)",
                "let ignored_ack = acknowledge (initial (), Root, Root, 1)\n    let ignored = remove_child (Root, Empty)");
            let (program, linked) = ordinary_ledger(&source);
            let candidate = |name| target_candidate(&program, &linked, name);
            let constructor = |name: &str| {
                program
                    .registry()
                    .constructors()
                    .iter()
                    .find(|item| item.spelling == name)
                    .expect("fixture constructor")
                    .id
            };
            let d = AcknowledgementDefinitions {
                entry: candidate("acknowledge"),
                record: candidate("ack_found"),
                child: candidate("ack_child"),
                commit: candidate("ack_commit"),
                record_lookup: candidate("find_record"),
                child_lookup: candidate("find_child"),
                record_update: candidate("update_record"),
                child_removal: candidate("remove_child"),
                comparison: candidate("same_id"),
                record_projection: candidate("record_id"),
                child_projection: candidate("child_id"),
            };
            let c = AcknowledgementConstructors {
                state: super::InitializationConstructors {
                    ledger: constructor("Ledger"),
                    record: constructor("Record"),
                    root: constructor("Root"),
                    work: constructor("Work"),
                    no_parent: constructor("NoParent"),
                    parent: constructor("Parent"),
                    open: constructor("Open"),
                    closed: constructor("Closed"),
                    children_empty: constructor("Empty"),
                    children_more: constructor("More"),
                    records_empty: constructor("NoRecords"),
                    records_more: constructor("RecordCons"),
                    outputs_empty: constructor("NoOutputs"),
                    outputs_more: constructor("OutputCons"),
                },
                child: constructor("Child"),
                no_record: constructor("NoRecord"),
                has_record: constructor("HasRecord"),
                no_child: constructor("NoChild"),
                has_child: constructor("HasChild"),
                removed: constructor("Found"),
                missing: constructor("Missing"),
            };
            let call = fixture_call(&program, d.entry.binder);
            let wrong = fixture_call(&program, d.child_removal.binder);
            let mut call_budget = TypeWorkBudget::unbounded();
            let witness = super::acknowledgement::check_nominated_acknowledgement_call(
                &program,
                &linked,
                call,
                d,
                c,
                &mut call_budget,
            )?;
            assert_eq!(witness.call(), call);
            assert_eq!(witness.input(), witness.arguments()[0]);
            assert_eq!(witness.arguments().len(), 4);
            assert_eq!(witness.return_expressions().len(), 4);
            assert_eq!(witness.successor_fields().len(), 3);
            let used = call_budget.used();
            assert!(
                super::acknowledgement::check_nominated_acknowledgement_call(
                    &program,
                    &linked,
                    call,
                    d,
                    c,
                    &mut TypeWorkBudget::with_limit(used)
                )
                .is_ok()
            );
            let mut spent = TypeWorkBudget::with_limit(used + 1);
            spent.charge(1).expect("fixture budget prefix");
            assert!(
                super::acknowledgement::check_nominated_acknowledgement_call(
                    &program, &linked, call, d, c, &mut spent
                )
                .is_ok()
            );
            let mut short = TypeWorkBudget::with_limit(used - 1);
            assert!(matches!(
                super::acknowledgement::check_nominated_acknowledgement_call(
                    &program, &linked, call, d, c, &mut short
                ),
                Err(super::Rejection::Exhausted)
            ));
            assert!(matches!(
                super::acknowledgement::check_nominated_acknowledgement_call(
                    &program, &linked, call, d, c, &mut short
                ),
                Err(super::Rejection::Exhausted)
            ));
            assert!(matches!(
                super::acknowledgement::check_nominated_acknowledgement_call(
                    &program,
                    &linked,
                    wrong,
                    d,
                    c,
                    &mut TypeWorkBudget::unbounded()
                ),
                Err(super::Rejection::Unsupported)
            ));
            let mut budget = TypeWorkBudget::unbounded();
            check_conditional_acknowledgement(&program, &linked, d, c, &mut budget)?;
            let used = budget.used();
            assert!(
                check_conditional_acknowledgement(
                    &program,
                    &linked,
                    d,
                    c,
                    &mut TypeWorkBudget::with_limit(used)
                )
                .is_ok()
            );
            assert!(matches!(
                check_conditional_acknowledgement(
                    &program,
                    &linked,
                    d,
                    c,
                    &mut TypeWorkBudget::with_limit(used - 1)
                ),
                Err(super::Rejection::Exhausted)
            ));
            Ok(())
        }
        assert!(inspect(ACK).is_ok());
        for (before, after) in [
            (
                "NoRecord => ledger",
                "NoRecord => Ledger(next, NoRecords, outputs)",
            ),
            (
                "NoChild => ledger",
                "NoChild => Ledger(next, NoRecords, outputs)",
            ),
            ("destination == peer", "peer == peer"),
            (
                "false => ledger",
                "false => Ledger(next, NoRecords, outputs)",
            ),
            (
                "Record(actual, parent, phase, remaining)",
                "Record(actual, parent, Open, remaining)",
            ),
            (
                "Record(actual, parent, phase, remaining)",
                "Record(actual, NoParent, phase, remaining)",
            ),
            (
                "remove_child (child_id, children)",
                "remove_child (parent_id, children)",
            ),
            (
                "Ledger(next, update_record",
                "Ledger(next + 1, update_record",
            ),
            ("), outputs)\n}", "), NoOutputs)\n}"),
        ] {
            let mutated = ACK.replace(before, after);
            assert_ne!(mutated, ACK, "fixture mutation must apply");
            assert!(
                matches!(inspect(&mutated), Err(super::Rejection::Unsupported)),
                "mutation: {before}"
            );
        }
    }

    #[test]
    fn retirement_reconstructs_every_actual_branch_and_successor() {
        const RETIREMENT: &str = include_str!("retirement.ash");
        fn inspect(extra: &str) -> Result<(), super::Rejection> {
            use super::retirement::{
                RetirementConstructors, RetirementDefinitions, check_conditional_retirement,
            };
            let source = ORDINARY_LEDGER.replace(
                "main : Unit -> Unit",
                &format!("{extra}\nmain : Unit -> Unit"),
            ).replace("let ignored = remove_child (Root, Empty)",
                "let ignored_retire = retire (initial (), Root)\n    let ignored = remove_child (Root, Empty)");
            let (program, linked) = ordinary_ledger(&source);
            let candidate = |name| target_candidate(&program, &linked, name);
            let constructor = |name: &str| {
                program
                    .registry()
                    .constructors()
                    .iter()
                    .find(|item| item.spelling == name)
                    .expect("fixture constructor")
                    .id
            };
            let d = RetirementDefinitions {
                entry: candidate("retire"),
                work: candidate("retire_work"),
                found: candidate("retire_found"),
                parent: candidate("retire_parent"),
                phase: candidate("retire_phase"),
                children: candidate("retire_children"),
                commit: candidate("commit_retirement"),
                lookup: candidate("find_record"),
                removal: candidate("remove_record"),
                append_output: candidate("append_output"),
                comparison: candidate("same_id"),
                projection: candidate("record_id"),
            };
            let c = RetirementConstructors {
                state: super::InitializationConstructors {
                    ledger: constructor("Ledger"),
                    record: constructor("Record"),
                    root: constructor("Root"),
                    work: constructor("Work"),
                    no_parent: constructor("NoParent"),
                    parent: constructor("Parent"),
                    open: constructor("Open"),
                    closed: constructor("Closed"),
                    children_empty: constructor("Empty"),
                    children_more: constructor("More"),
                    records_empty: constructor("NoRecords"),
                    records_more: constructor("RecordCons"),
                    outputs_empty: constructor("NoOutputs"),
                    outputs_more: constructor("OutputCons"),
                },
                no_record: constructor("NoRecord"),
                has_record: constructor("HasRecord"),
                found: constructor("Found"),
                missing: constructor("Missing"),
                ack: constructor("AckOut"),
            };
            let call = fixture_call(&program, d.entry.binder);
            let wrong = fixture_call(&program, candidate("remove_child").binder);
            let mut call_budget = TypeWorkBudget::unbounded();
            let witness = super::retirement::check_nominated_retirement_call(
                &program,
                &linked,
                call,
                d,
                c,
                &mut call_budget,
            )?;
            assert_eq!(witness.call(), call);
            assert_eq!(witness.input(), witness.arguments()[0]);
            assert_eq!(witness.arguments().len(), 2);
            assert_eq!(witness.return_expressions().len(), 6);
            assert_eq!(witness.successor_fields().len(), 3);
            let used = call_budget.used();
            assert!(
                super::retirement::check_nominated_retirement_call(
                    &program,
                    &linked,
                    call,
                    d,
                    c,
                    &mut TypeWorkBudget::with_limit(used)
                )
                .is_ok()
            );
            let mut spent = TypeWorkBudget::with_limit(used + 1);
            spent.charge(1).expect("fixture budget prefix");
            assert!(
                super::retirement::check_nominated_retirement_call(
                    &program, &linked, call, d, c, &mut spent
                )
                .is_ok()
            );
            let mut short = TypeWorkBudget::with_limit(used - 1);
            assert!(matches!(
                super::retirement::check_nominated_retirement_call(
                    &program, &linked, call, d, c, &mut short
                ),
                Err(super::Rejection::Exhausted)
            ));
            assert!(matches!(
                super::retirement::check_nominated_retirement_call(
                    &program, &linked, call, d, c, &mut short
                ),
                Err(super::Rejection::Exhausted)
            ));
            assert!(matches!(
                super::retirement::check_nominated_retirement_call(
                    &program,
                    &linked,
                    wrong,
                    d,
                    c,
                    &mut TypeWorkBudget::unbounded()
                ),
                Err(super::Rejection::Unsupported)
            ));
            let mut budget = TypeWorkBudget::unbounded();
            check_conditional_retirement(&program, &linked, d, c, &mut budget)?;
            let used = budget.used();
            assert!(
                check_conditional_retirement(
                    &program,
                    &linked,
                    d,
                    c,
                    &mut TypeWorkBudget::with_limit(used)
                )
                .is_ok()
            );
            assert!(matches!(
                check_conditional_retirement(
                    &program,
                    &linked,
                    d,
                    c,
                    &mut TypeWorkBudget::with_limit(used - 1)
                ),
                Err(super::Rejection::Exhausted)
            ));
            Ok(())
        }
        assert!(inspect(RETIREMENT).is_ok());
        for (before, after) in [
            (
                "Root => ledger",
                "Root => retire_work (ledger, next, wanted, records, outputs)",
            ),
            (
                "NoRecord => ledger",
                "NoRecord => Ledger(next, NoRecords, outputs)",
            ),
            (
                "NoParent => ledger",
                "NoParent => Ledger(next, NoRecords, outputs)",
            ),
            ("Open => ledger", "Open => Ledger(next, NoRecords, outputs)"),
            (
                "More(child, tail) => ledger",
                "More(child, tail) => Ledger(next, NoRecords, outputs)",
            ),
            ("AckOut(parent, wanted)", "AckOut(NoParent, wanted)"),
            (
                "Ledger(next, remaining, append_output",
                "Ledger(next + 1, remaining, append_output",
            ),
            ("RecordCons(entry, remaining), status", "remaining, status"),
            (
                "remove_record (wanted, tail)",
                "remove_record (wanted, records)",
            ),
        ] {
            let mutated = RETIREMENT.replace(before, after);
            assert_ne!(mutated, RETIREMENT, "fixture mutation must apply");
            assert!(
                matches!(inspect(&mutated), Err(super::Rejection::Unsupported)),
                "mutation: {before}"
            );
        }
    }

    #[test]
    fn record_removal_preserves_whole_entries_and_status() {
        const REMOVE_RECORD: &str = r#"
record_id : Record -> Identity
record_id record = match record {
    Record(actual, parent, phase, children) => actual
}

remove_record : (Identity, Records) -> (Records, Removal)
remove_record (wanted, records) = match records {
    NoRecords => (NoRecords, Missing)
    RecordCons(entry, tail) => match same_id (record_id entry, wanted) {
        true => (tail, Found)
        false => match remove_record (wanted, tail) {
            (remaining, status) => (RecordCons(entry, remaining), status)
        }
    }
}
"#;
        fn inspect(extra: &str) -> Result<usize, super::Rejection> {
            let source = ORDINARY_LEDGER.replace(
                "main : Unit -> Unit",
                &format!("{extra}\nmain : Unit -> Unit"),
            );
            let (program, linked) = ordinary_ledger(&source);
            let constructor = |name: &str| {
                program
                    .registry()
                    .constructors()
                    .iter()
                    .find(|item| item.spelling == name)
                    .expect("fixture constructor")
                    .id
            };
            let shape = super::RemovalConstructors {
                empty: constructor("NoRecords"),
                more: constructor("RecordCons"),
                found: constructor("Found"),
                missing: constructor("Missing"),
                root_id: constructor("Root"),
                work_id: constructor("Work"),
                entry: constructor("Record"),
            };
            let dependencies = super::RemovalDependencies {
                comparison: target_candidate(&program, &linked, "same_id"),
                projection: target_candidate(&program, &linked, "record_id"),
            };
            let target = target_candidate(&program, &linked, "remove_record");
            let mut budget = TypeWorkBudget::unbounded();
            super::check_conditional_record_removal(
                &program,
                &linked,
                target,
                shape,
                dependencies,
                &mut budget,
            )?;
            Ok(budget.used())
        }
        assert!(inspect(REMOVE_RECORD).is_ok());
        assert!(matches!(
            inspect(&REMOVE_RECORD.replace(
                "(RecordCons(entry, remaining), status)",
                "(remaining, status)"
            )),
            Err(super::Rejection::Unsupported)
        ));
        assert!(matches!(
            inspect(&REMOVE_RECORD.replace(
                "remove_record (wanted, tail)",
                "remove_record (wanted, records)"
            )),
            Err(super::Rejection::Unsupported)
        ));
        assert!(matches!(
            inspect(&REMOVE_RECORD.replace("true => (tail, Found)", "true => (tail, Missing)")),
            Err(super::Rejection::Unsupported)
        ));
    }

    #[test]
    fn removal_body_is_reconstructed_from_linked_core() {
        fn inspect(source: &str) -> Result<(), super::Rejection> {
            let (program, linked) = ordinary_ledger(source);
            let target = target_candidate(&program, &linked, "remove_child");
            let constructor = |name: &str| {
                program
                    .registry()
                    .constructors()
                    .iter()
                    .find(|item| item.spelling == name)
                    .expect("fixture constructor")
                    .id
            };
            let shape = super::RemovalConstructors {
                empty: constructor("Empty"),
                more: constructor("More"),
                found: constructor("Found"),
                missing: constructor("Missing"),
                root_id: constructor("Root"),
                work_id: constructor("Work"),
                entry: constructor("Child"),
            };
            let dependencies = super::RemovalDependencies {
                comparison: target_candidate(&program, &linked, "same_id"),
                projection: target_candidate(&program, &linked, "child_id"),
            };
            let mut budget = TypeWorkBudget::unbounded();
            let result = super::check_conditional_removal(
                &program,
                &linked,
                target,
                shape,
                dependencies,
                &mut budget,
            )
            .map(|summary| {
                assert!(std::ptr::eq(summary.linked, &linked));
                assert!(std::ptr::eq(summary.graph.arena, &program));
                assert_eq!(summary.graph.candidate.binder, target.binder);
                assert_eq!(
                    summary.graph.dependencies.comparison.binder,
                    dependencies.comparison.binder
                );
                assert_eq!(
                    summary.graph.dependencies.projection.binder,
                    dependencies.projection.binder
                );
            });
            if result.is_ok() {
                let used = budget.used();
                let graph = super::reconstruct_removal_graph(
                    &program,
                    &linked,
                    target,
                    shape,
                    dependencies,
                    false,
                    &mut TypeWorkBudget::unbounded(),
                )?;
                assert!(std::ptr::eq(graph.arena, &program));
                assert_eq!(graph.definition.api, graph.provider_api);
                assert_eq!(graph.comparison_pair.api, graph.provider_api);
                assert_eq!(graph.constructor_value.api, graph.provider_api);
                assert_eq!(graph.definition.root, target.initializer);
                assert_eq!(graph.comparison.root, dependencies.comparison.initializer);
                assert_eq!(graph.projection.root, dependencies.projection.initializer);
                assert_eq!(graph.definition.body, graph.argument_match);
                for closure in [
                    graph.definition,
                    graph.comparison,
                    graph.projection,
                    graph.constructor,
                ] {
                    assert!(std::ptr::eq(closure.arena, &program));
                    for node in [
                        closure.root,
                        closure.query,
                        closure.unit,
                        closure.closure,
                        closure.context,
                        closure.storage,
                        closure.storage_context,
                        closure.request,
                        closure.body,
                    ] {
                        assert!(program.node(node).is_some());
                    }
                    assert_eq!(
                        program
                            .node(closure.root)
                            .and_then(|node| match &node.kind {
                                crate::core::EffectExprKind::Pure(
                                    crate::core::PureExprKind::Computation(
                                        crate::core::PureComputation::Bind(bind),
                                    ),
                                ) => Some(bind.binder().id()),
                                _ => None,
                            }),
                        Some(closure.context_binder)
                    );
                    assert!(crate::resolved::RegionApi::for_module(closure.api).is_some());
                    assert!(
                        closure
                            .captures
                            .iter()
                            .all(|node| program.node(*node).is_some())
                    );
                }
                for tuple in [
                    graph.empty_pair,
                    graph.empty_value,
                    graph.missing_value,
                    graph.comparison_pair,
                    graph.comparator_pair,
                    graph.hit_pair,
                    graph.found_value,
                    graph.recursive_pair,
                    graph.result_pair,
                    graph.constructor_pair,
                    graph.constructor_value,
                ] {
                    assert!(std::ptr::eq(tuple.arena, &program));
                    assert!(program.node(tuple.root).is_some());
                }
                assert_eq!(graph.comparison_pair.fields[0], graph.projection_call);
                assert_eq!(graph.result_pair.fields[0], graph.rebuild_call);
                assert_eq!(
                    graph.empty_value.constructor,
                    Some(graph.constructors.empty)
                );
                assert_eq!(
                    graph.missing_value.constructor,
                    Some(graph.constructors.missing)
                );
                assert_eq!(
                    graph.found_value.constructor,
                    Some(graph.constructors.found)
                );
                assert_eq!(
                    graph.constructor_value.constructor,
                    Some(graph.constructors.more)
                );
                for node in [
                    graph.argument_match,
                    graph.list_match,
                    graph.comparison_match,
                    graph.recursive_match,
                    graph.comparison_call,
                    graph.projection_call,
                    graph.recursive_call,
                    graph.rebuild_call,
                ] {
                    assert!(program.node(node).is_some());
                }
                assert_eq!(graph.work_fields.len(), 4);
                assert_eq!(graph.projection_fields.len(), 2);
                assert_ne!(graph.wanted, graph.list);
                assert_ne!(graph.entry, graph.tail);
                assert_ne!(graph.remaining, graph.status);
                assert_ne!(graph.comparison_left, graph.comparison_right);
                let (other_program, other_linked) = ordinary_ledger(source);
                let mut identity_work = TypeWorkBudget::unbounded();
                assert!(matches!(
                    super::check_conditional_removal(
                        &other_program,
                        &other_linked,
                        target,
                        shape,
                        dependencies,
                        &mut identity_work,
                    ),
                    Err(super::Rejection::Unsupported)
                ));
                let mut wrong_dependencies = dependencies;
                wrong_dependencies.comparison = dependencies.projection;
                let mut dependency_work = TypeWorkBudget::unbounded();
                assert!(matches!(
                    super::check_conditional_removal(
                        &program,
                        &linked,
                        target,
                        shape,
                        wrong_dependencies,
                        &mut dependency_work,
                    ),
                    Err(super::Rejection::Unsupported)
                ));
                let mut bad_shape = shape;
                bad_shape.more = bad_shape.empty;
                let mut identity_work = TypeWorkBudget::unbounded();
                assert!(matches!(
                    super::check_conditional_removal(
                        &program,
                        &linked,
                        target,
                        bad_shape,
                        dependencies,
                        &mut identity_work,
                    ),
                    Err(super::Rejection::Unsupported)
                ));
                let mut exact = TypeWorkBudget::with_limit(used);
                assert_eq!(
                    super::check_conditional_removal(
                        &program,
                        &linked,
                        target,
                        shape,
                        dependencies,
                        &mut exact
                    )
                    .map(|_| ()),
                    Ok(())
                );
                let mut short = TypeWorkBudget::with_limit(used - 1);
                assert_eq!(
                    super::check_conditional_removal(
                        &program,
                        &linked,
                        target,
                        shape,
                        dependencies,
                        &mut short
                    )
                    .map(|_| ()),
                    Err(super::Rejection::Exhausted)
                );
            }
            result
        }
        assert_eq!(inspect(ORDINARY_LEDGER), Ok(()));
        let mutant = ORDINARY_LEDGER.replace("true => (tail, Found)", "true => (tail, Missing)");
        assert_eq!(inspect(&mutant), Err(super::Rejection::Unsupported));
        let wrong_tail = ORDINARY_LEDGER.replace(
            "remove_child (wanted, tail)",
            "remove_child (wanted, children)",
        );
        assert_eq!(inspect(&wrong_tail), Err(super::Rejection::Unsupported));
        let drop_head = ORDINARY_LEDGER.replace("More(entry, remaining)", "remaining");
        assert_eq!(inspect(&drop_head), Err(super::Rejection::Unsupported));
        let bad_equality = ORDINARY_LEDGER.replace("_ => false", "_ => true");
        assert_eq!(inspect(&bad_equality), Err(super::Rejection::Unsupported));
        let bad_projection = ORDINARY_LEDGER.replace(
            "Child(actual, destination) => actual",
            "Child(actual, destination) => Root",
        );
        assert_eq!(inspect(&bad_projection), Err(super::Rejection::Unsupported));
    }

    #[test]
    fn linked_entry_call_requires_the_default_provider_path() {
        fn inspect(source: &str) -> Result<crate::core::NodeId, super::Rejection> {
            let (program, linked) = ordinary_ledger(source);
            let removal = target_candidate(&program, &linked, "remove_child");
            let caller = target_candidate(&program, &linked, "main");
            let constructor = |name: &str| {
                program
                    .registry()
                    .constructors()
                    .iter()
                    .find(|item| item.spelling == name)
                    .expect("fixture constructor")
                    .id
            };
            let shape = super::RemovalConstructors {
                empty: constructor("Empty"),
                more: constructor("More"),
                found: constructor("Found"),
                missing: constructor("Missing"),
                root_id: constructor("Root"),
                work_id: constructor("Work"),
                entry: constructor("Child"),
            };
            let call = super::check_root_entry_removal_call(
                &program,
                &linked,
                removal,
                caller,
                shape,
                &mut TypeWorkBudget::unbounded(),
            )?;
            let mut work = TypeWorkBudget::unbounded();
            let mut inspector = super::CoreInspection {
                program: &program,
                work: &mut work,
            };
            let argument = inspector.application(call)?.argument();
            let witness = inspector.persistent_tuple(argument, None)?;
            assert!(std::ptr::eq(witness.arena, &program));
            assert_eq!(witness.root, argument);
            let super::EffectExprKind::Pure(super::PureExprKind::Computation(
                super::PureComputation::Bind(binding),
            )) = &program.node(witness.root).expect("witness root").kind
            else {
                unreachable!()
            };
            assert_eq!(witness.context_binder, binding.binder().id());
            assert_eq!(witness.query, binding.initializer());
            assert_eq!(witness.tuple, binding.body());
            let super::EffectExprKind::Operation(super::EffectOperation::Request(query)) =
                &program.node(witness.query).expect("query").kind
            else {
                unreachable!()
            };
            assert_eq!(witness.unit, query.operand());
            let super::EffectExprKind::Operation(super::EffectOperation::RegionTuple(tuple)) =
                &program.node(witness.tuple).expect("tuple").kind
            else {
                unreachable!()
            };
            assert_eq!(witness.api, tuple.api);
            assert_eq!(witness.constructor, tuple.constructor);
            assert_eq!(witness.context, tuple.context);
            assert_eq!(witness.storage, tuple.storage);
            assert_eq!(witness.fields, &*tuple.fields);
            let super::EffectExprKind::Operation(super::EffectOperation::RegionAllocate(storage)) =
                &program.node(witness.storage).expect("storage").kind
            else {
                unreachable!()
            };
            assert_eq!(witness.storage_context, storage.context);
            assert_eq!(witness.request, storage.request);
            Ok(call)
        }
        assert!(inspect(ORDINARY_LEDGER).is_ok());
        let local = ORDINARY_LEDGER.replace(
            "main () = {\n    let ignored = remove_child (Root, Empty)\n    ()\n}",
            "main () = region<R> owner {\n    let ignored = remove_child (Root, Empty)\n    ()\n}",
        );
        assert_ne!(local, ORDINARY_LEDGER);
        assert_eq!(inspect(&local), Err(super::Rejection::Unsupported));
    }

    #[test]
    fn ordinary_ledger_fixture_reaches_independently_validated_linked_core() {
        let (program, linked) = ordinary_ledger(ORDINARY_LEDGER);
        assert!(program.node(program.root()).is_some());
        assert!(std::sync::Arc::ptr_eq(
            program.registry(),
            linked.registry()
        ));
        if std::env::var_os("ASH_LEDGER_DUMP").is_some() {
            for (index, node) in program.nodes().iter().enumerate() {
                eprintln!("{index}: {:?}", node.kind);
            }
            for group in linked.groups() {
                for scheme in group.schemes() {
                    eprintln!("linked binder: {:?}", scheme.binder);
                }
            }
        }
    }
    #[test]
    fn linked_lookup_preserves_entry_and_uses_the_actual_tail() {
        const LOOKUP: &str = r#"
type ChildLookup =
    Absent
    | Present(Child)
lookup_child : (Identity, Children) -> ChildLookup
lookup_child (wanted, children) = match children {
    Empty => Absent
    More(entry, tail) => match same_id (child_id entry, wanted) {
        true => Present(entry)
        false => lookup_child (wanted, tail)
    }
}
"#;
        fn inspect(extra: &str) -> Result<(), super::Rejection> {
            let source = format!("{ORDINARY_LEDGER}\n{extra}");
            let (program, linked) = ordinary_ledger(&source);
            let candidate = target_candidate(&program, &linked, "lookup_child");
            let constructor = |name: &str| {
                program
                    .registry()
                    .constructors()
                    .iter()
                    .find(|item| item.spelling == name)
                    .expect("fixture constructor")
                    .id
            };
            let c = super::LookupConstructors {
                root: constructor("Root"),
                work: constructor("Work"),
                child: constructor("Child"),
                empty: constructor("Empty"),
                more: constructor("More"),
                absent: constructor("Absent"),
                present: constructor("Present"),
            };
            let dependencies = super::RemovalDependencies {
                comparison: target_candidate(&program, &linked, "same_id"),
                projection: target_candidate(&program, &linked, "child_id"),
            };
            let mut work = TypeWorkBudget::unbounded();
            let summary = super::check_conditional_lookup(
                &program,
                &linked,
                candidate,
                c,
                dependencies,
                &mut work,
            )?;
            assert!(std::ptr::eq(summary.linked, &linked));
            let graph = &summary.graph;
            assert_eq!(graph.candidate.binder, candidate.binder);
            assert_eq!(graph.constructors.present, c.present);
            assert_eq!(
                graph.dependencies.comparison.binder,
                dependencies.comparison.binder
            );
            assert_eq!(
                graph.dependencies.projection.binder,
                dependencies.projection.binder
            );
            assert!(std::ptr::eq(graph.arena, &program));
            assert_eq!(graph.definition.root, candidate.initializer);
            assert_eq!(graph.definition.body, graph.argument_match);
            assert_eq!(graph.comparison.root, dependencies.comparison.initializer);
            assert_eq!(graph.projection.root, dependencies.projection.initializer);
            assert_eq!(graph.comparison_pair.fields[0], graph.projection_call);
            assert_eq!(graph.absent.constructor, Some(c.absent));
            assert_eq!(graph.present_value.constructor, Some(c.present));
            assert_eq!(graph.present_constructor.body, graph.present_value.root);
            assert_eq!(graph.definition.api, graph.provider_api);
            assert_eq!(graph.comparator_pair.api, graph.provider_api);
            for id in [
                graph.argument_match,
                graph.list_match,
                graph.comparison_match,
                graph.comparison_call,
                graph.projection_call,
                graph.recursive_call,
                graph.present_call,
                graph.recursive_pair.root,
            ] {
                assert!(program.node(id).is_some());
            }
            assert_ne!(graph.wanted, graph.list);
            assert_ne!(graph.entry, graph.tail);
            let (other_program, other_linked) = ordinary_ledger(&source);
            let mut identity_work = TypeWorkBudget::unbounded();
            assert!(matches!(
                super::check_conditional_lookup(
                    &other_program,
                    &other_linked,
                    candidate,
                    c,
                    dependencies,
                    &mut identity_work,
                ),
                Err(super::Rejection::Unsupported)
            ));
            let mut wrong_dependencies = dependencies;
            wrong_dependencies.comparison = dependencies.projection;
            let mut dependency_work = TypeWorkBudget::unbounded();
            assert!(matches!(
                super::check_conditional_lookup(
                    &program,
                    &linked,
                    candidate,
                    c,
                    wrong_dependencies,
                    &mut dependency_work,
                ),
                Err(super::Rejection::Unsupported)
            ));
            let mut wrong = c;
            wrong.present = wrong.absent;
            let mut identity_work = TypeWorkBudget::unbounded();
            assert!(matches!(
                super::check_conditional_lookup(
                    &program,
                    &linked,
                    candidate,
                    wrong,
                    dependencies,
                    &mut identity_work,
                ),
                Err(super::Rejection::Unsupported)
            ));
            let used = work.used();
            let mut exact = TypeWorkBudget::with_limit(used);
            assert!(
                super::check_conditional_lookup(
                    &program,
                    &linked,
                    candidate,
                    c,
                    dependencies,
                    &mut exact
                )
                .is_ok()
            );
            let mut short = TypeWorkBudget::with_limit(used - 1);
            assert!(matches!(
                super::check_conditional_lookup(
                    &program,
                    &linked,
                    candidate,
                    c,
                    dependencies,
                    &mut short
                ),
                Err(super::Rejection::Exhausted)
            ));
            Ok(())
        }
        assert_eq!(inspect(LOOKUP), Ok(()));
        let wrong_hit = LOOKUP.replace("true => Present(entry)", "true => Absent");
        assert_eq!(inspect(&wrong_hit), Err(super::Rejection::Unsupported));
        let wrong_tail = LOOKUP.replace(
            "lookup_child (wanted, tail)",
            "lookup_child (wanted, children)",
        );
        assert_eq!(inspect(&wrong_tail), Err(super::Rejection::Unsupported));
    }
    // Reify only the already authenticated insertion view for the Lean
    // correspondence probe. Full identities are interned once in this view;
    // node numbers are valid only for its exact arena.
    fn insert_lean_fixture(
        graph: &super::InsertGraph<'_>,
        view: &super::InsertModelView<'_>,
        semantics: super::RemovalConstructors,
    ) -> String {
        use std::fmt::Write;
        let node = |id: super::NodeId| id.value();
        let binder = |id| {
            view.binders
                .iter()
                .position(|value| *value == id)
                .expect("projected binder")
        };
        let constructor = |id| {
            view.constructors
                .iter()
                .position(|value| *value == id)
                .expect("projected constructor")
        };
        let nodes = |items: &[super::NodeId]| {
            format!(
                "[{}]",
                items
                    .iter()
                    .map(|id| node(*id).to_string())
                    .collect::<Vec<_>>()
                    .join(", ")
            )
        };
        let optional = |id: Option<crate::types::ConstructorId>| match id {
            Some(id) => format!("(some {})", constructor(id)),
            None => "none".to_owned(),
        };
        let tuple = |v: super::CheckedPersistentTuple<'_>| {
            format!(
                "{{ root := {}, contextBinder := {}, queryNode := {}, unitNode := {}, tupleNode := {}, contextNode := {}, storageNode := {}, storageContextNode := {}, requestNode := {} }}",
                node(v.root),
                binder(v.context_binder),
                node(v.query),
                node(v.unit),
                node(v.tuple),
                node(v.context),
                node(v.storage),
                node(v.storage_context),
                node(v.request)
            )
        };
        let closure = |v: super::CheckedStoredFunction<'_>| {
            format!(
                "{{ root := {}, contextBinder := {}, queryNode := {}, unitNode := {}, closureNode := {}, contextNode := {}, storageNode := {}, storageContextNode := {}, requestNode := {}, parameter := {}, body := {} }}",
                node(v.root),
                binder(v.context_binder),
                node(v.query),
                node(v.unit),
                node(v.closure),
                node(v.context),
                node(v.storage),
                node(v.storage_context),
                node(v.request),
                binder(v.parameter),
                node(v.body)
            )
        };
        let mut out = String::from(
            "import NetworkLedgerCoreInsertBinding\nopen Ash.NetworkLedger.CoreEval Ash.NetworkLedger.CoreValues Ash.NetworkLedger.CoreInsertBinding\n\ndef actualInsertionProgram : Program := fun id => match id with\n",
        );
        for (id, operation) in &view.nodes {
            let rhs = match operation {
                super::InsertModelNode::Unit => ".unit".to_owned(),
                super::InsertModelNode::Variable(b) => format!(".variable {}", binder(*b)),
                super::InsertModelNode::Bind {
                    binder: b,
                    initializer,
                    body,
                } => format!(
                    ".bind {} {} {}",
                    binder(*b),
                    node(*initializer),
                    node(*body)
                ),
                super::InsertModelNode::Apply { function, argument } => {
                    format!(".apply {} {}", node(*function), node(*argument))
                }
                super::InsertModelNode::ArgumentMatch {
                    scrutinee,
                    first,
                    second,
                    body,
                } => format!(
                    ".caseMatch {} [(.tuple [.binder {}, .binder {}], {})]",
                    node(*scrutinee),
                    binder(*first),
                    binder(*second),
                    node(*body)
                ),
                super::InsertModelNode::ListMatch {
                    scrutinee,
                    empty,
                    more,
                    entry,
                    tail,
                    empty_body,
                    more_body,
                } => format!(
                    ".caseMatch {} [(.constructor {} none, {}), (.constructor {} (some (.tuple [.binder {}, .binder {}])), {})]",
                    node(*scrutinee),
                    constructor(*empty),
                    node(*empty_body),
                    constructor(*more),
                    binder(*entry),
                    binder(*tail),
                    node(*more_body)
                ),
                super::InsertModelNode::Query { operand } => format!(".query {}", node(*operand)),
                super::InsertModelNode::Request { fields } => format!(".request {}", fields),
                super::InsertModelNode::Allocate { context, request } => {
                    format!(".allocate {} {}", node(*context), node(*request))
                }
                super::InsertModelNode::Tuple {
                    constructor: tag,
                    context,
                    fields,
                    storage,
                } => format!(
                    ".tuple {} {} {} {}",
                    optional(*tag),
                    node(*context),
                    nodes(fields),
                    node(*storage)
                ),
                super::InsertModelNode::Closure {
                    context,
                    captures,
                    storage,
                    parameter,
                    body,
                } => format!(
                    ".closure {} {} {} {} {}",
                    node(*context),
                    nodes(captures),
                    node(*storage),
                    binder(*parameter),
                    node(*body)
                ),
            };
            writeln!(out, "  | {} => some ({})", node(*id), rhs).unwrap();
        }
        out.push_str("  | _ => none\n\n");
        writeln!(out, "def actualInsertionConstructors : Constructors := {{ root := {}, work := {}, child := {}, empty := {}, more := {}, found := {}, missing := {} }}", constructor(semantics.root_id), constructor(semantics.work_id), constructor(semantics.entry), constructor(semantics.empty), constructor(semantics.more), constructor(semantics.found), constructor(semantics.missing)).unwrap();
        let g = graph;
        writeln!(out, "def actualInsertionCoordinates : InsertCoordinates := {{\n  code := {}\n  context := {}\n  storage := {}\n  captureNodes := {}\n  parameter := {}\n  body := {}\n  argumentScrutinee := {}\n  listBody := {}\n  listScrutinee := {}\n  emptyBody := {}\n  moreBody := {}\n  singletonEntry := {}\n  singletonEmpty := {}\n  prependEntry := {}\n  recursiveCall := {}\n  recursiveFunction := {}\n  recursiveEntry := {}\n  recursiveTail := {}\n  singletonOperand := {}\n  prependOperand := {}\n  newName := {}\n  listName := {}\n  entryName := {}\n  tailName := {}\n  functionName := {}\n  singletonClosure := {}\n  singletonPair := {}\n  singletonValue := {}\n  emptyValue := {}\n  prependClosure := {}\n  prependPair := {}\n  prependValue := {}\n  recursivePair := {}\n}}",
            node(g.definition.closure), node(g.definition.context), node(g.definition.storage), nodes(g.definition.captures), binder(g.definition.parameter), node(g.definition.body),
            node(g.argument_scrutinee), node(g.list_match), node(g.list_scrutinee), node(g.singleton.call), node(g.prepend.call),
            node(g.singleton.arguments.fields[0]), node(g.singleton.arguments.fields[1]), node(g.prepend.arguments.fields[0]), node(g.recursive_call), node(g.recursive_function),
            node(g.recursive_pair.fields[0]), node(g.recursive_pair.fields[1]), node(g.singleton.value.fields[0]), node(g.prepend.value.fields[0]),
            binder(g.new_entry), binder(g.list), binder(g.entry), binder(g.tail), binder(g.candidate.binder),
            closure(g.singleton.closure), tuple(g.singleton.arguments), tuple(g.singleton.value), tuple(g.empty),
            closure(g.prepend.closure), tuple(g.prepend.arguments), tuple(g.prepend.value), tuple(g.recursive_pair)).unwrap();
        out.push_str("\nexample : (checkInsert actualInsertionConstructors actualInsertionProgram actualInsertionCoordinates).isSome = true := by decide\n");
        out
    }

    #[test]
    fn linked_insert_reconstructs_the_original_entry_and_proper_tail() {
        const INSERT: &str = r#"
insert_child : (Child, Children) -> Children
insert_child (fresh, children) = match children {
    Empty => More(fresh, Empty)
    More(entry, tail) => More(entry, insert_child (fresh, tail))
}
"#;
        fn inspect(extra: &str) -> Result<(), super::Rejection> {
            let source = format!("{ORDINARY_LEDGER}\n{extra}");
            let (program, linked) = ordinary_ledger(&source);
            let candidate = target_candidate(&program, &linked, "insert_child");
            let constructor = |name: &str| {
                program
                    .registry()
                    .constructors()
                    .iter()
                    .find(|item| item.spelling == name)
                    .expect("fixture constructor")
                    .id
            };
            let c = super::InsertConstructors {
                entry: constructor("Child"),
                empty: constructor("Empty"),
                more: constructor("More"),
            };
            let semantics = super::RemovalConstructors {
                root_id: constructor("Root"),
                work_id: constructor("Work"),
                entry: c.entry,
                empty: c.empty,
                more: c.more,
                found: constructor("Found"),
                missing: constructor("Missing"),
            };
            let mut work = TypeWorkBudget::unbounded();
            let summary = super::check_conditional_insertion(
                &program, &linked, candidate, c, semantics, &mut work,
            )?;
            assert!(std::ptr::eq(summary.linked, &linked));
            assert_eq!(summary.semantics.more, semantics.more);
            let graph = &summary.graph;
            let view = &summary.model;
            assert!(std::ptr::eq(graph.arena, &program));
            assert_eq!(graph.definition.root, candidate.initializer);
            assert_eq!(graph.candidate.binder, candidate.binder);
            assert_eq!(graph.constructors.more, c.more);
            assert_eq!(graph.definition.body, graph.argument_match);
            assert_eq!(graph.definition.api, graph.provider_api);
            let super::EffectExprKind::Pure(super::PureExprKind::Computation(
                super::PureComputation::Match(arguments),
            )) = &program.node(graph.argument_match).unwrap().kind
            else {
                panic!("checked argument match")
            };
            assert_eq!(arguments.scrutinee(), graph.argument_scrutinee);
            let super::EffectExprKind::Pure(super::PureExprKind::Computation(
                super::PureComputation::Match(list),
            )) = &program.node(graph.list_match).unwrap().kind
            else {
                panic!("checked list match")
            };
            assert_eq!(list.scrutinee(), graph.list_scrutinee);
            let super::EffectExprKind::Pure(super::PureExprKind::Computation(
                super::PureComputation::Apply(recursive),
            )) = &program.node(graph.recursive_call).unwrap().kind
            else {
                panic!("checked recursive call")
            };
            assert_eq!(recursive.function(), graph.recursive_function);
            assert_eq!(graph.empty.constructor, Some(c.empty));
            assert_eq!(graph.singleton.value.constructor, Some(c.more));
            assert_eq!(graph.prepend.value.constructor, Some(c.more));
            assert_eq!(graph.prepend.arguments.fields[1], graph.recursive_call);
            assert_ne!(graph.new_entry, graph.list);
            assert_ne!(graph.entry, graph.tail);
            for id in [
                graph.argument_match,
                graph.list_match,
                graph.recursive_call,
                graph.singleton.call,
                graph.prepend.call,
                graph.recursive_pair.root,
            ] {
                assert!(program.node(id).is_some());
            }
            assert!(std::ptr::eq(view.arena, &program));
            assert_eq!(
                view.nodes
                    .iter()
                    .filter(|(id, _)| *id == graph.candidate.initializer)
                    .count(),
                1
            );
            assert!(view.binders.contains(&graph.candidate.binder));
            assert!(view.constructors.contains(&c.empty));
            assert!(view.constructors.contains(&c.more));
            assert_eq!(
                view.binders.len(),
                view.binders
                    .iter()
                    .collect::<std::collections::HashSet<_>>()
                    .len()
            );
            assert_eq!(
                view.constructors.len(),
                view.constructors
                    .iter()
                    .collect::<std::collections::HashSet<_>>()
                    .len()
            );
            println!(
                "ASH_INSERT_LEAN_BEGIN\n{}ASH_INSERT_LEAN_END",
                insert_lean_fixture(graph, view, semantics)
            );
            let (other_program, other_linked) = ordinary_ledger(&source);
            let mut other_work = TypeWorkBudget::unbounded();
            assert!(matches!(
                super::check_conditional_insertion(
                    &other_program,
                    &other_linked,
                    candidate,
                    c,
                    semantics,
                    &mut other_work,
                ),
                Err(super::Rejection::Unsupported)
            ));
            let mut wrong_semantics = semantics;
            wrong_semantics.more = wrong_semantics.empty;
            let mut identity_work = TypeWorkBudget::unbounded();
            assert!(matches!(
                super::check_conditional_insertion(
                    &program,
                    &linked,
                    candidate,
                    c,
                    wrong_semantics,
                    &mut identity_work,
                ),
                Err(super::Rejection::Unsupported)
            ));
            let used = work.used();
            let mut exact = TypeWorkBudget::with_limit(used);
            assert!(
                super::check_conditional_insertion(
                    &program, &linked, candidate, c, semantics, &mut exact
                )
                .is_ok()
            );
            let mut short = TypeWorkBudget::with_limit(used - 1);
            assert!(matches!(
                super::check_conditional_insertion(
                    &program, &linked, candidate, c, semantics, &mut short
                ),
                Err(super::Rejection::Exhausted)
            ));
            Ok(())
        }
        assert_eq!(inspect(INSERT), Ok(()));
        let wrong_head = INSERT.replace("More(entry, insert_child", "More(fresh, insert_child");
        assert_eq!(inspect(&wrong_head), Err(super::Rejection::Unsupported));
        let wrong_tail = INSERT.replace(
            "insert_child (fresh, tail)",
            "insert_child (fresh, children)",
        );
        assert_eq!(inspect(&wrong_tail), Err(super::Rejection::Unsupported));
    }
}
