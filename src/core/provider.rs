//! Independent lifecycle flow proofs for unpublished provider drafts.
//!
//! Passing this check does not authenticate an entry context or publish code.
//! Ordinary contextual Core validation and complete template-entry validation
//! remain separate prerequisites for a checked executable template table.

use std::collections::{HashMap, HashSet};

use super::{
    CorePattern, CorePatternKind, EffectExprKind, EffectOperation, NodeId, PureComputation,
    PureExprKind, PureValue, UnvalidatedEffectProgram, ValidationError, ValidationReason,
    dialect::StoredNode, effect::EffectOperationFamily,
};
use crate::{
    foreign::{ForeignOperationFact, ForeignResultFact, ForeignStateAccessFact, ForeignStateFact},
    interface::MethodId,
    module::ForeignOperationRole,
    resolved::BinderId,
    types::{
        ConstructorId, EffectInstance, NominalTypeId, OperationId, Type, TypeWorkBudget,
        compare_effect_instances_with_budget, same_type_with_budget,
    },
};

pub(in crate::core) mod copy;
pub(crate) use copy::{
    ProviderCatalogRelocation, ProviderCopiedForest, ProviderCopyContext,
    copy_prepared_provider_forest, copy_provider_forest,
};
mod access;
pub(in crate::core) mod projection;
mod scope;
pub(in crate::core) mod specialization;
pub(crate) use scope::{
    AdmittedProviderScope, ProviderAttachedHandler, ProviderForwardingMethod,
    ProviderLifecycleEntry, ProviderScopeAuthority, ProviderScopeNode, ProviderScopeProtocol,
    derive_provider_scope_protocol, interpret_native_phase_row,
};
pub(crate) use specialization::{
    AdmittedNativeStorageRelation, ProviderCopiedTemplate, ProviderFamilyAdmission,
    ProviderFreshening, ProviderOccurrenceRelocation, ProviderOriginalTemplate,
    ProviderPreparedFamilyOriginal, ProviderScopeAdmission, ProviderSpecializationDictionaryEntry,
    ProviderSpecializationEntries, ProviderSpecializationFamilyEntries,
    ProviderTemplateSubstitution, source_resource_local_identities,
};
pub(in crate::core) use specialization::{
    AuthenticatedProviderSourceCapture, authenticate_admitted_provider_capture,
    authenticate_native_storage_relations, authenticate_prepared_provider_capture,
};
pub(crate) use specialization::{
    DeferredProviderHandlerRows, DeferredProviderRowPosition, LifecycleOriginal,
    ProviderGroupRowsInput, ResolvedProviderHandlerRows, admit_lifecycle_original,
    prepare_group_handler_rows,
};
mod external;
mod handler;
mod row;
pub(in crate::core) use external::ProviderLocalFlow;
#[cfg(test)]
pub(crate) use external::authenticate_plain_externals_with_defining;
#[cfg(test)]
pub(crate) use external::with_declared_layout_checks_for_test;
pub(crate) use external::{
    AuthenticatedProviderExternals, AuthenticatedProviderMethodEvidence,
    AuthenticatedProviderStateAccesses, ProviderExternalOccurrence, ProviderSourceRelation,
    authenticate_staged_externals_with_defining,
};
pub(crate) use external::{DeclaredLayoutMethod, DeclaredLayoutMethods};
#[cfg(test)]
pub(crate) use external::{
    ExternalMutation, check_external_data_type_for_test, external_scheme_for_test,
    introduce_external_for_test, mutate_external_for_test, mutate_method_catalog_for_test,
    mutate_polymorphic_prerequisite_for_test, put_state_access_in_local_callable_for_test,
    redirect_local_source_call_for_test, replace_external_registry_for_test,
    reuse_dictionary_producer_as_call_for_test, source_wrapper_for_test,
    source_wrapper_origin_prefixes_for_test, swap_dictionary_methods_for_test,
    wrong_dictionary_producer_for_test,
};
pub(crate) use external::{RetainedHandlerExternals, RetainedHandlerOrigin};
pub(in crate::core) use external::{
    authenticate_handler_externals, authenticate_handler_staged_externals,
};
pub(crate) use handler::HandlerFragmentDraft;
pub(in crate::core) use handler::RetainedHandlerStateAssociation;
pub(in crate::core) use handler::{
    HandlerAssociations, HandlerFragmentEntry, HandlerGraph, HandlerGraphDraft, HandlerGraphView,
};
#[cfg(test)]
pub(crate) use handler::{HandlerMutation, mutate_handler_for_test};
pub(crate) use row::CaptureInputId;
pub(in crate::core) use row::effect_operation as row_effect_operation;
#[cfg(test)]
pub(in crate::core) use row::owned_contract_links_for_test;
pub(crate) use row::{
    HandlerPendingRows, PendingRowEquality, PendingRowEquation, PendingRowRecomputation,
    PendingRowRecord,
};
pub(in crate::core) use row::{HandlerRowContract, HandlerRowRecipeDraft};
#[cfg(test)]
pub(crate) use row::{
    add_unused_pending_equality_for_test, drop_native_from_pending_demands_for_test,
    erase_pending_function_latent_for_test, has_actual_open_equation_for_test,
    pending_row_inventory_for_test, put_pending_on_unrelated_unit_for_test,
    reconstructed_row_inventory_for_test, row_recipe_links_for_test,
    wrong_pending_recomputation_owner_for_test,
};
pub(in crate::core) use row::{authenticate_definition_contract, authenticate_owned_contract};
mod entry;
pub(crate) use access::DraftStateAssociation;
pub(crate) use access::check_original_state_access_associations;
#[cfg(test)]
pub(crate) use access::check_state_access_associations;
#[cfg(test)]
pub(crate) use access::{AccessMutation, deepen_state_access_argument, mutate_state_access};
#[cfg(test)]
pub(crate) use entry::{EntryMutation, mutate_entry_for_test};
pub(crate) use entry::{LifecycleDefinitionView, LifecycleEntryContext, check_lifecycle_entry};

/// Original source family coordinates. An occurrence or template ordinal alone
/// cannot identify the payload binder authenticated by a family certificate.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) struct ProviderFamilyIdentity {
    pub(crate) definition: crate::resolved::ResourceDefinitionId,
    pub(crate) parameter: crate::types::TypeVariableId,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum LifecyclePhase {
    Acquire,
    Finish,
}

pub(crate) struct LifecycleFlowContext<'a> {
    pub phase: LifecyclePhase,
    pub body: NodeId,
    pub parameter: BinderId,
    pub native: &'a EffectInstance,
    pub state: &'a Type,
}

#[cfg(test)]
#[derive(Clone, Copy)]
pub(crate) enum LifecycleMutation {
    BorrowRole,
    OtherIdentity,
    CallableBody,
}

#[cfg(test)]
pub(crate) fn state_access_for_test(
    program: &UnvalidatedEffectProgram,
) -> Option<(
    &Type,
    &crate::types::EffectRow,
    &super::effect::ProviderStateAccessNode,
)> {
    program.nodes.iter().find_map(|node| match &node.kind {
        EffectExprKind::Operation(EffectOperation::ProviderStateAccess(access)) => {
            Some((&node.ty, &node.effects, access))
        }
        _ => None,
    })
}

#[cfg(test)]
pub(crate) fn mutate_lifecycle_for_test(
    program: &mut UnvalidatedEffectProgram,
    mutation: LifecycleMutation,
) {
    let request_index = program
        .nodes
        .iter()
        .position(|node| {
            matches!(
                node.kind,
                EffectExprKind::Operation(EffectOperation::Request(_))
            )
        })
        .unwrap();
    match mutation {
        LifecycleMutation::BorrowRole => {
            let EffectExprKind::Operation(EffectOperation::Request(request)) =
                &program.nodes[request_index].kind
            else {
                unreachable!()
            };
            let borrowed = program
                .registry
                .effect(request.effect().effect())
                .unwrap()
                .operations
                .iter()
                .find(|operation| {
                    program
                        .registry
                        .foreign_operation(operation.id)
                        .unwrap()
                        .role
                        == ForeignOperationRole::Borrow
                })
                .unwrap()
                .id;
            let EffectExprKind::Operation(EffectOperation::Request(request)) =
                &mut program.nodes[request_index].kind
            else {
                unreachable!()
            };
            request.operation = borrowed;
        }
        LifecycleMutation::OtherIdentity => {
            let EffectExprKind::Operation(EffectOperation::Request(request)) =
                &mut program.nodes[request_index].kind
            else {
                unreachable!()
            };
            request.effect =
                EffectInstance::new(request.effect.effect(), vec![Type::Int].into_boxed_slice());
        }
        LifecycleMutation::CallableBody => {
            let request = NodeId::new(program.arena, u32::try_from(request_index).unwrap());
            let index = program.nodes.iter().position(|node| matches!(&node.kind, EffectExprKind::Pure(PureExprKind::Value(PureValue::Function(function))) if function.body() != program.root && function.parameter().ty().outer_nominal().is_none_or(|id| program.registry.foreign_state(id).is_none()))).unwrap();
            let EffectExprKind::Pure(PureExprKind::Value(PureValue::Function(function))) =
                &program.nodes[index].kind
            else {
                unreachable!()
            };
            let replacement =
                super::function::FunctionNode::new(function.parameter().clone(), request);
            program.nodes[index].kind =
                EffectExprKind::Pure(PureExprKind::Value(PureValue::Function(replacement)));
        }
    }
}

fn invalid(node: NodeId) -> ValidationError {
    ValidationError::new(ValidationReason::ResourceEscape, Some(node))
}
fn resource() -> ValidationError {
    ValidationError::new(ValidationReason::Resource, None)
}
fn charge(work: &mut TypeWorkBudget, cells: usize) -> Result<(), ValidationError> {
    work.charge(cells).map_err(|()| resource())
}
fn node(
    program: &UnvalidatedEffectProgram,
    id: NodeId,
) -> Result<&StoredNode<EffectOperationFamily>, ValidationError> {
    if id.arena() != program.arena {
        return Err(ValidationError::new(ValidationReason::NodeBounds, Some(id)));
    }
    program
        .nodes
        .get(id.index().map_err(|_| invalid(id))?)
        .ok_or_else(|| invalid(id))
}

/// A bounded lookup index, not an authentication certificate. Canonical facts
/// are authenticated by the separate contextual registry validation.
struct NativeFacts<'a> {
    states: HashMap<NominalTypeId, &'a ForeignStateFact>,
    operations: HashMap<OperationId, &'a ForeignOperationFact>,
    access: HashMap<MethodId, &'a ForeignStateAccessFact>,
}

impl<'a> NativeFacts<'a> {
    fn index(
        program: &'a UnvalidatedEffectProgram,
        work: &mut TypeWorkBudget,
    ) -> Result<Self, ValidationError> {
        let mut index = Self {
            states: HashMap::new(),
            operations: HashMap::new(),
            access: HashMap::new(),
        };
        for module in program.registry.foreign_modules() {
            charge(work, 1)?;
            charge(work, module.states.len())?;
            charge(work, module.operations.len())?;
            index
                .states
                .try_reserve(module.states.len())
                .map_err(|_| resource())?;
            index
                .operations
                .try_reserve(module.operations.len())
                .map_err(|_| resource())?;
            for state in &module.states {
                if index.states.insert(state.id, state).is_some() {
                    return Err(ValidationError::new(ValidationReason::Registry, None));
                }
            }
            for operation in &module.operations {
                if index.operations.insert(operation.id, operation).is_some() {
                    return Err(ValidationError::new(ValidationReason::Registry, None));
                }
            }
            if let Some(access) = &module.state_access {
                charge(work, 1)?;
                index.access.try_reserve(1).map_err(|_| resource())?;
                if access.method.interface() != access.interface
                    || index.access.insert(access.method, access).is_some()
                {
                    return Err(ValidationError::new(ValidationReason::Registry, None));
                }
            }
        }
        Ok(index)
    }

    fn state(&self, id: NominalTypeId, work: &mut TypeWorkBudget) -> Result<bool, ValidationError> {
        charge(work, 1)?;
        Ok(self.states.contains_key(&id))
    }

    fn operation(
        &self,
        id: OperationId,
        work: &mut TypeWorkBudget,
    ) -> Result<Option<&'a ForeignOperationFact>, ValidationError> {
        charge(work, 1)?;
        Ok(self.operations.get(&id).copied())
    }
}

fn contains_state(
    native: &NativeFacts<'_>,
    root: &Type,
    work: &mut TypeWorkBudget,
) -> Result<bool, ValidationError> {
    let mut pending = Vec::new();
    pending.try_reserve(1).map_err(|_| resource())?;
    pending.push(root);
    while let Some(ty) = pending.pop() {
        charge(work, 1)?;
        pending.try_reserve(2).map_err(|_| resource())?;
        match ty {
            Type::Nominal(id) => {
                if native.state(*id, work)? {
                    return Ok(true);
                }
            }
            Type::Application(left, right) | Type::Function(left, right) => {
                pending.push(left);
                pending.push(right);
            }
            Type::Tuple(elements) => {
                charge(work, elements.len())?;
                pending
                    .try_reserve(elements.len())
                    .map_err(|_| resource())?;
                pending.extend(elements.iter());
            }
            Type::Forall(_, body) => pending.push(body),
            Type::EffectfulFunction(domain, computation) => {
                pending.push(domain);
                pending.push(computation.value());
                charge(work, computation.effects().known().len())?;
                for effect in computation.effects().known() {
                    schedule_state_owner_types(&mut pending, effect.arguments(), work)?;
                }
                if let Some(tail) = computation.effects().tail() {
                    charge(
                        work,
                        tail.lacks().len().checked_add(1).ok_or_else(resource)?,
                    )?;
                    for effect in tail.lacks() {
                        schedule_state_owner_types(&mut pending, effect.arguments(), work)?;
                    }
                }
            }
            Type::ResourceApply(_, arguments) => {
                schedule_state_owner_types(&mut pending, arguments, work)?;
            }
            _ => {}
        }
    }
    Ok(false)
}

fn schedule_state_owner_types<'a>(
    pending: &mut Vec<&'a Type>,
    arguments: &'a [crate::types::KindedArgument],
    work: &mut TypeWorkBudget,
) -> Result<(), ValidationError> {
    charge(work, arguments.len())?;
    pending
        .try_reserve(arguments.len())
        .map_err(|_| resource())?;
    if arguments
        .iter()
        .all(|argument| matches!(argument, crate::types::KindedArgument::TypeArg(_)))
    {
        for argument in arguments {
            let crate::types::KindedArgument::TypeArg(ty) = argument else {
                unreachable!()
            };
            pending.push(ty);
        }
        return Ok(());
    }
    crate::types::visit_owner_components_with_charge(
        arguments.iter(),
        work,
        |ty, work| {
            work.charge(1)?;
            pending.try_reserve(1).map_err(|_| ())?;
            pending.push(ty);
            Ok(())
        },
        |_, _| Ok(()),
    )
    .map_err(|()| resource())
}

#[cfg(test)]
mod budget_tests {
    use super::*;
    #[test]
    fn provider_state_scan_charges_nullary_row_labels_cumulatively() {
        let native = NativeFacts {
            states: HashMap::new(),
            operations: HashMap::new(),
            access: HashMap::new(),
        };
        let row = |width| {
            Type::EffectfulFunction(
                Box::new(Type::Unit),
                Box::new(crate::types::ComputationType::new(
                    Type::Int,
                    crate::types::EffectRow::closed(
                        (0..width)
                            .map(|ordinal| {
                                EffectInstance::new(
                                    crate::types::EffectId::new(
                                        crate::module::ModuleId::new(77),
                                        ordinal,
                                    ),
                                    Box::new([]),
                                )
                            })
                            .collect(),
                    ),
                )),
            )
        };
        let narrow = row(0);
        let wide = row(64);
        let mut measured = TypeWorkBudget::unbounded();
        assert!(!contains_state(&native, &narrow, &mut measured).unwrap());
        let narrow_cost = measured.used();
        measured = TypeWorkBudget::unbounded();
        assert!(!contains_state(&native, &wide, &mut measured).unwrap());
        let cost = measured.used();
        assert_eq!(cost, narrow_cost + 64);
        for prefix in [0, 13] {
            let mut short = TypeWorkBudget::with_limit(prefix + cost - 1);
            short.charge(prefix).unwrap();
            assert_eq!(
                contains_state(&native, &wide, &mut short)
                    .unwrap_err()
                    .reason(),
                ValidationReason::Resource
            );
            for _ in 0..2 {
                let mut exact = TypeWorkBudget::with_limit(prefix + cost);
                exact.charge(prefix).unwrap();
                assert!(!contains_state(&native, &wide, &mut exact).unwrap());
                assert_eq!(exact.used(), prefix + cost);
            }
        }
    }
}

/// Phase is reconstructed from the exact compiler envelope/body relation.
/// Every nested source function clears it, including an uncalled function.
fn phase_structure(
    program: &UnvalidatedEffectProgram,
    native: &NativeFacts<'_>,
    associations: &access::AssociationCatalog<'_, '_>,
    context: &LifecycleFlowContext<'_>,
    work: &mut TypeWorkBudget,
) -> Result<(), ValidationError> {
    let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::TypeAbstraction(
        abstraction,
    ))) = &node(program, program.root)?.kind
    else {
        return Err(invalid(program.root));
    };
    let EffectExprKind::Pure(PureExprKind::Value(PureValue::Function(function))) =
        &node(program, abstraction.body())?.kind
    else {
        return Err(invalid(abstraction.body()));
    };
    if function.body() != context.body || function.parameter().id() != context.parameter {
        return Err(invalid(context.body));
    }
    if context.phase == LifecyclePhase::Acquire
        && contains_state(native, function.parameter().ty(), work)?
    {
        return Err(invalid(context.body));
    }
    let state_nominal = context
        .state
        .outer_nominal()
        .ok_or_else(|| invalid(context.body))?;
    if !native.state(state_nominal, work)? {
        return Err(invalid(context.body));
    }
    if context.phase == LifecyclePhase::Finish
        && !same_type_with_budget(function.parameter().ty(), context.state, work)
            .map_err(|()| resource())?
    {
        return Err(invalid(context.body));
    }
    let body = node(program, context.body)?;
    let mut report = &body.ty;
    let mut state_argument = None;
    while let Type::Application(function, argument) = report {
        charge(work, 1)?;
        state_argument = Some(argument.as_ref());
        report = function;
    }
    let state_argument = state_argument.ok_or_else(|| invalid(context.body))?;
    if !same_type_with_budget(state_argument, context.state, work).map_err(|()| resource())? {
        return Err(invalid(context.body));
    }
    if body.effects.tail().is_some() {
        return Err(invalid(context.body));
    }
    for effect in body.effects.known() {
        if compare_effect_instances_with_budget(effect, context.native, work)
            .map_err(|()| resource())?
            != std::cmp::Ordering::Equal
        {
            return Err(invalid(context.body));
        }
    }
    let mut visited = HashSet::new();
    let mut pending = Vec::new();
    pending.try_reserve(1).map_err(|_| resource())?;
    pending.push((context.body, true));
    while let Some((id, controlled)) = pending.pop() {
        charge(work, 1)?;
        visited.try_reserve(1).map_err(|_| resource())?;
        if !visited.insert((id, controlled)) {
            continue;
        }
        let stored = node(program, id)?;
        if !controlled && contains_state(native, &stored.ty, work)? {
            return Err(invalid(id));
        }
        let mut children_controlled = controlled;
        match &stored.kind {
            EffectExprKind::Pure(PureExprKind::Value(PureValue::Function(function))) => {
                if contains_state(native, function.parameter().ty(), work)?
                    || contains_state(native, &stored.ty, work)?
                {
                    return Err(invalid(id));
                }
                children_controlled = false;
            }
            EffectExprKind::Operation(EffectOperation::Request(request)) => {
                if let Some(fact) = native.operation(request.operation(), work)? {
                    let role = match context.phase {
                        LifecyclePhase::Acquire => ForeignOperationRole::Acquire,
                        LifecyclePhase::Finish => ForeignOperationRole::Finish,
                    };
                    let state = match &fact.result {
                        ForeignResultFact::Acquire { state, .. }
                        | ForeignResultFact::Finish { state, .. } => Some(*state),
                        _ => None,
                    };
                    if !controlled
                        || fact.role != role
                        || state != context.state.outer_nominal()
                        || compare_effect_instances_with_budget(
                            request.effect(),
                            context.native,
                            work,
                        )
                        .map_err(|()| resource())?
                            != std::cmp::Ordering::Equal
                    {
                        return Err(invalid(id));
                    }
                } else if controlled {
                    return Err(invalid(id));
                }
            }
            EffectExprKind::Operation(EffectOperation::ProviderStateAccess(access)) => {
                if !controlled {
                    return Err(invalid(id));
                }
                associations.check(program, native, id, access, work)?;
            }
            EffectExprKind::Operation(_) => return Err(invalid(id)),
            _ => {}
        }
        charge(work, stored.kind.child_count())?;
        pending
            .try_reserve(stored.kind.child_count())
            .map_err(|_| resource())?;
        for child in 0..stored.kind.child_count() {
            pending.push((
                stored.kind.child_at(child).ok_or_else(|| invalid(id))?,
                children_controlled,
            ));
        }
    }
    Ok(())
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum State {
    Current,
    Acquired(NodeId),
    Retained(NodeId),
    Enclosing(NodeId),
}
#[derive(Debug)]
enum Fact {
    Independent,
    Callable,
    UnprovedExternalCallable {
        target: NodeId,
    },
    DictionaryCallable,
    DeclaredDictionaryCallable {
        source: NodeId,
    },
    ExternalCallable {
        binder: BinderId,
        occurrence: NodeId,
    },
    ConstructorFunction(ConstructorId),
    Data(ConstructorId, Option<usize>),
    Tuple(Box<[usize]>),
    State(State),
    /// Nonowning reference lineage; never a native state or keepalive.
    Reference(State),
    ResourceInput {
        clause: NodeId,
        path: Box<[usize]>,
    },
}
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum CallRequirement {
    Ordinary,
    DictionaryInstallation,
    ExternalInvocation,
}
impl CallRequirement {
    fn fact(self, target: NodeId) -> Fact {
        match self {
            Self::Ordinary => Fact::Callable,
            Self::DictionaryInstallation => Fact::DictionaryCallable,
            Self::ExternalInvocation => Fact::UnprovedExternalCallable { target },
        }
    }
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Finished {
    Consumed(NodeId),
    ConsumedFailure(NodeId),
    Retained(NodeId),
}
#[derive(Clone, Copy, Debug)]
enum Task {
    Evaluate(NodeId),
    Bind(NodeId),
    Apply(NodeId),
    TypeApplication(NodeId),
    Tuple(NodeId, usize),
    Match(NodeId),
    Request(NodeId),
    StateAccess(NodeId),
    Primitive(NodeId, usize),
    ResumeArgument(NodeId),
    HandlerResult(NodeId),
    CleanupAction(NodeId),
}
#[derive(Debug)]
struct Path {
    tasks: Vec<Task>,
    values: Vec<usize>,
    environment: HashMap<BinderId, usize>,
    acquired: Option<NodeId>,
    finished: Option<Finished>,
}
impl Path {
    fn fork(&self, work: &mut TypeWorkBudget) -> Result<Self, ValidationError> {
        charge(
            work,
            self.tasks
                .len()
                .checked_add(self.values.len())
                .and_then(|n| n.checked_add(self.environment.len()))
                .ok_or_else(resource)?,
        )?;
        let mut tasks = Vec::new();
        tasks
            .try_reserve_exact(self.tasks.len())
            .map_err(|_| resource())?;
        tasks.extend_from_slice(&self.tasks);
        let mut values = Vec::new();
        values
            .try_reserve_exact(self.values.len())
            .map_err(|_| resource())?;
        values.extend_from_slice(&self.values);
        let mut environment = HashMap::new();
        environment
            .try_reserve(self.environment.len())
            .map_err(|_| resource())?;
        environment.extend(self.environment.iter().map(|(id, value)| (*id, *value)));
        Ok(Self {
            tasks,
            values,
            environment,
            acquired: self.acquired,
            finished: self.finished,
        })
    }
    fn tasks(&mut self, tasks: &[Task], work: &mut TypeWorkBudget) -> Result<(), ValidationError> {
        charge(work, tasks.len())?;
        self.tasks
            .try_reserve(tasks.len())
            .map_err(|_| resource())?;
        self.tasks.extend_from_slice(tasks);
        Ok(())
    }
    fn value(&mut self, value: usize, work: &mut TypeWorkBudget) -> Result<(), ValidationError> {
        charge(work, 1)?;
        self.values.try_reserve(1).map_err(|_| resource())?;
        self.values.push(value);
        Ok(())
    }
    fn pop(&mut self, id: NodeId) -> Result<usize, ValidationError> {
        self.values.pop().ok_or_else(|| invalid(id))
    }
    fn bind(
        &mut self,
        binder: BinderId,
        value: usize,
        work: &mut TypeWorkBudget,
    ) -> Result<(), ValidationError> {
        charge(work, 1)?;
        self.environment.try_reserve(1).map_err(|_| resource())?;
        self.environment.insert(binder, value);
        Ok(())
    }
}
struct Facts(Vec<Fact>);
impl Facts {
    fn add(&mut self, fact: Fact, work: &mut TypeWorkBudget) -> Result<usize, ValidationError> {
        charge(work, 1)?;
        self.0.try_reserve(1).map_err(|_| resource())?;
        let id = self.0.len();
        self.0.push(fact);
        Ok(id)
    }
    fn independent_data(
        &self,
        root: usize,
        work: &mut TypeWorkBudget,
    ) -> Result<bool, ValidationError> {
        let mut pending = Vec::new();
        charge(work, 1)?;
        pending.try_reserve(1).map_err(|_| resource())?;
        pending.push(root);
        while let Some(id) = pending.pop() {
            charge(work, 1)?;
            match &self.0[id] {
                Fact::Independent | Fact::Data(_, None) => {}
                Fact::Data(_, Some(payload)) => {
                    charge(work, 1)?;
                    pending.try_reserve(1).map_err(|_| resource())?;
                    pending.push(*payload);
                }
                Fact::Tuple(elements) => {
                    charge(work, elements.len())?;
                    pending
                        .try_reserve(elements.len())
                        .map_err(|_| resource())?;
                    pending.extend(elements.iter().copied());
                }
                _ => return Ok(false),
            }
        }
        Ok(true)
    }

    fn family_data(&self, root: usize, work: &mut TypeWorkBudget) -> Result<bool, ValidationError> {
        self.family_data_with_resource_inputs(root, false, work)
    }

    // ResourceInput retains an authenticated original clause/path, not native
    // state. It may be passed to an outward request; it still cannot be resumed
    // as ordinary family data or used as a callable or native storage payload.
    fn outward_family_data(
        &self,
        root: usize,
        work: &mut TypeWorkBudget,
    ) -> Result<bool, ValidationError> {
        self.family_data_with_resource_inputs(root, true, work)
    }

    fn family_data_with_resource_inputs(
        &self,
        root: usize,
        resource_inputs: bool,
        work: &mut TypeWorkBudget,
    ) -> Result<bool, ValidationError> {
        let mut pending = Vec::new();
        charge(work, 1)?;
        pending.try_reserve(1).map_err(|_| resource())?;
        pending.push(root);
        while let Some(id) = pending.pop() {
            charge(work, 1)?;
            match &self.0[id] {
                Fact::Independent | Fact::Reference(_) | Fact::Data(_, None) => {}
                Fact::ResourceInput { .. } if resource_inputs => {}
                Fact::Data(_, Some(payload)) => {
                    charge(work, 1)?;
                    pending.try_reserve(1).map_err(|_| resource())?;
                    pending.push(*payload);
                }
                Fact::Tuple(elements) => {
                    charge(work, elements.len())?;
                    pending
                        .try_reserve(elements.len())
                        .map_err(|_| resource())?;
                    pending.extend(elements.iter().copied());
                }
                _ => return Ok(false),
            }
        }
        Ok(true)
    }

    fn call_requirement(
        &self,
        root: usize,
        work: &mut TypeWorkBudget,
    ) -> Result<CallRequirement, ValidationError> {
        let mut pending = Vec::new();
        let mut requirement = CallRequirement::Ordinary;
        charge(work, 1)?;
        pending.try_reserve(1).map_err(|_| resource())?;
        pending.push(root);
        while let Some(id) = pending.pop() {
            charge(work, 1)?;
            match &self.0[id] {
                Fact::ExternalCallable { .. }
                | Fact::UnprovedExternalCallable { .. }
                | Fact::DeclaredDictionaryCallable { .. } => {
                    return Ok(CallRequirement::ExternalInvocation);
                }
                Fact::DictionaryCallable => {
                    requirement = requirement.max(CallRequirement::DictionaryInstallation)
                }
                Fact::Data(_, Some(payload)) => {
                    charge(work, 1)?;
                    pending.try_reserve(1).map_err(|_| resource())?;
                    pending.push(*payload);
                }
                Fact::Tuple(elements) => {
                    charge(work, elements.len())?;
                    pending
                        .try_reserve(elements.len())
                        .map_err(|_| resource())?;
                    pending.extend(elements.iter().copied());
                }
                _ => {}
            }
        }
        Ok(requirement)
    }

    fn contains_state(
        &self,
        root: usize,
        work: &mut TypeWorkBudget,
    ) -> Result<bool, ValidationError> {
        let mut pending = Vec::new();
        pending.try_reserve(1).map_err(|_| resource())?;
        pending.push(root);
        while let Some(id) = pending.pop() {
            charge(work, 1)?;
            match &self.0[id] {
                Fact::State(_) => return Ok(true),
                Fact::Data(_, Some(payload)) => {
                    pending.try_reserve(1).map_err(|_| resource())?;
                    pending.push(*payload);
                }
                Fact::Tuple(elements) => {
                    charge(work, elements.len())?;
                    pending
                        .try_reserve(elements.len())
                        .map_err(|_| resource())?;
                    pending.extend(elements.iter().copied());
                }
                _ => {}
            }
        }
        Ok(false)
    }
    fn at_path(
        &self,
        root: usize,
        coordinates: &[usize],
        work: &mut TypeWorkBudget,
    ) -> Result<Option<usize>, ValidationError> {
        let mut value = root;
        for coordinate in coordinates {
            charge(work, 1)?;
            let Fact::Tuple(elements) = &self.0[value] else {
                return Ok(None);
            };
            let Some(next) = elements.get(*coordinate) else {
                return Ok(None);
            };
            value = *next;
        }
        Ok(Some(value))
    }
}

#[derive(Clone, Copy, Eq, PartialEq)]
enum MatchDecision {
    No,
    Maybe,
    Yes,
}
fn bind_pattern(
    pattern: &CorePattern,
    value: usize,
    path: &mut Path,
    facts: &Facts,
    work: &mut TypeWorkBudget,
) -> Result<MatchDecision, ValidationError> {
    let mut pending = Vec::new();
    pending.try_reserve(1).map_err(|_| resource())?;
    pending.push((pattern, value));
    let mut decision = MatchDecision::Yes;
    while let Some((pattern, value)) = pending.pop() {
        charge(work, 1)?;
        match (&pattern.kind, &facts.0[value]) {
            (CorePatternKind::Binder(binder), _) => path.bind(binder.id(), value, work)?,
            (CorePatternKind::Wildcard, _) => {}
            (CorePatternKind::Tuple(patterns), Fact::Tuple(elements))
                if patterns.len() == elements.len() =>
            {
                charge(work, patterns.len())?;
                pending
                    .try_reserve(patterns.len())
                    .map_err(|_| resource())?;
                pending.extend(patterns.iter().zip(elements.iter().copied()));
            }
            (
                CorePatternKind::Constructor {
                    constructor,
                    payload,
                },
                Fact::Data(actual, value),
            ) if constructor == actual => match (payload.as_deref(), value) {
                (Some(payload), Some(value)) => {
                    pending.try_reserve(1).map_err(|_| resource())?;
                    pending.push((payload, *value));
                }
                (None, None) => {}
                _ => return Ok(MatchDecision::No),
            },
            (CorePatternKind::Constructor { .. }, Fact::Data(_, _)) => {
                return Ok(MatchDecision::No);
            }
            (_, Fact::Independent) => {
                decision = MatchDecision::Maybe;
                match &pattern.kind {
                    CorePatternKind::Constructor {
                        payload: Some(payload),
                        ..
                    } => {
                        pending.try_reserve(1).map_err(|_| resource())?;
                        pending.push((payload, value));
                    }
                    CorePatternKind::Tuple(elements) => {
                        charge(work, elements.len())?;
                        pending
                            .try_reserve(elements.len())
                            .map_err(|_| resource())?;
                        pending.extend(elements.iter().map(|pattern| (pattern, value)));
                    }
                    _ => {}
                }
            }
            _ => return Ok(MatchDecision::No),
        }
    }
    Ok(decision)
}

fn lifecycle_constructors(
    program: &UnvalidatedEffectProgram,
    native: &NativeFacts<'_>,
    context: &LifecycleFlowContext<'_>,
    report: crate::types::NominalTypeId,
    work: &mut TypeWorkBudget,
) -> Result<Vec<ConstructorId>, ValidationError> {
    let declaration = program
        .registry
        .effect(context.native.effect())
        .ok_or_else(|| invalid(context.body))?;
    charge(work, declaration.operations.len())?;
    for operation in &declaration.operations {
        let fact = native
            .operation(operation.id, work)?
            .ok_or_else(|| invalid(context.body))?;
        let constructors: &[ConstructorId] = match (&fact.result, context.phase) {
            (
                ForeignResultFact::Acquire {
                    state,
                    report: actual,
                    constructors,
                    ..
                },
                LifecyclePhase::Acquire,
            ) if *actual == report && Some(*state) == context.state.outer_nominal() => constructors,
            (
                ForeignResultFact::Finish {
                    state,
                    report: actual,
                    constructors,
                    ..
                },
                LifecyclePhase::Finish,
            ) if *actual == report && Some(*state) == context.state.outer_nominal() => constructors,
            _ => continue,
        };
        charge(work, constructors.len())?;
        let mut result = Vec::new();
        result
            .try_reserve_exact(constructors.len())
            .map_err(|_| resource())?;
        result.extend_from_slice(constructors);
        return Ok(result);
    }
    Err(invalid(context.body))
}

fn terminal(
    program: &UnvalidatedEffectProgram,
    context: &LifecycleFlowContext<'_>,
    path: &mut Path,
    facts: &Facts,
    constructors: &[ConstructorId],
    work: &mut TypeWorkBudget,
) -> Result<(), ValidationError> {
    let value = path.pop(context.body)?;
    if !path.values.is_empty() {
        return Err(invalid(context.body));
    }
    let Fact::Data(constructor, payload) = facts.0[value] else {
        return Err(invalid(context.body));
    };
    charge(work, constructors.len())?;
    let ordinal = constructors
        .iter()
        .position(|id| *id == constructor)
        .ok_or_else(|| invalid(context.body))?;
    match context.phase {
        LifecyclePhase::Acquire => match ordinal {
            0 if payload.is_some_and(|value| matches!(facts.0[value], Fact::State(State::Acquired(call)) if Some(call) == path.acquired)) && path.acquired.is_some() => Ok(()),
            1 if path.acquired.is_none() => {
                let payload = payload.ok_or_else(|| invalid(context.body))?;
                if facts.contains_state(payload, work)? { Err(invalid(context.body)) } else { Ok(()) }
            }
            _ => Err(invalid(context.body)),
        },
        LifecyclePhase::Finish => match (ordinal, path.finished) {
            (0, Some(Finished::Consumed(_))) if payload.is_none() => Ok(()),
            (1, Some(Finished::ConsumedFailure(_))) => {
                let payload = payload.ok_or_else(|| invalid(context.body))?;
                if facts.contains_state(payload, work)? { Err(invalid(context.body)) } else { Ok(()) }
            }
            (2, Some(Finished::Retained(call))) => {
                let payload = payload.ok_or_else(|| invalid(context.body))?;
                let Fact::Tuple(elements) = &facts.0[payload] else { return Err(invalid(context.body)); };
                if elements.len() == 2 && matches!(facts.0[elements[0]], Fact::State(State::Retained(actual)) if actual == call) && !facts.contains_state(elements[1], work)? { Ok(()) } else { Err(invalid(context.body)) }
            }
            _ => Err(invalid(context.body)),
        },
    }?;
    let _ = program;
    Ok(())
}

fn require_current_state_lineage(
    facts: &Facts,
    operand: usize,
    lineages: &[crate::foreign::ForeignStateOperandFact],
    id: NodeId,
    work: &mut TypeWorkBudget,
) -> Result<(), ValidationError> {
    charge(work, lineages.len())?;
    for state in lineages {
        let value = facts
            .at_path(operand, &state.path, work)?
            .ok_or_else(|| invalid(id))?;
        if !matches!(facts.0[value], Fact::State(State::Current)) {
            return Err(invalid(id));
        }
    }
    Ok(())
}

#[cfg(test)]
pub(crate) fn check_enclosing_finish_rejection_for_test(
    program: &UnvalidatedEffectProgram,
    work: &mut TypeWorkBudget,
) -> Result<(), ValidationError> {
    let (state, _, _) = state_access_for_test(program).unwrap();
    let native = NativeFacts::index(program, work)?;
    let finish = native
        .operations
        .values()
        .find(|operation| {
            matches!(operation.result,
        ForeignResultFact::Finish { state: family, .. } if Some(family) == state.outer_nominal())
        })
        .unwrap();
    let mut facts = Facts(Vec::new());
    let current = facts.add(Fact::State(State::Current), work)?;
    let enclosing = facts.add(Fact::State(State::Enclosing(program.root)), work)?;
    // The state type is identical. Its native nominal and report codec cannot
    // turn the enclosing activation into the current finisher capability.
    require_current_state_lineage(&facts, current, &finish.state_lineage, program.root, work)?;
    assert!(
        require_current_state_lineage(&facts, enclosing, &finish.state_lineage, program.root, work)
            .is_err()
    );
    Ok(())
}

/// Tracks actual registered outcomes through ordinary bindings and total
/// matches. State aliases share a guard lineage; they never clone ownership.
/// Branching and environment transfer consume one cumulative work budget.
pub(crate) fn check_lifecycle_flow_with_associations(
    program: &UnvalidatedEffectProgram,
    context: &LifecycleFlowContext<'_>,
    associations: &[DraftStateAssociation<'_>],
    work: &mut TypeWorkBudget,
) -> Result<(), ValidationError> {
    check_lifecycle_flow_context(program, context, associations, None, work)
}

pub(crate) fn check_lifecycle_flow_with_externals(
    program: &UnvalidatedEffectProgram,
    context: &LifecycleFlowContext<'_>,
    externals: &AuthenticatedProviderExternals<'_>,
    associations: &[DraftStateAssociation<'_>],
    work: &mut TypeWorkBudget,
) -> Result<(), ValidationError> {
    check_lifecycle_flow_context(program, context, associations, Some(externals), work)
}

// The interim private entry retains dependencies whose invocation needs a
// separate proof. It does not yet execute or authenticate local source bodies.
fn callable_requirement(
    program: &UnvalidatedEffectProgram,
    root: NodeId,
    environment: &HashMap<BinderId, usize>,
    facts: &Facts,
    externals: Option<&AuthenticatedProviderExternals<'_>>,
    work: &mut TypeWorkBudget,
) -> Result<CallRequirement, ValidationError> {
    let Some(externals) = externals else {
        return Ok(CallRequirement::Ordinary);
    };
    let mut requirement = CallRequirement::Ordinary;
    let mut pending = Vec::new();
    let mut seen = HashSet::new();
    charge(work, 1)?;
    pending.try_reserve(1).map_err(|_| resource())?;
    pending.push(root);
    while let Some(id) = pending.pop() {
        charge(work, 2)?;
        seen.try_reserve(1).map_err(|_| resource())?;
        if !seen.insert(id) {
            continue;
        }
        let kind = &node(program, id)?.kind;
        if let EffectExprKind::Pure(PureExprKind::Variable(variable)) = kind {
            // Two authenticated membership lookups and one lexical lookup.
            charge(work, 3)?;
            if externals.contains(variable.binder()) {
                return Ok(CallRequirement::ExternalInvocation);
            }
            if externals.dictionary_method(program, id, work)? {
                return Ok(CallRequirement::ExternalInvocation);
            }
            if externals.dictionary_variable(program, id) {
                requirement = requirement.max(CallRequirement::DictionaryInstallation);
            }
            if let Some(value) = environment.get(&variable.binder()) {
                requirement = requirement.max(facts.call_requirement(*value, work)?);
                if requirement == CallRequirement::ExternalInvocation {
                    return Ok(requirement);
                }
            }
        }
        charge(work, kind.child_count())?;
        pending
            .try_reserve(kind.child_count())
            .map_err(|_| resource())?;
        for ordinal in 0..kind.child_count() {
            pending.push(kind.child_at(ordinal).ok_or_else(|| invalid(id))?);
        }
    }
    Ok(requirement)
}

fn check_lifecycle_flow_context(
    program: &UnvalidatedEffectProgram,
    context: &LifecycleFlowContext<'_>,
    associations: &[DraftStateAssociation<'_>],
    externals: Option<&AuthenticatedProviderExternals<'_>>,
    work: &mut TypeWorkBudget,
) -> Result<(), ValidationError> {
    let native = NativeFacts::index(program, work)?;
    let associations =
        access::AssociationCatalog::index(associations, &native, program.root, work)?;
    phase_structure(program, &native, &associations, context, work)?;
    let report = node(program, context.body)?
        .ty
        .outer_nominal()
        .ok_or_else(|| invalid(context.body))?;
    let constructors = lifecycle_constructors(program, &native, context, report, work)?;
    let mut facts = Facts(Vec::new());
    let independent = facts.add(Fact::Independent, work)?;
    let input = match context.phase {
        LifecyclePhase::Acquire => independent,
        LifecyclePhase::Finish => facts.add(Fact::State(State::Current), work)?,
    };
    let mut path = Path {
        tasks: Vec::new(),
        values: Vec::new(),
        environment: HashMap::new(),
        acquired: None,
        finished: None,
    };
    path.bind(context.parameter, input, work)?;
    path.tasks(&[Task::Evaluate(context.body)], work)?;
    let mut pending = Vec::new();
    pending.try_reserve(1).map_err(|_| resource())?;
    pending.push(path);
    execute_flow_paths(
        program,
        &native,
        &associations,
        externals,
        FlowMode::Lifecycle(context, &constructors),
        &mut facts,
        independent,
        pending,
        None,
        work,
    )
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(in crate::core) enum HandlerNativeStorageResult {
    Store {
        allocated: ConstructorId,
        refused: ConstructorId,
    },
    Load,
}

/// A relation emitted only after the original handler flow has checked the
/// actual State and Ref operand paths. Copied requests require reauthentication.
pub(in crate::core) struct HandlerNativeStorageRelation {
    request: NodeId,
    operation: OperationId,
    effect: EffectInstance,
    owner: crate::types::TypeVariableId,
    family: ProviderFamilyIdentity,
    result: HandlerNativeStorageResult,
}
impl HandlerNativeStorageRelation {
    pub(in crate::core) fn request(&self) -> NodeId {
        self.request
    }
    pub(in crate::core) fn operation(&self) -> OperationId {
        self.operation
    }
    pub(in crate::core) fn effect(&self) -> &EffectInstance {
        &self.effect
    }
    pub(in crate::core) fn owner(&self) -> crate::types::TypeVariableId {
        self.owner
    }
    pub(in crate::core) fn family(&self) -> ProviderFamilyIdentity {
        self.family
    }
    pub(in crate::core) fn result(&self) -> HandlerNativeStorageResult {
        self.result
    }
}

fn retain_handler_storage_relation(
    relations: &mut Option<&mut Vec<HandlerNativeStorageRelation>>,
    entry: &HandlerFragmentEntry<'_>,
    id: NodeId,
    request: &super::RequestNode,
    result: HandlerNativeStorageResult,
    work: &mut TypeWorkBudget,
) -> Result<(), ValidationError> {
    let Some(relations) = relations.as_deref_mut() else {
        return Ok(());
    };
    charge(work, relations.len().checked_add(1).ok_or_else(resource)?)?;
    if relations.iter().any(|relation| relation.request == id) {
        return Ok(());
    }
    let family = entry.family_identity().ok_or_else(|| invalid(id))?;
    let owner = entry
        .definition
        .parameters
        .first()
        .ok_or_else(|| invalid(id))?
        .id;
    let effect = crate::types::clone_effect_instance_with_budget(request.effect(), work)
        .map_err(|()| resource())?;
    relations.try_reserve(1).map_err(|_| resource())?;
    relations.push(HandlerNativeStorageRelation {
        request: id,
        operation: request.operation(),
        effect,
        owner,
        family,
        result,
    });
    Ok(())
}

pub(in crate::core) fn check_handler_native_storage_relations(
    entry: &HandlerFragmentEntry<'_>,
    associations: &[DraftStateAssociation<'_>],
    externals: Option<&AuthenticatedProviderExternals<'_>>,
    work: &mut TypeWorkBudget,
) -> Result<Box<[HandlerNativeStorageRelation]>, ValidationError> {
    let program = &entry.draft.program;
    let native = NativeFacts::index(program, work)?;
    let associations =
        access::AssociationCatalog::index(associations, &native, program.root, work)?;
    let mut seen = HashSet::new();
    let mut pending_nodes = Vec::new();
    charge(work, entry.roots().len())?;
    pending_nodes
        .try_reserve(entry.roots().len())
        .map_err(|_| resource())?;
    pending_nodes.extend(entry.roots().iter().copied().map(|root| (root, true)));
    while let Some((id, controlled)) = pending_nodes.pop() {
        charge(work, 1)?;
        seen.try_reserve(1).map_err(|_| resource())?;
        if !seen.insert((id, controlled)) {
            continue;
        }
        let stored = node(program, id)?;
        if !controlled && contains_state(&native, &stored.ty, work)? {
            return Err(invalid(id));
        }
        let children_controlled = match &stored.kind {
            EffectExprKind::Pure(PureExprKind::Value(PureValue::Function(function))) => {
                if contains_state(&native, function.parameter().ty(), work)?
                    || contains_state(&native, &stored.ty, work)?
                {
                    return Err(invalid(id));
                }
                false
            }
            EffectExprKind::Operation(EffectOperation::Request(request)) => {
                if let Some(operation) = native.operation(request.operation(), work)?
                    && (!controlled
                        || operation.role != ForeignOperationRole::Borrow
                        || !(matches!(operation.result, ForeignResultFact::Independent)
                            || (entry.family_identity().is_some()
                                && matches!(operation.result,
                                ForeignResultFact::Store { storage } | ForeignResultFact::Load { storage }
                                    if storage == entry.interpreted().effect())))
                        || compare_effect_instances_with_budget(
                            request.effect(),
                            entry.interpreted(),
                            work,
                        )
                        .map_err(|()| resource())?
                            != std::cmp::Ordering::Equal)
                {
                    return Err(invalid(id));
                }
                controlled
            }
            EffectExprKind::Operation(EffectOperation::ProviderStateAccess(access)) => {
                if !controlled {
                    return Err(invalid(id));
                }
                associations.check(program, &native, id, access, work)?;
                controlled
            }
            EffectExprKind::Operation(
                EffectOperation::Resume(_)
                | EffectOperation::Handler(_)
                | EffectOperation::Cleanup(_),
            ) => controlled,
            EffectExprKind::Operation(EffectOperation::Discard(_)) => {
                let Some(recipe) = entry.row_recipe else {
                    return Err(invalid(id));
                };
                if !recipe.discard_port(entry, id, work)? {
                    return Err(invalid(id));
                }
                controlled
            }
            EffectExprKind::Operation(_) => return Err(invalid(id)),
            _ => controlled,
        };
        charge(work, stored.kind.child_count())?;
        pending_nodes
            .try_reserve(stored.kind.child_count())
            .map_err(|_| resource())?;
        for index in 0..stored.kind.child_count() {
            pending_nodes.push((
                stored.kind.child_at(index).ok_or_else(|| invalid(id))?,
                children_controlled,
            ));
        }
    }
    let mut facts = Facts(Vec::new());
    let independent = facts.add(Fact::Independent, work)?;
    let current = facts.add(Fact::State(State::Current), work)?;
    let mut paths = Vec::new();
    charge(work, entry.draft.clauses.len())?;
    paths
        .try_reserve_exact(entry.draft.clauses.len())
        .map_err(|_| resource())?;
    for clause in &entry.draft.clauses {
        let mut path = Path {
            tasks: Vec::new(),
            values: Vec::new(),
            environment: HashMap::new(),
            acquired: None,
            finished: None,
        };
        path.bind(entry.draft.state.id(), current, work)?;
        let input = handler_domain_fact(entry, clause.body(), &mut facts, independent, work)?;
        bind_pattern(clause.pattern(), input, &mut path, &facts, work)?;
        path.tasks(&[Task::Evaluate(clause.body())], work)?;
        paths.push(path);
    }
    let mut relations = Vec::new();
    execute_flow_paths(
        program,
        &native,
        &associations,
        externals,
        FlowMode::Handler(entry),
        &mut facts,
        independent,
        paths,
        Some(&mut relations),
        work,
    )?;
    Ok(relations.into_boxed_slice())
}

fn handler_domain_fact(
    entry: &HandlerFragmentEntry<'_>,
    root: NodeId,
    facts: &mut Facts,
    independent: usize,
    work: &mut TypeWorkBudget,
) -> Result<usize, ValidationError> {
    enum Task<'a> {
        Enter(&'a Type, Vec<usize>),
        Tuple(usize),
    }
    let clause = entry.clause_at(root).ok_or_else(|| invalid(root))?;
    let mut pending = Vec::new();
    charge(work, 1)?;
    pending.try_reserve(1).map_err(|_| resource())?;
    pending.push(Task::Enter(&clause.pattern().ty, Vec::new()));
    let mut values = Vec::new();
    while let Some(task) = pending.pop() {
        charge(work, 1)?;
        match task {
            Task::Enter(Type::Tuple(elements), path) => {
                charge(work, elements.len().checked_add(1).ok_or_else(resource)?)?;
                pending
                    .try_reserve(elements.len() + 1)
                    .map_err(|_| resource())?;
                pending.push(Task::Tuple(elements.len()));
                for (index, element) in elements.iter().enumerate().rev() {
                    charge(work, path.len().checked_add(1).ok_or_else(resource)?)?;
                    let mut coordinates = Vec::new();
                    coordinates
                        .try_reserve_exact(path.len() + 1)
                        .map_err(|_| resource())?;
                    coordinates.extend_from_slice(&path);
                    coordinates.push(index);
                    pending.push(Task::Enter(element, coordinates));
                }
            }
            Task::Enter(ty, path) => {
                let family = ty.outer_nominal();
                charge(work, entry.module.resources().len())?;
                let is_resource = family.is_some_and(|family| {
                    entry
                        .module
                        .resources()
                        .iter()
                        .any(|definition| definition.family == family)
                });
                let storage = entry.family_identity().and_then(|_| {
                    entry
                        .canonical
                        .foreign_storage(entry.interpreted().effect())
                });
                let reference = if let Some(storage) = storage {
                    if family == Some(storage.reference()) {
                        let arguments = handler::type_arguments(ty, work)?;
                        let payload = entry
                            .family_identity()
                            .ok_or_else(|| invalid(root))?
                            .parameter;
                        if !matches!(arguments.get(storage.reference_owner_parameter()), Some(Type::Variable(owner)) if *owner == entry.definition.parameters[0].id)
                            || !matches!(arguments.get(storage.reference_payload_parameter()), Some(Type::Variable(actual)) if *actual == payload)
                        {
                            return Err(invalid(root));
                        }
                        true
                    } else {
                        false
                    }
                } else {
                    false
                };
                let value = if reference {
                    facts.add(Fact::Reference(State::Current), work)?
                } else if is_resource {
                    facts.add(
                        Fact::ResourceInput {
                            clause: root,
                            path: path.into_boxed_slice(),
                        },
                        work,
                    )?
                } else {
                    independent
                };
                charge(work, 1)?;
                values.try_reserve(1).map_err(|_| resource())?;
                values.push(value);
            }
            Task::Tuple(count) => {
                if count > values.len() {
                    return Err(invalid(root));
                }
                charge(work, count)?;
                let mut fields = Vec::new();
                fields.try_reserve_exact(count).map_err(|_| resource())?;
                fields.extend(values.drain(values.len() - count..));
                let value = facts.add(Fact::Tuple(fields.into_boxed_slice()), work)?;
                charge(work, 1)?;
                values.try_reserve(1).map_err(|_| resource())?;
                values.push(value);
            }
        }
    }
    if values.len() != 1 {
        return Err(invalid(root));
    }
    values.pop().ok_or_else(|| invalid(root))
}

#[derive(Clone, Copy)]
enum FlowMode<'a> {
    Lifecycle(&'a LifecycleFlowContext<'a>, &'a [ConstructorId]),
    Handler(&'a HandlerFragmentEntry<'a>),
}

#[expect(
    clippy::too_many_arguments,
    reason = "the shared flow driver borrows authenticated phase, native, association and external facts without duplicating their carriers"
)]
fn execute_flow_paths(
    program: &UnvalidatedEffectProgram,
    native: &NativeFacts<'_>,
    associations: &access::AssociationCatalog<'_, '_>,
    externals: Option<&AuthenticatedProviderExternals<'_>>,
    mode: FlowMode<'_>,
    facts: &mut Facts,
    independent: usize,
    mut pending: Vec<Path>,
    mut relations: Option<&mut Vec<HandlerNativeStorageRelation>>,
    work: &mut TypeWorkBudget,
) -> Result<(), ValidationError> {
    while let Some(mut path) = pending.pop() {
        while let Some(task) = path.tasks.pop() {
            charge(work, 1)?;
            match task {
                Task::Evaluate(id) => match &node(program, id)?.kind {
                    EffectExprKind::Pure(PureExprKind::Variable(variable)) => {
                        let value = if let Some(value) = path.environment.get(&variable.binder()) {
                            *value
                        } else if externals
                            .is_some_and(|externals| externals.contains(variable.binder()))
                        {
                            facts.add(
                                Fact::ExternalCallable {
                                    binder: variable.binder(),
                                    occurrence: id,
                                },
                                work,
                            )?
                        } else if externals
                            .is_some_and(|externals| externals.dictionary_variable(program, id))
                        {
                            let fact = if externals
                                .ok_or_else(|| invalid(id))?
                                .dictionary_method(program, id, work)?
                            {
                                Fact::DeclaredDictionaryCallable { source: id }
                            } else {
                                Fact::DictionaryCallable
                            };
                            facts.add(fact, work)?
                        } else {
                            return Err(invalid(id));
                        };
                        if matches!(facts.0[value], Fact::State(State::Current))
                            && path.finished.is_some()
                        {
                            return Err(invalid(id));
                        }
                        path.value(value, work)?;
                    }
                    EffectExprKind::Pure(PureExprKind::Value(PureValue::Constructor(
                        constructor,
                    ))) => {
                        let declaration = program
                            .registry
                            .constructor(constructor.constructor())
                            .ok_or_else(|| invalid(id))?;
                        let value = facts.add(
                            if declaration.payload.is_some() {
                                Fact::ConstructorFunction(constructor.constructor())
                            } else {
                                Fact::Data(constructor.constructor(), None)
                            },
                            work,
                        )?;
                        path.value(value, work)?;
                    }
                    EffectExprKind::Pure(PureExprKind::Value(PureValue::Function(function))) => {
                        let requirement = callable_requirement(
                            program,
                            function.body(),
                            &path.environment,
                            facts,
                            externals,
                            work,
                        )?;
                        let value = facts.add(requirement.fact(id), work)?;
                        path.value(value, work)?;
                    }
                    EffectExprKind::Pure(PureExprKind::Value(_)) => {
                        path.value(independent, work)?
                    }
                    EffectExprKind::Pure(PureExprKind::Computation(computation)) => {
                        match computation {
                            PureComputation::Bind(binding) => path.tasks(
                                &[Task::Bind(id), Task::Evaluate(binding.initializer())],
                                work,
                            )?,
                            PureComputation::Apply(application) => path.tasks(
                                &[
                                    Task::Apply(id),
                                    Task::Evaluate(application.argument()),
                                    Task::Evaluate(application.function()),
                                ],
                                work,
                            )?,
                            PureComputation::Tuple(tuple) => {
                                path.tasks(&[Task::Tuple(id, tuple.elements().len())], work)?;
                                for element in tuple.elements().iter().rev() {
                                    path.tasks(&[Task::Evaluate(*element)], work)?;
                                }
                            }
                            PureComputation::Match(matched) => path.tasks(
                                &[Task::Match(id), Task::Evaluate(matched.scrutinee())],
                                work,
                            )?,
                            PureComputation::TypeApplication(application) => path.tasks(
                                &[
                                    Task::TypeApplication(id),
                                    Task::Evaluate(application.function()),
                                ],
                                work,
                            )?,
                            PureComputation::TypeAbstraction(abstraction) => {
                                path.tasks(&[Task::Evaluate(abstraction.body())], work)?
                            }
                            PureComputation::NewtypeConversion(conversion) => {
                                if contains_state(
                                    native,
                                    &node(program, conversion.child())?.ty,
                                    work,
                                )? {
                                    return Err(invalid(id));
                                }
                                path.tasks(&[Task::Evaluate(conversion.child())], work)?;
                            }
                            PureComputation::LocalNominalScope(scope) => {
                                path.tasks(&[Task::Evaluate(scope.body())], work)?
                            }
                            PureComputation::RecursiveBind(recursive) => {
                                let mut requirement = CallRequirement::Ordinary;
                                for member in recursive.members() {
                                    requirement = requirement.max(callable_requirement(
                                        program,
                                        member.initializer(),
                                        &path.environment,
                                        facts,
                                        externals,
                                        work,
                                    )?);
                                }
                                for member in recursive.members() {
                                    let value =
                                        facts.add(requirement.fact(member.initializer()), work)?;
                                    path.bind(member.binder().id(), value, work)?;
                                }
                                path.tasks(&[Task::Evaluate(recursive.body())], work)?;
                            }
                            PureComputation::Primitive(_) => {
                                let kind = &node(program, id)?.kind;
                                path.tasks(&[Task::Primitive(id, kind.child_count())], work)?;
                                for ordinal in (0..kind.child_count()).rev() {
                                    path.tasks(
                                        &[Task::Evaluate(
                                            kind.child_at(ordinal).ok_or_else(|| invalid(id))?,
                                        )],
                                        work,
                                    )?;
                                }
                            }
                        }
                    }
                    EffectExprKind::Operation(EffectOperation::Request(request)) => path.tasks(
                        &[Task::Request(id), Task::Evaluate(request.operand())],
                        work,
                    )?,
                    EffectExprKind::Operation(EffectOperation::ProviderStateAccess(access)) => {
                        path.tasks(
                            &[Task::StateAccess(id), Task::Evaluate(access.operand())],
                            work,
                        )?;
                    }
                    EffectExprKind::Operation(EffectOperation::Resume(resume))
                        if matches!(mode, FlowMode::Handler(_)) =>
                    {
                        path.tasks(
                            &[Task::ResumeArgument(id), Task::Evaluate(resume.value())],
                            work,
                        )?;
                    }
                    EffectExprKind::Operation(EffectOperation::Discard(_))
                        if matches!(mode, FlowMode::Handler(_)) =>
                    {
                        let FlowMode::Handler(entry) = mode else {
                            return Err(invalid(id));
                        };
                        let Some(recipe) = entry.row_recipe else {
                            return Err(invalid(id));
                        };
                        if !recipe.discard_port(entry, id, work)? {
                            return Err(invalid(id));
                        }
                        // Unit is a data-flow fact only. The actual completion
                        // and captured segment remain in the conditional graph.
                        path.value(independent, work)?;
                    }
                    EffectExprKind::Operation(EffectOperation::Cleanup(scope))
                        if matches!(mode, FlowMode::Handler(_)) =>
                    {
                        // These tasks check provenance, not execution order or
                        // close/completion. The capture graph retains both.
                        path.tasks(
                            &[Task::CleanupAction(id), Task::Evaluate(scope.action)],
                            work,
                        )?;
                    }
                    EffectExprKind::Operation(EffectOperation::Handler(handler))
                        if matches!(mode, FlowMode::Handler(_)) =>
                    {
                        charge(work, handler.clauses().len())?;
                        pending
                            .try_reserve(handler.clauses().len())
                            .map_err(|_| resource())?;
                        for clause in handler.clauses() {
                            let mut branch = path.fork(work)?;
                            bind_pattern(clause.pattern(), independent, &mut branch, facts, work)?;
                            branch.tasks(
                                &[Task::HandlerResult(id), Task::Evaluate(clause.body())],
                                work,
                            )?;
                            pending.push(branch);
                        }
                        path.tasks(
                            &[Task::HandlerResult(id), Task::Evaluate(handler.body())],
                            work,
                        )?;
                    }
                    EffectExprKind::Operation(_) => return Err(invalid(id)),
                },
                Task::Bind(id) => {
                    let value = path.pop(id)?;
                    if matches!(&facts.0[value], Fact::Tuple(_))
                        && facts.contains_state(value, work)?
                    {
                        return Err(invalid(id));
                    }
                    let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Bind(
                        binding,
                    ))) = &node(program, id)?.kind
                    else {
                        return Err(invalid(id));
                    };
                    path.bind(binding.binder().id(), value, work)?;
                    path.tasks(&[Task::Evaluate(binding.body())], work)?;
                }
                Task::TypeApplication(id) => {
                    let value = path.pop(id)?;
                    let value = if let Fact::ExternalCallable { binder, .. } = facts.0[value] {
                        facts.add(
                            Fact::ExternalCallable {
                                binder,
                                occurrence: id,
                            },
                            work,
                        )?
                    } else {
                        value
                    };
                    path.value(value, work)?;
                }
                Task::Apply(id) => {
                    let argument = path.pop(id)?;
                    let function = path.pop(id)?;
                    let value = if let Fact::ConstructorFunction(constructor) = facts.0[function] {
                        if facts.contains_state(argument, work)? {
                            let owner = program
                                .registry
                                .constructor(constructor)
                                .ok_or_else(|| invalid(id))?
                                .owner;
                            let FlowMode::Lifecycle(context, _) = mode else {
                                return Err(invalid(id));
                            };
                            lifecycle_constructors(program, native, context, owner, work)?;
                        }
                        facts.add(Fact::Data(constructor, Some(argument)), work)?
                    } else if let Fact::UnprovedExternalCallable { target } = facts.0[function] {
                        if !facts.independent_data(argument, work)? {
                            return Err(invalid(id));
                        }
                        externals
                            .ok_or_else(|| invalid(id))?
                            .independent_local_call(
                                program,
                                id,
                                target,
                                &path.environment,
                                facts,
                                work,
                            )?;
                        independent
                    } else if let Fact::DeclaredDictionaryCallable { source } = facts.0[function] {
                        if !facts.independent_data(argument, work)? {
                            return Err(invalid(id));
                        }
                        externals
                            .ok_or_else(|| invalid(id))?
                            .dictionary_invocation(program, source, id, work)?;
                        independent
                    } else if matches!(facts.0[function], Fact::DictionaryCallable) {
                        if !externals
                            .ok_or_else(|| invalid(id))?
                            .dictionary_installation(program, id, work)?
                        {
                            return Err(invalid(id));
                        }
                        facts.add(Fact::DictionaryCallable, work)?
                    } else if let Fact::ExternalCallable { binder, occurrence } = facts.0[function]
                    {
                        if externals.is_some_and(|externals| {
                            externals.dictionary_application(program, id, binder, occurrence)
                        }) {
                            let value = facts.add(
                                Fact::ExternalCallable {
                                    binder,
                                    occurrence: id,
                                },
                                work,
                            )?;
                            path.value(value, work)?;
                            continue;
                        }
                        if !facts.independent_data(argument, work)? {
                            return Err(invalid(id));
                        }
                        externals
                            .ok_or_else(|| invalid(id))?
                            // Only an admitted handler original may call an ordinary
                            // helper with an internally owned scope. Lifecycle
                            // source calls retain their bounded pure bridge.
                            .independent_call(
                                program,
                                id,
                                binder,
                                occurrence,
                                matches!(mode, FlowMode::Handler(_)),
                                work,
                            )?;
                        independent
                    } else {
                        let EffectExprKind::Pure(PureExprKind::Computation(
                            PureComputation::Apply(application),
                        )) = &node(program, id)?.kind
                        else {
                            return Err(invalid(id));
                        };
                        if facts.call_requirement(argument, work)? != CallRequirement::Ordinary
                            || facts.contains_state(argument, work)?
                            || contains_state(
                                native,
                                &node(program, application.argument())?.ty,
                                work,
                            )?
                            || contains_state(native, &node(program, id)?.ty, work)?
                        {
                            return Err(invalid(id));
                        }
                        independent
                    };
                    path.value(value, work)?;
                }
                Task::Tuple(id, count) => {
                    if count > path.values.len() {
                        return Err(invalid(id));
                    }
                    charge(work, count)?;
                    let mut elements = Vec::new();
                    elements.try_reserve_exact(count).map_err(|_| resource())?;
                    elements.extend(path.values.drain(path.values.len() - count..));
                    let value = facts.add(Fact::Tuple(elements.into_boxed_slice()), work)?;
                    path.value(value, work)?;
                }
                Task::Primitive(id, count) => {
                    for _ in 0..count {
                        let value = path.pop(id)?;
                        if facts.contains_state(value, work)? {
                            return Err(invalid(id));
                        }
                    }
                    path.value(independent, work)?;
                }
                Task::Match(id) => {
                    let scrutinee = path.pop(id)?;
                    let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Match(
                        matched,
                    ))) = &node(program, id)?.kind
                    else {
                        return Err(invalid(id));
                    };
                    let mut branches = Vec::new();
                    charge(work, matched.arms().len())?;
                    branches
                        .try_reserve(matched.arms().len())
                        .map_err(|_| resource())?;
                    for arm in matched.arms() {
                        let mut branch = path.fork(work)?;
                        let decision =
                            bind_pattern(arm.pattern(), scrutinee, &mut branch, facts, work)?;
                        if decision != MatchDecision::No {
                            branch.tasks(&[Task::Evaluate(arm.body())], work)?;
                            branches.push(branch);
                        }
                        if decision == MatchDecision::Yes {
                            break;
                        }
                    }
                    path = branches.pop().ok_or_else(|| invalid(id))?;
                    pending
                        .try_reserve(branches.len())
                        .map_err(|_| resource())?;
                    pending.extend(branches);
                }
                Task::Request(id) => {
                    let operand = path.pop(id)?;
                    let EffectExprKind::Operation(EffectOperation::Request(request)) =
                        &node(program, id)?.kind
                    else {
                        return Err(invalid(id));
                    };
                    let operation = native.operation(request.operation(), work)?;
                    if matches!(mode, FlowMode::Handler(_)) && operation.is_none() {
                        let admitted = if matches!(mode, FlowMode::Handler(entry) if entry.family_identity().is_some())
                        {
                            facts.outward_family_data(operand, work)?
                        } else {
                            facts.independent_data(operand, work)?
                        };
                        if !admitted {
                            return Err(invalid(id));
                        }
                        path.value(independent, work)?;
                        continue;
                    }
                    let fact = operation.ok_or_else(|| invalid(id))?;
                    if let FlowMode::Handler(entry) = mode {
                        if fact.role != ForeignOperationRole::Borrow
                            || !(matches!(fact.result, ForeignResultFact::Independent)
                                || (entry.family_identity().is_some()
                                    && matches!(fact.result,
                                    ForeignResultFact::Store { storage } | ForeignResultFact::Load { storage }
                                        if storage == entry.interpreted().effect())))
                        {
                            return Err(invalid(id));
                        }
                        charge(work, fact.state_lineage.len())?;
                        for expected in &fact.state_lineage {
                            let value = facts
                                .at_path(operand, &expected.path, work)?
                                .ok_or_else(|| invalid(id))?;
                            match facts.0[value] {
                                Fact::State(State::Current)
                                    if Some(expected.state)
                                        == entry.definition.state.ty.outer_nominal() => {}
                                Fact::State(State::Enclosing(access)) => associations
                                    .check_enclosing_state(
                                        program, native, access, id, expected, work,
                                    )?,
                                _ => return Err(invalid(id)),
                            }
                        }
                        match fact.result {
                            ForeignResultFact::Store { storage } => {
                                let storage = entry
                                    .canonical
                                    .foreign_storage(storage)
                                    .ok_or_else(|| invalid(id))?;
                                if request.operation() != storage.store() {
                                    return Err(invalid(id));
                                }
                                let state = facts
                                    .at_path(operand, &[0], work)?
                                    .ok_or_else(|| invalid(id))?;
                                if !matches!(facts.0[state], Fact::State(State::Current)) {
                                    return Err(invalid(id));
                                }
                                retain_handler_storage_relation(
                                    &mut relations,
                                    entry,
                                    id,
                                    request,
                                    HandlerNativeStorageResult::Store {
                                        allocated: storage.allocated_constructor(),
                                        refused: storage.refused_constructor(),
                                    },
                                    work,
                                )?;
                                let reference = facts.add(Fact::Reference(State::Current), work)?;
                                let allocated = facts.add(
                                    Fact::Data(storage.allocated_constructor(), Some(reference)),
                                    work,
                                )?;
                                let refused = facts.add(
                                    Fact::Data(storage.refused_constructor(), Some(independent)),
                                    work,
                                )?;
                                let mut refusal = path.fork(work)?;
                                refusal.value(refused, work)?;
                                pending.try_reserve(1).map_err(|_| resource())?;
                                pending.push(refusal);
                                path.value(allocated, work)?;
                            }
                            ForeignResultFact::Load { storage } => {
                                let storage = entry
                                    .canonical
                                    .foreign_storage(storage)
                                    .ok_or_else(|| invalid(id))?;
                                if request.operation() != storage.load() {
                                    return Err(invalid(id));
                                }
                                let state = facts
                                    .at_path(operand, &[0], work)?
                                    .ok_or_else(|| invalid(id))?;
                                let reference = facts
                                    .at_path(operand, &[2], work)?
                                    .ok_or_else(|| invalid(id))?;
                                if !matches!(
                                    (&facts.0[state], &facts.0[reference]),
                                    (Fact::State(State::Current), Fact::Reference(State::Current))
                                ) {
                                    return Err(invalid(id));
                                }
                                retain_handler_storage_relation(
                                    &mut relations,
                                    entry,
                                    id,
                                    request,
                                    HandlerNativeStorageResult::Load,
                                    work,
                                )?;
                                path.value(independent, work)?;
                            }
                            _ => path.value(independent, work)?,
                        }
                        continue;
                    }
                    let FlowMode::Lifecycle(context, _) = mode else {
                        return Err(invalid(id));
                    };
                    let alternatives = match (&fact.result, context.phase) {
                        (
                            ForeignResultFact::Acquire { constructors, .. },
                            LifecyclePhase::Acquire,
                        ) => {
                            if path.acquired.is_some() {
                                return Err(invalid(id));
                            }
                            charge(work, fact.state_lineage.len())?;
                            for state in &fact.state_lineage {
                                let value = facts
                                    .at_path(operand, &state.path, work)?
                                    .ok_or_else(|| invalid(id))?;
                                let Fact::State(State::Enclosing(access)) = facts.0[value] else {
                                    return Err(invalid(id));
                                };
                                associations.check_enclosing_state(
                                    program, native, access, id, state, work,
                                )?;
                            }
                            constructors.as_slice()
                        }
                        (
                            ForeignResultFact::Finish { constructors, .. },
                            LifecyclePhase::Finish,
                        ) => {
                            if path.finished.is_some() {
                                return Err(invalid(id));
                            }
                            require_current_state_lineage(
                                facts,
                                operand,
                                &fact.state_lineage,
                                id,
                                work,
                            )?;
                            constructors.as_slice()
                        }
                        _ => return Err(invalid(id)),
                    };
                    let mut branches = Vec::new();
                    charge(work, alternatives.len())?;
                    branches
                        .try_reserve_exact(alternatives.len())
                        .map_err(|_| resource())?;
                    for (ordinal, constructor) in alternatives.iter().enumerate() {
                        let mut branch = path.fork(work)?;
                        let payload = match context.phase {
                            LifecyclePhase::Acquire if ordinal == 0 => {
                                branch.acquired = Some(id);
                                Some(facts.add(Fact::State(State::Acquired(id)), work)?)
                            }
                            LifecyclePhase::Acquire => Some(independent),
                            LifecyclePhase::Finish if ordinal == 0 => {
                                branch.finished = Some(Finished::Consumed(id));
                                None
                            }
                            LifecyclePhase::Finish if ordinal == 1 => {
                                branch.finished = Some(Finished::ConsumedFailure(id));
                                Some(independent)
                            }
                            LifecyclePhase::Finish => {
                                branch.finished = Some(Finished::Retained(id));
                                let state = facts.add(Fact::State(State::Retained(id)), work)?;
                                charge(work, 2)?;
                                let mut fields = Vec::new();
                                fields.try_reserve_exact(2).map_err(|_| resource())?;
                                fields.extend([state, independent]);
                                Some(facts.add(Fact::Tuple(fields.into_boxed_slice()), work)?)
                            }
                        };
                        let value = facts.add(Fact::Data(*constructor, payload), work)?;
                        branch.value(value, work)?;
                        branches.push(branch);
                    }
                    path = branches.pop().ok_or_else(|| invalid(id))?;
                    pending
                        .try_reserve(branches.len())
                        .map_err(|_| resource())?;
                    pending.extend(branches);
                }
                Task::ResumeArgument(id) => {
                    let value = path.pop(id)?;
                    let admitted = if matches!(mode, FlowMode::Handler(entry) if entry.family_identity().is_some())
                    {
                        facts.family_data(value, work)?
                    } else {
                        facts.independent_data(value, work)?
                    };
                    if !admitted {
                        return Err(invalid(id));
                    }
                    path.value(independent, work)?;
                }
                Task::CleanupAction(id) => {
                    let value = path.pop(id)?;
                    if !facts.independent_data(value, work)? {
                        return Err(invalid(id));
                    }
                    let EffectExprKind::Operation(EffectOperation::Cleanup(scope)) =
                        &node(program, id)?.kind
                    else {
                        return Err(invalid(id));
                    };
                    path.tasks(&[Task::Evaluate(scope.body)], work)?;
                }
                Task::HandlerResult(id) => {
                    let value = path.pop(id)?;
                    path.value(value, work)?;
                }
                Task::StateAccess(id) => {
                    let operand = path.pop(id)?;
                    if facts.contains_state(operand, work)? {
                        return Err(invalid(id));
                    }
                    if let FlowMode::Handler(entry) = mode {
                        let Fact::ResourceInput {
                            clause,
                            path: coordinates,
                        } = &facts.0[operand]
                        else {
                            return Err(invalid(id));
                        };
                        let clause = entry.clause_at(*clause).ok_or_else(|| invalid(id))?;
                        let mut expected = &clause.pattern().ty;
                        for coordinate in coordinates {
                            charge(work, 1)?;
                            let Type::Tuple(fields) = expected else {
                                return Err(invalid(id));
                            };
                            expected = fields.get(*coordinate).ok_or_else(|| invalid(id))?;
                        }
                        let EffectExprKind::Operation(EffectOperation::ProviderStateAccess(access)) =
                            &node(program, id)?.kind
                        else {
                            return Err(invalid(id));
                        };
                        if !same_type_with_budget(
                            expected,
                            &node(program, access.operand())?.ty,
                            work,
                        )
                        .map_err(|()| resource())?
                        {
                            return Err(invalid(id));
                        }
                    }
                    let value = facts.add(Fact::State(State::Enclosing(id)), work)?;
                    path.value(value, work)?;
                }
            }
        }
        match mode {
            FlowMode::Lifecycle(context, constructors) => {
                terminal(program, context, &mut path, facts, constructors, work)?
            }
            FlowMode::Handler(_) => {
                if path.values.len() != 1
                    || !facts.independent_data(path.pop(program.root)?, work)?
                {
                    return Err(invalid(program.root));
                }
            }
        }
    }
    Ok(())
}

#[cfg(test)]
mod dictionary_carrier_tests {
    use super::*;

    #[test]
    fn outward_family_request_handles_do_not_admit_state_callables_or_returns() {
        let constructor =
            ConstructorId::new(NominalTypeId::new(crate::module::ModuleId::new(0), 0), 0);
        let mut facts = Facts(vec![
            Fact::Independent,
            Fact::ResourceInput {
                clause: NodeId::new(crate::core::dialect::ArenaId::new(1), 0),
                path: Box::new([0]),
            },
            Fact::Data(constructor, Some(1)),
            Fact::Tuple(Box::new([0, 2])),
        ]);
        let mut measured = TypeWorkBudget::unbounded();
        assert!(facts.outward_family_data(3, &mut measured).unwrap());
        let cost = measured.used();
        assert!(cost > 0);
        assert!(
            !facts
                .family_data(3, &mut TypeWorkBudget::unbounded())
                .unwrap()
        );
        assert!(
            !facts
                .independent_data(3, &mut TypeWorkBudget::unbounded())
                .unwrap()
        );
        for prefix in [0, 17] {
            let mut short = TypeWorkBudget::with_limit(prefix + cost - 1);
            short.charge(prefix).unwrap();
            assert_eq!(
                facts
                    .outward_family_data(3, &mut short)
                    .unwrap_err()
                    .reason(),
                ValidationReason::Resource
            );
            let mut exact = TypeWorkBudget::with_limit(prefix + cost);
            exact.charge(prefix).unwrap();
            assert!(facts.outward_family_data(3, &mut exact).unwrap());
            assert_eq!(exact.used(), prefix + cost);
        }
        // Mutate the same nested operand, preserving its container graph.
        // Passing a resource handle grants no corresponding state/call right.
        for replacement in [
            Fact::State(State::Current),
            Fact::Callable,
            Fact::DictionaryCallable,
        ] {
            facts.0[1] = replacement;
            assert!(
                !facts
                    .outward_family_data(3, &mut TypeWorkBudget::unbounded())
                    .unwrap()
            );
        }
    }

    #[test]
    fn nested_dictionary_carriers_have_exact_fallible_traversal_and_retry() {
        let constructor =
            ConstructorId::new(NominalTypeId::new(crate::module::ModuleId::new(0), 0), 0);
        let facts = Facts(vec![
            Fact::DictionaryCallable,
            Fact::Independent,
            Fact::Tuple(vec![0, 1].into_boxed_slice()),
            Fact::Data(constructor, Some(2)),
            Fact::Tuple(vec![3, 1].into_boxed_slice()),
        ]);
        // Initial pending slot, six visited facts, four tuple edge slots,
        // and one payload slot. The two independent leaves are both visited.
        let cost = 1 + 6 + 4 + 1;
        for prefix in [0, 17] {
            let mut short = TypeWorkBudget::with_limit(prefix + cost - 1);
            short.charge(prefix).unwrap();
            assert!(facts.call_requirement(4, &mut short).is_err());
            for _ in 0..2 {
                let mut exact = TypeWorkBudget::with_limit(prefix + cost);
                exact.charge(prefix).unwrap();
                assert_eq!(
                    facts.call_requirement(4, &mut exact).unwrap(),
                    CallRequirement::DictionaryInstallation
                );
                assert_eq!(exact.used(), prefix + cost);
            }
        }
    }
}
