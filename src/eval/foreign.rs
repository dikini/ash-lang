//! Iterative codec conversion for authenticated executable foreign operations.

use super::super::value::{ActivationKey, HeapCell};
use super::{
    RuntimeFailure, RuntimePhase, Value, allocate_heap, charge_effect_work,
    resolve_location_with_work,
};
use crate::foreign::runtime::{
    ForeignData, ForeignDataNode, ForeignExecutionError, ForeignExecutionReason,
};
use crate::types::TypeWorkBudget;
use std::{collections::HashSet, sync::Arc};

fn foreign_failure(error: ForeignExecutionError, phase: RuntimePhase) -> RuntimeFailure {
    use super::{ResourceFailureCause, RuntimeResource};
    let (cause, resource) = match error.reason() {
        ForeignExecutionReason::Binding => return RuntimeFailure::ForeignBinding,
        ForeignExecutionReason::WorkExhausted => (
            ResourceFailureCause::WorkBudgetExhausted,
            RuntimeResource::WorkUnits,
        ),
        ForeignExecutionReason::StorageRefused => (
            ResourceFailureCause::StorageReservationFailed,
            RuntimeResource::ForeignCodecStorage,
        ),
        ForeignExecutionReason::ResourceRefused => (
            ResourceFailureCause::ResourceAdmissionRefused,
            RuntimeResource::ForeignAdmission,
        ),
    };
    // The generic adapter markers carry no measured quantities. Its work
    // bound need not be the evaluator's ledger, so neither count is inferred.
    super::resource_failure(cause, phase, resource, None, None)
}

fn codec_failure_phase(failure: RuntimeFailure, phase: RuntimePhase) -> RuntimeFailure {
    match failure {
        RuntimeFailure::Report(mut report) => {
            if let Some(details) = report.primary.resource.as_mut() {
                details.phase = phase;
            }
            RuntimeFailure::Report(report)
        }
        other => other,
    }
}

fn charge_integer_copy(
    integer: &crate::integer::Integer,
    work: &mut TypeWorkBudget,
    phase: RuntimePhase,
) -> Result<(), RuntimeFailure> {
    let bytes = usize::try_from(integer.magnitude_byte_length())
        .map_err(|_| super::effect_work_failure(work, None, phase))?;
    charge_effect_work(work, bytes.max(1), phase)
}

fn clone_codec_value(
    value: &Value,
    work: &mut TypeWorkBudget,
    phase: RuntimePhase,
) -> Result<Value, RuntimeFailure> {
    if let Value::Integer(integer) = value {
        charge_integer_copy(integer, work, phase)?;
    }
    Ok(value.clone())
}

pub(super) fn encode_input(
    value: &Value,
    heap: &[HeapCell],
    states: &mut Vec<ActivationKey>,
    work: &mut TypeWorkBudget,
    phase: RuntimePhase,
) -> Result<ForeignData, RuntimeFailure> {
    enum Task<'a> {
        Value(&'a Value),
        Tuple(usize),
        Constructor(crate::types::ConstructorId, bool),
        Exit(usize),
    }
    fn push_node(
        nodes: &mut Vec<ForeignDataNode>,
        node: ForeignDataNode,
        work: &mut TypeWorkBudget,
        phase: RuntimePhase,
    ) -> Result<usize, RuntimeFailure> {
        charge_effect_work(work, 1, phase)?;
        nodes
            .try_reserve(1)
            .map_err(|_| foreign_failure(ForeignExecutionError::STORAGE_REFUSED, phase))?;
        let index = nodes.len();
        nodes.push(node);
        Ok(index)
    }
    let mut pending = Vec::new();
    charge_effect_work(work, 1, phase)?;
    pending
        .try_reserve(1)
        .map_err(|_| foreign_failure(ForeignExecutionError::STORAGE_REFUSED, phase))?;
    pending.push(Task::Value(value));
    let mut results = Vec::new();
    let mut nodes = Vec::new();
    let mut active = HashSet::new();
    while let Some(task) = pending.pop() {
        charge_effect_work(work, 1, phase)?;
        let result = match task {
            Task::Exit(location) => {
                active.remove(&location);
                continue;
            }
            Task::Tuple(count) => {
                let start = results
                    .len()
                    .checked_sub(count)
                    .ok_or(RuntimeFailure::ForeignBinding)?;
                charge_effect_work(work, count, phase)?;
                let mut children = Vec::new();
                children
                    .try_reserve_exact(count)
                    .map_err(|_| foreign_failure(ForeignExecutionError::STORAGE_REFUSED, phase))?;
                children.extend_from_slice(&results[start..]);
                results.truncate(start);
                push_node(
                    &mut nodes,
                    ForeignDataNode::Tuple(children.into_boxed_slice()),
                    work,
                    phase,
                )?
            }
            Task::Constructor(id, has_payload) => {
                let payload = if has_payload {
                    Some(results.pop().ok_or(RuntimeFailure::ForeignBinding)?)
                } else {
                    None
                };
                push_node(
                    &mut nodes,
                    ForeignDataNode::Constructor(id, payload),
                    work,
                    phase,
                )?
            }
            Task::Value(value) => match value {
                Value::Integer(integer) => {
                    charge_integer_copy(integer, work, phase)?;
                    let integer = integer.clone();
                    push_node(&mut nodes, ForeignDataNode::Integer(integer), work, phase)?
                }
                Value::Bytes(value) => push_node(
                    &mut nodes,
                    ForeignDataNode::Bytes(Arc::clone(value)),
                    work,
                    phase,
                )?,
                Value::BytePrefix(value) => {
                    let bytes = value.as_bytes();
                    charge_effect_work(work, bytes.len(), phase)?;
                    let mut copied = Vec::new();
                    copied.try_reserve_exact(bytes.len()).map_err(|_| {
                        foreign_failure(ForeignExecutionError::STORAGE_REFUSED, phase)
                    })?;
                    copied.extend_from_slice(bytes);
                    push_node(
                        &mut nodes,
                        ForeignDataNode::Bytes(Arc::from(copied)),
                        work,
                        phase,
                    )?
                }
                Value::String(value) => push_node(
                    &mut nodes,
                    ForeignDataNode::String(Arc::clone(value)),
                    work,
                    phase,
                )?,
                Value::Boolean(value) => {
                    push_node(&mut nodes, ForeignDataNode::Boolean(*value), work, phase)?
                }
                Value::Unit => push_node(&mut nodes, ForeignDataNode::Unit, work, phase)?,
                Value::LayoutWitness(witness) => push_node(
                    &mut nodes,
                    ForeignDataNode::LayoutWitness(witness.clone()),
                    work,
                    phase,
                )?,
                Value::Reference {
                    activation,
                    reference,
                } => {
                    // This provisional slot is remapped to the exact live view
                    // order after the operation's state operands are admitted.
                    charge_effect_work(work, states.len(), phase)?;
                    let slot = match states.iter().position(|key| key == activation) {
                        Some(slot) => slot,
                        None => {
                            states.try_reserve(1).map_err(|_| {
                                foreign_failure(ForeignExecutionError::STORAGE_REFUSED, phase)
                            })?;
                            let slot = states.len();
                            states.push(*activation);
                            slot
                        }
                    };
                    push_node(
                        &mut nodes,
                        ForeignDataNode::Reference(reference.with_owner_slot(slot)),
                        work,
                        phase,
                    )?
                }

                Value::NativeStateView(key) => {
                    charge_effect_work(work, states.len(), phase)?;
                    let slot = match states.iter().position(|found| found == key) {
                        Some(slot) => slot,
                        None => {
                            charge_effect_work(work, 1, phase)?;
                            states.try_reserve(1).map_err(|_| {
                                foreign_failure(ForeignExecutionError::STORAGE_REFUSED, phase)
                            })?;
                            let slot = states.len();
                            states.push(*key);
                            slot
                        }
                    };
                    push_node(&mut nodes, ForeignDataNode::State(slot), work, phase)?
                }
                Value::Location(location) => {
                    let location = resolve_location_with_work(heap, *location, work)
                        .map_err(|failure| codec_failure_phase(failure, phase))?;
                    charge_effect_work(work, 1, phase)?;
                    active.try_reserve(1).map_err(|_| {
                        foreign_failure(ForeignExecutionError::STORAGE_REFUSED, phase)
                    })?;
                    if !active.insert(location) {
                        return Err(RuntimeFailure::AliasLoop);
                    }
                    let cell = heap.get(location).ok_or(RuntimeFailure::InvalidLocation)?;
                    let count = match cell {
                        HeapCell::Tuple(children) => children.len(),
                        HeapCell::Constructor(_, payload) => usize::from(payload.is_some()),
                        _ => return Err(RuntimeFailure::ForeignBinding),
                    };
                    let pending_count = count
                        .checked_add(2)
                        .ok_or_else(|| super::effect_work_failure(work, None, phase))?;
                    charge_effect_work(work, pending_count, phase)?;
                    pending.try_reserve(pending_count).map_err(|_| {
                        foreign_failure(ForeignExecutionError::STORAGE_REFUSED, phase)
                    })?;
                    pending.push(Task::Exit(location));
                    match cell {
                        HeapCell::Tuple(children) => {
                            pending.push(Task::Tuple(children.len()));
                            pending.extend(children.iter().rev().map(Task::Value));
                        }
                        HeapCell::Constructor(id, payload) => {
                            pending.push(Task::Constructor(*id, payload.is_some()));
                            if let Some(payload) = payload {
                                pending.push(Task::Value(payload));
                            }
                        }
                        _ => return Err(RuntimeFailure::ForeignBinding),
                    }
                    continue;
                }
                _ => return Err(RuntimeFailure::ForeignBinding),
            },
        };
        charge_effect_work(work, 1, phase)?;
        results
            .try_reserve(1)
            .map_err(|_| foreign_failure(ForeignExecutionError::STORAGE_REFUSED, phase))?;
        results.push(result);
    }
    if results.len() != 1 {
        return Err(RuntimeFailure::ForeignBinding);
    }
    ForeignData::new(nodes, results[0]).map_err(|error| foreign_failure(error, phase))
}

pub(super) fn decode_data(
    data: &ForeignData,
    heap: &mut Vec<HeapCell>,
    work: &mut TypeWorkBudget,
    phase: RuntimePhase,
) -> Result<Value, RuntimeFailure> {
    decode_data_with_owners(data, heap, work, phase, &[])
}

fn decode_data_with_owners(
    data: &ForeignData,
    heap: &mut Vec<HeapCell>,
    work: &mut TypeWorkBudget,
    phase: RuntimePhase,
    owners: &[ActivationKey],
) -> Result<Value, RuntimeFailure> {
    charge_effect_work(work, data.nodes().len(), phase)?;
    let mut values: Vec<Value> = Vec::new();
    values
        .try_reserve_exact(data.nodes().len())
        .map_err(|_| foreign_failure(ForeignExecutionError::STORAGE_REFUSED, phase))?;
    for node in data.nodes() {
        charge_effect_work(work, 1, phase)?;
        let value = match node {
            ForeignDataNode::Integer(value) => {
                charge_integer_copy(value, work, phase)?;
                Value::Integer(value.clone())
            }
            ForeignDataNode::Bytes(value) => Value::Bytes(Arc::clone(value)),
            ForeignDataNode::String(value) => Value::String(Arc::clone(value)),
            ForeignDataNode::Boolean(value) => Value::Boolean(*value),
            ForeignDataNode::Unit => Value::Unit,
            ForeignDataNode::LayoutWitness(witness) => Value::LayoutWitness(witness.clone()),
            ForeignDataNode::Reference(reference) => Value::Reference {
                activation: *owners
                    .get(reference.owner_slot())
                    .ok_or(RuntimeFailure::ForeignBinding)?,
                reference: reference.clone(),
            },
            ForeignDataNode::State(_) => return Err(RuntimeFailure::ForeignBinding),
            ForeignDataNode::Tuple(children) => {
                charge_effect_work(work, children.len() + 1, phase)?;
                let mut fields = Vec::new();
                fields
                    .try_reserve_exact(children.len())
                    .map_err(|_| foreign_failure(ForeignExecutionError::STORAGE_REFUSED, phase))?;
                for child in children {
                    fields.push(clone_codec_value(
                        values.get(*child).ok_or(RuntimeFailure::ForeignBinding)?,
                        work,
                        phase,
                    )?);
                }
                heap.try_reserve(1)
                    .map_err(|_| RuntimeFailure::HeapCapacity)?;
                Value::Location(allocate_heap(
                    heap,
                    HeapCell::Tuple(fields.into_boxed_slice()),
                )?)
            }
            ForeignDataNode::Constructor(id, payload) => {
                let payload = payload
                    .map(|child| {
                        clone_codec_value(
                            values.get(child).ok_or(RuntimeFailure::ForeignBinding)?,
                            work,
                            phase,
                        )
                    })
                    .transpose()?;
                charge_effect_work(work, 1, phase)?;
                heap.try_reserve(1)
                    .map_err(|_| RuntimeFailure::HeapCapacity)?;
                Value::Location(allocate_heap(heap, HeapCell::Constructor(*id, payload))?)
            }
        };
        values.push(value);
    }
    clone_codec_value(
        values
            .get(data.root())
            .ok_or(RuntimeFailure::ForeignBinding)?,
        work,
        phase,
    )
}

/// Checks codec shape against the original admitted operation scheme. Native
/// state is a borrowed slot only, and independent results cannot contain one.
pub(super) fn validate_codec(
    data: &ForeignData,
    expected: &crate::types::Type,
    registry: &crate::resolved::ResolvedRegistry,
    allow_state: bool,
    work: &mut TypeWorkBudget,
    phase: RuntimePhase,
) -> Result<(), RuntimeFailure> {
    use crate::types::{
        IterativeTypeOwner, Type, clone_type_with_budget, discard_type_iteratively,
        substitute_type_variables_with,
    };
    struct Replacements(std::collections::HashMap<crate::types::TypeVariableId, Type>);
    impl Drop for Replacements {
        fn drop(&mut self) {
            for (_, ty) in self.0.drain() {
                discard_type_iteratively(ty);
            }
        }
    }
    let root = IterativeTypeOwner::new(
        clone_type_with_budget(expected, work)
            .map_err(|_| foreign_failure(ForeignExecutionError::RESOURCE_REFUSED, phase))?,
    );
    let mut pending = Vec::new();
    charge_effect_work(work, 1, phase)?;
    pending
        .try_reserve(1)
        .map_err(|_| foreign_failure(ForeignExecutionError::STORAGE_REFUSED, phase))?;
    pending.push((data.root(), root));
    while let Some((index, expected)) = pending.pop() {
        charge_effect_work(work, 1, phase)?;
        let node = data.node(index).ok_or(RuntimeFailure::ForeignBinding)?;
        match (node, &*expected) {
            (ForeignDataNode::Bytes(_), Type::Bytes)
            | (ForeignDataNode::String(_), Type::String)
            | (ForeignDataNode::Integer(_), Type::Int)
            | (ForeignDataNode::Boolean(_), Type::Bool)
            | (ForeignDataNode::Unit, Type::Unit) => {}
            (ForeignDataNode::Tuple(children), Type::Tuple(types)) => {
                if children.len() != types.len() {
                    return Err(RuntimeFailure::ForeignBinding);
                }
                charge_effect_work(work, children.len(), phase)?;
                pending
                    .try_reserve(children.len())
                    .map_err(|_| foreign_failure(ForeignExecutionError::STORAGE_REFUSED, phase))?;
                for (child, ty) in children.iter().zip(types.iter()).rev() {
                    let ty = IterativeTypeOwner::new(clone_type_with_budget(ty, work).map_err(
                        |_| foreign_failure(ForeignExecutionError::RESOURCE_REFUSED, phase),
                    )?);
                    pending.push((*child, ty));
                }
            }
            (ForeignDataNode::LayoutWitness(witness), _) => {
                authenticate_codec_witness(witness, registry, work, phase)?;
                let ty = crate::types::IterativeTypeOwner::new(
                    witness.dictionary().producer().witness_type(),
                );
                if !crate::types::same_type_with_budget(&expected, &ty, work)
                    .map_err(|_| super::effect_work_failure(work, None, phase))?
                {
                    return Err(RuntimeFailure::ForeignBinding);
                }
            }
            (ForeignDataNode::Reference(reference), _) => {
                authenticate_codec_witness(reference.witness(), registry, work, phase)?;
                let Type::Application(head, second) = &*expected else {
                    return Err(RuntimeFailure::ForeignBinding);
                };
                let Type::Application(head, first) = head.as_ref() else {
                    return Err(RuntimeFailure::ForeignBinding);
                };
                let Type::Nominal(nominal) = head.as_ref() else {
                    return Err(RuntimeFailure::ForeignBinding);
                };
                charge_effect_work(work, registry.foreign_modules().count(), phase)?;
                let storage = registry
                    .foreign_modules()
                    .filter_map(|module| module.storage.as_ref())
                    .find(|storage| storage.reference() == *nominal)
                    .ok_or(RuntimeFailure::ForeignBinding)?;
                let arguments = [first.as_ref(), second.as_ref()];
                if storage.witness() != reference.witness().dictionary().producer().witness()
                    || !crate::types::same_type_with_budget(
                        arguments[storage.reference_payload_parameter()],
                        reference.witness().dictionary().payload_type(),
                        work,
                    )
                    .map_err(|_| super::effect_work_failure(work, None, phase))?
                {
                    return Err(RuntimeFailure::ForeignBinding);
                }
            }
            (ForeignDataNode::Constructor(_, _), _) | (ForeignDataNode::State(_), _) => {
                let mut arguments = Vec::new();
                let mut head = &*expected;
                while let Type::Application(function, argument) = head {
                    charge_effect_work(work, 1, phase)?;
                    arguments.try_reserve(1).map_err(|_| {
                        foreign_failure(ForeignExecutionError::STORAGE_REFUSED, phase)
                    })?;
                    arguments.push(argument.as_ref());
                    head = function;
                }
                let Type::Nominal(owner) = head else {
                    return Err(RuntimeFailure::ForeignBinding);
                };
                if matches!(node, ForeignDataNode::State(_)) {
                    if !allow_state
                        || registry
                            .foreign_state(*owner)
                            .is_none_or(|state| state.parameter_count != arguments.len())
                    {
                        return Err(RuntimeFailure::ForeignBinding);
                    }
                    continue;
                }
                let ForeignDataNode::Constructor(id, payload) = node else {
                    unreachable!()
                };
                let constructor = registry
                    .constructor(*id)
                    .ok_or(RuntimeFailure::ForeignBinding)?;
                if constructor.owner != *owner {
                    return Err(RuntimeFailure::ForeignBinding);
                }
                match (payload, constructor.payload.as_ref()) {
                    (None, None) => {}
                    (Some(child), Some(payload)) => {
                        let parameters = registry
                            .nominal_parameters(*owner)
                            .ok_or(RuntimeFailure::ForeignBinding)?;
                        if parameters.len() != arguments.len() {
                            return Err(RuntimeFailure::ForeignBinding);
                        }
                        charge_effect_work(work, parameters.len(), phase)?;
                        let mut replacements = Replacements(std::collections::HashMap::new());
                        replacements.0.try_reserve(parameters.len()).map_err(|_| {
                            foreign_failure(ForeignExecutionError::STORAGE_REFUSED, phase)
                        })?;
                        for (parameter, argument) in parameters.iter().zip(arguments.iter().rev()) {
                            let argument = IterativeTypeOwner::new(
                                clone_type_with_budget(argument, work).map_err(|_| {
                                    foreign_failure(ForeignExecutionError::RESOURCE_REFUSED, phase)
                                })?,
                            );
                            replacements.0.insert(parameter.id, argument.into_inner());
                        }
                        let payload = IterativeTypeOwner::new(substitute_type_variables_with(
                            payload,
                            &replacements.0,
                            |cells| charge_effect_work(work, cells, phase),
                            || foreign_failure(ForeignExecutionError::STORAGE_REFUSED, phase),
                        )?);
                        charge_effect_work(work, 1, phase)?;
                        pending.try_reserve(1).map_err(|_| {
                            foreign_failure(ForeignExecutionError::STORAGE_REFUSED, phase)
                        })?;
                        pending.push((*child, payload));
                    }
                    _ => return Err(RuntimeFailure::ForeignBinding),
                }
            }
            _ => return Err(RuntimeFailure::ForeignBinding),
        }
    }
    Ok(())
}

pub(super) fn instantiate_layout_witness(
    registry: &crate::resolved::ResolvedRegistry,
    producer: crate::foreign::ForeignLayoutProducer,
    work: &mut TypeWorkBudget,
    phase: RuntimePhase,
) -> Result<Value, RuntimeFailure> {
    let dictionary = registry
        .foreign_layout_dictionary(producer, work)
        .map_err(|failure| {
            if failure.is_resource_exhaustion() {
                super::effect_work_failure(work, None, phase)
            } else {
                RuntimeFailure::ForeignBinding
            }
        })?;
    Ok(Value::LayoutWitness(
        crate::foreign::runtime::ForeignLayoutWitness::from_dictionary(dictionary),
    ))
}

fn authenticate_codec_witness(
    witness: &crate::foreign::runtime::ForeignLayoutWitness,
    registry: &crate::resolved::ResolvedRegistry,
    work: &mut TypeWorkBudget,
    phase: RuntimePhase,
) -> Result<(), RuntimeFailure> {
    let canonical = registry
        .foreign_layout_dictionary(witness.dictionary().producer(), work)
        .map_err(|failure| {
            if failure.is_resource_exhaustion() {
                super::effect_work_failure(work, None, phase)
            } else {
                RuntimeFailure::ForeignBinding
            }
        })?;
    charge_effect_work(work, 8, phase)?;
    if canonical.as_ref() != witness.dictionary().as_ref() {
        return Err(RuntimeFailure::ForeignBinding);
    }
    Ok(())
}

use super::{
    Control, EffectTraceEvent, Environment, Frame, Instantiation, Machine, ProviderBoundary,
    ProviderFinish, ProviderPhase,
};
use crate::foreign::{
    ForeignResultFact,
    runtime::{ForeignAcquisition, ForeignCompletion, ForeignInvocation, ForeignRuntime},
};
use crate::types::{ConstructorId, EffectInstance, OperationId, Type};

fn provider_owner<'a>(
    runtime: Option<&'a ForeignRuntime>,
    boundary: &'a ProviderBoundary,
    finish_only: bool,
) -> Option<&'a crate::foreign::runtime::NativeOwnerGuard> {
    boundary.owner.as_ref().or_else(|| {
        if finish_only && boundary.phase == ProviderPhase::Finish && boundary.finished.is_none() {
            runtime?.quarantined_owner(boundary.quarantined_owner?)
        } else {
            None
        }
    })
}

impl<'runtime> Machine<'runtime> {
    fn charge_quarantine_lookup(&mut self) -> Result<(), RuntimeFailure> {
        let runtime = self
            .foreign_runtime
            .as_ref()
            .ok_or(RuntimeFailure::ForeignBinding)?;
        charge_effect_work(
            &mut self.instantiation_work,
            runtime
                .quarantine_count()
                .checked_mul(2)
                .ok_or(RuntimeFailure::ResourceCapacity)?,
            RuntimePhase::Teardown,
        )?;
        let edges = runtime
            .quarantine_dependency_count()
            .ok_or(RuntimeFailure::ResourceCapacity)?;
        charge_effect_work(&mut self.instantiation_work, edges, RuntimePhase::Teardown)
    }
    /// Preflights the complete dependency closure before moving any enclosing
    /// guard. The unique owners stay in the host; frame tokens retain only the
    /// one admitted finish capability and revoke ordinary source access.
    fn quarantine_provider_owner(
        &mut self,
        owner: crate::foreign::runtime::NativeOwnerGuard,
    ) -> Result<(), RuntimeFailure> {
        let identity = owner.identity;
        // Associated acquisition reserved quarantine capacity for every live
        // owner. Publish the retained root into this inaccessible holder before
        // fallible closure discovery, so host abort still owns it on refusal.
        let Some(runtime) = self.foreign_runtime.as_mut() else {
            std::mem::forget(owner);
            return Err(RuntimeFailure::ForeignBinding);
        };
        runtime.quarantine_prepared(owner);
        self.charge_quarantine_lookup()?;
        let dependencies = &self
            .foreign_runtime
            .as_ref()
            .expect("runtime retained above")
            .quarantined_owner(identity)
            .ok_or(RuntimeFailure::ForeignBinding)?
            .dependencies;
        let mut identities = Vec::new();
        let mut paths = Vec::new();
        charge_effect_work(
            &mut self.instantiation_work,
            dependencies.len(),
            RuntimePhase::Teardown,
        )?;
        identities
            .try_reserve_exact(dependencies.len())
            .map_err(|_| RuntimeFailure::ResourceCapacity)?;
        identities.extend(dependencies.iter().copied());
        let mut cursor = 0;
        while cursor < identities.len() {
            self.charge_quarantine_lookup()?;
            let identity = identities[cursor];
            cursor += 1;
            let path = find_provider_path_matching(
                &self.frames,
                |boundary| {
                    boundary
                        .owner
                        .as_ref()
                        .is_some_and(|owner| owner.identity == identity)
                },
                &mut self.instantiation_work,
            )?;
            let dependencies = if let Some(path) = path.as_ref() {
                &provider_at(&self.frames, path)
                    .ok_or(RuntimeFailure::ForeignBinding)?
                    .owner
                    .as_ref()
                    .ok_or(RuntimeFailure::ForeignBinding)?
                    .dependencies
            } else {
                &self
                    .foreign_runtime
                    .as_ref()
                    .ok_or(RuntimeFailure::ForeignBinding)?
                    .quarantined_owner(identity)
                    .ok_or(RuntimeFailure::ForeignBinding)?
                    .dependencies
            };
            charge_effect_work(
                &mut self.instantiation_work,
                dependencies
                    .len()
                    .checked_add(1)
                    .ok_or(RuntimeFailure::ResourceCapacity)?,
                RuntimePhase::Teardown,
            )?;
            for dependency in dependencies {
                charge_effect_work(
                    &mut self.instantiation_work,
                    identities.len(),
                    RuntimePhase::Teardown,
                )?;
                if !identities.contains(dependency) {
                    identities
                        .try_reserve(1)
                        .map_err(|_| RuntimeFailure::ResourceCapacity)?;
                    identities.push(*dependency);
                }
            }
            if let Some(path) = path {
                paths
                    .try_reserve(1)
                    .map_err(|_| RuntimeFailure::ResourceCapacity)?;
                paths.push(path);
            }
        }
        let count = paths.len();
        charge_effect_work(&mut self.instantiation_work, count, RuntimePhase::Teardown)?;
        self.foreign_runtime
            .as_mut()
            .ok_or(RuntimeFailure::ForeignBinding)?
            .reserve_quarantine(count)
            .map_err(|error| foreign_failure(error, RuntimePhase::Teardown))?;
        // Every path was checked against this unchanged frame forest. No
        // fallible operation follows the first enclosing ownership transfer.
        let runtime = self
            .foreign_runtime
            .as_mut()
            .expect("quarantine preflighted");
        for path in paths {
            let boundary =
                provider_at_mut(&mut self.frames, &path).expect("preflighted dependency frame");
            let owner = boundary
                .owner
                .take()
                .expect("preflighted unique dependency owner");
            boundary.quarantined_owner = Some(owner.identity);
            runtime.quarantine_prepared(owner);
        }
        Ok(())
    }
    fn provider_owner<'a>(
        &'a self,
        boundary: &'a ProviderBoundary,
        finish_only: bool,
    ) -> Option<&'a crate::foreign::runtime::NativeOwnerGuard> {
        provider_owner(self.foreign_runtime.as_deref(), boundary, finish_only)
    }
    pub(super) fn foreign_constructor(
        &mut self,
        id: ConstructorId,
        payload: Option<Value>,
        phase: RuntimePhase,
    ) -> Result<Value, RuntimeFailure> {
        charge_effect_work(&mut self.instantiation_work, 1, phase)?;
        self.heap
            .try_reserve(1)
            .map_err(|_| RuntimeFailure::HeapCapacity)?;
        Ok(Value::Location(allocate_heap(
            &mut self.heap,
            HeapCell::Constructor(id, payload),
        )?))
    }
    pub(super) fn foreign_tuple(
        &mut self,
        values: &[Value],
        phase: RuntimePhase,
    ) -> Result<Value, RuntimeFailure> {
        charge_effect_work(&mut self.instantiation_work, values.len() + 1, phase)?;
        let mut fields = Vec::new();
        fields
            .try_reserve_exact(values.len())
            .map_err(|_| foreign_failure(ForeignExecutionError::STORAGE_REFUSED, phase))?;
        fields.extend(values.iter().cloned());
        self.heap
            .try_reserve(1)
            .map_err(|_| RuntimeFailure::HeapCapacity)?;
        Ok(Value::Location(allocate_heap(
            &mut self.heap,
            HeapCell::Tuple(fields.into_boxed_slice()),
        )?))
    }
    pub(super) fn foreign_report(
        &mut self,
        value: &Value,
        phase: RuntimePhase,
    ) -> Result<(ConstructorId, Option<Value>), RuntimeFailure> {
        let Value::Location(location) = value else {
            return Err(RuntimeFailure::ForeignBinding);
        };
        let location =
            resolve_location_with_work(&self.heap, *location, &mut self.instantiation_work)
                .map_err(|failure| codec_failure_phase(failure, phase))?;
        match self.heap.get(location) {
            Some(HeapCell::Constructor(id, payload)) => Ok((*id, payload.clone())),
            _ => Err(RuntimeFailure::ForeignBinding),
        }
    }
    pub(super) fn enter_provider(
        &mut self,
        node: crate::core::NodeId,
        mut environment: Environment,
        input: Value,
    ) -> Result<(), RuntimeFailure> {
        let scope = self
            .provider_scope(node)
            .ok_or(RuntimeFailure::ForeignBinding)?;
        let descriptor = std::sync::Arc::clone(
            scope
                .descriptor
                .admitted_arc()
                .ok_or(RuntimeFailure::ForeignBinding)?,
        );
        let acquire = scope.acquire().clone();
        let live = self
            .live_resources
            .checked_add(1)
            .filter(|live| *live <= self.resource_limit)
            .ok_or(RuntimeFailure::ResourceCapacity)?;
        let key = ActivationKey(self.next_activation);
        let next = self
            .next_activation
            .checked_add(1)
            .ok_or(RuntimeFailure::ResourceCapacity)?;
        let runtime = self
            .foreign_runtime
            .as_mut()
            .ok_or(RuntimeFailure::ForeignBinding)?;
        // Executability is required by this admitted scope, not by unused
        // imports. Original facts, operations and codecs are checked before
        // the source acquisition entry can call any native operation.
        runtime
            .preflight(descriptor.native(), &mut self.instantiation_work)
            .map_err(|error| foreign_failure(error, RuntimePhase::Acquisition))?;
        charge_effect_work(
            &mut self.instantiation_work,
            live,
            RuntimePhase::Acquisition,
        )?;
        runtime
            .reserve_quarantine(live)
            .map_err(|error| foreign_failure(error, RuntimePhase::Acquisition))?;
        // Seal runtime metadata and reserve ownership storage before a native call.
        environment.instantiation = environment.instantiation.acquire(
            descriptor.identity(),
            key,
            &mut self.instantiation_work,
            Some(RuntimePhase::Acquisition),
        )?;
        self.frames
            .try_reserve(1)
            .map_err(|_| RuntimeFailure::ResourceCapacity)?;
        let acquire_environment = environment.clone().extend(acquire.parameter.id(), input)?;
        charge_effect_work(&mut self.instantiation_work, 1, RuntimePhase::Acquisition)?;
        self.frames
            .push(Frame::ProviderBoundary(Box::new(ProviderBoundary {
                node,
                key,
                environment,
                owner: None,
                quarantined_owner: None,
                phase: ProviderPhase::Acquire,
                finished: None,
                saved: None,
                discarded: false,
            })));
        self.live_resources = live;
        self.next_activation = next;
        self.control = Some(Control::Evaluate(acquire.body, acquire_environment));
        Ok(())
    }
    pub(super) fn return_provider(
        &mut self,
        mut boundary: Box<ProviderBoundary>,
        value: Value,
    ) -> Result<(), RuntimeFailure> {
        let node = boundary.node;
        let key = boundary.key;
        let phase = boundary.phase;
        let report_phase = match phase {
            ProviderPhase::Acquire => RuntimePhase::Acquisition,
            ProviderPhase::Body => RuntimePhase::Access,
            ProviderPhase::Finish => RuntimePhase::Cleanup,
        };
        let environment = std::mem::take(&mut boundary.environment);
        let mut owner = boundary.owner.take();
        let saved = boundary.saved.take();
        let finished = boundary.finished;
        let discarded = boundary.discarded;
        let quarantined_owner = boundary.quarantined_owner;
        let result = (|| {
            let scope = self
                .provider_scope(node)
                .ok_or(RuntimeFailure::ForeignBinding)?;
            let descriptor = std::sync::Arc::clone(
                scope
                    .descriptor
                    .admitted_arc()
                    .ok_or(RuntimeFailure::ForeignBinding)?,
            );
            let protocol = descriptor.protocol();
            match phase {
                ProviderPhase::Acquire => {
                    let (constructor, payload) = self.foreign_report(&value, report_phase)?;
                    if constructor == protocol.acquire[1] {
                        if owner.is_some() {
                            return Err(RuntimeFailure::ForeignBinding);
                        }
                        let error = payload.ok_or(RuntimeFailure::ForeignBinding)?;
                        self.live_resources = self
                            .live_resources
                            .checked_sub(1)
                            .ok_or(RuntimeFailure::InvalidControlState)?;
                        let result =
                            self.foreign_constructor(protocol.scope[0], Some(error), report_phase)?;
                        self.control = Some(Control::Return(result));
                        return Ok(());
                    }
                    if constructor != protocol.acquire[0]
                        || !matches!(payload,Some(Value::NativeStateView(found)) if found==key)
                        || owner.is_none()
                    {
                        return Err(RuntimeFailure::ForeignBinding);
                    }
                    let scope = self
                        .provider_scope(node)
                        .ok_or(RuntimeFailure::ForeignBinding)?;
                    let body = scope.handler().body();
                    let state_binder = scope.handler_state().id();
                    let handle = scope.handle().id();
                    let handler = scope.handler().id();
                    let handler_environment = environment
                        .clone()
                        .extend(state_binder, Value::NativeStateView(key))?;
                    let body_environment = environment
                        .clone()
                        .extend(handle, Value::ResourceHandle(key))?;
                    self.reserve_checked_terminal_spare(2, RuntimePhase::Cleanup)?;
                    self.frames
                        .try_reserve(2)
                        .map_err(|_| RuntimeFailure::ResourceCapacity)?;
                    boundary.environment = environment;
                    boundary.owner = owner.take();
                    boundary.phase = ProviderPhase::Body;
                    self.frames.push(Frame::ProviderBoundary(boundary));
                    self.frames.push(Frame::HandlerBoundary {
                        node,
                        environment: handler_environment,
                        registration: None,
                        provider: Some(key),
                    });
                    self.trace_effect(EffectTraceEvent::ResourceAcquired(key.0));
                    self.trace_effect(EffectTraceEvent::HandlerActivated(handler));
                    self.control = Some(Control::Evaluate(body, body_environment));
                }
                ProviderPhase::Body => {
                    let finish = self
                        .provider_scope(node)
                        .ok_or(RuntimeFailure::ForeignBinding)?
                        .finish()
                        .clone();
                    let finish_environment = environment
                        .clone()
                        .extend(finish.parameter.id(), Value::NativeStateView(key))?;
                    self.frames
                        .try_reserve(1)
                        .map_err(|_| RuntimeFailure::ResourceCapacity)?;
                    boundary.environment = environment;
                    boundary.owner = owner.take();
                    boundary.phase = ProviderPhase::Finish;
                    boundary.saved = (!discarded).then_some(value);
                    boundary.finished = None;
                    self.frames.push(Frame::ProviderBoundary(boundary));
                    self.control = Some(Control::Evaluate(finish.body, finish_environment));
                }
                ProviderPhase::Finish => {
                    let (constructor, payload) = self.foreign_report(&value, report_phase)?;
                    let kind = finished.ok_or(RuntimeFailure::ForeignBinding)?;
                    let completion = match kind {
                        ProviderFinish::Closed => {
                            if constructor != protocol.finish[0] || payload.is_some() {
                                return Err(RuntimeFailure::ForeignBinding);
                            }
                            drop(owner.take());
                            if discarded {
                                None
                            } else {
                                Some(self.foreign_constructor(
                                    protocol.completion[0],
                                    None,
                                    report_phase,
                                )?)
                            }
                        }
                        ProviderFinish::ConsumedError => {
                            if constructor != protocol.finish[1] {
                                return Err(RuntimeFailure::ForeignBinding);
                            }
                            let error = payload.ok_or(RuntimeFailure::ForeignBinding)?;
                            drop(owner.take());
                            if discarded {
                                None
                            } else {
                                Some(self.foreign_constructor(
                                    protocol.completion[1],
                                    Some(error),
                                    report_phase,
                                )?)
                            }
                        }
                        ProviderFinish::RetainedError => {
                            if constructor != protocol.finish[2] {
                                return Err(RuntimeFailure::ForeignBinding);
                            }
                            let Value::Location(location) =
                                payload.ok_or(RuntimeFailure::ForeignBinding)?
                            else {
                                return Err(RuntimeFailure::ForeignBinding);
                            };
                            let location = resolve_location_with_work(
                                &self.heap,
                                location,
                                &mut self.instantiation_work,
                            )
                            .map_err(|failure| codec_failure_phase(failure, report_phase))?;
                            let Some(HeapCell::Tuple(fields)) = self.heap.get(location) else {
                                return Err(RuntimeFailure::ForeignBinding);
                            };
                            if fields.len() != 2
                                || !matches!(&fields[0],Value::NativeStateView(found) if *found==key)
                            {
                                return Err(RuntimeFailure::ForeignBinding);
                            }
                            let error = fields[1].clone();
                            if let Some(owner) = owner.take() {
                                self.quarantine_provider_owner(owner)?;
                            } else if self
                                .foreign_runtime
                                .as_ref()
                                .ok_or(RuntimeFailure::ForeignBinding)?
                                .quarantined_owner(
                                    quarantined_owner.ok_or(RuntimeFailure::ForeignBinding)?,
                                )
                                .is_none()
                            {
                                return Err(RuntimeFailure::ForeignBinding);
                            }
                            if discarded {
                                None
                            } else {
                                Some(self.foreign_constructor(
                                    protocol.completion[2],
                                    Some(error),
                                    report_phase,
                                )?)
                            }
                        }
                    };
                    self.live_resources = self
                        .live_resources
                        .checked_sub(1)
                        .ok_or(RuntimeFailure::InvalidControlState)?;
                    self.trace_effect(EffectTraceEvent::ResourceReleased(key.0));
                    self.control = Some(if discarded {
                        Control::Return(Value::Unit)
                    } else {
                        let tuple = self.foreign_tuple(
                            &[
                                saved.ok_or(RuntimeFailure::ForeignBinding)?,
                                completion.ok_or(RuntimeFailure::ForeignBinding)?,
                            ],
                            report_phase,
                        )?;
                        Control::Return(self.foreign_constructor(
                            protocol.scope[1],
                            Some(tuple),
                            report_phase,
                        )?)
                    });
                }
            }
            Ok(())
        })();
        if result.is_err()
            && let Some(owner) = owner.take()
        {
            if phase == ProviderPhase::Acquire {
                // This fresh guard has never entered its body, so it has
                // no acquired dependents. Dispose it before abandoning
                // the enclosing owners whose state it may have borrowed.
                drop(owner);
            } else {
                // Active and retained owners keep their dependencies
                // until the machine's host-abort drain completes.
                self.quarantine_provider_owner(owner)?;
            }
        }
        result
    }
    pub(super) fn return_provider_state(
        &mut self,
        node: crate::core::NodeId,
        caller: &Instantiation,
        value: Value,
    ) -> Result<(), RuntimeFailure> {
        let Value::ResourceHandle(key) = value else {
            return Err(RuntimeFailure::ForeignBinding);
        };
        let program = self.program.clone();
        let access = match program.node(node) {
            Some(super::ExecutableNode::Effect(expression)) => match &expression.kind {
                crate::core::EffectExprKind::Operation(
                    crate::core::EffectOperation::ProviderStateAccess(access),
                ) => access,
                _ => return Err(RuntimeFailure::ForeignBinding),
            },
            _ => return Err(RuntimeFailure::ForeignBinding),
        };
        let path = find_provider_path(&self.frames, key, &mut self.instantiation_work)?
            .ok_or(RuntimeFailure::ForeignBinding)?;
        self.charge_quarantine_lookup()?;
        let boundary = provider_at(&self.frames, &path).ok_or(RuntimeFailure::ForeignBinding)?;
        if self.provider_owner(boundary, true).is_none()
            || boundary.finished.is_some()
            || !matches!(boundary.phase, ProviderPhase::Body | ProviderPhase::Finish)
        {
            return Err(RuntimeFailure::ForeignBinding);
        }
        let (scope_node, environment) = (boundary.node, boundary.environment.clone());
        let descriptor = std::sync::Arc::clone(
            self.provider_scope(scope_node)
                .ok_or(RuntimeFailure::ForeignBinding)?
                .descriptor
                .admitted_arc()
                .ok_or(RuntimeFailure::ForeignBinding)?,
        );
        if descriptor.definition().id != access.definition()
            || descriptor.arguments().len() != access.arguments().len()
        {
            return Err(RuntimeFailure::ForeignBinding);
        }
        for (actual, original) in access.arguments().iter().zip(descriptor.arguments()) {
            let actual = caller.argument(actual, &mut self.instantiation_work)?;
            let original = environment
                .instantiation
                .argument(original, &mut self.instantiation_work)?;
            if !crate::types::same_kinded_argument_with_budget(
                &actual,
                &original,
                &mut self.instantiation_work,
            )
            .map_err(|_| RuntimeFailure::ForeignBinding)?
            {
                return Err(RuntimeFailure::ForeignBinding);
            }
        }
        self.control = Some(Control::Return(Value::NativeStateView(key)));
        Ok(())
    }
}

impl<'runtime> Machine<'runtime> {
    pub(super) fn interpret_foreign(
        &mut self,
        effect: &EffectInstance,
        operation: OperationId,
        value: Value,
    ) -> Result<(), RuntimeFailure> {
        use crate::module::ForeignOperationRole;
        let operation_fact = self
            .program
            .registry()
            .foreign_operation(operation)
            .ok_or(RuntimeFailure::ForeignBinding)?;
        let key = Instantiation::activation_at(effect, operation_fact.owned_identity_position)
            .ok_or(RuntimeFailure::ForeignBinding)?;
        let boundary = find_provider_path(&self.frames, key, &mut self.instantiation_work)?
            .ok_or(RuntimeFailure::ForeignBinding)?;
        self.charge_quarantine_lookup()?;
        let candidate =
            provider_at(&self.frames, &boundary).ok_or(RuntimeFailure::ForeignBinding)?;
        let (scope_node, environment, phase) = (
            candidate.node,
            candidate.environment.clone(),
            candidate.phase,
        );
        let descriptor = std::sync::Arc::clone(
            self.provider_scope(scope_node)
                .ok_or(RuntimeFailure::ForeignBinding)?
                .descriptor
                .admitted_arc()
                .ok_or(RuntimeFailure::ForeignBinding)?,
        );
        let native = descriptor.native();
        let operation = native
            .operations
            .iter()
            .find(|fact| fact.id == operation)
            .ok_or(RuntimeFailure::ForeignBinding)?;
        let codec_phase = match operation.role {
            ForeignOperationRole::Acquire => RuntimePhase::Acquisition,
            ForeignOperationRole::Borrow => RuntimePhase::Access,
            ForeignOperationRole::Finish => RuntimePhase::Cleanup,
        };
        let scope_program = self.program.clone();
        let Some(super::ExecutableNode::Effect(expression)) = scope_program.node(scope_node) else {
            return Err(RuntimeFailure::ForeignBinding);
        };
        let crate::core::EffectExprKind::Operation(crate::core::EffectOperation::ProviderScope(
            scope,
        )) = &expression.kind
        else {
            return Err(RuntimeFailure::ForeignBinding);
        };
        let member_count = scope.member_count();
        let selected_member = if member_count == 1 || phase != ProviderPhase::Body {
            0
        } else {
            // An active group boundary grants source dispatch only. Its captured
            // clause grants precisely the selected member's native phase. Resume
            // restores the boundary above that clause and removes this permission.
            let mut selected = None;
            for frame in self.frames.iter().rev() {
                charge_effect_work(&mut self.instantiation_work, 1, codec_phase)?;
                match frame {
                    Frame::HandlerBoundary {
                        node,
                        provider: Some(found),
                        ..
                    } if *node == scope_node && *found == key => break,
                    Frame::ClauseBoundary {
                        handler,
                        continuation: Some(continuation),
                        ..
                    } => {
                        if !matches!(continuation.frames.first(),
                            Some(Frame::HandlerBoundary { node, provider: Some(found), .. })
                                if *node == scope_node && *found == key)
                        {
                            continue;
                        }
                        charge_effect_work(
                            &mut self.instantiation_work,
                            member_count,
                            codec_phase,
                        )?;
                        for member in 0..member_count {
                            if scope
                                .handler_member(member)
                                .is_some_and(|candidate| candidate.id() == *handler)
                            {
                                selected = Some(member);
                                break;
                            }
                        }
                        if selected.is_some() {
                            break;
                        }
                    }
                    _ => {}
                }
            }
            selected.ok_or(RuntimeFailure::ForeignBinding)?
        };
        let expected = environment.instantiation.effect(
            descriptor
                .native_effect_member(selected_member)
                .ok_or(RuntimeFailure::ForeignBinding)?,
            &mut self.instantiation_work,
            Some(codec_phase),
        )?;
        if !super::same_effect_instance(&expected, effect, &mut self.instantiation_work)
            .map_err(|failure| codec_failure_phase(failure, codec_phase))?
        {
            return Err(RuntimeFailure::ForeignBinding);
        }
        let mut state_keys = Vec::new();
        let mut input = encode_input(
            &value,
            &self.heap,
            &mut state_keys,
            &mut self.instantiation_work,
            codec_phase,
        )?;
        let storage = native
            .storage
            .as_ref()
            .filter(|storage| operation.id == storage.store() || operation.id == storage.load());
        let instantiated_signature = if storage.is_some() {
            let declaration = self
                .program
                .registry()
                .effect(operation.id.owner())
                .ok_or(RuntimeFailure::ForeignBinding)?;
            if declaration.parameters.len() != effect.arguments().len() {
                return Err(RuntimeFailure::ForeignBinding);
            }
            charge_effect_work(
                &mut self.instantiation_work,
                declaration.parameters.len(),
                codec_phase,
            )?;
            struct StorageReplacements(
                std::collections::HashMap<crate::types::TypeVariableId, Type>,
            );
            impl Drop for StorageReplacements {
                fn drop(&mut self) {
                    for (_, ty) in self.0.drain() {
                        crate::types::discard_type_iteratively(ty);
                    }
                }
            }
            let mut replacements = StorageReplacements(std::collections::HashMap::new());
            replacements
                .0
                .try_reserve(declaration.parameters.len())
                .map_err(|_| {
                    foreign_failure(ForeignExecutionError::STORAGE_REFUSED, codec_phase)
                })?;
            for (parameter, argument) in declaration.parameters.iter().zip(effect.arguments()) {
                let crate::types::KindedArgument::TypeArg(argument) = argument else {
                    return Err(RuntimeFailure::ForeignBinding);
                };
                replacements.0.insert(
                    parameter.id,
                    crate::types::clone_type_with_budget(argument, &mut self.instantiation_work)
                        .map_err(|_| {
                            super::effect_work_failure(&self.instantiation_work, None, codec_phase)
                        })?,
                );
            }
            let signature = crate::types::substitute_type_variables_with(
                &operation.signature,
                &replacements.0,
                |units| charge_effect_work(&mut self.instantiation_work, units, codec_phase),
                || foreign_failure(ForeignExecutionError::STORAGE_REFUSED, codec_phase),
            )?;
            Some(crate::types::IterativeTypeOwner::new(signature))
        } else {
            None
        };
        let signature = instantiated_signature
            .as_deref()
            .unwrap_or(&operation.signature);
        let Type::Function(domain, codomain) = signature else {
            return Err(RuntimeFailure::ForeignBinding);
        };
        validate_codec(
            &input,
            domain,
            self.program.registry(),
            true,
            &mut self.instantiation_work,
            codec_phase,
        )?;
        // Resolve each original state path and its complete effect lineage.
        let mut indices = Vec::new();
        charge_effect_work(
            &mut self.instantiation_work,
            operation.state_lineage.len(),
            codec_phase,
        )?;
        indices
            .try_reserve_exact(operation.state_lineage.len())
            .map_err(|_| foreign_failure(ForeignExecutionError::STORAGE_REFUSED, codec_phase))?;
        for operand in &operation.state_lineage {
            let mut node = input.root();
            for coordinate in &operand.path {
                charge_effect_work(&mut self.instantiation_work, 1, codec_phase)?;
                let Some(ForeignDataNode::Tuple(fields)) = input.node(node) else {
                    return Err(RuntimeFailure::ForeignBinding);
                };
                node = *fields
                    .get(*coordinate)
                    .ok_or(RuntimeFailure::ForeignBinding)?;
            }
            let Some(ForeignDataNode::State(slot)) = input.node(node) else {
                return Err(RuntimeFailure::ForeignBinding);
            };
            let found = *state_keys
                .get(*slot)
                .ok_or(RuntimeFailure::ForeignBinding)?;
            let state = native
                .states
                .iter()
                .find(|state| state.id == operand.state)
                .ok_or(RuntimeFailure::ForeignBinding)?;
            let coordinate = *operand
                .lineage
                .get(state.owned_identity_position)
                .ok_or(RuntimeFailure::ForeignBinding)?;
            if Instantiation::activation_at(effect, coordinate) != Some(found) {
                return Err(RuntimeFailure::ForeignBinding);
            }
            let index = find_provider_path(&self.frames, found, &mut self.instantiation_work)
                .map_err(|failure| codec_failure_phase(failure, codec_phase))?
                .ok_or(RuntimeFailure::ForeignBinding)?;
            let candidate =
                provider_at(&self.frames, &index).ok_or(RuntimeFailure::ForeignBinding)?;
            if !self
                .provider_owner(
                    candidate,
                    index == boundary && phase == ProviderPhase::Finish,
                )
                .is_some_and(|owner| owner.state == operand.state)
                || candidate.finished.is_some()
                || !(candidate.phase == ProviderPhase::Body
                    || (index == boundary && candidate.phase == ProviderPhase::Finish))
            {
                return Err(RuntimeFailure::ForeignBinding);
            }
            indices.push(index);
        }
        let mut reference_owners = Vec::new();
        if storage.is_some() {
            charge_effect_work(&mut self.instantiation_work, indices.len(), codec_phase)?;
            reference_owners
                .try_reserve_exact(indices.len())
                .map_err(|_| {
                    foreign_failure(ForeignExecutionError::STORAGE_REFUSED, codec_phase)
                })?;
            for operand in &operation.state_lineage {
                let state = native
                    .states
                    .iter()
                    .find(|state| state.id == operand.state)
                    .ok_or(RuntimeFailure::ForeignBinding)?;
                let coordinate = *operand
                    .lineage
                    .get(state.owned_identity_position)
                    .ok_or(RuntimeFailure::ForeignBinding)?;
                reference_owners.push(
                    Instantiation::activation_at(effect, coordinate)
                        .ok_or(RuntimeFailure::ForeignBinding)?,
                );
            }
            charge_effect_work(
                &mut self.instantiation_work,
                input.nodes().len(),
                codec_phase,
            )?;
            for node in input.nodes_mut() {
                if let ForeignDataNode::Reference(reference) = node {
                    let activation = state_keys
                        .get(reference.owner_slot())
                        .ok_or(RuntimeFailure::ForeignBinding)?;
                    charge_effect_work(
                        &mut self.instantiation_work,
                        reference_owners.len(),
                        codec_phase,
                    )?;
                    let slot = reference_owners
                        .iter()
                        .position(|key| key == activation)
                        .ok_or(RuntimeFailure::ForeignBinding)?;
                    *reference = reference.with_owner_slot(slot);
                } else if let ForeignDataNode::State(slot) = node {
                    let activation = state_keys
                        .get(*slot)
                        .ok_or(RuntimeFailure::ForeignBinding)?;
                    charge_effect_work(
                        &mut self.instantiation_work,
                        reference_owners.len(),
                        codec_phase,
                    )?;
                    *slot = reference_owners
                        .iter()
                        .position(|key| key == activation)
                        .ok_or(RuntimeFailure::ForeignBinding)?;
                }
            }
        }
        self.trace_effect(EffectTraceEvent::Request(operation.id));
        match operation.role {
            ForeignOperationRole::Acquire => {
                if phase != ProviderPhase::Acquire
                    || !provider_at(&self.frames, &boundary)
                        .is_some_and(|candidate| candidate.owner.is_none())
                {
                    return Err(RuntimeFailure::ForeignBinding);
                }
                let ForeignResultFact::Acquire {
                    state,
                    error,
                    constructors,
                    retained_parameters,
                    ..
                } = &operation.result
                else {
                    return Err(RuntimeFailure::ForeignBinding);
                };
                let mut dependencies = Vec::new();
                charge_effect_work(
                    &mut self.instantiation_work,
                    indices.len(),
                    RuntimePhase::Acquisition,
                )?;
                dependencies.try_reserve_exact(indices.len()).map_err(|_| {
                    foreign_failure(ForeignExecutionError::STORAGE_REFUSED, codec_phase)
                })?;
                for (index, operand) in indices.iter().zip(operation.state_lineage.iter()) {
                    let state_fact = native
                        .states
                        .iter()
                        .find(|state| state.id == operand.state)
                        .ok_or(RuntimeFailure::ForeignBinding)?;
                    if operand
                        .lineage
                        .get(state_fact.owned_identity_position)
                        .is_some_and(|coordinate| retained_parameters.contains(coordinate))
                    {
                        let candidate = provider_at(&self.frames, index)
                            .ok_or(RuntimeFailure::ForeignBinding)?;
                        let owner = candidate
                            .owner
                            .as_ref()
                            .ok_or(RuntimeFailure::ForeignBinding)?;
                        if !dependencies.contains(&owner.identity) {
                            dependencies.push(owner.identity)
                        }
                    }
                }
                charge_effect_work(
                    &mut self.instantiation_work,
                    indices.len(),
                    RuntimePhase::Access,
                )?;
                let mut views = Vec::new();
                views.try_reserve_exact(indices.len()).map_err(|_| {
                    foreign_failure(ForeignExecutionError::STORAGE_REFUSED, codec_phase)
                })?;
                for index in &indices {
                    let candidate =
                        provider_at(&self.frames, index).ok_or(RuntimeFailure::ForeignBinding)?;
                    let owner = candidate
                        .owner
                        .as_ref()
                        .ok_or(RuntimeFailure::ForeignBinding)?;
                    views.push(owner.payload.as_ref());
                }
                let runtime = self
                    .foreign_runtime
                    .as_ref()
                    .ok_or(RuntimeFailure::ForeignBinding)?;
                let binding = runtime
                    .binding(native)
                    .map_err(|_| RuntimeFailure::ForeignBinding)?;
                let operation_key = binding
                    .operation_key(native, operation)
                    .map_err(|_| RuntimeFailure::ForeignBinding)?;
                // Reserve report publication before handing any native state over.
                self.heap
                    .try_reserve(1)
                    .map_err(|_| RuntimeFailure::HeapCapacity)?;
                let acquired = binding
                    .executable()
                    .acquire(operation_key, native, &input, &views)
                    .map_err(|error| foreign_failure(error, RuntimePhase::Acquisition))?;
                drop(views);
                let report = match acquired {
                    ForeignAcquisition::Refused(error_data) => {
                        validate_codec(
                            &error_data,
                            &Type::Nominal(*error),
                            self.program.registry(),
                            false,
                            &mut self.instantiation_work,
                            RuntimePhase::Acquisition,
                        )?;
                        let error = decode_data(
                            &error_data,
                            &mut self.heap,
                            &mut self.instantiation_work,
                            RuntimePhase::Acquisition,
                        )?;
                        self.foreign_constructor(
                            *constructors.get(1).ok_or(RuntimeFailure::ForeignBinding)?,
                            Some(error),
                            codec_phase,
                        )?
                    }
                    ForeignAcquisition::Acquired(payload) => {
                        let owner = self
                            .foreign_runtime
                            .as_mut()
                            .ok_or(RuntimeFailure::ForeignBinding)?
                            .guard(payload, *state, dependencies)
                            .map_err(|error| foreign_failure(error, RuntimePhase::Acquisition))?;
                        let report = self.foreign_constructor(
                            *constructors.first().ok_or(RuntimeFailure::ForeignBinding)?,
                            Some(Value::NativeStateView(key)),
                            codec_phase,
                        )?;
                        let candidate = provider_at_mut(&mut self.frames, &boundary)
                            .ok_or(RuntimeFailure::ForeignBinding)?;
                        candidate.owner = Some(owner);
                        report
                    }
                };
                self.control = Some(Control::Return(report));
            }
            ForeignOperationRole::Borrow => {
                if !matches!(phase, ProviderPhase::Body | ProviderPhase::Finish)
                    || !provider_at(&self.frames, &boundary).is_some_and(|candidate| {
                        candidate.finished.is_none()
                            && self
                                .provider_owner(candidate, phase == ProviderPhase::Finish)
                                .is_some()
                    })
                {
                    return Err(RuntimeFailure::ForeignBinding);
                }
                charge_effect_work(
                    &mut self.instantiation_work,
                    indices.len(),
                    RuntimePhase::Access,
                )?;
                let mut views = Vec::new();
                views.try_reserve_exact(indices.len()).map_err(|_| {
                    foreign_failure(ForeignExecutionError::STORAGE_REFUSED, codec_phase)
                })?;
                // Borrow only the owner forest/runtime, so the same views stay
                // live while the disjoint heap and work ledger admit the reply.
                let runtime = self
                    .foreign_runtime
                    .as_deref()
                    .ok_or(RuntimeFailure::ForeignBinding)?;
                for index in &indices {
                    let candidate =
                        provider_at(&self.frames, index).ok_or(RuntimeFailure::ForeignBinding)?;
                    let owner = provider_owner(
                        Some(runtime),
                        candidate,
                        index == &boundary && phase == ProviderPhase::Finish,
                    )
                    .ok_or(RuntimeFailure::ForeignBinding)?;
                    views.push(owner.payload.as_ref());
                }
                let binding = runtime
                    .binding(native)
                    .map_err(|_| RuntimeFailure::ForeignBinding)?;
                let operation_key = binding
                    .operation_key(native, operation)
                    .map_err(|_| RuntimeFailure::ForeignBinding)?;
                // Lend only a debit operation, never the ledger or an owner.
                // Keep the first measured failure even if a binding ignores
                // its charge result; a refused preparation cannot publish.
                let mut preparation_failure = None;
                let invocation = {
                    let mut charge = |units| {
                        if preparation_failure.is_some() {
                            return Err(ForeignExecutionError::WORK_EXHAUSTED);
                        }
                        charge_effect_work(
                            &mut self.instantiation_work,
                            units,
                            RuntimePhase::Access,
                        )
                        .map_err(|failure| {
                            preparation_failure = Some(failure);
                            ForeignExecutionError::WORK_EXHAUSTED
                        })
                    };
                    let mut work = crate::foreign::runtime::ForeignInvocationWork::new(&mut charge);
                    binding.executable().prepare_invoke_with_work(
                        operation_key,
                        native,
                        &input,
                        &views,
                        &mut work,
                    )
                };
                if let Some(failure) = preparation_failure {
                    return Err(failure);
                }
                let invocation =
                    invocation.map_err(|error| foreign_failure(error, RuntimePhase::Access))?;
                let (output, pending) = match invocation {
                    ForeignInvocation::Immediate(output) => (output, None),
                    ForeignInvocation::Prepared { output, commit } => {
                        charge_effect_work(&mut self.instantiation_work, 1, RuntimePhase::Access)?;
                        charge_effect_work(
                            &mut self.instantiation_work,
                            views.len(),
                            RuntimePhase::Access,
                        )?;
                        (output, Some(commit))
                    }
                };
                validate_codec(
                    &output,
                    codomain,
                    self.program.registry(),
                    false,
                    &mut self.instantiation_work,
                    RuntimePhase::Access,
                )?;
                let value = decode_data_with_owners(
                    &output,
                    &mut self.heap,
                    &mut self.instantiation_work,
                    RuntimePhase::Access,
                    &reference_owners,
                )?;
                if let Some(commit) = pending {
                    // All evaluator admission and association work is paid.
                    // The original key/module and the same live views remain
                    // borrowed; successful commit is followed only by return.
                    commit
                        .commit(operation_key, native, &views)
                        .map_err(|error| foreign_failure(error, RuntimePhase::Access))?;
                }
                drop(views);
                self.control = Some(Control::Return(value));
            }
            ForeignOperationRole::Finish => {
                if phase != ProviderPhase::Finish
                    || indices.len() != 1
                    || indices.first() != Some(&boundary)
                {
                    return Err(RuntimeFailure::ForeignBinding);
                }
                let ForeignResultFact::Finish {
                    error,
                    constructors,
                    ..
                } = &operation.result
                else {
                    return Err(RuntimeFailure::ForeignBinding);
                };
                self.charge_quarantine_lookup()?;
                let candidate =
                    provider_at(&self.frames, &boundary).ok_or(RuntimeFailure::ForeignBinding)?;
                if candidate.finished.is_some() {
                    return Err(RuntimeFailure::ForeignBinding);
                }
                let identity = self
                    .provider_owner(candidate, true)
                    .ok_or(RuntimeFailure::ForeignBinding)?
                    .identity;
                let quarantined = candidate.quarantined_owner.is_some();
                let runtime = self
                    .foreign_runtime
                    .as_mut()
                    .ok_or(RuntimeFailure::ForeignBinding)?;
                let outcome = if quarantined {
                    runtime
                        .finish_quarantined(identity, native, operation)
                        .map_err(|error| foreign_failure(error, RuntimePhase::Cleanup))?
                } else {
                    let context = crate::foreign::runtime::ForeignFinishContext {
                        retained_dependents: runtime.retained_dependents(identity),
                    };
                    let binding = runtime
                        .binding(native)
                        .map_err(|_| RuntimeFailure::ForeignBinding)?;
                    let operation_key = binding
                        .operation_key(native, operation)
                        .map_err(|_| RuntimeFailure::ForeignBinding)?;
                    let candidate = provider_at_mut(&mut self.frames, &boundary)
                        .ok_or(RuntimeFailure::ForeignBinding)?;
                    let owner = candidate
                        .owner
                        .as_mut()
                        .ok_or(RuntimeFailure::ForeignBinding)?;
                    let outcome = binding
                        .executable()
                        .finish(operation_key, native, owner.payload.as_mut(), context)
                        .map_err(|error| foreign_failure(error, RuntimePhase::Cleanup))?;
                    if context.retained_dependents
                        && !matches!(outcome, ForeignCompletion::RetainedError(_))
                    {
                        return Err(RuntimeFailure::ForeignBinding);
                    }
                    outcome
                };
                let candidate = provider_at_mut(&mut self.frames, &boundary)
                    .ok_or(RuntimeFailure::ForeignBinding)?;
                candidate.finished = Some(match &outcome {
                    ForeignCompletion::Closed => ProviderFinish::Closed,
                    ForeignCompletion::ConsumedError(_) => ProviderFinish::ConsumedError,
                    ForeignCompletion::RetainedError(_) => ProviderFinish::RetainedError,
                });
                if candidate.finished == Some(ProviderFinish::RetainedError) {
                    if let Some(owner) = candidate.owner.take() {
                        candidate.quarantined_owner = Some(owner.identity);
                        self.quarantine_provider_owner(owner)?;
                    }
                } else {
                    drop(candidate.owner.take());
                }
                let report = match outcome {
                    ForeignCompletion::Closed => self.foreign_constructor(
                        *constructors.first().ok_or(RuntimeFailure::ForeignBinding)?,
                        None,
                        codec_phase,
                    )?,
                    ForeignCompletion::ConsumedError(data)
                    | ForeignCompletion::RetainedError(data) => {
                        let retained =
                            provider_at(&self.frames, &boundary).is_some_and(|candidate| {
                                candidate.finished == Some(ProviderFinish::RetainedError)
                            });
                        let converted = (|| {
                            let data = data
                                .map_err(|error| foreign_failure(error, RuntimePhase::Cleanup))?;
                            validate_codec(
                                &data,
                                &Type::Nominal(*error),
                                self.program.registry(),
                                false,
                                &mut self.instantiation_work,
                                RuntimePhase::Cleanup,
                            )?;
                            decode_data(
                                &data,
                                &mut self.heap,
                                &mut self.instantiation_work,
                                RuntimePhase::Cleanup,
                            )
                        })();
                        let error = match converted {
                            Ok(error) => error,
                            Err(failure) => {
                                return Err(failure);
                            }
                        };
                        let payload = if retained {
                            self.foreign_tuple(&[Value::NativeStateView(key), error], codec_phase)?
                        } else {
                            error
                        };
                        self.foreign_constructor(
                            *constructors
                                .get(if retained { 2 } else { 1 })
                                .ok_or(RuntimeFailure::ForeignBinding)?,
                            Some(payload),
                            codec_phase,
                        )?
                    }
                };
                self.control = Some(Control::Return(report));
            }
        }
        Ok(())
    }
}

/// A frame path borrows one unique owner through suspended control. It carries
/// no native owner and cannot recreate or duplicate an activation.
fn find_provider_path(
    frames: &[Frame],
    key: ActivationKey,
    work: &mut crate::types::TypeWorkBudget,
) -> Result<Option<Vec<usize>>, RuntimeFailure> {
    find_provider_path_matching(frames, |boundary| boundary.key == key, work)
}
fn find_provider_path_matching(
    frames: &[Frame],
    matches: impl Fn(&ProviderBoundary) -> bool,
    work: &mut crate::types::TypeWorkBudget,
) -> Result<Option<Vec<usize>>, RuntimeFailure> {
    charge_effect_work(work, 1, RuntimePhase::Access)?;
    let mut pending = Vec::new();
    pending
        .try_reserve(1)
        .map_err(|_| RuntimeFailure::HeapCapacity)?;
    pending.push((frames, frames.len()));
    let mut path = Vec::new();
    loop {
        let Some((_, next)) = pending.last() else {
            return Ok(None);
        };
        if *next == 0 {
            pending.pop();
            path.pop();
            continue;
        }
        let (frames, index) = {
            let (frames, next) = pending
                .last_mut()
                .ok_or(RuntimeFailure::InvalidControlState)?;
            *next -= 1;
            (*frames, *next)
        };
        let frame = &frames[index];
        charge_effect_work(work, 1, RuntimePhase::Access)?;
        path.try_reserve(1)
            .map_err(|_| RuntimeFailure::HeapCapacity)?;
        path.push(index);
        match frame {
            Frame::ProviderBoundary(boundary) if matches(boundary) => return Ok(Some(path)),
            Frame::ClauseBoundary {
                continuation: Some(captured),
                ..
            } => {
                charge_effect_work(work, 1, RuntimePhase::Access)?;
                pending
                    .try_reserve(1)
                    .map_err(|_| RuntimeFailure::HeapCapacity)?;
                pending.push((&captured.frames, captured.frames.len()));
            }
            _ => {
                path.pop();
            }
        }
    }
}
fn provider_at<'a>(mut frames: &'a [Frame], path: &[usize]) -> Option<&'a ProviderBoundary> {
    let (last, parents) = path.split_last()?;
    for index in parents {
        let Frame::ClauseBoundary {
            continuation: Some(captured),
            ..
        } = frames.get(*index)?
        else {
            return None;
        };
        frames = &captured.frames;
    }
    match frames.get(*last)? {
        Frame::ProviderBoundary(boundary) => Some(boundary),
        _ => None,
    }
}
fn provider_at_mut<'a>(
    mut frames: &'a mut [Frame],
    path: &[usize],
) -> Option<&'a mut ProviderBoundary> {
    let (last, parents) = path.split_last()?;
    for index in parents {
        let Frame::ClauseBoundary {
            continuation: Some(captured),
            ..
        } = frames.get_mut(*index)?
        else {
            return None;
        };
        frames = &mut captured.frames;
    }
    match frames.get_mut(*last)? {
        Frame::ProviderBoundary(boundary) => Some(boundary),
        _ => None,
    }
}

#[cfg(test)]
mod integer_codec_tests {
    use super::*;

    fn large_integer() -> crate::integer::Integer {
        crate::integer::Integer::parse_decimal(
            "999999999999999999999999999999999999999999999999999999999999999999",
        )
        .unwrap()
    }

    #[test]
    fn codec_budget_refusal_retains_phase_and_erased_clone_cause() {
        let data = ForeignData::new(vec![ForeignDataNode::Unit], 0).unwrap();
        let registry = crate::resolved::ResolvedRegistry::default();
        for phase in [
            RuntimePhase::Acquisition,
            RuntimePhase::Access,
            RuntimePhase::Cleanup,
        ] {
            let failure = validate_codec(
                &data,
                &Type::Unit,
                &registry,
                false,
                &mut TypeWorkBudget::with_limit(0),
                phase,
            )
            .unwrap_err();
            let RuntimeFailure::Report(report) = failure else {
                panic!("erased structural-clone resource refusal must not become a binding error");
            };
            let details = report.primary.resource().unwrap();
            assert_eq!(details.phase, phase);
            assert_eq!(
                details.cause,
                super::super::ResourceFailureCause::ResourceAdmissionRefused
            );
            assert_eq!(
                details.resource,
                super::super::RuntimeResource::ForeignAdmission
            );
            assert_eq!(details.requested, None);
            assert_eq!(details.available, None);
            for failure in [
                encode_input(
                    &Value::Unit,
                    &[],
                    &mut Vec::new(),
                    &mut TypeWorkBudget::with_limit(0),
                    phase,
                )
                .unwrap_err(),
                decode_data(
                    &data,
                    &mut Vec::new(),
                    &mut TypeWorkBudget::with_limit(0),
                    phase,
                )
                .unwrap_err(),
            ] {
                let RuntimeFailure::Report(report) = failure else {
                    panic!("structured codec work refusal");
                };
                let details = report.primary.resource().unwrap();
                assert_eq!(details.phase, phase);
                assert_eq!(
                    details.cause,
                    super::super::ResourceFailureCause::WorkBudgetExhausted
                );
                assert_eq!(details.resource, super::super::RuntimeResource::WorkUnits);
                assert_eq!(details.requested, Some(1));
                assert_eq!(details.available, Some(0));
            }
        }
        assert_eq!(
            validate_codec(
                &data,
                &Type::Int,
                &registry,
                false,
                &mut TypeWorkBudget::unbounded(),
                RuntimePhase::Access
            )
            .unwrap_err()
            .reason_code(),
            RuntimeFailure::ForeignBinding.reason_code()
        );
    }

    #[test]
    fn generic_codec_preserves_integers_beyond_native_range() {
        let integer = large_integer();
        assert_eq!(integer.to_i64(), None);
        let expected = integer.to_string();
        let encoded = encode_input(
            &Value::Integer(integer),
            &[],
            &mut Vec::new(),
            &mut TypeWorkBudget::unbounded(),
            RuntimePhase::Access,
        )
        .unwrap();
        let decoded = decode_data(
            &encoded,
            &mut Vec::new(),
            &mut TypeWorkBudget::unbounded(),
            RuntimePhase::Access,
        )
        .unwrap();
        assert_eq!(decoded.to_string(), expected);
    }

    #[test]
    fn integer_codec_copy_work_refuses_before_native_range_conversion() {
        let integer = large_integer();
        let bytes = usize::try_from(integer.magnitude_byte_length())
            .unwrap()
            .max(1);
        let encoded = ForeignData::new(vec![ForeignDataNode::Integer(integer.clone())], 0).unwrap();
        for failure in [
            encode_input(
                &Value::Integer(integer),
                &[],
                &mut Vec::new(),
                &mut TypeWorkBudget::with_limit(bytes + 1),
                RuntimePhase::Access,
            )
            .unwrap_err(),
            decode_data(
                &encoded,
                &mut Vec::new(),
                &mut TypeWorkBudget::with_limit(bytes + 1),
                RuntimePhase::Access,
            )
            .unwrap_err(),
        ] {
            let RuntimeFailure::Report(report) = failure else {
                panic!("structured work failure")
            };
            let details = report.primary.resource().unwrap();
            assert_eq!(
                details.cause,
                crate::eval::ResourceFailureCause::WorkBudgetExhausted
            );
            assert_eq!(details.phase, RuntimePhase::Access);
            assert_eq!(details.resource, crate::eval::RuntimeResource::WorkUnits);
            assert_eq!(details.requested, Some(bytes));
            assert_eq!(details.available, Some(bytes - 1));
        }
    }
}
