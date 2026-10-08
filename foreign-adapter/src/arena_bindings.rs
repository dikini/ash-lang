//! Minimal real native arena lifecycle through the generic Ash runtime.
// Scalar storage uses authenticated dictionaries and deferred publication.
#[path = "arena_codec.rs"]
mod codec;

use crate::arena::{
    AllocationError, AllocationKey, Arena, ArenaInitError, LayoutTag, PayloadLayout,
    PreparedAllocation, Usage,
};
use ash::foreign::{
    ForeignManifest, ForeignModuleFact, ForeignScalarEncoding, arena_manifest,
    runtime::{
        ExecutableForeignModule, ForeignAcquisition, ForeignCompletion, ForeignData,
        ForeignDataNode, ForeignExecutionError, ForeignFinishContext, ForeignInvocation,
        ForeignInvocationWork, ForeignLayoutWitness, ForeignOperationKey, ForeignReference,
        ForeignRuntimeBinding, NativeInvocationCommit, NativeResourceOwner,
    },
    typed_arena_manifest,
};
use std::{any::Any, cell::RefCell, num::NonZeroU64, rc::Rc, sync::Arc};

/// Observations of actual native arena owners and lifecycle calls.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ArenaEvent {
    /// The native constructor returned a real backing owner.
    Acquired {
        /// Observation-only activation sequence, granting no source authority.
        activation: u64,
        /// Counters read from the newly constructed native owner.
        usage: Usage,
    },
    /// A borrowed query read the actual owner's native counters.
    Usage {
        /// Observation-only activation sequence.
        activation: u64,
        /// Counters read from the native owner.
        usage: Usage,
    },
    /// A prepared store committed actual payload bytes and an object record.
    Stored {
        /// Observation-only activation sequence.
        activation: u64,
        /// Published physical identity, granting no Ash reference authority.
        allocation: AllocationKey,
        /// Physical encoded extent and alignment.
        layout: PayloadLayout,
        /// Counters read after native publication.
        usage: Usage,
    },
    /// A load read the published object's actual backing bytes.
    Loaded {
        /// Observation-only activation sequence.
        activation: u64,
        /// Physical identity checked against the live backing owner.
        allocation: AllocationKey,
        /// Physical discriminator checked against the published record.
        layout: LayoutTag,
        /// Actual backing byte extent read, including zero-size objects.
        bytes_read: usize,
        /// Counters read from the native owner.
        usage: Usage,
    },
    /// The backing owner was dropped before this event was recorded.
    Released {
        /// Observation-only activation sequence.
        activation: u64,
        /// True for guarded host destruction rather than source completion.
        host_teardown: bool,
    },
    /// Configuration validation or native acquisition refused publication.
    Refused,
}
#[derive(Debug, Default)]
struct ObservationState {
    events: Vec<ArenaEvent>,
    outstanding: usize,
    next_activation: u64,
}
/// Readable observations remain alive after source owners have completed.
#[derive(Clone, Debug, Default)]
pub struct ArenaObservations(Rc<RefCell<ObservationState>>);
impl ArenaObservations {
    /// Returns native observations, including distinct host destruction.
    #[must_use]
    pub fn events(&self) -> Vec<ArenaEvent> {
        self.0.borrow().events.clone()
    }
    fn reserve(&self, extra: usize) -> Result<(), ForeignExecutionError> {
        let mut state = self.0.borrow_mut();
        let needed = state
            .outstanding
            .checked_add(extra)
            .ok_or(ForeignExecutionError(
                "arena observation capacity exhausted",
            ))?;
        state
            .events
            .try_reserve(needed)
            .map_err(|_| ForeignExecutionError::STORAGE_REFUSED)
    }
    fn record(&self, event: ArenaEvent) {
        self.0.borrow_mut().events.push(event)
    }
    fn reserve_acquisition(&self) -> Result<(), ForeignExecutionError> {
        self.reserve(2)?;
        let state = self.0.borrow();
        state
            .next_activation
            .checked_add(1)
            .ok_or(ForeignExecutionError(
                "arena observation identities exhausted",
            ))?;
        state
            .outstanding
            .checked_add(1)
            .ok_or(ForeignExecutionError(
                "arena observation ownership exhausted",
            ))?;
        Ok(())
    }
    fn acquire(&self, usage: Usage) -> u64 {
        let mut state = self.0.borrow_mut();
        let activation = state.next_activation;
        state.next_activation += 1;
        state.outstanding += 1;
        state
            .events
            .push(ArenaEvent::Acquired { activation, usage });
        activation
    }
    fn release(&self, activation: u64, host_teardown: bool) {
        let mut state = self.0.borrow_mut();
        state.outstanding -= 1;
        state.events.push(ArenaEvent::Released {
            activation,
            host_teardown,
        });
    }
}
#[derive(Debug)]
struct ArenaOwner {
    arena: RefCell<Option<Arena>>,
    observations: ArenaObservations,
    activation: u64,
}
impl NativeResourceOwner for ArenaOwner {
    fn as_any(&self) -> &dyn Any {
        self
    }
    fn as_any_mut(&mut self) -> &mut dyn Any {
        self
    }
}
impl Drop for ArenaOwner {
    fn drop(&mut self) {
        if let Some(arena) = self.arena.get_mut().take() {
            drop(arena);
            self.observations.release(self.activation, true)
        }
    }
}
#[derive(Debug)]
struct ArenaBinding {
    observations: ArenaObservations,
}
/// Binds the exact lifecycle or explicitly opted-in typed arena manifest.
/// # Errors
/// Rejects any different schema before acquiring native backing.
pub fn arena_binding(
    manifest: Arc<ForeignManifest>,
    observations: ArenaObservations,
) -> Result<ForeignRuntimeBinding, ForeignExecutionError> {
    let expected = arena_manifest(manifest.id())
        .map_err(|_| ForeignExecutionError("invalid arena manifest"))?;
    let typed = typed_arena_manifest(manifest.id())
        .map_err(|_| ForeignExecutionError("invalid typed arena manifest"))?;
    if manifest.as_ref() != &expected && manifest.as_ref() != &typed {
        return Err(ForeignExecutionError("arena executable manifest mismatch"));
    }
    Ok(ForeignRuntimeBinding::new(
        manifest,
        Box::new(ArenaBinding { observations }),
    ))
}
fn error(module: &ForeignModuleFact, name: &str) -> Result<ForeignData, ForeignExecutionError> {
    let id = *module
        .constructors
        .get(name)
        .ok_or(ForeignExecutionError("arena error constructor absent"))?;
    let mut nodes = Vec::new();
    nodes
        .try_reserve_exact(1)
        .map_err(|_| ForeignExecutionError::STORAGE_REFUSED)?;
    nodes.push(ForeignDataNode::Constructor(id, None));
    ForeignData::new(nodes, 0)
}
impl ExecutableForeignModule for ArenaBinding {
    fn preflight(&self, module: &ForeignModuleFact) -> Result<(), ForeignExecutionError> {
        let expected = arena_manifest(module.manifest().id())
            .map_err(|_| ForeignExecutionError("invalid arena manifest"))?;
        let typed = typed_arena_manifest(module.manifest().id())
            .map_err(|_| ForeignExecutionError("invalid typed arena manifest"))?;
        let legacy = module.manifest().as_ref() == &expected && module.operations.len() == 3;
        let storage = module.manifest().as_ref() == &typed
            && module.operations.len() == 5
            && module.storage.is_some()
            && module.layout.is_some();
        if !legacy && !storage {
            return Err(ForeignExecutionError("arena executable facts mismatch"));
        }
        for name in [
            "ArenaConfig",
            "InvalidArenaConfig",
            "ArenaAllocationFailed",
            "ArenaFinishInvariant",
            "Acquired",
            "Refused",
            "Consumed",
            "ConsumedFailure",
            "Retained",
        ] {
            if !module.constructors.contains_key(name) {
                return Err(ForeignExecutionError("arena executable codec missing"));
            }
        }
        Ok(())
    }
    fn acquire(
        &self,
        key: ForeignOperationKey,
        module: &ForeignModuleFact,
        input: &ForeignData,
        states: &[&dyn NativeResourceOwner],
    ) -> Result<ForeignAcquisition, ForeignExecutionError> {
        if (key.effect, key.operation) != (0, 0) || !states.is_empty() {
            return Err(ForeignExecutionError("arena acquisition role mismatch"));
        }
        let Some(ForeignDataNode::Constructor(config, Some(payload))) = input.node(input.root())
        else {
            return Err(ForeignExecutionError("arena configuration codec mismatch"));
        };
        if Some(config) != module.constructors.get("ArenaConfig") {
            return Err(ForeignExecutionError(
                "arena configuration constructor mismatch",
            ));
        }
        let Some(ForeignDataNode::Tuple(fields)) = input.node(*payload) else {
            return Err(ForeignExecutionError(
                "arena configuration payload mismatch",
            ));
        };
        if fields.len() != 2 {
            return Err(ForeignExecutionError("arena configuration arity mismatch"));
        }
        let integer = |index| match input.node(index) {
            Some(ForeignDataNode::Integer(value)) => {
                Ok(value.to_i64().and_then(|value| usize::try_from(value).ok()))
            }
            _ => Err(ForeignExecutionError(
                "arena configuration integer mismatch",
            )),
        };
        let bytes = integer(fields[0])?;
        let slots = integer(fields[1])?;
        // Reserve both acquisition and later destruction observations first.
        self.observations.reserve_acquisition()?;
        let (Some(bytes), Some(slots)) = (bytes, slots) else {
            self.observations.record(ArenaEvent::Refused);
            return Ok(ForeignAcquisition::Refused(error(
                module,
                "InvalidArenaConfig",
            )?));
        };
        match Arena::new(bytes, slots) {
            Ok(arena) => {
                let activation = self.observations.acquire(arena.usage());
                Ok(ForeignAcquisition::Acquired(Box::new(ArenaOwner {
                    arena: RefCell::new(Some(arena)),
                    observations: self.observations.clone(),
                    activation,
                })))
            }
            Err(ArenaInitError::InvalidConfiguration) => {
                self.observations.record(ArenaEvent::Refused);
                Ok(ForeignAcquisition::Refused(error(
                    module,
                    "InvalidArenaConfig",
                )?))
            }
            Err(ArenaInitError::AllocationFailed) => {
                self.observations.record(ArenaEvent::Refused);
                Ok(ForeignAcquisition::Refused(error(
                    module,
                    "ArenaAllocationFailed",
                )?))
            }
            Err(ArenaInitError::IdentityExhausted) => {
                Err(ForeignExecutionError("native arena identities exhausted"))
            }
        }
    }
    fn invoke(
        &self,
        key: ForeignOperationKey,
        _module: &ForeignModuleFact,
        _input: &ForeignData,
        states: &[&dyn NativeResourceOwner],
    ) -> Result<ForeignData, ForeignExecutionError> {
        if (key.effect, key.operation) != (0, 1) || states.len() != 1 {
            return Err(ForeignExecutionError("arena borrowed role mismatch"));
        }
        let owner = states[0]
            .as_any()
            .downcast_ref::<ArenaOwner>()
            .ok_or(ForeignExecutionError("arena borrowed state mismatch"))?;
        let arena = owner.arena.borrow();
        let usage = arena
            .as_ref()
            .ok_or(ForeignExecutionError("arena usage after completion"))?
            .usage();
        self.observations.reserve(1)?;
        self.observations.record(ArenaEvent::Usage {
            activation: owner.activation,
            usage,
        });
        let mut nodes = Vec::new();
        nodes
            .try_reserve_exact(5)
            .map_err(|_| ForeignExecutionError::STORAGE_REFUSED)?;
        for value in [
            usage.used_payload_bytes,
            usage.payload_capacity,
            usage.object_count,
            usage.object_capacity,
        ] {
            nodes.push(ForeignDataNode::Integer(ash::integer::Integer::from_i64(
                i64::try_from(value)
                    .map_err(|_| ForeignExecutionError("arena native usage exceeds Int codec"))?,
            )));
        }
        let mut fields = Vec::new();
        fields
            .try_reserve_exact(4)
            .map_err(|_| ForeignExecutionError::STORAGE_REFUSED)?;
        fields.extend([0, 1, 2, 3]);
        nodes.push(ForeignDataNode::Tuple(fields.into_boxed_slice()));
        ForeignData::new(nodes, 4)
    }
    fn prepare_invoke_with_work(
        &self,
        key: ForeignOperationKey,
        module: &ForeignModuleFact,
        input: &ForeignData,
        states: &[&dyn NativeResourceOwner],
        work: &mut ForeignInvocationWork<'_>,
    ) -> Result<ForeignInvocation, ForeignExecutionError> {
        let Some(storage) = &module.storage else {
            return self.prepare_invoke(key, module, input, states);
        };
        let operation = module
            .effects
            .get(key.effect)
            .filter(|effect| **effect == storage.effect())
            .and_then(|_| {
                module.operations.iter().find(|operation| {
                    operation.id.owner() == storage.effect()
                        && operation.id.operation() as usize == key.operation
                })
            });
        let Some(operation) = operation else {
            return self.prepare_invoke(key, module, input, states);
        };
        if states.len() != 1 {
            return Err(ForeignExecutionError("arena storage owner count differs"));
        }
        work.charge(8)?;
        let owner = states[0]
            .as_any()
            .downcast_ref::<ArenaOwner>()
            .ok_or(ForeignExecutionError("arena storage owner differs"))?;
        if !Rc::ptr_eq(&owner.observations.0, &self.observations.0) {
            return Err(ForeignExecutionError("arena storage binding owner differs"));
        }
        let ForeignDataNode::Tuple(fields) = input
            .node(input.root())
            .ok_or(ForeignExecutionError("arena storage input absent"))?
        else {
            return Err(ForeignExecutionError("arena storage input differs"));
        };
        let store = operation.id == storage.store();
        if fields.len() != if store { 4 } else { 3 } || (!store && operation.id != storage.load()) {
            return Err(ForeignExecutionError("arena storage operation differs"));
        }
        if !matches!(input.node(fields[0]), Some(ForeignDataNode::State(0))) {
            return Err(ForeignExecutionError("arena storage owner slot differs"));
        }
        let Some(ForeignDataNode::LayoutWitness(witness)) = input.node(fields[1]) else {
            return Err(ForeignExecutionError("arena storage witness absent"));
        };
        authenticate_layout(module, witness)?;
        let dictionary = witness.dictionary();
        let (kind, tag) = scalar_layout(witness)?;
        if store {
            let Some(ForeignDataNode::Integer(alignment)) = input.node(fields[2]) else {
                return Err(ForeignExecutionError("arena storage alignment differs"));
            };
            work.charge(
                usize::try_from(alignment.magnitude_byte_length())
                    .map_err(|_| ForeignExecutionError::WORK_EXHAUSTED)?
                    .max(1),
            )?;
            let Some(alignment) = alignment
                .to_i64()
                .and_then(|value| usize::try_from(value).ok())
            else {
                return allocation_refusal(module, AllocationError::InvalidAlignment, work)
                    .map(ForeignInvocation::Immediate);
            };
            let value = input
                .node(fields[3])
                .ok_or(ForeignExecutionError("arena stored value absent"))?;
            if !scalar_node_matches(kind, value) {
                return Err(ForeignExecutionError(
                    "arena scalar witness differs from value",
                ));
            }
            let payload = match codec::prepare_scalar_with_work(tag, value, work) {
                Ok(payload) => payload,
                Err(codec::PreparationError::Refused(error)) => {
                    return allocation_refusal(module, error, work)
                        .map(ForeignInvocation::Immediate);
                }
                Err(codec::PreparationError::Internal(error)) => return Err(error),
            };
            if payload.layout().size() != dictionary.size()
                || payload.layout().natural_alignment() != dictionary.natural_alignment()
            {
                return Err(ForeignExecutionError(
                    "arena encoded layout differs from dictionary",
                ));
            }
            let prepared = {
                let arena = owner
                    .arena
                    .try_borrow()
                    .map_err(|_| ForeignExecutionError("arena owner already borrowed"))?;
                let arena = arena
                    .as_ref()
                    .ok_or(ForeignExecutionError("arena storage after completion"))?;
                match arena.prepare_allocation(payload.layout(), alignment) {
                    Ok(prepared) => prepared,
                    Err(error) => {
                        return allocation_refusal(module, error, work)
                            .map(ForeignInvocation::Immediate);
                    }
                }
            };
            work.charge(6)?;
            self.observations.reserve(1)?;
            let candidate = prepared.candidate_key();
            let reference = ForeignReference::candidate(
                witness.clone(),
                0,
                NonZeroU64::new(candidate.owner_id())
                    .ok_or(ForeignExecutionError("arena owner identity is zero"))?,
                NonZeroU64::new(candidate.object_id())
                    .ok_or(ForeignExecutionError("arena object identity is zero"))?,
            );
            let mut nodes = Vec::new();
            nodes
                .try_reserve_exact(2)
                .map_err(|_| ForeignExecutionError::STORAGE_REFUSED)?;
            nodes.push(ForeignDataNode::Reference(reference));
            nodes.push(ForeignDataNode::Constructor(
                storage.allocated_constructor(),
                Some(0),
            ));
            let output = ForeignData::new(nodes, 1)?;
            Ok(ForeignInvocation::Prepared {
                output,
                commit: Box::new(ArenaStoreCommit {
                    module: Arc::clone(module.manifest()),
                    key,
                    witness: witness.clone(),
                    activation: owner.activation,
                    observations: self.observations.clone(),
                    prepared,
                    payload,
                }),
            })
        } else {
            let Some(ForeignDataNode::Reference(reference)) = input.node(fields[2]) else {
                return Err(ForeignExecutionError("arena load reference absent"));
            };
            if reference.owner_slot() != 0
                || reference.witness().dictionary().as_ref() != dictionary.as_ref()
            {
                return Err(ForeignExecutionError(
                    "arena load reference context differs",
                ));
            }
            let allocation = AllocationKey::from_ids(
                reference.native_owner().get(),
                reference.native_object().get(),
            )
            .ok_or(ForeignExecutionError("arena load key invalid"))?;
            let arena = owner
                .arena
                .try_borrow()
                .map_err(|_| ForeignExecutionError("arena owner already borrowed"))?;
            let arena = arena
                .as_ref()
                .ok_or(ForeignExecutionError("arena load after completion"))?;
            let bytes = arena
                .read(allocation, tag)
                .map_err(|_| ForeignExecutionError("arena load key differs"))?;
            if bytes.len() != dictionary.size() {
                return Err(ForeignExecutionError("arena loaded extent differs"));
            }
            let output = codec::decode_scalar_with_work(kind, bytes, work)?;
            work.charge(1)?;
            self.observations.reserve(1)?;
            let bytes_read = bytes.len();
            Ok(ForeignInvocation::Prepared {
                output,
                commit: Box::new(ArenaLoadCommit {
                    module: Arc::clone(module.manifest()),
                    key,
                    witness: witness.clone(),
                    activation: owner.activation,
                    observations: self.observations.clone(),
                    allocation,
                    layout: tag,
                    bytes_read,
                }),
            })
        }
    }

    fn finish(
        &self,
        key: ForeignOperationKey,
        _module: &ForeignModuleFact,
        owner: &mut dyn NativeResourceOwner,
        context: ForeignFinishContext,
    ) -> Result<ForeignCompletion, ForeignExecutionError> {
        if (key.effect, key.operation) != (0, 2) {
            return Err(ForeignExecutionError("arena finish role mismatch"));
        }
        if context.retained_dependents {
            return Err(ForeignExecutionError(
                "retained native dependency prevents arena finish transition",
            ));
        }
        let owner = owner
            .as_any_mut()
            .downcast_mut::<ArenaOwner>()
            .ok_or(ForeignExecutionError("arena finish owner mismatch"))?;
        let arena = owner
            .arena
            .get_mut()
            .take()
            .ok_or(ForeignExecutionError("arena finish repeated"))?;
        drop(arena);
        owner.observations.release(owner.activation, false);
        Ok(ForeignCompletion::Closed)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ash::{
        driver::{PipelineFailure, RunConfiguration, run_path_with_foreign_runtime},
        eval::RuntimeFailure,
        foreign::{
            ForeignRegistrations,
            runtime::{ForeignExecutionReason, ForeignRuntime},
        },
        module::{ForeignRegistrationId, ModuleRoots},
    };
    use std::{
        fs,
        path::PathBuf,
        time::{SystemTime, UNIX_EPOCH},
    };

    #[derive(Debug)]
    struct StorePreparation {
        payload: i64,
        before: Usage,
        after: Usage,
        original_bytes: Option<Vec<u8>>,
    }

    #[derive(Debug)]
    struct LoadPreparation {
        before: Usage,
        after: Usage,
        original_bytes: Vec<u8>,
    }

    #[derive(Clone, Copy, Debug)]
    enum PendingOperation {
        Store(usize),
        Load,
    }

    #[derive(Clone, Copy, Debug)]
    enum ReplyRejection {
        SecondStore,
        Load,
    }

    #[derive(Debug, Default)]
    struct AdmissionTrace {
        preparations: Vec<StorePreparation>,
        commit_attempts: Vec<usize>,
        committed: Vec<usize>,
        abandoned: Vec<usize>,
        loaded: Vec<i64>,
        load_preparation: Option<LoadPreparation>,
        load_commit_attempts: usize,
        load_committed: usize,
        load_abandoned: usize,
    }

    /// Owns only genuine unpublished scratch and test counters, never an owner.
    #[derive(Debug)]
    struct TracedInvocationCommit {
        inner: Option<Box<dyn NativeInvocationCommit>>,
        trace: Rc<RefCell<AdmissionTrace>>,
        operation: PendingOperation,
        attempted: bool,
    }

    impl NativeInvocationCommit for TracedInvocationCommit {
        fn commit(
            mut self: Box<Self>,
            key: ForeignOperationKey,
            module: &ForeignModuleFact,
            states: &[&dyn NativeResourceOwner],
        ) -> Result<(), ForeignExecutionError> {
            self.attempted = true;
            match self.operation {
                PendingOperation::Store(ordinal) => {
                    self.trace.borrow_mut().commit_attempts.push(ordinal)
                }
                PendingOperation::Load => self.trace.borrow_mut().load_commit_attempts += 1,
            }
            self.inner
                .take()
                .expect("one genuine native commit")
                .commit(key, module, states)?;
            match self.operation {
                PendingOperation::Store(ordinal) => self.trace.borrow_mut().committed.push(ordinal),
                PendingOperation::Load => self.trace.borrow_mut().load_committed += 1,
            }
            Ok(())
        }
    }

    impl Drop for TracedInvocationCommit {
        fn drop(&mut self) {
            if !self.attempted {
                // Drop the real scratch before recording its abandonment.
                drop(self.inner.take());
                match self.operation {
                    PendingOperation::Store(ordinal) => {
                        self.trace.borrow_mut().abandoned.push(ordinal)
                    }
                    PendingOperation::Load => self.trace.borrow_mut().load_abandoned += 1,
                }
            }
        }
    }

    #[derive(Debug)]
    struct RejectTypedReply {
        real: ArenaBinding,
        trace: Rc<RefCell<AdmissionTrace>>,
        rejection: ReplyRejection,
    }

    impl ExecutableForeignModule for RejectTypedReply {
        fn preflight(&self, module: &ForeignModuleFact) -> Result<(), ForeignExecutionError> {
            self.real.preflight(module)
        }

        fn acquire(
            &self,
            key: ForeignOperationKey,
            module: &ForeignModuleFact,
            input: &ForeignData,
            states: &[&dyn NativeResourceOwner],
        ) -> Result<ForeignAcquisition, ForeignExecutionError> {
            self.real.acquire(key, module, input, states)
        }

        fn invoke(
            &self,
            key: ForeignOperationKey,
            module: &ForeignModuleFact,
            input: &ForeignData,
            states: &[&dyn NativeResourceOwner],
        ) -> Result<ForeignData, ForeignExecutionError> {
            self.real.invoke(key, module, input, states)
        }

        fn prepare_invoke_with_work(
            &self,
            key: ForeignOperationKey,
            module: &ForeignModuleFact,
            input: &ForeignData,
            states: &[&dyn NativeResourceOwner],
            work: &mut ForeignInvocationWork<'_>,
        ) -> Result<ForeignInvocation, ForeignExecutionError> {
            let storage = module
                .storage
                .as_ref()
                .expect("typed arena storage contract");
            let is_storage = module.effects.get(key.effect) == Some(&storage.effect());
            let is_store = is_storage && key.operation == storage.store().operation() as usize;
            let is_load = is_storage && key.operation == storage.load().operation() as usize;
            if !is_store {
                let before = is_load.then(|| {
                    states[0]
                        .as_any()
                        .downcast_ref::<ArenaOwner>()
                        .unwrap()
                        .arena
                        .borrow()
                        .as_ref()
                        .unwrap()
                        .usage()
                });
                let reply = self
                    .real
                    .prepare_invoke_with_work(key, module, input, states, work)?;
                if is_load {
                    let ForeignInvocation::Prepared { output, .. } = &reply else {
                        panic!("real load must defer its observation until admission");
                    };
                    let Some(ForeignDataNode::Integer(value)) = output.node(output.root()) else {
                        panic!("real load must decode native signed64 bytes");
                    };
                    self.trace.borrow_mut().loaded.push(value.to_i64().unwrap());
                    if matches!(self.rejection, ReplyRejection::Load) {
                        let owner = states[0].as_any().downcast_ref::<ArenaOwner>().unwrap();
                        let arena = owner.arena.borrow();
                        let arena = arena.as_ref().unwrap();
                        let (allocation, layout) = self
                            .real
                            .observations
                            .events()
                            .iter()
                            .find_map(|event| {
                                if let ArenaEvent::Stored {
                                    allocation, layout, ..
                                } = event
                                {
                                    Some((*allocation, *layout))
                                } else {
                                    None
                                }
                            })
                            .expect("a real store precedes rejected Load");
                        self.trace.borrow_mut().load_preparation = Some(LoadPreparation {
                            before: before.unwrap(),
                            after: arena.usage(),
                            original_bytes: arena.read(allocation, layout.tag()).unwrap().to_vec(),
                        });
                        let ForeignInvocation::Prepared { commit, .. } = reply else {
                            unreachable!("genuine Load preparation checked above");
                        };
                        return Ok(ForeignInvocation::Prepared {
                            output: ForeignData::new(vec![ForeignDataNode::Boolean(true)], 0)?,
                            commit: Box::new(TracedInvocationCommit {
                                inner: Some(commit),
                                trace: Rc::clone(&self.trace),
                                operation: PendingOperation::Load,
                                attempted: false,
                            }),
                        });
                    }
                }
                return Ok(reply);
            }

            let owner = states[0].as_any().downcast_ref::<ArenaOwner>().unwrap();
            let before = owner.arena.borrow().as_ref().unwrap().usage();
            let ForeignDataNode::Tuple(fields) = input.node(input.root()).unwrap() else {
                panic!("genuine typed store operand");
            };
            let Some(ForeignDataNode::Integer(payload)) = input.node(fields[3]) else {
                panic!("signed64 test payload");
            };
            // Preparation, including encoding and candidate allocation, is real.
            let ForeignInvocation::Prepared { mut output, commit } = self
                .real
                .prepare_invoke_with_work(key, module, input, states, work)?
            else {
                panic!("real store must return unpublished scratch");
            };
            let arena = owner.arena.borrow();
            let arena = arena.as_ref().unwrap();
            let after = arena.usage();
            let original_bytes = self.real.observations.events().iter().find_map(|event| {
                if let ArenaEvent::Stored {
                    allocation, layout, ..
                } = event
                {
                    Some(arena.read(*allocation, layout.tag()).unwrap().to_vec())
                } else {
                    None
                }
            });
            let ordinal = {
                let mut trace = self.trace.borrow_mut();
                trace.preparations.push(StorePreparation {
                    payload: payload.to_i64().unwrap(),
                    before,
                    after,
                    original_bytes,
                });
                trace.preparations.len()
            };
            if ordinal == 2 && matches!(self.rejection, ReplyRejection::SecondStore) {
                // Corrupt only the copied reply. Keep the real pending commit so
                // evaluator codomain rejection must abandon native preparation.
                output = ForeignData::new(vec![ForeignDataNode::Boolean(true)], 0)?;
            }
            Ok(ForeignInvocation::Prepared {
                output,
                commit: Box::new(TracedInvocationCommit {
                    inner: Some(commit),
                    trace: Rc::clone(&self.trace),
                    operation: PendingOperation::Store(ordinal),
                    attempted: false,
                }),
            })
        }

        fn finish(
            &self,
            key: ForeignOperationKey,
            module: &ForeignModuleFact,
            owner: &mut dyn NativeResourceOwner,
            context: ForeignFinishContext,
        ) -> Result<ForeignCompletion, ForeignExecutionError> {
            self.real.finish(key, module, owner, context)
        }
    }

    struct AdmissionFixture(PathBuf);

    impl AdmissionFixture {
        fn new() -> Self {
            let unique = SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_nanos();
            let path = std::env::temp_dir().join(format!(
                "ash-arena-result-admission-{}-{unique}",
                std::process::id(),
            ));
            fs::create_dir(&path).unwrap();
            let fixture = Self(path);
            let originals = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
                .join("../tests/fixtures/provider-experiments/arena-typed");
            for name in ["arena.ash", "provider.ash"] {
                fs::copy(originals.join(name), fixture.0.join(name)).unwrap();
            }
            fs::write(
                fixture.0.join("entry.ash"),
                r#"import provider as Provider
import arena as Memory

main : Unit -> Provider.Scope<Memory.ArenaInitError, Memory.ArenaFinishError, Int>
main () = resource Memory.Arena<R> arena = (Memory.ArenaConfig (16, 2)) {
match (Memory.allocate (arena, 41)) {
Memory.Allocated(first) => {
let loaded = Memory.load (arena, first)
match (Memory.allocate (arena, 99)) {
Memory.Allocated(second) => loaded
Memory.AllocationRefused(error) => 0
}
}
Memory.AllocationRefused(error) => 0
}
}
"#,
            )
            .unwrap();
            fixture
        }
    }

    impl Drop for AdmissionFixture {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.0);
        }
    }

    #[test]
    fn typed_store_reply_rejection_abandons_real_native_preparation() {
        let fixture = AdmissionFixture::new();
        let registrations = ForeignRegistrations::new([
            ash::foreign::provider_manifest(ForeignRegistrationId::new(1)).unwrap(),
            typed_arena_manifest(ForeignRegistrationId::new(2)).unwrap(),
        ])
        .unwrap();
        let observations = ArenaObservations::default();
        let trace = Rc::new(RefCell::new(AdmissionTrace::default()));
        let binding = ForeignRuntimeBinding::new(
            Arc::clone(registrations.get("@foreign.memory").unwrap()),
            Box::new(RejectTypedReply {
                real: ArenaBinding {
                    observations: observations.clone(),
                },
                trace: Rc::clone(&trace),
                rejection: ReplyRejection::SecondStore,
            }),
        );
        let mut runtime = ForeignRuntime::new(vec![binding]).unwrap();
        let failure = run_path_with_foreign_runtime(
            RunConfiguration {
                entry: fixture.0.join("entry.ash"),
                roots: ModuleRoots::empty().with_foreign_registrations(registrations),
            },
            &mut runtime,
        )
        .expect_err("Bool is not the typed Store result");
        assert!(
            matches!(
                failure.pipeline_failure(),
                Some(PipelineFailure::Runtime(RuntimeFailure::ForeignBinding))
            ),
            "{failure:?}"
        );

        let trace = trace.borrow();
        assert_eq!(trace.preparations.len(), 2);
        let first = &trace.preparations[0];
        let second = &trace.preparations[1];
        assert_eq!((first.payload, second.payload), (41, 99));
        assert_eq!(first.before, first.after);
        assert_eq!(first.before.used_payload_bytes, 0);
        assert_eq!(first.before.object_count, 0);
        assert_eq!(first.original_bytes, None);
        assert_eq!(second.before, second.after);
        assert_eq!(second.after.used_payload_bytes, 8);
        assert_eq!(second.after.object_count, 1);
        assert_eq!(
            second.original_bytes.as_deref(),
            Some(41_i64.to_le_bytes().as_slice())
        );
        assert_eq!(trace.loaded, [41]);
        assert_eq!(trace.commit_attempts, [1]);
        assert_eq!(trace.committed, [1]);
        assert_eq!(trace.abandoned, [2]);

        assert_eq!(runtime.retained_owner_count(), 1);
        assert_eq!(observations.0.borrow().outstanding, 1);
        assert!(
            !observations
                .events()
                .iter()
                .any(|event| matches!(event, ArenaEvent::Released { .. }))
        );
        drop(runtime);
        let events = observations.events();
        let [
            ArenaEvent::Acquired {
                activation,
                usage: acquired,
            },
            ArenaEvent::Stored {
                activation: stored_activation,
                allocation,
                layout,
                usage,
            },
            ArenaEvent::Loaded {
                activation: loaded_activation,
                allocation: loaded,
                layout: loaded_layout,
                bytes_read,
                usage: loaded_usage,
            },
            ArenaEvent::Released {
                activation: released_activation,
                host_teardown: true,
            },
        ] = events.as_slice()
        else {
            panic!("one real store/load, then teardown without second publication: {events:?}");
        };
        assert_eq!(acquired, &first.before);
        assert_eq!(usage, &second.after);
        assert_eq!(
            (*stored_activation, *loaded_activation, *released_activation),
            (*activation, *activation, *activation)
        );
        assert_eq!(loaded, allocation);
        assert_eq!(*loaded_layout, layout.tag());
        assert_eq!(
            (*bytes_read, layout.size(), layout.natural_alignment()),
            (8, 8, 8)
        );
        assert_eq!((usage.payload_capacity, usage.object_capacity), (16, 2));
        assert_eq!(loaded_usage, usage);
        assert_eq!(observations.0.borrow().outstanding, 0);
    }

    #[test]
    fn typed_load_reply_rejection_abandons_real_native_observation() {
        let registrations = ForeignRegistrations::new([
            ash::foreign::provider_manifest(ForeignRegistrationId::new(1)).unwrap(),
            typed_arena_manifest(ForeignRegistrationId::new(2)).unwrap(),
        ])
        .unwrap();
        let observations = ArenaObservations::default();
        let trace = Rc::new(RefCell::new(AdmissionTrace::default()));
        let binding = ForeignRuntimeBinding::new(
            Arc::clone(registrations.get("@foreign.memory").unwrap()),
            Box::new(RejectTypedReply {
                real: ArenaBinding {
                    observations: observations.clone(),
                },
                trace: Rc::clone(&trace),
                rejection: ReplyRejection::Load,
            }),
        );
        let mut runtime = ForeignRuntime::new(vec![binding]).unwrap();
        let failure = run_path_with_foreign_runtime(
            RunConfiguration {
                entry: PathBuf::from(env!("CARGO_MANIFEST_DIR")).join(
                    "../tests/fixtures/provider-experiments/arena-typed/allocation-entry.ash",
                ),
                roots: ModuleRoots::empty().with_foreign_registrations(registrations),
            },
            &mut runtime,
        )
        .expect_err("Bool is not the typed signed64 Load result");
        assert!(
            matches!(
                failure.pipeline_failure(),
                Some(PipelineFailure::Runtime(RuntimeFailure::ForeignBinding))
            ),
            "{failure:?}"
        );

        let trace = trace.borrow();
        assert_eq!(trace.preparations.len(), 1);
        assert_eq!(trace.preparations[0].payload, 41);
        assert_eq!(trace.commit_attempts, [1]);
        assert_eq!(trace.committed, [1]);
        assert!(trace.abandoned.is_empty());
        // The real Load decoded the published bytes before its copied reply was
        // replaced. Its actual pending observation must be dropped, not run.
        assert_eq!(trace.loaded, [41]);
        let load = trace
            .load_preparation
            .as_ref()
            .expect("genuine native Load prepared");
        assert_eq!(load.before, load.after);
        assert_eq!(
            (load.after.used_payload_bytes, load.after.object_count),
            (8, 1)
        );
        assert_eq!(load.original_bytes, 41_i64.to_le_bytes());
        assert_eq!(trace.load_commit_attempts, 0);
        assert_eq!(trace.load_committed, 0);
        assert_eq!(trace.load_abandoned, 1);

        assert_eq!(runtime.retained_owner_count(), 1);
        assert_eq!(observations.0.borrow().outstanding, 1);
        assert!(
            !observations
                .events()
                .iter()
                .any(|event| matches!(event, ArenaEvent::Released { .. }))
        );
        drop(runtime);
        let events = observations.events();
        let [
            ArenaEvent::Acquired {
                activation,
                usage: acquired,
            },
            ArenaEvent::Stored {
                activation: stored_activation,
                layout,
                usage,
                ..
            },
            ArenaEvent::Released {
                activation: released_activation,
                host_teardown: true,
            },
        ] = events.as_slice()
        else {
            panic!("real store, then teardown without a published Load: {events:?}");
        };
        assert_eq!((acquired.used_payload_bytes, acquired.object_count), (0, 0));
        assert_eq!(
            (*stored_activation, *released_activation),
            (*activation, *activation)
        );
        assert_eq!((layout.size(), layout.natural_alignment()), (8, 8));
        assert_eq!(usage, &load.after);
        assert_eq!((usage.payload_capacity, usage.object_capacity), (8, 1));
        assert_eq!(observations.0.borrow().outstanding, 0);
    }

    #[test]
    fn observation_capacity_refusal_preserves_storage_reason() {
        let observations = ArenaObservations::default();
        // This exceeds Vec's pointer-offset bound without allocating or relying
        // on host memory pressure. Exercise the real fallible reserve producer.
        let failure = observations.reserve(usize::MAX).unwrap_err();
        assert_eq!(failure.reason(), ForeignExecutionReason::StorageRefused);
        assert!(observations.events().is_empty());
        assert_eq!(observations.0.borrow().outstanding, 0);
    }
}

fn authenticate_layout(
    module: &ForeignModuleFact,
    witness: &ForeignLayoutWitness,
) -> Result<(), ForeignExecutionError> {
    let canonical = module
        .layout
        .as_ref()
        .and_then(|layout| layout.dictionary_for_producer(witness.dictionary().producer()))
        .ok_or(ForeignExecutionError(
            "arena witness is not from this module",
        ))?;
    if canonical.as_ref() != witness.dictionary().as_ref() {
        return Err(ForeignExecutionError("arena witness dictionary differs"));
    }
    Ok(())
}
fn scalar_layout(
    witness: &ForeignLayoutWitness,
) -> Result<(codec::ScalarKind, LayoutTag), ForeignExecutionError> {
    // These private physical discriminators never replace dictionary authority.
    let (kind, tag, size, alignment) = match witness.dictionary().encoding() {
        ForeignScalarEncoding::Unit => (codec::ScalarKind::Unit, 1, 0, 1),
        ForeignScalarEncoding::Bool => (codec::ScalarKind::Boolean, 2, 1, 1),
        ForeignScalarEncoding::Signed64 => (codec::ScalarKind::Integer, 3, 8, 8),
    };
    if witness.dictionary().size() != size || witness.dictionary().natural_alignment() != alignment
    {
        return Err(ForeignExecutionError("arena scalar layout policy differs"));
    }
    Ok((kind, LayoutTag::new(tag)))
}
fn scalar_node_matches(kind: codec::ScalarKind, value: &ForeignDataNode) -> bool {
    matches!(
        (kind, value),
        (codec::ScalarKind::Unit, ForeignDataNode::Unit)
            | (codec::ScalarKind::Boolean, ForeignDataNode::Boolean(_))
            | (codec::ScalarKind::Integer, ForeignDataNode::Integer(_))
    )
}
fn allocation_refusal(
    module: &ForeignModuleFact,
    error: AllocationError,
    work: &mut ForeignInvocationWork<'_>,
) -> Result<ForeignData, ForeignExecutionError> {
    work.charge(3)?;
    let name = match error {
        AllocationError::OutOfPayload => "OutOfPayload",
        AllocationError::OutOfObjects => "OutOfObjects",
        AllocationError::InvalidAlignment => "InvalidAlignment",
        AllocationError::InvalidPayload => "InvalidPayload",
    };
    let id = *module
        .constructors
        .get(name)
        .ok_or(ForeignExecutionError("arena refusal constructor absent"))?;
    let storage = module
        .storage
        .as_ref()
        .ok_or(ForeignExecutionError("arena storage contract absent"))?;
    let mut nodes = Vec::new();
    nodes
        .try_reserve_exact(2)
        .map_err(|_| ForeignExecutionError::STORAGE_REFUSED)?;
    nodes.push(ForeignDataNode::Constructor(id, None));
    nodes.push(ForeignDataNode::Constructor(
        storage.refused_constructor(),
        Some(0),
    ));
    ForeignData::new(nodes, 1)
}
#[derive(Debug)]
struct ArenaStoreCommit {
    module: Arc<ForeignManifest>,
    key: ForeignOperationKey,
    witness: ForeignLayoutWitness,
    activation: u64,
    observations: ArenaObservations,
    prepared: PreparedAllocation,
    payload: codec::PreparedPayload,
}
impl NativeInvocationCommit for ArenaStoreCommit {
    fn commit(
        self: Box<Self>,
        key: ForeignOperationKey,
        module: &ForeignModuleFact,
        states: &[&dyn NativeResourceOwner],
    ) -> Result<(), ForeignExecutionError> {
        if key != self.key || !Arc::ptr_eq(&self.module, module.manifest()) || states.len() != 1 {
            return Err(ForeignExecutionError(
                "arena prepared invocation context differs",
            ));
        }
        authenticate_layout(module, &self.witness)?;
        // Another host preparation may have consumed the earlier spare slot.
        // Renew it before any native publication; refusal leaves storage intact.
        self.observations.reserve(1)?;
        let owner = states[0]
            .as_any()
            .downcast_ref::<ArenaOwner>()
            .ok_or(ForeignExecutionError("arena prepared owner differs"))?;
        if owner.activation != self.activation
            || !Rc::ptr_eq(&owner.observations.0, &self.observations.0)
        {
            return Err(ForeignExecutionError("arena prepared activation differs"));
        }
        let mut arena = owner
            .arena
            .try_borrow_mut()
            .map_err(|_| ForeignExecutionError("arena prepared owner already borrowed"))?;
        let arena = arena
            .as_mut()
            .ok_or(ForeignExecutionError("arena prepared owner completed"))?;
        let layout = self.payload.layout();
        let allocation = arena
            .commit_prepared(self.prepared, |bytes| {
                bytes.copy_from_slice(self.payload.bytes());
                Ok::<(), ForeignExecutionError>(())
            })
            .map_err(|_| ForeignExecutionError("arena prepared allocation became stale"))?;
        self.observations.record(ArenaEvent::Stored {
            activation: self.activation,
            allocation,
            layout,
            usage: arena.usage(),
        });
        Ok(())
    }
}

/// A load owns copied output and observation scratch, never an arena owner.
#[derive(Debug)]
struct ArenaLoadCommit {
    module: Arc<ForeignManifest>,
    key: ForeignOperationKey,
    witness: ForeignLayoutWitness,
    activation: u64,
    observations: ArenaObservations,
    allocation: AllocationKey,
    layout: LayoutTag,
    bytes_read: usize,
}
impl NativeInvocationCommit for ArenaLoadCommit {
    fn commit(
        self: Box<Self>,
        key: ForeignOperationKey,
        module: &ForeignModuleFact,
        states: &[&dyn NativeResourceOwner],
    ) -> Result<(), ForeignExecutionError> {
        if key != self.key || !Arc::ptr_eq(&self.module, module.manifest()) || states.len() != 1 {
            return Err(ForeignExecutionError("arena prepared load context differs"));
        }
        authenticate_layout(module, &self.witness)?;
        // Another host preparation may have consumed the earlier spare slot.
        // Renew it before any native publication; refusal leaves storage intact.
        self.observations.reserve(1)?;
        let owner = states[0]
            .as_any()
            .downcast_ref::<ArenaOwner>()
            .ok_or(ForeignExecutionError("arena prepared load owner differs"))?;
        if owner.activation != self.activation
            || !Rc::ptr_eq(&owner.observations.0, &self.observations.0)
        {
            return Err(ForeignExecutionError(
                "arena prepared load activation differs",
            ));
        }
        let arena = owner
            .arena
            .try_borrow()
            .map_err(|_| ForeignExecutionError("arena prepared load owner already borrowed"))?;
        let arena = arena
            .as_ref()
            .ok_or(ForeignExecutionError("arena prepared load owner completed"))?;
        let bytes = arena
            .read(self.allocation, self.layout)
            .map_err(|_| ForeignExecutionError("arena prepared load allocation differs"))?;
        if bytes.len() != self.bytes_read {
            return Err(ForeignExecutionError("arena prepared load extent differs"));
        }
        self.observations.record(ArenaEvent::Loaded {
            activation: self.activation,
            allocation: self.allocation,
            layout: self.layout,
            bytes_read: self.bytes_read,
            usage: arena.usage(),
        });
        Ok(())
    }
}
