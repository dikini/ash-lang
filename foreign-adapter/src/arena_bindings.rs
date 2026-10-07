//! Minimal real native arena lifecycle through the generic Ash runtime.
// Prepared codec remains test-only until the authenticated storage bridge lands.
#[cfg(test)]
#[path = "arena_codec.rs"]
mod codec;

use crate::arena::{Arena, ArenaInitError, Usage};
use ash::foreign::{
    ForeignManifest, ForeignModuleFact, arena_manifest,
    runtime::{
        ExecutableForeignModule, ForeignAcquisition, ForeignCompletion, ForeignData,
        ForeignDataNode, ForeignExecutionError, ForeignFinishContext, ForeignOperationKey,
        ForeignRuntimeBinding, NativeResourceOwner,
    },
};
use std::{any::Any, cell::RefCell, rc::Rc, sync::Arc};

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
/// Binds only the exact admitted minimal arena manifest.
/// # Errors
/// Rejects any different schema before acquiring native backing.
pub fn arena_binding(
    manifest: Arc<ForeignManifest>,
    observations: ArenaObservations,
) -> Result<ForeignRuntimeBinding, ForeignExecutionError> {
    let expected = arena_manifest(manifest.id())
        .map_err(|_| ForeignExecutionError("invalid arena manifest"))?;
    if manifest.as_ref() != &expected {
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
        if module.manifest().as_ref() != &expected || module.operations.len() != 3 {
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
    use super::ArenaObservations;
    use ash::foreign::runtime::ForeignExecutionReason;

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
