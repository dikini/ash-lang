//! Executable host bindings for the bounded provider experiment.
//!
//! Manifest admission and executable binding are separate boundaries. Native
//! owners are unique host objects; copied codec data and borrowed state views
//! never transfer that ownership.

use std::{any::Any, fmt, sync::Arc};

use super::{ForeignManifest, ForeignModuleFact, ForeignOperationFact};
use crate::types::{ConstructorId, NominalTypeId, TYPE_WORK_LIMIT, TypeWorkBudget};

/// A binding, conversion, or host-contract refusal before source publication.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ForeignExecutionError(pub &'static str);

/// The detected generic boundary reason, independent of an adapter's message.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ForeignExecutionReason {
    /// A malformed codec, unavailable binding, or violated host contract.
    Binding,
    /// A bounded work admission was refused.
    WorkExhausted,
    /// A fallible storage reservation was refused.
    StorageRefused,
    /// Resource admission failed without preserving a more precise cause.
    ResourceRefused,
}

impl ForeignExecutionError {
    /// Reserved generic marker for a detected work-bound refusal.
    pub const WORK_EXHAUSTED: Self = Self("@ash.foreign/work-exhausted");
    /// Reserved generic marker for a detected fallible storage refusal.
    pub const STORAGE_REFUSED: Self = Self("@ash.foreign/storage-refused");
    /// Reserved generic marker when work versus storage information was erased.
    pub const RESOURCE_REFUSED: Self = Self("@ash.foreign/resource-refused");

    /// Classifies only the exact reserved markers. Legacy messages remain
    /// binding errors, including messages mentioning work or storage.
    #[must_use]
    pub fn reason(self) -> ForeignExecutionReason {
        match self.0 {
            "@ash.foreign/work-exhausted" => ForeignExecutionReason::WorkExhausted,
            "@ash.foreign/storage-refused" => ForeignExecutionReason::StorageRefused,
            "@ash.foreign/resource-refused" => ForeignExecutionReason::ResourceRefused,
            _ => ForeignExecutionReason::Binding,
        }
    }
}
impl fmt::Display for ForeignExecutionError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(self.0)
    }
}
impl std::error::Error for ForeignExecutionError {}

/// One node in independent copied foreign data. Child indices precede parents.
#[derive(Debug)]
pub enum ForeignDataNode {
    /// An ABI integer converted without narrowing an Ash integer silently.
    Integer(crate::integer::Integer),
    /// Independent immutable packed bytes.
    Bytes(Arc<[u8]>),
    /// Independent immutable UTF-8 contents.
    String(Arc<str>),
    /// A Boolean value.
    Boolean(bool),
    /// Unit.
    Unit,
    /// Ordered tuple children.
    Tuple(Box<[usize]>),
    /// An original admitted constructor and its optional payload.
    Constructor(ConstructorId, Option<usize>),
    /// A borrowed operand slot, permitted only in inputs, never copied results.
    State(usize),
}

/// Flat copied codec data with bounded, iterative validation and destruction.
#[derive(Debug)]
pub struct ForeignData {
    nodes: Vec<ForeignDataNode>,
    root: usize,
}
impl ForeignData {
    /// Checks an acyclic, backward-referencing codec graph.
    ///
    /// # Errors
    /// Rejects missing roots, forward edges, or excess codec work.
    pub fn new(nodes: Vec<ForeignDataNode>, root: usize) -> Result<Self, ForeignExecutionError> {
        if root >= nodes.len() {
            return Err(ForeignExecutionError("invalid foreign codec root"));
        }
        if nodes.len() > TYPE_WORK_LIMIT {
            return Err(ForeignExecutionError::WORK_EXHAUSTED);
        }
        fn scalar_copy_work(node: &ForeignDataNode) -> Result<usize, ForeignExecutionError> {
            match node {
                ForeignDataNode::Integer(integer) => {
                    usize::try_from(integer.magnitude_byte_length())
                        .map(|bytes| bytes.max(1))
                        .map_err(|_| ForeignExecutionError::WORK_EXHAUSTED)
                }
                _ => Ok(0),
            }
        }
        let mut work = nodes
            .len()
            .checked_add(scalar_copy_work(&nodes[root])?)
            .filter(|work| *work <= TYPE_WORK_LIMIT)
            .ok_or(ForeignExecutionError::WORK_EXHAUSTED)?;
        for (index, node) in nodes.iter().enumerate() {
            match node {
                ForeignDataNode::Integer(integer) => {
                    let bytes = usize::try_from(integer.magnitude_byte_length())
                        .map_err(|_| ForeignExecutionError::WORK_EXHAUSTED)?
                        .max(1);
                    work = work
                        .checked_add(bytes)
                        .filter(|work| *work <= TYPE_WORK_LIMIT)
                        .ok_or(ForeignExecutionError::WORK_EXHAUSTED)?;
                }
                ForeignDataNode::Bytes(bytes) => {
                    work = work
                        .checked_add(bytes.len())
                        .filter(|work| *work <= TYPE_WORK_LIMIT)
                        .ok_or(ForeignExecutionError::WORK_EXHAUSTED)?;
                }
                ForeignDataNode::String(text) => {
                    work = work
                        .checked_add(text.len())
                        .filter(|work| *work <= TYPE_WORK_LIMIT)
                        .ok_or(ForeignExecutionError::WORK_EXHAUSTED)?;
                }
                ForeignDataNode::Tuple(children) => {
                    work = work
                        .checked_add(children.len())
                        .filter(|work| *work <= TYPE_WORK_LIMIT)
                        .ok_or(ForeignExecutionError::WORK_EXHAUSTED)?;
                    if children.iter().any(|child| *child >= index) {
                        return Err(ForeignExecutionError(
                            "foreign codec tuple has a forward edge",
                        ));
                    }
                    for child in children {
                        work = work
                            .checked_add(scalar_copy_work(&nodes[*child])?)
                            .filter(|work| *work <= TYPE_WORK_LIMIT)
                            .ok_or(ForeignExecutionError::WORK_EXHAUSTED)?;
                    }
                }
                ForeignDataNode::Constructor(_, Some(child)) if *child >= index => {
                    return Err(ForeignExecutionError(
                        "foreign codec constructor has a forward edge",
                    ));
                }
                ForeignDataNode::Constructor(_, Some(child)) => {
                    work = work
                        .checked_add(scalar_copy_work(&nodes[*child])?)
                        .filter(|work| *work <= TYPE_WORK_LIMIT)
                        .ok_or(ForeignExecutionError::WORK_EXHAUSTED)?;
                }
                _ => {}
            }
        }
        Ok(Self { nodes, root })
    }
    /// Borrows the checked ordered codec nodes.
    #[must_use]
    pub fn nodes(&self) -> &[ForeignDataNode] {
        &self.nodes
    }
    /// Returns the root index.
    #[must_use]
    pub const fn root(&self) -> usize {
        self.root
    }
    /// Borrows one checked codec node.
    #[must_use]
    pub fn node(&self, index: usize) -> Option<&ForeignDataNode> {
        self.nodes.get(index)
    }
}

/// Unique native payload retained only by an evaluator ownership guard.
///
/// Implementations must destroy unpublished state safely. Borrowed calls may
/// mutate native state but cannot create another owner. A finish implementation
/// consumes native state only when its returned disposition says it did.
pub trait NativeResourceOwner: Any + fmt::Debug {
    /// Borrows the adapter's private payload without duplicating ownership.
    fn as_any(&self) -> &dyn Any;
    /// Mutably borrows the same private payload for its admitted finisher.
    fn as_any_mut(&mut self) -> &mut dyn Any;
}

/// A native acquisition before evaluator publication.
#[derive(Debug)]
pub enum ForeignAcquisition {
    /// Refusal carries independent data and never executes the body.
    Refused(ForeignData),
    /// A guarded unique owner; failure before publication destroys it safely.
    Acquired(Box<dyn NativeResourceOwner>),
}

/// The finisher's explicit ownership postcondition.
#[derive(Debug)]
pub enum ForeignCompletion {
    /// Native state was consumed successfully.
    Closed,
    /// Native state was consumed. Error conversion may fail independently.
    ConsumedError(Result<ForeignData, ForeignExecutionError>),
    /// Native state remains in the exact same guard and loses source access.
    /// Error conversion may fail without changing that ownership disposition.
    RetainedError(Result<ForeignData, ForeignExecutionError>),
}

/// Ownership obligations checked before the one native finish transition.
#[derive(Clone, Copy, Debug)]
pub struct ForeignFinishContext {
    /// A quarantined live child still requires this owner's native state.
    /// The binding must return RetainedError or refuse before transition; a
    /// consumed disposition would violate its admitted foreign safety contract.
    pub retained_dependents: bool,
}

/// Original manifest coordinates, authenticated against canonical operation IDs.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ForeignOperationKey {
    /// Ordered effect declaration in the original manifest.
    pub effect: usize,
    /// Ordered operation declaration within that effect.
    pub operation: usize,
}

/// Executable behavior supplied by a trusted Rust library adapter.
///
/// The evaluator authenticates original manifest facts before these calls.
/// Adapter conversion and native ABI contracts remain explicit foreign
/// assumptions; these methods cannot manufacture compiler authority.
pub trait ExecutableForeignModule: fmt::Debug {
    /// Checks all bindings and codec families before any associated acquisition.
    fn preflight(&self, module: &ForeignModuleFact) -> Result<(), ForeignExecutionError>;
    /// Acquires guarded state after input conversion and borrowed-state checks.
    fn acquire(
        &self,
        key: ForeignOperationKey,
        module: &ForeignModuleFact,
        input: &ForeignData,
        states: &[&dyn NativeResourceOwner],
    ) -> Result<ForeignAcquisition, ForeignExecutionError>;
    /// Executes a borrowed operation and returns independent copied data.
    fn invoke(
        &self,
        key: ForeignOperationKey,
        module: &ForeignModuleFact,
        input: &ForeignData,
        states: &[&dyn NativeResourceOwner],
    ) -> Result<ForeignData, ForeignExecutionError>;
    /// Completes this exact guard. Retention never substitutes another owner.
    /// An outer error is permitted only before the native ownership transition;
    /// after that transition, the disposition must survive conversion failure.
    fn finish(
        &self,
        key: ForeignOperationKey,
        module: &ForeignModuleFact,
        owner: &mut dyn NativeResourceOwner,
        context: ForeignFinishContext,
    ) -> Result<ForeignCompletion, ForeignExecutionError>;
}

/// One executable module tied to its original immutable registration entry.
#[derive(Debug)]
pub struct ForeignRuntimeBinding {
    manifest: Arc<ForeignManifest>,
    executable: Box<dyn ExecutableForeignModule>,
}
impl ForeignRuntimeBinding {
    /// Retains the registration entry used by the source loader, not a name.
    #[must_use]
    pub fn new(
        manifest: Arc<ForeignManifest>,
        executable: Box<dyn ExecutableForeignModule>,
    ) -> Self {
        Self {
            manifest,
            executable,
        }
    }
}

/// A retained native owner with no source access. Dependencies precede it.
#[derive(Debug)]
pub(crate) struct NativeOwnerGuard {
    pub(crate) payload: Box<dyn NativeResourceOwner>,
    pub(crate) state: NominalTypeId,
    pub(crate) dependencies: Vec<u64>,
    pub(crate) identity: u64,
}

/// Executable bindings and retained owners, owned by the calling host.
///
/// Borrow this runtime for public execution so retained owners remain
/// quarantined after the source result is returned. Host destruction drops
/// dependent owners before their dependencies; it never retries source finish.
#[derive(Debug, Default)]
pub struct ForeignRuntime {
    bindings: Vec<ForeignRuntimeBinding>,
    quarantine: Vec<NativeOwnerGuard>,
    next_owner: u64,
}
impl ForeignRuntime {
    /// Admits an executable table without executing or acquiring native state.
    ///
    /// # Errors
    /// Rejects duplicate registration entries, exhausted work, or failed storage reservation.
    pub fn new(bindings: Vec<ForeignRuntimeBinding>) -> Result<Self, ForeignExecutionError> {
        let mut work = TypeWorkBudget::default();
        work.charge(bindings.len())
            .map_err(|_| ForeignExecutionError::WORK_EXHAUSTED)?;
        let mut identities = std::collections::HashSet::new();
        identities
            .try_reserve(bindings.len())
            .map_err(|_| ForeignExecutionError::STORAGE_REFUSED)?;
        for binding in &bindings {
            if !identities.insert(binding.manifest.id()) {
                return Err(ForeignExecutionError(
                    "duplicate executable foreign registration",
                ));
            }
        }
        Ok(Self {
            bindings,
            quarantine: Vec::new(),
            next_owner: 0,
        })
    }
    /// Reports owners quarantined without source access or automatic retry.
    #[must_use]
    pub fn retained_owner_count(&self) -> usize {
        self.quarantine.len()
    }

    pub(crate) fn binding(
        &self,
        module: &ForeignModuleFact,
    ) -> Result<&ForeignRuntimeBinding, ForeignExecutionError> {
        self.bindings
            .iter()
            .find(|binding| Arc::ptr_eq(&binding.manifest, module.manifest()))
            .ok_or(ForeignExecutionError(
                "no executable binding for original foreign manifest",
            ))
    }
    pub(crate) fn preflight(
        &self,
        module: &ForeignModuleFact,
        work: &mut TypeWorkBudget,
    ) -> Result<(), ForeignExecutionError> {
        module.authenticate(work).map_err(|error| {
            if error.is_resource_exhaustion() {
                ForeignExecutionError::RESOURCE_REFUSED
            } else {
                ForeignExecutionError("foreign fact authentication failed")
            }
        })?;
        let binding = self.binding(module)?;
        for operation in &module.operations {
            binding.operation_key(module, operation)?;
        }
        binding.executable.preflight(module)
    }
    pub(crate) fn guard(
        &mut self,
        payload: Box<dyn NativeResourceOwner>,
        state: NominalTypeId,
        dependencies: Vec<u64>,
    ) -> Result<NativeOwnerGuard, ForeignExecutionError> {
        let identity = self.next_owner;
        if dependencies
            .iter()
            .any(|dependency| *dependency >= identity)
        {
            return Err(ForeignExecutionError(
                "native owner dependency is not an enclosing acquisition",
            ));
        }
        self.next_owner = identity
            .checked_add(1)
            .ok_or(ForeignExecutionError("native owner identities exhausted"))?;
        Ok(NativeOwnerGuard {
            payload,
            state,
            dependencies,
            identity,
        })
    }
    pub(crate) fn quarantined_owner(&self, identity: u64) -> Option<&NativeOwnerGuard> {
        self.quarantine
            .iter()
            .find(|owner| owner.identity == identity)
    }
    pub(crate) fn quarantine_count(&self) -> usize {
        self.quarantine.len()
    }
    pub(crate) fn quarantine_dependency_count(&self) -> Option<usize> {
        self.quarantine.iter().try_fold(0usize, |count, owner| {
            count.checked_add(owner.dependencies.len())
        })
    }
    pub(crate) fn retained_dependents(&self, identity: u64) -> bool {
        self.quarantine
            .iter()
            .any(|owner| owner.dependencies.contains(&identity))
    }
    pub(crate) fn finish_quarantined(
        &mut self,
        identity: u64,
        module: &ForeignModuleFact,
        operation: &ForeignOperationFact,
    ) -> Result<ForeignCompletion, ForeignExecutionError> {
        let context = ForeignFinishContext {
            retained_dependents: self.retained_dependents(identity),
        };
        let binding = self
            .bindings
            .iter()
            .find(|binding| Arc::ptr_eq(&binding.manifest, module.manifest()))
            .ok_or(ForeignExecutionError(
                "no executable binding for original foreign manifest",
            ))?;
        let key = binding.operation_key(module, operation)?;
        let owner = self
            .quarantine
            .iter_mut()
            .find(|owner| owner.identity == identity)
            .ok_or(ForeignExecutionError("missing quarantined finish owner"))?;
        let outcome = binding
            .executable
            .finish(key, module, owner.payload.as_mut(), context)?;
        if context.retained_dependents && !matches!(outcome, ForeignCompletion::RetainedError(_)) {
            return Err(ForeignExecutionError(
                "binding consumed a retained native dependency",
            ));
        }
        // This route exists only for an already-retained dependency. Its source
        // finish reports genuine adapter retention; host teardown owns disposal.
        if !matches!(outcome, ForeignCompletion::RetainedError(_)) {
            return Err(ForeignExecutionError(
                "quarantined dependency finish must retain its guard",
            ));
        }
        Ok(outcome)
    }
    /// Capacity must have been preflighted before detaching a frame owner.
    pub(crate) fn quarantine_prepared(&mut self, owner: NativeOwnerGuard) {
        debug_assert!(self.quarantine.len() < self.quarantine.capacity());
        self.quarantine.push(owner);
    }
    pub(crate) fn reserve_quarantine(
        &mut self,
        live_owners: usize,
    ) -> Result<(), ForeignExecutionError> {
        self.quarantine
            .try_reserve(live_owners)
            .map_err(|_| ForeignExecutionError::STORAGE_REFUSED)
    }
    pub(crate) fn quarantine(
        &mut self,
        owner: NativeOwnerGuard,
    ) -> Result<(), ForeignExecutionError> {
        self.quarantine
            .try_reserve(1)
            .map_err(|_| ForeignExecutionError::STORAGE_REFUSED)?;
        self.quarantine.push(owner);
        Ok(())
    }
}
impl Drop for ForeignRuntime {
    fn drop(&mut self) {
        // Owners are acquired after the owners they retain. Last acquisition
        // therefore disposes first, including retained dependent state.
        self.quarantine.sort_unstable_by_key(|owner| owner.identity);
        while let Some(owner) = self.quarantine.pop() {
            drop(owner);
        }
    }
}
impl ForeignRuntimeBinding {
    pub(crate) fn operation_key(
        &self,
        module: &ForeignModuleFact,
        operation: &ForeignOperationFact,
    ) -> Result<ForeignOperationKey, ForeignExecutionError> {
        if !Arc::ptr_eq(&self.manifest, module.manifest())
            || module.admission.registration_id != self.manifest.id()
            || module.admission.manifest_digest != self.manifest.digest()
        {
            return Err(ForeignExecutionError(
                "foreign binding manifest authority mismatch",
            ));
        }
        let effect = module
            .effects
            .iter()
            .position(|effect| *effect == operation.id.owner())
            .ok_or(ForeignExecutionError(
                "foreign operation has no original effect",
            ))?;
        let ordinal = usize::try_from(operation.id.operation())
            .map_err(|_| ForeignExecutionError("foreign operation ordinal is unrepresentable"))?;
        let declared = self
            .manifest
            .schema
            .effects
            .get(effect)
            .and_then(|effect| effect.operations.get(ordinal))
            .ok_or(ForeignExecutionError(
                "foreign operation has no original manifest slot",
            ))?;
        if declared.role != operation.role {
            return Err(ForeignExecutionError("foreign operation role mismatch"));
        }
        Ok(ForeignOperationKey {
            effect,
            operation: ordinal,
        })
    }
    pub(crate) fn executable(&self) -> &dyn ExecutableForeignModule {
        self.executable.as_ref()
    }
}

#[cfg(test)]
mod packed_codec_tests {
    use super::*;
    #[test]
    fn repeated_integer_edges_cannot_expand_beyond_codec_copy_work() {
        let integer = crate::integer::Integer::parse_decimal(&"9".repeat(1024)).unwrap();
        let nodes = vec![
            ForeignDataNode::Integer(integer),
            ForeignDataNode::Tuple(vec![0; 1000].into_boxed_slice()),
        ];
        assert!(ForeignData::new(nodes, 1).is_err());
    }
    #[test]
    fn packed_codec_rejects_single_and_cumulative_excess_payload_work() {
        assert!(
            ForeignData::new(
                vec![ForeignDataNode::Bytes(Arc::from(vec![0; TYPE_WORK_LIMIT]))],
                0
            )
            .is_err()
        );
        let text: Arc<str> = Arc::from("x".repeat(TYPE_WORK_LIMIT / 2));
        assert!(
            ForeignData::new(
                vec![
                    ForeignDataNode::String(Arc::clone(&text)),
                    ForeignDataNode::String(text)
                ],
                1
            )
            .is_err()
        );
        assert!(ForeignData::new(vec![ForeignDataNode::Bytes(Arc::from([0, 255]))], 0).is_ok());
    }
}
