//! Loop-driven control transitions for validated Ash Core families.

use std::{error::Error, fmt, sync::Arc};

#[path = "instantiation.rs"]
mod instantiation;
use instantiation::Instantiation;

#[cfg(test)]
#[path = "machine_test_hooks.rs"]
mod machine_test_hooks;
#[cfg(test)]
pub(super) fn refuse_disposal_growth() -> bool {
    machine_test_hooks::FAIL_DISPOSAL_GROWTH.replace(false)
}
#[cfg(test)]
#[path = "machine_storage_tests.rs"]
mod machine_storage_tests;

use super::disposal::{self, Pending};
use super::{
    Closure, ResourceFailureCause, RuntimePhase, RuntimeResource, Value,
    failure::{charge_runtime_work, resource_failure},
    value::{
        ActivationKey, ExecutableNode, ExecutableProgram, HeapCell, Location, ObservedHeap,
        ObservedValue,
    },
};
use crate::{
    core::{
        CoreMatchArm, CorePattern, CorePatternKind, EffectExprKind, EffectOperation, HandlerId,
        NodeId, Primitive, PureComputation, PureExprKind, PureValue, ValidatedEffectProgram,
        ValidatedProgram,
    },
    resolved::{BinderId, ResumeId},
    types::{ConstructorId, EffectInstance, OperationId, TypeWorkBudget},
};

/// Inspectable lexical values available while evaluating one expression.
///
/// Environments are immutable entry-chain snapshots. Cloning and ordinary
/// single-binder extension are O(1). A recursive group is sorted once and
/// stored in one entry; lookup walks entries from newest to oldest and uses a
/// binary search within each recursive entry. Entry destruction dismantles
/// uniquely owned tails iteratively so lexical depth does not become Rust
/// call-stack depth.
#[derive(Clone, Default)]
pub struct Environment {
    head: Option<Arc<EnvironmentEntry>>,
    len: usize,
    instantiation: Instantiation,
}

struct EnvironmentEntry {
    kind: EnvironmentEntryKind,
    parent: Option<Arc<Self>>,
    visible_len: usize,
    instantiation: Instantiation,
}

enum EnvironmentEntryKind {
    Binding {
        binder: BinderId,
        value: Value,
    },
    Recursive {
        members: Box<[RecursiveMemberTemplate]>,
    },
}

struct RecursiveMemberTemplate {
    binder: BinderId,
    kind: RecursiveMemberKind,
}

enum RecursiveMemberKind {
    Intrinsic {
        intrinsic: crate::core::packed::IntrinsicNode,
        abstraction: Option<NodeId>,
    },
    Function {
        parameter: BinderId,
        body: NodeId,
        origin: crate::source::Origin,
        abstraction: Option<NodeId>,
    },
    Data {
        location: Location,
    },
}

impl Drop for EnvironmentEntry {
    fn drop(&mut self) {
        let mut pending = Pending::new(RuntimeResource::EnvironmentDisposal);
        self.take_owned_edges(&mut pending);
        while let Some(entry) = pending.pop() {
            // Shared roots may occur more than once in `pending`. Consuming one
            // owner can make a later owner unique; that owner then detaches all
            // outgoing environment edges before its fields are destroyed.
            let Some(mut unique) = Arc::into_inner(entry) else {
                continue;
            };
            unique.take_owned_edges(&mut pending);
        }
    }
}

impl EnvironmentEntry {
    fn take_owned_edges(&mut self, pending: &mut Pending<Arc<Self>>) {
        if let Some(parent) = self.parent.take() {
            pending.push(parent);
        }
        if let EnvironmentEntryKind::Binding { value, .. } = &mut self.kind {
            let environment = match value {
                Value::Function(closure) => &mut closure.environment,
                Value::Polymorphic { environment, .. } => environment,
                _ => return,
            };
            if let Some(captured) = environment.head.take() {
                pending.push(captured);
            }
            environment.len = 0;
        }
    }
}

impl fmt::Debug for Environment {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        const BINDER_LIMIT: usize = 16;
        let mut binders = Vec::with_capacity(self.len.min(BINDER_LIMIT));
        let mut current = self.head.as_deref();
        while let Some(entry) = current.filter(|_| binders.len() < BINDER_LIMIT) {
            match &entry.kind {
                EnvironmentEntryKind::Binding { binder, .. } => binders.push(*binder),
                EnvironmentEntryKind::Recursive { members } => {
                    binders.extend(
                        members
                            .iter()
                            .map(|member| member.binder)
                            .take(BINDER_LIMIT - binders.len()),
                    );
                }
            }
            current = entry.parent.as_deref();
        }
        formatter
            .debug_struct("Environment")
            .field("len", &self.len)
            .field("binders_newest_first", &binders)
            .field("truncated", &(self.len > binders.len()))
            .finish()
    }
}

impl Environment {
    /// Creates an empty lexical environment.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Returns the number of captured lexical values.
    #[must_use]
    pub fn len(&self) -> usize {
        self.len
    }

    /// Reports whether the environment captures no lexical values.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.head.is_none()
    }

    fn lookup(&self, binder: BinderId, program: &ExecutableProgram) -> Option<Value> {
        let mut current = self.head.as_ref();
        while let Some(entry) = current {
            match &entry.kind {
                EnvironmentEntryKind::Binding {
                    binder: entry_binder,
                    value,
                } if *entry_binder == binder => return Some(value.clone()),
                EnvironmentEntryKind::Recursive { members } => {
                    if let Ok(index) = members.binary_search_by_key(&binder, |member| member.binder)
                    {
                        let member = &members[index];
                        return Some(match &member.kind {
                            RecursiveMemberKind::Function {
                                parameter,
                                body,
                                origin,
                                abstraction,
                            } => {
                                let environment = Self {
                                    head: Some(Arc::clone(entry)),
                                    len: entry.visible_len,
                                    instantiation: entry.instantiation.clone(),
                                };
                                if let Some(abstraction) = abstraction {
                                    return Some(Value::Polymorphic {
                                        abstraction: *abstraction,
                                        environment,
                                    });
                                }
                                Value::Function(Closure {
                                    parameter: *parameter,
                                    body: *body,
                                    program: program.clone(),
                                    environment,
                                    origin: origin.clone(),
                                })
                            }
                            RecursiveMemberKind::Intrinsic {
                                intrinsic,
                                abstraction,
                            } => {
                                if let Some(abstraction) = abstraction {
                                    return Some(Value::Polymorphic {
                                        abstraction: *abstraction,
                                        environment: Self {
                                            head: Some(Arc::clone(entry)),
                                            len: entry.visible_len,
                                            instantiation: entry.instantiation.clone(),
                                        },
                                    });
                                }
                                Value::Intrinsic(*intrinsic)
                            }
                            RecursiveMemberKind::Data { location } => Value::Location(*location),
                        });
                    }
                }
                EnvironmentEntryKind::Binding { .. } => {}
            }
            current = entry.parent.as_ref();
        }
        None
    }

    fn extend(self, binder: BinderId, value: Value) -> Result<Self, RuntimeFailure> {
        self.extend_in_phase(binder, value, RuntimePhase::Evaluation)
    }

    fn extend_in_phase(
        mut self,
        binder: BinderId,
        value: Value,
        phase: RuntimePhase,
    ) -> Result<Self, RuntimeFailure> {
        disposal::check()?;
        let len = checked_environment_len(self.len, 1, phase)?;
        Ok(Self {
            head: Some(Arc::new(EnvironmentEntry {
                kind: EnvironmentEntryKind::Binding { binder, value },
                parent: self.head.take(),
                visible_len: len,
                instantiation: self.instantiation.clone(),
            })),
            len,
            instantiation: self.instantiation,
        })
    }

    fn extend_many(mut self, bindings: Vec<(BinderId, Value)>) -> Result<Self, RuntimeFailure> {
        for (binder, value) in bindings {
            self = self.extend(binder, value)?;
        }
        Ok(self)
    }

    fn extend_recursive(
        mut self,
        mut members: Vec<RecursiveMemberTemplate>,
    ) -> Result<Self, RuntimeFailure> {
        let len = checked_environment_len(self.len, members.len(), RuntimePhase::Evaluation)?;
        members.sort_unstable_by_key(|member| member.binder);
        if members.is_empty()
            || members
                .windows(2)
                .any(|pair| pair[0].binder == pair[1].binder)
        {
            return Err(RuntimeFailure::UnexpectedRecursiveBinding);
        }
        Ok(Self {
            head: Some(Arc::new(EnvironmentEntry {
                kind: EnvironmentEntryKind::Recursive {
                    members: members.into_boxed_slice(),
                },
                parent: self.head.take(),
                visible_len: len,
                instantiation: self.instantiation.clone(),
            })),
            len,
            instantiation: self.instantiation,
        })
    }
}

/// The machine's current first-order control state.
#[derive(Clone, Debug)]
pub enum Control {
    /// Enter a Core expression under an explicit lexical environment.
    Evaluate(NodeId, Environment),
    /// Continue with a completed runtime value.
    Return(Value),
    /// Consume a clause capability and abandon its captured control.
    Discard(HandlerId, ResumeId),
}

/// An observational transition event that does not define semantics.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum TraceEvent {
    /// Evaluation entered this Core node.
    Enter(NodeId),
}

/// Observational effect-boundary transitions, absent from pure evaluation.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum EffectTraceEvent {
    /// A scope published owned access under a fresh activation key.
    ResourceAcquired(u32),
    /// The trusted interpreter copied a cell's current integer.
    ResourceRead(u32),
    /// The trusted interpreter replaced a cell's integer.
    ResourceWritten(u32),
    /// Completion ended source access. Native disposition is tracked separately.
    ResourceReleased(u32),
    /// A lexical handler boundary became active.
    HandlerActivated(HandlerId),
    /// A request reached dynamic handler selection.
    Request(OperationId),
    /// The nearest exact handler was selected and removed for its clause.
    HandlerSelected(HandlerId),
    /// A selected operation clause began evaluating.
    ClauseEntered(HandlerId, OperationId),
    /// A clause consumed its capability by restoring captured control.
    Resume(HandlerId),
    /// A clause consumed its capability by abandoning captured control.
    Discard(HandlerId),
    /// A captured handler boundary was restored around resumed control.
    HandlerRestored(HandlerId),
    /// The selected clause completed after consuming its capability.
    ClauseReturned(HandlerId),
}

/// A completed value, its retained heap, and its observational machine trace.
///
/// The heap remains owned when the visible value is a scalar or closure because
/// a closure environment can contain locations allocated during this run.
#[derive(Clone, Debug)]
pub struct Evaluation {
    /// The final runtime value.
    pub value: Value,
    /// Node-entry events in deterministic evaluation order.
    pub trace: Vec<TraceEvent>,
    /// Greatest number of explicit frames retained by the machine.
    pub max_frame_depth: usize,
    effect_trace: Option<Box<[EffectTraceEvent]>>,
    heap: Arc<ObservedHeap>,
    #[cfg(test)]
    registration_acquisitions: u32,
    #[cfg(test)]
    runtime_work: usize,
    #[cfg(test)]
    work_trace: Option<Vec<(NodeId, usize)>>,
}

impl Evaluation {
    #[cfg(test)]
    pub(crate) fn retained_effect_trace(&self) -> Option<&[EffectTraceEvent]> {
        self.effect_trace.as_deref()
    }

    pub(crate) fn into_observation_parts(self) -> (Value, Arc<ObservedHeap>) {
        (self.value, self.heap)
    }

    /// Returns effect-boundary observations, or an empty slice for pure Core.
    #[must_use]
    pub fn effect_trace(&self) -> &[EffectTraceEvent] {
        self.effect_trace.as_deref().unwrap_or_default()
    }
}

/// A structured evaluator invariant or runtime resource failure.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum RuntimeFailure {
    /// A bounded resource-failure or teardown report.
    Report(super::RuntimeFailureReport),
    /// A validated handle did not identify a node in the validated program.
    MissingNode,
    /// A validated primitive reached a value kind outside its signature.
    UnexpectedPrimitiveValue,
    /// A validated application reached a non-function runtime value.
    UnexpectedFunctionValue,
    /// A validated variable did not have a runtime lexical binding.
    MissingBinding,
    /// A validated recursive group contained an unsupported member initializer.
    UnexpectedRecursiveBinding,
    /// The runtime cannot represent another lexical environment entry.
    EnvironmentCapacity,
    /// Machine control completed without exactly one final value.
    InvalidControlState,
    /// A native callback or its runtime argument/result shape was inconsistent.
    ForeignBinding,
    /// The per-evaluation heap cannot represent another cell.
    HeapCapacity,
    /// A captured continuation cannot retain another control frame.
    CapturedControlCapacity,
    /// Another live cell or fresh activation cannot be represented.
    ResourceCapacity,
    /// A heap location is outside the current evaluation.
    InvalidLocation,
    /// Evaluation forced a recursive slot before initialization.
    UninitializedLocation,
    /// Heap aliases form a cycle without a constructed value.
    AliasLoop,
    /// Independently validated coverage selected no arm.
    ImpossibleMatch,
}

impl RuntimeFailure {
    /// Adds resource details while retaining this failure's stable reason.
    #[must_use]
    pub const fn with_resource_details(self, failure: super::ResourceFailure) -> Self {
        let mut report = match self {
            Self::Report(report) => report,
            other => super::RuntimeFailureReport {
                primary: super::RuntimeFailureSummary {
                    reason: other.reason_code(),
                    resource: None,
                },
                teardown: None,
                cleanup: super::CleanupStatus::Unknown,
            },
        };
        if report.primary.resource.is_none() {
            report.primary.resource = Some(failure);
        }
        Self::Report(report)
    }

    /// Records a resource failure; cleanup stays unknown until established.
    #[must_use]
    pub const fn resource(failure: super::ResourceFailure) -> Self {
        Self::Report(super::RuntimeFailureReport {
            primary: super::RuntimeFailureSummary {
                reason: failure.cause.reason_code(),
                resource: Some(failure),
            },
            teardown: None,
            cleanup: super::CleanupStatus::Unknown,
        })
    }

    /// Retains the original reason and first secondary teardown failure.
    #[must_use]
    pub const fn with_teardown_failure(
        self,
        failure: super::ResourceFailure,
        cleanup: super::CleanupStatus,
    ) -> Self {
        let mut report = match self {
            Self::Report(report) => report,
            other => super::RuntimeFailureReport {
                primary: super::RuntimeFailureSummary {
                    reason: other.reason_code(),
                    resource: None,
                },
                teardown: None,
                cleanup: super::CleanupStatus::Unknown,
            },
        };
        if report.teardown.is_none() {
            report.teardown = Some(failure);
        }
        report.cleanup = cleanup;
        Self::Report(report)
    }
    /// Returns the stable reason code owned by this runtime failure.
    #[must_use]
    pub const fn reason_code(self) -> &'static str {
        match self {
            Self::Report(report) => report.primary.reason_code(),
            Self::MissingNode => "runtime.missing-node",
            Self::UnexpectedPrimitiveValue => "runtime.unexpected-primitive-value",
            Self::UnexpectedFunctionValue => "runtime.unexpected-function-value",
            Self::MissingBinding => "runtime.missing-binding",
            Self::UnexpectedRecursiveBinding => "runtime.unexpected-recursive-binding",
            Self::EnvironmentCapacity => "runtime.environment-capacity",
            Self::InvalidControlState => "runtime.invalid-control-state",
            Self::ForeignBinding => "runtime.foreign-binding",
            Self::HeapCapacity => "runtime.heap-capacity",
            Self::CapturedControlCapacity => "runtime.captured-control-capacity",
            Self::ResourceCapacity => "runtime.resource-capacity",
            Self::InvalidLocation => "runtime.invalid-location",
            Self::UninitializedLocation => "runtime.uninitialized-location",
            Self::AliasLoop => "runtime.alias-loop",
            Self::ImpossibleMatch => "runtime.impossible-match",
        }
    }
}

impl fmt::Display for RuntimeFailure {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(match self {
            Self::Report(report) => {
                write!(formatter, "{}", report.primary.reason_code())?;
                if let Some(failure) = report.primary.resource() {
                    if report.primary.reason_code() != failure.cause.reason_code() {
                        write!(formatter, " ({})", failure.cause.reason_code())?;
                    }
                    write!(
                        formatter,
                        " during {} ({})",
                        failure.phase.label(),
                        failure.resource.label()
                    )?;
                }
                if let Some(failure) = report.teardown {
                    write!(
                        formatter,
                        "; teardown: {} during {} ({})",
                        failure.cause.reason_code(),
                        failure.phase.label(),
                        failure.resource.label()
                    )?;
                }
                return write!(formatter, "; cleanup: {}", report.cleanup.label());
            }
            Self::MissingNode => "runtime node handle is absent from validated Core",
            Self::UnexpectedPrimitiveValue => {
                "runtime primitive received a value outside its validated signature"
            }
            Self::UnexpectedFunctionValue => {
                "runtime application received a value outside its validated function type"
            }
            Self::MissingBinding => "runtime lexical binding is absent",
            Self::UnexpectedRecursiveBinding => {
                "runtime recursive binding violates its validated member shape"
            }
            Self::EnvironmentCapacity => "runtime lexical environment capacity is exhausted",
            Self::InvalidControlState => "runtime machine control state is inconsistent",
            Self::ForeignBinding => "executable foreign binding or pointer signature failed",
            Self::HeapCapacity => "runtime heap capacity is exhausted",
            Self::CapturedControlCapacity => "runtime captured-control capacity is exhausted",
            Self::ResourceCapacity => "runtime resource capacity is exhausted",
            Self::InvalidLocation => "runtime heap location is invalid",
            Self::UninitializedLocation => "runtime heap location is uninitialized",
            Self::AliasLoop => "runtime heap aliases form a loop",
            Self::ImpossibleMatch => "validated exhaustive match selected no arm",
        })
    }
}

impl Error for RuntimeFailure {}

#[derive(Debug)]
enum Frame {
    CloseCompletion,
    CleanupBoundary {
        action: NodeId,
        environment: Environment,
    },
    CleanupCompletion {
        saved: Value,
    },
    // This private, non-Clone frame is the release authority. Acquisition is
    // its only constructor in execution; capture/resume move it, and normal
    // return consumes it. Keys in handler/clause frames are non-owning facts.
    RegistrationBoundary {
        key: RegistrationKey,
        handler: NodeId,
        // Retain the evaluated callback independently of pending control.
        callback: Value,
        handler_active: bool,
        pending_invocations: usize,
    },
    ResourceInitializer {
        node: NodeId,
        environment: Environment,
    },
    ResourceBoundary {
        node: NodeId,
        key: ActivationKey,
        payload: ResourcePayload,
    },
    Bind {
        binder: BinderId,
        body: NodeId,
        environment: Environment,
    },
    PrimitiveLeft {
        primitive: Primitive,
        right: NodeId,
        environment: Environment,
    },
    PrimitiveRight {
        primitive: Primitive,
        left: Value,
    },
    ApplyFunction {
        argument: NodeId,
        caller_environment: Environment,
    },
    ApplyArgument {
        function: Value,
    },
    Tuple {
        elements: Box<[NodeId]>,
        next: usize,
        values: Vec<Value>,
        environment: Environment,
    },
    Match {
        arms: Box<[CoreMatchArm]>,
        environment: Environment,
    },
    InitializeRecursive {
        pending: Box<[(Location, NodeId)]>,
        next: usize,
        body: NodeId,
        environment: Environment,
    },
    NativeInterpretBoundary {
        node: NodeId,
        environment: Environment,
    },
    HandlerBoundary {
        node: NodeId,
        environment: Environment,
        registration: Option<RegistrationKey>,
    },
    Request {
        node: NodeId,
        instantiation: Instantiation,
    },
    TypeApplication {
        node: NodeId,
        caller: Instantiation,
    },
    Resume {
        node: NodeId,
    },
    ClauseBoundary {
        handler: HandlerId,
        owner: ResumeId,
        continuation: Option<CapturedContinuation>,
        registration: Option<RegistrationKey>,
    },
}

#[derive(Debug)]
enum ResourcePayload {
    Cell(crate::integer::Integer),
    Generic {
        value: Value,
        instance: EffectInstance,
    },
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct RegistrationKey(u32);

#[derive(Debug)]
struct CapturedContinuation {
    frames: Vec<Frame>,
}

// An explicit first handler is the segment's selected cut. A mismatched
// clause identity is malformed control, never a nonselected interpreter.
fn selected_handler_for_discard(
    program: &ExecutableProgram,
    captured: &CapturedContinuation,
    handler: HandlerId,
    work: &mut TypeWorkBudget,
) -> Result<bool, RuntimeFailure> {
    charge_effect_work(work, 1, RuntimePhase::Capture)?;
    let Some(Frame::HandlerBoundary { node, .. }) = captured.frames.first() else {
        return Ok(false);
    };
    let actual = match program.node(*node) {
        Some(ExecutableNode::Effect(expression)) => match &expression.kind {
            EffectExprKind::Operation(EffectOperation::Handler(boundary)) => boundary.id(),

            _ => return Err(RuntimeFailure::InvalidControlState),
        },
        _ => return Err(RuntimeFailure::InvalidControlState),
    };
    if actual != handler {
        return Err(RuntimeFailure::InvalidControlState);
    }
    Ok(true)
}

// Prove retention against the structural owner path before discard transfers
// any frame. These scalar coordinates never carry or clone native ownership.

// Rust allocations cannot represent a non-zero `Frame` vector whose byte
// length exceeds `isize::MAX`. This implementation bound is not Ash semantics.
const MAX_CAPTURED_FRAME_CELLS: usize = (isize::MAX as usize) / std::mem::size_of::<Frame>();

impl Drop for CapturedContinuation {
    fn drop(&mut self) {
        let mut pending = Pending::from_vec(
            std::mem::take(&mut self.frames),
            RuntimeResource::CapturedDisposal,
        );
        while let Some(mut frame) = pending.pop() {
            if let Frame::ClauseBoundary { continuation, .. } = &mut frame
                && let Some(mut nested) = continuation.take()
            {
                for child in nested.frames.drain(..) {
                    pending.push(child);
                }
            }
        }
    }
}

struct Transition {
    control: Control,
    frame: Option<Frame>,
}

impl Transition {
    const fn direct(control: Control) -> Self {
        Self {
            control,
            frame: None,
        }
    }

    const fn suspend(control: Control, frame: Frame) -> Self {
        Self {
            control,
            frame: Some(frame),
        }
    }
}

/// Shared test observation also retains the prefix of a failed run.
#[cfg(test)]
type WorkTrace = Arc<std::sync::Mutex<Vec<(NodeId, usize)>>>;

/// The retained explicit evaluator machine shared by pure and effect Core.
#[derive(Debug)]
pub struct Machine<'runtime> {
    source_bindings: Option<&'runtime crate::foreign::source_bindings::SourceNativeBindings>,
    cleanup_limit: usize,
    live_cleanups: usize,
    program: ExecutableProgram,
    control: Option<Control>,
    frames: Vec<Frame>,
    max_frame_depth: usize,
    trace: Vec<TraceEvent>,
    effect_trace: Option<Vec<EffectTraceEvent>>,
    heap: Vec<HeapCell>,
    capture_limit: usize,
    captured_cells: usize,
    instantiation_work: TypeWorkBudget,
    resource_limit: usize,
    live_resources: usize,
    next_activation: u32,
    registration_limit: usize,
    live_registrations: usize,
    next_registration: u32,
    #[cfg(test)]
    work_trace: Option<WorkTrace>,
}

impl<'runtime> Machine<'runtime> {
    fn new(program: &ValidatedProgram) -> Self {
        Self {
            source_bindings: None,
            program: ExecutableProgram::Pure(program.shared()),
            cleanup_limit: 0,
            live_cleanups: 0,
            control: Some(Control::Evaluate(program.root(), Environment::new())),
            frames: Vec::new(),
            max_frame_depth: 0,
            trace: Vec::new(),
            effect_trace: None,
            heap: Vec::new(),
            capture_limit: 0,
            captured_cells: 0,
            instantiation_work: TypeWorkBudget::unbounded(),
            resource_limit: 0,
            live_resources: 0,
            next_activation: 0,
            registration_limit: 0,
            live_registrations: 0,
            next_registration: 0,
            #[cfg(test)]
            work_trace: None,
        }
    }

    fn new_effect(program: &ValidatedEffectProgram) -> Self {
        Self::new_effect_with_capture_limit(program, MAX_CAPTURED_FRAME_CELLS)
    }

    fn new_effect_with_capture_limit(
        program: &ValidatedEffectProgram,
        capture_limit: usize,
    ) -> Self {
        Self {
            source_bindings: None,
            program: ExecutableProgram::Effect(program.shared()),
            cleanup_limit: MAX_CAPTURED_FRAME_CELLS,
            live_cleanups: 0,
            control: Some(Control::Evaluate(program.root(), Environment::new())),
            frames: Vec::new(),
            max_frame_depth: 0,
            trace: Vec::new(),
            effect_trace: Some(Vec::new()),
            heap: Vec::new(),
            capture_limit,
            captured_cells: 0,
            instantiation_work: TypeWorkBudget::unbounded(),
            resource_limit: MAX_CAPTURED_FRAME_CELLS,
            live_resources: 0,
            next_activation: 0,
            registration_limit: MAX_CAPTURED_FRAME_CELLS,
            live_registrations: 0,
            next_registration: 0,
            #[cfg(test)]
            work_trace: None,
        }
    }

    fn run(mut self) -> Result<Evaluation, RuntimeFailure> {
        let scope = disposal::Scope::enter();
        let result = self.run_loop();
        // Dispose all retained ordinary control/heap values inside the same
        // observation scope, on success and on failure.
        drop(self);
        scope.finish(result)
    }

    fn run_loop(&mut self) -> Result<Evaluation, RuntimeFailure> {
        loop {
            disposal::check()?;
            let control = self
                .control
                .take()
                .ok_or(RuntimeFailure::InvalidControlState)?;
            match control {
                Control::Evaluate(node, environment) => {
                    #[cfg(test)]
                    if let Some(trace) = &mut self.work_trace {
                        trace
                            .lock()
                            .unwrap()
                            .push((node, self.instantiation_work.used()));
                    }
                    self.trace.push(TraceEvent::Enter(node));
                    if let Some(ExecutableNode::Effect(expression)) = self.program.node(node)
                        && let EffectExprKind::Operation(EffectOperation::Cleanup(scope)) =
                            expression.kind
                    {
                        self.acquire_cleanup(scope, environment)?;
                        continue;
                    }
                    if self.registration(node).is_some() {
                        self.acquire_registration(node, environment)?;
                        continue;
                    }
                    if let Some(ExecutableNode::Effect(expression)) = self.program.node(node)
                        && let EffectExprKind::Operation(EffectOperation::Handler(handler)) =
                            &expression.kind
                    {
                        self.trace_effect(EffectTraceEvent::HandlerActivated(handler.id()));
                    }
                    if let Ok(PureExprKind::Value(PureValue::String(string))) =
                        pure_expression(&self.program, node)
                    {
                        charge_runtime_work(
                            &mut self.instantiation_work,
                            string.bytes().len(),
                            RuntimePhase::Evaluation,
                        )?;
                    }
                    let transition =
                        dispatch_entry(&self.program, node, environment, &mut self.heap)?;
                    if matches!(
                        &transition.frame,
                        Some(Frame::NativeInterpretBoundary { .. })
                    ) {
                        charge_effect_work(&mut self.instantiation_work, 1, RuntimePhase::Access)?;
                        self.frames.try_reserve(1).map_err(|_| {
                            resource_failure(
                                ResourceFailureCause::StorageReservationFailed,
                                RuntimePhase::Access,
                                RuntimeResource::FrameStorage,
                                Some(1),
                                None,
                            )
                        })?;
                    }
                    disposal::check()?;
                    self.apply(transition);
                }
                Control::Return(value) => {
                    let Some(frame) = self.frames.pop() else {
                        if self.live_resources != 0
                            || self.live_cleanups != 0
                            || self.live_registrations != 0
                            || self.captured_cells != 0
                        {
                            return Err(RuntimeFailure::InvalidControlState);
                        }
                        let heap = ObservedHeap::new(
                            Arc::clone(self.program.registry()),
                            std::mem::take(&mut self.heap),
                        );
                        let value = match value {
                            Value::Location(root) => {
                                Value::Data(ObservedValue::new(Arc::clone(&heap), root))
                            }
                            value => value,
                        };
                        return Ok(Evaluation {
                            value,
                            trace: std::mem::take(&mut self.trace),
                            max_frame_depth: self.max_frame_depth,
                            effect_trace: self.effect_trace.take().map(Vec::into_boxed_slice),
                            heap,
                            #[cfg(test)]
                            registration_acquisitions: self.next_registration,
                            #[cfg(test)]
                            runtime_work: self.instantiation_work.used(),
                            #[cfg(test)]
                            work_trace: self
                                .work_trace
                                .take()
                                .map(|trace| trace.lock().unwrap().clone()),
                        });
                    };
                    self.return_from(frame, value)?;
                }
                Control::Discard(handler, owner) => self.discard(handler, owner)?,
            }
        }
    }

    fn apply(&mut self, transition: Transition) {
        if let Some(frame) = transition.frame {
            self.frames.push(frame);
            self.max_frame_depth = self.max_frame_depth.max(self.frames.len());
        }
        self.control = Some(transition.control);
    }

    fn trace_effect(&mut self, event: EffectTraceEvent) {
        if let Some(trace) = &mut self.effect_trace {
            trace.push(event);
        }
    }

    fn return_from(&mut self, frame: Frame, value: Value) -> Result<(), RuntimeFailure> {
        disposal::check()?;
        match frame {
            Frame::CloseCompletion => {
                if !matches!(value, Value::Unit) {
                    return Err(RuntimeFailure::InvalidControlState);
                }
                self.control = Some(Control::Return(Value::Unit));
            }
            Frame::CleanupBoundary {
                action,
                environment,
            } => {
                charge_effect_work(&mut self.instantiation_work, 2, RuntimePhase::Cleanup)?;
                self.frames.try_reserve(1).map_err(|_| {
                    legacy_failure(
                        RuntimeFailure::ResourceCapacity,
                        ResourceFailureCause::StorageReservationFailed,
                        RuntimePhase::Cleanup,
                        RuntimeResource::FrameStorage,
                        Some(1),
                        None,
                    )
                })?;
                self.frames.push(Frame::CleanupCompletion { saved: value });
                self.control = Some(Control::Evaluate(action, environment));
            }
            Frame::CleanupCompletion { saved } => {
                if !matches!(value, Value::Unit) {
                    return Err(RuntimeFailure::InvalidControlState);
                }
                self.live_cleanups = self
                    .live_cleanups
                    .checked_sub(1)
                    .ok_or(RuntimeFailure::InvalidControlState)?;
                self.control = Some(Control::Return(saved));
            }
            Frame::RegistrationBoundary {
                handler_active,
                pending_invocations,
                callback,
                ..
            } => {
                if handler_active || pending_invocations != 0 {
                    return Err(RuntimeFailure::InvalidControlState);
                }
                let live = self
                    .live_registrations
                    .checked_sub(1)
                    .ok_or(RuntimeFailure::InvalidControlState)?;
                drop(callback);
                disposal::check()?;
                self.live_registrations = live;
                self.control = Some(Control::Return(value));
            }
            Frame::ResourceInitializer { node, environment } => {
                self.acquire_resource(node, environment, value)?;
            }
            Frame::ResourceBoundary { key, payload, .. } => {
                self.live_resources = self
                    .live_resources
                    .checked_sub(1)
                    .ok_or(RuntimeFailure::InvalidControlState)?;
                drop(payload);
                let result = value;
                self.trace_effect(EffectTraceEvent::ResourceReleased(key.0));
                self.control = Some(Control::Return(result));
            }
            Frame::NativeInterpretBoundary { .. } => {
                self.control = Some(Control::Return(value));
            }
            Frame::HandlerBoundary {
                node, registration, ..
            } => {
                if let Some(key) = registration {
                    let index = self.registration_owner(key, node, 0)?;
                    let Frame::RegistrationBoundary { handler_active, .. } =
                        &mut self.frames[index]
                    else {
                        return Err(RuntimeFailure::InvalidControlState);
                    };
                    if !*handler_active {
                        return Err(RuntimeFailure::InvalidControlState);
                    }
                    *handler_active = false;
                }
                self.control = Some(Control::Return(value));
            }
            Frame::Request {
                node,
                instantiation,
            } => self.return_request(node, &instantiation, value)?,
            Frame::TypeApplication { node, caller } => {
                self.return_type_application(node, &caller, value)?
            }
            Frame::Resume { node } => self.return_resume(node, value)?,
            Frame::ClauseBoundary {
                handler,
                continuation,
                registration,
                ..
            } => {
                if continuation.is_some() {
                    return Err(RuntimeFailure::InvalidControlState);
                }
                if let Some(key) = registration {
                    let index = self.registration_owner_for_handler(key, handler, true)?;
                    let Frame::RegistrationBoundary {
                        handler_active,
                        pending_invocations,
                        ..
                    } = &mut self.frames[index]
                    else {
                        return Err(RuntimeFailure::InvalidControlState);
                    };
                    if *handler_active {
                        return Err(RuntimeFailure::InvalidControlState);
                    }
                    *pending_invocations = pending_invocations
                        .checked_sub(1)
                        .ok_or(RuntimeFailure::InvalidControlState)?;
                }
                self.trace_effect(EffectTraceEvent::ClauseReturned(handler));
                self.control = Some(Control::Return(value));
            }
            Frame::ApplyArgument {
                function: Value::Intrinsic(intrinsic),
            } => {
                let result = apply_intrinsic(
                    intrinsic,
                    value,
                    &mut self.heap,
                    &mut self.instantiation_work,
                )?;
                self.control = Some(Control::Return(result));
            }
            frame => {
                let transition = dispatch_return(frame, value, &mut self.heap)?;
                disposal::check()?;
                self.apply(transition);
            }
        }
        Ok(())
    }

    fn registration_owner(
        &mut self,
        key: RegistrationKey,
        handler: NodeId,
        active_handlers: usize,
    ) -> Result<usize, RuntimeFailure> {
        let index = self.registration_owner_index(key, active_handlers, false)?;
        if !matches!(self.frames[index], Frame::RegistrationBoundary { handler: found, .. } if found == handler)
        {
            return Err(RuntimeFailure::InvalidControlState);
        }
        Ok(index)
    }

    fn registration_owner_index(
        &mut self,
        key: RegistrationKey,
        active_handlers: usize,
        returning_clause: bool,
    ) -> Result<usize, RuntimeFailure> {
        // The selected owner's frame remains active outside its generated
        // handler, even when younger owners have moved into captures. Charge
        // the complete scan before inspecting retained relationships. Request
        // requires its one selected handler; return has already popped it and
        // resume has not restored it, so both require zero active handlers.
        // Same-key clauses remain outside that handler with their owner, or
        // move with the owner in an outward capture. Their count must equal
        // pending invocations, including the one popped clause on its return.
        charge_effect_work(
            &mut self.instantiation_work,
            self.frames.len(),
            RuntimePhase::Capture,
        )?;
        let mut found = None;
        let mut handlers = 0;
        let mut clauses: usize = 0;
        for (index, frame) in self.frames.iter().enumerate() {
            if let Frame::HandlerBoundary {
                registration: Some(candidate),
                ..
            } = frame
                && *candidate == key
            {
                handlers += 1;
                if handlers > active_handlers {
                    return Err(RuntimeFailure::InvalidControlState);
                }
            }
            if let Frame::ClauseBoundary {
                registration: Some(candidate),
                ..
            } = frame
                && *candidate == key
            {
                clauses += 1;
            }
            if let Frame::RegistrationBoundary {
                key: candidate,
                pending_invocations,
                ..
            } = frame
                && *candidate == key
                && found.replace((index, *pending_invocations)).is_some()
            {
                return Err(RuntimeFailure::InvalidControlState);
            }
        }
        if handlers != active_handlers {
            return Err(RuntimeFailure::InvalidControlState);
        }
        let (index, pending) = found.ok_or(RuntimeFailure::InvalidControlState)?;
        if clauses.checked_add(usize::from(returning_clause)) != Some(pending) {
            return Err(RuntimeFailure::InvalidControlState);
        }
        Ok(index)
    }

    fn registration_owner_for_handler(
        &mut self,
        key: RegistrationKey,
        handler: HandlerId,
        returning_clause: bool,
    ) -> Result<usize, RuntimeFailure> {
        let index = self.registration_owner_index(key, 0, returning_clause)?;
        let Frame::RegistrationBoundary { handler: node, .. } = self.frames[index] else {
            return Err(RuntimeFailure::InvalidControlState);
        };
        if self
            .handler(node)
            .is_none_or(|candidate| candidate.id() != handler)
        {
            return Err(RuntimeFailure::InvalidControlState);
        }
        Ok(index)
    }

    fn acquire_cleanup(
        &mut self,
        scope: crate::core::effect::CleanupScopeNode,
        environment: Environment,
    ) -> Result<(), RuntimeFailure> {
        disposal::check()?;
        charge_effect_work(
            &mut self.instantiation_work,
            2usize.saturating_add(environment.len()),
            RuntimePhase::Acquisition,
        )?;
        let callback = environment
            .lookup(scope.callback, &self.program)
            .ok_or(RuntimeFailure::MissingBinding)?;
        if !matches!(callback, Value::Function(_)) {
            return Err(RuntimeFailure::UnexpectedFunctionValue);
        }
        let live = self
            .live_cleanups
            .checked_add(1)
            .filter(|live| *live <= self.cleanup_limit)
            .ok_or_else(|| {
                legacy_failure(
                    RuntimeFailure::ResourceCapacity,
                    ResourceFailureCause::ConfiguredCapacity,
                    RuntimePhase::Acquisition,
                    RuntimeResource::CleanupOwners,
                    Some(1),
                    Some(self.cleanup_limit.saturating_sub(self.live_cleanups)),
                )
            })?;
        self.frames.try_reserve(1).map_err(|_| {
            legacy_failure(
                RuntimeFailure::ResourceCapacity,
                ResourceFailureCause::StorageReservationFailed,
                RuntimePhase::Acquisition,
                RuntimeResource::FrameStorage,
                Some(1),
                None,
            )
        })?;
        self.frames.push(Frame::CleanupBoundary {
            action: scope.action,
            environment: environment.clone(),
        });
        self.live_cleanups = live;
        self.max_frame_depth = self.max_frame_depth.max(self.frames.len());
        self.control = Some(Control::Evaluate(scope.body, environment));
        Ok(())
    }

    fn acquire_registration(
        &mut self,
        node: NodeId,
        environment: Environment,
    ) -> Result<(), RuntimeFailure> {
        disposal::check()?;
        let scope = *self
            .registration(node)
            .ok_or(RuntimeFailure::InvalidControlState)?;
        let handler = self
            .handler(scope.body)
            .ok_or(RuntimeFailure::InvalidControlState)?;
        if handler.id() != scope.handler {
            return Err(RuntimeFailure::InvalidControlState);
        }
        let body = handler.body();
        // Two frames and their callback/handler relation, plus the lexical
        // lookup's upper bound, use the existing evaluator work ledger.
        charge_effect_work(
            &mut self.instantiation_work,
            3usize.saturating_add(environment.len()),
            RuntimePhase::Acquisition,
        )?;
        let callback = environment
            .lookup(scope.callback, &self.program)
            .ok_or(RuntimeFailure::MissingBinding)?;
        let live = self
            .live_registrations
            .checked_add(1)
            .filter(|live| *live <= self.registration_limit)
            .ok_or_else(|| {
                legacy_failure(
                    RuntimeFailure::ResourceCapacity,
                    ResourceFailureCause::ConfiguredCapacity,
                    RuntimePhase::Acquisition,
                    RuntimeResource::RegistrationOwners,
                    Some(1),
                    Some(
                        self.registration_limit
                            .saturating_sub(self.live_registrations),
                    ),
                )
            })?;
        let next = self.next_registration.checked_add(1).ok_or_else(|| {
            legacy_failure(
                RuntimeFailure::ResourceCapacity,
                ResourceFailureCause::ConfiguredCapacity,
                RuntimePhase::Acquisition,
                RuntimeResource::RegistrationKeys,
                Some(1),
                Some(0),
            )
        })?;
        self.frames.try_reserve(2).map_err(|_| {
            legacy_failure(
                RuntimeFailure::ResourceCapacity,
                ResourceFailureCause::StorageReservationFailed,
                RuntimePhase::Acquisition,
                RuntimeResource::FrameStorage,
                Some(2),
                None,
            )
        })?;
        self.trace.try_reserve(1).map_err(|_| {
            legacy_failure(
                RuntimeFailure::ResourceCapacity,
                ResourceFailureCause::StorageReservationFailed,
                RuntimePhase::Acquisition,
                RuntimeResource::EvaluationTrace,
                Some(1),
                None,
            )
        })?;
        if let Some(trace) = &mut self.effect_trace {
            trace.try_reserve(1).map_err(|_| {
                legacy_failure(
                    RuntimeFailure::ResourceCapacity,
                    ResourceFailureCause::StorageReservationFailed,
                    RuntimePhase::Acquisition,
                    RuntimeResource::EffectTrace,
                    Some(1),
                    None,
                )
            })?;
        }
        let key = RegistrationKey(self.next_registration);
        // No fallible work follows publication. The owner surrounds the
        // generated ordinary handler and never interprets an operation.
        self.frames.push(Frame::RegistrationBoundary {
            key,
            handler: scope.body,
            callback,
            handler_active: true,
            pending_invocations: 0,
        });
        self.frames.push(Frame::HandlerBoundary {
            node: scope.body,
            environment: environment.clone(),
            registration: Some(key),
        });
        self.live_registrations = live;
        self.next_registration = next;
        self.max_frame_depth = self.max_frame_depth.max(self.frames.len());
        self.trace.push(TraceEvent::Enter(scope.body));
        self.trace_effect(EffectTraceEvent::HandlerActivated(scope.handler));
        self.control = Some(Control::Evaluate(body, environment));
        Ok(())
    }

    fn acquire_resource(
        &mut self,
        node: NodeId,
        mut environment: Environment,
        value: Value,
    ) -> Result<(), RuntimeFailure> {
        disposal::check()?;
        let resource_program = self.program.clone();
        let Some(ExecutableNode::Effect(expression)) = resource_program.node(node) else {
            return Err(RuntimeFailure::InvalidControlState);
        };
        let EffectExprKind::Operation(EffectOperation::Resource(resource)) = &expression.kind
        else {
            return Err(RuntimeFailure::InvalidControlState);
        };
        let acquisition = resource.acquisition;
        let body = resource.body();
        let api = acquisition
            .api()
            .ok_or(RuntimeFailure::InvalidControlState)?;
        if !api.registry(self.program.registry()) {
            return Err(RuntimeFailure::InvalidControlState);
        }
        if !api.generic() && !matches!(value, Value::Integer(_)) {
            return Err(RuntimeFailure::InvalidControlState);
        }
        let live = self
            .live_resources
            .checked_add(1)
            .filter(|live| *live <= self.resource_limit)
            .ok_or_else(|| {
                legacy_failure(
                    RuntimeFailure::ResourceCapacity,
                    ResourceFailureCause::ConfiguredCapacity,
                    RuntimePhase::Acquisition,
                    RuntimeResource::ResourceOwners,
                    Some(1),
                    Some(self.resource_limit.saturating_sub(self.live_resources)),
                )
            })?;
        let next = self.next_activation.checked_add(1).ok_or_else(|| {
            legacy_failure(
                RuntimeFailure::ResourceCapacity,
                ResourceFailureCause::ConfiguredCapacity,
                RuntimePhase::Acquisition,
                RuntimeResource::ActivationKeys,
                Some(1),
                Some(0),
            )
        })?;
        let key = ActivationKey(self.next_activation);
        self.frames.try_reserve(1).map_err(|_| {
            legacy_failure(
                RuntimeFailure::ResourceCapacity,
                ResourceFailureCause::StorageReservationFailed,
                RuntimePhase::Acquisition,
                RuntimeResource::FrameStorage,
                Some(1),
                None,
            )
        })?;
        if let Some(trace) = &mut self.effect_trace {
            trace.try_reserve(1).map_err(|_| {
                legacy_failure(
                    RuntimeFailure::ResourceCapacity,
                    ResourceFailureCause::StorageReservationFailed,
                    RuntimePhase::Acquisition,
                    RuntimeResource::EffectTrace,
                    Some(1),
                    None,
                )
            })?;
        }
        environment.instantiation = environment.instantiation.acquire(
            acquisition.identity,
            key,
            &mut self.instantiation_work,
            None,
        )?;
        disposal::check()?;
        environment = environment.extend_in_phase(
            acquisition.handle,
            Value::ResourceHandle(key),
            RuntimePhase::Acquisition,
        )?;
        let payload = if api.generic() {
            charge_effect_work(&mut self.instantiation_work, 1, RuntimePhase::Acquisition)?;
            let instance = resource
                .instance_with_budget(&mut self.instantiation_work)
                .map_err(|error| match error {
                    crate::core::BuildError::TypeWorkExceeded => effect_work_failure(
                        &self.instantiation_work,
                        None,
                        RuntimePhase::Acquisition,
                    ),
                    _ => RuntimeFailure::InvalidControlState,
                })?;
            let instance = environment.instantiation.effect(
                &instance,
                &mut self.instantiation_work,
                Some(RuntimePhase::Acquisition),
            )?;
            ResourcePayload::Generic { value, instance }
        } else {
            let Value::Integer(cell) = value else {
                return Err(RuntimeFailure::InvalidControlState);
            };
            ResourcePayload::Cell(cell)
        };
        // Publish only after every fallible preflight. The frame is the sole
        // payload owner; handles and lexical metadata carry only its key.
        self.frames
            .push(Frame::ResourceBoundary { node, key, payload });
        self.live_resources = live;
        self.next_activation = next;
        self.max_frame_depth = self.max_frame_depth.max(self.frames.len());
        self.trace_effect(EffectTraceEvent::ResourceAcquired(key.0));
        self.control = Some(Control::Evaluate(body, environment));
        Ok(())
    }

    fn return_type_application(
        &mut self,
        node: NodeId,
        caller: &Instantiation,
        value: Value,
    ) -> Result<(), RuntimeFailure> {
        let PureExprKind::Computation(PureComputation::TypeApplication(application)) =
            pure_expression(&self.program, node)?
        else {
            return Err(RuntimeFailure::InvalidControlState);
        };
        match value {
            Value::Polymorphic {
                abstraction,
                mut environment,
            } => {
                let PureExprKind::Computation(PureComputation::TypeAbstraction(abstraction)) =
                    pure_expression(&self.program, abstraction)?
                else {
                    return Err(RuntimeFailure::InvalidControlState);
                };
                environment.instantiation = environment.instantiation.apply(
                    caller,
                    abstraction.parameters(),
                    application.arguments(),
                    application.row_arguments(),
                    &mut self.instantiation_work,
                )?;
                self.control = Some(Control::Evaluate(abstraction.body(), environment));
            }
            value @ (Value::ConstructorFunction(_) | Value::Location(_)) => {
                self.control = Some(Control::Return(value))
            }
            _ => return Err(RuntimeFailure::InvalidControlState),
        }
        Ok(())
    }

    fn return_request(
        &mut self,
        node: NodeId,
        instantiation: &Instantiation,
        value: Value,
    ) -> Result<(), RuntimeFailure> {
        disposal::check()?;
        let (effect, operation) = match self.program.node(node) {
            Some(ExecutableNode::Effect(expression)) => match &expression.kind {
                EffectExprKind::Operation(EffectOperation::Request(request)) => {
                    (request.effect(), request.operation())
                }
                _ => return Err(RuntimeFailure::InvalidControlState),
            },
            _ => return Err(RuntimeFailure::InvalidControlState),
        };
        let effect = instantiation.effect(
            effect,
            &mut self.instantiation_work,
            Some(RuntimePhase::Access),
        )?;
        charge_effect_work(&mut self.instantiation_work, 1, RuntimePhase::Access)?;
        let source_symbol = self
            .program
            .registry()
            .native_symbol(operation)
            .map(Arc::clone);
        let mut selected = None;
        // Keep immutable program authority borrowed independently of the mutable
        // runtime work ledger; retaining the admitted arena copies no payloads.
        let handler_program = self.program.clone();
        for (index, frame) in self.frames.iter().enumerate().rev() {
            charge_effect_work(&mut self.instantiation_work, 1, RuntimePhase::Access)?;
            if let Frame::NativeInterpretBoundary { node, environment } = frame {
                let Some(symbol) = &source_symbol else {
                    continue;
                };
                let Some(ExecutableNode::Effect(expression)) = handler_program.node(*node) else {
                    return Err(RuntimeFailure::InvalidControlState);
                };
                let EffectExprKind::Operation(EffectOperation::NativeInterpret(boundary)) =
                    &expression.kind
                else {
                    return Err(RuntimeFailure::InvalidControlState);
                };
                for entry in boundary.interpretations() {
                    charge_effect_work(&mut self.instantiation_work, 1, RuntimePhase::Access)?;
                    if !Arc::ptr_eq(entry.symbol(), symbol) {
                        continue;
                    }
                    let handled = environment.instantiation.effect(
                        entry.effect(),
                        &mut self.instantiation_work,
                        Some(RuntimePhase::Access),
                    )?;
                    if same_effect_instance(&handled, &effect, &mut self.instantiation_work)? {
                        self.trace_effect(EffectTraceEvent::Request(operation));
                        return self.invoke_native(symbol, value);
                    }
                }
                continue;
            }
            if let Frame::ResourceBoundary { node, key, payload } = frame {
                let resource = self
                    .resource(*node)
                    .ok_or(RuntimeFailure::InvalidControlState)?;
                let api = resource
                    .acquisition
                    .api()
                    .ok_or(RuntimeFailure::InvalidControlState)?;
                let matches = match payload {
                    ResourcePayload::Cell(_) => {
                        effect.effect() == api.ops()
                            && Instantiation::activation(&effect) == Some(*key)
                    }
                    ResourcePayload::Generic { instance, .. } => {
                        effect.effect() == api.ops()
                            && Instantiation::activation_at(&effect, 0) == Some(*key)
                            && same_effect_instance(
                                instance,
                                &effect,
                                &mut self.instantiation_work,
                            )?
                    }
                };
                if matches {
                    if !api.generic() {
                        self.trace_effect(EffectTraceEvent::Request(operation));
                    }
                    return self.interpret_cell(index, operation, value);
                }
                continue;
            }
            let Frame::HandlerBoundary {
                node, environment, ..
            } = frame
            else {
                continue;
            };
            let handler = match handler_program.node(*node) {
                Some(ExecutableNode::Effect(expression)) => match &expression.kind {
                    EffectExprKind::Operation(EffectOperation::Handler(handler)) => handler,
                    _ => return Err(RuntimeFailure::InvalidControlState),
                },
                _ => return Err(RuntimeFailure::InvalidControlState),
            };
            if handler.effect().effect() != effect.effect() {
                continue;
            }
            let handled = environment.instantiation.effect(
                handler.effect(),
                &mut self.instantiation_work,
                Some(RuntimePhase::Access),
            )?;
            if same_effect_instance(&handled, &effect, &mut self.instantiation_work)? {
                selected = Some(index);
            }
            if selected.is_some() {
                break;
            }
        }
        disposal::check()?;
        let Some(selected) = selected else {
            return Err(RuntimeFailure::ForeignBinding);
        };
        let registration = match &self.frames[selected] {
            Frame::HandlerBoundary {
                node,
                registration: Some(key),
                ..
            } => Some((*key, *node)),
            _ => None,
        };
        let registration_owner = if let Some((key, handler)) = registration {
            let index = self.registration_owner(key, handler, 1)?;
            let Frame::RegistrationBoundary {
                handler_active,
                pending_invocations,
                ..
            } = &self.frames[index]
            else {
                return Err(RuntimeFailure::InvalidControlState);
            };
            if !handler_active || index >= selected {
                return Err(RuntimeFailure::InvalidControlState);
            }
            Some((
                index,
                pending_invocations.checked_add(1).ok_or_else(|| {
                    legacy_failure(
                        RuntimeFailure::ResourceCapacity,
                        ResourceFailureCause::ConfiguredCapacity,
                        RuntimePhase::Capture,
                        RuntimeResource::RegistrationInvocations,
                        Some(1),
                        Some(0),
                    )
                })?,
            ))
        } else {
            None
        };
        let (handler_id, handler_environment, clause_owner, clause_body, bindings) = {
            let Frame::HandlerBoundary {
                node: handler_node,
                environment,
                ..
            } = &self.frames[selected]
            else {
                return Err(RuntimeFailure::InvalidControlState);
            };
            let handler = self
                .handler(*handler_node)
                .ok_or(RuntimeFailure::InvalidControlState)?;
            let clause = handler
                .clauses()
                .iter()
                .find(|clause| clause.operation() == operation)
                .ok_or(RuntimeFailure::InvalidControlState)?;
            let mut bindings = Vec::new();
            if !matches_pattern(clause.pattern(), &value, &self.heap, &mut bindings)? {
                return Err(RuntimeFailure::ImpossibleMatch);
            }
            (
                handler.id(),
                environment.clone(),
                clause.resume(),
                clause.body(),
                bindings,
            )
        };
        let clause_environment = handler_environment.extend_many(bindings)?;
        if let Some(trace) = &mut self.effect_trace {
            reserve_control(trace, 3, RuntimeResource::EffectTrace, false)?;
        }
        let continuation = self.capture_from(selected)?;
        if let Some((index, pending)) = registration_owner
            && let Frame::RegistrationBoundary {
                handler_active,
                pending_invocations,
                ..
            } = &mut self.frames[index]
        {
            *handler_active = false;
            *pending_invocations = pending;
        }
        self.frames.push(Frame::ClauseBoundary {
            handler: handler_id,
            owner: clause_owner,
            continuation: Some(continuation),
            registration: registration.map(|(key, _)| key),
        });
        self.trace_effect(EffectTraceEvent::Request(operation));
        self.trace_effect(EffectTraceEvent::HandlerSelected(handler_id));
        self.trace_effect(EffectTraceEvent::ClauseEntered(handler_id, operation));
        self.max_frame_depth = self.max_frame_depth.max(self.frames.len());
        self.control = Some(Control::Evaluate(clause_body, clause_environment));
        Ok(())
    }

    fn invoke_native(
        &mut self,
        symbol: &Arc<crate::foreign::checked_source::CheckedForeignSymbol>,
        value: Value,
    ) -> Result<(), RuntimeFailure> {
        use crate::foreign::{
            checked_source::{NativeArgument as Shape, NativeResult},
            source_runtime::{NativeArgument, NativeReply},
        };
        let shapes = symbol.arguments();
        charge_runtime_work(
            &mut self.instantiation_work,
            shapes.len(),
            RuntimePhase::Access,
        )?;
        // Keep owned ordinary values, including each Bytes Arc/prefix backing,
        // alive until the synchronous callback has returned.
        let mut retained = Vec::new();
        reserve_control(
            &mut retained,
            shapes.len(),
            RuntimeResource::HeapCells,
            false,
        )?;
        match shapes.len() {
            0 if matches!(value, Value::Unit) => {}
            0 => return Err(RuntimeFailure::ForeignBinding),
            1 => retained.push(value),
            _ => {
                let Value::Location(location) = value else {
                    return Err(RuntimeFailure::ForeignBinding);
                };
                let location =
                    resolve_location_with_work(&self.heap, location, &mut self.instantiation_work)?;
                let Some(HeapCell::Tuple(fields)) = self.heap.get(location) else {
                    return Err(RuntimeFailure::ForeignBinding);
                };
                if fields.len() != shapes.len() {
                    return Err(RuntimeFailure::ForeignBinding);
                }
                retained.extend(fields.iter().cloned());
            }
        }
        let mut arguments = Vec::new();
        reserve_control(
            &mut arguments,
            shapes.len(),
            RuntimeResource::HeapCells,
            false,
        )?;
        for (shape, value) in shapes.iter().zip(&retained) {
            let pointer = match (shape, value) {
                (Shape::Address, Value::Address(pointer)) => pointer.as_ptr(),
                (Shape::Bytes, bytes) if bytes.bytes().is_some() => bytes
                    .bytes()
                    .expect("guarded Bytes")
                    .as_ptr()
                    .cast_mut()
                    .cast(),
                _ => return Err(RuntimeFailure::ForeignBinding),
            };
            arguments.push(NativeArgument(pointer));
        }
        let reply = self
            .source_bindings
            .ok_or(RuntimeFailure::ForeignBinding)?
            .invoke(symbol, &arguments)?;
        let result = match (symbol.result(), reply) {
            (NativeResult::Address, NativeReply::Address(pointer)) => {
                Value::Address(super::value::Address::new(pointer))
            }
            (NativeResult::Void, NativeReply::Void) => Value::Unit,
            _ => return Err(RuntimeFailure::ForeignBinding),
        };
        drop(retained);
        self.control = Some(Control::Return(result));
        Ok(())
    }

    fn interpret_cell(
        &mut self,
        selected: usize,
        operation: OperationId,
        value: Value,
    ) -> Result<(), RuntimeFailure> {
        disposal::check()?;
        let Frame::ResourceBoundary { node, .. } = &self.frames[selected] else {
            return Err(RuntimeFailure::InvalidControlState);
        };
        let api = self
            .resource(*node)
            .and_then(|resource| resource.acquisition.api())
            .ok_or(RuntimeFailure::InvalidControlState)?;
        if api.generic() {
            return self.interpret_generic_cell(selected, operation, value);
        }
        let (handle, written) = if operation == OperationId::new(api.ops(), 0) {
            (value, None)
        } else if operation == OperationId::new(api.ops(), 1) {
            let Value::Location(location) = value else {
                return Err(RuntimeFailure::InvalidControlState);
            };
            let location = resolve_location(&self.heap, location)?;
            let Some(HeapCell::Tuple(elements)) = self.heap.get(location) else {
                return Err(RuntimeFailure::InvalidControlState);
            };
            let [handle, Value::Integer(written)] = elements.as_ref() else {
                return Err(RuntimeFailure::InvalidControlState);
            };
            (handle.clone(), Some(written.clone()))
        } else {
            return Err(RuntimeFailure::InvalidControlState);
        };
        let Frame::ResourceBoundary {
            key,
            payload: ResourcePayload::Cell(cell),
            ..
        } = &mut self.frames[selected]
        else {
            return Err(RuntimeFailure::InvalidControlState);
        };
        if !matches!(handle, Value::ResourceHandle(found) if found == *key) {
            return Err(RuntimeFailure::InvalidControlState);
        }
        let (result, event) = if let Some(written) = written {
            *cell = written;
            (Value::Unit, EffectTraceEvent::ResourceWritten(key.0))
        } else {
            (
                Value::Integer(cell.clone()),
                EffectTraceEvent::ResourceRead(key.0),
            )
        };
        self.trace_effect(event);
        self.control = Some(Control::Return(result));
        Ok(())
    }

    fn interpret_generic_cell(
        &mut self,
        selected: usize,
        operation: OperationId,
        value: Value,
    ) -> Result<(), RuntimeFailure> {
        disposal::check()?;
        let Frame::ResourceBoundary {
            key,
            payload: ResourcePayload::Generic { instance, .. },
            ..
        } = &self.frames[selected]
        else {
            return Err(RuntimeFailure::InvalidControlState);
        };
        let key = *key;
        let effect = instance.effect();
        let (handle, replacement) = if operation == OperationId::new(effect, 0) {
            (value, None)
        } else if operation == OperationId::new(effect, 1) {
            let Value::Location(location) = value else {
                return Err(RuntimeFailure::InvalidControlState);
            };
            let location =
                resolve_location_with_work(&self.heap, location, &mut self.instantiation_work)?;
            let Some(HeapCell::Tuple(elements)) = self.heap.get(location) else {
                return Err(RuntimeFailure::InvalidControlState);
            };
            let [Value::ResourceHandle(handle), replacement] = elements.as_ref() else {
                return Err(RuntimeFailure::InvalidControlState);
            };
            if *handle != key {
                return Err(RuntimeFailure::InvalidControlState);
            }
            let replacement = copy_generic_cell_value(replacement, &mut self.instantiation_work)?;
            (Value::ResourceHandle(*handle), Some(replacement))
        } else {
            return Err(RuntimeFailure::InvalidControlState);
        };
        if !matches!(handle, Value::ResourceHandle(found) if found == key) {
            return Err(RuntimeFailure::InvalidControlState);
        }
        // Both builtin events commit together only after all fallible preparation.
        charge_effect_work(&mut self.instantiation_work, 2, RuntimePhase::Access)?;
        if let Some(trace) = &mut self.effect_trace {
            trace.try_reserve(2).map_err(|_| {
                resource_failure(
                    ResourceFailureCause::StorageReservationFailed,
                    RuntimePhase::Access,
                    RuntimeResource::EffectTrace,
                    Some(2),
                    None,
                )
            })?;
        }
        let Frame::ResourceBoundary {
            payload: ResourcePayload::Generic { value: root, .. },
            ..
        } = &mut self.frames[selected]
        else {
            return Err(RuntimeFailure::InvalidControlState);
        };
        let (result, event) = if let Some(replacement) = replacement {
            *root = replacement;
            (Value::Unit, EffectTraceEvent::ResourceWritten(key.0))
        } else {
            let reply = copy_generic_cell_value(root, &mut self.instantiation_work)?;
            (reply, EffectTraceEvent::ResourceRead(key.0))
        };
        self.trace_effect(EffectTraceEvent::Request(operation));
        self.trace_effect(event);
        self.control = Some(Control::Return(result));
        Ok(())
    }

    fn capture_from(&mut self, selected: usize) -> Result<CapturedContinuation, RuntimeFailure> {
        charge_effect_work(
            &mut self.instantiation_work,
            self.frames.len(),
            RuntimePhase::Capture,
        )?;
        let captured_len = self
            .frames
            .len()
            .checked_sub(selected)
            .ok_or(RuntimeFailure::InvalidControlState)?;
        let retained = self
            .captured_cells
            .checked_add(captured_len)
            .ok_or_else(|| {
                control_failure(
                    ResourceFailureCause::ConfiguredCapacity,
                    RuntimeResource::FrameStorage,
                    Some(captured_len),
                    Some(usize::MAX - self.captured_cells),
                )
            })?;
        if retained > self.capture_limit {
            return Err(control_failure(
                ResourceFailureCause::ConfiguredCapacity,
                RuntimeResource::FrameStorage,
                Some(captured_len),
                Some(self.capture_limit.saturating_sub(self.captured_cells)),
            ));
        }
        let mut frames = Vec::new();
        reserve_control(
            &mut frames,
            captured_len,
            RuntimeResource::FrameStorage,
            true,
        )?;
        frames.extend(self.frames.drain(selected..));
        self.captured_cells = retained;
        Ok(CapturedContinuation { frames })
    }

    fn return_resume(&mut self, node: NodeId, value: Value) -> Result<(), RuntimeFailure> {
        disposal::check()?;
        let (handler, owner) = match self.program.node(node) {
            Some(ExecutableNode::Effect(expression)) => match &expression.kind {
                EffectExprKind::Operation(EffectOperation::Resume(resume)) => {
                    (resume.handler(), resume.owner())
                }
                _ => return Err(RuntimeFailure::InvalidControlState),
            },
            _ => return Err(RuntimeFailure::InvalidControlState),
        };
        let (boundary_index, registration) = self
            .frames
            .iter()
            .enumerate()
            .rev()
            .find_map(|(index, frame)| match frame {
                Frame::ClauseBoundary {
                    handler: found_handler,
                    owner: found_owner,
                    registration,
                    ..
                } if *found_handler == handler && *found_owner == owner => {
                    Some((index, *registration))
                }
                _ => None,
            })
            .ok_or(RuntimeFailure::InvalidControlState)?;
        let registration_owner = if let Some(key) = registration {
            let index = self.registration_owner_for_handler(key, handler, false)?;
            let Frame::RegistrationBoundary {
                handler_active,
                pending_invocations,
                ..
            } = &self.frames[index]
            else {
                return Err(RuntimeFailure::InvalidControlState);
            };
            if *handler_active || *pending_invocations == 0 {
                return Err(RuntimeFailure::InvalidControlState);
            }
            Some(index)
        } else {
            None
        };
        let Frame::ClauseBoundary { continuation, .. } = &self.frames[boundary_index] else {
            return Err(RuntimeFailure::InvalidControlState);
        };
        let captured = continuation
            .as_ref()
            .ok_or(RuntimeFailure::InvalidControlState)?;
        let captured_len = captured.frames.len();
        if let Some(key) = registration {
            charge_effect_work(
                &mut self.instantiation_work,
                captured_len,
                RuntimePhase::Capture,
            )?;
            let Some(Frame::HandlerBoundary {
                node,
                registration: Some(found),
                ..
            }) = captured.frames.first()
            else {
                return Err(RuntimeFailure::InvalidControlState);
            };
            if *found != key {
                return Err(RuntimeFailure::InvalidControlState);
            }
            let captured_node = *node;
            if self
                .handler(captured_node)
                .is_none_or(|found| found.id() != handler)
            {
                return Err(RuntimeFailure::InvalidControlState);
            }
            if captured.frames.iter().skip(1).any(|frame| {
                matches!(frame,
                Frame::HandlerBoundary { registration: Some(found), .. } if *found == key)
            }) {
                return Err(RuntimeFailure::InvalidControlState);
            }
        }
        let retained = self
            .captured_cells
            .checked_sub(captured_len)
            .ok_or(RuntimeFailure::InvalidControlState)?;
        if self.live_registrations != 0 {
            charge_effect_work(
                &mut self.instantiation_work,
                captured_len,
                RuntimePhase::Capture,
            )?;
            for frame in &captured.frames {
                if let Frame::HandlerBoundary { node, .. } = frame {
                    self.handler(*node)
                        .ok_or(RuntimeFailure::InvalidControlState)?;
                }
            }
        }
        if let Some(trace) = &mut self.effect_trace {
            reserve_control(
                trace,
                captured_len.saturating_add(1),
                RuntimeResource::EffectTrace,
                false,
            )?;
        }
        reserve_control(
            &mut self.frames,
            captured_len,
            RuntimeResource::FrameStorage,
            false,
        )?;
        let Frame::ClauseBoundary { continuation, .. } = &mut self.frames[boundary_index] else {
            return Err(RuntimeFailure::InvalidControlState);
        };
        let mut continuation = continuation
            .take()
            .ok_or(RuntimeFailure::InvalidControlState)?;
        self.trace_effect(EffectTraceEvent::Resume(handler));
        for frame in &continuation.frames {
            if let Frame::HandlerBoundary { node, .. } = frame {
                // Restore the original ordinary handler identity.
                let restored = self
                    .handler(*node)
                    .ok_or(RuntimeFailure::InvalidControlState)?;
                let restored_id = restored.id();
                self.trace_effect(EffectTraceEvent::HandlerRestored(restored_id));
            }
        }
        self.captured_cells = retained;
        self.frames.append(&mut continuation.frames);
        if let Some(index) = registration_owner
            && let Frame::RegistrationBoundary { handler_active, .. } = &mut self.frames[index]
        {
            *handler_active = true;
        }
        self.max_frame_depth = self.max_frame_depth.max(self.frames.len());
        self.control = Some(Control::Return(value));
        Ok(())
    }

    fn discard(&mut self, handler: HandlerId, owner: ResumeId) -> Result<(), RuntimeFailure> {
        disposal::check()?;
        let (boundary_index, registration) = self
            .frames
            .iter()
            .enumerate()
            .rev()
            .find_map(|(index, frame)| match frame {
                Frame::ClauseBoundary {
                    handler: found_handler,
                    owner: found_owner,
                    registration,
                    ..
                } if *found_handler == handler && *found_owner == owner => {
                    Some((index, *registration))
                }
                _ => None,
            })
            .ok_or(RuntimeFailure::InvalidControlState)?;
        // A generated registration clause must resume its publication. Local
        // source handlers in a callback have their own ordinary capabilities.
        if registration.is_some() {
            return Err(RuntimeFailure::InvalidControlState);
        }
        let Frame::ClauseBoundary {
            continuation: Some(captured),
            ..
        } = &self.frames[boundary_index]
        else {
            return Err(RuntimeFailure::InvalidControlState);
        };
        selected_handler_for_discard(
            &self.program,
            captured,
            handler,
            &mut self.instantiation_work,
        )?;
        let mut pending = Vec::new();
        let mut count = 0usize;
        let mut owners = 0usize;
        let mut registrations = Vec::new();
        let mut associated = Vec::new();
        charge_effect_work(&mut self.instantiation_work, 1, RuntimePhase::Capture)?;
        reserve_control(&mut pending, 1, RuntimeResource::CaptureInspection, false)?;
        pending.push(captured);
        while let Some(capture) = pending.pop() {
            charge_effect_work(
                &mut self.instantiation_work,
                capture.frames.len().saturating_add(1),
                RuntimePhase::Capture,
            )?;
            count = count.checked_add(capture.frames.len()).ok_or_else(|| {
                control_failure(
                    ResourceFailureCause::ConfiguredCapacity,
                    RuntimeResource::FrameStorage,
                    Some(capture.frames.len()),
                    Some(usize::MAX - count),
                )
            })?;
            for frame in &capture.frames {
                match frame {
                    Frame::CleanupCompletion { .. } | Frame::CloseCompletion => {
                        return Err(RuntimeFailure::InvalidControlState);
                    }
                    Frame::ClauseBoundary {
                        handler: nested_handler,
                        continuation,
                        registration,
                        ..
                    } => {
                        if let Some(nested) = continuation {
                            selected_handler_for_discard(
                                &self.program,
                                nested,
                                *nested_handler,
                                &mut self.instantiation_work,
                            )?;
                            reserve_control(
                                &mut pending,
                                1,
                                RuntimeResource::CaptureInspection,
                                false,
                            )?;
                            pending.push(nested);
                        }
                        // Consuming a capture does not complete its registration clause.
                        if let Some(key) = registration {
                            reserve_control(
                                &mut associated,
                                1,
                                RuntimeResource::RegistrationIdentities,
                                false,
                            )?;
                            associated.push(*key);
                        }
                    }
                    Frame::RegistrationBoundary { key, .. } => {
                        reserve_control(
                            &mut registrations,
                            1,
                            RuntimeResource::RegistrationIdentities,
                            false,
                        )?;
                        registrations.push(*key);
                        owners += 1;
                    }
                    Frame::ResourceBoundary { .. } | Frame::CleanupBoundary { .. } => owners += 1,
                    Frame::HandlerBoundary { node, .. } => {
                        self.handler(*node)
                            .ok_or(RuntimeFailure::InvalidControlState)?;
                    }
                    _ => {}
                }
            }
        }
        for key in associated {
            charge_effect_work(
                &mut self.instantiation_work,
                registrations.len(),
                RuntimePhase::Capture,
            )?;
            if !registrations.contains(&key) {
                return Err(RuntimeFailure::InvalidControlState);
            }
        }
        let retained = self
            .captured_cells
            .checked_sub(count)
            .ok_or(RuntimeFailure::InvalidControlState)?;
        charge_effect_work(
            &mut self.instantiation_work,
            count.saturating_add(owners).saturating_add(1),
            RuntimePhase::Capture,
        )?;
        let closing_cells = owners;
        let mut work = Vec::new();
        let mut closing = Vec::new();
        reserve_control(&mut work, count, RuntimeResource::FrameStorage, true)?;
        reserve_control(
            &mut closing,
            closing_cells,
            RuntimeResource::FrameStorage,
            true,
        )?;
        reserve_control(
            &mut self.frames,
            closing_cells.saturating_add(1),
            RuntimeResource::FrameStorage,
            false,
        )?;
        if let Some(trace) = &mut self.effect_trace {
            reserve_control(trace, 1, RuntimeResource::EffectTrace, false)?;
        }
        // All fallible checks precede consumption and accounting release.
        let Frame::ClauseBoundary { continuation, .. } = &mut self.frames[boundary_index] else {
            return Err(RuntimeFailure::InvalidControlState);
        };
        let mut captured = continuation
            .take()
            .ok_or(RuntimeFailure::InvalidControlState)?;
        work.append(&mut captured.frames);
        while let Some(mut frame) = work.pop() {
            // Inspection and every fallible reservation precede ownership transfer.
            match &mut frame {
                Frame::ClauseBoundary {
                    continuation: Some(nested),
                    ..
                } => work.append(&mut nested.frames),
                Frame::RegistrationBoundary {
                    handler_active,
                    pending_invocations,
                    ..
                } => {
                    // Generated hook handlers are ordinary captured handlers,
                    // so no handler or invocation survives owned discard.
                    *handler_active = false;
                    *pending_invocations = 0;
                    closing.push(frame);
                }
                Frame::ResourceBoundary { .. } => closing.push(frame),
                Frame::CleanupBoundary { .. } => closing.push(frame),
                _ => {}
            }
        }
        self.captured_cells = retained;
        if owners != 0 {
            self.frames.push(Frame::CloseCompletion);
        }
        self.frames.extend(closing.into_iter().rev());
        self.max_frame_depth = self.max_frame_depth.max(self.frames.len());
        self.trace_effect(EffectTraceEvent::Discard(handler));
        self.control = Some(Control::Return(Value::Unit));
        Ok(())
    }

    fn handler(&self, node: NodeId) -> Option<&crate::core::HandlerNode> {
        let ExecutableNode::Effect(expression) = self.program.node(node)? else {
            return None;
        };
        match &expression.kind {
            EffectExprKind::Operation(EffectOperation::Handler(handler)) => Some(handler),

            _ => None,
        }
    }

    fn resource(&self, node: NodeId) -> Option<&crate::core::effect::ResourceScopeNode> {
        let ExecutableNode::Effect(expression) = self.program.node(node)? else {
            return None;
        };
        let EffectExprKind::Operation(EffectOperation::Resource(resource)) = &expression.kind
        else {
            return None;
        };
        Some(resource)
    }

    fn registration(&self, node: NodeId) -> Option<&crate::core::effect::RegistrationScopeNode> {
        let ExecutableNode::Effect(expression) = self.program.node(node)? else {
            return None;
        };
        let EffectExprKind::Operation(EffectOperation::Registration(scope)) = &expression.kind
        else {
            return None;
        };
        Some(scope)
    }
}

fn legacy_failure(
    reason: RuntimeFailure,
    cause: ResourceFailureCause,
    phase: RuntimePhase,
    resource: RuntimeResource,
    requested: Option<usize>,
    available: Option<usize>,
) -> RuntimeFailure {
    reason.with_resource_details(super::ResourceFailure::new(
        cause, phase, resource, requested, available,
    ))
}

fn checked_environment_len(
    len: usize,
    additional: usize,
    phase: RuntimePhase,
) -> Result<usize, RuntimeFailure> {
    len.checked_add(additional).ok_or_else(|| {
        legacy_failure(
            RuntimeFailure::EnvironmentCapacity,
            ResourceFailureCause::ConfiguredCapacity,
            phase,
            RuntimeResource::EnvironmentBindings,
            Some(additional),
            Some(usize::MAX - len),
        )
    })
}

fn control_failure(
    cause: ResourceFailureCause,
    resource: RuntimeResource,
    requested: Option<usize>,
    available: Option<usize>,
) -> RuntimeFailure {
    RuntimeFailure::CapturedControlCapacity.with_resource_details(super::ResourceFailure::new(
        cause,
        RuntimePhase::Capture,
        resource,
        requested,
        available,
    ))
}

fn reserve_control<T>(
    storage: &mut Vec<T>,
    additional: usize,
    resource: RuntimeResource,
    exact: bool,
) -> Result<(), RuntimeFailure> {
    // Vec cannot represent more than isize::MAX bytes (or usize::MAX ZSTs).
    // This bound is known before asking the allocator; later reservation
    // errors retain their undetermined cause on stable Rust.
    let maximum = if size_of::<T>() == 0 {
        usize::MAX
    } else {
        isize::MAX as usize / size_of::<T>()
    };
    let available = maximum.saturating_sub(storage.len());
    if additional > available {
        return Err(control_failure(
            ResourceFailureCause::ConfiguredCapacity,
            resource,
            Some(additional),
            Some(available),
        ));
    }
    #[cfg(test)]
    if let Some(cause) = machine_test_hooks::FAIL_CONTROL_RESERVATION.take() {
        return Err(control_failure(cause, resource, Some(additional), None));
    }
    let reservation = if exact {
        storage.try_reserve_exact(additional)
    } else {
        storage.try_reserve(additional)
    };
    reservation.map_err(|_| {
        control_failure(
            ResourceFailureCause::StorageReservationFailed,
            resource,
            Some(additional),
            None,
        )
    })
}

fn charge_effect_work(
    work: &mut TypeWorkBudget,
    requested: usize,
    phase: RuntimePhase,
) -> Result<(), RuntimeFailure> {
    work.charge(requested)
        .map_err(|()| effect_work_failure(work, Some(requested), phase))
}

fn effect_work_failure(
    work: &TypeWorkBudget,
    requested: Option<usize>,
    phase: RuntimePhase,
) -> RuntimeFailure {
    RuntimeFailure::EnvironmentCapacity.with_resource_details(super::ResourceFailure::new(
        ResourceFailureCause::WorkBudgetExhausted,
        phase,
        RuntimeResource::WorkUnits,
        requested,
        Some(work.remaining()),
    ))
}

// Represented aggregate values and environments share their existing roots.
// Integer magnitude and function provenance are proportional retained copies.
fn copy_generic_cell_value(
    value: &Value,
    work: &mut TypeWorkBudget,
) -> Result<Value, RuntimeFailure> {
    let magnitude = match value {
        Value::Integer(integer) => usize::try_from(integer.magnitude_byte_length())
            .map_err(|_| effect_work_failure(work, None, RuntimePhase::Access))?,
        _ => 0,
    };
    charge_effect_work(work, magnitude.saturating_add(1), RuntimePhase::Access)?;
    if let Value::Function(function) = value {
        let origin = crate::resolved::clone_effect_origin_with_budget(&function.origin, work)
            .map_err(|()| effect_work_failure(work, None, RuntimePhase::Access))?;
        return Ok(Value::Function(Closure {
            parameter: function.parameter,
            body: function.body,
            program: function.program.clone(),
            environment: function.environment.clone(),
            origin,
        }));
    }
    Ok(value.clone())
}

fn same_effect_instance(
    left: &EffectInstance,
    right: &EffectInstance,
    work: &mut TypeWorkBudget,
) -> Result<bool, RuntimeFailure> {
    if left.effect() != right.effect() || left.arguments().len() != right.arguments().len() {
        return Ok(false);
    }
    for (left, right) in left.arguments().iter().zip(right.arguments()) {
        if !crate::types::same_kinded_argument_with_budget(left, right, work)
            .map_err(|()| effect_work_failure(work, None, RuntimePhase::Access))?
        {
            return Ok(false);
        }
    }
    Ok(true)
}

fn dispatch_entry(
    program: &ExecutableProgram,
    node: NodeId,
    environment: Environment,
    heap: &mut Vec<HeapCell>,
) -> Result<Transition, RuntimeFailure> {
    let expression = program.node(node).ok_or(RuntimeFailure::MissingNode)?;
    let (kind, origin) = match expression {
        ExecutableNode::Pure(expression) => (&expression.kind, &expression.origin),
        ExecutableNode::Effect(expression) => match &expression.kind {
            EffectExprKind::Pure(kind) => (kind, &expression.origin),
            EffectExprKind::Operation(operation) => {
                return Ok(match operation {
                    EffectOperation::Registration(_) => {
                        return Err(RuntimeFailure::InvalidControlState);
                    }
                    EffectOperation::Cleanup(_) => return Err(RuntimeFailure::InvalidControlState),
                    EffectOperation::Resource(resource) => Transition::suspend(
                        Control::Evaluate(resource.initializer(), environment.clone()),
                        Frame::ResourceInitializer { node, environment },
                    ),
                    EffectOperation::Request(request) => Transition::suspend(
                        Control::Evaluate(request.operand(), environment.clone()),
                        Frame::Request {
                            node,
                            instantiation: environment.instantiation,
                        },
                    ),
                    EffectOperation::NativeInterpret(boundary) => Transition::suspend(
                        Control::Evaluate(boundary.body(), environment.clone()),
                        Frame::NativeInterpretBoundary { node, environment },
                    ),
                    EffectOperation::Handler(handler) => Transition::suspend(
                        Control::Evaluate(handler.body(), environment.clone()),
                        Frame::HandlerBoundary {
                            node,
                            environment,
                            registration: None,
                        },
                    ),
                    EffectOperation::Resume(resume) => Transition::suspend(
                        Control::Evaluate(resume.value(), environment),
                        Frame::Resume { node },
                    ),
                    EffectOperation::Discard(discard) => {
                        Transition::direct(Control::Discard(discard.handler(), discard.owner()))
                    }
                });
            }
        },
    };
    Ok(match kind {
        PureExprKind::Value(PureValue::String(string)) => {
            let text = std::str::from_utf8(string.bytes())
                .map_err(|_| RuntimeFailure::InvalidControlState)?;
            Transition::direct(Control::Return(Value::String(packed_string(text)?)))
        }
        PureExprKind::Value(PureValue::Intrinsic(intrinsic)) => {
            Transition::direct(Control::Return(Value::Intrinsic(*intrinsic)))
        }
        PureExprKind::Value(PureValue::Integer(integer)) => enter_integer(integer),
        PureExprKind::Value(PureValue::Boolean(boolean)) => enter_boolean(*boolean),
        PureExprKind::Value(PureValue::Unit(unit)) => enter_unit(*unit),
        PureExprKind::Value(PureValue::Function(function)) => {
            enter_function(function, program.clone(), environment, origin.clone())
        }
        PureExprKind::Variable(variable) => enter_variable(program, *variable, environment)?,
        PureExprKind::Computation(PureComputation::Bind(binding)) => {
            enter_binding(binding, environment)
        }
        PureExprKind::Computation(PureComputation::RecursiveBind(group)) => {
            enter_recursive_binding(program, group, environment, heap)?
        }
        PureExprKind::Computation(PureComputation::Primitive(operation)) => {
            enter_primitive(*operation, environment)
        }
        PureExprKind::Computation(PureComputation::Apply(application)) => {
            enter_application(*application, environment)
        }
        PureExprKind::Value(PureValue::Constructor(constructor)) => {
            enter_constructor(program, *constructor, heap)?
        }
        PureExprKind::Computation(PureComputation::Tuple(tuple)) => {
            enter_tuple(tuple, environment)?
        }
        PureExprKind::Computation(PureComputation::Match(match_node)) => {
            enter_match(match_node, environment)
        }
        PureExprKind::Computation(PureComputation::NewtypeConversion(operation)) => {
            Transition::direct(Control::Evaluate(operation.child(), environment))
        }
        PureExprKind::Computation(PureComputation::LocalNominalScope(scope)) => {
            Transition::direct(Control::Evaluate(scope.body(), environment))
        }
        PureExprKind::Computation(PureComputation::TypeAbstraction(operation)) => {
            if matches!(program, ExecutableProgram::Effect(_)) {
                Transition::direct(Control::Return(Value::Polymorphic {
                    abstraction: node,
                    environment,
                }))
            } else {
                enter_type_abstraction(operation, environment)
            }
        }
        PureExprKind::Computation(PureComputation::TypeApplication(operation)) => {
            if matches!(program, ExecutableProgram::Effect(_)) {
                Transition::suspend(
                    Control::Evaluate(operation.function(), environment.clone()),
                    Frame::TypeApplication {
                        node,
                        caller: environment.instantiation,
                    },
                )
            } else {
                enter_type_application(operation, environment)
            }
        }
    })
}

fn enter_integer(integer: &crate::core::literal::IntegerNode) -> Transition {
    Transition::direct(Control::Return(Value::Integer(integer.value().clone())))
}

fn enter_boolean(boolean: crate::core::literal::BooleanNode) -> Transition {
    Transition::direct(Control::Return(Value::Boolean(boolean.value())))
}

fn enter_unit(_unit: crate::core::literal::UnitNode) -> Transition {
    Transition::direct(Control::Return(Value::Unit))
}

fn enter_constructor(
    program: &ExecutableProgram,
    constructor: crate::core::data::ConstructorNode,
    heap: &mut Vec<HeapCell>,
) -> Result<Transition, RuntimeFailure> {
    let info = program
        .registry()
        .constructor(constructor.constructor())
        .ok_or(RuntimeFailure::InvalidLocation)?;
    if info.payload.is_some() {
        Ok(Transition::direct(Control::Return(
            Value::ConstructorFunction(constructor.constructor()),
        )))
    } else {
        let location = allocate_heap(heap, HeapCell::Constructor(constructor.constructor(), None))?;
        Ok(Transition::direct(Control::Return(Value::Location(
            location,
        ))))
    }
}

fn enter_tuple(
    tuple: &crate::core::data::TupleNode,
    environment: Environment,
) -> Result<Transition, RuntimeFailure> {
    let Some(first) = tuple.elements().first().copied() else {
        return Err(RuntimeFailure::InvalidControlState);
    };
    Ok(Transition::suspend(
        Control::Evaluate(first, environment.clone()),
        Frame::Tuple {
            elements: tuple.elements().to_vec().into_boxed_slice(),
            next: 1,
            values: Vec::with_capacity(tuple.elements().len()),
            environment,
        },
    ))
}

fn enter_match(match_node: &crate::core::data::MatchNode, environment: Environment) -> Transition {
    Transition::suspend(
        Control::Evaluate(match_node.scrutinee(), environment.clone()),
        Frame::Match {
            arms: match_node.arms().to_vec().into_boxed_slice(),
            environment,
        },
    )
}

fn enter_type_abstraction(
    operation: &crate::core::type_ops::TypeAbstractionNode,
    environment: Environment,
) -> Transition {
    Transition::direct(Control::Evaluate(operation.body(), environment))
}

fn enter_type_application(
    operation: &crate::core::type_ops::TypeApplicationNode,
    environment: Environment,
) -> Transition {
    Transition::direct(Control::Evaluate(operation.function(), environment))
}

fn enter_function(
    function: &crate::core::function::FunctionNode,
    program: ExecutableProgram,
    environment: Environment,
    origin: crate::source::Origin,
) -> Transition {
    Transition::direct(Control::Return(Value::Function(Closure {
        parameter: function.parameter().id(),
        body: function.body(),
        program,
        environment,
        origin,
    })))
}

fn enter_variable(
    program: &ExecutableProgram,
    variable: crate::core::variable::VariableNode,
    environment: Environment,
) -> Result<Transition, RuntimeFailure> {
    let value = environment
        .lookup(variable.binder(), program)
        .ok_or(RuntimeFailure::MissingBinding)?;
    Ok(Transition::direct(Control::Return(value)))
}

fn enter_recursive_binding(
    program: &ExecutableProgram,
    group: &crate::core::recursion::RecursiveBindingNode,
    environment: Environment,
    heap: &mut Vec<HeapCell>,
) -> Result<Transition, RuntimeFailure> {
    let mut members = Vec::with_capacity(group.members().len());
    let mut pending = Vec::new();
    for member in group.members() {
        let initializer_origin = match program
            .node(member.initializer())
            .ok_or(RuntimeFailure::MissingNode)?
        {
            ExecutableNode::Pure(expression) => expression.origin.clone(),
            ExecutableNode::Effect(expression) => expression.origin.clone(),
        };
        let mut erased_initializer = member.initializer();
        loop {
            let expression = pure_expression(program, erased_initializer)?;
            let PureExprKind::Computation(PureComputation::TypeAbstraction(operation)) = expression
            else {
                break;
            };
            erased_initializer = operation.body();
        }
        let erased = pure_expression(program, erased_initializer)?;
        let kind = match erased {
            PureExprKind::Value(PureValue::Intrinsic(intrinsic)) => {
                RecursiveMemberKind::Intrinsic {
                    intrinsic: *intrinsic,
                    abstraction: (matches!(program, ExecutableProgram::Effect(_))
                        && erased_initializer != member.initializer())
                    .then_some(member.initializer()),
                }
            }
            PureExprKind::Value(PureValue::Function(function)) => RecursiveMemberKind::Function {
                parameter: function.parameter().id(),
                body: function.body(),
                origin: initializer_origin,
                abstraction: (matches!(program, ExecutableProgram::Effect(_))
                    && erased_initializer != member.initializer())
                .then_some(member.initializer()),
            },
            _ if member.binder().ty().outer_nominal().is_some() => {
                let location = allocate_heap(heap, HeapCell::Uninitialized)?;
                pending.push((location, member.initializer()));
                RecursiveMemberKind::Data { location }
            }
            _ => return Err(RuntimeFailure::UnexpectedRecursiveBinding),
        };
        members.push(RecursiveMemberTemplate {
            binder: member.binder().id(),
            kind,
        });
    }
    let environment = environment.extend_recursive(members)?;
    if let Some((_, initializer)) = pending.first().copied() {
        Ok(Transition::suspend(
            Control::Evaluate(initializer, environment.clone()),
            Frame::InitializeRecursive {
                pending: pending.into_boxed_slice(),
                next: 0,
                body: group.body(),
                environment,
            },
        ))
    } else {
        Ok(Transition::direct(Control::Evaluate(
            group.body(),
            environment,
        )))
    }
}

fn pure_expression(
    program: &ExecutableProgram,
    node: NodeId,
) -> Result<&PureExprKind, RuntimeFailure> {
    match program.node(node).ok_or(RuntimeFailure::MissingNode)? {
        ExecutableNode::Pure(expression) => Ok(&expression.kind),
        ExecutableNode::Effect(expression) => match &expression.kind {
            EffectExprKind::Pure(kind) => Ok(kind),
            EffectExprKind::Operation(_) => Err(RuntimeFailure::UnexpectedRecursiveBinding),
        },
    }
}

fn enter_binding(
    binding: &crate::core::binding::BindingNode,
    environment: Environment,
) -> Transition {
    Transition::suspend(
        Control::Evaluate(binding.initializer(), environment.clone()),
        Frame::Bind {
            binder: binding.binder().id(),
            body: binding.body(),
            environment,
        },
    )
}

fn enter_primitive(
    operation: crate::core::primitive::PrimitiveNode,
    environment: Environment,
) -> Transition {
    Transition::suspend(
        Control::Evaluate(operation.left(), environment.clone()),
        Frame::PrimitiveLeft {
            primitive: operation.primitive(),
            right: operation.right(),
            environment,
        },
    )
}

fn enter_application(
    application: crate::core::function::ApplicationNode,
    environment: Environment,
) -> Transition {
    Transition::suspend(
        Control::Evaluate(application.function(), environment.clone()),
        Frame::ApplyFunction {
            argument: application.argument(),
            caller_environment: environment,
        },
    )
}

fn dispatch_return(
    frame: Frame,
    value: Value,
    heap: &mut Vec<HeapCell>,
) -> Result<Transition, RuntimeFailure> {
    match frame {
        Frame::Bind {
            binder,
            body,
            environment,
        } => return_binding(binder, body, environment, value),
        Frame::PrimitiveLeft {
            primitive,
            right,
            environment,
        } => Ok(return_primitive_left(primitive, right, environment, value)),
        Frame::PrimitiveRight { primitive, left } => return_primitive_right(primitive, left, value),
        Frame::ApplyFunction {
            argument,
            caller_environment,
        } => return_application_function(argument, caller_environment, value),
        Frame::ApplyArgument { function } => return_application_argument(function, value, heap),
        Frame::Tuple {
            elements,
            next,
            values,
            environment,
        } => return_tuple(elements, next, values, environment, value, heap),
        Frame::Match { arms, environment } => return_match(arms, environment, value, heap),
        Frame::InitializeRecursive {
            pending,
            next,
            body,
            environment,
        } => return_recursive_initialization(pending, next, body, environment, value, heap),
        _ => Err(RuntimeFailure::InvalidControlState),
    }
}

fn return_tuple(
    elements: Box<[NodeId]>,
    next: usize,
    mut values: Vec<Value>,
    environment: Environment,
    value: Value,
    heap: &mut Vec<HeapCell>,
) -> Result<Transition, RuntimeFailure> {
    values.push(value);
    if let Some(element) = elements.get(next).copied() {
        Ok(Transition::suspend(
            Control::Evaluate(element, environment.clone()),
            Frame::Tuple {
                elements,
                next: next + 1,
                values,
                environment,
            },
        ))
    } else {
        let location = allocate_heap(heap, HeapCell::Tuple(values.into_boxed_slice()))?;
        Ok(Transition::direct(Control::Return(Value::Location(
            location,
        ))))
    }
}

fn return_match(
    arms: Box<[crate::core::data::CoreMatchArm]>,
    environment: Environment,
    value: Value,
    heap: &[HeapCell],
) -> Result<Transition, RuntimeFailure> {
    for arm in &arms {
        let mut bindings = Vec::new();
        if matches_pattern(arm.pattern(), &value, heap, &mut bindings)? {
            return Ok(Transition::direct(Control::Evaluate(
                arm.body(),
                environment.extend_many(bindings)?,
            )));
        }
    }
    Err(RuntimeFailure::ImpossibleMatch)
}

fn return_recursive_initialization(
    pending: Box<[(Location, NodeId)]>,
    next: usize,
    body: NodeId,
    environment: Environment,
    value: Value,
    heap: &mut [HeapCell],
) -> Result<Transition, RuntimeFailure> {
    let Value::Location(value_location) = value else {
        return Err(RuntimeFailure::UnexpectedRecursiveBinding);
    };
    let (slot, _) = pending
        .get(next)
        .copied()
        .ok_or(RuntimeFailure::InvalidControlState)?;
    let cell = heap.get_mut(slot).ok_or(RuntimeFailure::InvalidLocation)?;
    if !matches!(cell, HeapCell::Uninitialized) {
        return Err(RuntimeFailure::InvalidControlState);
    }
    *cell = HeapCell::Alias(value_location);
    let next = next + 1;
    if let Some((_, initializer)) = pending.get(next).copied() {
        Ok(Transition::suspend(
            Control::Evaluate(initializer, environment.clone()),
            Frame::InitializeRecursive {
                pending,
                next,
                body,
                environment,
            },
        ))
    } else {
        Ok(Transition::direct(Control::Evaluate(body, environment)))
    }
}

fn return_binding(
    binder: BinderId,
    body: NodeId,
    environment: Environment,
    value: Value,
) -> Result<Transition, RuntimeFailure> {
    Ok(Transition::direct(Control::Evaluate(
        body,
        environment.extend(binder, value)?,
    )))
}

fn return_primitive_left(
    primitive: Primitive,
    right: NodeId,
    environment: Environment,
    left: Value,
) -> Transition {
    Transition::suspend(
        Control::Evaluate(right, environment),
        Frame::PrimitiveRight { primitive, left },
    )
}

fn return_primitive_right(
    primitive: Primitive,
    left: Value,
    right: Value,
) -> Result<Transition, RuntimeFailure> {
    Ok(Transition::direct(Control::Return(apply_primitive(
        primitive, left, right,
    )?)))
}

fn return_application_function(
    argument: NodeId,
    caller_environment: Environment,
    function: Value,
) -> Result<Transition, RuntimeFailure> {
    if !matches!(
        function,
        Value::Function(_) | Value::ConstructorFunction(_) | Value::Intrinsic(_)
    ) {
        return Err(RuntimeFailure::UnexpectedFunctionValue);
    }
    Ok(Transition::suspend(
        Control::Evaluate(argument, caller_environment),
        Frame::ApplyArgument { function },
    ))
}

fn return_application_argument(
    function: Value,
    argument: Value,
    heap: &mut Vec<HeapCell>,
) -> Result<Transition, RuntimeFailure> {
    match function {
        Value::Function(closure) => Ok(Transition::direct(Control::Evaluate(
            closure.body,
            closure.environment.extend(closure.parameter, argument)?,
        ))),
        Value::ConstructorFunction(constructor) => {
            let location = allocate_heap(heap, HeapCell::Constructor(constructor, Some(argument)))?;
            Ok(Transition::direct(Control::Return(Value::Location(
                location,
            ))))
        }
        _ => Err(RuntimeFailure::UnexpectedFunctionValue),
    }
}

fn packed_storage_failure(requested: usize) -> RuntimeFailure {
    resource_failure(
        ResourceFailureCause::StorageReservationFailed,
        RuntimePhase::Evaluation,
        RuntimeResource::PackedBytes,
        Some(requested),
        None,
    )
}

fn packed_string(text: &str) -> Result<Arc<str>, RuntimeFailure> {
    let mut output = String::new();
    output
        .try_reserve_exact(text.len())
        .map_err(|_| packed_storage_failure(text.len()))?;
    output.push_str(text);
    Ok(Arc::from(output))
}

fn packed_bytes(bytes: &[u8], append: Option<u8>) -> Result<Arc<[u8]>, RuntimeFailure> {
    let len = bytes
        .len()
        .checked_add(usize::from(append.is_some()))
        .ok_or_else(|| packed_storage_failure(usize::MAX))?;
    let mut output = Vec::new();
    output
        .try_reserve_exact(len)
        .map_err(|_| packed_storage_failure(len))?;
    output.extend_from_slice(bytes);
    if let Some(byte) = append {
        output.push(byte);
    }
    Ok(Arc::from(output))
}

fn packed_tuple_location(
    heap: &[HeapCell],
    mut location: Location,
    work: &mut TypeWorkBudget,
) -> Result<Location, RuntimeFailure> {
    for _ in 0..=heap.len() {
        charge_runtime_work(work, 1, RuntimePhase::Evaluation)?;
        match heap.get(location) {
            Some(HeapCell::Alias(next)) => location = *next,
            Some(HeapCell::Uninitialized) => return Err(RuntimeFailure::UninitializedLocation),
            Some(_) => return Ok(location),
            None => return Err(RuntimeFailure::InvalidLocation),
        }
    }
    Err(RuntimeFailure::AliasLoop)
}

fn apply_intrinsic(
    intrinsic: crate::core::packed::IntrinsicNode,
    argument: Value,
    heap: &mut Vec<HeapCell>,
    work: &mut TypeWorkBudget,
) -> Result<Value, RuntimeFailure> {
    use crate::core::packed::Intrinsic;
    let operation = intrinsic.operation();
    if !intrinsic.authentic_module() {
        return Err(RuntimeFailure::InvalidControlState);
    }
    let result = match (operation, argument) {
        (Intrinsic::BytesAt { found, invalid }, Value::Location(location)) => {
            return apply_byte_lookup(found, invalid, location, heap, work);
        }
        (Intrinsic::AddressNull, Value::Unit) => {
            Value::Address(super::value::Address::new(core::ptr::null_mut()))
        }
        (Intrinsic::AddressIsNull, Value::Address(address)) => {
            Value::Boolean(address.as_ptr().is_null())
        }
        (Intrinsic::AddressEqual, Value::Location(location)) => {
            let location = packed_tuple_location(heap, location, work)?;
            let Some(HeapCell::Tuple(fields)) = heap.get(location) else {
                return Err(RuntimeFailure::InvalidControlState);
            };
            let [Value::Address(left), Value::Address(right)] = fields.as_ref() else {
                return Err(RuntimeFailure::InvalidControlState);
            };
            Value::Boolean(left.as_ptr() == right.as_ptr())
        }
        (Intrinsic::BytesEmpty, Value::Unit) => Value::Bytes(Arc::from([])),
        (Intrinsic::BytesLength, bytes) if bytes.bytes().is_some() => Value::Integer(
            crate::integer::Integer::from_usize(bytes.bytes().expect("guarded byte value").len()),
        ),
        (Intrinsic::StringByteLength, Value::String(text)) => {
            Value::Integer(crate::integer::Integer::from_usize(text.len()))
        }
        (Intrinsic::StringToUtf8, Value::String(text)) => {
            charge_runtime_work(work, text.len(), RuntimePhase::Evaluation)?;
            Value::Bytes(packed_bytes(text.as_bytes(), None)?)
        }
        (Intrinsic::StringFromUtf8 { decoded, invalid }, bytes) if bytes.bytes().is_some() => {
            let bytes = bytes.bytes().expect("guarded byte value");
            charge_runtime_work(work, bytes.len(), RuntimePhase::Evaluation)?;
            let (constructor, payload) = match std::str::from_utf8(bytes) {
                Ok(text) => (decoded, Some(Value::String(packed_string(text)?))),
                Err(_) => (invalid, None),
            };
            Value::Location(allocate_heap(
                heap,
                HeapCell::Constructor(constructor, payload),
            )?)
        }
        (
            operation @ (Intrinsic::BytesAppendByte { .. }
            | Intrinsic::BytesEqual
            | Intrinsic::StringEqual),
            Value::Location(location),
        ) => {
            let location = packed_tuple_location(heap, location, work)?;
            let Some(HeapCell::Tuple(fields)) = heap.get(location) else {
                return Err(RuntimeFailure::InvalidControlState);
            };
            if fields.len() != 2 {
                return Err(RuntimeFailure::InvalidControlState);
            }
            match (operation, &fields[0], &fields[1]) {
                (
                    Intrinsic::BytesAppendByte { appended, invalid },
                    bytes,
                    Value::Integer(integer),
                ) if bytes.bytes().is_some() => {
                    let bytes = bytes.bytes().expect("guarded byte value");
                    let byte = integer.to_i64().and_then(|value| u8::try_from(value).ok());
                    let (constructor, payload) = if let Some(byte) = byte {
                        let requested = bytes
                            .len()
                            .checked_add(1)
                            .ok_or_else(|| packed_storage_failure(usize::MAX))?;
                        charge_runtime_work(work, requested, RuntimePhase::Evaluation)?;
                        (
                            appended,
                            Some(Value::Bytes(packed_bytes(bytes, Some(byte))?)),
                        )
                    } else {
                        (invalid, None)
                    };
                    Value::Location(allocate_heap(
                        heap,
                        HeapCell::Constructor(constructor, payload),
                    )?)
                }
                (Intrinsic::BytesEqual, left, right)
                    if left.bytes().is_some() && right.bytes().is_some() =>
                {
                    let left = left.bytes().expect("guarded byte value");
                    let right = right.bytes().expect("guarded byte value");
                    charge_runtime_work(
                        work,
                        left.len().min(right.len()),
                        RuntimePhase::Evaluation,
                    )?;
                    Value::Boolean(left == right)
                }
                (Intrinsic::StringEqual, Value::String(left), Value::String(right)) => {
                    charge_runtime_work(
                        work,
                        left.len().min(right.len()),
                        RuntimePhase::Evaluation,
                    )?;
                    Value::Boolean(left == right)
                }
                _ => return Err(RuntimeFailure::InvalidControlState),
            }
        }
        _ => return Err(RuntimeFailure::InvalidControlState),
    };
    Ok(result)
}

// Result preparation stays outside the shared evaluator dispatch frame.
#[inline(never)]
fn apply_byte_lookup(
    found: crate::types::ConstructorId,
    invalid: crate::types::ConstructorId,
    location: Location,
    heap: &mut Vec<HeapCell>,
    work: &mut TypeWorkBudget,
) -> Result<Value, RuntimeFailure> {
    let location = packed_tuple_location(heap, location, work)?;
    let index = {
        let Some(HeapCell::Tuple(fields)) = heap.get(location) else {
            return Err(RuntimeFailure::InvalidControlState);
        };
        let [bytes, Value::Integer(index)] = fields.as_ref() else {
            return Err(RuntimeFailure::InvalidControlState);
        };
        let bytes = bytes.bytes().ok_or(RuntimeFailure::InvalidControlState)?;
        let magnitude = usize::try_from(index.magnitude_byte_length())
            .map_err(|_| packed_storage_failure(usize::MAX))?;
        let requested = magnitude
            .checked_add(3)
            .ok_or_else(|| packed_storage_failure(usize::MAX))?;
        // Index inspection, length/lookup and the complete ordinary result are
        // paid before inspecting a byte. No native permission is involved.
        charge_runtime_work(work, requested, RuntimePhase::Evaluation)?;
        index.to_usize().filter(|index| *index < bytes.len())
    };
    heap.len()
        .checked_add(1)
        .ok_or(RuntimeFailure::HeapCapacity)?;
    heap.try_reserve(1).map_err(|_| {
        resource_failure(
            ResourceFailureCause::StorageReservationFailed,
            RuntimePhase::Evaluation,
            RuntimeResource::ResultHeapCells,
            Some(1),
            None,
        )
    })?;
    let payload = if let Some(index) = index {
        let Some(HeapCell::Tuple(fields)) = heap.get(location) else {
            return Err(RuntimeFailure::InvalidControlState);
        };
        let byte = fields[0]
            .bytes()
            .and_then(|bytes| bytes.get(index))
            .copied()
            .ok_or(RuntimeFailure::InvalidControlState)?;
        Some(Value::Integer(crate::integer::Integer::from_u64(
            u64::from(byte),
        )))
    } else {
        None
    };
    let result = heap.len();
    heap.push(HeapCell::Constructor(
        if payload.is_some() { found } else { invalid },
        payload,
    ));
    Ok(Value::Location(result))
}

#[inline(never)]
/// A pure scan creates only an ordinary result. No prepared-input token,
/// pointer or native permission can be derived from this preflight.

fn allocate_heap(heap: &mut Vec<HeapCell>, cell: HeapCell) -> Result<Location, RuntimeFailure> {
    admit_heap_cell(heap.len())?;
    let location = heap.len();
    heap.push(cell);
    Ok(location)
}

fn admit_heap_cell(len: usize) -> Result<(), RuntimeFailure> {
    if len == usize::MAX {
        return Err(legacy_failure(
            RuntimeFailure::HeapCapacity,
            ResourceFailureCause::ConfiguredCapacity,
            RuntimePhase::Evaluation,
            RuntimeResource::HeapCells,
            Some(1),
            Some(0),
        ));
    }
    Ok(())
}

fn resolve_location(heap: &[HeapCell], start: Location) -> Result<Location, RuntimeFailure> {
    let mut current = start;
    let mut seen = std::collections::HashSet::new();
    loop {
        if !seen.insert(current) {
            return Err(RuntimeFailure::AliasLoop);
        }
        match heap.get(current) {
            Some(HeapCell::Alias(next)) => current = *next,
            Some(HeapCell::Uninitialized) => return Err(RuntimeFailure::UninitializedLocation),
            Some(_) => return Ok(current),
            None => return Err(RuntimeFailure::InvalidLocation),
        }
    }
}

fn resolve_location_with_work(
    heap: &[HeapCell],
    mut location: Location,
    work: &mut TypeWorkBudget,
) -> Result<Location, RuntimeFailure> {
    // A terminating chain visits at most heap.len() cells. This bound detects
    // cycles without allocating a visited set while native access is prepared.
    for _ in 0..=heap.len() {
        charge_runtime_work(work, 1, RuntimePhase::Access)?;
        match heap.get(location) {
            Some(HeapCell::Alias(next)) => location = *next,
            Some(HeapCell::Uninitialized) => return Err(RuntimeFailure::UninitializedLocation),
            Some(_) => return Ok(location),
            None => return Err(RuntimeFailure::InvalidLocation),
        }
    }
    Err(RuntimeFailure::AliasLoop)
}

fn matches_pattern(
    pattern: &CorePattern,
    value: &Value,
    heap: &[HeapCell],
    bindings: &mut Vec<(BinderId, Value)>,
) -> Result<bool, RuntimeFailure> {
    matches_pattern_with_work(pattern, value, heap, bindings, None)
}

fn matches_pattern_with_work(
    pattern: &CorePattern,
    value: &Value,
    heap: &[HeapCell],
    bindings: &mut Vec<(BinderId, Value)>,
    mut meter: Option<(&mut TypeWorkBudget, RuntimePhase)>,
) -> Result<bool, RuntimeFailure> {
    let mut work = Vec::new();
    work.try_reserve(1)
        .map_err(|_| RuntimeFailure::ResourceCapacity)?;
    work.push((pattern, value.clone()));
    while let Some((pattern, value)) = work.pop() {
        if let Some((budget, phase)) = &mut meter {
            charge_effect_work(budget, 1, *phase)?;
        }
        match &pattern.kind {
            CorePatternKind::Binder(binder) => {
                bindings
                    .try_reserve(1)
                    .map_err(|_| RuntimeFailure::ResourceCapacity)?;
                bindings.push((binder.id(), value));
            }
            CorePatternKind::Wildcard => {}
            CorePatternKind::Boolean(expected) => {
                if !matches!(value, Value::Boolean(found) if found == *expected) {
                    return Ok(false);
                }
            }
            CorePatternKind::Unit => {
                if !matches!(value, Value::Unit) {
                    return Ok(false);
                }
            }
            CorePatternKind::Tuple(patterns) => {
                let Value::Location(location) = value else {
                    return Ok(false);
                };
                let location = if let Some((budget, _)) = &mut meter {
                    resolve_location_with_work(heap, location, budget)?
                } else {
                    resolve_location(heap, location)?
                };
                let Some(HeapCell::Tuple(elements)) = heap.get(location) else {
                    return Ok(false);
                };
                if patterns.len() != elements.len() {
                    return Ok(false);
                }
                if let Some((budget, phase)) = &mut meter {
                    charge_effect_work(budget, patterns.len(), *phase)?;
                }
                work.try_reserve(patterns.len())
                    .map_err(|_| RuntimeFailure::ResourceCapacity)?;
                work.extend(
                    patterns
                        .iter()
                        .zip(elements.iter())
                        .rev()
                        .map(|(pattern, value)| (pattern, value.clone())),
                );
            }
            CorePatternKind::Constructor {
                constructor,
                payload,
            } => {
                let Value::Location(location) = value else {
                    return Ok(false);
                };
                let location = if let Some((budget, _)) = &mut meter {
                    resolve_location_with_work(heap, location, budget)?
                } else {
                    resolve_location(heap, location)?
                };
                let Some(HeapCell::Constructor(found, found_payload)) = heap.get(location) else {
                    return Ok(false);
                };
                if found != constructor {
                    return Ok(false);
                }
                match (payload.as_deref(), found_payload) {
                    (None, None) => {}
                    (Some(pattern), Some(value)) => {
                        work.try_reserve(1)
                            .map_err(|_| RuntimeFailure::ResourceCapacity)?;
                        work.push((pattern, value.clone()));
                    }
                    _ => return Ok(false),
                }
            }
        }
    }
    Ok(true)
}

/// Evaluates one independently validated pure Core program.
///
/// # Errors
///
/// Returns a structured runtime failure if a validated-input assumption is
/// violated or a represented runtime resource is exhausted.
pub fn evaluate(program: &ValidatedProgram) -> Result<Evaluation, RuntimeFailure> {
    Machine::new(program).run()
}

/// Evaluates one independently validated effect Core program.
pub fn evaluate_effect(program: &ValidatedEffectProgram) -> Result<Evaluation, RuntimeFailure> {
    Machine::new_effect(program).run()
}

/// Evaluates only a program whose source-native bindings were admitted before
/// Ash execution. This borrows the immutable original binding table throughout.
///
/// # Errors
/// Native conversion, work/storage admission and existing evaluation failures
/// terminate without retrying an already returned external call.
pub fn evaluate_effect_with_source_native_program(
    admitted: crate::foreign::source_bindings::AdmittedSourceNativeProgram<'_, '_>,
) -> Result<Evaluation, RuntimeFailure> {
    let (program, bindings) = admitted.into_parts();
    let mut machine = Machine::new_effect(program);
    machine.source_bindings = Some(bindings);
    machine.run()
}

/// Evaluates validated Effect Core using identity-bound executable host bindings.
///
/// Retained native owners stay in the borrowed host runtime after source return.
///
/// # Errors
/// Rejects changed manifest facts, absent bindings, malformed codecs or runtime
/// ownership failures before the corresponding native acquisition.

fn apply_primitive(
    primitive: Primitive,
    left: Value,
    right: Value,
) -> Result<Value, RuntimeFailure> {
    let (Value::Integer(left), Value::Integer(right)) = (left, right) else {
        return Err(RuntimeFailure::UnexpectedPrimitiveValue);
    };
    Ok(match primitive {
        Primitive::Add => Value::Integer(&left + &right),
        Primitive::Multiply => Value::Integer(&left * &right),
        Primitive::Equal => Value::Boolean(left == right),
    })
}

#[cfg(test)]
mod tests {
    pub(super) fn is_work_exhaustion(failure: super::RuntimeFailure) -> bool {
        use super::{ResourceFailureCause, RuntimeFailure, RuntimeResource};
        matches!(failure, RuntimeFailure::Report(report)
            if report.primary.reason_code() == "runtime.environment-capacity"
            && report.teardown.is_none()
            && report.primary.resource().is_some_and(|details|
                details.cause == ResourceFailureCause::WorkBudgetExhausted
                && details.resource == RuntimeResource::WorkUnits
                && details.available.is_some()))
    }

    fn is_configured_capacity(
        failure: super::RuntimeFailure,
        reason: super::RuntimeFailure,
        resource: super::RuntimeResource,
    ) -> bool {
        use super::{ResourceFailureCause, RuntimeFailure};
        matches!(failure, RuntimeFailure::Report(report)
            if report.primary.reason_code() == reason.reason_code()
            && report.teardown.is_none()
            && report.primary.resource().is_some_and(|details|
                details.cause == ResourceFailureCause::ConfiguredCapacity
                && details.resource == resource))
    }

    use std::sync::{Arc, Barrier};

    use super::*;
    use crate::{
        core::{
            CoreBuilder, EffectCoreBuilder, NewtypeConversionDirection,
            binding::BindingNode,
            function::ApplicationNode,
            function::FunctionNode,
            literal::BooleanNode,
            literal::IntegerNode,
            literal::UnitNode,
            primitive::PrimitiveNode,
            type_ops::{TypeAbstractionNode, TypeApplicationNode},
            validate, validate_effect, validate_effect_modules,
            variable::VariableNode,
        },
        elaborate::{EffectElaborator, check_module, link_modules},
        evidence_validation::validate_interface_evidence,
        integer::Integer,
        module::{ModuleRoots, load_module_graph},
        resolve::resolve_module,
        resolved::{
            ResolvedConstructor, ResolvedNominalType, ResolvedRegistry, ResolvedTypeProvenance,
            ResolvedTypeProvenanceNode,
        },
        source::{ByteRange, Origin, SourceFile},
        types::{ConstructorId, NominalTypeId, Type, TypeVariableId},
    };

    #[test]
    fn ordinary_byte_lookup_admits_the_whole_result_before_reading() {
        let module = crate::module::ModuleId::from(
            SourceFile::new("byte-lookup-mechanism", "").unwrap().id(),
        );
        let owner = crate::types::NominalTypeId::new(module, 1);
        let found = crate::types::ConstructorId::new(owner, 0);
        let invalid = crate::types::ConstructorId::new(owner, 1);
        let inputs = [
            crate::integer::Integer::from_i64(-1),
            crate::integer::Integer::from_usize(0),
            crate::integer::Integer::from_usize(1),
            crate::integer::Integer::from_usize(2),
            crate::integer::Integer::parse_decimal("999999999999999999999999999999999999999")
                .unwrap(),
        ];
        for bytes in [&[][..], &[0, 255][..]] {
            for index in &inputs {
                let heap = || {
                    vec![HeapCell::Tuple(Box::new([
                        Value::Bytes(Arc::from(bytes)),
                        Value::Integer(index.clone()),
                    ]))]
                };
                let expected = index.to_usize().and_then(|index| bytes.get(index)).copied();
                let mut measured = TypeWorkBudget::default();
                apply_byte_lookup(found, invalid, 0, &mut heap(), &mut measured).unwrap();
                let required = measured.used();
                for prefix in [0, 17] {
                    let mut short = TypeWorkBudget::with_limit(prefix + required - 1);
                    short.charge(prefix).unwrap();
                    let mut refused = heap();
                    assert!(matches!(
                        apply_byte_lookup(found, invalid, 0, &mut refused, &mut short),
                        Err(RuntimeFailure::Report(_))
                    ));
                    assert_eq!(
                        refused.len(),
                        1,
                        "terminal refusal publishes no partial ordinary result"
                    );
                    for _ in 0..2 {
                        let mut exact = TypeWorkBudget::with_limit(prefix + required);
                        exact.charge(prefix).unwrap();
                        let mut heap = heap();
                        let Value::Location(result) =
                            apply_byte_lookup(found, invalid, 0, &mut heap, &mut exact).unwrap()
                        else {
                            panic!("ordinary result");
                        };
                        let HeapCell::Constructor(constructor, payload) = &heap[result] else {
                            panic!("ordinary constructor");
                        };
                        assert_eq!(
                            *constructor,
                            if expected.is_some() { found } else { invalid }
                        );
                        assert_eq!(
                            payload.as_ref().map(|value| match value {
                                Value::Integer(value) => value.to_i64().unwrap(),
                                _ => panic!("copied integer"),
                            }),
                            expected.map(i64::from)
                        );
                        assert_eq!(heap.len(), 2);
                        assert_eq!(exact.used(), prefix + required);
                    }
                }
            }
        }
    }

    #[test]
    fn packed_literal_copy_reports_low_work_without_panicking() {
        let source = SourceFile::new("packed-limit.ash", "()").unwrap();
        let origin = Origin::Source(source.span(ByteRange::new(0, 2).unwrap()).unwrap());
        let mut builder = CoreBuilder::new();
        let root = builder
            .string(b"packed".as_slice(), Type::String, origin)
            .unwrap();
        let program = validate(builder.finish(root).unwrap(), &[&source]).unwrap();
        let mut machine = Machine::new(&program);
        machine.instantiation_work = TypeWorkBudget::with_limit(0);
        let RuntimeFailure::Report(report) = machine.run().unwrap_err() else {
            panic!("structured resource report")
        };
        assert_eq!(
            report.primary.reason_code(),
            "runtime.work-budget-exhausted"
        );
        let resource = report.primary.resource().unwrap();
        assert_eq!(resource.cause, ResourceFailureCause::WorkBudgetExhausted);
        assert_eq!(resource.phase, RuntimePhase::Evaluation);
        assert_eq!(resource.resource, RuntimeResource::WorkUnits);
        assert_eq!(resource.requested, Some(6));
        assert_eq!(resource.available, Some(0));
    }

    fn sequential_effect_program() -> ValidatedEffectProgram {
        effect_program(concat!(
            "effect Ask {\nask : Int -> Int\n}\n\n",
            "main : Unit -> Int\nmain () = handle ({\n",
            "let first = perform Ask.ask 1\nperform Ask.ask first\n",
            "}) with Ask {\nask value => resume (value + 1)\n}\n",
        ))
    }

    #[test]
    fn generic_execution_instantiation_work_is_exact_and_retryable() {
        let program = effect_program(concat!(
            "effect E<T> {\nask : Unit -> Int\n}\n",
            "helper<T> : T -> Int ! {E<T>}\nhelper ignored = perform E<T>.ask ()\n",
            "main : Unit -> Int\nmain () = handle (helper 0) with E<Int> {\nask ignored => resume 42\n}\n",
        ));
        // Application: 3. Request argument: 2 slots + substitution root + Int.
        // Exact source-native registry lookup (absent for this request): 1.
        // Handler search: 1. Handler argument: 2 slots + Int.
        // Exact comparison: argument tag + Int.
        // Measure this exact program under the current paid capture/index
        // implementation; a predecessor constant is not its exact cut.
        let measured = Machine::new_effect(&program).run().unwrap();
        assert_eq!(measured.value.to_string(), "42");
        let required = measured.runtime_work;
        assert!(
            required >= 14,
            "all original request/instantiation work remains paid"
        );
        let mut short = Machine::new_effect(&program);
        short.instantiation_work = TypeWorkBudget::with_limit(required - 1);
        assert!(is_work_exhaustion(short.run().unwrap_err()));
        for _ in 0..2 {
            let mut exact = Machine::new_effect(&program);
            exact.instantiation_work = TypeWorkBudget::with_limit(required);
            let result = exact.run().unwrap();
            assert_eq!(result.value.to_string(), "42");
            assert_eq!(result.runtime_work, required);
        }
    }

    #[test]
    fn polymorphic_environment_edges_are_disposed_iteratively() {
        let program = sequential_effect_program();
        std::thread::Builder::new()
            .stack_size(256 * 1024)
            .spawn(move || {
                let mut environment = Environment::new();
                for index in 0..32_000 {
                    let captured = environment.clone();
                    environment = environment
                        .extend(
                            BinderId::new(index),
                            Value::Polymorphic {
                                abstraction: program.root(),
                                environment: captured,
                            },
                        )
                        .unwrap();
                }
                drop(environment);
            })
            .unwrap()
            .join()
            .unwrap();
    }

    pub(super) fn effect_program(text: &str) -> ValidatedEffectProgram {
        let path = std::env::temp_dir().join(format!(
            "ash-machine-effect-budget-{}-{}.ash",
            std::process::id(),
            SourceFile::new("effect-budget-identity", "")
                .expect("source identity")
                .id()
                .value()
        ));
        std::fs::write(&path, text).expect("fixture should be writable");
        let graph = load_module_graph(&path, &ModuleRoots::empty()).expect("fixture should load");
        let mut checked: Vec<crate::resolved::CheckedModule> = Vec::new();
        for module in graph.modules() {
            let dependencies = module
                .dependencies()
                .iter()
                .map(|edge| {
                    crate::resolve::DependencyExports::new(
                        edge,
                        checked
                            .iter()
                            .find(|module| module.module() == edge.target())
                            .unwrap()
                            .exports(),
                    )
                    .unwrap()
                })
                .collect::<Vec<_>>();
            let resolved = resolve_module(module, &dependencies).unwrap();
            checked.push(check_module(resolved).unwrap());
        }
        let linked = link_modules(checked, graph.entry()).expect("fixture should link");
        let linked = validate_interface_evidence(linked).expect("evidence should authenticate");
        let mut elaborator =
            EffectElaborator::for_module_program(&linked).expect("builder should start");
        let typed = elaborator
            .synthesize_effect_module_program(&linked)
            .expect("fixture should lower");
        let unchecked = elaborator.finish(typed.node).expect("Core should finish");
        let sources = graph
            .modules()
            .iter()
            .map(|module| module.source())
            .collect::<Vec<_>>();
        let module_sources = graph
            .modules()
            .iter()
            .map(|module| (module.id(), module.source().id()))
            .collect::<Vec<_>>();
        let program = validate_effect_modules(unchecked, &sources, &module_sources)
            .expect("Effect Core should validate");
        let _ = std::fs::remove_file(path);
        program
    }

    fn resource_program() -> ValidatedEffectProgram {
        effect_program(
            "import @builtin.cell as Cell\nmain : Unit -> Int\nmain () = resource cell<R> c = 41 {\nCell.read c\n}\n",
        )
    }

    pub(super) fn resource_node(program: &ValidatedEffectProgram) -> NodeId {
        let mut pending = vec![program.root()];
        while let Some(id) = pending.pop() {
            let kind = &program.node(id).unwrap().kind;
            if matches!(
                kind,
                EffectExprKind::Operation(EffectOperation::Resource(_))
            ) {
                return id;
            }
            pending.extend((0..kind.child_count()).filter_map(|index| kind.child_at(index)));
        }
        panic!("resource fixture has an acquisition")
    }

    pub(super) fn integer(value: &str) -> Value {
        Value::Integer(Integer::parse_decimal(value).unwrap())
    }

    fn cleanup_fixture() -> (
        ValidatedEffectProgram,
        crate::core::effect::CleanupScopeNode,
        Environment,
    ) {
        let program =
            effect_program("main : Unit -> Int\nmain () = cleanup fn(ignored) {\n()\n} {\n42\n}\n");
        let mut pending = vec![program.root()];
        let mut scope = None;
        let mut bindings = Vec::new();
        while let Some(node) = pending.pop() {
            let expression = program.node(node).unwrap();
            match &expression.kind {
                EffectExprKind::Operation(EffectOperation::Cleanup(found)) => scope = Some(*found),
                EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Bind(binding))) => {
                    bindings.push((binding.binder().id(), binding.initializer()))
                }
                _ => {}
            }
            pending.extend(
                (0..expression.kind.child_count())
                    .filter_map(|index| expression.kind.child_at(index)),
            );
        }
        let scope = scope.unwrap();
        let initializer = bindings
            .into_iter()
            .find(|(binder, _)| *binder == scope.callback)
            .unwrap()
            .1;
        let executable = ExecutableProgram::Effect(program.shared());
        let transition = dispatch_entry(
            &executable,
            initializer,
            Environment::new(),
            &mut Vec::new(),
        )
        .unwrap();
        let Control::Return(callback) = transition.control else {
            panic!("ordinary callback")
        };
        let environment = Environment::new().extend(scope.callback, callback).unwrap();
        (program, scope, environment)
    }

    #[test]
    fn cleanup_preflight_charges_exactly_before_publication_and_reuses_capacity() {
        let (program, scope, environment) = cleanup_fixture();
        let exact = 2 + environment.len();
        for allowance in [exact - 1, exact, exact] {
            let mut machine = Machine::new_effect(&program);
            machine.instantiation_work = TypeWorkBudget::with_limit(allowance);
            let result = machine.acquire_cleanup(scope, environment.clone());
            if allowance < exact {
                assert!(is_work_exhaustion(result.unwrap_err()));
                assert!(machine.frames.is_empty());
                assert_eq!(machine.live_cleanups, 0);
            } else {
                result.unwrap();
                assert_eq!(machine.instantiation_work.used(), exact);
                assert_eq!(machine.live_cleanups, 1);
            }
        }
        let mut machine = Machine::new_effect(&program);
        machine.cleanup_limit = 1;
        for _ in 0..3 {
            machine.acquire_cleanup(scope, environment.clone()).unwrap();
            assert!(is_configured_capacity(
                machine
                    .acquire_cleanup(scope, environment.clone())
                    .unwrap_err(),
                RuntimeFailure::ResourceCapacity,
                RuntimeResource::CleanupOwners
            ));
            assert_eq!(machine.frames.len(), 1);
            let owner = machine.frames.pop().unwrap();
            machine.return_from(owner, integer("42")).unwrap();
            assert_eq!(
                machine.live_cleanups, 1,
                "running completion retains capacity"
            );
            let completion = machine.frames.pop().unwrap();
            machine.return_from(completion, Value::Unit).unwrap();
            assert_eq!(machine.live_cleanups, 0);
            assert!(
                matches!(&machine.control, Some(Control::Return(Value::Integer(value))) if value.to_string() == "42")
            );
        }
    }

    #[test]
    fn owned_discard_preflight_is_exact_atomic_and_fresh_retryable() {
        let (program, scope, environment) = cleanup_fixture();
        let handler = HandlerId::new(0);
        let owner = ResumeId::new(0);
        let prepared = || {
            let mut machine = Machine::new_effect(&program);
            machine.acquire_cleanup(scope, environment.clone()).unwrap();
            let nested = machine.capture_from(0).unwrap();
            machine.frames.push(Frame::ClauseBoundary {
                registration: None,
                handler: HandlerId::new(1),
                owner: ResumeId::new(1),
                continuation: Some(nested),
            });
            machine.acquire_cleanup(scope, environment.clone()).unwrap();
            let captured = machine.capture_from(0).unwrap();
            machine.frames.push(Frame::ClauseBoundary {
                registration: None,
                handler,
                owner,
                continuation: Some(captured),
            });
            machine.effect_trace = Some(Vec::new());
            machine.control = Some(Control::Return(Value::Unit));
            machine.instantiation_work = TypeWorkBudget::unbounded();
            machine
        };
        let mut measured = prepared();
        measured.discard(handler, owner).unwrap();
        let exact = measured.instantiation_work.used();
        assert!(exact > 0);
        for allowance in [exact - 1, exact, exact] {
            let mut machine = prepared();
            machine.instantiation_work = TypeWorkBudget::with_limit(allowance);
            let result = machine.discard(handler, owner);
            assert_eq!(machine.live_cleanups, 2);
            if allowance < exact {
                assert!(is_work_exhaustion(result.unwrap_err()));
                assert_eq!(machine.captured_cells, 3);
                assert!(matches!(
                    machine.frames.as_slice(),
                    [Frame::ClauseBoundary {
                        continuation: Some(_),
                        ..
                    }]
                ));
                assert!(machine.effect_trace.as_ref().unwrap().is_empty());
                assert!(matches!(
                    machine.control,
                    Some(Control::Return(Value::Unit))
                ));
                assert!(is_work_exhaustion(
                    machine.discard(handler, owner).unwrap_err()
                ));
                assert_eq!(machine.captured_cells, 3);
            } else {
                result.unwrap();
                assert_eq!(machine.instantiation_work.used(), exact);
                assert_eq!(machine.captured_cells, 0);
                assert!(matches!(
                    machine.frames.as_slice(),
                    [
                        Frame::ClauseBoundary {
                            continuation: None,
                            ..
                        },
                        Frame::CloseCompletion,
                        Frame::CleanupBoundary { .. },
                        Frame::CleanupBoundary { .. }
                    ]
                ));
                machine.instantiation_work = TypeWorkBudget::unbounded();
                assert_eq!(machine.run().unwrap().value.to_string(), "()");
            }
        }
    }

    #[test]
    fn owned_capture_and_running_action_share_cleanup_capacity_until_close() {
        let (program, scope, environment) = cleanup_fixture();
        let mut machine = Machine::new_effect(&program);
        machine.cleanup_limit = 1;
        for _ in 0..3 {
            machine.acquire_cleanup(scope, environment.clone()).unwrap();
            let captured = machine.capture_from(machine.frames.len() - 1).unwrap();
            assert!(is_configured_capacity(
                machine
                    .acquire_cleanup(scope, environment.clone())
                    .unwrap_err(),
                RuntimeFailure::ResourceCapacity,
                RuntimeResource::CleanupOwners
            ));
            machine.frames.push(Frame::ClauseBoundary {
                registration: None,
                handler: HandlerId::new(0),
                owner: ResumeId::new(0),
                continuation: Some(captured),
            });
            machine
                .discard(HandlerId::new(0), ResumeId::new(0))
                .unwrap();
            assert!(is_configured_capacity(
                machine
                    .acquire_cleanup(scope, environment.clone())
                    .unwrap_err(),
                RuntimeFailure::ResourceCapacity,
                RuntimeResource::CleanupOwners
            ));
            let armed = machine.frames.pop().unwrap();
            machine.return_from(armed, Value::Unit).unwrap();
            assert!(is_configured_capacity(
                machine
                    .acquire_cleanup(scope, environment.clone())
                    .unwrap_err(),
                RuntimeFailure::ResourceCapacity,
                RuntimeResource::CleanupOwners
            ));
            let running = machine.frames.pop().unwrap();
            machine.return_from(running, Value::Unit).unwrap();
            assert_eq!(machine.live_cleanups, 0);
            assert_eq!(machine.captured_cells, 0);
            let driver = machine.frames.pop().unwrap();
            machine.return_from(driver, Value::Unit).unwrap();
            let clause = machine.frames.pop().unwrap();
            machine.return_from(clause, Value::Unit).unwrap();
        }
    }

    #[test]
    fn cleanup_start_has_an_exact_charge_and_failure_does_not_start_an_action() {
        let (program, scope, environment) = cleanup_fixture();
        for allowance in [1, 2, 2] {
            let mut machine = Machine::new_effect(&program);
            machine.acquire_cleanup(scope, environment.clone()).unwrap();
            machine.instantiation_work = TypeWorkBudget::with_limit(allowance);
            let owner = machine.frames.pop().unwrap();
            let result = machine.return_from(owner, integer("42"));
            assert_eq!(machine.live_cleanups, 1);
            if allowance == 1 {
                assert!(is_work_exhaustion(result.unwrap_err()));
                assert!(machine.frames.is_empty());
                assert!(
                    !matches!(machine.control, Some(Control::Evaluate(node, _)) if node == scope.action)
                );
            } else {
                result.unwrap();
                assert_eq!(machine.instantiation_work.used(), 2);
                assert!(matches!(
                    machine.frames.as_slice(),
                    [Frame::CleanupCompletion { .. }]
                ));
            }
        }
    }

    #[test]
    fn cleanup_partial_action_and_completed_inner_action_are_not_replayed_on_failure() {
        let program = effect_program(
            "import @builtin.cell as Cell\nmain : Unit -> Int\nmain () = resource cell<R> trace = 0 {\nlet result = cleanup fn(ignored) {\nlet outer_started = 7003\nCell.write (trace, 1)\n} {\nlet result = cleanup fn(ignored) {\nlet written = Cell.write (trace, 2)\nlet first_write_completed = 7001\nCell.write (trace, 3)\n} {\n42\n}\nlet inner_completed = 7002\nresult\n}\nCell.read trace\n}\n",
        );
        let observed = Arc::new(std::sync::Mutex::new(Vec::new()));
        let mut measured = Machine::new_effect(&program);
        measured.work_trace = Some(Arc::clone(&observed));
        assert_eq!(measured.run().unwrap().value.to_string(), "1");
        let trace = observed.lock().unwrap();
        let marker = |value: &str| {
            trace
                .iter()
                .copied()
                .find(|(node, _)| {
                    matches!(&program.node(*node).unwrap().kind,
                    EffectExprKind::Pure(PureExprKind::Value(PureValue::Integer(integer)))
                        if integer.value().to_string() == value)
                })
                .unwrap()
        };
        let first_write = marker("7001");
        let inner_done = marker("7002");
        let outer_started = marker("7003");
        for (stop, completed_inner) in [(first_write, false), (inner_done, true)] {
            for _ in 0..2 {
                let observed = Arc::new(std::sync::Mutex::new(Vec::new()));
                let mut failure = Machine::new_effect(&program);
                failure.work_trace = Some(Arc::clone(&observed));
                failure.instantiation_work = TypeWorkBudget::with_limit(stop.1);
                assert!(is_work_exhaustion(failure.run().unwrap_err()));
                let trace = observed.lock().unwrap();
                let visits = |marker| trace.iter().filter(|(node, _)| *node == marker).count();
                // These strict markers run only after the preceding cell
                // write or inner action returned, not merely on request entry.
                assert_eq!(visits(first_write.0), 1);
                assert_eq!(visits(inner_done.0), usize::from(completed_inner));
                assert_eq!(visits(outer_started.0), 0);
            }
        }
    }

    #[test]
    fn owned_drain_internal_failure_retains_exact_written_and_reported_prefix_without_replay() {
        let program = effect_program(
            "import @builtin.cell as Cell\neffect Stop {\nstop : Unit -> Unit\n}\neffect Report {\nreport : Int -> Unit\n}\nmain : Unit -> Int\nmain () = resource cell<R> trace = 0 {\nlet result = handle (handle (cleanup fn(ignored) {\nlet outer_started = 7003\nCell.write (trace, 1)\n} {\ncleanup fn(ignored) {\nlet written = Cell.write (trace, 2)\nlet first_write_completed = 7001\nlet reported = perform Report.report 22\nlet report_completed = 7002\n()\n} {\nlet stopped = perform Stop.stop ()\n42\n}\n}) with Stop {\nstop ignored => {\nlet done = discard\nlet clause_continued = 7004\n7\n}\n}) with Report {\nreport error => resume ()\n}\nCell.read trace\n}\n",
        );
        let observed = Arc::new(std::sync::Mutex::new(Vec::new()));
        let mut measured = Machine::new_effect(&program);
        measured.work_trace = Some(Arc::clone(&observed));
        assert_eq!(measured.run().unwrap().value.to_string(), "1");
        let baseline = observed.lock().unwrap().clone();
        let marker = |value: &str| {
            baseline.iter().copied().find(|(node, _)| {
            matches!(&program.node(*node).unwrap().kind,
                EffectExprKind::Pure(PureExprKind::Value(PureValue::Integer(integer))) if integer.value().to_string() == value)
        }).unwrap()
        };
        let written = marker("7001");
        let reported = marker("7002");
        let outer = marker("7003");
        let clause = marker("7004");
        for stop in [written, outer] {
            for _ in 0..2 {
                let observed = Arc::new(std::sync::Mutex::new(Vec::new()));
                let mut failure = Machine::new_effect(&program);
                failure.work_trace = Some(Arc::clone(&observed));
                failure.instantiation_work = TypeWorkBudget::with_limit(stop.1);
                assert!(is_work_exhaustion(failure.run().unwrap_err()));
                let actual = observed.lock().unwrap();
                assert_eq!(actual.as_slice(), &baseline[..actual.len()]);
                let visits = |node| {
                    actual
                        .iter()
                        .filter(|(observed, _)| *observed == node)
                        .count()
                };
                assert_eq!(visits(written.0), 1);
                assert_eq!(visits(reported.0), usize::from(stop == outer));
                assert_eq!(visits(outer.0), usize::from(stop == outer));
                assert_eq!(visits(clause.0), 0);
            }
        }
    }

    #[test]
    fn cleanup_live_owner_cannot_be_published_as_a_successful_result() {
        let (program, _, _) = cleanup_fixture();
        let mut machine = Machine::new_effect(&program);
        machine.control = Some(Control::Return(integer("42")));
        machine.live_cleanups = 1;
        assert_eq!(
            machine.run().unwrap_err(),
            RuntimeFailure::InvalidControlState
        );
    }

    #[test]
    fn owned_deep_drain_success_and_partial_failure_use_the_predecessor_stack_bound() {
        const CHILD: &str = "ASH_OWNED_CLEANUP_MACHINE_STACK_CHILD";
        if std::env::var_os(CHILD).is_none() {
            let status = std::process::Command::new(std::env::current_exe().unwrap())
                .args(["--exact", "eval::machine::tests::owned_deep_drain_success_and_partial_failure_use_the_predecessor_stack_bound", "--nocapture"])
                .env(CHILD, "1").status().unwrap();
            assert!(status.success());
            return;
        }
        std::thread::Builder::new().stack_size(256 * 1024).spawn(|| {
            let mut source = String::from("effect Stop {\nstop : Unit -> Unit\n}\nmain : Unit -> Int\nmain () = handle (");
            for depth in 0..24 {
                source.push_str(&format!("cleanup fn(ignored) {{\nlet marker = {}\n()\n}} {{\n", 8000 + depth));
            }
            source.push_str("let stopped = perform Stop.stop ()\n42\n");
            for _ in 0..24 { source.push_str("}\n"); }
            source.push_str(") with Stop {\nstop ignored => {\nlet done = discard\n7\n}\n}\n");
            let program = effect_program(&source);
            let observed = Arc::new(std::sync::Mutex::new(Vec::new()));
            let mut exact = Machine::new_effect(&program);
            exact.cleanup_limit = 24;
            exact.work_trace = Some(Arc::clone(&observed));
            assert_eq!(exact.run().unwrap().value.to_string(), "7");
            let baseline = observed.lock().unwrap().clone();
            let stop = baseline.iter().copied().find(|(node, _)| {
                matches!(&program.node(*node).unwrap().kind, EffectExprKind::Pure(PureExprKind::Value(PureValue::Integer(integer))) if integer.value().to_string() == "8012")
            }).unwrap();
            let completed_inner = baseline.iter().copied().find(|(node, _)| {
                matches!(&program.node(*node).unwrap().kind, EffectExprKind::Pure(PureExprKind::Value(PureValue::Integer(integer))) if integer.value().to_string() == "8013")
            }).unwrap().0;
            for _ in 0..2 {
                let observed = Arc::new(std::sync::Mutex::new(Vec::new()));
                let mut partial = Machine::new_effect(&program);
                partial.work_trace = Some(Arc::clone(&observed));
                partial.instantiation_work = TypeWorkBudget::with_limit(stop.1);
                assert!(is_work_exhaustion(partial.run().unwrap_err()));
                let trace = observed.lock().unwrap();
                assert_eq!(trace.as_slice(), &baseline[..trace.len()]);
                assert_eq!(trace.iter().filter(|(node, _)| *node == stop.0).count(), 1);
                assert_eq!(trace.iter().filter(|(node, _)| *node == completed_inner).count(), 1);
            }
        }).unwrap().join().unwrap();
    }

    #[test]
    fn cleanup_deep_normal_completion_and_capacity_failure_use_a_small_stack() {
        const CHILD: &str = "ASH_CLEANUP_MACHINE_STACK_CHILD";
        if std::env::var_os(CHILD).is_none() {
            let status = std::process::Command::new(std::env::current_exe().unwrap()).args(["--exact", "eval::machine::tests::cleanup_deep_normal_completion_and_capacity_failure_use_a_small_stack", "--nocapture"]).env(CHILD, "1").status().unwrap();
            assert!(status.success());
            return;
        }
        std::thread::Builder::new()
            .stack_size(256 * 1024)
            .spawn(|| {
                let mut source = String::from("main : Unit -> Int\nmain () = ");
                for _ in 0..24 {
                    source.push_str("cleanup fn(ignored) {\n()\n} {\n");
                }
                source.push_str("42\n");
                for _ in 0..24 {
                    source.push_str("}\n");
                }
                let program = effect_program(&source);
                let mut exact = Machine::new_effect(&program);
                exact.cleanup_limit = 24;
                assert_eq!(exact.run().unwrap().value.to_string(), "42");
                let mut short = Machine::new_effect(&program);
                short.cleanup_limit = 23;
                assert!(is_configured_capacity(
                    short.run().unwrap_err(),
                    RuntimeFailure::ResourceCapacity,
                    RuntimeResource::CleanupOwners
                ));
            })
            .unwrap()
            .join()
            .unwrap();
    }

    #[test]
    fn discard_rejects_mismatched_selected_handlers_at_root_and_nested_cuts() {
        let (program, node, environment) = registration_fixture();
        let machine = Machine::new_effect(&program);
        let handler_node = machine.registration(node).unwrap().body;
        let handler = machine.handler(handler_node).unwrap().id();
        let wrong = HandlerId::new(handler.value().checked_add(1).unwrap());
        let captured = CapturedContinuation {
            frames: vec![Frame::HandlerBoundary {
                node: handler_node,
                environment,
                registration: None,
            }],
        };
        let mut measured = TypeWorkBudget::unbounded();
        assert!(
            selected_handler_for_discard(&machine.program, &captured, handler, &mut measured)
                .unwrap()
        );
        let exact = measured.used();
        assert!(
            selected_handler_for_discard(
                &machine.program,
                &captured,
                handler,
                &mut TypeWorkBudget::with_limit(exact - 1)
            )
            .is_err()
        );
        assert!(
            selected_handler_for_discard(
                &machine.program,
                &captured,
                handler,
                &mut TypeWorkBudget::with_limit(exact)
            )
            .unwrap()
        );
        assert_eq!(
            selected_handler_for_discard(
                &machine.program,
                &captured,
                wrong,
                &mut TypeWorkBudget::unbounded()
            ),
            Err(RuntimeFailure::InvalidControlState)
        );
        assert_eq!(captured.frames.len(), 1);
        let forest = CapturedContinuation {
            frames: vec![Frame::ClauseBoundary {
                handler: wrong,
                owner: ResumeId::new(0),
                continuation: Some(captured),
                registration: None,
            }],
        };
        let Frame::ClauseBoundary {
            continuation: Some(nested),
            ..
        } = &forest.frames[0]
        else {
            panic!("failed inspection consumed the nested continuation");
        };
        assert_eq!(
            selected_handler_for_discard(
                &machine.program,
                nested,
                wrong,
                &mut TypeWorkBudget::unbounded()
            ),
            Err(RuntimeFailure::InvalidControlState)
        );
        assert_eq!(nested.frames.len(), 1);
    }

    fn registration_fixture() -> (ValidatedEffectProgram, NodeId, Environment) {
        let program = effect_program(
            "effect Adjust {\npublish : Int -> Int\n}\nmain : Unit -> Int\nmain () = hook Adjust {\nregister Adjust (fn(value) {\nvalue + 1\n}) {\n42\n}\n}\n",
        );
        let mut pending = vec![program.root()];
        let mut nodes = Vec::new();
        while let Some(node) = pending.pop() {
            nodes.push(node);
            let kind = &program.node(node).unwrap().kind;
            pending.extend((0..kind.child_count()).filter_map(|index| kind.child_at(index)));
        }
        let node = *nodes
            .iter()
            .find(|node| {
                matches!(
                    &program.node(**node).unwrap().kind,
                    EffectExprKind::Operation(EffectOperation::Registration(_))
                )
            })
            .unwrap();
        let EffectExprKind::Operation(EffectOperation::Registration(scope)) =
            &program.node(node).unwrap().kind
        else {
            unreachable!()
        };
        let initializer =
            nodes
                .iter()
                .find_map(|node| match &program.node(*node).unwrap().kind {
                    EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Bind(
                        binding,
                    ))) if binding.binder().id() == scope.callback => Some(binding.initializer()),
                    _ => None,
                })
                .unwrap();
        let executable = ExecutableProgram::Effect(program.shared());
        let transition = dispatch_entry(
            &executable,
            initializer,
            Environment::new(),
            &mut Vec::new(),
        )
        .unwrap();
        let Control::Return(callback) = transition.control else {
            panic!("ordinary callback value")
        };
        let environment = Environment::new().extend(scope.callback, callback).unwrap();
        (program, node, environment)
    }

    #[test]
    fn registration_capacity_preflight_is_exact_atomic_and_reuses_fresh_activations() {
        let (program, node, environment) = registration_fixture();
        let mut measured = Machine::new_effect(&program);
        measured
            .acquire_registration(node, environment.clone())
            .unwrap();
        let work = measured.instantiation_work.used();
        assert_eq!(work, 3 + environment.len());
        for allowance in [work - 1, work, work] {
            let mut machine = Machine::new_effect(&program);
            machine.instantiation_work = TypeWorkBudget::with_limit(allowance);
            let result = machine.acquire_registration(node, environment.clone());
            if allowance < work {
                assert!(is_work_exhaustion(result.unwrap_err()));
                assert_eq!(machine.live_registrations, 0);
                assert_eq!(machine.next_registration, 0);
                assert!(machine.frames.is_empty());
                assert!(machine.trace.is_empty());
                assert!(machine.effect_trace.as_ref().unwrap().is_empty());
            } else {
                result.unwrap();
            }
        }
        let mut machine = Machine::new_effect(&program);
        machine.registration_limit = 1;
        for expected in 0..3 {
            machine
                .acquire_registration(node, environment.clone())
                .unwrap();
            assert!(
                matches!(machine.frames[0], Frame::RegistrationBoundary { key: RegistrationKey(key), .. } if key == expected)
            );
            let events = machine.effect_trace.clone();
            assert!(is_configured_capacity(
                machine
                    .acquire_registration(node, environment.clone())
                    .unwrap_err(),
                RuntimeFailure::ResourceCapacity,
                RuntimeResource::RegistrationOwners
            ));
            assert_eq!(machine.effect_trace, events);
            assert_eq!(machine.live_registrations, 1);
            assert_eq!(machine.next_registration, expected + 1);
            let handler = machine.frames.pop().unwrap();
            machine.return_from(handler, integer("42")).unwrap();
            let owner = machine.frames.pop().unwrap();
            machine.return_from(owner, integer("42")).unwrap();
            assert_eq!(machine.live_registrations, 0);
        }
        machine.next_registration = u32::MAX;
        assert!(is_configured_capacity(
            machine
                .acquire_registration(node, environment.clone())
                .unwrap_err(),
            RuntimeFailure::ResourceCapacity,
            RuntimeResource::RegistrationKeys
        ));
        assert!(machine.frames.is_empty());
        assert_eq!(machine.live_registrations, 0);
        let mut missing = Machine::new_effect(&program);
        assert_eq!(
            missing.acquire_registration(node, Environment::new()),
            Err(RuntimeFailure::MissingBinding)
        );
        assert_eq!(missing.next_registration, 0);
        assert!(missing.frames.is_empty());
    }

    #[test]
    fn registration_capacity_counts_active_and_captured_owners_and_releases_once() {
        for (source, expected) in [
            "effect Adjust {\npublish : Int -> Int\n}\nmain : Unit -> Int\nmain () = hook Adjust {\nregister Adjust (fn(value) {\nvalue + 1\n}) {\nregister Adjust (fn(value) {\nvalue * 2\n}) {\nperform Adjust.publish 3\n}\n}\n}\n",
            "effect Adjust {\npublish : Int -> Int\n}\neffect Pause {\nask : Unit -> Unit\n}\nmain : Unit -> Int\nmain () = hook Adjust {\nhandle (register Adjust (fn(value) {\nvalue + 1\n}) {\nlet _ = perform Pause.ask ()\nperform Adjust.publish 3\n}) with Pause {\nask ignored => {\nlet extra = register Adjust (fn(value) {\nvalue * 10\n}) {\nperform Adjust.publish 4\n}\nextra + (resume ())\n}\n}\n}\n",
        ].into_iter().zip(["8", "44"]) {
            let program = effect_program(source);
            for limit in [1, 2, 2] {
                let mut machine = Machine::new_effect(&program);
                machine.registration_limit = limit;
                let result = machine.run();
                if limit == 1 { assert!(is_configured_capacity(result.unwrap_err(), RuntimeFailure::ResourceCapacity, RuntimeResource::RegistrationOwners)); }
                else {
                    let evaluation = result.unwrap();
                    assert_eq!(evaluation.registration_acquisitions, 2);
                    assert_eq!(evaluation.value.to_string(), expected);
                }
            }
        }
        let program = effect_program(
            "effect Adjust {\npublish : Int -> Int\n}\nmain : Unit -> Int\nmain () = hook Adjust {\nlet first = register Adjust (fn(value) {\nvalue + 1\n}) {\nperform Adjust.publish 3\n}\nregister Adjust (fn(value) {\nvalue * 2\n}) {\nperform Adjust.publish first\n}\n}\n",
        );
        for _ in 0..2 {
            let mut machine = Machine::new_effect(&program);
            machine.registration_limit = 1;
            let result = machine.run().unwrap();
            assert_eq!(result.value.to_string(), "8");
            assert_eq!(result.registration_acquisitions, 2);
        }
    }

    #[test]
    fn registration_publication_work_is_exact_one_short_and_fresh_retryable() {
        let program = effect_program(
            "effect Adjust {\npublish : Int -> Int\n}\nmain : Unit -> Int\nmain () = hook Adjust {\nregister Adjust (fn(value) {\nvalue + 1\n}) {\nregister Adjust (fn(value) {\nvalue * 2\n}) {\nperform Adjust.publish 3\n}\n}\n}\n",
        );
        let measured = Machine::new_effect(&program).run().unwrap();
        let exact = measured.runtime_work;
        assert!(exact > 0);
        for allowance in [exact - 1, exact, exact] {
            let mut machine = Machine::new_effect(&program);
            machine.instantiation_work = TypeWorkBudget::with_limit(allowance);
            let result = machine.run();
            if allowance < exact {
                assert!(is_work_exhaustion(result.unwrap_err()));
            } else {
                let result = result.unwrap();
                assert_eq!(result.value.to_string(), "8");
                assert_eq!(result.runtime_work, exact);
            }
        }
    }

    #[test]
    fn registration_stale_duplicate_and_incomplete_facts_reject_before_mutation() {
        let (program, node, environment) = registration_fixture();
        let mut machine = Machine::new_effect(&program);
        machine
            .acquire_registration(node, environment.clone())
            .unwrap();
        let handler_node = machine.registration(node).unwrap().body;
        assert_eq!(
            machine.registration_owner(RegistrationKey(99), handler_node, 1),
            Err(RuntimeFailure::InvalidControlState)
        );
        machine.frames.push(Frame::HandlerBoundary {
            node: handler_node,
            environment: environment.clone(),
            registration: Some(RegistrationKey(0)),
        });
        assert_eq!(
            machine.registration_owner(RegistrationKey(0), handler_node, 1),
            Err(RuntimeFailure::InvalidControlState)
        );
        machine.frames.pop();
        machine.frames.push(Frame::RegistrationBoundary {
            key: RegistrationKey(0),
            handler: handler_node,
            callback: Value::Unit,
            handler_active: true,
            pending_invocations: 0,
        });
        assert_eq!(
            machine.registration_owner(RegistrationKey(0), handler_node, 1),
            Err(RuntimeFailure::InvalidControlState)
        );
        machine.frames.pop();
        assert_eq!(machine.live_registrations, 1);
        assert!(matches!(
            machine.frames[0],
            Frame::RegistrationBoundary {
                handler_active: true,
                pending_invocations: 0,
                ..
            }
        ));
        let owner = machine.frames.remove(0);
        assert_eq!(
            machine.return_from(owner, Value::Unit),
            Err(RuntimeFailure::InvalidControlState)
        );
        assert_eq!(machine.live_registrations, 1);
        let handler = machine.frames.pop().unwrap();
        assert_eq!(
            machine.return_from(handler, Value::Unit),
            Err(RuntimeFailure::InvalidControlState)
        );
        assert_eq!(machine.live_registrations, 1);
    }

    #[test]
    fn registration_invocation_preflight_keeps_the_owner_and_capture_unchanged() {
        let (program, node, environment) = registration_fixture();
        let mut machine = Machine::new_effect(&program);
        machine.acquire_registration(node, environment).unwrap();
        let handler = machine.registration(node).unwrap().body;
        let mut pending = vec![machine.handler(handler).unwrap().clauses()[0].body()];
        let request = loop {
            let node = pending.pop().unwrap();
            let ExecutableNode::Effect(expression) = machine.program.node(node).unwrap() else {
                unreachable!()
            };
            if matches!(
                expression.kind,
                EffectExprKind::Operation(EffectOperation::Request(_))
            ) {
                break node;
            }
            pending.extend(
                (0..expression.kind.child_count())
                    .filter_map(|index| expression.kind.child_at(index)),
            );
        };
        let Frame::HandlerBoundary { environment, .. } = &mut machine.frames[1] else {
            unreachable!()
        };
        environment.len = usize::MAX;
        let events = machine.effect_trace.clone();
        assert!(is_configured_capacity(
            machine
                .return_request(request, &Instantiation::default(), integer("3"))
                .unwrap_err(),
            RuntimeFailure::EnvironmentCapacity,
            RuntimeResource::EnvironmentBindings
        ));
        assert_eq!(machine.frames.len(), 2);
        assert_eq!(machine.captured_cells, 0);
        assert_eq!(machine.live_registrations, 1);
        assert_eq!(machine.effect_trace, events);
        assert!(matches!(
            machine.frames[0],
            Frame::RegistrationBoundary {
                handler_active: true,
                pending_invocations: 0,
                ..
            }
        ));
    }

    #[test]
    fn registration_request_and_resume_reject_stale_and_duplicate_nonowning_facts() {
        let (program, node, environment) = registration_fixture();
        let mut machine = Machine::new_effect(&program);
        machine
            .acquire_registration(node, environment.clone())
            .unwrap();
        let handler_node = machine.registration(node).unwrap().body;
        let mut pending = vec![machine.handler(handler_node).unwrap().clauses()[0].body()];
        let mut request = None;
        let mut resume = None;
        while let Some(node) = pending.pop() {
            let ExecutableNode::Effect(expression) = machine.program.node(node).unwrap() else {
                unreachable!()
            };
            match expression.kind {
                EffectExprKind::Operation(EffectOperation::Request(_)) => request = Some(node),
                EffectExprKind::Operation(EffectOperation::Resume(_)) => resume = Some(node),
                _ => {}
            }
            pending.extend(
                (0..expression.kind.child_count())
                    .filter_map(|index| expression.kind.child_at(index)),
            );
        }
        let (request, resume) = (request.unwrap(), resume.unwrap());
        let events = machine.effect_trace.clone();
        let Frame::HandlerBoundary { registration, .. } = &mut machine.frames[1] else {
            unreachable!()
        };
        *registration = Some(RegistrationKey(99));
        assert_eq!(
            machine.return_request(request, &Instantiation::default(), integer("3")),
            Err(RuntimeFailure::InvalidControlState)
        );
        assert_eq!(machine.frames.len(), 2);
        assert_eq!(machine.captured_cells, 0);
        assert_eq!(machine.effect_trace, events);
        let Frame::HandlerBoundary { registration, .. } = &mut machine.frames[1] else {
            unreachable!()
        };
        *registration = Some(RegistrationKey(0));
        machine.frames.push(Frame::HandlerBoundary {
            node: handler_node,
            environment: environment.clone(),
            registration: Some(RegistrationKey(0)),
        });
        assert_eq!(
            machine.return_request(request, &Instantiation::default(), integer("3")),
            Err(RuntimeFailure::InvalidControlState)
        );
        assert_eq!(machine.frames.len(), 3);
        assert_eq!(machine.captured_cells, 0);
        assert_eq!(machine.effect_trace, events);
        machine.frames.pop();
        machine
            .return_request(request, &Instantiation::default(), integer("3"))
            .unwrap();
        assert!(matches!(
            machine.frames[0],
            Frame::RegistrationBoundary {
                handler_active: false,
                pending_invocations: 1,
                ..
            }
        ));
        let events = machine.effect_trace.clone();
        let handler = machine.handler(handler_node).unwrap();
        let (handler_id, resume_owner) = (handler.id(), handler.clauses()[0].resume());
        assert_eq!(
            machine.discard(handler_id, resume_owner),
            Err(RuntimeFailure::InvalidControlState)
        );
        assert_eq!(machine.effect_trace, events);
        let Frame::ClauseBoundary { registration, .. } = &mut machine.frames[1] else {
            unreachable!()
        };
        *registration = Some(RegistrationKey(99));
        assert_eq!(
            machine.return_resume(resume, integer("4")),
            Err(RuntimeFailure::InvalidControlState)
        );
        let Frame::ClauseBoundary {
            registration,
            continuation: Some(captured),
            ..
        } = &mut machine.frames[1]
        else {
            unreachable!()
        };
        *registration = Some(RegistrationKey(0));
        let Frame::HandlerBoundary { registration, .. } = &mut captured.frames[0] else {
            unreachable!()
        };
        *registration = Some(RegistrationKey(99));
        assert_eq!(
            machine.return_resume(resume, integer("4")),
            Err(RuntimeFailure::InvalidControlState)
        );
        let Frame::ClauseBoundary {
            continuation: Some(captured),
            ..
        } = &mut machine.frames[1]
        else {
            unreachable!()
        };
        let Frame::HandlerBoundary { registration, .. } = &mut captured.frames[0] else {
            unreachable!()
        };
        *registration = Some(RegistrationKey(0));
        captured.frames.push(Frame::HandlerBoundary {
            node: handler_node,
            environment: environment.clone(),
            registration: Some(RegistrationKey(0)),
        });
        assert_eq!(
            machine.return_resume(resume, integer("4")),
            Err(RuntimeFailure::InvalidControlState)
        );
        assert_eq!(machine.captured_cells, 1);
        assert_eq!(machine.live_registrations, 1);
        assert_eq!(machine.effect_trace, events);
        let Frame::ClauseBoundary {
            continuation: Some(captured),
            ..
        } = &mut machine.frames[1]
        else {
            unreachable!()
        };
        captured.frames.pop();
        machine.return_resume(resume, integer("4")).unwrap();
        assert_eq!(
            machine.return_resume(resume, integer("4")),
            Err(RuntimeFailure::InvalidControlState)
        );
        assert_eq!(machine.captured_cells, 0);
        assert_eq!(machine.live_registrations, 1);
        for _ in 0..3 {
            let frame = machine.frames.pop().unwrap();
            machine.return_from(frame, integer("42")).unwrap();
        }
        assert_eq!(machine.live_registrations, 0);
        machine
            .acquire_registration(node, environment.clone())
            .unwrap();
        let stale = Frame::HandlerBoundary {
            node: handler_node,
            environment,
            registration: Some(RegistrationKey(0)),
        };
        assert_eq!(
            machine.return_from(stale, integer("42")),
            Err(RuntimeFailure::InvalidControlState)
        );
        assert_eq!(machine.live_registrations, 1);
        assert_eq!(machine.next_registration, 2);
    }

    #[test]
    fn registration_duplicate_consumed_clause_rejects_before_owner_mutation() {
        let (program, node, environment) = registration_fixture();
        let mut machine = Machine::new_effect(&program);
        machine.acquire_registration(node, environment).unwrap();
        let handler_node = machine.registration(node).unwrap().body;
        let handler = machine.handler(handler_node).unwrap();
        let (handler_id, owner) = (handler.id(), handler.clauses()[0].resume());
        let mut pending = vec![handler.clauses()[0].body()];
        let (mut request, mut resume) = (None, None);
        while let Some(node) = pending.pop() {
            let ExecutableNode::Effect(expression) = machine.program.node(node).unwrap() else {
                unreachable!()
            };
            match expression.kind {
                EffectExprKind::Operation(EffectOperation::Request(_)) => request = Some(node),
                EffectExprKind::Operation(EffectOperation::Resume(_)) => resume = Some(node),
                _ => {}
            }
            pending.extend(
                (0..expression.kind.child_count())
                    .filter_map(|index| expression.kind.child_at(index)),
            );
        }
        machine
            .return_request(request.unwrap(), &Instantiation::default(), integer("3"))
            .unwrap();
        machine
            .return_resume(resume.unwrap(), integer("4"))
            .unwrap();
        let restored = machine.frames.pop().unwrap();
        machine.return_from(restored, integer("4")).unwrap();
        let events = machine.effect_trace.clone();
        let duplicate = Frame::ClauseBoundary {
            handler: handler_id,
            owner,
            continuation: None,
            registration: Some(RegistrationKey(0)),
        };
        assert_eq!(
            machine.return_from(duplicate, integer("4")),
            Err(RuntimeFailure::InvalidControlState)
        );
        assert_eq!(machine.effect_trace, events);
        assert_eq!(machine.frames.len(), 2);
        assert_eq!(machine.live_registrations, 1);
        assert_eq!(machine.captured_cells, 0);
        assert!(matches!(
            machine.frames[0],
            Frame::RegistrationBoundary {
                handler_active: false,
                pending_invocations: 1,
                ..
            }
        ));
        for _ in 0..2 {
            let frame = machine.frames.pop().unwrap();
            machine.return_from(frame, integer("4")).unwrap();
        }
        assert_eq!(machine.live_registrations, 0);
    }

    #[test]
    fn registration_duplicate_active_handler_return_rejects_before_owner_mutation() {
        assert_registration_duplicate_rejected(false);
    }

    #[test]
    fn registration_duplicate_active_handler_resume_rejects_before_owner_mutation() {
        assert_registration_duplicate_rejected(true);
    }

    fn assert_registration_duplicate_rejected(resume_transition: bool) {
        let (program, node, environment) = registration_fixture();
        let mut machine = Machine::new_effect(&program);
        machine
            .acquire_registration(node, environment.clone())
            .unwrap();
        let handler_node = machine.registration(node).unwrap().body;
        let mut pending = vec![machine.handler(handler_node).unwrap().clauses()[0].body()];
        let (mut request, mut resume) = (None, None);
        while let Some(node) = pending.pop() {
            let ExecutableNode::Effect(expression) = machine.program.node(node).unwrap() else {
                unreachable!()
            };
            match expression.kind {
                EffectExprKind::Operation(EffectOperation::Request(_)) => request = Some(node),
                EffectExprKind::Operation(EffectOperation::Resume(_)) => resume = Some(node),
                _ => {}
            }
            pending.extend(
                (0..expression.kind.child_count())
                    .filter_map(|index| expression.kind.child_at(index)),
            );
        }
        if resume_transition {
            machine
                .return_request(request.unwrap(), &Instantiation::default(), integer("3"))
                .unwrap();
        }
        machine.frames.push(Frame::HandlerBoundary {
            node: handler_node,
            environment,
            registration: Some(RegistrationKey(0)),
        });
        let events = machine.effect_trace.clone();
        let result = if resume_transition {
            machine.return_resume(resume.unwrap(), integer("4"))
        } else {
            let duplicate = machine.frames.pop().unwrap();
            machine.return_from(duplicate, integer("4"))
        };
        assert_eq!(
            result,
            Err(RuntimeFailure::InvalidControlState),
            "resume transition: {resume_transition}"
        );
        assert_eq!(machine.frames.len(), if resume_transition { 3 } else { 2 });
        assert_eq!(machine.captured_cells, usize::from(resume_transition));
        assert_eq!(machine.live_registrations, 1);
        assert_eq!(machine.effect_trace, events);
        let Frame::RegistrationBoundary {
            handler_active,
            pending_invocations,
            ..
        } = &machine.frames[0]
        else {
            unreachable!()
        };
        assert_eq!(*handler_active, !resume_transition);
        assert_eq!(*pending_invocations, usize::from(resume_transition));
    }

    #[test]
    fn registration_chain_steps_are_separate_from_ordinary_callback_work() {
        for depth in [1, 2, 4] {
            for callback in ["value + 1", "(value + 1) + 0 + 0 + 0"] {
                let source = format!(
                    "effect Adjust {{\npublish : Int -> Int\n}}\ncallback : Int -> Int\ncallback value = {callback}\nmain : Unit -> Int\nmain () = hook Adjust {{\n{}perform Adjust.publish 3{}\n}}\n",
                    "register Adjust callback {\n".repeat(depth),
                    "\n}".repeat(depth)
                );
                let program = effect_program(&source);
                let evaluation = Machine::new_effect(&program).run().unwrap();
                let mut pending = vec![program.root()];
                let mut primitive_nodes = Vec::new();
                while let Some(node) = pending.pop() {
                    let kind = &program.node(node).unwrap().kind;
                    if matches!(
                        kind,
                        EffectExprKind::Pure(PureExprKind::Computation(
                            PureComputation::Primitive(_)
                        ))
                    ) {
                        primitive_nodes.push(node);
                    }
                    pending
                        .extend((0..kind.child_count()).filter_map(|index| kind.child_at(index)));
                }
                let selected = evaluation
                    .effect_trace()
                    .iter()
                    .filter(|event| matches!(event, EffectTraceEvent::HandlerSelected(_)))
                    .count();
                let requests = evaluation
                    .effect_trace()
                    .iter()
                    .filter(|event| matches!(event, EffectTraceEvent::Request(_)))
                    .count();
                let resumed = evaluation
                    .effect_trace()
                    .iter()
                    .filter(|event| matches!(event, EffectTraceEvent::Resume(_)))
                    .count();
                let callback_steps = evaluation.trace.iter().filter(|event| matches!(event, TraceEvent::Enter(node) if primitive_nodes.contains(node))).count();
                assert_eq!(evaluation.registration_acquisitions as usize, depth);
                assert_eq!(selected, depth + 1);
                assert_eq!(requests, depth + 1);
                assert_eq!(resumed, depth + 1);
                assert_eq!(callback_steps, depth * primitive_nodes.len());
                assert_eq!(evaluation.value.to_string(), (3 + depth).to_string());
            }
        }
    }

    #[test]
    fn deep_registration_callbacks_capture_cells_and_dispose_failure_on_a_small_stack() {
        const CHILD: &str = "ASH_REGISTRATION_CALLBACK_STACK_CHILD";
        if std::env::var_os(CHILD).is_none() {
            let status = std::process::Command::new(std::env::current_exe().unwrap())
                .args(["--exact", "eval::machine::tests::deep_registration_callbacks_capture_cells_and_dispose_failure_on_a_small_stack", "--nocapture"])
                .env(CHILD, "1").status().unwrap();
            assert!(
                status.success(),
                "fresh registration runtime child: {status}"
            );
            return;
        }
        const DEPTH: usize = 1024;
        let source = format!(
            "import @builtin.cell as Cell\neffect Adjust {{\npublish : Int -> Int\n}}\neffect Pause {{\nask : Int -> Int\n}}\ndescend : Int -> Int ! {{Adjust, Pause}}\ndescend depth = resource cell<R> c = depth {{\nlet callback : Int -> Int ! {{Cell.Ops<R>, Pause}} = fn(value) {{\nlet copied = Cell.read c\nperform Pause.ask (value + copied)\n}}\nregister Adjust callback {{\nmatch depth == {DEPTH} {{\ntrue => perform Adjust.publish 0\nfalse => descend (depth + 1)\n}}\n}}\n}}\nmain : Unit -> Int\nmain () = handle (hook Adjust {{\ndescend 0\n}}) with Pause {{\nask value => resume value\n}}\n"
        );
        let program = effect_program(&source);
        let mut pending = vec![program.root()];
        let mut requests = Vec::new();
        while let Some(node) = pending.pop() {
            let kind = &program.node(node).unwrap().kind;
            if let EffectExprKind::Operation(EffectOperation::Request(request)) = kind {
                // The source callback's explicit request is the only request
                // whose operation is named `ask` in this fixture.
                if program
                    .registry()
                    .effect(request.effect().effect())
                    .unwrap()
                    .operations[request.operation().operation() as usize]
                    .spelling
                    == "ask"
                {
                    requests.push(node);
                }
            }
            pending.extend((0..kind.child_count()).filter_map(|index| kind.child_at(index)));
        }
        assert_eq!(requests.len(), 1);
        let callback_request = requests[0];
        std::thread::Builder::new()
            .stack_size(256 * 1024)
            .spawn(move || {
                let mut machine = Machine::new_effect(&program);
                machine.work_trace = Some(Arc::new(std::sync::Mutex::new(Vec::new())));
                let result = machine.run().unwrap();
                assert_eq!(
                    result.value.to_string(),
                    (DEPTH * (DEPTH + 1) / 2).to_string()
                );
                assert_eq!(result.registration_acquisitions as usize, DEPTH + 1);
                let trace = result.work_trace.as_ref().unwrap();
                let failure_work = trace
                    .iter()
                    .find_map(|(node, work)| (*node == callback_request).then_some(*work))
                    .unwrap();
                assert_eq!(
                    trace
                        .iter()
                        .filter(|(node, _)| *node == callback_request)
                        .count(),
                    DEPTH + 1
                );
                assert!(result.max_frame_depth > DEPTH);
                for _ in 0..2 {
                    let mut failure = Machine::new_effect(&program);
                    failure.instantiation_work = TypeWorkBudget::with_limit(failure_work);
                    assert!(matches!(
                        failure.run(),
                        Err(failure) if is_work_exhaustion(failure)
                    ));
                }
            })
            .unwrap()
            .join()
            .unwrap();
    }

    #[test]
    fn generic_cell_acquisition_work_refusal_is_atomic_and_retryable() {
        let (program, _) = crate::core::validate::generic_cell_validated_fixture_for_test();
        let node = resource_node(&program);
        let mut measured = Machine::new_effect(&program);
        measured.instantiation_work = TypeWorkBudget::unbounded();
        measured
            .acquire_resource(node, Environment::new(), integer("41"))
            .unwrap();
        let required = measured.instantiation_work.used();
        for allowance in 0..required {
            let mut short = Machine::new_effect(&program);
            short.instantiation_work = TypeWorkBudget::with_limit(allowance);
            let trace = short.effect_trace.clone();
            let failure = short
                .acquire_resource(node, Environment::new(), integer("41"))
                .unwrap_err();
            assert!(is_work_exhaustion(failure), "allowance={allowance}");
            assert_eq!(short.live_resources, 0);
            assert_eq!(short.next_activation, 0);
            assert!(short.frames.is_empty());
            assert_eq!(short.effect_trace, trace);
        }
        for _ in 0..2 {
            let mut exact = Machine::new_effect(&program);
            exact.instantiation_work = TypeWorkBudget::with_limit(required);
            exact
                .acquire_resource(node, Environment::new(), integer("41"))
                .unwrap();
            assert_eq!(exact.instantiation_work.used(), required);
            assert_eq!(exact.live_resources, 1);
            assert_eq!(exact.next_activation, 1);
        }
    }

    #[test]
    fn generic_cell_write_preflight_is_atomic_paid_and_retryable() {
        let (program, _) = crate::core::validate::generic_cell_validated_fixture_for_test();
        let node = resource_node(&program);
        let prepare = || {
            let mut machine = Machine::new_effect(&program);
            machine
                .acquire_resource(node, Environment::new(), integer("41"))
                .unwrap();
            let operand = allocate_heap(
                &mut machine.heap,
                HeapCell::Tuple(Box::new([
                    Value::ResourceHandle(ActivationKey(0)),
                    integer("999999999999999999999999999999999999"),
                ])),
            )
            .unwrap();
            machine.instantiation_work = TypeWorkBudget::unbounded();
            (machine, Value::Location(operand))
        };
        let (mut measured, operand) = prepare();
        let write = OperationId::new(
            measured
                .resource(node)
                .unwrap()
                .acquisition
                .api()
                .unwrap()
                .ops(),
            1,
        );
        measured.interpret_cell(0, write, operand).unwrap();
        let required = measured.instantiation_work.used();
        assert_eq!(
            measured.effect_trace.as_deref().unwrap(),
            &[
                EffectTraceEvent::ResourceAcquired(0),
                EffectTraceEvent::Request(write),
                EffectTraceEvent::ResourceWritten(0),
            ]
        );
        assert!(required > 2, "integer magnitude is charged");
        for allowance in 0..required {
            let (mut short, operand) = prepare();
            short.instantiation_work = TypeWorkBudget::with_limit(allowance);
            let trace = short.effect_trace.clone();
            let failure = short.interpret_cell(0, write, operand).unwrap_err();
            assert!(matches!(failure, RuntimeFailure::Report(report)
                if report.primary.resource().is_some_and(|details|
                    details.cause == ResourceFailureCause::WorkBudgetExhausted
                    && details.phase == RuntimePhase::Access
                    && details.resource == RuntimeResource::WorkUnits)));

            assert_eq!(short.effect_trace, trace);
            assert!(matches!(&short.frames[0], Frame::ResourceBoundary {
                payload: ResourcePayload::Generic { value: Value::Integer(value), .. }, ..
            } if value.to_string() == "41"));
            assert_eq!(short.live_resources, 1);
            assert_eq!(short.next_activation, 1);
        }
        for _ in 0..2 {
            let (mut exact, operand) = prepare();
            exact.instantiation_work = TypeWorkBudget::with_limit(required);
            exact.interpret_cell(0, write, operand).unwrap();
            assert_eq!(exact.instantiation_work.used(), required);
            assert_eq!(
                exact.effect_trace.as_deref().unwrap(),
                &[
                    EffectTraceEvent::ResourceAcquired(0),
                    EffectTraceEvent::Request(write),
                    EffectTraceEvent::ResourceWritten(0),
                ]
            );
        }
    }

    #[test]
    fn generic_cell_function_copy_charges_origin_before_retaining_metadata() {
        let program =
            effect_program("main : Unit -> (Unit -> Int)\nmain () = fn(ignored) {\n7\n}\n");
        let Value::Function(mut function) = Machine::new_effect(&program).run().unwrap().value
        else {
            panic!("function fixture")
        };
        let span = function.origin.primary_span();
        function.origin = Origin::Source(span);
        for depth in 0..crate::core::dialect::CORE_PAYLOAD_DEPTH_LIMIT {
            function.origin = if depth % 2 == 0 {
                Origin::Generated {
                    cause: Box::new(function.origin),
                    reason: crate::source::GeneratedReason::TypeChecking,
                }
            } else {
                Origin::Related {
                    primary: Box::new(function.origin),
                    related: vec![span; 4],
                }
            };
        }
        let value = Value::Function(function);
        let mut measured = TypeWorkBudget::unbounded();
        drop(copy_generic_cell_value(&value, &mut measured).unwrap());
        let required = measured.used();
        assert!(required > crate::core::dialect::CORE_PAYLOAD_DEPTH_LIMIT);
        let mut short = TypeWorkBudget::with_limit(required - 1);
        assert!(copy_generic_cell_value(&value, &mut short).is_err());
        for _ in 0..2 {
            let mut exact = TypeWorkBudget::with_limit(required);
            let copied = copy_generic_cell_value(&value, &mut exact).unwrap();
            assert_eq!(exact.used(), required);
            assert!(
                matches!(&copied, Value::Function(function) if function.origin.primary_span() == span)
            );
            drop(copied);
        }
    }

    #[test]
    fn generic_cell_requests_reject_wrong_type_live_donor_stale_and_family() {
        let program = effect_program(
            "import @builtin.generic_cell as Cell\nimport @builtin.cell as Legacy\nmain : Unit -> Int\nmain () = resource cell<L> legacy = 7 {\nlet first = resource Cell.Cell<C,Int> c = 41 {\nCell.read c\n}\nlet second = resource Cell.Cell<B,Bool> b = true {\nCell.read b\n}\nlet ignored = Legacy.read legacy\nmatch second {\ntrue => first\nfalse => 0\n}\n}\n",
        );
        let mut pending = vec![program.root()];
        let mut generic_node = None;
        let mut int_request = None;
        let mut bool_request = None;
        let mut legacy_request = None;
        while let Some(node) = pending.pop() {
            let kind = &program.node(node).unwrap().kind;
            match kind {
                EffectExprKind::Operation(EffectOperation::Resource(scope))
                    if scope.acquisition.api().unwrap().generic() =>
                {
                    let Type::Application(_, payload) = scope.handle().ty() else {
                        panic!("complete handle")
                    };
                    match &**payload {
                        Type::Int => generic_node = Some((node, None)),
                        Type::Variable(parameter) if generic_node.is_none() => {
                            generic_node = Some((node, Some(*parameter)))
                        }
                        _ => {}
                    }
                }
                EffectExprKind::Operation(EffectOperation::Request(request)) => {
                    if let [
                        crate::types::KindedArgument::TypeArg(Type::Variable(owner)),
                        crate::types::KindedArgument::TypeArg(payload),
                    ] = request.effect().arguments()
                    {
                        match payload {
                            Type::Int => int_request = Some((node, *owner)),
                            Type::Bool => bool_request = Some((node, *owner)),
                            _ => {}
                        }
                    } else if let [crate::types::KindedArgument::TypeArg(Type::Variable(owner))] =
                        request.effect().arguments()
                        && request.effect().effect().module().is_builtin_cell()
                    {
                        legacy_request = Some((node, *owner));
                    }
                }
                _ => {}
            }
            pending.extend((0..kind.child_count()).filter_map(|index| kind.child_at(index)));
        }
        let (node, parameter) = generic_node.expect("Int acquisition");
        let (int_request, int_owner) = int_request.expect("actual closed Int request");
        let (bool_request, bool_owner) = bool_request.expect("actual closed Bool request");
        let instantiate = |owner, key| {
            Instantiation::default()
                .acquire(owner, key, &mut TypeWorkBudget::default(), None)
                .unwrap()
        };
        let mut environment = Environment::new();
        if let Some(parameter) = parameter {
            environment.instantiation = Instantiation::default()
                .apply(
                    &Instantiation::default(),
                    &[(parameter, crate::types::Kind::Type)],
                    &[Type::Int],
                    &[],
                    &mut TypeWorkBudget::default(),
                )
                .unwrap();
        }
        let mut machine = Machine::new_effect(&program);
        machine
            .acquire_resource(node, environment.clone(), integer("41"))
            .unwrap();
        machine
            .acquire_resource(node, environment.clone(), integer("99"))
            .unwrap();
        for (request, owner, handle, reason) in [
            (bool_request, bool_owner, 0, "runtime.foreign-binding"),
            (int_request, int_owner, 1, "runtime.invalid-control-state"),
        ] {
            let trace = machine.effect_trace.clone();
            let failure = machine
                .return_request(
                    request,
                    &instantiate(owner, ActivationKey(0)),
                    Value::ResourceHandle(ActivationKey(handle)),
                )
                .unwrap_err();
            assert_eq!(failure.reason_code(), reason);
            assert_eq!(machine.effect_trace, trace);
            for (frame, expected) in machine.frames.iter().zip(["41", "99"]) {
                assert!(
                    matches!(frame,Frame::ResourceBoundary { payload:ResourcePayload::Generic { value:Value::Integer(value),.. },.. } if value.to_string()==expected)
                );
            }
        }
        let (legacy, identity) = legacy_request.expect("legacy family request");
        let trace = machine.effect_trace.clone();
        assert_eq!(
            machine
                .return_request(
                    legacy,
                    &instantiate(identity, ActivationKey(0)),
                    Value::ResourceHandle(ActivationKey(0))
                )
                .unwrap_err()
                .reason_code(),
            "runtime.foreign-binding"
        );
        assert_eq!(machine.effect_trace, trace);
        machine
            .return_request(
                int_request,
                &instantiate(int_owner, ActivationKey(0)),
                Value::ResourceHandle(ActivationKey(0)),
            )
            .unwrap();
        assert!(
            matches!(&machine.control,Some(Control::Return(Value::Integer(value))) if value.to_string()=="41")
        );
        for _ in 0..2 {
            let frame = machine.frames.pop().unwrap();
            machine.return_from(frame, Value::Unit).unwrap();
        }
        machine
            .acquire_resource(node, environment, integer("7"))
            .unwrap();
        assert_eq!(machine.next_activation, 3);
        let trace = machine.effect_trace.clone();
        assert_eq!(
            machine
                .return_request(
                    int_request,
                    &instantiate(int_owner, ActivationKey(0)),
                    Value::ResourceHandle(ActivationKey(0))
                )
                .unwrap_err()
                .reason_code(),
            "runtime.foreign-binding"
        );
        assert_eq!(machine.effect_trace, trace);
        let donor = effect_program(
            "import @builtin.generic_cell as Cell\nmain : Unit -> Int\nmain () = resource Cell.Cell<R,Int> c = 41 {\nCell.read c\n}\n",
        );
        let mut pending = vec![donor.root()];
        let request = loop {
            let node = pending.pop().expect("donor request");
            let kind = &donor.node(node).unwrap().kind;
            if matches!(kind, EffectExprKind::Operation(EffectOperation::Request(_))) {
                break node;
            }
            pending.extend((0..kind.child_count()).filter_map(|index| kind.child_at(index)));
        };
        assert!(matches!(
            &donor.node(request).unwrap().kind,
            EffectExprKind::Operation(EffectOperation::Request(_))
        ));
        assert!(machine.program.node(request).is_none());
        assert_eq!(
            machine
                .return_request(
                    request,
                    &instantiate(int_owner, ActivationKey(2)),
                    Value::ResourceHandle(ActivationKey(2))
                )
                .unwrap_err(),
            RuntimeFailure::InvalidControlState
        );
        assert_eq!(machine.effect_trace, trace);
    }

    #[test]
    fn generic_cell_repeated_large_cyclic_reads_share_the_exact_heap_root() {
        let program = effect_program(
            "import @builtin.generic_cell as Cell\ntype Stream = Next(Int,Stream)\nmain : Unit -> Int\nmain () = {\nlet rec ones : Stream = Next(1,ones)\nresource Cell.Cell<R,Stream> c = ones {\nmatch Cell.read c {\nNext(first,rest) => first\n}\n}\n}\n",
        );
        let node = resource_node(&program);
        let constructor = program
            .registry()
            .constructors()
            .iter()
            .find(|constructor| constructor.spelling == "Next")
            .unwrap()
            .id;
        let mut costs = Vec::new();
        for depth in [1, 4096] {
            let mut machine = Machine::new_effect(&program);
            for index in 0..depth {
                let next = ((index + 1) % depth) * 2;
                machine.heap.push(HeapCell::Constructor(
                    constructor,
                    Some(Value::Location(index * 2 + 1)),
                ));
                machine.heap.push(HeapCell::Tuple(Box::new([
                    integer("1"),
                    Value::Location(next),
                ])));
            }
            machine
                .acquire_resource(node, Environment::new(), Value::Location(0))
                .unwrap();
            let read = OperationId::new(
                machine
                    .resource(node)
                    .unwrap()
                    .acquisition
                    .api()
                    .unwrap()
                    .ops(),
                0,
            );
            for _ in 0..2 {
                machine.instantiation_work = TypeWorkBudget::unbounded();
                machine
                    .interpret_cell(0, read, Value::ResourceHandle(ActivationKey(0)))
                    .unwrap();
                costs.push(machine.instantiation_work.used());
                assert!(matches!(
                    machine.control,
                    Some(Control::Return(Value::Location(0)))
                ));
                assert_eq!(machine.heap.len(), depth * 2);
                assert!(matches!(
                    &machine.frames[0],
                    Frame::ResourceBoundary {
                        payload: ResourcePayload::Generic {
                            value: Value::Location(0),
                            ..
                        },
                        ..
                    }
                ));
            }
        }
        assert!(
            costs.iter().all(|cost| *cost == costs[0]),
            "read does not walk shared cyclic payload"
        );
    }

    #[test]
    fn generic_cell_captured_capacity_preserves_latest_root_and_fresh_reuse() {
        let (program, _) = crate::core::validate::generic_cell_validated_fixture_for_test();
        let node = resource_node(&program);
        for discard in [false, true] {
            let mut machine = Machine::new_effect(&program);
            machine.resource_limit = 1;
            machine
                .acquire_resource(node, Environment::new(), integer("41"))
                .unwrap();
            let api = machine.resource(node).unwrap().acquisition.api().unwrap();
            let operand = allocate_heap(
                &mut machine.heap,
                HeapCell::Tuple(Box::new([
                    Value::ResourceHandle(ActivationKey(0)),
                    integer("99"),
                ])),
            )
            .unwrap();
            machine
                .interpret_cell(0, OperationId::new(api.ops(), 1), Value::Location(operand))
                .unwrap();
            let mut captured = machine.capture_from(0).unwrap();
            assert_eq!(machine.live_resources, 1);
            assert_eq!(machine.captured_cells, 1);
            assert!(
                matches!(&captured.frames[0], Frame::ResourceBoundary { payload: ResourcePayload::Generic { value: Value::Integer(value), .. }, .. } if value.to_string()=="99")
            );
            let trace = machine.effect_trace.clone();
            assert!(is_configured_capacity(
                machine
                    .acquire_resource(node, Environment::new(), integer("7"))
                    .unwrap_err(),
                RuntimeFailure::ResourceCapacity,
                RuntimeResource::ResourceOwners
            ));
            assert_eq!(machine.effect_trace, trace);
            assert_eq!(machine.next_activation, 1);
            if discard {
                let handler = HandlerId::new(0);
                let owner = ResumeId::new(0);
                machine.frames.push(Frame::ClauseBoundary {
                    registration: None,
                    handler,
                    owner,
                    continuation: Some(captured),
                });
                machine.discard(handler, owner).unwrap();
                let frame = machine.frames.pop().unwrap();
                machine.return_from(frame, Value::Unit).unwrap();
                let frame = machine.frames.pop().unwrap();
                machine.return_from(frame, Value::Unit).unwrap();
                let frame = machine.frames.pop().unwrap();
                machine.return_from(frame, Value::Unit).unwrap();
            } else {
                machine.frames.append(&mut captured.frames);
                machine.captured_cells = 0;
                machine
                    .interpret_cell(
                        0,
                        OperationId::new(api.ops(), 0),
                        Value::ResourceHandle(ActivationKey(0)),
                    )
                    .unwrap();
                assert!(
                    matches!(&machine.control,Some(Control::Return(Value::Integer(value))) if value.to_string()=="99")
                );
                let frame = machine.frames.pop().unwrap();
                machine.return_from(frame, Value::Unit).unwrap();
            }
            assert_eq!(machine.live_resources, 0);
            assert_eq!(machine.captured_cells, 0);
            machine
                .acquire_resource(node, Environment::new(), integer("7"))
                .unwrap();
            assert_eq!(machine.next_activation, 2);
            let trace = machine.effect_trace.clone();
            assert_eq!(
                machine.interpret_cell(
                    0,
                    OperationId::new(api.ops(), 0),
                    Value::ResourceHandle(ActivationKey(0))
                ),
                Err(RuntimeFailure::InvalidControlState)
            );
            assert_eq!(machine.effect_trace, trace);
        }
    }

    // Keep discard-local frame storage out of the common acquisition caller.
    #[inline(never)]
    fn discard_deep_generic_root(machine: &mut Machine<'_>) {
        let captured = machine.capture_from(0).unwrap();
        assert_eq!(machine.live_resources, 1);
        assert_eq!(machine.captured_cells, 1);
        assert_eq!(captured.frames.len(), 1);
        assert!(matches!(
            &captured.frames[0],
            Frame::ResourceBoundary {
                payload: ResourcePayload::Generic {
                    value: Value::Function(_),
                    ..
                },
                ..
            }
        ));
        let handler = HandlerId::new(0);
        let owner = ResumeId::new(0);
        machine.frames.push(Frame::ClauseBoundary {
            registration: None,
            handler,
            owner,
            continuation: Some(captured),
        });
        machine.discard(handler, owner).unwrap();
        for _ in 0..3 {
            let frame = machine.frames.pop().unwrap();
            machine.return_from(frame, Value::Unit).unwrap();
        }
        assert!(machine.frames.is_empty());
        assert_eq!(machine.live_resources, 0);
        assert_eq!(machine.captured_cells, 0);
        assert_eq!(machine.next_activation, 1);
        let trace = machine.effect_trace.as_deref().unwrap();
        assert_eq!(
            trace,
            &[
                EffectTraceEvent::ResourceAcquired(0),
                EffectTraceEvent::Discard(handler),
                EffectTraceEvent::ResourceReleased(0),
                EffectTraceEvent::ClauseReturned(handler),
            ]
        );
        disposal::check().unwrap();
    }

    #[test]
    fn generic_cell_admitted_function_origin_and_deep_environment_dispose_on_small_stack() {
        let program = effect_program(
            "import @builtin.generic_cell as Cell\ninitial : Unit -> Int\ninitial () = 7\nmain : Unit -> Int\nmain () = resource Cell.Cell<R,(Unit -> Int)> c = initial {\nlet action = Cell.read c\naction ()\n}\n",
        );
        let callable =
            effect_program("main : Unit -> (Unit -> Int)\nmain () = fn(ignored) {\n7\n}\n");
        let Value::Function(template) = Machine::new_effect(&callable).run().unwrap().value else {
            panic!("function")
        };
        std::thread::Builder::new()
            .stack_size(64 * 1024)
            .spawn(move || {
                let node = resource_node(&program);
                for mode in 0..4 {
                    let mut function = template.clone();
                    let span = function.origin.primary_span();
                    function.origin = Origin::Source(span);
                    for depth in 0..crate::core::dialect::CORE_PAYLOAD_DEPTH_LIMIT {
                        function.origin = if depth % 2 == 0 {
                            Origin::Generated {
                                cause: Box::new(function.origin),
                                reason: crate::source::GeneratedReason::TypeChecking,
                            }
                        } else {
                            Origin::Related {
                                primary: Box::new(function.origin),
                                related: vec![span; 4],
                            }
                        };
                    }
                    for index in 0..32_000 {
                        function.environment = function
                            .environment
                            .extend(BinderId::new(index), Value::Unit)
                            .unwrap();
                    }
                    assert_eq!(
                        Arc::strong_count(function.environment.head.as_ref().unwrap()),
                        1
                    );
                    let mut machine = Machine::new_effect(&program);
                    machine
                        .acquire_resource(node, Environment::new(), Value::Function(function))
                        .unwrap();
                    match mode {
                        0 => {
                            let frame = machine.frames.pop().unwrap();
                            machine.return_from(frame, Value::Unit).unwrap();
                            assert_eq!(machine.live_resources, 0);
                        }
                        1 => {
                            let api = machine.resource(node).unwrap().acquisition.api().unwrap();
                            let operand = allocate_heap(
                                &mut machine.heap,
                                HeapCell::Tuple(Box::new([
                                    Value::ResourceHandle(ActivationKey(0)),
                                    Value::Function(template.clone()),
                                ])),
                            )
                            .unwrap();
                            machine
                                .interpret_cell(
                                    0,
                                    OperationId::new(api.ops(), 1),
                                    Value::Location(operand),
                                )
                                .unwrap();
                            assert_eq!(machine.live_resources, 1);
                        }
                        2 => {
                            let scope = disposal::Scope::enter();
                            drop(machine);
                            assert_eq!(
                                scope.finish::<()>(Err(RuntimeFailure::MissingBinding)),
                                Err(RuntimeFailure::MissingBinding)
                            );
                        }
                        _ => discard_deep_generic_root(&mut machine),
                    }
                }
            })
            .unwrap()
            .join()
            .unwrap();
    }

    #[test]
    fn generic_cell_public_polymorphic_acquisition_matches_int_and_bool() {
        let (program, _, _) = crate::core::validate::generic_cell_source_fixture_for_test(
            "import @builtin.generic_cell as Cell\nscope<T> : T -> T\nscope initial = resource Cell.Cell<R,T> c = initial {\nCell.read c\n}\nmain : Unit -> (Int,Bool)\nmain () = (scope 41, scope true)\n",
            None,
        );
        assert_eq!(
            evaluate_effect(&program).unwrap().value.to_string(),
            "(41, true)"
        );
    }

    #[test]
    fn generic_cell_public_polymorphic_acquisition_coexists_with_legacy_helper() {
        let (program, _, _) = crate::core::validate::generic_cell_source_fixture_for_test(
            include_str!("../../tests/fixtures/generic-cell/polymorphic-acquisition-entry.ash"),
            None,
        );
        assert_eq!(evaluate_effect(&program).unwrap().value.to_string(), "7");
    }

    #[test]
    fn generic_cell_write_refusal_retains_prior_strict_operand_effects() {
        let program = effect_program(include_str!(
            "../../tests/fixtures/generic-cell/operand-order-entry.ash"
        ));
        let mut measured = Machine::new_effect(&program);
        measured.instantiation_work = TypeWorkBudget::unbounded();
        let observation = measured.run_loop().unwrap();
        assert_eq!(observation.value.to_string(), "(42, 12)");
        let required = observation.runtime_work;
        let mut cut = None;
        for allowance in 0..required {
            let mut machine = Machine::new_effect(&program);
            machine.instantiation_work = TypeWorkBudget::with_limit(allowance);
            let Err(RuntimeFailure::Report(report)) = machine.run_loop() else {
                continue;
            };
            if !report.primary.resource().is_some_and(|details| {
                details.phase == RuntimePhase::Access
                    && details.cause == ResourceFailureCause::WorkBudgetExhausted
            }) {
                continue;
            }
            let root = |key| {
                machine.frames.iter().find_map(|frame| match frame {
                    Frame::ResourceBoundary {
                        key: actual,
                        payload:
                            ResourcePayload::Generic {
                                value: Value::Integer(value),
                                ..
                            },
                        ..
                    } if actual.0 == key => Some(value.to_string()),
                    _ => None,
                })
            };
            if root(0).as_deref() != Some("12") || root(1).as_deref() != Some("41") {
                continue;
            }
            let trace = machine.effect_trace.as_deref().unwrap();
            assert_eq!(
                trace
                    .iter()
                    .filter(|event| matches!(event, EffectTraceEvent::ResourceWritten(0)))
                    .count(),
                2
            );
            assert!(
                !trace
                    .iter()
                    .any(|event| matches!(event, EffectTraceEvent::ResourceWritten(1)))
            );
            let api = machine
                .frames
                .iter()
                .find_map(|frame| match frame {
                    Frame::ResourceBoundary { node, key, .. } if key.0 == 1 => {
                        machine.resource(*node).unwrap().acquisition.api()
                    }
                    _ => None,
                })
                .unwrap();
            let write = OperationId::new(api.ops(), 1);
            assert_eq!(trace.iter().filter(|event|matches!(event,EffectTraceEvent::Request(operation) if *operation==write)).count(),2,"target request is not published");
            assert_eq!(machine.live_resources, 2);
            assert_eq!(machine.next_activation, 2);
            cut = Some(allowance);
            break;
        }
        let cut = cut.expect("write preparation can refuse after both operand effects");
        for _ in 0..2 {
            let mut exact = Machine::new_effect(&program);
            exact.instantiation_work = TypeWorkBudget::with_limit(required);
            assert_eq!(exact.run_loop().unwrap().value.to_string(), "(42, 12)");
        }
        println!("generic operand-order full work={required}; prewrite refusal allowance={cut}");
    }

    #[test]
    fn generic_cell_replaced_function_root_reports_internal_disposal_failure_after_commit() {
        let program = effect_program(
            "import @builtin.generic_cell as Cell\ninitial : Unit -> Int\ninitial () = 7\nmain : Unit -> Int\nmain () = resource Cell.Cell<R,(Unit -> Int)> c = initial {\nlet action = Cell.read c\naction ()\n}\n",
        );
        let callable =
            effect_program("main : Unit -> (Unit -> Int)\nmain () = fn(ignored) {\n7\n}\n");
        let Value::Function(template) = Machine::new_effect(&callable).run().unwrap().value else {
            panic!("function")
        };
        let mut frontier = (0..512).map(|_| Environment::new()).collect::<Vec<_>>();
        while frontier.len() > 1 {
            let mut next = Vec::new();
            while let Some(right) = frontier.pop() {
                let left = frontier.pop().unwrap();
                let mut function = template.clone();
                function.environment = right;
                next.push(
                    left.extend(BinderId::new(1), Value::Function(function))
                        .unwrap(),
                );
            }
            frontier = next;
        }
        let mut previous = template.clone();
        previous.environment = frontier.pop().unwrap();
        let mut machine = Machine::new_effect(&program);
        let node = resource_node(&program);
        machine
            .acquire_resource(node, Environment::new(), Value::Function(previous))
            .unwrap();
        let operation = OperationId::new(
            machine
                .resource(node)
                .unwrap()
                .acquisition
                .api()
                .unwrap()
                .ops(),
            1,
        );
        let operand = allocate_heap(
            &mut machine.heap,
            HeapCell::Tuple(Box::new([
                Value::ResourceHandle(ActivationKey(0)),
                Value::Function(template.clone()),
            ])),
        )
        .unwrap();
        let report = {
            let scope = disposal::Scope::enter();
            disposal::reset_growth_attempts();
            machine_test_hooks::FAIL_DISPOSAL_GROWTH.set(true);
            assert!(
                machine
                    .interpret_cell(0, operation, Value::Location(operand))
                    .is_ok()
            );
            assert!(
                matches!(&machine.frames[0],Frame::ResourceBoundary { payload:ResourcePayload::Generic { value:Value::Function(function),.. },.. } if function.environment.len()==template.environment.len())
            );
            assert!(machine.effect_trace.as_ref().unwrap().ends_with(&[
                EffectTraceEvent::Request(operation),
                EffectTraceEvent::ResourceWritten(0)
            ]));
            assert!(
                disposal::check().is_err(),
                "next control step cannot execute source code"
            );
            assert_eq!(disposal::growth_attempts(), 1);
            scope.finish(Ok::<_, RuntimeFailure>(())).unwrap_err()
        };
        let RuntimeFailure::Report(report) = report else {
            panic!("internal disposal report")
        };
        let details = report.primary.resource().unwrap();
        assert_eq!(details.phase, RuntimePhase::Teardown);
        assert_eq!(details.resource, RuntimeResource::EnvironmentDisposal);
        assert_eq!(details.cause, ResourceFailureCause::AllocatorRefused);
        assert_eq!(report.cleanup, super::super::CleanupStatus::Incomplete);
        machine_test_hooks::reset();
    }

    #[test]
    fn legacy_cell_invalid_initializer_precedes_capacity_and_metadata_work() {
        let program = resource_program();
        let node = resource_node(&program);
        let mut machine = Machine::new_effect(&program);
        machine.resource_limit = 0;
        machine.instantiation_work = TypeWorkBudget::with_limit(0);
        assert_eq!(
            machine.acquire_resource(node, Environment::new(), Value::Boolean(false)),
            Err(RuntimeFailure::InvalidControlState)
        );
        assert_eq!(machine.next_activation, 0);
        assert!(machine.frames.is_empty());
    }

    #[test]
    fn resource_capacity_is_live_exact_atomic_and_reused_with_fresh_keys() {
        let program = resource_program();
        let node = resource_node(&program);
        let mut machine = Machine::new_effect(&program);
        machine.resource_limit = 1;
        for expected in 0..3 {
            machine
                .acquire_resource(node, Environment::new(), integer("41"))
                .unwrap();
            assert_eq!(machine.live_resources, 1);
            assert_eq!(machine.next_activation, expected + 1);
            let key = match machine.frames.last().unwrap() {
                Frame::ResourceBoundary { key, .. } => *key,
                _ => panic!("cell owner"),
            };
            assert_eq!(key, ActivationKey(expected));
            let events = machine.effect_trace.clone();
            assert!(is_configured_capacity(
                machine
                    .acquire_resource(node, Environment::new(), integer("99"))
                    .unwrap_err(),
                RuntimeFailure::ResourceCapacity,
                RuntimeResource::ResourceOwners
            ));
            assert_eq!(machine.effect_trace, events);
            assert_eq!(machine.live_resources, 1);
            assert_eq!(machine.next_activation, expected + 1);
            let frame = machine.frames.pop().unwrap();
            machine.return_from(frame, integer("42")).unwrap();
            assert_eq!(machine.live_resources, 0);
        }
        assert!(machine.heap.is_empty());
        machine.next_activation = u32::MAX;
        assert!(is_configured_capacity(
            machine
                .acquire_resource(node, Environment::new(), integer("41"))
                .unwrap_err(),
            RuntimeFailure::ResourceCapacity,
            RuntimeResource::ActivationKeys
        ));
        assert!(machine.frames.is_empty());
        assert_eq!(machine.live_resources, 0);
    }

    #[test]
    fn full_source_reuses_capacity_with_retained_unused_handle_environment() {
        let program = effect_program(
            "import @builtin.cell as Cell\nmain : Unit -> Int\nmain () = {\nlet later = resource cell<R> c = 41 {\nlet copied = Cell.read c\nlet result : Unit -> Int = fn(ignored) {\ncopied + 1\n}\nresult\n}\nresource cell<S> other = 10 {\nlet _ = Cell.write (other, 99)\nlater ()\n}\n}\n",
        );
        for _ in 0..2 {
            let mut machine = Machine::new_effect(&program);
            machine.resource_limit = 1;
            let result = machine.run().unwrap();
            assert_eq!(result.value.to_string(), "42");
            let owners = result
                .effect_trace()
                .iter()
                .filter(|event| {
                    matches!(
                        event,
                        EffectTraceEvent::ResourceAcquired(_)
                            | EffectTraceEvent::ResourceReleased(_)
                    )
                })
                .cloned()
                .collect::<Vec<_>>();
            assert_eq!(
                owners,
                [
                    EffectTraceEvent::ResourceAcquired(0),
                    EffectTraceEvent::ResourceReleased(0),
                    EffectTraceEvent::ResourceAcquired(1),
                    EffectTraceEvent::ResourceReleased(1)
                ]
            );
        }
    }

    #[test]
    fn resource_context_preflight_publishes_no_partial_acquisition() {
        let program = resource_program();
        let node = resource_node(&program);
        let mut measured = Machine::new_effect(&program);
        measured
            .acquire_resource(node, Environment::new(), integer("41"))
            .unwrap();
        let work = measured.instantiation_work.used();
        assert!(work > 0);
        for remaining in [work - 1, work, work] {
            let mut machine = Machine::new_effect(&program);
            machine.instantiation_work = TypeWorkBudget::with_limit(remaining);
            let result = machine.acquire_resource(node, Environment::new(), integer("41"));
            if remaining < work {
                assert!(is_work_exhaustion(result.unwrap_err()));
                assert_eq!(machine.live_resources, 0);
                assert_eq!(machine.next_activation, 0);
                assert!(machine.frames.is_empty());
                assert!(machine.effect_trace.as_ref().unwrap().is_empty());
                assert!(matches!(machine.control, Some(Control::Evaluate(_, _))));
            } else {
                result.unwrap();
                assert_eq!(machine.live_resources, 1);
                assert_eq!(machine.next_activation, 1);
            }
        }
        let mut machine = Machine::new_effect(&program);
        let environment = Environment {
            len: usize::MAX,
            ..Environment::new()
        };
        assert!(is_configured_capacity(
            machine
                .acquire_resource(node, environment, integer("41"))
                .unwrap_err(),
            RuntimeFailure::EnvironmentCapacity,
            RuntimeResource::EnvironmentBindings
        ));
        assert_eq!(machine.live_resources, 0);
        assert_eq!(machine.next_activation, 0);
        assert!(machine.frames.is_empty());
    }

    #[test]
    fn final_observation_rejects_unreleased_ownership_accounting() {
        let program = resource_program();
        for (live_resources, captured_cells) in [(1, 0), (0, 1)] {
            let mut machine = Machine::new_effect(&program);
            machine.live_resources = live_resources;
            machine.captured_cells = captured_cells;
            machine.control = Some(Control::Return(Value::Unit));
            assert!(matches!(
                machine.run(),
                Err(RuntimeFailure::InvalidControlState)
            ));
        }
    }

    #[test]
    fn captured_resource_counts_until_normal_or_owned_release() {
        for discard in [false, true] {
            let program = resource_program();
            let node = resource_node(&program);
            let mut machine = Machine::new_effect(&program);
            machine.resource_limit = 1;
            machine
                .acquire_resource(node, Environment::new(), integer("41"))
                .unwrap();
            machine.capture_limit = 0;
            assert!(matches!(
                machine.capture_from(0),
                Err(failure) if is_configured_capacity(failure, RuntimeFailure::CapturedControlCapacity, RuntimeResource::FrameStorage)
            ));
            assert_eq!(machine.frames.len(), 1);
            machine.capture_limit = 1;
            let captured = machine.capture_from(0).unwrap();
            assert_eq!(machine.live_resources, 1);
            assert_eq!(machine.captured_cells, 1);
            assert!(is_configured_capacity(
                machine
                    .acquire_resource(node, Environment::new(), integer("99"))
                    .unwrap_err(),
                RuntimeFailure::ResourceCapacity,
                RuntimeResource::ResourceOwners
            ));
            let handler = HandlerId::new(0);
            let owner = ResumeId::new(0);
            machine.frames.push(Frame::ClauseBoundary {
                registration: None,
                handler,
                owner,
                continuation: Some(captured),
            });
            if discard {
                machine.discard(handler, owner).unwrap();
                assert_eq!(machine.captured_cells, 0);
                assert_eq!(machine.live_resources, 1);
            } else {
                let Frame::ClauseBoundary {
                    continuation: Some(mut captured),
                    ..
                } = machine.frames.pop().unwrap()
                else {
                    panic!("retained capture")
                };
                machine.frames.append(&mut captured.frames);
                machine.captured_cells = 0;
            }
            let frame = machine.frames.pop().unwrap();
            machine
                .return_from(frame, if discard { Value::Unit } else { integer("42") })
                .unwrap();
            assert_eq!(machine.live_resources, 0);
            if discard {
                let frame = machine.frames.pop().unwrap();
                assert!(matches!(frame, Frame::CloseCompletion));
                machine.return_from(frame, Value::Unit).unwrap();
                let frame = machine.frames.pop().unwrap();
                assert!(matches!(
                    frame,
                    Frame::ClauseBoundary {
                        continuation: None,
                        ..
                    }
                ));
                machine.return_from(frame, Value::Unit).unwrap();
            }
            machine
                .acquire_resource(node, Environment::new(), integer("42"))
                .unwrap();
            assert_eq!(machine.next_activation, 2);
        }
    }

    #[test]
    fn trusted_cell_rejects_wrong_handle_and_operation_before_mutation() {
        let program = resource_program();
        let node = resource_node(&program);
        let mut machine = Machine::new_effect(&program);
        machine
            .acquire_resource(node, Environment::new(), integer("41"))
            .unwrap();
        let api = machine.resource(node).unwrap().acquisition.api().unwrap();
        let read = OperationId::new(api.ops(), 0);
        let write = OperationId::new(api.ops(), 1);
        for operation in [read, write, OperationId::new(api.ops(), 2)] {
            let value = if operation == write {
                Value::Location(
                    allocate_heap(
                        &mut machine.heap,
                        HeapCell::Tuple(Box::new([
                            Value::ResourceHandle(ActivationKey(1)),
                            integer("99"),
                        ])),
                    )
                    .unwrap(),
                )
            } else {
                Value::ResourceHandle(ActivationKey(1))
            };
            assert_eq!(
                machine.interpret_cell(0, operation, value),
                Err(RuntimeFailure::InvalidControlState)
            );
            assert!(
                matches!(&machine.frames[0], Frame::ResourceBoundary { payload: ResourcePayload::Cell(cell), .. } if cell.to_string() == "41")
            );
        }
        machine
            .interpret_cell(0, read, Value::ResourceHandle(ActivationKey(0)))
            .unwrap();
        assert!(
            matches!(&machine.control, Some(Control::Return(Value::Integer(cell))) if cell.to_string() == "41")
        );
    }

    #[test]
    fn deep_resource_completion_and_failed_capture_disposal_use_a_small_stack() {
        let program = resource_program();
        std::thread::Builder::new()
            .stack_size(256 * 1024)
            .spawn(move || {
                let node = resource_node(&program);
                const DEPTH: usize = 32_000;
                let mut normal = Machine::new_effect(&program);
                normal.resource_limit = DEPTH;
                for _ in 0..DEPTH {
                    normal
                        .acquire_resource(node, Environment::new(), integer("41"))
                        .unwrap();
                }
                assert_eq!(normal.live_resources, DEPTH);
                normal.control = Some(Control::Return(integer("42")));
                let completed = normal.run().unwrap();
                assert_eq!(completed.value.to_string(), "42");
                assert_eq!(
                    completed
                        .effect_trace()
                        .iter()
                        .filter(|event| matches!(event, EffectTraceEvent::ResourceReleased(_)))
                        .count(),
                    DEPTH
                );
                let mut failure = Machine::new_effect(&program);
                let mut captured = CapturedContinuation { frames: Vec::new() };
                for key in 0..DEPTH {
                    captured = CapturedContinuation {
                        frames: vec![
                            Frame::ResourceBoundary {
                                node,
                                key: ActivationKey(key as u32),
                                payload: ResourcePayload::Cell(
                                    Integer::parse_decimal("41").unwrap(),
                                ),
                            },
                            Frame::ClauseBoundary {
                                registration: None,
                                handler: HandlerId::new(0),
                                owner: ResumeId::new(0),
                                continuation: Some(captured),
                            },
                        ],
                    };
                }
                failure.frames.push(Frame::ClauseBoundary {
                    registration: None,
                    handler: HandlerId::new(0),
                    owner: ResumeId::new(0),
                    continuation: Some(captured),
                });
                failure.live_resources = DEPTH;
                failure.captured_cells = DEPTH * 2;
                failure.control = Some(Control::Return(Value::Unit));
                assert!(matches!(
                    failure.run(),
                    Err(RuntimeFailure::InvalidControlState)
                ));
            })
            .unwrap()
            .join()
            .unwrap();
    }

    #[test]
    fn resource_free_pure_execution_retains_no_resource_state() {
        let source = SourceFile::new("pure-resource-locality", "42").unwrap();
        let origin = Origin::Source(source.span(ByteRange::new(0, 2).unwrap()).unwrap());
        let mut builder = CoreBuilder::new();
        let root = builder
            .integer(Integer::parse_decimal("42").unwrap(), Type::Int, origin)
            .unwrap();
        let program = validate(builder.finish(root).unwrap(), &[&source]).unwrap();
        let machine = Machine::new(&program);
        assert_eq!(machine.resource_limit, 0);
        assert_eq!(machine.registration_limit, 0);
        assert_eq!(machine.live_registrations, 0);
        assert_eq!(machine.next_registration, 0);
        assert!(machine.work_trace.is_none());
        assert_eq!(machine.live_resources, 0);
        assert_eq!(machine.next_activation, 0);
        assert!(machine.frames.is_empty());
        assert!(machine.effect_trace.is_none());
        assert!(machine.heap.is_empty());
        let evaluation = machine.run().unwrap();
        assert_eq!(evaluation.value.to_string(), "42");
        assert!(evaluation.effect_trace().is_empty());
        assert_eq!(evaluation.heap.cell_count(), 0);
    }

    fn capture_machine(limit: usize) -> Machine<'static> {
        let source = SourceFile::new("capture-budget.ash", "()").expect("test source");
        let origin = Origin::Source(
            source
                .span(ByteRange::new(0, 2).expect("ordered range"))
                .expect("source span"),
        );
        let mut builder = EffectCoreBuilder::with_effect_registry(Arc::new(ResolvedRegistry::new(
            Vec::new(),
            Vec::new(),
        )));
        let root = builder.unit(Type::Unit, origin).expect("unit should fit");
        let program = validate_effect(
            builder.finish(root).expect("Core should finish"),
            &[&source],
        )
        .expect("Core should validate");
        let mut machine = Machine::new_effect_with_capture_limit(&program, limit);
        machine.frames.extend((0..3).map(|_| Frame::Request {
            node: root,
            instantiation: Instantiation::default(),
        }));
        machine
    }

    #[test]
    fn captured_control_quota_is_exact_atomic_retryable_and_iteratively_disposed() {
        let source = SourceFile::new("pure-capture-budget.ash", "()").expect("test source");
        let origin = Origin::Source(
            source
                .span(ByteRange::new(0, 2).expect("ordered range"))
                .expect("source span"),
        );
        let mut builder = CoreBuilder::new();
        let root = builder.unit(Type::Unit, origin).expect("unit should fit");
        let program = validate(
            builder.finish(root).expect("Core should finish"),
            &[&source],
        )
        .expect("Core should validate");
        let mut pure = Machine::new(&program);
        pure.frames.push(Frame::Request {
            node: root,
            instantiation: Instantiation::default(),
        });
        assert!(is_configured_capacity(
            pure.capture_from(0).expect_err("Pure cannot capture"),
            RuntimeFailure::CapturedControlCapacity,
            RuntimeResource::FrameStorage
        ));
        assert_eq!(pure.frames.len(), 1);
        assert_eq!(pure.captured_cells, 0);

        let mut one_short = capture_machine(2);
        assert!(is_configured_capacity(
            one_short.capture_from(0).expect_err("one short must fail"),
            RuntimeFailure::CapturedControlCapacity,
            RuntimeResource::FrameStorage
        ));
        assert_eq!(one_short.frames.len(), 3);
        assert_eq!(one_short.captured_cells, 0);

        for _ in 0..2 {
            let mut exact = capture_machine(3);
            let continuation = exact.capture_from(0).expect("exact quota should fit");
            assert!(exact.frames.is_empty());
            assert_eq!(exact.captured_cells, 3);
            let node = match exact.control.as_ref() {
                Some(Control::Evaluate(node, _)) => *node,
                _ => unreachable!("fixture begins by evaluating its root"),
            };
            exact.frames.push(Frame::Request {
                node,
                instantiation: Instantiation::default(),
            });
            assert!(is_configured_capacity(
                exact.capture_from(0).expect_err("cumulative quota is full"),
                RuntimeFailure::CapturedControlCapacity,
                RuntimeResource::FrameStorage
            ));
            assert_eq!(exact.frames.len(), 1);
            assert_eq!(exact.captured_cells, 3);
            drop(continuation);
        }

        std::thread::Builder::new()
            .stack_size(64 * 1024)
            .spawn(|| {
                let mut continuation = CapturedContinuation { frames: Vec::new() };
                for depth in 0..32_768_u32 {
                    continuation = CapturedContinuation {
                        frames: vec![Frame::ClauseBoundary {
                            registration: None,
                            handler: HandlerId::new(depth),
                            owner: ResumeId::new(depth),
                            continuation: Some(continuation),
                        }],
                    };
                }
                drop(continuation);
            })
            .expect("small-stack teardown should spawn")
            .join()
            .expect("captured control should drop iteratively");
    }

    #[test]
    fn sequential_requests_reclaim_the_exact_effect_capture_quota() {
        let program = sequential_effect_program();
        assert!(matches!(
            Machine::new_effect_with_capture_limit(&program, 1).run(),
            Err(failure) if is_configured_capacity(failure, RuntimeFailure::CapturedControlCapacity, RuntimeResource::FrameStorage)
        ));

        let evaluation = Machine::new_effect_with_capture_limit(&program, 2)
            .run()
            .expect("exact quota should serve both sequential requests");
        assert_eq!(evaluation.value.to_string(), "3");
        assert_eq!(
            evaluation
                .effect_trace()
                .iter()
                .filter(|event| matches!(event, EffectTraceEvent::Request(_)))
                .count(),
            2
        );
        assert_eq!(
            evaluation
                .effect_trace()
                .iter()
                .filter(|event| matches!(event, EffectTraceEvent::Resume(_)))
                .count(),
            2
        );
    }

    #[test]
    fn sequential_discards_release_the_exact_capture_quota_for_fresh_requests() {
        let program = effect_program(concat!(
            "effect Ask {\nask : Unit -> Int\n}\n\n",
            "main : Unit -> Int\nmain () = {\n",
            "let first = handle (perform Ask.ask () + 100) with Ask {\n",
            "ask ignored => {\nlet _ = discard\n41\n}\n}\n",
            "handle (perform Ask.ask () + 100) with Ask {\n",
            "ask ignored => {\nlet _ = discard\nfirst + 1\n}\n}\n}\n",
        ));
        assert!(matches!(
            Machine::new_effect_with_capture_limit(&program, 1).run(),
            Err(failure) if is_configured_capacity(failure, RuntimeFailure::CapturedControlCapacity, RuntimeResource::FrameStorage)
        ));
        for _ in 0..2 {
            let evaluation = Machine::new_effect_with_capture_limit(&program, 2)
                .run()
                .expect("exact quota should be reused after discard");
            assert_eq!(evaluation.value.to_string(), "42");
            assert_eq!(
                evaluation
                    .effect_trace()
                    .iter()
                    .filter(|event| matches!(event, EffectTraceEvent::Discard(_)))
                    .count(),
                2
            );
        }
    }

    #[test]
    fn discard_releases_only_its_segment_and_preserves_clause_control() {
        let handler = HandlerId::new(0);
        let owner = ResumeId::new(0);
        let mut machine = capture_machine(4);
        let root = machine.program.root();
        // One retained cell belongs to an independent outer live owner.
        machine.captured_cells = 1;
        let captured = machine.capture_from(0).expect("exact remaining quota");
        machine.frames.push(Frame::ClauseBoundary {
            registration: None,
            handler: HandlerId::new(1),
            owner: ResumeId::new(1),
            continuation: Some(CapturedContinuation {
                frames: vec![Frame::Request {
                    node: root,
                    instantiation: Instantiation::default(),
                }],
            }),
        });
        machine.frames.push(Frame::ClauseBoundary {
            registration: None,
            handler,
            owner,
            continuation: Some(captured),
        });
        machine.frames.push(Frame::Request {
            node: root,
            instantiation: Instantiation::default(),
        });
        machine
            .discard(handler, owner)
            .expect("discard should release its three cells");
        assert_eq!(machine.captured_cells, 1);
        assert_eq!(machine.frames.len(), 3);
        assert!(matches!(
            machine.frames[0],
            Frame::ClauseBoundary {
                continuation: Some(_),
                ..
            }
        ));
        assert!(matches!(
            machine.frames[1],
            Frame::ClauseBoundary {
                continuation: None,
                ..
            }
        ));
        assert!(matches!(machine.frames[2], Frame::Request { .. }));
        assert!(matches!(
            machine.control,
            Some(Control::Return(Value::Unit))
        ));
        assert_eq!(
            machine.effect_trace.as_deref(),
            Some([EffectTraceEvent::Discard(handler)].as_slice())
        );
        assert_eq!(
            machine.discard(handler, owner),
            Err(RuntimeFailure::InvalidControlState)
        );
        assert_eq!(machine.captured_cells, 1);
        assert_eq!(
            machine
                .capture_from(2)
                .expect("released quota can be reused")
                .frames
                .len(),
            1
        );
    }

    #[test]
    fn discard_rejects_consumed_clause_with_outside_registration_before_consumption() {
        let handler = HandlerId::new(0);
        let owner = ResumeId::new(0);
        let key = RegistrationKey(0);
        let mut machine = capture_machine(2);
        let root = machine.program.root();
        machine.frames.clear();
        machine.frames.push(Frame::RegistrationBoundary {
            key,
            handler: root,
            callback: Value::Unit,
            handler_active: false,
            pending_invocations: 1,
        });
        machine.frames.push(Frame::ClauseBoundary {
            handler: HandlerId::new(1),
            owner: ResumeId::new(1),
            continuation: None,
            registration: Some(key),
        });
        machine.frames.push(Frame::CleanupBoundary {
            action: root,
            environment: Environment::new(),
        });
        machine.live_registrations = 1;
        machine.live_cleanups = 1;
        let captured = machine.capture_from(1).unwrap();
        machine.frames.push(Frame::ClauseBoundary {
            handler,
            owner,
            continuation: Some(captured),
            registration: None,
        });
        machine.control = Some(Control::Discard(handler, owner));

        for _ in 0..2 {
            assert_eq!(
                machine.discard(handler, owner),
                Err(RuntimeFailure::InvalidControlState)
            );
            assert_eq!(machine.captured_cells, 2);
            assert_eq!(machine.live_registrations, 1);
            assert_eq!(machine.live_cleanups, 1);
            assert_eq!(machine.frames.len(), 2);
            assert!(matches!(
                machine.frames[0],
                Frame::RegistrationBoundary {
                    key: found,
                    handler_active: false,
                    pending_invocations: 1,
                    ..
                } if found == key
            ));
            let Frame::ClauseBoundary {
                continuation: Some(captured),
                ..
            } = &machine.frames[1]
            else {
                panic!("rejected discard must retain its capability")
            };
            assert!(matches!(
                captured.frames.as_slice(),
                [Frame::ClauseBoundary {
                    continuation: None,
                    registration: Some(found),
                    ..
                }, Frame::CleanupBoundary { action, .. }]
                    if *found == key && *action == root
            ));
            assert!(
                matches!(machine.control, Some(Control::Discard(found, resume))
                if found == handler && resume == owner)
            );
            assert!(machine.trace.is_empty());
            assert!(machine.effect_trace.as_ref().unwrap().is_empty());
        }
    }

    #[test]
    fn malformed_discard_checks_owner_nested_obligations_and_accounting_before_consuming() {
        let handler = HandlerId::new(0);
        let owner = ResumeId::new(0);
        for (nested, retained, found_handler, found_owner) in [
            (true, 3, handler, owner),
            (true, 4, handler, owner),
            (false, 2, handler, owner),
            (false, 3, HandlerId::new(1), owner),
            (false, 3, handler, ResumeId::new(1)),
        ] {
            let mut machine = capture_machine(4);
            let mut captured = machine.capture_from(0).expect("capture fits");
            if nested {
                captured.frames[1] = Frame::ClauseBoundary {
                    registration: None,
                    handler: HandlerId::new(1),
                    owner: ResumeId::new(1),
                    continuation: Some(CapturedContinuation {
                        frames: if retained == 4 {
                            vec![Frame::CloseCompletion]
                        } else {
                            Vec::new()
                        },
                    }),
                };
            }
            machine.captured_cells = retained;
            machine.frames.push(Frame::ClauseBoundary {
                registration: None,
                handler: found_handler,
                owner: found_owner,
                continuation: Some(captured),
            });
            if nested && retained == 3 {
                machine.discard(handler, owner).unwrap();
                assert_eq!(machine.captured_cells, 0);
                assert!(matches!(
                    machine.frames[0],
                    Frame::ClauseBoundary {
                        continuation: None,
                        ..
                    }
                ));
                continue;
            }
            assert_eq!(
                machine.discard(handler, owner),
                Err(RuntimeFailure::InvalidControlState)
            );
            assert_eq!(machine.captured_cells, retained);
            let Frame::ClauseBoundary {
                continuation: Some(captured),
                ..
            } = &machine.frames[0]
            else {
                panic!("failed discard consumed its owner")
            };
            assert_eq!(captured.frames.len(), 3);
            assert_eq!(
                matches!(
                    captured.frames[1],
                    Frame::ClauseBoundary {
                        continuation: Some(_),
                        ..
                    }
                ),
                nested
            );
            assert!(
                machine
                    .effect_trace
                    .as_ref()
                    .expect("effect trace")
                    .is_empty()
            );
            assert!(matches!(machine.control, Some(Control::Evaluate(_, _))));
        }
    }

    #[test]
    fn deep_discard_success_and_malformed_failure_drop_on_a_small_stack() {
        std::thread::Builder::new()
            .stack_size(64 * 1024)
            .spawn(|| {
                const DEPTH: usize = 32_768;
                let handler = HandlerId::new(0);
                let owner = ResumeId::new(0);
                for (live_nested, malformed) in
                    [(false, false), (true, false), (true, true), (false, false)]
                {
                    let mut machine = capture_machine(DEPTH);
                    machine.frames.clear();
                    let mut captured = CapturedContinuation { frames: Vec::new() };
                    for _ in 0..DEPTH {
                        if live_nested {
                            captured = CapturedContinuation {
                                frames: vec![Frame::ClauseBoundary {
                                    registration: None,
                                    handler,
                                    owner,
                                    continuation: Some(captured),
                                }],
                            };
                        } else {
                            captured.frames.push(Frame::ClauseBoundary {
                                registration: None,
                                handler,
                                owner,
                                continuation: None,
                            });
                        }
                    }
                    if live_nested {
                        machine.captured_cells = if malformed { DEPTH - 1 } else { DEPTH };
                    } else {
                        machine.frames.append(&mut captured.frames);
                        machine.capture_limit = DEPTH - 1;
                        assert!(is_configured_capacity(
                            machine.capture_from(0).expect_err("one cell short"),
                            RuntimeFailure::CapturedControlCapacity,
                            RuntimeResource::FrameStorage
                        ));
                        assert_eq!(machine.frames.len(), DEPTH);
                        assert_eq!(machine.captured_cells, 0);
                        machine.capture_limit = DEPTH;
                        captured = machine.capture_from(0).expect("exact retry fits");
                        assert_eq!(machine.captured_cells, DEPTH);
                        assert!(machine.frames.is_empty());
                    }
                    machine.frames.push(Frame::ClauseBoundary {
                        registration: None,
                        handler,
                        owner,
                        continuation: Some(captured),
                    });
                    machine.control = Some(Control::Discard(handler, owner));
                    let result = machine.run();
                    if malformed {
                        assert!(matches!(result, Err(RuntimeFailure::InvalidControlState)));
                    } else {
                        let evaluation =
                            result.expect("consumed boundaries do not prohibit discard");
                        assert!(matches!(evaluation.value, Value::Unit));
                        assert_eq!(
                            evaluation.effect_trace(),
                            [
                                EffectTraceEvent::Discard(handler),
                                EffectTraceEvent::ClauseReturned(handler)
                            ]
                        );
                    }
                }
            })
            .expect("small-stack discard worker should spawn")
            .join()
            .expect("successful and failed discard must drop iteratively");
    }

    #[test]
    fn discard_does_not_skip_a_consumed_nearer_activation_of_the_same_owner() {
        let handler = HandlerId::new(0);
        let owner = ResumeId::new(0);
        let mut machine = capture_machine(3);
        let captured = machine.capture_from(0).expect("capture fits");
        machine.frames.push(Frame::ClauseBoundary {
            registration: None,
            handler,
            owner,
            continuation: Some(captured),
        });
        machine.frames.push(Frame::ClauseBoundary {
            registration: None,
            handler,
            owner,
            continuation: None,
        });
        assert_eq!(
            machine.discard(handler, owner),
            Err(RuntimeFailure::InvalidControlState)
        );
        assert_eq!(machine.captured_cells, 3);
        assert!(matches!(
            machine.frames[0],
            Frame::ClauseBoundary {
                continuation: Some(_),
                ..
            }
        ));
        assert!(
            machine
                .effect_trace
                .as_ref()
                .expect("effect trace")
                .is_empty()
        );
    }

    struct TransitionOwner {
        feature: &'static str,
        entry: &'static str,
        frames: &'static [&'static str],
        returns: &'static [&'static str],
    }

    const TRANSITION_OWNERSHIP: &[TransitionOwner] = &[
        TransitionOwner {
            feature: "integer",
            entry: "enter_integer",
            frames: &[],
            returns: &[],
        },
        TransitionOwner {
            feature: "boolean",
            entry: "enter_boolean",
            frames: &[],
            returns: &[],
        },
        TransitionOwner {
            feature: "unit",
            entry: "enter_unit",
            frames: &[],
            returns: &[],
        },
        TransitionOwner {
            feature: "function",
            entry: "enter_function",
            frames: &[],
            returns: &[],
        },
        TransitionOwner {
            feature: "constructor",
            entry: "enter_constructor",
            frames: &[],
            returns: &[],
        },
        TransitionOwner {
            feature: "variable",
            entry: "enter_variable",
            frames: &[],
            returns: &[],
        },
        TransitionOwner {
            feature: "binding",
            entry: "enter_binding",
            frames: &["Frame::Bind"],
            returns: &["return_binding"],
        },
        TransitionOwner {
            feature: "recursive binding",
            entry: "enter_recursive_binding",
            frames: &["Frame::InitializeRecursive"],
            returns: &["return_recursive_initialization"],
        },
        TransitionOwner {
            feature: "application",
            entry: "enter_application",
            frames: &["Frame::ApplyFunction", "Frame::ApplyArgument"],
            returns: &["return_application_function", "return_application_argument"],
        },
        TransitionOwner {
            feature: "primitive",
            entry: "enter_primitive",
            frames: &["Frame::PrimitiveLeft", "Frame::PrimitiveRight"],
            returns: &["return_primitive_left", "return_primitive_right"],
        },
        TransitionOwner {
            feature: "tuple",
            entry: "enter_tuple",
            frames: &["Frame::Tuple"],
            returns: &["return_tuple"],
        },
        TransitionOwner {
            feature: "match",
            entry: "enter_match",
            frames: &["Frame::Match"],
            returns: &["return_match"],
        },
        TransitionOwner {
            feature: "type abstraction",
            entry: "enter_type_abstraction",
            frames: &[],
            returns: &[],
        },
        TransitionOwner {
            feature: "type application",
            entry: "enter_type_application",
            frames: &[],
            returns: &[],
        },
    ];

    const EFFECT_TRANSITION_OWNERSHIP: &[TransitionOwner] = &[
        TransitionOwner {
            feature: "cleanup",
            entry: "Machine::acquire_cleanup",
            frames: &["Frame::CleanupBoundary", "Frame::CleanupCompletion"],
            // Both frame-return transitions belong to separate arms of this method.
            returns: &["Machine::return_from", "Machine::return_from"],
        },
        TransitionOwner {
            feature: "registration",
            entry: "Machine::acquire_registration",
            frames: &["Frame::RegistrationBoundary"],
            returns: &["Machine::return_from"],
        },
        TransitionOwner {
            feature: "resource",
            entry: "dispatch_entry",
            frames: &["Frame::ResourceInitializer", "Frame::ResourceBoundary"],
            returns: &["Machine::acquire_resource", "Machine::return_from"],
        },
        TransitionOwner {
            feature: "handler",
            entry: "dispatch_entry",
            frames: &["Frame::HandlerBoundary"],
            returns: &["Machine::return_from"],
        },
        TransitionOwner {
            feature: "request",
            entry: "dispatch_entry",
            frames: &["Frame::Request"],
            returns: &["Machine::return_request"],
        },
        TransitionOwner {
            feature: "resume",
            entry: "dispatch_entry",
            frames: &["Frame::Resume"],
            returns: &["Machine::return_resume"],
        },
        TransitionOwner {
            feature: "discard",
            entry: "Machine::discard",
            frames: &[],
            returns: &[],
        },
        TransitionOwner {
            feature: "clause boundary",
            entry: "Machine::return_request",
            frames: &["Frame::ClauseBoundary"],
            returns: &["Machine::return_from"],
        },
    ];

    mod mock_pure_feature {
        use super::{Control, Transition, Value};

        pub struct MockNode;

        pub fn enter(_node: &MockNode) -> Transition {
            Transition::direct(Control::Return(Value::Unit))
        }
    }

    enum ShadowEntry<'a> {
        Existing(&'a PureExprKind),
        Mock(&'a mock_pure_feature::MockNode),
    }

    fn dispatch_shadow_entry(entry: ShadowEntry<'_>) -> &'static str {
        match entry {
            ShadowEntry::Existing(kind) => match kind {
                PureExprKind::Value(_) => "existing value helper",
                PureExprKind::Variable(_) => "existing variable helper",
                PureExprKind::Computation(_) => "existing computation helper",
            },
            ShadowEntry::Mock(node) => {
                let _ = mock_pure_feature::enter(node);
                "mock feature helper"
            }
        }
    }

    #[test]
    fn every_core_feature_has_one_named_entry_owner_and_explicit_return_owners() {
        type EnterRecursive = fn(
            &ExecutableProgram,
            &crate::core::recursion::RecursiveBindingNode,
            Environment,
            &mut Vec<HeapCell>,
        ) -> Result<Transition, RuntimeFailure>;
        type EnterConstructor = fn(
            &ExecutableProgram,
            crate::core::data::ConstructorNode,
            &mut Vec<HeapCell>,
        ) -> Result<Transition, RuntimeFailure>;
        type ReturnTuple = fn(
            Box<[NodeId]>,
            usize,
            Vec<Value>,
            Environment,
            Value,
            &mut Vec<HeapCell>,
        ) -> Result<Transition, RuntimeFailure>;
        type ReturnMatch = fn(
            Box<[CoreMatchArm]>,
            Environment,
            Value,
            &[HeapCell],
        ) -> Result<Transition, RuntimeFailure>;
        type ReturnRecursiveInitialization = fn(
            Box<[(Location, NodeId)]>,
            usize,
            NodeId,
            Environment,
            Value,
            &mut [HeapCell],
        ) -> Result<Transition, RuntimeFailure>;

        let _: fn(&IntegerNode) -> Transition = enter_integer;
        let _: fn(BooleanNode) -> Transition = enter_boolean;
        let _: fn(UnitNode) -> Transition = enter_unit;
        let _: fn(
            &FunctionNode,
            ExecutableProgram,
            Environment,
            crate::source::Origin,
        ) -> Transition = enter_function;
        let _: EnterConstructor = enter_constructor;
        let _: fn(
            &ExecutableProgram,
            VariableNode,
            Environment,
        ) -> Result<Transition, RuntimeFailure> = enter_variable;
        let _: fn(&BindingNode, Environment) -> Transition = enter_binding;
        let _: EnterRecursive = enter_recursive_binding;
        let _: fn(ApplicationNode, Environment) -> Transition = enter_application;
        let _: fn(PrimitiveNode, Environment) -> Transition = enter_primitive;
        let _: fn(
            &crate::core::data::TupleNode,
            Environment,
        ) -> Result<Transition, RuntimeFailure> = enter_tuple;
        let _: fn(&crate::core::data::MatchNode, Environment) -> Transition = enter_match;
        let _: fn(&TypeAbstractionNode, Environment) -> Transition = enter_type_abstraction;
        let _: fn(&TypeApplicationNode, Environment) -> Transition = enter_type_application;
        let _: fn(BinderId, NodeId, Environment, Value) -> Result<Transition, RuntimeFailure> =
            return_binding;
        let _: fn(Primitive, NodeId, Environment, Value) -> Transition = return_primitive_left;
        let _: fn(Primitive, Value, Value) -> Result<Transition, RuntimeFailure> =
            return_primitive_right;
        let _: fn(NodeId, Environment, Value) -> Result<Transition, RuntimeFailure> =
            return_application_function;
        let _: fn(Value, Value, &mut Vec<HeapCell>) -> Result<Transition, RuntimeFailure> =
            return_application_argument;
        let _: ReturnTuple = return_tuple;
        let _: ReturnMatch = return_match;
        let _: ReturnRecursiveInitialization = return_recursive_initialization;

        assert_eq!(TRANSITION_OWNERSHIP.len(), 14);
        assert_eq!(
            TRANSITION_OWNERSHIP
                .iter()
                .map(|owner| owner.feature)
                .collect::<Vec<_>>(),
            [
                "integer",
                "boolean",
                "unit",
                "function",
                "constructor",
                "variable",
                "binding",
                "recursive binding",
                "application",
                "primitive",
                "tuple",
                "match",
                "type abstraction",
                "type application",
            ]
        );
        assert!(
            TRANSITION_OWNERSHIP
                .iter()
                .all(|owner| !owner.entry.is_empty())
        );
        for owner in TRANSITION_OWNERSHIP {
            assert_eq!(owner.frames.is_empty(), owner.returns.is_empty());
        }
    }

    #[test]
    fn every_effect_operation_has_one_explicit_transition_owner() {
        assert_eq!(TRANSITION_OWNERSHIP.len(), 14);
        assert_eq!(EFFECT_TRANSITION_OWNERSHIP.len(), 8);
        assert_eq!(
            EFFECT_TRANSITION_OWNERSHIP
                .iter()
                .map(|owner| owner.feature)
                .collect::<Vec<_>>(),
            [
                "cleanup",
                "registration",
                "resource",
                "handler",
                "request",
                "resume",
                "discard",
                "clause boundary"
            ]
        );
        assert!(EFFECT_TRANSITION_OWNERSHIP.iter().all(|owner| {
            !owner.entry.is_empty()
                && owner.frames.len()
                    == match owner.feature {
                        "resource" | "source resource" | "source copy window" | "cleanup" => 2,
                        "discard" => 0,
                        _ => 1,
                    }
                && owner.returns.len() == owner.frames.len()
        }));
    }

    #[test]
    fn type_erasure_enters_each_explicit_operation_once_without_runtime_state() {
        let source = SourceFile::new("type-erasure-trace.ash", "42").expect("test source");
        let origin = Origin::Source(
            source
                .span(ByteRange::new(0, 2).expect("ordered range"))
                .expect("source span"),
        );
        let parameter = TypeVariableId::new(0);
        let mut builder = CoreBuilder::new();
        let body = builder
            .integer(
                Integer::parse_decimal("42").expect("valid integer"),
                Type::Int,
                origin.clone(),
            )
            .expect("integer should fit");
        let abstraction = builder
            .type_abstraction(
                vec![(parameter, crate::types::Kind::Type)],
                body,
                Type::Forall(
                    vec![(parameter, crate::types::Kind::Type)].into_boxed_slice(),
                    Box::new(Type::Int),
                ),
                origin.clone(),
            )
            .expect("type abstraction should fit");
        let application = builder
            .type_application(abstraction, vec![Type::Unit], Type::Int, origin)
            .expect("type application should fit");
        let validated = validate(
            builder
                .finish(application)
                .expect("type application root should finish"),
            &[&source],
        )
        .expect("type-operation Core should validate");

        let evaluation = evaluate(&validated).expect("type operations should erase");

        assert_eq!(evaluation.value.to_string(), "42");
        assert_eq!(evaluation.heap.cell_count(), 0);
        assert_eq!(evaluation.max_frame_depth, 0);
        assert_eq!(
            evaluation.trace,
            vec![
                TraceEvent::Enter(application),
                TraceEvent::Enter(abstraction),
                TraceEvent::Enter(body),
            ]
        );
    }

    #[test]
    fn a_mock_pure_feature_changes_only_its_transition_helper_and_closed_dispatch() {
        let mock = mock_pure_feature::MockNode;
        assert_eq!(
            dispatch_shadow_entry(ShadowEntry::Mock(&mock)),
            "mock feature helper"
        );
        let existing = PureExprKind::Value(PureValue::Unit(UnitNode));
        assert_eq!(
            dispatch_shadow_entry(ShadowEntry::Existing(&existing)),
            "existing value helper"
        );
    }

    #[test]
    fn defensive_transition_failures_remain_structured() {
        let source = SourceFile::new("runtime-failures.ash", "1").expect("test source");
        let origin = Origin::Source(
            source
                .span(ByteRange::new(0, 1).expect("ordered range"))
                .expect("source span"),
        );
        let mut builder = CoreBuilder::new();
        let binder = builder
            .binder(Type::Int, origin.clone())
            .expect("binder should fit");
        let variable = builder
            .variable(binder.id(), Type::Int, origin.clone())
            .expect("variable should fit");
        let function = builder
            .function(
                binder,
                variable,
                Type::Function(Box::new(Type::Int), Box::new(Type::Int)),
                origin,
            )
            .expect("function should fit");
        let validated = validate(
            builder
                .finish(function)
                .expect("function root should finish"),
            &[&source],
        )
        .expect("function Core should validate");
        let program = validated.shared();
        let executable = ExecutableProgram::Pure(Arc::clone(&program));

        assert!(matches!(
            dispatch_entry(&executable, variable, Environment::new(), &mut Vec::new()),
            Err(RuntimeFailure::MissingBinding)
        ));
        assert!(matches!(
            return_application_function(variable, Environment::new(), Value::Unit),
            Err(RuntimeFailure::UnexpectedFunctionValue)
        ));
        assert!(matches!(
            apply_primitive(
                Primitive::Add,
                Value::Boolean(false),
                Value::Integer(Integer::parse_decimal("1").expect("valid integer")),
            ),
            Err(RuntimeFailure::UnexpectedPrimitiveValue)
        ));
        assert!(matches!(
            resolve_location(&[], 0),
            Err(RuntimeFailure::InvalidLocation)
        ));
        assert!(matches!(
            resolve_location(&[HeapCell::Uninitialized], 0),
            Err(RuntimeFailure::UninitializedLocation)
        ));
        assert!(matches!(
            resolve_location(&[HeapCell::Alias(0)], 0),
            Err(RuntimeFailure::AliasLoop)
        ));
        assert!(matches!(
            dispatch_return(
                Frame::Match {
                    arms: Box::new([]),
                    environment: Environment::new(),
                },
                Value::Boolean(true),
                &mut Vec::new(),
            ),
            Err(RuntimeFailure::ImpossibleMatch)
        ));
    }

    #[test]
    fn recursive_data_initializers_store_each_slot_before_entering_the_next() {
        let source = SourceFile::new("recursive-data-order.ash", "Flag First Second group")
            .expect("test source");
        let span = |start, end| {
            source
                .span(ByteRange::new(start, end).expect("ordered range"))
                .expect("source span")
        };
        let origin = Origin::Source(span(0, 23));
        let nominal = NominalTypeId::new(source.id(), 0);
        let first_constructor = ConstructorId::new(nominal, 0);
        let second_constructor = ConstructorId::new(nominal, 1);
        let registry = Arc::new(ResolvedRegistry::new(
            vec![ResolvedNominalType {
                representation_provenance: None,
                declaration_kind: crate::resolved::ResolvedNominalDeclarationKind::Data,
                representation: None,
                id: nominal,
                spelling: "Flag".into(),
                constructors: vec![first_constructor, second_constructor].into_boxed_slice(),
                origin: Origin::Source(span(0, 17)),
            }],
            vec![
                ResolvedConstructor {
                    id: first_constructor,
                    owner: nominal,
                    spelling: "First".into(),
                    payload: None,
                    origin: Origin::Source(span(5, 10)),
                },
                ResolvedConstructor {
                    id: second_constructor,
                    owner: nominal,
                    spelling: "Second".into(),
                    payload: None,
                    origin: Origin::Source(span(11, 17)),
                },
            ],
        ));
        let nominal_type = Type::Nominal(nominal);
        let mut builder = CoreBuilder::with_registry(registry);
        let first_binder = builder
            .binder(nominal_type.clone(), origin.clone())
            .expect("first recursive binder should fit");
        let second_binder = builder
            .binder(nominal_type.clone(), origin.clone())
            .expect("second recursive binder should fit");
        let first_initializer = builder
            .constructor(first_constructor, nominal_type.clone(), origin.clone())
            .expect("first constructor should fit");
        let second_initializer = builder
            .constructor(second_constructor, nominal_type.clone(), origin.clone())
            .expect("second constructor should fit");
        let body = builder
            .variable(first_binder.id(), nominal_type.clone(), origin.clone())
            .expect("recursive body should fit");
        let root = builder
            .recursive_binding(
                vec![
                    (first_binder, first_initializer),
                    (second_binder, second_initializer),
                ],
                body,
                nominal_type,
                origin,
            )
            .expect("recursive group should fit");
        let validated = validate(
            builder.finish(root).expect("Core should finish"),
            &[&source],
        )
        .expect("Core should validate");
        let program = validated.shared();
        let executable = ExecutableProgram::Pure(Arc::clone(&program));
        let root = program.node(program.root()).expect("recursive root");
        let PureExprKind::Computation(PureComputation::RecursiveBind(group)) = &root.kind else {
            panic!("block should lower to one recursive group")
        };
        let [first, second] = group.members() else {
            panic!("fixture should have two recursive data members")
        };

        let mut heap = Vec::new();
        let transition = enter_recursive_binding(&executable, group, Environment::new(), &mut heap)
            .expect("recursive entry should allocate both slots");
        let Transition {
            control: Control::Evaluate(first_initializer, recursive_environment),
            frame: Some(first_frame),
        } = transition
        else {
            panic!("recursive entry should suspend on the first initializer")
        };
        assert_eq!(first_initializer, first.initializer());
        assert!(matches!(
            heap.as_slice(),
            [HeapCell::Uninitialized, HeapCell::Uninitialized]
        ));
        assert!(matches!(
            recursive_environment.lookup(first.binder().id(), &executable),
            Some(Value::Location(0))
        ));
        assert!(matches!(
            recursive_environment.lookup(second.binder().id(), &executable),
            Some(Value::Location(1))
        ));

        let first_value = dispatch_entry(
            &executable,
            first_initializer,
            recursive_environment,
            &mut heap,
        )
        .expect("first initializer should enter");
        let Transition {
            control: Control::Return(first_value),
            frame: None,
        } = first_value
        else {
            panic!("nullary constructor should return its allocated location")
        };
        let transition = dispatch_return(first_frame, first_value, &mut heap)
            .expect("first result should store its alias");
        let Transition {
            control: Control::Evaluate(second_initializer, recursive_environment),
            frame: Some(second_frame),
        } = transition
        else {
            panic!("first store should suspend on the second initializer")
        };
        assert_eq!(second_initializer, second.initializer());
        assert!(matches!(heap[0], HeapCell::Alias(2)));
        assert!(matches!(heap[1], HeapCell::Uninitialized));

        let second_value = dispatch_entry(
            &executable,
            second_initializer,
            recursive_environment,
            &mut heap,
        )
        .expect("second initializer should enter");
        let Transition {
            control: Control::Return(second_value),
            frame: None,
        } = second_value
        else {
            panic!("nullary constructor should return its allocated location")
        };
        let transition = dispatch_return(second_frame, second_value, &mut heap)
            .expect("second result should store its alias");
        assert!(matches!(
            transition,
            Transition {
                control: Control::Evaluate(node, _),
                frame: None,
            } if node == group.body()
        ));
        assert!(matches!(heap[0], HeapCell::Alias(2)));
        assert!(matches!(heap[1], HeapCell::Alias(3)));
    }

    #[test]
    fn returned_closure_retains_the_heap_for_captured_structural_values() {
        let source = SourceFile::new("returned-structural-capture.ash", "pair keep ignored")
            .expect("test source");
        let origin = Origin::Source(
            source
                .span(ByteRange::new(0, 17).expect("ordered range"))
                .expect("source span"),
        );
        let tuple_type = Type::Tuple(vec![Type::Int, Type::Int].into_boxed_slice());
        let function_type = Type::Function(Box::new(Type::Unit), Box::new(tuple_type.clone()));
        let mut builder = CoreBuilder::new();
        let pair = builder
            .binder(tuple_type.clone(), origin.clone())
            .expect("pair binder should fit");
        let ignored = builder
            .binder(Type::Unit, origin.clone())
            .expect("function parameter should fit");
        let left = builder
            .integer(
                Integer::parse_decimal("20").expect("valid integer"),
                Type::Int,
                origin.clone(),
            )
            .expect("left tuple element should fit");
        let right = builder
            .integer(
                Integer::parse_decimal("22").expect("valid integer"),
                Type::Int,
                origin.clone(),
            )
            .expect("right tuple element should fit");
        let initializer = builder
            .tuple(vec![left, right], tuple_type.clone(), origin.clone())
            .expect("tuple initializer should fit");
        let body = builder
            .variable(pair.id(), tuple_type, origin.clone())
            .expect("captured pair occurrence should fit");
        let function = builder
            .function(ignored, body, function_type.clone(), origin.clone())
            .expect("returned closure should fit");
        let root = builder
            .binding(pair, initializer, function, function_type, origin)
            .expect("capturing binding should fit");
        let validated = validate(
            builder.finish(root).expect("Core should finish"),
            &[&source],
        )
        .expect("Core should validate");

        let evaluation = evaluate(&validated).expect("closure should evaluate");
        let Value::Function(closure) = &evaluation.value else {
            panic!("the program should return its closure")
        };
        let captured_location = closure
            .environment
            .head
            .as_ref()
            .and_then(|entry| match &entry.kind {
                EnvironmentEntryKind::Binding {
                    value: Value::Location(location),
                    ..
                } => Some(*location),
                EnvironmentEntryKind::Binding { .. } | EnvironmentEntryKind::Recursive { .. } => {
                    None
                }
            })
            .expect("the closure should capture the tuple location");

        assert!(captured_location < evaluation.heap.cell_count());
    }

    #[test]
    fn environment_clone_and_extension_share_the_existing_chain() {
        let first = Environment::new()
            .extend(
                BinderId::new(0),
                Value::Integer(Integer::parse_decimal("1").expect("valid integer")),
            )
            .expect("one binding should fit");
        let cloned = first.clone();
        let second = cloned
            .extend(
                BinderId::new(1),
                Value::Integer(Integer::parse_decimal("2").expect("valid integer")),
            )
            .expect("two bindings should fit");

        let first_head = first.head.as_ref().expect("first entry");
        let shared_parent = second
            .head
            .as_ref()
            .and_then(|entry| entry.parent.as_ref())
            .expect("shared parent entry");
        assert!(Arc::ptr_eq(first_head, shared_parent));
        assert_eq!(Arc::strong_count(first_head), 2);
        assert_eq!(first.len(), 1);
        assert_eq!(second.len(), 2);
    }

    #[test]
    fn environment_debug_is_bounded_for_deep_captures() {
        let value = Value::Unit;
        let mut environment = Environment::new();
        for binder in 0..100 {
            environment = environment
                .extend(BinderId::new(binder), value.clone())
                .expect("environment should fit");
        }

        let debug = format!("{environment:?}");
        assert!(debug.len() < 512);
        assert!(debug.contains("truncated: true"));
    }

    #[test]
    fn concurrent_shared_environment_tails_drop_on_small_stacks() {
        const ENTRIES: u32 = 50_000;
        const OWNERS: u32 = 8;
        let value = Value::Integer(Integer::parse_decimal("1").expect("valid environment value"));
        let mut environment = Environment::new();
        for binder in 0..ENTRIES {
            environment = environment
                .extend(BinderId::new(binder), value.clone())
                .expect("bounded environment should fit");
        }
        let shared_head = environment.head.as_ref().expect("shared head").clone();
        let mut branches = Vec::with_capacity(OWNERS as usize);
        for owner in 0..OWNERS {
            branches.push(
                environment
                    .clone()
                    .extend(BinderId::new(ENTRIES + owner), value.clone())
                    .expect("branch entry should fit"),
            );
        }
        drop(environment);
        assert_eq!(Arc::strong_count(&shared_head), OWNERS as usize + 1);

        let barrier = Arc::new(Barrier::new(OWNERS as usize));
        let mut workers = Vec::with_capacity(OWNERS as usize);
        for (owner, branch) in branches.into_iter().enumerate() {
            let barrier = Arc::clone(&barrier);
            workers.push(
                std::thread::Builder::new()
                    .name(format!("shared-environment-drop-{owner}"))
                    .stack_size(256 * 1024)
                    .spawn(move || {
                        barrier.wait();
                        drop(branch);
                    })
                    .expect("test thread should start"),
            );
        }
        drop(shared_head);
        for worker in workers {
            worker.join().expect("shared environment should drop");
        }
    }

    #[test]
    fn closure_captured_environment_chains_drop_on_a_small_stack() {
        const ENTRIES: u32 = 20_000;
        let worker = std::thread::Builder::new()
            .name("closure-environment-drop".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let source = SourceFile::new("closure-drop.ash", "1").expect("test source");
                let origin = Origin::Source(
                    source
                        .span(ByteRange::new(0, 1).expect("ordered range"))
                        .expect("source span"),
                );
                let mut builder = CoreBuilder::new();
                let parameter = builder
                    .binder(Type::Int, origin.clone())
                    .expect("parameter should fit");
                let body = builder
                    .variable(parameter.id(), Type::Int, origin.clone())
                    .expect("body should fit");
                let function = builder
                    .function(
                        parameter.clone(),
                        body,
                        Type::Function(Box::new(Type::Int), Box::new(Type::Int)),
                        origin.clone(),
                    )
                    .expect("function should fit");
                let validated = validate(
                    builder.finish(function).expect("root should finish"),
                    &[&source],
                )
                .expect("function Core should validate");
                let program = validated.shared();
                let mut environment = Environment::new();
                for binder in 0..ENTRIES {
                    let closure = Closure {
                        parameter: parameter.id(),
                        body,
                        program: ExecutableProgram::Pure(Arc::clone(&program)),
                        environment: environment.clone(),
                        origin: origin.clone(),
                    };
                    environment = environment
                        .extend(BinderId::new(binder), Value::Function(closure))
                        .expect("environment should fit");
                }
                drop(environment);
            })
            .expect("test thread should start");

        worker.join().expect("closure environment should drop");
    }

    #[test]
    fn recursive_template_frame_has_no_owning_edge_back_from_its_members() {
        const MEMBERS: u32 = 50_000;
        let worker = std::thread::Builder::new()
            .name("recursive-template-drop".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let source = SourceFile::new("recursive-drop.ash", "1").expect("test source");
                let origin = Origin::Source(
                    source
                        .span(ByteRange::new(0, 1).expect("ordered range"))
                        .expect("source span"),
                );
                let mut builder = CoreBuilder::new();
                let parameter = builder
                    .binder(Type::Unit, origin.clone())
                    .expect("parameter should fit");
                let body = builder
                    .integer(
                        Integer::parse_decimal("1").expect("valid integer"),
                        Type::Int,
                        origin.clone(),
                    )
                    .expect("body should fit");
                let function = builder
                    .function(
                        parameter.clone(),
                        body,
                        Type::Function(Box::new(Type::Unit), Box::new(Type::Int)),
                        origin.clone(),
                    )
                    .expect("function should fit");
                let validated = validate(
                    builder.finish(function).expect("root should finish"),
                    &[&source],
                )
                .expect("function Core should validate");
                let program = validated.shared();
                let executable = ExecutableProgram::Pure(Arc::clone(&program));
                let members = (0..MEMBERS)
                    .map(|binder| RecursiveMemberTemplate {
                        binder: BinderId::new(binder),
                        kind: RecursiveMemberKind::Function {
                            parameter: parameter.id(),
                            body,
                            origin: origin.clone(),
                            abstraction: None,
                        },
                    })
                    .collect();
                let environment = Environment::new()
                    .extend_recursive(members)
                    .expect("recursive frame should fit");
                let frame = environment.head.as_ref().expect("recursive frame").clone();

                assert_eq!(Arc::strong_count(&frame), 2);
                let first_value = environment
                    .lookup(BinderId::new(MEMBERS / 2), &executable)
                    .expect("member should materialize");
                assert_eq!(Arc::strong_count(&frame), 3);
                let second_value = environment
                    .lookup(BinderId::new(MEMBERS / 2 + 1), &executable)
                    .expect("another member should materialize");
                assert_eq!(Arc::strong_count(&frame), 4);
                let (Value::Function(first_closure), Value::Function(second_closure)) =
                    (first_value, second_value)
                else {
                    panic!("recursive members should materialize as functions")
                };
                assert!(Arc::ptr_eq(
                    first_closure
                        .environment
                        .head
                        .as_ref()
                        .expect("first recursive root"),
                    second_closure
                        .environment
                        .head
                        .as_ref()
                        .expect("second recursive root")
                ));
                drop(environment);
                assert_eq!(Arc::strong_count(&frame), 3);
                drop(first_closure);
                assert_eq!(Arc::strong_count(&frame), 2);
                drop(second_closure);
                assert_eq!(Arc::strong_count(&frame), 1);
                drop(frame);
            })
            .expect("test thread should start");

        worker
            .join()
            .expect("recursive template environment should drop iteratively");
    }

    #[test]
    fn evaluator_enters_a_validated_newtype_conversion_child_directly() {
        let source = SourceFile::new("runtime-conversion.ash", "()").expect("test source");
        let origin = Origin::Source(
            source
                .span(ByteRange::new(0, 2).expect("ordered range"))
                .expect("source span"),
        );
        let owner = NominalTypeId::new(source.id(), 0);
        let mut builder = CoreBuilder::new();
        let child = builder
            .unit(Type::Unit, origin.clone())
            .expect("the conversion child should fit");
        let root = builder
            .newtype_conversion(
                owner,
                NewtypeConversionDirection::Unwrap,
                child,
                Type::Unit,
                origin,
            )
            .expect("the conversion carrier should fit");
        let program = crate::core::dialect::forge_validated_for_test(
            builder.finish(root).expect("the conversion should finish"),
        );
        let executable = ExecutableProgram::Pure(program.shared());
        let mut heap = Vec::new();

        let transition = dispatch_entry(&executable, root, Environment::new(), &mut heap)
            .expect("dispatch should enter the conversion child");
        let Control::Evaluate(entered, _) = transition.control else {
            panic!("conversion dispatch should directly evaluate its child");
        };
        assert_eq!(entered, child);
        assert!(transition.frame.is_none());
        assert!(heap.is_empty());
        let evaluation = evaluate(&program).expect("evaluation should erase the conversion");
        assert!(matches!(evaluation.value, Value::Unit));
        assert_eq!(evaluation.heap.cell_count(), 0);
        assert_eq!(evaluation.max_frame_depth, 0);
    }

    #[test]
    fn module_newtype_wrapper_allocates_no_constructor_cell() {
        let source = SourceFile::new(
            "runtime-newtype-allocation.ash",
            "type Box = Box(Int)\nnewtype Wrapped = Wrapped(Box)\n",
        )
        .expect("test source");
        let span = |start, end| {
            source
                .span(ByteRange::new(start, end).expect("ordered range"))
                .expect("source span")
        };
        let origin = Origin::Source(span(0, 50));
        let box_declaration_origin = Origin::Source(span(0, 19));
        let box_constructor_origin = Origin::Source(span(11, 19));
        let wrapped_declaration_origin = Origin::Source(span(20, 50));
        let wrapped_constructor_origin = Origin::Source(span(38, 50));
        let wrapped_representation_span = span(46, 49);
        let module = source.id();
        let box_owner = NominalTypeId::new(module, 0);
        let wrapped_owner = NominalTypeId::new(module, 1);
        let box_constructor = ConstructorId::new(box_owner, 0);
        let wrapped_constructor = ConstructorId::new(wrapped_owner, 0);
        let registry = Arc::new(
            ResolvedRegistry::new(
                vec![
                    ResolvedNominalType {
                        id: box_owner,
                        declaration_kind: crate::resolved::ResolvedNominalDeclarationKind::Data,
                        spelling: "Box".to_owned(),
                        constructors: Box::new([box_constructor]),
                        representation: None,
                        representation_provenance: None,
                        origin: box_declaration_origin,
                    },
                    ResolvedNominalType {
                        id: wrapped_owner,
                        declaration_kind: crate::resolved::ResolvedNominalDeclarationKind::Newtype,
                        spelling: "Wrapped".to_owned(),
                        constructors: Box::new([wrapped_constructor]),
                        representation: Some(Type::Nominal(box_owner)),
                        representation_provenance: Some(ResolvedTypeProvenance::new(
                            vec![ResolvedTypeProvenanceNode::Fact(
                                wrapped_representation_span,
                            )],
                            0,
                        )),
                        origin: wrapped_declaration_origin,
                    },
                ],
                vec![
                    ResolvedConstructor {
                        id: box_constructor,
                        owner: box_owner,
                        spelling: "Box".to_owned(),
                        payload: Some(Type::Int),
                        origin: box_constructor_origin,
                    },
                    ResolvedConstructor {
                        id: wrapped_constructor,
                        owner: wrapped_owner,
                        spelling: "Wrapped".to_owned(),
                        payload: None,
                        origin: wrapped_constructor_origin,
                    },
                ],
            )
            .with_type_parameters(vec![(box_owner, Vec::new()), (wrapped_owner, Vec::new())]),
        );
        let mut builder = CoreBuilder::with_registry(registry);
        let constructor = builder
            .constructor(
                box_constructor,
                Type::Function(Box::new(Type::Int), Box::new(Type::Nominal(box_owner))),
                origin.clone(),
            )
            .expect("the ordinary constructor should fit");
        let payload = builder
            .integer(
                Integer::parse_decimal("42").expect("42 should parse"),
                Type::Int,
                origin.clone(),
            )
            .expect("the representation payload should fit");
        let representation = builder
            .application(
                constructor,
                payload,
                Type::Nominal(box_owner),
                origin.clone(),
            )
            .expect("the ordinary representation should fit");
        let root = builder
            .newtype_conversion(
                wrapped_owner,
                NewtypeConversionDirection::Wrap,
                representation,
                Type::Nominal(wrapped_owner),
                origin,
            )
            .expect("the newtype wrapper should fit");
        let program = validate(
            builder
                .finish(root)
                .expect("the wrapped value should finish"),
            &[&source],
        )
        .expect("the canonical conversion should independently authenticate");

        let evaluation = evaluate(&program).expect("the validated conversion should erase");
        assert!(matches!(evaluation.value, Value::Data(_)));
        assert_eq!(
            evaluation.heap.cell_count(),
            1,
            "only the ordinary representation constructor may allocate",
        );
    }

    #[test]
    fn local_newtype_closure_allocates_no_wrapper_or_scope_state() {
        let program = effect_program(concat!(
            "make : Unit -> (Unit -> Int)\n",
            "make () = {\n",
            "    newtype Offset = Offset(Int)\n",
            "    let offset = Offset(41)\n",
            "    fn(ignored) {\n",
            "        match offset {\n",
            "            Offset(value) => value + 1\n",
            "        }\n",
            "    }\n",
            "}\n\n",
            "main : Unit -> Int\n",
            "main () = make()()\n",
        ));
        let evaluation = evaluate_effect(&program)
            .expect("the identity-free closure should execute after its scope returns");
        assert!(matches!(evaluation.value, Value::Integer(ref value) if value.to_string() == "42"));
        assert_eq!(evaluation.heap.cell_count(), 0);
        assert!(evaluation.effect_trace().is_empty());
    }

    #[test]
    fn evaluator_conversion_erasure_and_teardown_fit_a_small_stack() {
        const DEPTH: usize = 32_768;

        std::thread::Builder::new()
            .name("runtime-newtype-conversion-erasure".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let source =
                    SourceFile::new("runtime-conversion-chain.ash", "()").expect("test source");
                let origin = Origin::Source(
                    source
                        .span(ByteRange::new(0, 2).expect("ordered range"))
                        .expect("source span"),
                );
                let owner = NominalTypeId::new(source.id(), 0);
                let mut builder = CoreBuilder::new();
                let mut root = builder
                    .unit(Type::Unit, origin.clone())
                    .expect("the conversion leaf should fit");
                for index in 0..DEPTH {
                    root = builder
                        .newtype_conversion(
                            owner,
                            if index % 2 == 0 {
                                NewtypeConversionDirection::Wrap
                            } else {
                                NewtypeConversionDirection::Unwrap
                            },
                            root,
                            Type::Unit,
                            origin.clone(),
                        )
                        .expect("the conversion chain should fit");
                }
                let program = crate::core::dialect::forge_validated_for_test(
                    builder.finish(root).expect("the conversion should finish"),
                );
                let evaluation =
                    evaluate(&program).expect("evaluation must erase the conversion chain");
                assert!(matches!(evaluation.value, Value::Unit));
                assert_eq!(evaluation.trace.len(), DEPTH + 1);
                assert_eq!(evaluation.max_frame_depth, 0);
                assert_eq!(evaluation.heap.cell_count(), 0);
            })
            .expect("the evaluator erasure thread should start")
            .join()
            .expect("evaluator conversion erasure must fit a small stack");
    }
}
