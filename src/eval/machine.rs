//! Loop-driven control transitions for validated Ash Core families.

use std::{error::Error, fmt, sync::Arc};

use super::{
    Closure, Value,
    value::{ExecutableNode, ExecutableProgram, HeapCell, Location, ObservedHeap, ObservedValue},
};
use crate::{
    core::{
        CoreMatchArm, CorePattern, CorePatternKind, EffectExprKind, EffectOperation, HandlerId,
        NodeId, Primitive, PureComputation, PureExprKind, PureValue, ValidatedEffectProgram,
        ValidatedProgram,
    },
    resolved::{BinderId, ResumeId},
    types::{EffectInstance, OperationId, same_type},
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
}

struct EnvironmentEntry {
    kind: EnvironmentEntryKind,
    parent: Option<Arc<Self>>,
    visible_len: usize,
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
    Function {
        parameter: BinderId,
        body: NodeId,
        origin: crate::source::Origin,
    },
    Data {
        location: Location,
    },
}

impl Drop for EnvironmentEntry {
    fn drop(&mut self) {
        let mut pending = Vec::new();
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
    fn take_owned_edges(&mut self, pending: &mut Vec<Arc<Self>>) {
        if let Some(parent) = self.parent.take() {
            pending.push(parent);
        }
        if let EnvironmentEntryKind::Binding {
            value: Value::Function(closure),
            ..
        } = &mut self.kind
        {
            if let Some(captured) = closure.environment.head.take() {
                pending.push(captured);
            }
            closure.environment.len = 0;
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
                            } => Value::Function(Closure {
                                parameter: *parameter,
                                body: *body,
                                program: program.clone(),
                                environment: Self {
                                    head: Some(Arc::clone(entry)),
                                    len: entry.visible_len,
                                },
                                origin: origin.clone(),
                            }),
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

    fn extend(mut self, binder: BinderId, value: Value) -> Result<Self, RuntimeFailure> {
        let len = self
            .len
            .checked_add(1)
            .ok_or(RuntimeFailure::EnvironmentCapacity)?;
        Ok(Self {
            head: Some(Arc::new(EnvironmentEntry {
                kind: EnvironmentEntryKind::Binding { binder, value },
                parent: self.head.take(),
                visible_len: len,
            })),
            len,
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
        let len = self
            .len
            .checked_add(members.len())
            .ok_or(RuntimeFailure::EnvironmentCapacity)?;
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
            })),
            len,
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
    /// A lexical handler boundary became active.
    HandlerActivated(HandlerId),
    /// A request reached dynamic handler selection.
    Request(OperationId),
    /// The nearest exact handler was selected and removed for its clause.
    HandlerSelected(HandlerId),
    /// A selected operation clause began evaluating.
    ClauseEntered(HandlerId, OperationId),
    /// A clause consumed its resume capability.
    Resume(HandlerId),
    /// A captured handler boundary was restored around resumed control.
    HandlerRestored(HandlerId),
    /// Resumed control returned and the selected clause completed.
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
}

impl Evaluation {
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
    /// The per-evaluation heap cannot represent another cell.
    HeapCapacity,
    /// A captured continuation cannot retain another control frame.
    CapturedControlCapacity,
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
    /// Returns the stable reason code owned by this runtime failure.
    #[must_use]
    pub const fn reason_code(self) -> &'static str {
        match self {
            Self::MissingNode => "runtime.missing-node",
            Self::UnexpectedPrimitiveValue => "runtime.unexpected-primitive-value",
            Self::UnexpectedFunctionValue => "runtime.unexpected-function-value",
            Self::MissingBinding => "runtime.missing-binding",
            Self::UnexpectedRecursiveBinding => "runtime.unexpected-recursive-binding",
            Self::EnvironmentCapacity => "runtime.environment-capacity",
            Self::InvalidControlState => "runtime.invalid-control-state",
            Self::HeapCapacity => "runtime.heap-capacity",
            Self::CapturedControlCapacity => "runtime.captured-control-capacity",
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
            Self::HeapCapacity => "runtime heap capacity is exhausted",
            Self::CapturedControlCapacity => "runtime captured-control capacity is exhausted",
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
    HandlerBoundary {
        node: NodeId,
        environment: Environment,
    },
    Request {
        node: NodeId,
    },
    Resume {
        node: NodeId,
    },
    ClauseBoundary {
        handler: HandlerId,
        owner: ResumeId,
        continuation: Option<CapturedContinuation>,
    },
}

#[derive(Debug)]
struct CapturedContinuation {
    frames: Vec<Frame>,
}

// Rust allocations cannot represent a non-zero `Frame` vector whose byte
// length exceeds `isize::MAX`. This implementation bound is not Ash semantics.
const MAX_CAPTURED_FRAME_CELLS: usize = (isize::MAX as usize) / std::mem::size_of::<Frame>();

impl Drop for CapturedContinuation {
    fn drop(&mut self) {
        let mut pending = std::mem::take(&mut self.frames);
        while let Some(mut frame) = pending.pop() {
            if let Frame::ClauseBoundary { continuation, .. } = &mut frame
                && let Some(mut nested) = continuation.take()
            {
                pending.append(&mut nested.frames);
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

/// The retained explicit evaluator machine shared by pure and effect Core.
#[derive(Debug)]
pub struct Machine {
    program: ExecutableProgram,
    control: Option<Control>,
    frames: Vec<Frame>,
    max_frame_depth: usize,
    trace: Vec<TraceEvent>,
    effect_trace: Option<Vec<EffectTraceEvent>>,
    heap: Vec<HeapCell>,
    capture_limit: usize,
    captured_cells: usize,
}

impl Machine {
    fn new(program: &ValidatedProgram) -> Self {
        Self {
            program: ExecutableProgram::Pure(program.shared()),
            control: Some(Control::Evaluate(program.root(), Environment::new())),
            frames: Vec::new(),
            max_frame_depth: 0,
            trace: Vec::new(),
            effect_trace: None,
            heap: Vec::new(),
            capture_limit: 0,
            captured_cells: 0,
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
            program: ExecutableProgram::Effect(program.shared()),
            control: Some(Control::Evaluate(program.root(), Environment::new())),
            frames: Vec::new(),
            max_frame_depth: 0,
            trace: Vec::new(),
            effect_trace: Some(Vec::new()),
            heap: Vec::new(),
            capture_limit,
            captured_cells: 0,
        }
    }

    fn run(mut self) -> Result<Evaluation, RuntimeFailure> {
        loop {
            let control = self
                .control
                .take()
                .ok_or(RuntimeFailure::InvalidControlState)?;
            match control {
                Control::Evaluate(node, environment) => {
                    self.trace.push(TraceEvent::Enter(node));
                    if let Some(handler) = self.handler(node) {
                        self.trace_effect(EffectTraceEvent::HandlerActivated(handler.id()));
                    }
                    let transition =
                        dispatch_entry(&self.program, node, environment, &mut self.heap)?;
                    self.apply(transition);
                }
                Control::Return(value) => {
                    let Some(frame) = self.frames.pop() else {
                        let heap =
                            ObservedHeap::new(Arc::clone(self.program.registry()), self.heap);
                        let value = match value {
                            Value::Location(root) => {
                                Value::Data(ObservedValue::new(Arc::clone(&heap), root))
                            }
                            value => value,
                        };
                        return Ok(Evaluation {
                            value,
                            trace: self.trace,
                            max_frame_depth: self.max_frame_depth,
                            effect_trace: self.effect_trace.take().map(Vec::into_boxed_slice),
                            heap,
                        });
                    };
                    self.return_from(frame, value)?;
                }
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
        match frame {
            Frame::HandlerBoundary { .. } => {
                self.control = Some(Control::Return(value));
            }
            Frame::Request { node } => self.return_request(node, value)?,
            Frame::Resume { node } => self.return_resume(node, value)?,
            Frame::ClauseBoundary {
                handler,
                continuation,
                ..
            } => {
                if continuation.is_some() {
                    return Err(RuntimeFailure::InvalidControlState);
                }
                self.trace_effect(EffectTraceEvent::ClauseReturned(handler));
                self.control = Some(Control::Return(value));
            }
            frame => {
                let transition = dispatch_return(frame, value, &mut self.heap)?;
                self.apply(transition);
            }
        }
        Ok(())
    }

    fn return_request(&mut self, node: NodeId, value: Value) -> Result<(), RuntimeFailure> {
        let (effect, operation) = match self.program.node(node) {
            Some(ExecutableNode::Effect(expression)) => match &expression.kind {
                EffectExprKind::Operation(EffectOperation::Request(request)) => {
                    (request.effect(), request.operation())
                }
                _ => return Err(RuntimeFailure::InvalidControlState),
            },
            _ => return Err(RuntimeFailure::InvalidControlState),
        };
        let selected = self
            .frames
            .iter()
            .rposition(|frame| match frame {
                Frame::HandlerBoundary { node, .. } => self
                    .handler(*node)
                    .is_some_and(|handler| same_effect_instance(handler.effect(), effect)),
                _ => false,
            })
            .ok_or(RuntimeFailure::InvalidControlState)?;
        self.trace_effect(EffectTraceEvent::Request(operation));
        let continuation = self.capture_from(selected)?;
        let captured = &continuation.frames;
        let (handler_id, handler_environment, clause_owner, clause_body, bindings) = {
            let Frame::HandlerBoundary {
                node: handler_node,
                environment,
            } = &captured[0]
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
        self.frames.push(Frame::ClauseBoundary {
            handler: handler_id,
            owner: clause_owner,
            continuation: Some(continuation),
        });
        self.trace_effect(EffectTraceEvent::HandlerSelected(handler_id));
        self.trace_effect(EffectTraceEvent::ClauseEntered(handler_id, operation));
        self.max_frame_depth = self.max_frame_depth.max(self.frames.len());
        self.control = Some(Control::Evaluate(
            clause_body,
            handler_environment.extend_many(bindings)?,
        ));
        Ok(())
    }

    fn capture_from(&mut self, selected: usize) -> Result<CapturedContinuation, RuntimeFailure> {
        let captured_len = self
            .frames
            .len()
            .checked_sub(selected)
            .ok_or(RuntimeFailure::InvalidControlState)?;
        let retained = self
            .captured_cells
            .checked_add(captured_len)
            .ok_or(RuntimeFailure::CapturedControlCapacity)?;
        if retained > self.capture_limit {
            return Err(RuntimeFailure::CapturedControlCapacity);
        }
        let mut frames = Vec::new();
        frames
            .try_reserve_exact(captured_len)
            .map_err(|_| RuntimeFailure::CapturedControlCapacity)?;
        frames.extend(self.frames.drain(selected..));
        self.captured_cells = retained;
        Ok(CapturedContinuation { frames })
    }

    fn return_resume(&mut self, node: NodeId, value: Value) -> Result<(), RuntimeFailure> {
        let (handler, owner) = match self.program.node(node) {
            Some(ExecutableNode::Effect(expression)) => match &expression.kind {
                EffectExprKind::Operation(EffectOperation::Resume(resume)) => {
                    (resume.handler(), resume.owner())
                }
                _ => return Err(RuntimeFailure::InvalidControlState),
            },
            _ => return Err(RuntimeFailure::InvalidControlState),
        };
        let boundary = self
            .frames
            .iter_mut()
            .rev()
            .find_map(|frame| match frame {
                Frame::ClauseBoundary {
                    handler: found_handler,
                    owner: found_owner,
                    continuation,
                } if found_handler == &handler && found_owner == &owner => Some(continuation),
                _ => None,
            })
            .ok_or(RuntimeFailure::InvalidControlState)?;
        let captured_len = boundary
            .as_ref()
            .ok_or(RuntimeFailure::InvalidControlState)?
            .frames
            .len();
        self.frames
            .try_reserve(captured_len)
            .map_err(|_| RuntimeFailure::CapturedControlCapacity)?;
        let boundary = self
            .frames
            .iter_mut()
            .rev()
            .find_map(|frame| match frame {
                Frame::ClauseBoundary {
                    handler: found_handler,
                    owner: found_owner,
                    continuation,
                } if found_handler == &handler && found_owner == &owner => Some(continuation),
                _ => None,
            })
            .ok_or(RuntimeFailure::InvalidControlState)?;
        let mut continuation = boundary.take().ok_or(RuntimeFailure::InvalidControlState)?;
        self.trace_effect(EffectTraceEvent::Resume(handler));
        for frame in &continuation.frames {
            if let Frame::HandlerBoundary { node, .. } = frame {
                let restored = self
                    .handler(*node)
                    .ok_or(RuntimeFailure::InvalidControlState)?;
                self.trace_effect(EffectTraceEvent::HandlerRestored(restored.id()));
            }
        }
        self.captured_cells = self
            .captured_cells
            .checked_sub(captured_len)
            .ok_or(RuntimeFailure::InvalidControlState)?;
        self.frames.append(&mut continuation.frames);
        self.max_frame_depth = self.max_frame_depth.max(self.frames.len());
        self.control = Some(Control::Return(value));
        Ok(())
    }

    fn handler(&self, node: NodeId) -> Option<&crate::core::HandlerNode> {
        let ExecutableNode::Effect(expression) = self.program.node(node)? else {
            return None;
        };
        let EffectExprKind::Operation(EffectOperation::Handler(handler)) = &expression.kind else {
            return None;
        };
        Some(handler)
    }
}

fn same_effect_instance(left: &EffectInstance, right: &EffectInstance) -> bool {
    left.effect() == right.effect()
        && left.arguments().len() == right.arguments().len()
        && left
            .arguments()
            .iter()
            .zip(right.arguments())
            .all(|(left, right)| same_type(left, right))
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
                    EffectOperation::Request(request) => Transition::suspend(
                        Control::Evaluate(request.operand(), environment),
                        Frame::Request { node },
                    ),
                    EffectOperation::Handler(handler) => Transition::suspend(
                        Control::Evaluate(handler.body(), environment.clone()),
                        Frame::HandlerBoundary { node, environment },
                    ),
                    EffectOperation::Resume(resume) => Transition::suspend(
                        Control::Evaluate(resume.value(), environment),
                        Frame::Resume { node },
                    ),
                });
            }
        },
    };
    Ok(match kind {
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
            enter_type_abstraction(operation, environment)
        }
        PureExprKind::Computation(PureComputation::TypeApplication(operation)) => {
            enter_type_application(operation, environment)
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
            PureExprKind::Value(PureValue::Function(function)) => RecursiveMemberKind::Function {
                parameter: function.parameter().id(),
                body: function.body(),
                origin: initializer_origin,
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
        Frame::HandlerBoundary { .. }
        | Frame::Request { .. }
        | Frame::Resume { .. }
        | Frame::ClauseBoundary { .. } => Err(RuntimeFailure::InvalidControlState),
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
    if !matches!(function, Value::Function(_) | Value::ConstructorFunction(_)) {
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

fn allocate_heap(heap: &mut Vec<HeapCell>, cell: HeapCell) -> Result<Location, RuntimeFailure> {
    if heap.len() == usize::MAX {
        return Err(RuntimeFailure::HeapCapacity);
    }
    let location = heap.len();
    heap.push(cell);
    Ok(location)
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

fn matches_pattern(
    pattern: &CorePattern,
    value: &Value,
    heap: &[HeapCell],
    bindings: &mut Vec<(BinderId, Value)>,
) -> Result<bool, RuntimeFailure> {
    let mut work = vec![(pattern, value.clone())];
    while let Some((pattern, value)) = work.pop() {
        match &pattern.kind {
            CorePatternKind::Binder(binder) => bindings.push((binder.id(), value)),
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
                let location = resolve_location(heap, location)?;
                let Some(HeapCell::Tuple(elements)) = heap.get(location) else {
                    return Ok(false);
                };
                if patterns.len() != elements.len() {
                    return Ok(false);
                }
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
                let location = resolve_location(heap, location)?;
                let Some(HeapCell::Constructor(found, found_payload)) = heap.get(location) else {
                    return Ok(false);
                };
                if found != constructor {
                    return Ok(false);
                }
                match (payload.as_deref(), found_payload) {
                    (None, None) => {}
                    (Some(pattern), Some(value)) => work.push((pattern, value.clone())),
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

    fn sequential_effect_program() -> ValidatedEffectProgram {
        let text = concat!(
            "effect Ask {\nask : Int -> Int\n}\n\n",
            "main : Unit -> Int\nmain () = handle ({\n",
            "let first = perform Ask.ask 1\nperform Ask.ask first\n",
            "}) with Ask {\nask value => resume (value + 1)\n}\n",
        );
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
        let module = graph.module(graph.entry()).expect("entry remains loaded");
        let checked = check_module(resolve_module(module, &[]).expect("fixture should resolve"))
            .expect("fixture should check");
        let linked = link_modules(vec![checked], graph.entry()).expect("fixture should link");
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

    fn capture_machine(limit: usize) -> Machine {
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
        machine
            .frames
            .extend((0..3).map(|_| Frame::Request { node: root }));
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
        pure.frames.push(Frame::Request { node: root });
        assert_eq!(
            pure.capture_from(0).expect_err("Pure cannot capture"),
            RuntimeFailure::CapturedControlCapacity
        );
        assert_eq!(pure.frames.len(), 1);
        assert_eq!(pure.captured_cells, 0);

        let mut one_short = capture_machine(2);
        assert_eq!(
            one_short.capture_from(0).expect_err("one short must fail"),
            RuntimeFailure::CapturedControlCapacity
        );
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
            exact.frames.push(Frame::Request { node });
            assert_eq!(
                exact.capture_from(0).expect_err("cumulative quota is full"),
                RuntimeFailure::CapturedControlCapacity
            );
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
            Err(RuntimeFailure::CapturedControlCapacity)
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
        assert_eq!(EFFECT_TRANSITION_OWNERSHIP.len(), 4);
        assert_eq!(
            EFFECT_TRANSITION_OWNERSHIP
                .iter()
                .map(|owner| owner.feature)
                .collect::<Vec<_>>(),
            ["handler", "request", "resume", "clause boundary"]
        );
        assert!(EFFECT_TRANSITION_OWNERSHIP.iter().all(|owner| {
            !owner.entry.is_empty() && owner.frames.len() == 1 && owner.returns.len() == 1
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
