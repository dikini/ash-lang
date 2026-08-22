//! Loop-driven control transitions for the pure Mini-Ash machine.

use std::{error::Error, fmt, sync::Arc};

use super::{
    Closure, Value,
    value::{HeapCell, Location, ObservedHeap, ObservedValue},
};
use crate::{
    core::{
        CoreMatchArm, CorePattern, CorePatternKind, NodeId, Primitive, PureComputation,
        PureExprKind, PureProgram, PureValue, ValidatedProgram,
    },
    resolved::BinderId,
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

    fn lookup(&self, binder: BinderId, program: &Arc<PureProgram>) -> Option<Value> {
        let mut current = self.head.as_ref();
        while let Some(entry) = current {
            match &entry.kind {
                EnvironmentEntryKind::Binding {
                    binder: entry_binder,
                    value,
                } if *entry_binder == binder => return Some(value.clone()),
                EnvironmentEntryKind::Recursive { members } => {
                    if let Ok(index) = members
                        .binary_search_by_key(&binder.value(), |member| member.binder.value())
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
                                program: Arc::clone(program),
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
        members.sort_unstable_by_key(|member| member.binder.value());
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
    heap: Arc<ObservedHeap>,
}

impl Evaluation {
    pub(crate) fn into_observation_parts(self) -> (Value, Arc<ObservedHeap>) {
        (self.value, self.heap)
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
    /// A heap location is outside the current evaluation.
    InvalidLocation,
    /// Evaluation forced a recursive slot before initialization.
    UninitializedLocation,
    /// Heap aliases form a cycle without a constructed value.
    AliasLoop,
    /// Independently validated coverage selected no arm.
    ImpossibleMatch,
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

/// The retained explicit evaluator machine.
#[derive(Debug)]
pub struct Machine {
    program: Arc<PureProgram>,
    control: Option<Control>,
    frames: Vec<Frame>,
    max_frame_depth: usize,
    trace: Vec<TraceEvent>,
    heap: Vec<HeapCell>,
}

impl Machine {
    fn new(program: &ValidatedProgram) -> Self {
        Self {
            program: program.shared(),
            control: Some(Control::Evaluate(program.root(), Environment::new())),
            frames: Vec::new(),
            max_frame_depth: 0,
            trace: Vec::new(),
            heap: Vec::new(),
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
                            heap,
                        });
                    };
                    let transition = dispatch_return(frame, value, &mut self.heap)?;
                    self.apply(transition);
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
}

fn dispatch_entry(
    program: &Arc<PureProgram>,
    node: NodeId,
    environment: Environment,
    heap: &mut Vec<HeapCell>,
) -> Result<Transition, RuntimeFailure> {
    let expression = program.node(node).ok_or(RuntimeFailure::MissingNode)?;
    Ok(match &expression.kind {
        PureExprKind::Value(PureValue::Integer(integer)) => enter_integer(integer),
        PureExprKind::Value(PureValue::Boolean(boolean)) => enter_boolean(*boolean),
        PureExprKind::Value(PureValue::Unit(unit)) => enter_unit(*unit),
        PureExprKind::Value(PureValue::Function(function)) => enter_function(
            function,
            Arc::clone(program),
            environment,
            expression.origin.clone(),
        ),
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
    program: &Arc<PureProgram>,
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

fn enter_function(
    function: &crate::core::function::FunctionNode,
    program: Arc<PureProgram>,
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
    program: &Arc<PureProgram>,
    variable: crate::core::variable::VariableNode,
    environment: Environment,
) -> Result<Transition, RuntimeFailure> {
    let value = environment
        .lookup(variable.binder(), program)
        .ok_or(RuntimeFailure::MissingBinding)?;
    Ok(Transition::direct(Control::Return(value)))
}

fn enter_recursive_binding(
    program: &Arc<PureProgram>,
    group: &crate::core::recursion::RecursiveBindingNode,
    environment: Environment,
    heap: &mut Vec<HeapCell>,
) -> Result<Transition, RuntimeFailure> {
    let mut members = Vec::with_capacity(group.members().len());
    let mut pending = Vec::new();
    for member in group.members() {
        let initializer = program
            .node(member.initializer())
            .ok_or(RuntimeFailure::MissingNode)?;
        let kind = match &initializer.kind {
            PureExprKind::Value(PureValue::Function(function)) => RecursiveMemberKind::Function {
                parameter: function.parameter().id(),
                body: function.body(),
                origin: initializer.origin.clone(),
            },
            _ if matches!(member.binder().ty(), crate::types::Type::Nominal(_)) => {
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
            CoreBuilder, binding::BindingNode, function::ApplicationNode, function::FunctionNode,
            literal::BooleanNode, literal::IntegerNode, literal::UnitNode,
            primitive::PrimitiveNode, validate, variable::VariableNode,
        },
        elaborate::Elaborator,
        integer::Integer,
        lexer::lex,
        parser::{parse, project},
        resolve::resolve,
        source::{ByteRange, Origin, SourceFile},
        types::Type,
    };

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
            &Arc<PureProgram>,
            &crate::core::recursion::RecursiveBindingNode,
            Environment,
            &mut Vec<HeapCell>,
        ) -> Result<Transition, RuntimeFailure>;
        type EnterConstructor = fn(
            &Arc<PureProgram>,
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
            Arc<PureProgram>,
            Environment,
            crate::source::Origin,
        ) -> Transition = enter_function;
        let _: EnterConstructor = enter_constructor;
        let _: fn(
            &Arc<PureProgram>,
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

        assert_eq!(TRANSITION_OWNERSHIP.len(), 12);
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

        assert!(matches!(
            dispatch_entry(&program, variable, Environment::new(), &mut Vec::new()),
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
        let source = SourceFile::new(
            "recursive-data-order.ash",
            "type Flag =\nFirst\n| Second\n\n{\nlet rec first : Flag = First\nand second : Flag = Second\nfirst\n}\n",
        )
        .expect("test source");
        let tree = parse(lex(&source).expect("source should lex"));
        let surface = project(&source, &tree).expect("source should project");
        let resolved = resolve(&surface).expect("source should resolve");
        let mut elaborator = Elaborator::for_program(&resolved).expect("reserve binders");
        let typed = elaborator
            .synthesize_program(&resolved)
            .expect("source should elaborate");
        let validated = validate(
            elaborator.finish(typed.node).expect("Core should finish"),
            &[&source],
        )
        .expect("Core should validate");
        let program = validated.shared();
        let root = program.node(program.root()).expect("recursive root");
        let PureExprKind::Computation(PureComputation::RecursiveBind(group)) = &root.kind else {
            panic!("block should lower to one recursive group")
        };
        let [first, second] = group.members() else {
            panic!("fixture should have two recursive data members")
        };

        let mut heap = Vec::new();
        let transition = enter_recursive_binding(&program, group, Environment::new(), &mut heap)
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
            recursive_environment.lookup(first.binder().id(), &program),
            Some(Value::Location(0))
        ));
        assert!(matches!(
            recursive_environment.lookup(second.binder().id(), &program),
            Some(Value::Location(1))
        ));

        let first_value = dispatch_entry(
            &program,
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
            &program,
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
        let source = SourceFile::new(
            "returned-structural-capture.ash",
            "{\nlet pair = (20, 22)\nlet keep : Unit -> (Int, Int) = fn(ignored) {\npair\n}\nkeep\n}\n",
        )
        .expect("test source");
        let tree = parse(lex(&source).expect("source should lex"));
        let surface = project(&source, &tree).expect("source should project");
        let resolved = resolve(&surface).expect("source should resolve");
        let mut elaborator = Elaborator::for_program(&resolved).expect("reserve binders");
        let typed = elaborator
            .synthesize_program(&resolved)
            .expect("source should elaborate");
        let validated = validate(
            elaborator.finish(typed.node).expect("Core should finish"),
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
                        program: Arc::clone(&program),
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
                    .lookup(BinderId::new(MEMBERS / 2), &program)
                    .expect("member should materialize");
                assert_eq!(Arc::strong_count(&frame), 3);
                let second_value = environment
                    .lookup(BinderId::new(MEMBERS / 2 + 1), &program)
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
}
