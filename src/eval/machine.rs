//! Loop-driven control transitions for the pure Mini-Ash machine.

use std::{error::Error, fmt, sync::Arc};

use super::{Closure, Value};
use crate::{
    core::{
        NodeId, Primitive, PureComputation, PureExprKind, PureProgram, PureValue, ValidatedProgram,
    },
    resolved::BinderId,
};

/// Inspectable lexical values available while evaluating one expression.
///
/// Environments are immutable entry-chain snapshots. Cloning and extension are
/// O(1); lookup is O(depth), walking from the newest binding toward the oldest.
/// Entry destruction dismantles uniquely owned tails iteratively so lexical
/// depth does not become Rust call-stack depth.
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
        members: Box<[RecursiveFunctionTemplate]>,
    },
}

struct RecursiveFunctionTemplate {
    binder: BinderId,
    parameter: BinderId,
    body: NodeId,
    origin: crate::source::Origin,
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
                        return Some(Value::Function(Closure {
                            parameter: member.parameter,
                            body: member.body,
                            program: Arc::clone(program),
                            environment: Self {
                                head: Some(Arc::clone(entry)),
                                len: entry.visible_len,
                            },
                            origin: member.origin.clone(),
                        }));
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

    fn extend_recursive(
        mut self,
        mut members: Vec<RecursiveFunctionTemplate>,
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

/// A completed value and its observational machine trace.
#[derive(Clone, Debug)]
pub struct Evaluation {
    /// The final runtime value.
    pub value: Value,
    /// Node-entry events in deterministic evaluation order.
    pub trace: Vec<TraceEvent>,
    /// Greatest number of explicit frames retained by the machine.
    pub max_frame_depth: usize,
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
    /// A validated recursive group did not contain function templates.
    UnexpectedRecursiveBinding,
    /// The runtime cannot represent another lexical environment entry.
    EnvironmentCapacity,
    /// Machine control completed without exactly one final value.
    InvalidControlState,
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
                "runtime recursive binding violates its validated function-group shape"
            }
            Self::EnvironmentCapacity => "runtime lexical environment capacity is exhausted",
            Self::InvalidControlState => "runtime machine control state is inconsistent",
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
        closure: Closure,
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
}

impl Machine {
    fn new(program: &ValidatedProgram) -> Self {
        Self {
            program: program.shared(),
            control: Some(Control::Evaluate(program.root(), Environment::new())),
            frames: Vec::new(),
            max_frame_depth: 0,
            trace: Vec::new(),
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
                    let transition = dispatch_entry(&self.program, node, environment)?;
                    self.apply(transition);
                }
                Control::Return(value) => {
                    let Some(frame) = self.frames.pop() else {
                        return Ok(Evaluation {
                            value,
                            trace: self.trace,
                            max_frame_depth: self.max_frame_depth,
                        });
                    };
                    let transition = dispatch_return(frame, value)?;
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
            enter_recursive_binding(program, group, environment)?
        }
        PureExprKind::Computation(PureComputation::Primitive(operation)) => {
            enter_primitive(*operation, environment)
        }
        PureExprKind::Computation(PureComputation::Apply(application)) => {
            enter_application(*application, environment)
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
) -> Result<Transition, RuntimeFailure> {
    let mut members = Vec::with_capacity(group.members().len());
    for member in group.members() {
        let initializer = program
            .node(member.initializer())
            .ok_or(RuntimeFailure::MissingNode)?;
        let PureExprKind::Value(PureValue::Function(function)) = &initializer.kind else {
            return Err(RuntimeFailure::UnexpectedRecursiveBinding);
        };
        members.push(RecursiveFunctionTemplate {
            binder: member.binder().id(),
            parameter: function.parameter().id(),
            body: function.body(),
            origin: initializer.origin.clone(),
        });
    }
    Ok(Transition::direct(Control::Evaluate(
        group.body(),
        environment.extend_recursive(members)?,
    )))
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

fn dispatch_return(frame: Frame, value: Value) -> Result<Transition, RuntimeFailure> {
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
        Frame::ApplyArgument { closure } => return_application_argument(closure, value),
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
    let Value::Function(closure) = function else {
        return Err(RuntimeFailure::UnexpectedFunctionValue);
    };
    Ok(Transition::suspend(
        Control::Evaluate(argument, caller_environment),
        Frame::ApplyArgument { closure },
    ))
}

fn return_application_argument(
    closure: Closure,
    argument: Value,
) -> Result<Transition, RuntimeFailure> {
    Ok(Transition::direct(Control::Evaluate(
        closure.body,
        closure.environment.extend(closure.parameter, argument)?,
    )))
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
        integer::Integer,
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
            frames: &[],
            returns: &[],
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
        let _: fn(&IntegerNode) -> Transition = enter_integer;
        let _: fn(BooleanNode) -> Transition = enter_boolean;
        let _: fn(UnitNode) -> Transition = enter_unit;
        let _: fn(
            &FunctionNode,
            Arc<PureProgram>,
            Environment,
            crate::source::Origin,
        ) -> Transition = enter_function;
        let _: fn(
            &Arc<PureProgram>,
            VariableNode,
            Environment,
        ) -> Result<Transition, RuntimeFailure> = enter_variable;
        let _: fn(&BindingNode, Environment) -> Transition = enter_binding;
        let _: fn(
            &Arc<PureProgram>,
            &crate::core::recursion::RecursiveBindingNode,
            Environment,
        ) -> Result<Transition, RuntimeFailure> = enter_recursive_binding;
        let _: fn(ApplicationNode, Environment) -> Transition = enter_application;
        let _: fn(PrimitiveNode, Environment) -> Transition = enter_primitive;
        let _: fn(BinderId, NodeId, Environment, Value) -> Result<Transition, RuntimeFailure> =
            return_binding;
        let _: fn(Primitive, NodeId, Environment, Value) -> Transition = return_primitive_left;
        let _: fn(Primitive, Value, Value) -> Result<Transition, RuntimeFailure> =
            return_primitive_right;
        let _: fn(NodeId, Environment, Value) -> Result<Transition, RuntimeFailure> =
            return_application_function;
        let _: fn(Closure, Value) -> Result<Transition, RuntimeFailure> =
            return_application_argument;

        assert_eq!(TRANSITION_OWNERSHIP.len(), 9);
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
                "variable",
                "binding",
                "recursive binding",
                "application",
                "primitive",
            ]
        );
        assert!(
            TRANSITION_OWNERSHIP
                .iter()
                .all(|owner| !owner.entry.is_empty())
        );
        assert!(
            TRANSITION_OWNERSHIP[..5]
                .iter()
                .all(|owner| owner.frames.is_empty() && owner.returns.is_empty())
        );
        assert!(
            [
                &TRANSITION_OWNERSHIP[5],
                &TRANSITION_OWNERSHIP[7],
                &TRANSITION_OWNERSHIP[8]
            ]
            .iter()
            .all(|owner| !owner.frames.is_empty() && !owner.returns.is_empty())
        );
        assert!(
            TRANSITION_OWNERSHIP[6].frames.is_empty() && TRANSITION_OWNERSHIP[6].returns.is_empty()
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

        assert!(matches!(
            dispatch_entry(&program, variable, Environment::new()),
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
}
