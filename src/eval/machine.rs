//! Loop-driven control transitions for the pure Mini-Ash machine.

use std::{collections::HashMap, error::Error, fmt, sync::Arc};

use super::Value;
use crate::{
    core::{
        NodeId, Primitive, PureComputation, PureExprKind, PureProgram, PureValue, ValidatedProgram,
    },
    resolved::BinderId,
};

/// Inspectable lexical values available while evaluating one expression.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Environment {
    bindings: HashMap<BinderId, Value>,
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
        self.bindings.len()
    }

    /// Reports whether the environment captures no lexical values.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.bindings.is_empty()
    }
}

/// The machine's current first-order control state.
#[derive(Clone, Debug, Eq, PartialEq)]
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
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Evaluation {
    /// The final primitive value.
    pub value: Value,
    /// Node-entry events in deterministic evaluation order.
    pub trace: Vec<TraceEvent>,
}

/// A structured evaluator invariant or pending-form failure.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum RuntimeFailure {
    /// A validated handle did not identify a node in the validated program.
    MissingNode,
    /// A validated primitive reached a value kind outside its signature.
    UnexpectedPrimitiveValue,
    /// This retained evaluator increment does not yet execute the Core form.
    UnsupportedForm,
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
            Self::UnsupportedForm => "validated Core form is pending evaluator implementation",
            Self::InvalidControlState => "runtime machine control state is inconsistent",
        })
    }
}

impl Error for RuntimeFailure {}

#[derive(Clone, Debug, Eq, PartialEq)]
enum Frame {
    PrimitiveLeft {
        primitive: Primitive,
        right: NodeId,
        environment: Environment,
    },
    PrimitiveRight {
        primitive: Primitive,
        left: Value,
    },
}

/// The retained explicit evaluator machine.
#[derive(Debug)]
pub struct Machine {
    program: Arc<PureProgram>,
    control: Control,
    frames: Vec<Frame>,
    trace: Vec<TraceEvent>,
}

impl Machine {
    fn new(program: &ValidatedProgram) -> Self {
        Self {
            program: program.shared(),
            control: Control::Evaluate(program.root(), Environment::new()),
            frames: Vec::new(),
            trace: Vec::new(),
        }
    }

    fn run(mut self) -> Result<Evaluation, RuntimeFailure> {
        loop {
            match self.control {
                Control::Evaluate(node, environment) => {
                    self.trace.push(TraceEvent::Enter(node));
                    let expression = self.program.node(node).ok_or(RuntimeFailure::MissingNode)?;
                    match &expression.kind {
                        PureExprKind::Value(PureValue::Integer(integer)) => {
                            self.control = Control::Return(Value::Integer(integer.value().clone()));
                        }
                        PureExprKind::Value(PureValue::Boolean(boolean)) => {
                            self.control = Control::Return(Value::Boolean(boolean.value()));
                        }
                        PureExprKind::Value(PureValue::Unit(_)) => {
                            self.control = Control::Return(Value::Unit);
                        }
                        PureExprKind::Computation(PureComputation::Primitive(operation)) => {
                            self.frames.push(Frame::PrimitiveLeft {
                                primitive: operation.primitive(),
                                right: operation.right(),
                                environment: environment.clone(),
                            });
                            self.control = Control::Evaluate(operation.left(), environment);
                        }
                        PureExprKind::Value(PureValue::Function(_))
                        | PureExprKind::Variable(_)
                        | PureExprKind::Computation(
                            PureComputation::Bind(_) | PureComputation::Apply(_),
                        ) => return Err(RuntimeFailure::UnsupportedForm),
                    }
                }
                Control::Return(value) => {
                    let Some(frame) = self.frames.pop() else {
                        return Ok(Evaluation {
                            value,
                            trace: self.trace,
                        });
                    };
                    match frame {
                        Frame::PrimitiveLeft {
                            primitive,
                            right,
                            environment,
                        } => {
                            self.frames.push(Frame::PrimitiveRight {
                                primitive,
                                left: value,
                            });
                            self.control = Control::Evaluate(right, environment);
                        }
                        Frame::PrimitiveRight { primitive, left } => {
                            self.control =
                                Control::Return(apply_primitive(primitive, left, value)?);
                        }
                    }
                }
            }
        }
    }
}

/// Evaluates one independently validated pure Core program.
///
/// # Errors
///
/// Returns a structured runtime failure if a validated-input assumption is
/// violated or the program contains a form assigned to a later increment.
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
