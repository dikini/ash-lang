//! Loop-driven control transitions for the pure Mini-Ash machine.

use std::{error::Error, fmt, sync::Arc};

use super::Value;
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
    binder: BinderId,
    value: Value,
    parent: Option<Arc<Self>>,
}

impl Drop for EnvironmentEntry {
    fn drop(&mut self) {
        let mut parent = self.parent.take();
        while let Some(entry) = parent {
            // When concurrent owners each consume one clone with `into_inner`,
            // exactly one receives the entry. That owner continues iterative
            // dismantling; the others stop at the still-shared prefix.
            let Some(mut unique) = Arc::into_inner(entry) else {
                break;
            };
            parent = unique.parent.take();
        }
    }
}

impl fmt::Debug for Environment {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut binders = Vec::with_capacity(self.len);
        let mut current = self.head.as_deref();
        while let Some(entry) = current {
            binders.push(entry.binder);
            current = entry.parent.as_deref();
        }
        formatter
            .debug_struct("Environment")
            .field("len", &self.len)
            .field("binders_newest_first", &binders)
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

    fn lookup(&self, binder: BinderId) -> Option<&Value> {
        let mut current = self.head.as_deref();
        while let Some(entry) = current {
            if entry.binder == binder {
                return Some(&entry.value);
            }
            current = entry.parent.as_deref();
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
                binder,
                value,
                parent: self.head.take(),
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
    /// A validated variable did not have a runtime lexical binding.
    MissingBinding,
    /// The runtime cannot represent another lexical environment entry.
    EnvironmentCapacity,
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
            Self::MissingBinding => "runtime lexical binding is absent",
            Self::EnvironmentCapacity => "runtime lexical environment capacity is exhausted",
            Self::UnsupportedForm => "validated Core form is pending evaluator implementation",
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
                        PureExprKind::Variable(variable) => {
                            let value = environment
                                .lookup(variable.binder())
                                .cloned()
                                .ok_or(RuntimeFailure::MissingBinding)?;
                            self.control = Control::Return(value);
                        }
                        PureExprKind::Computation(PureComputation::Bind(binding)) => {
                            self.frames.push(Frame::Bind {
                                binder: binding.binder().id(),
                                body: binding.body(),
                                environment: environment.clone(),
                            });
                            self.control = Control::Evaluate(binding.initializer(), environment);
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
                        | PureExprKind::Computation(PureComputation::Apply(_)) => {
                            return Err(RuntimeFailure::UnsupportedForm);
                        }
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
                        Frame::Bind {
                            binder,
                            body,
                            environment,
                        } => {
                            self.control =
                                Control::Evaluate(body, environment.extend(binder, value)?);
                        }
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

#[cfg(test)]
mod tests {
    use std::sync::{Arc, Barrier};

    use super::*;
    use crate::integer::Integer;

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
}
