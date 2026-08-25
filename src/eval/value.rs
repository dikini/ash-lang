//! Runtime values for the Ash evaluator.

use std::{collections::HashSet, fmt, sync::Arc};

use super::machine::Environment;
use crate::{
    core::{NodeId, PureProgram},
    integer::Integer,
    resolved::{BinderId, ResolvedRegistry},
    source::Origin,
    types::ConstructorId,
};

pub(crate) type Location = usize;

#[derive(Clone, Debug)]
pub(crate) enum HeapCell {
    Uninitialized,
    Alias(Location),
    Tuple(Box<[Value]>),
    Constructor(ConstructorId, Option<Value>),
}

/// A heap-backed tuple or nominal observation.
#[derive(Clone)]
pub struct ObservedValue {
    heap: Arc<ObservedHeap>,
    root: Location,
}

pub(crate) struct ObservedHeap {
    registry: Arc<ResolvedRegistry>,
    cells: Box<[HeapCell]>,
}

impl ObservedHeap {
    pub(crate) fn new(registry: Arc<ResolvedRegistry>, cells: Vec<HeapCell>) -> Arc<Self> {
        Arc::new(Self {
            registry,
            cells: cells.into_boxed_slice(),
        })
    }

    #[cfg(test)]
    pub(crate) fn cell_count(&self) -> usize {
        self.cells.len()
    }
}

impl fmt::Debug for ObservedHeap {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("ObservedHeap")
            .field("cells", &self.cells.len())
            .finish_non_exhaustive()
    }
}

impl ObservedValue {
    pub(crate) fn new(heap: Arc<ObservedHeap>, root: Location) -> Self {
        Self { heap, root }
    }

    fn render(&self) -> String {
        enum Task {
            Value(Value),
            Location(Location),
            Exit(Location),
            Text(&'static str),
        }
        let mut output = String::new();
        let mut active = HashSet::new();
        let mut tasks = vec![Task::Location(self.root)];
        while let Some(task) = tasks.pop() {
            match task {
                Task::Text(text) => output.push_str(text),
                Task::Exit(location) => {
                    active.remove(&location);
                }
                Task::Value(value) => match value {
                    Value::Integer(value) => output.push_str(&value.to_string()),
                    Value::Boolean(value) => output.push_str(if value { "true" } else { "false" }),
                    Value::Unit => output.push_str("()"),
                    Value::Function(_) | Value::ConstructorFunction(_) => {
                        output.push_str("<function>")
                    }
                    Value::Location(location) => tasks.push(Task::Location(location)),
                    Value::Data(value) => output.push_str(&value.render()),
                },
                Task::Location(requested) => {
                    let mut location = requested;
                    let mut aliases = HashSet::new();
                    loop {
                        if !aliases.insert(location) {
                            output.push_str("<alias-cycle>");
                            break;
                        }
                        match self.heap.cells.get(location) {
                            Some(HeapCell::Alias(next)) => location = *next,
                            Some(HeapCell::Uninitialized) => {
                                output.push_str("<uninitialized>");
                                break;
                            }
                            Some(cell) => {
                                if !active.insert(location) {
                                    output.push_str("<cycle>");
                                    break;
                                }
                                tasks.push(Task::Exit(location));
                                match cell {
                                    HeapCell::Tuple(elements) => {
                                        output.push('(');
                                        tasks.push(Task::Text(")"));
                                        for (index, element) in elements.iter().enumerate().rev() {
                                            tasks.push(Task::Value(element.clone()));
                                            if index > 0 {
                                                tasks.push(Task::Text(", "));
                                            }
                                        }
                                    }
                                    HeapCell::Constructor(id, payload) => {
                                        output.push_str(
                                            self.heap
                                                .registry
                                                .constructor(*id)
                                                .map_or("<foreign-constructor>", |constructor| {
                                                    constructor.spelling.as_str()
                                                }),
                                        );
                                        if let Some(payload) = payload {
                                            output.push('(');
                                            tasks.push(Task::Text(")"));
                                            if let Value::Location(payload_location) = payload
                                                && let Some(HeapCell::Tuple(elements)) =
                                                    self.heap.cells.get(*payload_location)
                                            {
                                                for (index, element) in
                                                    elements.iter().enumerate().rev()
                                                {
                                                    tasks.push(Task::Value(element.clone()));
                                                    if index > 0 {
                                                        tasks.push(Task::Text(", "));
                                                    }
                                                }
                                            } else {
                                                tasks.push(Task::Value(payload.clone()));
                                            }
                                        }
                                    }
                                    HeapCell::Uninitialized | HeapCell::Alias(_) => unreachable!(),
                                }
                                break;
                            }
                            None => {
                                output.push_str("<invalid-location>");
                                break;
                            }
                        }
                    }
                }
            }
        }
        output
    }
}

impl fmt::Debug for ObservedValue {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("ObservedValue")
            .field("root", &self.root)
            .field("heap_cells", &self.heap.cells.len())
            .finish()
    }
}

impl fmt::Display for ObservedValue {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(&self.render())
    }
}

/// An inspectable lexical Ash function value.
#[derive(Clone)]
pub struct Closure {
    /// Resolver identity bound when the function is applied.
    pub parameter: BinderId,
    /// Core body evaluated after parameter binding.
    pub body: NodeId,
    /// Validated code arena containing `body`.
    pub program: Arc<PureProgram>,
    /// Immutable lexical environment captured at function evaluation.
    pub environment: Environment,
    /// Causal source provenance of the function value.
    pub origin: Origin,
}

impl fmt::Debug for Closure {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("Closure")
            .field("parameter", &self.parameter)
            .field("body", &self.body)
            .field("program_node_count", &self.program.node_count())
            .field("environment", &self.environment)
            .field("origin", &self.origin)
            .finish()
    }
}

/// A fully evaluated Ash value.
///
/// Values intentionally do not implement host equality because Ash functions
/// have no equality operation or observable identity.
#[derive(Clone, Debug)]
pub enum Value {
    /// An arbitrary-precision mathematical integer.
    Integer(Integer),
    /// A Boolean value.
    Boolean(bool),
    /// The unit value.
    Unit,
    /// A lexical unary function and its captured Ash environment.
    Function(Closure),
    /// A payload constructor awaiting its one ordinary argument.
    ConstructorFunction(ConstructorId),
    /// An internal heap location used while the machine is running.
    Location(Location),
    /// A completed heap-backed structural observation.
    Data(ObservedValue),
}

impl fmt::Display for Value {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Integer(value) => value.fmt(formatter),
            Self::Boolean(value) => value.fmt(formatter),
            Self::Unit => formatter.write_str("()"),
            Self::Function(_) => formatter.write_str("<function>"),
            Self::ConstructorFunction(_) => formatter.write_str("<function>"),
            Self::Location(_) => formatter.write_str("<location>"),
            Self::Data(value) => value.fmt(formatter),
        }
    }
}
