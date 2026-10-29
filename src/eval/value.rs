//! Runtime values for the Ash evaluator.

use std::{collections::HashSet, fmt, sync::Arc};

use super::machine::Environment;
use crate::{
    core::dialect::CoreProgram,
    core::{EffectExpr, EffectOperationFamily, NodeId, PureProgram, TypedExpr},
    integer::Integer,
    resolved::{BinderId, ResolvedRegistry},
    source::Origin,
    types::ConstructorId,
};

/// One validated Core arena retained by a runtime closure.
#[derive(Clone, Debug)]
pub enum ExecutableProgram {
    /// Pure Core.
    Pure(Arc<PureProgram>),
    /// Effect Core.
    Effect(Arc<CoreProgram<EffectOperationFamily>>),
}

/// A borrowed runtime node from either accepted Core family.
#[derive(Debug)]
pub enum ExecutableNode<'a> {
    /// A pure-family node.
    Pure(&'a TypedExpr),
    /// An effect-family node.
    Effect(&'a EffectExpr),
}

impl ExecutableProgram {
    /// Returns the root node of the retained arena.
    #[must_use]
    pub fn root(&self) -> NodeId {
        match self {
            Self::Pure(program) => program.root(),
            Self::Effect(program) => program.root(),
        }
    }

    /// Returns a node from the retained arena.
    #[must_use]
    pub fn node(&self, id: NodeId) -> Option<ExecutableNode<'_>> {
        match self {
            Self::Pure(program) => program.node(id).map(ExecutableNode::Pure),
            Self::Effect(program) => program.node(id).map(ExecutableNode::Effect),
        }
    }

    /// Returns the number of nodes in the retained arena.
    #[must_use]
    pub fn node_count(&self) -> usize {
        match self {
            Self::Pure(program) => program.node_count(),
            Self::Effect(program) => program.node_count(),
        }
    }

    /// Returns the immutable registry retained by the executable arena.
    #[must_use]
    pub fn registry(&self) -> &Arc<ResolvedRegistry> {
        match self {
            Self::Pure(program) => program.registry(),
            Self::Effect(program) => program.registry(),
        }
    }
}

pub(crate) type Location = usize;

#[derive(Debug)]
pub(crate) enum HeapCell {
    Uninitialized,
    Alias(Location),
    Tuple(Box<[Value]>),
    NativeTuple(NativeTupleStorage),
    Bytes(Box<[u8]>, usize, bool),
    NativeBytes(NativeByteStorage, bool),
    Constructor(ConstructorId, Option<Value>),
}

impl HeapCell {
    pub(crate) fn byte_fields(&self) -> Option<(&[u8], bool)> {
        match self {
            Self::Bytes(bytes, len, string) => Some((&bytes[..*len], *string)),
            Self::NativeBytes(bytes, string) => Some(((bytes.adapter.bytes)(bytes), *string)),
            _ => None,
        }
    }
    pub(super) fn stored_fields(&self) -> Option<&[Value]> {
        match self {
            Self::Tuple(fields) => Some(fields),
            Self::NativeTuple(fields) => Some((fields.adapter.fields)(fields)),
            _ => None,
        }
    }

    pub(crate) fn tuple_fields(&self) -> Option<&[Value]> {
        let fields = self.stored_fields()?;
        (!matches!(
            fields.first(),
            Some(Value::ConstructorTag(_) | Value::ClosureCode(_))
        ))
        .then_some(fields)
    }

    pub(crate) fn constructor_fields(&self) -> Option<(ConstructorId, Option<&Value>)> {
        if let Self::Constructor(id, payload) = self {
            return Some((*id, payload.as_ref()));
        }
        match self.stored_fields()? {
            [Value::ConstructorTag(id)] => Some((*id, None)),
            [Value::ConstructorTag(id), payload] => Some((*id, Some(payload))),
            _ => None,
        }
    }
}

/// Passive typed-memory leaves emitted once in the existing native host.
#[doc(hidden)]
#[derive(Clone, Copy, Debug)]
pub struct NativeTupleAdapter {
    pub initialize: fn(&mut NativeTupleStorage, Vec<Value>),
    pub fields: for<'a> fn(&'a NativeTupleStorage) -> &'a [Value],
    pub drop_fields: fn(&mut NativeTupleStorage),
    pub copy_bytes: fn(&NativeByteStorage, &[u8]),
    pub bytes: for<'a> fn(&'a NativeByteStorage) -> &'a [u8],
}

/// Unique borrowed-byte metadata; the paired provider owns backing release.
#[doc(hidden)]
#[derive(Debug)]
pub struct NativeByteStorage {
    address: Address,
    len: usize,
    adapter: NativeTupleAdapter,
}
impl NativeByteStorage {
    pub(crate) fn initialize(address: Address, bytes: &[u8], adapter: NativeTupleAdapter) -> Self {
        let storage = Self {
            address,
            len: bytes.len(),
            adapter,
        };
        (adapter.copy_bytes)(&storage, bytes);
        storage
    }
    pub fn address(&self) -> *mut core::ffi::c_void {
        self.address.as_ptr()
    }
    pub const fn len(&self) -> usize {
        self.len
    }
    pub const fn is_empty(&self) -> bool {
        self.len == 0
    }
}

/// Unique metadata for initialized values in module-supplied backing.
/// Drops Rust representation contents without freeing the module's backing.
#[doc(hidden)]
#[derive(Debug)]
pub struct NativeTupleStorage {
    address: Address,
    len: usize,
    adapter: NativeTupleAdapter,
    initialized: bool,
}
impl NativeTupleStorage {
    pub(crate) fn initialize(
        address: Address,
        values: Vec<Value>,
        adapter: NativeTupleAdapter,
    ) -> Self {
        let mut storage = Self {
            address,
            len: values.len(),
            adapter,
            initialized: false,
        };
        (adapter.initialize)(&mut storage, values);
        storage.initialized = true;
        storage
    }
    pub fn address(&self) -> *mut core::ffi::c_void {
        self.address.as_ptr()
    }
    pub const fn len(&self) -> usize {
        self.len
    }
    pub const fn is_empty(&self) -> bool {
        self.len == 0
    }
}
impl Drop for NativeTupleStorage {
    fn drop(&mut self) {
        if self.initialized {
            self.initialized = false;
            (self.adapter.drop_fields)(self);
        }
    }
}

/// An opaque non-owning registration issued by a worker's network transport.
#[derive(Clone, Copy, Debug)]
pub struct NetworkRegistration {
    pub(super) network: ActivationKey,
    pub(super) token: super::network_transport::Registration,
}

/// A heap-backed tuple or nominal observation.
#[derive(Clone)]
pub struct ObservedValue {
    heap: Arc<ObservedHeap>,
    root: Location,
    integer_sign: Option<bool>,
}

pub(crate) struct ObservedHeap {
    registry: Arc<ResolvedRegistry>,
    cells: Box<[HeapCell]>,
    root_completion: Option<super::machine::HostRootCompletion>,
}

impl Drop for ObservedHeap {
    fn drop(&mut self) {
        if let Some(root) = &mut self.root_completion {
            root.close(&mut self.cells);
        }
    }
}

impl ObservedHeap {
    #[cfg(test)]
    pub(crate) fn new(registry: Arc<ResolvedRegistry>, cells: Vec<HeapCell>) -> Arc<Self> {
        Self::with_root_completion(registry, cells, None)
    }

    pub(super) fn with_root_completion(
        registry: Arc<ResolvedRegistry>,
        cells: Vec<HeapCell>,
        root_completion: Option<super::machine::HostRootCompletion>,
    ) -> Arc<Self> {
        Arc::new(Self {
            registry,
            cells: cells.into_boxed_slice(),
            root_completion,
        })
    }

    #[cfg(test)]
    pub(crate) fn cells_for_test(&self) -> &[HeapCell] {
        &self.cells
    }

    #[cfg(test)]
    pub(crate) fn cells_mut_for_test(&mut self) -> &mut [HeapCell] {
        &mut self.cells
    }

    #[cfg(test)]
    pub(super) fn take_root_completion_for_test(
        &mut self,
    ) -> Option<super::machine::HostRootCompletion> {
        self.root_completion.take()
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
        Self {
            heap,
            root,
            integer_sign: None,
        }
    }

    pub(crate) fn integer(heap: Arc<ObservedHeap>, root: Location, negative: bool) -> Self {
        Self {
            heap,
            root,
            integer_sign: Some(negative),
        }
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
        let mut tasks = vec![
            self.integer_sign
                .map_or(Task::Location(self.root), |negative| {
                    Task::Value(Value::RegionInteger {
                        digits: self.root,
                        negative,
                    })
                }),
        ];
        while let Some(task) = tasks.pop() {
            match task {
                Task::Text(text) => output.push_str(text),
                Task::Exit(location) => {
                    active.remove(&location);
                }
                Task::Value(value) => match value {
                    Value::RegionRequest(_) => output.push_str("<allocation-request>"),
                    Value::RegionStorage(_) => output.push_str("<storage>"),
                    Value::RegionBackingFunction(_) => output.push_str("<function>"),
                    Value::RegionView(_) => output.push_str("<region-view>"),
                    Value::RegionHostFunction { .. } => output.push_str("<function>"),
                    Value::ResourceHandle(_) => output.push_str("<resource-handle>"),
                    Value::RetainedKey(_) => output.push_str("<retained-key>"),
                    Value::NetworkRegistration(_) => output.push_str("<network-registration>"),

                    Value::Intrinsic(_) => output.push_str("<function>"),
                    Value::Address(_) => output.push_str("<address>"),
                    Value::Bytes(value) => output.push_str(&format!("{value:?}")),
                    Value::String(value) => output.push_str(&format!("{value:?}")),

                    Value::SmallInteger(value) => output.push_str(&value.to_string()),
                    Value::RegionInteger { digits, negative } => {
                        let bytes = self
                            .heap
                            .cells
                            .get(digits)
                            .and_then(HeapCell::byte_fields)
                            .expect("initialized integer digits")
                            .0;
                        output.push_str(&Integer::from_sign_magnitude(negative, bytes).to_string());
                    }
                    Value::Integer(value) => output.push_str(&value.to_string()),
                    Value::Boolean(value) => output.push_str(if value { "true" } else { "false" }),
                    Value::Unit => output.push_str("()"),
                    Value::ClosureCode(_) => output.push_str("<private-closure-code>"),
                    Value::RegionFunction(_)
                    | Value::Function(_)
                    | Value::Polymorphic { .. }
                    | Value::ConstructorFunction(_) => output.push_str("<function>"),
                    Value::ConstructorTag(_) => output.push_str("<private-constructor-tag>"),
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
                                    cell if matches!(
                                        cell.stored_fields().and_then(|fields| fields.first()),
                                        Some(Value::ClosureCode(_))
                                    ) =>
                                    {
                                        output.push_str("<function>")
                                    }
                                    cell if cell.byte_fields().is_some() => {
                                        let (bytes, string) =
                                            cell.byte_fields().expect("byte backing");
                                        if string {
                                            output.push_str(&format!(
                                                "{:?}",
                                                std::str::from_utf8(bytes)
                                                    .expect("validated UTF-8")
                                            ));
                                        } else {
                                            output.push_str(&format!("{bytes:?}"));
                                        }
                                    }
                                    cell if cell.tuple_fields().is_some() => {
                                        let elements = cell.tuple_fields().expect("tuple fields");
                                        output.push('(');
                                        tasks.push(Task::Text(")"));
                                        for (index, element) in elements.iter().enumerate().rev() {
                                            tasks.push(Task::Value(element.clone()));
                                            if index > 0 {
                                                tasks.push(Task::Text(", "));
                                            }
                                        }
                                    }
                                    cell if cell.constructor_fields().is_some() => {
                                        let (id, payload) =
                                            cell.constructor_fields().expect("constructor fields");
                                        output.push_str(
                                            self.heap
                                                .registry
                                                .constructor(id)
                                                .map_or("<foreign-constructor>", |constructor| {
                                                    constructor.spelling.as_str()
                                                }),
                                        );
                                        if let Some(payload) = payload {
                                            output.push('(');
                                            tasks.push(Task::Text(")"));
                                            if let Value::Location(payload_location) = payload
                                                && let Some(elements) = self
                                                    .heap
                                                    .cells
                                                    .get(*payload_location)
                                                    .and_then(HeapCell::tuple_fields)
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
                                    _ => unreachable!("validated record shape"),
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
    pub program: ExecutableProgram,
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

/// A callable view. All captured term Values remain in the supplied record.
#[doc(hidden)]
#[derive(Clone, Debug)]
pub struct RegionFunction {
    pub(super) record: Location,
    pub(super) instantiation: Option<super::machine::Instantiation>,
    pub(super) abstraction: Option<NodeId>,
}

/// Code and lexical type/row metadata only; captured term Values follow in slots.
#[doc(hidden)]
#[derive(Clone, Debug)]
pub struct ClosureCode {
    pub(super) abstraction: Option<NodeId>,
    pub(super) node: NodeId,
    pub(super) program: ExecutableProgram,
    pub(super) instantiation: super::machine::Instantiation,
}

/// An inert foreign address. This value owns no memory behind its pointer.
///
/// Relaxed loads preserve the pointer for ordinary value transport; they do not
/// synchronize foreign memory or establish its validity or lifetime.
#[doc(hidden)]
pub struct Address(std::sync::atomic::AtomicPtr<core::ffi::c_void>);
impl Address {
    pub(crate) fn new(pointer: *mut core::ffi::c_void) -> Self {
        Self(std::sync::atomic::AtomicPtr::new(pointer))
    }
    pub(crate) fn as_ptr(&self) -> *mut core::ffi::c_void {
        self.0.load(std::sync::atomic::Ordering::Relaxed)
    }
}
impl Clone for Address {
    fn clone(&self) -> Self {
        Self::new(self.as_ptr())
    }
}
impl fmt::Debug for Address {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str("<address>")
    }
}

/// Immediate request facts; selected invocation metadata is compiler-private.
#[doc(hidden)]
#[derive(Clone, Copy, Debug)]
pub struct RegionRequest {
    pub(crate) usable_bytes: usize,
    pub(crate) alignment: usize,
    pub(crate) invocation: Option<RegionInvocation>,
}

#[doc(hidden)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct RegionInvocation {
    pub(crate) owner: ActivationKey,
    pub(crate) serial: u64,
}

/// A pending registered allocation; this token does not expose initialized data.
#[doc(hidden)]
#[derive(Clone, Copy, Debug)]
pub struct RegionStorage {
    pub(crate) invocation: RegionInvocation,
    pub(crate) record: usize,
}

/// A fully evaluated Ash value.
///
/// Values intentionally do not implement host equality because Ash functions
/// have no equality operation or observable identity.
#[derive(Clone, Debug)]
pub enum Value {
    /// Private, nonrecursive allocation request descriptor.
    RegionRequest(RegionRequest),
    /// Private, pending supplied storage token.
    RegionStorage(RegionStorage),
    /// The checked backing adapter bound by lexical type instantiation.
    RegionBackingFunction(ActivationKey),
    /// Non-owning explicit access to one published lexical region.
    RegionView(ActivationKey),
    /// A host member bound to its prospective owner's lexical activation.
    RegionHostFunction {
        /// Exact activation reserved before provider evaluation.
        owner: ActivationKey,
        /// True for the paired release member.
        release: bool,
    },
    /// Opaque C data pointer. Copying this value neither owns nor retains its target.
    Address(Address),
    /// Immutable finite bytes in ordinary shared storage.
    Bytes(Arc<[u8]>),
    /// Immutable UTF-8 text, including embedded NUL.
    String(Arc<str>),
    /// An authenticated compiler-owned first-order pure callable.
    Intrinsic(crate::core::packed::IntrinsicNode),

    /// An opaque, non-owning access key for a live resource activation.
    ResourceHandle(ActivationKey),

    /// A non-owning locator for one generation in a retained-control store.
    RetainedKey(RetainedKey),

    /// A private registration for one network activation and transport lane.
    NetworkRegistration(NetworkRegistration),

    /// A private genuinely inline mathematical integer representation.
    SmallInteger(i128),
    /// Sign and existing region-owned digit backing; aliases never copy digits.
    RegionInteger { digits: Location, negative: bool },
    /// Pure/no-region compatibility representation.
    Integer(Integer),
    /// A Boolean value.
    Boolean(bool),
    /// The unit value.
    Unit,
    /// A lexical unary function and its captured Ash environment.
    Function(Closure),
    /// A region-backed callable with an independent lexical instantiation view.
    RegionFunction(RegionFunction),
    /// Private code identity in the first supplied closure slot; never a callable.
    ClosureCode(ClosureCode),
    /// Internal lexical construction retained until validated Effect instantiation.
    Polymorphic {
        /// The admitted abstraction in the current executable arena.
        abstraction: NodeId,
        /// Its immutable lexical definition environment.
        environment: Environment,
    },
    /// A payload constructor awaiting its one ordinary argument.
    ConstructorFunction(ConstructorId),
    /// Private discriminant stored in region-backed nominal records.
    ConstructorTag(ConstructorId),
    /// An internal heap location used while the machine is running.
    Location(Location),
    /// A completed heap-backed structural observation.
    Data(ObservedValue),
}

impl Value {
    pub(crate) fn integer(value: Integer) -> Self {
        value
            .to_i128()
            .map_or_else(|| Self::Integer(value), Self::SmallInteger)
    }
    pub(crate) fn bytes(&self) -> Option<&[u8]> {
        match self {
            Self::Bytes(bytes) => Some(bytes),
            _ => None,
        }
    }
}

impl fmt::Display for Value {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::RegionRequest(_) => formatter.write_str("<allocation-request>"),
            Self::RegionStorage(_) => formatter.write_str("<storage>"),
            Self::RegionBackingFunction(_) => formatter.write_str("<function>"),
            Self::RegionView(_) => formatter.write_str("<region-view>"),
            Self::RegionHostFunction { .. } => formatter.write_str("<function>"),
            Self::ResourceHandle(_) => formatter.write_str("<resource-handle>"),
            Self::RetainedKey(_) => formatter.write_str("<retained-key>"),
            Self::NetworkRegistration(_) => formatter.write_str("<network-registration>"),

            Self::Intrinsic(_) => formatter.write_str("<function>"),
            Self::Address(_) => formatter.write_str("<address>"),
            Self::Bytes(value) => write!(formatter, "{value:?}"),
            Self::String(value) => write!(formatter, "{value:?}"),

            Self::SmallInteger(value) => value.fmt(formatter),
            Self::RegionInteger { .. } => formatter.write_str("<region-integer>"),
            Self::Integer(value) => value.fmt(formatter),
            Self::Boolean(value) => value.fmt(formatter),
            Self::Unit => formatter.write_str("()"),
            Self::Function(_) | Self::RegionFunction(_) => formatter.write_str("<function>"),
            Self::ClosureCode(_) => formatter.write_str("<private-closure-code>"),
            Self::Polymorphic { .. } => formatter.write_str("<function>"),
            Self::ConstructorFunction(_) => formatter.write_str("<function>"),
            Self::ConstructorTag(_) => formatter.write_str("<private-constructor-tag>"),
            Self::Location(_) => formatter.write_str("<location>"),
            Self::Data(value) => value.fmt(formatter),
        }
    }
}

/// An evaluator-created activation identity with no public constructor.
/// It carries no cell payload or ownership edge.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ActivationKey(pub(super) u32);

/// An evaluator-created locator. Copying it does not copy its owned control.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct RetainedKey {
    pub(super) activation: ActivationKey,
    pub(super) slot: usize,
    pub(super) generation: u64,
}
