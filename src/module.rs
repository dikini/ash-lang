//! Canonical source loading for passive module graphs.

#[cfg(test)]
#[path = "module_staged_tests.rs"]
mod staged_tests;

use std::{
    borrow::Borrow,
    collections::{HashMap, HashSet, VecDeque},
    error::Error,
    fmt, fs, io,
    path::{Path, PathBuf},
    sync::atomic::{AtomicU32, Ordering},
};

use crate::{
    diagnostic::Diagnostic,
    lexer::{LexReason, lex_with_budget},
    parser::{
        ParseDiagnostic, ParserCheckpoint, ProjectionError, ResourceFailure,
        finish_module_from_checkpoint_with_syntax, module_span_from_checkpoint,
        parse_module_header, parse_with_budget_and_header, project_module, project_module_header,
    },
    source::{SourceError, SourceFile, SourceId, Span},
    surface::{
        SurfaceImport, SurfaceImportItem, SurfaceImportSelection, SurfaceModule, SurfaceModulePath,
    },
    syntax_resource::SyntaxBudget,
};

/// Maximum source files admitted by one module graph.
pub const MODULE_SOURCE_LIMIT: usize = 16_384;
/// Maximum import edges retained by one module graph.
pub const MODULE_EDGE_LIMIT: usize = 65_536;
/// Maximum module path segments processed by one module graph.
pub const MODULE_PATH_SEGMENT_LIMIT: usize = 262_144;
/// Maximum retained canonical-module and owning-root relations in one graph.
pub const MODULE_OWNER_FACT_LIMIT: usize = 262_144;
/// Maximum active traversal and owner-propagation work items.
pub const MODULE_PENDING_LIMIT: usize = 16_384;

const COMPILER_SYNTAX_SOURCE: &str = include_str!("compiler_syntax.ash");

const CELL_SOURCE: &str = concat!(
    "pub opaque type Handle<R> = Hidden\n",
    "pub effect Ops<R> {\nread : Handle<R> -> Int\nwrite : (Handle<R>, Int) -> Unit\n}\n",
    "pub interface Provider<R> {\nread : Handle<R> -> Int ! {Ops<R>}\nwrite : (Handle<R>, Int) -> Unit ! {Ops<R>}\n}\n",
);

const GENERIC_CELL_SOURCE: &str = concat!(
    "pub opaque type Cell<R,T> = Hidden\n",
    "pub effect Ops<R,T> {\nread : Cell<R,T> -> T\nwrite : (Cell<R,T>, T) -> Unit\n}\n",
    "pub interface Provider<R,T> {\nread : Cell<R,T> -> T ! {Ops<R,T>}\nwrite : (Cell<R,T>, T) -> Unit ! {Ops<R,T>}\n}\n",
);

// These types identify a local store and its non-owning locators. The
// compiler authenticates the complete source before granting either role.
const RETAINED_CONTROL_SOURCE: &str = concat!(
    "pub opaque type Store<N,D> = HiddenStore\n",
    "pub opaque type Key<N> = HiddenKey\n",
    "pub type Option<A> = None\n| Some(A)\n",
    "pub effect Drive<N> {\ninternal : Unit -> Unit\n}\n",
    "pub effect Probe<N> {\nquiescent : Unit -> Bool\n}\n",
    "pub advance<N,A,E : EffectRow> : (Store<N,(Unit -> A ! {| E})>, Key<N>) -> Option<A> ! {Drive<N> | E}\n",
    "advance pair = advance pair\n",
    "pub advance_with_drive<N,A,E : EffectRow> : (Store<N,(Unit -> A ! {Drive<N> | E})>, Key<N>) -> Option<A> ! {Drive<N> | E}\n",
    "advance_with_drive pair = advance_with_drive pair\n",
);

const NETWORK_SOURCE: &str = concat!(
    "pub opaque type Pair<N> = HiddenPair\n",
    "pub opaque type Worker<N> = HiddenWorker\n",
    "pub opaque type Registration<N> = HiddenRegistration\n",
    "pub type EnvelopeKind = Application\n| Control\n",
    "pub type Failure = Refused\n| Uncertain\n| WorkerFailed\n| IncompleteTeardown\n",
    "pub type SendResult = Sent\n| Full\n| Closed\n| SendFailed(Failure)\n",
    "pub type ReceiveResult = Message(EnvelopeKind, Bytes)\n| Empty\n| End\n| ReceiveFailed(Failure)\n",
    "pub type FinishResult = Ok\n| Failed(Failure)\n",
    "pub type Interest = Readable\n| Writable\n",
    "pub type WatchResult<N> = Watching(Registration<N>)\n| WatchFailed(Failure)\n",
    "pub type WakeResult<N> = Wake(Registration<N>)\n| NoWake\n| WakeFailed(Failure)\n",
    "pub effect IO<N> {\ninternal : Unit -> Unit\nsend : (Worker<N>, Bytes) -> SendResult\nreceive : Worker<N> -> ReceiveResult\nfinish : Worker<N> -> FinishResult\nwatch_internal : (Worker<N>, Interest) -> WatchResult<N>\ncancel_internal : (Worker<N>, Registration<N>) -> FinishResult\npoll_internal : Worker<N> -> WakeResult<N>\nfinish_receive_internal : Worker<N> -> FinishResult\nsend_control_internal : (Worker<N>, Bytes) -> SendResult\n}\n",
    "pub effect Join<N> {\ninternal : Unit -> Unit\nsettle_internal : Pair<N> -> FinishResult\n}\n",
    "pub try_send<N> : (Worker<N>, Bytes) -> SendResult ! {IO<N>}\ntry_send value = perform IO<N>.send value\n",
    "pub try_receive<N> : Worker<N> -> ReceiveResult ! {IO<N>}\ntry_receive value = perform IO<N>.receive value\n",
    "pub finish_send<N> : Worker<N> -> FinishResult ! {IO<N>}\nfinish_send value = finish_send value\n",
    "pub finish_receive<N> : Worker<N> -> FinishResult ! {IO<N>}\nfinish_receive value = finish_receive value\n",
    "pub watch<N> : (Worker<N>, Interest) -> WatchResult<N> ! {IO<N>}\nwatch value = watch value\n",
    "pub cancel_watch<N> : (Worker<N>, Registration<N>) -> FinishResult ! {IO<N>}\ncancel_watch value = cancel_watch value\n",
    "pub poll_wake<N> : Worker<N> -> WakeResult<N> ! {IO<N>}\npoll_wake value = poll_wake value\n",
    "pub settle<N> : Pair<N> -> FinishResult ! {Join<N>}\nsettle value = settle value\n",
    "pub send_control<N> : (Worker<N>, Bytes) -> SendResult ! {IO<N>}\nsend_control value = send_control value\n",
);

// One authenticated identity supplies the public binding facade and private
// generated allocation service. Importing the facade never exposes ownership.
const REGION_SOURCE: &str = concat!(
    "import @builtin.foreign as Foreign\n",
    "pub opaque type Request = HiddenRequest\n",
    "pub opaque type Storage<R> = HiddenStorage\n",
    "pub opaque type StorageView = HiddenStorageView\n",
    "pub opaque type RegionView = HiddenRegionView\n",
    "effect DefaultAlloc {\n",
    "allocate : Request -> StorageView\n",
    "context : Unit -> RegionView\n",
    "}\n",
    "pub usable_bytes : Request -> Int ! {DefaultAlloc}\nusable_bytes request = usable_bytes request\n",
    "pub alignment : Request -> Int ! {DefaultAlloc}\nalignment request = alignment request\n",
    "pub from_backing<R> : (Request, Foreign.Address, Int, Int) -> Storage<R> ! {DefaultAlloc}\nfrom_backing value = from_backing value\n",
);

// Ordinary selected reexports keep the generated service and views private.
const REGION_FACADE_SOURCE: &str = "pub import @builtin.region_service (Request, Storage, usable_bytes, alignment, from_backing)\n";

const INTEGER_SOURCE: &str = concat!(
    "pub type SplitResult = Parts((Int, Int))\n| Negative\n",
    "pub split_base256 : Int -> SplitResult\nsplit_base256 value = split_base256 value\n",
);

const BYTES_SOURCE: &str = concat!(
    "pub type AppendResult = BytesAppended(Bytes)\n| InvalidByte\n",
    "pub empty : Unit -> Bytes\nempty value = empty value\n",
    "pub append_byte : (Bytes, Int) -> AppendResult\nappend_byte value = append_byte value\n",
    "pub length : Bytes -> Int\nlength value = length value\n",
    "pub equal : (Bytes, Bytes) -> Bool\nequal value = equal value\n",
    "pub type ReadResult = ByteAt(Int)\n| InvalidIndex\n",
    "pub at : (Bytes, Int) -> ReadResult\nat value = at value\n",
);
const STRING_SOURCE: &str = concat!(
    "pub type DecodeResult = Decoded(String)\n| InvalidUtf8\n",
    "pub to_utf8 : String -> Bytes\nto_utf8 value = to_utf8 value\n",
    "pub from_utf8 : Bytes -> DecodeResult\nfrom_utf8 value = from_utf8 value\n",
    "pub byte_length : String -> Int\nbyte_length value = byte_length value\n",
    "pub equal : (String, String) -> Bool\nequal value = equal value\n",
);

// The common codec identities follow declaration order: ConversionError is
// nominal 0 and Call is nominal 1, with Returned 0 and ConversionFailed 1.
// ConversionError's private representation does not define a public inventory
// of conversion causes; only its opaque nominal identity is source-accessible.
const FOREIGN_SOURCE: &str = concat!(
    "pub opaque type Address = HiddenAddress\n",
    "pub null : Unit -> Address\nnull value = null value\n",
    "pub is_null : Address -> Bool\nis_null value = is_null value\n",
    "pub equal : (Address, Address) -> Bool\nequal value = equal value\n",
);

/// A validated name for one configured module root.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct ModuleRootName(String);

impl ModuleRootName {
    /// Validates one named-root spelling.
    ///
    /// # Errors
    ///
    /// Returns a non-source module failure when `name` is not an Ash lowercase
    /// identifier.
    pub fn new(name: impl Into<String>) -> Result<Self, ModuleFailure> {
        let name = name.into();
        if !is_lower_identifier(&name) {
            return Err(ModuleFailure::invocation(
                ModuleReason::InvalidRootName,
                None,
                Some(name),
                None,
            ));
        }
        Ok(Self(name))
    }

    /// Returns the validated root spelling.
    #[must_use]
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

impl Borrow<str> for ModuleRootName {
    fn borrow(&self) -> &str {
        self.as_str()
    }
}

/// Canonical paths configured under validated module-root names.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct ModuleRoots {
    named: HashMap<ModuleRootName, PathBuf>,
}

impl ModuleRoots {
    /// Creates an empty named-root configuration.
    #[must_use]
    pub fn empty() -> Self {
        Self::default()
    }

    /// Validates names, rejects duplicates, and canonicalizes configured paths.
    ///
    /// Duplicate names are rejected before any configured path is inspected.
    ///
    /// # Errors
    ///
    /// Returns an invocation failure for an invalid or duplicate name, a path
    /// that cannot be canonicalized, or a path that is not a directory.
    pub fn new<I, N, P>(roots: I) -> Result<Self, ModuleFailure>
    where
        I: IntoIterator<Item = (N, P)>,
        N: Into<String>,
        P: Into<PathBuf>,
    {
        let mut pending = Vec::new();
        let mut names = HashSet::new();
        for (name, path) in roots {
            let name = ModuleRootName::new(name)?;
            if matches!(name.as_str(), "builtin" | "foreign") {
                return Err(ModuleFailure::invocation(
                    ModuleReason::ReservedRoot,
                    None,
                    Some(name.0),
                    None,
                ));
            }
            if !names.insert(name.clone()) {
                return Err(ModuleFailure::invocation(
                    ModuleReason::DuplicateRoot,
                    None,
                    Some(name.0),
                    None,
                ));
            }
            pending.push((name, path.into()));
        }

        let mut named = HashMap::with_capacity(pending.len());
        for (name, path) in pending {
            let canonical = fs::canonicalize(&path).map_err(|error| {
                ModuleFailure::invocation(
                    ModuleReason::RootUnavailable,
                    Some(path.clone()),
                    Some(name.0.clone()),
                    Some(error.kind()),
                )
            })?;
            let is_directory = fs::metadata(&canonical)
                .map(|metadata| metadata.is_dir())
                .unwrap_or(false);
            if !is_directory {
                return Err(ModuleFailure::invocation(
                    ModuleReason::RootUnavailable,
                    Some(canonical),
                    Some(name.0),
                    None,
                ));
            }
            named.insert(name, canonical);
        }
        Ok(Self { named })
    }
}

/// Stable identity assigned when one canonical module source is admitted.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ModuleId {
    namespace: ModuleIdNamespace,
    graph: u32,
    value: u32,
}

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum ModuleIdNamespace {
    Admitted,
    BuiltinCell,
    BuiltinGenericCell,
    BuiltinRetainedControl,
    BuiltinNetwork,
    BuiltinRegion,
    BuiltinRegionFacade,
    BuiltinBytes,
    BuiltinString,
    BuiltinInteger,
    BuiltinForeign,
    BuiltinCompilerSyntax,
    DirectCoreSource,
}

impl ModuleId {
    pub(crate) const fn is_admitted_source(self) -> bool {
        matches!(self.namespace, ModuleIdNamespace::Admitted)
    }

    pub(crate) const fn is_direct_core_source(self) -> bool {
        matches!(self.namespace, ModuleIdNamespace::DirectCoreSource)
    }

    /// Reconstructs one graph-local module identity from its numeric value.
    ///
    /// Compiler stages should normally obtain identities from [`LoadedModule`].
    #[cfg(test)]
    #[must_use]
    pub(crate) const fn new(value: u32) -> Self {
        Self {
            namespace: ModuleIdNamespace::Admitted,
            graph: 0,
            value,
        }
    }

    const fn admitted(graph: u32, value: u32) -> Self {
        Self {
            namespace: ModuleIdNamespace::Admitted,
            graph,
            value,
        }
    }

    fn index(self) -> usize {
        debug_assert!(!matches!(
            self.namespace,
            ModuleIdNamespace::DirectCoreSource
        ));
        self.value as usize
    }

    pub(crate) const fn is_builtin_generic_cell(self) -> bool {
        matches!(self.namespace, ModuleIdNamespace::BuiltinGenericCell)
    }

    pub(crate) const fn is_builtin_retained_control(self) -> bool {
        matches!(self.namespace, ModuleIdNamespace::BuiltinRetainedControl)
    }

    pub(crate) const fn is_builtin_network(self) -> bool {
        matches!(self.namespace, ModuleIdNamespace::BuiltinNetwork)
    }

    pub(crate) const fn is_builtin_region_facade(self) -> bool {
        matches!(self.namespace, ModuleIdNamespace::BuiltinRegionFacade)
    }

    pub(crate) const fn is_builtin_region(self) -> bool {
        matches!(self.namespace, ModuleIdNamespace::BuiltinRegion)
    }

    pub(crate) const fn is_builtin_cell(self) -> bool {
        matches!(self.namespace, ModuleIdNamespace::BuiltinCell)
    }

    pub(crate) const fn is_builtin_bytes(self) -> bool {
        matches!(self.namespace, ModuleIdNamespace::BuiltinBytes)
    }
    pub(crate) const fn is_builtin_integer(self) -> bool {
        matches!(self.namespace, ModuleIdNamespace::BuiltinInteger)
    }
    pub(crate) const fn is_builtin_string(self) -> bool {
        matches!(self.namespace, ModuleIdNamespace::BuiltinString)
    }

    pub(crate) const fn is_builtin_foreign(self) -> bool {
        matches!(self.namespace, ModuleIdNamespace::BuiltinForeign)
    }

    pub(crate) const fn is_builtin_compiler_syntax(self) -> bool {
        matches!(self.namespace, ModuleIdNamespace::BuiltinCompilerSyntax)
    }

    #[cfg(test)]
    pub(crate) const fn builtin_foreign_for_test(value: u32) -> Self {
        Self {
            namespace: ModuleIdNamespace::BuiltinForeign,
            graph: 0,
            value,
        }
    }

    pub(crate) const fn is_builtin_resource(self) -> bool {
        self.is_builtin_cell() || self.is_builtin_generic_cell()
    }

    /// Returns the graph-local identity value.
    #[must_use]
    pub const fn value(self) -> u32 {
        self.value
    }
}

impl From<SourceId> for ModuleId {
    fn from(source: SourceId) -> Self {
        Self {
            namespace: ModuleIdNamespace::DirectCoreSource,
            graph: 0,
            value: source.value(),
        }
    }
}

impl fmt::Display for ModuleId {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.namespace {
            ModuleIdNamespace::BuiltinInteger => {
                write!(formatter, "builtin.integer:{}:{}", self.graph, self.value)
            }
            ModuleIdNamespace::BuiltinBytes => {
                write!(formatter, "builtin.bytes:{}:{}", self.graph, self.value)
            }
            ModuleIdNamespace::BuiltinString => {
                write!(formatter, "builtin.string:{}:{}", self.graph, self.value)
            }
            ModuleIdNamespace::BuiltinForeign => {
                write!(formatter, "builtin.foreign:{}:{}", self.graph, self.value)
            }
            ModuleIdNamespace::BuiltinCompilerSyntax => {
                write!(
                    formatter,
                    "builtin.compiler.syntax:{}:{}",
                    self.graph, self.value
                )
            }
            ModuleIdNamespace::Admitted => write!(formatter, "{}:{}", self.graph, self.value),
            ModuleIdNamespace::BuiltinGenericCell => {
                write!(
                    formatter,
                    "builtin.generic_cell:{}:{}",
                    self.graph, self.value
                )
            }
            ModuleIdNamespace::BuiltinRetainedControl => {
                write!(
                    formatter,
                    "builtin.retained_control:{}:{}",
                    self.graph, self.value
                )
            }
            ModuleIdNamespace::BuiltinNetwork => {
                write!(formatter, "builtin.network:{}:{}", self.graph, self.value)
            }
            ModuleIdNamespace::BuiltinCell => {
                write!(formatter, "builtin.cell:{}:{}", self.graph, self.value)
            }
            ModuleIdNamespace::BuiltinRegionFacade => write!(
                formatter,
                "builtin.region.facade:{}:{}",
                self.graph, self.value
            ),
            ModuleIdNamespace::BuiltinRegion => {
                write!(formatter, "builtin.region:{}:{}", self.graph, self.value)
            }
            ModuleIdNamespace::DirectCoreSource => write!(formatter, "source:{}", self.value),
        }
    }
}

/// One source import edge to an admitted canonical module.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ModuleDependency {
    target: ModuleId,
    import_span: Span,
    // A compiler dependency is not a fabricated SurfaceImport and binds no names.
    compiler_private: bool,
}

impl ModuleDependency {
    pub(crate) const fn is_region_service(self) -> bool {
        self.compiler_private && self.target.is_builtin_region()
    }

    pub(crate) const fn is_compiler_private(self) -> bool {
        self.compiler_private
    }
    /// Returns the imported module identity.
    #[must_use]
    pub const fn target(&self) -> ModuleId {
        self.target
    }

    /// Returns the complete source import span.
    #[must_use]
    pub const fn import_span(&self) -> Span {
        self.import_span
    }
}

/// One parsed module and its source-ordered dependency edges.
#[derive(Debug)]
pub struct LoadedModule {
    id: ModuleId,
    canonical_path: PathBuf,
    source: std::sync::Arc<SourceFile>,
    surface: SurfaceModule,
    dependencies: Box<[ModuleDependency]>,
    quote_sites: Vec<crate::syntax::SurfaceQuoteSite>,
    quote_introduction: Option<usize>,
    caller_quote_owner: Option<std::sync::Arc<crate::syntax::CallerQuoteOwner>>,
}

// A cloned surface has different Box allocations. Its source syntax is still
// equal, but the original module's transient quote authority must not follow it.
impl Clone for LoadedModule {
    fn clone(&self) -> Self {
        Self {
            id: self.id,
            canonical_path: self.canonical_path.clone(),
            source: self.source.clone(),
            surface: self.surface.clone(),
            dependencies: self.dependencies.clone(),
            quote_sites: Vec::new(),
            quote_introduction: None,
            caller_quote_owner: None,
        }
    }
}

impl PartialEq for LoadedModule {
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id
            && self.canonical_path == other.canonical_path
            && self.source == other.source
            && self.surface == other.surface
            && self.dependencies == other.dependencies
    }
}

impl Eq for LoadedModule {}

impl LoadedModule {
    pub(crate) fn caller_quote_owner(
        &self,
    ) -> Option<&std::sync::Arc<crate::syntax::CallerQuoteOwner>> {
        self.caller_quote_owner.as_ref()
    }

    fn into_source(mut self) -> SourceFile {
        // The completed-module association must not keep this module's own
        // source alive while attempting the existing move into diagnostics.
        drop(self.caller_quote_owner.take());
        std::sync::Arc::try_unwrap(self.source).unwrap_or_else(|source| (*source).clone())
    }

    /// Returns this module's graph-local identity.
    #[must_use]
    pub const fn id(&self) -> ModuleId {
        self.id
    }

    /// Returns the uniquely admitted canonical source path.
    #[must_use]
    pub fn canonical_path(&self) -> &Path {
        &self.canonical_path
    }

    /// Returns the admitted source model.
    #[must_use]
    pub fn source(&self) -> &SourceFile {
        &self.source
    }

    pub(crate) fn retained_source(&self) -> &std::sync::Arc<SourceFile> {
        &self.source
    }

    /// Returns the projected module syntax.
    #[must_use]
    pub const fn surface(&self) -> &SurfaceModule {
        &self.surface
    }

    /// Returns source-ordered dependency edges.
    #[must_use]
    pub fn dependencies(&self) -> &[ModuleDependency] {
        &self.dependencies
    }

    pub(crate) fn quote_sites(&self) -> &[crate::syntax::SurfaceQuoteSite] {
        &self.quote_sites
    }

    pub(crate) fn quote_introduction(&self) -> Option<usize> {
        self.quote_introduction
    }

    pub(crate) fn prepare_escape_probes(
        &mut self,
        budget: &mut SyntaxBudget,
    ) -> Result<Vec<usize>, crate::parser::MacroParseFailure> {
        crate::syntax::prepare_escape_probes(&mut self.surface, self.quote_introduction, budget)
    }

    pub(crate) fn finish_escape_probes(
        &mut self,
        probes: &[usize],
        categories: &[(crate::syntax::EscapeResultCategory, bool, bool)],
        budget: &mut SyntaxBudget,
    ) -> Result<(), crate::parser::MacroParseFailure> {
        crate::syntax::finish_escape_probes(
            &mut self.surface,
            self.quote_introduction,
            probes,
            categories,
            budget,
        )
    }
}

/// A canonical module graph ordered with dependencies before dependents.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ModuleGraph {
    modules: Box<[LoadedModule]>,
    entry: ModuleId,
}

impl ModuleGraph {
    /// Moves admitted sources out of a finished graph for compile diagnostics.
    pub(crate) fn into_sources(self) -> Box<[SourceFile]> {
        self.modules
            .into_vec()
            .into_iter()
            .map(LoadedModule::into_source)
            .collect::<Vec<_>>()
            .into_boxed_slice()
    }

    /// Returns modules in deterministic dependency order.
    #[must_use]
    pub fn modules(&self) -> &[LoadedModule] {
        &self.modules
    }

    #[cfg(test)]
    pub(crate) fn module_at_mut(&mut self, index: usize) -> Option<&mut LoadedModule> {
        self.modules.get_mut(index)
    }

    /// Looks up one canonical module by graph-local identity.
    #[must_use]
    pub fn module(&self, id: ModuleId) -> Option<&LoadedModule> {
        self.modules.iter().find(|module| module.id == id)
    }

    /// Returns the entry module identity.
    #[must_use]
    pub const fn entry(&self) -> ModuleId {
        self.entry
    }
}

/// Stable module-loader reason families.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ModuleReason {
    /// A syntax selector requires the checked compilation driver.
    SyntaxRequiresDriver,
    /// A configured root attempts to replace a compiler-owned module root.
    ReservedRoot,
    /// An absolute builtin import names no compiler-owned module.
    UnknownBuiltin,
    /// An absolute foreign path has no host registration.
    UnknownForeign,
    /// An absolute import names no configured root.
    UnknownRoot,
    /// An imported source path does not exist.
    NotFound,
    /// A canonical import target escapes an owning root.
    PathEscape,
    /// The dependency graph contains an import cycle.
    ImportCycle,
    /// A named-root configuration repeats one name.
    DuplicateRoot,
    /// A configured root name is not a lowercase Ash identifier.
    InvalidRootName,
    /// A configured root path cannot be used as a directory.
    RootUnavailable,
    /// Internal module data lacks required path segments or a canonical parent.
    InvalidPath,
    /// Module graph work exceeded an implementation budget.
    ResourceLimit,
}

impl fmt::Display for ModuleReason {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(match self {
            Self::SyntaxRequiresDriver => "module.syntax-requires-driver",
            Self::ReservedRoot => "invocation.reserved-root",
            Self::UnknownBuiltin => "module.unknown-builtin",
            Self::UnknownForeign => "module.unknown-foreign",
            Self::UnknownRoot => "module.unknown-root",
            Self::NotFound => "module.not-found",
            Self::PathEscape => "module.path-escape",
            Self::ImportCycle => "module.import-cycle",
            Self::DuplicateRoot => "invocation.duplicate-root",
            Self::InvalidRootName => "invocation.invalid-root-name",
            Self::RootUnavailable => "invocation.root-unavailable",
            Self::InvalidPath => "module.invalid-path",
            Self::ResourceLimit => "internal.resource.module-graph",
        })
    }
}

/// Stable I/O fact names, independent of operating-system message text.
pub(crate) const fn io_kind_name(kind: io::ErrorKind) -> &'static str {
    match kind {
        io::ErrorKind::NotFound => "not-found",
        io::ErrorKind::PermissionDenied => "permission-denied",
        io::ErrorKind::ConnectionRefused => "connection-refused",
        io::ErrorKind::ConnectionReset => "connection-reset",
        io::ErrorKind::HostUnreachable => "host-unreachable",
        io::ErrorKind::NetworkUnreachable => "network-unreachable",
        io::ErrorKind::ConnectionAborted => "connection-aborted",
        io::ErrorKind::NotConnected => "not-connected",
        io::ErrorKind::AddrInUse => "addr-in-use",
        io::ErrorKind::AddrNotAvailable => "addr-not-available",
        io::ErrorKind::NetworkDown => "network-down",
        io::ErrorKind::BrokenPipe => "broken-pipe",
        io::ErrorKind::AlreadyExists => "already-exists",
        io::ErrorKind::WouldBlock => "would-block",
        io::ErrorKind::NotADirectory => "not-a-directory",
        io::ErrorKind::IsADirectory => "is-a-directory",
        io::ErrorKind::DirectoryNotEmpty => "directory-not-empty",
        io::ErrorKind::ReadOnlyFilesystem => "read-only-filesystem",
        io::ErrorKind::StaleNetworkFileHandle => "stale-network-file-handle",
        io::ErrorKind::InvalidInput => "invalid-input",
        io::ErrorKind::InvalidData => "invalid-data",
        io::ErrorKind::TimedOut => "timed-out",
        io::ErrorKind::WriteZero => "write-zero",
        io::ErrorKind::StorageFull => "storage-full",
        io::ErrorKind::NotSeekable => "not-seekable",
        io::ErrorKind::QuotaExceeded => "quota-exceeded",
        io::ErrorKind::FileTooLarge => "file-too-large",
        io::ErrorKind::ResourceBusy => "resource-busy",
        io::ErrorKind::ExecutableFileBusy => "executable-file-busy",
        io::ErrorKind::Deadlock => "deadlock",
        io::ErrorKind::CrossesDevices => "crosses-devices",
        io::ErrorKind::TooManyLinks => "too-many-links",
        io::ErrorKind::InvalidFilename => "invalid-filename",
        io::ErrorKind::ArgumentListTooLong => "argument-list-too-long",
        io::ErrorKind::Interrupted => "interrupted",
        io::ErrorKind::Unsupported => "unsupported",
        io::ErrorKind::UnexpectedEof => "unexpected-eof",
        io::ErrorKind::OutOfMemory => "out-of-memory",
        io::ErrorKind::Other => "other",
        _ => "uncategorized",
    }
}

/// The graph resource whose budget was exhausted.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ModuleResource {
    /// Compilation-local graph identity allocation.
    GraphIdentities,
    /// Canonical source admission.
    Sources,
    /// Import-edge retention.
    Edges,
    /// Module-path segment processing.
    PathSegments,
    /// Retained canonical-module and owning-root relations.
    OwnerFacts,
    /// Active iterative traversal and owner-propagation work items.
    PendingWork,
}

static NEXT_MODULE_GRAPH: AtomicU32 = AtomicU32::new(1);

impl ModuleResource {
    pub(crate) const fn diagnostic_name(self) -> &'static str {
        match self {
            Self::GraphIdentities => "graph-identities",
            Self::Sources => "sources",
            Self::Edges => "edges",
            Self::PathSegments => "path-segments",
            Self::OwnerFacts => "owner-facts",
            Self::PendingWork => "pending-work",
        }
    }
}

fn allocate_module_graph_identity() -> Result<u32, LoadGraphError> {
    NEXT_MODULE_GRAPH
        .fetch_update(Ordering::Relaxed, Ordering::Relaxed, |value| {
            value.checked_add(1)
        })
        .map_err(|_| ModuleFailure::resource(ModuleResource::GraphIdentities).into())
}

/// The internal module-path relationship that failed.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ModulePathCause {
    MissingParent,
    MissingSegments,
}

/// A typed module-stage or root-configuration failure.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ModuleFailure {
    reason: ModuleReason,
    source_rejection: bool,
    primary: Option<Span>,
    path: Option<PathBuf>,
    root: Option<String>,
    io_kind: Option<io::ErrorKind>,
    resource: Option<ModuleResource>,
    path_cause: Option<ModulePathCause>,
}

impl ModuleFailure {
    pub(crate) const fn responsibility(&self) -> &'static str {
        match self.reason {
            ModuleReason::ReservedRoot
            | ModuleReason::SyntaxRequiresDriver
            | ModuleReason::DuplicateRoot
            | ModuleReason::InvalidRootName
            | ModuleReason::RootUnavailable => "invocation",
            ModuleReason::UnknownBuiltin
            | ModuleReason::UnknownForeign
            | ModuleReason::UnknownRoot
            | ModuleReason::NotFound
            | ModuleReason::PathEscape
            | ModuleReason::ImportCycle => "source",
            ModuleReason::InvalidPath | ModuleReason::ResourceLimit => "compiler",
        }
    }

    pub(crate) fn message(&self) -> Option<crate::message::Message<'_>> {
        use crate::message::Message;
        Some(match self.reason {
            ModuleReason::SyntaxRequiresDriver => Message::module_syntax_requires_driver(),
            ModuleReason::ReservedRoot => Message::module_reserved_root(self.root()?),
            ModuleReason::DuplicateRoot => Message::module_duplicate_root(self.root()?),
            ModuleReason::InvalidRootName => Message::module_invalid_root_name(self.root()?),
            ModuleReason::UnknownRoot => Message::module_unknown_root(self.root()?),
            ModuleReason::UnknownBuiltin => Message::module_unknown_builtin(),
            ModuleReason::UnknownForeign => Message::module_unknown_foreign(),
            ModuleReason::NotFound => Message::module_not_found(self.path()?),
            ModuleReason::ImportCycle => Message::module_import_cycle(self.path()?),
            ModuleReason::PathEscape => Message::module_path_escape(self.path()?),
            ModuleReason::ResourceLimit => Message::module_resource(self.resource_kind()?),
            ModuleReason::RootUnavailable => match self.io_kind() {
                Some(kind) => Message::module_root_io(self.path()?, self.root()?, kind),
                None => Message::module_root_unavailable(self.path()?, self.root()?),
            },
            ModuleReason::InvalidPath => match self.path_cause? {
                ModulePathCause::MissingParent => Message::module_missing_parent(),
                ModulePathCause::MissingSegments => Message::module_missing_segments(),
            },
        })
    }

    fn source(reason: ModuleReason, primary: Span, path: Option<PathBuf>) -> Self {
        Self {
            reason,
            source_rejection: true,
            primary: Some(primary),
            path,
            root: None,
            io_kind: None,
            resource: None,
            path_cause: None,
        }
    }

    fn unknown_root(primary: Span, root: String) -> Self {
        let mut failure = Self::source(ModuleReason::UnknownRoot, primary, None);
        failure.root = Some(root);
        failure
    }

    fn invalid_path(primary: Span, path: Option<PathBuf>, cause: ModulePathCause) -> Self {
        let mut failure = Self::source(ModuleReason::InvalidPath, primary, path);
        failure.source_rejection = false;
        failure.path_cause = Some(cause);
        failure
    }

    pub(crate) const fn path_cause_name(&self) -> Option<&'static str> {
        match self.path_cause {
            Some(ModulePathCause::MissingParent) => Some("missing-canonical-parent"),
            Some(ModulePathCause::MissingSegments) => Some("missing-path-segments"),
            None => None,
        }
    }

    fn invocation(
        reason: ModuleReason,
        path: Option<PathBuf>,
        root: Option<String>,
        io_kind: Option<io::ErrorKind>,
    ) -> Self {
        Self {
            reason,
            source_rejection: false,
            primary: None,
            path,
            root,
            io_kind,
            resource: None,
            path_cause: None,
        }
    }

    fn resource(resource: ModuleResource) -> Self {
        Self {
            reason: ModuleReason::ResourceLimit,
            source_rejection: false,
            primary: None,
            path: None,
            root: None,
            io_kind: None,
            resource: Some(resource),
            path_cause: None,
        }
    }

    /// Returns the stable module reason.
    #[must_use]
    pub const fn reason(&self) -> ModuleReason {
        self.reason
    }

    /// Reports whether this failure rejects Ash source.
    #[must_use]
    pub const fn is_source_rejection(&self) -> bool {
        self.source_rejection
    }

    /// Returns the import occurrence associated with this failure.
    #[must_use]
    pub const fn primary_span(&self) -> Option<Span> {
        self.primary
    }

    /// Returns the relevant canonical or requested path, when retained.
    #[must_use]
    pub fn path(&self) -> Option<&Path> {
        self.path.as_deref()
    }

    /// Returns the relevant named root, when retained.
    #[must_use]
    pub fn root(&self) -> Option<&str> {
        self.root.as_deref()
    }

    /// Returns the stable I/O category for a root failure, when retained.
    #[must_use]
    pub const fn io_kind(&self) -> Option<io::ErrorKind> {
        self.io_kind
    }

    /// Returns the exhausted graph resource, when relevant.
    #[must_use]
    pub const fn resource_kind(&self) -> Option<ModuleResource> {
        self.resource
    }
}

impl fmt::Display for ModuleFailure {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.reason.fmt(formatter)
    }
}

impl Error for ModuleFailure {}

#[cfg(test)]
mod presentation_tests {
    use super::*;

    #[test]
    fn staged_resource_location_requires_each_admitted_source() {
        use crate::{
            presentation::{PresentationError, compile_graph_diagnostics, write_json},
            source::ByteRange,
            syntax::{DiagnosticLocation, ExpansionFrame},
            syntax_resource::ResourceFailure,
        };
        use std::sync::Arc;

        let source = SourceFile::new("caller.ash", "invoke").unwrap();
        let missing = SourceFile::new("forms.ash", "definition").unwrap();
        let invocation = source.span(ByteRange::new(0, 6).unwrap()).unwrap();
        let definition = missing.span(ByteRange::new(0, 10).unwrap()).unwrap();
        let mut location = DiagnosticLocation::new(invocation.into());
        location.frames.push(Arc::new(ExpansionFrame {
            invocation,
            definition,
        }));
        let mut graph = GraphDiagnostic {
            failure: Box::new(LoadGraphError::Syntax(Box::new(ModuleSyntaxFailure {
                source,
                import_span: None,
                lexical: Vec::new(),
                parser: Vec::new(),
                resource: Some(ResourceFailure::StructuralDepth { limit: 128 }),
            }))),
            sources: Box::default(),
            compilation_work: None,
            resource_location: Some(location),
        };
        assert!(matches!(
            compile_graph_diagnostics(&graph),
            Err(PresentationError::MissingSource)
        ));

        graph.resource_location = None;
        let diagnostics = compile_graph_diagnostics(&graph).unwrap();
        assert_eq!(diagnostics.len(), 1);
        let mut output = Vec::new();
        write_json(&mut output, &diagnostics[0]).unwrap();
        let json: serde_json::Value = serde_json::from_slice(&output).unwrap();
        assert_eq!(json["reason"], "internal.resource.structural-depth");
        assert_eq!(json["responsibility"], "compiler");
        assert_eq!(json["labels"], serde_json::json!([]));
    }

    #[test]
    fn corrupt_projected_paths_report_compiler_failures_with_specific_causes() {
        for (input, missing_parent, expected_cause) in [
            ("import child as Child\n", true, "missing-canonical-parent"),
            ("import child as Child\n", false, "missing-path-segments"),
            (
                "import @std.child as Child\n",
                false,
                "missing-path-segments",
            ),
        ] {
            let (source, mut surface, needs_generator_dependency) = parse_surface_module(
                Path::new("entry.ash"),
                input.into(),
                None,
                &mut SyntaxBudget::default(),
            )
            .unwrap();
            if !missing_parent {
                match &mut surface.imports[0].path {
                    SurfaceModulePath::Relative(segments)
                    | SurfaceModulePath::Absolute { segments, .. } => segments.clear(),
                }
            }
            let module = StagedModule {
                id: ModuleId::new(0),
                canonical_path: if missing_parent {
                    PathBuf::new()
                } else {
                    PathBuf::from("entry.ash")
                },
                owners: OwnerSet {
                    ordered: Vec::new(),
                    membership: HashSet::new(),
                },
                source,
                surface: StagedSyntax::parsed(surface, None, needs_generator_dependency),
                dependencies: Vec::new(),
                relative_edges: Vec::new(),
                state: VisitState::Active,
            };
            let roots = ModuleRoots {
                named: HashMap::from([(ModuleRootName::new("std").unwrap(), PathBuf::from("."))]),
            };
            let failure = resolve_import(&module, &module.surface.imports[0], &roots).unwrap_err();
            assert_eq!(failure.module_reason(), Some(ModuleReason::InvalidPath));
            assert!(
                !failure.is_source_rejection(),
                "corrupt compiler data must not reject source"
            );
            let context = GraphDiagnostic {
                failure: Box::new(failure),
                sources: vec![module.source].into_boxed_slice(),
                compilation_work: None,
                resource_location: None,
            };
            let diagnostics = crate::presentation::compile_graph_diagnostics(&context).unwrap();
            let mut output = Vec::new();
            crate::presentation::write_json(&mut output, &diagnostics[0]).unwrap();
            let json: serde_json::Value = serde_json::from_slice(&output).unwrap();
            assert_eq!(json["responsibility"], "compiler");
            assert!(
                json["facts"]
                    .as_array()
                    .unwrap()
                    .iter()
                    .any(|fact| fact["name"] == "cause" && fact["value"] == expected_cause)
            );
            assert_eq!(json["labels"][0]["path"], "entry.ash");
            for locale in [
                crate::message::Locale::English,
                crate::message::Locale::Bulgarian,
            ] {
                let mut output = Vec::new();
                crate::presentation::write_short(
                    &mut output,
                    &diagnostics[0],
                    &crate::message::Catalogue::new(locale).unwrap(),
                )
                .unwrap();
                assert!(String::from_utf8(output).unwrap().contains("Ash"));
            }
        }
    }
    #[test]
    fn unavailable_root_retains_io_facts_without_inventing_a_directory_cause() {
        for kind in [None, Some(io::ErrorKind::PermissionDenied)] {
            let failure = GraphDiagnostic::from(LoadGraphError::Module(ModuleFailure::invocation(
                ModuleReason::RootUnavailable,
                Some(PathBuf::from("library")),
                Some("std".into()),
                kind,
            )));
            let diagnostics = crate::presentation::compile_graph_diagnostics(&failure).unwrap();
            for (locale, expected) in [
                (
                    crate::message::Locale::English,
                    if kind.is_some() {
                        "Cannot use `library` for module root `std`: access is denied."
                    } else {
                        "Cannot use `library` as a directory for module root `std`."
                    },
                ),
                (
                    crate::message::Locale::Bulgarian,
                    if kind.is_some() {
                        "Не може да се използва `library` за корен за модули `std`: достъпът е отказан."
                    } else {
                        "Не може да се използва `library` като директория за корен за модули `std`."
                    },
                ),
            ] {
                let mut output = Vec::new();
                crate::presentation::write_short(
                    &mut output,
                    &diagnostics[0],
                    &crate::message::Catalogue::new(locale).unwrap(),
                )
                .unwrap();
                assert_eq!(
                    String::from_utf8(output).unwrap(),
                    format!("{expected} [invocation.root-unavailable]\n")
                );
            }
            let mut output = Vec::new();
            crate::presentation::write_json(&mut output, &diagnostics[0]).unwrap();
            let json: serde_json::Value = serde_json::from_slice(&output).unwrap();
            assert_eq!(json["responsibility"], "invocation");
            assert_eq!(json["labels"], serde_json::json!([]));
            let facts = json["facts"].as_array().unwrap();
            assert_eq!(facts.len(), if kind.is_some() { 3 } else { 2 });
            if kind.is_some() {
                assert_eq!(facts[2]["value"], "permission-denied");
            }
        }
    }
    #[test]
    fn module_resource_messages_preserve_compiler_responsibility_and_kind() {
        for (resource, name, en, bg) in [
            (
                ModuleResource::GraphIdentities,
                "graph-identities",
                "module graph identities",
                "идентичности на графи от модули",
            ),
            (
                ModuleResource::Sources,
                "sources",
                "module sources",
                "изходни файлове на модули",
            ),
            (
                ModuleResource::Edges,
                "edges",
                "import edges",
                "ребра на импорти",
            ),
            (
                ModuleResource::PathSegments,
                "path-segments",
                "module path segments",
                "сегменти на пътища към модули",
            ),
            (
                ModuleResource::OwnerFacts,
                "owner-facts",
                "module ownership facts",
                "факти за принадлежност на модули",
            ),
            (
                ModuleResource::PendingWork,
                "pending-work",
                "pending module-loading work",
                "чакаща работа по зареждане на модули",
            ),
        ] {
            let failure =
                GraphDiagnostic::from(LoadGraphError::Module(ModuleFailure::resource(resource)));
            let diagnostics = crate::presentation::compile_graph_diagnostics(&failure).unwrap();
            for (locale, detail) in [
                (crate::message::Locale::English, en),
                (crate::message::Locale::Bulgarian, bg),
            ] {
                let mut output = Vec::new();
                crate::presentation::write_short(
                    &mut output,
                    &diagnostics[0],
                    &crate::message::Catalogue::new(locale).unwrap(),
                )
                .unwrap();
                assert!(String::from_utf8(output).unwrap().contains(detail));
            }
            let mut output = Vec::new();
            crate::presentation::write_json(&mut output, &diagnostics[0]).unwrap();
            let json: serde_json::Value = serde_json::from_slice(&output).unwrap();
            assert_eq!(json["responsibility"], "compiler");
            assert_eq!(json["reason"], "internal.resource.module-graph");
            assert_eq!(json["labels"], serde_json::json!([]));
            assert_eq!(
                json["facts"],
                serde_json::json!([{"name":"resource", "kind":"resource", "value":name}])
            );
        }
    }
}

/// Structured syntax facts retained for one rejected module source.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ModuleSyntaxFailure {
    /// The admitted source needed to render retained spans.
    pub source: SourceFile,
    /// The import selecting this source, or `None` for the entry source.
    pub import_span: Option<Span>,
    /// Independent lexical diagnostics.
    pub lexical: Vec<Diagnostic<LexReason>>,
    /// Structured parser diagnostics.
    pub parser: Vec<ParseDiagnostic>,
    /// A non-language syntax resource failure, when present.
    pub resource: Option<ResourceFailure>,
}

/// A graph-loading failure that preserves the stage which rejected input.
#[derive(Debug)]
pub enum LoadGraphError {
    /// Module path, graph, or root policy failed.
    Module(ModuleFailure),
    /// A canonical source could not be read.
    Read {
        /// The source path.
        path: PathBuf,
        /// Stable I/O error category.
        kind: io::ErrorKind,
        /// The causing import, or `None` for the entry path.
        import_span: Option<Span>,
    },
    /// A source file is not UTF-8.
    InvalidUtf8 {
        /// The source path.
        path: PathBuf,
        /// The causing import, or `None` for the entry path.
        import_span: Option<Span>,
    },
    /// Source-model admission or checked-span construction failed.
    SourceModel {
        /// The source path.
        path: PathBuf,
        /// The source-model failure.
        error: SourceError,
        /// Distinguishes input admission from checked operations on admitted text.
        operation: crate::source::SourceOperation,
        /// The causing import, or `None` for the entry path.
        import_span: Option<Span>,
    },
    /// Lexing or parsing rejected one admitted module source.
    Syntax(Box<ModuleSyntaxFailure>),
    /// Recovery-free concrete syntax violated projection invariants.
    Projection {
        /// The admitted source needed to render retained spans.
        source: SourceFile,
        /// The projection failure.
        error: ProjectionError,
        /// The import selecting this source, or `None` for the entry source.
        import_span: Option<Span>,
    },
}

impl LoadGraphError {
    /// Returns the import occurrence that caused this load failure, if any.
    #[must_use]
    pub const fn import_span(&self) -> Option<Span> {
        match self {
            Self::Module(failure) => failure.primary_span(),
            Self::Read { import_span, .. }
            | Self::InvalidUtf8 { import_span, .. }
            | Self::SourceModel { import_span, .. }
            | Self::Projection { import_span, .. } => *import_span,
            Self::Syntax(failure) => failure.import_span,
        }
    }
    /// Returns the module-stage payload, when this is a module failure.
    #[must_use]
    pub const fn as_module_failure(&self) -> Option<&ModuleFailure> {
        match self {
            Self::Module(failure) => Some(failure),
            Self::Read { .. }
            | Self::InvalidUtf8 { .. }
            | Self::SourceModel { .. }
            | Self::Syntax(_)
            | Self::Projection { .. } => None,
        }
    }

    /// Returns a module-owned reason only for a module-stage failure.
    #[must_use]
    pub const fn module_reason(&self) -> Option<ModuleReason> {
        match self {
            Self::Module(failure) => Some(failure.reason()),
            Self::Read { .. }
            | Self::InvalidUtf8 { .. }
            | Self::SourceModel { .. }
            | Self::Syntax(_)
            | Self::Projection { .. } => None,
        }
    }

    /// Reports whether this failure rejects Ash source rather than invocation,
    /// input, or compiler state.
    #[must_use]
    pub fn is_source_rejection(&self) -> bool {
        match self {
            Self::Module(failure) => failure.is_source_rejection(),
            Self::Syntax(failure) => {
                failure.resource.is_none()
                    && (!failure.lexical.is_empty() || !failure.parser.is_empty())
            }
            Self::Read { .. }
            | Self::InvalidUtf8 { .. }
            | Self::SourceModel { .. }
            | Self::Projection { .. } => false,
        }
    }
}

impl From<ModuleFailure> for LoadGraphError {
    fn from(failure: ModuleFailure) -> Self {
        Self::Module(failure)
    }
}

impl fmt::Display for LoadGraphError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Module(failure) => failure.fmt(formatter),
            Self::Read { path, kind, .. } => {
                write!(formatter, "cannot read {}: {kind}", path.display())
            }
            Self::InvalidUtf8 { path, .. } => {
                write!(formatter, "{} is not a UTF-8 source file", path.display())
            }
            Self::SourceModel { error, .. } => error.fmt(formatter),
            Self::Syntax(_) => formatter.write_str("module source syntax failure"),
            Self::Projection { .. } => formatter.write_str("module surface projection failure"),
        }
    }
}

impl Error for LoadGraphError {}

/// A graph-loading failure with the admitted sources needed for diagnostics.
/// Sources are moved out of traversal state only after loading fails.
#[derive(Debug)]
pub struct GraphDiagnostic {
    failure: Box<LoadGraphError>,
    sources: Box<[SourceFile]>,
    compilation_work: Option<Box<crate::compiler_work::CompilationWork>>,
    resource_location: Option<crate::syntax::DiagnosticLocation>,
}

impl GraphDiagnostic {
    pub(crate) fn resource_location(&self) -> Option<&crate::syntax::DiagnosticLocation> {
        self.resource_location.as_ref()
    }

    pub(crate) fn compilation_work(&self) -> Option<&crate::compiler_work::CompilationWork> {
        self.compilation_work.as_deref()
    }

    pub(crate) fn with_compilation_work(
        mut self,
        work: crate::compiler_work::CompilationWork,
    ) -> Self {
        self.compilation_work = Some(Box::new(work));
        self
    }

    /// Borrows the unchanged graph-loading failure.
    #[must_use]
    pub const fn failure(&self) -> &LoadGraphError {
        &self.failure
    }

    /// Consumes the diagnostic when only its semantic failure is needed.
    #[must_use]
    pub fn into_failure(self) -> LoadGraphError {
        *self.failure
    }

    pub(crate) fn into_sources(self) -> Box<[SourceFile]> {
        let mut sources = self.sources.into_vec();
        match *self.failure {
            LoadGraphError::Syntax(failure) => sources.push(failure.source),
            LoadGraphError::Projection { source, .. } => sources.push(source),
            _ => {}
        }
        sources.into_boxed_slice()
    }

    /// Borrows all admitted sources, including a rejected syntax source.
    pub fn sources(&self) -> impl Iterator<Item = &SourceFile> {
        let rejected = match &*self.failure {
            LoadGraphError::Syntax(failure) => Some(&failure.source),
            LoadGraphError::Projection { source, .. } => Some(source),
            _ => None,
        };
        self.sources.iter().chain(rejected)
    }

    /// Returns the module-stage failure, if present.
    #[must_use]
    pub const fn as_module_failure(&self) -> Option<&ModuleFailure> {
        self.failure.as_module_failure()
    }

    /// Returns the stable module-stage reason, if present.
    #[must_use]
    pub const fn module_reason(&self) -> Option<ModuleReason> {
        self.failure.module_reason()
    }

    /// Preserves the original source-rejection classification.
    #[must_use]
    pub fn is_source_rejection(&self) -> bool {
        self.failure.is_source_rejection()
    }
}

impl fmt::Display for GraphDiagnostic {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.failure.fmt(formatter)
    }
}

impl Error for GraphDiagnostic {}

impl From<LoadGraphError> for GraphDiagnostic {
    fn from(failure: LoadGraphError) -> Self {
        Self {
            failure: Box::new(failure),
            sources: Box::default(),
            compilation_work: None,
            resource_location: None,
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum VisitState {
    Active,
    Finished,
}

#[derive(Clone, Debug)]
struct RelativeEdge {
    target: ModuleId,
    canonical_target: PathBuf,
    import_span: Span,
}

#[derive(Clone, Debug)]
struct OwnerSet {
    ordered: Vec<PathBuf>,
    membership: HashSet<PathBuf>,
}

impl OwnerSet {
    fn from_paths(paths: &[PathBuf], budget: &mut GraphBudget) -> Result<Self, LoadGraphError> {
        budget.charge_owner_facts(paths.len())?;
        let mut ordered = Vec::new();
        ordered
            .try_reserve(paths.len())
            .map_err(|_| ModuleFailure::resource(ModuleResource::OwnerFacts))?;
        let mut membership = HashSet::new();
        membership
            .try_reserve(paths.len())
            .map_err(|_| ModuleFailure::resource(ModuleResource::OwnerFacts))?;
        for path in paths {
            let retained = path.clone();
            let inserted = membership.insert(retained.clone());
            debug_assert!(inserted, "admission paths must carry distinct owners");
            ordered.push(retained);
        }
        Ok(Self {
            ordered,
            membership,
        })
    }

    fn contains(&self, owner: &Path) -> bool {
        self.membership.contains(owner)
    }

    fn insert(&mut self, owner: &Path, budget: &mut GraphBudget) -> Result<(), LoadGraphError> {
        budget.charge_owner_facts(1)?;
        self.ordered
            .try_reserve(1)
            .map_err(|_| ModuleFailure::resource(ModuleResource::OwnerFacts))?;
        self.membership
            .try_reserve(1)
            .map_err(|_| ModuleFailure::resource(ModuleResource::OwnerFacts))?;
        let retained = owner.to_path_buf();
        let inserted = self.membership.insert(retained.clone());
        debug_assert!(inserted, "owner insertion follows a membership check");
        self.ordered.push(retained);
        Ok(())
    }
}

#[derive(Debug)]
enum ImportOwners {
    Inherited(ModuleId),
    Absolute(PathBuf),
}

struct StagedModule {
    id: ModuleId,
    canonical_path: PathBuf,
    owners: OwnerSet,
    source: SourceFile,
    surface: StagedSyntax,
    dependencies: Vec<ModuleDependency>,
    relative_edges: Vec<RelativeEdge>,
    state: VisitState,
}

// The view exists only while this actual module is being projected. Its
// snapshot is populated lazily by a reached checked generator adapter.
pub(crate) struct StagedModuleLoan<'a> {
    id: ModuleId,
    source_id: SourceId,
    canonical_path: &'a Path,
    imports: &'a [SurfaceImport],
    dependencies: &'a [ModuleDependency],
    span: Span,
    source_snapshot: &'a std::cell::RefCell<Option<std::sync::Arc<SourceFile>>>,
    caller_quote_owner:
        &'a std::cell::RefCell<Option<std::sync::Arc<crate::syntax::CallerQuoteOwner>>>,
    quote_projection: Option<&'a std::cell::RefCell<crate::parser::QuoteProjection>>,
}

pub(crate) type StagedDeclarationTransformer<'a> = dyn for<'call, 'module> FnMut(
        &'call crate::syntax::SelectedSyntax,
        crate::syntax::DeclarationAdapter<'call>,
        &'call [crate::surface::SurfaceSyntaxCapture],
        &'call SourceFile,
        &'call StagedModuleLoan<'module>,
        &'call crate::surface::SurfaceName,
        usize,
        std::sync::Arc<crate::syntax::SyntaxContexts>,
        std::sync::Arc<crate::syntax::ExpansionFrame>,
        &'call mut Vec<crate::syntax::SyntaxOwner>,
        &'call mut SyntaxBudget,
    ) -> Result<(Vec<crate::syntax::MacroOutputNode>, usize), Span>
    + 'a;

impl StagedModuleLoan<'_> {
    pub(crate) fn quote_projection(
        &self,
    ) -> Option<&std::cell::RefCell<crate::parser::QuoteProjection>> {
        self.quote_projection
    }

    fn retained_source(
        &self,
        source: &SourceFile,
        budget: &mut SyntaxBudget,
    ) -> Result<std::sync::Arc<SourceFile>, ResourceFailure> {
        debug_assert_eq!(source.id(), self.source_id);
        if let Some(source) = self.source_snapshot.borrow().as_ref() {
            budget.charge()?;
            return Ok(std::sync::Arc::clone(source));
        }
        // Pay the one deep snapshot, its Arc, and the returned Arc retain
        // before constructing or publishing any part of the snapshot.
        budget.charge_units(
            source
                .snapshot_work()
                .unwrap_or(usize::MAX)
                .saturating_add(2),
        )?;
        let retained = std::sync::Arc::new(source.clone());
        let result = std::sync::Arc::clone(&retained);
        *self.source_snapshot.borrow_mut() = Some(retained);
        Ok(result)
    }

    pub(crate) fn retain_caller_quote_owner(
        &self,
        source: &SourceFile,
        selected: &[crate::syntax::SelectedSyntax],
        budget: &mut SyntaxBudget,
    ) -> Result<Option<std::sync::Arc<crate::syntax::CallerQuoteOwner>>, ResourceFailure> {
        if source.id() != self.source_id {
            return Ok(None);
        }
        if let Some(owner) = self.caller_quote_owner.borrow().as_ref() {
            budget.charge()?;
            return Ok(Some(std::sync::Arc::clone(owner)));
        }
        // Selection records, temporary/final slice slots, the record and its
        // cached and returned Arc retains are paid before any construction.
        budget.charge_units(selected.len().saturating_mul(2).saturating_add(3))?;
        for selection in selected {
            crate::syntax::charge_selected(selection, budget)?;
        }
        let retained = self.retained_source(source, budget)?;
        let owner = std::sync::Arc::new(crate::syntax::CallerQuoteOwner {
            module: self.id,
            source: retained,
            selected: std::sync::Arc::from(selected.to_vec().into_boxed_slice()),
        });
        *self.caller_quote_owner.borrow_mut() = Some(std::sync::Arc::clone(&owner));
        Ok(Some(owner))
    }

    #[cfg(test)]
    pub(crate) fn no_quote_adapter_view(
        &self,
        source: &SourceFile,
        definition: crate::surface::SurfaceDefinition,
        budget: &mut SyntaxBudget,
    ) -> Result<LoadedModule, ResourceFailure> {
        self.adapter_view(source, definition, Vec::new(), None, budget)
    }

    pub(crate) fn adapter_view(
        &self,
        source: &SourceFile,
        definition: crate::surface::SurfaceDefinition,
        quote_sites: Vec<crate::syntax::SurfaceQuoteSite>,
        quote_introduction: Option<usize>,
        budget: &mut SyntaxBudget,
    ) -> Result<LoadedModule, ResourceFailure> {
        use crate::surface::{
            SurfaceDeclarationIndex, SurfaceImportItem, SurfaceImportSelection, SurfaceModulePath,
        };

        fn charge_name(
            name: &crate::surface::SurfaceName,
            budget: &mut SyntaxBudget,
        ) -> Result<(), ResourceFailure> {
            crate::syntax::charge_type_name_copy(name, 0, budget)?;
            if let Some(location) = name.diagnostic.as_deref() {
                budget.charge_units(location.frames.len())?;
            }
            Ok(())
        }

        // The view owns an exact copy of the caller's real import syntax and
        // dependency edge order; only its private adapter is new.
        budget.charge_units(
            self.imports
                .len()
                .saturating_add(self.dependencies.len().saturating_mul(2))
                .saturating_add(self.canonical_path.as_os_str().as_encoded_bytes().len())
                .saturating_add(2),
        )?;
        for import in self.imports {
            let segments = match &import.path {
                SurfaceModulePath::Relative(segments) => segments,
                SurfaceModulePath::Absolute { root, segments } => {
                    charge_name(root, budget)?;
                    segments
                }
            };
            budget.charge_units(segments.len())?;
            for name in segments {
                charge_name(name, budget)?;
            }
            match &import.selection {
                SurfaceImportSelection::Qualified { alias } => charge_name(alias, budget)?,
                SurfaceImportSelection::Targeted(items) => {
                    budget.charge_units(items.len())?;
                    for item in items {
                        match item {
                            SurfaceImportItem::Syntax { name, alias, .. }
                            | SurfaceImportItem::Name { name, alias, .. } => {
                                charge_name(name, budget)?;
                                if let Some(alias) = alias {
                                    charge_name(alias, budget)?;
                                }
                            }
                            SurfaceImportItem::Implementation { interface, .. } => {
                                charge_name(interface, budget)?
                            }
                        }
                    }
                }
            }
        }
        let source = self.retained_source(source, budget)?;
        Ok(LoadedModule {
            id: self.id,
            canonical_path: self.canonical_path.to_path_buf(),
            source,
            surface: SurfaceModule {
                imports: self.imports.to_vec(),
                syntax_declarations: Vec::new(),
                declaration_order: vec![SurfaceDeclarationIndex::Global(0)],
                foreign_libraries: Vec::new(),
                type_declarations: Vec::new(),
                interfaces: Vec::new(),
                effects: Vec::new(),
                implementations: Vec::new(),
                resources: Vec::new(),
                definitions: vec![definition],
                span: self.span,
            },
            dependencies: self.dependencies.to_vec().into_boxed_slice(),
            quote_sites,
            quote_introduction,
            caller_quote_owner: None,
        })
    }
}

struct StagedSyntax {
    imports: Vec<SurfaceImport>,
    span: Span,
    body: ModuleBody,
    import_span: Option<Span>,
    needs_quote_dependency: bool,
    needs_generator_dependency: bool,
}

enum ModuleBody {
    Parsed(SurfaceModule),
    Header(ParserCheckpoint),
}

impl StagedSyntax {
    fn parsed(
        mut surface: SurfaceModule,
        import_span: Option<Span>,
        needs_generator_dependency: bool,
    ) -> Self {
        Self {
            imports: std::mem::take(&mut surface.imports),
            span: surface.span,
            body: ModuleBody::Parsed(surface),
            import_span,
            needs_quote_dependency: false,
            needs_generator_dependency,
        }
    }
}

impl StagedModule {
    fn into_loaded(
        self,
        budget: &mut SyntaxBudget,
        syntax: &[crate::syntax::SelectedSyntax],
        owner_imports: &[Vec<crate::syntax::SelectedSyntax>],
        owners: &mut Vec<crate::syntax::SyntaxOwner>,
        transformer: Option<&mut StagedDeclarationTransformer<'_>>,
        quote: (Option<crate::syntax::SyntaxOwner>, &mut usize),
        resource_location: &mut Option<crate::syntax::DiagnosticLocation>,
    ) -> Result<LoadedModule, LoadGraphError> {
        let (quote_owner, next_quote_ordinal) = quote;
        let StagedSyntax {
            imports,
            span,
            body,
            import_span,
            needs_quote_dependency,
            needs_generator_dependency: _,
        } = self.surface;
        let mut completed_owners = None;
        let mut completed_sites = Vec::new();
        let mut completed_quote_introduction = None;
        let source_snapshot = std::cell::RefCell::new(None);
        let caller_quote_owner = std::cell::RefCell::new(None);
        let (source, surface) = match body {
            ModuleBody::Parsed(mut surface) => {
                surface.imports = imports;
                (self.source, surface)
            }
            ModuleBody::Header(checkpoint) => {
                let (tree, retained) = finish_module_from_checkpoint_with_syntax(
                    checkpoint,
                    budget.clone(),
                    Some(&self.source),
                    syntax,
                );
                *budget = retained;
                if let Err(resource) = budget
                    .charge_units(owners.len())
                    .and_then(|()| crate::syntax::charge_caller_owner_retains(owners, budget))
                {
                    return Err(LoadGraphError::Syntax(Box::new(ModuleSyntaxFailure {
                        lexical: Vec::new(),
                        parser: Vec::new(),
                        resource: Some(resource),
                        source: self.source,
                        import_span,
                    })));
                }
                let mut staged_owners = owners.clone();
                let quote_projection = if needs_quote_dependency {
                    if let Some(quote_owner) = quote_owner {
                        let owner_work = if staged_owners.len() == staged_owners.capacity() {
                            staged_owners.len().saturating_mul(2).saturating_add(1)
                        } else {
                            1
                        };
                        if let Err(resource) = budget.charge_units(owner_work) {
                            return Err(LoadGraphError::Syntax(Box::new(ModuleSyntaxFailure {
                                lexical: Vec::new(),
                                parser: Vec::new(),
                                resource: Some(resource),
                                source: self.source,
                                import_span,
                            })));
                        }
                        if staged_owners.len() == staged_owners.capacity() {
                            staged_owners.reserve_exact(1);
                        }
                        staged_owners.push(quote_owner);
                        completed_quote_introduction = Some(staged_owners.len());
                        Some(std::cell::RefCell::new(crate::parser::QuoteProjection {
                            introduction: staged_owners.len(),
                            next_ordinal: *next_quote_ordinal,
                            sites: Vec::new(),
                        }))
                    } else {
                        None
                    }
                } else {
                    None
                };
                let (source, mut surface) = {
                    let loan = StagedModuleLoan {
                        id: self.id,
                        source_id: self.source.id(),
                        canonical_path: &self.canonical_path,
                        imports: &imports,
                        dependencies: &self.dependencies,
                        span,
                        source_snapshot: &source_snapshot,
                        caller_quote_owner: &caller_quote_owner,
                        quote_projection: quote_projection.as_ref(),
                    };
                    let enabled = transformer.is_some();
                    let mut transformer = transformer;
                    let mut routed =
                        |selection: &crate::syntax::SelectedSyntax,
                         adapter: crate::syntax::DeclarationAdapter<'_>,
                         captures: &[crate::surface::SurfaceSyntaxCapture],
                         source: &SourceFile,
                         caller: &crate::surface::SurfaceName,
                         introduction: usize,
                         contexts: std::sync::Arc<crate::syntax::SyntaxContexts>,
                         frame: std::sync::Arc<crate::syntax::ExpansionFrame>,
                         owners: &mut Vec<crate::syntax::SyntaxOwner>,
                         budget: &mut SyntaxBudget| {
                            let Some(transformer) = transformer.as_deref_mut() else {
                                return Err(caller.span);
                            };
                            transformer(
                                selection,
                                adapter,
                                captures,
                                source,
                                &loan,
                                caller,
                                introduction,
                                contexts,
                                frame,
                                owners,
                                budget,
                            )
                        };
                    let callback = enabled
                        .then_some(&mut routed as &mut crate::syntax::DeclarationTransformer<'_>);
                    project_finished_module(
                        self.source,
                        tree,
                        import_span,
                        syntax,
                        owner_imports,
                        &mut staged_owners,
                        budget,
                        callback,
                        quote_projection.as_ref(),
                        resource_location,
                    )?
                };
                if surface.imports != imports {
                    return Err(LoadGraphError::Projection {
                        source,
                        error: ProjectionError::MalformedTree(
                            crate::parser::InternalReason::UnexpectedShape,
                        ),
                        import_span,
                    });
                }
                surface.imports = imports;
                completed_owners = Some(staged_owners);
                if let Some(quote_projection) = quote_projection {
                    let quote_projection = quote_projection.into_inner();
                    *next_quote_ordinal = quote_projection.next_ordinal;
                    completed_sites = quote_projection.sites;
                }
                (source, surface)
            }
        };
        if surface.span != span {
            return Err(LoadGraphError::Projection {
                source,
                error: ProjectionError::MalformedTree(crate::parser::InternalReason::InvalidSpan),
                import_span,
            });
        }
        let caller_quote_owner = caller_quote_owner.into_inner();
        if let Some(staged_owners) = completed_owners {
            *owners = staged_owners;
        }
        let source = match source_snapshot.into_inner() {
            Some(retained) => retained,
            None => std::sync::Arc::new(source),
        };
        Ok(LoadedModule {
            id: self.id,
            canonical_path: self.canonical_path,
            source,
            surface,
            dependencies: self.dependencies.into_boxed_slice(),
            quote_sites: completed_sites,
            quote_introduction: completed_quote_introduction,
            caller_quote_owner,
        })
    }
}

pub(crate) struct HeaderGraph {
    pending: VecDeque<StagedModule>,
    loaded: Vec<LoadedModule>,
    completed: Option<ModuleGraph>,
    entry: ModuleId,
    syntax_budget: SyntaxBudget,
    next_quote_ordinal: usize,
}

impl HeaderGraph {
    pub(crate) fn source_work(&self) -> Result<(crate::types::TypeWorkBudget, usize), ()> {
        if !self.loaded.is_empty() || self.completed.is_some() {
            return Err(());
        }
        crate::compiler_work::source_work_for_sources(
            self.pending.iter().map(|module| &module.source),
        )
    }

    pub(crate) fn len(&self) -> usize {
        self.pending.len() + self.loaded.len()
    }

    pub(crate) fn has_pending(&self) -> bool {
        !self.pending.is_empty()
    }

    pub(crate) fn next_imports(&self) -> Option<(&[SurfaceImport], &[ModuleDependency])> {
        self.pending.front().map(|module| {
            (
                module.surface.imports.as_slice(),
                module.dependencies.as_slice(),
            )
        })
    }

    pub(crate) fn next_quote_dependency(&self) -> Option<ModuleDependency> {
        let module = self.pending.front()?;
        module.surface.needs_quote_dependency.then(|| {
            module
                .dependencies
                .iter()
                .copied()
                .find(|edge| edge.target().is_builtin_compiler_syntax())
        })?
    }

    #[cfg(feature = "resource-calibration")]
    pub(crate) fn all_loaded(&self) -> bool {
        self.pending.is_empty()
    }

    #[cfg(test)]
    pub(crate) fn current_module(&self) -> Option<&LoadedModule> {
        match &self.completed {
            Some(graph) => graph.modules.last(),
            None => self.loaded.last(),
        }
    }

    pub(crate) fn current_module_with_syntax_budget(
        &mut self,
    ) -> Option<(&mut LoadedModule, &mut SyntaxBudget, &mut usize)> {
        let module = match &mut self.completed {
            Some(graph) => graph.modules.last_mut(),
            None => self.loaded.last_mut(),
        }?;
        Some((
            module,
            &mut self.syntax_budget,
            &mut self.next_quote_ordinal,
        ))
    }

    pub(crate) fn next_module(&mut self) -> Result<Option<&LoadedModule>, GraphDiagnostic> {
        self.next_module_with_syntax(&[], &[], &mut Vec::new(), None)
    }

    pub(crate) fn next_module_with_syntax(
        &mut self,
        syntax: &[crate::syntax::SelectedSyntax],
        owner_imports: &[Vec<crate::syntax::SelectedSyntax>],
        owners: &mut Vec<crate::syntax::SyntaxOwner>,
        transformer: Option<&mut StagedDeclarationTransformer<'_>>,
    ) -> Result<Option<&LoadedModule>, GraphDiagnostic> {
        self.next_module_with_syntax_and_quote_owner(
            syntax,
            owner_imports,
            owners,
            transformer,
            None,
        )
    }

    pub(crate) fn next_module_with_syntax_and_quote_owner(
        &mut self,
        syntax: &[crate::syntax::SelectedSyntax],
        owner_imports: &[Vec<crate::syntax::SelectedSyntax>],
        owners: &mut Vec<crate::syntax::SyntaxOwner>,
        transformer: Option<&mut StagedDeclarationTransformer<'_>>,
        quote_owner: Option<crate::syntax::SyntaxOwner>,
    ) -> Result<Option<&LoadedModule>, GraphDiagnostic> {
        let Some(module) = self.pending.pop_front() else {
            return Ok(None);
        };
        let mut resource_location = None;
        match module.into_loaded(
            &mut self.syntax_budget,
            syntax,
            owner_imports,
            owners,
            transformer,
            (quote_owner, &mut self.next_quote_ordinal),
            &mut resource_location,
        ) {
            Ok(module) => {
                self.loaded.push(module);
                Ok(self.loaded.last())
            }
            Err(failure) => {
                let loaded = std::mem::take(&mut self.loaded);
                let pending = std::mem::take(&mut self.pending);
                Err(GraphDiagnostic {
                    failure: Box::new(failure),
                    sources: loaded
                        .into_iter()
                        .map(LoadedModule::into_source)
                        .chain(pending.into_iter().map(|module| module.source))
                        .collect::<Vec<_>>()
                        .into_boxed_slice(),
                    compilation_work: None,
                    resource_location,
                })
            }
        }
    }

    pub(crate) fn completed_graph(&mut self) -> Option<&ModuleGraph> {
        if !self.pending.is_empty() {
            return None;
        }
        if self.completed.is_none() {
            self.completed = Some(ModuleGraph {
                modules: std::mem::take(&mut self.loaded).into_boxed_slice(),
                entry: self.entry,
            });
        }
        self.completed.as_ref()
    }

    pub(crate) fn completed_graph_with_syntax_budget(
        &mut self,
    ) -> Option<(&ModuleGraph, &mut SyntaxBudget)> {
        self.completed_graph()?;
        Some((self.completed.as_ref()?, &mut self.syntax_budget))
    }

    pub(crate) fn into_sources(self) -> Box<[SourceFile]> {
        if let Some(graph) = self.completed {
            return graph.into_sources();
        }
        self.loaded
            .into_iter()
            .map(LoadedModule::into_source)
            .chain(self.pending.into_iter().map(|module| module.source))
            .collect::<Vec<_>>()
            .into_boxed_slice()
    }
}

#[derive(Clone, Copy, Debug)]
struct TraversalFrame {
    module: ModuleId,
    next_import: usize,
}

#[derive(Clone, Copy, Debug)]
struct GraphLimits {
    sources: usize,
    edges: usize,
    path_segments: usize,
    owner_facts: usize,
    pending_work: usize,
}

impl Default for GraphLimits {
    fn default() -> Self {
        Self {
            sources: MODULE_SOURCE_LIMIT,
            edges: MODULE_EDGE_LIMIT,
            path_segments: MODULE_PATH_SEGMENT_LIMIT,
            owner_facts: MODULE_OWNER_FACT_LIMIT,
            pending_work: MODULE_PENDING_LIMIT,
        }
    }
}

#[derive(Debug, Default)]
struct GraphBudget {
    sources: usize,
    edges: usize,
    path_segments: usize,
    owner_facts: usize,
    pending_work: usize,
    syntax_work: SyntaxBudget,
    mode: BodyMode,
    limits: GraphLimits,
}

#[derive(Clone, Copy, Debug, Default)]
enum BodyMode {
    #[default]
    Complete,
    Header,
}

impl GraphBudget {
    #[cfg(test)]
    fn with_limits(limits: GraphLimits) -> Self {
        Self {
            limits,
            ..Self::default()
        }
    }

    fn charge_sources(&mut self) -> Result<(), LoadGraphError> {
        charge(
            &mut self.sources,
            1,
            self.limits.sources,
            ModuleResource::Sources,
        )
    }

    fn charge_edge(&mut self) -> Result<(), LoadGraphError> {
        charge(&mut self.edges, 1, self.limits.edges, ModuleResource::Edges)
    }

    fn charge_path_segments(&mut self, amount: usize) -> Result<(), LoadGraphError> {
        charge(
            &mut self.path_segments,
            amount,
            self.limits.path_segments,
            ModuleResource::PathSegments,
        )
    }

    fn charge_owner_facts(&mut self, amount: usize) -> Result<(), LoadGraphError> {
        charge(
            &mut self.owner_facts,
            amount,
            self.limits.owner_facts,
            ModuleResource::OwnerFacts,
        )
    }

    fn retain_pending_work(&mut self) -> Result<(), LoadGraphError> {
        charge(
            &mut self.pending_work,
            1,
            self.limits.pending_work,
            ModuleResource::PendingWork,
        )
    }

    fn release_pending_work(&mut self) {
        debug_assert!(
            self.pending_work > 0,
            "pending graph work must be retained before it is released"
        );
        self.pending_work -= 1;
    }
}

fn charge(
    used: &mut usize,
    amount: usize,
    limit: usize,
    resource: ModuleResource,
) -> Result<(), LoadGraphError> {
    let Some(next) = used.checked_add(amount) else {
        return Err(ModuleFailure::resource(resource).into());
    };
    if next > limit {
        return Err(ModuleFailure::resource(resource).into());
    }
    *used = next;
    Ok(())
}

/// Loads and parses the canonical dependency closure of one entry module.
///
/// Modules are returned in deterministic dependency order. One canonical
/// source receives one [`ModuleId`] even when multiple paths or overlapping
/// roots reach it.
///
/// # Errors
///
/// Returns the first failing input or compiler stage in source-ordered
/// depth-first traversal, with the admitted diagnostic sources retained. Syntax
/// selectors require [`crate::driver::compile_path`] and are rejected here.
pub fn load_module_graph(
    entry: &Path,
    roots: &ModuleRoots,
) -> Result<ModuleGraph, GraphDiagnostic> {
    let mut graph = discover_graph(entry, roots, BodyMode::Complete)?;
    while graph.next_module()?.is_some() {}
    graph.completed_graph();
    Ok(graph.completed.expect("all complete modules were retained"))
}

pub(crate) fn discover_headers(
    entry: &Path,
    roots: &ModuleRoots,
) -> Result<HeaderGraph, GraphDiagnostic> {
    discover_graph(entry, roots, BodyMode::Header)
}

fn discover_graph(
    entry: &Path,
    roots: &ModuleRoots,
    mode: BodyMode,
) -> Result<HeaderGraph, GraphDiagnostic> {
    discover_graph_with_budget(
        entry,
        roots,
        GraphBudget {
            mode,
            ..GraphBudget::default()
        },
    )
}

fn discover_graph_with_budget(
    entry: &Path,
    roots: &ModuleRoots,
    mut budget: GraphBudget,
) -> Result<HeaderGraph, GraphDiagnostic> {
    let mut staged = Vec::new();
    let result: Result<HeaderGraph, LoadGraphError> = (|| {
        let canonical_entry = fs::canonicalize(entry).map_err(|error| LoadGraphError::Read {
            path: entry.to_path_buf(),
            kind: error.kind(),
            import_span: None,
        })?;
        let entry_root = canonical_entry
            .parent()
            .map(Path::to_path_buf)
            .ok_or_else(|| LoadGraphError::Read {
                path: canonical_entry.clone(),
                kind: io::ErrorKind::InvalidInput,
                import_span: None,
            })?;

        let graph_identity = allocate_module_graph_identity()?;
        let mut by_path = HashMap::new();
        let entry_id = admit_module(
            canonical_entry,
            OwnerSet::from_paths(std::slice::from_ref(&entry_root), &mut budget)?,
            None,
            &mut staged,
            &mut by_path,
            &mut budget,
            graph_identity,
        )?;
        budget.retain_pending_work()?;
        let mut frames = vec![TraversalFrame {
            module: entry_id,
            next_import: 0,
        }];
        let mut dependency_order = Vec::new();
        let mut builtin_cell = None;
        let mut builtin_generic_cell = None;
        let mut builtin_retained_control = None;
        let mut builtin_network = None;
        let mut builtin_integer = None;
        let mut builtin_bytes = None;
        let mut builtin_string = None;
        let mut builtin_foreign = None;
        let mut builtin_compiler_syntax = None;
        let mut builtin_region = None;
        let mut builtin_region_facade = None;

        while let Some(frame) = frames.last() {
            let module = frame.module;
            let module_index = module.index();
            let import_index = frame.next_import;
            if import_index == 0
                && staged[module_index].dependencies.is_empty()
                && matches!(module.namespace, ModuleIdNamespace::Admitted)
            {
                let span = staged[module_index].surface.span;
                let target = if let Some(region) = builtin_region {
                    region
                } else {
                    let region = admit_builtin_region(
                        graph_identity,
                        span,
                        &mut budget,
                        &mut staged,
                        &mut dependency_order,
                        &mut builtin_foreign,
                    )?;
                    builtin_region = Some(region);
                    region
                };
                budget.charge_edge()?;
                staged[module_index]
                    .dependencies
                    .try_reserve(1)
                    .map_err(|_| ModuleFailure::resource(ModuleResource::Edges))?;
                staged[module_index].dependencies.push(ModuleDependency {
                    target,
                    import_span: span,
                    compiler_private: true,
                });
            }
            if import_index == staged[module_index].surface.imports.len() {
                let completed = module;
                // Source import ordinals stay unchanged. The private compiler
                // dependency follows the explicit imports and binds no namespace.
                if staged[module_index]
                    .dependencies
                    .first()
                    .is_some_and(|edge| edge.is_compiler_private())
                {
                    staged[module_index].dependencies.rotate_left(1);
                }
                if (staged[module_index].surface.needs_quote_dependency
                    || staged[module_index].surface.needs_generator_dependency)
                    && !staged[module_index]
                        .dependencies
                        .iter()
                        .any(|edge| edge.target.is_builtin_compiler_syntax())
                {
                    let span = staged[module_index].surface.span;
                    let target = if let Some(id) = builtin_compiler_syntax {
                        id
                    } else {
                        let region = builtin_region
                            .ok_or_else(|| ModuleFailure::resource(ModuleResource::Sources))?;
                        let id = admit_builtin_packed(
                            "compiler.syntax",
                            region,
                            graph_identity,
                            span,
                            &mut budget,
                            &mut staged,
                            &mut dependency_order,
                        )?;
                        builtin_compiler_syntax = Some(id);
                        id
                    };
                    budget.charge_edge()?;
                    staged[module_index]
                        .dependencies
                        .try_reserve(1)
                        .map_err(|_| ModuleFailure::resource(ModuleResource::Edges))?;
                    staged[module_index].dependencies.push(ModuleDependency {
                        target,
                        import_span: span,
                        compiler_private: true,
                    });
                }
                staged[module_index].state = VisitState::Finished;
                dependency_order.push(completed);
                frames.pop();
                budget.release_pending_work();
                continue;
            }

            budget.charge_edge()?;
            budget.charge_path_segments(import_segment_count(
                &staged[module_index].surface.imports[import_index],
            ))?;
            let import = staged[module_index].surface.imports[import_index].clone();
            if matches!(budget.mode, BodyMode::Complete)
                && let SurfaceImportSelection::Targeted(items) = &import.selection
                && let Some(span) = items.iter().find_map(|item| match item {
                    SurfaceImportItem::Syntax { span, .. } => Some(*span),
                    _ => None,
                })
            {
                let mut failure =
                    ModuleFailure::source(ModuleReason::SyntaxRequiresDriver, span, None);
                failure.source_rejection = false;
                return Err(failure.into());
            }
            frames
                .last_mut()
                .expect("the loop observed one traversal frame")
                .next_import += 1;

            if let SurfaceModulePath::Absolute { root, .. } = &import.path
                && root.text == "foreign"
            {
                return Err(
                    ModuleFailure::source(ModuleReason::UnknownForeign, import.span, None).into(),
                );
            }

            if let SurfaceModulePath::Absolute { root, segments } = &import.path
                && root.text == "builtin"
            {
                let name = match segments.as_slice() {
                    [compiler, syntax]
                        if compiler.text == "compiler" && syntax.text == "syntax" =>
                    {
                        "compiler.syntax"
                    }
                    [segment]
                        if matches!(
                            segment.text.as_str(),
                            "cell"
                                | "generic_cell"
                                | "retained_control"
                                | "network"
                                | "bytes"
                                | "string"
                                | "integer"
                                | "foreign"
                                | "regions"
                        ) =>
                    {
                        segment.text.as_str()
                    }
                    _ => {
                        return Err(ModuleFailure::source(
                            ModuleReason::UnknownBuiltin,
                            import.span,
                            None,
                        )
                        .into());
                    }
                };
                let packed = matches!(name, "bytes" | "string" | "integer" | "compiler.syntax");
                let cached = if name == "compiler.syntax" {
                    &mut builtin_compiler_syntax
                } else if name == "regions" {
                    &mut builtin_region_facade
                } else if name == "integer" {
                    &mut builtin_integer
                } else if name == "bytes" {
                    &mut builtin_bytes
                } else if name == "string" {
                    &mut builtin_string
                } else if name == "foreign" {
                    &mut builtin_foreign
                } else if name == "generic_cell" {
                    &mut builtin_generic_cell
                } else if name == "retained_control" {
                    &mut builtin_retained_control
                } else if name == "network" {
                    &mut builtin_network
                } else {
                    &mut builtin_cell
                };
                let target = if let Some(id) = *cached {
                    id
                } else {
                    let id = if name == "regions" {
                        let service = builtin_region.ok_or_else(|| {
                            ModuleFailure::source(ModuleReason::UnknownBuiltin, import.span, None)
                        })?;
                        admit_builtin_region_facade(
                            graph_identity,
                            import.span,
                            service,
                            &mut budget,
                            &mut staged,
                            &mut dependency_order,
                        )?
                    } else if name == "foreign" {
                        admit_builtin_foreign(
                            graph_identity,
                            import.span,
                            &mut budget,
                            &mut staged,
                            &mut dependency_order,
                        )?
                    } else if name == "retained_control" {
                        admit_builtin_retained_control(
                            graph_identity,
                            import.span,
                            builtin_region
                                .ok_or_else(|| ModuleFailure::resource(ModuleResource::Sources))?,
                            &mut budget,
                            &mut staged,
                            &mut dependency_order,
                        )?
                    } else if name == "network" {
                        admit_builtin_network(
                            graph_identity,
                            import.span,
                            builtin_region
                                .ok_or_else(|| ModuleFailure::resource(ModuleResource::Sources))?,
                            &mut budget,
                            &mut staged,
                            &mut dependency_order,
                        )?
                    } else if packed {
                        admit_builtin_packed(
                            name,
                            builtin_region
                                .ok_or_else(|| ModuleFailure::resource(ModuleResource::Sources))?,
                            graph_identity,
                            import.span,
                            &mut budget,
                            &mut staged,
                            &mut dependency_order,
                        )?
                    } else {
                        admit_builtin_resource(
                            name == "generic_cell",
                            graph_identity,
                            import.span,
                            &mut budget,
                            &mut staged,
                            &mut dependency_order,
                        )?
                    };
                    *cached = Some(id);
                    id
                };
                staged[module_index]
                    .dependencies
                    .try_reserve(1)
                    .map_err(|_| ModuleFailure::resource(ModuleResource::Edges))?;
                staged[module_index].dependencies.push(ModuleDependency {
                    target,
                    import_span: import.span,
                    compiler_private: false,
                });
                continue;
            }

            let (target_path, owners, relative) =
                resolve_import(&staged[module_index], &import, roots)?;
            let existing = by_path.get(&target_path).copied();
            let target = if let Some(target) = existing {
                propagate_owners(target, owners, import.span, &mut staged, &mut budget)?;
                target
            } else {
                let owners = admitted_owners(owners, &staged, &mut budget)?;
                admit_module(
                    target_path.clone(),
                    owners,
                    Some(import.span),
                    &mut staged,
                    &mut by_path,
                    &mut budget,
                    graph_identity,
                )?
            };

            staged[module_index].dependencies.push(ModuleDependency {
                target,
                import_span: import.span,
                compiler_private: false,
            });
            if relative {
                staged[module_index].relative_edges.push(RelativeEdge {
                    target,
                    canonical_target: target_path,
                    import_span: import.span,
                });
            }

            if existing.is_some() {
                if staged[target.index()].state == VisitState::Active {
                    return Err(ModuleFailure::source(
                        ModuleReason::ImportCycle,
                        import.span,
                        Some(staged[target.index()].canonical_path.clone()),
                    )
                    .into());
                }
            } else {
                budget.retain_pending_work()?;
                frames.push(TraversalFrame {
                    module: target,
                    next_import: 0,
                });
            }
        }

        let mut positions = vec![0_usize; staged.len()];
        for (position, module) in dependency_order.into_iter().enumerate() {
            positions[module.index()] = position;
        }
        staged.sort_by_key(|module| positions[module.id.index()]);
        let pending = std::mem::take(&mut staged).into();
        Ok(HeaderGraph {
            pending,
            loaded: Vec::new(),
            completed: None,
            entry: entry_id,
            syntax_budget: budget.syntax_work,
            next_quote_ordinal: 0,
        })
    })();
    result.map_err(|failure| GraphDiagnostic {
        failure: Box::new(failure),
        sources: staged
            .into_iter()
            .map(|module| module.source)
            .collect::<Vec<_>>()
            .into_boxed_slice(),
        compilation_work: None,
        resource_location: None,
    })
}

fn admit_builtin_region_facade(
    graph: u32,
    import_span: Span,
    service: ModuleId,
    budget: &mut GraphBudget,
    staged: &mut Vec<StagedModule>,
    dependency_order: &mut Vec<ModuleId>,
) -> Result<ModuleId, LoadGraphError> {
    budget.charge_sources()?;
    budget.charge_edge()?;
    staged
        .try_reserve(1)
        .map_err(|_| ModuleFailure::resource(ModuleResource::Sources))?;
    dependency_order
        .try_reserve(1)
        .map_err(|_| ModuleFailure::resource(ModuleResource::Sources))?;
    let mut text = String::new();
    text.try_reserve_exact(REGION_FACADE_SOURCE.len())
        .map_err(|_| ModuleFailure::resource(ModuleResource::Sources))?;
    text.push_str(REGION_FACADE_SOURCE);
    let path = PathBuf::from("@builtin.regions");
    let (source, surface) = parse_graph_module(
        &path,
        text,
        Some(import_span),
        &mut budget.syntax_work,
        budget.mode,
    )?;
    let value = u32::try_from(staged.len())
        .map_err(|_| ModuleFailure::resource(ModuleResource::Sources))?;
    let id = ModuleId {
        namespace: ModuleIdNamespace::BuiltinRegionFacade,
        graph,
        value,
    };
    let mut dependencies = Vec::new();
    dependencies
        .try_reserve_exact(1)
        .map_err(|_| ModuleFailure::resource(ModuleResource::Edges))?;
    let span = surface
        .imports
        .first()
        .ok_or_else(|| ModuleFailure::resource(ModuleResource::Sources))?
        .span;
    dependencies.push(ModuleDependency {
        target: service,
        import_span: span,
        compiler_private: false,
    });
    staged.push(StagedModule {
        id,
        canonical_path: path,
        owners: OwnerSet::from_paths(&[], budget)?,
        source,
        surface,
        dependencies,
        relative_edges: Vec::new(),
        state: VisitState::Finished,
    });
    dependency_order.push(id);
    Ok(id)
}

fn admit_builtin_region(
    graph: u32,
    owner_span: Span,
    budget: &mut GraphBudget,
    staged: &mut Vec<StagedModule>,
    dependency_order: &mut Vec<ModuleId>,
    builtin_foreign: &mut Option<ModuleId>,
) -> Result<ModuleId, LoadGraphError> {
    let foreign = if let Some(module) = *builtin_foreign {
        module
    } else {
        let module = admit_builtin_foreign(graph, owner_span, budget, staged, dependency_order)?;
        *builtin_foreign = Some(module);
        module
    };
    budget.charge_sources()?;
    staged
        .try_reserve(1)
        .map_err(|_| ModuleFailure::resource(ModuleResource::Sources))?;
    dependency_order
        .try_reserve(1)
        .map_err(|_| ModuleFailure::resource(ModuleResource::Sources))?;
    let mut text = String::new();
    text.try_reserve_exact(REGION_SOURCE.len())
        .map_err(|_| ModuleFailure::resource(ModuleResource::Sources))?;
    text.push_str(REGION_SOURCE);
    let path = PathBuf::from("@compiler.region");
    let (source, surface) = parse_graph_module(
        &path,
        text,
        Some(owner_span),
        &mut budget.syntax_work,
        budget.mode,
    )?;
    let value = u32::try_from(staged.len())
        .map_err(|_| ModuleFailure::resource(ModuleResource::Sources))?;
    let id = ModuleId {
        namespace: ModuleIdNamespace::BuiltinRegion,
        graph,
        value,
    };
    budget.charge_edge()?;
    let mut dependencies = Vec::new();
    dependencies
        .try_reserve_exact(1)
        .map_err(|_| ModuleFailure::resource(ModuleResource::Edges))?;
    let import_span = surface
        .imports
        .first()
        .ok_or_else(|| ModuleFailure::resource(ModuleResource::Sources))?
        .span;
    dependencies.push(ModuleDependency {
        target: foreign,
        import_span,
        compiler_private: false,
    });
    staged.push(StagedModule {
        id,
        canonical_path: path,
        owners: OwnerSet::from_paths(&[], budget)?,
        source,
        surface,
        dependencies,
        relative_edges: Vec::new(),
        state: VisitState::Finished,
    });
    dependency_order.push(id);
    Ok(id)
}

fn admit_builtin_foreign(
    graph: u32,
    import_span: Span,
    budget: &mut GraphBudget,
    staged: &mut Vec<StagedModule>,
    dependency_order: &mut Vec<ModuleId>,
) -> Result<ModuleId, LoadGraphError> {
    budget.charge_sources()?;
    staged
        .try_reserve(1)
        .map_err(|_| ModuleFailure::resource(ModuleResource::Sources))?;
    dependency_order
        .try_reserve(1)
        .map_err(|_| ModuleFailure::resource(ModuleResource::Sources))?;
    let mut text = String::new();
    text.try_reserve_exact(FOREIGN_SOURCE.len())
        .map_err(|_| ModuleFailure::resource(ModuleResource::Sources))?;
    text.push_str(FOREIGN_SOURCE);
    let path = PathBuf::from("@builtin.foreign");
    let (source, surface) = parse_graph_module(
        &path,
        text,
        Some(import_span),
        &mut budget.syntax_work,
        budget.mode,
    )?;
    let value = u32::try_from(staged.len())
        .map_err(|_| ModuleFailure::resource(ModuleResource::Sources))?;
    let id = ModuleId {
        namespace: ModuleIdNamespace::BuiltinForeign,
        graph,
        value,
    };
    let owners = OwnerSet::from_paths(&[], budget)?;
    staged.push(StagedModule {
        id,
        canonical_path: path,
        owners,
        source,
        surface,
        dependencies: Vec::new(),
        relative_edges: Vec::new(),
        state: VisitState::Finished,
    });
    dependency_order.push(id);
    Ok(id)
}

fn admit_builtin_packed(
    kind: &str,
    region: ModuleId,
    graph: u32,
    import_span: Span,
    budget: &mut GraphBudget,
    staged: &mut Vec<StagedModule>,
    dependency_order: &mut Vec<ModuleId>,
) -> Result<ModuleId, LoadGraphError> {
    budget.charge_sources()?;
    staged
        .try_reserve(1)
        .map_err(|_| ModuleFailure::resource(ModuleResource::Sources))?;
    dependency_order
        .try_reserve(1)
        .map_err(|_| ModuleFailure::resource(ModuleResource::Sources))?;
    let (path, text, namespace) = match kind {
        "bytes" => (
            "@builtin.bytes",
            BYTES_SOURCE,
            ModuleIdNamespace::BuiltinBytes,
        ),
        "string" => (
            "@builtin.string",
            STRING_SOURCE,
            ModuleIdNamespace::BuiltinString,
        ),
        "integer" => (
            "@builtin.integer",
            INTEGER_SOURCE,
            ModuleIdNamespace::BuiltinInteger,
        ),
        "compiler.syntax" => (
            "@builtin.compiler.syntax",
            COMPILER_SYNTAX_SOURCE,
            ModuleIdNamespace::BuiltinCompilerSyntax,
        ),
        _ => {
            return Err(
                ModuleFailure::source(ModuleReason::UnknownBuiltin, import_span, None).into(),
            );
        }
    };
    let path = PathBuf::from(path);
    let (source, surface) = parse_graph_module(
        &path,
        text.to_owned(),
        Some(import_span),
        &mut budget.syntax_work,
        budget.mode,
    )?;
    let value = u32::try_from(staged.len())
        .map_err(|_| ModuleFailure::resource(ModuleResource::Sources))?;
    let id = ModuleId {
        namespace,
        graph,
        value,
    };
    budget.charge_edge()?;
    let service_span = surface.span;
    staged.push(StagedModule {
        id,
        canonical_path: path,
        owners: OwnerSet::from_paths(&[], budget)?,
        source,
        surface,
        dependencies: vec![ModuleDependency {
            target: region,
            import_span: service_span,
            compiler_private: true,
        }],
        relative_edges: Vec::new(),
        state: VisitState::Finished,
    });
    dependency_order.push(id);
    Ok(id)
}

fn admit_builtin_resource(
    generic: bool,
    graph: u32,
    import_span: Span,
    budget: &mut GraphBudget,
    staged: &mut Vec<StagedModule>,
    dependency_order: &mut Vec<ModuleId>,
) -> Result<ModuleId, LoadGraphError> {
    budget.charge_sources()?;
    staged
        .try_reserve(1)
        .map_err(|_| ModuleFailure::resource(ModuleResource::Sources))?;
    dependency_order
        .try_reserve(1)
        .map_err(|_| ModuleFailure::resource(ModuleResource::Sources))?;
    let path = PathBuf::from(if generic {
        "@builtin.generic_cell"
    } else {
        "@builtin.cell"
    });
    let (source, surface) = parse_graph_module(
        &path,
        if generic {
            GENERIC_CELL_SOURCE
        } else {
            CELL_SOURCE
        }
        .to_owned(),
        Some(import_span),
        &mut budget.syntax_work,
        budget.mode,
    )?;
    let value = u32::try_from(staged.len())
        .map_err(|_| ModuleFailure::resource(ModuleResource::Sources))?;
    let id = ModuleId {
        namespace: if generic {
            ModuleIdNamespace::BuiltinGenericCell
        } else {
            ModuleIdNamespace::BuiltinCell
        },
        graph,
        value,
    };
    staged.push(StagedModule {
        id,
        canonical_path: path,
        owners: OwnerSet::from_paths(&[], budget)?,
        source,
        surface,
        dependencies: Vec::new(),
        relative_edges: Vec::new(),
        state: VisitState::Finished,
    });
    dependency_order.push(id);
    Ok(id)
}

fn admit_builtin_retained_control(
    graph: u32,
    import_span: Span,
    region: ModuleId,
    budget: &mut GraphBudget,
    staged: &mut Vec<StagedModule>,
    dependency_order: &mut Vec<ModuleId>,
) -> Result<ModuleId, LoadGraphError> {
    budget.charge_sources()?;
    staged
        .try_reserve(1)
        .map_err(|_| ModuleFailure::resource(ModuleResource::Sources))?;
    dependency_order
        .try_reserve(1)
        .map_err(|_| ModuleFailure::resource(ModuleResource::Sources))?;
    let path = PathBuf::from("@builtin.retained_control");
    let (source, surface) = parse_graph_module(
        &path,
        RETAINED_CONTROL_SOURCE.to_owned(),
        Some(import_span),
        &mut budget.syntax_work,
        budget.mode,
    )?;
    let value = u32::try_from(staged.len())
        .map_err(|_| ModuleFailure::resource(ModuleResource::Sources))?;
    let id = ModuleId {
        namespace: ModuleIdNamespace::BuiltinRetainedControl,
        graph,
        value,
    };
    budget.charge_edge()?;
    let service_span = surface.span;
    staged.push(StagedModule {
        id,
        canonical_path: path,
        owners: OwnerSet::from_paths(&[], budget)?,
        source,
        surface,
        dependencies: vec![ModuleDependency {
            target: region,
            import_span: service_span,
            compiler_private: true,
        }],
        relative_edges: Vec::new(),
        state: VisitState::Finished,
    });
    dependency_order.push(id);
    Ok(id)
}

fn admit_builtin_network(
    graph: u32,
    import_span: Span,
    region: ModuleId,
    budget: &mut GraphBudget,
    staged: &mut Vec<StagedModule>,
    dependency_order: &mut Vec<ModuleId>,
) -> Result<ModuleId, LoadGraphError> {
    budget.charge_sources()?;
    staged
        .try_reserve(1)
        .map_err(|_| ModuleFailure::resource(ModuleResource::Sources))?;
    dependency_order
        .try_reserve(1)
        .map_err(|_| ModuleFailure::resource(ModuleResource::Sources))?;
    let path = PathBuf::from("@builtin.network");
    let (source, surface) = parse_graph_module(
        &path,
        NETWORK_SOURCE.to_owned(),
        Some(import_span),
        &mut budget.syntax_work,
        budget.mode,
    )?;
    let value = u32::try_from(staged.len())
        .map_err(|_| ModuleFailure::resource(ModuleResource::Sources))?;
    let id = ModuleId {
        namespace: ModuleIdNamespace::BuiltinNetwork,
        graph,
        value,
    };
    budget.charge_edge()?;
    let service_span = surface.span;
    staged.push(StagedModule {
        id,
        canonical_path: path,
        owners: OwnerSet::from_paths(&[], budget)?,
        source,
        surface,
        dependencies: vec![ModuleDependency {
            target: region,
            import_span: service_span,
            compiler_private: true,
        }],
        relative_edges: Vec::new(),
        state: VisitState::Finished,
    });
    dependency_order.push(id);
    Ok(id)
}

fn admit_module(
    canonical_path: PathBuf,
    owners: OwnerSet,
    import_span: Option<Span>,
    staged: &mut Vec<StagedModule>,
    by_path: &mut HashMap<PathBuf, ModuleId>,
    budget: &mut GraphBudget,
    graph_identity: u32,
) -> Result<ModuleId, LoadGraphError> {
    budget.charge_sources()?;
    let (source, surface) = load_surface_module(
        &canonical_path,
        import_span,
        &mut budget.syntax_work,
        budget.mode,
    )?;
    let id_value = u32::try_from(staged.len())
        .map_err(|_| ModuleFailure::resource(ModuleResource::Sources))?;
    let id = ModuleId::admitted(graph_identity, id_value);
    by_path.insert(canonical_path.clone(), id);
    staged.push(StagedModule {
        id,
        canonical_path,
        owners,
        source,
        surface,
        dependencies: Vec::new(),
        relative_edges: Vec::new(),
        state: VisitState::Active,
    });
    Ok(id)
}

fn load_surface_module(
    path: &Path,
    import_span: Option<Span>,
    syntax_budget: &mut SyntaxBudget,
    mode: BodyMode,
) -> Result<(SourceFile, StagedSyntax), LoadGraphError> {
    let bytes = fs::read(path).map_err(|error| LoadGraphError::Read {
        path: path.to_path_buf(),
        kind: error.kind(),
        import_span,
    })?;
    let text = String::from_utf8(bytes).map_err(|_| LoadGraphError::InvalidUtf8 {
        path: path.to_path_buf(),
        import_span,
    })?;
    parse_graph_module(path, text, import_span, syntax_budget, mode)
}

fn parse_graph_module(
    path: &Path,
    text: String,
    import_span: Option<Span>,
    syntax_budget: &mut SyntaxBudget,
    mode: BodyMode,
) -> Result<(SourceFile, StagedSyntax), LoadGraphError> {
    if matches!(mode, BodyMode::Complete) {
        let (source, surface, needs_generator_dependency) =
            parse_surface_module(path, text, import_span, syntax_budget)?;
        return Ok((
            source,
            StagedSyntax::parsed(surface, import_span, needs_generator_dependency),
        ));
    }
    let source = SourceFile::new(path.to_string_lossy(), text).map_err(|error| {
        LoadGraphError::SourceModel {
            path: path.to_path_buf(),
            error,
            operation: crate::source::SourceOperation::Admission,
            import_span,
        }
    })?;
    let lexed =
        lex_with_budget(&source, syntax_budget).map_err(|error| LoadGraphError::SourceModel {
            path: path.to_path_buf(),
            error,
            operation: crate::source::SourceOperation::SpanConstruction,
            import_span,
        })?;
    let needs_quote_dependency = lexed.needs_quote_dependency();
    let needs_generator_dependency = lexed.needs_generator_dependency();
    let (tokens, lexical, _, lexical_failure) = lexed.into_parts();
    if let Some(resource) = lexical_failure {
        return Err(LoadGraphError::Syntax(Box::new(ModuleSyntaxFailure {
            lexical,
            parser: Vec::new(),
            resource: Some(resource),
            source,
            import_span,
        })));
    }
    let (checkpoint, retained) = parse_module_header(tokens, lexical, syntax_budget.clone());
    *syntax_budget = retained;
    let imports = match project_module_header(&source, &checkpoint) {
        Ok(imports) => imports,
        Err(error) => {
            if matches!(
                error,
                ProjectionError::RecoveryNodesPresent | ProjectionError::ResourceLimit(_)
            ) && (checkpoint.resource_failure().is_some()
                || !checkpoint.lexical_diagnostics().is_empty()
                || !checkpoint.parse_diagnostics().is_empty())
            {
                return Err(LoadGraphError::Syntax(Box::new(ModuleSyntaxFailure {
                    lexical: checkpoint.lexical_diagnostics().to_vec(),
                    parser: checkpoint.parse_diagnostics().to_vec(),
                    resource: checkpoint.resource_failure(),
                    source,
                    import_span,
                })));
            }
            return Err(LoadGraphError::Projection {
                source,
                error,
                import_span,
            });
        }
    };
    let span = match module_span_from_checkpoint(&source, &checkpoint) {
        Ok(span) => span,
        Err(error) => {
            return Err(LoadGraphError::Projection {
                source,
                error,
                import_span,
            });
        }
    };
    Ok((
        source,
        StagedSyntax {
            imports,
            span,
            body: ModuleBody::Header(checkpoint),
            import_span,
            needs_quote_dependency,
            needs_generator_dependency,
        },
    ))
}

// Source, syntax owners and the budget are separate projection inputs.
#[allow(clippy::too_many_arguments)]
fn project_finished_module(
    source: SourceFile,
    tree: crate::parser::ConcreteTree,
    import_span: Option<Span>,
    syntax: &[crate::syntax::SelectedSyntax],
    owner_imports: &[Vec<crate::syntax::SelectedSyntax>],
    owners: &mut Vec<crate::syntax::SyntaxOwner>,
    budget: &mut SyntaxBudget,
    transformer: Option<&mut crate::syntax::DeclarationTransformer<'_>>,
    quote_sites: Option<&std::cell::RefCell<crate::parser::QuoteProjection>>,
    resource_location: &mut Option<crate::syntax::DiagnosticLocation>,
) -> Result<(SourceFile, SurfaceModule), LoadGraphError> {
    if tree.resource_failure().is_some()
        || !tree.lexical_diagnostics().is_empty()
        || !tree.parse_diagnostics().is_empty()
    {
        return Err(LoadGraphError::Syntax(Box::new(ModuleSyntaxFailure {
            lexical: tree.lexical_diagnostics().to_vec(),
            parser: tree.parse_diagnostics().to_vec(),
            resource: tree.resource_failure(),
            source,
            import_span,
        })));
    }
    match crate::parser::project_declaration_expansions_with_resource(
        &source,
        &tree,
        syntax,
        owner_imports,
        owners,
        budget,
        transformer,
        quote_sites,
        resource_location,
    ) {
        Ok(surface) => Ok((source, surface)),
        Err(crate::parser::DeclarationExpansionFailure::Projection(error)) => {
            Err(LoadGraphError::Projection {
                source,
                error,
                import_span,
            })
        }
        Err(crate::parser::DeclarationExpansionFailure::Syntax {
            diagnostics,
            resource,
        }) => Err(LoadGraphError::Syntax(Box::new(ModuleSyntaxFailure {
            lexical: Vec::new(),
            parser: diagnostics,
            resource,
            source,
            import_span,
        }))),
    }
}

fn parse_surface_module(
    path: &Path,
    text: String,
    import_span: Option<Span>,
    syntax_budget: &mut SyntaxBudget,
) -> Result<(SourceFile, SurfaceModule, bool), LoadGraphError> {
    let source = SourceFile::new(path.to_string_lossy(), text).map_err(|error| {
        LoadGraphError::SourceModel {
            path: path.to_path_buf(),
            error,
            operation: crate::source::SourceOperation::Admission,
            import_span,
        }
    })?;
    let lexed =
        lex_with_budget(&source, syntax_budget).map_err(|error| LoadGraphError::SourceModel {
            path: path.to_path_buf(),
            error,
            operation: crate::source::SourceOperation::SpanConstruction,
            import_span,
        })?;
    let needs_generator_dependency = lexed.needs_generator_dependency();
    let (tree, header_imports) = parse_with_budget_and_header(&source, lexed, syntax_budget);
    if tree.resource_failure().is_some()
        || !tree.lexical_diagnostics().is_empty()
        || !tree.parse_diagnostics().is_empty()
    {
        return Err(LoadGraphError::Syntax(Box::new(ModuleSyntaxFailure {
            lexical: tree.lexical_diagnostics().to_vec(),
            parser: tree.parse_diagnostics().to_vec(),
            resource: tree.resource_failure(),
            source,
            import_span,
        })));
    }
    let surface = match project_module(&source, &tree).and_then(|mut surface| {
        let imports = header_imports?;
        if surface.imports != imports {
            return Err(ProjectionError::MalformedTree(
                crate::parser::InternalReason::UnexpectedShape,
            ));
        }
        surface.imports = imports;
        Ok(surface)
    }) {
        Ok(surface) => surface,
        Err(error) => {
            return Err(LoadGraphError::Projection {
                source,
                error,
                import_span,
            });
        }
    };
    Ok((source, surface, needs_generator_dependency))
}

fn resolve_import(
    module: &StagedModule,
    import: &SurfaceImport,
    roots: &ModuleRoots,
) -> Result<(PathBuf, ImportOwners, bool), LoadGraphError> {
    match &import.path {
        SurfaceModulePath::Relative(segments) => {
            let parent = module.canonical_path.parent().ok_or_else(|| {
                ModuleFailure::invalid_path(
                    import.span,
                    Some(module.canonical_path.clone()),
                    ModulePathCause::MissingParent,
                )
            })?;
            let candidate =
                target_path(parent, segments.iter().map(|segment| segment.text.as_str()))
                    .ok_or_else(|| {
                        ModuleFailure::invalid_path(
                            import.span,
                            None,
                            ModulePathCause::MissingSegments,
                        )
                    })?;
            let canonical = canonical_import_target(candidate, import.span)?;
            for owner in &module.owners.ordered {
                require_within_owner(&canonical, owner, import.span)?;
            }
            Ok((canonical, ImportOwners::Inherited(module.id), true))
        }
        SurfaceModulePath::Absolute { root, segments } => {
            let owner = roots
                .named
                .get(root.text.as_str())
                .ok_or_else(|| ModuleFailure::unknown_root(import.span, root.text.clone()))?;
            let candidate =
                target_path(owner, segments.iter().map(|segment| segment.text.as_str()))
                    .ok_or_else(|| {
                        ModuleFailure::invalid_path(
                            import.span,
                            None,
                            ModulePathCause::MissingSegments,
                        )
                    })?;
            let canonical = canonical_import_target(candidate, import.span)?;
            require_within_owner(&canonical, owner, import.span)?;
            Ok((canonical, ImportOwners::Absolute(owner.clone()), false))
        }
    }
}

fn admitted_owners(
    owners: ImportOwners,
    staged: &[StagedModule],
    budget: &mut GraphBudget,
) -> Result<OwnerSet, LoadGraphError> {
    match owners {
        ImportOwners::Inherited(module) => {
            OwnerSet::from_paths(&staged[module.index()].owners.ordered, budget)
        }
        ImportOwners::Absolute(owner) => OwnerSet::from_paths(std::slice::from_ref(&owner), budget),
    }
}

fn target_path<'a>(base: &Path, segments: impl IntoIterator<Item = &'a str>) -> Option<PathBuf> {
    let mut segments = segments.into_iter().peekable();
    let mut target = base.to_path_buf();
    let mut saw_segment = false;
    while let Some(segment) = segments.next() {
        saw_segment = true;
        target.push(segment);
        if segments.peek().is_none() {
            target.set_extension("ash");
        }
    }
    saw_segment.then_some(target)
}

fn canonical_import_target(
    candidate: PathBuf,
    import_span: Span,
) -> Result<PathBuf, LoadGraphError> {
    match fs::canonicalize(&candidate) {
        Ok(canonical) => Ok(canonical),
        Err(error) if error.kind() == io::ErrorKind::NotFound => {
            Err(ModuleFailure::source(ModuleReason::NotFound, import_span, Some(candidate)).into())
        }
        Err(error) => Err(LoadGraphError::Read {
            path: candidate,
            kind: error.kind(),
            import_span: Some(import_span),
        }),
    }
}

fn require_within_owner(
    canonical_target: &Path,
    owner: &Path,
    import_span: Span,
) -> Result<(), LoadGraphError> {
    if canonical_target.starts_with(owner) {
        return Ok(());
    }
    Err(ModuleFailure::source(
        ModuleReason::PathEscape,
        import_span,
        Some(canonical_target.to_path_buf()),
    )
    .into())
}

fn propagate_owners(
    start: ModuleId,
    owners: ImportOwners,
    causing_import: Span,
    staged: &mut [StagedModule],
    budget: &mut GraphBudget,
) -> Result<(), LoadGraphError> {
    struct Frame {
        module: ModuleId,
        owner: PathBuf,
        cause: Span,
        next_edge: usize,
        entered: bool,
    }

    let owner_paths = match &owners {
        ImportOwners::Inherited(module) => &staged[module.index()].owners.ordered,
        ImportOwners::Absolute(owner) => std::slice::from_ref(owner),
    };
    let mut pending = Vec::new();
    for owner in owner_paths.iter().rev() {
        budget.retain_pending_work()?;
        pending.push(Frame {
            module: start,
            owner: owner.clone(),
            cause: causing_import,
            next_edge: 0,
            entered: false,
        });
    }
    while !pending.is_empty() {
        let frame_index = pending.len() - 1;
        let module_index = pending[frame_index].module.index();
        if !pending[frame_index].entered {
            if staged[module_index]
                .owners
                .contains(&pending[frame_index].owner)
            {
                pending.pop();
                budget.release_pending_work();
                continue;
            }
            require_within_owner(
                &staged[module_index].canonical_path,
                &pending[frame_index].owner,
                pending[frame_index].cause,
            )?;
            staged[module_index]
                .owners
                .insert(&pending[frame_index].owner, budget)?;
            pending[frame_index].entered = true;
        }

        let Some(edge) = staged[module_index]
            .relative_edges
            .get(pending[frame_index].next_edge)
        else {
            pending.pop();
            budget.release_pending_work();
            continue;
        };
        require_within_owner(
            &edge.canonical_target,
            &pending[frame_index].owner,
            edge.import_span,
        )?;
        let child = Frame {
            module: edge.target,
            owner: pending[frame_index].owner.clone(),
            cause: edge.import_span,
            next_edge: 0,
            entered: false,
        };
        pending[frame_index].next_edge += 1;
        budget.retain_pending_work()?;
        pending.push(child);
    }
    Ok(())
}

fn import_segment_count(import: &SurfaceImport) -> usize {
    match &import.path {
        SurfaceModulePath::Relative(segments) => segments.len(),
        SurfaceModulePath::Absolute { segments, .. } => segments.len().saturating_add(1),
    }
}

fn is_lower_identifier(name: &str) -> bool {
    if is_reserved_word(name) {
        return false;
    }
    let mut bytes = name.bytes();
    let Some(first) = bytes.next() else {
        return false;
    };
    (first == b'_' || first.is_ascii_lowercase())
        && bytes.all(|byte| byte == b'_' || byte.is_ascii_alphanumeric())
}

fn is_reserved_word(name: &str) -> bool {
    matches!(
        name,
        "true"
            | "false"
            | "fn"
            | "let"
            | "rec"
            | "and"
            | "type"
            | "match"
            | "import"
            | "syntax"
            | "as"
            | "pub"
            | "opaque"
            | "interface"
            | "impl"
            | "where"
            | "resource"
            | "_"
            | "Int"
            | "Bool"
            | "Unit"
    )
}

#[cfg(test)]
mod tests {
    use crate::parser::parse_with_budget;

    use super::*;

    fn h1_staged_fixture(text: &str) -> (HeaderGraph, crate::syntax::SelectedSyntax) {
        let definition = SourceFile::new(
            "definition.ash",
            "pub syntax declaration: (make) $name:ident => {\n$name : Unit -> Int\n$name () = 42\n}\n",
        ).unwrap();
        let declaration = crate::parser::project_module_retaining_templates(
            &definition,
            &crate::parser::parse(crate::lexer::lex(&definition).unwrap()),
        )
        .unwrap()
        .syntax_declarations
        .remove(0);
        let selected = crate::syntax::SelectedSyntax {
            name: "make".into(),
            owner: 0,
            import_span: declaration.span,
            declaration,
        };
        let source = SourceFile::new("caller.ash", text).unwrap();
        let mut budget = SyntaxBudget::default();
        let lexed = lex_with_budget(&source, &mut budget).unwrap();
        let (tokens, diagnostics, _, resource) = lexed.into_parts();
        assert!(resource.is_none());
        let (checkpoint, budget) = parse_module_header(tokens, diagnostics, budget);
        let imports = project_module_header(&source, &checkpoint).unwrap();
        let span = module_span_from_checkpoint(&source, &checkpoint).unwrap();
        let entry = ModuleId::new(0);
        let staged = StagedModule {
            id: entry,
            canonical_path: PathBuf::from("caller.ash"),
            owners: OwnerSet {
                ordered: Vec::new(),
                membership: HashSet::new(),
            },
            source,
            surface: StagedSyntax {
                imports,
                span,
                body: ModuleBody::Header(checkpoint),
                import_span: None,
                needs_quote_dependency: false,
                needs_generator_dependency: false,
            },
            dependencies: Vec::new(),
            relative_edges: Vec::new(),
            state: VisitState::Finished,
        };
        (
            HeaderGraph {
                pending: VecDeque::from([staged]),
                loaded: Vec::new(),
                completed: None,
                entry,
                syntax_budget: budget,
                next_quote_ordinal: 0,
            },
            selected,
        )
    }

    #[test]
    fn current_module_borrows_the_same_syntax_ledger_before_and_after_completion() {
        let (mut graph, selected) = h1_staged_fixture("make good\n");
        assert!(graph.current_module_with_syntax_budget().is_none());
        graph
            .next_module_with_syntax(&[selected], &[], &mut Vec::new(), None)
            .unwrap()
            .unwrap();
        let consumed = graph.syntax_budget.consumed();
        let loaded_id = {
            let (module, budget, ordinal) = graph.current_module_with_syntax_budget().unwrap();
            budget.charge_units(7).unwrap();
            *ordinal = 11;
            module.id()
        };
        assert_eq!(graph.syntax_budget.consumed(), consumed + 7);
        assert_eq!(graph.next_quote_ordinal, 11);
        assert!(graph.completed_graph().is_some());
        let (module, budget, ordinal) = graph.current_module_with_syntax_budget().unwrap();
        assert_eq!(module.id(), loaded_id);
        assert_eq!(budget.consumed(), consumed + 7);
        assert_eq!(*ordinal, 11);
        *ordinal += 1;
        budget.charge().unwrap();
        assert_eq!(graph.syntax_budget.consumed(), consumed + 8);
        assert_eq!(graph.next_quote_ordinal, 12);
    }

    #[test]
    fn h1_late_output_failure_never_reaches_the_loaded_module_boundary() {
        let (mut graph, selected) = h1_staged_fixture("make good\nmake Upper\n");
        let mut owners = Vec::new();
        assert!(
            graph
                .next_module_with_syntax(&[selected], &[], &mut owners, None)
                .is_err()
        );
        assert!(graph.loaded.is_empty());
        assert!(graph.current_module().is_none());
        assert!(graph.completed.is_none());
        assert!(owners.is_empty());
    }

    #[test]
    fn h1_header_consistency_failure_keeps_preexisting_owners_unchanged() {
        let (mut graph, selected) = h1_staged_fixture("make good\n");
        let staged = graph.pending.front_mut().unwrap();
        staged.surface.span = staged
            .source
            .span(crate::source::ByteRange::new(0, 0).unwrap())
            .unwrap();
        let previous = crate::syntax::SyntaxOwner {
            caller_quote_owner: None,
            owner: Some(9),
            declaration: selected.declaration.span,
            import_span: selected.import_span,
        };
        let mut owners = vec![previous.clone()];
        let error = graph
            .next_module_with_syntax(&[selected], &[], &mut owners, None)
            .unwrap_err();
        assert!(matches!(
            error.failure(),
            LoadGraphError::Projection {
                error: ProjectionError::MalformedTree(crate::parser::InternalReason::InvalidSpan),
                ..
            }
        ));
        assert!(graph.loaded.is_empty());
        assert!(graph.current_module().is_none());
        assert!(graph.completed.is_none());
        assert_eq!(owners.len(), 1);
        assert_eq!(owners[0].owner, previous.owner);
        assert_eq!(owners[0].declaration, previous.declaration);
        assert_eq!(owners[0].import_span, previous.import_span);
    }

    #[test]
    fn common_foreign_identity_and_admission_remain_distinct_and_retryable() {
        let fixture = ModuleId::builtin_foreign_for_test(7);
        assert!(fixture.is_builtin_foreign());
        assert_eq!(fixture.to_string(), "builtin.foreign:0:7");
        assert_ne!(fixture, ModuleId::new(7));
        let source = SourceFile::new("importer", "import @builtin.foreign as Foreign\n").unwrap();
        let span = source
            .span(crate::source::ByteRange::new(0, 1).unwrap())
            .unwrap();
        for allowance in [0, 1, 1] {
            let mut budget = GraphBudget::with_limits(GraphLimits {
                sources: allowance,
                ..GraphLimits::default()
            });
            let mut staged = Vec::new();
            let mut order = Vec::new();
            let result = admit_builtin_foreign(17, span, &mut budget, &mut staged, &mut order);
            if allowance == 0 {
                assert_resource(result.map(|_| ()), ModuleResource::Sources);
                assert!(staged.is_empty() && order.is_empty());
            } else {
                let id = result.unwrap();
                assert!(id.is_builtin_foreign());
                assert_eq!(id.to_string(), "builtin.foreign:17:0");
                assert_eq!(order, [id]);
                assert_ne!(id, ModuleId::from(staged[0].source.id()));
                assert_ne!(id, ModuleId::admitted(17, 0));
                assert_eq!(staged[0].source.text(), FOREIGN_SOURCE);
                assert_eq!(staged[0].surface.span.range().start(), 0);
                assert_eq!(
                    staged[0].surface.span.range().end() as usize,
                    FOREIGN_SOURCE.len()
                );
                assert!(staged[0].dependencies.is_empty() && staged[0].relative_edges.is_empty());
                assert_eq!(budget.owner_facts, 0);
            }
        }
    }

    #[test]
    fn generic_cell_image_role_allocates_a_fresh_identity_with_paid_retry() {
        let source = SourceFile::new("@builtin.generic_cell", GENERIC_CELL_SOURCE).unwrap();
        let required = 2;
        let mut short = crate::types::TypeWorkBudget::with_limit(required - 1);
        assert!(
            restore_image_module(&source, ImageModuleRole::BuiltinGenericCell, &mut short).is_err()
        );
        let mut previous = None;
        for _ in 0..2 {
            let mut exact = crate::types::TypeWorkBudget::with_limit(required);
            let module =
                restore_image_module(&source, ImageModuleRole::BuiltinGenericCell, &mut exact)
                    .unwrap();
            assert!(module.is_builtin_generic_cell());
            assert_eq!(exact.used(), required);
            assert_ne!(Some(module), previous);
            previous = Some(module);
        }
    }

    #[test]
    fn builtin_admission_charges_sources_before_publishing_and_retries() {
        let source = SourceFile::new("importer", "import @builtin.cell as Cell\n").unwrap();
        let span = source
            .span(crate::source::ByteRange::new(0, 1).unwrap())
            .unwrap();
        for allowance in [0, 1, 1] {
            let mut budget = GraphBudget::with_limits(GraphLimits {
                sources: allowance,
                ..GraphLimits::default()
            });
            let mut staged = Vec::new();
            let mut order = Vec::new();
            let result =
                admit_builtin_resource(false, 17, span, &mut budget, &mut staged, &mut order);
            if allowance == 0 {
                assert_resource(result.map(|_| ()), ModuleResource::Sources);
                assert!(staged.is_empty() && order.is_empty());
            } else {
                let id = result.unwrap();
                assert_eq!(order, [id]);
                assert!(id.is_builtin_cell());
                assert_ne!(id, ModuleId::from(staged[0].source.id()));
                assert_ne!(id, ModuleId::admitted(17, 0));
                assert!(staged[0].dependencies.is_empty() && staged[0].relative_edges.is_empty());
                assert_eq!(budget.owner_facts, 0);
            }
        }
    }

    #[test]
    fn builtin_and_resource_syntax_accept_exact_work_and_retry_after_one_short() {
        for text in [
            CELL_SOURCE,
            FOREIGN_SOURCE,
            "main : Unit -> Int\nmain () = resource cell<R> c = (1 + 2) {\n42\n}\n",
        ] {
            let path = Path::new("syntax-boundary");
            let accepts = |limit| {
                parse_surface_module(
                    path,
                    text.to_owned(),
                    None,
                    &mut SyntaxBudget::with_limit(limit),
                )
                .is_ok()
            };
            let (mut low, mut high) = (0, 10_000);
            assert!(accepts(high));
            while low + 1 < high {
                let middle = (low + high) / 2;
                if accepts(middle) {
                    high = middle;
                } else {
                    low = middle;
                }
            }
            for _ in 0..2 {
                assert!(!accepts(high - 1));
                assert!(accepts(high));
            }
        }
    }

    #[test]
    fn graph_lookup_uses_identity_after_dependency_ordering() {
        let first = ModuleId::new(0);
        let second = ModuleId::new(1);
        let graph = ModuleGraph {
            modules: vec![
                loaded_module_for_lookup(second, "second"),
                loaded_module_for_lookup(first, "first"),
            ]
            .into_boxed_slice(),
            entry: first,
        };

        assert_eq!(graph.module(first).map(LoadedModule::id), Some(first));
        assert_eq!(graph.module(second).map(LoadedModule::id), Some(second));
    }

    #[test]
    fn direct_core_source_identity_cannot_collide_with_admitted_module() {
        let source = SourceFile::new("direct-core", "x").expect("test source");

        assert_ne!(
            ModuleId::from(source.id()),
            ModuleId::new(source.id().value())
        );
    }

    #[test]
    fn graph_budgets_accept_exact_boundaries_and_reject_the_next_unit() {
        let mut budget = GraphBudget::with_limits(GraphLimits {
            sources: 1,
            edges: 1,
            path_segments: 2,
            owner_facts: 1,
            pending_work: 1,
        });

        assert!(budget.charge_sources().is_ok());
        assert_resource(budget.charge_sources(), ModuleResource::Sources);
        assert!(budget.charge_edge().is_ok());
        assert_resource(budget.charge_edge(), ModuleResource::Edges);
        assert!(budget.charge_path_segments(2).is_ok());
        assert_resource(budget.charge_path_segments(1), ModuleResource::PathSegments);
        assert!(budget.charge_owner_facts(1).is_ok());
        assert_resource(budget.charge_owner_facts(1), ModuleResource::OwnerFacts);
        assert!(budget.retain_pending_work().is_ok());
        assert_resource(budget.retain_pending_work(), ModuleResource::PendingWork);
        budget.release_pending_work();
        assert!(budget.retain_pending_work().is_ok());
    }

    #[test]
    fn owner_facts_are_charged_before_initial_and_propagated_retention() {
        let first = PathBuf::from("first");
        let second = PathBuf::from("second");
        let mut budget = GraphBudget::with_limits(GraphLimits {
            sources: 1,
            edges: 1,
            path_segments: 1,
            owner_facts: 1,
            pending_work: 1,
        });

        let mut owners = OwnerSet::from_paths(std::slice::from_ref(&first), &mut budget)
            .expect("the exact initial owner allowance should fit");
        assert_resource(
            owners.insert(&second, &mut budget),
            ModuleResource::OwnerFacts,
        );
        assert!(!owners.contains(&second));
    }

    #[test]
    fn one_syntax_budget_spans_all_admitted_module_sources() {
        let first = SourceFile::new("first.ash", "").expect("first source");
        let second = SourceFile::new("second.ash", "").expect("second source");
        let mut budget = SyntaxBudget::with_limit(6);

        let first = parse_with_budget(
            lex_with_budget(&first, &mut budget).expect("first source should lex"),
            &mut budget,
        );
        assert_eq!(first.resource_failure(), None);

        let second = parse_with_budget(
            lex_with_budget(&second, &mut budget).expect("second source should lex"),
            &mut budget,
        );
        assert_eq!(
            second.resource_failure(),
            Some(ResourceFailure::SyntaxWork { limit: 6 })
        );
    }

    fn assert_resource(result: Result<(), LoadGraphError>, expected: ModuleResource) {
        let Err(LoadGraphError::Module(failure)) = result else {
            panic!("the budget should report a module resource failure");
        };
        assert_eq!(failure.reason(), ModuleReason::ResourceLimit);
        assert_eq!(failure.resource_kind(), Some(expected));
        assert!(!failure.is_source_rejection());
    }

    #[test]
    fn caller_quote_name_authenticates_completed_module_and_keeps_lexical_precedence() {
        use crate::{
            interface::InterfaceConstraintBudget,
            resolve::{ResolveModuleError, ResolveReason, resolve_module_with_syntax},
            resolved::{
                ResolvedDefinitionKind, ResolvedExprKind, ResolvedLocalDeclaration,
                ResolvedPatternKind,
            },
            surface::{
                SurfaceDefinitionKind, SurfaceExprKind, SurfaceLocalDeclaration,
                SurfacePatternKind, SurfaceReference,
            },
            syntax::{CallerQuoteOwner, SyntaxExpansion, SyntaxOwner},
            types::TypeWorkBudget,
        };
        use std::{cell::RefCell, sync::Arc};

        #[derive(Clone, Copy)]
        enum Case {
            Valid,
            Local,
            WrongModule,
            CopiedSource,
            SwappedRecord,
            Missing,
            Clone,
            Adapter,
        }

        let run = |case: Case, limit: usize| {
            let source = Arc::new(SourceFile::new(
                "caller-quote-auth.ash",
                "value : Unit -> Int\nvalue () = 42\nmain : Unit -> Int\nmain () = {\n    let value = 99\n    value\n}\n",
            ).unwrap());
            let tree = crate::parser::parse(crate::lexer::lex(&source).unwrap());
            let mut surface = crate::parser::project_module(&source, &tree).unwrap();
            let span = surface.span;
            let main = surface
                .definitions
                .iter_mut()
                .find_map(|definition| match &mut definition.kind {
                    SurfaceDefinitionKind::Equational(global)
                        if global.interface.name.text == "main" =>
                    {
                        Some(global)
                    }
                    _ => None,
                })
                .unwrap();
            let SurfaceExprKind::Block(block) = &mut main.equations[0].body.kind else {
                panic!("main block")
            };
            let SurfaceExprKind::Name(SurfaceReference::Unqualified(reference)) =
                &mut block.result.kind
            else {
                panic!("block reference")
            };
            reference.introduction = 1;
            reference.introduced_at = Some(span);
            reference.written = false;
            if matches!(case, Case::Local) {
                let [SurfaceLocalDeclaration::Binding(binding)] = block.declarations.as_mut_slice()
                else {
                    panic!("local binding")
                };
                let SurfacePatternKind::Binder(binder) = &mut binding.pattern.kind else {
                    panic!("local binder")
                };
                binder.name.introduction = 1;
                binder.name.introduced_at = Some(span);
                binder.name.written = false;
            }
            let id = ModuleId::new(90_399);
            let owner = Arc::new(CallerQuoteOwner {
                module: if matches!(case, Case::WrongModule) {
                    ModuleId::new(90_400)
                } else {
                    id
                },
                source: if matches!(case, Case::CopiedSource) {
                    Arc::new(source.as_ref().clone())
                } else {
                    Arc::clone(&source)
                },
                selected: Arc::from([]),
            });
            let completed = if matches!(case, Case::SwappedRecord) {
                Arc::new(CallerQuoteOwner {
                    module: id,
                    source: Arc::clone(&source),
                    selected: Arc::from([]),
                })
            } else {
                Arc::clone(&owner)
            };
            let mut loaded = LoadedModule {
                id,
                canonical_path: PathBuf::from("caller-quote-auth.ash"),
                source: Arc::clone(&source),
                surface,
                dependencies: Box::new([]),
                quote_sites: Vec::new(),
                quote_introduction: None,
                caller_quote_owner: (!matches!(case, Case::Missing)).then_some(completed),
            };
            if matches!(case, Case::Clone) {
                loaded = loaded.clone();
            }
            if matches!(case, Case::Adapter) {
                let source_slot = RefCell::new(Some(Arc::clone(&source)));
                let owner_slot = RefCell::new(Some(Arc::clone(&owner)));
                let loan = StagedModuleLoan {
                    id,
                    source_id: source.id(),
                    canonical_path: &loaded.canonical_path,
                    imports: &loaded.surface.imports,
                    dependencies: &loaded.dependencies,
                    span,
                    source_snapshot: &source_slot,
                    caller_quote_owner: &owner_slot,
                    quote_projection: None,
                };
                let definition = loaded.surface.definitions.iter().find(|definition| matches!(&definition.kind,
                    SurfaceDefinitionKind::Equational(global) if global.interface.name.text == "main")).unwrap().clone();
                loaded = loan
                    .no_quote_adapter_view(&source, definition, &mut SyntaxBudget::default())
                    .unwrap();
                assert!(Arc::ptr_eq(loaded.retained_source(), &owner.source));
            }
            let mut transformer =
                |_: &crate::syntax::SelectedSyntax,
                 _: &[crate::surface::SurfaceSyntaxCapture],
                 span: Span,
                 _: &crate::surface::SurfaceName,
                 _: usize,
                 _: &[Option<usize>],
                 _: &Arc<crate::syntax::ExpansionFrame>,
                 _: &mut InterfaceConstraintBudget,
                 _: Option<crate::syntax::QuoteExpansionLoan<'_>>|
                 -> Result<(crate::syntax::ExpandedExpression, usize), Span> {
                    Err(span)
                };
            let mut expansion = SyntaxExpansion::new(
                loaded.source(),
                &[],
                &[],
                vec![SyntaxOwner {
                    owner: None,
                    caller_quote_owner: Some(owner),
                    declaration: span,
                    import_span: span,
                }],
                None,
                None,
                &mut transformer,
            );
            let mut work = TypeWorkBudget::with_limit(limit);
            let result = resolve_module_with_syntax(
                &loaded,
                &[],
                &mut work,
                &mut InterfaceConstraintBudget::with_limit(usize::MAX),
                &[],
                &[],
                &[],
                Some(&mut expansion),
            );
            (result, work.used())
        };

        let (resolved, exact) = run(Case::Valid, usize::MAX);
        let resolved = resolved.expect("authenticated current caller resolves");
        let global = resolved
            .definitions()
            .iter()
            .find_map(|definition| match &definition.kind {
                ResolvedDefinitionKind::Equational(global)
                    if global.interface.name.spelling == "value" =>
                {
                    Some(global.interface.name.id)
                }
                _ => None,
            })
            .unwrap();
        let main = resolved
            .definitions()
            .iter()
            .find_map(|definition| match &definition.kind {
                ResolvedDefinitionKind::Equational(global)
                    if global.interface.name.spelling == "main" =>
                {
                    Some(global)
                }
                _ => None,
            })
            .unwrap();
        let ResolvedExprKind::Block(block) = &main.equations[0].body.kind else {
            panic!("resolved main block")
        };
        let [ResolvedLocalDeclaration::Binding(binding)] = block.declarations.as_slice() else {
            panic!("resolved local")
        };
        let ResolvedPatternKind::Binder(local) = &binding.pattern.kind else {
            panic!("resolved binder")
        };
        let ResolvedExprKind::Occurrence(reference) = &block.result.kind else {
            panic!("resolved reference")
        };
        assert_eq!(reference.global_binder(), Some(global));
        assert_ne!(reference.global_binder(), Some(local.id));
        let (local, _) = run(Case::Local, usize::MAX);
        let local = local.unwrap();
        let main = local
            .definitions()
            .iter()
            .find_map(|definition| match &definition.kind {
                ResolvedDefinitionKind::Equational(global)
                    if global.interface.name.spelling == "main" =>
                {
                    Some(global)
                }
                _ => None,
            })
            .unwrap();
        let ResolvedExprKind::Block(block) = &main.equations[0].body.kind else {
            panic!("resolved main block")
        };
        let [ResolvedLocalDeclaration::Binding(binding)] = block.declarations.as_slice() else {
            panic!("resolved local")
        };
        let ResolvedPatternKind::Binder(local) = &binding.pattern.kind else {
            panic!("resolved binder")
        };
        let ResolvedExprKind::Occurrence(reference) = &block.result.kind else {
            panic!("resolved reference")
        };
        assert_eq!(reference.global_binder(), Some(local.id));

        for case in [
            Case::WrongModule,
            Case::CopiedSource,
            Case::SwappedRecord,
            Case::Missing,
            Case::Clone,
            Case::Adapter,
        ] {
            let (result, _) = run(case, usize::MAX);
            assert!(
                matches!(result, Err(ResolveModuleError::Resolution(error)) if error.reason == ResolveReason::InternalState)
            );
        }
        assert!(matches!(run(Case::Valid, exact - 1).0,
            Err(ResolveModuleError::Resolution(error)) if error.reason == ResolveReason::TypeResourceExhausted));
        for _ in 0..2 {
            let (result, used) = run(Case::Valid, exact);
            result.expect("fresh exact retry resolves");
            assert_eq!(used, exact);
        }
    }

    #[test]
    fn caller_quote_interface_lookup_pays_reached_type_scopes() {
        use crate::{
            interface::InterfaceConstraintBudget,
            resolve::{ResolveModuleError, ResolveReason, resolve_module_with_syntax},
            surface::{
                SurfaceDefinitionKind, SurfaceExprKind, SurfaceLocalDeclaration, SurfaceReference,
            },
            syntax::{CallerQuoteOwner, SyntaxExpansion, SyntaxOwner},
            types::TypeWorkBudget,
        };
        use std::sync::Arc;

        let run = |depth: usize,
                   reference_introduction: usize,
                   binder_introduction: usize,
                   limit: usize,
                   spent: usize| {
            let mut text = String::from("main : Unit -> Int\nmain () = region<A> outer {\n");
            for (name, handle) in [("B", "inner_b"), ("C", "inner_c"), ("D", "inner_d")]
                .iter()
                .take(depth)
            {
                text.push_str(&format!("region<{name}> {handle} {{\n"));
            }
            text.push_str("with A<Int> {\nunused value = value\n}\n42\n");
            for _ in 0..=depth {
                text.push_str("}\n");
            }
            let source =
                Arc::new(SourceFile::new("caller-quote-interface-budget.ash", &text).unwrap());
            let tree = crate::parser::parse(crate::lexer::lex(&source).unwrap());
            let mut surface = crate::parser::project_module(&source, &tree).unwrap();
            let span = surface.span;
            let SurfaceDefinitionKind::Equational(main) = &mut surface.definitions[0].kind else {
                panic!("equational main")
            };
            let SurfaceExprKind::Region(outer) = &mut main.equations[0].body.kind else {
                panic!("outer region")
            };
            outer.identity.introduction = binder_introduction;
            if binder_introduction != 0 {
                outer.identity.introduced_at = Some(span);
                outer.identity.written = false;
            }
            let mut body = &mut outer.body;
            for _ in 0..depth {
                let SurfaceExprKind::Region(inner) = &mut body.result.kind else {
                    panic!("inner region")
                };
                body = &mut inner.body;
            }
            let [SurfaceLocalDeclaration::Evidence(evidence)] = body.declarations.as_mut_slice()
            else {
                panic!("lexical evidence")
            };
            let SurfaceReference::Unqualified(member) = &mut evidence.application.interface else {
                panic!("unqualified interface")
            };
            member.introduction = reference_introduction;
            if reference_introduction != 0 {
                member.introduced_at = Some(span);
                member.written = false;
            }
            let id = ModuleId::new(90_402);
            let owner = Arc::new(CallerQuoteOwner {
                module: id,
                source: Arc::clone(&source),
                selected: Arc::from([]),
            });
            let loaded = LoadedModule {
                id,
                canonical_path: PathBuf::from("caller-quote-interface-budget.ash"),
                source: Arc::clone(&source),
                surface,
                dependencies: Box::new([]),
                quote_sites: Vec::new(),
                quote_introduction: None,
                caller_quote_owner: Some(Arc::clone(&owner)),
            };
            let mut transformer =
                |_: &crate::syntax::SelectedSyntax,
                 _: &[crate::surface::SurfaceSyntaxCapture],
                 span: Span,
                 _: &crate::surface::SurfaceName,
                 _: usize,
                 _: &[Option<usize>],
                 _: &Arc<crate::syntax::ExpansionFrame>,
                 _: &mut InterfaceConstraintBudget,
                 _: Option<crate::syntax::QuoteExpansionLoan<'_>>|
                 -> Result<(crate::syntax::ExpandedExpression, usize), Span> {
                    Err(span)
                };
            let mut expansion = SyntaxExpansion::new(
                loaded.source(),
                &[],
                &[],
                vec![SyntaxOwner {
                    owner: None,
                    caller_quote_owner: Some(owner),
                    declaration: span,
                    import_span: span,
                }],
                None,
                None,
                &mut transformer,
            );
            let mut work = TypeWorkBudget::with_limit(limit);
            work.charge(spent).unwrap();
            let result = resolve_module_with_syntax(
                &loaded,
                &[],
                &mut work,
                &mut InterfaceConstraintBudget::with_limit(usize::MAX),
                &[],
                &[],
                &[],
                Some(&mut expansion),
            );
            let Err(ResolveModuleError::Resolution(error)) = result else {
                panic!("the fixture reaches the interface lookup")
            };
            (
                error.reason,
                error.diagnostic().primary.message().to_owned(),
                work.used(),
            )
        };

        for depth in 0..=3 {
            let (ordinary, _, ordinary_work) = run(depth, 0, 0, usize::MAX, 0);
            assert_eq!(ordinary, ResolveReason::InterfaceKind);
            let (introduced, _, exact) = run(depth, 1, 1, usize::MAX, 0);
            assert_eq!(introduced, ResolveReason::InterfaceKind);
            // Retaining the introduced region's Expansion origin costs two;
            // owner authentication costs three, the key copy one byte, and
            // each reached scope costs a hash, comparison, and visit.
            assert_eq!(exact - ordinary_work, 2 + 3 + 1 + 3 * (depth + 1));
            assert_eq!(
                run(depth, 1, 2, usize::MAX, 0).0,
                ResolveReason::UnknownInterface
            );
            for spent in [0, 17] {
                let (reason, message, _) = run(depth, 1, 1, exact + spent - 1, spent);
                assert_eq!(reason, ResolveReason::TypeResourceExhausted);
                assert_eq!(
                    message,
                    "caller quote interface type-scope lookup exceeded its type-work budget"
                );
                for _ in 0..2 {
                    let (reason, _, used) = run(depth, 1, 1, exact + spent, spent);
                    assert_eq!(reason, ResolveReason::InterfaceKind);
                    assert_eq!(used, exact + spent);
                }
            }
        }
    }

    #[test]
    fn completed_caller_record_releases_its_source_before_extraction() {
        use std::sync::Arc;
        for external in [false, true] {
            let mut module = loaded_module_for_lookup(ModuleId::new(90_401), "source-move.ash");
            let original_pointer = module.source.text().as_ptr();
            module.caller_quote_owner = Some(Arc::new(crate::syntax::CallerQuoteOwner {
                module: module.id,
                source: Arc::clone(&module.source),
                selected: Arc::from([]),
            }));
            let clone = module.clone();
            assert!(clone.caller_quote_owner.is_none());
            drop(clone);
            let outside = external.then(|| Arc::clone(module.caller_quote_owner.as_ref().unwrap()));
            let weak = Arc::downgrade(module.caller_quote_owner.as_ref().unwrap());
            let source = module.into_source();
            assert_eq!(source.text().as_ptr() == original_pointer, !external);
            assert_eq!(weak.upgrade().is_some(), external);
            drop(outside);
            assert!(weak.upgrade().is_none());
        }
    }

    fn loaded_module_for_lookup(id: ModuleId, name: &str) -> LoadedModule {
        let source = SourceFile::new(name, "main : Unit -> Unit\nmain value = value\n")
            .expect("test module source");
        let span = source
            .span(crate::source::ByteRange::new(0, 1).expect("ordered test range"))
            .expect("test span belongs to source");
        LoadedModule {
            id,
            canonical_path: PathBuf::from(name),
            source: std::sync::Arc::new(source),
            surface: SurfaceModule {
                imports: Vec::new(),
                syntax_declarations: Vec::new(),
                declaration_order: Vec::new(),
                type_declarations: Vec::new(),
                interfaces: Vec::new(),
                effects: Vec::new(),
                implementations: Vec::new(),
                definitions: Vec::new(),
                resources: Vec::new(),

                foreign_libraries: Vec::new(),
                span,
            },
            dependencies: Box::new([]),
            quote_sites: Vec::new(),
            quote_introduction: None,
            caller_quote_owner: None,
        }
    }
}

/// Host-selected identity of one immutable foreign registration manifest.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ForeignRegistrationId(u64);

/// Immutable admission metadata for a registered module with an ordinary ModuleId.
///
/// Retained only for declarations loaded from the immutable host registration table.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ForeignModuleAdmission {
    /// Ordinary admitted module identity, with no library-specific namespace.
    pub module_id: ModuleId,
    /// Immutable host registry entry.

    /// Digest of the admitted manifest.
    pub manifest_digest: [u8; 32],
    /// Manifest admission provenance.
    pub origin: crate::source::Origin,
}

/// Controlled roles attached to authenticated foreign operation identities.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ForeignOperationRole {
    /// Produces guarded unpublished state in an acquire template.
    Acquire,
    /// Uses live state without transferring native ownership.
    Borrow,
    /// Consumes or retains ownership under a finish capability.
    Finish,
}

// Compiler-private role reconstruction. Put beside module graph identity
// allocation; the image retains this enum separately from its source pathname.
#[derive(Clone, Copy, Debug)]
pub(crate) enum ImageModuleRole {
    Ordinary,
    BuiltinRegion,
    BuiltinRegionFacade,
    BuiltinForeign,
    BuiltinCell,
    BuiltinGenericCell,
    BuiltinRetainedControl,
    BuiltinNetwork,
    BuiltinString,
    BuiltinBytes,
    BuiltinInteger,
    BuiltinCompilerSyntax,
}

#[derive(Clone, Copy, Debug)]
pub(crate) enum ImageModuleFailure {
    Resource,
}

pub(crate) fn restore_image_module(
    source: &SourceFile,
    role: ImageModuleRole,
    work: &mut crate::types::TypeWorkBudget,
) -> Result<ModuleId, ImageModuleFailure> {
    work.charge(1).map_err(|()| ImageModuleFailure::Resource)?;
    let namespace = match role {
        ImageModuleRole::Ordinary => return Ok(ModuleId::from(source.id())),
        ImageModuleRole::BuiltinRegion => ModuleIdNamespace::BuiltinRegion,
        ImageModuleRole::BuiltinRegionFacade => ModuleIdNamespace::BuiltinRegionFacade,
        ImageModuleRole::BuiltinForeign => ModuleIdNamespace::BuiltinForeign,
        ImageModuleRole::BuiltinGenericCell => ModuleIdNamespace::BuiltinGenericCell,
        ImageModuleRole::BuiltinRetainedControl => ModuleIdNamespace::BuiltinRetainedControl,
        ImageModuleRole::BuiltinNetwork => ModuleIdNamespace::BuiltinNetwork,
        ImageModuleRole::BuiltinCell => ModuleIdNamespace::BuiltinCell,
        ImageModuleRole::BuiltinString => ModuleIdNamespace::BuiltinString,
        ImageModuleRole::BuiltinBytes => ModuleIdNamespace::BuiltinBytes,
        ImageModuleRole::BuiltinInteger => ModuleIdNamespace::BuiltinInteger,
        ImageModuleRole::BuiltinCompilerSyntax => ModuleIdNamespace::BuiltinCompilerSyntax,
    };
    work.charge(1).map_err(|()| ImageModuleFailure::Resource)?;
    let graph = allocate_module_graph_identity().map_err(|_| ImageModuleFailure::Resource)?;
    Ok(ModuleId {
        namespace,
        graph,
        value: source.id().value(),
    })
}

pub(crate) fn compiler_syntax_builtin_source_text() -> &'static str {
    COMPILER_SYNTAX_SOURCE
}

pub(crate) fn foreign_builtin_source_text() -> &'static str {
    FOREIGN_SOURCE
}

pub(crate) fn retained_control_builtin_source_text() -> &'static str {
    RETAINED_CONTROL_SOURCE
}

pub(crate) fn network_builtin_source_text() -> &'static str {
    NETWORK_SOURCE
}

pub(crate) fn region_facade_builtin_source_text() -> &'static str {
    REGION_FACADE_SOURCE
}

pub(crate) fn region_builtin_source_text() -> &'static str {
    REGION_SOURCE
}
