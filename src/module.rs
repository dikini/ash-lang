//! Canonical source loading for passive module graphs.

use std::{
    borrow::Borrow,
    collections::{HashMap, HashSet},
    error::Error,
    fmt, fs, io,
    path::{Path, PathBuf},
    sync::atomic::{AtomicU32, Ordering},
};

use crate::{
    diagnostic::Diagnostic,
    lexer::{LexReason, lex_with_budget},
    parser::{
        ParseDiagnostic, ProjectionError, ResourceFailure, parse_with_budget, project_module,
    },
    source::{SourceError, SourceFile, SourceId, Span},
    surface::{SurfaceImport, SurfaceModule, SurfaceModulePath},
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

const CELL_SOURCE: &str = concat!(
    "pub opaque type Handle<R> = Hidden\n",
    "pub effect Ops<R> {\nread : Handle<R> -> Int\nwrite : (Handle<R>, Int) -> Unit\n}\n",
    "pub interface Provider<R> {\nread : Handle<R> -> Int ! {Ops<R>}\nwrite : (Handle<R>, Int) -> Unit ! {Ops<R>}\n}\n",
);

const NATIVE_BUFFER_SOURCE: &str = concat!(
    "pub opaque type Handle<R> = Hidden\n",
    "pub type Outcome<T> = Success(T)\n| Failure(Error)\n",
    "pub type Error = InvalidLength\n| AllocationFailed\n| InvalidIndex\n| InvalidByte\n",
    "pub effect Ops<R> {\nlength : Handle<R> -> Int\nread : (Handle<R>, Int) -> Outcome<Int>\nwrite : (Handle<R>, Int, Int) -> Outcome<Unit>\n}\n",
    "pub interface Provider<R> {\nlength : Handle<R> -> Int ! {Ops<R>}\nread : (Handle<R>, Int) -> Outcome<Int> ! {Ops<R>}\nwrite : (Handle<R>, Int, Int) -> Outcome<Unit> ! {Ops<R>}\n}\n",
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
    foreign: crate::foreign::ForeignRegistrations,
}

impl ModuleRoots {
    /// Creates an empty named-root configuration.
    #[must_use]
    pub fn empty() -> Self {
        Self::default()
    }

    /// Attaches an immutable host-authored registration table.
    #[must_use]
    pub fn with_foreign_registrations(
        mut self,
        foreign: crate::foreign::ForeignRegistrations,
    ) -> Self {
        self.foreign = foreign;
        self
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
        Ok(Self {
            named,
            foreign: crate::foreign::ForeignRegistrations::default(),
        })
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
    BuiltinNativeBuffer,
    DirectCoreSource,
}

impl ModuleId {
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

    pub(crate) const fn is_builtin_cell(self) -> bool {
        matches!(self.namespace, ModuleIdNamespace::BuiltinCell)
    }

    pub(crate) const fn is_builtin_native_buffer(self) -> bool {
        matches!(self.namespace, ModuleIdNamespace::BuiltinNativeBuffer)
    }

    pub(crate) const fn is_builtin_resource(self) -> bool {
        self.is_builtin_cell() || self.is_builtin_native_buffer()
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
            ModuleIdNamespace::Admitted => write!(formatter, "{}:{}", self.graph, self.value),
            ModuleIdNamespace::BuiltinCell => {
                write!(formatter, "builtin.cell:{}:{}", self.graph, self.value)
            }
            ModuleIdNamespace::DirectCoreSource => write!(formatter, "source:{}", self.value),
            ModuleIdNamespace::BuiltinNativeBuffer => write!(
                formatter,
                "builtin.native_buffer:{}:{}",
                self.graph, self.value
            ),
        }
    }
}

/// One source import edge to an admitted canonical module.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ModuleDependency {
    target: ModuleId,
    import_span: Span,
}

impl ModuleDependency {
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
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct LoadedModule {
    id: ModuleId,
    canonical_path: PathBuf,
    source: std::sync::Arc<SourceFile>,
    surface: SurfaceModule,
    dependencies: Box<[ModuleDependency]>,
    foreign: Option<crate::foreign::ForeignModuleSource>,
}

impl LoadedModule {
    /// Returns authenticated foreign admission metadata, when host-registered.
    #[must_use]
    pub fn foreign_admission(&self) -> Option<&ForeignModuleAdmission> {
        self.foreign.as_ref().map(|foreign| &foreign.admission)
    }

    pub(crate) fn foreign_source(&self) -> Option<&crate::foreign::ForeignModuleSource> {
        self.foreign.as_ref()
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
            .map(|module| {
                std::sync::Arc::try_unwrap(module.source).unwrap_or_else(|source| (*source).clone())
            })
            .collect::<Vec<_>>()
            .into_boxed_slice()
    }

    /// Returns modules in deterministic dependency order.
    #[must_use]
    pub fn modules(&self) -> &[LoadedModule] {
        &self.modules
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
            let (source, mut surface) = parse_surface_module(
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
                surface,
                dependencies: Vec::new(),
                relative_edges: Vec::new(),
                state: VisitState::Active,
                foreign: None,
            };
            let roots = ModuleRoots {
                named: HashMap::from([(ModuleRootName::new("std").unwrap(), PathBuf::from("."))]),
                foreign: crate::foreign::ForeignRegistrations::default(),
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
}

impl GraphDiagnostic {
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

#[derive(Clone, Debug)]
struct StagedModule {
    id: ModuleId,
    canonical_path: PathBuf,
    owners: OwnerSet,
    source: SourceFile,
    surface: SurfaceModule,
    dependencies: Vec<ModuleDependency>,
    relative_edges: Vec<RelativeEdge>,
    state: VisitState,
    foreign: Option<crate::foreign::ForeignModuleSource>,
}

impl StagedModule {
    fn into_loaded(self) -> LoadedModule {
        LoadedModule {
            id: self.id,
            canonical_path: self.canonical_path,
            source: std::sync::Arc::new(self.source),
            surface: self.surface,
            dependencies: self.dependencies.into_boxed_slice(),
            foreign: self.foreign,
        }
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
    limits: GraphLimits,
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
/// depth-first traversal, with the admitted diagnostic sources retained.
pub fn load_module_graph(
    entry: &Path,
    roots: &ModuleRoots,
) -> Result<ModuleGraph, GraphDiagnostic> {
    let mut staged = Vec::new();
    let result: Result<ModuleGraph, LoadGraphError> = (|| {
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
        let mut budget = GraphBudget::default();
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
        let mut builtin_native_buffer = None;

        while let Some(frame) = frames.last() {
            let module = frame.module;
            let module_index = module.index();
            let import_index = frame.next_import;
            if import_index == staged[module_index].surface.imports.len() {
                let completed = module;
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
            frames
                .last_mut()
                .expect("the loop observed one traversal frame")
                .next_import += 1;

            if let SurfaceModulePath::Absolute { root, segments } = &import.path
                && root.text == "foreign"
            {
                let path = format!(
                    "@foreign.{}",
                    segments
                        .iter()
                        .map(|segment| segment.text.as_str())
                        .collect::<Vec<_>>()
                        .join(".")
                );
                let registration = roots.foreign.get(&path).ok_or_else(|| {
                    ModuleFailure::source(
                        ModuleReason::UnknownForeign,
                        import.span,
                        Some(PathBuf::from(&path)),
                    )
                })?;
                let target = if let Some(target) = by_path.get(Path::new(&path)).copied() {
                    target
                } else {
                    budget.charge_sources()?;
                    staged
                        .try_reserve(1)
                        .map_err(|_| ModuleFailure::resource(ModuleResource::Sources))?;
                    dependency_order
                        .try_reserve(1)
                        .map_err(|_| ModuleFailure::resource(ModuleResource::Sources))?;
                    let (source, surface) = parse_surface_module(
                        Path::new(&path),
                        registration.source().to_owned(),
                        Some(import.span),
                        &mut budget.syntax_work,
                    )?;
                    let id = ModuleId::admitted(
                        graph_identity,
                        u32::try_from(staged.len())
                            .map_err(|_| ModuleFailure::resource(ModuleResource::Sources))?,
                    );
                    let admission = ForeignModuleAdmission {
                        module_id: id,
                        registration_id: registration.id(),
                        manifest_digest: registration.digest(),
                        origin: crate::source::Origin::Source(surface.span),
                    };
                    staged.push(StagedModule {
                        id,
                        canonical_path: PathBuf::from(&path),
                        source,
                        surface,
                        owners: OwnerSet::from_paths(&[], &mut budget)?,
                        dependencies: Vec::new(),
                        relative_edges: Vec::new(),
                        state: VisitState::Finished,
                        foreign: Some(crate::foreign::ForeignModuleSource {
                            admission,
                            manifest: std::sync::Arc::clone(registration),
                        }),
                    });
                    by_path.insert(PathBuf::from(&path), id);
                    dependency_order.push(id);
                    id
                };
                staged[module_index]
                    .dependencies
                    .try_reserve(1)
                    .map_err(|_| ModuleFailure::resource(ModuleResource::Edges))?;
                staged[module_index].dependencies.push(ModuleDependency {
                    target,
                    import_span: import.span,
                });
                continue;
            }

            if let SurfaceModulePath::Absolute { root, segments } = &import.path
                && root.text == "builtin"
            {
                if segments.len() != 1
                    || !matches!(segments[0].text.as_str(), "cell" | "native_buffer")
                {
                    return Err(ModuleFailure::source(
                        ModuleReason::UnknownBuiltin,
                        import.span,
                        None,
                    )
                    .into());
                }
                let native_buffer = segments[0].text == "native_buffer";
                let cached = if native_buffer {
                    &mut builtin_native_buffer
                } else {
                    &mut builtin_cell
                };
                let target = if let Some(id) = *cached {
                    id
                } else {
                    let id = admit_builtin_resource(
                        native_buffer,
                        graph_identity,
                        import.span,
                        &mut budget,
                        &mut staged,
                        &mut dependency_order,
                    )?;
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
        let modules = std::mem::take(&mut staged)
            .into_iter()
            .map(StagedModule::into_loaded)
            .collect::<Vec<_>>()
            .into_boxed_slice();
        Ok(ModuleGraph {
            modules,
            entry: entry_id,
        })
    })();
    result.map_err(|failure| GraphDiagnostic {
        failure: Box::new(failure),
        sources: staged
            .into_iter()
            .map(|module| module.source)
            .collect::<Vec<_>>()
            .into_boxed_slice(),
    })
}

fn admit_builtin_resource(
    native_buffer: bool,
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
    let path = PathBuf::from(if native_buffer {
        "@builtin.native_buffer"
    } else {
        "@builtin.cell"
    });
    let (source, surface) = parse_surface_module(
        &path,
        if native_buffer {
            NATIVE_BUFFER_SOURCE
        } else {
            CELL_SOURCE
        }
        .to_owned(),
        Some(import_span),
        &mut budget.syntax_work,
    )?;
    let value = u32::try_from(staged.len())
        .map_err(|_| ModuleFailure::resource(ModuleResource::Sources))?;
    let id = ModuleId {
        namespace: if native_buffer {
            ModuleIdNamespace::BuiltinNativeBuffer
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
        foreign: None,
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
    let (source, surface) =
        load_surface_module(&canonical_path, import_span, &mut budget.syntax_work)?;
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
        foreign: None,
    });
    Ok(id)
}

fn load_surface_module(
    path: &Path,
    import_span: Option<Span>,
    syntax_budget: &mut SyntaxBudget,
) -> Result<(SourceFile, SurfaceModule), LoadGraphError> {
    let bytes = fs::read(path).map_err(|error| LoadGraphError::Read {
        path: path.to_path_buf(),
        kind: error.kind(),
        import_span,
    })?;
    let text = String::from_utf8(bytes).map_err(|_| LoadGraphError::InvalidUtf8 {
        path: path.to_path_buf(),
        import_span,
    })?;
    parse_surface_module(path, text, import_span, syntax_budget)
}

fn parse_surface_module(
    path: &Path,
    text: String,
    import_span: Option<Span>,
    syntax_budget: &mut SyntaxBudget,
) -> Result<(SourceFile, SurfaceModule), LoadGraphError> {
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
    let tree = parse_with_budget(lexed, syntax_budget);
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
    let surface = match project_module(&source, &tree) {
        Ok(surface) => surface,
        Err(error) => {
            return Err(LoadGraphError::Projection {
                source,
                error,
                import_span,
            });
        }
    };
    Ok((source, surface))
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
    use super::*;

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
                declaration_order: Vec::new(),
                type_declarations: Vec::new(),
                interfaces: Vec::new(),
                effects: Vec::new(),
                implementations: Vec::new(),
                definitions: Vec::new(),
                resources: Vec::new(),
                span,
            },
            dependencies: Box::new([]),
            foreign: None,
        }
    }
}

/// Host-selected identity of one immutable foreign registration manifest.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ForeignRegistrationId(u64);

impl ForeignRegistrationId {
    /// Creates a host registration identity, independently of source spelling.
    #[must_use]
    pub const fn new(value: u64) -> Self {
        Self(value)
    }
    /// Returns the host registration key.
    #[must_use]
    pub const fn value(self) -> u64 {
        self.0
    }
}

/// Immutable admission metadata for a registered module with an ordinary ModuleId.
///
/// Retained only for declarations loaded from the immutable host registration table.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ForeignModuleAdmission {
    /// Ordinary admitted module identity, with no library-specific namespace.
    pub module_id: ModuleId,
    /// Immutable host registry entry.
    pub registration_id: ForeignRegistrationId,
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
