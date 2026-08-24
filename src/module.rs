//! Canonical source loading for passive module graphs.

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
/// Maximum active traversal and owner-propagation work items.
pub const MODULE_PENDING_LIMIT: usize = 16_384;

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
        debug_assert!(matches!(self.namespace, ModuleIdNamespace::Admitted));
        self.value as usize
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
            ModuleIdNamespace::DirectCoreSource => write!(formatter, "source:{}", self.value),
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
    source: SourceFile,
    surface: SurfaceModule,
    dependencies: Box<[ModuleDependency]>,
}

impl LoadedModule {
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
    pub const fn source(&self) -> &SourceFile {
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
    /// Projected module data contains no path segment where one is required.
    InvalidPath,
    /// Module graph work exceeded an implementation budget.
    ResourceLimit,
}

impl fmt::Display for ModuleReason {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(match self {
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
    /// Active iterative traversal and owner-propagation work items.
    PendingWork,
}

static NEXT_MODULE_GRAPH: AtomicU32 = AtomicU32::new(1);

fn allocate_module_graph_identity() -> Result<u32, LoadGraphError> {
    NEXT_MODULE_GRAPH
        .fetch_update(Ordering::Relaxed, Ordering::Relaxed, |value| {
            value.checked_add(1)
        })
        .map_err(|_| ModuleFailure::resource(ModuleResource::GraphIdentities).into())
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
}

impl ModuleFailure {
    fn source(reason: ModuleReason, primary: Span, path: Option<PathBuf>) -> Self {
        Self {
            reason,
            source_rejection: true,
            primary: Some(primary),
            path,
            root: None,
            io_kind: None,
            resource: None,
        }
    }

    fn unknown_root(primary: Span, root: String) -> Self {
        let mut failure = Self::source(ModuleReason::UnknownRoot, primary, None);
        failure.root = Some(root);
        failure
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

    /// Returns the import occurrence that caused a source rejection.
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

/// Structured syntax facts retained for one rejected module source.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ModuleSyntaxFailure {
    /// The admitted source needed to render retained spans.
    pub source: SourceFile,
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
    },
}

impl LoadGraphError {
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
    fn from_paths(paths: Vec<PathBuf>) -> Self {
        let mut ordered = Vec::with_capacity(paths.len());
        let mut membership = HashSet::with_capacity(paths.len());
        for path in paths {
            if membership.insert(path.clone()) {
                ordered.push(path);
            }
        }
        Self {
            ordered,
            membership,
        }
    }

    fn contains(&self, owner: &Path) -> bool {
        self.membership.contains(owner)
    }

    fn insert(&mut self, owner: PathBuf) {
        let retained = owner.clone();
        let inserted = self.membership.insert(owner);
        debug_assert!(inserted, "owner insertion follows a membership check");
        self.ordered.push(retained);
    }
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
}

impl StagedModule {
    fn into_loaded(self) -> LoadedModule {
        LoadedModule {
            id: self.id,
            canonical_path: self.canonical_path,
            source: self.source,
            surface: self.surface,
            dependencies: self.dependencies.into_boxed_slice(),
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
    pending_work: usize,
}

impl Default for GraphLimits {
    fn default() -> Self {
        Self {
            sources: MODULE_SOURCE_LIMIT,
            edges: MODULE_EDGE_LIMIT,
            path_segments: MODULE_PATH_SEGMENT_LIMIT,
            pending_work: MODULE_PENDING_LIMIT,
        }
    }
}

#[derive(Debug, Default)]
struct GraphBudget {
    sources: usize,
    edges: usize,
    path_segments: usize,
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
/// Returns [`LoadGraphError`] from the first failing input or compiler stage in
/// source-ordered depth-first traversal.
pub fn load_module_graph(entry: &Path, roots: &ModuleRoots) -> Result<ModuleGraph, LoadGraphError> {
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
    let mut staged = Vec::new();
    let mut by_path = HashMap::new();
    let entry_id = admit_module(
        canonical_entry,
        vec![entry_root],
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

        let (target_path, owners, relative) =
            resolve_import(&staged[module_index], &import, roots)?;
        let existing = by_path.get(&target_path).copied();
        let target = if let Some(target) = existing {
            propagate_owners(target, owners, import.span, &mut staged, &mut budget)?;
            target
        } else {
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
    let modules = staged
        .into_iter()
        .map(StagedModule::into_loaded)
        .collect::<Vec<_>>()
        .into_boxed_slice();
    Ok(ModuleGraph {
        modules,
        entry: entry_id,
    })
}

fn admit_module(
    canonical_path: PathBuf,
    owners: Vec<PathBuf>,
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
        owners: OwnerSet::from_paths(owners),
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
    let source = SourceFile::new(path.to_string_lossy(), text).map_err(|error| {
        LoadGraphError::SourceModel {
            path: path.to_path_buf(),
            error,
            import_span,
        }
    })?;
    let lexed =
        lex_with_budget(&source, syntax_budget).map_err(|error| LoadGraphError::SourceModel {
            path: path.to_path_buf(),
            error,
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
        })));
    }
    let surface = project_module(&source, &tree).map_err(|error| LoadGraphError::Projection {
        source: source.clone(),
        error,
    })?;
    Ok((source, surface))
}

fn resolve_import(
    module: &StagedModule,
    import: &SurfaceImport,
    roots: &ModuleRoots,
) -> Result<(PathBuf, Vec<PathBuf>, bool), LoadGraphError> {
    match &import.path {
        SurfaceModulePath::Relative(segments) => {
            let parent = module.canonical_path.parent().ok_or_else(|| {
                ModuleFailure::source(
                    ModuleReason::InvalidPath,
                    import.span,
                    Some(module.canonical_path.clone()),
                )
            })?;
            let candidate =
                target_path(parent, segments.iter().map(|segment| segment.text.as_str()))
                    .ok_or_else(|| {
                        ModuleFailure::source(ModuleReason::InvalidPath, import.span, None)
                    })?;
            let canonical = canonical_import_target(candidate, import.span)?;
            for owner in &module.owners.ordered {
                require_within_owner(&canonical, owner, import.span)?;
            }
            Ok((canonical, module.owners.ordered.clone(), true))
        }
        SurfaceModulePath::Absolute { root, segments } => {
            let owner = roots
                .named
                .get(root.text.as_str())
                .ok_or_else(|| ModuleFailure::unknown_root(import.span, root.text.clone()))?;
            let candidate =
                target_path(owner, segments.iter().map(|segment| segment.text.as_str()))
                    .ok_or_else(|| {
                        ModuleFailure::source(ModuleReason::InvalidPath, import.span, None)
                    })?;
            let canonical = canonical_import_target(candidate, import.span)?;
            require_within_owner(&canonical, owner, import.span)?;
            Ok((canonical, vec![owner.clone()], false))
        }
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
    owners: Vec<PathBuf>,
    causing_import: Span,
    staged: &mut [StagedModule],
    budget: &mut GraphBudget,
) -> Result<(), LoadGraphError> {
    let mut pending = VecDeque::new();
    for owner in owners {
        budget.retain_pending_work()?;
        pending.push_back((start, owner, causing_import));
    }
    while let Some((module, owner, cause)) = pending.pop_front() {
        let module_index = module.index();
        if staged[module_index].owners.contains(&owner) {
            budget.release_pending_work();
            continue;
        }
        require_within_owner(&staged[module_index].canonical_path, &owner, cause)?;
        staged[module_index].owners.insert(owner.clone());
        for edge_index in 0..staged[module_index].relative_edges.len() {
            let edge = &staged[module_index].relative_edges[edge_index];
            require_within_owner(&edge.canonical_target, &owner, edge.import_span)?;
            let target = edge.target;
            let import_span = edge.import_span;
            budget.retain_pending_work()?;
            pending.push_back((target, owner.clone(), import_span));
        }
        budget.release_pending_work();
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
            pending_work: 1,
        });

        assert!(budget.charge_sources().is_ok());
        assert_resource(budget.charge_sources(), ModuleResource::Sources);
        assert!(budget.charge_edge().is_ok());
        assert_resource(budget.charge_edge(), ModuleResource::Edges);
        assert!(budget.charge_path_segments(2).is_ok());
        assert_resource(budget.charge_path_segments(1), ModuleResource::PathSegments);
        assert!(budget.retain_pending_work().is_ok());
        assert_resource(budget.retain_pending_work(), ModuleResource::PendingWork);
        budget.release_pending_work();
        assert!(budget.retain_pending_work().is_ok());
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
            source,
            surface: SurfaceModule {
                imports: Vec::new(),
                type_declarations: Vec::new(),
                definitions: Vec::new(),
                span,
            },
            dependencies: Box::new([]),
        }
    }
}
