//! Reusable, stage-preserving Ash pipeline orchestration.

use std::{collections::HashMap, error::Error, fmt, io, path::PathBuf, sync::Arc};

use crate::{
    core::{UnvalidatedProgram, ValidatedProgram, ValidationError, validate_modules},
    diagnostic::{Diagnostic, SourceLabel, compare_source_spans},
    elaborate::{Elaborator, TypeError, check_module_with_budget, link_modules},
    eval::{Evaluation, ObservedHeap, RuntimeFailure, Value, evaluate},
    lexer::LexReason,
    module::{LoadGraphError, ModuleId, ModuleRoots, load_module_graph},
    parser::{ParseDiagnostic, ProjectionError, ResourceFailure},
    pattern::UsefulnessBudget,
    resolve::{DependencyExports, ResolveError, ResolveReason, resolve_module_with_budget},
    resolved::{ResolvedApplicationExpr, ResolvedExpr, ResolvedExprKind, ResolvedOccurrence},
    source::{SourceError, SourceFile, SourceId, Span},
    types::{Type, TypeWorkBudget},
};

/// Tool-facing inputs for one modular Ash execution.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RunConfiguration {
    /// Entry module source path.
    pub entry: PathBuf,
    /// Explicit named module roots.
    pub roots: ModuleRoots,
}

/// Stable entry-contract failure families.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum EntryReason {
    /// The entry module declares no local `main`.
    MissingMain,
    /// The local `main` scheme is polymorphic.
    MainPolymorphic,
    /// The local `main` domain is not `Unit`.
    MainDomain,
    /// The local `main` result is not closed.
    MainOpenResult,
}

impl fmt::Display for EntryReason {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(match self {
            Self::MissingMain => "entry.missing-main",
            Self::MainPolymorphic => "entry.main-polymorphic",
            Self::MainDomain => "entry.main-domain",
            Self::MainOpenResult => "entry.main-open-result",
        })
    }
}

/// One source-owned entry-contract rejection.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct EntryFailure {
    /// Structured entry-contract diagnostic.
    pub diagnostic: Box<Diagnostic<EntryReason>>,
}

impl EntryFailure {
    fn new(reason: EntryReason, primary: Span) -> Self {
        let message = match reason {
            EntryReason::MissingMain => "this entry module declares no local main",
            EntryReason::MainPolymorphic => "this main has a polymorphic scheme",
            EntryReason::MainDomain => "this main does not accept Unit",
            EntryReason::MainOpenResult => "this main result is not closed",
        };
        Self {
            diagnostic: Box::new(Diagnostic::new(reason, SourceLabel::new(primary, message))),
        }
    }

    /// Returns the stable entry-contract reason.
    #[must_use]
    pub fn reason(&self) -> EntryReason {
        self.diagnostic.reason
    }
}

impl fmt::Display for EntryFailure {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.diagnostic.reason.fmt(formatter)
    }
}

impl Error for EntryFailure {}

/// The observable result of one successful source-file pipeline.
///
/// The observation retains the evaluation heap even when `value` is a closure
/// whose captured environment contains structural locations.
#[derive(Clone, Debug)]
pub struct Observation {
    /// The evaluated Ash value.
    pub value: Value,
    /// The structural type assigned to the program result.
    pub ty: Type,
    type_display: Option<String>,
    _heap: Arc<ObservedHeap>,
}

impl Observation {
    /// Returns the structural rendering of the observed value.
    #[must_use]
    pub fn value_display(&self) -> String {
        self.value.to_string()
    }

    /// Returns the source-facing rendering of the observed result type.
    #[must_use]
    pub fn type_display(&self) -> String {
        self.type_display
            .clone()
            .unwrap_or_else(|| self.ty.to_string())
    }
}

/// Lexical, parser, and resource facts retained before surface projection.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SyntaxFailure {
    /// Independently structured lexical diagnostics.
    pub lexical: Vec<Diagnostic<LexReason>>,
    /// Structured parser diagnostics and recovery context.
    pub parser: Vec<ParseDiagnostic>,
    /// A non-language parser resource failure, when present.
    pub resource: Option<ResourceFailure>,
}

/// A failure from one explicit compiler or runtime stage.
#[derive(Debug)]
pub enum PipelineFailure {
    /// The admitted source model could not produce a checked token span.
    SourceModel(SourceError),
    /// Lexing or parsing retained diagnostics or exhausted a resource budget.
    Syntax(Box<SyntaxFailure>),
    /// Recovery-free concrete syntax violated the projection contract.
    Projection(ProjectionError),
    /// Name resolution rejected the source or lost an invariant.
    Resolution(ResolveError),
    /// Typed elaboration rejected the source or lost an invariant.
    Typing(TypeError),
    /// The entry module violated the local `main` contract.
    Entry(EntryFailure),
    /// Independent Core validation rejected compiler output.
    Validation(ValidationError),
    /// The explicit evaluator reported a runtime invariant failure.
    Runtime(RuntimeFailure),
}

impl PipelineFailure {
    /// Returns the stable reason owned by the first failing stage.
    #[must_use]
    pub fn reason_code(&self) -> String {
        match self {
            Self::SourceModel(_) => "internal.source-model".into(),
            Self::Syntax(failure) => {
                syntax_reason_code(&failure.lexical, &failure.parser, failure.resource)
            }
            Self::Projection(error) => projection_reason(*error).into(),
            Self::Resolution(error) => error.reason.to_string(),
            Self::Typing(TypeError::Source(diagnostic)) => diagnostic.reason.to_string(),
            Self::Typing(TypeError::Mismatch(_)) => "type.mismatch".into(),
            Self::Typing(TypeError::Internal(failure)) => failure.reason_code().into(),
            Self::Entry(failure) => failure.reason().to_string(),
            Self::Validation(error) => error.reason().to_string(),
            Self::Runtime(error) => error.reason_code().to_owned(),
        }
    }

    /// Reports whether this failure rejects Ash source rather than the tool.
    #[must_use]
    pub fn is_source_rejection(&self) -> bool {
        match self {
            Self::Syntax(failure) => {
                failure.resource.is_none()
                    && (!failure.lexical.is_empty() || !failure.parser.is_empty())
            }
            Self::Resolution(error) => !matches!(
                error.reason,
                ResolveReason::BinderIdExhausted
                    | ResolveReason::TypeResourceExhausted
                    | ResolveReason::InternalState
            ),
            Self::Typing(TypeError::Source(_) | TypeError::Mismatch(_)) => true,
            Self::Entry(_) => true,
            Self::SourceModel(_)
            | Self::Projection(_)
            | Self::Typing(TypeError::Internal(_))
            | Self::Validation(_)
            | Self::Runtime(_) => false,
        }
    }
}

impl fmt::Display for PipelineFailure {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(match self {
            Self::SourceModel(_) => "source-model failure",
            Self::Syntax(_) => "source syntax failure",
            Self::Projection(_) => "surface projection failure",
            Self::Resolution(_) => "name-resolution failure",
            Self::Typing(_) => "typed-elaboration failure",
            Self::Entry(_) => "entry-contract failure",
            Self::Validation(_) => "Core validation failure",
            Self::Runtime(_) => "runtime failure",
        })
    }
}

impl Error for PipelineFailure {}

/// A file-input failure or a stage-preserving pipeline failure.
#[derive(Debug)]
pub enum FileFailure {
    /// Module graph loading failed at its owning stage.
    Graph(LoadGraphError),
    /// The source path could not be read.
    Read {
        /// The requested path.
        path: PathBuf,
        /// Stable I/O error category.
        kind: io::ErrorKind,
    },
    /// The file contents are not UTF-8.
    InvalidUtf8 {
        /// The requested path.
        path: PathBuf,
    },
    /// The UTF-8 text cannot fit the source representation.
    Source(SourceError),
    /// The admitted source reached a compiler or runtime stage failure.
    Pipeline(PipelineFailure),
}

impl FileFailure {
    /// Reports whether this failure rejects Ash source rather than invocation,
    /// input, compiler, or runtime state.
    #[must_use]
    pub fn is_source_rejection(&self) -> bool {
        match self {
            Self::Graph(error) => error.is_source_rejection(),
            Self::Pipeline(failure) => failure.is_source_rejection(),
            Self::Read { .. } | Self::InvalidUtf8 { .. } | Self::Source(_) => false,
        }
    }

    /// Returns the stable first-stage reason code.
    #[must_use]
    pub fn reason_code(&self) -> String {
        match self {
            Self::Graph(error) => match error {
                LoadGraphError::Module(failure) => failure.reason().to_string(),
                LoadGraphError::Read { .. } => "input.read".to_owned(),
                LoadGraphError::InvalidUtf8 { .. } => "input.invalid-utf8".to_owned(),
                LoadGraphError::SourceModel { .. } => "input.source-model".to_owned(),
                LoadGraphError::Syntax(failure) => {
                    syntax_reason_code(&failure.lexical, &failure.parser, failure.resource)
                }
                LoadGraphError::Projection { error, .. } => projection_reason(*error).to_owned(),
            },
            Self::Read { .. } => "input.read".to_owned(),
            Self::InvalidUtf8 { .. } => "input.invalid-utf8".to_owned(),
            Self::Source(_) => "input.source-model".to_owned(),
            Self::Pipeline(failure) => failure.reason_code(),
        }
    }
}

fn syntax_reason_code(
    lexical: &[Diagnostic<LexReason>],
    parser: &[ParseDiagnostic],
    resource: Option<ResourceFailure>,
) -> String {
    if let Some(resource) = resource {
        return resource.reason_code().to_owned();
    }
    match (lexical.first(), parser.first()) {
        (Some(lexical), Some(parser))
            if compare_source_spans(parser.primary.span(), lexical.primary.span()).is_lt() =>
        {
            parser.reason.to_string()
        }
        (Some(lexical), _) => lexical.reason.to_string(),
        (None, Some(parser)) => parser.reason.to_string(),
        (None, None) => "internal.syntax".to_owned(),
    }
}

impl fmt::Display for FileFailure {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Graph(error) => error.fmt(formatter),
            Self::Read { path, kind } => {
                write!(formatter, "cannot read {}: {kind}", path.display())
            }
            Self::InvalidUtf8 { path } => {
                write!(formatter, "{} is not a UTF-8 source file", path.display())
            }
            Self::Source(error) => error.fmt(formatter),
            Self::Pipeline(error) => error.fmt(formatter),
        }
    }
}

impl Error for FileFailure {}

/// Loads, checks, links, validates, and evaluates one modular Ash graph.
///
/// # Errors
///
/// Returns a structured input, source-model, compiler, source-rejection, or
/// runtime failure.
pub fn run_path(configuration: RunConfiguration) -> Result<Observation, FileFailure> {
    run_path_with_consumers(configuration, validate_modules, evaluate)
}

fn run_path_with_consumers<V, E>(
    configuration: RunConfiguration,
    validator: V,
    evaluator: E,
) -> Result<Observation, FileFailure>
where
    V: FnOnce(
        UnvalidatedProgram,
        &[&SourceFile],
        &[(ModuleId, SourceId)],
    ) -> Result<ValidatedProgram, ValidationError>,
    E: FnOnce(&ValidatedProgram) -> Result<Evaluation, RuntimeFailure>,
{
    let graph = load_module_graph(&configuration.entry, &configuration.roots)
        .map_err(FileFailure::Graph)?;
    let mut checked: Vec<crate::resolved::CheckedModule> =
        Vec::with_capacity(graph.modules().len());
    let mut checked_by_module: HashMap<ModuleId, usize> =
        HashMap::with_capacity(graph.modules().len());
    let mut resolution_type_work = TypeWorkBudget::default();
    let mut checking_type_work = TypeWorkBudget::default();
    let mut coverage_work = UsefulnessBudget::default();
    for module in graph.modules() {
        let dependencies = module
            .dependencies()
            .iter()
            .map(|edge| {
                let dependency = checked_by_module
                    .get(&edge.target())
                    .and_then(|index| checked.get(*index))
                    .ok_or(PipelineFailure::Typing(TypeError::Internal(
                        crate::elaborate::ElaborationFailure::InvalidState,
                    )))?;
                DependencyExports::new(edge, dependency.exports()).map_err(|_| {
                    PipelineFailure::Typing(TypeError::Internal(
                        crate::elaborate::ElaborationFailure::InvalidState,
                    ))
                })
            })
            .collect::<Result<Vec<_>, _>>()
            .map_err(FileFailure::Pipeline)?;
        let resolved = resolve_module_with_budget(module, &dependencies, &mut resolution_type_work)
            .map_err(PipelineFailure::Resolution)
            .map_err(FileFailure::Pipeline)?;
        drop(dependencies);
        let checked_module =
            check_module_with_budget(resolved, &mut checking_type_work, &mut coverage_work)
                .map_err(PipelineFailure::Typing)
                .map_err(FileFailure::Pipeline)?;
        checked_by_module.insert(module.id(), checked.len());
        checked.push(checked_module);
    }

    let entry = checked
        .iter()
        .find(|module| module.module() == graph.entry())
        .ok_or_else(internal_file_failure)?;
    let main = entry
        .schemes()
        .iter()
        .find(|scheme| scheme.spelling == "main")
        .ok_or_else(|| {
            FileFailure::Pipeline(PipelineFailure::Entry(EntryFailure::new(
                EntryReason::MissingMain,
                entry.span(),
            )))
        })?;
    let main_span = main.origin.primary_span();
    let result_type = match &main.scheme {
        Type::Forall(_, _) => {
            return Err(entry_failure(EntryReason::MainPolymorphic, main_span));
        }
        Type::Function(domain, result) if matches!(domain.as_ref(), Type::Unit) => result.as_ref(),
        Type::Function(_, _)
        | Type::Int
        | Type::Bool
        | Type::Unit
        | Type::Tuple(_)
        | Type::Nominal(_)
        | Type::AppliedNominal(_, _)
        | Type::Variable(_)
        | Type::Inference(_) => {
            return Err(entry_failure(EntryReason::MainDomain, main_span));
        }
    };
    if !closed_entry_result(result_type) {
        return Err(entry_failure(EntryReason::MainOpenResult, main_span));
    }
    let result = ResolvedExpr {
        kind: ResolvedExprKind::Apply(ResolvedApplicationExpr {
            function: Box::new(ResolvedExpr {
                kind: ResolvedExprKind::Occurrence(ResolvedOccurrence {
                    binder: main.binder,
                    spelling: "main".to_owned(),
                    origin: main.origin.clone(),
                }),
                span: main_span,
            }),
            argument: Box::new(ResolvedExpr {
                kind: ResolvedExprKind::Unit,
                span: main_span,
            }),
        }),
        span: main_span,
    };
    let linked = link_modules(checked, graph.entry(), result)
        .map_err(PipelineFailure::Typing)
        .map_err(FileFailure::Pipeline)?;
    let registry = Arc::clone(&linked.registry);
    let mut elaborator = Elaborator::for_module_program(&linked)
        .map_err(TypeError::Internal)
        .map_err(PipelineFailure::Typing)
        .map_err(FileFailure::Pipeline)?;
    let typed = elaborator
        .synthesize_module_program(&linked)
        .map_err(PipelineFailure::Typing)
        .map_err(FileFailure::Pipeline)?;
    let ty = typed.ty;
    let type_display = registry.display_type(&ty);
    let unchecked = elaborator
        .finish(typed.node)
        .map_err(TypeError::Internal)
        .map_err(PipelineFailure::Typing)
        .map_err(FileFailure::Pipeline)?;
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
    let validated = validator(unchecked, &sources, &module_sources)
        .map_err(PipelineFailure::Validation)
        .map_err(FileFailure::Pipeline)?;
    let evaluation = evaluator(&validated)
        .map_err(PipelineFailure::Runtime)
        .map_err(FileFailure::Pipeline)?;
    let (value, heap) = evaluation.into_observation_parts();
    Ok(Observation {
        value,
        ty,
        type_display: Some(type_display),
        _heap: heap,
    })
}

fn entry_failure(reason: EntryReason, primary: Span) -> FileFailure {
    FileFailure::Pipeline(PipelineFailure::Entry(EntryFailure::new(reason, primary)))
}

fn internal_file_failure() -> FileFailure {
    FileFailure::Pipeline(PipelineFailure::Typing(TypeError::Internal(
        crate::elaborate::ElaborationFailure::InvalidState,
    )))
}

fn closed_entry_result(root: &Type) -> bool {
    let mut work = vec![root];
    while let Some(ty) = work.pop() {
        match ty {
            Type::Variable(_) | Type::Inference(_) | Type::Forall(_, _) => return false,
            Type::Tuple(elements) | Type::AppliedNominal(_, elements) => work.extend(elements),
            Type::Function(domain, codomain) => {
                work.push(codomain);
                work.push(domain);
            }
            Type::Int | Type::Bool | Type::Unit | Type::Nominal(_) => {}
        }
    }
    true
}

const fn projection_reason(error: ProjectionError) -> &'static str {
    match error {
        ProjectionError::ResourceLimit(ResourceFailure::StructuralDepth { .. }) => {
            "internal.resource.structural-depth"
        }
        ProjectionError::ResourceLimit(ResourceFailure::SyntaxWork { .. }) => {
            "internal.resource.syntax-work"
        }
        ProjectionError::RecoveryNodesPresent => "internal.projection.recovery-nodes",
        ProjectionError::MalformedTree(_) => "internal.projection.malformed-tree",
    }
}

#[cfg(test)]
mod tests {
    use std::{
        cell::Cell,
        fs,
        path::PathBuf,
        sync::atomic::{AtomicU64, Ordering},
    };

    use super::*;
    use crate::types::{InferenceVariableId, TypeVariableId};

    static TEST_SOURCE_IDS: AtomicU64 = AtomicU64::new(0);

    struct TestSource(PathBuf);

    impl TestSource {
        fn write(text: &str) -> Self {
            loop {
                let id = TEST_SOURCE_IDS.fetch_add(1, Ordering::Relaxed);
                let path = std::env::temp_dir()
                    .join(format!("ash-driver-unit-{}-{id}.ash", std::process::id()));
                match fs::OpenOptions::new()
                    .write(true)
                    .create_new(true)
                    .open(&path)
                {
                    Ok(mut file) => {
                        use std::io::Write as _;
                        file.write_all(text.as_bytes())
                            .expect("the modular fixture should be writable");
                        return Self(path);
                    }
                    Err(error) if error.kind() == io::ErrorKind::AlreadyExists => continue,
                    Err(error) => panic!("the modular fixture should be creatable: {error}"),
                }
            }
        }

        fn configuration(&self) -> RunConfiguration {
            RunConfiguration {
                entry: self.0.clone(),
                roots: ModuleRoots::empty(),
            }
        }
    }

    impl Drop for TestSource {
        fn drop(&mut self) {
            let _ = fs::remove_file(&self.0);
        }
    }

    #[test]
    fn entry_result_closure_walks_every_nested_type() {
        let closed = Type::Tuple(
            vec![
                Type::Int,
                Type::Function(Box::new(Type::Unit), Box::new(Type::Bool)),
            ]
            .into_boxed_slice(),
        );
        let rigid = Type::Tuple(
            vec![Type::Int, Type::Variable(TypeVariableId::generated(0))].into_boxed_slice(),
        );
        let inference = Type::Function(
            Box::new(Type::Unit),
            Box::new(Type::Inference(InferenceVariableId::new(0))),
        );

        assert!(closed_entry_result(&closed));
        assert!(!closed_entry_result(&rigid));
        assert!(!closed_entry_result(&inference));
    }

    #[test]
    fn injected_validation_failure_stops_before_evaluation() {
        let source = TestSource::write("main : Unit -> Int\nmain () = 1\n");
        let evaluation_called = Cell::new(false);

        let failure = run_path_with_consumers(
            source.configuration(),
            |unchecked, _, _| validate_modules(unchecked, &[], &[]),
            |_| {
                evaluation_called.set(true);
                panic!("evaluation must not run after validation fails")
            },
        )
        .expect_err("omitting the admitted source must fail provenance validation");

        let FileFailure::Pipeline(PipelineFailure::Validation(error)) = failure else {
            panic!("the injected validator failure should retain its stage");
        };
        assert_eq!(error.reason(), crate::core::ValidationReason::Provenance);
        assert!(!evaluation_called.get());
    }

    #[test]
    fn returned_closure_observation_retains_its_captured_structural_heap() {
        let source = TestSource::write(concat!(
            "main : Unit -> Unit -> (Int, Int)\n",
            "main () = {\n",
            "let pair = (20, 22)\n",
            "fn(ignored) {\n",
            "pair\n",
            "}\n",
            "}\n",
        ));

        let observation = run_path(source.configuration()).expect("the closure should evaluate");

        assert!(matches!(observation.value, Value::Function(_)));
        assert_eq!(observation._heap.cell_count(), 1);
    }
}
