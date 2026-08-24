//! Reusable, stage-preserving Ash pipeline orchestration.

use std::{collections::HashMap, error::Error, fmt, io, path::PathBuf, sync::Arc};

use crate::{
    core::{UnvalidatedProgram, ValidatedProgram, ValidationError, validate, validate_modules},
    diagnostic::{Diagnostic, SourceLabel},
    elaborate::{Elaborator, TypeError, check_module, link_modules},
    eval::{Evaluation, ObservedHeap, RuntimeFailure, Value, evaluate},
    lexer::{LexReason, lex},
    module::{LoadGraphError, ModuleId, ModuleRoots, load_module_graph},
    parser::{ParseDiagnostic, ProjectionError, ResourceFailure, parse, project},
    resolve::{DependencyExports, ResolveError, ResolveReason, resolve, resolve_module},
    resolved::{ResolvedApplicationExpr, ResolvedExpr, ResolvedExprKind, ResolvedOccurrence},
    source::{SourceError, SourceFile, Span},
    types::Type,
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
            Self::SourceModel(_) => "source.invalid".into(),
            Self::Syntax(failure) if failure.resource.is_some() => "parse.resource".into(),
            Self::Syntax(failure) => failure
                .lexical
                .first()
                .map(|diagnostic| diagnostic.reason.to_string())
                .or_else(|| {
                    failure
                        .parser
                        .first()
                        .map(|diagnostic| diagnostic.reason.to_string())
                })
                .unwrap_or_else(|| "parse.resource".into()),
            Self::Projection(error) => projection_reason(*error).into(),
            Self::Resolution(error) => error.reason.to_string(),
            Self::Typing(TypeError::Source(diagnostic)) => diagnostic.reason.to_string(),
            Self::Typing(TypeError::Mismatch(_)) => "type.mismatch".into(),
            Self::Typing(TypeError::Internal(_)) => "type.internal".into(),
            Self::Entry(failure) => failure.reason().to_string(),
            Self::Validation(error) => error.reason().to_string(),
            Self::Runtime(error) => format!("runtime.{error:?}"),
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
                LoadGraphError::Syntax(failure) if failure.resource.is_some() => {
                    "parse.resource".to_owned()
                }
                LoadGraphError::Syntax(failure) => failure
                    .lexical
                    .first()
                    .map(|diagnostic| diagnostic.reason.to_string())
                    .or_else(|| {
                        failure
                            .parser
                            .first()
                            .map(|diagnostic| diagnostic.reason.to_string())
                    })
                    .unwrap_or_else(|| "parse.resource".to_owned()),
                LoadGraphError::Projection { error, .. } => projection_reason(*error).to_owned(),
            },
            Self::Read { .. } => "input.read".to_owned(),
            Self::InvalidUtf8 { .. } => "input.invalid-utf8".to_owned(),
            Self::Source(_) => "input.source-model".to_owned(),
            Self::Pipeline(failure) => failure.reason_code(),
        }
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

/// Runs every retained Ash stage over one admitted source file.
///
/// # Errors
///
/// Returns a stage-specific failure without allowing recovery-bearing syntax,
/// unchecked Core, or a pending feature to bypass its owning stage.
pub fn run_source(source: SourceFile) -> Result<Observation, PipelineFailure> {
    run_source_with_consumers(source, validate, evaluate)
}

fn run_source_with_consumers<V, E>(
    source: SourceFile,
    validator: V,
    evaluator: E,
) -> Result<Observation, PipelineFailure>
where
    V: FnOnce(UnvalidatedProgram, &[&SourceFile]) -> Result<ValidatedProgram, ValidationError>,
    E: FnOnce(&ValidatedProgram) -> Result<Evaluation, RuntimeFailure>,
{
    let lexed = lex(&source).map_err(PipelineFailure::SourceModel)?;
    let tree = parse(lexed);
    if tree.resource_failure().is_some()
        || !tree.lexical_diagnostics().is_empty()
        || !tree.parse_diagnostics().is_empty()
    {
        return Err(PipelineFailure::Syntax(Box::new(SyntaxFailure {
            lexical: tree.lexical_diagnostics().to_vec(),
            parser: tree.parse_diagnostics().to_vec(),
            resource: tree.resource_failure(),
        })));
    }
    let surface = project(&source, &tree).map_err(PipelineFailure::Projection)?;
    drop(tree);
    let resolved = resolve(&surface).map_err(PipelineFailure::Resolution)?;
    drop(surface);
    let registry = std::sync::Arc::clone(&resolved.registry);
    let mut elaborator = Elaborator::for_program(&resolved)
        .map_err(|failure| PipelineFailure::Typing(TypeError::Internal(failure)))?;
    let typed = elaborator
        .synthesize_program(&resolved)
        .map_err(PipelineFailure::Typing)?;
    let ty = typed.ty;
    let type_display = registry.display_type(&ty);
    let unchecked = elaborator
        .finish(typed.node)
        .map_err(|failure| PipelineFailure::Typing(TypeError::Internal(failure)))?;
    let validated = validator(unchecked, &[&source]).map_err(PipelineFailure::Validation)?;
    let evaluation = evaluator(&validated).map_err(PipelineFailure::Runtime)?;
    let (value, heap) = evaluation.into_observation_parts();
    Ok(Observation {
        value,
        ty,
        type_display: Some(type_display),
        _heap: heap,
    })
}

/// Loads, checks, links, validates, and evaluates one modular Ash graph.
///
/// # Errors
///
/// Returns a structured input, source-model, compiler, source-rejection, or
/// runtime failure.
pub fn run_path(configuration: RunConfiguration) -> Result<Observation, FileFailure> {
    let graph = load_module_graph(&configuration.entry, &configuration.roots)
        .map_err(FileFailure::Graph)?;
    let mut checked: Vec<crate::resolved::CheckedModule> =
        Vec::with_capacity(graph.modules().len());
    let mut checked_by_module: HashMap<ModuleId, usize> =
        HashMap::with_capacity(graph.modules().len());
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
        let resolved = resolve_module(module, &dependencies)
            .map_err(PipelineFailure::Resolution)
            .map_err(FileFailure::Pipeline)?;
        drop(dependencies);
        let checked_module = check_module(resolved)
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
    let validated = validate_modules(unchecked, &sources, &module_sources)
        .map_err(PipelineFailure::Validation)
        .map_err(FileFailure::Pipeline)?;
    let evaluation = evaluate(&validated)
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
    use std::cell::Cell;

    use super::*;
    use crate::types::{InferenceVariableId, TypeVariableId};

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
        let source =
            SourceFile::new("validation-injection.ash", "1\n").expect("the test source should fit");
        let evaluation_called = Cell::new(false);

        let failure = run_source_with_consumers(
            source,
            |unchecked, _| validate(unchecked, &[]),
            |_| {
                evaluation_called.set(true);
                panic!("evaluation must not run after validation fails")
            },
        )
        .expect_err("omitting the admitted source must fail provenance validation");

        let PipelineFailure::Validation(error) = failure else {
            panic!("the injected validator failure should retain its stage");
        };
        assert_eq!(error.reason(), crate::core::ValidationReason::Provenance);
        assert!(!evaluation_called.get());
    }

    #[test]
    fn returned_closure_observation_retains_its_captured_structural_heap() {
        let source = SourceFile::new(
            "observed-structural-capture.ash",
            "{\nlet pair = (20, 22)\nlet keep : Unit -> (Int, Int) = fn(ignored) {\npair\n}\nkeep\n}\n",
        )
        .expect("the test source should fit");

        let observation = run_source(source).expect("the closure should evaluate");

        assert!(matches!(observation.value, Value::Function(_)));
        assert_eq!(observation._heap.cell_count(), 1);
    }
}
