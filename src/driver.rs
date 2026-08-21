//! Reusable, stage-preserving Mini-Ash pipeline orchestration.

use std::{error::Error, fmt, fs, io, path::PathBuf};

use crate::{
    core::{ValidationError, validate},
    diagnostic::Diagnostic,
    elaborate::{ElaborationFailure, Elaborator, PendingFeature, TypeContext, TypeError},
    eval::{RuntimeFailure, Value, evaluate},
    lexer::{LexReason, lex},
    parser::{ParseDiagnostic, ProjectionError, ResourceFailure, parse, project},
    resolve::{ResolveError, ResolveReason, resolve},
    source::{SourceError, SourceFile},
    types::Type,
};

/// The observable result of one successful source-file pipeline.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Observation {
    /// The evaluated Mini-Ash value.
    pub value: Value,
    /// The structural type assigned to the program result.
    pub ty: Type,
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
    /// Independent Core validation rejected compiler output.
    Validation(ValidationError),
    /// The explicit evaluator reported a runtime invariant failure.
    Runtime(RuntimeFailure),
}

impl PipelineFailure {
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
                ResolveReason::BinderIdExhausted | ResolveReason::InternalState
            ),
            Self::Typing(TypeError::Source(_) | TypeError::Mismatch(_)) => true,
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
            Self::Validation(_) => "Core validation failure",
            Self::Runtime(_) => "runtime failure",
        })
    }
}

impl Error for PipelineFailure {}

/// A file-input failure or a stage-preserving pipeline failure.
#[derive(Debug)]
pub enum FileFailure {
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
        matches!(self, Self::Pipeline(failure) if failure.is_source_rejection())
    }
}

impl fmt::Display for FileFailure {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
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

/// Runs every retained Mini-Ash stage over one admitted source file.
///
/// # Errors
///
/// Returns a stage-specific failure without allowing recovery-bearing syntax,
/// unchecked Core, or a pending feature to bypass its owning stage.
pub fn run_source(source: SourceFile) -> Result<Observation, PipelineFailure> {
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
    let resolved = resolve(&surface).map_err(PipelineFailure::Resolution)?;
    if !resolved.definitions.is_empty() {
        return Err(PipelineFailure::Typing(TypeError::Internal(
            ElaborationFailure::Pending(PendingFeature::Definition),
        )));
    }

    let mut elaborator = Elaborator::for_program(&resolved)
        .map_err(|failure| PipelineFailure::Typing(TypeError::Internal(failure)))?;
    let typed = elaborator
        .synthesize(&resolved.result, &TypeContext::new())
        .map_err(PipelineFailure::Typing)?;
    let ty = typed.ty;
    let unchecked = elaborator
        .finish(typed.node)
        .map_err(|failure| PipelineFailure::Typing(TypeError::Internal(failure)))?;
    let validated = validate(unchecked, &[&source]).map_err(PipelineFailure::Validation)?;
    let evaluation = evaluate(&validated).map_err(PipelineFailure::Runtime)?;
    Ok(Observation {
        value: evaluation.value,
        ty,
    })
}

/// Reads one path as UTF-8 and runs the complete retained pipeline.
///
/// # Errors
///
/// Returns a structured input, source-model, compiler, source-rejection, or
/// runtime failure.
pub fn run_path(path: PathBuf) -> Result<Observation, FileFailure> {
    let bytes = fs::read(&path).map_err(|error| FileFailure::Read {
        path: path.clone(),
        kind: error.kind(),
    })?;
    let text =
        String::from_utf8(bytes).map_err(|_| FileFailure::InvalidUtf8 { path: path.clone() })?;
    let source = SourceFile::new(path.to_string_lossy(), text).map_err(FileFailure::Source)?;
    run_source(source).map_err(FileFailure::Pipeline)
}
