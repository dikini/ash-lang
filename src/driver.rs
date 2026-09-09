//! Reusable, stage-preserving Ash pipeline orchestration.

use std::{collections::HashMap, error::Error, fmt, io, path::PathBuf, sync::Arc};

use crate::{
    core::{
        UnvalidatedProgram, ValidatedProgram, ValidationError, validate_effect_modules,
        validate_modules,
    },
    diagnostic::{Diagnostic, SourceLabel, compare_source_spans},
    elaborate::{
        EffectElaborator, Elaborator, TypeError, check_module_with_budget,
        checked_program_contains_effect_syntax, link_modules_with_budget,
    },
    eval::{Evaluation, ObservedHeap, RuntimeFailure, Value, evaluate, evaluate_effect},
    evidence_validation::{
        EvidenceValidationFailure, ValidatedInterfaceProgram,
        validate_interface_evidence_with_budget,
    },
    interface::InterfaceConstraintBudget,
    kind::KindFailure,
    lexer::LexReason,
    module::{LoadGraphError, ModuleGraph, ModuleId, ModuleRoots, load_module_graph},
    parser::{ParseDiagnostic, ProjectionError, ResourceFailure},
    pattern::UsefulnessBudget,
    resolve::{
        DependencyExports, ResolveError, ResolveModuleError, ResolveReason,
        resolve_module_with_budget,
    },
    resolved::ResolvedModuleProgram,
    source::{SourceError, SourceFile, SourceId, Span},
    types::{IterativeTypeOwner, Type, TypeWorkBudget},
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
    /// The local `main` computation has an outstanding effect requirement.
    MainEffects,
    /// The local `main` result is not closed.
    MainOpenResult,
    /// The local `main` requires interface evidence.
    MainConstrained,
}

impl fmt::Display for EntryReason {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(match self {
            Self::MissingMain => "entry.missing-main",
            Self::MainPolymorphic => "entry.main-polymorphic",
            Self::MainDomain => "entry.main-domain",
            Self::MainEffects => "entry.main-effects",
            Self::MainOpenResult => "entry.main-open-result",
            Self::MainConstrained => "entry.main-constrained",
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
            EntryReason::MainEffects => "this main has an outstanding effect requirement",
            EntryReason::MainOpenResult => "this main result is not closed",
            EntryReason::MainConstrained => "this main requires interface evidence",
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
///
/// The owned value and type are intentionally borrow-only. In particular, a
/// caller cannot overwrite a deep structural type and trigger recursive drop:
///
/// ```compile_fail
/// use ash::{driver::Observation, types::Type};
///
/// fn overwrite(observation: &mut Observation) {
///     observation.ty = Type::Unit;
/// }
/// ```
#[derive(Clone, Debug)]
pub struct Observation {
    value: Value,
    ty: Type,
    type_display: Option<String>,
    _heap: Arc<ObservedHeap>,
}

/// An evaluated value that retains the heap needed by captured locations.
///
/// A closure can capture structural values as evaluator heap locations. This
/// owner keeps those locations valid after the containing [`Observation`] is
/// consumed.
#[derive(Clone, Debug)]
pub struct ObservationValue {
    value: Value,
    _heap: Arc<ObservedHeap>,
}

impl ObservationValue {
    /// Borrows the evaluated Ash value.
    #[must_use]
    pub const fn value(&self) -> &Value {
        &self.value
    }

    /// Returns the structural rendering of the evaluated value.
    #[must_use]
    pub fn value_display(&self) -> String {
        self.value.to_string()
    }
}

impl AsRef<Value> for ObservationValue {
    fn as_ref(&self) -> &Value {
        self.value()
    }
}

impl std::ops::Deref for ObservationValue {
    type Target = Value;

    fn deref(&self) -> &Self::Target {
        self.value()
    }
}

impl fmt::Display for ObservationValue {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&self.value, formatter)
    }
}

/// The heap-owning value and structural type consumed from an observation.
///
/// Dropping this owner dismantles an unconsumed structural type iteratively.
#[derive(Debug)]
pub struct ObservationParts {
    value: Option<ObservationValue>,
    ty: Option<Type>,
    type_display: Option<String>,
}

impl ObservationParts {
    /// Borrows the evaluated Ash value.
    #[must_use]
    pub fn value(&self) -> &Value {
        self.observation_value().value()
    }

    /// Borrows the heap-owning evaluated value.
    #[must_use]
    pub fn observation_value(&self) -> &ObservationValue {
        self.value
            .as_ref()
            .expect("observation parts retain their value until consumption")
    }

    /// Borrows the structural result type.
    #[must_use]
    pub fn ty(&self) -> &Type {
        self.ty
            .as_ref()
            .expect("observation parts retain their type until consumption")
    }

    /// Returns the structural rendering of the evaluated value.
    #[must_use]
    pub fn value_display(&self) -> String {
        self.observation_value().value_display()
    }

    /// Returns the source-facing rendering of the result type.
    #[must_use]
    pub fn type_display(&self) -> String {
        self.type_display
            .clone()
            .unwrap_or_else(|| self.ty().to_string())
    }

    /// Returns the heap-owning value and dismantles the unreturned type.
    #[must_use]
    pub fn into_value(mut self) -> ObservationValue {
        self.value
            .take()
            .expect("observation parts retain their value until consumption")
    }

    /// Returns the type and releases the unreturned value with its heap.
    ///
    /// Call [`crate::types::discard_type_iteratively`] when the returned type
    /// may contain a deep structural spine.
    #[must_use]
    pub fn into_type(mut self) -> Type {
        self.ty
            .take()
            .expect("observation parts retain their type until consumption")
    }

    /// Returns the heap-owning value and structural type together.
    ///
    /// Call [`crate::types::discard_type_iteratively`] when the returned type
    /// may contain a deep structural spine.
    #[must_use]
    pub fn into_pair(mut self) -> (ObservationValue, Type) {
        let value = self
            .value
            .take()
            .expect("observation parts retain their value until consumption");
        let ty = self
            .ty
            .take()
            .expect("observation parts retain their type until consumption");
        (value, ty)
    }
}

impl Drop for ObservationParts {
    fn drop(&mut self) {
        if let Some(ty) = self.ty.take() {
            crate::types::discard_type_iteratively(ty);
        }
    }
}

impl Observation {
    /// Borrows the evaluated Ash value while retaining its observation heap.
    #[must_use]
    pub const fn value(&self) -> &Value {
        &self.value
    }

    /// Borrows the structural type assigned to the program result.
    #[must_use]
    pub const fn ty(&self) -> &Type {
        &self.ty
    }

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

    /// Consumes the observation and returns its heap-owning evaluated value.
    ///
    /// The unreturned structural type is dismantled iteratively, including
    /// canonical application spines at the compiler work bound. The returned
    /// owner retains heap locations captured by closures.
    #[must_use]
    pub fn into_value(mut self) -> ObservationValue {
        crate::types::discard_type_iteratively(std::mem::replace(&mut self.ty, Type::Unit));
        ObservationValue {
            value: std::mem::replace(&mut self.value, Value::Unit),
            _heap: Arc::clone(&self._heap),
        }
    }

    /// Consumes the observation and returns its structural result type.
    ///
    /// Call [`crate::types::discard_type_iteratively`] when the returned type
    /// may contain a deep structural spine.
    #[must_use]
    pub fn into_type(mut self) -> Type {
        std::mem::replace(&mut self.ty, Type::Unit)
    }

    /// Consumes the observation into a heap-owning value-and-type owner.
    ///
    /// Dropping the returned owner dismantles its structural type iteratively.
    #[must_use]
    pub fn into_parts(mut self) -> ObservationParts {
        ObservationParts {
            value: Some(ObservationValue {
                value: std::mem::replace(&mut self.value, Value::Unit),
                _heap: Arc::clone(&self._heap),
            }),
            ty: Some(std::mem::replace(&mut self.ty, Type::Unit)),
            type_display: self.type_display.take(),
        }
    }
}

impl Drop for Observation {
    fn drop(&mut self) {
        crate::types::discard_type_iteratively(std::mem::replace(&mut self.ty, Type::Unit));
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
    /// Total resolved kind checking rejected the source or lost an invariant.
    Kind(KindFailure),
    /// Typed elaboration rejected the source or lost an invariant.
    Typing(TypeError),
    /// The entry module violated the local `main` contract.
    Entry(EntryFailure),
    /// Linked interface evidence failed authentication before Core synthesis.
    EvidenceValidation(EvidenceValidationFailure),
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
            Self::Kind(error) => error.reason_code(),
            Self::Typing(TypeError::Source(diagnostic)) => diagnostic.reason.to_string(),
            Self::Typing(TypeError::Interface(diagnostic)) => diagnostic.reason.to_string(),
            Self::Typing(TypeError::Mismatch(_)) => "type.mismatch".into(),
            Self::Typing(TypeError::Internal(failure)) => failure.reason_code().into(),
            Self::Entry(failure) => failure.reason().to_string(),
            Self::EvidenceValidation(failure) => failure.reason().to_string(),
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
                    | ResolveReason::ConstraintResourceExhausted
                    | ResolveReason::InternalState
            ),
            Self::Kind(error) => error.is_source_rejection(),
            Self::Typing(
                TypeError::Source(_) | TypeError::Interface(_) | TypeError::Mismatch(_),
            ) => true,
            Self::Entry(_) => true,
            Self::SourceModel(_)
            | Self::Projection(_)
            | Self::Typing(TypeError::Internal(_))
            | Self::EvidenceValidation(_)
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
            Self::Kind(_) => "resolved-kind failure",
            Self::Typing(_) => "typed-elaboration failure",
            Self::Entry(_) => "entry-contract failure",
            Self::EvidenceValidation(_) => "interface-evidence validation failure",
            Self::Validation(_) => "Core validation failure",
            Self::Runtime(_) => "runtime failure",
        })
    }
}

impl Error for PipelineFailure {}

/// A pipeline failure and its admitted compile-time source context.
///
/// Runtime failures carry no source catalogue. Only the graph-owning driver
/// attaches sources, by moving them after a compile-time failure.
#[derive(Debug)]
pub struct PipelineDiagnostic {
    failure: PipelineFailure,
    sources: Box<[SourceFile]>,
}

impl PipelineDiagnostic {
    /// Returns the unchanged phase failure.
    #[must_use]
    pub const fn failure(&self) -> &PipelineFailure {
        &self.failure
    }

    /// Consumes context when a caller needs only the semantic phase failure.
    #[must_use]
    pub fn into_failure(self) -> PipelineFailure {
        self.failure
    }
}

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
    Pipeline(PipelineDiagnostic),
}

impl From<PipelineFailure> for FileFailure {
    fn from(failure: PipelineFailure) -> Self {
        Self::Pipeline(PipelineDiagnostic {
            failure,
            sources: Box::default(),
        })
    }
}

impl FileFailure {
    /// Borrows the underlying phase failure, when graph loading succeeded.
    #[must_use]
    pub fn pipeline_failure(&self) -> Option<&PipelineFailure> {
        match self {
            Self::Pipeline(context) => Some(&context.failure),
            _ => None,
        }
    }

    /// Returns sources retained for a compile-time pipeline diagnostic.
    /// Input failures and runtime reports do not acquire a source catalogue.
    #[must_use]
    pub fn sources(&self) -> &[SourceFile] {
        match self {
            Self::Pipeline(context) => &context.sources,
            _ => &[],
        }
    }

    /// Reports whether this failure rejects Ash source rather than invocation,
    /// input, compiler, or runtime state.
    #[must_use]
    pub fn is_source_rejection(&self) -> bool {
        match self {
            Self::Graph(error) => error.is_source_rejection(),
            Self::Pipeline(context) => context.failure.is_source_rejection(),
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
            Self::Pipeline(context) => context.failure.reason_code(),
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
            Self::Pipeline(context) => context.failure.fmt(formatter),
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
    run_path_with_consumers_internal(
        configuration,
        &mut InterfaceConstraintBudget::default(),
        validate_interface_evidence_with_budget,
        validate_modules,
        evaluate,
        true,
    )
}

#[cfg(test)]
fn run_path_with_consumers<I, V, E>(
    configuration: RunConfiguration,
    interface_validator: I,
    validator: V,
    evaluator: E,
) -> Result<Observation, FileFailure>
where
    I: FnOnce(
        ResolvedModuleProgram,
        &mut InterfaceConstraintBudget,
        &mut TypeWorkBudget,
    ) -> Result<ValidatedInterfaceProgram, EvidenceValidationFailure>,
    V: FnOnce(
        UnvalidatedProgram,
        &[&SourceFile],
        &[(ModuleId, SourceId)],
    ) -> Result<ValidatedProgram, ValidationError>,
    E: FnOnce(&ValidatedProgram) -> Result<Evaluation, RuntimeFailure>,
{
    run_path_with_consumers_internal(
        configuration,
        &mut InterfaceConstraintBudget::default(),
        interface_validator,
        validator,
        evaluator,
        false,
    )
}

#[cfg(test)]
fn run_path_with_consumers_and_constraint_budget<I, V, E>(
    configuration: RunConfiguration,
    constraint_work: &mut InterfaceConstraintBudget,
    interface_validator: I,
    validator: V,
    evaluator: E,
) -> Result<Observation, FileFailure>
where
    I: FnOnce(
        ResolvedModuleProgram,
        &mut InterfaceConstraintBudget,
        &mut TypeWorkBudget,
    ) -> Result<ValidatedInterfaceProgram, EvidenceValidationFailure>,
    V: FnOnce(
        UnvalidatedProgram,
        &[&SourceFile],
        &[(ModuleId, SourceId)],
    ) -> Result<ValidatedProgram, ValidationError>,
    E: FnOnce(&ValidatedProgram) -> Result<Evaluation, RuntimeFailure>,
{
    run_path_with_consumers_internal(
        configuration,
        constraint_work,
        interface_validator,
        validator,
        evaluator,
        false,
    )
}

fn run_path_with_consumers_internal<I, V, E>(
    configuration: RunConfiguration,
    constraint_work: &mut InterfaceConstraintBudget,
    interface_validator: I,
    validator: V,
    evaluator: E,
    select_effect_core: bool,
) -> Result<Observation, FileFailure>
where
    I: FnOnce(
        ResolvedModuleProgram,
        &mut InterfaceConstraintBudget,
        &mut TypeWorkBudget,
    ) -> Result<ValidatedInterfaceProgram, EvidenceValidationFailure>,
    V: FnOnce(
        UnvalidatedProgram,
        &[&SourceFile],
        &[(ModuleId, SourceId)],
    ) -> Result<ValidatedProgram, ValidationError>,
    E: FnOnce(&ValidatedProgram) -> Result<Evaluation, RuntimeFailure>,
{
    let graph = load_module_graph(&configuration.entry, &configuration.roots)
        .map_err(FileFailure::Graph)?;
    let result = run_graph_with_consumers(
        &graph,
        constraint_work,
        interface_validator,
        validator,
        evaluator,
        select_effect_core,
    );
    match result {
        Err(FileFailure::Pipeline(mut context))
            if !matches!(context.failure, PipelineFailure::Runtime(_)) =>
        {
            context.sources = graph.into_sources();
            Err(FileFailure::Pipeline(context))
        }
        other => other,
    }
}

fn run_graph_with_consumers<I, V, E>(
    graph: &ModuleGraph,
    constraint_work: &mut InterfaceConstraintBudget,
    interface_validator: I,
    validator: V,
    evaluator: E,
    select_effect_core: bool,
) -> Result<Observation, FileFailure>
where
    I: FnOnce(
        ResolvedModuleProgram,
        &mut InterfaceConstraintBudget,
        &mut TypeWorkBudget,
    ) -> Result<ValidatedInterfaceProgram, EvidenceValidationFailure>,
    V: FnOnce(
        UnvalidatedProgram,
        &[&SourceFile],
        &[(ModuleId, SourceId)],
    ) -> Result<ValidatedProgram, ValidationError>,
    E: FnOnce(&ValidatedProgram) -> Result<Evaluation, RuntimeFailure>,
{
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
            .map_err(FileFailure::from)?;
        let resolved = resolve_module_with_budget(
            module,
            &dependencies,
            &mut resolution_type_work,
            constraint_work,
        )
        .map_err(|error| match error {
            ResolveModuleError::Resolution(error) => PipelineFailure::Resolution(error),
            ResolveModuleError::Kind(error) => PipelineFailure::Kind(error),
        })
        .map_err(FileFailure::from)?;
        drop(dependencies);
        let checked_module = check_module_with_budget(
            resolved,
            &mut checking_type_work,
            &mut coverage_work,
            constraint_work,
        )
        .map_err(PipelineFailure::Typing)
        .map_err(FileFailure::from)?;
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
            FileFailure::from(PipelineFailure::Entry(EntryFailure::new(
                EntryReason::MissingMain,
                entry.span(),
            )))
        })?;
    let main_span = main.origin.primary_span();
    if !main.scheme.type_parameters.is_empty() {
        return Err(entry_failure(EntryReason::MainPolymorphic, main_span));
    }
    let (result_type, main_has_effects) = match &main.scheme.value_type {
        Type::Forall(_, _) => {
            return Err(entry_failure(EntryReason::MainPolymorphic, main_span));
        }
        Type::Function(domain, result) if matches!(domain.as_ref(), Type::Unit) => {
            (result.as_ref(), false)
        }
        Type::EffectfulFunction(domain, computation) if matches!(domain.as_ref(), Type::Unit) => {
            (computation.value(), !computation.effects().is_empty())
        }
        Type::Function(_, _)
        | Type::EffectfulFunction(_, _)
        | Type::Int
        | Type::Bool
        | Type::Unit
        | Type::Tuple(_)
        | Type::Nominal(_)
        | Type::Application(_, _)
        | Type::Variable(_)
        | Type::Inference(_) => {
            return Err(entry_failure(EntryReason::MainDomain, main_span));
        }
    };
    if main_has_effects {
        return Err(entry_failure(EntryReason::MainEffects, main_span));
    }
    if !closed_entry_result(result_type) {
        return Err(entry_failure(EntryReason::MainOpenResult, main_span));
    }
    if !main.scheme.requirements.is_empty() {
        return Err(entry_failure(EntryReason::MainConstrained, main_span));
    }
    let linked = link_modules_with_budget(checked, graph.entry(), constraint_work)
        .map_err(PipelineFailure::Typing)
        .map_err(FileFailure::from)?;
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
    let mut linked_type_work = TypeWorkBudget::default();
    let (ty, type_display, unchecked): (IterativeTypeOwner, String, UnvalidatedProgram) = {
        let validated_interfaces =
            interface_validator(linked, constraint_work, &mut linked_type_work)
                .map_err(PipelineFailure::EvidenceValidation)
                .map_err(FileFailure::from)?;
        let registry = Arc::clone(validated_interfaces.registry());
        if select_effect_core
            && checked_program_contains_effect_syntax(&validated_interfaces, &mut linked_type_work)
                .map_err(PipelineFailure::Typing)
                .map_err(FileFailure::from)?
        {
            return finish_effect_observation(&validated_interfaces, &sources, &module_sources);
        }
        let mut elaborator = Elaborator::for_module_program(&validated_interfaces)
            .map_err(TypeError::Internal)
            .map_err(PipelineFailure::Typing)
            .map_err(FileFailure::from)?;
        let typed = if select_effect_core {
            elaborator.synthesize_module_program_after_effect_scan(&validated_interfaces)
        } else {
            elaborator.synthesize_module_program(&validated_interfaces)
        }
        .map_err(PipelineFailure::Typing)
        .map_err(FileFailure::from)?;
        let ty = IterativeTypeOwner::new(typed.ty);
        let type_display = registry.display_type(&ty);
        let unchecked = elaborator
            .finish(typed.node)
            .map_err(TypeError::Internal)
            .map_err(PipelineFailure::Typing)
            .map_err(FileFailure::from)?;
        ::std::mem::drop(validated_interfaces);
        (ty, type_display, unchecked)
    };
    finish_observation(
        ty,
        type_display,
        unchecked,
        &sources,
        &module_sources,
        validator,
        evaluator,
    )
}

// Keep later Effect-phase temporaries out of the source-checking caller's frame.
fn finish_effect_observation(
    validated_interfaces: &ValidatedInterfaceProgram,
    sources: &[&SourceFile],
    module_sources: &[(ModuleId, SourceId)],
) -> Result<Observation, FileFailure> {
    let mut elaborator = EffectElaborator::for_module_program(validated_interfaces)
        .map_err(TypeError::Internal)
        .map_err(PipelineFailure::Typing)
        .map_err(FileFailure::from)?;
    let typed = elaborator
        .synthesize_effect_module_program(validated_interfaces)
        .map_err(PipelineFailure::Typing)
        .map_err(FileFailure::from)?;
    let ty = IterativeTypeOwner::new(typed.ty);
    let type_display = validated_interfaces.registry().display_type(&ty);
    let unchecked = elaborator
        .finish(typed.node)
        .map_err(TypeError::Internal)
        .map_err(PipelineFailure::Typing)
        .map_err(FileFailure::from)?;
    let validated = validate_effect_modules(unchecked, sources, module_sources)
        .map_err(PipelineFailure::Validation)
        .map_err(FileFailure::from)?;
    let evaluation = evaluate_effect(&validated)
        .map_err(PipelineFailure::Runtime)
        .map_err(FileFailure::from)?;
    let (value, heap) = evaluation.into_observation_parts();
    Ok(Observation {
        value,
        ty: ty.into_inner(),
        type_display: Some(type_display),
        _heap: heap,
    })
}

fn finish_observation<V, E>(
    ty: IterativeTypeOwner,
    type_display: String,
    unchecked: UnvalidatedProgram,
    sources: &[&SourceFile],
    module_sources: &[(ModuleId, SourceId)],
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
    let validated = validator(unchecked, sources, module_sources)
        .map_err(PipelineFailure::Validation)
        .map_err(FileFailure::from)?;
    let evaluation = evaluator(&validated)
        .map_err(PipelineFailure::Runtime)
        .map_err(FileFailure::from)?;
    let (value, heap) = evaluation.into_observation_parts();
    Ok(Observation {
        value,
        ty: ty.into_inner(),
        type_display: Some(type_display),
        _heap: heap,
    })
}

fn entry_failure(reason: EntryReason, primary: Span) -> FileFailure {
    FileFailure::from(PipelineFailure::Entry(EntryFailure::new(reason, primary)))
}

fn internal_file_failure() -> FileFailure {
    FileFailure::from(PipelineFailure::Typing(TypeError::Internal(
        crate::elaborate::ElaborationFailure::InvalidState,
    )))
}

fn closed_entry_result(root: &Type) -> bool {
    let mut work = vec![root];
    while let Some(ty) = work.pop() {
        match ty {
            Type::Variable(_) | Type::Inference(_) | Type::Forall(_, _) => return false,
            Type::Tuple(elements) => work.extend(elements),
            Type::Application(function, argument) => {
                work.push(argument);
                work.push(function);
            }
            Type::Function(domain, codomain) => {
                work.push(codomain);
                work.push(domain);
            }
            Type::EffectfulFunction(domain, codomain) => {
                if codomain.effects().tail().is_some() {
                    return false;
                }
                for instance in codomain.effects().known() {
                    work.extend(instance.arguments());
                }
                work.push(codomain.value());
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
        cell::{Cell, RefCell},
        fs,
        path::PathBuf,
        sync::atomic::{AtomicU64, Ordering},
    };

    use super::*;
    use crate::{
        source::{ByteRange, Origin},
        types::{InferenceVariableId, NominalTypeId, TypeVariableId},
    };

    static TEST_SOURCE_IDS: AtomicU64 = AtomicU64::new(0);

    struct TestSource(PathBuf);

    impl TestSource {
        fn write(text: &str) -> Self {
            loop {
                let id = TEST_SOURCE_IDS.fetch_add(1, Ordering::Relaxed);
                let directory = std::env::temp_dir()
                    .join(format!("ash-driver-unit-{}-{id}", std::process::id()));
                match fs::create_dir(&directory) {
                    Ok(()) => {
                        let path = directory.join("entry.ash");
                        fs::write(&path, text).expect("the modular fixture should be writable");
                        return Self(path);
                    }
                    Err(error) if error.kind() == io::ErrorKind::AlreadyExists => continue,
                    Err(error) => panic!("the modular fixture should be creatable: {error}"),
                }
            }
        }

        fn write_sibling(&self, name: &str, text: &str) {
            let path = self
                .0
                .parent()
                .expect("the modular fixture should have a parent")
                .join(name);
            fs::write(path, text).expect("the dependency fixture should be writable");
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
            if let Some(directory) = self.0.parent() {
                let _ = fs::remove_dir_all(directory);
            }
        }
    }

    fn relational_interface_graph_source() -> TestSource {
        let source = TestSource::write(include_str!(
            "../tests/fixtures/relational-interfaces/linked-composite/entry.ash"
        ));
        for (name, contents) in [
            (
                "base.ash",
                include_str!("../tests/fixtures/relational-interfaces/linked-composite/base.ash"),
            ),
            (
                "short.ash",
                include_str!("../tests/fixtures/relational-interfaces/linked-composite/short.ash"),
            ),
            (
                "long_one.ash",
                include_str!(
                    "../tests/fixtures/relational-interfaces/linked-composite/long_one.ash"
                ),
            ),
            (
                "long_two.ash",
                include_str!(
                    "../tests/fixtures/relational-interfaces/linked-composite/long_two.ash"
                ),
            ),
        ] {
            source.write_sibling(name, contents);
        }
        source
    }

    fn public_route_declarations(width: usize) -> String {
        let mut source = String::new();
        for index in 0..width {
            source.push_str(&format!(
                "pub interface Marker{index}<A> {{\nmark{index} : A -> A\n}}\n\n\
                 pub impl Marker{index}<Int> {{\nmark{index} value = value\n}}\n\n"
            ));
        }
        source
    }

    fn public_interface_declarations(width: usize) -> String {
        let mut source = String::new();
        for index in 0..width {
            source.push_str(&format!(
                "pub interface Marker{index}<A> {{\nmark{index} : A -> A\n}}\n\n"
            ));
        }
        source
    }

    fn public_route_reexports(module: &str, width: usize) -> String {
        let mut selected = Vec::with_capacity(width * 3);
        let mut repeated_implementations = Vec::with_capacity(width);
        for index in 0..width {
            selected.push(format!("Marker{index}"));
            selected.push(format!("mark{index}"));
            selected.push(format!("impl Marker{index}"));
            repeated_implementations.push(format!("impl Marker{index}"));
        }
        format!(
            "pub import {module} ({})\npub import {module} ({})\n",
            selected.join(", "),
            repeated_implementations.join(", ")
        )
    }

    fn deep_wide_public_route_source(depth: usize, width: usize) -> TestSource {
        assert!(depth > 0);
        assert!(width > 0);
        let last_layer = format!("layer{}", depth - 1);
        let entry = format!(
            "{}main : Unit -> Int\nmain () = mark0(42)\n",
            public_route_reexports(&last_layer, width)
        );
        let source = TestSource::write(&entry);
        source.write_sibling("base.ash", &public_route_declarations(width));
        let mut dependency = String::from("base");
        for layer in 0..depth {
            let module = format!("layer{layer}");
            source.write_sibling(
                &format!("{module}.ash"),
                &public_route_reexports(&dependency, width),
            );
            dependency = module;
        }
        source
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
    fn runtime_failures_do_not_retain_compile_time_sources() {
        let source = TestSource::write("main : Unit -> Int\nmain () = 1\n");
        let failure = run_path_with_consumers(
            source.configuration(),
            validate_interface_evidence_with_budget,
            validate_modules,
            |_| Err(RuntimeFailure::InvalidControlState),
        )
        .expect_err("injected runtime failure");
        assert!(matches!(
            failure.pipeline_failure(),
            Some(PipelineFailure::Runtime(
                RuntimeFailure::InvalidControlState
            ))
        ));
        assert!(failure.sources().is_empty());
        assert!(!failure.is_source_rejection());
    }

    #[test]
    fn compile_failure_can_render_after_the_input_has_been_removed() {
        let text = include_str!("../tests/fixtures/first-stratum/type/binding-initializer.ash");
        let source = TestSource::write(text);
        let path = source.configuration().entry;
        let failure = run_path(source.configuration()).expect_err("wrong initializer type");
        drop(source);
        assert!(!path.exists());
        let Some(PipelineFailure::Typing(TypeError::Source(diagnostic))) =
            failure.pipeline_failure()
        else {
            panic!("expected the original type error");
        };
        let sources: Vec<_> = failure.sources().iter().collect();
        assert_eq!(sources[0].text(), text);
        let view = crate::presentation::compile_type_diagnostic(diagnostic, &sources).unwrap();
        let catalogue = crate::message::Catalogue::new(crate::message::Locale::English).unwrap();
        let mut output = Vec::new();
        crate::presentation::write_human(&mut output, &view, &catalogue).unwrap();
        assert!(
            String::from_utf8(output)
                .unwrap()
                .contains("let value : Bool = 1")
        );
    }

    #[test]
    fn injected_validation_failure_stops_before_evaluation() {
        let source = TestSource::write("main : Unit -> Int\nmain () = 1\n");
        let evaluation_called = Cell::new(false);

        let failure = run_path_with_consumers(
            source.configuration(),
            validate_interface_evidence_with_budget,
            |unchecked, _, _| validate_modules(unchecked, &[], &[]),
            |_| {
                evaluation_called.set(true);
                panic!("evaluation must not run after validation fails")
            },
        )
        .expect_err("omitting the admitted source must fail provenance validation");

        let PipelineFailure::Validation(error) =
            failure.pipeline_failure().expect("pipeline failure")
        else {
            panic!("the injected validator failure should retain its stage");
        };
        assert_eq!(error.reason(), crate::core::ValidationReason::Provenance);
        assert!(!evaluation_called.get());
    }

    fn deep_observation_type(depth: usize) -> Type {
        let mut ty = Type::Nominal(NominalTypeId::new(ModuleId::new(0), 0));
        for _ in 0..depth {
            ty = Type::Application(Box::new(ty), Box::new(Type::Unit));
        }
        ty
    }

    fn unit_program(source: &SourceFile) -> UnvalidatedProgram {
        let origin = Origin::Source(
            source
                .span(ByteRange::new(0, 2).expect("ordered range"))
                .expect("fixture span"),
        );
        let mut builder = crate::core::CoreBuilder::new();
        let root = builder
            .unit(Type::Unit, origin)
            .expect("the unit program should fit");
        builder.finish(root).expect("the unit root is present")
    }

    #[test]
    fn downstream_validation_failure_discards_deep_result_type_iteratively() {
        std::thread::Builder::new()
            .name("pipeline-validation-type-owner".into())
            .stack_size(256 * 1024)
            .spawn(|| {
                const DEPTH: usize = 32_000;
                let source = SourceFile::new("pipeline-validation.ash", "()")
                    .expect("the fixture should fit");
                let program = unit_program(&source);
                let error = finish_observation(
                    IterativeTypeOwner::new(deep_observation_type(DEPTH)),
                    "Deep".into(),
                    program,
                    &[&source],
                    &[],
                    |unchecked, _, _| validate_modules(unchecked, &[], &[]),
                    |_| panic!("evaluation must not run after validation failure"),
                )
                .expect_err("omitting the source rejects Core provenance");
                assert!(matches!(
                    error.pipeline_failure(),
                    Some(PipelineFailure::Validation(_))
                ));
            })
            .expect("small-stack pipeline thread should start")
            .join()
            .expect("validator failure must dismantle the result type iteratively");
    }

    #[test]
    fn downstream_evaluator_failure_discards_deep_result_type_iteratively() {
        std::thread::Builder::new()
            .name("pipeline-evaluator-type-owner".into())
            .stack_size(256 * 1024)
            .spawn(|| {
                const DEPTH: usize = 32_000;
                let source = SourceFile::new("pipeline-evaluator.ash", "()")
                    .expect("the fixture should fit");
                let program = unit_program(&source);
                let error = finish_observation(
                    IterativeTypeOwner::new(deep_observation_type(DEPTH)),
                    "Deep".into(),
                    program,
                    &[&source],
                    &[],
                    |unchecked, sources, _| crate::core::validate(unchecked, sources),
                    |_| Err(RuntimeFailure::InvalidControlState),
                )
                .expect_err("the injected evaluator failure is preserved");
                assert!(matches!(
                    error.pipeline_failure(),
                    Some(PipelineFailure::Runtime(
                        RuntimeFailure::InvalidControlState
                    ))
                ));
            })
            .expect("small-stack pipeline thread should start")
            .join()
            .expect("evaluator failure must dismantle the result type iteratively");
    }

    #[test]
    fn injected_evidence_failure_stops_before_core_synthesis_consumers() {
        let source = TestSource::write(concat!(
            "interface Equal<A> {\n",
            "equal : (A, A) -> Bool\n",
            "}\n",
            "main : Unit -> Int\n",
            "main () = 1\n",
        ));
        let core_validation_called = Cell::new(false);
        let evaluation_called = Cell::new(false);

        let failure = run_path_with_consumers(
            source.configuration(),
            |mut linked, budget, type_work| {
                let module = linked
                    .groups()
                    .first()
                    .expect("the fixture should retain one linked group")
                    .module();
                assert!(linked.replace_first_interface_fact_id_for_test(
                    module,
                    crate::interface::InterfaceId::new(module, u32::MAX),
                ));
                validate_interface_evidence_with_budget(linked, budget, type_work)
            },
            |_, _, _| {
                core_validation_called.set(true);
                panic!("Core validation must not run after evidence validation fails")
            },
            |_| {
                evaluation_called.set(true);
                panic!("evaluation must not run after evidence validation fails")
            },
        )
        .expect_err("the forged linked interface identity should fail evidence validation");

        let PipelineFailure::EvidenceValidation(error) =
            failure.pipeline_failure().expect("pipeline failure")
        else {
            panic!("the injected evidence validator failure should retain its stage");
        };
        assert_eq!(
            error.reason(),
            crate::evidence_validation::EvidenceValidationReason::UnknownIdentity,
        );
        assert!(!core_validation_called.get());
        assert!(!evaluation_called.get());
    }

    #[test]
    fn independent_core_validation_starts_with_only_the_core_registry_owner() {
        let source = TestSource::write("main : Unit -> Int\nmain () = 42\n");
        let registry_lifetime = RefCell::new(None);

        let observation = run_path_with_consumers(
            source.configuration(),
            |linked, budget, type_work| {
                let validated =
                    validate_interface_evidence_with_budget(linked, budget, type_work)?;
                registry_lifetime
                    .borrow_mut()
                    .replace(Arc::downgrade(validated.registry()));
                Ok(validated)
            },
            |unchecked, sources, module_sources| {
                let registry_lifetime = registry_lifetime.borrow();
                let registry = registry_lifetime
                    .as_ref()
                    .expect("interface validation should record the resolved registry");
                assert_eq!(
                    registry.strong_count(),
                    1,
                    "only the unchecked Core program may own the registry when Core validation begins"
                );
                validate_modules(unchecked, sources, module_sources)
            },
            evaluate,
        )
        .expect("the ownership witness should complete the real pipeline");

        assert_eq!(observation.value_display(), "42");
    }

    #[test]
    fn exact_constraint_budget_persists_through_evidence_validation() {
        let source = TestSource::write(concat!(
            "import dependency as Dependency\n",
            "import dependency (impl Equal)\n",
            "main : Unit -> Int\n",
            "main () = Dependency.equal(42)\n",
        ));
        source.write_sibling(
            "dependency.ash",
            concat!(
                "pub interface Equal<A> {\n",
                "equal : A -> A\n",
                "}\n",
                "pub impl Equal<Int> {\n",
                "equal value = value\n",
                "}\n",
            ),
        );

        let validation_prefix = Cell::new(0);
        let mut measured = InterfaceConstraintBudget::default();
        let observation = run_path_with_consumers_and_constraint_budget(
            source.configuration(),
            &mut measured,
            |linked, budget, type_work| {
                validation_prefix.set(budget.used());
                validate_interface_evidence_with_budget(linked, budget, type_work)
            },
            validate_modules,
            evaluate,
        )
        .expect("the fixture should fit the default graph-wide constraint budget");
        assert_eq!(observation.value_display(), "42");
        let exact = measured.used();
        assert!(validation_prefix.get() > 0);
        assert!(validation_prefix.get() < exact);

        let one_short_entered_validation = Cell::new(false);
        let mut one_short = InterfaceConstraintBudget::with_limit(exact - 1);
        let failure = run_path_with_consumers_and_constraint_budget(
            source.configuration(),
            &mut one_short,
            |linked, budget, type_work| {
                one_short_entered_validation.set(true);
                validate_interface_evidence_with_budget(linked, budget, type_work)
            },
            validate_modules,
            evaluate,
        )
        .expect_err("one less than the cumulative work must exhaust validation");
        assert!(one_short_entered_validation.get());
        let PipelineFailure::EvidenceValidation(error) =
            failure.pipeline_failure().expect("pipeline failure")
        else {
            panic!("the one-short cumulative budget should fail in evidence validation");
        };
        assert_eq!(
            error.reason(),
            crate::evidence_validation::EvidenceValidationReason::ConstraintResourceExhausted,
        );

        let mut exact_budget = InterfaceConstraintBudget::with_limit(exact);
        let observation = run_path_with_consumers_and_constraint_budget(
            source.configuration(),
            &mut exact_budget,
            validate_interface_evidence_with_budget,
            validate_modules,
            evaluate,
        )
        .expect("the measured cumulative work should fit exactly");
        assert_eq!(observation.value_display(), "42");
        assert_eq!(exact_budget.used(), exact);
    }

    #[test]
    fn relational_interface_graph_has_an_exact_cross_stage_boundary() {
        // Each checked boundary includes the module's body-free summary
        // publication. The fixed graph order is base, short facade, first long
        // facade, second long facade, then entry; linking and linked evidence
        // validation contribute the final two additive boundaries.
        // Producer authentication adds 329, 317, 317, 318, and 3 cells to
        // checking. Shared capture visits remove 72, 72, 74, and 73 repeated
        // nominal-retention cells from the four importers. Linking still
        // contributes 149 cells; linked-evidence validation contributes 1660.
        // Shared type-clone preflights remove 24 checking cells in the base
        // and 12 in each importer, without changing retained type work.
        const EXPECTED_BOUNDARIES: [usize; 13] = [
            0, 1, 1_134, 1_697, 2_286, 2_849, 3_438, 3_993, 4_587, 5_572, 5_988, 6_137, 7_797,
        ];
        const EXACT_CONSTRAINT_WORK: usize =
            6_876 + (329 + 317 + 317 + 318 + 3) - (72 + 72 + 74 + 73) - (24 + 4 * 12);
        let source = relational_interface_graph_source();
        let directory = source
            .0
            .parent()
            .expect("the relational fixture should have a directory");
        let input_paths = [
            "base.ash",
            "short.ash",
            "long_one.ash",
            "long_two.ash",
            "entry.ash",
        ]
        .map(|name| directory.join(name));
        let input_before = input_paths
            .iter()
            .map(|path| fs::read(path).expect("each relational input should remain readable"))
            .collect::<Vec<_>>();
        let graph = load_module_graph(&source.0, &ModuleRoots::empty())
            .expect("the relational interface graph should load");
        let mut checked: Vec<crate::resolved::CheckedModule> = Vec::new();
        let mut checked_by_module: HashMap<ModuleId, usize> = HashMap::new();
        let mut resolution_type_work = TypeWorkBudget::unbounded();
        let mut checking_type_work = TypeWorkBudget::unbounded();
        let mut coverage_work = UsefulnessBudget::default();
        let mut measured = InterfaceConstraintBudget::with_limit(usize::MAX);
        let mut boundaries = vec![measured.used()];
        for module in graph.modules() {
            let dependencies = module
                .dependencies()
                .iter()
                .map(|edge| {
                    let index = checked_by_module
                        .get(&edge.target())
                        .expect("dependency order should publish each summary first");
                    DependencyExports::new(edge, checked[*index].exports())
                        .expect("the retained dependency summary should match its edge")
                })
                .collect::<Vec<_>>();
            let resolved = resolve_module_with_budget(
                module,
                &dependencies,
                &mut resolution_type_work,
                &mut measured,
            )
            .expect("relational resolution should fit");
            boundaries.push(measured.used());
            drop(dependencies);
            let checked_module = check_module_with_budget(
                resolved,
                &mut checking_type_work,
                &mut coverage_work,
                &mut measured,
            )
            .expect("relational checking and summary publication should fit");
            boundaries.push(measured.used());
            checked_by_module.insert(module.id(), checked.len());
            checked.push(checked_module);
        }
        let linked = link_modules_with_budget(checked, graph.entry(), &mut measured)
            .expect("the complete relational graph should link");
        boundaries.push(measured.used());
        let validated_interfaces = validate_interface_evidence_with_budget(
            linked,
            &mut measured,
            &mut TypeWorkBudget::unbounded(),
        )
        .expect("the complete relational evidence graph should validate");
        boundaries.push(measured.used());
        assert_eq!(boundaries, EXPECTED_BOUNDARIES);

        let mut elaborator = Elaborator::for_module_program(&validated_interfaces)
            .expect("the relational Core namespace should fit");
        let typed = elaborator
            .synthesize_module_program(&validated_interfaces)
            .expect("validated relational evidence should lower to Core");
        let unchecked = elaborator
            .finish(typed.node)
            .expect("the relational Core root should finish");
        drop(validated_interfaces);
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
        drop(
            validate_modules(unchecked, &sources, &module_sources)
                .expect("independent Core validation should accept the exact relational graph"),
        );

        let validation_prefix = Cell::new(0);
        let core_validation_called = Cell::new(false);
        let mut exact = InterfaceConstraintBudget::with_limit(EXACT_CONSTRAINT_WORK);
        let observation = run_path_with_consumers_and_constraint_budget(
            source.configuration(),
            &mut exact,
            |linked, budget, type_work| {
                validation_prefix.set(budget.used());
                validate_interface_evidence_with_budget(linked, budget, type_work)
            },
            |unchecked, sources, module_sources| {
                core_validation_called.set(true);
                validate_modules(unchecked, sources, module_sources)
            },
            evaluate,
        )
        .expect("the exact relational cross-stage boundary should fit");
        assert_eq!(observation.value_display(), "42");
        assert_eq!(validation_prefix.get(), EXPECTED_BOUNDARIES[11]);
        assert!(core_validation_called.get());
        assert_eq!(exact.used(), EXACT_CONSTRAINT_WORK);
        drop(observation);

        let one_short_entered_validation = Cell::new(false);
        let one_short_reached_core = Cell::new(false);
        let mut one_short = InterfaceConstraintBudget::with_limit(EXACT_CONSTRAINT_WORK - 1);
        let failure = run_path_with_consumers_and_constraint_budget(
            source.configuration(),
            &mut one_short,
            |linked, budget, type_work| {
                one_short_entered_validation.set(true);
                validate_interface_evidence_with_budget(linked, budget, type_work)
            },
            |_, _, _| {
                one_short_reached_core.set(true);
                panic!("one-short linked evidence must stop before Core validation")
            },
            |_| panic!("one-short linked evidence must stop before evaluation"),
        )
        .expect_err("one less relational work unit must reject atomically");
        let PipelineFailure::EvidenceValidation(error) =
            failure.pipeline_failure().expect("pipeline failure")
        else {
            panic!("the relational one-short boundary should fail in evidence validation");
        };
        assert_eq!(
            error.reason(),
            crate::evidence_validation::EvidenceValidationReason::ConstraintResourceExhausted,
        );
        assert!(one_short_entered_validation.get());
        assert!(!one_short_reached_core.get());
        assert_eq!(one_short.used(), EXACT_CONSTRAINT_WORK - 1);

        let retry_reached_core = Cell::new(false);
        let mut retry = InterfaceConstraintBudget::with_limit(EXACT_CONSTRAINT_WORK);
        let observation = run_path_with_consumers_and_constraint_budget(
            source.configuration(),
            &mut retry,
            validate_interface_evidence_with_budget,
            |unchecked, sources, module_sources| {
                retry_reached_core.set(true);
                validate_modules(unchecked, sources, module_sources)
            },
            evaluate,
        )
        .expect("the immutable relational inputs should retry at the exact boundary");
        assert_eq!(observation.value_display(), "42");
        assert!(retry_reached_core.get());
        assert_eq!(retry.used(), EXACT_CONSTRAINT_WORK);
        drop(observation);

        let input_after = input_paths
            .iter()
            .map(|path| fs::read(path).expect("each relational input should remain readable"))
            .collect::<Vec<_>>();
        assert_eq!(input_after, input_before);
    }

    #[test]
    fn wide_interface_graph_records_the_exact_validation_prefix() {
        // Keep linking just below the unchanged graph limit so the witness
        // continues to isolate validation as the first over-budget phase.
        const WIDTH: usize = (crate::interface::INTERFACE_CONSTRAINT_WORK_LIMIT - 29) / 65;
        // Dependency checking is declaration 8W + checked facts 6W +
        // selector admission 7W + summary freeze 10W + producer
        // authentication 7W. Both clone preflights charge their three type
        // cells to both ledgers. A monomorphic method
        // has no private binder payload and therefore adds no authority work.
        const DEPENDENCY_CHECKED: usize = 38 * WIDTH;
        // Entry resolution adds complete-vector summary authentication 7W, first-route
        // interface retention 9W, and one dependency-route cell.
        const ENTRY_RESOLVED: usize = 54 * WIDTH + 1;
        // Entry checking additionally authenticates the W imported interface
        // arities and visits its one global declaration before interface and
        // method admission. Producer authentication adds three cells for
        // the entry's withheld main name.
        const ENTRY_CHECKED: usize = 62 * WIDTH + 16;
        // Linking adds its W+7 graph/carrier prefix, W+5 structural
        // authentication, and the W-cell canonical-owner uniqueness index.
        // It does not repeat the 3W complete interface mirror owned by the
        // consuming evidence validator.
        const LINKED: usize = 65 * WIDTH + 28;
        // Validation owns a 49W+55 complete-application authentication suffix
        // and publishes one private method-evidence capability only after the
        // complete graph succeeds.
        const VALIDATED: usize = 114 * WIDTH + 83;
        let source = TestSource::write(concat!(
            "import dependency as Dependency\n",
            "main : Unit -> Int\n",
            "main () = 42\n",
        ));
        source.write_sibling("dependency.ash", &public_interface_declarations(WIDTH));

        let graph = load_module_graph(&source.0, &ModuleRoots::empty())
            .expect("the wide interface graph should load");
        let mut checked: Vec<crate::resolved::CheckedModule> = Vec::new();
        let mut checked_by_module: HashMap<ModuleId, usize> = HashMap::new();
        let mut resolution_type_work = TypeWorkBudget::unbounded();
        let mut checking_type_work = TypeWorkBudget::unbounded();
        let mut coverage_work = UsefulnessBudget::default();
        let mut measured = InterfaceConstraintBudget::with_limit(usize::MAX);
        let mut phase_boundaries = Vec::new();
        for module in graph.modules() {
            let dependencies = module
                .dependencies()
                .iter()
                .map(|edge| {
                    let index = checked_by_module
                        .get(&edge.target())
                        .expect("dependency order should publish the dependency first");
                    DependencyExports::new(edge, checked[*index].exports())
                        .expect("the dependency summary should match its edge")
                })
                .collect::<Vec<_>>();
            let resolved = resolve_module_with_budget(
                module,
                &dependencies,
                &mut resolution_type_work,
                &mut measured,
            )
            .expect("the unbounded resolution stage should fit");
            if !dependencies.is_empty() {
                let imported_interfaces = resolved.imported_facts().interface_imports();
                let (interface_count, authority_method_count) = imported_interfaces.fold(
                    (0usize, 0usize),
                    |(interfaces, authority_methods), imported| {
                        (
                            interfaces + 1,
                            authority_methods + imported.authority_methods().count(),
                        )
                    },
                );
                assert_eq!(interface_count, WIDTH);
                assert_eq!(
                    authority_method_count, 0,
                    "monomorphic imports must expose no checker-view authority-discovery work",
                );
            }
            phase_boundaries.push(measured.used());
            let checked_module = check_module_with_budget(
                resolved,
                &mut checking_type_work,
                &mut coverage_work,
                &mut measured,
            )
            .expect("the unbounded checking stage should fit");
            phase_boundaries.push(measured.used());
            checked_by_module.insert(module.id(), checked.len());
            checked.push(checked_module);
        }
        let linked = link_modules_with_budget(checked, graph.entry(), &mut measured)
            .expect("the unbounded link stage should fit");
        phase_boundaries.push(measured.used());
        drop(
            validate_interface_evidence_with_budget(
                linked,
                &mut measured,
                &mut TypeWorkBudget::unbounded(),
            )
            .expect("the unbounded validation stage should fit"),
        );
        phase_boundaries.push(measured.used());
        assert_eq!(
            phase_boundaries,
            [
                0,
                DEPENDENCY_CHECKED,
                ENTRY_RESOLVED,
                ENTRY_CHECKED,
                LINKED,
                VALIDATED,
            ],
        );
        const {
            assert!(LINKED < crate::interface::INTERFACE_CONSTRAINT_WORK_LIMIT);
            assert!(LINKED + 65 >= crate::interface::INTERFACE_CONSTRAINT_WORK_LIMIT);
            assert!(VALIDATED > crate::interface::INTERFACE_CONSTRAINT_WORK_LIMIT);
        }
    }

    #[test]
    fn deep_wide_public_routes_admit_and_reject_on_a_small_stack() {
        const DEPTH: usize = 48;
        const WIDTH: usize = 4;
        const STACK_SIZE: usize = 320 * 1024;

        std::thread::Builder::new()
            .name(String::from("deep-public-route-budget"))
            .stack_size(STACK_SIZE)
            .spawn(|| {
                let source = deep_wide_public_route_source(DEPTH, WIDTH);
                let mut measured = InterfaceConstraintBudget::default();
                let observation = run_path_with_consumers_and_constraint_budget(
                    source.configuration(),
                    &mut measured,
                    validate_interface_evidence_with_budget,
                    validate_modules,
                    evaluate,
                )
                .expect("the deep public routes should fit the default constraint budget");
                assert_eq!(observation.value_display(), "42");
                drop(observation);
                let exact = measured.used();
                assert!(exact > 0);

                let mut exact_budget = InterfaceConstraintBudget::with_limit(exact);
                let observation = run_path_with_consumers_and_constraint_budget(
                    source.configuration(),
                    &mut exact_budget,
                    validate_interface_evidence_with_budget,
                    validate_modules,
                    evaluate,
                )
                .expect("the measured deep-route constraint work should fit exactly");
                assert_eq!(observation.value_display(), "42");
                assert_eq!(exact_budget.used(), exact);
                drop(observation);

                let validation_entered = Cell::new(false);
                let mut one_short = InterfaceConstraintBudget::with_limit(exact - 1);
                let failure = run_path_with_consumers_and_constraint_budget(
                    source.configuration(),
                    &mut one_short,
                    |linked, budget, type_work| {
                        validation_entered.set(true);
                        validate_interface_evidence_with_budget(linked, budget, type_work)
                    },
                    validate_modules,
                    evaluate,
                )
                .expect_err("one less than the measured deep-route work must fail");
                assert!(validation_entered.get());
                let PipelineFailure::EvidenceValidation(error) = failure.pipeline_failure().expect("pipeline failure")
                else {
                    panic!("the one-short deep-route budget should fail in evidence validation");
                };
                assert_eq!(
                    error.reason(),
                    crate::evidence_validation::EvidenceValidationReason::ConstraintResourceExhausted,
                );
                drop(failure);
            })
            .expect("the small-stack route witness thread should spawn")
            .join()
            .expect("the deep public routes should admit and dispose on a small stack");
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

    #[test]
    fn consumed_closure_observation_value_retains_its_captured_structural_heap() {
        let source = TestSource::write(concat!(
            "main : Unit -> Unit -> (Int, Int)\n",
            "main () = {\n",
            "let pair = (20, 22)\n",
            "fn(ignored) {\n",
            "pair\n",
            "}\n",
            "}\n",
        ));

        let consumed = run_path(source.configuration())
            .expect("the closure should evaluate")
            .into_value();

        assert!(matches!(consumed.value(), Value::Function(_)));
        assert_eq!(consumed.value_display(), "<function>");
        assert_eq!(consumed._heap.cell_count(), 1);

        let parts = run_path(source.configuration())
            .expect("the closure should evaluate again")
            .into_parts();
        assert!(matches!(parts.value(), Value::Function(_)));
        assert_eq!(parts.observation_value()._heap.cell_count(), 1);
        let consumed = parts.into_value();
        assert!(matches!(consumed.value(), Value::Function(_)));
        assert_eq!(consumed._heap.cell_count(), 1);
    }

    #[test]
    fn observation_discards_a_canonical_application_spine_on_a_small_stack() {
        const DEPTH: usize = 32_768;

        std::thread::Builder::new()
            .name("observation-type-disposal".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let mut ty = Type::Nominal(NominalTypeId::new(ModuleId::new(0), 0));
                for _ in 0..DEPTH {
                    ty = Type::Application(Box::new(ty), Box::new(Type::Unit));
                }
                let observation = Observation {
                    value: Value::Unit,
                    ty,
                    type_display: Some("Wide<Unit>".to_owned()),
                    _heap: ObservedHeap::new(
                        Arc::new(crate::resolved::ResolvedRegistry::default()),
                        Vec::new(),
                    ),
                };
                drop(observation);
            })
            .expect("the observation disposal thread should start")
            .join()
            .expect("Observation must dismantle its canonical type iteratively");
    }

    #[test]
    fn observation_consuming_accessors_preserve_parts_and_discard_unconsumed_type() {
        const DEPTH: usize = 32_768;

        std::thread::Builder::new()
            .name("observation-consuming-accessors".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let heap = || {
                    ObservedHeap::new(
                        Arc::new(crate::resolved::ResolvedRegistry::default()),
                        Vec::new(),
                    )
                };
                let deep_type = || {
                    let mut ty = Type::Nominal(NominalTypeId::new(ModuleId::new(0), 0));
                    for _ in 0..DEPTH {
                        ty = Type::Application(Box::new(ty), Box::new(Type::Unit));
                    }
                    ty
                };

                let value = Observation {
                    value: Value::Boolean(true),
                    ty: deep_type(),
                    type_display: Some("Wide<Unit>".to_owned()),
                    _heap: heap(),
                }
                .into_value();
                assert!(matches!(value.value(), Value::Boolean(true)));

                let value = Observation {
                    value: Value::Boolean(true),
                    ty: deep_type(),
                    type_display: Some("Wide<Unit>".to_owned()),
                    _heap: heap(),
                }
                .into_parts()
                .into_value();
                assert!(matches!(value.value(), Value::Boolean(true)));

                let ty = Observation {
                    value: Value::Unit,
                    ty: Type::Int,
                    type_display: Some("Int".to_owned()),
                    _heap: heap(),
                }
                .into_type();
                assert_eq!(ty, Type::Int);

                let parts = Observation {
                    value: Value::Boolean(false),
                    ty: deep_type(),
                    type_display: Some("Wide<Unit>".to_owned()),
                    _heap: heap(),
                }
                .into_parts();
                assert!(matches!(parts.value(), Value::Boolean(false)));
                assert_eq!(parts.type_display(), "Wide<Unit>");
                let (value, ty) = parts.into_pair();
                assert!(matches!(value.value(), Value::Boolean(false)));
                assert_eq!(
                    ty.outer_nominal(),
                    Some(NominalTypeId::new(ModuleId::new(0), 0))
                );
                crate::types::discard_type_iteratively(ty);
            })
            .expect("the consuming-accessor thread should start")
            .join()
            .expect("consuming accessors must preserve selected parts and dismantle safely");
    }
}
