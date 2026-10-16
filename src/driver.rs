//! Reusable, stage-preserving Ash pipeline orchestration.

use std::{collections::HashMap, error::Error, fmt, io, path::PathBuf, sync::Arc};

use crate::{
    core::{UnvalidatedProgram, ValidatedEffectProgram, ValidatedProgram, ValidationError},
    diagnostic::{Diagnostic, SourceLabel, compare_source_spans},
    elaborate::{
        EffectElaborator, Elaborator, ProviderCodeAvailability, TypeError,
        check_module_with_budget_and_provider_codes_and_rewrite_work,
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
    module::{
        GraphDiagnostic, LoadGraphError, ModuleGraph, ModuleId, ModuleRoots, load_module_graph,
    },
    parser::{ParseDiagnostic, ProjectionError, ResourceFailure},
    pattern::UsefulnessBudget,
    resolve::{DependencyExports, ResolveError, ResolveModuleError},
    resolved::ResolvedModuleProgram,
    source::{SourceError, SourceFile, SourceId, Span},
    types::{IterativeTypeOwner, Type, TypeWorkBudget},
};

#[cfg(test)]
use crate::resolve::resolve_module_with_budget;

/// Tool-facing inputs for one modular Ash execution.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RunConfiguration {
    /// Entry module source path.
    pub entry: PathBuf,
    /// Explicit named module roots.
    pub roots: ModuleRoots,
}

type SourceProvenance = [(ModuleId, Arc<SourceFile>)];

/// An immutable, independently validated whole program prepared for evaluation.
///
/// This owner retains compiler-private Pure or Effect Core, its result type and
/// completed compilation ledger, together with the original admitted sources.
/// It contains no evaluator heap, resource owner or
/// runtime activation. Source-native interpretation requires a separate admitted
/// executable binding table. Only [`compile_path`] constructs this capability; repeated
/// [`execute`] calls use fresh evaluator state without reading source files.
///
/// This is an in-process compiler/runtime capability, not a stable Core format
/// or a linked native executable. Native program building and Core embedding are
/// separate phases; no cross-version representation compatibility is promised.
pub struct CompiledProgram {
    core: CompiledCore,
    ty: IterativeTypeOwner,
    type_display: String,
    compilation_work: crate::compiler_work::CompilationWork,
    provenance: Vec<(ModuleId, Arc<SourceFile>)>,
}

#[derive(Clone, Copy)]
enum ProvenanceRetention {
    Retain,
    Discard,
}

enum CompiledCore {
    Pure(ValidatedProgram),
    Effect(ValidatedEffectProgram),
}

struct ObservationMetadata {
    ty: IterativeTypeOwner,
    type_display: String,
}

impl CompiledProgram {
    /// Borrows the independently checked outer interpreter, never a second
    /// copied requirements vector or native executable authority.
    pub(crate) fn source_native_entry(
        &self,
    ) -> Option<(&ValidatedEffectProgram, &crate::core::NativeInterpretNode)> {
        match &self.core {
            CompiledCore::Effect(program) => {
                let crate::core::EffectExprKind::Operation(
                    crate::core::EffectOperation::NativeInterpret(boundary),
                ) = &program.node(program.root())?.kind
                else {
                    return None;
                };
                Some((program, boundary))
            }
            CompiledCore::Pure(_) => None,
        }
    }

    pub(crate) fn pure_build_input(&self) -> Option<(&ValidatedProgram, &SourceProvenance)> {
        match &self.core {
            CompiledCore::Pure(program) if !self.provenance.is_empty() => {
                Some((program, &self.provenance))
            }
            CompiledCore::Pure(_) | CompiledCore::Effect(_) => None,
        }
    }

    pub(crate) fn effect_build_input(
        &self,
    ) -> Option<(&ValidatedEffectProgram, &SourceProvenance)> {
        match &self.core {
            CompiledCore::Effect(program) if !self.provenance.is_empty() => {
                Some((program, &self.provenance))
            }
            CompiledCore::Pure(_) | CompiledCore::Effect(_) => None,
        }
    }

    /// Borrows the structural type of the checked entry result.
    #[must_use]
    pub fn ty(&self) -> &Type {
        &self.ty
    }

    /// Borrows the source-facing rendering of the checked result type.
    #[must_use]
    pub fn type_display(&self) -> &str {
        &self.type_display
    }

    /// Borrows completed compilation work; execution never adds to this ledger.
    #[must_use]
    pub const fn compilation_work(&self) -> &crate::compiler_work::CompilationWork {
        &self.compilation_work
    }
}

impl fmt::Debug for CompiledProgram {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("CompiledProgram")
            .field("type_display", &self.type_display)
            .field("compilation_work", &self.compilation_work)
            .field("source_count", &self.provenance.len())
            .finish_non_exhaustive()
    }
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
    pub(crate) fn message(&self) -> crate::message::Message<'static> {
        use crate::message::Message;
        match self.reason() {
            EntryReason::MissingMain => Message::entry_missing_main(),
            EntryReason::MainPolymorphic => Message::entry_polymorphic(),
            EntryReason::MainDomain => Message::entry_domain(),
            EntryReason::MainEffects => Message::entry_effects(),
            EntryReason::MainOpenResult => Message::entry_open_result(),
            EntryReason::MainConstrained => Message::entry_constrained(),
        }
    }

    pub(crate) fn primary_message(&self) -> (crate::message::Message<'static>, &'static str) {
        if self.reason() == EntryReason::MissingMain {
            (crate::message::Message::entry_module(), "entry_module")
        } else {
            (crate::message::Message::entry_main(), "entry_main")
        }
    }

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
    compilation_work: crate::compiler_work::CompilationWork,
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
    /// Borrows completed work assessments, including accepted optimization targets.
    /// These experimental ledgers do not measure CPU, RSS or builder-owned work.
    #[must_use]
    pub const fn compilation_work(&self) -> &crate::compiler_work::CompilationWork {
        &self.compilation_work
    }

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
            Self::Resolution(error) => error.is_source_rejection(),
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
    compilation_work: crate::compiler_work::CompilationWork,
    failure: Box<PipelineFailure>,
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
        *self.failure
    }
}

/// A file-input failure or a stage-preserving pipeline failure.
#[derive(Debug)]
pub enum FileFailure {
    /// Module graph loading failed at its owning stage.
    Graph(GraphDiagnostic),
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
            compilation_work: Default::default(),
            failure: Box::new(failure),
            sources: Box::default(),
        })
    }
}

impl FileFailure {
    /// Returns observed work, retaining completed phases and partial failure costs.
    /// Missing fields were not observed; input failures carry no compiler report.
    #[must_use]
    pub fn compilation_work(&self) -> Option<&crate::compiler_work::CompilationWork> {
        match self {
            Self::Pipeline(context) => Some(&context.compilation_work),
            _ => None,
        }
    }

    fn with_phase_work(mut self, cost: crate::compiler_work::PhaseCost) -> Self {
        if let Self::Pipeline(context) = &mut self {
            use crate::compiler_work::CompilationPhase;
            match cost.phase {
                CompilationPhase::SourceChecking => {
                    context.compilation_work.source_checking = Some(cost)
                }
                CompilationPhase::FinalElaboration => {
                    context.compilation_work.final_elaboration = Some(cost)
                }
                CompilationPhase::IndependentCore => {
                    context.compilation_work.independent_core = Some(cost)
                }
            }
        }
        self
    }

    fn with_compilation_work(mut self, costs: crate::compiler_work::CompilationWork) -> Self {
        if let Self::Pipeline(context) = &mut self {
            context.compilation_work.source_checking = context
                .compilation_work
                .source_checking
                .or(costs.source_checking);
            context.compilation_work.final_elaboration = context
                .compilation_work
                .final_elaboration
                .or(costs.final_elaboration);
            context.compilation_work.independent_core = context
                .compilation_work
                .independent_core
                .or(costs.independent_core);
        }
        self
    }

    /// Borrows the original graph-loading failure without its source context.
    #[must_use]
    pub fn graph_failure(&self) -> Option<&LoadGraphError> {
        match self {
            Self::Graph(context) => Some(context.failure()),
            _ => None,
        }
    }
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
            Self::Graph(error) => match error.failure() {
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
    let pipeline_phase = crate::calibration::Phase::start("pipeline");
    let compiled = compile_path_for_execution(configuration)?;
    let observation = execute_owned_with_consumer(compiled, evaluate, None)?;
    pipeline_phase.finish(None, 0, 0);
    Ok(observation)
}

/// Loads, checks, links and independently validates one whole Ash source graph.
///
/// Compilation performs no Ash evaluation or native resource acquisition. The
/// resulting private Core can be executed repeatedly after its sources change
/// or disappear. This does not generate or link a native program.
/// Original sources are retained through shared handles for later build
/// preparation. Retention charges two source-checking units per admitted module:
/// one provenance record reservation and one shared source handle copy.
///
/// # Errors
/// Returns the structured input and compiler-stage failures of [`run_path`],
/// retaining their original source context and observed compilation work.
pub fn compile_path(configuration: RunConfiguration) -> Result<CompiledProgram, FileFailure> {
    compile_path_with_consumers_internal(
        configuration,
        &mut InterfaceConstraintBudget::default(),
        validate_interface_evidence_with_budget,
        validate_modular_core,
        true,
        ProvenanceRetention::Retain,
    )
}

/// Authoring-only catalogue. No partial compilation or executable binding is
/// exposed; the retained Arcs are the originals used by ordinary admission.
pub(crate) fn compile_path_for_ffi(
    configuration: RunConfiguration,
) -> Result<(CompiledProgram, Vec<crate::check_ffi::CheckedForeignModule>), FileFailure> {
    let graph = load_module_graph(&configuration.entry, &configuration.roots)
        .map_err(FileFailure::Graph)?;
    let mut catalogue = Vec::new();
    let mut work = crate::compiler_work::CompilationWork::default();
    let result = compile_graph_with_report(
        &graph,
        &mut InterfaceConstraintBudget::default(),
        validate_interface_evidence_with_budget,
        validate_modular_core,
        true,
        ProvenanceRetention::Retain,
        &mut work,
        Some(&mut catalogue),
    );
    match result {
        Ok(program) => Ok((program, catalogue)),
        Err(FileFailure::Pipeline(mut context)) => {
            context.sources = graph.into_sources();
            Err(FileFailure::Pipeline(context).with_compilation_work(work))
        }
        Err(failure) => Err(failure.with_compilation_work(work)),
    }
}

fn compile_path_for_execution(
    configuration: RunConfiguration,
) -> Result<CompiledProgram, FileFailure> {
    compile_path_with_consumers_internal(
        configuration,
        &mut InterfaceConstraintBudget::default(),
        validate_interface_evidence_with_budget,
        validate_modular_core,
        true,
        ProvenanceRetention::Discard,
    )
}

/// Evaluates an already checked whole program with fresh runtime activations.
///
/// This consumes no source files and performs no compiler checking. The
/// observation retains the program's completed compilation ledger unchanged.
/// Independent observation metadata is prepared with bounded work and fallible
/// storage reservation before entering the evaluator.
///
/// # Errors
/// Returns a structured preparation or evaluation failure without compile-time
/// source context. Preparation refusal executes no Ash code or native call.
pub fn execute(program: &CompiledProgram) -> Result<Observation, FileFailure> {
    execute_with_consumer(program, evaluate, None)
}

/// Evaluates checked Core using authenticated executable foreign bindings.
///
/// The borrowed runtime authenticates original operation contracts before native
/// use and keeps retained owners quarantined until host teardown. It does not
/// compile source or generate bindings. This supports the existing experimental
/// host-registration path; it does not claim generated native-program support.
/// Observation metadata preparation precedes all native execution.
///
/// # Errors
/// Returns structured runtime, foreign-binding or conversion failures with the
/// unchanged compilation ledger and no compile-time source context.
pub fn execute_with_foreign_runtime(
    program: &CompiledProgram,
    runtime: &mut crate::foreign::runtime::ForeignRuntime,
) -> Result<Observation, FileFailure> {
    execute_with_consumer(program, evaluate, Some(runtime))
}

fn execute_with_consumer<E>(
    program: &CompiledProgram,
    evaluator: E,
    runtime: Option<&mut crate::foreign::runtime::ForeignRuntime>,
) -> Result<Observation, FileFailure>
where
    E: FnOnce(&ValidatedProgram) -> Result<Evaluation, RuntimeFailure>,
{
    let metadata = prepare_observation_metadata(program).map_err(|failure| {
        FileFailure::from(PipelineFailure::Runtime(failure))
            .with_compilation_work(program.compilation_work)
    })?;
    execute_prepared(
        &program.core,
        metadata,
        program.compilation_work,
        evaluator,
        runtime,
    )
}

fn prepare_observation_metadata(
    program: &CompiledProgram,
) -> Result<ObservationMetadata, RuntimeFailure> {
    let mut work = TypeWorkBudget::default();
    let ty = IterativeTypeOwner::new(
        crate::types::clone_type_with_budget(program.ty(), &mut work).map_err(|()| {
            observation_metadata_failure(
                crate::eval::ResourceFailureCause::ResourceAdmissionRefused,
            )
        })?,
    );
    let display_bytes = program.type_display.len();
    work.charge(display_bytes).map_err(|()| {
        RuntimeFailure::resource(crate::eval::ResourceFailure::new(
            crate::eval::ResourceFailureCause::WorkBudgetExhausted,
            crate::eval::RuntimePhase::Evaluation,
            crate::eval::RuntimeResource::WorkUnits,
            Some(display_bytes),
            Some(work.remaining()),
        ))
    })?;
    let mut type_display = String::new();
    type_display.try_reserve_exact(display_bytes).map_err(|_| {
        observation_metadata_failure(crate::eval::ResourceFailureCause::StorageReservationFailed)
    })?;
    type_display.push_str(&program.type_display);
    Ok(ObservationMetadata { ty, type_display })
}

fn observation_metadata_failure(cause: crate::eval::ResourceFailureCause) -> RuntimeFailure {
    RuntimeFailure::resource(crate::eval::ResourceFailure::new(
        cause,
        crate::eval::RuntimePhase::Evaluation,
        crate::eval::RuntimeResource::InstantiationStorage,
        None,
        None,
    ))
}

fn execute_owned_with_consumer<E>(
    program: CompiledProgram,
    evaluator: E,
    runtime: Option<&mut crate::foreign::runtime::ForeignRuntime>,
) -> Result<Observation, FileFailure>
where
    E: FnOnce(&ValidatedProgram) -> Result<Evaluation, RuntimeFailure>,
{
    let CompiledProgram {
        core,
        ty,
        type_display,
        compilation_work,
        provenance,
    } = program;
    drop(provenance);
    execute_prepared(
        &core,
        ObservationMetadata { ty, type_display },
        compilation_work,
        evaluator,
        runtime,
    )
}

fn execute_prepared<E>(
    core: &CompiledCore,
    metadata: ObservationMetadata,
    compilation_work: crate::compiler_work::CompilationWork,
    evaluator: E,
    runtime: Option<&mut crate::foreign::runtime::ForeignRuntime>,
) -> Result<Observation, FileFailure>
where
    E: FnOnce(&ValidatedProgram) -> Result<Evaluation, RuntimeFailure>,
{
    refuse_unbound_source_native_entry(core).map_err(|failure| {
        FileFailure::from(PipelineFailure::Runtime(failure)).with_compilation_work(compilation_work)
    })?;
    let evaluation_phase = crate::calibration::Phase::start("evaluation");
    let evaluation = match core {
        CompiledCore::Pure(core) => evaluator(core),
        CompiledCore::Effect(core) => match runtime {
            Some(runtime) => crate::eval::evaluate_effect_with_foreign_runtime(core, runtime),
            None => evaluate_effect(core),
        },
    }
    .map_err(|failure| {
        FileFailure::from(PipelineFailure::Runtime(failure)).with_compilation_work(compilation_work)
    })?;
    evaluation_phase.finish(None, 0, 0);
    let (value, heap) = evaluation.into_observation_parts();
    Ok(Observation {
        value,
        ty: metadata.ty.into_inner(),
        type_display: Some(metadata.type_display),
        _heap: heap,
        compilation_work,
    })
}

/// Executes a modular Ash graph with authenticated executable foreign bindings.
///
/// The configuration retains its source registrations. The runtime must bind
/// those original entries; equal names do not authorize native dispatch. It is
/// borrowed so retained native owners remain quarantined until host teardown.
///
/// # Errors
/// Returns the same input, compiler and runtime failures as [`run_path`], plus
/// foreign binding or conversion failures before the associated native use.
pub fn run_path_with_foreign_runtime(
    configuration: RunConfiguration,
    runtime: &mut crate::foreign::runtime::ForeignRuntime,
) -> Result<Observation, FileFailure> {
    let pipeline_phase = crate::calibration::Phase::start("pipeline");
    let compiled = compile_path_for_execution(configuration)?;
    let observation = execute_owned_with_consumer(compiled, evaluate, Some(runtime))?;
    pipeline_phase.finish(None, 0, 0);
    Ok(observation)
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
        |program, sources, modules| {
            validator(program, sources, modules)
                .map(|program| (program, None))
                .map_err(|failure| (failure, None))
        },
        evaluator,
        false,
        None,
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
        |program, sources, modules| {
            validator(program, sources, modules)
                .map(|program| (program, None))
                .map_err(|failure| (failure, None))
        },
        evaluator,
        false,
        None,
    )
}

#[cfg(test)]
fn run_path_with_consumers_internal<I, V, E>(
    configuration: RunConfiguration,
    constraint_work: &mut InterfaceConstraintBudget,
    interface_validator: I,
    validator: V,
    evaluator: E,
    select_effect_core: bool,
    runtime: Option<&mut crate::foreign::runtime::ForeignRuntime>,
) -> Result<Observation, FileFailure>
where
    I: FnOnce(
        ResolvedModuleProgram,
        &mut InterfaceConstraintBudget,
        &mut TypeWorkBudget,
    ) -> Result<ValidatedInterfaceProgram, EvidenceValidationFailure>,
    V: FnOnce(UnvalidatedProgram, &[&SourceFile], &[(ModuleId, SourceId)]) -> ModularCoreResult,
    E: FnOnce(&ValidatedProgram) -> Result<Evaluation, RuntimeFailure>,
{
    let pipeline_phase = crate::calibration::Phase::start("pipeline");
    let compiled = compile_path_with_consumers_internal(
        configuration,
        constraint_work,
        interface_validator,
        validator,
        select_effect_core,
        ProvenanceRetention::Discard,
    )?;
    let observation = execute_owned_with_consumer(compiled, evaluator, runtime)?;
    pipeline_phase.finish(None, 0, 0);
    Ok(observation)
}

fn compile_path_with_consumers_internal<I, V>(
    configuration: RunConfiguration,
    constraint_work: &mut InterfaceConstraintBudget,
    interface_validator: I,
    validator: V,
    select_effect_core: bool,
    retention: ProvenanceRetention,
) -> Result<CompiledProgram, FileFailure>
where
    I: FnOnce(
        ResolvedModuleProgram,
        &mut InterfaceConstraintBudget,
        &mut TypeWorkBudget,
    ) -> Result<ValidatedInterfaceProgram, EvidenceValidationFailure>,
    V: FnOnce(UnvalidatedProgram, &[&SourceFile], &[(ModuleId, SourceId)]) -> ModularCoreResult,
{
    let compilation_phase = crate::calibration::Phase::start("compilation");
    let loading_phase = crate::calibration::Phase::start("loading");
    let graph = load_module_graph(&configuration.entry, &configuration.roots)
        .map_err(FileFailure::Graph)?;
    loading_phase.finish(None, 0, 0);
    #[cfg(feature = "resource-calibration")]
    if crate::calibration::observing() {
        let metrics = crate::calibration::Phase::start("input-metrics");
        crate::calibration_features::observe_input(&graph);
        metrics.finish(None, 0, 0);
    }
    let result = compile_graph_with_consumers(
        &graph,
        constraint_work,
        interface_validator,
        validator,
        select_effect_core,
        retention,
    );
    if result.is_ok() {
        compilation_phase.finish(None, 0, 0);
    }
    match result {
        Err(FileFailure::Pipeline(mut context))
            if !matches!(context.failure.as_ref(), PipelineFailure::Runtime(_)) =>
        {
            context.sources = graph.into_sources();
            Err(FileFailure::Pipeline(context))
        }
        other => other,
    }
}

fn compile_graph_with_consumers<I, V>(
    graph: &ModuleGraph,
    constraint_work: &mut InterfaceConstraintBudget,
    interface_validator: I,
    validator: V,
    select_effect_core: bool,
    retention: ProvenanceRetention,
) -> Result<CompiledProgram, FileFailure>
where
    I: FnOnce(
        ResolvedModuleProgram,
        &mut InterfaceConstraintBudget,
        &mut TypeWorkBudget,
    ) -> Result<ValidatedInterfaceProgram, EvidenceValidationFailure>,
    V: FnOnce(UnvalidatedProgram, &[&SourceFile], &[(ModuleId, SourceId)]) -> ModularCoreResult,
{
    let mut compilation_work = crate::compiler_work::CompilationWork::default();
    compile_graph_with_report(
        graph,
        constraint_work,
        interface_validator,
        validator,
        select_effect_core,
        retention,
        &mut compilation_work,
        None,
    )
    .map_err(|failure| failure.with_compilation_work(compilation_work))
}

#[expect(
    clippy::too_many_arguments,
    reason = "the optional authoring consumer shares the complete compiler pipeline without changing ordinary paths"
)]
fn compile_graph_with_report<I, V>(
    graph: &ModuleGraph,
    constraint_work: &mut InterfaceConstraintBudget,
    interface_validator: I,
    validator: V,
    select_effect_core: bool,
    retention: ProvenanceRetention,
    compilation_work: &mut crate::compiler_work::CompilationWork,
    mut foreign_catalogue: Option<&mut Vec<crate::check_ffi::CheckedForeignModule>>,
) -> Result<CompiledProgram, FileFailure>
where
    I: FnOnce(
        ResolvedModuleProgram,
        &mut InterfaceConstraintBudget,
        &mut TypeWorkBudget,
    ) -> Result<ValidatedInterfaceProgram, EvidenceValidationFailure>,
    V: FnOnce(UnvalidatedProgram, &[&SourceFile], &[(ModuleId, SourceId)]) -> ModularCoreResult,
{
    let mut checked: Vec<crate::resolved::CheckedModule> =
        Vec::with_capacity(graph.modules().len());
    let mut checked_by_module: HashMap<ModuleId, usize> =
        HashMap::with_capacity(graph.modules().len());
    let mut resolution_type_work = TypeWorkBudget::default();
    let (mut checking_type_work, source_bytes) =
        crate::compiler_work::source_work(graph).map_err(|()| {
            FileFailure::from(PipelineFailure::Typing(TypeError::Internal(
                crate::elaborate::ElaborationFailure::TypeResourceExhausted,
            )))
        })?;
    let source_normal_limit = checking_type_work.limit();
    // Preserve the existing explicit diagnostic feature, with the paid census
    // already in the same ledger. Ordinary builds retain exactly 800*S.
    checking_type_work
        .finish_sizing(crate::calibration::limit(
            source_normal_limit,
            crate::calibration::DiagnosticOwner::Structural,
        ))
        .map_err(|()| {
            FileFailure::from(PipelineFailure::Typing(TypeError::Internal(
                crate::elaborate::ElaborationFailure::TypeResourceExhausted,
            )))
        })?;
    let rewrite_limit = modular_rewrite_limit(source_bytes).map_err(|()| {
        FileFailure::from(PipelineFailure::Typing(TypeError::Internal(
            crate::elaborate::ElaborationFailure::TypeResourceExhausted,
        )))
    })?;
    let mut provider_codes = ProviderCodeAvailability::default();
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
        let resolution_phase = crate::calibration::Phase::start("resolution");
        let mut libraries = Vec::new();
        let resolved = crate::resolve::resolve_module_with_foreign_catalog(
            module,
            &dependencies,
            &mut resolution_type_work,
            constraint_work,
            foreign_catalogue.as_ref().map(|_| &mut libraries),
        )
        .map_err(|error| match error {
            ResolveModuleError::Resolution(error) => PipelineFailure::Resolution(error),
            ResolveModuleError::Kind(error) => PipelineFailure::Kind(error),
        })
        .map_err(FileFailure::from)?;
        if let Some(catalogue) = foreign_catalogue.as_deref_mut() {
            crate::check_ffi::retain_module(
                catalogue,
                module,
                libraries,
                &mut resolution_type_work,
            )
            .map_err(|()| {
                FileFailure::from(PipelineFailure::Typing(TypeError::Internal(
                    crate::elaborate::ElaborationFailure::TypeResourceExhausted,
                )))
            })?;
        }
        resolution_phase.finish(
            Some(resolution_type_work.used()),
            crate::types::TYPE_WORK_LIMIT,
            resolution_type_work.limit(),
        );
        drop(dependencies);
        let source_phase = crate::calibration::Phase::start("source-checking");
        let checked_module = check_module_with_budget_and_provider_codes_and_rewrite_work(
            resolved,
            &provider_codes,
            &mut checking_type_work,
            &mut coverage_work,
            constraint_work,
            Some(TypeWorkBudget::with_limit(rewrite_limit)),
        )
        .map_err(|failure| {
            FileFailure::from(PipelineFailure::Typing(failure)).with_phase_work(
                crate::compiler_work::CompilationPhase::SourceChecking
                    .assess_with_allowance(checking_type_work.used(), checking_type_work.limit())
                    .incomplete(),
            )
        })?;
        if let Some(code) = checked_module.provider_code() {
            provider_codes
                .retain(module.id(), code, &mut checking_type_work)
                .map_err(|failure| {
                    FileFailure::from(PipelineFailure::Typing(failure)).with_phase_work(
                        crate::compiler_work::CompilationPhase::SourceChecking
                            .assess_with_allowance(
                                checking_type_work.used(),
                                checking_type_work.limit(),
                            )
                            .incomplete(),
                    )
                })?;
        }
        if let Some(code) = checked_module.source_resource_code() {
            provider_codes
                .retain_source(module.id(), code, &mut checking_type_work)
                .map_err(|failure| {
                    FileFailure::from(PipelineFailure::Typing(failure)).with_phase_work(
                        crate::compiler_work::CompilationPhase::SourceChecking
                            .assess_with_allowance(
                                checking_type_work.used(),
                                checking_type_work.limit(),
                            )
                            .incomplete(),
                    )
                })?;
        }
        checked_by_module.insert(module.id(), checked.len());
        checked.push(checked_module);
        source_phase.finish(
            Some(checking_type_work.used()),
            source_normal_limit,
            checking_type_work.limit(),
        );
        compilation_work.source_checking = Some(
            crate::compiler_work::CompilationPhase::SourceChecking
                .assess_with_allowance(checking_type_work.used(), checking_type_work.limit())
                .incomplete(),
        );
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
        | Type::Bytes
        | Type::String
        | Type::Int
        | Type::Bool
        | Type::Unit
        | Type::Tuple(_)
        | Type::ResourceApply(_, _)
        | Type::Nominal(_)
        | Type::Application(_, _)
        | Type::Variable(_)
        | Type::Inference(_) => {
            return Err(entry_failure(EntryReason::MainDomain, main_span));
        }
    };
    if main_has_effects {
        let Type::EffectfulFunction(_, computation) = &main.scheme.value_type else {
            return Err(internal_file_failure());
        };
        // Reuse the checked graph's defining-module index. The entry's local
        // registry excludes imported symbols; rebuilding a checker view would
        // repeat completed preparation and copy its immutable contracts.
        let native_entry = select_effect_core
            && crate::core::effect::owner_free_native_entry_row(
                |effect| {
                    checked_by_module
                        .get(&effect.module())
                        .and_then(|index| checked.get(*index))
                        .filter(|module| module.module() == effect.module())
                        .map(|module| module.registry().as_ref())
                },
                computation.effects(),
                &mut checking_type_work,
            )
            .map_err(|()| {
                FileFailure::from(PipelineFailure::Typing(TypeError::Internal(
                    crate::elaborate::ElaborationFailure::TypeResourceExhausted,
                )))
                .with_phase_work(
                    crate::compiler_work::CompilationPhase::SourceChecking
                        .assess_with_allowance(
                            checking_type_work.used(),
                            checking_type_work.limit(),
                        )
                        .incomplete(),
                )
            })?;
        if !native_entry {
            return Err(entry_failure(EntryReason::MainEffects, main_span));
        }
    }
    let closed_result =
        closed_entry_result(result_type, &mut checking_type_work).map_err(|()| {
            FileFailure::from(PipelineFailure::Typing(TypeError::Internal(
                crate::elaborate::ElaborationFailure::TypeResourceExhausted,
            )))
            .with_phase_work(
                crate::compiler_work::CompilationPhase::SourceChecking
                    .assess_with_allowance(checking_type_work.used(), checking_type_work.limit())
                    .incomplete(),
            )
        })?;
    compilation_work.source_checking = Some(
        crate::compiler_work::CompilationPhase::SourceChecking
            .assess_with_allowance(checking_type_work.used(), checking_type_work.limit())
            .incomplete(),
    );
    if !closed_result {
        return Err(entry_failure(EntryReason::MainOpenResult, main_span));
    }
    if !main.scheme.requirements.is_empty() {
        return Err(entry_failure(EntryReason::MainConstrained, main_span));
    }
    let provenance =
        retain_source_provenance(graph, retention, &mut checking_type_work).map_err(|()| {
            FileFailure::from(PipelineFailure::Typing(TypeError::Internal(
                crate::elaborate::ElaborationFailure::TypeResourceExhausted,
            )))
            .with_phase_work(
                crate::compiler_work::CompilationPhase::SourceChecking
                    .assess_with_allowance(checking_type_work.used(), checking_type_work.limit())
                    .incomplete(),
            )
        })?;
    compilation_work.source_checking = Some(
        crate::compiler_work::CompilationPhase::SourceChecking
            .assess_with_allowance(checking_type_work.used(), checking_type_work.limit()),
    );
    crate::calibration::work(
        "resolution",
        resolution_type_work.used(),
        crate::types::TYPE_WORK_LIMIT,
        resolution_type_work.limit(),
        true,
    );
    crate::calibration::work(
        "source-checking",
        checking_type_work.used(),
        source_normal_limit,
        checking_type_work.limit(),
        true,
    );
    let linking_phase = crate::calibration::Phase::start("module-linking");
    let linked = link_modules_with_budget(checked, graph.entry(), constraint_work)
        .map_err(PipelineFailure::Typing)
        .map_err(FileFailure::from)?;
    linking_phase.finish(None, 0, 0);
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
    let (ty, type_display, unchecked, final_work, final_limit) = {
        let interface_phase = crate::calibration::Phase::start("linked-interface");
        let validated_interfaces =
            interface_validator(linked, constraint_work, &mut linked_type_work)
                .map_err(PipelineFailure::EvidenceValidation)
                .map_err(FileFailure::from)?;
        let registry = Arc::clone(validated_interfaces.registry());
        if select_effect_core
            && (main_has_effects
                || checked_program_contains_effect_syntax(
                    &validated_interfaces,
                    &mut linked_type_work,
                )
                .map_err(PipelineFailure::Typing)
                .map_err(FileFailure::from)?)
        {
            interface_phase.finish(
                Some(linked_type_work.used()),
                crate::types::TYPE_WORK_LIMIT,
                linked_type_work.limit(),
            );
            crate::calibration::work(
                "linked-interface",
                linked_type_work.used(),
                crate::types::TYPE_WORK_LIMIT,
                linked_type_work.limit(),
                true,
            );
            return finish_effect_compilation(
                &validated_interfaces,
                &sources,
                &module_sources,
                compilation_work,
                main_has_effects.then_some(main_span),
            )
            .map(|mut compiled| {
                compiled.provenance = provenance;
                compiled
            });
        }
        interface_phase.finish(
            Some(linked_type_work.used()),
            crate::types::TYPE_WORK_LIMIT,
            linked_type_work.limit(),
        );
        crate::calibration::work(
            "linked-interface",
            linked_type_work.used(),
            crate::types::TYPE_WORK_LIMIT,
            linked_type_work.limit(),
            true,
        );
        let elaboration_phase = crate::calibration::Phase::start("final-elaboration");
        let (final_budget, final_normal_limit, source_bytes) = modular_phase_work(
            crate::compiler_work::CompilationPhase::FinalElaboration,
            &sources,
        )
        .map_err(|()| {
            FileFailure::from(PipelineFailure::Typing(TypeError::Internal(
                crate::elaborate::ElaborationFailure::TypeResourceExhausted,
            )))
        })?;
        let final_limit = final_budget.limit();
        let rewrite_budget =
            TypeWorkBudget::with_limit(modular_rewrite_limit(source_bytes).map_err(|()| {
                FileFailure::from(PipelineFailure::Typing(TypeError::Internal(
                    crate::elaborate::ElaborationFailure::TypeResourceExhausted,
                )))
            })?);
        let mut elaborator = Elaborator::for_module_program_with_budgets(
            &validated_interfaces,
            final_budget,
            rewrite_budget,
        )
        .map_err(|(failure, used)| {
            FileFailure::from(PipelineFailure::Typing(TypeError::Internal(failure)))
                .with_phase_work(
                    crate::compiler_work::CompilationPhase::FinalElaboration
                        .assess_with_allowance(used, final_limit)
                        .incomplete(),
                )
        })?;
        let typed = if select_effect_core {
            elaborator.synthesize_module_program_after_effect_scan(&validated_interfaces)
        } else {
            elaborator.synthesize_module_program(&validated_interfaces)
        }
        .map_err(|failure| {
            FileFailure::from(PipelineFailure::Typing(failure)).with_phase_work(
                crate::compiler_work::CompilationPhase::FinalElaboration
                    .assess_with_allowance(elaborator.measured_type_work(), final_limit)
                    .incomplete(),
            )
        })?;
        let ty = IterativeTypeOwner::new(typed.ty);
        let type_display = registry.display_type(&ty);
        let (unchecked, final_work) =
            elaborator
                .finish_with_work(typed.node)
                .map_err(|(failure, used)| {
                    FileFailure::from(PipelineFailure::Typing(TypeError::Internal(failure)))
                        .with_phase_work(
                            crate::compiler_work::CompilationPhase::FinalElaboration
                                .assess_with_allowance(used, final_limit)
                                .incomplete(),
                        )
                })?;
        crate::calibration::work(
            "final-elaboration",
            final_work,
            final_normal_limit,
            final_limit,
            true,
        );
        ::std::mem::drop(validated_interfaces);
        elaboration_phase.finish(Some(final_work), final_normal_limit, final_limit);
        (ty, type_display, unchecked, final_work, final_limit)
    };
    compilation_work.final_elaboration = Some(
        crate::compiler_work::CompilationPhase::FinalElaboration
            .assess_with_allowance(final_work, final_limit),
    );
    finish_compilation(
        ty,
        type_display,
        unchecked,
        &sources,
        &module_sources,
        validator,
        compilation_work,
    )
    .map(|mut compiled| {
        compiled.provenance = provenance;
        compiled
    })
}

fn retain_source_provenance(
    graph: &ModuleGraph,
    retention: ProvenanceRetention,
    work: &mut TypeWorkBudget,
) -> Result<Vec<(ModuleId, Arc<SourceFile>)>, ()> {
    let mut provenance = Vec::new();
    if matches!(retention, ProvenanceRetention::Discard) {
        return Ok(provenance);
    }
    // Charge record storage and shared-handle copies before allocating or
    // inspecting the admitted modules. Source bytes themselves remain shared.
    work.charge(graph.modules().len().checked_mul(2).ok_or(())?)?;
    provenance
        .try_reserve_exact(graph.modules().len())
        .map_err(|_| ())?;
    for module in graph.modules() {
        provenance.push((module.id(), Arc::clone(module.retained_source())));
    }
    Ok(provenance)
}

// Select experimental overrides only for complete public phase owners. Exact
// caller-provided and remaining sub-budgets retain their supplied capacities.
fn modular_phase_work(
    phase: crate::compiler_work::CompilationPhase,
    sources: &[&SourceFile],
) -> Result<(TypeWorkBudget, usize, usize), ()> {
    use crate::{calibration::DiagnosticOwner, compiler_work::CompilationPhase};
    let owner = match phase {
        CompilationPhase::SourceChecking | CompilationPhase::FinalElaboration => {
            DiagnosticOwner::Structural
        }
        CompilationPhase::IndependentCore => DiagnosticOwner::Core,
    };
    let (mut work, source_bytes) = crate::compiler_work::resident_phase_work(phase, sources)?;
    let normal = work.limit();
    work.finish_sizing(crate::calibration::limit(normal, owner))?;
    Ok((work, normal, source_bytes))
}

fn modular_rewrite_limit(source_bytes: usize) -> Result<usize, ()> {
    Ok(crate::calibration::limit(
        crate::compiler_work::rewrite_total(source_bytes)?,
        crate::calibration::DiagnosticOwner::Structural,
    ))
}

type ModularCoreResult = Result<
    (ValidatedProgram, Option<crate::compiler_work::PhaseCost>),
    (ValidationError, Option<crate::compiler_work::PhaseCost>),
>;

fn validate_modular_core(
    program: UnvalidatedProgram,
    sources: &[&SourceFile],
    modules: &[(ModuleId, SourceId)],
) -> ModularCoreResult {
    let phase = crate::compiler_work::CompilationPhase::IndependentCore;
    let validation_phase = crate::calibration::Phase::start("independent-effect-core");
    let (mut work, normal_limit, _) = match modular_phase_work(phase, sources) {
        Ok(work) => work,
        Err(()) => {
            return Err((ValidationError::resource_exhausted(program), None));
        }
    };
    let result =
        crate::core::validate::validate_modules_with_work(program, sources, modules, &mut work);
    crate::calibration::work(
        "independent-effect-core",
        work.used(),
        normal_limit,
        work.limit(),
        result.is_ok(),
    );
    if result.is_ok() {
        validation_phase.finish(Some(work.used()), normal_limit, work.limit());
    }
    result
        .map(|program| {
            (
                program,
                Some(phase.assess_with_allowance(work.used(), work.limit())),
            )
        })
        .map_err(|failure| {
            (
                failure,
                Some(
                    phase
                        .assess_with_allowance(work.used(), work.limit())
                        .incomplete(),
                ),
            )
        })
}

// Keep later Effect-phase temporaries out of the source-checking caller's frame.
fn finish_effect_compilation(
    validated_interfaces: &ValidatedInterfaceProgram,
    sources: &[&SourceFile],
    module_sources: &[(ModuleId, SourceId)],
    compilation_work: &mut crate::compiler_work::CompilationWork,
    native_entry_span: Option<Span>,
) -> Result<CompiledProgram, FileFailure> {
    let elaboration_phase = crate::calibration::Phase::start("final-elaboration");
    let (final_budget, final_normal_limit, source_bytes) = modular_phase_work(
        crate::compiler_work::CompilationPhase::FinalElaboration,
        sources,
    )
    .map_err(|()| {
        FileFailure::from(PipelineFailure::Typing(TypeError::Internal(
            crate::elaborate::ElaborationFailure::TypeResourceExhausted,
        )))
    })?;
    let final_limit = final_budget.limit();
    let rewrite_budget =
        TypeWorkBudget::with_limit(modular_rewrite_limit(source_bytes).map_err(|()| {
            FileFailure::from(PipelineFailure::Typing(TypeError::Internal(
                crate::elaborate::ElaborationFailure::TypeResourceExhausted,
            )))
        })?);
    let mut elaborator = EffectElaborator::for_module_program_with_budgets(
        validated_interfaces,
        final_budget,
        rewrite_budget,
    )
    .map_err(|(failure, used)| {
        FileFailure::from(PipelineFailure::Typing(TypeError::Internal(failure))).with_phase_work(
            crate::compiler_work::CompilationPhase::FinalElaboration
                .assess_with_allowance(used, final_limit)
                .incomplete(),
        )
    })?;
    let typed = elaborator
        .synthesize_effect_module_program(validated_interfaces)
        .map_err(|failure| {
            FileFailure::from(PipelineFailure::Typing(failure)).with_phase_work(
                crate::compiler_work::CompilationPhase::FinalElaboration
                    .assess_with_allowance(elaborator.measured_type_work(), final_limit)
                    .incomplete(),
            )
        })?;
    let ty = IterativeTypeOwner::new(typed.ty);
    let type_display = validated_interfaces.registry().display_type(&ty);
    let finished = match native_entry_span {
        Some(span) => elaborator.finish_with_owner_free_native_entry(typed.node, span),
        None => elaborator
            .finish_with_work(typed.node)
            .map_err(|(failure, used)| {
                (
                    crate::elaborate::NativeEntryFinishFailure::Elaboration(failure),
                    used,
                )
            }),
    };
    let (unchecked, final_work) = finished.map_err(|(failure, used)| {
        let failure = match failure {
            crate::elaborate::NativeEntryFinishFailure::ResidualEffects => entry_failure(
                EntryReason::MainEffects,
                native_entry_span.expect("native finalizer has an entry span"),
            ),
            crate::elaborate::NativeEntryFinishFailure::Elaboration(failure) => {
                FileFailure::from(PipelineFailure::Typing(TypeError::Internal(failure)))
            }
        };
        failure.with_phase_work(
            crate::compiler_work::CompilationPhase::FinalElaboration
                .assess_with_allowance(used, final_limit)
                .incomplete(),
        )
    })?;
    compilation_work.final_elaboration = Some(
        crate::compiler_work::CompilationPhase::FinalElaboration
            .assess_with_allowance(final_work, final_limit),
    );
    crate::calibration::work(
        "final-elaboration",
        final_work,
        final_normal_limit,
        final_limit,
        true,
    );
    elaboration_phase.finish(Some(final_work), final_normal_limit, final_limit);
    let validation_phase = crate::calibration::Phase::start("independent-effect-core");
    let (mut core_work, core_normal_limit, _) = match modular_phase_work(
        crate::compiler_work::CompilationPhase::IndependentCore,
        sources,
    ) {
        Ok(work) => work,
        Err(()) => {
            return Err(FileFailure::from(PipelineFailure::Validation(
                ValidationError::resource_exhausted(unchecked),
            )));
        }
    };
    let core_result = crate::core::validate::validate_effect_modules_with_work(
        unchecked,
        sources,
        module_sources,
        &mut core_work,
    );
    crate::calibration::work(
        "independent-effect-core",
        core_work.used(),
        core_normal_limit,
        core_work.limit(),
        core_result.is_ok(),
    );
    let validated = core_result.map_err(|failure| {
        FileFailure::from(PipelineFailure::Validation(failure)).with_phase_work(
            crate::compiler_work::CompilationPhase::IndependentCore
                .assess_with_allowance(core_work.used(), core_work.limit())
                .incomplete(),
        )
    })?;
    compilation_work.independent_core = Some(
        crate::compiler_work::CompilationPhase::IndependentCore
            .assess_with_allowance(core_work.used(), core_work.limit()),
    );
    validation_phase.finish(Some(core_work.used()), core_normal_limit, core_work.limit());
    Ok(CompiledProgram {
        core: CompiledCore::Effect(validated),
        ty,
        type_display,
        compilation_work: *compilation_work,
        provenance: Vec::new(),
    })
}

fn finish_compilation<V>(
    ty: IterativeTypeOwner,
    type_display: String,
    unchecked: UnvalidatedProgram,
    sources: &[&SourceFile],
    module_sources: &[(ModuleId, SourceId)],
    validator: V,
    compilation_work: &mut crate::compiler_work::CompilationWork,
) -> Result<CompiledProgram, FileFailure>
where
    V: FnOnce(UnvalidatedProgram, &[&SourceFile], &[(ModuleId, SourceId)]) -> ModularCoreResult,
{
    let (validated, core_work) =
        validator(unchecked, sources, module_sources).map_err(|(failure, cost)| {
            let failure = FileFailure::from(PipelineFailure::Validation(failure))
                .with_compilation_work(*compilation_work);
            match cost {
                Some(cost) => failure.with_phase_work(cost),
                None => failure,
            }
        })?;
    compilation_work.independent_core = core_work;
    Ok(CompiledProgram {
        core: CompiledCore::Pure(validated),
        ty,
        type_display,
        compilation_work: *compilation_work,
        provenance: Vec::new(),
    })
}

#[cfg(test)]
#[expect(
    clippy::too_many_arguments,
    reason = "injected failure tests retain the existing validation/evaluation handoff"
)]
fn finish_observation<V, E>(
    ty: IterativeTypeOwner,
    type_display: String,
    unchecked: UnvalidatedProgram,
    sources: &[&SourceFile],
    module_sources: &[(ModuleId, SourceId)],
    validator: V,
    evaluator: E,
    compilation_work: &mut crate::compiler_work::CompilationWork,
) -> Result<Observation, FileFailure>
where
    V: FnOnce(UnvalidatedProgram, &[&SourceFile], &[(ModuleId, SourceId)]) -> ModularCoreResult,
    E: FnOnce(&ValidatedProgram) -> Result<Evaluation, RuntimeFailure>,
{
    let compiled = finish_compilation(
        ty,
        type_display,
        unchecked,
        sources,
        module_sources,
        validator,
        compilation_work,
    )?;
    execute_owned_with_consumer(compiled, evaluator, None)
}

fn entry_failure(reason: EntryReason, primary: Span) -> FileFailure {
    FileFailure::from(PipelineFailure::Entry(EntryFailure::new(reason, primary)))
}

fn internal_file_failure() -> FileFailure {
    FileFailure::from(PipelineFailure::Typing(TypeError::Internal(
        crate::elaborate::ElaborationFailure::InvalidState,
    )))
}

fn closed_entry_result(root: &Type, work: &mut TypeWorkBudget) -> Result<bool, ()> {
    crate::types::visit_type_structure_with_budget(root, work, |node, _| {
        Ok(matches!(
            node,
            crate::types::TypeStructureNode::Type(
                Type::Variable(_) | Type::Inference(_) | Type::Forall(_, _)
            ) | crate::types::TypeStructureNode::Tail(_)
        ))
    })
    .map(|open| !open)
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

fn refuse_unbound_source_native_entry(core: &CompiledCore) -> Result<(), RuntimeFailure> {
    if let CompiledCore::Effect(program) = core {
        let root = program
            .node(program.root())
            .ok_or(RuntimeFailure::MissingNode)?;
        if let crate::core::EffectExprKind::Operation(
            crate::core::EffectOperation::NativeInterpret(boundary),
        ) = &root.kind
            && !boundary.interpretations().is_empty()
        {
            return Err(RuntimeFailure::ForeignBinding);
        }
    }
    Ok(())
}

/// Evaluates a prepared source-native program with already supplied generated
/// bindings. It performs no source loading, host compilation or library linking.
/// Binding admission and observation preparation both precede Ash execution.
///
/// The generated linked host supplies bindings through sealed bridge admission.
/// Public empty binding construction grants no native invocation authority;
/// this function neither registers callbacks nor selects them by source name.
///
/// # Errors
/// Refuses missing or changed bindings before Ash execution and retains runtime
/// failures without retrying a returned external call.
pub fn execute_with_source_native_bindings(
    program: &CompiledProgram,
    bindings: &mut crate::foreign::source_runtime::SourceNativeBindings,
) -> Result<Observation, FileFailure> {
    let Some((core, boundary)) = program.source_native_entry() else {
        return execute(program);
    };
    if boundary.interpretations().is_empty() {
        return execute(program);
    }
    let preparation_failure = |failure| {
        FileFailure::from(PipelineFailure::Runtime(failure))
            .with_compilation_work(program.compilation_work)
    };
    let mut work = TypeWorkBudget::default();
    let admitted =
        crate::foreign::source_runtime::admit_source_native_program(core, bindings, &mut work)
            .map_err(preparation_failure)?;
    let metadata = prepare_observation_metadata(program).map_err(preparation_failure)?;
    let phase = crate::calibration::Phase::start("evaluation");
    let evaluation = crate::eval::evaluate_effect_with_source_native_program(admitted)
        .map_err(preparation_failure)?;
    phase.finish(None, 0, 0);
    let (value, heap) = evaluation.into_observation_parts();
    Ok(Observation {
        value,
        ty: metadata.ty.into_inner(),
        type_display: Some(metadata.type_display),
        _heap: heap,
        compilation_work: program.compilation_work,
    })
}

#[cfg(test)]
mod tests {
    use crate::core::validate_modules;
    use crate::elaborate::check_module_with_budget;
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

        assert_eq!(
            closed_entry_result(&closed, &mut TypeWorkBudget::unbounded()),
            Ok(true)
        );
        assert_eq!(
            closed_entry_result(&rigid, &mut TypeWorkBudget::unbounded()),
            Ok(false)
        );
        assert_eq!(
            closed_entry_result(&inference, &mut TypeWorkBudget::unbounded()),
            Ok(false)
        );
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
        let work = failure.compilation_work().unwrap();
        assert!(work.source_checking.unwrap().completed);
        assert!(work.final_elaboration.unwrap().completed);
        assert!(
            work.independent_core.is_none(),
            "injected validators do not manufacture measured work"
        );
        assert!(failure.sources().is_empty());
        assert!(!failure.is_source_rejection());
    }

    #[test]
    fn source_gas_counts_canonical_loaded_closure_and_builtins_once() {
        let source = TestSource::write(concat!(
            "import @builtin.bytes as First\n",
            "import @builtin.bytes as Second\n",
            "import helper (answer)\n",
            "main : Unit -> Int\nmain () = answer ()\n",
        ));
        source.write_sibling("helper.ash", "pub answer : Unit -> Int\nanswer () = 42\n");
        let graph = load_module_graph(&source.0, &ModuleRoots::empty()).unwrap();
        assert_eq!(graph.modules().len(), 3);
        let bytes: usize = graph
            .modules()
            .iter()
            .map(|module| module.source().text().len())
            .sum();
        let (work, counted_bytes) = crate::compiler_work::source_work(&graph).unwrap();
        assert_eq!(counted_bytes, bytes);
        assert_eq!(
            (work.used(), work.limit()),
            (graph.modules().len() + 1, 800 * bytes)
        );
        let sources = graph
            .modules()
            .iter()
            .map(|module| module.source())
            .collect::<Vec<_>>();
        for (phase, coefficient) in [
            (
                crate::compiler_work::CompilationPhase::FinalElaboration,
                800,
            ),
            (crate::compiler_work::CompilationPhase::IndependentCore, 345),
        ] {
            let (work, counted_bytes) =
                crate::compiler_work::resident_phase_work(phase, &sources).unwrap();
            assert_eq!(counted_bytes, bytes);
            assert_eq!(
                (work.used(), work.limit()),
                (sources.len() + 1, coefficient * bytes)
            );
        }
    }

    #[test]
    fn compilation_retains_original_source_handles_only_for_reusable_programs() {
        let entry = concat!(
            "import @builtin.cell as Cell\n",
            "import helper (advance)\n",
            "main : Unit -> Int\n",
            "main () = resource cell<R> value = 41 {\n    advance value\n}\n",
        );
        let source = TestSource::write(entry);
        source.write_sibling(
            "helper.ash",
            concat!(
                "import @builtin.cell as Cell\n",
                "pub advance<R> : Cell.Handle<R> -> Int ! {Cell.Ops<R>} where Cell.Provider<R>\n",
                "advance value = {\n",
                "    let previous = Cell.read value\n",
                "    let _ = Cell.write (value, previous + 1)\n",
                "    Cell.read value\n",
                "}\n",
            ),
        );
        let graph = load_module_graph(&source.0, &ModuleRoots::empty())
            .expect("imported cell source graph loads");
        let original_handle_count = Arc::strong_count(graph.modules()[0].retained_source());
        let mut refused_work = TypeWorkBudget::with_limit(2 * graph.modules().len() - 1);
        assert!(
            retain_source_provenance(&graph, ProvenanceRetention::Retain, &mut refused_work)
                .is_err()
        );
        assert_eq!(refused_work.used(), 0);
        assert_eq!(
            Arc::strong_count(graph.modules()[0].retained_source()),
            original_handle_count,
            "refusal precedes all shared-handle copies",
        );
        let compile = |retention| {
            compile_graph_with_consumers(
                &graph,
                &mut InterfaceConstraintBudget::default(),
                validate_interface_evidence_with_budget,
                validate_modular_core,
                true,
                retention,
            )
            .expect("imported cell graph compiles")
        };
        let retained = compile(ProvenanceRetention::Retain);
        let transient = compile(ProvenanceRetention::Discard);
        assert_eq!(retained.provenance.len(), graph.modules().len());
        assert!(transient.provenance.is_empty());
        for ((module_id, retained_source), module) in
            retained.provenance.iter().zip(graph.modules())
        {
            assert_eq!(*module_id, module.id());
            assert!(Arc::ptr_eq(retained_source, module.retained_source()));
            assert_eq!(retained_source.id(), module.source().id());
        }
        let mut expected_work = *transient.compilation_work();
        expected_work.source_checking.as_mut().unwrap().used += 2 * graph.modules().len();
        assert_eq!(retained.compilation_work(), &expected_work);
        let entry_module = graph.entry();
        fs::write(&source.0, "invalid replacement\n").expect("replace original entry");
        drop(graph);
        drop(source);
        assert_eq!(
            retained
                .provenance
                .iter()
                .find(|(module_id, _)| *module_id == entry_module)
                .expect("original entry provenance survives")
                .1
                .text(),
            entry,
        );
        assert_eq!(execute(&retained).unwrap().value_display(), "42");
        assert_eq!(execute(&transient).unwrap().value_display(), "42");
    }

    #[test]
    fn execution_result_preparation_refusal_precedes_evaluator_entry() {
        std::thread::Builder::new()
            .name("execution-result-preparation".into())
            .stack_size(256 * 1024)
            .spawn(|| {
                let source = TestSource::write("main : Unit -> Unit\nmain () = ()\n");
                let mut compiled = compile_path(source.configuration()).expect("checked unit Core");
                let work = *compiled.compilation_work();
                // Inject oversized result metadata at the private phase boundary;
                // source admission cannot produce this fixture within its limits.
                for cause in [
                    crate::eval::ResourceFailureCause::ResourceAdmissionRefused,
                    crate::eval::ResourceFailureCause::WorkBudgetExhausted,
                ] {
                    if cause == crate::eval::ResourceFailureCause::ResourceAdmissionRefused {
                        compiled
                            .ty
                            .replace(deep_observation_type(crate::types::TYPE_WORK_LIMIT));
                    } else {
                        compiled.ty.replace(Type::Unit);
                        compiled.type_display = "x".repeat(crate::types::TYPE_WORK_LIMIT);
                    }
                    let evaluated = Cell::new(false);
                    let failure = execute_with_consumer(
                        &compiled,
                        |_| {
                            evaluated.set(true);
                            Err(RuntimeFailure::InvalidControlState)
                        },
                        None,
                    )
                    .expect_err("result metadata preparation exceeds bounded work");
                    assert!(
                        !evaluated.get(),
                        "preparation must precede all evaluator effects"
                    );
                    let Some(PipelineFailure::Runtime(RuntimeFailure::Report(report))) =
                        failure.pipeline_failure()
                    else {
                        panic!("preparation refusal must carry runtime resource details");
                    };
                    let details = report
                        .primary
                        .resource()
                        .expect("classified preparation failure");
                    assert_eq!(details.phase, crate::eval::RuntimePhase::Evaluation);
                    assert_eq!(details.cause, cause);
                    if cause == crate::eval::ResourceFailureCause::WorkBudgetExhausted {
                        assert_eq!(details.resource, crate::eval::RuntimeResource::WorkUnits);
                        assert_eq!(details.requested, Some(compiled.type_display.len()));
                        assert!(
                            details.available.is_some_and(|available| {
                                available < compiled.type_display.len()
                            })
                        );
                    }
                    assert_eq!(failure.compilation_work(), Some(&work));
                    assert_eq!(compiled.compilation_work(), &work);
                    assert!(failure.sources().is_empty());
                }
            })
            .expect("small-stack preparation thread starts")
            .join()
            .expect("failed preparation drops both types iteratively");
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
        let work = failure.compilation_work().unwrap();
        assert!(work.source_checking.unwrap().completed);
        assert!(work.final_elaboration.unwrap().completed);
        assert!(work.independent_core.is_none());
    }

    #[test]
    fn measured_core_rejection_retains_completed_prior_work_without_evaluating() {
        let source = TestSource::write("main : Unit -> Int\nmain () = 42\n");
        let failure = run_path_with_consumers_internal(
            source.configuration(),
            &mut InterfaceConstraintBudget::default(),
            validate_interface_evidence_with_budget,
            |unchecked, sources, _| validate_modular_core(unchecked, sources, &[]),
            |_| panic!("evaluation must not run after independent Core rejection"),
            false,
            None,
        )
        .expect_err("missing canonical module identities fail validation after paid source sizing");
        assert!(matches!(
            failure.pipeline_failure(),
            Some(PipelineFailure::Validation(_))
        ));
        let work = failure.compilation_work().unwrap();
        assert!(work.source_checking.unwrap().completed);
        assert!(work.final_elaboration.unwrap().completed);
        assert!(!work.independent_core.unwrap().completed);
    }

    #[test]
    fn modular_core_debits_the_callers_prefix_with_exact_bounded_retry() {
        let source = SourceFile::new("unit.ash", "()").unwrap();
        let modules = [(ModuleId::new(0), source.id())];
        let mut measured = TypeWorkBudget::with_limit(100_000);
        crate::core::validate::validate_modules_with_work(
            unit_program(&source),
            &[&source],
            &modules,
            &mut measured,
        )
        .unwrap();
        let exact = measured.used();
        assert!(exact > 0);
        let mut short = TypeWorkBudget::with_limit(7 + exact - 1);
        short.charge(7).unwrap();
        let failure = crate::core::validate::validate_modules_with_work(
            unit_program(&source),
            &[&source],
            &modules,
            &mut short,
        )
        .unwrap_err();
        assert_eq!(failure.reason(), crate::core::ValidationReason::Resource);
        assert!(short.used() >= 7 && short.used() < 7 + exact);
        let mut retry = TypeWorkBudget::with_limit(7 + exact);
        retry.charge(7).unwrap();
        crate::core::validate::validate_modules_with_work(
            unit_program(&source),
            &[&source],
            &modules,
            &mut retry,
        )
        .unwrap();
        assert_eq!(retry.used(), 7 + exact);
        assert_eq!(retry.charge(1), Err(()));
    }

    fn deep_observation_type(depth: usize) -> Type {
        let mut ty = Type::Nominal(NominalTypeId::new(ModuleId::new(0), 0));
        for _ in 0..depth {
            ty = Type::Application(Box::new(ty), Box::new(Type::Unit));
        }
        ty
    }

    #[test]
    fn resident_core_gas_refuses_metadata_amplification_with_paid_prefix_and_retry() {
        let source = SourceFile::new("core-gas.ash", "()").unwrap();
        let modules = [(ModuleId::new(0), source.id())];
        for prefix in [0, 11] {
            for _ in 0..2 {
                let (mut work, counted_bytes) = crate::compiler_work::resident_phase_work(
                    crate::compiler_work::CompilationPhase::IndependentCore,
                    &[&source],
                )
                .unwrap();
                assert_eq!(counted_bytes, source.text().len());
                assert_eq!((work.used(), work.limit()), (2, 690));
                work.charge(prefix).unwrap();
                let origin = Origin::Source(source.span(ByteRange::new(0, 2).unwrap()).unwrap());
                let mut builder = crate::core::CoreBuilder::new();
                let leaf = builder.unit(Type::Unit, origin.clone()).unwrap();
                let root = builder
                    .tuple(
                        vec![leaf; 512],
                        Type::Tuple(vec![Type::Unit; 512].into_boxed_slice()),
                        origin,
                    )
                    .unwrap();
                let failure = crate::core::validate::validate_modules_with_work(
                    builder.finish(root).unwrap(),
                    &[&source],
                    &modules,
                    &mut work,
                )
                .unwrap_err();
                assert_eq!(failure.reason(), crate::core::ValidationReason::Resource);
                assert_eq!(work.limit(), 690);
                assert!(work.used() >= 2 + prefix && work.used() <= 690);
            }
        }
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
                    |unchecked, _, _| {
                        validate_modules(unchecked, &[], &[])
                            .map(|p| (p, None))
                            .map_err(|e| (e, None))
                    },
                    |_| panic!("evaluation must not run after validation failure"),
                    &mut Default::default(),
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
                    |unchecked, sources, _| {
                        crate::core::validate(unchecked, sources)
                            .map(|p| (p, None))
                            .map_err(|e| (e, None))
                    },
                    |_| Err(RuntimeFailure::InvalidControlState),
                    &mut Default::default(),
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
        let work = failure.compilation_work().unwrap();
        assert!(work.source_checking.unwrap().completed);
        assert!(work.final_elaboration.is_none());
        assert!(work.independent_core.is_none());
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
        // Complete tagged argument traversal and inherited-owner roles are
        // charged at each consuming boundary. Linking contributes 149 cells;
        // independent linked-evidence validation contributes 1,769 cells.
        // Immutable imported facts retain one original authority; each of the
        // four import routes removes three duplicate retention cells.
        // Final method admission removes four duplicate binder-map slots and
        // one repeated Function-result kind queue; full child checks remain.
        const EXPECTED_BOUNDARIES: [usize; 13] = [
            0, 1, 1_138, 1_721, 2_335, 2_918, 3_532, 4_107, 4_726, 5_756, 6_208, 6_357, 8_126,
        ];
        const EXACT_CONSTRAINT_WORK: usize = 8_126;
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
        const WIDTH: usize = (crate::interface::INTERFACE_CONSTRAINT_WORK_LIMIT - 29) / 63;
        // Dependency checking is declaration 6W + checked facts 6W +
        // selector admission 7W + summary freeze 10W + producer
        // authentication 7W. Both clone preflights charge their three type
        // cells to both ledgers. A monomorphic method
        // has no private binder payload and therefore adds no authority work.
        const DEPENDENCY_CHECKED: usize = 36 * WIDTH;
        // Entry resolution adds complete-vector summary authentication 7W, first-route
        // interface retention 9W, and one dependency-route cell.
        const ENTRY_RESOLVED: usize = 52 * WIDTH + 1;
        // Entry checking additionally authenticates the W imported interface
        // arities and visits its one global declaration before interface and
        // method admission. Producer authentication adds three cells for
        // the entry's withheld main name.
        const ENTRY_CHECKED: usize = 60 * WIDTH + 16;
        // Linking adds its W+7 graph/carrier prefix, W+5 structural
        // authentication, and the W-cell canonical-owner uniqueness index.
        // It does not repeat the 3W complete interface mirror owned by the
        // consuming evidence validator.
        const LINKED: usize = 63 * WIDTH + 28;
        // Validation owns a 46W+55 complete-application authentication suffix
        // and publishes one private method-evidence capability only after the
        // complete graph succeeds. Borrowed singleton binder coverage removes
        // two map slots; the proved Function kind removes one repeated queue.
        const VALIDATED: usize = 109 * WIDTH + 83;
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
            assert!(LINKED + 63 >= crate::interface::INTERFACE_CONSTRAINT_WORK_LIMIT);
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
                    compilation_work: Default::default(),
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
                    compilation_work: Default::default(),
                    value: Value::Boolean(true),
                    ty: deep_type(),
                    type_display: Some("Wide<Unit>".to_owned()),
                    _heap: heap(),
                }
                .into_value();
                assert!(matches!(value.value(), Value::Boolean(true)));

                let value = Observation {
                    compilation_work: Default::default(),
                    value: Value::Boolean(true),
                    ty: deep_type(),
                    type_display: Some("Wide<Unit>".to_owned()),
                    _heap: heap(),
                }
                .into_parts()
                .into_value();
                assert!(matches!(value.value(), Value::Boolean(true)));

                let ty = Observation {
                    compilation_work: Default::default(),
                    value: Value::Unit,
                    ty: Type::Int,
                    type_display: Some("Int".to_owned()),
                    _heap: heap(),
                }
                .into_type();
                assert_eq!(ty, Type::Int);

                let parts = Observation {
                    compilation_work: Default::default(),
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
