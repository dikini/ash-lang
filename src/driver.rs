//! Reusable, stage-preserving Ash pipeline orchestration.

use std::{collections::HashMap, error::Error, fmt, io, path::PathBuf, sync::Arc};

use crate::surface::{SurfaceImport, SurfaceImportItem, SurfaceImportSelection};
use {
    crate::core::UnvalidatedEffectProgram, crate::core::UnvalidatedProgram,
    crate::core::ValidatedEffectProgram, crate::core::ValidatedProgram,
    crate::core::ValidationError, crate::diagnostic::Diagnostic, crate::diagnostic::SourceLabel,
    crate::diagnostic::compare_source_spans, crate::elaborate::EffectElaborator,
    crate::elaborate::Elaborator, crate::elaborate::TypeError,
    crate::elaborate::check_module_with_budget_and_rewrite_work,
    crate::elaborate::link_modules_with_budget, crate::eval::Evaluation, crate::eval::ObservedHeap,
    crate::eval::RuntimeFailure, crate::eval::Value, crate::eval::evaluate,
    crate::evidence_validation::EvidenceValidationFailure,
    crate::evidence_validation::ValidatedInterfaceProgram,
    crate::evidence_validation::validate_interface_evidence_with_budget,
    crate::interface::InterfaceConstraintBudget, crate::kind::KindFailure, crate::lexer::LexReason,
    crate::module::GraphDiagnostic, crate::module::HeaderGraph, crate::module::LoadGraphError,
    crate::module::LoadedModule, crate::module::ModuleGraph, crate::module::ModuleId,
    crate::module::ModuleRoots, crate::module::discover_headers, crate::parser::ParseDiagnostic,
    crate::parser::ProjectionError, crate::parser::ResourceFailure,
    crate::pattern::UsefulnessBudget, crate::resolve::DependencyExports,
    crate::resolve::ResolveError, crate::resolve::ResolveModuleError,
    crate::resolved::ResolvedModuleProgram, crate::source::SourceError, crate::source::SourceFile,
    crate::source::SourceId, crate::source::Span, crate::types::IterativeTypeOwner,
    crate::types::Type, crate::types::TypeWorkBudget,
};

#[cfg(test)]
use crate::module::load_module_graph;
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
    Effect(ValidatedEffectProgram, Arc<[crate::core::NodeId]>),
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
            CompiledCore::Effect(program, _) => {
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
            CompiledCore::Pure(_) | CompiledCore::Effect(_, _) => None,
        }
    }

    pub(crate) fn effect_build_input(
        &self,
    ) -> Option<(&ValidatedEffectProgram, &SourceProvenance)> {
        match &self.core {
            CompiledCore::Effect(program, _) if !self.provenance.is_empty() => {
                Some((program, &self.provenance))
            }
            CompiledCore::Pure(_) | CompiledCore::Effect(_, _) => None,
        }
    }

    pub(crate) fn effect_build_quote_guards(&self) -> Option<&[crate::core::NodeId]> {
        match &self.core {
            CompiledCore::Effect(_, guards) if !self.provenance.is_empty() => Some(guards),
            CompiledCore::Pure(_) | CompiledCore::Effect(_, _) => None,
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

/// A transformer-authored rejection and its retained causal locations.
#[derive(Debug)]
pub struct SyntaxExpansionFailure {
    pub(crate) message: String,
    pub(crate) primary: crate::syntax::MacroOrigin,
    pub(crate) related: Vec<crate::syntax::MacroOrigin>,
    pub(crate) invocation: Span,
    pub(crate) definition: Span,
    pub(crate) invocation_location: Option<Box<crate::syntax::DiagnosticLocation>>,
    pub(crate) teardown: Option<crate::eval::ResourceFailure>,
}

impl SyntaxExpansionFailure {
    fn retain_invocation_location(
        &mut self,
        location: &crate::syntax::DiagnosticLocation,
        budget: &mut crate::syntax_resource::SyntaxBudget,
    ) -> Result<(), ResourceFailure> {
        budget.charge_units(location.frames.len())?;
        crate::syntax::charge_diagnostic_location_copy(location, budget)?;
        self.invocation_location = Some(Box::new(location.clone()));
        Ok(())
    }

    /// Returns the first host teardown failure, if cleanup was incomplete.
    #[must_use]
    pub const fn teardown(&self) -> Option<crate::eval::ResourceFailure> {
        self.teardown
    }

    /// Returns the transformer's message.
    #[must_use]
    pub fn message(&self) -> &str {
        &self.message
    }

    /// Returns the primary causal source span.
    #[must_use]
    pub fn primary_span(&self) -> Span {
        self.primary.primary()
    }

    pub(crate) fn related_spans(&self) -> Vec<(Span, &'static str)> {
        let mut spans = self
            .primary
            .spans()
            .into_iter()
            .skip(1)
            .map(|span| (span, "syntax_cause"))
            .collect::<Vec<_>>();
        for origin in &self.related {
            spans.extend(
                origin
                    .spans()
                    .into_iter()
                    .map(|span| (span, "syntax_cause")),
            );
        }
        if self.invocation != self.primary_span() {
            spans.push((self.invocation, "syntax_invocation"));
        }
        if self.definition != self.primary_span() {
            spans.push((self.definition, "syntax_definition"));
        }
        spans
    }
}

/// Parser facts retained from syntax produced by an expansion.
#[derive(Debug)]
pub struct SyntaxParseFailure {
    pub(crate) diagnostics: Vec<ParseDiagnostic>,
    pub(crate) resource: Option<ResourceFailure>,
    pub(crate) invocation: Span,
    pub(crate) definition: Span,
    pub(crate) teardown: Option<crate::eval::ResourceFailure>,
}

/// A transformer evaluator failure with its expansion context.
#[derive(Debug)]
pub struct SyntaxRuntimeFailure {
    pub(crate) cause: RuntimeFailure,
    pub(crate) invocation: Span,
    pub(crate) definition: Span,
}

impl SyntaxRuntimeFailure {
    /// Returns the unchanged evaluator failure.
    #[must_use]
    pub const fn cause(&self) -> RuntimeFailure {
        self.cause
    }
}

impl SyntaxParseFailure {
    /// Returns the first host teardown failure, if cleanup was incomplete.
    #[must_use]
    pub const fn teardown(&self) -> Option<crate::eval::ResourceFailure> {
        self.teardown
    }

    /// Returns the original parser diagnostics in order.
    #[must_use]
    pub fn diagnostics(&self) -> &[ParseDiagnostic] {
        &self.diagnostics
    }
}

/// A failure from one explicit compiler or runtime stage.
#[derive(Debug)]
pub enum PipelineFailure {
    /// The admitted source model could not produce a checked token span.
    SourceModel(SourceError),
    /// Lexing or parsing retained diagnostics or exhausted a resource budget.
    Syntax(Box<SyntaxFailure>),
    /// An Ash syntax transformer rejected its invocation.
    SyntaxExpansion(SyntaxExpansionFailure),
    /// Transformer-produced syntax retained parser failures.
    SyntaxParse(SyntaxParseFailure),
    /// Evaluating a syntax transformer failed.
    SyntaxRuntime(SyntaxRuntimeFailure),
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
            Self::SyntaxExpansion(_) => "syntax.rejected".into(),
            Self::SyntaxParse(failure) => {
                syntax_reason_code(&[], &failure.diagnostics, failure.resource)
            }
            Self::SyntaxRuntime(_) => "syntax.transformer-failed".into(),
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
            Self::SyntaxExpansion(_) => true,
            Self::SyntaxParse(failure) => {
                failure.resource.is_none() && !failure.diagnostics.is_empty()
            }
            Self::Resolution(error) => error.is_source_rejection(),
            Self::Kind(error) => error.is_source_rejection(),
            Self::Typing(
                TypeError::Source(_) | TypeError::Interface(_) | TypeError::Mismatch(_),
            ) => true,
            Self::Entry(_) => true,
            Self::SourceModel(_)
            | Self::Projection(_)
            | Self::SyntaxRuntime(_)
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
            Self::SyntaxExpansion(_) => "syntax expansion rejection",
            Self::SyntaxParse(_) => "syntax expansion parse failure",
            Self::SyntaxRuntime(_) => "syntax transformer failure",
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
    compilation_work: Box<crate::compiler_work::CompilationWork>,
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
    /// Missing fields were not observed; failures before the source census carry
    /// no compiler report.
    #[must_use]
    pub fn compilation_work(&self) -> Option<&crate::compiler_work::CompilationWork> {
        match self {
            Self::Pipeline(context) => Some(context.compilation_work.as_ref()),
            Self::Graph(context) => context.compilation_work(),
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
        if let Self::Graph(context) = self {
            return Self::Graph(context.with_compilation_work(costs));
        }
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
    let observation = execute_owned_with_consumer(compiled, evaluate_compiled_core)?;
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
        validate_modular_effect_core,
        true,
        ProvenanceRetention::Retain,
    )
}

#[cfg(test)]
pub(crate) fn compile_path_with_effect_validation_for_test(
    configuration: RunConfiguration,
    validator: impl FnOnce(
        UnvalidatedEffectProgram,
        &[&SourceFile],
        &[(ModuleId, SourceId)],
        &ValidatedInterfaceProgram,
    ) -> Result<ValidatedEffectProgram, ValidationError>,
) -> Result<CompiledProgram, FileFailure> {
    compile_path_with_consumers_internal(
        configuration,
        &mut InterfaceConstraintBudget::default(),
        validate_interface_evidence_with_budget,
        |program, sources, modules, linked| {
            validator(program, sources, modules, linked)
                .map(|program| (program, None))
                .map_err(|error| (error, None))
        },
        true,
        ProvenanceRetention::Retain,
    )
}

fn compile_path_for_execution(
    configuration: RunConfiguration,
) -> Result<CompiledProgram, FileFailure> {
    compile_path_with_consumers_internal(
        configuration,
        &mut InterfaceConstraintBudget::default(),
        validate_interface_evidence_with_budget,
        validate_modular_effect_core,
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
    execute_with_consumer(program, evaluate_compiled_core)
}

fn execute_with_consumer<E>(
    program: &CompiledProgram,
    evaluator: E,
) -> Result<Observation, FileFailure>
where
    E: FnOnce(&CompiledCore) -> Result<Evaluation, RuntimeFailure>,
{
    let metadata = prepare_observation_metadata(program).map_err(|failure| {
        FileFailure::from(PipelineFailure::Runtime(failure))
            .with_compilation_work(program.compilation_work)
    })?;
    execute_prepared(&program.core, metadata, program.compilation_work, evaluator)
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

fn evaluate_compiled_core(core: &CompiledCore) -> Result<Evaluation, RuntimeFailure> {
    match core {
        CompiledCore::Pure(core) => evaluate(core),
        CompiledCore::Effect(core, quote_guards) => {
            crate::eval::evaluate_effect_with_quote_guards(core, quote_guards)
        }
    }
}

fn execute_owned_with_consumer<E>(
    program: CompiledProgram,
    evaluator: E,
) -> Result<Observation, FileFailure>
where
    E: FnOnce(&CompiledCore) -> Result<Evaluation, RuntimeFailure>,
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
    )
}

fn execute_prepared<E>(
    core: &CompiledCore,
    metadata: ObservationMetadata,
    compilation_work: crate::compiler_work::CompilationWork,
    evaluator: E,
) -> Result<Observation, FileFailure>
where
    E: FnOnce(&CompiledCore) -> Result<Evaluation, RuntimeFailure>,
{
    refuse_unbound_source_native_entry(core).map_err(|failure| {
        FileFailure::from(PipelineFailure::Runtime(failure)).with_compilation_work(compilation_work)
    })?;
    let evaluation_phase = crate::calibration::Phase::start("evaluation");
    let evaluation = evaluator(core).map_err(|failure| {
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
        UnvalidatedEffectProgram,
        &[&SourceFile],
        &[(ModuleId, SourceId)],
    ) -> Result<ValidatedEffectProgram, ValidationError>,
    E: FnOnce(&CompiledCore) -> Result<Evaluation, RuntimeFailure>,
{
    run_path_with_consumers_internal(
        configuration,
        &mut InterfaceConstraintBudget::default(),
        interface_validator,
        |program, sources, modules, _linked| {
            validator(program, sources, modules)
                .map(|program| (program, None))
                .map_err(|failure| (failure, None))
        },
        evaluator,
        true,
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
        UnvalidatedEffectProgram,
        &[&SourceFile],
        &[(ModuleId, SourceId)],
    ) -> Result<ValidatedEffectProgram, ValidationError>,
    E: FnOnce(&CompiledCore) -> Result<Evaluation, RuntimeFailure>,
{
    run_path_with_consumers_internal(
        configuration,
        constraint_work,
        interface_validator,
        |program, sources, modules, _linked| {
            validator(program, sources, modules)
                .map(|program| (program, None))
                .map_err(|failure| (failure, None))
        },
        evaluator,
        true,
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
) -> Result<Observation, FileFailure>
where
    I: FnOnce(
        ResolvedModuleProgram,
        &mut InterfaceConstraintBudget,
        &mut TypeWorkBudget,
    ) -> Result<ValidatedInterfaceProgram, EvidenceValidationFailure>,
    V: FnOnce(
        UnvalidatedEffectProgram,
        &[&SourceFile],
        &[(ModuleId, SourceId)],
        &ValidatedInterfaceProgram,
    ) -> ModularEffectCoreResult,
    E: FnOnce(&CompiledCore) -> Result<Evaluation, RuntimeFailure>,
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
    let observation = execute_owned_with_consumer(compiled, evaluator)?;
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
    V: FnOnce(
        UnvalidatedEffectProgram,
        &[&SourceFile],
        &[(ModuleId, SourceId)],
        &ValidatedInterfaceProgram,
    ) -> ModularEffectCoreResult,
{
    let compilation_phase = crate::calibration::Phase::start("compilation");
    let loading_phase = crate::calibration::Phase::start("loading");
    let mut graph =
        discover_headers(&configuration.entry, &configuration.roots).map_err(FileFailure::Graph)?;
    loading_phase.finish(None, 0, 0);
    let result = compile_input_with_consumers(
        &mut CompilationInput::Staged(&mut graph),
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
            if context.sources.is_empty() {
                context.sources = graph.into_sources();
            }
            Err(FileFailure::Pipeline(context))
        }
        other => other,
    }
}

enum CompilationInput<'a> {
    #[cfg(test)]
    Parsed {
        graph: &'a mut ModuleGraph,
        next: usize,
    },
    Staged(&'a mut HeaderGraph),
}

#[cfg(test)]
pub(crate) fn compile_staged_graph_for_test(
    graph: &mut HeaderGraph,
) -> Result<CompiledProgram, FileFailure> {
    compile_input_with_consumers(
        &mut CompilationInput::Staged(graph),
        &mut InterfaceConstraintBudget::default(),
        validate_interface_evidence_with_budget,
        validate_modular_effect_core,
        true,
        ProvenanceRetention::Retain,
    )
}

impl CompilationInput<'_> {
    fn len(&self) -> usize {
        match self {
            #[cfg(test)]
            Self::Parsed { graph, .. } => graph.modules().len(),
            Self::Staged(graph) => graph.len(),
        }
    }

    fn source_work(&self) -> Result<(TypeWorkBudget, usize), ()> {
        match self {
            #[cfg(test)]
            Self::Parsed { graph, .. } => crate::compiler_work::source_work(graph),
            Self::Staged(graph) => graph.source_work(),
        }
    }

    fn has_next(&self) -> bool {
        match self {
            #[cfg(test)]
            Self::Parsed { graph, next } => *next < graph.modules().len(),
            Self::Staged(graph) => graph.has_pending(),
        }
    }

    fn next_imports(&self) -> Option<(&[SurfaceImport], &[crate::module::ModuleDependency])> {
        match self {
            #[cfg(test)]
            Self::Parsed { .. } => None,
            Self::Staged(graph) => graph.next_imports(),
        }
    }

    fn next_quote_dependency(&self) -> Option<crate::module::ModuleDependency> {
        match self {
            #[cfg(test)]
            Self::Parsed { .. } => None,
            Self::Staged(graph) => graph.next_quote_dependency(),
        }
    }

    fn advance(
        &mut self,
        syntax: &[crate::syntax::SelectedSyntax],
        owner_imports: &[Vec<crate::syntax::SelectedSyntax>],
        owners: &mut Vec<crate::syntax::SyntaxOwner>,
        transformer: Option<&mut crate::module::StagedDeclarationTransformer<'_>>,
        quote_owner: Option<crate::syntax::SyntaxOwner>,
    ) -> Result<bool, FileFailure> {
        match self {
            #[cfg(test)]
            Self::Parsed { graph, next } => {
                if *next == graph.modules().len() {
                    Ok(false)
                } else {
                    *next += 1;
                    Ok(true)
                }
            }
            Self::Staged(graph) => {
                if !graph.has_pending() {
                    return Ok(false);
                }
                let phase = crate::calibration::Phase::start("loading");
                let advanced = graph
                    .next_module_with_syntax_and_quote_owner(
                        syntax,
                        owner_imports,
                        owners,
                        transformer,
                        quote_owner,
                    )
                    .map(|module| module.is_some())
                    .map_err(FileFailure::Graph)?;
                phase.finish(None, 0, 0);
                Ok(advanced)
            }
        }
    }

    fn current_with_syntax_budget(
        &mut self,
    ) -> Option<(
        &mut LoadedModule,
        Option<&mut crate::syntax_resource::SyntaxBudget>,
        Option<&mut usize>,
    )> {
        match self {
            #[cfg(test)]
            Self::Parsed { graph, next } => next
                .checked_sub(1)
                .and_then(|i| graph.module_at_mut(i))
                .map(|module| (module, None, None)),
            Self::Staged(graph) => graph
                .current_module_with_syntax_budget()
                .map(|(module, budget, ordinal)| (module, Some(budget), Some(ordinal))),
        }
    }

    #[cfg(feature = "resource-calibration")]
    fn completed(&mut self) -> Option<&ModuleGraph> {
        match self {
            #[cfg(test)]
            Self::Parsed { graph, .. } => Some(graph),
            Self::Staged(graph) => graph.completed_graph(),
        }
    }

    fn completed_with_syntax_budget(
        &mut self,
    ) -> Option<(
        &ModuleGraph,
        Option<&mut crate::syntax_resource::SyntaxBudget>,
    )> {
        match self {
            #[cfg(test)]
            Self::Parsed { graph, .. } => Some((graph, None)),
            Self::Staged(graph) => graph
                .completed_graph_with_syntax_budget()
                .map(|(graph, budget)| (graph, Some(budget))),
        }
    }

    #[cfg(feature = "resource-calibration")]
    fn all_staged_surfaces_loaded(&self) -> bool {
        match self {
            #[cfg(test)]
            Self::Parsed { .. } => false,
            Self::Staged(graph) => graph.all_loaded(),
        }
    }
}

#[cfg(test)]
fn compile_graph_with_consumers<I, V>(
    graph: &mut ModuleGraph,
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
    V: FnOnce(
        UnvalidatedEffectProgram,
        &[&SourceFile],
        &[(ModuleId, SourceId)],
        &ValidatedInterfaceProgram,
    ) -> ModularEffectCoreResult,
{
    compile_input_with_consumers(
        &mut CompilationInput::Parsed { graph, next: 0 },
        constraint_work,
        interface_validator,
        validator,
        select_effect_core,
        retention,
    )
}

fn compile_input_with_consumers<I, V>(
    input: &mut CompilationInput<'_>,
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
    V: FnOnce(
        UnvalidatedEffectProgram,
        &[&SourceFile],
        &[(ModuleId, SourceId)],
        &ValidatedInterfaceProgram,
    ) -> ModularEffectCoreResult,
{
    let mut compilation_work = crate::compiler_work::CompilationWork::default();
    compile_graph_with_report(
        input,
        constraint_work,
        interface_validator,
        validator,
        select_effect_core,
        retention,
        &mut compilation_work,
    )
    .map_err(|failure| failure.with_compilation_work(compilation_work))
}

// Parsing runs before this separate frame, so checking and expansion do not
// reserve their stack while the next module's surface is being projected.
#[inline(never)]
fn check_loaded_module(check: impl FnOnce() -> Result<(), FileFailure>) -> Result<(), FileFailure> {
    check()
}

fn select_imported_syntax<'a>(
    imports: &[SurfaceImport],
    edges: &[crate::module::ModuleDependency],
    mut exports: impl FnMut(
        ModuleId,
    ) -> Result<
        (usize, &'a [crate::surface::SurfaceSyntaxDeclaration]),
        FileFailure,
    >,
) -> Result<Vec<crate::syntax::SelectedSyntax>, FileFailure> {
    let mut selected = Vec::new();
    for (import, edge) in imports
        .iter()
        .zip(edges.iter().filter(|edge| !edge.is_compiler_private()))
    {
        let SurfaceImportSelection::Targeted(items) = &import.selection else {
            continue;
        };
        for item in items {
            let SurfaceImportItem::Syntax { name, alias, .. } = item else {
                continue;
            };
            let (owner, declarations) = exports(edge.target())?;
            let declaration = declarations
                .iter()
                .find(|declaration| declaration.name.text == name.text)
                .ok_or_else(|| {
                    FileFailure::from(PipelineFailure::Resolution(
                        crate::resolve::unavailable_syntax_export(name),
                    ))
                })?;
            let local = alias.as_ref().unwrap_or(name);
            if selected
                .iter()
                .any(|selection: &crate::syntax::SelectedSyntax| selection.name == local.text)
            {
                return Err(FileFailure::from(PipelineFailure::Resolution(
                    crate::resolve::duplicate_syntax_import(local),
                )));
            }
            selected.push(crate::syntax::SelectedSyntax {
                name: local.text.clone(),
                declaration: declaration.clone(),
                owner,
                import_span: import.span,
            });
        }
    }
    Ok(selected)
}

fn compile_graph_with_report<I, V>(
    input: &mut CompilationInput<'_>,
    constraint_work: &mut InterfaceConstraintBudget,
    interface_validator: I,
    validator: V,
    select_effect_core: bool,
    retention: ProvenanceRetention,
    compilation_work: &mut crate::compiler_work::CompilationWork,
) -> Result<CompiledProgram, FileFailure>
where
    I: FnOnce(
        ResolvedModuleProgram,
        &mut InterfaceConstraintBudget,
        &mut TypeWorkBudget,
    ) -> Result<ValidatedInterfaceProgram, EvidenceValidationFailure>,
    V: FnOnce(
        UnvalidatedEffectProgram,
        &[&SourceFile],
        &[(ModuleId, SourceId)],
        &ValidatedInterfaceProgram,
    ) -> ModularEffectCoreResult,
{
    let mut checked: Vec<Arc<crate::resolved::CheckedModule>> = Vec::with_capacity(input.len());
    let mut checked_syntax = Vec::<Vec<crate::surface::SurfaceSyntaxDeclaration>>::new();
    let mut checked_syntax_imports = Vec::<Vec<crate::syntax::SelectedSyntax>>::new();
    let mut checked_syntax_terms = Vec::<crate::syntax::SyntaxOwnerBindings>::new();
    let mut checked_by_module: HashMap<ModuleId, usize> = HashMap::with_capacity(input.len());
    let mut transformer_entries = HashMap::<
        (ModuleId, crate::resolved::BinderId),
        crate::core::validate::ValidatedMacroEntry,
    >::new();
    let (mut checking_type_work, source_bytes) = input.source_work().map_err(|()| {
        FileFailure::from(PipelineFailure::Typing(TypeError::Internal(
            crate::elaborate::ElaborationFailure::TypeResourceExhausted,
        )))
    })?;
    let resolution_normal_limit =
        crate::compiler_work::resolution_total(source_bytes).map_err(|()| {
            FileFailure::from(PipelineFailure::Typing(TypeError::Internal(
                crate::elaborate::ElaborationFailure::TypeResourceExhausted,
            )))
        })?;
    let mut resolution_type_work = TypeWorkBudget::with_limit(crate::calibration::limit(
        resolution_normal_limit,
        crate::calibration::DiagnosticOwner::Structural,
    ));
    let source_normal_limit = checking_type_work.limit();
    // Preserve the existing explicit diagnostic feature, with the paid census
    // already in the same ledger. Ordinary builds retain exactly 10000*S.
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
    compilation_work.source_checking = Some(
        crate::compiler_work::CompilationPhase::SourceChecking
            .assess_with_allowance(checking_type_work.used(), checking_type_work.limit())
            .incomplete(),
    );
    let rewrite_limit = modular_rewrite_limit(source_bytes).map_err(|()| {
        FileFailure::from(PipelineFailure::Typing(TypeError::Internal(
            crate::elaborate::ElaborationFailure::TypeResourceExhausted,
        )))
    })?;
    let mut coverage_work = UsefulnessBudget::default();
    while input.has_next() {
        let selected = if let Some((imports, edges)) = input.next_imports() {
            select_imported_syntax(imports, edges, |target| {
                let index = *checked_by_module
                    .get(&target)
                    .ok_or_else(internal_file_failure)?;
                if checked
                    .get(index)
                    .is_none_or(|dependency| dependency.module() != target)
                {
                    return Err(internal_file_failure());
                }
                Ok((index, checked_syntax.get(index).map_or(&[], Vec::as_slice)))
            })?
        } else {
            Vec::new()
        };
        let mut syntax_owners = Vec::new();
        let quote_owner = input
            .next_quote_dependency()
            .map(|edge| {
                let owner = *checked_by_module
                    .get(&edge.target())
                    .ok_or_else(internal_file_failure)?;
                let dependency = checked.get(owner).ok_or_else(internal_file_failure)?;
                if !dependency.module().is_builtin_compiler_syntax() {
                    return Err(internal_file_failure());
                }
                Ok(crate::syntax::SyntaxOwner {
                    owner: Some(owner),
                    declaration: dependency.span(),
                    import_span: edge.import_span(),
                })
            })
            .transpose()?;
        let mut declaration_failure = None;
        let advanced = {
            let mut transformer =
                |selection: &crate::syntax::SelectedSyntax,
                 adapter: crate::syntax::DeclarationAdapter<'_>,
                 captures: &[crate::surface::SurfaceSyntaxCapture],
                 source: &SourceFile,
                 staged: &crate::module::StagedModuleLoan<'_>,
                 caller: &crate::surface::SurfaceName,
                 introduction: usize,
                 contexts: Arc<crate::syntax::SyntaxContexts>,
                 frame: Arc<crate::syntax::ExpansionFrame>,
                 owners: &mut Vec<crate::syntax::SyntaxOwner>,
                 budget: &mut crate::syntax_resource::SyntaxBudget| {
                    let span = frame.invocation;
                    let result = match adapter {
                        crate::syntax::DeclarationAdapter::Generators(plan) => {
                            evaluate_generator_transformer(
                                plan,
                                selection,
                                captures,
                                source,
                                staged,
                                caller,
                                introduction,
                                frame,
                                &selected,
                                &checked_syntax_imports,
                                &checked,
                                &checked_by_module,
                                &checked_syntax_terms,
                                owners,
                                budget,
                                &mut resolution_type_work,
                                &mut checking_type_work,
                                &mut coverage_work,
                                constraint_work,
                                source_bytes,
                                rewrite_limit,
                            )
                        }
                        other => evaluate_selected_transformer(
                            selection,
                            match other {
                                crate::syntax::DeclarationAdapter::Transformer => None,
                                crate::syntax::DeclarationAdapter::Escape(name) => Some(name),
                                crate::syntax::DeclarationAdapter::Generators(_) => unreachable!(),
                            },
                            captures,
                            source,
                            caller,
                            introduction,
                            TransformerContexts::Shared(contexts),
                            frame,
                            &checked,
                            &mut transformer_entries,
                            constraint_work,
                            Some(&mut *budget),
                            Some(owners),
                        ),
                    }
                    .and_then(|(output, fresh_count)| match output {
                        crate::syntax::TransformerOutput::Expanded(nodes) => {
                            #[cfg(test)]
                            if let Some(observe) = TRANSFORMER_OUTPUT_OBSERVER.get() {
                                observe(selection, captures, &nodes);
                            }
                            Ok((nodes, fresh_count))
                        }
                        crate::syntax::TransformerOutput::Rejected(mut failure) => {
                            if let Some(location) = caller.diagnostic.as_deref() {
                                failure
                                    .retain_invocation_location(location, budget)
                                    .map_err(quote_resource_failure)?;
                            }
                            Err(FileFailure::from(PipelineFailure::SyntaxExpansion(failure)))
                        }
                        crate::syntax::TransformerOutput::SyntaxRejected(failure) => {
                            Err(FileFailure::from(PipelineFailure::SyntaxParse(failure)))
                        }
                    });
                    result.map_err(|failure| {
                        declaration_failure = Some(failure);
                        span
                    })
                };
            input.advance(
                &selected,
                &checked_syntax_imports,
                &mut syntax_owners,
                Some(&mut transformer),
                quote_owner,
            )
        };
        let advanced = match (advanced, declaration_failure) {
            (Err(FileFailure::Graph(graph)), Some(mut failure)) => {
                if let FileFailure::Pipeline(context) = &mut failure {
                    context.sources = graph.into_sources();
                }
                return Err(failure);
            }
            (other, _) => other?,
        };
        if !advanced {
            return Err(internal_file_failure());
        }
        #[cfg(feature = "resource-calibration")]
        if crate::calibration::observing() && input.all_staged_surfaces_loaded() {
            let metrics = crate::calibration::Phase::start("input-metrics");
            let graph = input.completed().ok_or_else(internal_file_failure)?;
            crate::calibration_features::observe_input(graph);
            metrics.finish(None, 0, 0);
        }
        let (module, mut syntax_budget, mut next_quote_ordinal) = input
            .current_with_syntax_budget()
            .ok_or_else(internal_file_failure)?;
        check_loaded_module(|| -> Result<(), FileFailure> {
            let contexts =
                crate::syntax::SyntaxContexts::new(&selected, &checked_syntax_imports, &[]);
            let mut has_escape_probes = false;
            for declaration in &module.surface().syntax_declarations {
                has_escape_probes |= declaration.template_escapes.is_some();
                let admission = if declaration.category
                    != crate::surface::SurfaceSyntaxCategory::Expression
                    && (declaration.contains_quote_or_escape || declaration.contains_generators)
                {
                    let budget = syntax_budget
                        .as_deref_mut()
                        .ok_or_else(internal_file_failure)?;
                    crate::syntax::validate_quote_template_syntax(
                        declaration,
                        module.source(),
                        &contexts,
                        budget,
                    )
                } else {
                    crate::syntax::validate_template_syntax(declaration, module.source(), &contexts)
                };
                match admission {
                    Ok(()) => {}
                    Err(crate::parser::MacroParseFailure::Syntax {
                        diagnostics,
                        resource,
                    }) => {
                        return Err(FileFailure::from(PipelineFailure::Syntax(Box::new(
                            SyntaxFailure {
                                lexical: Vec::new(),
                                parser: diagnostics,
                                resource,
                            },
                        ))));
                    }
                    Err(crate::parser::MacroParseFailure::Invalid) => {
                        return Err(FileFailure::from(PipelineFailure::Resolution(
                            crate::resolve::unsupported_syntax_template(declaration.span),
                        )));
                    }
                }
            }
            let escape_probes = if has_escape_probes {
                let budget = syntax_budget
                    .as_deref_mut()
                    .ok_or_else(internal_file_failure)?;
                module
                    .prepare_escape_probes(budget)
                    .map_err(|failure| match failure {
                        crate::parser::MacroParseFailure::Syntax {
                            diagnostics,
                            resource,
                        } => FileFailure::from(PipelineFailure::Syntax(Box::new(SyntaxFailure {
                            lexical: Vec::new(),
                            parser: diagnostics,
                            resource,
                        }))),
                        crate::parser::MacroParseFailure::Invalid => internal_file_failure(),
                    })?
            } else {
                Vec::new()
            };
            let mut preliminary = !escape_probes.is_empty();
            loop {
                let mut transformer_failure = None;
                let mut transformer =
                |selection: &crate::syntax::SelectedSyntax,
                 captures: &[crate::surface::SurfaceSyntaxCapture],
                 span: Span,
                 caller: &crate::surface::SurfaceName,
                 introduction: usize,
                 owners: &[Option<usize>],
                 frame: &std::sync::Arc<crate::syntax::ExpansionFrame>,
                 constraint_work: &mut crate::interface::InterfaceConstraintBudget,
                 quote_loan: Option<crate::syntax::QuoteExpansionLoan<'_>>| {
                    if let Some(loan) = quote_loan {
                        let resource_failure = |resource| {
                            FileFailure::from(PipelineFailure::SyntaxParse(SyntaxParseFailure {
                                diagnostics: Vec::new(),
                                resource: Some(resource),
                                invocation: span,
                                definition: selection.declaration.span,
                                teardown: None,
                            }))
                        };
                        let contexts = match crate::syntax::SyntaxContexts::new_budgeted_expression(
                            &selected,
                            &checked_syntax_imports,
                            loan.owners,
                            loan.budget,
                        ) {
                            Ok(contexts) => contexts,
                            Err(resource) => {
                                transformer_failure = Some(resource_failure(resource));
                                return Err(span);
                            }
                        };
                        if let Err(resource) = loan.budget.charge_units(2) {
                            transformer_failure = Some(resource_failure(resource));
                            return Err(span);
                        }
                        let mut contexts = Some(Arc::new(contexts));
                        let evaluated = evaluate_selected_transformer(
                            selection,
                            None,
                            captures,
                            module.source(),
                            caller,
                            introduction,
                            TransformerContexts::Quote(&mut contexts),
                            Arc::clone(frame),
                            &checked,
                            &mut transformer_entries,
                            constraint_work,
                            Some(&mut *loan.budget),
                            Some(&mut *loan.owners),
                        );
                        return match evaluated {
                            Ok((
                                crate::syntax::TransformerOutput::Expanded(output),
                                fresh_count,
                            )) => {
                                #[cfg(test)]
                                if let Some(observe) = TRANSFORMER_OUTPUT_OBSERVER.get() {
                                    observe(selection, captures, &output);
                                }
                                let Some(contexts) = contexts.as_deref() else {
                                    transformer_failure = Some(internal_file_failure());
                                    return Err(span);
                                };
                                match crate::parser::parse_macro_expression_with_quotes(
                                    module.source(),
                                    span,
                                    output,
                                    contexts,
                                    frame,
                                    loan.budget,
                                    loan.next_quote_ordinal,
                                    loan.quote_introduction,
                                ) {
                                    Ok(mut expression) => {
                                        expression.expression.span = span;
                                        Ok((expression, fresh_count))
                                    }
                                    Err(crate::parser::MacroParseFailure::Syntax {
                                        diagnostics,
                                        resource,
                                    }) => {
                                        transformer_failure = Some(FileFailure::from(
                                            PipelineFailure::SyntaxParse(SyntaxParseFailure {
                                                diagnostics,
                                                resource,
                                                invocation: span,
                                                definition: selection.declaration.span,
                                                teardown: None,
                                            }),
                                        ));
                                        Err(span)
                                    }
                                    Err(crate::parser::MacroParseFailure::Invalid) => Err(span),
                                }
                            }
                            Ok((crate::syntax::TransformerOutput::Rejected(failure), _)) => {
                                transformer_failure = Some(FileFailure::from(
                                    PipelineFailure::SyntaxExpansion(failure),
                                ));
                                Err(span)
                            }
                            Ok((crate::syntax::TransformerOutput::SyntaxRejected(failure), _)) => {
                                transformer_failure =
                                    Some(FileFailure::from(PipelineFailure::SyntaxParse(failure)));
                                Err(span)
                            }
                            Err(error) => {
                                transformer_failure = Some(error);
                                Err(span)
                            }
                        };
                    }
                    let contexts = std::sync::Arc::new(crate::syntax::SyntaxContexts::new(
                        &selected,
                        &checked_syntax_imports,
                        owners,
                    ));
                    match evaluate_selected_transformer(
                        selection,
                        None,
                        captures,
                        module.source(),
                        caller,
                        introduction,
                        TransformerContexts::Shared(std::sync::Arc::clone(&contexts)),
                        std::sync::Arc::clone(frame),
                        &checked,
                        &mut transformer_entries,
                        constraint_work,
                        None,
                        None,
                    ) {
                        Ok((crate::syntax::TransformerOutput::Expanded(output), fresh_count)) => {
                            #[cfg(test)]
                            if let Some(observe) = TRANSFORMER_OUTPUT_OBSERVER.get() {
                                observe(selection, captures, &output);
                            }
                            match crate::syntax::admit_transformer_output(
                                module.source(),
                                output,
                                &contexts,
                                frame,
                            ) {
                                Ok(expression) => Ok((
                                    crate::syntax::ExpandedExpression {
                                        expression,
                                        quote_sites: Vec::new(),
                                    },
                                    fresh_count,
                                )),
                                Err(crate::parser::MacroParseFailure::Syntax {
                                    diagnostics,
                                    resource,
                                }) => {
                                    transformer_failure = Some(FileFailure::from(
                                        PipelineFailure::SyntaxParse(SyntaxParseFailure {
                                            diagnostics,
                                            resource,
                                            invocation: span,
                                            definition: selection.declaration.span,
                                            teardown: None,
                                        }),
                                    ));
                                    Err(span)
                                }
                                Err(crate::parser::MacroParseFailure::Invalid) => Err(span),
                            }
                        }
                        Ok((crate::syntax::TransformerOutput::Rejected(failure), _)) => {
                            transformer_failure =
                                Some(FileFailure::from(PipelineFailure::SyntaxExpansion(failure)));
                            Err(span)
                        }
                        Ok((crate::syntax::TransformerOutput::SyntaxRejected(failure), _)) => {
                            transformer_failure =
                                Some(FileFailure::from(PipelineFailure::SyntaxParse(failure)));
                            Err(span)
                        }
                        Err(error) => {
                            transformer_failure = Some(error);
                            Err(span)
                        }
                    }
                };
                let owners = if preliminary {
                    let budget = syntax_budget
                        .as_deref_mut()
                        .ok_or_else(internal_file_failure)?;
                    budget
                        .charge_units(syntax_owners.len())
                        .map_err(quote_resource_failure)?;
                    syntax_owners.clone()
                } else {
                    std::mem::take(&mut syntax_owners)
                };
                let mut syntax_expansion = crate::syntax::SyntaxExpansion::new(
                    module.source(),
                    &selected,
                    &checked_syntax_imports,
                    owners,
                    syntax_budget.as_deref_mut(),
                    next_quote_ordinal
                        .as_deref_mut()
                        .zip(module.quote_introduction()),
                    &mut transformer,
                );
                let dependencies = module
                    .dependencies()
                    .iter()
                    .map(|edge| {
                        let dependency = checked_by_module
                            .get(&edge.target())
                            .and_then(|index| checked.get(*index))
                            .ok_or(())?;
                        DependencyExports::new(edge, dependency.exports()).map_err(|_| ())
                    })
                    .collect::<Result<Vec<_>, _>>()
                    .map_err(|()| {
                        FileFailure::from(PipelineFailure::Typing(TypeError::Internal(
                            crate::elaborate::ElaborationFailure::InvalidState,
                        )))
                    })?;
                let resolution_phase = crate::calibration::Phase::start("resolution");
                let resolved = crate::resolve::resolve_module_with_syntax(
                    module,
                    &dependencies,
                    &mut resolution_type_work,
                    constraint_work,
                    &[],
                    &checked,
                    &checked_syntax_terms,
                    Some(&mut syntax_expansion),
                );
                let template_parse_failure = syntax_expansion.take_parse_failure();
                drop(syntax_expansion);
                drop(transformer);
                if let Some(failure) = template_parse_failure {
                    return Err(FileFailure::from(PipelineFailure::SyntaxParse(failure)));
                }
                if let Some(failure) = transformer_failure {
                    return Err(failure);
                }
                let resolved = resolved
                    .map_err(|error| match error {
                        ResolveModuleError::Resolution(error) => match error.syntax_depth() {
                            Some((invocation, definition)) => {
                                PipelineFailure::SyntaxParse(SyntaxParseFailure {
                                    diagnostics: Vec::new(),
                                    resource: Some(ResourceFailure::StructuralDepth {
                                        limit: crate::parser::STRUCTURAL_DEPTH_LIMIT,
                                    }),
                                    invocation,
                                    definition,
                                    teardown: None,
                                })
                            }
                            None => PipelineFailure::Resolution(error),
                        },
                        ResolveModuleError::Kind(error) => PipelineFailure::Kind(error),
                        ResolveModuleError::Representation(error) => PipelineFailure::Typing(error),
                    })
                    .map_err(FileFailure::from)?;
                resolution_phase.finish(
                    Some(resolution_type_work.used()),
                    resolution_normal_limit,
                    resolution_type_work.limit(),
                );
                drop(dependencies);
                let requested = if preliminary {
                    crate::syntax::escape_probe_binders(
                        module.surface(),
                        &resolved,
                        &escape_probes,
                        &mut checking_type_work,
                    )
                    .map_err(|()| {
                        FileFailure::from(PipelineFailure::Typing(TypeError::Internal(
                            crate::elaborate::ElaborationFailure::TypeResourceExhausted,
                        )))
                    })?
                } else {
                    Vec::new()
                };
                let source_phase = crate::calibration::Phase::start("source-checking");
                let primary_work = Some(TypeWorkBudget::with_limit(
                    modular_primary_limit(source_bytes).map_err(|()| {
                        FileFailure::from(PipelineFailure::Typing(TypeError::Internal(
                            crate::elaborate::ElaborationFailure::TypeResourceExhausted,
                        )))
                    })?,
                ));
                let rewrite_work = Some(TypeWorkBudget::with_limit(rewrite_limit));
                let mut quote_resource = None;
                let checked_module = if preliminary {
                    crate::elaborate::check_escape_probes_with_quote_work(
                        resolved,
                        &mut checking_type_work,
                        &mut coverage_work,
                        constraint_work,
                        primary_work,
                        rewrite_work,
                        syntax_budget.as_deref_mut(),
                        &mut quote_resource,
                        &requested,
                    )
                    .map(|(module, results)| (module, Some(results)))
                } else if select_effect_core {
                    crate::elaborate::check_module_in_effect_profile_with_quote_work(
                        resolved,
                        &mut checking_type_work,
                        &mut coverage_work,
                        constraint_work,
                        primary_work,
                        rewrite_work,
                        syntax_budget.as_deref_mut(),
                        &mut quote_resource,
                    )
                    .map(|module| (module, None))
                } else {
                    check_module_with_budget_and_rewrite_work(
                        resolved,
                        &mut checking_type_work,
                        &mut coverage_work,
                        constraint_work,
                        primary_work,
                        rewrite_work,
                    )
                    .map(|module| (module, None))
                };
                if let Some(resource) = quote_resource {
                    return Err(FileFailure::from(PipelineFailure::Syntax(Box::new(
                        SyntaxFailure {
                            lexical: Vec::new(),
                            parser: Vec::new(),
                            resource: Some(resource),
                        },
                    ))));
                }
                let (checked_module, probe_results) = checked_module.map_err(|failure| {
                    FileFailure::from(PipelineFailure::Typing(failure)).with_phase_work(
                        crate::compiler_work::CompilationPhase::SourceChecking
                            .assess_with_allowance(
                                checking_type_work.used(),
                                checking_type_work.limit(),
                            )
                            .incomplete(),
                    )
                })?;
                if let Some(results) = probe_results {
                    checking_type_work
                        .charge(module.dependencies().len().saturating_add(2))
                        .map_err(|()| {
                            FileFailure::from(PipelineFailure::Typing(TypeError::Internal(
                                crate::elaborate::ElaborationFailure::TypeResourceExhausted,
                            )))
                        })?;
                    let builtin = module
                        .dependencies()
                        .iter()
                        .find(|edge| edge.target().is_builtin_compiler_syntax())
                        .and_then(|edge| checked_by_module.get(&edge.target()))
                        .and_then(|index| checked.get(*index))
                        .ok_or_else(internal_file_failure)?;
                    checking_type_work.charge(requested.len()).map_err(|()| {
                        FileFailure::from(PipelineFailure::Typing(TypeError::Internal(
                            crate::elaborate::ElaborationFailure::TypeResourceExhausted,
                        )))
                    })?;
                    let mut categories = Vec::new();
                    categories
                        .try_reserve_exact(requested.len())
                        .map_err(|_| internal_file_failure())?;
                    for (index, binder) in requested.iter().enumerate() {
                        let mut selected = None;
                        for result in &results {
                            checking_type_work.charge(1).map_err(|()| {
                                FileFailure::from(PipelineFailure::Typing(TypeError::Internal(
                                    crate::elaborate::ElaborationFailure::TypeResourceExhausted,
                                )))
                            })?;
                            if result.binder == *binder {
                                selected = Some(result);
                                break;
                            }
                        }
                        let result = selected.ok_or_else(internal_file_failure)?;
                        let _ = result.origin();
                        let category = crate::syntax::escape_result_category(
                            result.ty(),
                            builtin,
                            &mut checking_type_work,
                        )
                        .map_err(|()| {
                            FileFailure::from(PipelineFailure::Typing(TypeError::Internal(
                                crate::elaborate::ElaborationFailure::TypeResourceExhausted,
                            )))
                        })?;
                        let category = match category {
                            Some(category) => category,
                            // These closed builtin atoms cannot be a syntax
                            // fragment. Finish the existing expression shell
                            // and let the full ordinary module check diagnose
                            // the unchanged initializer against its result.
                            None if matches!(
                                result.ty(),
                                Type::Bytes | Type::String | Type::Int | Type::Bool | Type::Unit
                            ) =>
                            {
                                crate::syntax::EscapeResultCategory::Expression
                            }
                            None => {
                                return Err(FileFailure::from(PipelineFailure::Resolution(
                                    crate::resolve::unsupported_syntax_template(
                                        module.surface().definitions[escape_probes[index]].span,
                                    ),
                                )));
                            }
                        };
                        checking_type_work.charge(1).map_err(|()| {
                            FileFailure::from(PipelineFailure::Typing(TypeError::Internal(
                                crate::elaborate::ElaborationFailure::TypeResourceExhausted,
                            )))
                        })?;
                        categories.push((category, result.effects().is_empty()));
                    }
                    drop(checked_module);
                    drop(results);
                    let budget = syntax_budget
                        .as_deref_mut()
                        .ok_or_else(internal_file_failure)?;
                    module
                        .finish_escape_probes(&escape_probes, &categories, budget)
                        .map_err(|failure| match failure {
                            crate::parser::MacroParseFailure::Syntax {
                                diagnostics,
                                resource,
                            } => FileFailure::from(PipelineFailure::Syntax(Box::new(
                                SyntaxFailure {
                                    lexical: Vec::new(),
                                    parser: diagnostics,
                                    resource,
                                },
                            ))),
                            crate::parser::MacroParseFailure::Invalid => internal_file_failure(),
                        })?;
                    preliminary = false;
                    continue;
                }
                crate::syntax::validate_transformers(
                    &checked_module,
                    &checked,
                    &module.surface().syntax_declarations,
                )
                .map_err(|span| {
                    FileFailure::from(PipelineFailure::Resolution(
                        crate::resolve::invalid_syntax_transformer(span),
                    ))
                })?;
                let syntax_terms = if module.surface().syntax_declarations.is_empty()
                    && !module.id().is_builtin_compiler_syntax()
                    && module.quote_sites().is_empty()
                {
                    crate::syntax::SyntaxOwnerBindings::empty(checked_module.module())
                } else {
                    crate::syntax::SyntaxOwnerBindings::new(
                        &checked_module,
                        module,
                        &checked,
                        &mut checking_type_work,
                    )
                    .map_err(|()| {
                        FileFailure::from(PipelineFailure::Typing(TypeError::Internal(
                            crate::elaborate::ElaborationFailure::TypeResourceExhausted,
                        )))
                    })?
                };
                checked_by_module.insert(module.id(), checked.len());
                checked_syntax.push(module.surface().syntax_declarations.clone());
                checked_syntax_imports.push(selected);
                checked_syntax_terms.push(syntax_terms);
                checked.push(Arc::new(checked_module));
                source_phase.finish(
                    Some(checking_type_work.used()),
                    source_normal_limit,
                    checking_type_work.limit(),
                );
                compilation_work.source_checking = Some(
                    crate::compiler_work::CompilationPhase::SourceChecking
                        .assess_with_allowance(
                            checking_type_work.used(),
                            checking_type_work.limit(),
                        )
                        .incomplete(),
                );
                break;
            }
            Ok(())
        })?;
    }

    let (graph, syntax_work) = input
        .completed_with_syntax_budget()
        .ok_or_else(internal_file_failure)?;
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
        _ => return Err(entry_failure(EntryReason::MainDomain, main_span)),
    };
    if main_has_effects {
        let Type::EffectfulFunction(_, computation) = &main.scheme.value_type else {
            return Err(internal_file_failure());
        };
        // Reuse the checked graph's defining-module index. The entry's local
        // registry excludes imported symbols; rebuilding a checker view would
        // repeat completed preparation and copy its immutable contracts.
        // The generated root supplies only the authenticated private default
        // service. Every other entry effect still needs its native contract.
        let mut entry_row = crate::types::clone_effect_row_with_budget(
            computation.effects(),
            &mut checking_type_work,
        )
        .map_err(|()| internal_file_failure())?;
        for instance in computation.effects().known() {
            checking_type_work
                .charge(1)
                .map_err(|()| internal_file_failure())?;
            if crate::resolved::RegionApi::for_module(instance.effect().module())
                .is_some_and(|api| api.default_alloc() == instance.effect())
                && instance.arguments().is_empty()
            {
                entry_row = entry_row
                    .remove_exact_with_budget(instance, &mut checking_type_work)
                    .map_err(|()| internal_file_failure())?
                    .map_err(|_| internal_file_failure())?;
            }
        }
        let native_entry = select_effect_core
            && crate::core::effect::owner_free_native_entry_row(
                |effect| {
                    checked_by_module
                        .get(&effect.module())
                        .and_then(|index| checked.get(*index))
                        .filter(|module| module.module() == effect.module())
                        .map(|module| module.registry().as_ref())
                },
                &entry_row,
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
        resolution_normal_limit,
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
    let checked = checked
        .into_iter()
        .map(|owner| Arc::try_unwrap(owner).map_err(|_| internal_file_failure()))
        .collect::<Result<Vec<_>, _>>()?;
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
        // Every admitted file graph retains the compiler-owned Region module,
        // whose checked schemes select Effect Core even for an empty-row main.
        if select_effect_core {
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
                validated_interfaces,
                &sources,
                &module_sources,
                compilation_work,
                main_has_effects.then_some(main_span),
                validator,
                syntax_work,
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
        let registry = Arc::clone(validated_interfaces.registry());
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
            TypeWorkBudget::with_limit(modular_primary_limit(source_bytes).map_err(|()| {
                FileFailure::from(PipelineFailure::Typing(TypeError::Internal(
                    crate::elaborate::ElaborationFailure::TypeResourceExhausted,
                )))
            })?),
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
        validate_modular_core,
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

#[cfg(test)]
std::thread_local! {
    static TRANSFORMER_ENTRY_PREPARATIONS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
    static TRANSFORMER_ENTRY_VALIDATIONS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
    static TRANSFORMER_OUTPUT_OBSERVER: std::cell::Cell<Option<TransformerOutputObserver>> = const { std::cell::Cell::new(None) };
    static GENERATOR_OWNER_OBSERVER: std::cell::Cell<Option<fn(&crate::resolved::CheckedModule, &crate::syntax::GeneratorPlan)>> = const { std::cell::Cell::new(None) };
    static GENERATOR_LIFECYCLE_OBSERVER: std::cell::Cell<Option<fn([usize; 5], [usize; 5])>> = const { std::cell::Cell::new(None) };
}

#[cfg(test)]
type TransformerOutputObserver = fn(
    &crate::syntax::SelectedSyntax,
    &[crate::surface::SurfaceSyntaxCapture],
    &[crate::syntax::MacroOutputNode],
);

// Keep invocation inputs separate so their borrows and ownership stay explicit.
enum TransformerContexts<'a> {
    Shared(Arc<crate::syntax::SyntaxContexts>),
    Quote(&'a mut Option<Arc<crate::syntax::SyntaxContexts>>),
}

#[allow(clippy::too_many_arguments)]
fn evaluate_generator_transformer(
    plan: &crate::syntax::GeneratorPlan,
    selection: &crate::syntax::SelectedSyntax,
    captures: &[crate::surface::SurfaceSyntaxCapture],
    source: &SourceFile,
    staged: &crate::module::StagedModuleLoan<'_>,
    caller: &crate::surface::SurfaceName,
    introduction: usize,
    frame: Arc<crate::syntax::ExpansionFrame>,
    selected: &[crate::syntax::SelectedSyntax],
    selected_imports: &[Vec<crate::syntax::SelectedSyntax>],
    checked: &[Arc<crate::resolved::CheckedModule>],
    checked_by_module: &HashMap<ModuleId, usize>,
    checked_terms: &[crate::syntax::SyntaxOwnerBindings],
    owners: &mut Vec<crate::syntax::SyntaxOwner>,
    budget: &mut crate::syntax_resource::SyntaxBudget,
    resolution_work: &mut TypeWorkBudget,
    checking_work: &mut TypeWorkBudget,
    coverage_work: &mut UsefulnessBudget,
    constraint_work: &mut InterfaceConstraintBudget,
    source_bytes: usize,
    rewrite_limit: usize,
) -> Result<(crate::syntax::TransformerOutput, usize), FileFailure> {
    let selected_owner = checked
        .get(selection.owner)
        .ok_or_else(internal_file_failure)?;
    #[cfg(test)]
    if let Some(observe) = GENERATOR_OWNER_OBSERVER.get() {
        observe(selected_owner, plan);
    }
    budget
        .charge_units(
            selected_owner
                .direct_dependencies()
                .len()
                .saturating_add(checked.len())
                .saturating_add(2),
        )
        .map_err(quote_resource_failure)?;
    let route = selected_owner
        .direct_dependencies()
        .iter()
        .find(|edge| edge.target().is_builtin_compiler_syntax())
        .ok_or_else(internal_file_failure)?;
    let builtin_index = *checked_by_module
        .get(&route.target())
        .ok_or_else(internal_file_failure)?;
    let builtin = checked
        .get(builtin_index)
        .ok_or_else(internal_file_failure)?;
    let live = owners.len();
    budget
        .charge_units(if live == owners.capacity() {
            live.saturating_mul(2).saturating_add(1)
        } else {
            1
        })
        .map_err(quote_resource_failure)?;
    if live == owners.capacity() {
        owners.reserve_exact(1);
    }
    owners.push(crate::syntax::SyntaxOwner {
        owner: Some(builtin_index),
        declaration: builtin.span(),
        import_span: route.import_span(),
    });
    let builtin_introduction = owners.len();
    let bindings = checked_terms
        .get(selection.owner)
        .ok_or_else(internal_file_failure)?;
    if bindings.module != selected_owner.module() {
        return Err(internal_file_failure());
    }
    let type_resource = |()| {
        FileFailure::from(PipelineFailure::Typing(TypeError::Internal(
            crate::elaborate::ElaborationFailure::TypeResourceExhausted,
        )))
    };
    checking_work
        .charge(plan.actions.len())
        .map_err(type_resource)?;
    let mut escape_categories = Vec::with_capacity(plan.actions.len());
    for action in &plan.actions {
        let category = if let crate::syntax::GeneratorAction::Escape {
            escapes,
            descriptor,
            ..
        } = action
        {
            let escape = escapes.get(*descriptor).ok_or_else(internal_file_failure)?;
            checking_work
                .charge(escape.adapter.text.len().saturating_add(1))
                .map_err(type_resource)?;
            let fact = bindings
                .get(&escape.adapter.text)
                .ok_or_else(internal_file_failure)?;
            if fact.binder.module() != Some(selected_owner.module())
                || !fact.scheme.type_parameters.is_empty()
                || !fact.scheme.requirements.is_empty()
            {
                return Err(internal_file_failure());
            }
            let result = match fact.scheme.value_type() {
                crate::types::Type::Function(_, result) => result.as_ref(),
                crate::types::Type::EffectfulFunction(_, result) => result.value(),
                _ => return Err(internal_file_failure()),
            };
            Some(
                crate::syntax::escape_result_category(result, builtin, checking_work)
                    .map_err(type_resource)?
                    .ok_or_else(internal_file_failure)?,
            )
        } else {
            None
        };
        escape_categories.push(category);
    }
    let (definition, uses) = crate::syntax::generator_adapter_definition(
        plan,
        &escape_categories,
        &selection.declaration.matcher,
        captures,
        introduction,
        builtin_introduction,
        owners,
        frame.invocation,
        budget,
    )
    .map_err(|error| match error {
        crate::parser::MacroParseFailure::Syntax {
            diagnostics,
            resource,
        } => FileFailure::from(PipelineFailure::SyntaxParse(SyntaxParseFailure {
            diagnostics,
            resource,
            invocation: frame.invocation,
            definition: selection.declaration.span,
            teardown: None,
        })),
        crate::parser::MacroParseFailure::Invalid => internal_file_failure(),
    })?;
    let module = staged
        .no_quote_adapter_view(source, definition, budget)
        .map_err(quote_resource_failure)?;
    budget
        .charge_units(module.dependencies().len())
        .map_err(quote_resource_failure)?;
    let dependencies = module
        .dependencies()
        .iter()
        .map(|edge| {
            let dependency = checked_by_module
                .get(&edge.target())
                .and_then(|index| checked.get(*index))
                .ok_or_else(internal_file_failure)?;
            DependencyExports::new(edge, dependency.exports()).map_err(|_| internal_file_failure())
        })
        .collect::<Result<Vec<_>, _>>()?;
    budget
        .charge_units(owners.len())
        .map_err(quote_resource_failure)?;
    let mut nested =
        |_: &crate::syntax::SelectedSyntax,
         _: &[crate::surface::SurfaceSyntaxCapture],
         span: Span,
         _: &crate::surface::SurfaceName,
         _: usize,
         _: &[Option<usize>],
         _: &Arc<crate::syntax::ExpansionFrame>,
         _: &mut InterfaceConstraintBudget,
         _: Option<crate::syntax::QuoteExpansionLoan<'_>>| Err(span);
    let mut expansion = crate::syntax::SyntaxExpansion::new(
        source,
        selected,
        selected_imports,
        owners.to_vec(),
        Some(&mut *budget),
        None,
        &mut nested,
    );
    let resolved = crate::resolve::resolve_module_with_syntax(
        &module,
        &dependencies,
        resolution_work,
        constraint_work,
        &uses,
        checked,
        checked_terms,
        Some(&mut expansion),
    );
    let parse_failure = expansion.take_parse_failure();
    drop(expansion);
    if let Some(failure) = parse_failure {
        return Err(FileFailure::from(PipelineFailure::SyntaxParse(failure)));
    }
    let resolved = resolved
        .map_err(|error| match error {
            ResolveModuleError::Resolution(error) => PipelineFailure::Resolution(error),
            ResolveModuleError::Kind(error) => PipelineFailure::Kind(error),
            ResolveModuleError::Representation(error) => PipelineFailure::Typing(error),
        })
        .map_err(FileFailure::from)?;
    let primary = TypeWorkBudget::with_limit(
        modular_primary_limit(source_bytes).map_err(|()| internal_file_failure())?,
    );
    let rewrite = TypeWorkBudget::with_limit(rewrite_limit);
    let mut quote_resource = None;
    let checked_module = crate::elaborate::check_module_in_effect_profile_with_quote_work(
        resolved,
        checking_work,
        coverage_work,
        constraint_work,
        Some(primary),
        Some(rewrite),
        Some(&mut *budget),
        &mut quote_resource,
    );
    if let Some(error) = quote_resource {
        return Err(quote_resource_failure(error));
    }
    let checked_module = checked_module
        .map_err(PipelineFailure::Typing)
        .map_err(FileFailure::from)?;
    budget.charge().map_err(quote_resource_failure)?;
    let checked_module = Arc::new(checked_module);
    let binder = checked_module
        .schemes()
        .iter()
        .find(|scheme| scheme.spelling == "\0ash_generator_adapter")
        .map(|scheme| scheme.binder)
        .ok_or_else(internal_file_failure)?;
    budget
        .charge_units(checked.len().saturating_add(2))
        .map_err(quote_resource_failure)?;
    let mut local = Vec::with_capacity(checked.len().saturating_add(1));
    local.extend(checked.iter().cloned());
    local.push(Arc::clone(&checked_module));
    let entry = prepare_transformer_entry(
        &checked_module,
        binder,
        &local,
        constraint_work,
        Some(&mut *budget),
    )?;
    let contexts =
        crate::syntax::SyntaxContexts::new_budgeted(selected, selected_imports, owners, budget)
            .map_err(quote_resource_failure)?;
    budget.charge().map_err(quote_resource_failure)?;
    #[cfg(test)]
    let lifecycle_before = generator_lifecycle_counters();
    let evaluated = crate::eval::evaluate_transformer_with_owners(
        &entry,
        // Only selected scalar leaves are exposed through the existing host.
        &plan.captures,
        source,
        caller,
        introduction,
        Arc::new(contexts),
        Arc::clone(&frame),
        Some(&mut *budget),
        Some(owners),
    );
    #[cfg(test)]
    if let Some(observe) = GENERATOR_LIFECYCLE_OBSERVER.get() {
        observe(lifecycle_before, generator_lifecycle_counters());
    }
    evaluated.map_err(|cause| {
        FileFailure::from(PipelineFailure::SyntaxRuntime(SyntaxRuntimeFailure {
            cause,
            invocation: frame.invocation,
            definition: selection.declaration.span,
        }))
    })
}

#[cfg(test)]
fn generator_lifecycle_counters() -> [usize; 5] {
    use crate::eval::machine_test_hooks as hooks;
    [
        hooks::TRANSFER_ATTEMPTS.get(),
        hooks::TRANSFER_FAILURES.get(),
        hooks::ROOT_CLOSES.get(),
        hooks::TRANSFORMER_DROPS.get(),
        hooks::ACTIVE_ROOT_DROPS.get(),
    ]
}

#[allow(clippy::too_many_arguments)]
fn evaluate_selected_transformer(
    selection: &crate::syntax::SelectedSyntax,
    adapter: Option<&crate::surface::SurfaceName>,
    captures: &[crate::surface::SurfaceSyntaxCapture],
    source: &SourceFile,
    caller: &crate::surface::SurfaceName,
    introduction: usize,
    contexts: TransformerContexts<'_>,
    frame: Arc<crate::syntax::ExpansionFrame>,
    checked: &[Arc<crate::resolved::CheckedModule>],
    entries: &mut HashMap<
        (ModuleId, crate::resolved::BinderId),
        crate::core::validate::ValidatedMacroEntry,
    >,
    constraint_work: &mut InterfaceConstraintBudget,
    mut syntax_work: Option<&mut crate::syntax_resource::SyntaxBudget>,
    staged_owners: Option<&mut Vec<crate::syntax::SyntaxOwner>>,
) -> Result<(crate::syntax::TransformerOutput, usize), FileFailure> {
    let (owner, binder) = transformer_owner_and_binder(selection, adapter, checked)?;
    let entry = match entries.entry((owner.module(), binder)) {
        std::collections::hash_map::Entry::Occupied(entry) => entry.into_mut(),
        std::collections::hash_map::Entry::Vacant(entry) => {
            entry.insert(prepare_transformer_entry(
                owner,
                binder,
                checked,
                constraint_work,
                syntax_work.as_deref_mut(),
            )?)
        }
    };
    let invocation = frame.invocation;
    let staged_owners =
        if entry.quote_sites.is_empty() && matches!(&contexts, TransformerContexts::Shared(_)) {
            None
        } else {
            staged_owners
        };
    let result = match contexts {
        TransformerContexts::Shared(contexts) => crate::eval::evaluate_transformer_with_owners(
            entry,
            captures,
            source,
            caller,
            introduction,
            contexts,
            frame,
            syntax_work,
            staged_owners,
        ),
        TransformerContexts::Quote(contexts) => {
            crate::eval::evaluate_transformer_with_context_slot(
                entry,
                captures,
                source,
                caller,
                introduction,
                contexts,
                frame,
                syntax_work,
                staged_owners,
            )
        }
    };
    result.map_err(|cause| {
        FileFailure::from(PipelineFailure::SyntaxRuntime(SyntaxRuntimeFailure {
            cause,
            invocation,
            definition: selection.declaration.span,
        }))
    })
}

fn transformer_owner_and_binder<'a>(
    selection: &crate::syntax::SelectedSyntax,
    adapter: Option<&crate::surface::SurfaceName>,
    checked: &'a [Arc<crate::resolved::CheckedModule>],
) -> Result<
    (
        &'a crate::resolved::CheckedModule,
        crate::resolved::BinderId,
    ),
    FileFailure,
> {
    let owner = checked
        .get(selection.owner)
        .ok_or_else(internal_file_failure)?;
    let name = match (adapter, &selection.declaration.implementation) {
        (Some(name), crate::surface::SurfaceSyntaxImplementation::Template) => name,
        (None, crate::surface::SurfaceSyntaxImplementation::Transformer(name)) => name,
        _ => return Err(internal_file_failure()),
    };
    let binder = owner
        .schemes()
        .iter()
        .find(|scheme| scheme.spelling == name.text)
        .map(|scheme| scheme.binder)
        .ok_or_else(internal_file_failure)?;
    Ok((owner, binder))
}

fn prepare_transformer_entry(
    owner: &crate::resolved::CheckedModule,
    binder: crate::resolved::BinderId,
    checked: &[Arc<crate::resolved::CheckedModule>],
    constraint_work: &mut InterfaceConstraintBudget,
    mut syntax_work: Option<&mut crate::syntax_resource::SyntaxBudget>,
) -> Result<crate::core::validate::ValidatedMacroEntry, FileFailure> {
    #[cfg(test)]
    TRANSFORMER_ENTRY_PREPARATIONS.set(TRANSFORMER_ENTRY_PREPARATIONS.get() + 1);
    let mut reachable = std::collections::HashSet::new();
    let mut pending = vec![owner.module()];
    while let Some(id) = pending.pop() {
        if !reachable.insert(id) {
            continue;
        }
        let module = checked
            .iter()
            .find(|module| module.module() == id)
            .ok_or_else(internal_file_failure)?;
        pending.extend(
            module
                .direct_dependencies()
                .iter()
                .map(|edge| edge.target()),
        );
    }
    let modules = checked
        .iter()
        .filter(|module| reachable.contains(&module.module()))
        .cloned()
        .collect::<Vec<_>>();
    let syntax_module = modules
        .iter()
        .find(|module| module.module().is_builtin_compiler_syntax())
        .map(|module| module.module())
        .ok_or_else(internal_file_failure)?;
    let retained_sources = owner.exports().defining_sources();
    let sources = modules
        .iter()
        .map(|module| {
            retained_sources
                .iter()
                .find(|(id, _)| *id == module.module())
                .map(|(_, source)| source.as_ref())
                .ok_or_else(internal_file_failure)
        })
        .collect::<Result<Vec<_>, _>>()?;
    let module_sources = modules
        .iter()
        .zip(&sources)
        .map(|(module, source)| (module.module(), source.id()))
        .collect::<Vec<_>>();
    let mut work = TypeWorkBudget::default();
    let linked = crate::elaborate::link_transformer_modules(
        modules,
        owner.module(),
        binder,
        constraint_work,
        &mut work,
    )
    .map_err(PipelineFailure::Typing)
    .map_err(FileFailure::from)?;
    let linked = validate_interface_evidence_with_budget(linked, constraint_work, &mut work)
        .map_err(PipelineFailure::EvidenceValidation)
        .map_err(FileFailure::from)?;
    let mut elaborator = EffectElaborator::for_module_program(&linked)
        .map_err(TypeError::Internal)
        .map_err(PipelineFailure::Typing)
        .map_err(FileFailure::from)?;
    elaborator.set_quote_syntax_work(syntax_work.as_deref_mut().map(std::mem::take));
    let synthesis = elaborator.synthesize_effect_transformer_program(&linked);
    let (returned_work, quote_failure) = elaborator.take_quote_syntax_work();
    if let (Some(destination), Some(work)) = (syntax_work.as_deref_mut(), returned_work) {
        *destination = work;
    }
    if let Some(resource) = quote_failure {
        return Err(quote_resource_failure(resource));
    }
    let typed = synthesis
        .map_err(PipelineFailure::Typing)
        .map_err(FileFailure::from)?;
    let quote_sites = elaborator.take_checked_quote_sites();
    let _ty = IterativeTypeOwner::new(typed.ty);
    let program = elaborator
        .finish(typed.node)
        .map_err(TypeError::Internal)
        .map_err(PipelineFailure::Typing)
        .map_err(FileFailure::from)?;
    #[cfg(test)]
    TRANSFORMER_ENTRY_VALIDATIONS.set(TRANSFORMER_ENTRY_VALIDATIONS.get() + 1);
    let mut entry = crate::core::validate::validate_effect_macro_modules_linked_with_work(
        program,
        &sources,
        &module_sources,
        &linked,
        binder,
        syntax_module,
        &mut work,
    )
    .map_err(PipelineFailure::Validation)
    .map_err(FileFailure::from)?;
    if !quote_sites.is_empty() {
        let budget = syntax_work.ok_or_else(internal_file_failure)?;
        budget
            .charge_units(quote_sites.len())
            .map_err(quote_resource_failure)?;
        let mut prepared = Vec::new();
        prepared
            .try_reserve_exact(quote_sites.len())
            .map_err(|_| internal_file_failure())?;
        for nodes in quote_sites {
            let mut owner_index = None;
            for (index, checked_owner) in checked.iter().enumerate() {
                budget.charge().map_err(quote_resource_failure)?;
                if checked_owner.module() == nodes.owner {
                    owner_index = Some(index);
                    break;
                }
            }
            let owner_index = owner_index.ok_or_else(internal_file_failure)?;
            let mut source = None;
            for (module, candidate) in retained_sources {
                budget.charge().map_err(quote_resource_failure)?;
                if *module == nodes.owner && candidate.id() == nodes.template.origin.source() {
                    budget.charge().map_err(quote_resource_failure)?;
                    source = Some(Arc::clone(candidate));
                    break;
                }
            }
            prepared.push(crate::syntax::PreparedQuoteSite {
                nodes,
                owner: owner_index,
                source: source.ok_or_else(internal_file_failure)?,
            });
        }
        budget
            .charge_units(prepared.len().saturating_mul(2).saturating_add(1))
            .map_err(quote_resource_failure)?;
        entry.quote_sites = Arc::from(prepared.into_boxed_slice());
    }
    Ok(entry)
}

fn quote_resource_failure(resource: ResourceFailure) -> FileFailure {
    FileFailure::from(PipelineFailure::Syntax(Box::new(SyntaxFailure {
        lexical: Vec::new(),
        parser: Vec::new(),
        resource: Some(resource),
    })))
}

fn modular_primary_limit(source_bytes: usize) -> Result<usize, ()> {
    Ok(crate::calibration::limit(
        crate::compiler_work::primary_total(source_bytes)?,
        crate::calibration::DiagnosticOwner::Structural,
    ))
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

type ModularEffectCoreResult = Result<
    (
        ValidatedEffectProgram,
        Option<crate::compiler_work::PhaseCost>,
    ),
    (ValidationError, Option<crate::compiler_work::PhaseCost>),
>;

fn validate_modular_effect_core(
    program: UnvalidatedEffectProgram,
    sources: &[&SourceFile],
    modules: &[(ModuleId, SourceId)],
    linked: &ValidatedInterfaceProgram,
) -> ModularEffectCoreResult {
    let phase = crate::compiler_work::CompilationPhase::IndependentCore;
    let validation_phase = crate::calibration::Phase::start("independent-effect-core");
    let (mut work, normal_limit, _) = match modular_phase_work(phase, sources) {
        Ok(work) => work,
        Err(()) => {
            return Err((ValidationError::resource_exhausted(program), None));
        }
    };
    let result = crate::core::validate::validate_effect_modules_linked_with_work(
        program, sources, modules, linked, &mut work,
    );
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
fn finish_effect_compilation<V>(
    validated_interfaces: ValidatedInterfaceProgram,
    sources: &[&SourceFile],
    module_sources: &[(ModuleId, SourceId)],
    compilation_work: &mut crate::compiler_work::CompilationWork,
    native_entry_span: Option<Span>,
    validator: V,
    mut syntax_work: Option<&mut crate::syntax_resource::SyntaxBudget>,
) -> Result<CompiledProgram, FileFailure>
where
    V: FnOnce(
        UnvalidatedEffectProgram,
        &[&SourceFile],
        &[(ModuleId, SourceId)],
        &ValidatedInterfaceProgram,
    ) -> ModularEffectCoreResult,
{
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
        &validated_interfaces,
        final_budget,
        TypeWorkBudget::with_limit(modular_primary_limit(source_bytes).map_err(|()| {
            FileFailure::from(PipelineFailure::Typing(TypeError::Internal(
                crate::elaborate::ElaborationFailure::TypeResourceExhausted,
            )))
        })?),
        rewrite_budget,
    )
    .map_err(|(failure, used)| {
        FileFailure::from(PipelineFailure::Typing(TypeError::Internal(failure))).with_phase_work(
            crate::compiler_work::CompilationPhase::FinalElaboration
                .assess_with_allowance(used, final_limit)
                .incomplete(),
        )
    })?;
    elaborator.set_quote_syntax_work(syntax_work.as_deref_mut().map(std::mem::take));
    let synthesis = elaborator.synthesize_effect_module_program(&validated_interfaces);
    let (returned_work, quote_failure) = elaborator.take_quote_syntax_work();
    if let (Some(destination), Some(work)) = (syntax_work.as_deref_mut(), returned_work) {
        *destination = work;
    }
    if let Some(resource) = quote_failure {
        return Err(quote_resource_failure(resource));
    }
    let typed = synthesis.map_err(|failure| {
        FileFailure::from(PipelineFailure::Typing(failure)).with_phase_work(
            crate::compiler_work::CompilationPhase::FinalElaboration
                .assess_with_allowance(elaborator.measured_type_work(), final_limit)
                .incomplete(),
        )
    })?;
    let quote_sites = elaborator.take_checked_quote_sites();
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
    let (validated, core_work) =
        validator(unchecked, sources, module_sources, &validated_interfaces).map_err(
            |(failure, cost)| {
                let failure = FileFailure::from(PipelineFailure::Validation(failure))
                    .with_compilation_work(*compilation_work);
                match cost {
                    Some(cost) => failure.with_phase_work(cost),
                    None => failure,
                }
            },
        )?;
    compilation_work.independent_core = core_work;
    let quote_guards = if quote_sites.is_empty() {
        Arc::from([])
    } else {
        let budget = syntax_work.ok_or_else(internal_file_failure)?;
        budget
            .charge_units(quote_sites.len().saturating_mul(3).saturating_add(1))
            .map_err(quote_resource_failure)?;
        let mut guards = Vec::new();
        guards
            .try_reserve_exact(quote_sites.len())
            .map_err(|_| internal_file_failure())?;
        for site in quote_sites {
            let node = validated
                .node(site.constructor_result)
                .ok_or_else(internal_file_failure)?;
            let crate::core::EffectExprKind::Operation(crate::core::EffectOperation::RegionTuple(
                tuple,
            )) = &node.kind
            else {
                return Err(internal_file_failure());
            };
            if tuple.constructor != Some(site.constructor) {
                return Err(internal_file_failure());
            }
            guards.push(site.constructor_result);
        }
        Arc::from(guards.into_boxed_slice())
    };
    Ok(CompiledProgram {
        core: CompiledCore::Effect(validated, quote_guards),
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
    E: FnOnce(&CompiledCore) -> Result<Evaluation, RuntimeFailure>,
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
    execute_owned_with_consumer(compiled, evaluator)
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
    if let CompiledCore::Effect(program, _) = core {
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
/// Refuses changed supplied bindings before Ash execution. A missing selected
/// binding fails at invocation. Runtime failures never retry a returned external call.
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
    let CompiledCore::Effect(_, quote_guards) = &program.core else {
        return Err(preparation_failure(RuntimeFailure::InvalidControlState));
    };
    let evaluation =
        crate::eval::evaluate_effect_with_source_native_quote_guards(admitted, quote_guards)
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
    use crate::core::{validate_effect_modules, validate_modules};
    use crate::elaborate::check_module_in_effect_profile_with_rewrite_work;
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

    #[test]
    fn parsed_input_has_no_syntax_ledger_loan() {
        let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("tests/fixtures/surface-macros/type-host/control.ash");
        let mut graph = load_module_graph(&path, &ModuleRoots::empty()).unwrap();
        let first_id = graph.modules()[0].id();
        let mut input = CompilationInput::Parsed {
            graph: &mut graph,
            next: 0,
        };
        assert!(input.current_with_syntax_budget().is_none());
        let mut input = CompilationInput::Parsed {
            graph: &mut graph,
            next: 1,
        };
        let (module, budget, ordinal) = input.current_with_syntax_budget().unwrap();
        assert!(ordinal.is_none());
        assert_eq!(module.id(), first_id);
        assert!(budget.is_none());
    }

    fn i21_graph(name: &str) -> HeaderGraph {
        let entry = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("docs/design/macros/fixtures/header_compat")
            .join(name);
        discover_headers(&entry, &ModuleRoots::empty()).unwrap()
    }

    fn projected_syntax_dependencies(
        graph: &mut HeaderGraph,
    ) -> Vec<(ModuleId, Vec<crate::surface::SurfaceSyntaxDeclaration>)> {
        let mut dependencies = Vec::new();
        while dependencies.len() + 1 < graph.len() {
            let module = graph.next_module().unwrap().expect("fixture dependency");
            dependencies.push((module.id(), module.surface().syntax_declarations.clone()));
        }
        dependencies
    }

    fn select_projected_syntax(
        graph: &HeaderGraph,
        dependencies: &[(ModuleId, Vec<crate::surface::SurfaceSyntaxDeclaration>)],
    ) -> Result<Vec<crate::syntax::SelectedSyntax>, FileFailure> {
        let (imports, edges) = graph.next_imports().expect("fixture importer");
        select_imported_syntax(imports, edges, |target| {
            let owner = dependencies
                .iter()
                .position(|(module, _)| *module == target)
                .ok_or_else(internal_file_failure)?;
            Ok((owner, dependencies[owner].1.as_slice()))
        })
    }

    fn parse_selected_fixture(
        path: &std::path::Path,
    ) -> (
        SourceFile,
        crate::parser::ConcreteTree,
        Vec<crate::syntax::SelectedSyntax>,
    ) {
        let mut graph = discover_headers(path, &ModuleRoots::empty()).unwrap();
        let dependencies = projected_syntax_dependencies(&mut graph);
        let selected = select_projected_syntax(&graph, &dependencies).unwrap();
        let source = SourceFile::new(
            path.to_string_lossy(),
            std::fs::read_to_string(path).unwrap(),
        )
        .unwrap();
        let lexed = crate::lexer::lex(&source).unwrap();
        let (tokens, diagnostics, budget, resource) = lexed.into_parts();
        assert!(resource.is_none());
        let (checkpoint, budget) = crate::parser::parse_module_header(tokens, diagnostics, budget);
        let (tree, _) = crate::parser::finish_module_from_checkpoint_with_syntax(
            checkpoint,
            budget,
            Some(&source),
            &selected,
        );
        (source, tree, selected)
    }

    #[test]
    fn d2_selects_renamed_declaration_export_and_retains_its_context() {
        use crate::surface::SurfaceSyntaxCategory;

        let mut graph = i21_graph("renamed.ash");
        let dependencies = projected_syntax_dependencies(&mut graph);
        let (imports, _) = graph.next_imports().unwrap();
        let selected = select_projected_syntax(&graph, &dependencies).unwrap();
        let [declaration] = selected.as_slice() else {
            panic!("one syntax import was selected");
        };
        assert_eq!(declaration.name, "make_number");
        assert_eq!(declaration.declaration.name.text, "make_value");
        assert_eq!(
            declaration.declaration.category,
            SurfaceSyntaxCategory::Declaration
        );
        assert_eq!(
            declaration.declaration,
            dependencies[declaration.owner].1[0]
        );
        assert_eq!(declaration.import_span, imports[0].span);

        let SurfaceImportSelection::Targeted(items) = &imports[0].selection else {
            panic!("the fixture has a targeted import");
        };
        let [
            SurfaceImportItem::Syntax {
                alias: Some(alias), ..
            },
        ] = items.as_slice()
        else {
            panic!("the fixture selects a renamed syntax");
        };
        let owner_imports = vec![selected.clone()];
        let caller_contexts = crate::syntax::SyntaxContexts::new(&selected, &[], &[]);
        assert_eq!(
            caller_contexts.select(alias).unwrap().declaration,
            declaration.declaration
        );
        let owner_contexts = crate::syntax::SyntaxContexts::new(&[], &owner_imports, &[Some(0)]);
        assert!(owner_contexts.select(alias).is_none());
        let mut introduced = alias.clone();
        introduced.introduction = 1;
        assert_eq!(
            owner_contexts.select(&introduced).unwrap().owner,
            declaration.owner
        );
        introduced.introduction = 2;
        assert!(owner_contexts.select(&introduced).is_none());

        let source = SourceFile::new("generated.ash", "make_number").unwrap();
        let span = source.span(ByteRange::new(0, 11).unwrap()).unwrap();
        for introduction in [0, 1] {
            let mut name = alias.clone();
            name.span = span;
            name.introduction = introduction;
            let expression = crate::parser::parse_macro_expression(
                &source,
                span,
                None,
                vec![crate::syntax::MacroOutputNode::Identifier(
                    name,
                    crate::syntax::MacroOrigin::Source(span),
                )],
                if introduction == 0 {
                    &caller_contexts
                } else {
                    &owner_contexts
                },
                None,
            )
            .expect("declaration syntax is not an expression invocation");
            assert!(matches!(
                expression.kind,
                crate::surface::SurfaceExprKind::Name(reference)
                    if reference.member().text == "make_number"
            ));
        }
    }

    #[test]
    fn d2_selects_both_i21_categories_without_changing_their_exports() {
        use crate::surface::SurfaceSyntaxCategory;

        let mut graph = i21_graph("both.ash");
        let dependencies = projected_syntax_dependencies(&mut graph);
        let (imports, _) = graph.next_imports().unwrap();
        let selected = select_projected_syntax(&graph, &dependencies).unwrap();
        let [expression, declaration] = selected.as_slice() else {
            panic!("the two syntax imports were selected");
        };
        assert_eq!(expression.name, "declaration");
        assert_eq!(
            expression.declaration.category,
            SurfaceSyntaxCategory::Expression
        );
        assert_eq!(declaration.name, "make_value");
        assert_eq!(
            declaration.declaration.category,
            SurfaceSyntaxCategory::Declaration
        );
        for (selection, import) in selected.iter().zip(imports) {
            assert_eq!(selection.declaration, dependencies[selection.owner].1[0]);
            assert_eq!(selection.import_span, import.span);
        }
    }

    #[test]
    fn d2_rejects_the_i21_collision_at_the_second_selected_name() {
        let mut graph = i21_graph("collision.ash");
        let dependencies = projected_syntax_dependencies(&mut graph);
        let (imports, _) = graph.next_imports().unwrap();
        let SurfaceImportSelection::Targeted(items) = &imports[1].selection else {
            panic!("the fixture has a targeted import");
        };
        let [SurfaceImportItem::Syntax { name, .. }] = items.as_slice() else {
            panic!("the fixture selects expression syntax");
        };
        let failure = select_projected_syntax(&graph, &dependencies).unwrap_err();
        let Some(PipelineFailure::Resolution(error)) = failure.pipeline_failure() else {
            panic!("expected an import conflict: {failure:?}");
        };
        assert_eq!(error.reason, crate::resolve::ResolveReason::ImportConflict);
        assert_eq!(error.primary.span(), name.span);
        assert_eq!(name.text, "declaration");
    }

    #[test]
    fn d2_reports_a_missing_export_from_a_declaration_syntax_module() {
        let entry =
            TestSource::write("import forms (syntax absent)\nmain : Unit -> Int\nmain () = 42\n");
        entry.write_sibling(
            "forms.ash",
            include_str!("../docs/design/macros/fixtures/header_compat/forms.ash"),
        );
        let mut graph = discover_headers(&entry.0, &ModuleRoots::empty()).unwrap();
        let dependencies = projected_syntax_dependencies(&mut graph);
        let failure = select_projected_syntax(&graph, &dependencies).unwrap_err();
        let Some(PipelineFailure::Resolution(error)) = failure.pipeline_failure() else {
            panic!("expected an unavailable export: {failure:?}");
        };
        assert_eq!(
            error.reason,
            crate::resolve::ResolveReason::UnavailableExport
        );
        assert_eq!(error.found.as_deref(), Some("absent"));
    }

    #[test]
    fn d2_does_not_select_same_module_definitions_without_an_import() {
        let mut graph = i21_graph("own_definition.ash");
        let _dependencies = projected_syntax_dependencies(&mut graph);
        let (imports, edges) = graph.next_imports().unwrap();
        assert!(imports.is_empty());
        let selected = select_imported_syntax(imports, edges, |_| {
            panic!("an unimported local definition must not be looked up")
        })
        .unwrap();
        assert!(selected.is_empty());
    }

    #[test]
    fn d3_parses_a_renamed_imported_declaration_invocation_in_module_order() {
        let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("docs/design/macros/fixtures/header_compat/renamed.ash");
        let (source, tree, selected) = parse_selected_fixture(&path);
        assert!(
            tree.parse_diagnostics().is_empty(),
            "{:?}",
            tree.parse_diagnostics()
        );
        let kinds = tree
            .root()
            .unwrap()
            .children
            .iter()
            .filter_map(|child| match child {
                crate::parser::ConcreteElement::Node(node) => Some(format!("{:?}", node.kind)),
                _ => None,
            })
            .collect::<Vec<_>>();
        assert_eq!(
            kinds,
            [
                "ImportDeclaration",
                "DeclarationSyntaxInvocation",
                "EquationalGlobal"
            ]
        );
        let node = tree
            .root()
            .unwrap()
            .children
            .iter()
            .find_map(|child| match child {
                crate::parser::ConcreteElement::Node(node)
                    if node.kind == crate::parser::NodeKind::DeclarationSyntaxInvocation =>
                {
                    Some(node)
                }
                _ => None,
            })
            .unwrap();
        let contexts = crate::syntax::SyntaxContexts::new(&selected, &[], &[]);
        let invocation =
            crate::parser::project_declaration_invocation(&source, &tree, node, &contexts).unwrap();
        assert_eq!(invocation.name.text, "make_number");
        assert_eq!(invocation.selection.name, "make_number");
        assert_eq!(invocation.selection.declaration.name.text, "make_value");
        assert_eq!(invocation.selection.owner, selected[0].owner);
        assert_eq!(invocation.selection.import_span, selected[0].import_span);
        let [crate::surface::SurfaceSyntaxCapture::Identifier(capture)] =
            invocation.captures.as_slice()
        else {
            panic!("the selected matcher captures one identifier");
        };
        assert_eq!(capture.name.text, "number");
        assert_eq!(capture.name.introduction, 0);
        assert_eq!(capture.origin.primary(), capture.name.span);
        assert_eq!(capture.name.span.source(), source.id());
        let range = invocation.span.range();
        assert_eq!(
            &source.text()[range.start() as usize..range.end() as usize],
            "make_number number"
        );
        assert!(crate::parser::project_module_retaining_templates(&source, &tree).is_err());
        assert!(
            crate::parser::project_declaration_invocation(&source, &tree, &node.clone(), &contexts)
                .is_err()
        );
    }

    #[test]
    fn d3_missing_identifier_fails_at_the_invocation_boundary() {
        let entry = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("docs/design/macros/fixtures/diagnostics/missing.ash");
        let failure = compile_path(RunConfiguration {
            entry,
            roots: ModuleRoots::empty(),
        })
        .unwrap_err();
        let Some(LoadGraphError::Syntax(error)) = failure.graph_failure() else {
            panic!("expected a matcher syntax failure: {failure:?}");
        };
        assert!(error.source.display_path().ends_with("missing.ash"));
        let diagnostic = &error.parser[0];
        assert_eq!(diagnostic.reason, crate::parser::ParseReason::ExpectedForm);
        assert_eq!(
            diagnostic.expected_form(),
            Some(crate::parser::ExpectedForm::Identifier)
        );
        assert_eq!(
            diagnostic.found_token(),
            Some(crate::parser::FoundToken::LineEnd)
        );
        let start = error.source.text().find("need_name\n").unwrap() + "need_name".len();
        assert_eq!(diagnostic.primary.span().range().start() as usize, start);
        let location = diagnostic
            .primary
            .diagnostic_location()
            .expect("the matcher diagnostic retains its selected definition frame");
        let [frame] = location.frames.as_slice() else {
            panic!("expected one declaration invocation frame");
        };
        assert_eq!(frame.invocation.source(), error.source.id());
        assert_eq!(
            frame.invocation.range().start() as usize,
            start - "need_name".len()
        );
        assert_eq!(frame.invocation.range().end() as usize, start);
        let FileFailure::Graph(context) = &failure else {
            panic!("the matcher failure retains the graph sources");
        };
        let definition = context
            .sources()
            .find(|source| source.id() == frame.definition.source())
            .expect("the selected definition source is retained");
        assert!(definition.display_path().ends_with("typed_forms.ash"));
        let range = frame.definition.range();
        assert!(
            definition.text()[range.start() as usize..range.end() as usize]
                .starts_with("pub syntax declaration: (need_name)")
        );
    }

    #[test]
    fn d3_projects_the_i01_identifier_captures_from_selected_syntax() {
        let forms = include_str!("../docs/design/macros/fixtures/declarations/forms.ash");
        let start = forms.find("pub syntax declaration: (make_type)").unwrap();
        let end = start + forms[start..].find("\n}\n").unwrap() + "\n}\n".len();
        let fixture = TestSource::write(include_str!(
            "../docs/design/macros/fixtures/declarations/case_01.ash"
        ));
        fixture.write_sibling("forms.ash", &forms[start..end]);
        let (source, tree, selected) = parse_selected_fixture(&fixture.0);
        assert!(
            tree.parse_diagnostics().is_empty(),
            "{:?}",
            tree.parse_diagnostics()
        );
        let node = tree
            .root()
            .unwrap()
            .children
            .iter()
            .find_map(|child| match child {
                crate::parser::ConcreteElement::Node(node)
                    if node.kind == crate::parser::NodeKind::DeclarationSyntaxInvocation =>
                {
                    Some(node)
                }
                _ => None,
            })
            .unwrap();
        let contexts = crate::syntax::SyntaxContexts::new(&selected, &[], &[]);
        let matched =
            crate::parser::project_declaration_invocation(&source, &tree, node, &contexts).unwrap();
        let [
            crate::surface::SurfaceSyntaxCapture::Identifier(first),
            crate::surface::SurfaceSyntaxCapture::Identifier(second),
        ] = matched.captures.as_slice()
        else {
            panic!("the selected I01 matcher captures two identifiers");
        };
        assert_eq!(
            (&first.name.text[..], &second.name.text[..]),
            ("Color", "Red")
        );
        for capture in [first, second] {
            assert_eq!(capture.name.introduction, 0);
            assert_eq!(capture.origin.primary(), capture.name.span);
            assert_eq!(capture.name.span.source(), source.id());
        }
        assert_eq!(matched.selection.declaration.name.text, "make_type");
        assert_eq!(matched.selection.owner, selected[0].owner);
        assert_eq!(matched.selection.import_span, selected[0].import_span);
        assert!(crate::parser::project_module_retaining_templates(&source, &tree).is_err());
        let program = compile_path(fixture.configuration()).unwrap();
        assert_eq!(execute(&program).unwrap().value_display(), "42");
    }

    #[test]
    fn d3_projects_the_i19_expression_capture_in_source_order() {
        let forms = include_str!("../docs/design/macros/fixtures/captures/forms.ash");
        let end = forms.find("\n}\n").unwrap() + "\n}\n".len();
        let fixed = include_str!("../docs/design/macros/fixtures/captures/main.ash")
            .lines()
            .find(|line| line.starts_with("expression_value "))
            .unwrap();
        let fixture = TestSource::write(&format!(
            "import forms (syntax expression_value)\n\nbefore : Unit -> Int\nbefore () = 1\n{fixed}\nafter : Unit -> Int\nafter () = 2\nmain : Unit -> Int\nmain () = 42\n"
        ));
        fixture.write_sibling("forms.ash", &forms[..end]);
        let (source, tree, selected) = parse_selected_fixture(&fixture.0);
        assert!(
            tree.parse_diagnostics().is_empty(),
            "{:?}",
            tree.parse_diagnostics()
        );
        let nodes = tree
            .root()
            .unwrap()
            .children
            .iter()
            .filter_map(|child| match child {
                crate::parser::ConcreteElement::Node(node) => Some(node),
                _ => None,
            })
            .collect::<Vec<_>>();
        assert_eq!(
            nodes.iter().map(|node| node.kind).collect::<Vec<_>>(),
            [
                crate::parser::NodeKind::ImportDeclaration,
                crate::parser::NodeKind::EquationalGlobal,
                crate::parser::NodeKind::DeclarationSyntaxInvocation,
                crate::parser::NodeKind::EquationalGlobal,
                crate::parser::NodeKind::EquationalGlobal,
            ]
        );
        let contexts = crate::syntax::SyntaxContexts::new(&selected, &[], &[]);
        let matched =
            crate::parser::project_declaration_invocation(&source, &tree, nodes[2], &contexts)
                .unwrap();
        let [
            crate::surface::SurfaceSyntaxCapture::Identifier(name),
            crate::surface::SurfaceSyntaxCapture::Expression(value),
        ] = matched.captures.as_slice()
        else {
            panic!("the selected I19 matcher captures an identifier and expression");
        };
        assert_eq!(name.name.text, "forty_two");
        assert_eq!(name.origin.primary(), name.name.span);
        assert!(matches!(
            value.expression.kind,
            crate::surface::SurfaceExprKind::Add(_)
        ));
        let range = value.expression.span.range();
        assert_eq!(
            &source.text()[range.start() as usize..range.end() as usize],
            "40 + 2"
        );
        assert_eq!(value.contents.len(), 3);
        assert!(
            matches!(&value.contents[1], crate::syntax::MacroOutputNode::Token(crate::lexer::TokenKind::Plus, _, origin)
            if origin.primary().source() == source.id())
        );
        assert_eq!(matched.selection.owner, selected[0].owner);
        assert_eq!(matched.selection.import_span, selected[0].import_span);
        assert!(crate::parser::project_module_retaining_templates(&source, &tree).is_err());
    }

    fn d4_invocation_node(tree: &crate::parser::ConcreteTree) -> &crate::parser::ConcreteNode {
        tree.root()
            .unwrap()
            .children
            .iter()
            .find_map(|child| match child {
                crate::parser::ConcreteElement::Node(node)
                    if node.kind == crate::parser::NodeKind::DeclarationSyntaxInvocation =>
                {
                    Some(node)
                }
                _ => None,
            })
            .unwrap()
    }

    #[test]
    fn d4_i07_captures_type_and_rejects_missing_type() {
        let forms = include_str!("../docs/design/macros/fixtures/declarations/forms.ash");
        let start = forms
            .find("pub syntax declaration: (make_identity)")
            .unwrap();
        let forms = &forms[start..];
        let fixed = include_str!("../docs/design/macros/fixtures/declarations/case_07.ash");
        for missing in [false, true] {
            let text = if missing {
                fixed.replace("make_identity id for Int", "make_identity id for")
            } else {
                fixed.to_owned()
            };
            let fixture = TestSource::write(&text);
            fixture.write_sibling("forms.ash", forms);
            let (source, tree, selected) = parse_selected_fixture(&fixture.0);
            if missing {
                let diagnostic = &tree.parse_diagnostics()[0];
                assert_eq!(
                    diagnostic.expected_form(),
                    Some(crate::parser::ExpectedForm::Type)
                );
                let start =
                    text.find("make_identity id for\n").unwrap() + "make_identity id for".len();
                assert_eq!(diagnostic.primary.span().range().start() as usize, start);
                let frames = &diagnostic.primary.diagnostic_location().unwrap().frames;
                assert_eq!(frames.len(), 1);
                assert_eq!(frames[0].definition, selected[0].declaration.span);
                continue;
            }
            assert!(
                tree.parse_diagnostics().is_empty(),
                "{:?}",
                tree.parse_diagnostics()
            );
            let contexts = crate::syntax::SyntaxContexts::new(&selected, &[], &[]);
            let matched = crate::parser::project_declaration_invocation(
                &source,
                &tree,
                d4_invocation_node(&tree),
                &contexts,
            )
            .unwrap();
            let [
                crate::surface::SurfaceSyntaxCapture::Identifier(name),
                crate::surface::SurfaceSyntaxCapture::Type(ty),
            ] = matched.captures.as_slice()
            else {
                panic!("I07 captures an identifier and a type");
            };
            assert_eq!(name.name.text, "id");
            assert!(matches!(ty.ty.kind, crate::surface::SurfaceTypeKind::Int));
            let range = ty.ty.span.range();
            assert_eq!(
                &source.text()[range.start() as usize..range.end() as usize],
                "Int"
            );
            assert!(
                matches!(&ty.contents[..], [crate::syntax::MacroOutputNode::Token(crate::lexer::TokenKind::IntType, _, origin)]
                if origin.primary() == ty.ty.span)
            );
            assert_eq!(matched.selection.owner, selected[0].owner);
            assert_eq!(matched.selection.import_span, selected[0].import_span);
            assert!(crate::parser::project_module_retaining_templates(&source, &tree).is_err());
        }
    }

    #[test]
    fn d4_i19_preserves_pattern_binder_and_body_captures() {
        let fixture = TestSource::write(include_str!(
            "../docs/design/macros/fixtures/captures/binder.ash"
        ));
        fixture.write_sibling(
            "binder_forms.ash",
            include_str!("../docs/design/macros/fixtures/captures/binder_forms.ash"),
        );
        let (source, tree, selected) = parse_selected_fixture(&fixture.0);
        assert!(
            tree.parse_diagnostics().is_empty(),
            "{:?}",
            tree.parse_diagnostics()
        );
        let contexts = crate::syntax::SyntaxContexts::new(&selected, &[], &[]);
        let matched = crate::parser::project_declaration_invocation(
            &source,
            &tree,
            d4_invocation_node(&tree),
            &contexts,
        )
        .unwrap();
        let [
            crate::surface::SurfaceSyntaxCapture::Identifier(name),
            crate::surface::SurfaceSyntaxCapture::Pattern(pattern),
            crate::surface::SurfaceSyntaxCapture::Expression(body),
        ] = matched.captures.as_slice()
        else {
            panic!("I19 captures a name, pattern and expression");
        };
        assert_eq!(name.name.text, "identity");
        let crate::surface::SurfacePatternKind::Binder(binder) = &pattern.pattern.kind else {
            panic!("the fixed pattern is a binder");
        };
        assert_eq!(binder.name.text, "value");
        assert_eq!(binder.name.introduction, 0);
        assert!(
            matches!(&pattern.contents[..], [crate::syntax::MacroOutputNode::Identifier(name, origin)]
            if name.text == "value" && origin.primary() == binder.name.span)
        );
        let range = body.expression.span.range();
        assert_eq!(
            &source.text()[range.start() as usize..range.end() as usize],
            "value"
        );
        assert!(
            matches!(&body.contents[..], [crate::syntax::MacroOutputNode::Identifier(name, _)]
            if name.text == "value" && name.introduction == binder.name.introduction)
        );
        assert_eq!(matched.selection.owner, selected[0].owner);
        assert_eq!(matched.selection.import_span, selected[0].import_span);

        // Follow the loader-selected import through the actual declaration
        // collector and inspect the generated consumer's original context.
        let owner_imports = vec![Vec::new(); selected[0].owner + 1];
        let mut owners = Vec::new();
        let surface = crate::parser::project_declaration_expansions(
            &source,
            &tree,
            &selected,
            &owner_imports,
            &mut owners,
            &mut crate::syntax_resource::SyntaxBudget::default(),
            None,
        )
        .unwrap();
        assert_eq!(owners.len(), 1);
        assert_eq!(owners[0].owner, Some(selected[0].owner));
        assert_eq!(owners[0].declaration, selected[0].declaration.span);
        assert_eq!(owners[0].import_span, selected[0].import_span);
        let generated = surface
            .definitions
            .iter()
            .find_map(|definition| {
                let crate::surface::SurfaceDefinitionKind::Equational(global) = &definition.kind
                else {
                    return None;
                };
                (global.interface.name.text == "identity").then_some(global)
            })
            .unwrap();
        let crate::surface::SurfacePatternKind::Binder(generated_binder) =
            &generated.equations[0].patterns[0].kind
        else {
            panic!("the generated equation keeps the caller binder");
        };
        assert_eq!(generated_binder.name.span, binder.name.span);
        assert_eq!(generated_binder.name.span.source(), source.id());
        assert_eq!(generated_binder.name.introduction, 0);
        let binder_location = generated_binder.name.diagnostic.as_ref().unwrap();
        assert_eq!(binder_location.primary.primary(), binder.name.span);
        assert!(binder_location.frames.iter().any(|frame| {
            frame.invocation == matched.span && frame.definition == selected[0].declaration.span
        }));
        let generated_body = &generated.equations[0].body;
        let crate::surface::SurfaceExprKind::Name(crate::surface::SurfaceReference::Unqualified(
            generated_name,
        )) = &generated_body.kind
        else {
            panic!("the generated body keeps the caller name");
        };
        assert_eq!(generated_name.span, body.expression.span);
        assert_eq!(generated_name.span.source(), source.id());
        assert_eq!(generated_name.introduction, 0);
        let body_location = generated_body.diagnostic.as_ref().unwrap();
        assert_eq!(body_location.primary.primary(), body.expression.span);
        assert!(body_location.frames.iter().any(|frame| {
            frame.invocation == matched.span && frame.definition == selected[0].declaration.span
        }));
    }

    #[test]
    fn d4_i19_predicate_captures_the_fixed_boolean_pattern() {
        let forms = include_str!("../docs/design/macros/fixtures/captures/forms.ash");
        let start = forms.find("pub syntax declaration: (predicate)").unwrap();
        let end = start + forms[start..].find("\n}\n").unwrap() + "\n}\n".len();
        let line = include_str!("../docs/design/macros/fixtures/captures/main.ash")
            .lines()
            .find(|line| line.starts_with("predicate "))
            .unwrap();
        let fixture = TestSource::write(&format!("import forms (syntax predicate)\n\n{line}\n"));
        fixture.write_sibling("forms.ash", &forms[start..end]);
        let (source, tree, selected) = parse_selected_fixture(&fixture.0);
        assert!(
            tree.parse_diagnostics().is_empty(),
            "{:?}",
            tree.parse_diagnostics()
        );
        let contexts = crate::syntax::SyntaxContexts::new(&selected, &[], &[]);
        let matched = crate::parser::project_declaration_invocation(
            &source,
            &tree,
            d4_invocation_node(&tree),
            &contexts,
        )
        .unwrap();
        let [
            crate::surface::SurfaceSyntaxCapture::Identifier(name),
            crate::surface::SurfaceSyntaxCapture::Pattern(pattern),
        ] = matched.captures.as_slice()
        else {
            panic!("the I19 predicate captures a name and pattern");
        };
        assert_eq!(name.name.text, "selected");
        assert!(matches!(
            pattern.pattern.kind,
            crate::surface::SurfacePatternKind::Boolean(true)
        ));
        assert!(
            matches!(&pattern.contents[..], [crate::syntax::MacroOutputNode::Token(crate::lexer::TokenKind::True, _, origin)] if origin.primary() == pattern.pattern.span)
        );
    }

    #[test]
    fn d4_type_captures_use_ordinary_boundaries_and_hide_nested_stops() {
        use crate::parser::ExpectedForm;
        for (matcher, line, expected_text, error) in [
            (
                "$T:type , $name:ident",
                "take Pair<Foo, Bar> , item",
                Some("Pair<Foo, Bar>"),
                None,
            ),
            (
                "$T:type , $name:ident",
                "take (Foo, Bar) , item",
                Some("(Foo, Bar)"),
                None,
            ),
            (
                "$T:type , $name:ident",
                "take Mod.Foo -> Pair<Bar, Baz> , item",
                Some("Mod.Foo -> Pair<Bar, Baz>"),
                None,
            ),
            (
                "$T:type -> $name:ident",
                "take (Int -> Bool) -> item",
                Some("(Int -> Bool)"),
                None,
            ),
            (
                "$T:type . $name:ident",
                "take Foo -> Bar . item",
                Some("Foo -> Bar"),
                None,
            ),
            (
                "$T:type < $name:ident",
                "take Foo < item",
                Some("Foo"),
                None,
            ),
            (
                "$T:type , $name:ident",
                "take , item",
                None,
                Some(ExpectedForm::Type),
            ),
            (
                "$T:type , $name:ident",
                "take 42 , item",
                None,
                Some(ExpectedForm::Type),
            ),
            (
                "$T:type , $name:ident",
                "take Pair<Foo,> , item",
                None,
                Some(ExpectedForm::Type),
            ),
            (
                "$T:type End $name:ident",
                "take Foo -> End item",
                None,
                Some(ExpectedForm::Type),
            ),
        ] {
            let fixture = TestSource::write(&format!("import forms (syntax take)\n\n{line}\n"));
            fixture.write_sibling(
                "forms.ash",
                &format!("pub syntax declaration: (take) {matcher} => {{}}\n"),
            );
            let (source, tree, selected) = parse_selected_fixture(&fixture.0);
            if let Some(error) = error {
                assert_eq!(
                    tree.parse_diagnostics()[0].expected_form(),
                    Some(error),
                    "{line}"
                );
                continue;
            }
            assert!(
                tree.parse_diagnostics().is_empty(),
                "{line}: {:?}",
                tree.parse_diagnostics()
            );
            let contexts = crate::syntax::SyntaxContexts::new(&selected, &[], &[]);
            let matched = crate::parser::project_declaration_invocation(
                &source,
                &tree,
                d4_invocation_node(&tree),
                &contexts,
            )
            .unwrap();
            let [
                crate::surface::SurfaceSyntaxCapture::Type(ty),
                crate::surface::SurfaceSyntaxCapture::Identifier(name),
            ] = matched.captures.as_slice()
            else {
                panic!("expected type and identifier captures for {line}");
            };
            let range = ty.ty.span.range();
            assert_eq!(
                &source.text()[range.start() as usize..range.end() as usize],
                expected_text.unwrap()
            );
            assert_eq!(name.name.text, "item");
            assert!(!ty.contents.is_empty());
            if expected_text == Some("Pair<Foo, Bar>") {
                assert!(
                    matches!(&ty.ty.kind, crate::surface::SurfaceTypeKind::Application { arguments, .. } if arguments.len() == 2)
                );
            }
            if expected_text == Some("Mod.Foo -> Pair<Bar, Baz>") {
                assert!(
                    matches!(&ty.ty.kind, crate::surface::SurfaceTypeKind::Function(function)
                    if matches!(&function.domain.kind, crate::surface::SurfaceTypeKind::Named(crate::surface::SurfaceReference::Qualified(_)))
                        && matches!(&function.codomain.kind, crate::surface::SurfaceTypeKind::Application { arguments, .. } if arguments.len() == 2))
                );
            }
        }
    }

    #[test]
    fn d4_patterns_stop_before_literals_and_reject_wrong_categories() {
        use crate::parser::ExpectedForm;
        for (line, expected_text, error) in [
            (
                "take (Some(value), flag) yields value",
                Some("(Some(value), flag)"),
                None,
            ),
            (
                "take (yields, flag) yields value",
                Some("(yields, flag)"),
                None,
            ),
            (
                "take Mod.Some(value) yields value",
                Some("Mod.Some(value)"),
                None,
            ),
            ("take yields value", None, Some(ExpectedForm::Pattern)),
            ("take 42 yields value", None, Some(ExpectedForm::Pattern)),
            (
                "take (Some(value) yields value",
                None,
                Some(ExpectedForm::RightParen),
            ),
        ] {
            let fixture = TestSource::write(&format!("import forms (syntax take)\n\n{line}\n"));
            fixture.write_sibling(
                "forms.ash",
                "pub syntax declaration: (take) $p:pattern yields $body:expr => {}\n",
            );
            let (source, tree, selected) = parse_selected_fixture(&fixture.0);
            if let Some(error) = error {
                assert_eq!(
                    tree.parse_diagnostics()[0].expected_form(),
                    Some(error),
                    "{line}"
                );
                continue;
            }
            assert!(
                tree.parse_diagnostics().is_empty(),
                "{line}: {:?}",
                tree.parse_diagnostics()
            );
            let contexts = crate::syntax::SyntaxContexts::new(&selected, &[], &[]);
            let matched = crate::parser::project_declaration_invocation(
                &source,
                &tree,
                d4_invocation_node(&tree),
                &contexts,
            )
            .unwrap();
            let [
                crate::surface::SurfaceSyntaxCapture::Pattern(pattern),
                crate::surface::SurfaceSyntaxCapture::Expression(_),
            ] = matched.captures.as_slice()
            else {
                panic!("expected pattern and expression captures for {line}");
            };
            let range = pattern.pattern.span.range();
            assert_eq!(
                &source.text()[range.start() as usize..range.end() as usize],
                expected_text.unwrap()
            );
            assert!(!pattern.contents.is_empty());
            if expected_text == Some("(Some(value), flag)") {
                assert!(
                    matches!(&pattern.pattern.kind, crate::surface::SurfacePatternKind::Tuple(items) if items.len() == 2)
                );
            }
            if expected_text == Some("Mod.Some(value)") {
                assert!(matches!(
                    &pattern.pattern.kind,
                    crate::surface::SurfacePatternKind::Constructor {
                        name: crate::surface::SurfaceReference::Qualified(_),
                        payload: Some(_),
                        ..
                    }
                ));
            }
        }
        for line in ["take Some . item", "take binder . item"] {
            let fixture = TestSource::write(&format!("import forms (syntax take)\n\n{line}\n"));
            fixture.write_sibling(
                "forms.ash",
                "pub syntax declaration: (take) $p:pattern . $name:ident => {}\n",
            );
            let (source, tree, selected) = parse_selected_fixture(&fixture.0);
            assert!(
                tree.parse_diagnostics().is_empty(),
                "{line}: {:?}",
                tree.parse_diagnostics()
            );
            let contexts = crate::syntax::SyntaxContexts::new(&selected, &[], &[]);
            let matched = crate::parser::project_declaration_invocation(
                &source,
                &tree,
                d4_invocation_node(&tree),
                &contexts,
            )
            .unwrap();
            let [
                crate::surface::SurfaceSyntaxCapture::Pattern(_),
                crate::surface::SurfaceSyntaxCapture::Identifier(name),
            ] = matched.captures.as_slice()
            else {
                panic!("expected pattern and identifier captures for {line}");
            };
            assert_eq!(name.name.text, "item");
        }
    }

    #[test]
    fn d3_expression_captures_stop_at_their_literal_and_reject_incomplete_input() {
        let forms = "pub syntax declaration: (pair) $value:expr then $name:ident => {}\n";
        for (line, expected) in [
            ("pair (f(then) + 2) then answer", None),
            (
                "pair then answer",
                Some(crate::parser::ExpectedForm::Expression),
            ),
            (
                "pair 1 then answer extra",
                Some(crate::parser::ExpectedForm::LineEnd),
            ),
        ] {
            let fixture = TestSource::write(&format!(
                "import forms (syntax pair)\n\n{line}\nmain : Unit -> Int\nmain () = 42\n"
            ));
            fixture.write_sibling("forms.ash", forms);
            let (source, tree, selected) = parse_selected_fixture(&fixture.0);
            if let Some(expected) = expected {
                assert_eq!(
                    tree.parse_diagnostics()[0].expected_form(),
                    Some(expected),
                    "{line}"
                );
                let frames = &tree.parse_diagnostics()[0]
                    .primary
                    .diagnostic_location()
                    .expect("matcher failure retains its invocation frame")
                    .frames;
                assert_eq!(frames.len(), 1);
                assert_eq!(frames[0].definition, selected[0].declaration.span);
                assert_eq!(frames[0].invocation.source(), source.id());
                continue;
            }
            assert!(
                tree.parse_diagnostics().is_empty(),
                "{line}: {:?}",
                tree.parse_diagnostics()
            );
            let node = tree
                .root()
                .unwrap()
                .children
                .iter()
                .find_map(|child| match child {
                    crate::parser::ConcreteElement::Node(node)
                        if node.kind == crate::parser::NodeKind::DeclarationSyntaxInvocation =>
                    {
                        Some(node)
                    }
                    _ => None,
                })
                .unwrap();
            let contexts = crate::syntax::SyntaxContexts::new(&selected, &[], &[]);
            let matched =
                crate::parser::project_declaration_invocation(&source, &tree, node, &contexts)
                    .unwrap();
            let [
                crate::surface::SurfaceSyntaxCapture::Expression(value),
                crate::surface::SurfaceSyntaxCapture::Identifier(name),
            ] = matched.captures.as_slice()
            else {
                panic!("the matcher retains its ordered expression and identifier captures");
            };
            let range = value.expression.span.range();
            assert_eq!(
                &source.text()[range.start() as usize..range.end() as usize],
                "(f(then) + 2)"
            );
            assert_eq!(name.name.text, "answer");
        }
    }

    #[test]
    fn d3_empty_matcher_requires_a_complete_invocation_line() {
        for (line, valid) in [("tag", true), ("tag extra", false), ("tag : Unit", false)] {
            let fixture = TestSource::write(&format!(
                "import forms (syntax tag)\n\n{line}\nmain : Unit -> Int\nmain () = 42\n"
            ));
            fixture.write_sibling("forms.ash", "pub syntax declaration: (tag) => {}\n");
            let (source, tree, selected) = parse_selected_fixture(&fixture.0);
            if !valid {
                assert_eq!(
                    tree.parse_diagnostics()[0].expected_form(),
                    Some(crate::parser::ExpectedForm::LineEnd),
                    "{line}"
                );
                continue;
            }
            assert!(tree.parse_diagnostics().is_empty());
            let node = tree
                .root()
                .unwrap()
                .children
                .iter()
                .find_map(|child| match child {
                    crate::parser::ConcreteElement::Node(node)
                        if node.kind == crate::parser::NodeKind::DeclarationSyntaxInvocation =>
                    {
                        Some(node)
                    }
                    _ => None,
                })
                .unwrap();
            let contexts = crate::syntax::SyntaxContexts::new(&selected, &[], &[]);
            let matched =
                crate::parser::project_declaration_invocation(&source, &tree, node, &contexts)
                    .unwrap();
            assert!(matched.captures.is_empty());
            assert_eq!(matched.selection.owner, selected[0].owner);
        }
    }

    #[test]
    fn d2_i21_checked_exports_reach_selection_before_declaration_invocation() {
        for name in ["renamed.ash", "both.ash"] {
            let entry = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
                .join("docs/design/macros/fixtures/header_compat")
                .join(name);
            let program = compile_path(RunConfiguration {
                entry,
                roots: ModuleRoots::empty(),
            })
            .unwrap_or_else(|failure| panic!("{name}: {failure:?}"));
            let value = execute(&program).unwrap();
            assert_eq!(value.value_display(), "42", "{name}");
            assert_eq!(value.type_display(), "Int", "{name}");
        }

        let entry = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("docs/design/macros/fixtures/header_compat/collision.ash");
        let failure = compile_path(RunConfiguration {
            entry,
            roots: ModuleRoots::empty(),
        })
        .unwrap_err();
        let Some(PipelineFailure::Resolution(error)) = failure.pipeline_failure() else {
            panic!("expected an import collision after definition admission: {failure:?}");
        };
        assert_eq!(error.reason, crate::resolve::ResolveReason::ImportConflict);
        let source = failure
            .sources()
            .iter()
            .find(|source| source.id() == error.primary.span().source())
            .expect("the importer is retained");
        assert!(source.display_path().ends_with("collision.ash"));
        let range = error.primary.span().range();
        assert_eq!(
            &source.text()[range.start() as usize..range.end() as usize],
            "declaration"
        );
    }

    #[test]
    fn d6_template_admission_uses_the_defining_modules_expression_syntax() {
        let entry =
            TestSource::write("import forms (syntax make)\nmain : Unit -> Int\nmain () = 42\n");
        entry.write_sibling(
            "expressions.ash",
            include_str!("../docs/design/macros/fixtures/header_compat/expressions.ash"),
        );
        entry.write_sibling(
            "forms.ash",
            "import expressions (syntax declaration)\n\
             pub syntax declaration: (make) $name:ident => {\n\
                 pub $name : Unit -> Int\n\
                 $name () = declaration : foo 42\n\
             }\n",
        );
        let program = compile_path(RunConfiguration {
            entry: entry.0.clone(),
            roots: ModuleRoots::empty(),
        })
        .expect("the template can contain expression syntax selected by its defining module");
        assert_eq!(execute(&program).unwrap().value_display(), "42");
    }

    #[test]
    fn copied_macro_fragments_have_distinct_checked_local_identities() {
        fn reachable(
            program: &ValidatedEffectProgram,
            root: crate::core::NodeId,
        ) -> Vec<&crate::core::EffectExpr> {
            let mut pending = vec![root];
            let mut seen = std::collections::HashSet::new();
            let mut nodes = Vec::new();
            while let Some(id) = pending.pop() {
                if !seen.insert(id) {
                    continue;
                }
                let node = program.node(id).expect("the validated child exists");
                pending.extend(
                    (0..node.kind.child_count()).filter_map(|index| node.kind.child_at(index)),
                );
                nodes.push(node);
            }
            nodes
        }
        fn uses(nodes: &[&crate::core::EffectExpr], binder: crate::resolved::BinderId) -> bool {
            nodes.iter().any(|node| {
                matches!(
                    &node.kind,
                    crate::core::EffectExprKind::Pure(crate::core::PureExprKind::Variable(variable))
                        if variable.binder() == binder
                )
            })
        }

        let fixture = |name: &str| RunConfiguration {
            entry: PathBuf::from(env!("CARGO_MANIFEST_DIR"))
                .join("tests/fixtures/surface-macros/copied-declarations")
                .join(name),
            roots: ModuleRoots::empty(),
        };

        let mut previous: Option<([ByteRange; 6], String)> = None;
        for _ in 0..2 {
            let compiled = compile_path(fixture("binder.ash")).expect("copied binders compile");
            let (program, _) = compiled
                .effect_build_input()
                .expect("validated effect Core");
            let source = compiled
                .provenance
                .iter()
                .find(|(_, source)| {
                    source
                        .display_path()
                        .ends_with("copied-declarations/binder.ash")
                })
                .expect("caller source")
                .1
                .id();
            let bindings = program
                .nodes()
                .iter()
                .filter_map(|node| match &node.kind {
                    crate::core::EffectExprKind::Pure(crate::core::PureExprKind::Computation(
                        crate::core::PureComputation::Bind(binding),
                    )) if binding.binder().origin().primary_span().source() == source => {
                        Some(binding)
                    }
                    _ => None,
                })
                .collect::<Vec<_>>();
            let pair = bindings
                .iter()
                .enumerate()
                .find_map(|(index, first)| {
                    bindings[index + 1..].iter().find_map(|second| {
                        (first.binder().origin().primary_span()
                            == second.binder().origin().primary_span()
                            && first.binder().id() != second.binder().id())
                        .then_some((*first, *second))
                    })
                })
                .expect("copies of the same source binding receive distinct identities");
            for binding in [pair.0, pair.1] {
                assert!(uses(
                    &reachable(program, binding.body()),
                    binding.binder().id()
                ));
            }
            let binder_ranges = [
                pair.0.binder().origin().primary_span().range(),
                pair.1.binder().origin().primary_span().range(),
            ];
            assert_eq!(execute(&compiled).unwrap().value_display(), "42");

            let compiled = compile_path(fixture("combined.ash"))
                .expect("copied newtypes, resources, and nested syntax compile");
            let (program, _) = compiled
                .effect_build_input()
                .expect("validated effect Core");
            let [first, second] = program.registry().lexical_nominals() else {
                panic!("the two copies retain two local nominal declarations");
            };
            assert_eq!(first.origin.primary_span(), second.origin.primary_span());
            assert_ne!(first.id, second.id);
            assert_eq!(first.constructors.len(), 1);
            assert_eq!(second.constructors.len(), 1);
            assert_eq!(first.constructors[0].owner(), first.id);
            assert_eq!(second.constructors[0].owner(), second.id);
            let nominal_ranges = [
                first.origin.primary_span().range(),
                second.origin.primary_span().range(),
            ];
            for nominal in [first, second] {
                let scope = program
                    .nodes()
                    .iter()
                    .find_map(|node| match &node.kind {
                        crate::core::EffectExprKind::Pure(
                            crate::core::PureExprKind::Computation(
                                crate::core::PureComputation::LocalNominalScope(scope),
                            ),
                        ) if scope.owner() == nominal.id => Some(scope),
                        _ => None,
                    })
                    .expect("the copied nominal has its own scope");
                let descendants = reachable(program, scope.body());
                for direction in [
                    crate::core::NewtypeConversionDirection::Wrap,
                    crate::core::NewtypeConversionDirection::Unwrap,
                ] {
                    assert!(descendants.iter().any(|node| matches!(
                    &node.kind,
                    crate::core::EffectExprKind::Pure(crate::core::PureExprKind::Computation(
                        crate::core::PureComputation::NewtypeConversion(conversion),
                    )) if conversion.owner() == nominal.id && conversion.direction() == direction
                )), "each copy uses its own nominal for {direction:?}");
                }
            }
            let resources = program
                .nodes()
                .iter()
                .filter_map(|node| match &node.kind {
                    crate::core::EffectExprKind::Operation(
                        crate::core::EffectOperation::Resource(resource),
                    ) => Some(resource),
                    _ => None,
                })
                .collect::<Vec<_>>();
            let [first, second] = resources.as_slice() else {
                panic!("the two copies retain two resource scopes");
            };
            assert_ne!(first.acquisition.identity, second.acquisition.identity);
            assert_ne!(first.handle().id(), second.handle().id());
            for resource in [first, second] {
                assert!(uses(
                    &reachable(program, resource.body()),
                    resource.handle().id()
                ));
            }
            let initializer_use = |resource: &crate::core::effect::ResourceScopeNode| match &program
                .node(resource.initializer())
                .expect("resource initializer")
                .kind
            {
                crate::core::EffectExprKind::Pure(crate::core::PureExprKind::Variable(
                    variable,
                )) => variable.binder(),
                other => panic!("expected caller variable in resource initializer: {other:?}"),
            };
            let caller_source = compiled
                .provenance
                .iter()
                .find(|(_, source)| {
                    source
                        .display_path()
                        .ends_with("copied-declarations/combined.ash")
                })
                .expect("caller source")
                .1
                .id();
            let outside = u32::try_from(
                include_str!("../tests/fixtures/surface-macros/copied-declarations/combined.ash")
                    .find("outside = 20")
                    .expect("caller binding"),
            )
            .expect("the fixture offset fits a source span");
            let caller_binder = program
                .nodes()
                .iter()
                .find_map(|node| match &node.kind {
                    crate::core::EffectExprKind::Pure(crate::core::PureExprKind::Computation(
                        crate::core::PureComputation::Bind(binding),
                    )) if binding.binder().origin().primary_span().source() == caller_source
                        && binding.binder().origin().primary_span().range().start() == outside =>
                    {
                        Some(binding.binder().id())
                    }
                    _ => None,
                })
                .expect("the caller's outside binding remains in checked Core");
            assert_eq!(initializer_use(first), caller_binder);
            assert_eq!(initializer_use(second), caller_binder);
            let first_identity = program
                .registry()
                .type_variable(first.acquisition.identity)
                .expect("first resource identity");
            let second_identity = program
                .registry()
                .type_variable(second.acquisition.identity)
                .expect("second resource identity");
            assert_eq!(
                first_identity.origin.primary_span(),
                second_identity.origin.primary_span()
            );
            assert_eq!(execute(&compiled).unwrap().value_display(), "42");
            let resource_ranges = [
                first_identity.origin.primary_span().range(),
                second_identity.origin.primary_span().range(),
            ];
            let observation = (
                [
                    binder_ranges[0],
                    binder_ranges[1],
                    nominal_ranges[0],
                    nominal_ranges[1],
                    resource_ranges[0],
                    resource_ranges[1],
                ],
                compiled.type_display().to_owned(),
            );
            if let Some(previous) = &previous {
                assert_eq!(&observation, previous);
            }
            previous = Some(observation);
        }

        for control in ["region_handwritten.ash", "region_once.ash"] {
            let compiled = compile_path(fixture(control)).expect(control);
            assert_eq!(
                execute(&compiled).unwrap().value_display(),
                "42",
                "{control}"
            );
        }
        let compiled = compile_path(fixture("region.ash")).expect("copied regions compile");
        let (program, _) = compiled
            .effect_build_input()
            .expect("validated effect Core");
        let source = compiled
            .provenance
            .iter()
            .find(|(_, source)| {
                source
                    .display_path()
                    .ends_with("copied-declarations/region.ash")
            })
            .expect("caller source")
            .1
            .id();
        let fixture_source =
            include_str!("../tests/fixtures/surface-macros/copied-declarations/region.ash");
        let source_offset = |needle: &str| {
            u32::try_from(fixture_source.find(needle).expect("fixture binding"))
                .expect("the fixture offset fits a source span")
        };
        let outside = source_offset("outside = 20");
        let caller_binder = program
            .nodes()
            .iter()
            .find_map(|node| match &node.kind {
                crate::core::EffectExprKind::Pure(crate::core::PureExprKind::Computation(
                    crate::core::PureComputation::Bind(binding),
                )) if binding.binder().origin().primary_span().source() == source
                    && binding.binder().origin().primary_span().range().start() == outside =>
                {
                    Some(binding.binder().id())
                }
                _ => None,
            })
            .expect("the caller's outside binding remains in checked Core");
        let owner = source_offset("owner {");
        let regions = program
            .nodes()
            .iter()
            .filter_map(|node| match &node.kind {
                crate::core::EffectExprKind::Operation(crate::core::EffectOperation::Region(
                    scope,
                )) if scope.access().origin().primary_span().source() == source
                    && scope.access().origin().primary_span().range().start() == owner =>
                {
                    Some(scope)
                }
                _ => None,
            })
            .collect::<Vec<_>>();
        let [first, second] = regions.as_slice() else {
            panic!("the two copies retain two lexical region scopes");
        };
        assert_eq!(
            first.access().origin().primary_span(),
            second.access().origin().primary_span()
        );
        assert_ne!(first.identity(), second.identity());
        assert_ne!(first.access().id(), second.access().id());
        for region in [first, second] {
            let body = reachable(program, region.body());
            assert!(uses(&body, region.access().id()));
            assert!(uses(&body, caller_binder));
        }
        assert_eq!(execute(&compiled).unwrap().value_display(), "42");
    }

    #[test]
    fn deep_local_nominal_scope_census_fits_a_small_stack() {
        const DEPTH: usize = 4_096;
        std::thread::Builder::new().name("deep-local-nominal-census".to_owned())
            .stack_size(256 * 1024).spawn(|| {
                let mut declarations = String::new();
                for index in 0..DEPTH {
                    declarations.push_str(&format!("        newtype N{index} = N{index}(Int)\n"));
                }
                let accepted = TestSource::write(&format!(
                    "main : Unit -> Unit\nmain () = {{\n    let accepted = {{\n{declarations}        ()\n    }}\n    accepted\n}}\n"
                ));
                // This is the original integration witness's Core census under
                // existing paid program owners, not larger standalone defaults.
                let compiled = compile_path(accepted.configuration())
                    .unwrap_or_else(|failure| panic!("deep census: {failure:?}; work={:?}", failure.compilation_work()));
                let (program, _) = compiled.effect_build_input().expect("independently validated Effect Core");
                let mut pending = vec![program.root()];
                let mut seen = std::collections::HashSet::new();
                let mut scopes = 0;
                while let Some(id) = pending.pop() {
                    if !seen.insert(id) { continue; }
                    let node = program.node(id).expect("reachable deep Core node");
                    if matches!(node.kind, crate::core::EffectExprKind::Pure(
                        crate::core::PureExprKind::Computation(crate::core::PureComputation::LocalNominalScope(_)))) {
                        scopes += 1;
                    }
                    pending.extend((0..node.kind.child_count()).filter_map(|i| node.kind.child_at(i)));
                }
                assert_eq!(scopes, DEPTH);
                assert!(matches!(crate::eval::evaluate_effect(program).expect("deep Core executes").value, crate::eval::Value::Unit));
                let rejected = TestSource::write(&format!(
                    "main : Unit -> Unit\nmain () = {{\n    let escaped = {{\n{declarations}        N{}(0)\n    }}\n    ()\n}}\n", DEPTH - 1,
                ));
                let failure = compile_path(rejected.configuration())
                    .expect_err("the deep outward local identity must be rejected");
                let Some(PipelineFailure::Typing(TypeError::Source(diagnostic))) = failure.pipeline_failure() else {
                    panic!("deep escape stays source-owned: {failure:?}");
                };
                assert_eq!(diagnostic.reason, crate::elaborate::TypeReason::LocalNominalEscape);
            }).unwrap().join().expect("deep census and teardown fit the original small stack");
    }

    #[test]
    fn nested_source_execution_and_release_fit_a_fresh_small_stack() {
        const CHILD: &str = "ASH_RESOURCE_RUNTIME_STACK_CHILD";
        if std::env::var_os(CHILD).is_none() {
            let status = std::process::Command::new(std::env::current_exe().unwrap())
                .args([
                    "--exact",
                    "driver::tests::nested_source_execution_and_release_fit_a_fresh_small_stack",
                    "--nocapture",
                ])
                .env(CHILD, "1")
                .status()
                .unwrap();
            assert!(status.success(), "fresh resource runtime process: {status}");
            return;
        }
        std::thread::Builder::new()
            .stack_size(256 * 1024)
            .spawn(|| {
                let mut source =
                    String::from("import @builtin.cell as Cell\nmain : Unit -> Int\nmain () = ");
                for _ in 0..24 {
                    source.push_str("resource cell<R> c = 42 {\n");
                }
                source.push_str("Cell.read c\n");
                for _ in 0..24 {
                    source.push_str("}\n");
                }
                // Preserve the original staged pipeline and small-stack claim;
                // each compiler phase receives its existing canonical-source owner
                // allowance once. Standalone API defaults remain unchanged.
                let fixture = TestSource::write(&source);
                let graph = load_module_graph(&fixture.0, &ModuleRoots::empty()).unwrap();
                let (mut source_work, bytes) = crate::compiler_work::source_work(&graph).unwrap();
                let mut checked = Vec::<crate::resolved::CheckedModule>::new();
                for module in graph.modules() {
                    let dependencies = module
                        .dependencies()
                        .iter()
                        .map(|edge| {
                            crate::resolve::DependencyExports::new(
                                edge,
                                checked
                                    .iter()
                                    .find(|module| module.module() == edge.target())
                                    .unwrap()
                                    .exports(),
                            )
                            .unwrap()
                        })
                        .collect::<Vec<_>>();
                    let resolved = crate::resolve::resolve_module(module, &dependencies).unwrap();
                    checked.push(
                        crate::elaborate::check_module_with_budget_and_rewrite_work(
                            resolved,
                            &mut source_work,
                            &mut crate::pattern::UsefulnessBudget::default(),
                            &mut InterfaceConstraintBudget::default(),
                            Some(TypeWorkBudget::with_limit(
                                crate::compiler_work::primary_total(bytes).unwrap(),
                            )),
                            Some(TypeWorkBudget::with_limit(
                                crate::compiler_work::rewrite_total(bytes).unwrap(),
                            )),
                        )
                        .unwrap(),
                    );
                }
                let linked = crate::evidence_validation::validate_interface_evidence(
                    crate::elaborate::link_modules(checked, graph.entry()).unwrap(),
                )
                .unwrap();
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
                let (final_work, _) = crate::compiler_work::resident_phase_work(
                    crate::compiler_work::CompilationPhase::FinalElaboration,
                    &sources,
                )
                .unwrap();
                let mut elaborator = EffectElaborator::for_module_program_with_budgets(
                    &linked,
                    final_work,
                    TypeWorkBudget::with_limit(crate::compiler_work::primary_total(bytes).unwrap()),
                    TypeWorkBudget::with_limit(crate::compiler_work::rewrite_total(bytes).unwrap()),
                )
                .unwrap();
                let typed = elaborator
                    .synthesize_effect_module_program(&linked)
                    .unwrap();
                let (core, _) = elaborator.finish_with_work(typed.node).unwrap();
                let (mut core_work, _) = crate::compiler_work::resident_phase_work(
                    crate::compiler_work::CompilationPhase::IndependentCore,
                    &sources,
                )
                .unwrap();
                let program = crate::core::validate::validate_effect_modules_with_work(
                    core,
                    &sources,
                    &module_sources,
                    &mut core_work,
                )
                .unwrap();
                let result = crate::eval::evaluate_effect(&program).unwrap();
                assert_eq!(result.value.to_string(), "42");
                let released = result
                    .effect_trace()
                    .iter()
                    .filter_map(|event| match event {
                        crate::eval::EffectTraceEvent::ResourceReleased(key) => Some(*key),
                        _ => None,
                    })
                    .collect::<Vec<_>>();
                let acquired = result
                    .effect_trace()
                    .iter()
                    .filter_map(|event| match event {
                        crate::eval::EffectTraceEvent::ResourceAcquired(key) => Some(*key),
                        _ => None,
                    })
                    .collect::<Vec<_>>();
                assert_eq!(acquired.len(), 24);
                assert_eq!(
                    acquired
                        .iter()
                        .collect::<std::collections::HashSet<_>>()
                        .len(),
                    24
                );
                assert_eq!(released, acquired.into_iter().rev().collect::<Vec<_>>());
            })
            .unwrap()
            .join()
            .unwrap();
    }

    #[test]
    fn integer_cell_regressions_fit_normal_modular_allowances() {
        for (name, source) in [
            (
                "same-site",
                "import @builtin.cell as Cell\neffect Pause {\nask : Unit -> Unit\n}\nvisit : Int -> Int ! {Pause}\nvisit depth = resource cell<R> c = (match depth == 0 {\ntrue => 1\nfalse => 41\n}) {\nmatch depth == 0 {\ntrue => {\nlet _ = perform Pause.ask ()\nCell.read c\n}\nfalse => {\nlet observe : Unit -> Int ! {Cell.Ops<R>} = fn(ignored) {\nCell.read c\n}\nhandle (visit 0) with Pause {\nask ignored => {\nlet outer = observe ()\nlet inner = resume ()\nouter + inner\n}\n}\n}\n}\n}\nmain : Unit -> Int\nmain () = handle (visit 1) with Pause {\nask ignored => resume ()\n}\n\n",
            ),
            (
                "metadata",
                "import @builtin.cell as Cell\neffect E<T> {\nask : Unit -> Int\n}\neffect Pause {\nask : Unit -> Unit\n}\nvisit : Int -> Int ! {Pause}\nvisit depth = resource cell<R> c = depth {\nlet observe : Unit -> Int ! {E<R>} = fn(ignored) {\nperform E<R>.ask ()\n}\nhandle (match depth == 0 {\ntrue => {\nlet _ = perform Pause.ask ()\nobserve ()\n}\nfalse => {\nhandle (visit 0) with Pause {\nask ignored => {\nlet outer = observe ()\nlet inner = resume ()\nouter + inner\n}\n}\n}\n}) with E<R> {\nask ignored => resume (match depth == 0 {\ntrue => 1\nfalse => 41\n})\n}\n}\nmain : Unit -> Int\nmain () = handle (visit 1) with Pause {\nask ignored => resume ()\n}\n",
            ),
            (
                "nested24",
                "import @builtin.cell as Cell\nmain : Unit -> Int\nmain () = resource cell<R> c = 42 {\nresource cell<R> c = 42 {\nresource cell<R> c = 42 {\nresource cell<R> c = 42 {\nresource cell<R> c = 42 {\nresource cell<R> c = 42 {\nresource cell<R> c = 42 {\nresource cell<R> c = 42 {\nresource cell<R> c = 42 {\nresource cell<R> c = 42 {\nresource cell<R> c = 42 {\nresource cell<R> c = 42 {\nresource cell<R> c = 42 {\nresource cell<R> c = 42 {\nresource cell<R> c = 42 {\nresource cell<R> c = 42 {\nresource cell<R> c = 42 {\nresource cell<R> c = 42 {\nresource cell<R> c = 42 {\nresource cell<R> c = 42 {\nresource cell<R> c = 42 {\nresource cell<R> c = 42 {\nresource cell<R> c = 42 {\nresource cell<R> c = 42 {\nCell.read c\n}\n}\n}\n}\n}\n}\n}\n}\n}\n}\n}\n}\n}\n}\n}\n}\n}\n}\n}\n}\n}\n}\n}\n}\n",
            ),
        ] {
            let fixture = TestSource::write(source);
            let graph = load_module_graph(&fixture.0, &ModuleRoots::empty()).unwrap();
            let bytes: usize = graph
                .modules()
                .iter()
                .map(|module| module.source().text().len())
                .sum();
            let compiled = compile_path(fixture.configuration())
                .unwrap_or_else(|failure| panic!("{name}: {failure:?}"));
            eprintln!(
                "integer Cell {name}: canonical_bytes={bytes}, work={:?}",
                compiled.compilation_work()
            );
            let (program, _) = compiled.effect_build_input().expect("region Effect Core");
            let evaluation =
                crate::eval::evaluate_effect(program).expect("resource fixture evaluates");
            assert_eq!(evaluation.value.to_string(), "42");
            if name == "nested24" {
                use crate::eval::EffectTraceEvent;
                let acquired = evaluation
                    .effect_trace()
                    .iter()
                    .filter_map(|event| match event {
                        EffectTraceEvent::ResourceAcquired(key) => Some(*key),
                        _ => None,
                    })
                    .collect::<Vec<_>>();
                let released = evaluation
                    .effect_trace()
                    .iter()
                    .filter_map(|event| match event {
                        EffectTraceEvent::ResourceReleased(key) => Some(*key),
                        _ => None,
                    })
                    .collect::<Vec<_>>();
                assert_eq!(acquired.len(), 24);
                assert_eq!(
                    acquired
                        .iter()
                        .collect::<std::collections::HashSet<_>>()
                        .len(),
                    24
                );
                assert_eq!(released, acquired.into_iter().rev().collect::<Vec<_>>());
            }
            eprintln!("integer Cell {name}: result=42");
        }
    }

    #[test]
    fn deep_recursive_group_and_call_chain_use_explicit_work_stacks() {
        const MEMBERS: usize = 8_000;
        let worker = std::thread::Builder::new()
            .name("deep-recursive-group".into())
            .stack_size(256 * 1024)
            .spawn(|| {
                use std::fmt::Write as _;

                let mut text = String::from("main : Unit -> Int\nmain () = {\n");
                for index in 0..MEMBERS {
                    let introducer = if index == 0 { "let rec" } else { "and" };
                    if index + 1 == MEMBERS {
                        writeln!(text, "{introducer} f{index} : Unit -> Int = fn(ignored) {{")
                            .expect("String writing cannot fail");
                        text.push_str(
                            "let saved : Unit -> Int = fn(value) {\nf0 value\n}\n1\n}\n",
                        );
                    } else {
                        writeln!(
                            text,
                            "{introducer} f{index} : Unit -> Int = fn(ignored) {{\n1 + f{} ()\n}}",
                            index + 1
                        )
                        .expect("String writing cannot fail");
                    }
                }
                text.push_str("f0 ()\n}\n");

                let fixture = TestSource::write(&text);
                // The former integration harness used four separate public
                // calls, each with its own constraint ledger. Preserve that
                // aggregate stress envelope without changing driver admission
                // or resetting its continuous ledger between phases.
                const ORIGINAL_PHASE_ALLOWANCE: usize = 327_680;
                const AGGREGATE: usize = 4 * ORIGINAL_PHASE_ALLOWANCE;
                let mut constraints = InterfaceConstraintBudget::with_limit(AGGREGATE);
                let evidence_entry = Cell::new(0);
                let evidence_exit = Cell::new(0);
                let compiled = compile_path_with_consumers_internal(
                    fixture.configuration(),
                    &mut constraints,
                    |program, work, types| {
                        evidence_entry.set(work.used());
                        let result = validate_interface_evidence_with_budget(program, work, types);
                        evidence_exit.set(work.used());
                        result
                    },
                    validate_modular_effect_core,
                    true,
                    ProvenanceRetention::Retain,
                );
                eprintln!("deep stress constraints: aggregate={AGGREGATE}, evidence_entry={}, evidence_exit={}, total={}",
                    evidence_entry.get(), evidence_exit.get(), constraints.used());
                let compiled = compiled.unwrap_or_else(|failure| panic!(
                    "recursive stress compilation failed: {:?}", failure.pipeline_failure()));
                assert!(evidence_entry.get() <= 3 * ORIGINAL_PHASE_ALLOWANCE);
                assert!(evidence_exit.get() - evidence_entry.get() <= ORIGINAL_PHASE_ALLOWANCE);
                let (program, _) = compiled
                    .effect_build_input()
                    .expect("explicit default root uses Effect Core");
                let evaluation =
                    crate::eval::evaluate_effect(program).expect("recursive chain should evaluate");

                assert_eq!(evaluation.value.to_string(), MEMBERS.to_string());
                assert!(evaluation.trace.len() > MEMBERS * 5);
            })
            .expect("depth-test thread should start");

        worker
            .join()
            .expect("recursive pipeline and destruction should stay within the host stack budget");
    }

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

    std::thread_local! {
        static S3_TRANSFERRED: RefCell<Option<(Vec<crate::syntax::MacroOutputNode>, Vec<crate::surface::SurfaceSyntaxCapture>)>> = const { RefCell::new(None) };
        static DERIVE_INPUTS: RefCell<Vec<Vec<crate::surface::SurfaceSyntaxCapture>>> = const { RefCell::new(Vec::new()) };
        static DERIVE_MODULE_ORDER: RefCell<Option<Vec<String>>> = const { RefCell::new(None) };
        static INDEXED_TRANSFERRED: RefCell<Vec<(Vec<crate::surface::SurfaceSyntaxCapture>, Vec<crate::syntax::MacroOutputNode>)>> = const { RefCell::new(Vec::new()) };
        static DERIVE_WORK: RefCell<Vec<usize>> = const { RefCell::new(Vec::new()) };
        static BOUNDED_OUTPUTS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
        static GENERATOR_BINDERS: RefCell<Option<(crate::resolved::BinderId, crate::resolved::BinderId)>> = const { RefCell::new(None) };
        static GENERATOR_TRACE: RefCell<Vec<&'static str>> = const { RefCell::new(Vec::new()) };
        static GENERATOR_OUTPUT: RefCell<Vec<String>> = const { RefCell::new(Vec::new()) };
        static GENERATOR_ORDER: RefCell<Vec<String>> = const { RefCell::new(Vec::new()) };
        static GENERATOR_PLAN: RefCell<Vec<(String, String)>> = const { RefCell::new(Vec::new()) };
        static GENERATOR_TRANSFERS: Cell<usize> = const { Cell::new(0) };
        static GENERATOR_LIFECYCLES: RefCell<Vec<[usize; 5]>> = const { RefCell::new(Vec::new()) };
        static ESCAPE_OBSERVATIONS: RefCell<Vec<String>> = const { RefCell::new(Vec::new()) };
        static ESCAPE_CHECKED_HELPERS: Cell<usize> = const { Cell::new(0) };
    }

    fn observe_generator_owner(
        owner: &crate::resolved::CheckedModule,
        plan: &crate::syntax::GeneratorPlan,
    ) {
        let binder = |name| {
            owner
                .schemes()
                .iter()
                .find(|scheme| scheme.spelling == name)
                .expect("the original forms module owns the step")
                .binder
        };
        GENERATOR_BINDERS
            .with(|slot| *slot.borrow_mut() = Some((binder("is_first"), binder("next_number"))));
        GENERATOR_PLAN.with(|slot| {
            *slot.borrow_mut() = plan
                .actions
                .iter()
                .map(|action| match action {
                    crate::syntax::GeneratorAction::Enter {
                        generators,
                        binding,
                        ..
                    } => ("enter".to_owned(), generators[*binding].name.text.clone()),
                    crate::syntax::GeneratorAction::Advance {
                        generators,
                        binding,
                        ..
                    } => ("step".to_owned(), generators[*binding].name.text.clone()),
                    crate::syntax::GeneratorAction::Escape {
                        escapes,
                        descriptor,
                        ..
                    } => (
                        "escape".to_owned(),
                        escapes[*descriptor].adapter.text.clone(),
                    ),
                })
                .collect();
        });
    }

    fn observe_generator_trace(
        entry: &crate::core::validate::ValidatedMacroEntry,
        evaluation: &crate::eval::Evaluation,
    ) {
        use crate::core::{EffectExprKind, PureComputation, PureExprKind};
        let (first, number) = GENERATOR_BINDERS.with(|slot| slot.borrow().unwrap());
        GENERATOR_TRACE.with(|slot| {
            let mut output = slot.borrow_mut();
            for event in &evaluation.trace {
                let crate::eval::TraceEvent::Enter(node) = event;
                let Some(expression) = entry.program.node(*node) else {
                    continue;
                };
                let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Apply(
                    application,
                ))) = &expression.kind
                else {
                    continue;
                };
                let mut function = application.function();
                let variable = loop {
                    let Some(function_expression) = entry.program.node(function) else {
                        break None;
                    };
                    match &function_expression.kind {
                        EffectExprKind::Pure(PureExprKind::Variable(variable)) => {
                            break Some(variable);
                        }
                        EffectExprKind::Pure(PureExprKind::Computation(
                            PureComputation::TypeApplication(application),
                        )) => {
                            function = application.function();
                        }
                        _ => break None,
                    }
                };
                let Some(variable) = variable else {
                    continue;
                };
                let name = if variable.binder() == first {
                    Some("is_first")
                } else if variable.binder() == number {
                    Some("next_number")
                } else {
                    None
                };
                if let Some(name) = name {
                    output.push(name);
                }
            }
        });
    }

    fn observe_generator_lifecycle(before: [usize; 5], after: [usize; 5]) {
        GENERATOR_LIFECYCLES.with(|slot| {
            slot.borrow_mut()
                .push(std::array::from_fn(|index| after[index] - before[index]));
        });
    }

    fn assert_generator_cleanup(ordinary_executions: usize) {
        use crate::eval::machine_test_hooks as hooks;
        assert_eq!(hooks::TRANSFER_FAILURES.get(), 0);
        assert_eq!(
            hooks::ROOT_CLOSES.get(),
            hooks::TRANSFORMER_DROPS.get() + ordinary_executions
        );
        assert_eq!(hooks::ACTIVE_ROOT_DROPS.get(), 0);
    }

    fn observe_escape_checked_owner(
        owner: &crate::resolved::CheckedModule,
        plan: &crate::syntax::GeneratorPlan,
    ) {
        for action in &plan.actions {
            let crate::syntax::GeneratorAction::Escape {
                escapes,
                descriptor,
                ..
            } = action
            else {
                panic!("the early categories adapter contains only escapes")
            };
            let helper = &escapes[*descriptor].adapter;
            let scheme = owner
                .schemes()
                .iter()
                .find(|scheme| scheme.spelling == helper.text)
                .expect("the final defining owner contains the actual escape helper");
            assert_eq!(scheme.binder.module(), Some(owner.module()));
            assert_eq!(owner.span().source(), helper.span.source());
            assert!(scheme.scheme.type_parameters.is_empty());
            assert!(scheme.scheme.requirements.is_empty());
            ESCAPE_CHECKED_HELPERS.set(ESCAPE_CHECKED_HELPERS.get() + 1);
        }
    }

    fn observe_escape_categories(
        selection: &crate::syntax::SelectedSyntax,
        captures: &[crate::surface::SurfaceSyntaxCapture],
        output: &[crate::syntax::MacroOutputNode],
    ) {
        use crate::{
            eval::machine_test_hooks as hooks,
            surface::{SurfaceExprKind, SurfaceSyntaxCapture},
            syntax::MacroOutputNode,
        };
        let name = selection.declaration.name.text.as_str();
        assert_eq!(hooks::ROOT_CLOSES.get(), hooks::TRANSFORMER_DROPS.get());
        assert_eq!(hooks::ACTIVE_ROOT_DROPS.get(), 0);
        match name {
            "make_expr" | "local_capture" => {
                let original = captures
                    .iter()
                    .find_map(|capture| match capture {
                        SurfaceSyntaxCapture::Expression(value) => Some(value),
                        _ => None,
                    })
                    .expect("the caller expression is captured");
                let [MacroOutputNode::Expression(returned, origin)] = output else {
                    panic!("{name} returns one quoted Expression: {output:?}")
                };
                fn has_caller_fragment(
                    nodes: &[MacroOutputNode],
                    original: &crate::surface::SurfaceExpressionCapture,
                ) -> bool {
                    nodes.iter().any(|node| match node {
                        MacroOutputNode::Group(_, children, _) => {
                            has_caller_fragment(children, original)
                        }
                        MacroOutputNode::Expression(fragment, _)
                        | MacroOutputNode::ForwardedExpression(fragment, _) => {
                            Arc::ptr_eq(&fragment.contents, &original.contents)
                                || has_caller_fragment(&fragment.contents, original)
                        }
                        _ => false,
                    })
                }
                assert!(
                    has_caller_fragment(&returned.contents, original),
                    "{name} retains the caller fragment and its original context: {returned:?}"
                );
                assert_eq!(origin.primary().source(), original.expression.span.source());
                let SurfaceExprKind::Add(addition) = &returned.expression.kind else {
                    panic!("the returned quote retains its addition")
                };
                let (caller, local, local_value) = if name == "make_expr" {
                    (&addition.left, &addition.right, "100")
                } else {
                    (&addition.right, &addition.left, "7")
                };
                assert_eq!(caller.span, original.expression.span);
                let caller_location = caller.diagnostic.as_ref().expect("caller origin");
                assert_eq!(caller_location.primary.primary(), original.expression.span);
                assert!(caller_location.captured_expression);
                assert!(
                    caller_location
                        .frames
                        .iter()
                        .any(|frame| frame.invocation.source()
                            == original.expression.span.source()
                            && frame.definition.source() == selection.declaration.span.source())
                );
                let SurfaceExprKind::Integer(value) = &local.kind else {
                    panic!("the definition quote retains its literal")
                };
                assert_eq!(value.to_string(), local_value);
                assert_eq!(
                    local
                        .diagnostic
                        .as_ref()
                        .unwrap()
                        .primary
                        .primary()
                        .source(),
                    selection.declaration.span.source()
                );
                assert_eq!(
                    addition.operator_span.source(),
                    selection.declaration.span.source()
                );
                eprintln!("{name}: caller fragment and definition literal retain separate origins");
            }
            "make_ident" => {
                let original = captures
                    .iter()
                    .find_map(|capture| match capture {
                        SurfaceSyntaxCapture::Identifier(value) => Some(value),
                        _ => None,
                    })
                    .expect("the caller identifier is captured");
                assert_eq!(output.len(), 2);
                for node in output {
                    let MacroOutputNode::Identifier(returned, origin) = node else {
                        panic!("the identifier escape returns identifier and origin")
                    };
                    assert_eq!(returned, &original.name);
                    assert_eq!(origin, &original.origin);
                }
            }
            "make_type" => {
                let original = captures
                    .iter()
                    .find_map(|capture| match capture {
                        SurfaceSyntaxCapture::Type(value) => Some(value),
                        _ => None,
                    })
                    .expect("the caller type is captured");
                assert_eq!(output.len(), 2);
                for node in output {
                    let MacroOutputNode::ForwardedType(returned, origin) = node else {
                        panic!("the type escape returns a protected type")
                    };
                    assert_eq!(returned.ty, original.ty);
                    assert!(Arc::ptr_eq(&returned.contents, &original.contents));
                    assert_eq!(origin.primary().source(), original.ty.span.source());
                }
            }
            "make_pattern" => {
                let original = captures
                    .iter()
                    .find_map(|capture| match capture {
                        SurfaceSyntaxCapture::Pattern(value) => Some(value),
                        _ => None,
                    })
                    .expect("the caller pattern is captured");
                let [MacroOutputNode::ForwardedPattern(returned, origin)] = output else {
                    panic!("the pattern escape returns a protected pattern")
                };
                assert_eq!(returned.pattern, original.pattern);
                assert!(Arc::ptr_eq(&returned.contents, &original.contents));
                assert_eq!(origin.primary().source(), original.pattern.span.source());
            }
            "pass_declaration" => {
                let original = captures
                    .iter()
                    .find_map(|capture| match capture {
                        SurfaceSyntaxCapture::Declaration(value) => Some(value),
                        _ => None,
                    })
                    .expect("the caller declaration is captured");
                let [MacroOutputNode::ForwardedDeclaration(returned, _)] = output else {
                    panic!("the declaration escape returns a protected declaration")
                };
                assert!(Arc::ptr_eq(&returned.contents, &original.contents));
                assert_eq!(returned.contents, original.contents);
            }
            _ => return,
        }
        ESCAPE_OBSERVATIONS.with(|slot| slot.borrow_mut().push(name.to_owned()));
    }

    #[test]
    fn original_escape_categories_retain_captures_after_host_teardown() {
        use crate::eval::machine_test_hooks as hooks;

        hooks::reset();
        ESCAPE_OBSERVATIONS.with(|slot| slot.borrow_mut().clear());
        ESCAPE_CHECKED_HELPERS.set(0);
        GENERATOR_LIFECYCLES.with(|slot| slot.borrow_mut().clear());
        GENERATOR_OWNER_OBSERVER.set(Some(observe_escape_checked_owner));
        GENERATOR_LIFECYCLE_OBSERVER.set(Some(observe_generator_lifecycle));
        TRANSFORMER_OUTPUT_OBSERVER.set(Some(observe_escape_categories));
        let compiled = compile_path(RunConfiguration {
            entry: PathBuf::from(env!("CARGO_MANIFEST_DIR"))
                .join("docs/design/macros/fixtures/escapes/early_categories.ash"),
            roots: ModuleRoots::empty(),
        })
        .expect("the unchanged early categories graph compiles");
        GENERATOR_OWNER_OBSERVER.set(None);
        GENERATOR_LIFECYCLE_OBSERVER.set(None);
        TRANSFORMER_OUTPUT_OBSERVER.set(None);
        assert_eq!(ESCAPE_CHECKED_HELPERS.get(), 8);
        assert_eq!(
            ESCAPE_OBSERVATIONS.with(|slot| slot.borrow().clone()),
            [
                "make_expr",
                "local_capture",
                "make_ident",
                "make_type",
                "make_pattern",
                "pass_declaration",
            ]
        );
        assert_eq!(
            GENERATOR_LIFECYCLES.with(|slot| slot.borrow().clone()),
            vec![[1, 0, 1, 1, 0]; 6]
        );
        assert_generator_cleanup(0);
        assert_eq!(execute(&compiled).unwrap().value_display(), "246");
        assert_generator_cleanup(1);
        hooks::reset();
    }

    fn observe_generator_output(
        selection: &crate::syntax::SelectedSyntax,
        _captures: &[crate::surface::SurfaceSyntaxCapture],
        output: &[crate::syntax::MacroOutputNode],
    ) {
        use crate::{surface::SurfaceExprKind, syntax::MacroOutputNode};
        if !matches!(
            selection.declaration.name.text.as_str(),
            "make_constants" | "mixed_depth"
        ) {
            return;
        }
        GENERATOR_TRANSFERS.set(GENERATOR_TRANSFERS.get() + 1);
        GENERATOR_OUTPUT.with(|slot| {
            let mut values = slot.borrow_mut();
            for node in output {
                let MacroOutputNode::Expression(capture, _) = node else {
                    panic!("the generator returned expression fragments")
                };
                values.push(match &capture.expression.kind {
                    SurfaceExprKind::Boolean(value) => value.to_string(),
                    SurfaceExprKind::Integer(value) => value.to_string(),
                    other => panic!("the fixed step returned an unexpected fragment: {other:?}"),
                });
            }
        });
    }

    fn observe_generator_order(_source: &SourceFile, module: &crate::surface::SurfaceModule) {
        use crate::surface::SurfaceDefinitionKind;
        let names = module
            .definitions
            .iter()
            .filter_map(|definition| match &definition.kind {
                SurfaceDefinitionKind::Equational(global) => {
                    Some(global.interface.name.text.as_str())
                }
                SurfaceDefinitionKind::InlineOperational(_) => None,
            })
            .filter(|name| ["first", "second", "third"].contains(name))
            .map(str::to_owned)
            .collect::<Vec<_>>();
        if !names.is_empty() {
            GENERATOR_ORDER.with(|slot| *slot.borrow_mut() = names);
        }
    }

    #[test]
    fn original_generator_steps_once_per_iteration_and_survives_host_teardown() {
        use crate::eval::machine_test_hooks as hooks;
        use crate::parser::STAGED_MODULE_OBSERVER;

        hooks::reset();
        GENERATOR_TRACE.with(|slot| slot.borrow_mut().clear());
        GENERATOR_OUTPUT.with(|slot| slot.borrow_mut().clear());
        GENERATOR_ORDER.with(|slot| slot.borrow_mut().clear());
        GENERATOR_PLAN.with(|slot| slot.borrow_mut().clear());
        GENERATOR_TRANSFERS.set(0);
        GENERATOR_LIFECYCLES.with(|slot| slot.borrow_mut().clear());
        GENERATOR_OWNER_OBSERVER.set(Some(observe_generator_owner));
        GENERATOR_LIFECYCLE_OBSERVER.set(Some(observe_generator_lifecycle));
        hooks::TRANSFORMER_EVALUATION_OBSERVER.set(Some(observe_generator_trace));
        TRANSFORMER_OUTPUT_OBSERVER.set(Some(observe_generator_output));
        STAGED_MODULE_OBSERVER.set(Some(observe_generator_order));
        let fixtures = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("docs/design/macros/fixtures/generators");
        let compiled = compile_path(RunConfiguration {
            entry: fixtures.join("main.ash"),
            roots: ModuleRoots::empty(),
        })
        .expect("the unchanged I17 graph compiles");
        GENERATOR_OWNER_OBSERVER.set(None);
        GENERATOR_LIFECYCLE_OBSERVER.set(None);
        hooks::TRANSFORMER_EVALUATION_OBSERVER.set(None);
        TRANSFORMER_OUTPUT_OBSERVER.set(None);
        STAGED_MODULE_OBSERVER.set(None);
        assert_generator_cleanup(0);
        assert_eq!(execute(&compiled).unwrap().value_display(), "310");
        assert_generator_cleanup(1);
        assert_eq!(
            GENERATOR_PLAN.with(|slot| slot.borrow().clone()),
            [
                ("enter".to_owned(), "number".to_owned()),
                ("enter".to_owned(), "first".to_owned()),
                ("step".to_owned(), "first".to_owned()),
                ("step".to_owned(), "number".to_owned()),
                ("step".to_owned(), "first".to_owned()),
                ("step".to_owned(), "number".to_owned()),
                ("step".to_owned(), "first".to_owned()),
                ("step".to_owned(), "number".to_owned()),
            ]
        );
        assert_eq!(
            GENERATOR_TRACE.with(|slot| slot.borrow().clone()),
            [
                "is_first",
                "next_number",
                "is_first",
                "next_number",
                "is_first",
                "next_number"
            ]
        );
        assert_eq!(
            GENERATOR_OUTPUT.with(|slot| slot.borrow().clone()),
            ["true", "0", "false", "1", "false", "2"]
        );
        assert_eq!(
            GENERATOR_ORDER.with(|slot| slot.borrow().clone()),
            ["first", "second", "third"]
        );
        assert_eq!(GENERATOR_TRANSFERS.get(), 1);
        assert_eq!(
            GENERATOR_LIFECYCLES.with(|slot| slot.borrow().clone()),
            [[1, 0, 1, 1, 0]]
        );
        assert_generator_cleanup(1);

        // A separate ordinary consumer calls every unchanged generated output
        // after expansion's host has transferred and closed its root.
        let consumer = TestSource::write(concat!(
            "import original (first, second, third)\n",
            "main : Unit -> Int\n",
            "main () = match (first(()) == 100, second(()) == 1, third(()) == 2) {\n",
            "    (true, true, true) => 42\n",
            "    _ => 0\n",
            "}\n",
        ));
        consumer.write_sibling(
            "original.ash",
            &fs::read_to_string(fixtures.join("main.ash")).unwrap(),
        );
        consumer.write_sibling(
            "forms.ash",
            &fs::read_to_string(fixtures.join("forms.ash")).unwrap(),
        );
        let compiled =
            compile_path(consumer.configuration()).expect("the generated functions remain usable");
        assert_generator_cleanup(1);
        assert_eq!(execute(&compiled).unwrap().value_display(), "42");
        assert_generator_cleanup(2);
        hooks::reset();
    }

    #[test]
    fn two_generator_invocations_do_not_alias_their_checked_entries() {
        use crate::eval::machine_test_hooks as hooks;

        hooks::reset();
        GENERATOR_OUTPUT.with(|slot| slot.borrow_mut().clear());
        GENERATOR_TRANSFERS.set(0);
        GENERATOR_LIFECYCLES.with(|slot| slot.borrow_mut().clear());
        GENERATOR_LIFECYCLE_OBSERVER.set(Some(observe_generator_lifecycle));
        TRANSFORMER_OUTPUT_OBSERVER.set(Some(observe_generator_output));
        let source = TestSource::write(concat!(
            "import forms (syntax make_constants)\n",
            "make_constants starting_at 0 names first, second, third\n",
            "make_constants starting_at 3 names fourth, fifth, sixth\n",
            "main : Unit -> Int\n",
            "main () = match (first(()) == 100, second(()) == 1, third(()) == 2, fourth(()) == 103, fifth(()) == 4, sixth(()) == 5) {\n",
            "    (true, true, true, true, true, true) => 42\n",
            "    _ => 0\n",
            "}\n",
        ));
        let forms = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("docs/design/macros/fixtures/generators/forms.ash");
        source.write_sibling("forms.ash", &fs::read_to_string(forms).unwrap());
        let compiled = compile_path(source.configuration())
            .expect("both independent generator invocations compile");
        TRANSFORMER_OUTPUT_OBSERVER.set(None);
        GENERATOR_LIFECYCLE_OBSERVER.set(None);
        assert_generator_cleanup(0);
        assert_eq!(execute(&compiled).unwrap().value_display(), "42");
        assert_generator_cleanup(1);
        assert_eq!(GENERATOR_TRANSFERS.get(), 2);
        assert_eq!(
            GENERATOR_OUTPUT.with(|slot| slot.borrow().clone()),
            [
                "true", "0", "false", "1", "false", "2", "true", "3", "false", "4", "false", "5"
            ]
        );
        assert_eq!(
            GENERATOR_LIFECYCLES.with(|slot| slot.borrow().clone()),
            [[1, 0, 1, 1, 0], [1, 0, 1, 1, 0]]
        );
        assert_generator_cleanup(1);
        hooks::reset();
    }

    #[test]
    fn mixed_depth_generator_restores_each_outer_cached_value() {
        use crate::eval::machine_test_hooks as hooks;

        hooks::reset();
        GENERATOR_TRACE.with(|slot| slot.borrow_mut().clear());
        GENERATOR_OUTPUT.with(|slot| slot.borrow_mut().clear());
        GENERATOR_LIFECYCLES.with(|slot| slot.borrow_mut().clear());
        GENERATOR_TRANSFERS.set(0);
        GENERATOR_OWNER_OBSERVER.set(Some(observe_generator_owner));
        GENERATOR_LIFECYCLE_OBSERVER.set(Some(observe_generator_lifecycle));
        hooks::TRANSFORMER_EVALUATION_OBSERVER.set(Some(observe_generator_trace));
        TRANSFORMER_OUTPUT_OBSERVER.set(Some(observe_generator_output));
        let fixtures = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("docs/design/macros/fixtures/generators");
        let compiled = compile_path(RunConfiguration {
            entry: fixtures.join("mixed_depth.ash"),
            roots: ModuleRoots::empty(),
        })
        .expect("the unchanged mixed-depth graph compiles");
        GENERATOR_OWNER_OBSERVER.set(None);
        GENERATOR_LIFECYCLE_OBSERVER.set(None);
        hooks::TRANSFORMER_EVALUATION_OBSERVER.set(None);
        TRANSFORMER_OUTPUT_OBSERVER.set(None);
        assert_generator_cleanup(0);
        assert_eq!(execute(&compiled).unwrap().value_display(), "546210");
        assert_generator_cleanup(1);
        assert_eq!(
            GENERATOR_TRACE.with(|slot| slot.borrow().clone()),
            ["next_number"; 6]
        );
        assert_eq!(
            GENERATOR_OUTPUT.with(|slot| slot.borrow().clone()),
            ["0", "1", "2", "3", "4", "5"]
        );
        assert_eq!(GENERATOR_TRANSFERS.get(), 1);
        assert_eq!(
            GENERATOR_LIFECYCLES.with(|slot| slot.borrow().clone()),
            [[1, 0, 1, 1, 0]]
        );
        assert_generator_cleanup(1);

        // These eight ordinary calls expose the repeated outer values on both
        // sides of each nested repetition, after the host root is closed.
        let consumer = TestSource::write(concat!(
            "import original (left_before, first, second, left_after, right_before, third, fourth, right_after)\n",
            "main : Unit -> Int\n",
            "main () = match (left_before(()) == 0, first(()) == 1, second(()) == 2, left_after(()) == 0, right_before(()) == 3, third(()) == 4, fourth(()) == 5, right_after(()) == 3) {\n",
            "    (true, true, true, true, true, true, true, true) => 42\n",
            "    _ => 0\n",
            "}\n",
        ));
        consumer.write_sibling(
            "original.ash",
            &fs::read_to_string(fixtures.join("mixed_depth.ash")).unwrap(),
        );
        consumer.write_sibling(
            "forms.ash",
            &fs::read_to_string(fixtures.join("forms.ash")).unwrap(),
        );
        let compiled =
            compile_path(consumer.configuration()).expect("the mixed-depth outputs remain usable");
        assert_generator_cleanup(1);
        assert_eq!(execute(&compiled).unwrap().value_display(), "42");
        assert_generator_cleanup(2);
        hooks::reset();
    }

    fn observe_derive_input(
        _source: &SourceFile,
        captures: &[crate::surface::SurfaceSyntaxCapture],
        _budget: &crate::syntax_resource::SyntaxBudget,
    ) {
        if matches!(
            captures.first(),
            Some(crate::surface::SurfaceSyntaxCapture::Declaration(_))
        ) {
            DERIVE_INPUTS.with(|slot| slot.borrow_mut().push(captures.to_vec()));
        }
    }

    fn observe_derive_module(_source: &SourceFile, module: &crate::surface::SurfaceModule) {
        use crate::surface::{SurfaceDeclarationIndex, SurfaceTypeKind};
        if !module
            .type_declarations
            .iter()
            .any(|item| item.name.text == "Color")
            || !module
                .type_declarations
                .iter()
                .any(|item| item.name.text == "Count")
        {
            return;
        }
        let mut order = Vec::new();
        for item in &module.declaration_order {
            match *item {
                SurfaceDeclarationIndex::Type(index) => {
                    order.push(module.type_declarations[index].name.text.clone())
                }
                SurfaceDeclarationIndex::Implementation(index) => {
                    let implementation = &module.implementations[index];
                    let [argument] = implementation.head.arguments.as_ref() else {
                        panic!("one interface argument")
                    };
                    let SurfaceTypeKind::Named(name) = &argument.kind else {
                        panic!("the subject is a named nominal")
                    };
                    order.push(format!(
                        "{}<{}>",
                        implementation.head.interface.member().text,
                        name.member().text
                    ));
                }
                _ => {}
            }
        }
        DERIVE_MODULE_ORDER.with(|slot| *slot.borrow_mut() = Some(order));
    }

    #[test]
    fn rejected_generated_derive_location_is_paid_and_retryable() {
        use crate::syntax_resource::SyntaxBudget;

        let mut failure = compile_path(RunConfiguration {
            entry: PathBuf::from(env!("CARGO_MANIFEST_DIR"))
                .join("docs/design/macros/fixtures/derives/generated_failure.ash"),
            roots: ModuleRoots::empty(),
        })
        .expect_err("the nested checked derive rejects");
        let FileFailure::Pipeline(context) = &mut failure else {
            panic!("the checked host produces a pipeline failure");
        };
        let PipelineFailure::SyntaxExpansion(rejection) = context.failure.as_mut() else {
            panic!("the authored rejection remains intact");
        };
        let location = rejection
            .invocation_location
            .take()
            .expect("the real invocation location is retained");
        assert!(!location.related.is_empty());
        assert!(!location.frames.is_empty());
        let mut measured = SyntaxBudget::default();
        rejection
            .retain_invocation_location(&location, &mut measured)
            .unwrap();
        let used = measured.consumed();
        assert!(used > 1);
        let mut prior_copy = SyntaxBudget::default();
        crate::syntax::charge_diagnostic_location_copy(&location, &mut prior_copy).unwrap();
        assert_eq!(used, prior_copy.consumed() + location.frames.len());
        assert_eq!(rejection.invocation_location.take().unwrap(), location);
        for limit in [0, used - 1] {
            let mut short = SyntaxBudget::with_limit(limit);
            assert!(matches!(
                rejection.retain_invocation_location(&location, &mut short),
                Err(ResourceFailure::SyntaxWork { limit: found }) if found == limit
            ));
            assert!(rejection.invocation_location.is_none());
            assert_eq!(rejection.message(), "first derive rejected");
        }
        let mut exact = SyntaxBudget::with_limit(used);
        rejection
            .retain_invocation_location(&location, &mut exact)
            .unwrap();
        assert_eq!(exact.consumed(), used);
        assert_eq!(rejection.invocation_location.as_deref(), Some(&*location));
    }

    fn observe_bounded_output(
        selection: &crate::syntax::SelectedSyntax,
        _captures: &[crate::surface::SurfaceSyntaxCapture],
        _output: &[crate::syntax::MacroOutputNode],
    ) {
        if selection.declaration.name.text == "repeat" {
            BOUNDED_OUTPUTS.set(BOUNDED_OUTPUTS.get() + 1);
        }
    }

    #[test]
    fn checked_derive_recursion_stops_at_existing_bound_and_closes_hosts() {
        use crate::eval::machine_test_hooks as hooks;

        hooks::reset();
        BOUNDED_OUTPUTS.set(0);
        TRANSFORMER_OUTPUT_OBSERVER.set(Some(observe_bounded_output));
        let result = compile_path(RunConfiguration {
            entry: PathBuf::from(env!("CARGO_MANIFEST_DIR"))
                .join("tests/fixtures/surface-macros/derive-bounded/main.ash"),
            roots: ModuleRoots::empty(),
        });
        TRANSFORMER_OUTPUT_OBSERVER.set(None);
        let failure = result.expect_err("recursive derived output must not publish a module");
        let reason = failure.reason_code();
        assert!(
            reason == "internal.resource.structural-depth"
                || reason == "internal.resource.syntax-work",
            "the existing syntax bound must refuse the repeated output: {failure:?}"
        );
        let completed = BOUNDED_OUTPUTS.get();
        let attempts = hooks::TRANSFER_ATTEMPTS.get();
        assert!(completed > 1, "the real checked derive must recur");
        assert_eq!(attempts, completed + hooks::TRANSFER_FAILURES.get());
        assert!(hooks::ROOT_CLOSES.get() >= attempts);
        assert_eq!(hooks::ROOT_CLOSES.get(), hooks::TRANSFORMER_DROPS.get());
        assert_eq!(hooks::ACTIVE_ROOT_DROPS.get(), 0);
        println!(
            "{reason}; {completed} completed outputs, {attempts} transfer attempts, {} root closes, {} transformer drops",
            hooks::ROOT_CLOSES.get(),
            hooks::TRANSFORMER_DROPS.get()
        );
        hooks::reset();
    }

    #[test]
    fn derive_i09_retains_each_original_and_collects_outputs_in_order() {
        use crate::{
            parser::{G1_CAPTURE_OBSERVER, STAGED_MODULE_OBSERVER},
            surface::SurfaceSyntaxCapture,
            syntax::{MacroDelimiter, MacroOutputNode},
        };
        DERIVE_INPUTS.with(|slot| slot.borrow_mut().clear());
        DERIVE_MODULE_ORDER.with(|slot| *slot.borrow_mut() = None);
        G1_CAPTURE_OBSERVER.set(Some(observe_derive_input));
        STAGED_MODULE_OBSERVER.set(Some(observe_derive_module));
        let result = compile_path(RunConfiguration {
            entry: PathBuf::from(env!("CARGO_MANIFEST_DIR"))
                .join("docs/design/macros/fixtures/derives/main.ash"),
            roots: ModuleRoots::empty(),
        });
        G1_CAPTURE_OBSERVER.set(None);
        STAGED_MODULE_OBSERVER.set(None);
        let compiled = result.expect("the fixed derive graph compiles");
        assert_eq!(execute(&compiled).unwrap().value_display(), "42");
        let order = DERIVE_MODULE_ORDER.with(|slot| {
            slot.borrow_mut()
                .take()
                .expect("the staged module was observed")
        });
        assert_eq!(
            order,
            [
                "Color",
                "Marker<Color>",
                "Tagged<Color>",
                "Count",
                "Marker<Count>",
                "Tagged<Count>"
            ]
        );
        let captures = DERIVE_INPUTS.with(|slot| std::mem::take(&mut *slot.borrow_mut()));
        assert_eq!(captures.len(), 4);
        for (index, expected) in ["Color", "Color", "Count", "Count"].into_iter().enumerate() {
            let [
                SurfaceSyntaxCapture::Declaration(subject),
                SurfaceSyntaxCapture::Identifier(target),
            ] = captures[index].as_slice()
            else {
                panic!("derive receives the original subject and its optional name")
            };
            assert_eq!(target.name.text, expected);
            assert_eq!(target.name.introduction, 0);
            assert!(subject.contents.iter().any(|node| matches!(node, MacroOutputNode::Identifier(name, _) if name.text == "deriving" && name.introduction == 0)));
            assert!(subject.contents.iter().any(|node| matches!(node,
                MacroOutputNode::Group(MacroDelimiter::Parentheses, names, _)
                    if names.iter().filter_map(|node| match node { MacroOutputNode::Identifier(name, _) => Some(name.text.as_str()), _ => None }).collect::<Vec<_>>() == ["marker", "tagged"]
            )));
        }
        let subject = |index: usize| match &captures[index][0] {
            SurfaceSyntaxCapture::Declaration(subject) => &subject.contents,
            _ => unreachable!(),
        };
        assert!(Arc::ptr_eq(subject(0), subject(1)));
        assert!(Arc::ptr_eq(subject(2), subject(3)));
        assert!(!Arc::ptr_eq(subject(0), subject(2)));
    }

    fn observe_indexed_transfer(
        selection: &crate::syntax::SelectedSyntax,
        captures: &[crate::surface::SurfaceSyntaxCapture],
        output: &[crate::syntax::MacroOutputNode],
    ) {
        if selection.declaration.name.text == "indexed" {
            INDEXED_TRANSFERRED
                .with(|slot| slot.borrow_mut().push((captures.to_vec(), output.to_vec())));
        }
    }

    #[test]
    fn indexed_i11_traverses_original_constructors_and_transfers_equations_before_teardown() {
        use crate::{
            eval::machine_test_hooks as hooks,
            lexer::TokenKind,
            surface::SurfaceSyntaxCapture,
            syntax::{MacroDelimiter, MacroOutputNode},
        };
        for (entry, expected) in [
            ("one.ash", vec!["Red"]),
            ("main.ash", vec!["Red", "Blue"]),
            ("three.ash", vec!["Red", "Blue", "Green"]),
        ] {
            hooks::reset();
            INDEXED_TRANSFERRED.with(|slot| slot.borrow_mut().clear());
            TRANSFORMER_OUTPUT_OBSERVER.set(Some(observe_indexed_transfer));
            let result = compile_path(RunConfiguration {
                entry: PathBuf::from(env!("CARGO_MANIFEST_DIR"))
                    .join("docs/design/macros/fixtures/indexed")
                    .join(entry),
                roots: ModuleRoots::empty(),
            });
            TRANSFORMER_OUTPUT_OBSERVER.set(None);
            let compiled = result.unwrap_or_else(|failure| panic!("{entry}: {failure:?}"));
            assert_eq!(hooks::DECLARATION_CAPTURES.get(), 1, "{entry}");
            assert_eq!(hooks::DECLARATION_UNWRAPS.get(), 1, "{entry}");
            assert_eq!(hooks::DECLARATION_TRANSFERS_BEFORE_DROP.get(), 1, "{entry}");
            assert_eq!(hooks::ROOT_CLOSES.get(), 1, "{entry}");
            assert_eq!(hooks::TRANSFORMER_DROPS.get(), 1, "{entry}");
            assert_eq!(hooks::ACTIVE_ROOT_DROPS.get(), 0, "{entry}");
            let observed = INDEXED_TRANSFERRED.with(|slot| std::mem::take(&mut *slot.borrow_mut()));
            let [(captures, output)] = observed.as_slice() else {
                panic!("{entry}: one output is transferred")
            };
            let [
                SurfaceSyntaxCapture::Declaration(subject),
                SurfaceSyntaxCapture::Identifier(target),
            ] = captures.as_slice()
            else {
                panic!("{entry}: original subject and name are provided")
            };
            assert_eq!(target.name.text, "Color");
            assert_eq!(target.name.introduction, 0);
            let original_names = subject
                .contents
                .iter()
                .filter_map(|node| match node {
                    MacroOutputNode::Identifier(name, origin) => Some((name, origin)),
                    _ => None,
                })
                .collect::<Vec<_>>();
            assert_eq!(original_names[0].0.text, "Color");
            assert_eq!(original_names[0].1.primary(), target.origin.primary());
            let constructors = &original_names[1..1 + expected.len()];
            assert_eq!(
                constructors
                    .iter()
                    .map(|(name, _)| name.text.as_str())
                    .collect::<Vec<_>>(),
                expected
            );
            assert!(constructors.iter().all(|(name, _)| name.introduction == 0));
            assert!(subject.contents.iter().any(|node| matches!(node, MacroOutputNode::Identifier(name, _) if name.text == "deriving")));
            let body = output
                .iter()
                .find_map(|node| match node {
                    MacroOutputNode::Group(MacroDelimiter::Braces, body, _) => Some(body),
                    _ => None,
                })
                .expect("the transferred implementation body is present");
            let names = body
                .iter()
                .filter_map(|node| match node {
                    MacroOutputNode::Identifier(name, origin) => Some((name, origin)),
                    _ => None,
                })
                .collect::<Vec<_>>();
            assert_eq!(names.len(), expected.len() * 2);
            for (pair, (original, original_origin)) in names.chunks_exact(2).zip(constructors) {
                assert_eq!(pair[0].0.text, "index");
                assert_ne!(pair[0].0.introduction, 0);
                assert_eq!(pair[1].0.text, original.text);
                assert_eq!(pair[1].0.introduction, original.introduction);
                assert_eq!(pair[1].1.primary(), original_origin.primary());
            }
            assert_eq!(
                body.iter()
                    .filter(|node| matches!(node, MacroOutputNode::Token(TokenKind::Equal, _, _)))
                    .count(),
                expected.len()
            );
            assert_eq!(body.iter().filter(|node| matches!(node, MacroOutputNode::Token(TokenKind::Integer(_), spelling, _) if spelling.as_ref() == "1")).count(), expected.len());
            assert_eq!(execute(&compiled).unwrap().value_display(), "42");
            hooks::reset();
        }
    }

    fn observe_import_transfer(
        selection: &crate::syntax::SelectedSyntax,
        captures: &[crate::surface::SurfaceSyntaxCapture],
        output: &[crate::syntax::MacroOutputNode],
    ) {
        if selection.declaration.name.text == "invalid" {
            INDEXED_TRANSFERRED
                .with(|slot| slot.borrow_mut().push((captures.to_vec(), output.to_vec())));
        }
    }

    #[test]
    fn checked_derive_import_transfers_then_is_refused_without_a_module() {
        use crate::{
            eval::machine_test_hooks as hooks, lexer::TokenKind, surface::SurfaceSyntaxCapture,
            syntax::MacroOutputNode,
        };
        hooks::reset();
        INDEXED_TRANSFERRED.with(|slot| slot.borrow_mut().clear());
        TRANSFORMER_OUTPUT_OBSERVER.set(Some(observe_import_transfer));
        let result = compile_path(RunConfiguration {
            entry: PathBuf::from(env!("CARGO_MANIFEST_DIR"))
                .join("tests/fixtures/surface-macros/derive-import/ordered.ash"),
            roots: ModuleRoots::empty(),
        });
        TRANSFORMER_OUTPUT_OBSERVER.set(None);
        let failure = result.expect_err("Import output must not publish a module");
        assert!(failure.is_source_rejection());
        assert!(failure.reason_code().starts_with("parse."));
        let observed = INDEXED_TRANSFERRED.with(|slot| std::mem::take(&mut *slot.borrow_mut()));
        let [(captures, output)] = observed.as_slice() else {
            panic!("the checked transformer returned exactly one output")
        };
        assert!(matches!(
            captures.as_slice(),
            [SurfaceSyntaxCapture::Declaration(_)]
        ));
        assert!(matches!(
            output.first(),
            Some(MacroOutputNode::Token(TokenKind::Import, _, _))
        ));
        assert_eq!(hooks::DECLARATION_TRANSFERS_BEFORE_DROP.get(), 1);
        assert_eq!(hooks::ROOT_CLOSES.get(), 1);
        assert_eq!(hooks::TRANSFORMER_DROPS.get(), 1);
        assert_eq!(hooks::ACTIVE_ROOT_DROPS.get(), 0);
        hooks::reset();
    }

    fn observe_derive_work(
        _source: &SourceFile,
        captures: &[crate::surface::SurfaceSyntaxCapture],
        budget: &crate::syntax_resource::SyntaxBudget,
    ) {
        if matches!(
            captures.first(),
            Some(crate::surface::SurfaceSyntaxCapture::Declaration(_))
        ) {
            DERIVE_WORK.with(|slot| slot.borrow_mut().push(budget.consumed()));
        }
    }

    #[test]
    fn derive_list_work_refusals_leave_owners_unchanged_and_retry() {
        use crate::{
            parser::{
                DeclarationExpansionFailure, G1_CAPTURE_OBSERVER, ProjectionError, ResourceFailure,
            },
            syntax::SyntaxOwner,
            syntax_resource::SyntaxBudget,
        };
        let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("docs/design/macros/fixtures/derives/main.ash");
        let (source, tree, selected) = parse_selected_fixture(&path);
        assert!(tree.parse_diagnostics().is_empty());
        let owner_imports = vec![
            Vec::new();
            selected
                .iter()
                .map(|selection| selection.owner)
                .max()
                .unwrap()
                + 1
        ];
        let span = selected[0].import_span;
        let original = SyntaxOwner {
            owner: None,
            declaration: span,
            import_span: span,
        };
        let mut owners = vec![original];
        let mut full = SyntaxBudget::default();
        DERIVE_WORK.with(|slot| slot.borrow_mut().clear());
        G1_CAPTURE_OBSERVER.set(Some(observe_derive_work));
        let module = crate::parser::project_declaration_expansions(
            &source,
            &tree,
            &selected,
            &owner_imports,
            &mut owners,
            &mut full,
            None,
        )
        .expect("the whole list stages with its full allowance");
        G1_CAPTURE_OBSERVER.set(None);
        assert_eq!(module.type_declarations.len(), 2);
        assert_eq!(module.implementations.len(), 4);
        assert_eq!(owners.len(), 5);
        let reached = DERIVE_WORK.with(|slot| std::mem::take(&mut *slot.borrow_mut()));
        assert_eq!(reached.len(), 4);
        let total = full.consumed();
        assert!(reached[0] < reached[1] && reached[1] < total);
        let mut limits = vec![0, reached[0], reached[1], total - 1];
        limits.sort_unstable();
        limits.dedup();
        for limit in limits {
            let mut owners = vec![original];
            let mut short = SyntaxBudget::with_limit(limit);
            let failure = crate::parser::project_declaration_expansions(
                &source,
                &tree,
                &selected,
                &owner_imports,
                &mut owners,
                &mut short,
                None,
            )
            .expect_err("a short allowance must refuse before publishing");
            assert!(match failure {
                DeclarationExpansionFailure::Syntax {
                    resource: Some(ResourceFailure::SyntaxWork { limit: actual }),
                    ..
                }
                | DeclarationExpansionFailure::Projection(ProjectionError::ResourceLimit(
                    ResourceFailure::SyntaxWork { limit: actual },
                )) => actual == limit,
                _ => false,
            });
            assert_eq!(owners.len(), 1);
            assert_eq!(
                (
                    owners[0].owner,
                    owners[0].declaration,
                    owners[0].import_span
                ),
                (original.owner, original.declaration, original.import_span)
            );
        }
        let mut owners = vec![original];
        let mut exact = SyntaxBudget::with_limit(total);
        let module = crate::parser::project_declaration_expansions(
            &source,
            &tree,
            &selected,
            &owner_imports,
            &mut owners,
            &mut exact,
            None,
        )
        .expect("the same tree and selections succeed at the exact allowance");
        assert_eq!(module.implementations.len(), 4);
        assert_eq!(exact.consumed(), total);
        assert_eq!(owners.len(), 5);
    }

    #[test]
    fn forwarded_source_nominal_siblings_preserve_real_core_origins() {
        let compiled = compile_path(RunConfiguration {
            entry: PathBuf::from(env!("CARGO_MANIFEST_DIR"))
                .join("tests/fixtures/surface-macros/derive-source-forward/main.ash"),
            roots: ModuleRoots::empty(),
        })
        .expect("ordinary source siblings and the forwarded declaration compile together");
        let registry = match &compiled.core {
            CompiledCore::Pure(program) => program.registry(),
            CompiledCore::Effect(program, _) => program.registry(),
        };
        let nominals = registry
            .nominals()
            .iter()
            .filter(|item| ["First", "Second", "Third"].contains(&item.spelling.as_str()))
            .collect::<Vec<_>>();
        assert_eq!(
            nominals
                .iter()
                .map(|item| item.spelling.as_str())
                .collect::<Vec<_>>(),
            ["First", "Second", "Third"]
        );
        assert!(
            nominals
                .iter()
                .all(|item| matches!(item.origin, Origin::Source(_)))
        );
        let constructors = registry
            .constructors()
            .iter()
            .filter(|item| ["First", "Second", "Other", "Third"].contains(&item.spelling.as_str()))
            .collect::<Vec<_>>();
        assert_eq!(
            constructors
                .iter()
                .map(|item| item.spelling.as_str())
                .collect::<Vec<_>>(),
            ["First", "Second", "Other", "Third"]
        );
        assert!(
            constructors
                .iter()
                .all(|item| matches!(item.origin, Origin::Source(_)))
        );
        assert_eq!(
            constructors[1].origin.primary_span(),
            constructors[2].origin.primary_span(),
            "the real forwarded sibling constructors share the full primary Source span"
        );
        assert_eq!(constructors[1].owner, nominals[1].id);
        assert_eq!(constructors[2].owner, nominals[1].id);
        assert_eq!(execute(&compiled).unwrap().value_display(), "42");
    }

    fn observe_s3_transfer(
        selection: &crate::syntax::SelectedSyntax,
        captures: &[crate::surface::SurfaceSyntaxCapture],
        output: &[crate::syntax::MacroOutputNode],
    ) {
        if selection.declaration.name.text != "declaration_output" {
            return;
        }
        TRANSFORMER_OUTPUT_OBSERVER.set(None);
        S3_TRANSFERRED.with(|slot| {
            assert!(slot.borrow().is_none());
            *slot.borrow_mut() = Some((output.to_vec(), captures.to_vec()));
        });
    }

    #[test]
    fn s3_checked_host_output_reaches_declaration_parser_after_teardown() {
        use crate::{
            lexer::TokenKind,
            surface::{SurfaceDefinitionKind, SurfaceSyntaxCapture},
            syntax::{
                ExpansionFrame, MacroDelimiter, MacroOrigin, MacroOutputNode, SyntaxContexts,
            },
        };

        S3_TRANSFERRED.with(|slot| assert!(slot.borrow().is_none()));
        TRANSFORMER_OUTPUT_OBSERVER.set(Some(observe_s3_transfer));
        let result = compile_path(RunConfiguration {
            entry: PathBuf::from(env!("CARGO_MANIFEST_DIR"))
                .join("tests/fixtures/surface-macros/s3-transfer/entry.ash"),
            roots: ModuleRoots::empty(),
        });
        let observed = TRANSFORMER_OUTPUT_OBSERVER.replace(None).is_none();
        let failure = result.expect_err("declaration output cannot be admitted as an expression");
        let Some(PipelineFailure::SyntaxParse(parse)) = failure.pipeline_failure() else {
            panic!("expected expression admission to reject: {failure:?}");
        };
        assert!(observed, "the checked host output observer was not reached");
        assert!(!parse.diagnostics().is_empty());
        assert!(parse.teardown().is_none());
        let (output, captures) = S3_TRANSFERRED.with(|slot| {
            slot.borrow_mut()
                .take()
                .expect("the checked host transferred its output before expression admission")
        });
        let [
            SurfaceSyntaxCapture::Identifier(captured_name),
            SurfaceSyntaxCapture::Expression(captured_value),
        ] = captures.as_slice()
        else {
            panic!("the transformer receives the caller's identifier and expression");
        };
        let [
            MacroOutputNode::Identifier(first_name, first_origin),
            MacroOutputNode::Token(TokenKind::Colon, _, _),
            MacroOutputNode::Token(TokenKind::UnitType, _, _),
            MacroOutputNode::Token(TokenKind::Arrow, _, _),
            MacroOutputNode::Token(TokenKind::IntType, _, _),
            MacroOutputNode::Token(TokenKind::LineEnd, _, _),
            MacroOutputNode::Identifier(second_name, second_origin),
            MacroOutputNode::Group(MacroDelimiter::Parentheses, parameter, _),
            MacroOutputNode::Token(TokenKind::Equal, _, _),
            MacroOutputNode::Group(MacroDelimiter::Parentheses, middle, group_origin),
            MacroOutputNode::Token(TokenKind::Plus, _, _),
            MacroOutputNode::Expression(last_value, _),
        ] = output.as_slice()
        else {
            panic!("the host must return a complete structured declaration");
        };
        assert_eq!(first_name, &captured_name.name);
        assert_eq!(second_name, &captured_name.name);
        assert_eq!(first_origin, &captured_name.origin);
        assert_eq!(second_origin, &captured_name.origin);
        assert!(parameter.is_empty());
        assert_eq!(group_origin, &MacroOrigin::Source(parse.invocation));
        assert_eq!(last_value, captured_value);
        let [
            MacroOutputNode::Expression(middle_value, _),
            MacroOutputNode::Token(TokenKind::Plus, _, _),
            MacroOutputNode::Group(MacroDelimiter::Parentheses, inner, _),
        ] = middle.as_slice()
        else {
            panic!("the outer group's siblings must survive both transfers");
        };
        assert_eq!(middle_value, captured_value);
        let [
            MacroOutputNode::Expression(left_value, _),
            MacroOutputNode::Token(TokenKind::Plus, _, _),
            MacroOutputNode::Expression(right_value, _),
        ] = inner.as_slice()
        else {
            panic!("the nested group's siblings must survive both transfers");
        };
        assert_eq!(left_value, captured_value);
        assert_eq!(right_value, captured_value);

        let source = failure
            .sources()
            .iter()
            .find(|source| source.id() == parse.invocation.source())
            .expect("the actual invocation source is retained");
        let frame = Arc::new(ExpansionFrame {
            invocation: parse.invocation,
            definition: parse.definition,
        });
        let contexts = SyntaxContexts::new(&[], &[], &[]);
        let module = crate::parser::parse_macro_declarations(
            source,
            parse.invocation,
            None,
            output,
            &contexts,
            Some(&frame),
        )
        .expect("the transferred output is a complete declaration");
        let [definition] = module.definitions.as_slice() else {
            panic!("the output contains one declaration");
        };
        let SurfaceDefinitionKind::Equational(global) = &definition.kind else {
            panic!("the output is an equational global");
        };
        assert_eq!(global.interface.name, captured_name.name);
        assert_eq!(global.equations[0].name, captured_name.name);
        let diagnostic = global
            .interface
            .name
            .diagnostic
            .as_ref()
            .expect("the caller name retains its origin");
        assert_eq!(diagnostic.primary, captured_name.origin);
        assert!(
            diagnostic
                .frames
                .iter()
                .any(|item| Arc::ptr_eq(item, &frame))
        );
    }

    #[test]
    fn ash_identity_transformer_round_trips_mixed_capture() {
        use crate::{
            lexer::TokenKind,
            surface::SurfaceSyntaxCapture,
            syntax::{MacroDelimiter, MacroOrigin, MacroOutputNode, SelectedSyntax},
        };

        fn inspect(
            selection: &SelectedSyntax,
            captures: &[SurfaceSyntaxCapture],
            output: &[MacroOutputNode],
        ) {
            if selection.declaration.name.text != "identity" {
                return;
            }
            TRANSFORMER_OUTPUT_OBSERVER.set(None);
            let [SurfaceSyntaxCapture::Expression(original)] = captures else {
                panic!("identity receives one expression capture")
            };
            assert_eq!(output, original.contents.as_ref());
            let [
                MacroOutputNode::Group(
                    MacroDelimiter::Parentheses,
                    children,
                    MacroOrigin::Combined { inputs, frame, .. },
                ),
            ] = original.contents.as_ref()
            else {
                panic!("identity receives a group with a combined origin")
            };
            let [
                MacroOutputNode::Group(
                    _,
                    returned_children,
                    MacroOrigin::Combined {
                        inputs: returned_inputs,
                        frame: returned_frame,
                        ..
                    },
                ),
            ] = output
            else {
                panic!("identity returns the group and combined origin")
            };
            assert!(Arc::ptr_eq(frame, returned_frame));
            assert!(Arc::ptr_eq(inputs, returned_inputs));
            assert_eq!(
                inputs.as_ref(),
                [
                    MacroOrigin::Source(frame.invocation),
                    MacroOrigin::Source(frame.definition),
                ]
            );
            let [
                MacroOutputNode::Identifier(introduced, _),
                MacroOutputNode::Token(TokenKind::Integer(_), one, _),
                MacroOutputNode::Token(TokenKind::Plus, plus, _),
                MacroOutputNode::Expression(captured, _),
            ] = children.as_slice()
            else {
                panic!("the mixed group has the expected token and fragment order")
            };
            assert_eq!(one.as_ref(), "1");
            assert_eq!(plus.as_ref(), "+");
            let [MacroOutputNode::Identifier(caller, _)] = captured.contents.as_ref() else {
                panic!("the protected caller fragment retains its identifier")
            };
            assert_eq!(introduced.text, "same");
            assert_eq!(caller.text, "same");
            assert_ne!(introduced.introduction, caller.introduction);
            assert!(!introduced.written && caller.written);
            let MacroOutputNode::Expression(returned_capture, _) = &returned_children[3] else {
                panic!("the returned caller fragment stays protected")
            };
            assert!(Arc::ptr_eq(&captured.contents, &returned_capture.contents));
        }

        TRANSFORMER_OUTPUT_OBSERVER.set(Some(inspect));
        let configuration = RunConfiguration {
            entry: PathBuf::from(env!("CARGO_MANIFEST_DIR"))
                .join("tests/fixtures/surface-macros/identity-roundtrip/entry.ash"),
            roots: ModuleRoots::empty(),
        };
        let compiled = compile_path(configuration).expect("the identity graph compiles");
        assert!(TRANSFORMER_OUTPUT_OBSERVER.get().is_none());
        assert_eq!(execute(&compiled).unwrap().value_display(), "42");

        fn inspect_quote(
            selection: &SelectedSyntax,
            captures: &[SurfaceSyntaxCapture],
            output: &[MacroOutputNode],
        ) {
            if selection.declaration.name.text != "identity" {
                return;
            }
            TRANSFORMER_OUTPUT_OBSERVER.set(None);
            let [SurfaceSyntaxCapture::Expression(original)] = captures else {
                panic!("identity receives the protected quote expression")
            };
            let crate::surface::CapturedQuoteSites::Owned(sites) = &original.quote_sites else {
                panic!("the original capture owns its unissued quote sites")
            };
            let crate::surface::SurfaceExprKind::Apply(application) = &original.expression.kind
            else {
                panic!("the captured quote owns its lowered call")
            };
            let callee = std::ptr::from_ref(application.function.as_ref()) as usize;
            assert!(sites.iter().any(|site| site.callee == callee));
            assert_eq!(output, original.contents.as_ref());

            let mut pending = original.contents.iter().collect::<Vec<_>>();
            let mut syntax_tokens = 0;
            let mut dollars = 0;
            let mut groups = 0;
            let mut fragment = false;
            while let Some(node) = pending.pop() {
                match node {
                    MacroOutputNode::Group(_, children, _) => {
                        groups += 1;
                        pending.extend(children);
                    }
                    MacroOutputNode::Token(TokenKind::SyntaxKeyword, spelling, _) => {
                        assert_eq!(spelling.as_ref(), "syntax");
                        syntax_tokens += 1;
                    }
                    MacroOutputNode::Token(TokenKind::Dollar, spelling, _) => {
                        assert_eq!(spelling.as_ref(), "$");
                        dollars += 1;
                    }
                    MacroOutputNode::Identifier(name, MacroOrigin::Source(span))
                        if name.text == "fragment" =>
                    {
                        assert_eq!(name.introduction, 0);
                        assert!(name.written);
                        assert_eq!(span.source(), original.expression.span.source());
                        fragment = true;
                    }
                    _ => {}
                }
            }
            assert!(
                groups >= 3 && syntax_tokens >= 2 && dollars >= 2 && fragment,
                "the protected quote retains its nested groups, tokens, and identifier: {:?}",
                original.contents
            );
        }

        TRANSFORMER_OUTPUT_OBSERVER.set(Some(inspect_quote));
        let configuration = RunConfiguration {
            entry: PathBuf::from(env!("CARGO_MANIFEST_DIR"))
                .join("docs/design/macros/fixtures/escapes/quote_roundtrip.ash"),
            roots: ModuleRoots::empty(),
        };
        let compiled = compile_path(configuration).expect("the fixed quote roundtrip compiles");
        assert!(TRANSFORMER_OUTPUT_OBSERVER.get().is_none());
        assert_eq!(execute(&compiled).unwrap().value_display(), "42");
    }

    #[test]
    fn unused_transformer_rejects_polymorphic_and_constrained_targets() {
        let declarations = [
            r#"wrong<E : EffectRow> : Syntax.Input -> Syntax.MacroResult ! {Syntax.Ops | E}
wrong input = {
    let origin = Syntax.invocation_origin(input)
    Syntax.Rejected(Syntax.MacroDiagnostic("unused", origin, Syntax.NoOrigins))
}
"#,
            r#"interface Marker<A> {
    mark : A -> Int
}
wrong : Syntax.Input -> Syntax.MacroResult ! {Syntax.Ops} where Marker<Int>
wrong input = {
    let origin = Syntax.invocation_origin(input)
    Syntax.Rejected(Syntax.MacroDiagnostic("unused", origin, Syntax.NoOrigins))
}
"#,
        ];
        for declaration in declarations {
            let ordinary = format!(
                "import @builtin.compiler.syntax as Syntax\n\n{declaration}\nmain : Unit -> Int\nmain () = 42\n"
            );
            let fixture = TestSource::write(&ordinary);
            let compiled = compile_path(fixture.configuration())
                .expect("the same ordinary declaration checks without a syntax target");
            assert_eq!(execute(&compiled).unwrap().value_display(), "42");

            let syntax = ordinary.replace(
                "import @builtin.compiler.syntax as Syntax\n",
                "import @builtin.compiler.syntax as Syntax\npub syntax invalid $value:expr => using wrong\n",
            );
            fs::write(&fixture.0, syntax).unwrap();
            let failure = compile_path(fixture.configuration())
                .expect_err("an unused invalid transformer is refused at admission");
            assert_eq!(failure.reason_code(), "syntax.invalid-transformer");
        }
    }

    #[test]
    fn independently_issued_same_spelled_term_names_keep_their_bindings() {
        let fixture = |name: &str| RunConfiguration {
            entry: PathBuf::from(env!("CARGO_MANIFEST_DIR"))
                .join("tests/fixtures/surface-macros/fresh-term")
                .join(name),
            roots: ModuleRoots::empty(),
        };
        let compiled = compile_path(fixture("distinct.ash")).expect("fresh names compile");
        let (program, provenance) = compiled.effect_build_input().unwrap();
        let source = provenance
            .iter()
            .find(|(_, source)| source.display_path().ends_with("fresh-term/distinct.ash"))
            .unwrap()
            .1
            .id();
        let fixture_source =
            include_str!("../tests/fixtures/surface-macros/fresh-term/distinct.ash");
        let offset = |name| u32::try_from(fixture_source.find(name).unwrap()).unwrap();
        let caller = program
            .nodes()
            .iter()
            .find_map(|node| match &node.kind {
                crate::core::EffectExprKind::Pure(crate::core::PureExprKind::Computation(
                    crate::core::PureComputation::Bind(binding),
                )) if binding.binder().origin().primary_span().source() == source
                    && binding.binder().origin().primary_span().range().start()
                        == offset("temp = 39") =>
                {
                    Some(binding.binder().id())
                }
                _ => None,
            })
            .expect("the caller's temp binding remains in checked Core");
        let bindings = program
            .nodes()
            .iter()
            .filter_map(|node| match &node.kind {
                crate::core::EffectExprKind::Pure(crate::core::PureExprKind::Computation(
                    crate::core::PureComputation::Bind(binding),
                )) if binding.binder().id().module().is_some()
                    && binding.binder().origin().primary_span().source() == source
                    && binding.binder().origin().primary_span().range().start()
                        == offset("fresh_pair (temp") =>
                {
                    Some(binding)
                }
                _ => None,
            })
            .collect::<Vec<_>>();
        let [first, second] = bindings.as_slice() else {
            panic!("the two fresh term binders remain in checked Core")
        };
        assert_ne!(first.binder().id(), second.binder().id());
        let uses_caller = |root| {
            let mut pending = vec![root];
            let mut seen = std::collections::HashSet::new();
            while let Some(id) = pending.pop() {
                if !seen.insert(id) {
                    continue;
                }
                let node = program.node(id).unwrap();
                if matches!(&node.kind,
                    crate::core::EffectExprKind::Pure(crate::core::PureExprKind::Variable(variable))
                        if variable.binder() == caller)
                {
                    return true;
                }
                pending.extend(
                    (0..node.kind.child_count()).filter_map(|index| node.kind.child_at(index)),
                );
            }
            false
        };
        let (left, right) = match (
            uses_caller(first.initializer()),
            uses_caller(second.initializer()),
        ) {
            (true, false) => (first.binder().id(), second.binder().id()),
            (false, true) => (second.binder().id(), first.binder().id()),
            _ => panic!("only the first initializer uses the caller's temp"),
        };
        let variable = |node| match &program.node(node)?.kind {
            crate::core::EffectExprKind::Pure(crate::core::PureExprKind::Variable(variable)) => {
                Some(variable.binder())
            }
            _ => None,
        };
        assert!(program.nodes().iter().any(|node| matches!(
            &node.kind,
            crate::core::EffectExprKind::Operation(crate::core::EffectOperation::RegionBuffer(buffer))
                if matches!(buffer.operation,
                    crate::core::region::RegionBufferOperation::IntegerArithmetic(crate::core::Primitive::Add))
                    && buffer.operand.and_then(variable) == Some(left)
                    && buffer.right.and_then(variable) == Some(right)
        )), "the final addition uses each fresh binder in order");
        assert_eq!(execute(&compiled).unwrap().value_display(), "42");
        let reused = compile_path(fixture("reused.ash")).expect("reused name compiles");
        assert_eq!(execute(&reused).unwrap().value_display(), "4");
    }

    #[test]
    fn unchanged_transformer_entry_is_reused_only_within_one_compilation() {
        let fixture = TestSource::write(
            "import macros (syntax twice)\n\
             import support (value)\n\
             main : Unit -> Int\n\
             main () = value(()) + (twice 11)\n",
        );
        fixture.write_sibling(
            "support.ash",
            "import macros (syntax twice)\n\
             pub value : Unit -> Int\n\
             value () = twice 10\n",
        );
        fixture.write_sibling(
            "other_dsl.ash",
            include_str!("../tests/fixtures/surface-macros/other_dsl.ash"),
        );
        let macros = include_str!("../tests/fixtures/surface-macros/macros.ash").replace(
            "Syntax.make_token(Syntax.Plus, \"+\")",
            "Syntax.make_token(Syntax.Plus, Helpers.operator_spelling(()))",
        );
        fixture.write_sibling("macros.ash", &macros);
        let helpers = format!(
            "{}\npub operator_spelling : Unit -> String\noperator_spelling () = \"+\"\n",
            include_str!("../tests/fixtures/surface-macros/helpers.ash")
        );
        fixture.write_sibling("helpers.ash", &helpers);

        TRANSFORMER_ENTRY_PREPARATIONS.set(0);
        TRANSFORMER_ENTRY_VALIDATIONS.set(0);
        let compiled = compile_path(fixture.configuration()).expect("both invocations compile");
        assert_eq!(execute(&compiled).unwrap().value_display(), "42");
        assert_eq!(TRANSFORMER_ENTRY_PREPARATIONS.get(), 1);
        assert_eq!(TRANSFORMER_ENTRY_VALIDATIONS.get(), 1);

        fixture.write_sibling(
            "helpers.ash",
            &helpers.replace(
                "operator_spelling () = \"+\"",
                "operator_spelling () = \"-\"",
            ),
        );
        let failure =
            compile_path(fixture.configuration()).expect_err("the changed helper rejects");
        assert_eq!(failure.reason_code(), "syntax.rejected");
        assert_eq!(TRANSFORMER_ENTRY_PREPARATIONS.get(), 2);
        assert_eq!(TRANSFORMER_ENTRY_VALIDATIONS.get(), 2);
    }

    #[test]
    fn changed_macro_inputs_are_checked_in_each_compilation() {
        let entry =
            include_str!("../tests/fixtures/surface-macros/copied-declarations/combined.ash")
                .replace("duplicate ({", "duplicate 0 when ({");
        let forms = format!(
            "import nested (syntax bump)\n{}",
            include_str!("../tests/fixtures/surface-macros/copied-declarations/forms.ash")
                .replace(
                    "pub syntax duplicate $value:expr =>",
                    "pub syntax duplicate $ignored:expr when $value:expr =>",
                )
                .replace("    $value + 1\n", "    bump $value\n")
        );
        let nested = "import helpers (increment)\npub syntax bump $value:expr => {\n    increment $value\n}\n";
        let helpers = "pub increment : Int -> Int\nincrement value = value + 1\n";
        let alternate = "pub syntax bump $value:expr => {\n    $value + 2\n}\n";
        let fixture = TestSource::write(&entry);
        fixture.write_sibling("forms.ash", &forms);
        fixture.write_sibling("nested.ash", nested);
        fixture.write_sibling("alternate.ash", alternate);
        fixture.write_sibling("helpers.ash", helpers);
        let run = || {
            let compiled = compile_path(fixture.configuration()).expect("graph compiles");
            execute(&compiled).unwrap().value_display()
        };
        assert_eq!(run(), "42");

        fs::write(&fixture.0, entry.replace("outside = 20", "outside = 21")).unwrap();
        assert_eq!(run(), "44");
        fs::write(&fixture.0, &entry).unwrap();

        fixture.write_sibling("forms.ash", &forms.replace("when $value", "through $value"));
        let failure = compile_path(fixture.configuration()).expect_err("changed matcher rejects");
        assert_eq!(failure.reason_code(), "parse.expected-form");
        fs::write(
            &fixture.0,
            entry.replace("duplicate 0 when", "duplicate 0 through"),
        )
        .unwrap();
        assert_eq!(run(), "42");
        fs::write(&fixture.0, &entry).unwrap();
        fixture.write_sibling("forms.ash", &forms);

        fixture.write_sibling("helpers.ash", &helpers.replace("value + 1", "value + 2"));
        assert_eq!(run(), "44");
        fixture.write_sibling("helpers.ash", helpers);

        fixture.write_sibling(
            "forms.ash",
            &forms.replace("import nested", "import alternate"),
        );
        assert_eq!(run(), "44");
        fixture.write_sibling("forms.ash", &forms);

        let method_forms =
            include_str!("../tests/fixtures/surface-macros/template-method/forms.ash");
        let method_entry =
            include_str!("../tests/fixtures/surface-macros/template-method/entry.ash")
                .replace("import forms (", "import method_forms (");
        fixture.write_sibling("method_forms.ash", method_forms);
        fs::write(&fixture.0, method_entry).unwrap();
        assert_eq!(run(), "42");
        fixture.write_sibling(
            "method_forms.ash",
            &method_forms.replace("read : A -> Int", "read : A -> Bool"),
        );
        let failure = compile_path(fixture.configuration()).expect_err("changed interface rejects");
        assert_eq!(failure.reason_code(), "type.definition-result");
    }

    #[test]
    fn empty_row_file_entry_uses_the_effect_profile() {
        let fixture = TestSource::write("main : Unit -> Int ! {}\nmain () = 42\n");
        let compiled = compile_path(fixture.configuration()).expect("the file graph compiles");
        assert!(compiled.effect_build_input().is_some());
        assert_eq!(
            execute(&compiled)
                .expect("the entry executes")
                .value_display(),
            "42"
        );
    }

    #[test]
    fn shared_verified_module_bodies_are_checked_once_before_execution() {
        use crate::core::capture::InitializerRootObservation;
        use crate::elaborate::{ModuleBodyObservation, ObservedModuleBody};
        use crate::resolved::ModuleSummaryObservation;
        use std::collections::{HashMap, HashSet};

        let fixture = TestSource::write(concat!(
            "import left (Some, Observe, observe, impl Observe)\n",
            "import right (relay)\n",
            "main : Unit -> Int\n",
            "main () = observe(relay(Some(1)))\n",
        ));
        fixture.write_sibling(
            "base.ash",
            concat!(
                "import @builtin.cell as Cell\n",
                "pub type Option<A> =\n    None\n    | Some(A)\n",
                "pub interface Observe<F : Type -> Type> {\n    observe : F<Int> -> Int\n}\n",
                "pub impl Observe<Option> {\n",
                "    observe (Some(value)) = resource cell<R> c = value {\n",
                "        41 + Cell.read c\n    }\n    observe None = 0\n}\n",
                "pub relay<F : Type -> Type> : F<Int> -> F<Int>\n",
                "relay value = value\n",
            ),
        );
        fixture.write_sibling(
            "left.ash",
            "pub import base (Some, Observe, observe, impl Observe)\n",
        );
        fixture.write_sibling("right.ash", "pub import base (relay)\n");

        let observer = ModuleBodyObservation::start();
        let summary_observer = ModuleSummaryObservation::start();
        let initializer_observer = InitializerRootObservation::start();
        let compiled = compile_path_with_consumers_internal(
            fixture.configuration(),
            &mut InterfaceConstraintBudget::default(),
            |program, constraint_work, type_work| {
                let group = |spelling: &str| {
                    program
                        .groups()
                        .iter()
                        .find(|group| {
                            group
                                .schemes()
                                .iter()
                                .any(|scheme| scheme.spelling == spelling)
                        })
                        .expect("the authored module is linked")
                };
                let base = group("relay");
                let entry = group("main");
                for group in [base, entry] {
                    assert!(
                        group
                            .typed_fragment()
                            .expect("the checked module retains its fragment")
                            .has_completed_physical_bindings(),
                        "the module's physical graph must be complete before linking"
                    );
                }
                assert!(
                    base.local_lowering()
                        .expect("the base retains its lowered metadata")
                        .catalog()
                        .expect("the base retains its evidence catalog")
                        .method_count()
                        > 0
                );
                validate_interface_evidence_with_budget(program, constraint_work, type_work)
            },
            validate_modular_effect_core,
            true,
            ProvenanceRetention::Retain,
        )
        .expect("the linked graph compiles");
        let observed = observer.finish();
        let summaries = summary_observer.finish();
        let initializers = initializer_observer.finish();
        let authored_sources: HashSet<_> = compiled
            .provenance
            .iter()
            .filter_map(|(_, source)| {
                let name = std::path::Path::new(source.display_path()).file_name()?;
                (name == "base.ash" || name == "entry.ash").then_some(source.id())
            })
            .collect();
        assert_eq!(authored_sources.len(), 2);
        let base_source = compiled
            .provenance
            .iter()
            .find(|(_, source)| {
                std::path::Path::new(source.display_path())
                    .file_name()
                    .is_some_and(|name| name == "base.ash")
            })
            .expect("the shared provider source is retained")
            .1
            .id();
        let mut initializer_counts = HashMap::new();
        for span in initializers {
            if span.source() == base_source {
                *initializer_counts.entry(span).or_insert(0usize) += 1;
            }
        }
        assert!(
            !initializer_counts.is_empty(),
            "the provider initializer reaches the safety checker"
        );
        assert!(
            initializer_counts.values().all(|&count| count == 1),
            "the provider's initializers must be checked once: {initializer_counts:?}"
        );
        for (module, source) in &compiled.provenance {
            if authored_sources.contains(&source.id()) {
                assert_eq!(
                    summaries
                        .iter()
                        .filter(|candidate| *candidate == module)
                        .count(),
                    1,
                    "a verified module summary must be checked once, not once per importer"
                );
            }
        }
        let result = execute(&compiled).expect("the linked graph executes");
        assert_eq!(result.value_display(), "42");
        let mut counts = HashMap::new();
        for (span, kind, final_synthesis) in observed {
            if !authored_sources.contains(&span.source()) {
                continue;
            }
            let count = counts.entry((span, kind)).or_insert((0, 0));
            if final_synthesis {
                count.1 += 1;
            } else {
                count.0 += 1;
            }
        }
        assert_eq!(counts.len(), 3);
        assert!(
            counts
                .keys()
                .any(|(_, kind)| *kind == ObservedModuleBody::Method)
        );
        assert!(
            counts.values().all(|&count| count == (1, 0)),
            "every module body must be checked once and reused: {counts:?}"
        );
    }

    #[test]
    fn imported_checked_constrained_global_uses_selected_evidence() {
        let fixture = TestSource::write(concat!(
            "import base (apply, Observe, impl Observe)\n",
            "main : Unit -> Int\n",
            "main () = apply(1)\n",
        ));
        fixture.write_sibling(
            "base.ash",
            concat!(
                "pub interface Observe<A> {\n    observe : A -> Int\n}\n",
                "pub impl Observe<Int> {\n    observe value = 41 + value\n}\n",
                "pub apply<A> : A -> Int where Observe<A>\n",
                "apply value = observe value\n",
            ),
        );
        let compiled = compile_path(fixture.configuration())
            .expect("the imported checked global and selected evidence compile");
        let result = execute(&compiled).expect("the imported checked global executes");
        assert_eq!(result.value_display(), "42");
    }

    #[test]
    fn imported_recursive_generic_implementation_preserves_evidence() {
        let fixture = TestSource::write(concat!(
            "import base (Nil, Cons, measure, impl Measure)\n",
            "main : Unit -> Int\n",
            "main () = measure(Cons(40, Cons(2, Nil)))\n",
        ));
        fixture.write_sibling(
            "base.ash",
            concat!(
                "pub type List<A> =\n    Nil\n    | Cons(A, List<A>)\n",
                "pub interface Measure<A> {\n    measure : A -> Int\n}\n",
                "pub impl Measure<Int> {\n    measure value = value\n}\n",
                "pub impl<A> Measure<List<A>> where Measure<A> {\n",
                "    measure Nil = 0\n",
                "    measure (Cons(value, rest)) = measure(value) + measure(rest)\n",
                "}\n",
            ),
        );
        let compiled = compile_path(fixture.configuration())
            .expect("the imported recursive generic implementation compiles");
        let result = execute(&compiled).expect("the recursive implementation executes");
        assert_eq!(result.value_display(), "42");
    }

    #[test]
    fn imported_generic_abis_preserve_colliding_module_local_identities() {
        use crate::elaborate::FragmentTypeObservation;

        let fixture = TestSource::write(concat!(
            "import base (measure, impl Measure)\n",
            "import left (Left, impl Measure)\n",
            "import right (Right, impl Measure)\n",
            "main : Unit -> Int\n",
            "main () = measure(Left(40)) + measure(Right(2))\n",
        ));
        fixture.write_sibling(
            "base.ash",
            concat!(
                "pub interface Measure<A> {\n    measure : A -> Int\n}\n",
                "pub impl Measure<Int> {\n    measure value = value\n}\n",
            ),
        );
        fixture.write_sibling(
            "left.ash",
            concat!(
                "pub import base (Measure, measure, impl Measure)\n",
                "pub type Left<A> = Left(A)\n",
                "pub impl<A> Measure<Left<A>> where Measure<A> {\n",
                "    measure (Left(value)) = measure(value)\n}\n",
                "pub left_marker : Unit -> Int\nleft_marker () = 0\n",
            ),
        );
        fixture.write_sibling(
            "right.ash",
            concat!(
                "pub import base (Measure, measure, impl Measure)\n",
                "pub type Right<A> = Right(A)\n",
                "pub impl<A> Measure<Right<A>> where Measure<A> {\n",
                "    measure (Right(value)) = measure(value)\n}\n",
                "pub right_marker : Unit -> Int\nright_marker () = 0\n",
            ),
        );
        let observer = FragmentTypeObservation::start();
        let mut expected = None;
        let compiled = compile_path_with_consumers_internal(
            fixture.configuration(),
            &mut InterfaceConstraintBudget::default(),
            |program, constraint_work, type_work| {
                let group = |spelling: &str| {
                    program
                        .groups()
                        .iter()
                        .find(|group| {
                            group
                                .schemes()
                                .iter()
                                .any(|scheme| scheme.spelling == spelling)
                        })
                        .expect("the authored module is linked")
                };
                let left = group("left_marker");
                let right = group("right_marker");
                let entry = group("main");
                let left_ids: std::collections::HashSet<_> = left
                    .local_lowering()
                    .expect("left retains its physical schemes")
                    .owned_abi_variables()
                    .collect();
                let collision = right
                    .local_lowering()
                    .expect("right retains its physical schemes")
                    .owned_abi_variables()
                    .find(|id| left_ids.contains(id))
                    .expect("the independently generated ABI identities collide locally");
                let entry_fragment = entry
                    .typed_fragment()
                    .expect("entry retains its checked fragment");
                assert!(entry_fragment.owns_generated_variable(collision));
                let aliases: Vec<_> = entry_fragment
                    .imported_type_aliases()
                    .filter(|(_, module, id)| {
                        *id == collision && (*module == left.module() || *module == right.module())
                    })
                    .collect();
                assert_eq!(aliases.len(), 2);
                assert_ne!(aliases[0].0, aliases[1].0);
                let left_alias = aliases
                    .iter()
                    .find(|(_, module, _)| *module == left.module())
                    .expect("left's alias exists")
                    .0;
                let right_alias = aliases
                    .iter()
                    .find(|(_, module, _)| *module == right.module())
                    .expect("right's alias exists")
                    .0;
                expected = Some((
                    entry.module(),
                    left.module(),
                    right.module(),
                    collision,
                    left_alias,
                    right_alias,
                ));
                validate_interface_evidence_with_budget(program, constraint_work, type_work)
            },
            validate_modular_effect_core,
            true,
            ProvenanceRetention::Retain,
        )
        .expect("the independently generated imported ABIs compile");
        let entries = observer.finish();
        let (entry, left, right, source, left_alias, right_alias) =
            expected.expect("the linked groups were observed");
        let destination = |module, identity| {
            entries
                .iter()
                .find_map(|(candidate, source, destination)| {
                    (*candidate == module && *source == identity).then_some(*destination)
                })
                .expect("the final identity was mapped")
        };
        let left_destination = destination(left, source);
        let right_destination = destination(right, source);
        assert_eq!(destination(entry, left_alias), left_destination);
        assert_eq!(destination(entry, right_alias), right_destination);
        assert_ne!(left_destination, right_destination);
        let entry_destination = destination(entry, source);
        assert_ne!(entry_destination, left_destination);
        assert_ne!(entry_destination, right_destination);
        let result = execute(&compiled).expect("both selected implementations execute");
        assert_eq!(result.value_display(), "42");
    }

    #[test]
    fn importer_rejects_argument_incompatible_with_verified_method() {
        let fixture = TestSource::write(concat!(
            "import base (Some, Observe, observe, impl Observe)\n",
            "main : Unit -> Int\n",
            "main () = observe(Some(true))\n",
        ));
        fixture.write_sibling(
            "base.ash",
            concat!(
                "pub type Option<A> =\n    None\n    | Some(A)\n",
                "pub interface Observe<F : Type -> Type> {\n    observe : F<Int> -> Int\n}\n",
                "pub impl Observe<Option> {\n",
                "    observe (Some(value)) = 41 + value\n    observe None = 0\n}\n",
            ),
        );

        let failure = compile_path(fixture.configuration()).expect_err("the argument is Bool");
        assert!(matches!(
            failure.pipeline_failure(),
            Some(PipelineFailure::Typing(TypeError::Source(_)))
        ));
        assert_eq!(failure.reason_code(), "type.argument");
    }

    #[test]
    fn linked_native_binding_and_network_cleanup_share_one_program() {
        use crate::foreign::source_runtime::{
            NativeArgument, NativeCallError, NativeReply, SourceNativeBindings,
        };
        use std::sync::atomic::AtomicUsize;

        static CALLS: AtomicUsize = AtomicUsize::new(0);
        fn echo_bytes(arguments: &[NativeArgument]) -> Result<NativeReply, NativeCallError> {
            let [NativeArgument(address)] = arguments else {
                return Err(NativeCallError);
            };
            if address.is_null() {
                return Err(NativeCallError);
            }
            CALLS.fetch_add(1, Ordering::SeqCst);
            Ok(NativeReply::Address(*address))
        }

        let fixture = TestSource::write(include_str!(
            "../tests/fixtures/source-native/cases/network-binding.ash"
        ));
        for (name, source) in [
            (
                "native.ash",
                include_str!("../tests/fixtures/source-native/native.ash"),
            ),
            (
                "binding.ash",
                include_str!("../tests/fixtures/source-native/binding.ash"),
            ),
            (
                "network_types.ash",
                include_str!("../libraries/network_types.ash"),
            ),
            (
                "network_codec.ash",
                include_str!("../libraries/network_codec.ash"),
            ),
            (
                "network_protocol.ash",
                include_str!("../libraries/network_protocol.ash"),
            ),
        ] {
            fixture.write_sibling(name, source);
        }
        let compiled = compile_path(fixture.configuration()).expect("combined source compiles");
        let directory = fixture.0.parent().expect("the fixture has a directory");
        for name in [
            "entry.ash",
            "native.ash",
            "binding.ash",
            "network_types.ash",
            "network_codec.ash",
            "network_protocol.ash",
        ] {
            fs::remove_file(directory.join(name)).expect("compiled source should be removable");
        }
        let (_, boundary) = compiled
            .source_native_entry()
            .expect("native entry is present");
        let mut bindings = SourceNativeBindings::default();
        let symbol = boundary
            .interpretations()
            .iter()
            .map(|interpretation| interpretation.symbol())
            .find(|symbol| symbol.symbol().name() == "EchoBytes")
            .expect("the checked boundary retains EchoBytes");
        bindings
            .insert(
                Arc::clone(symbol),
                echo_bytes,
                &mut TypeWorkBudget::default(),
            )
            .expect("checked symbol binds the trusted callback");
        CALLS.store(0, Ordering::SeqCst);
        let result = execute_with_source_native_bindings(&compiled, &mut bindings)
            .expect("combined program executes and settles");
        assert_eq!(result.value_display(), "42");
        assert_eq!(CALLS.load(Ordering::SeqCst), 1);
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
            validate_effect_modules,
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
        assert_eq!(
            graph
                .modules()
                .iter()
                .filter(|module| module.source().display_path() == "@builtin.bytes")
                .count(),
            1
        );
        let bytes: usize = graph
            .modules()
            .iter()
            .map(|module| module.source().text().len())
            .sum();
        let (work, counted_bytes) = crate::compiler_work::source_work(&graph).unwrap();
        assert_eq!(counted_bytes, bytes);
        assert_eq!(
            (work.used(), work.limit()),
            (graph.modules().len() + 1, 10000 * bytes)
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
            (
                crate::compiler_work::CompilationPhase::IndependentCore,
                25000,
            ),
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
        let mut graph = load_module_graph(&source.0, &ModuleRoots::empty())
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
        let mut compile = |retention| {
            compile_graph_with_consumers(
                &mut graph,
                &mut InterfaceConstraintBudget::default(),
                validate_interface_evidence_with_budget,
                validate_modular_effect_core,
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
                    let failure = execute_with_consumer(&compiled, |_| {
                        evaluated.set(true);
                        Err(RuntimeFailure::InvalidControlState)
                    })
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
        let entry = sources
            .iter()
            .find(|source| source.id() == diagnostic.primary.span().source())
            .unwrap();
        assert_eq!(entry.text(), text);
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
            |unchecked, sources, modules| {
                let entry = sources
                    .iter()
                    .find(|input| input.display_path() == source.0.to_str().unwrap())
                    .expect("actual entry source")
                    .id();
                let retained_sources = sources
                    .iter()
                    .copied()
                    .filter(|input| input.id() != entry)
                    .collect::<Vec<_>>();
                let retained_modules = modules
                    .iter()
                    .copied()
                    .filter(|(_, source)| *source != entry)
                    .collect::<Vec<_>>();
                validate_effect_modules(unchecked, &retained_sources, &retained_modules)
            },
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
            |unchecked, sources, _, linked| {
                validate_modular_effect_core(unchecked, sources, &[], linked)
            },
            |_| panic!("evaluation must not run after independent Core rejection"),
            true,
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
        let program = |width| {
            let origin = Origin::Source(source.span(ByteRange::new(0, 2).unwrap()).unwrap());
            let mut builder = crate::core::CoreBuilder::new();
            let leaf = builder.unit(Type::Unit, origin.clone()).unwrap();
            let root = builder
                .tuple(
                    vec![leaf; width],
                    Type::Tuple(vec![Type::Unit; width].into_boxed_slice()),
                    origin,
                )
                .unwrap();
            builder.finish(root).unwrap()
        };
        for prefix in [0, 11] {
            for _ in 0..2 {
                // The original 512-element, two-node metadata control fits the
                // current policy. It does not receive an extra source-size credit.
                let (mut control, _) = crate::compiler_work::resident_phase_work(
                    crate::compiler_work::CompilationPhase::IndependentCore,
                    &[&source],
                )
                .unwrap();
                control.charge(prefix).unwrap();
                crate::core::validate::validate_modules_with_work(
                    program(512),
                    &[&source],
                    &modules,
                    &mut control,
                )
                .expect("original metadata control fits current Core policy");
                assert!(control.used() >= 2 + prefix && control.used() <= control.limit());

                let (mut work, counted_bytes) = crate::compiler_work::resident_phase_work(
                    crate::compiler_work::CompilationPhase::IndependentCore,
                    &[&source],
                )
                .unwrap();
                assert_eq!(counted_bytes, source.text().len());
                assert_eq!((work.used(), work.limit()), (2, 2 * 25000));
                work.charge(prefix).unwrap();
                // Still only two Core nodes; resident payload metadata alone
                // exceeds the independently paid allowance.
                let width = work.limit().checked_add(1).unwrap();
                let failure = crate::core::validate::validate_modules_with_work(
                    program(width),
                    &[&source],
                    &modules,
                    &mut work,
                )
                .unwrap_err();
                assert_eq!(failure.reason(), crate::core::ValidationReason::Resource);
                assert_eq!(work.limit(), 2 * 25000);
                assert!(work.used() >= 2 + prefix && work.used() <= work.limit());
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
                let module = linked.entry();
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
    fn independent_core_validation_releases_linked_registry_before_evaluation() {
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
                    2,
                    "unchecked Core and linked interface evidence own the registry during validation"
                );
                validate_effect_modules(unchecked, sources, module_sources)
            },
            |core| {
                assert_eq!(
                    registry_lifetime.borrow().as_ref().unwrap().strong_count(),
                    1,
                    "the linked interface owner is released before evaluation"
                );
                evaluate_compiled_core(core)
            },
        )
        .expect("the ownership witness should complete the real pipeline");

        assert_eq!(observation.value_display(), "42");
        drop(observation);
        assert_eq!(
            registry_lifetime.borrow().as_ref().unwrap().strong_count(),
            0
        );
    }

    #[test]
    fn explicit_constraint_owners_retain_wide_graph_refusal_and_fresh_recovery() {
        const SHARED_LIMIT: usize = 380_000;
        const ORIGINAL_LIMIT: usize = 327_680;
        let source = TestSource::write(concat!(
            "import dependency as Dependency\n",
            "main : Unit -> Int\n",
            "main () = 42\n",
        ));
        source.write_sibling("dependency.ash", &public_interface_declarations(4_500));
        for _ in 0..2 {
            let prefix = Cell::new(0);
            let mut shared = InterfaceConstraintBudget::with_limit(SHARED_LIMIT);
            let failure = run_path_with_consumers_and_constraint_budget(
                source.configuration(),
                &mut shared,
                |linked, budget, types| {
                    prefix.set(budget.used());
                    validate_interface_evidence_with_budget(linked, budget, types)
                },
                validate_effect_modules,
                evaluate_compiled_core,
            )
            .expect_err("the continuous owner must retain admission work during validation");
            assert_eq!(prefix.get(), 367_893);
            assert_eq!(failure.reason_code(), "internal.resource.constraint-work");
            let PipelineFailure::EvidenceValidation(error) = failure.pipeline_failure().unwrap()
            else {
                panic!("the finite cumulative owner should reach evidence validation");
            };
            assert_eq!(
                error.reason(),
                crate::evidence_validation::EvidenceValidationReason::ConstraintResourceExhausted
            );
            assert!(shared.used() <= SHARED_LIMIT);
        }
        // A fresh evidence-stage owner fits; the real continuous owner above must
        // not receive this refill after the same completed admission prefix.
        let mut admission = InterfaceConstraintBudget::with_limit(SHARED_LIMIT);
        let observation = run_path_with_consumers_and_constraint_budget(
            source.configuration(),
            &mut admission,
            |linked, budget, types| {
                assert_eq!(budget.used(), 367_893);
                let mut fresh = InterfaceConstraintBudget::with_limit(SHARED_LIMIT);
                let result = validate_interface_evidence_with_budget(linked, &mut fresh, types);
                assert_eq!(fresh.used(), 18_032);
                result
            },
            validate_effect_modules,
            evaluate_compiled_core,
        )
        .expect("the independent evidence stage should fit its own finite owner");
        assert_eq!(observation.value_display(), "42");
        drop(observation);

        let mut declarations = String::new();
        for index in 0..5_000 {
            declarations.push_str(&format!(
                "pub interface Marker{index}<A> {{\nmark{index}<T> : (A, T) -> A\n}}\n\n"
            ));
        }
        source.write_sibling("dependency.ash", &declarations);
        for _ in 0..2 {
            let mut original = InterfaceConstraintBudget::with_limit(ORIGINAL_LIMIT);
            let failure = run_path_with_consumers_and_constraint_budget(
                source.configuration(),
                &mut original,
                validate_interface_evidence_with_budget,
                validate_effect_modules,
                evaluate_compiled_core,
            )
            .expect_err("the original finite owner should still reject polymorphic ingress");
            assert_eq!(failure.reason_code(), "internal.resource.constraint-work");
            assert!(matches!(
                failure.pipeline_failure(),
                Some(PipelineFailure::Typing(TypeError::Internal(_)))
            ));
            assert!(original.used() <= ORIGINAL_LIMIT);
        }
        declarations.clear();
        for index in 0..1_024 {
            declarations.push_str(&format!(
                "pub interface Marker{index}<A> {{\nmark{index}<T> : (A, T) -> A\n}}\n\n"
            ));
        }
        source.write_sibling("dependency.ash", &declarations);
        let mut fresh = InterfaceConstraintBudget::with_limit(ORIGINAL_LIMIT);
        let observation = run_path_with_consumers_and_constraint_budget(
            source.configuration(),
            &mut fresh,
            validate_interface_evidence_with_budget,
            validate_effect_modules,
            evaluate_compiled_core,
        )
        .expect("the unchanged smaller polymorphic graph should recover with a fresh owner");
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
            validate_effect_modules,
            evaluate_compiled_core,
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
            validate_effect_modules,
            evaluate_compiled_core,
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
            validate_effect_modules,
            evaluate_compiled_core,
        )
        .expect("the measured cumulative work should fit exactly");
        assert_eq!(observation.value_display(), "42");
        assert_eq!(exact_budget.used(), exact);
    }

    #[test]
    fn relational_interface_graph_has_an_exact_cross_stage_boundary() {
        // Retain every resolve/check boundary in actual dependency order:
        // Foreign, Region, base, short, long_one, long_two and entry, then
        // linking and independent evidence. The two service modules contribute
        // their real declarations/rows; user modules retain their full closure.
        // Resolve/check debits: Foreign 0/129, Region 14/243, base 74/1532,
        // short 727/399, long_one 727/399, long_two 731/410, entry 845/581;
        // structural linking adds 214 and the new entry evidence adds 129.
        const EXPECTED_BOUNDARIES: [usize; 17] = [
            0, 0, 129, 143, 386, 460, 1_992, 2_719, 3_118, 3_845, 4_244, 4_975, 5_385, 6_230,
            6_811, 7_025, 7_154,
        ];
        const EXACT_CONSTRAINT_WORK: usize = 7_154;
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
            let checked_module = check_module_in_effect_profile_with_rewrite_work(
                resolved,
                &mut checking_type_work,
                &mut coverage_work,
                &mut measured,
                None,
                None,
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

        let mut elaborator = EffectElaborator::for_module_program(&validated_interfaces)
            .expect("the relational Core namespace should fit");
        let typed = elaborator
            .synthesize_effect_module_program(&validated_interfaces)
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
            validate_effect_modules(unchecked, &sources, &module_sources)
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
                validate_effect_modules(unchecked, sources, module_sources)
            },
            evaluate_compiled_core,
        )
        .expect("the exact relational cross-stage boundary should fit");
        assert_eq!(observation.value_display(), "42");
        assert_eq!(validation_prefix.get(), EXPECTED_BOUNDARIES[15]);
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
                validate_effect_modules(unchecked, sources, module_sources)
            },
            evaluate_compiled_core,
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
        // Keep the original 327,680-unit reference boundary and the complete
        // implicit Foreign/Region service modules.
        const ORIGINAL_ALLOWANCE: usize = 327_680;
        const WIDTH: usize = 3_990;
        // Local checking adds 48W+56; entry resolution adds 16W+74, and
        // checking adds 14W+59 for the imported rows and main.
        const DEPENDENCY_CHECKED: usize = 48 * WIDTH + 515;
        const ENTRY_RESOLVED: usize = 64 * WIDTH + 589;
        const ENTRY_CHECKED: usize = 78 * WIDTH + 648;
        // The fixture's generated-variable map has 7,168 occupied capacity
        // cells; linking charges those in addition to 2W+77 other work.
        const LINKED: usize = ENTRY_CHECKED + 2 * WIDTH + 7_168 + 77;
        // Interface indexes and the new entry add 4W+32.
        const VALIDATED: usize = LINKED + 4 * WIDTH + 32;
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
            if module.id() == graph.entry() {
                let dependency_id = graph
                    .modules()
                    .iter()
                    .find(|module| {
                        std::path::Path::new(module.source().display_path()).file_name()
                            == Some("dependency.ash".as_ref())
                    })
                    .expect("the user dependency should remain in the complete graph")
                    .id();
                let imported_interfaces = resolved
                    .imported_facts()
                    .interface_imports()
                    .filter(|imported| imported.fact.id.module() == dependency_id);
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
            let checked_module = check_module_in_effect_profile_with_rewrite_work(
                resolved,
                &mut checking_type_work,
                &mut coverage_work,
                &mut measured,
                None,
                None,
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
                129,
                143,
                386,
                459,
                DEPENDENCY_CHECKED,
                ENTRY_RESOLVED,
                ENTRY_CHECKED,
                LINKED,
                VALIDATED,
            ],
        );
        const { assert!(LINKED < ORIGINAL_ALLOWANCE) };
        const { assert!(VALIDATED > ORIGINAL_ALLOWANCE) };
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
                    validate_effect_modules,
                    evaluate_compiled_core,
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
                    validate_effect_modules,
                    evaluate_compiled_core,
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
                    validate_effect_modules,
                    evaluate_compiled_core,
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

        assert!(matches!(observation.value, Value::RegionFunction(_)));
        let weak = Arc::downgrade(&observation._heap);
        let clone = observation.clone();
        drop(observation);
        assert!(weak.upgrade().is_some());
        assert_eq!(clone.value_display(), "<function>");
        drop(clone);
        assert!(
            weak.upgrade().is_none(),
            "only the last observation releases its root"
        );
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

        for accessor in 0..3 {
            let observation =
                run_path(source.configuration()).expect("the closure should evaluate");
            let weak = Arc::downgrade(&observation._heap);
            let consumed = match accessor {
                0 => observation.into_value(),
                1 => observation.into_parts().into_value(),
                _ => {
                    let (value, ty) = observation.into_parts().into_pair();
                    crate::types::discard_type_iteratively(ty);
                    value
                }
            };
            assert!(matches!(consumed.value(), Value::RegionFunction(_)));
            assert_eq!(consumed.value_display(), "<function>");
            let clone = consumed.clone();
            drop(consumed);
            assert!(weak.upgrade().is_some());
            drop(clone);
            assert!(weak.upgrade().is_none());
        }
        let observation = run_path(source.configuration()).expect("the closure should evaluate");
        let weak = Arc::downgrade(&observation._heap);
        let ty = observation.into_type();
        assert!(
            weak.upgrade().is_none(),
            "returning only its type releases the observation root"
        );
        crate::types::discard_type_iteratively(ty);
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
