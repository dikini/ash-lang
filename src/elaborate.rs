//! Bidirectional typed elaboration from resolved surface syntax to pure Core.

use std::{
    collections::{HashMap, HashSet},
    error::Error,
    fmt,
    sync::Arc,
};

use crate::{
    core::{
        BuildError, CORE_PAYLOAD_DEPTH_LIMIT, CoreBuilder, CoreMatchArm, CorePattern,
        CorePatternKind, NodeId, Primitive, TypedBinder, UnvalidatedProgram,
    },
    diagnostic::{Diagnostic, SourceLabel},
    evidence::{
        EvidenceSelector, SelectionCauseKind, SelectionError, SelectionFailure, SelectionSite,
    },
    evidence_audit::{EvidenceAuditFailure, audit_checked_body_evidence},
    evidence_validation::ValidatedInterfaceProgram,
    interface::{
        CheckedImplMethod, CheckedImplementation, CheckedInterface, CheckedRequirement,
        ConstrainedScheme, EvidenceNode, EvidenceSelection, ImplId, ImplMethodId,
        InterfaceConstraintBudget, InterfaceId, InterfaceReason, MethodId, OverlapFailure,
        RequirementId, implementation_heads_overlap, implementation_prerequisite_terminates,
        same_type_with_constraint_budget,
    },
    pattern::{
        UsefulnessBudget, UsefulnessError, display_witness, missing_witness_for_types_with_budget,
        usefulness_with_budget,
    },
    resolved::{
        AvailableImplementation, BinderId, CheckedDefinition, CheckedGlobalScheme,
        CheckedImplementationBody, CheckedImplementationFact, CheckedImplementationMethodFact,
        CheckedInterfaceFact, CheckedInterfaceMethodFact, CheckedModule, CheckedModuleParts,
        ExportSummary, ResolvedBinding, ResolvedBlock, ResolvedBuildFailure,
        ResolvedDeclarationIndex, ResolvedDefinitionKind, ResolvedExpr, ResolvedExprKind,
        ResolvedLocalDeclaration, ResolvedModule, ResolvedModuleGroup, ResolvedModuleProgram,
        ResolvedPattern, ResolvedPatternKind, ResolvedRecursiveGroup, ResolvedRegistry,
        ResolvedType, ResolvedTypeProvenance, ResolvedTypeProvenanceNode,
    },
    source::{GeneratedReason, Origin, Span, discard_origin_iteratively},
    types::{
        InferenceVariableId, Type, TypeVariableId, TypeWorkBudget, charge_type_cells,
        discard_type_iteratively, same_type, substitute_type_variables_with,
    },
};

/// The source-language typing rule that rejected an expression.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum TypeReason {
    /// A primitive operation received a non-`Int` operand.
    OperatorOperand,
    /// An anonymous function was used without an expected function type.
    FunctionNeedsContext,
    /// An application function position did not have a function type.
    NotApplicable,
    /// An application argument did not match the function domain.
    Argument,
    /// An annotated binding initializer did not match its annotation.
    BindingInitializer,
    /// A global function body did not match its declared result type.
    DefinitionResult,
    /// An equational interface did not expose one function domain.
    EquationInterfaceNotFunction,
    /// A recursive member is not initialized directly by an anonymous function.
    UnsafeRecursiveInitializer,
    /// A recursive data member is not rooted at its declared constructor.
    UnsafeRecursiveRoot,
    /// A recursive occurrence crosses a forcing or transporting form.
    UnguardedRecursiveUse,
    /// A constructor occurrence or pattern disagrees with its declaration.
    ConstructorMismatch,
    /// A pattern constructor belongs to a different nominal declaration.
    ConstructorOwner,
    /// A pattern form disagrees with its expected type.
    PatternMismatch,
    /// Equational clauses consume different or impossible arrow arities.
    EquationArity,
    /// A local binding pattern is semantically refutable.
    RefutableBinding,
    /// A single anonymous or operational domain pattern can fail.
    RefutableFunctionDomain,
    /// A case group leaves a concrete value uncovered.
    NonExhaustive,
    /// A case can never be selected after preceding cases.
    RedundantCase,
    /// First-order inference would construct an infinite type.
    InfiniteType,
    /// Inference left a result type undetermined.
    AmbiguousType,
    /// A recursive use requires distinct instantiations.
    PolymorphicRecursion,
}

impl fmt::Display for TypeReason {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::OperatorOperand => formatter.write_str("type.operator-operand"),
            Self::FunctionNeedsContext => formatter.write_str("type.function-needs-context"),
            Self::NotApplicable => formatter.write_str("type.not-applicable"),
            Self::Argument => formatter.write_str("type.argument"),
            Self::BindingInitializer => formatter.write_str("type.binding-initializer"),
            Self::DefinitionResult => formatter.write_str("type.definition-result"),
            Self::EquationInterfaceNotFunction => {
                formatter.write_str("type.equation-interface-not-function")
            }
            Self::UnsafeRecursiveInitializer => formatter.write_str("recursion.unsafe-initializer"),
            Self::UnsafeRecursiveRoot => formatter.write_str("recursion.unsafe-root"),
            Self::UnguardedRecursiveUse => formatter.write_str("recursion.unguarded-use"),
            Self::ConstructorMismatch => formatter.write_str("pattern.constructor-payload"),
            Self::ConstructorOwner => formatter.write_str("pattern.constructor-owner"),
            Self::PatternMismatch => formatter.write_str("pattern.type-mismatch"),
            Self::EquationArity => formatter.write_str("equation.arity"),
            Self::RefutableBinding => formatter.write_str("pattern.refutable-binding"),
            Self::RefutableFunctionDomain => {
                formatter.write_str("pattern.refutable-function-domain")
            }
            Self::NonExhaustive => formatter.write_str("coverage.non-exhaustive"),
            Self::RedundantCase => formatter.write_str("coverage.redundant-case"),
            Self::InfiniteType => formatter.write_str("type.infinite"),
            Self::AmbiguousType => formatter.write_str("type.ambiguous"),
            Self::PolymorphicRecursion => formatter.write_str("type.polymorphic-recursion"),
        }
    }
}

/// A structural mismatch produced by the general checking rule.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TypeMismatch {
    span: Span,
    expected: Box<Type>,
    found: Box<Type>,
    expected_display: String,
    found_display: String,
}

impl TypeMismatch {
    /// Returns the expression that did not check.
    #[must_use]
    pub const fn span(&self) -> Span {
        self.span
    }

    /// Returns the required structural type.
    #[must_use]
    pub const fn expected(&self) -> &Type {
        &self.expected
    }

    /// Returns the synthesized structural type.
    #[must_use]
    pub const fn found(&self) -> &Type {
        &self.found
    }
}

/// A compiler-owned elaboration failure, distinct from rejected Ash source.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ElaborationFailure {
    /// Core construction could not represent the requested node.
    Core(BuildError),
    /// The explicit elaboration work stack lost an invariant.
    InvalidState,
    /// Pattern coverage exceeded its deterministic compiler resource budget.
    CoverageResourceExhausted,
    /// Cumulative inference and type construction exceeded its work budget.
    TypeResourceExhausted,
    /// Graph-wide interface and constraint processing exceeded its work budget.
    ConstraintResourceExhausted,
}

impl ElaborationFailure {
    /// Returns the stable reason code owned by this elaboration failure.
    #[must_use]
    pub const fn reason_code(&self) -> &'static str {
        match self {
            Self::Core(_) => "internal.core-build",
            Self::InvalidState => "type.internal",
            Self::CoverageResourceExhausted => "internal.resource.coverage",
            Self::TypeResourceExhausted => "internal.resource.type-work",
            Self::ConstraintResourceExhausted => "internal.resource.constraint-work",
        }
    }
}

impl fmt::Display for ElaborationFailure {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Core(error) => write!(formatter, "typed Core construction failed: {error}"),
            Self::InvalidState => formatter.write_str("typed elaboration state is inconsistent"),
            Self::CoverageResourceExhausted => {
                formatter.write_str("pattern coverage resource limit exceeded")
            }
            Self::TypeResourceExhausted => formatter.write_str("type work resource limit exceeded"),
            Self::ConstraintResourceExhausted => {
                formatter.write_str("interface and constraint work resource limit exceeded")
            }
        }
    }
}

impl Error for ElaborationFailure {}

impl From<BuildError> for ElaborationFailure {
    fn from(error: BuildError) -> Self {
        if error == BuildError::TypeWorkExceeded {
            Self::TypeResourceExhausted
        } else {
            Self::Core(error)
        }
    }
}

/// A source diagnostic, general checking mismatch, or compiler failure.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum TypeError {
    /// A categorized Ash source rejection.
    Source(Box<Diagnostic<TypeReason>>),
    /// A categorized interface or implementation source rejection.
    Interface(Box<Diagnostic<InterfaceReason>>),
    /// The general checking rule found structurally unequal types.
    Mismatch(TypeMismatch),
    /// Typed elaboration could not preserve its compiler invariants.
    Internal(ElaborationFailure),
}

impl fmt::Display for TypeError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Source(diagnostic) => formatter.write_str(&diagnostic.render_plain()),
            Self::Interface(diagnostic) => formatter.write_str(&diagnostic.render_plain()),
            Self::Mismatch(mismatch) => write!(
                formatter,
                "type mismatch: expected {}, found {}",
                mismatch.expected_display, mismatch.found_display
            ),
            Self::Internal(failure) => failure.fmt(formatter),
        }
    }
}

impl Error for TypeError {}

impl From<BuildError> for TypeError {
    fn from(error: BuildError) -> Self {
        Self::Internal(error.into())
    }
}

impl From<UsefulnessError> for TypeError {
    fn from(_: UsefulnessError) -> Self {
        Self::Internal(ElaborationFailure::CoverageResourceExhausted)
    }
}

/// Monomorphic types assigned to resolved binder identities.
#[derive(Debug, Default, Eq, PartialEq)]
pub struct TypeContext {
    binders: HashMap<BinderId, TypeFact>,
}

#[cfg(test)]
thread_local! {
    static TYPE_CONTEXT_CLONES: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

impl Clone for TypeContext {
    fn clone(&self) -> Self {
        #[cfg(test)]
        TYPE_CONTEXT_CLONES.with(|clones| clones.set(clones.get() + 1));
        Self {
            binders: self.binders.clone(),
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct TypeFact {
    ty: Type,
    provenance: TypeProvenance,
    quantified: Box<[TypeVariableId]>,
}

#[derive(Debug)]
struct LoweredInterfaceMethod {
    interface: InterfaceId,
    parameter: TypeVariableId,
    value_type: Type,
    declaration_span: Span,
}

#[derive(Debug)]
struct LoweredRequirementMethod {
    method: MethodId,
    ty: Type,
}

#[derive(Debug)]
struct LoweredRequirement {
    id: RequirementId,
    methods: Box<[LoweredRequirementMethod]>,
}

#[derive(Debug)]
struct LoweredScheme {
    source_type_parameters: Option<Box<[TypeVariableId]>>,
    type_parameters: Box<[TypeVariableId]>,
    requirements: Box<[LoweredRequirement]>,
    value_type: Type,
    core_scheme: Type,
}

#[derive(Debug)]
struct LoweredImplementationMethod {
    binder: BinderId,
    scheme: LoweredScheme,
    span: Span,
}

#[derive(Clone, Debug)]
struct ActiveEvidenceBinder {
    binder: BinderId,
    ty: Type,
}

#[derive(Clone, Debug)]
struct LoweredEvidenceMethod {
    method: MethodId,
    node: NodeId,
    ty: Type,
}

struct ScopedEvidenceBinder {
    requirement: RequirementId,
    method: MethodId,
    binder: TypedBinder,
}

#[derive(Debug)]
struct EvidenceLowering {
    interfaces: HashMap<InterfaceId, Box<[MethodId]>>,
    interface_methods: HashMap<MethodId, LoweredInterfaceMethod>,
    global_schemes: HashMap<BinderId, LoweredScheme>,
    implementation_methods: HashMap<ImplMethodId, LoweredImplementationMethod>,
    active_binders: HashMap<(RequirementId, MethodId), ActiveEvidenceBinder>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum TypeProvenance {
    Built {
        nodes: Arc<[TypeProvenanceNode]>,
        root: usize,
    },
    Resolved(ResolvedTypeProvenance),
    Function {
        span: Option<Span>,
        parts: Arc<(TypeProvenance, TypeProvenance)>,
    },
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum TypeProvenanceNode {
    Fact(Option<Span>),
    Function {
        span: Option<Span>,
        domain: usize,
        codomain: usize,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct ProvenancedType {
    ty: Type,
    provenance: TypeProvenance,
}

impl TypeProvenance {
    fn atom(span: Option<Span>) -> Self {
        Self::Built {
            nodes: Arc::from([TypeProvenanceNode::Fact(span)]),
            root: 0,
        }
    }

    fn unknown(ty: &Type) -> Self {
        Self::uniform(ty, None)
    }

    fn at_span(ty: &Type, span: Span) -> Self {
        Self::uniform(ty, Some(span))
    }

    fn uniform(ty: &Type, span: Option<Span>) -> Self {
        let mut tasks = vec![(ty, false)];
        let mut nodes = Vec::new();
        let mut roots = Vec::new();
        while let Some((current, visited)) = tasks.pop() {
            match current {
                Type::Function(domain, codomain) if !visited => {
                    tasks.push((current, true));
                    tasks.push((codomain, false));
                    tasks.push((domain, false));
                }
                Type::Function(_, _) => {
                    let codomain = roots.pop().unwrap_or(0);
                    let domain = roots.pop().unwrap_or(0);
                    nodes.push(TypeProvenanceNode::Function {
                        span,
                        domain,
                        codomain,
                    });
                    roots.push(nodes.len() - 1);
                }
                Type::Int
                | Type::Bool
                | Type::Unit
                | Type::Tuple(_)
                | Type::Nominal(_)
                | Type::Variable(_)
                | Type::Inference(_)
                | Type::AppliedNominal(_, _)
                | Type::Forall(_, _) => {
                    nodes.push(TypeProvenanceNode::Fact(span));
                    roots.push(nodes.len() - 1);
                }
            }
        }
        let root = roots.pop().unwrap_or(0);
        Self::Built {
            nodes: nodes.into(),
            root,
        }
    }

    fn span(&self) -> Option<Span> {
        match self {
            Self::Built { nodes, root } => match nodes.get(*root) {
                Some(
                    TypeProvenanceNode::Fact(span) | TypeProvenanceNode::Function { span, .. },
                ) => *span,
                None => None,
            },
            Self::Resolved(resolved) => resolved.span(),
            Self::Function { span, .. } => *span,
        }
    }

    fn aligns(&self, ty: &Type) -> bool {
        #[derive(Clone, Copy)]
        enum Cursor<'a> {
            Built(&'a [TypeProvenanceNode], usize),
            Resolved(&'a ResolvedTypeProvenance, usize),
            Provenance(&'a TypeProvenance),
        }

        let mut work = vec![(ty, Cursor::Provenance(self))];
        while let Some((current, cursor)) = work.pop() {
            let cursor = match cursor {
                Cursor::Provenance(Self::Built { nodes, root }) => Cursor::Built(nodes, *root),
                Cursor::Provenance(Self::Resolved(resolved)) => {
                    Cursor::Resolved(resolved, resolved.root())
                }
                Cursor::Provenance(provenance @ Self::Function { .. }) => {
                    if let (Type::Function(domain, codomain), Self::Function { parts, .. }) =
                        (current, provenance)
                    {
                        work.push((codomain, Cursor::Provenance(&parts.1)));
                        work.push((domain, Cursor::Provenance(&parts.0)));
                        continue;
                    }
                    return false;
                }
                cursor => cursor,
            };
            match cursor {
                Cursor::Built(nodes, node) => match (current, nodes.get(node)) {
                    (
                        Type::Int
                        | Type::Bool
                        | Type::Unit
                        | Type::Tuple(_)
                        | Type::Nominal(_)
                        | Type::Variable(_)
                        | Type::Inference(_)
                        | Type::AppliedNominal(_, _),
                        Some(TypeProvenanceNode::Fact(_)),
                    ) => {}
                    (
                        Type::Function(domain, codomain),
                        Some(TypeProvenanceNode::Function {
                            domain: domain_node,
                            codomain: codomain_node,
                            ..
                        }),
                    ) => {
                        work.push((codomain, Cursor::Built(nodes, *codomain_node)));
                        work.push((domain, Cursor::Built(nodes, *domain_node)));
                    }
                    _ => return false,
                },
                Cursor::Resolved(resolved, node) => match (current, resolved.nodes().get(node)) {
                    (
                        Type::Function(domain, codomain),
                        Some(ResolvedTypeProvenanceNode::Function {
                            domain: domain_node,
                            codomain: codomain_node,
                            ..
                        }),
                    ) => {
                        work.push((codomain, Cursor::Resolved(resolved, *codomain_node)));
                        work.push((domain, Cursor::Resolved(resolved, *domain_node)));
                    }
                    (
                        Type::Int
                        | Type::Bool
                        | Type::Unit
                        | Type::Tuple(_)
                        | Type::Nominal(_)
                        | Type::Variable(_)
                        | Type::Inference(_)
                        | Type::AppliedNominal(_, _),
                        Some(
                            ResolvedTypeProvenanceNode::Fact(_)
                            | ResolvedTypeProvenanceNode::Tuple { .. }
                            | ResolvedTypeProvenanceNode::Application { .. },
                        ),
                    ) => {}
                    _ => return false,
                },
                Cursor::Provenance(_) => unreachable!(),
            }
        }
        true
    }

    fn child(&self, node: usize) -> Result<Self, TypeError> {
        match self {
            Self::Built { nodes, .. } if nodes.get(node).is_some() => Ok(Self::Built {
                nodes: Arc::clone(nodes),
                root: node,
            }),
            _ => Err(invalid_state()),
        }
    }

    fn function_parts(&self, ty: &Type) -> Result<(Self, Self), TypeError> {
        let Type::Function(_, _) = ty else {
            return Err(invalid_state());
        };
        match self {
            Self::Built { nodes, root } => {
                let Some(TypeProvenanceNode::Function {
                    domain, codomain, ..
                }) = nodes.get(*root)
                else {
                    return Err(invalid_state());
                };
                Ok((self.child(*domain)?, self.child(*codomain)?))
            }
            Self::Resolved(resolved) => resolved
                .function_parts()
                .map(|(domain, codomain)| (Self::Resolved(domain), Self::Resolved(codomain)))
                .ok_or_else(invalid_state),
            Self::Function { parts, .. } => Ok((parts.0.clone(), parts.1.clone())),
        }
    }
}

impl ProvenancedType {
    #[cfg(test)]
    fn unknown(ty: Type) -> Self {
        let provenance = TypeProvenance::unknown(&ty);
        Self { ty, provenance }
    }

    fn from_resolved_with_budget(
        resolved: &ResolvedType,
        budget: &mut TypeWorkBudget,
    ) -> Result<Self, TypeError> {
        charge_type_cells(&resolved.ty, budget)
            .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
        budget
            .charge(1)
            .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
        Ok(Self {
            ty: zonk_type(&resolved.ty, &HashMap::new()),
            provenance: TypeProvenance::Resolved(resolved.provenance.clone()),
        })
    }

    fn function_with_budget(
        domain: Self,
        codomain: Self,
        span: Option<Span>,
        budget: &mut TypeWorkBudget,
    ) -> Result<Self, TypeError> {
        if !domain.provenance.aligns(&domain.ty) || !codomain.provenance.aligns(&codomain.ty) {
            return Err(invalid_state());
        }
        budget
            .charge(2)
            .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
        Ok(Self {
            ty: Type::Function(Box::new(domain.ty), Box::new(codomain.ty)),
            provenance: TypeProvenance::Function {
                span,
                parts: Arc::new((domain.provenance, codomain.provenance)),
            },
        })
    }

    fn into_function_parts(self) -> Result<(Self, Self), TypeError> {
        let (domain_provenance, codomain_provenance) = self.provenance.function_parts(&self.ty)?;
        let Type::Function(domain, codomain) = self.ty else {
            return Err(invalid_state());
        };
        Ok((
            Self {
                ty: *domain,
                provenance: domain_provenance,
            },
            Self {
                ty: *codomain,
                provenance: codomain_provenance,
            },
        ))
    }
}

impl TypeContext {
    /// Creates an empty typing context.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Adds or replaces one resolved binder type.
    ///
    /// This prepares caller-owned context metadata. Public elaboration entry
    /// points validate and charge the complete context before cloning it.
    pub fn insert(&mut self, binder: BinderId, ty: Type) -> Option<Type> {
        let provenance = TypeProvenance::unknown(&ty);
        self.binders
            .insert(
                binder,
                TypeFact {
                    ty,
                    provenance,
                    quantified: Box::new([]),
                },
            )
            .map(|fact| fact.ty)
    }

    /// Returns the monotype assigned to a resolved binder.
    #[must_use]
    pub fn lookup(&self, binder: BinderId) -> Option<&Type> {
        self.binders.get(&binder).map(|fact| &fact.ty)
    }

    fn insert_with_provenance(
        &mut self,
        binder: BinderId,
        ty: Type,
        provenance: TypeProvenance,
    ) -> Result<Option<TypeFact>, TypeError> {
        if !provenance.aligns(&ty) {
            return Err(invalid_state());
        }
        Ok(self.binders.insert(
            binder,
            TypeFact {
                ty,
                provenance,
                quantified: Box::new([]),
            },
        ))
    }

    fn fact(&self, binder: BinderId) -> Option<&TypeFact> {
        self.binders.get(&binder)
    }

    fn set_quantified(
        &mut self,
        binder: BinderId,
        quantified: Box<[TypeVariableId]>,
    ) -> Result<(), TypeError> {
        let fact = self.binders.get_mut(&binder).ok_or_else(invalid_state)?;
        fact.quantified = quantified;
        Ok(())
    }
}

/// A typed Core node returned by a synthesis or checking rule.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TypedNode {
    /// Core identity allocated for the expression.
    pub node: NodeId,
    /// Structural result type.
    pub ty: Type,
    provenance: TypeProvenance,
}

struct CheckedSchemeBuffer(Vec<CheckedGlobalScheme>);

impl CheckedSchemeBuffer {
    fn into_vec(mut self) -> Vec<CheckedGlobalScheme> {
        std::mem::take(&mut self.0)
    }
}

struct CheckedImplementationFactBuffer(Vec<CheckedImplementationFact>);

impl CheckedImplementationFactBuffer {
    fn into_boxed_slice(mut self) -> Box<[CheckedImplementationFact]> {
        std::mem::take(&mut self.0).into_boxed_slice()
    }
}

impl Drop for CheckedImplementationFactBuffer {
    fn drop(&mut self) {
        for fact in self.0.drain(..) {
            drop(fact);
        }
    }
}

impl Drop for CheckedSchemeBuffer {
    fn drop(&mut self) {
        for checked in self.0.drain(..) {
            drop(checked.scheme);
            discard_origin_iteratively(checked.origin);
        }
    }
}

#[derive(Debug)]
struct CheckedBodyBuffers {
    definitions: Vec<CheckedDefinition>,
    implementations: Vec<CheckedImplementationBody>,
}

fn reserve_checked_body_buffers(
    definition_count: usize,
    implementation_count: usize,
) -> Result<CheckedBodyBuffers, TypeError> {
    let mut definitions = Vec::new();
    definitions
        .try_reserve_exact(definition_count)
        .map_err(|_| constraint_resource())?;
    let mut implementations = Vec::new();
    implementations
        .try_reserve_exact(implementation_count)
        .map_err(|_| constraint_resource())?;
    Ok(CheckedBodyBuffers {
        definitions,
        implementations,
    })
}

struct TypeReplacementBuffer(HashMap<TypeVariableId, Type>);

impl Drop for TypeReplacementBuffer {
    fn drop(&mut self) {
        for (_, ty) in self.0.drain() {
            discard_type_iteratively(ty);
        }
    }
}

trait DefinitionView {
    fn kind(&self) -> &ResolvedDefinitionKind;
    fn span(&self) -> Span;
}

impl DefinitionView for crate::resolved::ResolvedDefinition {
    fn kind(&self) -> &ResolvedDefinitionKind {
        &self.kind
    }

    fn span(&self) -> Span {
        self.span
    }
}

impl DefinitionView for CheckedDefinition {
    fn kind(&self) -> &ResolvedDefinitionKind {
        self.kind()
    }

    fn span(&self) -> Span {
        self.span()
    }
}

/// The one bidirectional typed elaborator for resolved Ash syntax.
#[derive(Debug)]
#[must_use]
pub struct Elaborator {
    builder: CoreBuilder,
    registry: Arc<ResolvedRegistry>,
    purpose: ElaborationPurpose,
    state: ElaboratorState,
    final_root: Option<NodeId>,
    next_inference: u32,
    inference_origins: Vec<Span>,
    next_generated_type_variable: u32,
    inference_solutions: HashMap<InferenceVariableId, Type>,
    monomorphic_recursive: HashSet<BinderId>,
    method_binders: HashMap<MethodId, BinderId>,
    selection: Option<EvidenceSelector>,
    evidence_lowering: Option<EvidenceLowering>,
    type_work: TypeWorkBudget,
    constraint_work: InterfaceConstraintBudget,
    coverage_work: UsefulnessBudget,
    base_context: TypeContext,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ElaboratorState {
    Ready,
    Poisoned,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ElaborationPurpose {
    Standalone,
    ModuleCheck,
    FinalSynthesis,
}

impl Elaborator {
    /// Starts an elaborator for an expression with no resolved binder namespace.
    pub fn new() -> Self {
        let registry = Arc::new(ResolvedRegistry::default());
        Self {
            builder: CoreBuilder::with_registry(Arc::clone(&registry)),
            registry,
            purpose: ElaborationPurpose::Standalone,
            state: ElaboratorState::Ready,
            final_root: None,
            next_inference: 0,
            inference_origins: Vec::new(),
            next_generated_type_variable: u32::MAX,
            inference_solutions: HashMap::new(),
            monomorphic_recursive: HashSet::new(),
            method_binders: HashMap::new(),
            selection: None,
            evidence_lowering: None,
            type_work: TypeWorkBudget::default(),
            constraint_work: InterfaceConstraintBudget::default(),
            coverage_work: UsefulnessBudget::default(),
            base_context: TypeContext::new(),
        }
    }

    #[cfg(test)]
    fn for_module(module: &ResolvedModule) -> Result<Self, TypeError> {
        let mut elaborator = Self::for_module_with_work(
            module,
            TypeWorkBudget::default(),
            UsefulnessBudget::default(),
        )?;
        elaborator.purpose = ElaborationPurpose::Standalone;
        Ok(elaborator)
    }

    fn for_module_with_work(
        module: &ResolvedModule,
        mut type_work: TypeWorkBudget,
        coverage_work: UsefulnessBudget,
    ) -> Result<Self, TypeError> {
        let registry = Arc::new(
            module
                .registry()
                .checker_view(module.imported_facts(), &mut type_work)
                .map_err(resolved_build_error)?,
        );
        let mut builder = CoreBuilder::with_registry(Arc::clone(&registry));
        builder
            .reserve_resolved_binders(resolved_module_binders(module))
            .map_err(TypeError::from)?;
        let mut base_context = TypeContext::new();
        for imported in module.imported_facts().globals() {
            type_work
                .charge(imported.scheme.type_parameters.len())
                .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
            let mut quantified = Vec::new();
            quantified
                .try_reserve(imported.scheme.type_parameters.len())
                .map_err(|_| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
            quantified.extend_from_slice(&imported.scheme.type_parameters);
            let quantified = quantified.into_boxed_slice();
            let body = clone_type_with_budget(&imported.scheme.value_type, &mut type_work)
                .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
            let provenance = TypeProvenance::at_span(&body, imported.origin.primary_span());
            if base_context
                .insert_with_provenance(imported.binder, body, provenance)?
                .is_some()
            {
                return Err(invalid_state());
            }
            base_context.set_quantified(imported.binder, quantified)?;
        }
        Ok(Self {
            builder,
            registry,
            purpose: ElaborationPurpose::ModuleCheck,
            state: ElaboratorState::Ready,
            final_root: None,
            next_inference: 0,
            inference_origins: Vec::new(),
            next_generated_type_variable: u32::MAX,
            inference_solutions: HashMap::new(),
            monomorphic_recursive: HashSet::new(),
            method_binders: HashMap::new(),
            selection: None,
            evidence_lowering: None,
            type_work,
            constraint_work: InterfaceConstraintBudget::default(),
            coverage_work,
            base_context,
        })
    }

    /// Starts the one final elaborator for a dependency-ordered module graph.
    ///
    /// # Errors
    ///
    /// Returns a construction failure if any resolved binder identity is
    /// duplicated or cannot be reserved before lowering begins.
    pub fn for_module_program(
        program: &ValidatedInterfaceProgram,
    ) -> Result<Self, ElaborationFailure> {
        let registry = Arc::clone(program.registry());
        let mut builder = CoreBuilder::with_registry(Arc::clone(&registry));
        let mut binders = Vec::new();
        let mut expressions = vec![program.result()];
        for group in program.groups() {
            for definition in group.definitions() {
                collect_definition_kind_binders(definition.kind(), &mut binders, &mut expressions);
            }
            for implementation in group.implementations() {
                collect_implementation_binders(
                    std::slice::from_ref(implementation.source()),
                    &mut binders,
                    &mut expressions,
                );
            }
        }
        collect_expression_binders(&mut binders, expressions);
        builder.reserve_resolved_binders(binders)?;
        let mut elaborator = Self {
            builder,
            registry,
            purpose: ElaborationPurpose::FinalSynthesis,
            state: ElaboratorState::Ready,
            final_root: None,
            next_inference: 0,
            inference_origins: Vec::new(),
            next_generated_type_variable: u32::MAX,
            inference_solutions: HashMap::new(),
            monomorphic_recursive: HashSet::new(),
            method_binders: HashMap::new(),
            selection: None,
            evidence_lowering: None,
            type_work: TypeWorkBudget::default(),
            constraint_work: InterfaceConstraintBudget::default(),
            coverage_work: UsefulnessBudget::default(),
            base_context: TypeContext::new(),
        };
        elaborator.evidence_lowering = Some(elaborator.build_evidence_lowering(program).map_err(
            |error| match error {
                TypeError::Internal(failure) => failure,
                TypeError::Source(_) | TypeError::Interface(_) | TypeError::Mismatch(_) => {
                    ElaborationFailure::InvalidState
                }
            },
        )?);
        Ok(elaborator)
    }

    fn build_evidence_lowering(
        &mut self,
        program: &ValidatedInterfaceProgram,
    ) -> Result<EvidenceLowering, TypeError> {
        let interface_count: usize = program
            .groups()
            .iter()
            .map(|group| group.interface_facts().len())
            .sum();
        let method_count: usize = program
            .groups()
            .iter()
            .flat_map(|group| group.interface_facts())
            .map(|interface| interface.methods.len())
            .sum();
        let global_count: usize = program
            .groups()
            .iter()
            .map(|group| group.schemes().len())
            .sum();
        let implementation_method_count: usize = program
            .groups()
            .iter()
            .flat_map(|group| group.implementation_facts())
            .map(|implementation| implementation.methods.len())
            .sum();
        self.type_work
            .charge(
                interface_count
                    .saturating_add(method_count)
                    .saturating_add(global_count)
                    .saturating_add(implementation_method_count),
            )
            .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
        let mut interfaces = HashMap::new();
        interfaces
            .try_reserve(interface_count)
            .map_err(|_| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
        let mut interface_methods = HashMap::new();
        interface_methods
            .try_reserve(method_count)
            .map_err(|_| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
        for group in program.groups() {
            for interface in group.interface_facts() {
                let mut methods = Vec::new();
                methods
                    .try_reserve(interface.methods.len())
                    .map_err(|_| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
                for method in &interface.methods {
                    methods.push(method.id);
                    let lowered = LoweredInterfaceMethod {
                        interface: interface.id,
                        parameter: interface.parameter.id,
                        value_type: self.clone_type(&method.value_type)?,
                        declaration_span: method.span,
                    };
                    if interface_methods.insert(method.id, lowered).is_some() {
                        return Err(invalid_state());
                    }
                }
                if interfaces
                    .insert(interface.id, methods.into_boxed_slice())
                    .is_some()
                {
                    return Err(invalid_state());
                }
            }
        }

        let mut lowering = EvidenceLowering {
            interfaces,
            interface_methods,
            global_schemes: HashMap::new(),
            implementation_methods: HashMap::new(),
            active_binders: HashMap::new(),
        };
        lowering
            .global_schemes
            .try_reserve(global_count)
            .map_err(|_| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
        lowering
            .implementation_methods
            .try_reserve(implementation_method_count)
            .map_err(|_| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
        for group in program.groups() {
            for checked in group.schemes() {
                let scheme = self.lower_constrained_scheme(&checked.scheme, &lowering, false)?;
                if lowering
                    .global_schemes
                    .insert(checked.binder, scheme)
                    .is_some()
                {
                    return Err(invalid_state());
                }
            }
            for implementation in group.implementation_facts() {
                for method in &implementation.methods {
                    let scheme = self.lower_constrained_scheme(&method.scheme, &lowering, true)?;
                    let lowered = LoweredImplementationMethod {
                        binder: method.binder,
                        scheme,
                        span: method.span,
                    };
                    if lowering
                        .implementation_methods
                        .insert(method.id, lowered)
                        .is_some()
                    {
                        return Err(invalid_state());
                    }
                }
            }
        }
        Ok(lowering)
    }

    fn lower_constrained_scheme(
        &mut self,
        scheme: &ConstrainedScheme,
        lowering: &EvidenceLowering,
        freshen_core_parameters: bool,
    ) -> Result<LoweredScheme, TypeError> {
        self.type_work
            .charge(
                scheme
                    .type_parameters
                    .len()
                    .saturating_add(scheme.requirements.len()),
            )
            .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
        let original_type_parameters =
            clone_type_variables_with_budget(&scheme.type_parameters, &mut self.type_work)
                .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?
                .into_boxed_slice();
        let value_type = self.clone_type(&scheme.value_type)?;
        let mut parameter_replacements = TypeReplacementBuffer(HashMap::new());
        let (source_type_parameters, type_parameters) = if freshen_core_parameters {
            parameter_replacements
                .0
                .try_reserve(original_type_parameters.len())
                .map_err(|_| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
            let mut type_parameters = Vec::new();
            type_parameters
                .try_reserve(original_type_parameters.len())
                .map_err(|_| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
            for source in &original_type_parameters {
                let core = self.fresh_type_variable()?;
                type_parameters.push(core);
                parameter_replacements
                    .0
                    .insert(*source, Type::Variable(core));
            }
            (
                Some(original_type_parameters),
                type_parameters.into_boxed_slice(),
            )
        } else {
            (None, original_type_parameters)
        };
        let mut requirements = Vec::new();
        requirements
            .try_reserve(scheme.requirements.len())
            .map_err(|_| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
        for requirement in &scheme.requirements {
            let method_order = lowering
                .interfaces
                .get(&requirement.interface)
                .ok_or_else(invalid_state)?;
            let mut methods = Vec::new();
            methods
                .try_reserve(method_order.len())
                .map_err(|_| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
            for method in method_order {
                let method_fact = lowering
                    .interface_methods
                    .get(method)
                    .ok_or_else(invalid_state)?;
                if method_fact.interface != requirement.interface {
                    return Err(invalid_state());
                }
                let mut replacement = HashMap::new();
                replacement
                    .try_reserve(1)
                    .map_err(|_| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
                replacement.insert(
                    method_fact.parameter,
                    self.clone_type(&requirement.argument)?,
                );
                let ty = substitute_type_variables_with(
                    &method_fact.value_type,
                    &replacement,
                    |cells| self.type_work.charge(cells),
                )
                .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
                for (_, replacement) in replacement {
                    discard_type_iteratively(replacement);
                }
                methods.push(LoweredRequirementMethod {
                    method: *method,
                    ty,
                });
            }
            requirements.push(LoweredRequirement {
                id: requirement.id,
                methods: methods.into_boxed_slice(),
            });
        }

        let mut core_body = self.clone_type(&value_type)?;
        for requirement in requirements.iter().rev() {
            for method in requirement.methods.iter().rev() {
                self.type_work
                    .charge(1)
                    .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
                core_body =
                    Type::Function(Box::new(self.clone_type(&method.ty)?), Box::new(core_body));
            }
        }
        if !parameter_replacements.0.is_empty() {
            let renamed =
                substitute_type_variables_with(&core_body, &parameter_replacements.0, |cells| {
                    self.type_work.charge(cells)
                })
                .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
            discard_type_iteratively(core_body);
            core_body = renamed;
        }
        let core_scheme = if type_parameters.is_empty() {
            core_body
        } else {
            self.type_work
                .charge(1)
                .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
            Type::Forall(
                clone_type_variables_with_budget(&type_parameters, &mut self.type_work)
                    .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?
                    .into_boxed_slice(),
                Box::new(core_body),
            )
        };
        Ok(LoweredScheme {
            source_type_parameters,
            type_parameters,
            requirements: requirements.into_boxed_slice(),
            value_type,
            core_scheme,
        })
    }

    /// Starts a standalone elaborator for one resolved expression probe.
    ///
    /// This entry point reserves binders reachable from the expression but does
    /// not accept module definitions or construct a linked module program.
    pub fn for_resolved_expression(
        module: &ResolvedModule,
        expression: &ResolvedExpr,
    ) -> Result<Self, ElaborationFailure> {
        let registry = Arc::clone(module.registry());
        let mut builder = CoreBuilder::with_registry(Arc::clone(&registry));
        let mut binders = Vec::new();
        collect_expression_binders(&mut binders, vec![expression]);
        builder.reserve_resolved_binders(binders)?;
        Ok(Self {
            builder,
            registry,
            purpose: ElaborationPurpose::Standalone,
            state: ElaboratorState::Ready,
            final_root: None,
            next_inference: 0,
            inference_origins: Vec::new(),
            next_generated_type_variable: u32::MAX,
            inference_solutions: HashMap::new(),
            monomorphic_recursive: HashSet::new(),
            method_binders: HashMap::new(),
            selection: None,
            evidence_lowering: None,
            type_work: TypeWorkBudget::default(),
            constraint_work: InterfaceConstraintBudget::default(),
            coverage_work: UsefulnessBudget::default(),
            base_context: TypeContext::new(),
        })
    }

    /// Synthesizes an expression type and emits its typed pure Core node.
    ///
    /// # Errors
    ///
    /// Returns a structured source error when a primitive operand is not an
    /// integer, or a structured internal failure when the public context is not
    /// a bounded monotype context or Core construction fails. The failing call
    /// preserves that original error and poisons this elaborator; later
    /// synthesis, checking, and completion return an internal invalid-state
    /// error so partially emitted Core cannot escape.
    pub fn synthesize(
        &mut self,
        expression: &ResolvedExpr,
        context: &TypeContext,
    ) -> Result<TypedNode, TypeError> {
        if self.state == ElaboratorState::Poisoned || self.purpose != ElaborationPurpose::Standalone
        {
            return Err(invalid_state());
        }
        if let Err(error) = self.admit_public_context(context) {
            self.state = ElaboratorState::Poisoned;
            return Err(error);
        }
        let mut context = context.clone();
        let result = self.elaborate_expression_with_context(
            ElaborationTask::Synthesize {
                expression,
                cause: None,
            },
            &mut context,
        );
        if result.is_err() {
            self.state = ElaboratorState::Poisoned;
        }
        result
    }

    /// Checks an expression against an expected structural type.
    ///
    /// # Errors
    ///
    /// Returns the synthesis failure, an internal failure when either public
    /// type input is not a bounded monotype, or [`TypeError::Mismatch`] when the
    /// synthesized and expected type structures differ. Any failure poisons
    /// this elaborator after preserving the original error from this call.
    pub fn check(
        &mut self,
        expression: &ResolvedExpr,
        expected: &Type,
        context: &TypeContext,
    ) -> Result<TypedNode, TypeError> {
        if self.state == ElaboratorState::Poisoned || self.purpose != ElaborationPurpose::Standalone
        {
            return Err(invalid_state());
        }
        if let Err(error) = self
            .admit_public_monotype(expected)
            .and_then(|()| self.admit_public_context(context))
        {
            self.state = ElaboratorState::Poisoned;
            return Err(error);
        }
        let expected_provenance = match self.unknown_provenance(expected) {
            Ok(provenance) => provenance,
            Err(error) => {
                self.state = ElaboratorState::Poisoned;
                return Err(error);
            }
        };
        let mut context = context.clone();
        let result = self.elaborate_expression_with_context(
            ElaborationTask::Check {
                expression,
                expected: ProvenancedType {
                    ty: expected.clone(),
                    provenance: expected_provenance,
                },
                kind: CheckKind::General,
            },
            &mut context,
        );
        if result.is_err() {
            self.state = ElaboratorState::Poisoned;
        }
        result
    }

    /// Lowers checked modules into nested ordinary Core recursive groups.
    ///
    /// # Errors
    ///
    /// Returns a source typing error or Core construction failure and poisons
    /// the elaborator on failure.
    pub fn synthesize_module_program(
        &mut self,
        program: &ValidatedInterfaceProgram,
    ) -> Result<TypedNode, TypeError> {
        if self.state == ElaboratorState::Poisoned
            || self.purpose != ElaborationPurpose::FinalSynthesis
            || self.final_root.is_some()
        {
            return Err(invalid_state());
        }
        let result = self.elaborate_module_program(program);
        match result {
            Ok(typed) => {
                self.final_root = Some(typed.node);
                Ok(typed)
            }
            Err(error) => {
                self.state = ElaboratorState::Poisoned;
                Err(error)
            }
        }
    }

    fn check_module_bodies(
        &mut self,
        module: &ResolvedModule,
        checked_schemes: &[CheckedGlobalScheme],
        checked_interfaces: &[CheckedInterface],
        checked_implementations: &[CheckedImplementation],
        constraint_work: &mut InterfaceConstraintBudget,
    ) -> Result<Box<[CheckedImplementationFact]>, TypeError> {
        if self.purpose != ElaborationPurpose::ModuleCheck {
            return Err(invalid_state());
        }
        std::mem::swap(&mut self.constraint_work, constraint_work);
        let result = self.check_module_bodies_with_owned_budget(
            module,
            checked_schemes,
            checked_interfaces,
            checked_implementations,
        );
        std::mem::swap(&mut self.constraint_work, constraint_work);
        result
    }

    fn check_module_bodies_with_owned_budget(
        &mut self,
        module: &ResolvedModule,
        checked_schemes: &[CheckedGlobalScheme],
        checked_interfaces: &[CheckedInterface],
        checked_implementations: &[CheckedImplementation],
    ) -> Result<Box<[CheckedImplementationFact]>, TypeError> {
        let base_context = self.base_context.clone();
        let mut globals = self.prepare_definition_views(
            module.definitions().iter(),
            Some(checked_schemes),
            base_context,
        )?;
        let mut facts = CheckedImplementationFactBuffer(Vec::new());
        let mut facts_reserved = false;
        let mut next_global = 0;
        let mut next_implementation = 0;
        for declaration in module.declaration_order() {
            match *declaration {
                ResolvedDeclarationIndex::Global(source_index) => {
                    if source_index != next_global {
                        return Err(invalid_state());
                    }
                    let definition = module
                        .definitions()
                        .get(source_index)
                        .ok_or_else(invalid_state)?;
                    self.elaborate_prepared_definition(definition, &mut globals)?;
                    next_global = next_global.checked_add(1).ok_or_else(invalid_state)?;
                }
                ResolvedDeclarationIndex::Implementation(source_index) => {
                    if source_index != next_implementation {
                        return Err(invalid_state());
                    }
                    if !facts_reserved {
                        self.constraint_work
                            .charge(checked_implementations.len())
                            .map_err(|()| constraint_resource())?;
                        facts
                            .0
                            .try_reserve(checked_implementations.len())
                            .map_err(|_| constraint_resource())?;
                        facts_reserved = true;
                    }
                    let checked = checked_implementations
                        .get(source_index)
                        .ok_or_else(invalid_state)?;
                    if checked.source_index != source_index {
                        return Err(invalid_state());
                    }
                    facts.0.push(self.check_implementation_body(
                        module,
                        checked_interfaces,
                        checked,
                        &mut globals.context,
                    )?);
                    next_implementation = next_implementation
                        .checked_add(1)
                        .ok_or_else(invalid_state)?;
                }
                ResolvedDeclarationIndex::Type(_) | ResolvedDeclarationIndex::Interface(_) => {}
            }
        }
        if next_global != module.definitions().len()
            || next_implementation != module.implementations().len()
            || next_implementation != checked_implementations.len()
        {
            return Err(invalid_state());
        }

        let (_, mut context) = self.finish_prepared_definitions(globals)?;
        let result = ResolvedExpr {
            kind: ResolvedExprKind::Unit,
            span: module.span(),
        };
        self.elaborate_result(&result, &mut context)?;
        Ok(facts.into_boxed_slice())
    }

    fn check_implementation_body(
        &mut self,
        module: &ResolvedModule,
        checked_interfaces: &[CheckedInterface],
        checked: &CheckedImplementation,
        context: &mut TypeContext,
    ) -> Result<CheckedImplementationFact, TypeError> {
        let implementation = module
            .implementations()
            .get(checked.source_index)
            .ok_or_else(invalid_state)?;
        if implementation.id != checked.id || implementation.interface.id != checked.interface {
            return Err(invalid_state());
        }
        let interface = checked_interface(
            module,
            checked_interfaces,
            checked.interface,
            &mut self.constraint_work,
        )?
        .ok_or_else(invalid_state)?;

        self.type_work
            .charge(1)
            .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
        let mut replacements = TypeReplacementBuffer(HashMap::new());
        replacements
            .0
            .try_reserve(1)
            .map_err(|_| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
        replacements.0.insert(
            interface.parameter(),
            self.clone_type(&implementation.argument.ty)?,
        );

        if checked.methods.len() != interface.method_count() {
            return Err(invalid_state());
        }
        self.constraint_work
            .charge(
                implementation
                    .head_parameters
                    .len()
                    .saturating_add(implementation.prerequisites.len())
                    .saturating_add(checked.methods.len())
                    .saturating_add(1),
            )
            .map_err(|()| constraint_resource())?;
        let mut method_facts = Vec::new();
        method_facts
            .try_reserve(checked.methods.len())
            .map_err(|_| constraint_resource())?;
        for (method_index, checked_method) in checked.methods.iter().enumerate() {
            let method = interface.method(method_index).ok_or_else(invalid_state)?;
            let group = implementation
                .method_groups
                .get(checked_method.source_group)
                .ok_or_else(invalid_state)?;
            if method.id() != checked_method.method
                || group.method != Some(method.id())
                || group.identity != Some(checked_method.id)
                || group.binder.id != checked_method.binder
                || checked_method.id.implementation() != implementation.id
            {
                return Err(invalid_state());
            }
            let method_type =
                substitute_type_variables_with(method.value_type(), &replacements.0, |cells| {
                    self.constraint_work
                        .charge(cells)
                        .map_err(|()| constraint_resource())?;
                    self.type_work.charge(cells).map_err(|()| {
                        TypeError::Internal(ElaborationFailure::TypeResourceExhausted)
                    })
                })?;
            charge_type_provenance_nodes(&method_type, &mut self.type_work)
                .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
            let provenance = TypeProvenance::at_span(&method_type, method.annotation_span());
            let presentation = implementation_method_origin(
                implementation,
                group,
                method.span(),
                method.annotation_span(),
            );
            let evidence_marker = self.enter_implementation_evidence_scope(implementation.id)?;
            let body_result = self.elaborate_equations(
                &group.equations,
                ProvenancedType {
                    ty: method_type,
                    provenance,
                },
                context,
                group.span,
                &presentation,
            );
            let close_result = if body_result.is_ok() {
                self.close_evidence_obligations(evidence_marker)
            } else {
                Ok(())
            };
            let leave_result = self.leave_evidence_scope();
            let checked_body = body_result?;
            close_result?;
            leave_result?;
            let scheme =
                self.checked_implementation_method_scheme(implementation, &checked_body.ty)?;
            method_facts.push(CheckedImplementationMethodFact {
                id: checked_method.id,
                method: checked_method.method,
                binder: checked_method.binder,
                scheme,
                origin: presentation,
                span: group.span,
            });
        }

        let mut head_parameters = Vec::new();
        head_parameters
            .try_reserve(implementation.head_parameters.len())
            .map_err(|_| constraint_resource())?;
        head_parameters.extend(implementation.head_parameters.iter().cloned());
        let prerequisites =
            self.clone_implementation_requirements(&implementation.prerequisites)?;
        self.constraint_work
            .charge_type(&implementation.argument.ty)
            .map_err(|()| constraint_resource())?;
        Ok(CheckedImplementationFact {
            id: implementation.id,
            interface: implementation.interface.id,
            head_parameters: head_parameters.into_boxed_slice(),
            argument: self.clone_type(&implementation.argument.ty)?,
            prerequisites,
            methods: method_facts.into_boxed_slice(),
            origin: Origin::Source(implementation.span),
            span: implementation.span,
        })
    }

    fn checked_implementation_method_scheme(
        &mut self,
        implementation: &crate::resolved::ResolvedImplementation,
        value_type: &Type,
    ) -> Result<ConstrainedScheme, TypeError> {
        self.constraint_work
            .charge(
                implementation
                    .head_parameters
                    .len()
                    .saturating_add(implementation.prerequisites.len())
                    .saturating_add(1),
            )
            .map_err(|()| constraint_resource())?;
        self.constraint_work
            .charge_type(value_type)
            .map_err(|()| constraint_resource())?;
        self.type_work
            .charge(implementation.head_parameters.len())
            .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
        let mut type_parameters = Vec::new();
        type_parameters
            .try_reserve(implementation.head_parameters.len())
            .map_err(|_| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
        type_parameters.extend(
            implementation
                .head_parameters
                .iter()
                .map(|parameter| parameter.id),
        );
        Ok(ConstrainedScheme {
            type_parameters: type_parameters.into_boxed_slice(),
            requirements: self.clone_implementation_requirements(&implementation.prerequisites)?,
            value_type: self.clone_type(value_type)?,
        })
    }

    fn clone_implementation_requirements(
        &mut self,
        requirements: &[crate::resolved::ResolvedRequirement],
    ) -> Result<Box<[CheckedRequirement]>, TypeError> {
        self.constraint_work
            .charge(requirements.len())
            .map_err(|()| constraint_resource())?;
        let mut checked = Vec::new();
        checked
            .try_reserve(requirements.len())
            .map_err(|_| constraint_resource())?;
        for requirement in requirements {
            self.constraint_work
                .charge_type(&requirement.argument.ty)
                .map_err(|()| constraint_resource())?;
            checked.push(CheckedRequirement {
                id: requirement.id,
                interface: requirement.interface.id,
                argument: self.clone_type(&requirement.argument.ty)?,
                origin: Origin::Source(requirement.span),
                span: requirement.span,
            });
        }
        Ok(checked.into_boxed_slice())
    }

    fn checked_module_schemes(
        &mut self,
        definitions: &[crate::resolved::ResolvedDefinition],
    ) -> Result<Vec<CheckedGlobalScheme>, TypeError> {
        let mut checked = CheckedSchemeBuffer(Vec::with_capacity(definitions.len()));
        for definition in definitions {
            let (name, parameters, requirements) = match &definition.kind {
                ResolvedDefinitionKind::Equational(equational) => (
                    &equational.interface.name,
                    equational.interface.type_parameters.as_ref(),
                    equational.interface.requirements.as_ref(),
                ),
                ResolvedDefinitionKind::InlineOperational(operational) => (
                    &operational.header.name,
                    operational.header.type_parameters.as_ref(),
                    operational.header.requirements.as_ref(),
                ),
            };
            self.type_work
                .charge(parameters.len().saturating_add(requirements.len()))
                .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
            let mut type_parameters = Vec::new();
            type_parameters
                .try_reserve(parameters.len())
                .map_err(|_| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
            type_parameters.extend(parameters.iter().map(|parameter| parameter.id));
            let mut checked_requirements = Vec::new();
            checked_requirements
                .try_reserve(requirements.len())
                .map_err(|_| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
            for requirement in requirements {
                checked_requirements.push(CheckedRequirement {
                    id: requirement.id,
                    interface: requirement.interface.id,
                    argument: self.clone_type(&requirement.argument.ty)?,
                    origin: Origin::Source(requirement.span),
                    span: requirement.span,
                });
            }
            let body = match &definition.kind {
                ResolvedDefinitionKind::Equational(equational) => {
                    self.clone_type(&equational.interface.annotation.ty)?
                }
                ResolvedDefinitionKind::InlineOperational(operational) => {
                    let domain = operational_domain(
                        &operational.header.parameters,
                        operational.header.span,
                        &mut self.type_work,
                    )?;
                    let codomain = ProvenancedType::from_resolved_with_budget(
                        &operational.header.result_type,
                        &mut self.type_work,
                    )?;
                    let function = ProvenancedType::function_with_budget(
                        domain,
                        codomain,
                        Some(operational.header.span),
                        &mut self.type_work,
                    )?;
                    function.ty
                }
            };
            let scheme = ConstrainedScheme {
                type_parameters: type_parameters.into_boxed_slice(),
                requirements: checked_requirements.into_boxed_slice(),
                value_type: body,
            };
            checked.0.push(CheckedGlobalScheme {
                binder: name.id,
                spelling: name.spelling.clone(),
                scheme,
                origin: name.origin.clone(),
            });
        }
        Ok(checked.into_vec())
    }

    /// Consumes the elaborator and selects the program root for validation.
    ///
    /// # Errors
    ///
    /// Returns a Core construction failure unless `root` belongs to this
    /// elaborator and names one of its allocated nodes. Returns
    /// [`ElaborationFailure::InvalidState`] if an earlier public synthesis or
    /// checking call failed.
    pub fn finish(mut self, root: NodeId) -> Result<UnvalidatedProgram, ElaborationFailure> {
        let root_is_authorized = match self.purpose {
            ElaborationPurpose::Standalone => self.final_root.is_none(),
            ElaborationPurpose::FinalSynthesis => self.final_root == Some(root),
            ElaborationPurpose::ModuleCheck => false,
        };
        if self.state == ElaboratorState::Poisoned || !root_is_authorized {
            return Err(ElaborationFailure::InvalidState);
        }
        if self.builder.requires_type_rewrite() {
            let solutions = &self.inference_solutions;
            let type_work = &mut self.type_work;
            self.builder.rewrite_types(|ty| {
                let (zonked, unresolved) = zonk_type_with_status(ty, solutions, |cells| {
                    type_work
                        .charge(cells)
                        .map_err(|()| BuildError::TypeWorkExceeded)
                })?;
                if unresolved {
                    Err(BuildError::InvalidPayload)
                } else {
                    Ok(zonked)
                }
            })?;
        }
        self.builder.finish(root).map_err(Into::into)
    }

    fn fresh_inference(&mut self, origin: Span) -> Result<Type, TypeError> {
        self.type_work
            .charge(1)
            .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
        self.inference_origins
            .try_reserve(1)
            .map_err(|_| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
        self.fresh_inference_reserved(origin)
    }

    fn fresh_inference_reserved(&mut self, origin: Span) -> Result<Type, TypeError> {
        let identity = InferenceVariableId::new(self.next_inference);
        self.next_inference = self
            .next_inference
            .checked_add(1)
            .ok_or_else(invalid_state)?;
        self.inference_origins.push(origin);
        Ok(Type::Inference(identity))
    }

    fn fresh_type_variable(&mut self) -> Result<TypeVariableId, TypeError> {
        let identity = TypeVariableId::generated(self.next_generated_type_variable);
        self.next_generated_type_variable = self
            .next_generated_type_variable
            .checked_sub(1)
            .ok_or_else(invalid_state)?;
        Ok(identity)
    }

    fn instantiate(
        &mut self,
        fact: &TypeFact,
        rigid: bool,
        origin: Span,
    ) -> Result<(Type, Vec<Type>), TypeError> {
        if fact.quantified.is_empty() {
            return Ok((
                clone_type_with_budget(&fact.ty, &mut self.type_work)
                    .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?,
                Vec::new(),
            ));
        }
        let count = fact.quantified.len();
        self.type_work
            .charge(count.saturating_mul(if rigid { 2 } else { 3 }))
            .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
        let mut replacements = HashMap::new();
        replacements
            .try_reserve(count)
            .map_err(|_| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
        let mut arguments = Vec::new();
        arguments
            .try_reserve(count)
            .map_err(|_| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
        if !rigid {
            self.inference_origins
                .try_reserve(count)
                .map_err(|_| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
        }
        for binder in &fact.quantified {
            let argument = if rigid {
                Type::Variable(*binder)
            } else {
                self.fresh_inference_reserved(origin)?
            };
            replacements.insert(*binder, argument.clone());
            arguments.push(argument);
        }
        let instantiated = substitute_type_variables_with(&fact.ty, &replacements, |cells| {
            self.type_work.charge(cells)
        })
        .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
        Ok((instantiated, arguments))
    }

    fn enter_global_evidence_scope(&mut self, binder: BinderId) -> Result<usize, TypeError> {
        if self.purpose != ElaborationPurpose::ModuleCheck {
            return Err(invalid_state());
        }
        let selector = self.selection.as_mut().ok_or_else(invalid_state)?;
        selector
            .enter_global_scope(binder, &mut self.constraint_work, &mut self.type_work)
            .map_err(|failure| selection_failure(failure, None))?;
        Ok(selector.pending_marker())
    }

    fn enter_implementation_evidence_scope(
        &mut self,
        implementation: ImplId,
    ) -> Result<usize, TypeError> {
        if self.purpose != ElaborationPurpose::ModuleCheck {
            return Err(invalid_state());
        }
        let selector = self.selection.as_mut().ok_or_else(invalid_state)?;
        selector
            .enter_implementation_scope(
                implementation,
                &mut self.constraint_work,
                &mut self.type_work,
            )
            .map_err(|failure| selection_failure(failure, None))?;
        Ok(selector.pending_marker())
    }

    fn evidence_marker(&self) -> Result<usize, TypeError> {
        if self.purpose != ElaborationPurpose::ModuleCheck {
            return Err(invalid_state());
        }
        self.selection
            .as_ref()
            .map(EvidenceSelector::pending_marker)
            .ok_or_else(invalid_state)
    }

    fn leave_evidence_scope(&mut self) -> Result<(), TypeError> {
        if self.purpose != ElaborationPurpose::ModuleCheck {
            return Err(invalid_state());
        }
        self.selection
            .as_mut()
            .ok_or_else(invalid_state)?
            .clear_scope();
        Ok(())
    }

    fn close_evidence_obligations(&mut self, marker: usize) -> Result<(), TypeError> {
        if self.purpose != ElaborationPurpose::ModuleCheck {
            return Err(invalid_state());
        }
        let mut selector = self.selection.take().ok_or_else(invalid_state)?;
        let solutions = &self.inference_solutions;
        let result = selector.close(
            marker,
            |argument, type_work| {
                let zonked =
                    zonk_type_with_status(&argument, solutions, |cells| type_work.charge(cells));
                discard_type_iteratively(argument);
                zonked
                    .map(|(ty, _)| ty)
                    .map_err(|()| SelectionFailure::TypeResource)
            },
            &mut self.constraint_work,
            &mut self.type_work,
        );
        self.selection = Some(selector);
        result.map_err(selected_obligation_error)
    }

    fn record_global_obligations(
        &mut self,
        binder: BinderId,
        occurrence: &crate::resolved::ResolvedOccurrence,
        arguments: &[Type],
        span: Span,
    ) -> Result<(), TypeError> {
        if self.purpose != ElaborationPurpose::ModuleCheck {
            return if occurrence.evidence.is_empty() {
                Ok(())
            } else {
                Err(invalid_state())
            };
        }
        if self.selection.is_none() {
            return if occurrence.evidence.is_empty() {
                Ok(())
            } else {
                Err(invalid_state())
            };
        }
        let mut selector = self.selection.take().ok_or_else(invalid_state)?;
        let result = (|| {
            let mut replacements = TypeReplacementBuffer(HashMap::new());
            let requirement_count = {
                let Some(scheme) = selector.scheme(binder) else {
                    return if occurrence.evidence.is_empty() {
                        Ok(())
                    } else {
                        Err(invalid_state())
                    };
                };
                if scheme.type_parameters.len() != arguments.len()
                    || scheme.requirements.len() != occurrence.evidence.len()
                {
                    return Err(invalid_state());
                }
                self.type_work
                    .charge(scheme.type_parameters.len())
                    .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
                replacements
                    .0
                    .try_reserve(scheme.type_parameters.len())
                    .map_err(|_| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
                for (parameter, argument) in scheme.type_parameters.iter().zip(arguments) {
                    if replacements
                        .0
                        .insert(*parameter, self.clone_type(argument)?)
                        .is_some()
                    {
                        return Err(invalid_state());
                    }
                }
                scheme.requirements.len()
            };
            let declaration_span = selector
                .scheme_declaration_span(binder)
                .ok_or_else(invalid_state)?;
            for (index, slot) in occurrence.evidence.iter().enumerate() {
                if index >= requirement_count {
                    return Err(invalid_state());
                }
                let (interface, argument) = {
                    let scheme = selector.scheme(binder).ok_or_else(invalid_state)?;
                    let requirement = scheme.requirements.get(index).ok_or_else(invalid_state)?;
                    let argument = substitute_type_variables_with(
                        &requirement.argument,
                        &replacements.0,
                        |cells| self.type_work.charge(cells),
                    )
                    .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
                    (requirement.interface, argument)
                };
                selector
                    .push_owned_obligation(
                        interface,
                        argument,
                        SelectionSite::contextual(
                            slot.handle(),
                            span,
                            declaration_span,
                            occurrence.import_span(),
                        ),
                        &mut self.constraint_work,
                    )
                    .map_err(|failure| selection_failure(failure, Some(span)))?;
            }
            Ok(())
        })();
        self.selection = Some(selector);
        result
    }

    fn synthesize_method_occurrence(
        &mut self,
        method: MethodId,
        occurrence: &crate::resolved::ResolvedOccurrence,
        span: Span,
    ) -> Result<TypedNode, TypeError> {
        if self.purpose != ElaborationPurpose::ModuleCheck || occurrence.evidence.len() != 1 {
            return Err(invalid_state());
        }
        let mut selector = self.selection.take().ok_or_else(invalid_state)?;
        let result = (|| {
            let method_fact = selector.method(method).ok_or_else(invalid_state)?;
            let interface = method_fact.interface();
            let parameter = method_fact.interface_parameter();
            let value_type = self.clone_type(method_fact.value_type())?;
            let method_span = method_fact.declaration_span();
            let fact = TypeFact {
                provenance: TypeProvenance::at_span(&value_type, method_span),
                ty: value_type,
                quantified: vec![parameter].into_boxed_slice(),
            };
            let (ty, arguments) = self.instantiate(&fact, false, span)?;
            let [argument] = arguments.as_slice() else {
                return Err(invalid_state());
            };
            selector
                .push_cloned_obligation(
                    interface,
                    argument,
                    SelectionSite::contextual(
                        occurrence.evidence[0].handle(),
                        span,
                        method_span,
                        occurrence.import_span(),
                    ),
                    &mut self.constraint_work,
                    &mut self.type_work,
                )
                .map_err(|failure| selection_failure(failure, Some(span)))?;

            self.type_work
                .charge(2)
                .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
            let core_scheme = Type::Forall(
                vec![parameter].into_boxed_slice(),
                Box::new(self.clone_type(&fact.ty)?),
            );
            let binder = if let Some(binder) = self.method_binders.get(&method).copied() {
                binder
            } else {
                self.type_work
                    .charge(1)
                    .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
                self.method_binders
                    .try_reserve(1)
                    .map_err(|_| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
                let binder_type = self.clone_type(&core_scheme)?;
                let typed = self.builder.binder(
                    binder_type,
                    Origin::Generated {
                        cause: Box::new(occurrence.origin.clone()),
                        reason: GeneratedReason::TypeChecking,
                    },
                )?;
                let binder = typed.id();
                if self.method_binders.insert(method, binder).is_some() {
                    return Err(invalid_state());
                }
                binder
            };
            let mut node = self
                .builder
                .variable(binder, core_scheme, occurrence.origin.clone())?;
            let core_ty = self.clone_type(&ty)?;
            node = self.builder.type_application(
                node,
                arguments,
                core_ty,
                occurrence.origin.clone(),
            )?;
            Ok(TypedNode {
                node,
                ty,
                provenance: fact.provenance,
            })
        })();
        self.selection = Some(selector);
        result
    }

    fn synthesize_lowered_method_occurrence(
        &mut self,
        method: MethodId,
        occurrence: &crate::resolved::ResolvedOccurrence,
    ) -> Result<TypedNode, TypeError> {
        let [slot] = occurrence.evidence.as_ref() else {
            return Err(invalid_state());
        };
        let selection = slot.selection().ok_or_else(invalid_state)?;
        if selection.interface() != method.interface() {
            return Err(invalid_state());
        }
        let mut lowering = self.evidence_lowering.take().ok_or_else(invalid_state)?;
        let result = (|| {
            let method_fact = lowering
                .interface_methods
                .get(&method)
                .ok_or_else(invalid_state)?;
            let parameter = method_fact.parameter;
            let declaration_span = method_fact.declaration_span;
            let value_type = self.clone_type(&method_fact.value_type)?;
            let mut replacement = TypeReplacementBuffer(HashMap::new());
            replacement
                .0
                .try_reserve(1)
                .map_err(|_| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
            replacement
                .0
                .insert(parameter, self.clone_type(selection.argument())?);
            let expected = substitute_type_variables_with(&value_type, &replacement.0, |cells| {
                self.type_work.charge(cells)
            })
            .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
            discard_type_iteratively(value_type);
            let mut methods = self.lower_evidence_selection(
                selection,
                &mut lowering,
                &occurrence.origin,
                Some(method),
            )?;
            if methods.len() != 1 {
                return Err(invalid_state());
            }
            let selected = methods.pop().ok_or_else(invalid_state)?;
            if selected.method != method {
                return Err(invalid_state());
            }
            if !same_type(&selected.ty, &expected) {
                discard_type_iteratively(expected);
                return Err(invalid_state());
            }
            discard_type_iteratively(expected);
            Ok(TypedNode {
                node: selected.node,
                provenance: TypeProvenance::at_span(&selected.ty, declaration_span),
                ty: selected.ty,
            })
        })();
        self.evidence_lowering = Some(lowering);
        result
    }

    fn enter_lowered_global_evidence_scope(
        &mut self,
        binder: BinderId,
        cause: &Origin,
    ) -> Result<Vec<ScopedEvidenceBinder>, TypeError> {
        let lowering = self.evidence_lowering.as_ref().ok_or_else(invalid_state)?;
        let scheme = lowering
            .global_schemes
            .get(&binder)
            .ok_or_else(invalid_state)?;
        let mut specifications = Vec::new();
        let method_count = scheme
            .requirements
            .iter()
            .map(|requirement| requirement.methods.len())
            .sum();
        specifications
            .try_reserve(method_count)
            .map_err(|_| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
        for requirement in &scheme.requirements {
            for method in &requirement.methods {
                specifications.push((
                    requirement.id,
                    method.method,
                    clone_type_with_budget(&method.ty, &mut self.type_work).map_err(|()| {
                        TypeError::Internal(ElaborationFailure::TypeResourceExhausted)
                    })?,
                ));
            }
        }
        self.enter_lowered_evidence_specifications(specifications, cause)
    }

    fn enter_lowered_implementation_evidence_scope(
        &mut self,
        method: ImplMethodId,
        cause: &Origin,
    ) -> Result<Vec<ScopedEvidenceBinder>, TypeError> {
        let lowering = self.evidence_lowering.as_ref().ok_or_else(invalid_state)?;
        let scheme = &lowering
            .implementation_methods
            .get(&method)
            .ok_or_else(invalid_state)?
            .scheme;
        let mut specifications = Vec::new();
        let method_count = scheme
            .requirements
            .iter()
            .map(|requirement| requirement.methods.len())
            .sum();
        specifications
            .try_reserve(method_count)
            .map_err(|_| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
        for requirement in &scheme.requirements {
            for method in &requirement.methods {
                specifications.push((
                    requirement.id,
                    method.method,
                    clone_type_with_budget(&method.ty, &mut self.type_work).map_err(|()| {
                        TypeError::Internal(ElaborationFailure::TypeResourceExhausted)
                    })?,
                ));
            }
        }
        self.enter_lowered_evidence_specifications(specifications, cause)
    }

    fn enter_lowered_evidence_specifications(
        &mut self,
        specifications: Vec<(RequirementId, MethodId, Type)>,
        cause: &Origin,
    ) -> Result<Vec<ScopedEvidenceBinder>, TypeError> {
        {
            let lowering = self.evidence_lowering.as_mut().ok_or_else(invalid_state)?;
            if !lowering.active_binders.is_empty() {
                return Err(invalid_state());
            }
            lowering
                .active_binders
                .try_reserve(specifications.len())
                .map_err(|_| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
        }
        let mut binders = Vec::new();
        binders
            .try_reserve(specifications.len())
            .map_err(|_| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
        for (requirement, method, ty) in specifications {
            let binder_ty = self.clone_type(&ty)?;
            let binder = self.builder.binder(
                binder_ty,
                Origin::Generated {
                    cause: Box::new(cause.clone()),
                    reason: GeneratedReason::TypeChecking,
                },
            )?;
            let active = ActiveEvidenceBinder {
                binder: binder.id(),
                ty,
            };
            if self
                .evidence_lowering
                .as_mut()
                .ok_or_else(invalid_state)?
                .active_binders
                .insert((requirement, method), active)
                .is_some()
            {
                return Err(invalid_state());
            }
            binders.push(ScopedEvidenceBinder {
                requirement,
                method,
                binder,
            });
        }
        Ok(binders)
    }

    fn wrap_lowered_evidence_scope(
        &mut self,
        mut function: TypedNode,
        binders: Vec<ScopedEvidenceBinder>,
        cause: &Origin,
    ) -> Result<TypedNode, TypeError> {
        for scoped in binders.into_iter().rev() {
            let active = self
                .evidence_lowering
                .as_mut()
                .ok_or_else(invalid_state)?
                .active_binders
                .remove(&(scoped.requirement, scoped.method))
                .ok_or_else(invalid_state)?;
            if active.binder != scoped.binder.id() || !same_type(&active.ty, scoped.binder.ty()) {
                return Err(invalid_state());
            }
            let domain = self.clone_type(scoped.binder.ty())?;
            let codomain = self.clone_type(&function.ty)?;
            let ty = Type::Function(Box::new(domain), Box::new(codomain));
            let core_ty = self.clone_type(&ty)?;
            function.node = self.builder.function(
                scoped.binder,
                function.node,
                core_ty,
                Origin::Generated {
                    cause: Box::new(cause.clone()),
                    reason: GeneratedReason::TypeChecking,
                },
            )?;
            function.ty = ty;
            function.provenance = TypeProvenance::at_span(&function.ty, cause.primary_span());
        }
        if !self
            .evidence_lowering
            .as_ref()
            .ok_or_else(invalid_state)?
            .active_binders
            .is_empty()
        {
            return Err(invalid_state());
        }
        Ok(function)
    }

    fn clear_lowered_evidence_scope(
        &mut self,
        binders: Vec<ScopedEvidenceBinder>,
    ) -> Result<(), TypeError> {
        let lowering = self.evidence_lowering.as_mut().ok_or_else(invalid_state)?;
        for scoped in binders {
            let active = lowering
                .active_binders
                .remove(&(scoped.requirement, scoped.method))
                .ok_or_else(invalid_state)?;
            if active.binder != scoped.binder.id() {
                return Err(invalid_state());
            }
        }
        if lowering.active_binders.is_empty() {
            Ok(())
        } else {
            Err(invalid_state())
        }
    }

    fn instantiate_lowered_core_body(
        &mut self,
        scheme: &LoweredScheme,
        arguments: &[Type],
    ) -> Result<Type, TypeError> {
        if scheme.type_parameters.len() != arguments.len() {
            return Err(invalid_state());
        }
        if arguments.is_empty() {
            return self.clone_type(&scheme.core_scheme);
        }
        let Type::Forall(parameters, body) = &scheme.core_scheme else {
            return Err(invalid_state());
        };
        if parameters.as_ref() != scheme.type_parameters.as_ref() {
            return Err(invalid_state());
        }
        self.type_work
            .charge(arguments.len())
            .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
        let mut replacements = TypeReplacementBuffer(HashMap::new());
        replacements
            .0
            .try_reserve(arguments.len())
            .map_err(|_| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
        for (parameter, argument) in parameters.iter().zip(arguments) {
            if replacements
                .0
                .insert(*parameter, self.clone_type(argument)?)
                .is_some()
            {
                return Err(invalid_state());
            }
        }
        substitute_type_variables_with(body, &replacements.0, |cells| self.type_work.charge(cells))
            .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))
    }

    fn apply_lowered_argument(
        &mut self,
        function: TypedNode,
        argument: &LoweredEvidenceMethod,
        origin: &Origin,
    ) -> Result<TypedNode, TypeError> {
        let Type::Function(domain, codomain) = &function.ty else {
            return Err(invalid_state());
        };
        match self.unify(domain, &argument.ty) {
            Ok(()) => {}
            Err(UnificationFailure::Mismatch | UnificationFailure::Infinite) => {
                return Err(invalid_state());
            }
            Err(UnificationFailure::Resource) => {
                return Err(TypeError::Internal(
                    ElaborationFailure::TypeResourceExhausted,
                ));
            }
        }
        let ty = self.clone_type(codomain)?;
        let core_ty = self.clone_type(&ty)?;
        let node =
            self.builder
                .application(function.node, argument.node, core_ty, origin.clone())?;
        let provenance = TypeProvenance::at_span(&ty, origin.primary_span());
        Ok(TypedNode {
            node,
            ty,
            provenance,
        })
    }

    fn lower_evidence_selection(
        &mut self,
        selection: &EvidenceSelection,
        lowering: &mut EvidenceLowering,
        origin: &Origin,
        root_method: Option<MethodId>,
    ) -> Result<Vec<LoweredEvidenceMethod>, TypeError> {
        enum Task {
            Visit(crate::interface::EvidenceNodeId),
            Build(crate::interface::EvidenceNodeId),
        }

        let mut tasks = vec![Task::Visit(selection.root())];
        let mut values: HashMap<crate::interface::EvidenceNodeId, Vec<LoweredEvidenceMethod>> =
            HashMap::new();
        values
            .try_reserve(selection.node_count())
            .map_err(|_| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
        while let Some(task) = tasks.pop() {
            match task {
                Task::Visit(node) => {
                    if values.contains_key(&node) {
                        continue;
                    }
                    let evidence = selection.node(node).ok_or_else(invalid_state)?;
                    tasks.push(Task::Build(node));
                    if let EvidenceNode::Implementation { prerequisites, .. } = evidence {
                        tasks.try_reserve(prerequisites.len()).map_err(|_| {
                            TypeError::Internal(ElaborationFailure::TypeResourceExhausted)
                        })?;
                        tasks.extend(prerequisites.iter().rev().copied().map(Task::Visit));
                    }
                }
                Task::Build(node) => {
                    if values.contains_key(&node) {
                        continue;
                    }
                    let methods = match selection.node(node).ok_or_else(invalid_state)? {
                        EvidenceNode::Abstract {
                            requirement,
                            methods,
                        } => {
                            let requested =
                                (node == selection.root()).then_some(root_method).flatten();
                            let mut results = Vec::new();
                            results
                                .try_reserve(requested.map_or(methods.len(), |_| 1))
                                .map_err(|_| {
                                    TypeError::Internal(ElaborationFailure::TypeResourceExhausted)
                                })?;
                            for method in methods {
                                if requested.is_some_and(|requested| requested != *method) {
                                    continue;
                                }
                                let active = lowering
                                    .active_binders
                                    .get(&(requirement, *method))
                                    .ok_or_else(invalid_state)?;
                                let ty = self.clone_type(&active.ty)?;
                                let core_ty = self.clone_type(&ty)?;
                                let node = self.builder.variable(
                                    active.binder,
                                    core_ty,
                                    origin.clone(),
                                )?;
                                results.push(LoweredEvidenceMethod {
                                    method: *method,
                                    node,
                                    ty,
                                });
                            }
                            results
                        }
                        EvidenceNode::Implementation {
                            implementation: _,
                            substitution,
                            prerequisites,
                            methods,
                        } => {
                            let requested =
                                (node == selection.root()).then_some(root_method).flatten();
                            let mut results = Vec::new();
                            results
                                .try_reserve(requested.map_or(methods.len(), |_| 1))
                                .map_err(|_| {
                                    TypeError::Internal(ElaborationFailure::TypeResourceExhausted)
                                })?;
                            for method in methods {
                                if requested.is_some_and(|requested| requested != method.method()) {
                                    continue;
                                }
                                let lowered = lowering
                                    .implementation_methods
                                    .get(method)
                                    .ok_or_else(invalid_state)?;
                                let source_parameters = lowered
                                    .scheme
                                    .source_type_parameters
                                    .as_deref()
                                    .ok_or_else(invalid_state)?;
                                if source_parameters.len() != substitution.len()
                                    || source_parameters.iter().zip(substitution).any(
                                        |(parameter, substitution)| {
                                            *parameter != substitution.parameter()
                                        },
                                    )
                                {
                                    return Err(invalid_state());
                                }
                                let core_scheme = self.clone_type(&lowered.scheme.core_scheme)?;
                                let variable_ty = self.clone_type(&core_scheme)?;
                                let mut current = TypedNode {
                                    node: self.builder.variable(
                                        lowered.binder,
                                        variable_ty,
                                        origin.clone(),
                                    )?,
                                    ty: core_scheme,
                                    provenance: TypeProvenance::at_span(
                                        &lowered.scheme.value_type,
                                        lowered.span,
                                    ),
                                };
                                if !substitution.is_empty() {
                                    let mut arguments = Vec::new();
                                    arguments.try_reserve(substitution.len()).map_err(|_| {
                                        TypeError::Internal(
                                            ElaborationFailure::TypeResourceExhausted,
                                        )
                                    })?;
                                    for substitution in substitution {
                                        arguments.push(self.clone_type(substitution.argument())?);
                                    }
                                    let instantiated = self.instantiate_lowered_core_body(
                                        &lowered.scheme,
                                        &arguments,
                                    )?;
                                    let core_ty = self.clone_type(&instantiated)?;
                                    current.node = self.builder.type_application(
                                        current.node,
                                        arguments,
                                        core_ty,
                                        origin.clone(),
                                    )?;
                                    current.ty = instantiated;
                                }
                                for prerequisite in prerequisites {
                                    let prerequisite_methods =
                                        values.get(prerequisite).ok_or_else(invalid_state)?;
                                    for argument in prerequisite_methods {
                                        current =
                                            self.apply_lowered_argument(current, argument, origin)?;
                                    }
                                }
                                results.push(LoweredEvidenceMethod {
                                    method: method.method(),
                                    node: current.node,
                                    ty: current.ty,
                                });
                            }
                            results
                        }
                    };
                    if values.insert(node, methods).is_some() {
                        return Err(invalid_state());
                    }
                }
            }
        }
        values.remove(&selection.root()).ok_or_else(invalid_state)
    }

    fn zonk(&mut self, ty: &Type) -> Result<Type, TypeError> {
        self.zonk_with_status(ty).map(|(ty, _)| ty)
    }

    fn zonk_owned(&mut self, ty: Type) -> Result<Type, TypeError> {
        if self.next_inference == 0 {
            Ok(ty)
        } else {
            self.zonk(&ty)
        }
    }

    fn zonk_with_status(&mut self, ty: &Type) -> Result<(Type, bool), TypeError> {
        zonk_type_with_status(ty, &self.inference_solutions, |cells| {
            self.type_work.charge(cells)
        })
        .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))
    }

    fn charge_type(&mut self, ty: &Type) -> Result<(), TypeError> {
        charge_type_cells(ty, &mut self.type_work)
            .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))
    }

    fn clone_type(&mut self, ty: &Type) -> Result<Type, TypeError> {
        clone_type_with_budget(ty, &mut self.type_work)
            .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))
    }

    fn unknown_provenance(&mut self, ty: &Type) -> Result<TypeProvenance, TypeError> {
        unknown_provenance_with_budget(ty, &mut self.type_work)
            .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))
    }

    fn admit_public_context(&mut self, context: &TypeContext) -> Result<(), TypeError> {
        self.type_work
            .charge(context.binders.len())
            .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
        let mut invalid = false;
        for fact in context.binders.values() {
            if !fact.quantified.is_empty() {
                invalid = true;
            }
            match validate_and_charge_public_monotype(&fact.ty, &mut self.type_work) {
                Ok(()) => {}
                Err(PublicTypeAdmissionError::Invalid) => invalid = true,
                Err(PublicTypeAdmissionError::Resource) => {
                    return Err(TypeError::Internal(
                        ElaborationFailure::TypeResourceExhausted,
                    ));
                }
            }
        }
        if invalid {
            Err(invalid_state())
        } else {
            Ok(())
        }
    }

    fn admit_public_monotype(&mut self, ty: &Type) -> Result<(), TypeError> {
        validate_and_charge_public_monotype(ty, &mut self.type_work).map_err(|error| match error {
            PublicTypeAdmissionError::Invalid => invalid_state(),
            PublicTypeAdmissionError::Resource => {
                TypeError::Internal(ElaborationFailure::TypeResourceExhausted)
            }
        })
    }

    fn unify(&mut self, left: &Type, right: &Type) -> Result<(), UnificationFailure> {
        if let Some(equal) = compare_concrete_types(left, right, &mut self.type_work)
            .map_err(|()| UnificationFailure::Resource)?
        {
            return if equal {
                Ok(())
            } else {
                Err(UnificationFailure::Mismatch)
            };
        }

        enum Task {
            Pair(Type, Type),
            Sequence(std::vec::IntoIter<Type>, std::vec::IntoIter<Type>),
        }

        let left = clone_type_with_budget(left, &mut self.type_work)
            .map_err(|()| UnificationFailure::Resource)?;
        let right = clone_type_with_budget(right, &mut self.type_work)
            .map_err(|()| UnificationFailure::Resource)?;
        let mut work = vec![Task::Pair(left, right)];
        while let Some(task) = work.pop() {
            let (left, right) = match task {
                Task::Pair(left, right) => (left, right),
                Task::Sequence(mut left_types, mut right_types) => {
                    match (left_types.next(), right_types.next()) {
                        (Some(left), Some(right)) => {
                            work.push(Task::Sequence(left_types, right_types));
                            work.push(Task::Pair(left, right));
                            continue;
                        }
                        (None, None) => continue,
                        _ => return Err(UnificationFailure::Mismatch),
                    }
                }
            };
            let left = self.zonk(&left).map_err(|_| UnificationFailure::Resource)?;
            let right = self
                .zonk(&right)
                .map_err(|_| UnificationFailure::Resource)?;
            match (left, right) {
                (Type::Inference(left), Type::Inference(right)) if left == right => {}
                (Type::Inference(variable), ty) | (ty, Type::Inference(variable)) => {
                    self.charge_type(&ty)
                        .map_err(|_| UnificationFailure::Resource)?;
                    if type_contains_inference(&ty, variable, &self.inference_solutions) {
                        return Err(UnificationFailure::Infinite);
                    }
                    self.type_work
                        .charge(1)
                        .map_err(|()| UnificationFailure::Resource)?;
                    self.inference_solutions
                        .try_reserve(1)
                        .map_err(|_| UnificationFailure::Resource)?;
                    self.inference_solutions.insert(variable, ty);
                }
                (Type::Int, Type::Int) | (Type::Bool, Type::Bool) | (Type::Unit, Type::Unit) => {}
                (Type::Nominal(left), Type::Nominal(right)) if left == right => {}
                (Type::Variable(left), Type::Variable(right)) if left == right => {}
                (Type::AppliedNominal(left_id, left), Type::AppliedNominal(right_id, right))
                    if left_id == right_id && left.len() == right.len() =>
                {
                    work.push(Task::Sequence(
                        left.into_vec().into_iter(),
                        right.into_vec().into_iter(),
                    ));
                }
                (Type::Tuple(left), Type::Tuple(right)) if left.len() == right.len() => {
                    work.push(Task::Sequence(
                        left.into_vec().into_iter(),
                        right.into_vec().into_iter(),
                    ));
                }
                (
                    Type::Function(left_domain, left_codomain),
                    Type::Function(right_domain, right_codomain),
                ) => {
                    work.push(Task::Pair(*left_codomain, *right_codomain));
                    work.push(Task::Pair(*left_domain, *right_domain));
                }
                _ => return Err(UnificationFailure::Mismatch),
            }
        }
        Ok(())
    }

    fn expose_expected_function(
        &mut self,
        expected: ProvenancedType,
        span: Span,
    ) -> Result<ProvenancedType, TypeError> {
        match &expected.ty {
            Type::Function(_, _) => Ok(expected),
            Type::Inference(_) => {
                let expected_ty = self.zonk(&expected.ty)?;
                if matches!(expected_ty, Type::Function(_, _)) {
                    let provenance = if expected.provenance.aligns(&expected_ty) {
                        expected.provenance
                    } else {
                        self.unknown_provenance(&expected_ty)?
                    };
                    return Ok(ProvenancedType {
                        ty: expected_ty,
                        provenance,
                    });
                }
                if !matches!(expected_ty, Type::Inference(_)) {
                    return Err(function_needs_context(span, None));
                }
                self.type_work
                    .charge(3)
                    .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
                let domain = self.fresh_inference(span)?;
                let codomain = self.fresh_inference(span)?;
                let exposed = Type::Function(Box::new(domain), Box::new(codomain));
                self.unify(&expected_ty, &exposed)
                    .map_err(|failure| match failure {
                        UnificationFailure::Infinite => inference_failure(
                            TypeReason::InfiniteType,
                            span,
                            "this function context would require an infinite type",
                        ),
                        UnificationFailure::Mismatch => function_needs_context(span, None),
                        UnificationFailure::Resource => {
                            TypeError::Internal(ElaborationFailure::TypeResourceExhausted)
                        }
                    })?;
                let provenance = self.unknown_provenance(&exposed)?;
                Ok(ProvenancedType {
                    ty: exposed,
                    provenance,
                })
            }
            _ => Err(function_needs_context(span, None)),
        }
    }

    fn require_integer(
        &mut self,
        operand: &TypedNode,
        operand_span: Span,
        operator_span: Span,
    ) -> Result<(), TypeError> {
        match self.unify(&operand.ty, &Type::Int) {
            Ok(()) => Ok(()),
            Err(UnificationFailure::Mismatch) => {
                let found = self.zonk(&operand.ty)?;
                let mut diagnostic = Diagnostic::new(
                    TypeReason::OperatorOperand,
                    SourceLabel::new(operand_span, "this operand is not an Int"),
                );
                diagnostic.related.push(SourceLabel::new(
                    operator_span,
                    "this primitive operator requires Int operands",
                ));
                diagnostic.expected = Some(Type::Int.to_string());
                diagnostic.found = Some(self.registry.display_source_type(&found));
                Err(TypeError::Source(Box::new(diagnostic)))
            }
            Err(UnificationFailure::Infinite) => Err(inference_failure(
                TypeReason::InfiniteType,
                operand_span,
                "this primitive operand would require an infinite type",
            )),
            Err(UnificationFailure::Resource) => Err(TypeError::Internal(
                ElaborationFailure::TypeResourceExhausted,
            )),
        }
    }

    fn refine_pattern_expected(
        &mut self,
        expected: &Type,
        required: &Type,
        span: Span,
    ) -> Result<Type, TypeError> {
        match self.unify(expected, required) {
            Ok(()) => self.zonk(required),
            Err(UnificationFailure::Mismatch) => {
                let expected = self.zonk(expected)?;
                Err(pattern_mismatch(span, &expected, &self.registry))
            }
            Err(UnificationFailure::Infinite) => Err(inference_failure(
                TypeReason::InfiniteType,
                span,
                "this pattern would require an infinite type",
            )),
            Err(UnificationFailure::Resource) => Err(TypeError::Internal(
                ElaborationFailure::TypeResourceExhausted,
            )),
        }
    }

    fn elaborate_module_program(
        &mut self,
        program: &ValidatedInterfaceProgram,
    ) -> Result<TypedNode, TypeError> {
        let mut context = TypeContext::new();
        let mut groups = Vec::with_capacity(program.groups().len());
        for group in program.groups() {
            let (members, next_context) = self.elaborate_checked_module_group(group, context)?;
            context = next_context;
            groups.push((members, group.span()));
        }
        let mut result = self.elaborate_result(program.result(), &mut context)?;
        for (members, span) in groups.into_iter().rev() {
            if members.is_empty() {
                continue;
            }
            let members = members
                .into_iter()
                .map(|member| (member.binder, member.initializer))
                .collect();
            let result_type = self.clone_type(&result.ty)?;
            result.node = self.builder.recursive_binding(
                members,
                result.node,
                result_type,
                Origin::Generated {
                    cause: Box::new(Origin::Source(span)),
                    reason: GeneratedReason::RecursiveBindingLowering,
                },
            )?;
        }
        Ok(result)
    }

    fn elaborate_checked_module_group(
        &mut self,
        group: &ResolvedModuleGroup,
        context: TypeContext,
    ) -> Result<(Vec<ElaboratedBinding>, TypeContext), TypeError> {
        let mut prepared = self.prepare_definition_views(
            group.definitions().iter(),
            Some(group.schemes()),
            context,
        )?;
        self.prepare_implementation_method_views(group, &mut prepared)?;
        let mut next_global = 0usize;
        let mut next_implementation = 0usize;
        for declaration in group.declaration_order() {
            match *declaration {
                ResolvedDeclarationIndex::Global(index) if index == next_global => {
                    let definition = group.definitions().get(index).ok_or_else(invalid_state)?;
                    self.elaborate_prepared_definition(definition, &mut prepared)?;
                    next_global = next_global.checked_add(1).ok_or_else(invalid_state)?;
                }
                ResolvedDeclarationIndex::Implementation(index) if index == next_implementation => {
                    self.elaborate_prepared_implementation(group, index, &mut prepared)?;
                    next_implementation = next_implementation
                        .checked_add(1)
                        .ok_or_else(invalid_state)?;
                }
                ResolvedDeclarationIndex::Type(_) | ResolvedDeclarationIndex::Interface(_) => {}
                ResolvedDeclarationIndex::Global(_)
                | ResolvedDeclarationIndex::Implementation(_) => return Err(invalid_state()),
            }
        }
        if next_global != group.definitions().len()
            || next_implementation != group.implementations().len()
        {
            return Err(invalid_state());
        }
        self.finish_prepared_definitions(prepared)
    }

    fn prepare_implementation_method_views(
        &mut self,
        group: &ResolvedModuleGroup,
        prepared: &mut PreparedGlobals,
    ) -> Result<(), TypeError> {
        if group.implementations().len() != group.implementation_facts().len() {
            return Err(invalid_state());
        }
        let method_count: usize = group
            .implementation_facts()
            .iter()
            .map(|implementation| implementation.methods.len())
            .sum();
        prepared
            .globals
            .try_reserve(method_count)
            .map_err(|_| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
        prepared
            .binders
            .try_reserve(method_count)
            .map_err(|_| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
        prepared
            .quantifiers
            .try_reserve(method_count)
            .map_err(|_| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
        for (implementation, fact) in group
            .implementations()
            .iter()
            .zip(group.implementation_facts())
        {
            if implementation.id() != fact.id {
                return Err(invalid_state());
            }
            for method in &fact.methods {
                let lowered = self
                    .evidence_lowering
                    .as_ref()
                    .and_then(|lowering| lowering.implementation_methods.get(&method.id))
                    .ok_or_else(invalid_state)?;
                if lowered.binder != method.binder
                    || lowered.scheme.source_type_parameters.as_deref()
                        != Some(method.scheme.type_parameters.as_ref())
                    || !same_type(&lowered.scheme.value_type, &method.scheme.value_type)
                {
                    return Err(invalid_state());
                }
                let binder_ty =
                    clone_type_with_budget(&lowered.scheme.core_scheme, &mut self.type_work)
                        .map_err(|()| {
                            TypeError::Internal(ElaborationFailure::TypeResourceExhausted)
                        })?;
                let binder = self.builder.resolved_binder(
                    method.binder,
                    binder_ty,
                    method.origin.clone(),
                )?;
                let source_ty =
                    clone_type_with_budget(&lowered.scheme.value_type, &mut self.type_work)
                        .map_err(|()| {
                            TypeError::Internal(ElaborationFailure::TypeResourceExhausted)
                        })?;
                let provenance = TypeProvenance::at_span(&source_ty, method.span);
                if prepared
                    .context
                    .insert_with_provenance(method.binder, source_ty, provenance)?
                    .is_some()
                    || prepared.binders.insert(method.binder, binder).is_some()
                {
                    return Err(invalid_state());
                }
                let source_quantified = clone_type_variables_with_budget(
                    lowered
                        .scheme
                        .source_type_parameters
                        .as_deref()
                        .ok_or_else(invalid_state)?,
                    &mut self.type_work,
                )
                .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?
                .into_boxed_slice();
                prepared
                    .context
                    .set_quantified(method.binder, source_quantified.clone())?;
                if prepared
                    .quantifiers
                    .insert(method.binder, source_quantified)
                    .is_some()
                {
                    return Err(invalid_state());
                }
            }
        }
        Ok(())
    }

    fn elaborate_prepared_implementation(
        &mut self,
        group: &ResolvedModuleGroup,
        implementation_index: usize,
        prepared: &mut PreparedGlobals,
    ) -> Result<(), TypeError> {
        let implementation = group
            .implementations()
            .get(implementation_index)
            .ok_or_else(invalid_state)?;
        let checked = group
            .checked_implementations()
            .get(implementation_index)
            .ok_or_else(invalid_state)?;
        let fact = group
            .implementation_facts()
            .get(implementation_index)
            .ok_or_else(invalid_state)?;
        if implementation.id() != checked.id
            || implementation.id() != fact.id
            || checked.methods.len() != fact.methods.len()
        {
            return Err(invalid_state());
        }
        for (checked_method, fact_method) in checked.methods.iter().zip(&fact.methods) {
            let source = implementation
                .method_groups()
                .get(checked_method.source_group)
                .ok_or_else(invalid_state)?;
            if checked_method.id != fact_method.id
                || checked_method.binder != fact_method.binder
                || source.identity != Some(fact_method.id)
                || source.binder.id != fact_method.binder
            {
                return Err(invalid_state());
            }
            self.elaborate_prepared_implementation_method(source, fact_method, prepared)?;
        }
        Ok(())
    }

    fn elaborate_prepared_implementation_method(
        &mut self,
        source: &crate::resolved::ResolvedImplementationMethodGroup,
        fact: &CheckedImplementationMethodFact,
        prepared: &mut PreparedGlobals,
    ) -> Result<(), TypeError> {
        if !self.monomorphic_recursive.insert(fact.binder) {
            return Err(invalid_state());
        }
        let rewrite_checkpoint = self.builder.type_rewrite_checkpoint();
        let mut core_type_replacements = TypeReplacementBuffer(HashMap::new());
        {
            let lowered = self
                .evidence_lowering
                .as_ref()
                .and_then(|lowering| lowering.implementation_methods.get(&fact.id))
                .ok_or_else(invalid_state)?;
            let source_type_parameters = lowered
                .scheme
                .source_type_parameters
                .as_deref()
                .ok_or_else(invalid_state)?;
            if source_type_parameters.len() != lowered.scheme.type_parameters.len() {
                return Err(invalid_state());
            }
            self.type_work
                .charge(lowered.scheme.type_parameters.len())
                .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
            core_type_replacements
                .0
                .try_reserve(lowered.scheme.type_parameters.len())
                .map_err(|_| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
            for (source, core) in source_type_parameters
                .iter()
                .zip(&lowered.scheme.type_parameters)
            {
                if core_type_replacements
                    .0
                    .insert(*source, Type::Variable(*core))
                    .is_some()
                {
                    return Err(invalid_state());
                }
            }
        }
        let evidence = self.enter_lowered_implementation_evidence_scope(fact.id, &fact.origin)?;
        let source_ty = self
            .evidence_lowering
            .as_ref()
            .and_then(|lowering| lowering.implementation_methods.get(&fact.id))
            .map(|method| &method.scheme.value_type)
            .ok_or_else(invalid_state)?;
        let function_type = clone_type_with_budget(source_ty, &mut self.type_work)
            .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
        let body_result = self.elaborate_equations(
            &source.equations,
            ProvenancedType {
                provenance: TypeProvenance::at_span(&function_type, fact.span),
                ty: function_type,
            },
            &mut prepared.context,
            source.span,
            &fact.origin,
        );
        let mut function = match body_result {
            Ok(function) => function,
            Err(error) => {
                self.clear_lowered_evidence_scope(evidence)?;
                self.monomorphic_recursive.remove(&fact.binder);
                return Err(error);
            }
        };
        function = self.wrap_lowered_evidence_scope(function, evidence, &fact.origin)?;
        if !core_type_replacements.0.is_empty() {
            let inference_solutions = &self.inference_solutions;
            let type_work = &mut self.type_work;
            self.builder.rewrite_types_since(rewrite_checkpoint, |ty| {
                let (zonked, _) = zonk_type_with_status(ty, inference_solutions, |cells| {
                    type_work
                        .charge(cells)
                        .map_err(|()| BuildError::TypeWorkExceeded)
                })?;
                let renamed =
                    substitute_type_variables_with(&zonked, &core_type_replacements.0, |cells| {
                        type_work
                            .charge(cells)
                            .map_err(|()| BuildError::TypeWorkExceeded)
                    });
                discard_type_iteratively(zonked);
                renamed
            })?;
            let zonked_function_type = self.zonk(&function.ty)?;
            let renamed_function_type = substitute_type_variables_with(
                &zonked_function_type,
                &core_type_replacements.0,
                |cells| self.type_work.charge(cells),
            )
            .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
            discard_type_iteratively(zonked_function_type);
            let source_function_type = std::mem::replace(&mut function.ty, renamed_function_type);
            discard_type_iteratively(source_function_type);
        }
        if !self.monomorphic_recursive.remove(&fact.binder) {
            return Err(invalid_state());
        }
        let lowered = self
            .evidence_lowering
            .as_ref()
            .and_then(|lowering| lowering.implementation_methods.get(&fact.id))
            .ok_or_else(invalid_state)?;
        if lowered.scheme.type_parameters.is_empty() {
            if !same_type(&function.ty, &lowered.scheme.core_scheme) {
                return Err(invalid_state());
            }
        } else {
            let Type::Forall(_, expected_body) = &lowered.scheme.core_scheme else {
                return Err(invalid_state());
            };
            if !same_type(&function.ty, expected_body) {
                return Err(invalid_state());
            }
            let parameters = clone_type_variables_with_budget(
                &lowered.scheme.type_parameters,
                &mut self.type_work,
            )
            .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
            let core_scheme =
                clone_type_with_budget(&lowered.scheme.core_scheme, &mut self.type_work)
                    .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
            function.node = self.builder.type_abstraction(
                parameters,
                function.node,
                core_scheme,
                fact.origin.clone(),
            )?;
            function.ty = clone_type_with_budget(&lowered.scheme.core_scheme, &mut self.type_work)
                .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
        }
        let binder = prepared
            .binders
            .remove(&fact.binder)
            .ok_or_else(invalid_state)?;
        prepared.globals.push(ElaboratedBinding {
            binder,
            initializer: function.node,
        });
        Ok(())
    }

    fn prepare_definition_views<'a, I, D>(
        &mut self,
        definitions: I,
        checked_schemes: Option<&[CheckedGlobalScheme]>,
        mut context: TypeContext,
    ) -> Result<PreparedGlobals, TypeError>
    where
        I: Clone + ExactSizeIterator<Item = &'a D>,
        D: DefinitionView + 'a,
    {
        let checked_by_binder = if let Some(checked) = checked_schemes {
            self.type_work
                .charge(checked.len())
                .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
            let mut by_binder = HashMap::new();
            by_binder
                .try_reserve(checked.len())
                .map_err(|_| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
            for scheme in checked {
                if by_binder.insert(scheme.binder, scheme).is_some() {
                    return Err(invalid_state());
                }
            }
            Some(by_binder)
        } else {
            None
        };
        self.type_work
            .charge(definitions.len().saturating_mul(3))
            .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
        let mut globals = Vec::new();
        globals
            .try_reserve(definitions.len())
            .map_err(|_| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
        let mut global_binders = HashMap::new();
        global_binders
            .try_reserve(definitions.len())
            .map_err(|_| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
        let mut global_quantifiers = HashMap::new();
        global_quantifiers
            .try_reserve(definitions.len())
            .map_err(|_| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;

        for definition in definitions.clone() {
            let (name, function_type, type_parameters, requirements) = match definition.kind() {
                ResolvedDefinitionKind::Equational(equational) => {
                    let function_type = ProvenancedType::from_resolved_with_budget(
                        &equational.interface.annotation,
                        &mut self.type_work,
                    )?;
                    if !matches!(function_type.ty, Type::Function(_, _)) {
                        return Err(equation_interface_not_function(
                            &equational.interface.annotation,
                            &equational.equations.first().ok_or_else(invalid_state)?.name,
                            &self.registry,
                        ));
                    }
                    (
                        &equational.interface.name,
                        function_type,
                        equational.interface.type_parameters.as_ref(),
                        equational.interface.requirements.as_ref(),
                    )
                }
                ResolvedDefinitionKind::InlineOperational(operational) => {
                    let domain = operational_domain(
                        &operational.header.parameters,
                        operational.header.span,
                        &mut self.type_work,
                    )?;
                    let codomain = ProvenancedType::from_resolved_with_budget(
                        &operational.header.result_type,
                        &mut self.type_work,
                    )?;
                    (
                        &operational.header.name,
                        ProvenancedType::function_with_budget(
                            domain,
                            codomain,
                            Some(operational.header.span),
                            &mut self.type_work,
                        )?,
                        operational.header.type_parameters.as_ref(),
                        operational.header.requirements.as_ref(),
                    )
                }
            };
            self.type_work
                .charge(type_parameters.len())
                .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
            let mut quantified = Vec::new();
            quantified
                .try_reserve(type_parameters.len())
                .map_err(|_| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
            quantified.extend(type_parameters.iter().map(|parameter| parameter.id));
            let quantified = quantified.into_boxed_slice();
            let binder_body = self.clone_type(&function_type.ty)?;
            let binder_type = if quantified.is_empty() {
                binder_body
            } else {
                self.type_work
                    .charge(1)
                    .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
                let binder_parameters =
                    clone_type_variables_with_budget(&quantified, &mut self.type_work)
                        .map_err(|()| {
                            TypeError::Internal(ElaborationFailure::TypeResourceExhausted)
                        })?
                        .into_boxed_slice();
                Type::Forall(binder_parameters, Box::new(binder_body))
            };
            let binder_type = if let Some(checked) = &checked_by_binder {
                let checked = checked.get(&name.id).ok_or_else(invalid_state)?;
                let requirements_match = checked.scheme.requirements.len() == requirements.len()
                    && checked.scheme.requirements.iter().zip(requirements).all(
                        |(checked, resolved)| {
                            checked.id == resolved.id
                                && checked.interface == resolved.interface.id
                                && same_type(&checked.argument, &resolved.argument.ty)
                        },
                    );
                if checked.spelling != name.spelling
                    || checked.scheme.type_parameters.as_ref() != quantified.as_ref()
                    || !same_type(&checked.scheme.value_type, &function_type.ty)
                    || !requirements_match
                {
                    discard_type_iteratively(binder_type);
                    return Err(invalid_state());
                }
                binder_type
            } else {
                binder_type
            };
            let binder_type = if self.purpose == ElaborationPurpose::FinalSynthesis {
                discard_type_iteratively(binder_type);
                let lowered = self
                    .evidence_lowering
                    .as_ref()
                    .and_then(|lowering| lowering.global_schemes.get(&name.id))
                    .ok_or_else(invalid_state)?;
                if lowered.type_parameters.as_ref() != quantified.as_ref()
                    || !same_type(&lowered.value_type, &function_type.ty)
                {
                    return Err(invalid_state());
                }
                clone_type_with_budget(&lowered.core_scheme, &mut self.type_work)
                    .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?
            } else {
                binder_type
            };
            let binder = self.builder.resolved_binder(
                name.id,
                binder_type,
                Origin::Generated {
                    cause: Box::new(name.origin.clone()),
                    reason: GeneratedReason::BindingLowering,
                },
            )?;
            if context
                .insert_with_provenance(name.id, function_type.ty, function_type.provenance)?
                .is_some()
                || global_binders.insert(name.id, binder).is_some()
            {
                return Err(invalid_state());
            }
            let context_quantified =
                clone_type_variables_with_budget(&quantified, &mut self.type_work)
                    .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?
                    .into_boxed_slice();
            context.set_quantified(name.id, context_quantified)?;
            if global_quantifiers.insert(name.id, quantified).is_some() {
                return Err(invalid_state());
            }
        }

        Ok(PreparedGlobals {
            context,
            globals,
            binders: global_binders,
            quantifiers: global_quantifiers,
        })
    }

    fn elaborate_prepared_definition<D>(
        &mut self,
        definition: &D,
        prepared: &mut PreparedGlobals,
    ) -> Result<(), TypeError>
    where
        D: DefinitionView,
    {
        let recursive_binder = match definition.kind() {
            ResolvedDefinitionKind::Equational(equational) => equational.interface.name.id,
            ResolvedDefinitionKind::InlineOperational(operational) => operational.header.name.id,
        };
        if !self.monomorphic_recursive.insert(recursive_binder) {
            return Err(invalid_state());
        }
        let evidence_marker =
            if self.purpose == ElaborationPurpose::ModuleCheck && self.selection.is_some() {
                Some(self.enter_global_evidence_scope(recursive_binder)?)
            } else {
                None
            };
        let mut lowered_evidence = if self.purpose == ElaborationPurpose::FinalSynthesis {
            let cause = match definition.kind() {
                ResolvedDefinitionKind::Equational(equational) => &equational.interface.name.origin,
                ResolvedDefinitionKind::InlineOperational(operational) => {
                    &operational.header.name.origin
                }
            };
            Some(self.enter_lowered_global_evidence_scope(recursive_binder, cause)?)
        } else {
            None
        };
        let definition_result: Result<_, TypeError> = (|| {
            Ok(match definition.kind() {
                ResolvedDefinitionKind::Equational(equational) => {
                    let function_type = ProvenancedType::from_resolved_with_budget(
                        &equational.interface.annotation,
                        &mut self.type_work,
                    )?;
                    if !matches!(function_type.ty, Type::Function(_, _)) {
                        return Err(equation_interface_not_function(
                            &equational.interface.annotation,
                            &equational.equations.first().ok_or_else(invalid_state)?.name,
                            &self.registry,
                        ));
                    }
                    (
                        &equational.interface.name,
                        self.elaborate_equation_group(
                            equational,
                            function_type,
                            &mut prepared.context,
                            definition.span(),
                        )?,
                    )
                }
                ResolvedDefinitionKind::InlineOperational(operational) => {
                    let domain = operational_domain(
                        &operational.header.parameters,
                        operational.header.span,
                        &mut self.type_work,
                    )?;
                    let codomain = ProvenancedType::from_resolved_with_budget(
                        &operational.header.result_type,
                        &mut self.type_work,
                    )?;
                    let function_type = ProvenancedType::function_with_budget(
                        domain,
                        codomain,
                        Some(operational.header.span),
                        &mut self.type_work,
                    )?;
                    (
                        &operational.header.name,
                        self.elaborate_operational_function(
                            operational,
                            function_type,
                            &mut prepared.context,
                            definition.span(),
                        )?,
                    )
                }
            })
        })();
        let close_result = if definition_result.is_ok() {
            evidence_marker
                .map(|marker| self.close_evidence_obligations(marker))
                .unwrap_or(Ok(()))
        } else {
            Ok(())
        };
        let leave_result = if evidence_marker.is_some() {
            self.leave_evidence_scope()
        } else {
            Ok(())
        };
        let lowered_clear_result = if definition_result.is_err() {
            lowered_evidence
                .take()
                .map(|binders| self.clear_lowered_evidence_scope(binders))
                .unwrap_or(Ok(()))
        } else {
            Ok(())
        };
        if !self.monomorphic_recursive.remove(&recursive_binder) {
            return Err(invalid_state());
        }
        let (name, mut function) = definition_result?;
        close_result?;
        leave_result?;
        lowered_clear_result?;
        if let Some(binders) = lowered_evidence {
            function = self.wrap_lowered_evidence_scope(function, binders, &name.origin)?;
        }
        if !function.provenance.aligns(&function.ty) {
            return Err(invalid_state());
        }
        let binder = prepared
            .binders
            .remove(&name.id)
            .ok_or_else(invalid_state)?;
        let quantified = prepared
            .quantifiers
            .get(&name.id)
            .ok_or_else(invalid_state)?;
        if !quantified.is_empty() {
            self.type_work
                .charge(1)
                .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
            let scheme_parameters =
                clone_type_variables_with_budget(quantified, &mut self.type_work)
                    .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?
                    .into_boxed_slice();
            let scheme_body = self.clone_type(&function.ty)?;
            let scheme = Type::Forall(scheme_parameters, Box::new(scheme_body));
            let abstraction_parameters =
                clone_type_variables_with_budget(quantified, &mut self.type_work)
                    .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
            function.node = self.builder.type_abstraction(
                abstraction_parameters,
                function.node,
                scheme,
                Origin::Generated {
                    cause: Box::new(name.origin.clone()),
                    reason: GeneratedReason::TypeChecking,
                },
            )?;
        }
        prepared.globals.push(ElaboratedBinding {
            binder,
            initializer: function.node,
        });
        Ok(())
    }

    fn finish_prepared_definitions(
        &mut self,
        mut prepared: PreparedGlobals,
    ) -> Result<(Vec<ElaboratedBinding>, TypeContext), TypeError> {
        if !prepared.binders.is_empty() || prepared.globals.len() != prepared.quantifiers.len() {
            return Err(invalid_state());
        }
        for (binder, quantified) in prepared.quantifiers {
            prepared.context.set_quantified(binder, quantified)?;
        }
        self.monomorphic_recursive.clear();

        Ok((prepared.globals, prepared.context))
    }

    fn elaborate_result(
        &mut self,
        result_expression: &ResolvedExpr,
        context: &mut TypeContext,
    ) -> Result<TypedNode, TypeError> {
        let mut result = self.elaborate_expression_with_context(
            ElaborationTask::Synthesize {
                expression: result_expression,
                cause: Some(SynthesisCause::ProgramResult(result_expression.span)),
            },
            context,
        )?;
        let (zonked_result, result_is_ambiguous) = self.zonk_with_status(&result.ty)?;
        if result_is_ambiguous {
            return Err(inference_failure(
                TypeReason::AmbiguousType,
                result_expression.span,
                "this result does not determine every inferred type",
            ));
        }
        result.ty = zonked_result;
        if !result.provenance.aligns(&result.ty) {
            result.provenance = self.unknown_provenance(&result.ty)?;
        }
        let ambiguous = (0..self.next_inference).find(|identity| {
            !self
                .inference_solutions
                .contains_key(&InferenceVariableId::new(*identity))
        });
        if let Some(identity) = ambiguous {
            let index = usize::try_from(identity).map_err(|_| invalid_state())?;
            let origin = self
                .inference_origins
                .get(index)
                .copied()
                .ok_or_else(invalid_state)?;
            return Err(inference_failure(
                TypeReason::AmbiguousType,
                origin,
                "this expression does not determine every inferred type",
            ));
        }
        Ok(result)
    }

    fn elaborate_expression_with_context<'a>(
        &mut self,
        initial: ElaborationTask<'a>,
        context: &mut TypeContext,
    ) -> Result<TypedNode, TypeError> {
        let mut tasks = vec![initial];
        let mut values = Vec::new();
        let mut declarations = Vec::new();
        while let Some(task) = tasks.pop() {
            match task {
                ElaborationTask::Synthesize {
                    expression: current,
                    cause,
                } => match &current.kind {
                    ResolvedExprKind::Integer(value) => {
                        let ty = Type::Int;
                        let node = self.builder.integer(
                            value.clone(),
                            ty.clone(),
                            Origin::Source(current.span),
                        )?;
                        values.push(TypedNode {
                            node,
                            ty,
                            provenance: TypeProvenance::atom(Some(current.span)),
                        });
                    }
                    ResolvedExprKind::Boolean(value) => {
                        let ty = Type::Bool;
                        let node = self.builder.boolean(
                            *value,
                            ty.clone(),
                            Origin::Source(current.span),
                        )?;
                        values.push(TypedNode {
                            node,
                            ty,
                            provenance: TypeProvenance::atom(Some(current.span)),
                        });
                    }
                    ResolvedExprKind::Unit => {
                        let ty = Type::Unit;
                        let node = self
                            .builder
                            .unit(ty.clone(), Origin::Source(current.span))?;
                        values.push(TypedNode {
                            node,
                            ty,
                            provenance: TypeProvenance::atom(Some(current.span)),
                        });
                    }
                    ResolvedExprKind::Add(binary) => {
                        schedule_left(Primitive::Add, current.span, binary, &mut tasks)
                    }
                    ResolvedExprKind::Multiply(binary) => {
                        schedule_left(Primitive::Multiply, current.span, binary, &mut tasks)
                    }
                    ResolvedExprKind::Equal(binary) => {
                        schedule_left(Primitive::Equal, current.span, binary, &mut tasks)
                    }
                    ResolvedExprKind::Occurrence(occurrence) => match occurrence.term {
                        crate::resolved::ResolvedTermName::Global(binder) => {
                            let fact = context.fact(binder).ok_or_else(invalid_state)?;
                            let rigid = self.monomorphic_recursive.contains(&binder);
                            let (ty, arguments) = self.instantiate(fact, rigid, current.span)?;
                            let provenance = fact.provenance.clone();
                            let has_lowered_global_scheme =
                                self.evidence_lowering.as_ref().is_some_and(|lowering| {
                                    lowering.global_schemes.contains_key(&binder)
                                });
                            if self.purpose == ElaborationPurpose::FinalSynthesis
                                && has_lowered_global_scheme
                            {
                                let mut lowering =
                                    self.evidence_lowering.take().ok_or_else(invalid_state)?;
                                let result = (|| {
                                    let scheme = lowering
                                        .global_schemes
                                        .get(&binder)
                                        .ok_or_else(invalid_state)?;
                                    let core_scheme = self.clone_type(&scheme.core_scheme)?;
                                    let variable_ty = self.clone_type(&core_scheme)?;
                                    let mut current = TypedNode {
                                        node: self.builder.variable(
                                            binder,
                                            variable_ty,
                                            occurrence.origin.clone(),
                                        )?,
                                        ty: core_scheme,
                                        provenance: provenance.clone(),
                                    };
                                    if !arguments.is_empty() {
                                        let core_ty =
                                            self.instantiate_lowered_core_body(scheme, &arguments)?;
                                        let application_ty = self.clone_type(&core_ty)?;
                                        current.node = self.builder.type_application(
                                            current.node,
                                            arguments,
                                            application_ty,
                                            occurrence.origin.clone(),
                                        )?;
                                        current.ty = core_ty;
                                    }
                                    for slot in &occurrence.evidence {
                                        let selection =
                                            slot.selection().ok_or_else(invalid_state)?;
                                        let methods = self.lower_evidence_selection(
                                            selection,
                                            &mut lowering,
                                            &occurrence.origin,
                                            None,
                                        )?;
                                        for method in &methods {
                                            current = self.apply_lowered_argument(
                                                current,
                                                method,
                                                &occurrence.origin,
                                            )?;
                                        }
                                    }
                                    if !same_type(&current.ty, &ty) {
                                        return Err(invalid_state());
                                    }
                                    current.provenance = provenance;
                                    Ok(current)
                                })();
                                self.evidence_lowering = Some(lowering);
                                values.push(result?);
                            } else {
                                self.record_global_obligations(
                                    binder,
                                    occurrence,
                                    &arguments,
                                    current.span,
                                )?;
                                let scheme = clone_scheme_with_budget(fact, &mut self.type_work)
                                    .map_err(|()| {
                                        TypeError::Internal(
                                            ElaborationFailure::TypeResourceExhausted,
                                        )
                                    })?;
                                let mut node = self.builder.variable(
                                    binder,
                                    scheme,
                                    occurrence.origin.clone(),
                                )?;
                                if !arguments.is_empty() {
                                    let core_ty = clone_type_with_budget(&ty, &mut self.type_work)
                                        .map_err(|()| {
                                            TypeError::Internal(
                                                ElaborationFailure::TypeResourceExhausted,
                                            )
                                        })?;
                                    node = self.builder.type_application(
                                        node,
                                        arguments,
                                        core_ty,
                                        occurrence.origin.clone(),
                                    )?;
                                }
                                values.push(TypedNode {
                                    node,
                                    ty,
                                    provenance,
                                });
                            }
                        }
                        crate::resolved::ResolvedTermName::Method(method) => {
                            if self.purpose == ElaborationPurpose::FinalSynthesis {
                                values.push(
                                    self.synthesize_lowered_method_occurrence(method, occurrence)?,
                                );
                            } else {
                                values.push(self.synthesize_method_occurrence(
                                    method,
                                    occurrence,
                                    current.span,
                                )?);
                            }
                        }
                    },
                    ResolvedExprKind::Constructor(occurrence) => {
                        let constructor = self
                            .registry
                            .constructor(occurrence.constructor)
                            .ok_or_else(invalid_state)?;
                        let declaration_span = constructor.origin.primary_span();
                        let parameters = self
                            .registry
                            .nominal_parameters(constructor.owner)
                            .ok_or_else(invalid_state)?;
                        let parameter_count = parameters.len();
                        let result_cells = if parameters.is_empty() {
                            1
                        } else {
                            parameter_count.saturating_add(1)
                        };
                        self.type_work
                            .charge(result_cells.saturating_add(parameter_count))
                            .map_err(|()| {
                                TypeError::Internal(ElaborationFailure::TypeResourceExhausted)
                            })?;
                        let payload = if let Some(payload) = &constructor.payload {
                            self.type_work.charge(1).map_err(|()| {
                                TypeError::Internal(ElaborationFailure::TypeResourceExhausted)
                            })?;
                            Some(
                                clone_type_with_budget(payload, &mut self.type_work).map_err(
                                    |()| {
                                        TypeError::Internal(
                                            ElaborationFailure::TypeResourceExhausted,
                                        )
                                    },
                                )?,
                            )
                        } else {
                            None
                        };
                        let mut quantified = Vec::new();
                        quantified.try_reserve(parameter_count).map_err(|_| {
                            TypeError::Internal(ElaborationFailure::TypeResourceExhausted)
                        })?;
                        quantified.extend(parameters.iter().map(|parameter| parameter.id));
                        let result = if parameters.is_empty() {
                            Type::Nominal(constructor.owner)
                        } else {
                            let mut arguments = Vec::new();
                            arguments.try_reserve(parameter_count).map_err(|_| {
                                TypeError::Internal(ElaborationFailure::TypeResourceExhausted)
                            })?;
                            arguments.extend(
                                parameters
                                    .iter()
                                    .map(|parameter| Type::Variable(parameter.id)),
                            );
                            Type::AppliedNominal(constructor.owner, arguments.into_boxed_slice())
                        };
                        let scheme = if let Some(payload) = payload {
                            Type::Function(Box::new(payload), Box::new(result))
                        } else {
                            result
                        };
                        let scheme_provenance = TypeProvenance::at_span(&scheme, declaration_span);
                        let fact = TypeFact {
                            ty: scheme,
                            provenance: scheme_provenance,
                            quantified: quantified.into_boxed_slice(),
                        };
                        let (ty, arguments) = self.instantiate(&fact, false, current.span)?;
                        let TypeFact {
                            ty: fact_ty,
                            provenance: _,
                            quantified,
                        } = fact;
                        let core_scheme = if quantified.is_empty() {
                            fact_ty
                        } else {
                            self.type_work.charge(1).map_err(|()| {
                                TypeError::Internal(ElaborationFailure::TypeResourceExhausted)
                            })?;
                            Type::Forall(quantified, Box::new(fact_ty))
                        };
                        let mut node = self.builder.constructor(
                            occurrence.constructor,
                            core_scheme,
                            occurrence.origin.clone(),
                        )?;
                        if !arguments.is_empty() {
                            let core_ty = clone_type_with_budget(&ty, &mut self.type_work)
                                .map_err(|()| {
                                    TypeError::Internal(ElaborationFailure::TypeResourceExhausted)
                                })?;
                            node = self.builder.type_application(
                                node,
                                arguments,
                                core_ty,
                                occurrence.origin.clone(),
                            )?;
                        }
                        let provenance = TypeProvenance::at_span(&ty, declaration_span);
                        values.push(TypedNode {
                            node,
                            provenance,
                            ty,
                        });
                    }
                    ResolvedExprKind::Tuple(elements) => {
                        let tuple = self.elaborate_tuple(elements, current.span, context)?;
                        values.push(tuple);
                    }
                    ResolvedExprKind::Match(match_expression) => {
                        tasks.push(ElaborationTask::AfterMatchScrutinee {
                            expression: match_expression,
                            span: current.span,
                            expected: None,
                        });
                        tasks.push(ElaborationTask::Synthesize {
                            expression: &match_expression.scrutinee,
                            cause: None,
                        });
                    }
                    ResolvedExprKind::Apply(application) => {
                        let recursive_call = matches!(
                            &application.function.kind,
                            ResolvedExprKind::Occurrence(occurrence)
                                if occurrence.global_binder().is_some_and(|binder|
                                    self.monomorphic_recursive.contains(&binder))
                        );
                        tasks.push(ElaborationTask::AfterApplicationFunction {
                            whole_span: current.span,
                            function_span: application.function.span,
                            argument: &application.argument,
                            recursive_call,
                        });
                        tasks.push(ElaborationTask::Synthesize {
                            expression: &application.function,
                            cause: Some(SynthesisCause::Application(current.span)),
                        });
                    }
                    ResolvedExprKind::Block(block) => {
                        schedule_block(
                            block,
                            None,
                            cause,
                            &mut tasks,
                            declarations.len(),
                            &mut self.type_work,
                        )?;
                    }
                    ResolvedExprKind::Function(_) => {
                        if !matches!(cause, Some(SynthesisCause::Binding(_))) {
                            return Err(function_needs_context(current.span, cause));
                        }
                        self.type_work.charge(3).map_err(|()| {
                            TypeError::Internal(ElaborationFailure::TypeResourceExhausted)
                        })?;
                        let domain = self.fresh_inference(current.span)?;
                        let codomain = self.fresh_inference(current.span)?;
                        let expected_ty = Type::Function(Box::new(domain), Box::new(codomain));
                        let expected = ProvenancedType {
                            provenance: self.unknown_provenance(&expected_ty)?,
                            ty: expected_ty,
                        };
                        tasks.push(ElaborationTask::Check {
                            expression: current,
                            expected,
                            kind: CheckKind::General,
                        });
                    }
                },
                ElaborationTask::Check {
                    expression,
                    expected,
                    kind,
                } => match &expression.kind {
                    ResolvedExprKind::Function(function) => {
                        let expected = self.expose_expected_function(expected, expression.span)?;
                        let (domain_ty, codomain_ty) =
                            clone_function_parts_with_budget(&expected.ty, &mut self.type_work)
                                .map_err(|()| {
                                    TypeError::Internal(ElaborationFailure::TypeResourceExhausted)
                                })?;
                        let (domain_provenance, codomain_provenance) =
                            expected.provenance.function_parts(&expected.ty)?;
                        let domain = ProvenancedType {
                            ty: domain_ty,
                            provenance: domain_provenance,
                        };
                        let codomain = ProvenancedType {
                            ty: codomain_ty,
                            provenance: codomain_provenance,
                        };
                        tasks.push(ElaborationTask::CheckFunction {
                            parameter: &function.pattern,
                            domain,
                            codomain,
                            body: FunctionBody::Block(&function.body),
                            presentation: anonymous_function_origin(expression.span, function),
                            function_type: expected,
                            body_check: kind,
                        });
                    }
                    ResolvedExprKind::Block(block) => {
                        schedule_block(
                            block,
                            Some((expected, kind)),
                            None,
                            &mut tasks,
                            declarations.len(),
                            &mut self.type_work,
                        )?;
                    }
                    ResolvedExprKind::Match(match_expression) => {
                        tasks.push(ElaborationTask::AfterMatchScrutinee {
                            expression: match_expression,
                            span: expression.span,
                            expected: Some((expected, kind)),
                        });
                        tasks.push(ElaborationTask::Synthesize {
                            expression: &match_expression.scrutinee,
                            cause: None,
                        });
                    }
                    _ => {
                        tasks.push(ElaborationTask::FinishCheck {
                            span: expression.span,
                            expected,
                            kind,
                        });
                        tasks.push(ElaborationTask::Synthesize {
                            expression,
                            cause: None,
                        });
                    }
                },
                ElaborationTask::CheckBlock {
                    block,
                    expected,
                    kind,
                } => schedule_block(
                    block,
                    Some((expected, kind)),
                    None,
                    &mut tasks,
                    declarations.len(),
                    &mut self.type_work,
                )?,
                ElaborationTask::FinishCheck {
                    span,
                    expected,
                    kind,
                } => {
                    let synthesized = values.pop().ok_or_else(invalid_state)?;
                    if !expected.provenance.aligns(&expected.ty)
                        || !synthesized.provenance.aligns(&synthesized.ty)
                    {
                        return Err(invalid_state());
                    }
                    match self.unify(&synthesized.ty, &expected.ty) {
                        Ok(()) => {}
                        Err(UnificationFailure::Infinite) => {
                            return Err(inference_failure(
                                TypeReason::InfiniteType,
                                span,
                                "this expression would require an infinite type",
                            ));
                        }
                        Err(UnificationFailure::Mismatch) => {
                            return Err(check_mismatch(
                                kind,
                                span,
                                self.zonk(&expected.ty)?,
                                self.zonk(&synthesized.ty)?,
                                expected.provenance.span(),
                                &self.registry,
                            ));
                        }
                        Err(UnificationFailure::Resource) => {
                            return Err(TypeError::Internal(
                                ElaborationFailure::TypeResourceExhausted,
                            ));
                        }
                    }
                    let ty = self.zonk_owned(synthesized.ty)?;
                    self.builder
                        .record_type_check(synthesized.node, expected.provenance.span())?;
                    values.push(TypedNode {
                        node: synthesized.node,
                        ty,
                        provenance: synthesized.provenance,
                    });
                }
                ElaborationTask::CheckFunction {
                    parameter,
                    domain,
                    codomain,
                    body,
                    presentation,
                    function_type,
                    body_check,
                } => {
                    self.schedule_function_check(
                        context,
                        &mut tasks,
                        declarations.len(),
                        FunctionCheck {
                            parameter,
                            domain,
                            codomain,
                            body,
                            presentation,
                            function_type,
                            body_check,
                        },
                    )?;
                }
                ElaborationTask::FinishFunction {
                    direct_binder,
                    pattern_binders,
                    binder,
                    pattern,
                    domain,
                    ty,
                    origin,
                    provenance,
                } => {
                    let mut body = values.pop().ok_or_else(invalid_state)?;
                    if let Some(binder) = direct_binder
                        && context.binders.remove(&binder).is_none()
                    {
                        return Err(invalid_state());
                    }
                    self.remove_pattern_binders(context, &pattern_binders)?;
                    if let Some(pattern) = pattern {
                        let domain = domain.ok_or_else(invalid_state)?;
                        let pattern_span = pattern.origin.primary_span();
                        let mut matrix = vec![vec![pattern]];
                        if let Some(witness) = missing_witness_for_types_with_budget(
                            &matrix,
                            std::slice::from_ref(&domain),
                            &self.registry,
                            &mut self.coverage_work,
                        )? {
                            return Err(case_error(
                                TypeReason::RefutableFunctionDomain,
                                pattern_span,
                                "this function pattern is not exhaustive",
                                Some(display_witness(&witness, &self.registry)),
                            ));
                        }
                        let mut row = matrix.pop().ok_or_else(invalid_state)?;
                        let pattern = row.pop().ok_or_else(invalid_state)?;
                        if !row.is_empty() {
                            return Err(invalid_state());
                        }
                        let scrutinee_origin = pattern.origin.clone();
                        let arm_origin = pattern.origin.clone();
                        let match_origin = pattern.origin.clone();
                        let scrutinee =
                            self.builder
                                .variable(binder.id(), domain, scrutinee_origin)?;
                        let core_body_type = self.clone_type(&body.ty)?;
                        let match_node = self.builder.match_expression(
                            scrutinee,
                            vec![CoreMatchArm::new(pattern, body.node, arm_origin)],
                            core_body_type,
                            match_origin,
                        )?;
                        body.node = match_node;
                    }
                    let core_ty = self.clone_type(&ty)?;
                    let node = self.builder.function(binder, body.node, core_ty, origin)?;
                    values.push(TypedNode {
                        node,
                        ty,
                        provenance,
                    });
                }
                ElaborationTask::AfterApplicationFunction {
                    whole_span,
                    function_span,
                    argument,
                    recursive_call,
                } => {
                    let mut function = values.pop().ok_or_else(invalid_state)?;
                    let mut function_ty = self.zonk_owned(function.ty)?;
                    if matches!(function_ty, Type::Inference(_)) {
                        self.type_work.charge(3).map_err(|()| {
                            TypeError::Internal(ElaborationFailure::TypeResourceExhausted)
                        })?;
                        let domain = self.fresh_inference(function_span)?;
                        let codomain = self.fresh_inference(function_span)?;
                        let exposed = Type::Function(Box::new(domain), Box::new(codomain));
                        self.unify(&function_ty, &exposed)
                            .map_err(|failure| match failure {
                                UnificationFailure::Infinite => inference_failure(
                                    TypeReason::InfiniteType,
                                    function_span,
                                    "this application would require an infinite type",
                                ),
                                UnificationFailure::Mismatch => not_applicable(
                                    function_span,
                                    whole_span,
                                    &function_ty,
                                    &self.registry,
                                ),
                                UnificationFailure::Resource => {
                                    TypeError::Internal(ElaborationFailure::TypeResourceExhausted)
                                }
                            })?;
                        function_ty = self.zonk(&exposed)?;
                    }
                    let Type::Function(_, _) = &function_ty else {
                        return Err(not_applicable(
                            function_span,
                            whole_span,
                            &function_ty,
                            &self.registry,
                        ));
                    };
                    let provenance = if function.provenance.aligns(&function_ty) {
                        function.provenance.clone()
                    } else {
                        self.unknown_provenance(&function_ty)?
                    };
                    let (domain_provenance, codomain_provenance) =
                        provenance.function_parts(&function_ty)?;
                    let (domain_ty, codomain_ty) =
                        clone_function_parts_with_budget(&function_ty, &mut self.type_work)
                            .map_err(|()| {
                                TypeError::Internal(ElaborationFailure::TypeResourceExhausted)
                            })?;
                    function.ty = function_ty;
                    let domain = ProvenancedType {
                        ty: domain_ty,
                        provenance: domain_provenance,
                    };
                    let codomain = ProvenancedType {
                        ty: codomain_ty,
                        provenance: codomain_provenance,
                    };
                    tasks.push(ElaborationTask::FinishApplication {
                        whole_span,
                        function_span,
                        argument_span: argument.span,
                        function,
                        codomain,
                    });
                    tasks.push(ElaborationTask::Check {
                        expression: argument,
                        expected: domain,
                        kind: CheckKind::Argument {
                            function_span,
                            whole_span,
                            recursive_call,
                        },
                    });
                }
                ElaborationTask::FinishApplication {
                    whole_span,
                    function_span,
                    argument_span,
                    function,
                    codomain,
                } => {
                    let argument = values.pop().ok_or_else(invalid_state)?;
                    let core_codomain = self.clone_type(&codomain.ty)?;
                    let ty = self.zonk_owned(codomain.ty)?;
                    let provenance = if codomain.provenance.aligns(&ty) {
                        codomain.provenance
                    } else {
                        self.unknown_provenance(&ty)?
                    };
                    let origin = Origin::Related {
                        primary: Box::new(Origin::Source(whole_span)),
                        related: vec![function_span, argument_span],
                    };
                    let node = self.builder.application(
                        function.node,
                        argument.node,
                        core_codomain,
                        origin,
                    )?;
                    values.push(TypedNode {
                        node,
                        ty,
                        provenance,
                    });
                }
                ElaborationTask::AfterLeft {
                    primitive,
                    whole_span,
                    operator_span,
                    right,
                    left_span,
                } => {
                    let left = values.pop().ok_or_else(invalid_state)?;
                    self.require_integer(&left, left_span, operator_span)?;
                    tasks.push(ElaborationTask::AfterRight {
                        primitive,
                        whole_span,
                        operator_span,
                        left,
                        right_span: right.span,
                    });
                    tasks.push(ElaborationTask::Synthesize {
                        expression: right,
                        cause: Some(SynthesisCause::Operator(operator_span)),
                    });
                }
                ElaborationTask::AfterRight {
                    primitive,
                    whole_span,
                    operator_span,
                    left,
                    right_span,
                } => {
                    let right = values.pop().ok_or_else(invalid_state)?;
                    self.require_integer(&right, right_span, operator_span)?;
                    let ty = match primitive {
                        Primitive::Add | Primitive::Multiply => Type::Int,
                        Primitive::Equal => Type::Bool,
                    };
                    let origin = Origin::Related {
                        primary: Box::new(Origin::Source(whole_span)),
                        related: vec![operator_span],
                    };
                    let node = self.builder.primitive(
                        primitive,
                        left.node,
                        right.node,
                        ty.clone(),
                        origin,
                    )?;
                    values.push(TypedNode {
                        node,
                        ty,
                        provenance: TypeProvenance::atom(Some(operator_span)),
                    });
                }
                ElaborationTask::BeginBinding {
                    binding,
                    expected,
                    finish_expected,
                } => {
                    let evidence_marker = if self.purpose == ElaborationPurpose::ModuleCheck
                        && self.selection.is_some()
                        && finish_expected.is_none()
                        && matches!(binding.pattern.kind, ResolvedPatternKind::Binder(_))
                        && matches!(binding.initializer.kind, ResolvedExprKind::Function(_))
                    {
                        Some(self.evidence_marker()?)
                    } else {
                        None
                    };
                    tasks.push(ElaborationTask::FinishBinding {
                        binding,
                        expected: finish_expected,
                        evidence_marker,
                    });
                    match (expected, binding.annotation.as_ref()) {
                        (Some(expected), Some(annotation)) => {
                            tasks.push(ElaborationTask::Check {
                                expression: &binding.initializer,
                                expected,
                                kind: CheckKind::BindingInitializer {
                                    initializer_span: binding.initializer.span,
                                    annotation_span: annotation.span,
                                },
                            });
                        }
                        (None, None) => tasks.push(ElaborationTask::Synthesize {
                            expression: &binding.initializer,
                            cause: Some(SynthesisCause::Binding(binding.span)),
                        }),
                        _ => return Err(invalid_state()),
                    }
                }
                ElaborationTask::FinishBinding {
                    binding,
                    expected,
                    evidence_marker,
                } => {
                    let mut initializer = values.pop().ok_or_else(invalid_state)?;
                    if let Some(marker) = evidence_marker {
                        self.close_evidence_obligations(marker)?;
                    }
                    let mut generalized = Vec::new();
                    if expected.is_none()
                        && matches!(binding.pattern.kind, ResolvedPatternKind::Binder(_))
                        && matches!(binding.initializer.kind, ResolvedExprKind::Function(_))
                    {
                        let inferred = self.zonk(&initializer.ty)?;
                        let mut variables =
                            collect_unsolved_inference(&inferred, &mut self.type_work).map_err(
                                |()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted),
                            )?;
                        let mut environment_variables = HashSet::new();
                        for fact in context.binders.values() {
                            let ty = self.zonk(&fact.ty)?;
                            let variables = collect_unsolved_inference(&ty, &mut self.type_work)
                                .map_err(|()| {
                                    TypeError::Internal(ElaborationFailure::TypeResourceExhausted)
                                })?;
                            self.type_work.charge(variables.len()).map_err(|()| {
                                TypeError::Internal(ElaborationFailure::TypeResourceExhausted)
                            })?;
                            environment_variables
                                .try_reserve(variables.len())
                                .map_err(|_| {
                                    TypeError::Internal(ElaborationFailure::TypeResourceExhausted)
                                })?;
                            environment_variables.extend(variables);
                        }
                        self.type_work.charge(variables.len()).map_err(|()| {
                            TypeError::Internal(ElaborationFailure::TypeResourceExhausted)
                        })?;
                        variables.retain(|variable| !environment_variables.contains(variable));
                        let generalized_count = variables.len();
                        self.type_work
                            .charge(generalized_count.saturating_mul(3))
                            .map_err(|()| {
                                TypeError::Internal(ElaborationFailure::TypeResourceExhausted)
                            })?;
                        generalized.try_reserve(generalized_count).map_err(|_| {
                            TypeError::Internal(ElaborationFailure::TypeResourceExhausted)
                        })?;
                        self.inference_solutions
                            .try_reserve(generalized_count)
                            .map_err(|_| {
                                TypeError::Internal(ElaborationFailure::TypeResourceExhausted)
                            })?;
                        for variable in variables {
                            let binder = self.fresh_type_variable()?;
                            self.inference_solutions
                                .insert(variable, Type::Variable(binder));
                            generalized.push(binder);
                        }
                        initializer.ty = self.zonk(&initializer.ty)?;
                    }
                    let mut binding_type = if let Some(expected) = expected {
                        expected
                    } else {
                        ProvenancedType {
                            ty: initializer.ty,
                            provenance: initializer.provenance,
                        }
                    };
                    let mut binder_ids = Vec::new();
                    let checked = self.check_core_pattern(
                        &binding.pattern,
                        &binding_type.ty,
                        context,
                        &mut binder_ids,
                        GeneratedReason::BindingLowering,
                    )?;
                    let pattern = checked.pattern;
                    if checked.inference_changed {
                        binding_type.ty = clone_type_with_budget(&pattern.ty, &mut self.type_work)
                            .map_err(|()| {
                                TypeError::Internal(ElaborationFailure::TypeResourceExhausted)
                            })?;
                        if !binding_type.provenance.aligns(&binding_type.ty) {
                            binding_type.provenance = self.unknown_provenance(&binding_type.ty)?;
                        }
                    }
                    let mut matrix = vec![vec![pattern]];
                    if let Some(witness) = missing_witness_for_types_with_budget(
                        &matrix,
                        std::slice::from_ref(&binding_type.ty),
                        &self.registry,
                        &mut self.coverage_work,
                    )? {
                        self.remove_pattern_binders(context, &binder_ids)?;
                        return Err(case_error(
                            TypeReason::RefutableBinding,
                            binding.span,
                            "this local binding pattern can fail",
                            Some(display_witness(&witness, &self.registry)),
                        ));
                    }
                    let mut row = matrix.pop().ok_or_else(invalid_state)?;
                    let pattern = row.pop().ok_or_else(invalid_state)?;
                    if !row.is_empty() {
                        return Err(invalid_state());
                    }
                    match pattern {
                        CorePattern {
                            ty,
                            origin: pattern_origin,
                            kind: CorePatternKind::Binder(mut binder),
                        } => {
                            discard_type_iteratively(ty);
                            discard_origin_iteratively(pattern_origin);
                            let quantified = generalized.into_boxed_slice();
                            let context_quantified =
                                clone_type_variables_with_budget(&quantified, &mut self.type_work)
                                    .map_err(|()| {
                                        TypeError::Internal(
                                            ElaborationFailure::TypeResourceExhausted,
                                        )
                                    })?
                                    .into_boxed_slice();
                            let abstraction = if quantified.is_empty() {
                                None
                            } else {
                                self.type_work.charge(1).map_err(|()| {
                                    TypeError::Internal(ElaborationFailure::TypeResourceExhausted)
                                })?;
                                let scheme_body = self.clone_type(&binding_type.ty)?;
                                let scheme = Type::Forall(quantified, Box::new(scheme_body));
                                let binder_scheme = self.clone_type(&scheme)?;
                                let abstraction_parameters = match &scheme {
                                    Type::Forall(parameters, _) => {
                                        clone_type_variables_with_budget(
                                            parameters,
                                            &mut self.type_work,
                                        )
                                        .map_err(|()| {
                                            TypeError::Internal(
                                                ElaborationFailure::TypeResourceExhausted,
                                            )
                                        })?
                                    }
                                    _ => return Err(invalid_state()),
                                };
                                Some((scheme, binder_scheme, abstraction_parameters))
                            };
                            let origin = binding_origin(binding);
                            context.set_quantified(binder.id(), context_quantified)?;
                            if let Some((scheme, binder_scheme, abstraction_parameters)) =
                                abstraction
                            {
                                binder.replace_type(binder_scheme);
                                initializer.node = self.builder.type_abstraction(
                                    abstraction_parameters,
                                    initializer.node,
                                    scheme,
                                    Origin::Generated {
                                        cause: Box::new(origin.clone()),
                                        reason: GeneratedReason::TypeChecking,
                                    },
                                )?;
                            }
                            declarations.push(ElaboratedDeclaration::Binding {
                                binder,
                                initializer: initializer.node,
                                origin,
                            });
                        }
                        pattern => {
                            let origin = binding_origin(binding);
                            declarations.push(ElaboratedDeclaration::PatternBinding {
                                pattern,
                                initializer: initializer.node,
                                origin,
                            });
                        }
                    }
                }
                ElaborationTask::CheckRecursiveMember(member) => {
                    let fact = context.fact(member.binder.id).ok_or_else(invalid_state)?;
                    let expected = ProvenancedType {
                        ty: clone_type_with_budget(&fact.ty, &mut self.type_work).map_err(
                            |()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted),
                        )?,
                        provenance: fact.provenance.clone(),
                    };
                    tasks.push(ElaborationTask::Check {
                        expression: &member.initializer,
                        expected,
                        kind: CheckKind::BindingInitializer {
                            initializer_span: member.initializer.span,
                            annotation_span: member.annotation.span,
                        },
                    });
                }
                ElaborationTask::BeginRecursiveGroup(group) => {
                    for member in &group.members {
                        validate_recursive_member(group, member, &self.registry)?;
                    }
                    for member in &group.members {
                        let expected = ProvenancedType::from_resolved_with_budget(
                            &member.annotation,
                            &mut self.type_work,
                        )?;
                        if context
                            .insert_with_provenance(
                                member.binder.id,
                                expected.ty,
                                expected.provenance,
                            )?
                            .is_some()
                        {
                            return Err(invalid_state());
                        }
                    }
                    tasks.push(ElaborationTask::FinishRecursiveGroup { group });
                    for member in group.members.iter().rev() {
                        tasks.push(ElaborationTask::CheckRecursiveMember(member));
                    }
                }
                ElaborationTask::FinishRecursiveGroup { group } => {
                    if values.len() < group.members.len() {
                        return Err(invalid_state());
                    }
                    let value_start = values.len() - group.members.len();
                    let initializers = values.split_off(value_start);
                    self.type_work.charge(group.members.len()).map_err(|()| {
                        TypeError::Internal(ElaborationFailure::TypeResourceExhausted)
                    })?;
                    let mut members = Vec::new();
                    members.try_reserve(group.members.len()).map_err(|_| {
                        TypeError::Internal(ElaborationFailure::TypeResourceExhausted)
                    })?;
                    for (member, initializer) in group.members.iter().zip(initializers) {
                        let binder = self.builder.resolved_binder(
                            member.binder.id,
                            initializer.ty,
                            Origin::Generated {
                                cause: Box::new(member.binder.origin.clone()),
                                reason: GeneratedReason::BindingLowering,
                            },
                        )?;
                        members.push((binder, initializer.node));
                    }
                    declarations.push(ElaboratedDeclaration::Recursive {
                        members,
                        origin: recursive_group_origin(group),
                    });
                }
                ElaborationTask::AfterMatchScrutinee {
                    expression,
                    span,
                    expected,
                } => {
                    let scrutinee = values.pop().ok_or_else(invalid_state)?;
                    if expression.arms.is_empty() {
                        return Err(case_error(
                            TypeReason::NonExhaustive,
                            span,
                            "a match requires at least one arm",
                            None,
                        ));
                    }
                    let arm_count = expression.arms.len();
                    self.type_work
                        .charge(arm_count.saturating_mul(2))
                        .map_err(|()| {
                            TypeError::Internal(ElaborationFailure::TypeResourceExhausted)
                        })?;
                    let mut matrix = Vec::new();
                    matrix.try_reserve(arm_count).map_err(|_| {
                        TypeError::Internal(ElaborationFailure::TypeResourceExhausted)
                    })?;
                    let mut arm_bodies = Vec::new();
                    arm_bodies.try_reserve(arm_count).map_err(|_| {
                        TypeError::Internal(ElaborationFailure::TypeResourceExhausted)
                    })?;
                    let progress = Box::new(MatchProgress {
                        expression,
                        span,
                        scrutinee,
                        next_arm: 0,
                        matrix,
                        arm_bodies,
                        result_type: expected
                            .map(|(expected, kind)| (expected.ty, expected.provenance, kind)),
                    });
                    self.schedule_match_arm(progress, context, &mut tasks)?;
                }
                ElaborationTask::FinishMatchArm {
                    mut progress,
                    binders,
                    row,
                    arm_span,
                } => {
                    let body_result = values.pop().ok_or_else(invalid_state);
                    self.remove_pattern_binders(context, &binders)?;
                    let body = body_result?;
                    if progress.result_type.is_none() {
                        progress.result_type = Some((body.ty, body.provenance, CheckKind::General));
                    }
                    progress.matrix.push(row);
                    progress.arm_bodies.push((body.node, arm_span));
                    self.schedule_match_arm(progress, context, &mut tasks)?;
                }
                ElaborationTask::FinishMatch(progress) => {
                    let Some((ty, provenance, _)) = progress.result_type else {
                        return Err(invalid_state());
                    };
                    if progress.matrix.len() != progress.arm_bodies.len() {
                        return Err(invalid_state());
                    }
                    self.type_work
                        .charge(progress.arm_bodies.len())
                        .map_err(|()| {
                            TypeError::Internal(ElaborationFailure::TypeResourceExhausted)
                        })?;
                    let mut arms = Vec::new();
                    arms.try_reserve(progress.arm_bodies.len()).map_err(|_| {
                        TypeError::Internal(ElaborationFailure::TypeResourceExhausted)
                    })?;
                    for (mut row, (body, arm_span)) in
                        progress.matrix.into_iter().zip(progress.arm_bodies)
                    {
                        let pattern = row.pop().ok_or_else(invalid_state)?;
                        if !row.is_empty() {
                            return Err(invalid_state());
                        }
                        arms.push(CoreMatchArm::new(pattern, body, Origin::Source(arm_span)));
                    }
                    let core_ty = self.clone_type(&ty)?;
                    let node = self.builder.match_expression(
                        progress.scrutinee.node,
                        arms,
                        core_ty,
                        Origin::Source(progress.span),
                    )?;
                    values.push(TypedNode {
                        node,
                        ty,
                        provenance,
                    });
                }
                ElaborationTask::FinishBlock {
                    declarations: source_declarations,
                    declaration_start,
                } => {
                    let mut body = values.pop().ok_or_else(invalid_state)?;
                    if declaration_start > declarations.len()
                        || declarations.len() - declaration_start != source_declarations.len()
                    {
                        return Err(invalid_state());
                    }
                    for declaration in declarations.drain(declaration_start..).rev() {
                        let core_body_type = self.clone_type(&body.ty)?;
                        let node = match declaration {
                            ElaboratedDeclaration::Binding {
                                binder,
                                initializer,
                                origin,
                            } => self.builder.binding(
                                binder,
                                initializer,
                                body.node,
                                core_body_type,
                                origin,
                            )?,
                            ElaboratedDeclaration::PatternBinding {
                                pattern,
                                initializer,
                                origin,
                                ..
                            } => self.builder.match_expression(
                                initializer,
                                vec![CoreMatchArm::new(pattern, body.node, origin.clone())],
                                core_body_type,
                                origin,
                            )?,
                            ElaboratedDeclaration::Recursive { members, origin } => self
                                .builder
                                .recursive_binding(members, body.node, core_body_type, origin)?,
                        };
                        body = TypedNode {
                            node,
                            ty: body.ty,
                            provenance: body.provenance,
                        };
                    }
                    for declaration in source_declarations {
                        match declaration {
                            ResolvedLocalDeclaration::Binding(binding) => {
                                let mut ids = Vec::new();
                                collect_pattern_binders(&binding.pattern, &mut ids);
                                for id in ids {
                                    if context.binders.remove(&id).is_none() {
                                        return Err(invalid_state());
                                    }
                                }
                            }
                            ResolvedLocalDeclaration::Recursive(group) => {
                                for member in &group.members {
                                    if context.binders.remove(&member.binder.id).is_none() {
                                        return Err(invalid_state());
                                    }
                                }
                            }
                        }
                    }
                    values.push(body);
                }
            }
        }
        let result = values.pop().ok_or_else(invalid_state)?;
        if values.is_empty() && result.provenance.aligns(&result.ty) {
            Ok(result)
        } else {
            Err(invalid_state())
        }
    }

    fn elaborate_tuple(
        &mut self,
        elements: &[ResolvedExpr],
        span: Span,
        context: &mut TypeContext,
    ) -> Result<TypedNode, TypeError> {
        if elements.len() < 2 {
            return Err(invalid_state());
        }
        let mut nodes = Vec::with_capacity(elements.len());
        let mut types = Vec::with_capacity(elements.len());
        for element in elements {
            let typed = self.elaborate_expression_with_context(
                ElaborationTask::Synthesize {
                    expression: element,
                    cause: None,
                },
                context,
            )?;
            nodes.push(typed.node);
            types.push(typed.ty);
        }
        self.type_work
            .charge(1)
            .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
        let ty = Type::Tuple(types.into_boxed_slice());
        let core_ty = self.clone_type(&ty)?;
        let node = self.builder.tuple(nodes, core_ty, Origin::Source(span))?;
        Ok(TypedNode {
            node,
            provenance: TypeProvenance::atom(Some(span)),
            ty,
        })
    }

    fn schedule_match_arm<'a>(
        &mut self,
        mut progress: Box<MatchProgress<'a>>,
        context: &mut TypeContext,
        tasks: &mut Vec<ElaborationTask<'a>>,
    ) -> Result<(), TypeError> {
        let Some(arm) = progress.expression.arms.get(progress.next_arm) else {
            if let Some(witness) = missing_witness_for_types_with_budget(
                &progress.matrix,
                std::slice::from_ref(&progress.scrutinee.ty),
                &self.registry,
                &mut self.coverage_work,
            )? {
                return Err(case_error(
                    TypeReason::NonExhaustive,
                    progress.span,
                    "this match does not cover every value",
                    Some(display_witness(&witness, &self.registry)),
                ));
            }
            tasks.push(ElaborationTask::FinishMatch(progress));
            return Ok(());
        };

        self.type_work
            .charge(1)
            .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
        let mut row = Vec::new();
        row.try_reserve(1)
            .map_err(|_| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
        let mut binders = Vec::new();
        let checked = self.check_core_pattern(
            &arm.pattern,
            &progress.scrutinee.ty,
            context,
            &mut binders,
            GeneratedReason::BindingLowering,
        )?;
        let pattern = checked.pattern;
        if checked.inference_changed {
            progress.scrutinee.ty = clone_type_with_budget(&pattern.ty, &mut self.type_work)
                .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
            if !progress.scrutinee.provenance.aligns(&progress.scrutinee.ty) {
                progress.scrutinee.provenance = self.unknown_provenance(&progress.scrutinee.ty)?;
            }
        }
        row.push(pattern);
        if usefulness_with_budget(
            &progress.matrix,
            &row,
            std::slice::from_ref(&progress.scrutinee.ty),
            &self.registry,
            &mut self.coverage_work,
        )?
        .is_none()
        {
            self.remove_pattern_binders(context, &binders)?;
            return Err(case_error(
                TypeReason::RedundantCase,
                arm.span,
                "this match arm can never be selected",
                None,
            ));
        }
        progress.next_arm += 1;
        let body_task = if let Some((ty, provenance, kind)) = &progress.result_type {
            let expected_ty = self.clone_type(ty)?;
            ElaborationTask::Check {
                expression: &arm.body,
                expected: ProvenancedType {
                    ty: expected_ty,
                    provenance: provenance.clone(),
                },
                kind: *kind,
            }
        } else {
            ElaborationTask::Synthesize {
                expression: &arm.body,
                cause: None,
            }
        };
        tasks.push(ElaborationTask::FinishMatchArm {
            progress,
            binders,
            row,
            arm_span: arm.span,
        });
        tasks.push(body_task);
        Ok(())
    }

    fn check_core_pattern(
        &mut self,
        pattern: &ResolvedPattern,
        expected: &Type,
        context: &mut TypeContext,
        binders: &mut Vec<BinderId>,
        binder_reason: GeneratedReason,
    ) -> Result<CheckedPattern, TypeError> {
        let (mut expected, mut inference_changed) = if let Type::Inference(identity) = expected {
            let zonked = self.zonk(expected)?;
            let changed = !matches!(&zonked, Type::Inference(zonked) if *zonked == *identity);
            (zonked, changed)
        } else {
            self.charge_type(expected)?;
            (expected.clone(), false)
        };
        let mut rebuild_expected = false;
        let kind = match &pattern.kind {
            ResolvedPatternKind::Binder(binder) => {
                charge_pattern_binder_storage(&expected, &mut self.type_work)
                    .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
                binders
                    .try_reserve(1)
                    .map_err(|_| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
                context
                    .binders
                    .try_reserve(1)
                    .map_err(|_| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
                let typed = self.builder.resolved_binder(
                    binder.id,
                    expected.clone(),
                    Origin::Generated {
                        cause: Box::new(binder.origin.clone()),
                        reason: binder_reason,
                    },
                )?;
                if context
                    .insert_with_provenance(
                        binder.id,
                        expected.clone(),
                        // `charge_pattern_binder_storage` reserves this tree
                        // before the binder and context entries are retained.
                        TypeProvenance::unknown(&expected),
                    )?
                    .is_some()
                {
                    return Err(invalid_state());
                }
                binders.push(binder.id);
                CorePatternKind::Binder(typed)
            }
            ResolvedPatternKind::Wildcard => CorePatternKind::Wildcard,
            ResolvedPatternKind::Boolean(value) => {
                if matches!(expected, Type::Inference(_)) {
                    expected =
                        self.refine_pattern_expected(&expected, &Type::Bool, pattern.span)?;
                    inference_changed = true;
                } else if !matches!(expected, Type::Bool) {
                    return Err(pattern_mismatch(pattern.span, &expected, &self.registry));
                }
                CorePatternKind::Boolean(*value)
            }
            ResolvedPatternKind::Unit => {
                if matches!(expected, Type::Inference(_)) {
                    expected =
                        self.refine_pattern_expected(&expected, &Type::Unit, pattern.span)?;
                    inference_changed = true;
                } else if !matches!(expected, Type::Unit) {
                    return Err(pattern_mismatch(pattern.span, &expected, &self.registry));
                }
                CorePatternKind::Unit
            }
            ResolvedPatternKind::Tuple(patterns) => {
                if matches!(expected, Type::Inference(_)) {
                    self.type_work
                        .charge(patterns.len().saturating_add(1))
                        .map_err(|()| {
                            TypeError::Internal(ElaborationFailure::TypeResourceExhausted)
                        })?;
                    let mut types = Vec::new();
                    types.try_reserve(patterns.len()).map_err(|_| {
                        TypeError::Internal(ElaborationFailure::TypeResourceExhausted)
                    })?;
                    for _ in patterns {
                        types.push(self.fresh_inference(pattern.span)?);
                    }
                    let required = Type::Tuple(types.into_boxed_slice());
                    expected = self.refine_pattern_expected(&expected, &required, pattern.span)?;
                    inference_changed = true;
                }
                let Type::Tuple(types) = &expected else {
                    return Err(pattern_mismatch(pattern.span, &expected, &self.registry));
                };
                if patterns.len() != types.len() {
                    return Err(pattern_mismatch(pattern.span, &expected, &self.registry));
                }
                let mut checked = Vec::new();
                checked
                    .try_reserve(patterns.len())
                    .map_err(|_| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
                for (pattern, ty) in patterns.iter().zip(types) {
                    let outcome =
                        self.check_core_pattern(pattern, ty, context, binders, binder_reason)?;
                    rebuild_expected |= outcome.inference_changed;
                    inference_changed |= outcome.inference_changed;
                    checked.push(outcome.pattern);
                }
                CorePatternKind::Tuple(checked.into_boxed_slice())
            }
            ResolvedPatternKind::Constructor {
                constructor,
                payload,
                ..
            } => {
                return self.check_core_constructor_pattern(
                    pattern,
                    *constructor,
                    payload.as_deref(),
                    expected,
                    context,
                    binders,
                    binder_reason,
                    inference_changed,
                );
            }
        };
        let expected = if rebuild_expected {
            self.zonk(&expected)?
        } else {
            expected
        };
        Ok(CheckedPattern {
            pattern: CorePattern::new(expected, Origin::Source(pattern.span), kind),
            inference_changed,
        })
    }

    #[allow(clippy::too_many_arguments)]
    fn check_core_constructor_pattern(
        &mut self,
        whole_pattern: &ResolvedPattern,
        constructor: crate::types::ConstructorId,
        payload: Option<&ResolvedPattern>,
        mut expected: Type,
        context: &mut TypeContext,
        binders: &mut Vec<BinderId>,
        binder_reason: GeneratedReason,
        mut inference_changed: bool,
    ) -> Result<CheckedPattern, TypeError> {
        let Some(info) = self.registry.constructor(constructor) else {
            return Err(invalid_state());
        };
        let info_owner = info.owner;
        if let Some(payload) = &info.payload {
            charge_type_cells(payload, &mut self.type_work)
                .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
        }
        let declared_payload = info.payload.clone();
        if matches!(expected, Type::Inference(_)) {
            let parameter_count = self
                .registry
                .nominal_parameters(info_owner)
                .ok_or_else(invalid_state)?
                .len();
            self.type_work
                .charge(parameter_count.saturating_add(1))
                .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
            let required = if parameter_count == 0 {
                Type::Nominal(info_owner)
            } else {
                let mut arguments = Vec::new();
                arguments
                    .try_reserve(parameter_count)
                    .map_err(|_| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
                for _ in 0..parameter_count {
                    arguments.push(self.fresh_inference(whole_pattern.span)?);
                }
                Type::AppliedNominal(info_owner, arguments.into_boxed_slice())
            };
            expected = self.refine_pattern_expected(&expected, &required, whole_pattern.span)?;
            inference_changed = true;
        }
        let (owner, arguments): (_, &[Type]) = match &expected {
            Type::Nominal(owner) => (*owner, &[]),
            Type::AppliedNominal(owner, arguments) => (*owner, arguments),
            _ => {
                return Err(pattern_mismatch(
                    whole_pattern.span,
                    &expected,
                    &self.registry,
                ));
            }
        };
        let parameters = self
            .registry
            .nominal_parameters(owner)
            .ok_or_else(invalid_state)?;
        if parameters.len() != arguments.len() {
            return Err(invalid_state());
        }
        let replacements =
            constructor_replacements_with_budget(parameters, arguments, &mut self.type_work)
                .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
        let payload_type = declared_payload
            .as_ref()
            .map(|payload| {
                substitute_type_variables_with(payload, &replacements, |cells| {
                    self.type_work.charge(cells)
                })
                .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))
            })
            .transpose()?;
        if info_owner != owner {
            return Err(case_error(
                TypeReason::ConstructorOwner,
                whole_pattern.span,
                "this constructor belongs to another nominal type",
                None,
            ));
        }
        let checked_payload = match (payload, payload_type.as_ref()) {
            (None, None) => None,
            (Some(pattern), Some(ty)) => {
                let outcome = if let ResolvedPatternKind::Constructor {
                    constructor,
                    payload,
                    ..
                } = &pattern.kind
                {
                    let expected = self.clone_type(ty)?;
                    self.check_core_constructor_pattern(
                        pattern,
                        *constructor,
                        payload.as_deref(),
                        expected,
                        context,
                        binders,
                        binder_reason,
                        false,
                    )?
                } else {
                    self.check_core_pattern(pattern, ty, context, binders, binder_reason)?
                };
                if outcome.inference_changed {
                    expected = self.zonk(&expected)?;
                    inference_changed = true;
                }
                Some(Box::new(outcome.pattern))
            }
            _ => return Err(constructor_mismatch(whole_pattern.span)),
        };
        Ok(CheckedPattern {
            pattern: CorePattern::new(
                expected,
                Origin::Source(whole_pattern.span),
                CorePatternKind::Constructor {
                    constructor,
                    payload: checked_payload,
                },
            ),
            inference_changed,
        })
    }

    fn remove_pattern_binders(
        &self,
        context: &mut TypeContext,
        binders: &[BinderId],
    ) -> Result<(), TypeError> {
        for binder in binders {
            if context.binders.remove(binder).is_none() {
                return Err(invalid_state());
            }
        }
        Ok(())
    }

    fn schedule_function_check<'a>(
        &mut self,
        context: &mut TypeContext,
        tasks: &mut Vec<ElaborationTask<'a>>,
        binding_start: usize,
        check: FunctionCheck<'a>,
    ) -> Result<(), TypeError> {
        let FunctionCheck {
            parameter,
            mut domain,
            mut codomain,
            body,
            presentation,
            mut function_type,
            body_check,
        } = check;
        let mut pattern_binders = Vec::new();
        let (checked_pattern, inference_changed) =
            if matches!(&parameter.kind, ResolvedPatternKind::Binder(_)) {
                (None, false)
            } else {
                let checked = self.check_core_pattern(
                    parameter,
                    &domain.ty,
                    context,
                    &mut pattern_binders,
                    GeneratedReason::FunctionLowering,
                )?;
                (Some(checked.pattern), checked.inference_changed)
            };
        if inference_changed {
            domain.ty = self.zonk(&domain.ty)?;
            if !domain.provenance.aligns(&domain.ty) {
                domain.provenance = self.unknown_provenance(&domain.ty)?;
            }
            codomain.ty = self.zonk(&codomain.ty)?;
            if !codomain.provenance.aligns(&codomain.ty) {
                codomain.provenance = self.unknown_provenance(&codomain.ty)?;
            }
            function_type.ty = self.zonk(&function_type.ty)?;
            if !function_type.provenance.aligns(&function_type.ty) {
                function_type.provenance = self.unknown_provenance(&function_type.ty)?;
            }
        }
        let function_parts_align = matches!(
            &function_type.ty,
            Type::Function(expected_domain, expected_codomain)
                if structurally_equal(expected_domain, &domain.ty)
                    && structurally_equal(expected_codomain, &codomain.ty)
        );
        if !function_parts_align || !function_type.provenance.aligns(&function_type.ty) {
            return Err(invalid_state());
        }
        let (parameter_binder, retained_pattern, finish_domain, direct_binder) =
            if let ResolvedPatternKind::Binder(source_binder) = &parameter.kind {
                reserve_context_entry(context, &mut self.type_work)
                    .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
                let context_type = self.clone_type(&domain.ty)?;
                let binder = self.builder.resolved_binder(
                    source_binder.id,
                    domain.ty,
                    Origin::Generated {
                        cause: Box::new(source_binder.origin.clone()),
                        reason: GeneratedReason::FunctionLowering,
                    },
                )?;
                if context
                    .insert_with_provenance(source_binder.id, context_type, domain.provenance)?
                    .is_some()
                {
                    return Err(invalid_state());
                }
                (binder, None, None, Some(source_binder.id))
            } else {
                let pattern = checked_pattern.ok_or_else(invalid_state)?;
                let binder_type = self.clone_type(&domain.ty)?;
                let binder = self.builder.binder(
                    binder_type,
                    Origin::Generated {
                        cause: Box::new(Origin::Source(parameter.span)),
                        reason: GeneratedReason::FunctionLowering,
                    },
                )?;
                (binder, Some(pattern), Some(domain.ty), None)
            };
        let origin = Origin::Generated {
            cause: Box::new(presentation),
            reason: GeneratedReason::FunctionLowering,
        };
        tasks.push(ElaborationTask::FinishFunction {
            direct_binder,
            pattern_binders,
            binder: parameter_binder,
            pattern: retained_pattern,
            domain: finish_domain,
            ty: function_type.ty,
            origin,
            provenance: function_type.provenance,
        });
        match body {
            FunctionBody::Block(block) => schedule_block(
                block,
                Some((codomain, body_check)),
                None,
                tasks,
                binding_start,
                &mut self.type_work,
            )?,
        }
        Ok(())
    }

    fn elaborate_equation_group(
        &mut self,
        equational: &crate::resolved::ResolvedEquationalGlobal,
        function_type: ProvenancedType,
        context: &mut TypeContext,
        definition_span: Span,
    ) -> Result<TypedNode, TypeError> {
        let origin = equational_origin(definition_span, equational);
        self.elaborate_equations(
            &equational.equations,
            function_type,
            context,
            definition_span,
            &origin,
        )
    }

    fn elaborate_equations(
        &mut self,
        equations: &[crate::resolved::ResolvedEquation],
        function_type: ProvenancedType,
        context: &mut TypeContext,
        definition_span: Span,
        presentation: &Origin,
    ) -> Result<TypedNode, TypeError> {
        let Some(first) = equations.first() else {
            return Err(invalid_state());
        };
        let arity = first.patterns.len();
        if arity == 0
            || equations
                .iter()
                .any(|clause| clause.patterns.len() != arity)
        {
            return Err(case_error(
                TypeReason::EquationArity,
                definition_span,
                "equational clauses must have the same positive pattern count",
                None,
            ));
        }
        let mut remainder = ProvenancedType {
            ty: self.clone_type(&function_type.ty)?,
            provenance: function_type.provenance.clone(),
        };
        self.type_work
            .charge(arity.saturating_mul(2))
            .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
        let mut domains = Vec::new();
        domains
            .try_reserve(arity)
            .map_err(|_| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
        for _ in 0..arity {
            if !matches!(remainder.ty, Type::Function(_, _)) {
                return Err(case_error(
                    TypeReason::EquationArity,
                    definition_span,
                    "the equation has more patterns than the declared arrows",
                    None,
                ));
            }
            let (domain, codomain) = remainder.into_function_parts()?;
            domains.push(domain);
            remainder = codomain;
        }

        let mut parameters = Vec::new();
        parameters
            .try_reserve(arity)
            .map_err(|_| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
        for domain in &domains {
            let parameter_type = self.clone_type(&domain.ty)?;
            parameters.push(self.builder.binder(
                parameter_type,
                Origin::Generated {
                    cause: Box::new(presentation.clone()),
                    reason: GeneratedReason::FunctionLowering,
                },
            )?);
        }

        self.type_work
            .charge(arity)
            .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
        let mut domain_types = Vec::new();
        domain_types
            .try_reserve(arity)
            .map_err(|_| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
        for domain in &domains {
            domain_types.push(self.clone_type(&domain.ty)?);
        }

        self.type_work
            .charge(equations.len().saturating_mul(2))
            .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
        let mut coverage_matrix = Vec::new();
        coverage_matrix
            .try_reserve(equations.len())
            .map_err(|_| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
        let mut clause_bodies = Vec::new();
        clause_bodies
            .try_reserve(equations.len())
            .map_err(|_| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
        for clause in equations {
            let mut binder_ids = Vec::new();
            self.type_work
                .charge(arity)
                .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
            let mut patterns = Vec::new();
            patterns
                .try_reserve(arity)
                .map_err(|_| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
            for (pattern, domain) in clause.patterns.iter().zip(&domains) {
                patterns.push(
                    self.check_core_pattern(
                        pattern,
                        &domain.ty,
                        context,
                        &mut binder_ids,
                        GeneratedReason::FunctionLowering,
                    )?
                    .pattern,
                );
            }
            if usefulness_with_budget(
                &coverage_matrix,
                &patterns,
                &domain_types,
                &self.registry,
                &mut self.coverage_work,
            )?
            .is_none()
            {
                self.remove_pattern_binders(context, &binder_ids)?;
                return Err(case_error(
                    TypeReason::RedundantCase,
                    clause.span,
                    "this equation clause can never be selected",
                    None,
                ));
            }
            let expected_type = self.clone_type(&remainder.ty)?;
            let body_result = self.elaborate_expression_with_context(
                ElaborationTask::Check {
                    expression: &clause.body,
                    expected: ProvenancedType {
                        ty: expected_type,
                        provenance: remainder.provenance.clone(),
                    },
                    kind: CheckKind::Definition {
                        result_cause: remainder.provenance.span().unwrap_or(definition_span),
                    },
                },
                context,
            );
            self.remove_pattern_binders(context, &binder_ids)?;
            let body = body_result?;
            coverage_matrix.push(patterns);
            clause_bodies.push((body.node, clause.span));
        }
        if let Some(witness) = missing_witness_for_types_with_budget(
            &coverage_matrix,
            &domain_types,
            &self.registry,
            &mut self.coverage_work,
        )? {
            return Err(case_error(
                TypeReason::NonExhaustive,
                definition_span,
                "these equation clauses do not cover every argument",
                Some(display_witness(&witness, &self.registry)),
            ));
        }

        let direct_clause = arity == 1
            && coverage_matrix.len() == 1
            && matches!(&coverage_matrix[0][0].kind, CorePatternKind::Binder(_));
        let mut body_node = if direct_clause {
            let mut row = coverage_matrix.pop().ok_or_else(invalid_state)?;
            let pattern = row.pop().ok_or_else(invalid_state)?;
            if !row.is_empty() {
                return Err(invalid_state());
            }
            let CorePattern {
                ty,
                origin,
                kind: CorePatternKind::Binder(parameter),
            } = pattern
            else {
                return Err(invalid_state());
            };
            discard_type_iteratively(ty);
            discard_origin_iteratively(origin);
            parameters[0] = parameter;
            clause_bodies
                .pop()
                .map(|(body, _)| body)
                .ok_or_else(invalid_state)?
        } else {
            self.type_work
                .charge(clause_bodies.len())
                .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
            let mut arms = Vec::new();
            arms.try_reserve(clause_bodies.len())
                .map_err(|_| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
            for (patterns, (body, clause_span)) in coverage_matrix.into_iter().zip(clause_bodies) {
                let arm_pattern = if patterns.len() == 1 {
                    patterns.into_iter().next().ok_or_else(invalid_state)?
                } else {
                    self.type_work.charge(1).map_err(|()| {
                        TypeError::Internal(ElaborationFailure::TypeResourceExhausted)
                    })?;
                    let mut tuple_domains = Vec::new();
                    tuple_domains.try_reserve(arity).map_err(|_| {
                        TypeError::Internal(ElaborationFailure::TypeResourceExhausted)
                    })?;
                    for domain in &domains {
                        tuple_domains.push(self.clone_type(&domain.ty)?);
                    }
                    CorePattern::new(
                        Type::Tuple(tuple_domains.into_boxed_slice()),
                        Origin::Source(clause_span),
                        CorePatternKind::Tuple(patterns.into_boxed_slice()),
                    )
                };
                arms.push(CoreMatchArm::new(
                    arm_pattern,
                    body,
                    Origin::Source(clause_span),
                ));
            }
            self.type_work
                .charge(parameters.len())
                .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
            let mut arguments = Vec::new();
            arguments
                .try_reserve(parameters.len())
                .map_err(|_| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
            for (parameter, domain) in parameters.iter().zip(&domains) {
                let variable_type = self.clone_type(&domain.ty)?;
                arguments.push(self.builder.variable(
                    parameter.id(),
                    variable_type,
                    Origin::Source(definition_span),
                )?);
            }
            let scrutinee = if arguments.len() == 1 {
                arguments[0]
            } else {
                self.type_work
                    .charge(1)
                    .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
                let mut tuple_domains = Vec::new();
                tuple_domains
                    .try_reserve(domain_types.len())
                    .map_err(|_| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
                for domain in &domain_types {
                    tuple_domains.push(self.clone_type(domain)?);
                }
                let ty = Type::Tuple(tuple_domains.into_boxed_slice());
                self.builder
                    .tuple(arguments, ty, Origin::Source(definition_span))?
            };
            let core_remainder = self.clone_type(&remainder.ty)?;
            self.builder.match_expression(
                scrutinee,
                arms,
                core_remainder,
                Origin::Source(definition_span),
            )?
        };
        let mut body_type = self.clone_type(&remainder.ty)?;
        for (parameter, domain) in parameters.into_iter().zip(&domains).rev() {
            let domain_type = self.clone_type(&domain.ty)?;
            self.type_work
                .charge(1)
                .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
            let ty = Type::Function(Box::new(domain_type), Box::new(body_type));
            let core_ty = self.clone_type(&ty)?;
            body_node = self.builder.function(
                parameter,
                body_node,
                core_ty,
                Origin::Generated {
                    cause: Box::new(presentation.clone()),
                    reason: GeneratedReason::FunctionLowering,
                },
            )?;
            body_type = ty;
        }
        if !same_type(&body_type, &function_type.ty) {
            return Err(invalid_state());
        }
        Ok(TypedNode {
            node: body_node,
            ty: body_type,
            provenance: function_type.provenance,
        })
    }

    fn elaborate_operational_function(
        &mut self,
        operational: &crate::resolved::ResolvedInlineOperationalGlobal,
        function_type: ProvenancedType,
        context: &mut TypeContext,
        definition_span: Span,
    ) -> Result<TypedNode, TypeError> {
        let (domain_ty, codomain_ty) =
            clone_function_parts_with_budget(&function_type.ty, &mut self.type_work)
                .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
        let (domain_provenance, codomain_provenance) =
            function_type.provenance.function_parts(&function_type.ty)?;
        let domain = ProvenancedType {
            ty: domain_ty,
            provenance: domain_provenance,
        };
        let codomain = ProvenancedType {
            ty: codomain_ty,
            provenance: codomain_provenance,
        };
        let mut binder_ids = Vec::new();
        let pattern = if operational.header.parameters.len() == 1 {
            self.check_core_pattern(
                &operational.header.parameters[0].pattern,
                &domain.ty,
                context,
                &mut binder_ids,
                GeneratedReason::FunctionLowering,
            )?
            .pattern
        } else {
            let Type::Tuple(types) = &domain.ty else {
                return Err(invalid_state());
            };
            if types.len() != operational.header.parameters.len() {
                return Err(invalid_state());
            }
            self.type_work
                .charge(types.len())
                .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
            let mut elements = Vec::new();
            elements
                .try_reserve(types.len())
                .map_err(|_| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
            for (parameter, ty) in operational.header.parameters.iter().zip(types) {
                elements.push(
                    self.check_core_pattern(
                        &parameter.pattern,
                        ty,
                        context,
                        &mut binder_ids,
                        GeneratedReason::FunctionLowering,
                    )?
                    .pattern,
                );
            }
            CorePattern::new(
                self.clone_type(&domain.ty)?,
                Origin::Source(operational.header.span),
                CorePatternKind::Tuple(elements.into_boxed_slice()),
            )
        };
        let (parameter, retained_pattern) = match pattern {
            CorePattern {
                ty,
                origin,
                kind: CorePatternKind::Binder(binder),
            } => {
                discard_type_iteratively(ty);
                discard_origin_iteratively(origin);
                (binder, None)
            }
            pattern => {
                let binder_type = self.clone_type(&domain.ty)?;
                (
                    self.builder
                        .binder(binder_type, Origin::Source(operational.header.span))?,
                    Some(pattern),
                )
            }
        };
        let body_result = self.elaborate_expression_with_context(
            ElaborationTask::CheckBlock {
                block: &operational.body,
                expected: codomain,
                kind: CheckKind::Definition {
                    result_cause: operational.header.result_type.span,
                },
            },
            context,
        );
        self.remove_pattern_binders(context, &binder_ids)?;
        let mut body = body_result?;
        if let Some(pattern) = retained_pattern {
            let mut matrix = vec![vec![pattern]];
            if let Some(witness) = missing_witness_for_types_with_budget(
                &matrix,
                std::slice::from_ref(&domain.ty),
                &self.registry,
                &mut self.coverage_work,
            )? {
                return Err(case_error(
                    TypeReason::RefutableFunctionDomain,
                    operational.header.span,
                    "this operational parameter pattern is not exhaustive",
                    Some(display_witness(&witness, &self.registry)),
                ));
            }
            let mut row = matrix.pop().ok_or_else(invalid_state)?;
            let pattern = row.pop().ok_or_else(invalid_state)?;
            if !row.is_empty() {
                return Err(invalid_state());
            }
            let scrutinee_type = self.clone_type(&domain.ty)?;
            let scrutinee = self.builder.variable(
                parameter.id(),
                scrutinee_type,
                Origin::Source(operational.header.span),
            )?;
            let core_body_type = self.clone_type(&body.ty)?;
            body.node = self.builder.match_expression(
                scrutinee,
                vec![CoreMatchArm::new(
                    pattern,
                    body.node,
                    Origin::Source(operational.header.span),
                )],
                core_body_type,
                Origin::Source(operational.header.span),
            )?;
        }
        let core_function_type = self.clone_type(&function_type.ty)?;
        let node = self.builder.function(
            parameter,
            body.node,
            core_function_type,
            Origin::Generated {
                cause: Box::new(operational_origin(definition_span, operational)),
                reason: GeneratedReason::FunctionLowering,
            },
        )?;
        Ok(TypedNode {
            node,
            ty: function_type.ty,
            provenance: function_type.provenance,
        })
    }
}

fn check_interface_declarations(
    module: &ResolvedModule,
    budget: &mut InterfaceConstraintBudget,
) -> Result<Box<[CheckedInterface]>, TypeError> {
    budget
        .charge(module.interfaces().len())
        .map_err(|()| constraint_resource())?;
    let mut checked = Vec::new();
    checked
        .try_reserve(module.interfaces().len())
        .map_err(|_| constraint_resource())?;
    for (source_index, interface) in module.interfaces().iter().enumerate() {
        budget.charge(1).map_err(|()| constraint_resource())?;
        for method in &interface.methods {
            budget
                .charge(method.type_parameters.len().saturating_add(1))
                .map_err(|()| constraint_resource())?;
            let parameter_occurs =
                type_contains_variable(&method.annotation.ty, interface.parameter.id, budget)
                    .map_err(|()| constraint_resource())?;
            if !method.type_parameters.is_empty() || !parameter_occurs {
                let mut diagnostic = Diagnostic::new(
                    InterfaceReason::MethodParameter,
                    SourceLabel::new(
                        method.span,
                        "this method signature must use only its interface parameter",
                    ),
                );
                diagnostic.related.push(SourceLabel::new(
                    interface.parameter.origin.primary_span(),
                    "the interface parameter is declared here",
                ));
                return Err(TypeError::Interface(Box::new(diagnostic)));
            }
            if !matches!(&method.annotation.ty, Type::Function(_, _)) {
                let mut diagnostic = Diagnostic::new(
                    InterfaceReason::MethodNotFunction,
                    SourceLabel::new(
                        method.annotation.span,
                        "this method type must have a top-level function arrow",
                    ),
                );
                diagnostic.related.push(SourceLabel::new(
                    method.span,
                    "the method signature is declared here",
                ));
                return Err(TypeError::Interface(Box::new(diagnostic)));
            }
        }
        checked.push(CheckedInterface {
            source_index,
            id: interface.id,
        });
    }
    Ok(checked.into_boxed_slice())
}

fn check_global_requirements(
    module: &ResolvedModule,
    checked_interfaces: &[CheckedInterface],
    budget: &mut InterfaceConstraintBudget,
) -> Result<(), TypeError> {
    for definition in module.definitions() {
        let (name, requirements, value_type_count) = match &definition.kind {
            ResolvedDefinitionKind::Equational(global) => {
                (&global.interface.name, &global.interface.requirements, 1)
            }
            ResolvedDefinitionKind::InlineOperational(global) => (
                &global.header.name,
                &global.header.requirements,
                global.header.parameters.len().saturating_add(1),
            ),
        };
        if requirements.is_empty() {
            continue;
        }
        budget.charge(1).map_err(|()| constraint_resource())?;
        budget
            .charge(value_type_count)
            .map_err(|()| constraint_resource())?;
        let mut value_types = Vec::new();
        value_types
            .try_reserve(value_type_count)
            .map_err(|_| constraint_resource())?;
        match &definition.kind {
            ResolvedDefinitionKind::Equational(global) => {
                value_types.push(&global.interface.annotation.ty);
            }
            ResolvedDefinitionKind::InlineOperational(global) => {
                value_types.extend(
                    global
                        .header
                        .parameters
                        .iter()
                        .map(|parameter| &parameter.annotation.ty),
                );
                value_types.push(&global.header.result_type.ty);
            }
        }
        let public = module.export_candidate().term(&name.spelling).is_some();
        if public {
            for requirement in requirements.iter() {
                budget.charge(1).map_err(|()| constraint_resource())?;
                let private = checked_interface(
                    module,
                    checked_interfaces,
                    requirement.interface.id,
                    budget,
                )?
                .filter(|interface| !interface.is_public());
                if let Some(interface) = private {
                    let mut diagnostic = Diagnostic::new(
                        InterfaceReason::ConstraintPrivateInterface,
                        SourceLabel::new(
                            requirement.span,
                            "a public global cannot expose this private interface",
                        ),
                    );
                    diagnostic.related.push(SourceLabel::new(
                        interface.span(),
                        "the private interface is declared here",
                    ));
                    return Err(TypeError::Interface(Box::new(diagnostic)));
                }
            }
        }
        for (index, requirement) in requirements.iter().enumerate() {
            budget.charge(1).map_err(|()| constraint_resource())?;
            let mut duplicate = None;
            for first in &requirements[..index] {
                budget.charge(1).map_err(|()| constraint_resource())?;
                if first.interface.id == requirement.interface.id
                    && same_type_with_constraint_budget(
                        &first.argument.ty,
                        &requirement.argument.ty,
                        budget,
                    )
                    .map_err(|()| constraint_resource())?
                {
                    duplicate = Some(first);
                    break;
                }
            }
            if let Some(first) = duplicate {
                let mut diagnostic = Diagnostic::new(
                    InterfaceReason::DuplicateRequirement,
                    SourceLabel::new(requirement.span, "this requirement is already declared"),
                );
                diagnostic.related.push(SourceLabel::new(
                    first.span,
                    "the first identical requirement is here",
                ));
                return Err(TypeError::Interface(Box::new(diagnostic)));
            }
        }
        for requirement in requirements.iter() {
            budget.charge(1).map_err(|()| constraint_resource())?;
            if let Some(variable) =
                first_variable_absent_from_types(&requirement.argument.ty, &value_types, budget)
                    .map_err(|()| constraint_resource())?
            {
                let mut diagnostic = Diagnostic::new(
                    InterfaceReason::UndeterminedParameter,
                    SourceLabel::new(
                        requirement.span,
                        "this requirement parameter is not determined by the value type",
                    ),
                );
                if let Some(parameter) = module.registry().type_variable(variable) {
                    diagnostic.related.push(SourceLabel::new(
                        parameter.origin.primary_span(),
                        "this candidate parameter occurs only in a requirement",
                    ));
                }
                return Err(TypeError::Interface(Box::new(diagnostic)));
            }
        }
    }
    Ok(())
}

fn check_implementation_headers_and_membership(
    module: &ResolvedModule,
    checked_interfaces: &[CheckedInterface],
    budget: &mut InterfaceConstraintBudget,
) -> Result<Box<[CheckedImplementation]>, TypeError> {
    for implementation in module.implementations() {
        check_implementation_header(module, checked_interfaces, implementation, budget)?;
    }
    check_effective_implementation_overlap(module, budget)?;

    budget
        .charge(module.implementations().len())
        .map_err(|()| constraint_resource())?;
    let mut checked = Vec::new();
    checked
        .try_reserve(module.implementations().len())
        .map_err(|_| constraint_resource())?;
    for (source_index, implementation) in module.implementations().iter().enumerate() {
        checked.push(check_implementation_membership(
            module,
            checked_interfaces,
            source_index,
            implementation,
            budget,
        )?);
    }
    Ok(checked.into_boxed_slice())
}

#[derive(Clone, Copy)]
enum ImplementationHeadRef<'a> {
    Imported(&'a crate::resolved::ImportedImplementationFact),
    Local(&'a crate::resolved::ResolvedImplementation),
}

impl<'a> ImplementationHeadRef<'a> {
    const fn id(self) -> crate::interface::ImplId {
        match self {
            Self::Imported(implementation) => implementation.fact.id,
            Self::Local(implementation) => implementation.id,
        }
    }

    const fn interface(self) -> crate::interface::InterfaceId {
        match self {
            Self::Imported(implementation) => implementation.fact.interface,
            Self::Local(implementation) => implementation.interface.id,
        }
    }

    const fn argument(self) -> &'a Type {
        match self {
            Self::Imported(implementation) => &implementation.fact.argument,
            Self::Local(implementation) => &implementation.argument.ty,
        }
    }

    const fn head_parameters(self) -> &'a [crate::resolved::ResolvedTypeVariable] {
        match self {
            Self::Imported(implementation) => &implementation.fact.head_parameters,
            Self::Local(implementation) => &implementation.head_parameters,
        }
    }

    const fn primary_span(self) -> Span {
        match self {
            Self::Imported(implementation) => implementation.available_at,
            Self::Local(implementation) => implementation.argument.span,
        }
    }

    const fn definition_span(self) -> Span {
        match self {
            Self::Imported(implementation) => implementation.fact.span,
            Self::Local(implementation) => implementation.argument.span,
        }
    }

    const fn import_span(self) -> Option<Span> {
        match self {
            Self::Imported(implementation) => Some(implementation.available_at),
            Self::Local(_) => None,
        }
    }
}

fn check_effective_implementation_overlap(
    module: &ResolvedModule,
    budget: &mut InterfaceConstraintBudget,
) -> Result<(), TypeError> {
    let imported_count = module.imported_facts().implementations().count();
    budget
        .charge(imported_count.saturating_add(module.implementations().len()))
        .map_err(|()| constraint_resource())?;
    let mut imported = Vec::new();
    imported
        .try_reserve(imported_count)
        .map_err(|_| constraint_resource())?;
    imported.extend(
        module
            .imported_facts()
            .implementations()
            .map(ImplementationHeadRef::Imported),
    );
    let mut effective = imported;
    effective
        .try_reserve(module.implementations().len())
        .map_err(|_| constraint_resource())?;
    effective.extend(
        module
            .implementations()
            .iter()
            .map(ImplementationHeadRef::Local),
    );

    check_effective_implementation_heads(&effective, budget)
}

fn check_effective_implementation_heads(
    effective: &[ImplementationHeadRef<'_>],
    budget: &mut InterfaceConstraintBudget,
) -> Result<(), TypeError> {
    for (index, implementation) in effective.iter().copied().enumerate() {
        budget.charge(1).map_err(|()| constraint_resource())?;
        for previous in effective[..index].iter().copied() {
            budget.charge(1).map_err(|()| constraint_resource())?;
            if implementation.interface() != previous.interface()
                || implementation.id() == previous.id()
            {
                continue;
            }
            let overlaps = implementation_heads_overlap(
                previous
                    .head_parameters()
                    .iter()
                    .map(|parameter| parameter.id),
                previous.argument(),
                implementation
                    .head_parameters()
                    .iter()
                    .map(|parameter| parameter.id),
                implementation.argument(),
                budget,
            );
            let overlaps = match overlaps {
                Ok(overlaps) => overlaps,
                Err(OverlapFailure::Resource) => return Err(constraint_resource()),
                Err(OverlapFailure::InvalidState) => return Err(invalid_state()),
            };
            if overlaps {
                let mut diagnostic = Diagnostic::new(
                    InterfaceReason::ImplOverlap,
                    SourceLabel::new(
                        implementation.primary_span(),
                        "this implementation overlaps an earlier available implementation",
                    ),
                );
                diagnostic.related.push(SourceLabel::new(
                    previous.definition_span(),
                    "the earlier overlapping implementation head is here",
                ));
                if let Some(span) = previous.import_span() {
                    diagnostic.related.push(SourceLabel::new(
                        span,
                        "the earlier implementation became available through this import",
                    ));
                }
                if implementation.import_span().is_some() {
                    diagnostic.related.push(SourceLabel::new(
                        implementation.definition_span(),
                        "the later implementation is defined here",
                    ));
                }
                return Err(TypeError::Interface(Box::new(diagnostic)));
            }
        }
    }
    Ok(())
}

fn check_implementation_header(
    module: &ResolvedModule,
    checked_interfaces: &[CheckedInterface],
    implementation: &crate::resolved::ResolvedImplementation,
    budget: &mut InterfaceConstraintBudget,
) -> Result<(), TypeError> {
    budget
        .charge(
            implementation
                .head_parameters
                .len()
                .saturating_add(implementation.prerequisite_only_parameters.len())
                .saturating_add(implementation.prerequisites.len())
                .saturating_add(1),
        )
        .map_err(|()| constraint_resource())?;
    budget
        .charge_type(&implementation.argument.ty)
        .map_err(|()| constraint_resource())?;
    for prerequisite in &implementation.prerequisites {
        budget
            .charge_type(&prerequisite.argument.ty)
            .map_err(|()| constraint_resource())?;
    }

    if implementation.public {
        if let Some(interface) = checked_interface(
            module,
            checked_interfaces,
            implementation.interface.id,
            budget,
        )? && !interface.is_public()
        {
            let mut diagnostic = Diagnostic::new(
                InterfaceReason::ImplPrivateInterface,
                SourceLabel::new(
                    implementation.interface.origin.primary_span(),
                    "a public implementation cannot expose this private interface",
                ),
            );
            diagnostic.related.push(SourceLabel::new(
                interface.span(),
                "the private interface is declared here",
            ));
            return Err(TypeError::Interface(Box::new(diagnostic)));
        }
        for prerequisite in &implementation.prerequisites {
            if let Some(interface) = checked_interface(
                module,
                checked_interfaces,
                prerequisite.interface.id,
                budget,
            )? && !interface.is_public()
            {
                let mut diagnostic = Diagnostic::new(
                    InterfaceReason::ImplPrivateInterface,
                    SourceLabel::new(
                        prerequisite.span,
                        "a public implementation cannot expose this private prerequisite",
                    ),
                );
                diagnostic.related.push(SourceLabel::new(
                    interface.span(),
                    "the private interface is declared here",
                ));
                return Err(TypeError::Interface(Box::new(diagnostic)));
            }
        }
    }

    if matches!(implementation.argument.ty, Type::Variable(_)) {
        let mut diagnostic = Diagnostic::new(
            InterfaceReason::ImplVariableHead,
            SourceLabel::new(
                implementation.argument.span,
                "an implementation head cannot be a bare type variable",
            ),
        );
        diagnostic.related.push(SourceLabel::new(
            implementation.interface.origin.primary_span(),
            "this is the implemented interface",
        ));
        return Err(TypeError::Interface(Box::new(diagnostic)));
    }

    if let Some(parameter) = implementation.prerequisite_only_parameters.first() {
        let mut diagnostic = Diagnostic::new(
            InterfaceReason::ImplPrerequisiteVariable,
            SourceLabel::new(
                parameter.origin.primary_span(),
                "this prerequisite variable does not occur in the implementation head",
            ),
        );
        diagnostic.related.push(SourceLabel::new(
            implementation.argument.span,
            "the implementation head determines every prerequisite variable",
        ));
        return Err(TypeError::Interface(Box::new(diagnostic)));
    }

    let local_interface_owner = implementation.interface.id.module() == module.module();
    let local_nominal_owner = match implementation.argument.ty {
        Type::Nominal(id) | Type::AppliedNominal(id, _) => id.module() == module.module(),
        Type::Int
        | Type::Bool
        | Type::Unit
        | Type::Tuple(_)
        | Type::Function(_, _)
        | Type::Forall(_, _)
        | Type::Variable(_)
        | Type::Inference(_) => false,
    };
    if !local_interface_owner && !local_nominal_owner {
        let mut diagnostic = Diagnostic::new(
            InterfaceReason::ImplOrphan,
            SourceLabel::new(
                implementation.argument.span,
                "this module owns neither the interface nor the outer nominal type",
            ),
        );
        diagnostic.related.push(SourceLabel::new(
            implementation.interface.origin.primary_span(),
            "the foreign interface is selected here",
        ));
        return Err(TypeError::Interface(Box::new(diagnostic)));
    }

    for prerequisite in &implementation.prerequisites {
        if !implementation_prerequisite_terminates(
            &prerequisite.argument.ty,
            &implementation.argument.ty,
            budget,
        )
        .map_err(|()| constraint_resource())?
        {
            let mut diagnostic = Diagnostic::new(
                InterfaceReason::ImplPrerequisiteNotDecreasing,
                SourceLabel::new(
                    prerequisite.span,
                    "this generic prerequisite does not strictly decrease",
                ),
            );
            diagnostic.related.push(SourceLabel::new(
                implementation.argument.span,
                "the prerequisite must be a strict subterm of this head",
            ));
            return Err(TypeError::Interface(Box::new(diagnostic)));
        }
    }
    Ok(())
}

fn check_implementation_membership(
    module: &ResolvedModule,
    checked_interfaces: &[CheckedInterface],
    source_index: usize,
    implementation: &crate::resolved::ResolvedImplementation,
    budget: &mut InterfaceConstraintBudget,
) -> Result<CheckedImplementation, TypeError> {
    let interface = checked_interface(
        module,
        checked_interfaces,
        implementation.interface.id,
        budget,
    )?
    .ok_or_else(invalid_state)?;
    budget
        .charge(implementation.method_groups.len())
        .map_err(|()| constraint_resource())?;
    let mut supplied = HashMap::new();
    supplied
        .try_reserve(implementation.method_groups.len())
        .map_err(|_| constraint_resource())?;
    for (source_group, group) in implementation.method_groups.iter().enumerate() {
        budget.charge(1).map_err(|()| constraint_resource())?;
        let Some(method) = group
            .method
            .filter(|method| method.interface() == interface.id())
        else {
            let mut diagnostic = Diagnostic::new(
                InterfaceReason::ImplExtraMethod,
                SourceLabel::new(
                    group.span,
                    "this method is not declared by the implemented interface",
                ),
            );
            diagnostic.related.push(SourceLabel::new(
                interface.span(),
                "the implemented interface is declared here",
            ));
            return Err(TypeError::Interface(Box::new(diagnostic)));
        };
        if let Some((_, first)) = supplied.insert(method, (source_group, group)) {
            let mut diagnostic = Diagnostic::new(
                InterfaceReason::ImplDuplicateMethod,
                SourceLabel::new(group.span, "this interface method is implemented twice"),
            );
            diagnostic.related.push(SourceLabel::new(
                first.span,
                "the first method group is here",
            ));
            return Err(TypeError::Interface(Box::new(diagnostic)));
        }
    }
    for method_index in 0..interface.method_count() {
        let method = interface.method(method_index).ok_or_else(invalid_state)?;
        budget.charge(1).map_err(|()| constraint_resource())?;
        if !supplied.contains_key(&method.id()) {
            let mut diagnostic = Diagnostic::new(
                InterfaceReason::ImplMissingMethod,
                SourceLabel::new(
                    implementation.span,
                    "this implementation does not supply every interface method",
                ),
            );
            diagnostic.related.push(SourceLabel::new(
                method.span(),
                "this required method is missing",
            ));
            return Err(TypeError::Interface(Box::new(diagnostic)));
        }
    }

    budget
        .charge(interface.method_count().saturating_add(1))
        .map_err(|()| constraint_resource())?;
    let mut methods = Vec::new();
    methods
        .try_reserve(interface.method_count())
        .map_err(|_| constraint_resource())?;
    for method_index in 0..interface.method_count() {
        let method = interface.method(method_index).ok_or_else(invalid_state)?;
        let (source_group, group) = supplied.get(&method.id()).ok_or_else(invalid_state)?;
        let identity = group.identity.ok_or_else(invalid_state)?;
        if identity != crate::interface::ImplMethodId::new(implementation.id, method.id()) {
            return Err(invalid_state());
        }
        methods.push(CheckedImplMethod {
            source_group: *source_group,
            id: identity,
            method: method.id(),
            binder: group.binder.id,
        });
    }
    Ok(CheckedImplementation {
        source_index,
        id: implementation.id,
        interface: implementation.interface.id,
        methods: methods.into_boxed_slice(),
    })
}

#[derive(Clone, Copy)]
enum CheckedInterfaceRef<'a> {
    Local(&'a crate::resolved::ResolvedInterfaceDeclaration),
    Imported(&'a crate::resolved::CheckedInterfaceFact),
}

impl<'a> CheckedInterfaceRef<'a> {
    const fn id(self) -> crate::interface::InterfaceId {
        match self {
            Self::Local(interface) => interface.id,
            Self::Imported(interface) => interface.id,
        }
    }

    const fn is_public(self) -> bool {
        match self {
            Self::Local(interface) => interface.public,
            Self::Imported(_) => true,
        }
    }

    const fn parameter(self) -> TypeVariableId {
        match self {
            Self::Local(interface) => interface.parameter.id,
            Self::Imported(interface) => interface.parameter.id,
        }
    }

    const fn span(self) -> Span {
        match self {
            Self::Local(interface) => interface.span,
            Self::Imported(interface) => interface.span,
        }
    }

    fn method_count(self) -> usize {
        match self {
            Self::Local(interface) => interface.methods.len(),
            Self::Imported(interface) => interface.methods.len(),
        }
    }

    fn method(self, index: usize) -> Option<CheckedInterfaceMethodRef<'a>> {
        match self {
            Self::Local(interface) => interface
                .methods
                .get(index)
                .map(CheckedInterfaceMethodRef::Local),
            Self::Imported(interface) => interface
                .methods
                .get(index)
                .map(CheckedInterfaceMethodRef::Imported),
        }
    }
}

#[derive(Clone, Copy)]
enum CheckedInterfaceMethodRef<'a> {
    Local(&'a crate::resolved::ResolvedInterfaceMethod),
    Imported(&'a crate::resolved::CheckedInterfaceMethodFact),
}

impl<'a> CheckedInterfaceMethodRef<'a> {
    const fn id(self) -> crate::interface::MethodId {
        match self {
            Self::Local(method) => method.id,
            Self::Imported(method) => method.id,
        }
    }

    const fn value_type(self) -> &'a Type {
        match self {
            Self::Local(method) => &method.annotation.ty,
            Self::Imported(method) => &method.value_type,
        }
    }

    const fn annotation_span(self) -> Span {
        match self {
            Self::Local(method) => method.annotation.span,
            Self::Imported(method) => method.span,
        }
    }

    const fn span(self) -> Span {
        match self {
            Self::Local(method) => method.span,
            Self::Imported(method) => method.span,
        }
    }
}

fn checked_interface<'a>(
    module: &'a ResolvedModule,
    checked_interfaces: &[CheckedInterface],
    id: crate::interface::InterfaceId,
    budget: &mut InterfaceConstraintBudget,
) -> Result<Option<CheckedInterfaceRef<'a>>, TypeError> {
    for checked in checked_interfaces {
        budget.charge(1).map_err(|()| constraint_resource())?;
        let interface = module
            .interfaces()
            .get(checked.source_index)
            .ok_or_else(invalid_state)?;
        if interface.id != checked.id {
            return Err(invalid_state());
        }
        if checked.id == id {
            return Ok(Some(CheckedInterfaceRef::Local(interface)));
        }
    }
    budget.charge(1).map_err(|()| constraint_resource())?;
    Ok(module
        .imported_facts()
        .interface(id)
        .map(CheckedInterfaceRef::Imported))
}

fn constraint_resource() -> TypeError {
    TypeError::Internal(ElaborationFailure::ConstraintResourceExhausted)
}

fn selection_failure(error: SelectionFailure, span: Option<Span>) -> TypeError {
    match error {
        SelectionFailure::Reason(reason) => {
            let Some(span) = span else {
                return invalid_state();
            };
            TypeError::Interface(Box::new(Diagnostic::new(
                reason,
                SourceLabel::new(span, selection_reason_message(reason)),
            )))
        }
        SelectionFailure::TypeResource => {
            TypeError::Internal(ElaborationFailure::TypeResourceExhausted)
        }
        SelectionFailure::ConstraintResource => constraint_resource(),
        SelectionFailure::InvalidState => invalid_state(),
    }
}

fn selected_obligation_error(error: SelectionError) -> TypeError {
    let SelectionFailure::Reason(reason) = error.failure() else {
        return selection_failure(error.failure(), error.span());
    };
    let Some(span) = error.span() else {
        return invalid_state();
    };
    let mut diagnostic = Diagnostic::new(
        reason,
        SourceLabel::new(span, selection_reason_message(reason)),
    );
    if let Some(declaration_span) = error.declaration_span() {
        diagnostic.related.push(SourceLabel::new(
            declaration_span,
            "this declaration introduced the interface obligation",
        ));
    }
    if let Some(import_span) = error.import_span() {
        diagnostic.related.push(SourceLabel::new(
            import_span,
            "this import made the declaration available",
        ));
    }
    for cause in error.causes() {
        let message = match cause.kind() {
            SelectionCauseKind::Interface => {
                "this interface declaration participates in the failing selection"
            }
            SelectionCauseKind::Implementation => {
                "selection followed this available implementation"
            }
            SelectionCauseKind::ImplementationMethod => {
                "this implementation method supplies the selected evidence"
            }
            SelectionCauseKind::ImplementationImport => {
                "this import made the selected implementation available"
            }
        };
        diagnostic
            .related
            .push(SourceLabel::new(cause.span(), message));
    }
    TypeError::Interface(Box::new(diagnostic))
}

const fn selection_reason_message(reason: InterfaceReason) -> &'static str {
    match reason {
        InterfaceReason::Unsatisfied => {
            "no available implementation satisfies this interface obligation"
        }
        InterfaceReason::Ambiguous => "this interface obligation's type is not determined",
        InterfaceReason::Cycle => {
            "selecting this interface obligation re-enters an active obligation"
        }
        _ => "this interface obligation is invalid",
    }
}

fn type_contains_variable(
    root: &Type,
    needle: TypeVariableId,
    budget: &mut InterfaceConstraintBudget,
) -> Result<bool, ()> {
    visit_type_variables(root, budget, |variable, _| Ok(variable == needle))
}

fn first_variable_absent_from_types(
    root: &Type,
    value_types: &[&Type],
    budget: &mut InterfaceConstraintBudget,
) -> Result<Option<TypeVariableId>, ()> {
    let mut seen = HashSet::new();
    let mut absent = None;
    visit_type_variables(root, budget, |variable, budget| {
        budget.charge(1)?;
        if seen.contains(&variable) {
            return Ok(false);
        }
        budget.charge(1)?;
        seen.try_reserve(1).map_err(|_| ())?;
        seen.insert(variable);
        for value_type in value_types {
            budget.charge(1)?;
            if type_contains_variable(value_type, variable, budget)? {
                return Ok(false);
            }
        }
        absent = Some(variable);
        Ok(true)
    })?;
    Ok(absent)
}

fn visit_type_variables<F>(
    root: &Type,
    budget: &mut InterfaceConstraintBudget,
    mut visit: F,
) -> Result<bool, ()>
where
    F: FnMut(TypeVariableId, &mut InterfaceConstraintBudget) -> Result<bool, ()>,
{
    budget.charge(1)?;
    let mut pending = Vec::new();
    pending.try_reserve(1).map_err(|_| ())?;
    pending.push(root);
    while let Some(ty) = pending.pop() {
        budget.charge(1)?;
        match ty {
            Type::Variable(variable) => {
                if visit(*variable, budget)? {
                    return Ok(true);
                }
            }
            Type::Tuple(elements) | Type::AppliedNominal(_, elements) => {
                budget.charge(elements.len())?;
                pending.try_reserve(elements.len()).map_err(|_| ())?;
                pending.extend(elements.iter().rev());
            }
            Type::Function(domain, codomain) => {
                budget.charge(2)?;
                pending.try_reserve(2).map_err(|_| ())?;
                pending.push(codomain);
                pending.push(domain);
            }
            Type::Forall(parameters, body) => {
                budget.charge(parameters.len().saturating_add(1))?;
                pending.try_reserve(1).map_err(|_| ())?;
                pending.push(body);
            }
            Type::Int | Type::Bool | Type::Unit | Type::Nominal(_) | Type::Inference(_) => {}
        }
    }
    Ok(false)
}

/// Checks every local definition and publishes an immutable dependency summary.
///
/// No Core program escapes this phase. A summary is created only after all
/// bodies have checked against their declared interfaces.
///
/// # Errors
///
/// Returns the first source typing error or bounded internal elaboration
/// failure. Failed modules do not produce a [`CheckedModule`].
pub fn check_module(resolved: ResolvedModule) -> Result<CheckedModule, TypeError> {
    let mut type_work = TypeWorkBudget::default();
    let mut coverage_work = UsefulnessBudget::default();
    let mut constraint_work = InterfaceConstraintBudget::default();
    check_module_with_budget(
        resolved,
        &mut type_work,
        &mut coverage_work,
        &mut constraint_work,
    )
}

/// Checks one module while sharing type-work accounting across a graph pass.
pub(crate) fn check_module_with_budget(
    mut resolved: ResolvedModule,
    type_work: &mut TypeWorkBudget,
    coverage_work: &mut UsefulnessBudget,
    constraint_work: &mut InterfaceConstraintBudget,
) -> Result<CheckedModule, TypeError> {
    let checked_interfaces = check_interface_declarations(&resolved, constraint_work)?;
    check_global_requirements(&resolved, &checked_interfaces, constraint_work)?;
    let checked_implementations = check_implementation_headers_and_membership(
        &resolved,
        &checked_interfaces,
        constraint_work,
    )?;
    let mut elaborator =
        Elaborator::for_module_with_work(&resolved, type_work.clone(), coverage_work.clone())?;
    let result: Result<_, TypeError> = (|| {
        let interface_facts = checked_interface_facts(
            &resolved,
            &checked_interfaces,
            &mut elaborator.type_work,
            constraint_work,
        )?;
        let schemes = elaborator.checked_module_schemes(resolved.definitions())?;
        elaborator.selection = Some(build_evidence_selector(
            &resolved,
            &schemes,
            &interface_facts,
            &checked_implementations,
            &mut elaborator.type_work,
            constraint_work,
        )?);
        let implementation_facts = elaborator.check_module_bodies(
            &resolved,
            &schemes,
            &checked_interfaces,
            &checked_implementations,
            constraint_work,
        )?;
        let selector = elaborator.selection.as_ref().ok_or_else(invalid_state)?;
        audit_checked_body_evidence(
            resolved.definitions(),
            resolved.implementations(),
            |binder| selector.scheme(binder),
            |method| selector.method(method).is_some(),
            constraint_work,
        )
        .map_err(|failure| match failure {
            EvidenceAuditFailure::InvalidState => invalid_state(),
            EvidenceAuditFailure::ConstraintResource => constraint_resource(),
        })?;
        let exports = ExportSummary::freeze(
            &resolved,
            &schemes,
            &interface_facts,
            &checked_implementations,
            &implementation_facts,
            &mut elaborator.type_work,
            constraint_work,
        )
        .map_err(resolved_build_error)?;
        Ok((
            schemes,
            checked_implementations,
            interface_facts,
            implementation_facts,
            exports,
        ))
    })();
    *type_work = std::mem::take(&mut elaborator.type_work);
    *coverage_work = std::mem::take(&mut elaborator.coverage_work);
    let (schemes, checked_implementations, interface_facts, implementation_facts, exports) =
        result?;
    let imported_implementation_count = resolved.imported_facts().implementations().count();
    let local_implementation_count = resolved.implementations().len();
    constraint_work
        .charge(
            imported_implementation_count
                .saturating_add(local_implementation_count)
                .saturating_add(resolved.definitions().len()),
        )
        .map_err(|()| constraint_resource())?;
    let mut available_implementations = Vec::new();
    available_implementations
        .try_reserve(imported_implementation_count.saturating_add(local_implementation_count))
        .map_err(|_| constraint_resource())?;
    available_implementations.extend(resolved.imported_facts().implementations().map(|imported| {
        AvailableImplementation::direct_import(
            imported.fact.id,
            imported.direct_dependency,
            imported.available_at,
        )
    }));
    available_implementations.extend(
        resolved
            .implementations()
            .iter()
            .map(|implementation| AvailableImplementation::local(implementation.id)),
    );
    let CheckedBodyBuffers {
        mut definitions,
        mut implementations,
    } = reserve_checked_body_buffers(
        resolved.definitions().len(),
        resolved.implementations().len(),
    )?;
    definitions.extend(
        resolved
            .take_definitions()
            .into_vec()
            .into_iter()
            .map(CheckedDefinition::new),
    );
    implementations.extend(
        resolved
            .take_implementations()
            .into_vec()
            .into_iter()
            .map(CheckedImplementationBody::new),
    );
    Ok(CheckedModule::new(
        resolved,
        CheckedModuleParts {
            definitions: definitions.into_boxed_slice(),
            implementations: implementations.into_boxed_slice(),
            available_implementations: available_implementations.into_boxed_slice(),
            schemes,
            checked_interfaces,
            checked_implementations,
            interface_facts,
            implementation_facts,
            exports,
        },
    ))
}

fn build_evidence_selector(
    resolved: &ResolvedModule,
    schemes: &[CheckedGlobalScheme],
    interface_facts: &[CheckedInterfaceFact],
    checked_implementations: &[CheckedImplementation],
    type_work: &mut TypeWorkBudget,
    constraint_work: &mut InterfaceConstraintBudget,
) -> Result<EvidenceSelector, TypeError> {
    let mut selector = EvidenceSelector::new();
    for imported in resolved.imported_facts().interface_imports() {
        selector
            .add_imported_interface_fact(&imported.fact, constraint_work, type_work)
            .map_err(|failure| selection_failure(failure, None))?;
    }
    for interface in interface_facts {
        selector
            .add_interface_fact(interface, constraint_work, type_work)
            .map_err(|failure| selection_failure(failure, None))?;
    }
    for scheme in resolved.imported_facts().globals() {
        selector
            .add_imported_scheme(scheme, constraint_work, type_work)
            .map_err(|failure| selection_failure(failure, None))?;
    }
    for scheme in schemes {
        selector
            .add_scheme(scheme, constraint_work, type_work)
            .map_err(|failure| selection_failure(failure, None))?;
    }
    for imported in resolved.imported_facts().implementations() {
        selector
            .add_implementation_fact(imported, constraint_work, type_work)
            .map_err(|failure| selection_failure(failure, None))?;
    }
    for checked in checked_implementations {
        let implementation = resolved
            .implementations()
            .get(checked.source_index)
            .ok_or_else(invalid_state)?;
        selector
            .add_local_implementation(implementation, checked, constraint_work, type_work)
            .map_err(|failure| selection_failure(failure, None))?;
    }
    Ok(selector)
}

fn checked_interface_facts(
    resolved: &ResolvedModule,
    checked: &[CheckedInterface],
    type_work: &mut TypeWorkBudget,
    constraint_work: &mut InterfaceConstraintBudget,
) -> Result<Box<[CheckedInterfaceFact]>, TypeError> {
    constraint_work
        .charge(checked.len())
        .map_err(|()| constraint_resource())?;
    let mut facts = Vec::new();
    facts
        .try_reserve(checked.len())
        .map_err(|_| constraint_resource())?;
    for token in checked {
        let interface = resolved
            .interfaces()
            .get(token.source_index)
            .ok_or_else(invalid_state)?;
        if interface.id != token.id {
            return Err(invalid_state());
        }
        constraint_work
            .charge(interface.methods.len().saturating_add(1))
            .map_err(|()| constraint_resource())?;
        let mut methods = Vec::new();
        methods
            .try_reserve(interface.methods.len())
            .map_err(|_| constraint_resource())?;
        for method in &interface.methods {
            constraint_work
                .charge_type(&method.annotation.ty)
                .map_err(|()| constraint_resource())?;
            methods.push(CheckedInterfaceMethodFact {
                id: method.id,
                spelling: method.spelling.clone(),
                value_type: clone_type_with_budget(&method.annotation.ty, type_work)
                    .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?,
                origin: method.origin.clone(),
                span: method.span,
            });
        }
        facts.push(CheckedInterfaceFact {
            id: interface.id,
            spelling: interface.spelling.clone(),
            parameter: interface.parameter.clone(),
            methods: methods.into_boxed_slice(),
            origin: interface.origin.clone(),
            span: interface.span,
        });
    }
    Ok(facts.into_boxed_slice())
}

/// Assembles dependency-ordered checked modules for one final Core lowering.
///
/// # Errors
///
/// Returns an internal failure for duplicate module identities, modules outside
/// the selected entry's complete dependency closure, misordered dependencies,
/// a missing or malformed checked entry `main`, or conflicting full-registry
/// identities.
pub fn link_modules(
    modules: Vec<CheckedModule>,
    entry: crate::module::ModuleId,
) -> Result<ResolvedModuleProgram, TypeError> {
    link_modules_with_budget(modules, entry, &mut InterfaceConstraintBudget::default())
}

/// Links one checked graph while preserving its graph-wide constraint accounting.
pub(crate) fn link_modules_with_budget(
    modules: Vec<CheckedModule>,
    entry: crate::module::ModuleId,
    constraint_work: &mut InterfaceConstraintBudget,
) -> Result<ResolvedModuleProgram, TypeError> {
    constraint_work
        .charge(modules.len())
        .map_err(|()| constraint_resource())?;
    let entry_module = modules
        .iter()
        .find(|module| module.module() == entry)
        .ok_or_else(invalid_state)?;
    constraint_work
        .charge(entry_module.schemes().len())
        .map_err(|()| constraint_resource())?;
    let main = entry_module
        .schemes()
        .iter()
        .find(|scheme| scheme.spelling == "main")
        .ok_or_else(invalid_state)?;
    let Type::Function(domain, _) = &main.scheme.value_type else {
        return Err(invalid_state());
    };
    if !main.scheme.type_parameters.is_empty()
        || !main.scheme.requirements.is_empty()
        || !matches!(domain.as_ref(), Type::Unit)
    {
        return Err(invalid_state());
    }
    let retained = modules.iter().try_fold(modules.len(), |total, module| {
        total
            .checked_add(module.direct_dependencies().len())
            .and_then(|total| total.checked_add(module.interface_facts().len()))
            .and_then(|total| total.checked_add(module.implementation_facts().len()))
            .and_then(|total| total.checked_add(module.available_implementations().len()))
            .and_then(|total| total.checked_add(module.schemes().len()))
    });
    constraint_work
        .charge(retained.ok_or_else(constraint_resource)?)
        .map_err(|()| constraint_resource())?;
    let mut module_positions = HashMap::new();
    module_positions
        .try_reserve(modules.len())
        .map_err(|_| constraint_resource())?;
    for (index, module) in modules.iter().enumerate() {
        if module_positions.insert(module.module(), index).is_some() {
            return Err(invalid_state());
        }
    }
    for (index, module) in modules.iter().enumerate() {
        if module.direct_dependencies().iter().any(|dependency| {
            module_positions
                .get(&dependency.target())
                .is_none_or(|dependency_index| *dependency_index >= index)
        }) {
            return Err(invalid_state());
        }
    }
    let entry_index = *module_positions.get(&entry).ok_or_else(invalid_state)?;
    let mut reachable = Vec::new();
    reachable
        .try_reserve(modules.len())
        .map_err(|_| constraint_resource())?;
    reachable.resize(modules.len(), false);
    let mut pending = Vec::new();
    pending
        .try_reserve(modules.len())
        .map_err(|_| constraint_resource())?;
    reachable[entry_index] = true;
    pending.push(entry_index);
    while let Some(index) = pending.pop() {
        let module = modules.get(index).ok_or_else(invalid_state)?;
        for dependency in module.direct_dependencies() {
            let dependency_index = *module_positions
                .get(&dependency.target())
                .ok_or_else(invalid_state)?;
            if !reachable[dependency_index] {
                reachable[dependency_index] = true;
                pending.push(dependency_index);
            }
        }
    }
    if reachable.iter().any(|reached| !reached) {
        return Err(invalid_state());
    }
    let span = main.origin.primary_span();
    let result = ResolvedExpr {
        kind: ResolvedExprKind::Apply(crate::resolved::ResolvedApplicationExpr {
            function: Box::new(ResolvedExpr {
                kind: ResolvedExprKind::Occurrence(crate::resolved::ResolvedOccurrence {
                    term: crate::resolved::ResolvedTermName::Global(main.binder),
                    spelling: main.spelling.clone(),
                    origin: main.origin.clone(),
                    import_span: None,
                    evidence: Box::new([]),
                }),
                span,
            }),
            argument: Box::new(ResolvedExpr {
                kind: ResolvedExprKind::Unit,
                span,
            }),
        }),
        span,
    };
    let mut budget = TypeWorkBudget::default();
    let registry = Arc::new(
        ResolvedRegistry::combine_checked(&modules, &mut budget).map_err(resolved_build_error)?,
    );
    let mut groups = Vec::new();
    groups
        .try_reserve(modules.len())
        .map_err(|_| constraint_resource())?;
    groups.extend(modules.into_iter().map(CheckedModule::into_group));
    Ok(ResolvedModuleProgram::new(
        registry,
        groups.into_boxed_slice(),
        entry,
        result,
    ))
}

impl Default for Elaborator {
    fn default() -> Self {
        Self::new()
    }
}

enum ElaborationTask<'a> {
    Synthesize {
        expression: &'a ResolvedExpr,
        cause: Option<SynthesisCause>,
    },
    Check {
        expression: &'a ResolvedExpr,
        expected: ProvenancedType,
        kind: CheckKind,
    },
    CheckBlock {
        block: &'a ResolvedBlock,
        expected: ProvenancedType,
        kind: CheckKind,
    },
    FinishCheck {
        span: Span,
        expected: ProvenancedType,
        kind: CheckKind,
    },
    CheckFunction {
        parameter: &'a ResolvedPattern,
        domain: ProvenancedType,
        codomain: ProvenancedType,
        body: FunctionBody<'a>,
        presentation: Origin,
        function_type: ProvenancedType,
        body_check: CheckKind,
    },
    FinishFunction {
        direct_binder: Option<BinderId>,
        pattern_binders: Vec<BinderId>,
        binder: TypedBinder,
        pattern: Option<CorePattern>,
        domain: Option<Type>,
        ty: Type,
        origin: Origin,
        provenance: TypeProvenance,
    },
    AfterApplicationFunction {
        whole_span: Span,
        function_span: Span,
        argument: &'a ResolvedExpr,
        recursive_call: bool,
    },
    FinishApplication {
        whole_span: Span,
        function_span: Span,
        argument_span: Span,
        function: TypedNode,
        codomain: ProvenancedType,
    },
    AfterMatchScrutinee {
        expression: &'a crate::resolved::ResolvedMatchExpr,
        span: Span,
        expected: Option<(ProvenancedType, CheckKind)>,
    },
    FinishMatchArm {
        progress: Box<MatchProgress<'a>>,
        binders: Vec<BinderId>,
        row: Vec<CorePattern>,
        arm_span: Span,
    },
    FinishMatch(Box<MatchProgress<'a>>),
    AfterLeft {
        primitive: Primitive,
        whole_span: Span,
        operator_span: Span,
        right: &'a ResolvedExpr,
        left_span: Span,
    },
    AfterRight {
        primitive: Primitive,
        whole_span: Span,
        operator_span: Span,
        left: TypedNode,
        right_span: Span,
    },
    BeginBinding {
        binding: &'a ResolvedBinding,
        expected: Option<ProvenancedType>,
        finish_expected: Option<ProvenancedType>,
    },
    FinishBinding {
        binding: &'a ResolvedBinding,
        expected: Option<ProvenancedType>,
        evidence_marker: Option<usize>,
    },
    CheckRecursiveMember(&'a crate::resolved::ResolvedRecursiveMember),
    BeginRecursiveGroup(&'a ResolvedRecursiveGroup),
    FinishRecursiveGroup {
        group: &'a ResolvedRecursiveGroup,
    },
    FinishBlock {
        declarations: &'a [ResolvedLocalDeclaration],
        declaration_start: usize,
    },
}

struct MatchProgress<'a> {
    expression: &'a crate::resolved::ResolvedMatchExpr,
    span: Span,
    scrutinee: TypedNode,
    next_arm: usize,
    matrix: Vec<Vec<CorePattern>>,
    arm_bodies: Vec<(NodeId, Span)>,
    result_type: Option<(Type, TypeProvenance, CheckKind)>,
}

#[derive(Clone, Copy)]
enum FunctionBody<'a> {
    Block(&'a ResolvedBlock),
}

#[derive(Clone, Copy)]
enum CheckKind {
    General,
    Argument {
        function_span: Span,
        whole_span: Span,
        recursive_call: bool,
    },
    Definition {
        result_cause: Span,
    },
    BindingInitializer {
        initializer_span: Span,
        annotation_span: Span,
    },
}

#[derive(Clone, Copy)]
enum SynthesisCause {
    Binding(Span),
    NestedBinding(Span),
    ProgramResult(Span),
    Application(Span),
    Operator(Span),
}

struct FunctionCheck<'a> {
    parameter: &'a ResolvedPattern,
    domain: ProvenancedType,
    codomain: ProvenancedType,
    body: FunctionBody<'a>,
    presentation: Origin,
    function_type: ProvenancedType,
    body_check: CheckKind,
}

struct CheckedPattern {
    pattern: CorePattern,
    inference_changed: bool,
}

struct ElaboratedBinding {
    binder: TypedBinder,
    initializer: NodeId,
}

struct PreparedGlobals {
    context: TypeContext,
    globals: Vec<ElaboratedBinding>,
    binders: HashMap<BinderId, TypedBinder>,
    quantifiers: HashMap<BinderId, Box<[TypeVariableId]>>,
}

enum ElaboratedDeclaration {
    Binding {
        binder: TypedBinder,
        initializer: NodeId,
        origin: Origin,
    },
    PatternBinding {
        pattern: CorePattern,
        initializer: NodeId,
        origin: Origin,
    },
    Recursive {
        members: Vec<(TypedBinder, NodeId)>,
        origin: Origin,
    },
}

fn operational_domain(
    parameters: &[crate::resolved::ResolvedTypedPattern],
    span: Span,
    budget: &mut TypeWorkBudget,
) -> Result<ProvenancedType, TypeError> {
    match parameters {
        [] => Err(invalid_state()),
        [parameter] => ProvenancedType::from_resolved_with_budget(&parameter.annotation, budget),
        parameters => {
            budget
                .charge(2)
                .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
            for parameter in parameters {
                charge_type_cells(&parameter.annotation.ty, budget)
                    .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
            }
            let mut types = Vec::new();
            types
                .try_reserve(parameters.len())
                .map_err(|_| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
            types.extend(
                parameters
                    .iter()
                    .map(|parameter| zonk_type(&parameter.annotation.ty, &HashMap::new())),
            );
            let ty = Type::Tuple(types.into_boxed_slice());
            Ok(ProvenancedType {
                provenance: TypeProvenance::atom(Some(span)),
                ty,
            })
        }
    }
}

fn schedule_block<'a>(
    block: &'a ResolvedBlock,
    expected: Option<(ProvenancedType, CheckKind)>,
    synthesis_cause: Option<SynthesisCause>,
    tasks: &mut Vec<ElaborationTask<'a>>,
    declaration_start: usize,
    type_work: &mut TypeWorkBudget,
) -> Result<(), TypeError> {
    tasks.push(ElaborationTask::FinishBlock {
        declarations: &block.declarations,
        declaration_start,
    });
    if let Some((expected, kind)) = expected {
        tasks.push(ElaborationTask::Check {
            expression: &block.result,
            expected,
            kind,
        });
    } else {
        let result_cause = match synthesis_cause {
            Some(SynthesisCause::Binding(span)) => Some(SynthesisCause::NestedBinding(span)),
            cause => cause,
        };
        tasks.push(ElaborationTask::Synthesize {
            expression: &block.result,
            cause: result_cause,
        });
    }
    for declaration in block.declarations.iter().rev() {
        match declaration {
            ResolvedLocalDeclaration::Binding(binding) => {
                let expected = binding
                    .annotation
                    .as_ref()
                    .map(|annotation| {
                        ProvenancedType::from_resolved_with_budget(annotation, type_work)
                    })
                    .transpose()?;
                let finish_expected = expected
                    .as_ref()
                    .map(|expected| {
                        clone_type_with_budget(&expected.ty, type_work).map(|ty| ProvenancedType {
                            ty,
                            provenance: expected.provenance.clone(),
                        })
                    })
                    .transpose()
                    .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
                tasks.push(ElaborationTask::BeginBinding {
                    binding,
                    expected,
                    finish_expected,
                });
            }
            ResolvedLocalDeclaration::Recursive(group) => {
                tasks.push(ElaborationTask::BeginRecursiveGroup(group));
            }
        }
    }
    Ok(())
}

fn check_mismatch(
    kind: CheckKind,
    span: Span,
    expected: Type,
    found: Type,
    expected_cause: Option<Span>,
    registry: &ResolvedRegistry,
) -> TypeError {
    match kind {
        CheckKind::General => TypeError::Mismatch(TypeMismatch {
            span,
            expected_display: registry.display_source_type(&expected),
            found_display: registry.display_source_type(&found),
            expected: Box::new(expected),
            found: Box::new(found),
        }),
        CheckKind::Argument {
            function_span,
            whole_span,
            recursive_call,
        } => {
            if recursive_call {
                let mut diagnostic = Diagnostic::new(
                    TypeReason::PolymorphicRecursion,
                    SourceLabel::new(
                        span,
                        "this recursive call requires a different type instantiation",
                    ),
                );
                diagnostic.related.push(SourceLabel::new(
                    function_span,
                    "this recursive function is checked monomorphically",
                ));
                diagnostic.expected = Some(registry.display_source_type(&expected));
                diagnostic.found = Some(registry.display_source_type(&found));
                return TypeError::Source(Box::new(diagnostic));
            }
            let expected = registry.display_source_type(&expected);
            let found = registry.display_source_type(&found);
            let mut diagnostic = Diagnostic::new(
                TypeReason::Argument,
                SourceLabel::new(span, "this argument does not match the function domain"),
            );
            diagnostic.related.push(SourceLabel::new(
                expected_cause.unwrap_or(function_span),
                "the function domain is required here",
            ));
            if whole_span != span && whole_span != function_span {
                diagnostic.related.push(SourceLabel::new(
                    whole_span,
                    "this application supplies the argument",
                ));
            }
            diagnostic.expected = Some(expected);
            diagnostic.found = Some(found);
            TypeError::Source(Box::new(diagnostic))
        }
        CheckKind::Definition { result_cause } => {
            let expected = registry.display_source_type(&expected);
            let found = registry.display_source_type(&found);
            let mut diagnostic = Diagnostic::new(
                TypeReason::DefinitionResult,
                SourceLabel::new(span, "this function body has the wrong result type"),
            );
            diagnostic.related.push(SourceLabel::new(
                expected_cause.unwrap_or(result_cause),
                "the function interface requires this result type",
            ));
            diagnostic.expected = Some(expected);
            diagnostic.found = Some(found);
            TypeError::Source(Box::new(diagnostic))
        }
        CheckKind::BindingInitializer {
            initializer_span,
            annotation_span,
        } => {
            let expected = registry.display_source_type(&expected);
            let found = registry.display_source_type(&found);
            let mut diagnostic = Diagnostic::new(
                TypeReason::BindingInitializer,
                SourceLabel::new(
                    initializer_span,
                    format!("this initializer has type {found}"),
                ),
            );
            diagnostic.related.push(SourceLabel::new(
                annotation_span,
                format!("this binding annotation requires {expected}"),
            ));
            diagnostic.expected = Some(expected);
            diagnostic.found = Some(found);
            TypeError::Source(Box::new(diagnostic))
        }
    }
}

fn function_needs_context(span: Span, cause: Option<SynthesisCause>) -> TypeError {
    let mut diagnostic = Diagnostic::new(
        TypeReason::FunctionNeedsContext,
        SourceLabel::new(
            span,
            "this anonymous function needs an expected function type",
        ),
    );
    if let Some(cause) = cause {
        let (span, message, help) = match cause {
            SynthesisCause::Binding(span) | SynthesisCause::NestedBinding(span) => (
                span,
                "this unannotated binding requires its initializer to synthesize a type",
                Some("add a function type annotation to this binding"),
            ),
            SynthesisCause::ProgramResult(span) => (
                span,
                "the program result requires this expression to synthesize a type",
                None,
            ),
            SynthesisCause::Application(span) => (
                span,
                "this application requires its function position to synthesize a type",
                None,
            ),
            SynthesisCause::Operator(span) => (
                span,
                "this operator requires its operand to synthesize a type",
                None,
            ),
        };
        diagnostic.related.push(SourceLabel::new(span, message));
        diagnostic.help = help.map(str::to_owned);
    }
    TypeError::Source(Box::new(diagnostic))
}

fn not_applicable(
    function_span: Span,
    whole_span: Span,
    found: &Type,
    registry: &ResolvedRegistry,
) -> TypeError {
    let mut diagnostic = Diagnostic::new(
        TypeReason::NotApplicable,
        SourceLabel::new(function_span, "this expression is not a function"),
    );
    diagnostic.related.push(SourceLabel::new(
        whole_span,
        "this application requires a function here",
    ));
    diagnostic.expected = Some("function".to_owned());
    diagnostic.found = Some(registry.display_source_type(found));
    TypeError::Source(Box::new(diagnostic))
}

fn equation_interface_not_function(
    annotation: &ResolvedType,
    equation_name: &crate::resolved::ResolvedEquationHead,
    registry: &ResolvedRegistry,
) -> TypeError {
    let found = registry.display_source_type(&annotation.ty);
    let mut diagnostic = Diagnostic::new(
        TypeReason::EquationInterfaceNotFunction,
        SourceLabel::new(
            annotation.span,
            "this equational interface does not declare a function",
        ),
    );
    diagnostic.related.push(SourceLabel::new(
        equation_name.origin.primary_span(),
        "this equation head requires one function domain",
    ));
    diagnostic.expected = Some("function".to_owned());
    diagnostic.found = Some(found);
    TypeError::Source(Box::new(diagnostic))
}

fn schedule_left<'a>(
    primitive: Primitive,
    whole_span: Span,
    binary: &'a crate::resolved::ResolvedBinaryExpr,
    tasks: &mut Vec<ElaborationTask<'a>>,
) {
    tasks.push(ElaborationTask::AfterLeft {
        primitive,
        whole_span,
        operator_span: binary.operator_span,
        right: &binary.right,
        left_span: binary.left.span,
    });
    tasks.push(ElaborationTask::Synthesize {
        expression: &binary.left,
        cause: Some(SynthesisCause::Operator(binary.operator_span)),
    });
}

fn invalid_state() -> TypeError {
    TypeError::Internal(ElaborationFailure::InvalidState)
}

fn resolved_build_error(error: ResolvedBuildFailure) -> TypeError {
    match error {
        ResolvedBuildFailure::InvalidState => invalid_state(),
        ResolvedBuildFailure::TypeResource => {
            TypeError::Internal(ElaborationFailure::TypeResourceExhausted)
        }
        ResolvedBuildFailure::ConstraintResource => constraint_resource(),
    }
}

fn pattern_mismatch(span: Span, expected: &Type, registry: &ResolvedRegistry) -> TypeError {
    let mut diagnostic = Diagnostic::new(
        TypeReason::PatternMismatch,
        SourceLabel::new(span, "this pattern does not match its expected type"),
    );
    diagnostic.expected = Some(registry.display_source_type(expected));
    TypeError::Source(Box::new(diagnostic))
}

fn constructor_mismatch(span: Span) -> TypeError {
    TypeError::Source(Box::new(Diagnostic::new(
        TypeReason::ConstructorMismatch,
        SourceLabel::new(span, "this constructor has the wrong payload shape"),
    )))
}

fn case_error(
    reason: TypeReason,
    span: Span,
    message: &'static str,
    witness: Option<String>,
) -> TypeError {
    let mut diagnostic = Diagnostic::new(reason, SourceLabel::new(span, message));
    diagnostic.found = witness;
    TypeError::Source(Box::new(diagnostic))
}

fn binding_origin(binding: &ResolvedBinding) -> Origin {
    let mut related = vec![binding.initializer.span];
    if let Some(annotation) = &binding.annotation {
        related.push(annotation.span);
    }
    Origin::Generated {
        cause: Box::new(Origin::Related {
            primary: Box::new(Origin::Source(binding.span)),
            related,
        }),
        reason: GeneratedReason::BindingLowering,
    }
}

fn recursive_group_origin(group: &ResolvedRecursiveGroup) -> Origin {
    let related = group
        .members
        .iter()
        .flat_map(|member| [member.span, member.annotation.span, member.initializer.span])
        .collect();
    Origin::Generated {
        cause: Box::new(Origin::Related {
            primary: Box::new(Origin::Source(group.span)),
            related,
        }),
        reason: GeneratedReason::RecursiveBindingLowering,
    }
}

fn validate_recursive_member(
    group: &ResolvedRecursiveGroup,
    member: &crate::resolved::ResolvedRecursiveMember,
    registry: &ResolvedRegistry,
) -> Result<(), TypeError> {
    match &member.annotation.ty {
        Type::Function(_, _)
            if matches!(member.initializer.kind, ResolvedExprKind::Function(_)) =>
        {
            Ok(())
        }
        Type::Function(_, _) => Err(unsafe_recursive_initializer(group, member)),
        Type::Nominal(owner) | Type::AppliedNominal(owner, _) => {
            let payload = match &member.initializer.kind {
                ResolvedExprKind::Constructor(occurrence) => {
                    let Some(constructor) = registry.constructor(occurrence.constructor) else {
                        return Err(invalid_state());
                    };
                    if constructor.owner != *owner || constructor.payload.is_some() {
                        return Err(unsafe_recursive_root(group, member));
                    }
                    None
                }
                ResolvedExprKind::Apply(application) => {
                    let ResolvedExprKind::Constructor(occurrence) = &application.function.kind
                    else {
                        return Err(unsafe_recursive_root(group, member));
                    };
                    let Some(constructor) = registry.constructor(occurrence.constructor) else {
                        return Err(invalid_state());
                    };
                    if constructor.owner != *owner || constructor.payload.is_none() {
                        return Err(unsafe_recursive_root(group, member));
                    }
                    Some(application.argument.as_ref())
                }
                _ => return Err(unsafe_recursive_root(group, member)),
            };
            if let Some(payload) = payload {
                let recursive = group
                    .members
                    .iter()
                    .map(|member| member.binder.id)
                    .collect::<HashSet<_>>();
                validate_guarded_payload(payload, &recursive, registry)?;
            }
            Ok(())
        }
        Type::Int
        | Type::Bool
        | Type::Unit
        | Type::Tuple(_)
        | Type::Variable(_)
        | Type::Inference(_)
        | Type::Forall(_, _) => Err(unsafe_recursive_root(group, member)),
    }
}

fn validate_guarded_payload(
    expression: &ResolvedExpr,
    recursive: &HashSet<BinderId>,
    registry: &ResolvedRegistry,
) -> Result<(), TypeError> {
    if !contains_recursive_occurrence(expression, recursive) {
        return Ok(());
    }
    match &expression.kind {
        ResolvedExprKind::Occurrence(occurrence)
            if occurrence
                .global_binder()
                .is_some_and(|binder| recursive.contains(&binder)) =>
        {
            Ok(())
        }
        ResolvedExprKind::Tuple(elements) => {
            for element in elements {
                validate_guarded_payload(element, recursive, registry)?;
            }
            Ok(())
        }
        ResolvedExprKind::Apply(application)
            if matches!(application.function.kind, ResolvedExprKind::Constructor(_)) =>
        {
            let ResolvedExprKind::Constructor(occurrence) = &application.function.kind else {
                return Err(invalid_state());
            };
            if registry.constructor(occurrence.constructor).is_none() {
                return Err(invalid_state());
            }
            validate_guarded_payload(&application.argument, recursive, registry)
        }
        ResolvedExprKind::Function(_) => Ok(()),
        _ => Err(unguarded_recursive_use(expression.span)),
    }
}

fn contains_recursive_occurrence(expression: &ResolvedExpr, recursive: &HashSet<BinderId>) -> bool {
    let mut work = vec![expression];
    while let Some(expression) = work.pop() {
        match &expression.kind {
            ResolvedExprKind::Occurrence(occurrence)
                if occurrence
                    .global_binder()
                    .is_some_and(|binder| recursive.contains(&binder)) =>
            {
                return true;
            }
            ResolvedExprKind::Apply(application) => {
                work.push(&application.argument);
                work.push(&application.function);
            }
            ResolvedExprKind::Add(binary)
            | ResolvedExprKind::Multiply(binary)
            | ResolvedExprKind::Equal(binary) => {
                work.push(&binary.right);
                work.push(&binary.left);
            }
            ResolvedExprKind::Tuple(elements) => work.extend(elements),
            ResolvedExprKind::Block(block) => {
                work.push(&block.result);
                for declaration in &block.declarations {
                    match declaration {
                        ResolvedLocalDeclaration::Binding(binding) => {
                            work.push(&binding.initializer)
                        }
                        ResolvedLocalDeclaration::Recursive(group) => {
                            work.extend(group.members.iter().map(|member| &member.initializer));
                        }
                    }
                }
            }
            ResolvedExprKind::Function(function) => {
                work.push(&function.body.result);
                for declaration in &function.body.declarations {
                    match declaration {
                        ResolvedLocalDeclaration::Binding(binding) => {
                            work.push(&binding.initializer)
                        }
                        ResolvedLocalDeclaration::Recursive(group) => {
                            work.extend(group.members.iter().map(|member| &member.initializer));
                        }
                    }
                }
            }
            ResolvedExprKind::Match(match_expression) => {
                work.push(&match_expression.scrutinee);
                work.extend(match_expression.arms.iter().map(|arm| &arm.body));
            }
            ResolvedExprKind::Integer(_)
            | ResolvedExprKind::Boolean(_)
            | ResolvedExprKind::Unit
            | ResolvedExprKind::Constructor(_)
            | ResolvedExprKind::Occurrence(_) => {}
        }
    }
    false
}

fn unsafe_recursive_root(
    group: &ResolvedRecursiveGroup,
    member: &crate::resolved::ResolvedRecursiveMember,
) -> TypeError {
    let mut diagnostic = Diagnostic::new(
        TypeReason::UnsafeRecursiveRoot,
        SourceLabel::new(
            member.initializer.span,
            "this recursive data initializer has no fully applied constructor root",
        ),
    );
    diagnostic.related.push(SourceLabel::new(
        group.span,
        "this declaration is a simultaneous recursive group",
    ));
    diagnostic.related.push(SourceLabel::new(
        member.annotation.span,
        "this is the member's declared nominal type",
    ));
    TypeError::Source(Box::new(diagnostic))
}

fn unguarded_recursive_use(span: Span) -> TypeError {
    TypeError::Source(Box::new(Diagnostic::new(
        TypeReason::UnguardedRecursiveUse,
        SourceLabel::new(
            span,
            "a recursive occurrence crosses a forcing or transporting expression",
        ),
    )))
}

fn unsafe_recursive_initializer(
    group: &ResolvedRecursiveGroup,
    member: &crate::resolved::ResolvedRecursiveMember,
) -> TypeError {
    let mut diagnostic = Diagnostic::new(
        TypeReason::UnsafeRecursiveInitializer,
        SourceLabel::new(
            member.initializer.span,
            "this recursive initializer is not a direct anonymous function",
        ),
    );
    diagnostic.related.push(SourceLabel::new(
        group.span,
        "this declaration is a simultaneous recursive group",
    ));
    diagnostic.related.push(SourceLabel::new(
        member.annotation.span,
        "this is the member's declared type",
    ));
    diagnostic.expected = Some("a direct `fn` initializer".into());
    diagnostic.help = Some("initialize the recursive member directly with `fn`".into());
    TypeError::Source(Box::new(diagnostic))
}

fn equational_origin(
    definition_span: Span,
    equational: &crate::resolved::ResolvedEquationalGlobal,
) -> Origin {
    let first = equational.equations.first();
    Origin::Related {
        primary: Box::new(Origin::Source(
            first.map_or(definition_span, |equation| equation.span),
        )),
        related: [
            definition_span,
            equational.interface.span,
            equational.interface.annotation.span,
        ]
        .into_iter()
        .chain(first.map(|equation| equation.body.span))
        .collect(),
    }
}

fn implementation_method_origin(
    implementation: &crate::resolved::ResolvedImplementation,
    group: &crate::resolved::ResolvedImplementationMethodGroup,
    method_span: Span,
    annotation_span: Span,
) -> Origin {
    let first = group.equations.first();
    Origin::Related {
        primary: Box::new(Origin::Source(
            first.map_or(group.span, |equation| equation.span),
        )),
        related: [
            implementation.span,
            group.span,
            method_span,
            annotation_span,
        ]
        .into_iter()
        .chain(first.map(|equation| equation.body.span))
        .collect(),
    }
}

fn operational_origin(
    definition_span: Span,
    operational: &crate::resolved::ResolvedInlineOperationalGlobal,
) -> Origin {
    Origin::Related {
        primary: Box::new(Origin::Source(definition_span)),
        related: vec![
            operational.header.span,
            operational
                .header
                .parameters
                .first()
                .map_or(operational.header.span, |parameter| {
                    parameter.annotation.span
                }),
            operational.header.result_type.span,
            operational.body.span,
        ],
    }
}

fn anonymous_function_origin(
    expression_span: Span,
    function: &crate::resolved::ResolvedFunctionExpr,
) -> Origin {
    Origin::Related {
        primary: Box::new(Origin::Source(expression_span)),
        related: vec![function.pattern.span, function.body.span],
    }
}

/// Applies the structural type-equality rule without inference or coercion.
#[must_use]
pub fn structurally_equal(left: &Type, right: &Type) -> bool {
    same_type(left, right)
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum PublicTypeAdmissionError {
    Invalid,
    Resource,
}

fn validate_and_charge_public_monotype(
    ty: &Type,
    budget: &mut TypeWorkBudget,
) -> Result<(), PublicTypeAdmissionError> {
    enum Task<'a> {
        Visit(&'a Type, usize),
        Sequence(std::slice::Iter<'a, Type>, usize),
    }

    let mut work = vec![Task::Visit(ty, 0)];
    while let Some(task) = work.pop() {
        let Task::Visit(ty, depth) = task else {
            let Task::Sequence(mut remaining, depth) = task else {
                unreachable!("public type admission task is closed")
            };
            if let Some(next) = remaining.next() {
                work.push(Task::Sequence(remaining, depth));
                work.push(Task::Visit(next, depth));
            }
            continue;
        };
        budget
            .charge(1)
            .map_err(|()| PublicTypeAdmissionError::Resource)?;
        match ty {
            Type::Tuple(elements) | Type::AppliedNominal(_, elements) => {
                let child_depth = depth.saturating_add(1);
                if child_depth > CORE_PAYLOAD_DEPTH_LIMIT {
                    return Err(PublicTypeAdmissionError::Invalid);
                }
                work.push(Task::Sequence(elements.iter(), child_depth));
            }
            Type::Function(domain, codomain) => {
                let child_depth = depth.saturating_add(1);
                if child_depth > CORE_PAYLOAD_DEPTH_LIMIT {
                    return Err(PublicTypeAdmissionError::Invalid);
                }
                work.push(Task::Visit(codomain, child_depth));
                work.push(Task::Visit(domain, child_depth));
            }
            Type::Inference(_) | Type::Forall(_, _) => {
                return Err(PublicTypeAdmissionError::Invalid);
            }
            Type::Int | Type::Bool | Type::Unit | Type::Nominal(_) | Type::Variable(_) => {}
        }
    }
    Ok(())
}

fn clone_type_with_budget(ty: &Type, budget: &mut TypeWorkBudget) -> Result<Type, ()> {
    charge_type_cells(ty, budget)?;
    Ok(zonk_type(ty, &HashMap::new()))
}

fn clone_scheme_with_budget(fact: &TypeFact, budget: &mut TypeWorkBudget) -> Result<Type, ()> {
    charge_type_cells(&fact.ty, budget)?;
    if fact.quantified.is_empty() {
        return Ok(zonk_type(&fact.ty, &HashMap::new()));
    }
    budget.charge(fact.quantified.len().saturating_add(1))?;
    let mut quantified = Vec::new();
    quantified
        .try_reserve(fact.quantified.len())
        .map_err(|_| ())?;
    quantified.extend_from_slice(&fact.quantified);
    Ok(Type::Forall(
        quantified.into_boxed_slice(),
        Box::new(zonk_type(&fact.ty, &HashMap::new())),
    ))
}

fn clone_type_variables_with_budget(
    variables: &[TypeVariableId],
    budget: &mut TypeWorkBudget,
) -> Result<Vec<TypeVariableId>, ()> {
    budget.charge(variables.len())?;
    let mut copy = Vec::new();
    copy.try_reserve(variables.len()).map_err(|_| ())?;
    copy.extend_from_slice(variables);
    Ok(copy)
}

fn charge_pattern_binder_storage(ty: &Type, budget: &mut TypeWorkBudget) -> Result<(), ()> {
    charge_type_cells(ty, budget)?;
    charge_type_cells(ty, budget)?;
    charge_type_provenance_nodes(ty, budget)?;
    budget.charge(2)?;
    Ok(())
}

fn reserve_context_entry(context: &mut TypeContext, budget: &mut TypeWorkBudget) -> Result<(), ()> {
    budget.charge(1)?;
    context.binders.try_reserve(1).map_err(|_| ())
}

fn charge_type_provenance_nodes(ty: &Type, budget: &mut TypeWorkBudget) -> Result<(), ()> {
    let mut work = vec![ty];
    while let Some(ty) = work.pop() {
        budget.charge(1)?;
        if let Type::Function(domain, codomain) = ty {
            work.push(codomain);
            work.push(domain);
        }
    }
    Ok(())
}

fn unknown_provenance_with_budget(
    ty: &Type,
    budget: &mut TypeWorkBudget,
) -> Result<TypeProvenance, ()> {
    charge_type_provenance_nodes(ty, budget)?;
    Ok(TypeProvenance::unknown(ty))
}

fn constructor_replacements_with_budget(
    parameters: &[crate::resolved::ResolvedTypeVariable],
    arguments: &[Type],
    budget: &mut TypeWorkBudget,
) -> Result<HashMap<TypeVariableId, Type>, ()> {
    if parameters.len() != arguments.len() {
        return Err(());
    }
    budget.charge(arguments.len())?;
    for argument in arguments {
        charge_type_cells(argument, budget)?;
    }
    let mut replacements = HashMap::new();
    replacements.try_reserve(arguments.len()).map_err(|_| ())?;
    for (parameter, argument) in parameters.iter().zip(arguments) {
        replacements.insert(parameter.id, zonk_type(argument, &HashMap::new()));
    }
    Ok(replacements)
}

fn compare_concrete_types(
    left: &Type,
    right: &Type,
    budget: &mut TypeWorkBudget,
) -> Result<Option<bool>, ()> {
    enum Task<'a> {
        Pair(&'a Type, &'a Type),
        Sequence(std::slice::Iter<'a, Type>, std::slice::Iter<'a, Type>),
    }

    let mut work = vec![Task::Pair(left, right)];
    while let Some(task) = work.pop() {
        let (left, right) = match task {
            Task::Pair(left, right) => (left, right),
            Task::Sequence(mut left_types, mut right_types) => {
                match (left_types.next(), right_types.next()) {
                    (Some(left), Some(right)) => {
                        work.push(Task::Sequence(left_types, right_types));
                        work.push(Task::Pair(left, right));
                        continue;
                    }
                    (None, None) => continue,
                    _ => return Ok(Some(false)),
                }
            }
        };
        budget.charge(2)?;
        match (left, right) {
            (Type::Inference(_) | Type::Forall(_, _), _)
            | (_, Type::Inference(_) | Type::Forall(_, _)) => return Ok(None),
            (Type::Int, Type::Int) | (Type::Bool, Type::Bool) | (Type::Unit, Type::Unit) => {}
            (Type::Nominal(left), Type::Nominal(right)) if left == right => {}
            (Type::Variable(left), Type::Variable(right)) if left == right => {}
            (Type::Tuple(left), Type::Tuple(right)) if left.len() == right.len() => {
                work.push(Task::Sequence(left.iter(), right.iter()));
            }
            (Type::AppliedNominal(left_owner, left), Type::AppliedNominal(right_owner, right))
                if left_owner == right_owner && left.len() == right.len() =>
            {
                work.push(Task::Sequence(left.iter(), right.iter()));
            }
            (
                Type::Function(left_domain, left_codomain),
                Type::Function(right_domain, right_codomain),
            ) => {
                work.push(Task::Pair(left_codomain, right_codomain));
                work.push(Task::Pair(left_domain, right_domain));
            }
            _ => return Ok(Some(false)),
        }
    }
    Ok(Some(true))
}

fn clone_function_parts_with_budget(
    ty: &Type,
    budget: &mut TypeWorkBudget,
) -> Result<(Type, Type), ()> {
    let Type::Function(domain, codomain) = ty else {
        return Err(());
    };
    charge_type_cells(domain, budget)?;
    charge_type_cells(codomain, budget)?;
    let solutions = HashMap::new();
    Ok((
        zonk_type(domain, &solutions),
        zonk_type(codomain, &solutions),
    ))
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum UnificationFailure {
    Mismatch,
    Infinite,
    Resource,
}

#[cfg(test)]
std::thread_local! {
    static ZONK_REBUILD_PENDING_PEAK: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
    static OCCURS_PENDING_PEAK: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

#[cfg(test)]
fn record_zonk_rebuild_pending(pending: usize) {
    ZONK_REBUILD_PENDING_PEAK.with(|peak| peak.set(peak.get().max(pending)));
}

#[cfg(test)]
fn record_occurs_pending(pending: usize) {
    OCCURS_PENDING_PEAK.with(|peak| peak.set(peak.get().max(pending)));
}

fn zonk_type_with_status<E>(
    ty: &Type,
    solutions: &HashMap<InferenceVariableId, Type>,
    mut charge: impl FnMut(usize) -> Result<(), E>,
) -> Result<(Type, bool), E> {
    enum ChargeTask<'a> {
        Visit(&'a Type),
        Slice(std::slice::Iter<'a, Type>),
    }

    let mut work = vec![ChargeTask::Visit(ty)];
    let mut unresolved = false;
    while let Some(task) = work.pop() {
        match task {
            ChargeTask::Visit(Type::Inference(identity)) if solutions.contains_key(identity) => {
                work.push(ChargeTask::Visit(&solutions[identity]));
            }
            ChargeTask::Visit(Type::Tuple(elements) | Type::AppliedNominal(_, elements)) => {
                charge(1)?;
                work.push(ChargeTask::Slice(elements.iter()));
            }
            ChargeTask::Visit(Type::Function(domain, codomain)) => {
                charge(1)?;
                work.push(ChargeTask::Visit(codomain));
                work.push(ChargeTask::Visit(domain));
            }
            ChargeTask::Visit(Type::Forall(parameters, body)) => {
                charge(1)?;
                charge(parameters.len())?;
                work.push(ChargeTask::Visit(body));
            }
            ChargeTask::Visit(
                Type::Int | Type::Bool | Type::Unit | Type::Nominal(_) | Type::Variable(_),
            ) => charge(1)?,
            ChargeTask::Visit(Type::Inference(_)) => {
                charge(1)?;
                unresolved = true;
            }
            ChargeTask::Slice(mut remaining) => {
                if let Some(element) = remaining.next() {
                    work.push(ChargeTask::Slice(remaining));
                    work.push(ChargeTask::Visit(element));
                }
            }
        }
    }

    Ok((zonk_type(ty, solutions), unresolved))
}

fn zonk_type(ty: &Type, solutions: &HashMap<InferenceVariableId, Type>) -> Type {
    enum Task<'a> {
        Visit(&'a Type),
        VisitSequence(std::slice::Iter<'a, Type>),
        FinishTuple(usize),
        FinishApplied(crate::types::NominalTypeId, usize),
        FinishFunction,
        FinishForall(Box<[TypeVariableId]>),
    }

    let mut work = vec![Task::Visit(ty)];
    let mut rebuilt = Vec::new();
    while let Some(task) = work.pop() {
        #[cfg(test)]
        record_zonk_rebuild_pending(work.len().saturating_add(1));
        match task {
            Task::Visit(Type::Inference(identity)) if solutions.contains_key(identity) => {
                work.push(Task::Visit(&solutions[identity]));
            }
            Task::Visit(Type::Int) => rebuilt.push(Type::Int),
            Task::Visit(Type::Bool) => rebuilt.push(Type::Bool),
            Task::Visit(Type::Unit) => rebuilt.push(Type::Unit),
            Task::Visit(Type::Nominal(owner)) => rebuilt.push(Type::Nominal(*owner)),
            Task::Visit(Type::Variable(identity)) => rebuilt.push(Type::Variable(*identity)),
            Task::Visit(Type::Inference(identity)) => rebuilt.push(Type::Inference(*identity)),
            Task::Visit(Type::Tuple(elements)) => {
                work.push(Task::FinishTuple(elements.len()));
                work.push(Task::VisitSequence(elements.iter()));
            }
            Task::Visit(Type::AppliedNominal(owner, arguments)) => {
                work.push(Task::FinishApplied(*owner, arguments.len()));
                work.push(Task::VisitSequence(arguments.iter()));
            }
            Task::Visit(Type::Function(domain, codomain)) => {
                work.push(Task::FinishFunction);
                work.push(Task::Visit(codomain));
                work.push(Task::Visit(domain));
            }
            Task::Visit(Type::Forall(parameters, body)) => {
                work.push(Task::FinishForall(parameters.clone()));
                work.push(Task::Visit(body));
            }
            Task::VisitSequence(mut remaining) => {
                if let Some(element) = remaining.next() {
                    work.push(Task::VisitSequence(remaining));
                    work.push(Task::Visit(element));
                }
            }
            Task::FinishTuple(count) => {
                let elements = rebuilt.split_off(rebuilt.len() - count);
                rebuilt.push(Type::Tuple(elements.into_boxed_slice()));
            }
            Task::FinishApplied(owner, count) => {
                let arguments = rebuilt.split_off(rebuilt.len() - count);
                rebuilt.push(Type::AppliedNominal(owner, arguments.into_boxed_slice()));
            }
            Task::FinishFunction => {
                let codomain = rebuilt.pop().expect("zonked codomain");
                let domain = rebuilt.pop().expect("zonked domain");
                rebuilt.push(Type::Function(Box::new(domain), Box::new(codomain)));
            }
            Task::FinishForall(parameters) => {
                let body = rebuilt.pop().expect("zonked scheme body");
                rebuilt.push(Type::Forall(parameters, Box::new(body)));
            }
        }
    }
    rebuilt.pop().expect("one zonked type")
}

fn type_contains_inference(
    ty: &Type,
    needle: InferenceVariableId,
    solutions: &HashMap<InferenceVariableId, Type>,
) -> bool {
    enum Task<'a> {
        Visit(&'a Type),
        VisitSequence(std::slice::Iter<'a, Type>),
    }

    let mut work = vec![Task::Visit(ty)];
    let mut visited = HashSet::new();
    while let Some(task) = work.pop() {
        #[cfg(test)]
        record_occurs_pending(work.len().saturating_add(1));
        let Task::Visit(ty) = task else {
            let Task::VisitSequence(mut remaining) = task else {
                unreachable!()
            };
            if let Some(element) = remaining.next() {
                work.push(Task::VisitSequence(remaining));
                work.push(Task::Visit(element));
            }
            continue;
        };
        match ty {
            Type::Inference(identity) if *identity == needle => return true,
            Type::Inference(identity) if visited.insert(*identity) => {
                if let Some(solution) = solutions.get(identity) {
                    work.push(Task::Visit(solution));
                }
            }
            Type::Tuple(elements) | Type::AppliedNominal(_, elements) => {
                work.push(Task::VisitSequence(elements.iter()));
            }
            Type::Function(domain, codomain) => {
                work.push(Task::Visit(codomain));
                work.push(Task::Visit(domain));
            }
            Type::Forall(_, body) => work.push(Task::Visit(body)),
            Type::Int
            | Type::Bool
            | Type::Unit
            | Type::Nominal(_)
            | Type::Variable(_)
            | Type::Inference(_) => {}
        }
    }
    false
}

fn collect_unsolved_inference(
    ty: &Type,
    budget: &mut TypeWorkBudget,
) -> Result<Vec<InferenceVariableId>, ()> {
    enum Task<'a> {
        Visit(&'a Type),
        Slice(std::slice::Iter<'a, Type>),
    }

    let mut work = vec![Task::Visit(ty)];
    let mut seen = HashSet::new();
    let mut found = Vec::new();
    while let Some(task) = work.pop() {
        let Task::Visit(ty) = task else {
            let Task::Slice(mut remaining) = task else {
                unreachable!("inference collection task is closed")
            };
            if let Some(next) = remaining.next() {
                work.push(Task::Slice(remaining));
                work.push(Task::Visit(next));
            }
            continue;
        };
        budget.charge(1)?;
        match ty {
            Type::Inference(identity) if !seen.contains(identity) => {
                budget.charge(2)?;
                seen.try_reserve(1).map_err(|_| ())?;
                found.try_reserve(1).map_err(|_| ())?;
                seen.insert(*identity);
                found.push(*identity);
            }
            Type::Tuple(elements) | Type::AppliedNominal(_, elements) => {
                work.push(Task::Slice(elements.iter()));
            }
            Type::Function(domain, codomain) => {
                work.push(Task::Visit(codomain));
                work.push(Task::Visit(domain));
            }
            Type::Forall(_, body) => work.push(Task::Visit(body)),
            Type::Int
            | Type::Bool
            | Type::Unit
            | Type::Nominal(_)
            | Type::Variable(_)
            | Type::Inference(_) => {}
        }
    }
    Ok(found)
}

fn inference_failure(reason: TypeReason, span: Span, message: &str) -> TypeError {
    TypeError::Source(Box::new(Diagnostic::new(
        reason,
        SourceLabel::new(span, message),
    )))
}

fn resolved_module_binders(module: &ResolvedModule) -> Vec<BinderId> {
    let mut binders = Vec::new();
    let mut expressions = Vec::new();
    collect_definition_binders(module.definitions(), &mut binders, &mut expressions);
    collect_implementation_binders(module.implementations(), &mut binders, &mut expressions);
    collect_expression_binders(&mut binders, expressions);
    binders
}

fn collect_implementation_binders<'a>(
    implementations: &'a [crate::resolved::ResolvedImplementation],
    binders: &mut Vec<BinderId>,
    expressions: &mut Vec<&'a ResolvedExpr>,
) {
    for implementation in implementations {
        for group in &implementation.method_groups {
            binders.push(group.binder.id);
            for equation in &group.equations {
                for pattern in &equation.patterns {
                    collect_pattern_binders(pattern, binders);
                }
                expressions.push(&equation.body);
            }
        }
    }
}

fn collect_definition_binders<'a>(
    definitions: &'a [crate::resolved::ResolvedDefinition],
    binders: &mut Vec<BinderId>,
    expressions: &mut Vec<&'a ResolvedExpr>,
) {
    for definition in definitions {
        collect_definition_kind_binders(&definition.kind, binders, expressions);
    }
}

fn collect_definition_kind_binders<'a>(
    kind: &'a ResolvedDefinitionKind,
    binders: &mut Vec<BinderId>,
    expressions: &mut Vec<&'a ResolvedExpr>,
) {
    match kind {
        ResolvedDefinitionKind::Equational(equational) => {
            binders.push(equational.interface.name.id);
            for equation in &equational.equations {
                for pattern in &equation.patterns {
                    collect_pattern_binders(pattern, binders);
                }
                expressions.push(&equation.body);
            }
        }
        ResolvedDefinitionKind::InlineOperational(operational) => {
            binders.push(operational.header.name.id);
            for parameter in &operational.header.parameters {
                collect_pattern_binders(&parameter.pattern, binders);
            }
            expressions.push(&operational.body.result);
            for declaration in &operational.body.declarations {
                collect_resolved_declaration(declaration, binders, expressions);
            }
        }
    }
}

fn collect_expression_binders(binders: &mut Vec<BinderId>, mut expressions: Vec<&ResolvedExpr>) {
    while let Some(expression) = expressions.pop() {
        match &expression.kind {
            ResolvedExprKind::Apply(application) => {
                expressions.push(&application.argument);
                expressions.push(&application.function);
            }
            ResolvedExprKind::Add(binary)
            | ResolvedExprKind::Multiply(binary)
            | ResolvedExprKind::Equal(binary) => {
                expressions.push(&binary.right);
                expressions.push(&binary.left);
            }
            ResolvedExprKind::Block(block) => {
                expressions.push(&block.result);
                for declaration in &block.declarations {
                    collect_resolved_declaration(declaration, binders, &mut expressions);
                }
            }
            ResolvedExprKind::Function(function) => {
                collect_pattern_binders(&function.pattern, binders);
                expressions.push(&function.body.result);
                for declaration in &function.body.declarations {
                    collect_resolved_declaration(declaration, binders, &mut expressions);
                }
            }
            ResolvedExprKind::Tuple(elements) => expressions.extend(elements),
            ResolvedExprKind::Match(match_expression) => {
                expressions.push(&match_expression.scrutinee);
                for arm in &match_expression.arms {
                    collect_pattern_binders(&arm.pattern, binders);
                    expressions.push(&arm.body);
                }
            }
            ResolvedExprKind::Integer(_)
            | ResolvedExprKind::Boolean(_)
            | ResolvedExprKind::Unit
            | ResolvedExprKind::Occurrence(_)
            | ResolvedExprKind::Constructor(_) => {}
        }
    }
}

fn collect_resolved_declaration<'a>(
    declaration: &'a ResolvedLocalDeclaration,
    binders: &mut Vec<BinderId>,
    expressions: &mut Vec<&'a ResolvedExpr>,
) {
    match declaration {
        ResolvedLocalDeclaration::Binding(binding) => {
            collect_pattern_binders(&binding.pattern, binders);
            expressions.push(&binding.initializer);
        }
        ResolvedLocalDeclaration::Recursive(group) => {
            for member in &group.members {
                binders.push(member.binder.id);
                expressions.push(&member.initializer);
            }
        }
    }
}

fn collect_pattern_binders(
    pattern: &crate::resolved::ResolvedPattern,
    binders: &mut Vec<BinderId>,
) {
    let mut patterns = vec![pattern];
    while let Some(pattern) = patterns.pop() {
        match &pattern.kind {
            crate::resolved::ResolvedPatternKind::Binder(binder) => binders.push(binder.id),
            crate::resolved::ResolvedPatternKind::Tuple(elements) => patterns.extend(elements),
            crate::resolved::ResolvedPatternKind::Constructor { payload, .. } => {
                if let Some(payload) = payload {
                    patterns.push(payload);
                }
            }
            crate::resolved::ResolvedPatternKind::Wildcard
            | crate::resolved::ResolvedPatternKind::Boolean(_)
            | crate::resolved::ResolvedPatternKind::Unit => {}
        }
    }
}

#[cfg(test)]
mod tests {
    use std::{
        fs,
        path::{Path, PathBuf},
        sync::atomic::{AtomicU64, Ordering},
    };

    use super::*;
    use crate::{
        module::{ModuleId, ModuleRoots, load_module_graph},
        resolve::resolve_module,
        resolved::{
            ImportedFacts, ResolvedExportCandidate, ResolvedInterfaceDeclaration,
            ResolvedInterfaceMethod, ResolvedModuleParts, ResolvedTypeVariable,
        },
        source::{ByteRange, SourceFile},
    };

    static MODULE_FIXTURE_IDS: AtomicU64 = AtomicU64::new(0);

    struct ModuleFixtureFile(PathBuf);

    impl ModuleFixtureFile {
        fn write(display_path: &str, text: &str) -> Self {
            let id = MODULE_FIXTURE_IDS.fetch_add(1, Ordering::Relaxed);
            let label = Path::new(display_path)
                .file_name()
                .and_then(|name| name.to_str())
                .unwrap_or("fixture.ash");
            let path = std::env::temp_dir()
                .join(format!("ash-elaborate-{}-{id}-{label}", std::process::id(),));
            fs::write(&path, text).expect("the module fixture should be writable");
            Self(path)
        }
    }

    impl Drop for ModuleFixtureFile {
        fn drop(&mut self) {
            let _ = fs::remove_file(&self.0);
        }
    }

    fn resolved_module_fixture(
        display_path: &str,
        declarations: &str,
        result_type: &str,
        result: &str,
    ) -> ResolvedModule {
        let separator = if !declarations.is_empty() && !declarations.ends_with('\n') {
            "\n"
        } else {
            ""
        };
        let text =
            format!("{declarations}{separator}main : Unit -> {result_type}\nmain () = {result}\n");
        let file = ModuleFixtureFile::write(display_path, &text);
        let graph = load_module_graph(&file.0, &ModuleRoots::empty())
            .expect("the module fixture should load");
        let loaded = graph
            .module(graph.entry())
            .expect("the module fixture should retain its entry");
        assert!(loaded.dependencies().is_empty());
        let resolved = resolve_module(loaded, &[]).expect("the module fixture should resolve");
        let wrapper = resolved
            .definitions()
            .last()
            .expect("the module fixture should retain its result wrapper");
        let ResolvedDefinitionKind::Equational(wrapper) = &wrapper.kind else {
            panic!("the module fixture result should be equational");
        };
        assert_eq!(wrapper.interface.name.spelling, "main");
        assert_eq!(wrapper.equations.len(), 1);
        resolved
    }

    fn fixture_result(module: &ResolvedModule) -> &ResolvedExpr {
        let wrapper = module
            .definitions()
            .last()
            .expect("the module fixture should retain its result wrapper");
        let ResolvedDefinitionKind::Equational(wrapper) = &wrapper.kind else {
            panic!("the module fixture result should be equational");
        };
        &wrapper
            .equations
            .first()
            .expect("the module fixture should retain one result body")
            .body
    }

    #[test]
    fn checked_body_buffers_reserve_before_owning_resolved_bodies() {
        let resolved = resolved_module_fixture(
            "checked-body-reservation.ash",
            "interface Keep<A> {\nkeep : A -> A\n}\n\nimpl Keep<Int> {\nkeep value = value\n}\n",
            "Unit",
            "()",
        );

        let failure = reserve_checked_body_buffers(resolved.definitions().len(), usize::MAX)
            .expect_err("an impossible implementation capacity should fail before body transfer");

        assert_eq!(
            failure,
            TypeError::Internal(ElaborationFailure::ConstraintResourceExhausted)
        );
        assert!(!resolved.definitions().is_empty());
        assert!(!resolved.implementations().is_empty());
    }

    #[test]
    fn final_module_lowering_boundary_accepts_validated_checked_groups() {
        type CheckedLoweringBoundary =
            fn(
                &mut Elaborator,
                &ResolvedModuleGroup,
                TypeContext,
            ) -> Result<(Vec<ElaboratedBinding>, TypeContext), TypeError>;

        let boundary: CheckedLoweringBoundary = Elaborator::elaborate_checked_module_group;

        let _ = boundary;
    }

    #[test]
    fn module_binder_collection_includes_impl_groups_patterns_and_nested_bodies() {
        let resolved = resolved_module_fixture(
            "impl-binder-collection.ash",
            "interface Convert<A> {\nconvert : A -> A\n}\n\nimpl Convert<Int> {\nconvert value = {\nlet saved = value\nsaved\n}\n}\n",
            "Unit",
            "()",
        );
        let group = &resolved.implementations()[0].method_groups[0];
        let ResolvedPatternKind::Binder(parameter) = &group.equations[0].patterns[0].kind else {
            panic!("the impl equation should retain its parameter binder");
        };
        let ResolvedExprKind::Block(body) = &group.equations[0].body.kind else {
            panic!("the impl equation should retain its block body");
        };
        let ResolvedLocalDeclaration::Binding(binding) = &body.declarations[0] else {
            panic!("the impl body should retain its nested binding");
        };
        let ResolvedPatternKind::Binder(nested) = &binding.pattern.kind else {
            panic!("the nested binding should retain its binder");
        };

        let binders = resolved_module_binders(&resolved);

        assert!(binders.contains(&group.binder.id));
        assert!(binders.contains(&parameter.id));
        assert!(binders.contains(&nested.id));
    }

    #[test]
    fn program_elaborator_reserves_hidden_impl_binders() {
        let resolved = resolved_module_fixture(
            "impl-program-reservation.ash",
            "interface Convert<A> {\nconvert : A -> A\n}\n\nimpl Convert<Int> {\nconvert value = value\n}\n",
            "Unit",
            "()",
        );
        let module = resolved.module();
        let hidden = resolved.implementations()[0].method_groups[0].binder.id;
        let checked = check_module(resolved).expect("Task 3 ignores impl bodies while checking");
        let program = link_modules(vec![checked], module)
            .expect("the checked fixture should link into one module program");
        let program = crate::evidence_validation::validate_interface_evidence(program)
            .expect("the linked fixture evidence should validate");
        let origin = Origin::Source(program.groups()[0].span());
        let mut elaborator = Elaborator::for_module_program(&program)
            .expect("the complete resolved namespace should reserve");

        elaborator
            .builder
            .resolved_binder(hidden, Type::Unit, origin)
            .expect("the hidden impl binder should be reserved before lowering");
    }

    #[test]
    fn final_elaborator_requires_the_authorized_module_program_root() {
        let resolved = resolved_module_fixture("final-root-authorization.ash", "", "Unit", "()");
        let module = resolved.module();
        let checked = check_module(resolved).expect("the fixture module should check");
        let program = link_modules(vec![checked], module)
            .expect("the checked fixture should link into one module program");
        let program = crate::evidence_validation::validate_interface_evidence(program)
            .expect("the linked fixture evidence should validate");
        let mut elaborator = Elaborator::for_module_program(&program)
            .expect("the complete resolved namespace should reserve");
        let unrelated = elaborator
            .builder
            .unit(Type::Unit, Origin::Source(program.groups()[0].span()))
            .expect("the adversarial root should allocate");

        assert!(matches!(
            elaborator.finish(unrelated),
            Err(ElaborationFailure::InvalidState)
        ));
    }

    fn nested_function_type(depth: usize) -> Type {
        let mut ty = Type::Unit;
        for _ in 0..depth {
            ty = Type::Function(Box::new(Type::Unit), Box::new(ty));
        }
        ty
    }

    fn static_rule_outcome(
        left: &Type,
        right: &Type,
        equality_rule: fn(&Type, &Type) -> bool,
    ) -> bool {
        equality_rule(left, right)
    }

    fn mock_bool_distinct_rule(left: &Type, right: &Type) -> bool {
        if matches!((left, right), (Type::Bool, Type::Bool)) {
            false
        } else {
            structurally_equal(left, right)
        }
    }

    #[test]
    fn zonking_charges_the_expanded_result_before_rebuilding() {
        let inference = InferenceVariableId::new(0);
        let source = Type::Tuple(vec![Type::Inference(inference); 16].into_boxed_slice());
        let solutions = HashMap::from([(
            inference,
            Type::Tuple(vec![Type::Int; 16].into_boxed_slice()),
        )]);
        let mut remaining = 128_usize;

        let result = zonk_type_with_status(&source, &solutions, |cells| {
            remaining = remaining.checked_sub(cells).ok_or(())?;
            Ok(())
        });

        assert_eq!(result, Err(()));
        assert_eq!(remaining, 0);
    }

    #[test]
    fn zonking_charges_forall_quantifiers_before_cloning_them() {
        const WIDTH: usize = 4_096;
        const EXACT_WORK: usize = WIDTH + 2;
        let parameters = (0..WIDTH)
            .map(|index| TypeVariableId::new(u32::try_from(index).expect("parameter identity")))
            .collect::<Vec<_>>()
            .into_boxed_slice();
        let source = Type::Forall(parameters, Box::new(Type::Unit));

        let mut short_remaining = EXACT_WORK - 1;
        let short = zonk_type_with_status(&source, &HashMap::new(), |cells| {
            short_remaining = short_remaining.checked_sub(cells).ok_or(())?;
            Ok::<(), ()>(())
        });
        assert!(matches!(short, Err(())));
        assert_eq!(short_remaining, 0);

        let mut exact_remaining = EXACT_WORK;
        let (zonked, unresolved) = zonk_type_with_status(&source, &HashMap::new(), |cells| {
            exact_remaining = exact_remaining.checked_sub(cells).ok_or(())?;
            Ok::<(), ()>(())
        })
        .expect("the wrapper, quantifiers, and body fit exactly");
        assert_eq!(zonked, source);
        assert!(!unresolved);
        assert_eq!(exact_remaining, 0);
    }

    #[test]
    fn one_coverage_budget_spans_all_checked_modules() {
        let first = resolved_module_fixture("first.ash", "", "Unit", "()");
        let second = resolved_module_fixture("second.ash", "", "Unit", "()");
        let mut type_work = TypeWorkBudget::default();
        let mut coverage_work = UsefulnessBudget::with_limit(20);
        let mut constraint_work = InterfaceConstraintBudget::default();

        check_module_with_budget(
            first,
            &mut type_work,
            &mut coverage_work,
            &mut constraint_work,
        )
        .expect("the first module should fit the shared coverage budget");
        let failure = check_module_with_budget(
            second,
            &mut type_work,
            &mut coverage_work,
            &mut constraint_work,
        )
        .expect_err("the second module should exhaust cumulative coverage work");

        assert_eq!(
            failure,
            TypeError::Internal(ElaborationFailure::CoverageResourceExhausted)
        );
    }

    #[test]
    fn one_coverage_budget_spans_local_binding_irrefutability() {
        let body = "{\nlet (left, right) = ((), ())\n()\n}";
        let first = resolved_module_fixture("first.ash", "", "Unit", body);
        let second = resolved_module_fixture("second.ash", "", "Unit", body);
        let mut type_work = TypeWorkBudget::default();
        let mut coverage_work = UsefulnessBudget::with_limit(40);
        let mut constraint_work = InterfaceConstraintBudget::default();

        check_module_with_budget(
            first,
            &mut type_work,
            &mut coverage_work,
            &mut constraint_work,
        )
        .expect("the first local binding should fit the shared coverage budget");
        let failure = check_module_with_budget(
            second,
            &mut type_work,
            &mut coverage_work,
            &mut constraint_work,
        )
        .expect_err("the second local binding should exhaust cumulative coverage work");

        assert_eq!(
            failure,
            TypeError::Internal(ElaborationFailure::CoverageResourceExhausted)
        );
    }

    #[test]
    fn one_type_budget_spans_all_checked_modules() {
        let first = resolved_module_fixture("first.ash", "", "Unit", "()");
        let second = resolved_module_fixture("second.ash", "", "Unit", "()");
        let mut type_work = TypeWorkBudget::with_limit(60);
        let mut coverage_work = UsefulnessBudget::default();
        let mut constraint_work = InterfaceConstraintBudget::default();

        check_module_with_budget(
            first,
            &mut type_work,
            &mut coverage_work,
            &mut constraint_work,
        )
        .expect("the first module should fit the shared type budget");
        let failure = check_module_with_budget(
            second,
            &mut type_work,
            &mut coverage_work,
            &mut constraint_work,
        )
        .expect_err("the second module should exhaust cumulative type work");

        assert_eq!(
            failure,
            TypeError::Internal(ElaborationFailure::TypeResourceExhausted)
        );
    }

    #[test]
    fn one_constraint_budget_spans_all_checked_modules() {
        let interface = "interface Marker<A> {\nmarker : A -> Bool\n}\n";
        let short_module = resolved_module_fixture("short-constraint.ash", interface, "Unit", "()");
        let first = resolved_module_fixture("first-constraint.ash", interface, "Unit", "()");
        let second = resolved_module_fixture("second-constraint.ash", interface, "Unit", "()");
        let mut type_work = TypeWorkBudget::default();
        let mut coverage_work = UsefulnessBudget::default();
        let mut short = InterfaceConstraintBudget::with_limit(36);

        let failure =
            check_module_with_budget(short_module, &mut type_work, &mut coverage_work, &mut short)
                .expect_err("one missing unit should reject one interface");
        assert_eq!(
            failure,
            TypeError::Internal(ElaborationFailure::ConstraintResourceExhausted)
        );
        assert_eq!(short.used(), 36);

        let mut type_work = TypeWorkBudget::default();
        let mut coverage_work = UsefulnessBudget::default();
        let mut constraint_work = InterfaceConstraintBudget::with_limit(37);

        check_module_with_budget(
            first,
            &mut type_work,
            &mut coverage_work,
            &mut constraint_work,
        )
        .expect("one interface should fit the exact constraint budget");
        assert_eq!(constraint_work.used(), 37);
        assert_eq!(constraint_work.charge(1), Err(()));
        let failure = check_module_with_budget(
            second,
            &mut type_work,
            &mut coverage_work,
            &mut constraint_work,
        )
        .expect_err("the second module should exhaust cumulative constraint work");

        assert_eq!(
            failure,
            TypeError::Internal(ElaborationFailure::ConstraintResourceExhausted)
        );
    }

    #[test]
    fn impl_method_substitution_uses_the_exact_constraint_budget() {
        let declarations = concat!(
            "interface Keep<A> {\nkeep : A -> A\n}\n\n",
            "impl Keep<Int> {\nkeep value = value\n}\n",
        );
        let short_module = resolved_module_fixture(
            "short-impl-method-constraint.ash",
            declarations,
            "Unit",
            "()",
        );
        let exact_module =
            resolved_module_fixture("impl-method-constraint.ash", declarations, "Unit", "()");
        let mut type_work = TypeWorkBudget::default();
        let mut coverage_work = UsefulnessBudget::default();
        let mut short = InterfaceConstraintBudget::with_limit(76);

        let failure =
            check_module_with_budget(short_module, &mut type_work, &mut coverage_work, &mut short)
                .expect_err("one missing unit should reject the method substitution");
        assert_eq!(
            failure,
            TypeError::Internal(ElaborationFailure::ConstraintResourceExhausted)
        );

        let mut type_work = TypeWorkBudget::default();
        let mut coverage_work = UsefulnessBudget::default();
        let mut exact = InterfaceConstraintBudget::with_limit(77);
        check_module_with_budget(exact_module, &mut type_work, &mut coverage_work, &mut exact)
            .expect("the exact budget should admit one implementation method");

        assert_eq!(exact.used(), 77);
        assert_eq!(exact.charge(1), Err(()));
    }

    #[test]
    fn invalid_outer_method_shape_has_an_exact_stack_safe_constraint_boundary() {
        std::thread::Builder::new()
            .name("interface-method-shape-boundary".to_owned())
            .stack_size(64 * 1024)
            .spawn(|| {
                const DEPTH: usize = 10_000;
                let source = SourceFile::new(
                    "deep-interface-method.ash",
                    "interface Deep<A> {\ndeep : A\n}\n",
                )
                .expect("the interface fixture should fit");
                let span = source
                    .span(
                        ByteRange::new(
                            0,
                            u32::try_from(source.text().len())
                                .expect("the fixture length should fit"),
                        )
                        .expect("the span is ordered"),
                    )
                    .expect("the span should belong to the fixture");
                let module_id = ModuleId::new(1);
                let interface_id = InterfaceId::new(module_id, 0);
                let parameter_id = TypeVariableId::resolved(module_id, 0);
                let mut nested_tail = Type::Function(Box::new(Type::Unit), Box::new(Type::Bool));
                for _ in 0..DEPTH {
                    nested_tail = Type::Tuple(vec![Type::Unit, nested_tail].into_boxed_slice());
                }
                let method_type =
                    Type::Tuple(vec![Type::Variable(parameter_id), nested_tail].into_boxed_slice());
                let module = ResolvedModule::new(ResolvedModuleParts {
                    module: module_id,
                    registry: Arc::new(ResolvedRegistry::new(Vec::new(), Vec::new())),
                    imported: ImportedFacts::default(),
                    direct_dependencies: Vec::new(),
                    declaration_order: vec![ResolvedDeclarationIndex::Interface(0)],
                    interfaces: vec![ResolvedInterfaceDeclaration {
                        id: interface_id,
                        public: false,
                        spelling: "Deep".to_owned(),
                        parameter: ResolvedTypeVariable {
                            id: parameter_id,
                            spelling: "A".to_owned(),
                            origin: Origin::Source(span),
                        },
                        methods: vec![ResolvedInterfaceMethod {
                            id: MethodId::new(interface_id, 0),
                            spelling: "deep".to_owned(),
                            annotation: ResolvedType {
                                ty: method_type,
                                provenance: ResolvedTypeProvenance::new(
                                    vec![ResolvedTypeProvenanceNode::Fact(span)],
                                    0,
                                ),
                                origin: Origin::Source(span),
                                span,
                            },
                            type_parameters: Box::new([]),
                            origin: Origin::Source(span),
                            span,
                        }]
                        .into_boxed_slice(),
                        origin: Origin::Source(span),
                        span,
                    }],
                    implementations: Vec::new(),
                    definitions: Vec::new(),
                    export_candidate: ResolvedExportCandidate::default(),
                    span,
                });

                let mut short = InterfaceConstraintBudget::with_limit(7);
                assert_eq!(
                    check_interface_declarations(&module, &mut short),
                    Err(TypeError::Internal(
                        ElaborationFailure::ConstraintResourceExhausted
                    ))
                );
                assert_eq!(short.used(), 7);

                let mut exact = InterfaceConstraintBudget::with_limit(8);
                let error = check_interface_declarations(&module, &mut exact)
                    .expect_err("the exact budget should reach the source diagnostic");
                let TypeError::Interface(diagnostic) = error else {
                    panic!("the invalid outer method shape should use an interface diagnostic");
                };
                assert_eq!(diagnostic.reason, InterfaceReason::MethodNotFunction);
                assert_eq!(exact.used(), 8);
                assert_eq!(exact.charge(1), Err(()));
                drop(module);
            })
            .expect("the small-stack method-shape thread should start")
            .join()
            .expect("method-shape rejection and destruction must fit the small stack");
    }

    #[test]
    fn imported_overlap_uses_retained_route_order_and_exact_budget() {
        let source = SourceFile::new("import-overlap.ash", "abcdefghijklmnop")
            .expect("the overlap span fixture should fit");
        let span = |start, end| {
            source
                .span(ByteRange::new(start, end).expect("the span should be ordered"))
                .expect("the span should belong to the fixture")
        };
        let first_definition = span(0, 2);
        let first_route = span(3, 5);
        let second_definition = span(6, 8);
        let second_route = span(9, 11);
        let interface = crate::interface::InterfaceId::new(ModuleId::new(40), 0);
        let first = crate::resolved::ImportedImplementationFact {
            fact: CheckedImplementationFact {
                id: crate::interface::ImplId::new(ModuleId::new(90), 0),
                interface,
                head_parameters: Box::new([]),
                argument: Type::Int,
                prerequisites: Box::new([]),
                methods: Box::new([]),
                origin: Origin::Source(first_definition),
                span: first_definition,
            },
            direct_dependency: ModuleId::new(90),
            available_at: first_route,
        };
        let second = crate::resolved::ImportedImplementationFact {
            fact: CheckedImplementationFact {
                id: crate::interface::ImplId::new(ModuleId::new(10), 0),
                interface,
                head_parameters: Box::new([]),
                argument: Type::Int,
                prerequisites: Box::new([]),
                methods: Box::new([]),
                origin: Origin::Source(second_definition),
                span: second_definition,
            },
            direct_dependency: ModuleId::new(10),
            available_at: second_route,
        };
        let effective = [
            ImplementationHeadRef::Imported(&first),
            ImplementationHeadRef::Imported(&second),
        ];

        let mut short = InterfaceConstraintBudget::with_limit(6);
        assert_eq!(
            check_effective_implementation_heads(&effective, &mut short),
            Err(TypeError::Internal(
                ElaborationFailure::ConstraintResourceExhausted
            ))
        );

        let mut exact = InterfaceConstraintBudget::with_limit(7);
        let error = check_effective_implementation_heads(&effective, &mut exact)
            .expect_err("the later retained route should expose the overlap");
        let TypeError::Interface(diagnostic) = error else {
            panic!("the overlap should use an interface diagnostic");
        };
        assert_eq!(diagnostic.primary.span(), second_route);
        assert_eq!(
            diagnostic
                .related
                .iter()
                .map(SourceLabel::span)
                .collect::<Vec<_>>(),
            vec![first_definition, first_route, second_definition]
        );
        assert_eq!(exact.used(), 7);
        assert_eq!(exact.charge(1), Err(()));
    }

    #[test]
    fn impl_head_replacement_storage_drops_iteratively_on_a_small_stack() {
        std::thread::Builder::new()
            .stack_size(64 * 1024)
            .spawn(|| {
                let mut head = Type::Int;
                for _ in 0..10_000 {
                    head = Type::Function(Box::new(Type::Unit), Box::new(head));
                }
                let mut replacements = TypeReplacementBuffer(HashMap::new());
                replacements.0.insert(TypeVariableId::generated(0), head);
                drop(replacements);
            })
            .expect("the small-stack replacement drop thread should start")
            .join()
            .expect("the replacement buffer should dismantle the deep head iteratively");
    }

    #[test]
    fn zonking_reports_unsolved_inference_during_its_charged_pass() {
        let inference = InferenceVariableId::new(0);
        let source = Type::Function(Box::new(Type::Inference(inference)), Box::new(Type::Int));
        let mut remaining = 3_usize;

        let (zonked, unresolved) = zonk_type_with_status(&source, &HashMap::new(), |cells| {
            remaining = remaining.checked_sub(cells).ok_or(())?;
            Ok::<(), ()>(())
        })
        .expect("the exact expanded type should fit");

        assert_eq!(zonked, source);
        assert!(unresolved);
        assert_eq!(remaining, 0);
    }

    #[test]
    fn wide_zonk_rebuilds_keep_pending_fan_out_constant() {
        const WIDTH: usize = 4_096;
        let source =
            SourceFile::new("wide-zonk-pending.ash", "()").expect("the fixture should fit");
        let owner = crate::types::NominalTypeId::new(source.id(), 0);
        for ty in [
            Type::Tuple(vec![Type::Int; WIDTH].into_boxed_slice()),
            Type::AppliedNominal(owner, vec![Type::Int; WIDTH].into_boxed_slice()),
        ] {
            ZONK_REBUILD_PENDING_PEAK.with(|peak| peak.set(0));
            let rebuilt = zonk_type(&ty, &HashMap::new());
            assert_eq!(rebuilt, ty);
            let peak = ZONK_REBUILD_PENDING_PEAK.with(std::cell::Cell::get);
            assert!(peak <= 3, "wide zonk retained {peak} pending tasks");
        }
    }

    #[test]
    fn wide_occurs_checks_keep_pending_fan_out_constant() {
        const WIDTH: usize = 4_096;
        let source =
            SourceFile::new("wide-occurs-pending.ash", "()").expect("the fixture should fit");
        let owner = crate::types::NominalTypeId::new(source.id(), 0);
        let needle = InferenceVariableId::new(0);
        for ty in [
            Type::Tuple(vec![Type::Int; WIDTH].into_boxed_slice()),
            Type::AppliedNominal(owner, vec![Type::Int; WIDTH].into_boxed_slice()),
        ] {
            OCCURS_PENDING_PEAK.with(|peak| peak.set(0));
            assert!(!type_contains_inference(&ty, needle, &HashMap::new()));
            let peak = OCCURS_PENDING_PEAK.with(std::cell::Cell::get);
            assert!(peak <= 2, "wide occurs check retained {peak} pending tasks");
        }
    }

    #[test]
    fn retained_type_clones_require_the_exact_preallocation_budget() {
        let ty = Type::Tuple(vec![Type::Int, Type::Bool, Type::Unit].into_boxed_slice());

        let mut short = TypeWorkBudget::default();
        short
            .charge(crate::types::TYPE_WORK_LIMIT - 3)
            .expect("the fixture leaves one fewer cell than the clone requires");
        assert_eq!(clone_type_with_budget(&ty, &mut short), Err(()));

        let mut exact = TypeWorkBudget::default();
        exact
            .charge(crate::types::TYPE_WORK_LIMIT - 4)
            .expect("the fixture leaves the exact clone size");
        assert_eq!(clone_type_with_budget(&ty, &mut exact), Ok(ty));
        assert_eq!(exact.charge(1), Err(()));
    }

    #[test]
    fn ordinary_tuple_type_wrapper_requires_one_preallocated_unit() {
        let resolved =
            resolved_module_fixture("ordinary-tuple-budget.ash", "", "(Int, Int)", "(1, 2)");

        let mut short = Elaborator::for_module(&resolved).expect("the binder namespace should fit");
        short
            .type_work
            .charge(crate::types::TYPE_WORK_LIMIT - 3)
            .expect("the fixture leaves only the complete Core type copy");
        assert_eq!(
            short.elaborate_expression_with_context(
                ElaborationTask::Synthesize {
                    expression: fixture_result(&resolved),
                    cause: None,
                },
                &mut TypeContext::new(),
            ),
            Err(TypeError::Internal(
                ElaborationFailure::TypeResourceExhausted
            ))
        );

        let mut exact = Elaborator::for_module(&resolved).expect("the binder namespace should fit");
        exact
            .type_work
            .charge(crate::types::TYPE_WORK_LIMIT - 4)
            .expect("the fixture leaves the tuple wrapper and complete Core type copy");
        let typed = exact
            .elaborate_expression_with_context(
                ElaborationTask::Synthesize {
                    expression: fixture_result(&resolved),
                    cause: None,
                },
                &mut TypeContext::new(),
            )
            .expect("the exact retained tuple type cost should fit");
        assert_eq!(
            typed.ty,
            Type::Tuple(vec![Type::Int, Type::Int].into_boxed_slice())
        );
        assert_eq!(exact.type_work.charge(1), Err(()));
    }

    #[test]
    fn inferred_anonymous_function_type_precharges_three_cells_before_inference_origins() {
        const EXACT_WORK: usize = 26;
        let resolved = resolved_module_fixture(
            "inferred-anonymous-function-budget.ash",
            "",
            "A -> A",
            "fn(value) {\nvalue\n}",
        );

        let mut short = Elaborator::for_module(&resolved).expect("the binder namespace should fit");
        short
            .type_work
            .charge(crate::types::TYPE_WORK_LIMIT - 2)
            .expect("the fixture leaves less than one inferred function type");
        assert_eq!(
            short.elaborate_expression_with_context(
                ElaborationTask::Synthesize {
                    expression: fixture_result(&resolved),
                    cause: Some(SynthesisCause::Binding(fixture_result(&resolved).span)),
                },
                &mut TypeContext::new(),
            ),
            Err(TypeError::Internal(
                ElaborationFailure::TypeResourceExhausted
            ))
        );
        assert_eq!(short.next_inference, 0);
        assert!(short.inference_origins.is_empty());

        let mut exact = Elaborator::for_module(&resolved).expect("the binder namespace should fit");
        exact
            .type_work
            .charge(crate::types::TYPE_WORK_LIMIT - EXACT_WORK)
            .expect("the fixture leaves the exact complete synthesis cost");
        let typed = exact
            .elaborate_expression_with_context(
                ElaborationTask::Synthesize {
                    expression: fixture_result(&resolved),
                    cause: Some(SynthesisCause::Binding(fixture_result(&resolved).span)),
                },
                &mut TypeContext::new(),
            )
            .expect("the exact inferred function type cost should fit");
        assert!(matches!(typed.ty, Type::Function(_, _)));
        assert_eq!(exact.type_work.charge(1), Err(()));
    }

    #[test]
    fn ordinary_match_precharges_retained_arm_and_matrix_storage() {
        let resolved = resolved_module_fixture(
            "ordinary-match-budget.ash",
            "",
            "Int",
            "match true {\ntrue => 1\nfalse => 0\n}",
        );
        let mut short = Elaborator::for_module(&resolved).expect("the binder namespace should fit");
        short
            .type_work
            .charge(crate::types::TYPE_WORK_LIMIT - 13)
            .expect("the fixture leaves one fewer unit than complete match storage requires");

        assert_eq!(
            short.elaborate_expression_with_context(
                ElaborationTask::Synthesize {
                    expression: fixture_result(&resolved),
                    cause: None,
                },
                &mut TypeContext::new(),
            ),
            Err(TypeError::Internal(
                ElaborationFailure::TypeResourceExhausted
            ))
        );

        let mut exact = Elaborator::for_module(&resolved).expect("the binder namespace should fit");
        exact
            .type_work
            .charge(crate::types::TYPE_WORK_LIMIT - 14)
            .expect("the fixture leaves type copies plus both progress and Core arm storage");
        let typed = exact
            .elaborate_expression_with_context(
                ElaborationTask::Synthesize {
                    expression: fixture_result(&resolved),
                    cause: None,
                },
                &mut TypeContext::new(),
            )
            .expect("the exact retained match cost should fit");
        assert_eq!(typed.ty, Type::Int);
        assert_eq!(exact.type_work.charge(1), Err(()));
    }

    #[test]
    fn retained_scheme_clones_precharge_body_quantifiers_and_wrapper() {
        let fact = TypeFact {
            ty: Type::Tuple(vec![Type::Int, Type::Bool, Type::Unit].into_boxed_slice()),
            provenance: TypeProvenance::atom(None),
            quantified: vec![
                TypeVariableId::new(0),
                TypeVariableId::new(1),
                TypeVariableId::new(2),
            ]
            .into_boxed_slice(),
        };

        let mut short = TypeWorkBudget::default();
        short
            .charge(crate::types::TYPE_WORK_LIMIT - 7)
            .expect("the fixture leaves one fewer unit than the complete scheme copy");
        assert_eq!(clone_scheme_with_budget(&fact, &mut short), Err(()));

        let mut exact = TypeWorkBudget::default();
        exact
            .charge(crate::types::TYPE_WORK_LIMIT - 8)
            .expect("the fixture leaves the body, quantifiers, and wrapper");
        assert_eq!(
            clone_scheme_with_budget(&fact, &mut exact),
            Ok(Type::Forall(
                fact.quantified.clone(),
                Box::new(fact.ty.clone())
            ))
        );
        assert_eq!(exact.charge(1), Err(()));
    }

    #[test]
    fn resolved_type_copies_precharge_type_and_provenance_storage() {
        let resolved = resolved_module_fixture(
            "resolved-type-copy.ash",
            "identity : Int -> Bool\nidentity value = false\n",
            "Int",
            "0",
        );
        let ResolvedDefinitionKind::Equational(equational) = &resolved.definitions()[0].kind else {
            panic!("the fixture should resolve to an equational definition");
        };
        let annotation = &equational.interface.annotation;

        let mut short = TypeWorkBudget::default();
        short
            .charge(crate::types::TYPE_WORK_LIMIT - 3)
            .expect("the fixture leaves one fewer unit than type plus the shared arena handle");
        assert_eq!(
            ProvenancedType::from_resolved_with_budget(annotation, &mut short),
            Err(TypeError::Internal(
                ElaborationFailure::TypeResourceExhausted
            ))
        );

        let mut exact = TypeWorkBudget::default();
        exact
            .charge(crate::types::TYPE_WORK_LIMIT - 4)
            .expect("the fixture leaves three type cells and one shared arena handle");
        let copied = ProvenancedType::from_resolved_with_budget(annotation, &mut exact)
            .expect("the exact retained copy should fit");
        assert_eq!(copied.ty, annotation.ty);
        assert_eq!(exact.charge(1), Err(()));
    }

    #[test]
    fn pattern_binder_storage_precharges_types_provenance_and_indexes() {
        let ty = Type::Function(Box::new(Type::Int), Box::new(Type::Bool));

        let mut short = TypeWorkBudget::default();
        short
            .charge(crate::types::TYPE_WORK_LIMIT - 10)
            .expect("the fixture leaves one fewer unit than all binder storage");
        assert_eq!(charge_pattern_binder_storage(&ty, &mut short), Err(()));

        let mut exact = TypeWorkBudget::default();
        exact
            .charge(crate::types::TYPE_WORK_LIMIT - 11)
            .expect("the fixture leaves two type copies, provenance, and two indexes");
        assert_eq!(charge_pattern_binder_storage(&ty, &mut exact), Ok(()));
        assert_eq!(exact.charge(1), Err(()));
    }

    #[test]
    fn rebuilt_unknown_provenance_requires_the_exact_node_budget() {
        let ty = Type::Function(
            Box::new(Type::Int),
            Box::new(Type::Function(Box::new(Type::Bool), Box::new(Type::Unit))),
        );

        let mut short = TypeWorkBudget::default();
        short
            .charge(crate::types::TYPE_WORK_LIMIT - 4)
            .expect("the fixture leaves one fewer unit than five provenance nodes");
        assert_eq!(unknown_provenance_with_budget(&ty, &mut short), Err(()));
        assert_eq!(
            short.charge(1),
            Err(()),
            "the failed traversal must consume the affordable prefix"
        );

        let mut exact = TypeWorkBudget::default();
        exact
            .charge(crate::types::TYPE_WORK_LIMIT - 5)
            .expect("the fixture leaves exactly five provenance nodes");
        let provenance = unknown_provenance_with_budget(&ty, &mut exact)
            .expect("the complete rebuilt provenance should fit");
        assert!(provenance.aligns(&ty));
        assert_eq!(exact.charge(1), Err(()));
    }

    #[test]
    fn direct_function_binder_context_entries_require_one_reserved_unit() {
        let mut context = TypeContext::new();
        let mut short = TypeWorkBudget::default();
        short
            .charge(crate::types::TYPE_WORK_LIMIT)
            .expect("the fixture exhausts the budget before context storage");
        assert_eq!(reserve_context_entry(&mut context, &mut short), Err(()));
        assert_eq!(context.binders.capacity(), 0);

        let mut exact = TypeWorkBudget::default();
        exact
            .charge(crate::types::TYPE_WORK_LIMIT - 1)
            .expect("the fixture leaves exactly one context-entry unit");
        assert_eq!(reserve_context_entry(&mut context, &mut exact), Ok(()));
        assert!(context.binders.capacity() >= 1);
        assert_eq!(exact.charge(1), Err(()));
    }

    #[test]
    fn tuple_operational_domains_charge_the_provenance_handle_separately() {
        let resolved = resolved_module_fixture(
            "tuple-operational-domain-budget.ash",
            "fn choose(left: Int, right: Bool) -> Int {\nleft\n}\n",
            "Int",
            "choose(42, false)",
        );
        let ResolvedDefinitionKind::InlineOperational(operational) =
            &resolved.definitions()[0].kind
        else {
            panic!("the fixture should resolve to an operational definition");
        };

        let mut short = TypeWorkBudget::default();
        short
            .charge(crate::types::TYPE_WORK_LIMIT - 3)
            .expect("the fixture leaves one fewer unit than tuple, annotations, and provenance");
        assert_eq!(
            operational_domain(
                &operational.header.parameters,
                operational.header.span,
                &mut short,
            ),
            Err(TypeError::Internal(
                ElaborationFailure::TypeResourceExhausted
            ))
        );

        let mut exact = TypeWorkBudget::default();
        exact
            .charge(crate::types::TYPE_WORK_LIMIT - 4)
            .expect("the fixture leaves tuple, two annotation cells, and provenance");
        let copied = operational_domain(
            &operational.header.parameters,
            operational.header.span,
            &mut exact,
        )
        .expect("the complete retained tuple domain should fit exactly");
        assert_eq!(
            copied.ty,
            Type::Tuple(vec![Type::Int, Type::Bool].into_boxed_slice())
        );
        assert!(copied.provenance.aligns(&copied.ty));
        assert_eq!(exact.charge(1), Err(()));
    }

    #[test]
    fn unsolved_inference_collection_precharges_indexes_and_results() {
        let first = InferenceVariableId::new(0);
        let second = InferenceVariableId::new(1);
        let ty =
            Type::Tuple(vec![Type::Inference(first), Type::Inference(second)].into_boxed_slice());

        let mut short = TypeWorkBudget::default();
        short
            .charge(crate::types::TYPE_WORK_LIMIT - 6)
            .expect("the fixture leaves one fewer unit than traversal plus retained indexes");
        assert_eq!(collect_unsolved_inference(&ty, &mut short), Err(()));

        let mut exact = TypeWorkBudget::default();
        exact
            .charge(crate::types::TYPE_WORK_LIMIT - 7)
            .expect("the fixture leaves three visits and two units per retained inference");
        assert_eq!(
            collect_unsolved_inference(&ty, &mut exact),
            Ok(vec![first, second])
        );
        assert_eq!(exact.charge(1), Err(()));
    }

    #[test]
    fn polymorphic_instantiation_precharges_all_retained_metadata() {
        let source =
            SourceFile::new("instantiate-budget.ash", "()\n").expect("the fixture should fit");
        let span = source
            .span(ByteRange::new(0, 2).expect("the range is ordered"))
            .expect("the complete fixture should form a span");
        let fact = TypeFact {
            ty: Type::Unit,
            provenance: TypeProvenance::atom(Some(span)),
            quantified: vec![
                TypeVariableId::new(0),
                TypeVariableId::new(1),
                TypeVariableId::new(2),
            ]
            .into_boxed_slice(),
        };

        let mut short = Elaborator::new();
        short
            .type_work
            .charge(crate::types::TYPE_WORK_LIMIT - 8)
            .expect("the fixture leaves one fewer unit than the metadata preflight");
        assert_eq!(
            short.instantiate(&fact, false, span),
            Err(TypeError::Internal(
                ElaborationFailure::TypeResourceExhausted
            ))
        );
        assert_eq!(short.next_inference, 0);
        assert_eq!(short.inference_origins.len(), 0);
        assert_eq!(short.inference_origins.capacity(), 0);

        let mut exact = Elaborator::new();
        exact
            .type_work
            .charge(crate::types::TYPE_WORK_LIMIT - 10)
            .expect("the fixture leaves metadata plus the substituted result");
        let (instantiated, arguments) = exact
            .instantiate(&fact, false, span)
            .expect("the exact retained allocation cost should fit");
        assert_eq!(instantiated, Type::Unit);
        assert_eq!(arguments.len(), 3);
        assert_eq!(exact.inference_origins.len(), 3);
        assert_eq!(exact.type_work.charge(1), Err(()));
    }

    #[test]
    fn wide_polymorphic_occurrence_fails_before_instantiation_allocation() {
        const WIDTH: usize = 4_096;
        let resolved = resolved_module_fixture(
            "wide-occurrence-budget.ash",
            "",
            "A -> A",
            "fn(value) {\nvalue\n}",
        );
        let ResolvedExprKind::Function(function) = &fixture_result(&resolved).kind else {
            panic!("the fixture result should be a function");
        };
        let ResolvedPatternKind::Binder(parameter) = &function.pattern.kind else {
            panic!("the fixture parameter should be a binder");
        };
        let quantified = (0..WIDTH)
            .map(|index| TypeVariableId::new(u32::try_from(index).expect("parameter identity")))
            .collect::<Vec<_>>()
            .into_boxed_slice();
        let mut context = TypeContext::new();
        context.binders.insert(
            parameter.id,
            TypeFact {
                ty: Type::Unit,
                provenance: TypeProvenance::atom(Some(function.body.result.span)),
                quantified,
            },
        );
        let mut elaborator =
            Elaborator::for_module(&resolved).expect("the binder namespace should fit");
        elaborator
            .type_work
            .charge(crate::types::TYPE_WORK_LIMIT - (WIDTH * 3 - 1))
            .expect("the fixture leaves one fewer unit than metadata ownership requires");

        assert_eq!(
            elaborator.elaborate_expression_with_context(
                ElaborationTask::Synthesize {
                    expression: &function.body.result,
                    cause: None,
                },
                &mut context,
            ),
            Err(TypeError::Internal(
                ElaborationFailure::TypeResourceExhausted
            ))
        );
        assert_eq!(elaborator.next_inference, 0);
        assert_eq!(elaborator.inference_origins.len(), 0);
        assert_eq!(elaborator.inference_origins.capacity(), 0);
    }

    #[test]
    fn unification_charges_operand_copies_and_solution_metadata_exactly() {
        let inference = Type::Inference(InferenceVariableId::new(0));

        let mut short = Elaborator::new();
        short
            .type_work
            .charge(crate::types::TYPE_WORK_LIMIT - 7)
            .expect("the fixture leaves one fewer unit than one scalar solution requires");
        assert_eq!(
            short.unify(&inference, &Type::Int),
            Err(UnificationFailure::Resource)
        );
        assert!(short.inference_solutions.is_empty());

        let mut exact = Elaborator::new();
        exact
            .type_work
            .charge(crate::types::TYPE_WORK_LIMIT - 8)
            .expect("the fixture leaves comparison, operand copies, zonks, and solution storage");
        assert_eq!(exact.unify(&inference, &Type::Int), Ok(()));
        assert_eq!(
            exact.inference_solutions,
            HashMap::from([(InferenceVariableId::new(0), Type::Int)])
        );
        assert_eq!(exact.type_work.charge(1), Err(()));
    }

    #[test]
    fn public_monotype_admission_enforces_the_exact_core_payload_depth() {
        let accepted = nested_function_type(CORE_PAYLOAD_DEPTH_LIMIT);
        let rejected = nested_function_type(CORE_PAYLOAD_DEPTH_LIMIT + 1);
        let mut accepted_budget = TypeWorkBudget::default();
        let mut rejected_budget = TypeWorkBudget::default();

        assert_eq!(
            validate_and_charge_public_monotype(&accepted, &mut accepted_budget),
            Ok(())
        );
        assert_eq!(
            validate_and_charge_public_monotype(&rejected, &mut rejected_budget),
            Err(PublicTypeAdmissionError::Invalid)
        );

        crate::types::discard_type_iteratively(accepted);
        crate::types::discard_type_iteratively(rejected);
    }

    #[test]
    fn public_context_admission_charges_fact_metadata_before_context_clone() {
        let mut context = TypeContext::new();
        context.insert(BinderId::new(0), Type::Unit);

        let mut short = Elaborator::new();
        short
            .type_work
            .charge(crate::types::TYPE_WORK_LIMIT - 1)
            .expect("the fixture leaves only the retained map entry cost");
        assert_eq!(
            short.admit_public_context(&context),
            Err(TypeError::Internal(
                ElaborationFailure::TypeResourceExhausted
            ))
        );

        let mut exact = Elaborator::new();
        exact
            .type_work
            .charge(crate::types::TYPE_WORK_LIMIT - 2)
            .expect("the fixture leaves the map entry and scalar type copy costs");
        assert_eq!(exact.admit_public_context(&context), Ok(()));
        assert_eq!(exact.type_work.charge(1), Err(()));
    }

    #[test]
    fn function_part_clones_charge_both_children_but_not_the_outer_arrow() {
        let domain = Type::Tuple(vec![Type::Int, Type::Bool].into_boxed_slice());
        let codomain = Type::Function(Box::new(Type::Unit), Box::new(Type::Int));
        let function = Type::Function(Box::new(domain.clone()), Box::new(codomain.clone()));

        let mut short = TypeWorkBudget::default();
        short
            .charge(crate::types::TYPE_WORK_LIMIT - 5)
            .expect("the fixture leaves one fewer cell than both children require");
        assert_eq!(
            clone_function_parts_with_budget(&function, &mut short),
            Err(())
        );

        let mut exact = TypeWorkBudget::default();
        exact
            .charge(crate::types::TYPE_WORK_LIMIT - 6)
            .expect("the fixture leaves exactly the two child sizes");
        assert_eq!(
            clone_function_parts_with_budget(&function, &mut exact),
            Ok((domain, codomain))
        );
        assert_eq!(exact.charge(1), Err(()));
    }

    #[test]
    fn retained_forall_clones_charge_quantifier_identities_before_allocation() {
        let parameters = vec![
            TypeVariableId::new(0),
            TypeVariableId::new(1),
            TypeVariableId::new(2),
        ]
        .into_boxed_slice();
        let ty = Type::Forall(parameters, Box::new(Type::Int));

        let mut short = TypeWorkBudget::default();
        short
            .charge(crate::types::TYPE_WORK_LIMIT - 4)
            .expect("the fixture leaves one fewer cell than the retained clone requires");
        assert_eq!(clone_type_with_budget(&ty, &mut short), Err(()));

        let mut exact = TypeWorkBudget::default();
        exact
            .charge(crate::types::TYPE_WORK_LIMIT - 5)
            .expect("the fixture leaves the wrapper, binder identities, and body");
        assert_eq!(clone_type_with_budget(&ty, &mut exact), Ok(ty));
        assert_eq!(exact.charge(1), Err(()));
    }

    #[test]
    fn function_part_clones_charge_forall_domain_binders() {
        let parameters = vec![
            TypeVariableId::new(0),
            TypeVariableId::new(1),
            TypeVariableId::new(2),
        ]
        .into_boxed_slice();
        let domain = Type::Forall(parameters, Box::new(Type::Int));
        let function = Type::Function(Box::new(domain.clone()), Box::new(Type::Bool));

        let mut short = TypeWorkBudget::default();
        short
            .charge(crate::types::TYPE_WORK_LIMIT - 5)
            .expect("the fixture leaves one fewer cell than both retained children require");
        assert_eq!(
            clone_function_parts_with_budget(&function, &mut short),
            Err(())
        );

        let mut exact = TypeWorkBudget::default();
        exact
            .charge(crate::types::TYPE_WORK_LIMIT - 6)
            .expect("the fixture leaves the exact two-child clone cost");
        assert_eq!(
            clone_function_parts_with_budget(&function, &mut exact),
            Ok((domain, Type::Bool))
        );
        assert_eq!(exact.charge(1), Err(()));
    }

    #[test]
    fn zonking_charges_only_expanded_cells_through_solved_aliases() {
        let root_alias = InferenceVariableId::new(9);
        let nested_alias = InferenceVariableId::new(8);
        let unresolved_leaf = InferenceVariableId::new(1);
        let result = Type::Tuple(vec![Type::Bool, Type::Unit].into_boxed_slice());
        let expected = Type::Function(
            Box::new(Type::Int),
            Box::new(Type::Function(
                Box::new(Type::Inference(unresolved_leaf)),
                Box::new(result.clone()),
            )),
        );
        let solutions = HashMap::from([
            (
                root_alias,
                Type::Function(
                    Box::new(Type::Int),
                    Box::new(Type::Function(
                        Box::new(Type::Inference(nested_alias)),
                        Box::new(result),
                    )),
                ),
            ),
            (nested_alias, Type::Inference(unresolved_leaf)),
        ]);
        let source = Type::Inference(root_alias);
        let mut exact_remaining = 7_usize;

        let (zonked, unresolved) = zonk_type_with_status(&source, &solutions, |cells| {
            exact_remaining = exact_remaining.checked_sub(cells).ok_or(())?;
            Ok::<(), ()>(())
        })
        .expect("seven expanded-result cells should fit exactly");

        assert_eq!(zonked, expected);
        assert!(unresolved);
        assert_eq!(exact_remaining, 0);

        let mut short_remaining = 6_usize;
        let short = zonk_type_with_status(&source, &solutions, |cells| {
            short_remaining = short_remaining.checked_sub(cells).ok_or(())?;
            Ok::<(), ()>(())
        });

        assert_eq!(short, Err(()));
        assert_eq!(short_remaining, 0);
    }

    #[test]
    fn finish_rejects_unresolved_inference_without_core_escape() {
        let resolved = resolved_module_fixture(
            "unresolved-finish.ash",
            "",
            "Unit",
            "{\nlet _ = fn(value) {\nvalue\n}\n()\n}",
        );
        let mut elaborator =
            Elaborator::for_module(&resolved).expect("the binder namespace should fit");
        let typed = elaborator
            .synthesize(fixture_result(&resolved), &TypeContext::new())
            .expect("standalone synthesis defers whole-program ambiguity");

        assert!(matches!(
            elaborator.finish(typed.node),
            Err(ElaborationFailure::Core(BuildError::InvalidPayload))
        ));
    }

    #[test]
    fn public_synthesis_rejects_unresolved_inference_before_context_clone() {
        let resolved = resolved_module_fixture(
            "external-inference-finish.ash",
            "identity : Int -> Int\nidentity value = value\n",
            "Int -> Int",
            "identity",
        );
        let ResolvedExprKind::Occurrence(occurrence) = &fixture_result(&resolved).kind else {
            panic!("the result should be a resolved occurrence");
        };
        let mut context = TypeContext::new();
        context.insert(
            occurrence
                .global_binder()
                .expect("the fixture occurrence should be an ordinary binder"),
            Type::Inference(InferenceVariableId::new(999)),
        );
        let mut elaborator =
            Elaborator::for_module(&resolved).expect("the binder namespace should fit");
        TYPE_CONTEXT_CLONES.with(|clones| clones.set(0));

        assert_eq!(
            elaborator.synthesize(fixture_result(&resolved), &context),
            Err(TypeError::Internal(ElaborationFailure::InvalidState))
        );
        TYPE_CONTEXT_CLONES.with(|clones| assert_eq!(clones.get(), 0));
    }

    #[test]
    fn public_context_inference_cannot_alias_a_fresh_private_solution() {
        let resolved = resolved_module_fixture(
            "external-inference-collision.ash",
            "external : Int -> Int\nexternal value = value\n",
            "Int -> Int",
            "{\nlet increment = fn(value) {\nvalue + 1\n}\nexternal\n}",
        );
        let ResolvedExprKind::Block(block) = &fixture_result(&resolved).kind else {
            panic!("the result should be a block");
        };
        let ResolvedExprKind::Occurrence(occurrence) = &block.result.kind else {
            panic!("the block result should be a resolved occurrence");
        };
        let mut context = TypeContext::new();
        context.insert(
            occurrence
                .global_binder()
                .expect("the fixture occurrence should be an ordinary binder"),
            Type::Inference(InferenceVariableId::new(0)),
        );
        let mut elaborator =
            Elaborator::for_module(&resolved).expect("the binder namespace should fit");

        assert_eq!(
            elaborator.synthesize(fixture_result(&resolved), &context),
            Err(TypeError::Internal(ElaborationFailure::InvalidState))
        );
    }

    #[test]
    fn public_synthesis_charges_a_wide_context_type_before_context_clone() {
        let resolved = resolved_module_fixture(
            "external-wide-context.ash",
            "identity : Int -> Int\nidentity value = value\n",
            "Int -> Int",
            "identity",
        );
        let ResolvedExprKind::Occurrence(occurrence) = &fixture_result(&resolved).kind else {
            panic!("the result should be a resolved occurrence");
        };
        let mut context = TypeContext::new();
        context.insert(
            occurrence
                .global_binder()
                .expect("the fixture occurrence should be an ordinary binder"),
            Type::Tuple(vec![Type::Int; crate::types::TYPE_WORK_LIMIT].into_boxed_slice()),
        );
        let mut elaborator =
            Elaborator::for_module(&resolved).expect("the binder namespace should fit");
        TYPE_CONTEXT_CLONES.with(|clones| clones.set(0));

        assert_eq!(
            elaborator.synthesize(fixture_result(&resolved), &context),
            Err(TypeError::Internal(
                ElaborationFailure::TypeResourceExhausted
            ))
        );
        TYPE_CONTEXT_CLONES.with(|clones| assert_eq!(clones.get(), 0));
    }

    #[test]
    fn public_context_resource_precedes_invalid_type_independent_of_insertion_order() {
        let resolved = resolved_module_fixture("public-context-order.ash", "", "Int", "42");

        for round in 0..16_u32 {
            let first_id = BinderId::new(round * 2);
            let second_id = BinderId::new(round * 2 + 1);
            let mut context = TypeContext::new();
            if round % 2 == 0 {
                context.insert(first_id, Type::Unit);
                context.insert(second_id, Type::Unit);
            } else {
                context.insert(second_id, Type::Unit);
                context.insert(first_id, Type::Unit);
            }
            let ids = context.binders.keys().copied().collect::<Vec<_>>();
            context.insert(ids[0], Type::Inference(InferenceVariableId::new(0)));
            context.insert(ids[1], Type::Tuple(vec![Type::Int; 8].into_boxed_slice()));
            let mut elaborator = Elaborator::new();
            elaborator
                .type_work
                .charge(crate::types::TYPE_WORK_LIMIT - 9)
                .expect("the fixture leaves exactly the wide valid type allowance");
            TYPE_CONTEXT_CLONES.with(|clones| clones.set(0));

            assert_eq!(
                elaborator.synthesize(fixture_result(&resolved), &context),
                Err(TypeError::Internal(
                    ElaborationFailure::TypeResourceExhausted
                ))
            );
            TYPE_CONTEXT_CLONES.with(|clones| assert_eq!(clones.get(), 0));
        }
    }

    #[test]
    fn public_context_resource_precedes_invalid_quantification() {
        let resolved =
            resolved_module_fixture("public-context-quantification.ash", "", "Int", "42");
        let mut context = TypeContext::new();
        context.insert(BinderId::new(0), Type::Unit);
        context.insert(BinderId::new(1), Type::Unit);
        let ids = context.binders.keys().copied().collect::<Vec<_>>();
        context
            .set_quantified(ids[0], vec![TypeVariableId::new(0)].into_boxed_slice())
            .expect("the fact exists");
        context.insert(ids[1], Type::Tuple(vec![Type::Int; 8].into_boxed_slice()));
        let mut elaborator = Elaborator::new();
        elaborator
            .type_work
            .charge(crate::types::TYPE_WORK_LIMIT - 9)
            .expect("the fixture leaves exactly the wide valid type allowance");
        TYPE_CONTEXT_CLONES.with(|clones| clones.set(0));

        assert_eq!(
            elaborator.synthesize(fixture_result(&resolved), &context),
            Err(TypeError::Internal(
                ElaborationFailure::TypeResourceExhausted
            ))
        );
        TYPE_CONTEXT_CLONES.with(|clones| assert_eq!(clones.get(), 0));
    }

    #[test]
    fn public_check_rejects_inference_in_the_expected_type() {
        let resolved = resolved_module_fixture("external-expected-inference.ash", "", "Int", "42");
        let mut elaborator = Elaborator::new();

        assert_eq!(
            elaborator.check(
                fixture_result(&resolved),
                &Type::Inference(InferenceVariableId::new(0)),
                &TypeContext::new(),
            ),
            Err(TypeError::Internal(ElaborationFailure::InvalidState))
        );
    }

    #[test]
    fn public_check_rejects_wide_higher_rank_expected_type_before_clone() {
        let resolved = resolved_module_fixture(
            "external-higher-rank.ash",
            "",
            "A -> Int",
            "fn(value) {\n42\n}",
        );
        let parameters = (0..crate::types::TYPE_WORK_LIMIT)
            .map(|index| TypeVariableId::new(u32::try_from(index).expect("parameter identity")))
            .collect::<Vec<_>>()
            .into_boxed_slice();
        let expected = Type::Function(
            Box::new(Type::Forall(parameters, Box::new(Type::Int))),
            Box::new(Type::Int),
        );
        let mut elaborator = Elaborator::new();

        assert_eq!(
            elaborator.check(fixture_result(&resolved), &expected, &TypeContext::new()),
            Err(TypeError::Internal(ElaborationFailure::InvalidState))
        );
    }

    #[test]
    fn public_deep_types_reject_before_clone_and_drop_on_a_small_stack() {
        std::thread::Builder::new()
            .name("public-type-depth-boundary".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                const DEPTH: usize = 10_000;
                let resolved = resolved_module_fixture("external-deep-type.ash", "", "Int", "42");

                let expected = nested_function_type(DEPTH);
                let mut checking = Elaborator::new();
                let check_result =
                    checking.check(fixture_result(&resolved), &expected, &TypeContext::new());
                crate::types::discard_type_iteratively(expected);
                assert_eq!(
                    check_result,
                    Err(TypeError::Internal(ElaborationFailure::InvalidState))
                );

                let binder = BinderId::new(0);
                let mut context = TypeContext::new();
                context.insert(binder, nested_function_type(DEPTH));
                let mut synthesizing = Elaborator::new();
                TYPE_CONTEXT_CLONES.with(|clones| clones.set(0));
                let synthesize_result =
                    synthesizing.synthesize(fixture_result(&resolved), &context);
                let clone_count = TYPE_CONTEXT_CLONES.with(std::cell::Cell::get);
                let TypeFact {
                    ty,
                    provenance,
                    quantified,
                } = context.binders.remove(&binder).expect("the fact exists");
                crate::types::discard_type_iteratively(ty);
                drop(provenance);
                drop(quantified);

                assert_eq!(
                    synthesize_result,
                    Err(TypeError::Internal(ElaborationFailure::InvalidState))
                );
                assert_eq!(clone_count, 0);
            })
            .expect("the depth-boundary thread should start")
            .join()
            .expect("public type depth rejection must fit the small stack");
    }

    #[test]
    fn constrained_scheme_construction_has_an_exact_stack_safe_type_budget() {
        std::thread::Builder::new()
            .name("constrained-scheme-budget".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                const DEPTH: usize = 10_000;
                const EXACT_WORK: usize = 2 * DEPTH + 4;
                let resolved = resolved_module_fixture(
                    "constrained-scheme-budget.ash",
                    "interface Equal<A> {\nequal : (A, A) -> Bool\n}\n\nvalue : A -> Bool where Equal<A>\nvalue argument = true\n",
                    "Unit",
                    "()",
                );
                let mut definitions = resolved.definitions()[..1].to_vec();
                let ResolvedDefinitionKind::Equational(global) = &mut definitions[0].kind else {
                    panic!("the constrained fixture should be equational");
                };
                global.interface.annotation.ty = nested_function_type(DEPTH);

                let mut short = Elaborator::for_module(&resolved)
                    .expect("the constrained fixture namespace should fit");
                short.type_work = TypeWorkBudget::with_limit(EXACT_WORK - 1);
                assert_eq!(
                    short.checked_module_schemes(&definitions),
                    Err(TypeError::Internal(
                        ElaborationFailure::TypeResourceExhausted
                    ))
                );

                let mut exact = Elaborator::for_module(&resolved)
                    .expect("the constrained fixture namespace should fit");
                exact.type_work = TypeWorkBudget::with_limit(EXACT_WORK);
                let schemes = exact
                    .checked_module_schemes(&definitions)
                    .expect("the exact constrained-scheme type budget should fit");
                assert_eq!(exact.type_work.charge(1), Err(()));
                drop(schemes);

                let ResolvedDefinitionKind::Equational(global) = &mut definitions[0].kind else {
                    unreachable!()
                };
                let deep = std::mem::replace(&mut global.interface.annotation.ty, Type::Unit);
                discard_type_iteratively(deep);
            })
            .expect("the constrained-scheme budget thread should start")
            .join()
            .expect("constrained-scheme construction must fit the small stack");
    }

    #[test]
    fn unsolved_inference_collection_is_indexed_and_charged_in_source_order() {
        let first = InferenceVariableId::new(2);
        let second = InferenceVariableId::new(1);
        let third = InferenceVariableId::new(3);
        let ty = Type::Tuple(
            vec![
                Type::Inference(first),
                Type::Inference(second),
                Type::Inference(first),
                Type::Inference(third),
            ]
            .into_boxed_slice(),
        );
        let mut budget = TypeWorkBudget::default();
        budget
            .charge(crate::types::TYPE_WORK_LIMIT - 11)
            .expect("the fixture leaves visits plus two retained indexes per unique inference");

        let found = collect_unsolved_inference(&ty, &mut budget)
            .expect("the exact traversal and retained-index budget should fit");

        assert_eq!(found, [first, second, third]);
        assert_eq!(budget.charge(1), Err(()));
    }

    #[test]
    fn a_changed_static_outcome_remains_inside_its_owning_rule_helper() {
        assert!(static_rule_outcome(
            &Type::Bool,
            &Type::Bool,
            structurally_equal
        ));
        assert!(!static_rule_outcome(
            &Type::Bool,
            &Type::Bool,
            mock_bool_distinct_rule
        ));
        assert!(static_rule_outcome(
            &Type::Int,
            &Type::Int,
            mock_bool_distinct_rule
        ));
    }

    #[test]
    fn provenance_rejects_a_shape_mismatch() {
        let ty = Type::Function(Box::new(Type::Int), Box::new(Type::Bool));
        let provenance = TypeProvenance::atom(None);

        assert!(!provenance.aligns(&ty));
        assert_eq!(
            provenance.function_parts(&ty),
            Err(TypeError::Internal(ElaborationFailure::InvalidState))
        );
    }

    #[test]
    fn a_shape_mismatch_poisoning_prevents_later_elaboration() {
        let program = resolved_module_fixture(
            "mismatched-provenance.ash",
            "",
            "A -> A",
            "fn(value) {\n    value\n}",
        );
        let ResolvedExprKind::Function(function) = &fixture_result(&program).kind else {
            panic!("expected an anonymous function");
        };
        let ResolvedPatternKind::Binder(parameter) = &function.pattern.kind else {
            panic!("expected a binder parameter");
        };
        let mut context = TypeContext::new();
        context.binders.insert(
            parameter.id,
            TypeFact {
                ty: Type::Function(Box::new(Type::Int), Box::new(Type::Int)),
                provenance: TypeProvenance::atom(None),
                quantified: Box::new([]),
            },
        );
        let mut elaborator = Elaborator::for_module_with_work(
            &program,
            TypeWorkBudget::default(),
            UsefulnessBudget::default(),
        )
        .expect("binder reservation should fit");

        assert_eq!(
            elaborator.synthesize(&function.body.result, &context),
            Err(TypeError::Internal(ElaborationFailure::InvalidState))
        );
        assert_eq!(
            elaborator.synthesize(&function.body.result, &context),
            Err(TypeError::Internal(ElaborationFailure::InvalidState))
        );
    }

    #[test]
    fn recursive_global_elaboration_does_not_clone_the_complete_context() {
        let mut text = String::new();
        text.push_str("f0 : Int -> Int\nf0 value = value\n");
        for index in 1..32 {
            use std::fmt::Write as _;
            writeln!(text, "f{index} : Int -> Int").expect("writing to a String cannot fail");
            writeln!(text, "f{index} value = f{} value", index - 1)
                .expect("writing to a String cannot fail");
        }
        let program = resolved_module_fixture("sequential-globals.ash", &text, "Int", "f31 42");
        let mut elaborator = Elaborator::for_module_with_work(
            &program,
            TypeWorkBudget::default(),
            UsefulnessBudget::default(),
        )
        .expect("binder reservation should fit");
        let schemes = elaborator
            .checked_module_schemes(program.definitions())
            .expect("the declared global schemes should fit");
        TYPE_CONTEXT_CLONES.with(|clones| clones.set(0));

        elaborator
            .check_module_bodies(
                &program,
                &schemes,
                &[],
                &[],
                &mut InterfaceConstraintBudget::default(),
            )
            .expect("recursive globals should elaborate");

        TYPE_CONTEXT_CLONES.with(|clones| {
            assert_eq!(
                clones.get(),
                1,
                "the fixed base context may be cloned once, independent of global count"
            );
        });
    }

    #[test]
    fn successful_function_work_restores_parameter_and_block_scopes() {
        let program = resolved_module_fixture(
            "restored-function-scope.ash",
            "",
            "A -> A",
            "fn(parameter) {\n    let local = parameter\n    local\n}",
        );
        let mut elaborator =
            Elaborator::for_module(&program).expect("binder reservation should fit");
        let mut context = TypeContext::new();
        let expected =
            ProvenancedType::unknown(Type::Function(Box::new(Type::Int), Box::new(Type::Int)));

        elaborator
            .elaborate_expression_with_context(
                ElaborationTask::Check {
                    expression: fixture_result(&program),
                    expected,
                    kind: CheckKind::General,
                },
                &mut context,
            )
            .expect("the function should elaborate");

        assert_eq!(context, TypeContext::new());
    }

    #[test]
    fn provenance_cursor_is_stack_safe_at_the_type_depth_boundary() {
        const DEPTH: usize = 128;
        std::thread::Builder::new()
            .stack_size(256 * 1024)
            .spawn(|| {
                let mut ty = Type::Int;
                for _ in 0..DEPTH {
                    ty = Type::Function(Box::new(Type::Unit), Box::new(ty));
                }
                let mut current = ProvenancedType::unknown(ty);
                assert!(current.provenance.aligns(&current.ty));
                for _ in 0..DEPTH {
                    let (_, codomain) = current
                        .into_function_parts()
                        .expect("the constructed type is a function at this depth");
                    current = codomain;
                }
                assert_eq!(current.ty, Type::Int);
                assert!(current.provenance.aligns(&current.ty));
            })
            .expect("the boundary thread should start")
            .join()
            .expect("provenance construction and cursor movement should not overflow");
    }
}
