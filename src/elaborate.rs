//! Bidirectional typed elaboration from resolved surface syntax to pure Core.

use std::{
    collections::{HashMap, HashSet},
    error::Error,
    fmt,
    ops::Deref,
    sync::Arc,
};

use crate::{
    core::dialect::{
        MethodEvidenceAnchorRole, MethodEvidenceOwner,
        MethodEvidenceProducer as CoreMethodEvidenceProducer,
    },
    core::{
        BuildError, CORE_PAYLOAD_DEPTH_LIMIT, CoreBuilder, CoreMatchArm, CorePattern,
        CorePatternKind, NodeId, Primitive, TypedBinder, UnvalidatedProgram,
    },
    diagnostic::{Diagnostic, SourceLabel},
    evidence::{
        EvidenceSelector, ImprovementTask, MethodObligationMetadata, MethodRigidityCheck,
        MethodRigidityCondition, MethodRigiditySite, MethodRigidityTarget,
        PendingEvidencePublication, PendingObligationMarker, SelectionCauseKind, SelectionError,
        SelectionFailure, SelectionSite,
    },
    evidence_audit::{EvidenceAuditFailure, audit_checked_body_evidence},
    evidence_validation::ValidatedInterfaceProgram,
    interface::{
        CheckedImplMethod, CheckedImplementation, CheckedInterface, CheckedRequirement,
        ConstrainedScheme, DeterminationKey, EvidenceNode, EvidenceSelection, ImplId, ImplMethodId,
        InterfaceApplication, InterfaceConstraintBudget, InterfaceId, InterfaceOperationWork,
        InterfaceReason, MethodId, OverlapFailure, RequirementId,
        implementation_application_heads_overlap,
        implementation_prerequisite_selection_key_terminates, same_type_with_constraint_budget,
    },
    kind::{KindEnvironments, KindFailure},
    pattern::{
        UsefulnessBudget, UsefulnessError, display_witness, missing_witness_for_types_with_budget,
        usefulness_with_budget,
    },
    resolved::{
        AvailableImplementation, BinderId, CanonicalNominalKind, CheckedDefinition,
        CheckedGlobalScheme, CheckedImplementationBody, CheckedImplementationFact,
        CheckedImplementationMethodFact, CheckedInterfaceFact, CheckedInterfaceMethodFact,
        CheckedModule, CheckedModuleParts, ExportSummary, ResolvedBinding, ResolvedBlock,
        ResolvedBuildFailure, ResolvedDeclarationIndex, ResolvedDefinitionKind, ResolvedExpr,
        ResolvedExprKind, ResolvedLocalDeclaration, ResolvedModule, ResolvedModuleGroup,
        ResolvedModuleProgram, ResolvedNominalDeclarationKind, ResolvedPattern,
        ResolvedPatternKind, ResolvedRecursiveGroup, ResolvedRegistry, ResolvedType,
        ResolvedTypeProvenance, ResolvedTypeProvenanceNode,
        clone_resolved_type_variable_with_budget,
    },
    source::{GeneratedReason, Origin, Span, discard_origin_iteratively},
    types::{
        InferenceVariableId, IterativeTypeOwner, Kind, Type, TypeVariableId, TypeWorkBudget,
        charge_type_cells, clone_kind_with_budget, clone_kinded_type_parameters_with_budget,
        discard_type_iteratively, replace_type_iteratively, same_kind_with_budget,
        same_kinded_type_parameters_with_budget, same_type, same_type_with_budget,
        substitute_type_variables_with,
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
    /// A module newtype representation reaches itself through newtype declarations.
    NewtypeRecursiveRepresentation,
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
            Self::NewtypeRecursiveRepresentation => {
                formatter.write_str("newtype.recursive-representation")
            }
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

impl Drop for TypeMismatch {
    fn drop(&mut self) {
        discard_type_iteratively(std::mem::replace(self.expected.as_mut(), Type::Unit));
        discard_type_iteratively(std::mem::replace(self.found.as_mut(), Type::Unit));
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

impl Drop for TypeContext {
    fn drop(&mut self) {
        for (_, mut fact) in self.binders.drain() {
            discard_type_iteratively(std::mem::replace(&mut fact.ty, Type::Unit));
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct TypeFact {
    ty: Type,
    provenance: TypeProvenance,
    quantified: Box<[(TypeVariableId, Kind)]>,
}

type KindedTypeParameters = Box<[(TypeVariableId, Kind)]>;

fn discard_type_fact(mut fact: TypeFact) {
    discard_type_iteratively(std::mem::replace(&mut fact.ty, Type::Unit));
}

#[derive(Debug)]
struct LoweredInterfaceMethod {
    interface: InterfaceId,
    parameters: Box<[TypeVariableId]>,
    type_parameters: Box<[(TypeVariableId, Kind)]>,
    value_type: Type,
    declaration_span: Span,
}

#[derive(Debug)]
struct LoweredInterface {
    methods: Box<[MethodId]>,
    determination: Option<Box<[usize]>>,
}

impl Drop for LoweredInterfaceMethod {
    fn drop(&mut self) {
        discard_type_iteratively(std::mem::replace(&mut self.value_type, Type::Unit));
    }
}

#[derive(Debug)]
struct LoweredRequirementMethod {
    method: MethodId,
    application: InterfaceApplication,
    ty: Type,
}

impl Drop for LoweredRequirementMethod {
    fn drop(&mut self) {
        discard_type_iteratively(std::mem::replace(&mut self.ty, Type::Unit));
    }
}

#[derive(Debug)]
struct LoweredRequirement {
    owner: MethodEvidenceOwner,
    id: RequirementId,
    methods: Box<[LoweredRequirementMethod]>,
}

#[derive(Debug)]
struct LoweredScheme {
    source_type_parameters: Option<Box<[(TypeVariableId, Kind)]>>,
    type_parameters: Box<[(TypeVariableId, Kind)]>,
    requirements: Box<[LoweredRequirement]>,
    value_type: Type,
    core_scheme: Type,
}

impl LoweredScheme {
    fn source_binder_parameters(&self) -> Option<&[(TypeVariableId, Kind)]> {
        self.source_type_parameters.as_deref()
    }

    fn binder_parameters(&self) -> &[(TypeVariableId, Kind)] {
        &self.type_parameters
    }
}

impl Drop for LoweredScheme {
    fn drop(&mut self) {
        discard_type_iteratively(std::mem::replace(&mut self.value_type, Type::Unit));
        discard_type_iteratively(std::mem::replace(&mut self.core_scheme, Type::Unit));
    }
}

#[derive(Debug)]
struct LoweredImplementationMethod {
    binder: BinderId,
    head_type_parameter_count: usize,
    application: InterfaceApplication,
    scheme: LoweredScheme,
    span: Span,
}

#[derive(Debug)]
struct ActiveEvidenceBinder {
    binder: BinderId,
    application: InterfaceApplication,
    ty: Type,
}

impl Drop for ActiveEvidenceBinder {
    fn drop(&mut self) {
        discard_type_iteratively(std::mem::replace(&mut self.ty, Type::Unit));
    }
}

#[derive(Debug)]
struct LoweredEvidenceMethod {
    method: MethodId,
    node: NodeId,
    ty: Type,
    producer: PolymorphicEvidenceProducer,
    adapter_application: Option<InterfaceApplication>,
}

#[derive(Clone, Copy, Debug)]
enum PolymorphicEvidenceProducer {
    Abstract {
        requirement: RequirementId,
        selection_node: crate::interface::EvidenceNodeId,
        binder: BinderId,
    },
    Adapter {
        implementation: ImplMethodId,
        selection_node: crate::interface::EvidenceNodeId,
    },
}

impl Drop for LoweredEvidenceMethod {
    fn drop(&mut self) {
        discard_type_iteratively(std::mem::replace(&mut self.ty, Type::Unit));
    }
}

struct ScopedEvidenceBinder {
    owner: MethodEvidenceOwner,
    requirement: RequirementId,
    method: MethodId,
    application: InterfaceApplication,
    binder: TypedBinder,
}

#[derive(Debug)]
struct EvidenceLowering {
    interfaces: HashMap<InterfaceId, LoweredInterface>,
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
    Application {
        span: Option<Span>,
        function: usize,
        argument: usize,
    },
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
                Type::Application(function, argument) if !visited => {
                    tasks.push((current, true));
                    tasks.push((argument, false));
                    tasks.push((function, false));
                }
                Type::Application(_, _) => {
                    let argument = roots.pop().unwrap_or(0);
                    let function = roots.pop().unwrap_or(0);
                    nodes.push(TypeProvenanceNode::Application {
                        span,
                        function,
                        argument,
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
                    TypeProvenanceNode::Fact(span)
                    | TypeProvenanceNode::Application { span, .. }
                    | TypeProvenanceNode::Function { span, .. },
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
                        | Type::Forall(_, _),
                        Some(TypeProvenanceNode::Fact(_)),
                    ) => {}
                    (
                        Type::Application(function, argument),
                        Some(TypeProvenanceNode::Application {
                            function: function_node,
                            argument: argument_node,
                            ..
                        }),
                    ) => {
                        work.push((argument, Cursor::Built(nodes, *argument_node)));
                        work.push((function, Cursor::Built(nodes, *function_node)));
                    }
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
                        Type::Application(function, argument),
                        Some(ResolvedTypeProvenanceNode::Application {
                            function: function_node,
                            argument: argument_node,
                            ..
                        }),
                    ) => {
                        work.push((argument, Cursor::Resolved(resolved, *argument_node)));
                        work.push((function, Cursor::Resolved(resolved, *function_node)));
                    }
                    (
                        Type::Int
                        | Type::Bool
                        | Type::Unit
                        | Type::Tuple(_)
                        | Type::Nominal(_)
                        | Type::Variable(_)
                        | Type::Inference(_),
                        Some(
                            ResolvedTypeProvenanceNode::Fact(_)
                            | ResolvedTypeProvenanceNode::Tuple { .. },
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
        let domain = ProvenancedTypeOwner::new(domain);
        let codomain = ProvenancedTypeOwner::new(codomain);
        if !domain.provenance.aligns(&domain.ty) || !codomain.provenance.aligns(&codomain.ty) {
            return Err(invalid_state());
        }
        budget
            .charge(2)
            .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
        let domain = domain.into_inner();
        let codomain = codomain.into_inner();
        Ok(Self {
            ty: Type::Function(Box::new(domain.ty), Box::new(codomain.ty)),
            provenance: TypeProvenance::Function {
                span,
                parts: Arc::new((domain.provenance, codomain.provenance)),
            },
        })
    }

    fn into_function_parts(self) -> Result<(Self, Self), TypeError> {
        let value = ProvenancedTypeOwner::new(self);
        let (domain_provenance, codomain_provenance) =
            value.provenance.function_parts(&value.ty)?;
        let value = value.into_inner();
        let Type::Function(domain, codomain) = value.ty else {
            discard_type_iteratively(value.ty);
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
    pub fn insert(&mut self, binder: BinderId, ty: Type) {
        let provenance = TypeProvenance::unknown(&ty);
        if let Some(displaced) = self.binders.insert(
            binder,
            TypeFact {
                ty,
                provenance,
                quantified: Box::new([]),
            },
        ) {
            discard_type_fact(displaced);
        }
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
    ) -> Result<bool, TypeError> {
        let ty = IterativeTypeOwner::new(ty);
        if !provenance.aligns(&ty) {
            return Err(invalid_state());
        }
        let displaced = self.binders.insert(
            binder,
            TypeFact {
                ty: ty.into_inner(),
                provenance,
                quantified: Box::new([]),
            },
        );
        if let Some(displaced) = displaced {
            discard_type_fact(displaced);
            Ok(true)
        } else {
            Ok(false)
        }
    }

    fn remove_and_discard(&mut self, binder: BinderId) -> bool {
        let Some(fact) = self.binders.remove(&binder) else {
            return false;
        };
        discard_type_fact(fact);
        true
    }

    fn fact(&self, binder: BinderId) -> Option<&TypeFact> {
        self.binders.get(&binder)
    }

    fn set_quantified(
        &mut self,
        binder: BinderId,
        quantified: Box<[(TypeVariableId, Kind)]>,
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

impl TypedNode {
    /// Consumes a typed result and dismantles its structural type without
    /// following the host call stack.
    ///
    /// Use this when a potentially deep result is not transferred into a Core
    /// program or a [`crate::driver::Observation`].
    pub fn discard_iteratively(self) {
        discard_typed_node(self);
    }
}

struct ProvenancedTypeOwner(Option<ProvenancedType>);

impl ProvenancedTypeOwner {
    fn new(value: ProvenancedType) -> Self {
        Self(Some(value))
    }

    fn into_inner(mut self) -> ProvenancedType {
        self.0.take().expect("provenanced type transfers once")
    }

    fn replace_type(&mut self, ty: Type) {
        replace_type_iteratively(
            &mut self.0.as_mut().expect("provenanced type remains live").ty,
            ty,
        );
    }

    fn set_provenance(&mut self, provenance: TypeProvenance) {
        self.0
            .as_mut()
            .expect("provenanced type remains live")
            .provenance = provenance;
    }
}

impl Deref for ProvenancedTypeOwner {
    type Target = ProvenancedType;

    fn deref(&self) -> &Self::Target {
        self.0.as_ref().expect("provenanced type remains live")
    }
}

impl Drop for ProvenancedTypeOwner {
    fn drop(&mut self) {
        if let Some(value) = self.0.take() {
            discard_provenanced_type(value);
        }
    }
}

struct TypedNodeOwner(Option<TypedNode>);

fn take_type_iteratively(ty: &mut Type) -> IterativeTypeOwner {
    IterativeTypeOwner::new(std::mem::replace(ty, Type::Unit))
}

impl TypedNodeOwner {
    fn new(value: TypedNode) -> Self {
        Self(Some(value))
    }

    fn into_inner(mut self) -> TypedNode {
        self.0.take().expect("typed node transfers once")
    }

    fn set_node(&mut self, node: NodeId) {
        self.0.as_mut().expect("typed node remains live").node = node;
    }

    fn replace_type(&mut self, ty: Type) {
        replace_type_iteratively(
            &mut self.0.as_mut().expect("typed node remains live").ty,
            ty,
        );
    }

    fn take_type(&mut self) -> IterativeTypeOwner {
        take_type_iteratively(&mut self.0.as_mut().expect("typed node remains live").ty)
    }

    fn set_provenance(&mut self, provenance: TypeProvenance) {
        self.0.as_mut().expect("typed node remains live").provenance = provenance;
    }
}

impl Deref for TypedNodeOwner {
    type Target = TypedNode;

    fn deref(&self) -> &Self::Target {
        self.0.as_ref().expect("typed node remains live")
    }
}

impl Drop for TypedNodeOwner {
    fn drop(&mut self) {
        if let Some(value) = self.0.take() {
            discard_typed_node(value);
        }
    }
}

struct TypeFactOwner(Option<TypeFact>);

impl TypeFactOwner {
    fn new(value: TypeFact) -> Self {
        Self(Some(value))
    }

    fn into_inner(mut self) -> TypeFact {
        self.0.take().expect("type fact transfers once")
    }
}

impl Deref for TypeFactOwner {
    type Target = TypeFact;

    fn deref(&self) -> &Self::Target {
        self.0.as_ref().expect("type fact remains live")
    }
}

impl Drop for TypeFactOwner {
    fn drop(&mut self) {
        if let Some(value) = self.0.take() {
            discard_type_fact(value);
        }
    }
}

struct OriginOwner(Option<Origin>);

impl OriginOwner {
    fn new(origin: Origin) -> Self {
        Self(Some(origin))
    }

    fn into_inner(mut self) -> Origin {
        self.0.take().expect("origin transfers once")
    }
}

impl Drop for OriginOwner {
    fn drop(&mut self) {
        if let Some(origin) = self.0.take() {
            discard_origin_iteratively(origin);
        }
    }
}

struct CheckedTypeVariableBuffer(Vec<crate::resolved::ResolvedTypeVariable>);

impl CheckedTypeVariableBuffer {
    fn try_reserve(&mut self, additional: usize) -> Result<(), std::collections::TryReserveError> {
        self.0.try_reserve(additional)
    }

    fn push(&mut self, parameter: crate::resolved::ResolvedTypeVariable) {
        self.0.push(parameter);
    }

    #[cfg(test)]
    fn len(&self) -> usize {
        self.0.len()
    }

    fn into_boxed_slice(mut self) -> Box<[crate::resolved::ResolvedTypeVariable]> {
        std::mem::take(&mut self.0).into_boxed_slice()
    }
}

impl Drop for CheckedTypeVariableBuffer {
    fn drop(&mut self) {
        while let Some(parameter) = self.0.pop() {
            let crate::resolved::ResolvedTypeVariable { origin, .. } = parameter;
            discard_origin_iteratively(origin);
        }
    }
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

impl TypeReplacementBuffer {
    fn new() -> Self {
        Self(HashMap::new())
    }

    fn as_map(&self) -> &HashMap<TypeVariableId, Type> {
        &self.0
    }

    fn try_reserve(&mut self, additional: usize) -> Result<(), std::collections::TryReserveError> {
        self.0.try_reserve(additional)
    }

    fn try_insert_unique(&mut self, parameter: TypeVariableId, ty: Type) -> Result<(), ()> {
        if let Some(displaced) = self.0.insert(parameter, ty) {
            discard_type_iteratively(displaced);
            Err(())
        } else {
            Ok(())
        }
    }
}

impl Drop for TypeReplacementBuffer {
    fn drop(&mut self) {
        for (_, ty) in self.0.drain() {
            discard_type_iteratively(ty);
        }
    }
}

fn substitute_fresh_type_variables_in_order(
    ty: &Type,
    replacements: &[(TypeVariableId, TypeVariableId)],
    type_work: &mut TypeWorkBudget,
) -> Result<Type, ()> {
    if replacements.is_empty() {
        return clone_type_with_budget(ty, type_work);
    }
    let mut current: Option<IterativeTypeOwner> = None;
    for (source, fresh) in replacements {
        let mut replacement = TypeReplacementBuffer::new();
        replacement.try_reserve(1).map_err(|_| ())?;
        replacement.try_insert_unique(*source, Type::Variable(*fresh))?;
        let input = current.as_deref().unwrap_or(ty);
        let renamed = substitute_type_variables_with(input, replacement.as_map(), |cells| {
            type_work.charge(cells)
        })?;
        match current.as_mut() {
            Some(current) => current.replace(renamed),
            None => current = Some(IterativeTypeOwner::new(renamed)),
        }
    }
    Ok(current.expect("non-empty fresh substitutions").into_inner())
}

#[derive(Debug, Default, Eq, PartialEq)]
struct InferenceSolutionMap(HashMap<InferenceVariableId, Type>);

impl Deref for InferenceSolutionMap {
    type Target = HashMap<InferenceVariableId, Type>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl InferenceSolutionMap {
    fn try_reserve(&mut self, additional: usize) -> Result<(), std::collections::TryReserveError> {
        self.0.try_reserve(additional)
    }

    fn insert_unique(&mut self, variable: InferenceVariableId, ty: Type) -> Result<(), Type> {
        match self.0.entry(variable) {
            std::collections::hash_map::Entry::Vacant(entry) => {
                entry.insert(ty);
                Ok(())
            }
            std::collections::hash_map::Entry::Occupied(_) => Err(ty),
        }
    }

    fn remove_and_discard(&mut self, variable: InferenceVariableId) {
        if let Some((_, solution)) = self.0.remove_entry(&variable) {
            discard_type_iteratively(solution);
        }
    }
}

impl PartialEq<HashMap<InferenceVariableId, Type>> for InferenceSolutionMap {
    fn eq(&self, other: &HashMap<InferenceVariableId, Type>) -> bool {
        self.0 == *other
    }
}

impl Drop for InferenceSolutionMap {
    fn drop(&mut self) {
        for (_, ty) in self.0.drain() {
            discard_type_iteratively(ty);
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum InferenceRegistryFailure {
    Missing,
    Duplicate,
    Conflict,
    Resource,
}

#[derive(Debug)]
struct InferenceVariableFact {
    origin: Span,
    kind: Kind,
}

#[derive(Debug, Default)]
struct InferenceVariableRegistry(Vec<InferenceVariableFact>);

impl InferenceVariableRegistry {
    fn len(&self) -> usize {
        self.0.len()
    }

    #[cfg(test)]
    fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    fn truncate(&mut self, len: usize) {
        self.0.truncate(len);
    }

    fn insert(
        &mut self,
        identity: InferenceVariableId,
        kind: &Kind,
        origin: Span,
        budget: &mut TypeWorkBudget,
    ) -> Result<(), InferenceRegistryFailure> {
        budget
            // The first unit authenticates the source-order Omega index.
            .charge(1)
            .map_err(|()| InferenceRegistryFailure::Resource)?;
        let index =
            usize::try_from(identity.value()).map_err(|_| InferenceRegistryFailure::Missing)?;
        if let Some(existing) = self.0.get(index) {
            let equal = same_kind_with_budget(&existing.kind, kind, budget)
                .map_err(|()| InferenceRegistryFailure::Resource)?;
            return Err(if equal {
                InferenceRegistryFailure::Duplicate
            } else {
                InferenceRegistryFailure::Conflict
            });
        }
        if index != self.0.len() {
            return Err(InferenceRegistryFailure::Missing);
        }
        budget
            // Retaining a fresh fact also preserves the predecessor causal
            // origin beside the canonical fixed-kind record.
            .charge(1)
            .map_err(|()| InferenceRegistryFailure::Resource)?;
        self.0
            .try_reserve(1)
            .map_err(|_| InferenceRegistryFailure::Resource)?;
        let kind = clone_kind_with_budget(kind, budget)
            .map_err(|()| InferenceRegistryFailure::Resource)?;
        self.0.push(InferenceVariableFact { origin, kind });
        Ok(())
    }

    fn fact(
        &self,
        identity: InferenceVariableId,
        budget: &mut TypeWorkBudget,
    ) -> Result<&InferenceVariableFact, InferenceRegistryFailure> {
        budget
            .charge(1)
            .map_err(|()| InferenceRegistryFailure::Resource)?;
        let index =
            usize::try_from(identity.value()).map_err(|_| InferenceRegistryFailure::Missing)?;
        self.0.get(index).ok_or(InferenceRegistryFailure::Missing)
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum GeneratedTypeVariableRegistryFailure {
    Missing,
    Duplicate,
    Conflict,
    Resource,
}

#[derive(Debug)]
struct GeneratedTypeVariableFact {
    origin: Span,
    kind: Kind,
}

/// Fixed kinds for compiler-generated abstraction binders, retained in their
/// allocation order. Generated identities count down from `u32::MAX`, so the
/// inverse offset is a stable, constant-time source-order index.
#[derive(Debug, Default)]
struct GeneratedTypeVariableRegistry(Vec<GeneratedTypeVariableFact>);

impl GeneratedTypeVariableRegistry {
    fn len(&self) -> usize {
        self.0.len()
    }

    fn truncate(&mut self, len: usize) {
        self.0.truncate(len);
    }

    fn insert(
        &mut self,
        identity: TypeVariableId,
        kind: &Kind,
        origin: Span,
        budget: &mut TypeWorkBudget,
    ) -> Result<(), GeneratedTypeVariableRegistryFailure> {
        budget
            .charge(1)
            .map_err(|()| GeneratedTypeVariableRegistryFailure::Resource)?;
        let TypeVariableId::Generated(local) = identity else {
            return Err(GeneratedTypeVariableRegistryFailure::Missing);
        };
        let index = usize::try_from(u32::MAX - local)
            .map_err(|_| GeneratedTypeVariableRegistryFailure::Missing)?;
        if let Some(existing) = self.0.get(index) {
            let equal = same_kind_with_budget(&existing.kind, kind, budget)
                .map_err(|()| GeneratedTypeVariableRegistryFailure::Resource)?;
            return Err(if equal {
                GeneratedTypeVariableRegistryFailure::Duplicate
            } else {
                GeneratedTypeVariableRegistryFailure::Conflict
            });
        }
        if index != self.0.len() {
            return Err(GeneratedTypeVariableRegistryFailure::Missing);
        }
        budget
            .charge(1)
            .map_err(|()| GeneratedTypeVariableRegistryFailure::Resource)?;
        self.0
            .try_reserve(1)
            .map_err(|_| GeneratedTypeVariableRegistryFailure::Resource)?;
        let kind = clone_kind_with_budget(kind, budget)
            .map_err(|()| GeneratedTypeVariableRegistryFailure::Resource)?;
        self.0.push(GeneratedTypeVariableFact { origin, kind });
        Ok(())
    }

    fn fact(
        &self,
        identity: TypeVariableId,
        budget: &mut TypeWorkBudget,
    ) -> Result<&GeneratedTypeVariableFact, GeneratedTypeVariableRegistryFailure> {
        budget
            .charge(1)
            .map_err(|()| GeneratedTypeVariableRegistryFailure::Resource)?;
        let TypeVariableId::Generated(local) = identity else {
            return Err(GeneratedTypeVariableRegistryFailure::Missing);
        };
        let index = usize::try_from(u32::MAX - local)
            .map_err(|_| GeneratedTypeVariableRegistryFailure::Missing)?;
        self.0
            .get(index)
            .ok_or(GeneratedTypeVariableRegistryFailure::Missing)
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
    inference_variables: InferenceVariableRegistry,
    next_generated_type_variable: u32,
    generated_type_variables: GeneratedTypeVariableRegistry,
    inference_solutions: InferenceSolutionMap,
    authenticated_inference_solutions: HashSet<InferenceVariableId>,
    monomorphic_recursive: HashSet<BinderId>,
    current_implementation_method: Option<CurrentImplementationMethod>,
    method_binders: HashMap<MethodId, BinderId>,
    selection: Option<EvidenceSelector>,
    evidence_lowering: Option<EvidenceLowering>,
    type_work: TypeWorkBudget,
    constraint_work: InterfaceConstraintBudget,
    coverage_work: UsefulnessBudget,
    base_context: TypeContext,
}

#[derive(Debug)]
struct CurrentImplementationMethod {
    method: MethodId,
    method_arguments: Box<[Type]>,
}

impl Drop for CurrentImplementationMethod {
    fn drop(&mut self) {
        for argument in std::mem::take(&mut self.method_arguments).into_vec() {
            discard_type_iteratively(argument);
        }
    }
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
            inference_variables: InferenceVariableRegistry::default(),
            next_generated_type_variable: u32::MAX,
            generated_type_variables: GeneratedTypeVariableRegistry::default(),
            inference_solutions: InferenceSolutionMap::default(),
            authenticated_inference_solutions: HashSet::new(),
            monomorphic_recursive: HashSet::new(),
            current_implementation_method: None,
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

    #[cfg(test)]
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
        Self::for_module_with_registry(module, registry, type_work, coverage_work)
    }

    fn for_module_with_registry(
        module: &ResolvedModule,
        registry: Arc<ResolvedRegistry>,
        mut type_work: TypeWorkBudget,
        coverage_work: UsefulnessBudget,
    ) -> Result<Self, TypeError> {
        let mut builder = CoreBuilder::with_registry(Arc::clone(&registry));
        builder
            .reserve_resolved_binders(resolved_module_binders(module))
            .map_err(TypeError::from)?;
        let mut base_context = TypeContext::new();
        for imported in module.imported_facts().globals() {
            let quantified = clone_kinded_type_parameters_with_budget(
                &imported.scheme.type_parameters,
                &mut type_work,
            )
            .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?
            .into_boxed_slice();
            let body = IterativeTypeOwner::new(
                clone_type_with_budget(&imported.scheme.value_type, &mut type_work)
                    .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?,
            );
            let provenance = at_span_provenance_with_budget(
                &body,
                imported.origin.primary_span(),
                &mut type_work,
            )
            .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
            if base_context.insert_with_provenance(
                imported.binder,
                body.into_inner(),
                provenance,
            )? {
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
            inference_variables: InferenceVariableRegistry::default(),
            next_generated_type_variable: u32::MAX,
            generated_type_variables: GeneratedTypeVariableRegistry::default(),
            inference_solutions: InferenceSolutionMap::default(),
            authenticated_inference_solutions: HashSet::new(),
            monomorphic_recursive: HashSet::new(),
            current_implementation_method: None,
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
        let mut builder = CoreBuilder::with_registry_and_method_evidence(
            Arc::clone(&registry),
            Arc::clone(program.method_evidence()),
        )?;
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
            inference_variables: InferenceVariableRegistry::default(),
            next_generated_type_variable: u32::MAX,
            generated_type_variables: GeneratedTypeVariableRegistry::default(),
            inference_solutions: InferenceSolutionMap::default(),
            authenticated_inference_solutions: HashSet::new(),
            monomorphic_recursive: HashSet::new(),
            current_implementation_method: None,
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
                self.type_work
                    .charge(interface.methods.len())
                    .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
                methods
                    .try_reserve(interface.methods.len())
                    .map_err(|_| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
                for method in &interface.methods {
                    methods.push(method.id);
                    let mut type_parameters = Vec::new();
                    self.type_work
                        .charge(method.authoritative_type_parameters().len())
                        .map_err(|()| {
                            TypeError::Internal(ElaborationFailure::TypeResourceExhausted)
                        })?;
                    type_parameters
                        .try_reserve(method.authoritative_type_parameters().len())
                        .map_err(|_| {
                            TypeError::Internal(ElaborationFailure::TypeResourceExhausted)
                        })?;
                    for parameter in method.authoritative_type_parameters() {
                        type_parameters.push((
                            parameter.id,
                            clone_kind_with_budget(&parameter.kind, &mut self.type_work).map_err(
                                |()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted),
                            )?,
                        ));
                    }
                    self.type_work
                        .charge(interface.parameters.len())
                        .map_err(|()| {
                            TypeError::Internal(ElaborationFailure::TypeResourceExhausted)
                        })?;
                    let mut interface_parameters = Vec::new();
                    interface_parameters
                        .try_reserve(interface.parameters.len())
                        .map_err(|_| {
                            TypeError::Internal(ElaborationFailure::TypeResourceExhausted)
                        })?;
                    interface_parameters
                        .extend(interface.parameters.iter().map(|parameter| parameter.id));
                    let lowered = LoweredInterfaceMethod {
                        interface: interface.id,
                        parameters: interface_parameters.into_boxed_slice(),
                        type_parameters: type_parameters.into_boxed_slice(),
                        value_type: self.clone_type(&method.value_type)?,
                        declaration_span: method.span,
                    };
                    if interface_methods.insert(method.id, lowered).is_some() {
                        return Err(invalid_state());
                    }
                }
                let determination = interface
                    .determination()
                    .map(|determination| {
                        self.constraint_work
                            .charge(determination.positions().len())
                            .map_err(|()| constraint_resource())?;
                        let mut positions = Vec::new();
                        positions
                            .try_reserve_exact(determination.positions().len())
                            .map_err(|_| constraint_resource())?;
                        positions.extend_from_slice(determination.positions());
                        Ok::<_, TypeError>(positions.into_boxed_slice())
                    })
                    .transpose()?;
                if interfaces
                    .insert(
                        interface.id,
                        LoweredInterface {
                            methods: methods.into_boxed_slice(),
                            determination,
                        },
                    )
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
                let scheme = self.lower_constrained_scheme(
                    &checked.scheme,
                    &lowering,
                    MethodEvidenceOwner::Global(checked.binder),
                    false,
                    checked.origin.primary_span(),
                )?;
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
                    let scheme = self.lower_constrained_scheme(
                        &method.scheme,
                        &lowering,
                        MethodEvidenceOwner::Implementation(method.id),
                        true,
                        method.span,
                    )?;
                    let lowered = LoweredImplementationMethod {
                        binder: method.binder,
                        head_type_parameter_count: method.head_type_parameter_count(),
                        application: implementation
                            .application()
                            .clone_with_budget(&mut self.type_work)
                            .map_err(|()| {
                                TypeError::Internal(ElaborationFailure::TypeResourceExhausted)
                            })?,
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
        owner: MethodEvidenceOwner,
        freshen_core_parameters: bool,
        origin: Span,
    ) -> Result<LoweredScheme, TypeError> {
        self.type_work
            .charge(scheme.requirements.len())
            .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
        let original_type_parameters = crate::types::clone_kinded_type_parameters_with_budget(
            &scheme.type_parameters,
            &mut self.type_work,
        )
        .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?
        .into_boxed_slice();
        let value_type = IterativeTypeOwner::new(self.clone_type(&scheme.value_type)?);
        let (source_type_parameters, type_parameters) = if freshen_core_parameters {
            let mut type_parameters = Vec::new();
            type_parameters
                .try_reserve(original_type_parameters.len())
                .map_err(|_| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
            for (_, kind) in &original_type_parameters {
                let core = self.fresh_type_variable(kind, origin)?;
                self.type_work
                    .charge(1)
                    .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
                type_parameters.push((
                    core,
                    clone_kind_with_budget(kind, &mut self.type_work).map_err(|()| {
                        TypeError::Internal(ElaborationFailure::TypeResourceExhausted)
                    })?,
                ));
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
            let lowered_interface = lowering
                .interfaces
                .get(&requirement.interface())
                .ok_or_else(invalid_state)?;
            self.type_work
                .charge(lowered_interface.methods.len())
                .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
            let mut methods = Vec::new();
            methods
                .try_reserve(lowered_interface.methods.len())
                .map_err(|_| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
            for method in &lowered_interface.methods {
                let method_fact = lowering
                    .interface_methods
                    .get(method)
                    .ok_or_else(invalid_state)?;
                if method_fact.interface != requirement.interface()
                    || method_fact.parameters.len() != requirement.arguments().len()
                {
                    return Err(invalid_state());
                }
                self.type_work
                    .charge(method_fact.parameters.len())
                    .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
                let mut replacement = TypeReplacementBuffer::new();
                replacement
                    .try_reserve(method_fact.parameters.len())
                    .map_err(|_| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
                for (parameter, argument) in
                    method_fact.parameters.iter().zip(requirement.arguments())
                {
                    replacement
                        .try_insert_unique(*parameter, self.clone_type(argument)?)
                        .map_err(|()| invalid_state())?;
                }
                let ty = IterativeTypeOwner::new(
                    substitute_type_variables_with(
                        &method_fact.value_type,
                        replacement.as_map(),
                        |cells| self.type_work.charge(cells),
                    )
                    .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?,
                );
                let ty = if method_fact.type_parameters.is_empty() {
                    ty.into_inner()
                } else {
                    self.type_work.charge(1).map_err(|()| {
                        TypeError::Internal(ElaborationFailure::TypeResourceExhausted)
                    })?;
                    let parameters = clone_kinded_type_parameters_with_budget(
                        &method_fact.type_parameters,
                        &mut self.type_work,
                    )
                    .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
                    Type::Forall(parameters.into_boxed_slice(), Box::new(ty.into_inner()))
                };
                methods.push(LoweredRequirementMethod {
                    method: *method,
                    application: requirement
                        .application()
                        .clone_with_budget(&mut self.type_work)
                        .map_err(|()| {
                            TypeError::Internal(ElaborationFailure::TypeResourceExhausted)
                        })?,
                    ty,
                });
            }
            requirements.push(LoweredRequirement {
                owner,
                id: requirement.id,
                methods: methods.into_boxed_slice(),
            });
        }

        let mut core_body = IterativeTypeOwner::new(self.clone_type(&value_type)?);
        for requirement in requirements.iter().rev() {
            for method in requirement.methods.iter().rev() {
                self.type_work
                    .charge(1)
                    .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
                let domain = self.clone_type(&method.ty)?;
                core_body = IterativeTypeOwner::new(Type::Function(
                    Box::new(domain),
                    Box::new(core_body.into_inner()),
                ));
            }
        }
        if let Some(source_parameters) = source_type_parameters.as_deref() {
            if source_parameters.len() != type_parameters.len() {
                return Err(invalid_state());
            }
            let mut ordered_replacements = Vec::new();
            ordered_replacements
                .try_reserve_exact(source_parameters.len())
                .map_err(|_| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
            self.type_work
                .charge(
                    source_parameters
                        .len()
                        .checked_mul(2)
                        .ok_or_else(invalid_state)?,
                )
                .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
            ordered_replacements.extend(
                source_parameters
                    .iter()
                    .zip(&type_parameters)
                    .map(|((source, _), (fresh, _))| (*source, *fresh)),
            );
            let renamed = substitute_fresh_type_variables_in_order(
                &core_body,
                &ordered_replacements,
                &mut self.type_work,
            )
            .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
            core_body.replace(renamed);
        }
        let core_scheme = if type_parameters.is_empty() {
            core_body.into_inner()
        } else {
            self.type_work
                .charge(1)
                .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
            let parameters =
                clone_kinded_type_parameters_with_budget(&type_parameters, &mut self.type_work)
                    .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
            Type::Forall(
                parameters.into_boxed_slice(),
                Box::new(core_body.into_inner()),
            )
        };
        Ok(LoweredScheme {
            source_type_parameters,
            type_parameters,
            requirements: requirements.into_boxed_slice(),
            value_type: value_type.into_inner(),
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
            inference_variables: InferenceVariableRegistry::default(),
            next_generated_type_variable: u32::MAX,
            generated_type_variables: GeneratedTypeVariableRegistry::default(),
            inference_solutions: InferenceSolutionMap::default(),
            authenticated_inference_solutions: HashSet::new(),
            monomorphic_recursive: HashSet::new(),
            current_implementation_method: None,
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
    ) -> Result<(Box<[CheckedImplementationFact]>, PendingEvidencePublication), TypeError> {
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
    ) -> Result<(Box<[CheckedImplementationFact]>, PendingEvidencePublication), TypeError> {
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
        let publication = self.prepare_evidence_publication()?;
        Ok((facts.into_boxed_slice(), publication))
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
        if implementation.id != checked.id
            || implementation.head.interface.id != checked.interface()
            || implementation.head.arguments.len() != checked.arguments().len()
        {
            return Err(invalid_state());
        }
        for (resolved_argument, checked_argument) in implementation
            .head
            .arguments
            .iter()
            .zip(checked.arguments())
        {
            if !same_type(&resolved_argument.ty, checked_argument) {
                return Err(invalid_state());
            }
        }
        let interface = checked_interface(
            module,
            checked_interfaces,
            checked.interface(),
            &mut self.constraint_work,
        )?
        .ok_or_else(invalid_state)?;

        if interface.parameters().len() != implementation.head.arguments.len() {
            return Err(invalid_state());
        }
        self.type_work
            .charge(interface.parameters().len())
            .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
        let mut replacements = TypeReplacementBuffer::new();
        replacements
            .try_reserve(interface.parameters().len())
            .map_err(|_| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
        for (parameter, argument) in interface
            .parameters()
            .iter()
            .zip(&implementation.head.arguments)
        {
            replacements
                .try_insert_unique(parameter.id, self.clone_type(&argument.ty)?)
                .map_err(|()| invalid_state())?;
        }

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
            let method_type = IterativeTypeOwner::new(substitute_type_variables_with(
                method.value_type(),
                replacements.as_map(),
                |cells| {
                    self.constraint_work
                        .charge(cells)
                        .map_err(|()| constraint_resource())?;
                    self.type_work.charge(cells).map_err(|()| {
                        TypeError::Internal(ElaborationFailure::TypeResourceExhausted)
                    })
                },
            )?);
            let provenance = self.at_span_provenance(&method_type, method.annotation_span())?;
            let presentation = implementation_method_origin(
                implementation,
                group,
                method.span(),
                method.annotation_span(),
            );
            if self.current_implementation_method.is_some() {
                return Err(invalid_state());
            }
            let current_method_work = method
                .type_parameters()
                .len()
                .checked_add(1)
                .ok_or_else(|| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
            self.type_work
                .charge(current_method_work)
                .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
            let mut rigid_method_arguments = Vec::new();
            rigid_method_arguments
                .try_reserve(method.type_parameters().len())
                .map_err(|_| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
            rigid_method_arguments.extend(
                method
                    .type_parameters()
                    .iter()
                    .map(|parameter| Type::Variable(parameter.id)),
            );
            let current_method = CurrentImplementationMethod {
                method: method.id(),
                method_arguments: rigid_method_arguments.into_boxed_slice(),
            };
            let evidence_marker = self.enter_implementation_evidence_scope(implementation.id)?;
            self.current_implementation_method = Some(current_method);
            let body_result = self.elaborate_equations(
                &group.equations,
                ProvenancedType {
                    ty: method_type.into_inner(),
                    provenance,
                },
                context,
                group.span,
                &presentation,
            );
            let current_method = self
                .current_implementation_method
                .take()
                .ok_or_else(invalid_state)?;
            if current_method.method != method.id() {
                return Err(invalid_state());
            }
            drop(current_method);
            let checked_body = match body_result {
                Ok(body) => {
                    self.close_evidence_obligations(evidence_marker)?;
                    self.leave_evidence_scope()?;
                    TypedNodeOwner::new(body)
                }
                Err(body_error) => {
                    let failure_span = match &body_error {
                        TypeError::Source(diagnostic) => Some(diagnostic.primary.span()),
                        TypeError::Interface(diagnostic) => Some(diagnostic.primary.span()),
                        TypeError::Mismatch(mismatch) => Some(mismatch.span),
                        TypeError::Internal(_) => None,
                    };
                    if let Some(failure_span) = failure_span {
                        match self
                            .close_method_rigidity_for_failed_body(evidence_marker, failure_span)
                        {
                            Ok(_) => {}
                            Err(close_error)
                                if is_polymorphic_recursion_error(&close_error)
                                    || matches!(close_error, TypeError::Internal(_)) =>
                            {
                                return Err(close_error);
                            }
                            Err(_) => {}
                        }
                    }
                    return Err(body_error);
                }
            };
            let scheme = self.checked_implementation_method_scheme(
                implementation,
                method.type_parameters(),
                &checked_body.ty,
            )?;
            method_facts.push(CheckedImplementationMethodFact {
                id: checked_method.id,
                method: checked_method.method,
                binder: checked_method.binder,
                scheme,
                head_type_parameter_count: implementation.head_parameters.len(),
                origin: presentation,
                span: group.span,
            });
        }

        let mut head_parameters = Vec::new();
        head_parameters
            .try_reserve(implementation.head_parameters.len())
            .map_err(|_| constraint_resource())?;
        for parameter in &implementation.head_parameters {
            head_parameters.push(
                clone_resolved_type_variable_with_budget(parameter, &mut self.type_work)
                    .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?,
            );
        }
        let prerequisites =
            self.clone_implementation_requirements(&implementation.prerequisites)?;
        Ok(CheckedImplementationFact {
            id: implementation.id,
            application: self.clone_resolved_interface_application(&implementation.head)?,
            head_parameters: head_parameters.into_boxed_slice(),
            prerequisites,
            methods: method_facts.into_boxed_slice(),
            origin: Origin::Source(implementation.span),
            span: implementation.span,
        })
    }

    fn checked_implementation_method_scheme(
        &mut self,
        implementation: &crate::resolved::ResolvedImplementation,
        method_parameters: &[crate::resolved::ResolvedTypeVariable],
        value_type: &Type,
    ) -> Result<ConstrainedScheme, TypeError> {
        let parameter_count = implementation
            .head_parameters
            .len()
            .checked_add(method_parameters.len())
            .ok_or_else(|| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
        let retained_work = parameter_count
            .checked_add(implementation.prerequisites.len())
            .and_then(|work| work.checked_add(1))
            .ok_or_else(constraint_resource)?;
        self.constraint_work
            .charge(retained_work)
            .map_err(|()| constraint_resource())?;
        self.constraint_work
            .charge_type(value_type)
            .map_err(|()| constraint_resource())?;
        self.type_work
            .charge(parameter_count)
            .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
        let mut type_parameters = Vec::new();
        type_parameters
            .try_reserve(parameter_count)
            .map_err(|_| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
        for parameter in &implementation.head_parameters {
            type_parameters.push((
                parameter.id,
                clone_kind_with_budget(&parameter.kind, &mut self.type_work)
                    .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?,
            ));
        }
        for parameter in method_parameters {
            type_parameters.push((
                parameter.id,
                clone_kind_with_budget(&parameter.kind, &mut self.type_work)
                    .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?,
            ));
        }
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
            checked.push(CheckedRequirement {
                id: requirement.id,
                application: self.clone_resolved_interface_application(&requirement.application)?,
                origin: Origin::Source(requirement.application.span),
                span: requirement.application.span,
            });
        }
        Ok(checked.into_boxed_slice())
    }

    fn clone_resolved_interface_application(
        &mut self,
        application: &crate::resolved::ResolvedInterfaceApplication,
    ) -> Result<InterfaceApplication, TypeError> {
        self.constraint_work
            .charge(application.arguments.len())
            .map_err(|()| constraint_resource())?;
        let mut arguments = OwnedTypeBuffer(Vec::new());
        arguments
            .try_reserve(application.arguments.len())
            .map_err(|_| constraint_resource())?;
        for argument in &application.arguments {
            self.constraint_work
                .charge_type(&argument.ty)
                .map_err(|()| constraint_resource())?;
            arguments.push(self.clone_type(&argument.ty)?);
        }
        Ok(InterfaceApplication::new(
            application.interface.id,
            arguments.into_boxed_slice(),
        ))
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
            for parameter in parameters {
                type_parameters.push((
                    parameter.id,
                    clone_kind_with_budget(&parameter.kind, &mut self.type_work).map_err(|()| {
                        TypeError::Internal(ElaborationFailure::TypeResourceExhausted)
                    })?,
                ));
            }
            let mut checked_requirements = Vec::new();
            checked_requirements
                .try_reserve(requirements.len())
                .map_err(|_| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
            for requirement in requirements {
                checked_requirements.push(CheckedRequirement {
                    id: requirement.id,
                    application: self
                        .clone_resolved_interface_application(&requirement.application)?,
                    origin: Origin::Source(requirement.application.span),
                    span: requirement.application.span,
                });
            }
            let body = match &definition.kind {
                ResolvedDefinitionKind::Equational(equational) => {
                    self.clone_type(&equational.interface.annotation.ty)?
                }
                ResolvedDefinitionKind::InlineOperational(operational) => {
                    let domain = ProvenancedTypeOwner::new(operational_domain(
                        &operational.header.parameters,
                        operational.header.span,
                        &mut self.type_work,
                    )?);
                    let codomain =
                        ProvenancedTypeOwner::new(ProvenancedType::from_resolved_with_budget(
                            &operational.header.result_type,
                            &mut self.type_work,
                        )?);
                    let function = ProvenancedType::function_with_budget(
                        domain.into_inner(),
                        codomain.into_inner(),
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
            let inference_variables = &self.inference_variables;
            let authenticated_solutions = &self.authenticated_inference_solutions;
            let type_work = &mut self.type_work;
            self.builder.rewrite_types(|ty| {
                let (zonked, unresolved) =
                    zonk_type_with_status_and_inference(ty, solutions, |work| match work {
                        ZonkWork::TypeCells(cells) => type_work
                            .charge(cells)
                            .map_err(|()| BuildError::TypeWorkExceeded),
                        ZonkWork::Inference(identity) => authenticate_zonk_inference_occurrence(
                            identity,
                            inference_variables,
                            solutions,
                            authenticated_solutions,
                            type_work,
                        )
                        .map_err(|failure| match failure {
                            UnificationFailure::Resource => BuildError::TypeWorkExceeded,
                            UnificationFailure::Mismatch
                            | UnificationFailure::Infinite
                            | UnificationFailure::Invariant => BuildError::InvalidPayload,
                        }),
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

    fn fresh_inference(&mut self, kind: &Kind, origin: Span) -> Result<Type, TypeError> {
        self.fresh_inference_reserved(kind, origin)
    }

    fn fresh_inference_reserved(&mut self, kind: &Kind, origin: Span) -> Result<Type, TypeError> {
        allocate_inference_variable(
            &mut self.next_inference,
            &mut self.inference_variables,
            &mut self.type_work,
            kind,
            origin,
        )
    }

    fn fresh_type_variable(
        &mut self,
        kind: &Kind,
        origin: Span,
    ) -> Result<TypeVariableId, TypeError> {
        let identity = TypeVariableId::generated(self.next_generated_type_variable);
        let next = self
            .next_generated_type_variable
            .checked_sub(1)
            .ok_or_else(invalid_state)?;
        self.generated_type_variables
            .insert(identity, kind, origin, &mut self.type_work)
            .map_err(generated_type_variable_registry_error)?;
        self.next_generated_type_variable = next;
        Ok(identity)
    }

    fn generalize_inference_variables(
        &mut self,
        variables: &[InferenceVariableId],
        initializer: &Type,
    ) -> Result<(Vec<(TypeVariableId, Kind)>, Type), TypeError> {
        self.type_work
            .charge(variables.len().saturating_mul(3))
            .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
        let mut generalized = Vec::new();
        generalized
            .try_reserve(variables.len())
            .map_err(|_| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
        self.inference_solutions
            .try_reserve(variables.len())
            .map_err(|_| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
        self.authenticated_inference_solutions
            .try_reserve(variables.len())
            .map_err(|_| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
        let generated_marker = self.generated_type_variables.len();
        let next_generated_type_variable = self.next_generated_type_variable;
        let result = (|| {
            for variable in variables {
                let fact = self
                    .inference_variables
                    .fact(*variable, &mut self.type_work)
                    .map_err(inference_registry_error)?;
                let kind = clone_kind_with_budget(&fact.kind, &mut self.type_work)
                    .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
                let origin = fact.origin;
                let binder = self.fresh_type_variable(&kind, origin)?;
                if let Err(replacement) = self
                    .inference_solutions
                    .insert_unique(*variable, Type::Variable(binder))
                {
                    discard_type_iteratively(replacement);
                    return Err(invalid_state());
                }
                if !self.authenticated_inference_solutions.insert(*variable) {
                    self.inference_solutions.remove_and_discard(*variable);
                    return Err(invalid_state());
                }
                generalized.push((binder, kind));
            }
            self.zonk(initializer)
        })();
        match result {
            Ok(zonked) => Ok((generalized, zonked)),
            Err(error) => {
                for variable in variables.iter().take(generalized.len()) {
                    self.inference_solutions.remove_and_discard(*variable);
                    self.authenticated_inference_solutions.remove(variable);
                }
                self.generated_type_variables.truncate(generated_marker);
                self.next_generated_type_variable = next_generated_type_variable;
                Err(error)
            }
        }
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
            .charge(count.saturating_mul(2))
            .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
        let mut replacements = HashMap::new();
        replacements
            .try_reserve(count)
            .map_err(|_| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
        let mut arguments = Vec::new();
        arguments
            .try_reserve(count)
            .map_err(|_| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
        let inference_marker = self.inference_variables.len();
        let next_inference = self.next_inference;
        let result = (|| {
            for (binder, kind) in &fact.quantified {
                let argument = if rigid {
                    Type::Variable(*binder)
                } else {
                    self.fresh_inference_reserved(kind, origin)?
                };
                replacements.insert(*binder, argument.clone());
                arguments.push(argument);
            }
            let instantiated = substitute_type_variables_with(&fact.ty, &replacements, |cells| {
                self.type_work.charge(cells)
            })
            .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
            Ok((instantiated, arguments))
        })();
        if result.is_err() && !rigid {
            self.inference_variables.truncate(inference_marker);
            self.next_inference = next_inference;
        }
        result
    }

    fn enter_global_evidence_scope(
        &mut self,
        binder: BinderId,
    ) -> Result<PendingObligationMarker, TypeError> {
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
    ) -> Result<PendingObligationMarker, TypeError> {
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

    fn evidence_marker(&self) -> Result<PendingObligationMarker, TypeError> {
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
        let selector = self.selection.as_mut().ok_or_else(invalid_state)?;
        if selector.method_rigidity_count() != 0 {
            return Err(invalid_state());
        }
        selector.clear_scope();
        Ok(())
    }

    fn close_evidence_obligations(
        &mut self,
        marker: PendingObligationMarker,
    ) -> Result<(), TypeError> {
        if self.purpose != ElaborationPurpose::ModuleCheck {
            return Err(invalid_state());
        }
        let mut selector = self.selection.take().ok_or_else(invalid_state)?;
        let mut snapshot = {
            let solutions = &self.inference_solutions;
            let inference_variables = &self.inference_variables;
            let authenticated_solutions = &self.authenticated_inference_solutions;
            selector
                .prepare_determination_snapshot(
                    &self.registry,
                    marker,
                    |argument, type_work| {
                        let zonked =
                            zonk_type_with_status_and_inference(&argument, solutions, |work| {
                                match work {
                                    ZonkWork::TypeCells(cells) => type_work
                                        .charge(cells)
                                        .map_err(|()| SelectionFailure::TypeResource),
                                    ZonkWork::Inference(identity) => {
                                        authenticate_zonk_inference_occurrence(
                                            identity,
                                            inference_variables,
                                            solutions,
                                            authenticated_solutions,
                                            type_work,
                                        )
                                        .map_err(
                                            |failure| match failure {
                                                UnificationFailure::Resource => {
                                                    SelectionFailure::TypeResource
                                                }
                                                UnificationFailure::Mismatch
                                                | UnificationFailure::Infinite
                                                | UnificationFailure::Invariant => {
                                                    SelectionFailure::InvalidState
                                                }
                                            },
                                        )
                                    }
                                }
                            });
                        discard_type_iteratively(argument);
                        zonked.map(|(ty, _)| ty)
                    },
                    &mut self.constraint_work,
                    &mut self.type_work,
                )
                .map_err(|failure| selection_failure(failure, None))?
        };
        if let Err(error) = self.apply_improvement_tasks(snapshot.take_tasks()) {
            self.selection = Some(selector);
            return Err(error);
        }
        let solutions = &self.inference_solutions;
        let inference_variables = &self.inference_variables;
        let authenticated_solutions = &self.authenticated_inference_solutions;
        let result = selector.close_with_snapshot_and_registry(
            &self.registry,
            marker,
            &snapshot,
            |argument, type_work| {
                let zonked =
                    zonk_type_with_status_and_inference(&argument, solutions, |work| match work {
                        ZonkWork::TypeCells(cells) => type_work
                            .charge(cells)
                            .map_err(|()| SelectionFailure::TypeResource),
                        ZonkWork::Inference(identity) => authenticate_zonk_inference_occurrence(
                            identity,
                            inference_variables,
                            solutions,
                            authenticated_solutions,
                            type_work,
                        )
                        .map_err(|failure| match failure {
                            UnificationFailure::Resource => SelectionFailure::TypeResource,
                            UnificationFailure::Mismatch
                            | UnificationFailure::Infinite
                            | UnificationFailure::Invariant => SelectionFailure::InvalidState,
                        }),
                    });
                discard_type_iteratively(argument);
                zonked.map(|(ty, _)| ty)
            },
            &mut self.constraint_work,
            &mut self.type_work,
        );
        if let Err(error) = result {
            self.selection = Some(selector);
            return Err(selected_obligation_error(error));
        }
        for index in 0..selector.method_rigidity_count() {
            let check = selector.method_rigidity(index).ok_or_else(invalid_state)?;
            if let Err(error) = self.enforce_selected_method_rigidity(check) {
                self.selection = Some(selector);
                return Err(error);
            }
        }
        selector.clear_method_rigidities();
        self.selection = Some(selector);
        Ok(())
    }

    fn apply_improvement_tasks(
        &mut self,
        tasks: impl IntoIterator<Item = ImprovementTask>,
    ) -> Result<(), TypeError> {
        for task in tasks {
            let (key, expected, actual, obligation_span, source_span) = task.into_parts();
            let key = IterativeTypeOwner::new(Type::Tuple(key));
            let expected = IterativeTypeOwner::new(Type::Tuple(expected));
            let actual = IterativeTypeOwner::new(Type::Tuple(actual));
            match self.unify(&expected, &actual) {
                Ok(()) => {}
                Err(UnificationFailure::Resource) => {
                    return Err(TypeError::Internal(
                        ElaborationFailure::TypeResourceExhausted,
                    ));
                }
                Err(UnificationFailure::Invariant) => return Err(invalid_state()),
                Err(UnificationFailure::Mismatch | UnificationFailure::Infinite) => {
                    let key = IterativeTypeOwner::new(self.zonk(&key)?);
                    let expected = IterativeTypeOwner::new(self.zonk(&expected)?);
                    let actual = IterativeTypeOwner::new(self.zonk(&actual)?);
                    self.constraint_work
                        .charge(3)
                        .map_err(|()| constraint_resource())?;
                    let mut diagnostic = Diagnostic::new(
                        InterfaceReason::DeterminationConflict,
                        SourceLabel::new(
                            obligation_span,
                            "this dependent tuple conflicts with the tuple determined by the known key",
                        ),
                    );
                    retain_interface_label(
                        &mut diagnostic,
                        source_span,
                        "this source determines the expected dependent tuple",
                        &mut self.constraint_work,
                    )?;
                    diagnostic.expected = Some(self.registry.display_source_type(&expected));
                    diagnostic.found = Some(self.registry.display_source_type(&actual));
                    diagnostic.help = Some(format!(
                        "the known determinant key is {}",
                        self.registry.display_source_type(&key)
                    ));
                    return Err(TypeError::Interface(Box::new(diagnostic)));
                }
            }
        }
        Ok(())
    }

    fn close_method_rigidity_for_failed_body(
        &mut self,
        marker: PendingObligationMarker,
        failure_span: Span,
    ) -> Result<bool, TypeError> {
        if self.purpose != ElaborationPurpose::ModuleCheck {
            return Err(invalid_state());
        }
        let mut selector = self.selection.take().ok_or_else(invalid_state)?;
        let mut snapshot = {
            let solutions = &self.inference_solutions;
            let inference_variables = &self.inference_variables;
            let authenticated_solutions = &self.authenticated_inference_solutions;
            selector
                .prepare_method_rigidity_determination(
                    &self.registry,
                    MethodRigidityTarget::new(marker, failure_span),
                    |argument, type_work| {
                        let zonked =
                            zonk_type_with_status_and_inference(&argument, solutions, |work| {
                                match work {
                                    ZonkWork::TypeCells(cells) => type_work
                                        .charge(cells)
                                        .map_err(|()| SelectionFailure::TypeResource),
                                    ZonkWork::Inference(identity) => {
                                        authenticate_zonk_inference_occurrence(
                                            identity,
                                            inference_variables,
                                            solutions,
                                            authenticated_solutions,
                                            type_work,
                                        )
                                        .map_err(
                                            |failure| match failure {
                                                UnificationFailure::Resource => {
                                                    SelectionFailure::TypeResource
                                                }
                                                UnificationFailure::Mismatch
                                                | UnificationFailure::Infinite
                                                | UnificationFailure::Invariant => {
                                                    SelectionFailure::InvalidState
                                                }
                                            },
                                        )
                                    }
                                }
                            });
                        discard_type_iteratively(argument);
                        zonked.map(|(ty, _)| ty)
                    },
                    &mut self.constraint_work,
                    &mut self.type_work,
                )
                .map_err(|failure| selection_failure(failure, None))?
        };
        if let Some(task) = snapshot.take_task()
            && let Err(error) = self.apply_improvement_tasks(std::iter::once(task))
        {
            self.selection = Some(selector);
            return Err(error);
        }
        let solutions = &self.inference_solutions;
        let inference_variables = &self.inference_variables;
        let authenticated_solutions = &self.authenticated_inference_solutions;
        let result = selector.close_method_rigidity_with_snapshot_and_registry(
            &self.registry,
            MethodRigidityTarget::new(marker, failure_span),
            &snapshot,
            |argument, type_work| {
                let zonked =
                    zonk_type_with_status_and_inference(&argument, solutions, |work| match work {
                        ZonkWork::TypeCells(cells) => type_work
                            .charge(cells)
                            .map_err(|()| SelectionFailure::TypeResource),
                        ZonkWork::Inference(identity) => authenticate_zonk_inference_occurrence(
                            identity,
                            inference_variables,
                            solutions,
                            authenticated_solutions,
                            type_work,
                        )
                        .map_err(|failure| match failure {
                            UnificationFailure::Resource => SelectionFailure::TypeResource,
                            UnificationFailure::Mismatch
                            | UnificationFailure::Infinite
                            | UnificationFailure::Invariant => SelectionFailure::InvalidState,
                        }),
                    });
                discard_type_iteratively(argument);
                zonked.map(|(ty, _)| ty)
            },
            &mut self.constraint_work,
            &mut self.type_work,
        );
        let found = match result {
            Ok(found) => found,
            Err(error) => {
                self.selection = Some(selector);
                return Err(selected_obligation_error(error));
            }
        };
        for index in 0..selector.method_rigidity_count() {
            let check = selector.method_rigidity(index).ok_or_else(invalid_state)?;
            if let Err(error) = self.enforce_selected_method_rigidity(check) {
                self.selection = Some(selector);
                return Err(error);
            }
        }
        selector.clear_method_rigidities();
        self.selection = Some(selector);
        Ok(found)
    }

    fn enforce_selected_method_rigidity(
        &mut self,
        check: MethodRigidityCheck<'_>,
    ) -> Result<(), TypeError> {
        if check.method_arguments().len() != check.rigid_arguments().len() {
            return Err(invalid_state());
        }
        self.type_work
            .charge(check.method_arguments().len())
            .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
        for (method_argument, rigid_argument) in
            check.method_arguments().iter().zip(check.rigid_arguments())
        {
            match self.unify(method_argument, rigid_argument) {
                Ok(()) => {}
                Err(UnificationFailure::Resource) => {
                    return Err(TypeError::Internal(
                        ElaborationFailure::TypeResourceExhausted,
                    ));
                }
                Err(UnificationFailure::Invariant) => return Err(invalid_state()),
                Err(UnificationFailure::Mismatch | UnificationFailure::Infinite) => {
                    let expected = IterativeTypeOwner::new(self.zonk(rigid_argument)?);
                    let found = IterativeTypeOwner::new(self.zonk(method_argument)?);
                    let site = check.site();
                    let primary = site.argument_span().unwrap_or(site.occurrence_span());
                    let mut diagnostic = Diagnostic::new(
                        TypeReason::PolymorphicRecursion,
                        SourceLabel::new(
                            primary,
                            "this recursive call requires a different type instantiation",
                        ),
                    );
                    if primary != site.occurrence_span() {
                        diagnostic.related.push(SourceLabel::new(
                            site.occurrence_span(),
                            "this recursive function is checked monomorphically",
                        ));
                    }
                    if let Some(application_span) = site.application_span()
                        && application_span != primary
                        && application_span != site.occurrence_span()
                    {
                        diagnostic.related.push(SourceLabel::new(
                            application_span,
                            "this application supplies the recursive argument",
                        ));
                    }
                    diagnostic.expected = Some(self.registry.display_source_type(&expected));
                    diagnostic.found = Some(self.registry.display_source_type(&found));
                    return Err(TypeError::Source(Box::new(diagnostic)));
                }
            }
        }
        Ok(())
    }

    fn prepare_evidence_publication(&mut self) -> Result<PendingEvidencePublication, TypeError> {
        if self.purpose != ElaborationPurpose::ModuleCheck {
            return Err(invalid_state());
        }
        let mut selector = self.selection.take().ok_or_else(invalid_state)?;
        let solutions = &self.inference_solutions;
        let inference_variables = &self.inference_variables;
        let authenticated_solutions = &self.authenticated_inference_solutions;
        let result = selector.prepare_publication(
            |argument, type_work| {
                let zonked =
                    zonk_type_with_status_and_inference(&argument, solutions, |work| match work {
                        ZonkWork::TypeCells(cells) => type_work
                            .charge(cells)
                            .map_err(|()| SelectionFailure::TypeResource),
                        ZonkWork::Inference(identity) => authenticate_zonk_inference_occurrence(
                            identity,
                            inference_variables,
                            solutions,
                            authenticated_solutions,
                            type_work,
                        )
                        .map_err(|failure| match failure {
                            UnificationFailure::Resource => SelectionFailure::TypeResource,
                            UnificationFailure::Mismatch
                            | UnificationFailure::Infinite
                            | UnificationFailure::Invariant => SelectionFailure::InvalidState,
                        }),
                    });
                discard_type_iteratively(argument);
                zonked.map(|(ty, _)| ty)
            },
            &mut self.constraint_work,
            &mut self.type_work,
        );
        self.selection = Some(selector);
        result.map_err(|failure| selection_failure(failure, None))
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
            let mut replacements = TypeReplacementBuffer::new();
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
                    .try_reserve(scheme.type_parameters.len())
                    .map_err(|_| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
                for ((parameter, _), argument) in scheme.type_parameters.iter().zip(arguments) {
                    if replacements
                        .try_insert_unique(*parameter, self.clone_type(argument)?)
                        .is_err()
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
                let application = {
                    let scheme = selector.scheme(binder).ok_or_else(invalid_state)?;
                    let requirement = scheme.requirements.get(index).ok_or_else(invalid_state)?;
                    self.type_work
                        .charge(requirement.arguments().len())
                        .map_err(|()| {
                            TypeError::Internal(ElaborationFailure::TypeResourceExhausted)
                        })?;
                    let mut application_arguments = OwnedTypeBuffer(Vec::new());
                    application_arguments
                        .try_reserve(requirement.arguments().len())
                        .map_err(|_| {
                            TypeError::Internal(ElaborationFailure::TypeResourceExhausted)
                        })?;
                    for argument in requirement.arguments() {
                        application_arguments.push(
                            substitute_type_variables_with(
                                argument,
                                replacements.as_map(),
                                |cells| self.type_work.charge(cells),
                            )
                            .map_err(|()| {
                                TypeError::Internal(ElaborationFailure::TypeResourceExhausted)
                            })?,
                        );
                    }
                    InterfaceApplication::new(
                        requirement.interface(),
                        application_arguments.into_boxed_slice(),
                    )
                };
                selector
                    .push_owned_obligation(
                        application,
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
        cause: Option<SynthesisCause>,
    ) -> Result<TypedNode, TypeError> {
        if self.purpose != ElaborationPurpose::ModuleCheck || occurrence.evidence.len() != 1 {
            return Err(invalid_state());
        }
        let mut selector = self.selection.take().ok_or_else(invalid_state)?;
        let result = (|| {
            let method_fact = selector.method(method).ok_or_else(invalid_state)?;
            let interface = method_fact.interface();
            let (fact_parameters, scheme_parameters) = retain_method_occurrence_parameters(
                method_fact.interface_parameters(),
                method_fact.type_parameters(),
                &mut self.type_work,
            )
            .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
            let value_type = IterativeTypeOwner::new(self.clone_type(method_fact.value_type())?);
            let method_span = method_fact.declaration_span();
            let fact = TypeFactOwner::new(TypeFact {
                provenance: self.at_span_provenance(&value_type, method_span)?,
                ty: value_type.into_inner(),
                quantified: fact_parameters,
            });
            let (ty, arguments) = self.instantiate(&fact, false, span)?;
            let ty = IterativeTypeOwner::new(ty);
            let arguments = OwnedTypeBuffer(arguments);
            let interface_parameter_count = method_fact.interface_parameters().len();
            if interface_parameter_count == 0 || arguments.len() < interface_parameter_count {
                return Err(invalid_state());
            }
            let (interface_arguments, method_arguments) =
                arguments.as_slice().split_at(interface_parameter_count);
            let mut retained_interface_arguments = OwnedTypeBuffer(Vec::new());
            self.type_work
                .charge(interface_arguments.len())
                .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
            retained_interface_arguments
                .try_reserve(interface_arguments.len())
                .map_err(|_| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
            for argument in interface_arguments {
                retained_interface_arguments.push(self.clone_type(argument)?);
            }
            let application = InterfaceApplication::new(
                interface,
                retained_interface_arguments.into_boxed_slice(),
            );
            let mut retained_method_arguments = Vec::new();
            self.type_work
                .charge(method_arguments.len())
                .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
            retained_method_arguments
                .try_reserve(method_arguments.len())
                .map_err(|_| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
            for method_argument in method_arguments {
                retained_method_arguments.push(self.clone_type(method_argument)?);
            }
            let current_method = self.current_implementation_method.take();
            let method_rigidity = current_method
                .as_ref()
                .filter(|current| current.method == method)
                .map(|current| {
                    self.type_work
                        .charge(current.method_arguments.len())
                        .map_err(|()| {
                            TypeError::Internal(ElaborationFailure::TypeResourceExhausted)
                        })?;
                    let mut rigid_arguments = OwnedTypeBuffer(Vec::new());
                    rigid_arguments
                        .try_reserve(current.method_arguments.len())
                        .map_err(|_| {
                            TypeError::Internal(ElaborationFailure::TypeResourceExhausted)
                        })?;
                    for argument in &current.method_arguments {
                        rigid_arguments.push(
                            clone_type_with_budget(argument, &mut self.type_work).map_err(
                                |()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted),
                            )?,
                        );
                    }
                    let site = match cause {
                        Some(SynthesisCause::Application {
                            whole_span,
                            argument_span,
                        }) => MethodRigiditySite::application(span, whole_span, argument_span),
                        _ => MethodRigiditySite::occurrence(span),
                    };
                    Ok::<MethodRigidityCondition, TypeError>(MethodRigidityCondition::new(
                        rigid_arguments.into_boxed_slice(),
                        site,
                    ))
                })
                .transpose();
            self.current_implementation_method = current_method;
            let method_rigidity = method_rigidity?;
            selector
                .push_cloned_obligation(
                    &application,
                    MethodObligationMetadata::new(
                        method,
                        retained_method_arguments.into_boxed_slice(),
                        method_rigidity,
                    )
                    .with_checked_value_type(self.clone_type(&ty)?),
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

            let core_scheme = IterativeTypeOwner::new(Type::Forall(
                scheme_parameters,
                Box::new(self.clone_type(&fact.ty)?),
            ));
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
            let mut node = self.builder.variable(
                binder,
                core_scheme.into_inner(),
                occurrence.origin.clone(),
            )?;
            let core_ty = self.clone_type(&ty)?;
            node = self.builder.type_application(
                node,
                arguments.into_vec(),
                core_ty,
                occurrence.origin.clone(),
            )?;
            let TypeFact {
                ty: fact_ty,
                provenance,
                quantified: _,
            } = fact.into_inner();
            discard_type_iteratively(fact_ty);
            Ok(TypedNode {
                node,
                ty: ty.into_inner(),
                provenance,
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
        let (checked_method, _, method_arguments, checked_value_type, selection) =
            slot.filled_method().ok_or_else(invalid_state)?;
        if checked_method != method {
            return Err(invalid_state());
        }
        if selection.interface() != method.interface() {
            return Err(invalid_state());
        }
        let mut lowering = self.evidence_lowering.take().ok_or_else(invalid_state)?;
        let result = (|| {
            let method_fact = lowering
                .interface_methods
                .get(&method)
                .ok_or_else(invalid_state)?;
            let declaration_span = method_fact.declaration_span;
            let expected = IterativeTypeOwner::new(self.clone_type(checked_value_type)?);
            let mut methods = self.lower_evidence_selection(
                selection,
                &mut lowering,
                &occurrence.origin,
                Some(method),
                slot.storage_id(),
            )?;
            if methods.len() != 1 {
                return Err(invalid_state());
            }
            let mut selected = methods.pop().ok_or_else(invalid_state)?;
            if selected.method != method {
                return Err(invalid_state());
            }
            if method_arguments.is_empty() {
                if !same_type_with_budget(&selected.ty, &expected, &mut self.type_work)
                    .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?
                {
                    return Err(invalid_state());
                }
            } else {
                let Type::Forall(parameters, _) = &selected.ty else {
                    return Err(invalid_state());
                };
                if parameters.len() != method_arguments.len() {
                    return Err(invalid_state());
                }
                let mut arguments = OwnedTypeBuffer(Vec::new());
                self.type_work
                    .charge(method_arguments.len())
                    .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
                arguments
                    .try_reserve(method_arguments.len())
                    .map_err(|_| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
                for argument in method_arguments {
                    arguments.push(self.clone_type(argument)?);
                }
                let authentication = match selection.node(selection.root()) {
                    Some(EvidenceNode::Abstract { requirement, .. }) => lowering
                        .active_binders
                        .get(&(requirement, method))
                        .map(|active| (Some(requirement), Some(active.binder))),
                    Some(EvidenceNode::Implementation { .. }) => Some((None, None)),
                    None => None,
                };
                let application_type = self.clone_type(&expected)?;
                let node = self.builder.type_application(
                    selected.node,
                    arguments.into_vec(),
                    application_type,
                    occurrence.origin.clone(),
                )?;
                if let Some((requirement, binder)) = authentication {
                    let application = InterfaceApplication::new(
                        selection.interface(),
                        self.clone_types(selection.arguments())?,
                    );
                    self.builder.authenticate_method_evidence(
                        node,
                        None,
                        requirement,
                        method,
                        application,
                        MethodEvidenceAnchorRole::Instantiation { binder },
                        Some(slot.storage_id()),
                    )?;
                }
                selected.node = node;
                discard_type_iteratively(std::mem::replace(
                    &mut selected.ty,
                    self.clone_type(&expected)?,
                ));
            }
            let ty = IterativeTypeOwner::new(std::mem::replace(&mut selected.ty, Type::Unit));
            let provenance = self.at_span_provenance(&ty, declaration_span)?;
            Ok(TypedNode {
                node: selected.node,
                provenance,
                ty: ty.into_inner(),
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
        let mut specifications = EvidenceSpecificationBuffer(Vec::new());
        let method_count = self
            .evidence_lowering
            .as_ref()
            .ok_or_else(invalid_state)?
            .global_schemes
            .get(&binder)
            .ok_or_else(invalid_state)?
            .requirements
            .iter()
            .map(|requirement| requirement.methods.len())
            .sum();
        self.reserve_evidence_specifications(&mut specifications, method_count)?;
        let scheme = self
            .evidence_lowering
            .as_ref()
            .ok_or_else(invalid_state)?
            .global_schemes
            .get(&binder)
            .ok_or_else(invalid_state)?;
        for requirement in &scheme.requirements {
            for method in &requirement.methods {
                specifications.push((
                    requirement.owner,
                    requirement.id,
                    method.method,
                    method
                        .application
                        .clone_with_budget(&mut self.type_work)
                        .map_err(|()| {
                            TypeError::Internal(ElaborationFailure::TypeResourceExhausted)
                        })?,
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
        let mut specifications = EvidenceSpecificationBuffer(Vec::new());
        let method_count = self
            .evidence_lowering
            .as_ref()
            .ok_or_else(invalid_state)?
            .implementation_methods
            .get(&method)
            .ok_or_else(invalid_state)?
            .scheme
            .requirements
            .iter()
            .map(|requirement| requirement.methods.len())
            .sum();
        self.reserve_evidence_specifications(&mut specifications, method_count)?;
        let scheme = &self
            .evidence_lowering
            .as_ref()
            .ok_or_else(invalid_state)?
            .implementation_methods
            .get(&method)
            .ok_or_else(invalid_state)?
            .scheme;
        for requirement in &scheme.requirements {
            for method in &requirement.methods {
                specifications.push((
                    requirement.owner,
                    requirement.id,
                    method.method,
                    method
                        .application
                        .clone_with_budget(&mut self.type_work)
                        .map_err(|()| {
                            TypeError::Internal(ElaborationFailure::TypeResourceExhausted)
                        })?,
                    clone_type_with_budget(&method.ty, &mut self.type_work).map_err(|()| {
                        TypeError::Internal(ElaborationFailure::TypeResourceExhausted)
                    })?,
                ));
            }
        }
        self.enter_lowered_evidence_specifications(specifications, cause)
    }

    fn reserve_evidence_specifications(
        &mut self,
        specifications: &mut EvidenceSpecificationBuffer,
        count: usize,
    ) -> Result<(), TypeError> {
        self.type_work
            .charge(count)
            .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
        specifications
            .try_reserve(count)
            .map_err(|_| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))
    }

    fn enter_lowered_evidence_specifications(
        &mut self,
        specifications: EvidenceSpecificationBuffer,
        cause: &Origin,
    ) -> Result<Vec<ScopedEvidenceBinder>, TypeError> {
        let scope_carrier_work = specifications
            .len()
            .checked_mul(3)
            .ok_or(TypeError::Internal(
                ElaborationFailure::TypeResourceExhausted,
            ))?;
        self.type_work
            .charge(scope_carrier_work)
            .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
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
        let mut staged_active = HashMap::new();
        staged_active
            .try_reserve(specifications.len())
            .map_err(|_| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
        for (owner, requirement, method, application, ty) in specifications.into_sequence() {
            let ty = IterativeTypeOwner::new(ty);
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
                application: application
                    .clone_with_budget(&mut self.type_work)
                    .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?,
                ty: ty.into_inner(),
            };
            if staged_active
                .insert((requirement, method), active)
                .is_some()
            {
                return Err(invalid_state());
            }
            binders.push(ScopedEvidenceBinder {
                owner,
                requirement,
                method,
                application,
                binder,
            });
        }
        self.evidence_lowering
            .as_mut()
            .ok_or_else(invalid_state)?
            .active_binders
            .extend(staged_active);
        Ok(binders)
    }

    fn wrap_lowered_evidence_scope(
        &mut self,
        function: TypedNode,
        binders: Vec<ScopedEvidenceBinder>,
        cause: &Origin,
    ) -> Result<TypedNode, TypeError> {
        let mut function = TypedNodeOwner::new(function);
        for scoped in binders.into_iter().rev() {
            let ScopedEvidenceBinder {
                owner,
                requirement,
                method,
                application,
                binder,
            } = scoped;
            let active = self
                .evidence_lowering
                .as_mut()
                .ok_or_else(invalid_state)?
                .active_binders
                .remove(&(requirement, method))
                .ok_or_else(invalid_state)?;
            if active.binder != binder.id()
                || !same_type_with_budget(&active.ty, binder.ty(), &mut self.type_work)
                    .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?
            {
                return Err(invalid_state());
            }
            if !same_interface_application_with_budget(
                &active.application,
                &application,
                &mut self.type_work,
            )? {
                return Err(invalid_state());
            }
            let is_polymorphic = matches!(binder.ty(), Type::Forall(_, _));
            let binder_id = binder.id();
            let domain = IterativeTypeOwner::new(self.clone_type(binder.ty())?);
            let codomain = self.clone_type(&function.ty)?;
            let ty = IterativeTypeOwner::new(Type::Function(
                Box::new(domain.into_inner()),
                Box::new(codomain),
            ));
            let core_ty = self.clone_type(&ty)?;
            let node = self.builder.function(
                binder,
                function.node,
                core_ty,
                Origin::Generated {
                    cause: Box::new(cause.clone()),
                    reason: GeneratedReason::TypeChecking,
                },
            )?;
            if is_polymorphic {
                self.builder.authenticate_method_evidence(
                    node,
                    Some(owner),
                    Some(requirement),
                    method,
                    application,
                    MethodEvidenceAnchorRole::Domain { binder: binder_id },
                    None,
                )?;
            } else {
                drop(application);
            }
            function.set_node(node);
            function.replace_type(ty.into_inner());
            let provenance = self.at_span_provenance(&function.ty, cause.primary_span())?;
            function.set_provenance(provenance);
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
        Ok(function.into_inner())
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
        if scheme.binder_parameters().len() != arguments.len() {
            return Err(invalid_state());
        }
        if arguments.is_empty() {
            return self.clone_type(&scheme.core_scheme);
        }
        let Type::Forall(parameters, body) = &scheme.core_scheme else {
            return Err(invalid_state());
        };
        if !same_kinded_type_parameters_with_budget(
            parameters,
            scheme.binder_parameters(),
            &mut self.type_work,
        )
        .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?
        {
            return Err(invalid_state());
        }
        self.type_work
            .charge(arguments.len())
            .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
        let mut replacements = TypeReplacementBuffer::new();
        replacements
            .try_reserve(arguments.len())
            .map_err(|_| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
        for ((parameter, _), argument) in parameters.iter().zip(arguments) {
            if replacements
                .try_insert_unique(*parameter, self.clone_type(argument)?)
                .is_err()
            {
                return Err(invalid_state());
            }
        }
        substitute_type_variables_with(body, replacements.as_map(), |cells| {
            self.type_work.charge(cells)
        })
        .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))
    }

    fn instantiate_lowered_source_type(
        &mut self,
        parameters: &[(TypeVariableId, Kind)],
        ty: &Type,
        arguments: &[Type],
    ) -> Result<Type, TypeError> {
        if parameters.len() != arguments.len() {
            return Err(invalid_state());
        }
        self.type_work
            .charge(parameters.len())
            .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
        let mut replacements = TypeReplacementBuffer::new();
        replacements
            .try_reserve(arguments.len())
            .map_err(|_| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
        for ((parameter, _), argument) in parameters.iter().zip(arguments) {
            if replacements
                .try_insert_unique(*parameter, self.clone_type(argument)?)
                .is_err()
            {
                return Err(invalid_state());
            }
        }
        substitute_type_variables_with(ty, replacements.as_map(), |cells| {
            self.type_work.charge(cells)
        })
        .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))
    }

    fn instantiate_lowered_source_application(
        &mut self,
        parameters: &[(TypeVariableId, Kind)],
        application: &InterfaceApplication,
        arguments: &[Type],
    ) -> Result<InterfaceApplication, TypeError> {
        self.type_work
            .charge(application.arguments().len())
            .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
        let mut instantiated = OwnedTypeBuffer(Vec::new());
        instantiated
            .try_reserve(application.arguments().len())
            .map_err(|_| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
        for ty in application.arguments() {
            instantiated.push(self.instantiate_lowered_source_type(parameters, ty, arguments)?);
        }
        Ok(InterfaceApplication::new(
            application.interface(),
            instantiated.into_boxed_slice(),
        ))
    }

    fn replay_lowered_global_determination(
        &mut self,
        scheme: &LoweredScheme,
        arguments: &[Type],
        occurrence: &crate::resolved::ResolvedOccurrence,
        lowering: &EvidenceLowering,
    ) -> Result<(), TypeError> {
        if occurrence.evidence.len() != scheme.requirements.len() {
            return Err(invalid_state());
        }
        for (requirement, slot) in scheme.requirements.iter().zip(&occurrence.evidence) {
            let source_application = requirement
                .methods
                .first()
                .map(|method| &method.application)
                .ok_or_else(invalid_state)?;
            let lowered_interface = lowering
                .interfaces
                .get(&source_application.interface())
                .ok_or_else(invalid_state)?;
            let Some(determination) = lowered_interface.determination.as_deref() else {
                continue;
            };
            let (checked_application, _) = slot.filled().ok_or_else(invalid_state)?;
            let instantiated = self.instantiate_lowered_source_application(
                scheme.binder_parameters(),
                source_application,
                arguments,
            )?;
            if checked_application.interface() != instantiated.interface()
                || checked_application.arguments().len() != instantiated.arguments().len()
            {
                return Err(invalid_state());
            }
            let mut previous = None;
            for &position in determination {
                self.constraint_work
                    .charge(1)
                    .map_err(|()| constraint_resource())?;
                if position >= instantiated.arguments().len()
                    || previous.is_some_and(|previous| previous >= position)
                {
                    return Err(invalid_state());
                }
                previous = Some(position);
            }
            let dependent_count = instantiated
                .arguments()
                .len()
                .checked_sub(determination.len())
                .ok_or_else(invalid_state)?;
            let dependent_storage_work = dependent_count
                .checked_mul(2)
                .and_then(|work| work.checked_add(1))
                .ok_or_else(constraint_resource)?;
            self.constraint_work
                .charge(dependent_storage_work)
                .map_err(|()| constraint_resource())?;
            let mut expected = OwnedTypeBuffer(Vec::new());
            let mut found = OwnedTypeBuffer(Vec::new());
            expected
                .try_reserve(dependent_count)
                .map_err(|_| constraint_resource())?;
            found
                .try_reserve(dependent_count)
                .map_err(|_| constraint_resource())?;
            let mut next_key = determination.iter().copied().peekable();
            for (position, (instantiated, checked)) in instantiated
                .arguments()
                .iter()
                .zip(checked_application.arguments())
                .enumerate()
            {
                if next_key.peek() == Some(&position) {
                    next_key.next();
                    continue;
                }
                expected.push(self.clone_type(instantiated)?);
                found.push(self.clone_type(checked)?);
            }
            if next_key.next().is_some() || expected.len() != dependent_count {
                return Err(invalid_state());
            }
            let expected = IterativeTypeOwner::new(Type::Tuple(expected.into_boxed_slice()));
            let found = IterativeTypeOwner::new(Type::Tuple(found.into_boxed_slice()));
            match self.unify(&expected, &found) {
                Ok(()) => {}
                Err(
                    UnificationFailure::Mismatch
                    | UnificationFailure::Infinite
                    | UnificationFailure::Invariant,
                ) => {
                    return Err(invalid_state());
                }
                Err(UnificationFailure::Resource) => {
                    return Err(TypeError::Internal(
                        ElaborationFailure::TypeResourceExhausted,
                    ));
                }
            }
        }
        Ok(())
    }

    fn unify_interface_applications(
        &mut self,
        expected: &InterfaceApplication,
        actual: &InterfaceApplication,
    ) -> Result<(), TypeError> {
        if expected.interface() != actual.interface()
            || expected.arguments().len() != actual.arguments().len()
        {
            return Err(invalid_state());
        }
        for (expected, actual) in expected.arguments().iter().zip(actual.arguments()) {
            match self.unify(expected, actual) {
                Ok(()) => {}
                Err(UnificationFailure::Mismatch | UnificationFailure::Infinite) => {
                    return Err(invalid_state());
                }
                Err(UnificationFailure::Resource) => {
                    return Err(TypeError::Internal(
                        ElaborationFailure::TypeResourceExhausted,
                    ));
                }
                Err(UnificationFailure::Invariant) => return Err(invalid_state()),
            }
        }
        Ok(())
    }

    fn zonk_interface_application(
        &mut self,
        application: &InterfaceApplication,
    ) -> Result<InterfaceApplication, TypeError> {
        self.type_work
            .charge(application.arguments().len())
            .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
        let mut arguments = OwnedTypeBuffer(Vec::new());
        arguments
            .try_reserve(application.arguments().len())
            .map_err(|_| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
        for argument in application.arguments() {
            arguments.push(self.zonk(argument)?);
        }
        Ok(InterfaceApplication::new(
            application.interface(),
            arguments.into_boxed_slice(),
        ))
    }

    #[allow(
        clippy::too_many_arguments,
        reason = "the authenticated adapter edge is checked field-for-field"
    )]
    fn apply_lowered_argument(
        &mut self,
        function: TypedNode,
        argument: &LoweredEvidenceMethod,
        target_owner: MethodEvidenceOwner,
        target_requirement: RequirementId,
        target: &LoweredRequirementMethod,
        target_application: &InterfaceApplication,
        canonical_method: &LoweredInterfaceMethod,
        adapter_edge: Option<(ImplMethodId, crate::interface::EvidenceNodeId, usize)>,
        origin: &Origin,
        occurrence: usize,
    ) -> Result<TypedNode, TypeError> {
        let function = TypedNodeOwner::new(function);
        let Type::Function(domain, codomain) = &function.ty else {
            return Err(invalid_state());
        };
        let polymorphic = matches!(domain.as_ref(), Type::Forall(_, _));
        if polymorphic {
            let producer_matches = match argument.producer {
                PolymorphicEvidenceProducer::Abstract { .. } => {
                    let Some(application) = argument.adapter_application.as_ref() else {
                        return Err(invalid_state());
                    };
                    self.unify_interface_applications(target_application, application)?;
                    let current_domain = IterativeTypeOwner::new(self.zonk(domain)?);
                    same_type_with_budget(&current_domain, &argument.ty, &mut self.type_work)
                        .map_err(|()| {
                            TypeError::Internal(ElaborationFailure::TypeResourceExhausted)
                        })?
                }
                PolymorphicEvidenceProducer::Adapter { implementation, .. } => {
                    let Some(application) = argument.adapter_application.as_ref() else {
                        return Err(invalid_state());
                    };
                    self.unify_interface_applications(target_application, application)?;
                    let current_domain = IterativeTypeOwner::new(self.zonk(domain)?);
                    implementation.method() == target.method
                        && self.authenticated_adapter_scheme_matches(
                            &current_domain,
                            &argument.ty,
                            &canonical_method.type_parameters,
                        )?
                }
            };
            if target.method != argument.method
                || canonical_method.interface != argument.method.interface()
                || !producer_matches
            {
                return Err(invalid_state());
            }
        } else {
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
                Err(UnificationFailure::Invariant) => return Err(invalid_state()),
            }
        }
        let ty = IterativeTypeOwner::new(self.clone_type(codomain)?);
        let core_ty = self.clone_type(&ty)?;
        let node =
            self.builder
                .application(function.node, argument.node, core_ty, origin.clone())?;
        if polymorphic || adapter_edge.is_some() {
            let application = self.zonk_interface_application(target_application)?;
            let (producer, producer_selection_node, producer_binder) = match argument.producer {
                PolymorphicEvidenceProducer::Abstract {
                    requirement,
                    selection_node,
                    binder,
                } => (
                    CoreMethodEvidenceProducer::Abstract { requirement },
                    selection_node,
                    Some(binder),
                ),
                PolymorphicEvidenceProducer::Adapter {
                    implementation,
                    selection_node,
                } => (
                    CoreMethodEvidenceProducer::Adapter { implementation },
                    selection_node,
                    None,
                ),
            };
            let role = adapter_edge.map_or(
                MethodEvidenceAnchorRole::Application { producer },
                |(adapter, adapter_selection_node, ordinal)| {
                    MethodEvidenceAnchorRole::AdapterEdge {
                        adapter,
                        adapter_selection_node,
                        ordinal,
                        producer_node: argument.node,
                        producer_selection_node,
                        producer_binder,
                        producer,
                    }
                },
            );
            self.builder.authenticate_method_evidence(
                node,
                Some(target_owner),
                Some(target_requirement),
                target.method,
                application,
                role,
                Some(occurrence),
            )?;
        }
        let provenance = self.at_span_provenance(&ty, origin.primary_span())?;
        Ok(TypedNode {
            node,
            ty: ty.into_inner(),
            provenance,
        })
    }

    fn authenticated_adapter_scheme_matches(
        &mut self,
        expected: &Type,
        actual: &Type,
        canonical_parameters: &[(TypeVariableId, Kind)],
    ) -> Result<bool, TypeError> {
        let (
            Type::Forall(expected_parameters, expected_body),
            Type::Forall(actual_parameters, actual_body),
        ) = (expected, actual)
        else {
            return Ok(false);
        };
        if expected_parameters.len() != canonical_parameters.len()
            || actual_parameters.len() != canonical_parameters.len()
            || !same_kinded_type_parameters_with_budget(
                expected_parameters,
                canonical_parameters,
                &mut self.type_work,
            )
            .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?
        {
            return Ok(false);
        }
        let mut actual_ids = HashSet::new();
        let alpha_carrier_work =
            actual_parameters
                .len()
                .checked_mul(2)
                .ok_or(TypeError::Internal(
                    ElaborationFailure::TypeResourceExhausted,
                ))?;
        self.type_work
            .charge(alpha_carrier_work)
            .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
        actual_ids
            .try_reserve(actual_parameters.len())
            .map_err(|_| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
        let mut replacements = TypeReplacementBuffer::new();
        replacements
            .try_reserve(actual_parameters.len())
            .map_err(|_| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
        for (((expected, expected_kind), (actual, actual_kind)), (canonical, _)) in
            expected_parameters
                .iter()
                .zip(actual_parameters)
                .zip(canonical_parameters)
        {
            if expected != canonical
                || !matches!(actual, TypeVariableId::Generated(_))
                || !actual_ids.insert(*actual)
                || !same_kind_with_budget(expected_kind, actual_kind, &mut self.type_work)
                    .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?
                || self.type_contains_any_variable(expected_body, &actual_ids)?
                || replacements
                    .try_insert_unique(*expected, Type::Variable(*actual))
                    .is_err()
            {
                return Ok(false);
            }
        }
        let renamed = IterativeTypeOwner::new(
            substitute_type_variables_with(expected_body, replacements.as_map(), |cells| {
                self.type_work.charge(cells)
            })
            .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?,
        );
        same_type_with_budget(&renamed, actual_body, &mut self.type_work)
            .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))
    }

    fn type_contains_any_variable(
        &mut self,
        ty: &Type,
        variables: &HashSet<TypeVariableId>,
    ) -> Result<bool, TypeError> {
        let mut pending = Vec::new();
        self.type_work
            .charge(1)
            .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
        pending
            .try_reserve(1)
            .map_err(|_| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
        pending.push(ty);
        while let Some(ty) = pending.pop() {
            self.type_work
                .charge(1)
                .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
            match ty {
                Type::Variable(variable) if variables.contains(variable) => return Ok(true),
                Type::Application(function, argument) | Type::Function(function, argument) => {
                    self.type_work.charge(2).map_err(|()| {
                        TypeError::Internal(ElaborationFailure::TypeResourceExhausted)
                    })?;
                    pending.try_reserve(2).map_err(|_| {
                        TypeError::Internal(ElaborationFailure::TypeResourceExhausted)
                    })?;
                    pending.push(argument);
                    pending.push(function);
                }
                Type::Tuple(elements) => {
                    self.type_work.charge(elements.len()).map_err(|()| {
                        TypeError::Internal(ElaborationFailure::TypeResourceExhausted)
                    })?;
                    pending.try_reserve(elements.len()).map_err(|_| {
                        TypeError::Internal(ElaborationFailure::TypeResourceExhausted)
                    })?;
                    pending.extend(elements);
                }
                Type::Forall(_, body) => {
                    self.type_work.charge(1).map_err(|()| {
                        TypeError::Internal(ElaborationFailure::TypeResourceExhausted)
                    })?;
                    pending.try_reserve(1).map_err(|_| {
                        TypeError::Internal(ElaborationFailure::TypeResourceExhausted)
                    })?;
                    pending.push(body);
                }
                Type::Int
                | Type::Bool
                | Type::Unit
                | Type::Nominal(_)
                | Type::Variable(_)
                | Type::Inference(_) => {}
            }
        }
        Ok(false)
    }

    fn lower_evidence_selection(
        &mut self,
        selection: &EvidenceSelection,
        lowering: &mut EvidenceLowering,
        origin: &Origin,
        root_method: Option<MethodId>,
        occurrence: usize,
    ) -> Result<Vec<LoweredEvidenceMethod>, TypeError> {
        enum Task {
            Visit(crate::interface::EvidenceNodeId),
            Build(crate::interface::EvidenceNodeId),
        }

        let mut tasks = Vec::new();
        self.type_work
            .charge(selection.node_count())
            .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
        tasks
            .try_reserve(selection.node_count())
            .map_err(|_| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
        self.type_work
            .charge(1)
            .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
        tasks.push(Task::Visit(selection.root()));
        let mut values: HashMap<crate::interface::EvidenceNodeId, Vec<LoweredEvidenceMethod>> =
            HashMap::new();
        self.type_work
            .charge(selection.node_count())
            .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
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
                    self.type_work.charge(1).map_err(|()| {
                        TypeError::Internal(ElaborationFailure::TypeResourceExhausted)
                    })?;
                    tasks.try_reserve(1).map_err(|_| {
                        TypeError::Internal(ElaborationFailure::TypeResourceExhausted)
                    })?;
                    tasks.push(Task::Build(node));
                    if let EvidenceNode::Implementation { prerequisites, .. } = evidence {
                        self.type_work.charge(prerequisites.len()).map_err(|()| {
                            TypeError::Internal(ElaborationFailure::TypeResourceExhausted)
                        })?;
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
                            let result_count = requested.map_or(methods.len(), |_| 1);
                            self.type_work.charge(result_count).map_err(|()| {
                                TypeError::Internal(ElaborationFailure::TypeResourceExhausted)
                            })?;
                            results.try_reserve(result_count).map_err(|_| {
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
                                let ty = IterativeTypeOwner::new(self.clone_type(&active.ty)?);
                                let core_ty = self.clone_type(&ty)?;
                                let core_node = self.builder.variable(
                                    active.binder,
                                    core_ty,
                                    origin.clone(),
                                )?;
                                results.push(LoweredEvidenceMethod {
                                    method: *method,
                                    node: core_node,
                                    producer: PolymorphicEvidenceProducer::Abstract {
                                        requirement,
                                        selection_node: node,
                                        binder: active.binder,
                                    },
                                    adapter_application: Some(
                                        active
                                            .application
                                            .clone_with_budget(&mut self.type_work)
                                            .map_err(|()| {
                                            TypeError::Internal(
                                                ElaborationFailure::TypeResourceExhausted,
                                            )
                                        })?,
                                    ),
                                    ty: ty.into_inner(),
                                });
                            }
                            results
                        }
                        EvidenceNode::Implementation {
                            implementation,
                            substitution,
                            prerequisites,
                            methods,
                        } => {
                            let requested =
                                (node == selection.root()).then_some(root_method).flatten();
                            let mut results = Vec::new();
                            let result_count = requested.map_or(methods.len(), |_| 1);
                            self.type_work.charge(result_count).map_err(|()| {
                                TypeError::Internal(ElaborationFailure::TypeResourceExhausted)
                            })?;
                            results.try_reserve(result_count).map_err(|_| {
                                TypeError::Internal(ElaborationFailure::TypeResourceExhausted)
                            })?;
                            for method in methods {
                                if requested.is_some_and(|requested| requested != method.method()) {
                                    continue;
                                }
                                if method.implementation() != implementation {
                                    return Err(invalid_state());
                                }
                                let lowered = lowering
                                    .implementation_methods
                                    .get(method)
                                    .ok_or_else(invalid_state)?;
                                let source_parameters = lowered
                                    .scheme
                                    .source_binder_parameters()
                                    .ok_or_else(invalid_state)?;
                                let interface_method = lowering
                                    .interface_methods
                                    .get(&method.method())
                                    .ok_or_else(invalid_state)?;
                                let method_parameter_count = interface_method.type_parameters.len();
                                if lowered.head_type_parameter_count != substitution.len()
                                    || source_parameters.len()
                                        != substitution.len().saturating_add(method_parameter_count)
                                    || source_parameters
                                        .iter()
                                        .take(substitution.len())
                                        .zip(substitution)
                                        .any(|(parameter, substitution)| {
                                            parameter.0 != substitution.parameter()
                                        })
                                {
                                    return Err(invalid_state());
                                }
                                let core_scheme = IterativeTypeOwner::new(
                                    self.clone_type(&lowered.scheme.core_scheme)?,
                                );
                                let variable_ty =
                                    IterativeTypeOwner::new(self.clone_type(&core_scheme)?);
                                let provenance = self
                                    .at_span_provenance(&lowered.scheme.value_type, lowered.span)?;
                                let mut current = TypedNodeOwner::new(TypedNode {
                                    node: self.builder.variable(
                                        lowered.binder,
                                        variable_ty.into_inner(),
                                        origin.clone(),
                                    )?,
                                    ty: core_scheme.into_inner(),
                                    provenance,
                                });
                                let mut adapter_parameters = Vec::new();
                                self.type_work
                                    .charge(method_parameter_count)
                                    .map_err(|()| {
                                        TypeError::Internal(
                                            ElaborationFailure::TypeResourceExhausted,
                                        )
                                    })?;
                                adapter_parameters
                                    .try_reserve(method_parameter_count)
                                    .map_err(|_| {
                                        TypeError::Internal(
                                            ElaborationFailure::TypeResourceExhausted,
                                        )
                                    })?;
                                for (_, kind) in &interface_method.type_parameters {
                                    let identity = self.fresh_type_variable(kind, lowered.span)?;
                                    adapter_parameters.push((
                                        identity,
                                        clone_kind_with_budget(kind, &mut self.type_work).map_err(
                                            |()| {
                                                TypeError::Internal(
                                                    ElaborationFailure::TypeResourceExhausted,
                                                )
                                            },
                                        )?,
                                    ));
                                }
                                let mut current_arguments = OwnedTypeBuffer(Vec::new());
                                if !source_parameters.is_empty() {
                                    let mut arguments = OwnedTypeBuffer(Vec::new());
                                    self.type_work.charge(source_parameters.len()).map_err(
                                        |()| {
                                            TypeError::Internal(
                                                ElaborationFailure::TypeResourceExhausted,
                                            )
                                        },
                                    )?;
                                    arguments.try_reserve(source_parameters.len()).map_err(
                                        |_| {
                                            TypeError::Internal(
                                                ElaborationFailure::TypeResourceExhausted,
                                            )
                                        },
                                    )?;
                                    for substitution in substitution {
                                        arguments.push(self.clone_type(substitution.argument())?);
                                    }
                                    for (parameter, _) in &adapter_parameters {
                                        arguments.push(Type::Variable(*parameter));
                                    }
                                    self.type_work.charge(arguments.len()).map_err(|()| {
                                        TypeError::Internal(
                                            ElaborationFailure::TypeResourceExhausted,
                                        )
                                    })?;
                                    current_arguments.try_reserve(arguments.len()).map_err(
                                        |_| {
                                            TypeError::Internal(
                                                ElaborationFailure::TypeResourceExhausted,
                                            )
                                        },
                                    )?;
                                    for argument in arguments.iter() {
                                        current_arguments.push(self.clone_type(argument)?);
                                    }
                                    let instantiated = IterativeTypeOwner::new(
                                        self.instantiate_lowered_core_body(
                                            &lowered.scheme,
                                            &arguments,
                                        )?,
                                    );
                                    let core_ty = self.clone_type(&instantiated)?;
                                    let node = self.builder.type_application(
                                        current.node,
                                        arguments.into_vec(),
                                        core_ty,
                                        origin.clone(),
                                    )?;
                                    current.set_node(node);
                                    current.replace_type(instantiated.into_inner());
                                }
                                if prerequisites.len() != lowered.scheme.requirements.len() {
                                    return Err(invalid_state());
                                }
                                let mut adapter_edge_ordinal = 0usize;
                                for (prerequisite, target_requirement) in
                                    prerequisites.iter().zip(&lowered.scheme.requirements)
                                {
                                    let prerequisite_methods =
                                        values.get(prerequisite).ok_or_else(invalid_state)?;
                                    if prerequisite_methods.len()
                                        != target_requirement.methods.len()
                                    {
                                        return Err(invalid_state());
                                    }
                                    for (argument, target_method) in
                                        prerequisite_methods.iter().zip(&target_requirement.methods)
                                    {
                                        let target_application = self
                                            .instantiate_lowered_source_application(
                                                source_parameters,
                                                &target_method.application,
                                                &current_arguments,
                                            )?;
                                        let canonical_method = lowering
                                            .interface_methods
                                            .get(&target_method.method)
                                            .ok_or_else(invalid_state)?;
                                        current = TypedNodeOwner::new(
                                            self.apply_lowered_argument(
                                                current.into_inner(),
                                                argument,
                                                target_requirement.owner,
                                                target_requirement.id,
                                                target_method,
                                                &target_application,
                                                canonical_method,
                                                (!interface_method.type_parameters.is_empty())
                                                    .then_some((
                                                        *method,
                                                        node,
                                                        adapter_edge_ordinal,
                                                    )),
                                                origin,
                                                occurrence,
                                            )?,
                                        );
                                        adapter_edge_ordinal = adapter_edge_ordinal
                                            .checked_add(1)
                                            .ok_or_else(invalid_state)?;
                                    }
                                }
                                let adapter_application =
                                    (!interface_method.type_parameters.is_empty())
                                        .then(|| {
                                            self.instantiate_lowered_source_application(
                                                source_parameters,
                                                &lowered.application,
                                                &current_arguments,
                                            )
                                        })
                                        .transpose()?;
                                if !adapter_parameters.is_empty() {
                                    self.type_work.charge(1).map_err(|()| {
                                        TypeError::Internal(
                                            ElaborationFailure::TypeResourceExhausted,
                                        )
                                    })?;
                                    let scheme_parameters =
                                        clone_kinded_type_parameters_with_budget(
                                            &adapter_parameters,
                                            &mut self.type_work,
                                        )
                                        .map_err(|()| {
                                            TypeError::Internal(
                                                ElaborationFailure::TypeResourceExhausted,
                                            )
                                        })?;
                                    let scheme_body = self.clone_type(&current.ty)?;
                                    let scheme = IterativeTypeOwner::new(Type::Forall(
                                        scheme_parameters.into_boxed_slice(),
                                        Box::new(scheme_body),
                                    ));
                                    let abstraction_type = self.clone_type(&scheme)?;
                                    let abstraction = self.builder.type_abstraction(
                                        adapter_parameters,
                                        current.node,
                                        abstraction_type,
                                        origin.clone(),
                                    )?;
                                    let application = adapter_application
                                        .as_ref()
                                        .ok_or_else(invalid_state)?
                                        .clone_with_budget(&mut self.type_work)
                                        .map_err(|()| {
                                            TypeError::Internal(
                                                ElaborationFailure::TypeResourceExhausted,
                                            )
                                        })?;
                                    self.builder.authenticate_method_evidence(
                                        abstraction,
                                        None,
                                        None,
                                        method.method(),
                                        application,
                                        MethodEvidenceAnchorRole::Adapter {
                                            implementation: *method,
                                            selection_node: node,
                                        },
                                        Some(occurrence),
                                    )?;
                                    current.set_node(abstraction);
                                    current.replace_type(scheme.into_inner());
                                }
                                let current = current.into_inner();
                                results.push(LoweredEvidenceMethod {
                                    method: method.method(),
                                    node: current.node,
                                    producer: PolymorphicEvidenceProducer::Adapter {
                                        implementation: *method,
                                        selection_node: node,
                                    },
                                    adapter_application,
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
            let zonked = self.zonk(&ty);
            discard_type_iteratively(ty);
            zonked
        }
    }

    fn zonk_with_status(&mut self, ty: &Type) -> Result<(Type, bool), TypeError> {
        let solutions = &self.inference_solutions;
        let inference_variables = &self.inference_variables;
        let authenticated_solutions = &self.authenticated_inference_solutions;
        let type_work = &mut self.type_work;
        zonk_type_with_status_and_inference(ty, solutions, |work| match work {
            ZonkWork::TypeCells(cells) => type_work
                .charge(cells)
                .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted)),
            ZonkWork::Inference(identity) => authenticate_zonk_inference_occurrence(
                identity,
                inference_variables,
                solutions,
                authenticated_solutions,
                type_work,
            )
            .map_err(|failure| match failure {
                UnificationFailure::Resource => {
                    TypeError::Internal(ElaborationFailure::TypeResourceExhausted)
                }
                UnificationFailure::Mismatch
                | UnificationFailure::Infinite
                | UnificationFailure::Invariant => invalid_state(),
            }),
        })
    }

    fn charge_type(&mut self, ty: &Type) -> Result<(), TypeError> {
        charge_type_cells(ty, &mut self.type_work)
            .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))
    }

    fn clone_type(&mut self, ty: &Type) -> Result<Type, TypeError> {
        clone_type_with_budget(ty, &mut self.type_work)
            .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))
    }

    fn clone_types(&mut self, types: &[Type]) -> Result<Box<[Type]>, TypeError> {
        self.type_work
            .charge(types.len())
            .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
        let mut cloned = OwnedTypeBuffer(Vec::new());
        cloned
            .try_reserve(types.len())
            .map_err(|_| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
        for ty in types {
            cloned.push(self.clone_type(ty)?);
        }
        Ok(cloned.into_boxed_slice())
    }

    fn unknown_provenance(&mut self, ty: &Type) -> Result<TypeProvenance, TypeError> {
        unknown_provenance_with_budget(ty, &mut self.type_work)
            .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))
    }

    fn at_span_provenance(&mut self, ty: &Type, span: Span) -> Result<TypeProvenance, TypeError> {
        at_span_provenance_with_budget(ty, span, &mut self.type_work)
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
            match validate_and_charge_public_monotype(&fact.ty, &self.registry, &mut self.type_work)
            {
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
        validate_and_charge_public_monotype(ty, &self.registry, &mut self.type_work).map_err(
            |error| match error {
                PublicTypeAdmissionError::Invalid => invalid_state(),
                PublicTypeAdmissionError::Resource => {
                    TypeError::Internal(ElaborationFailure::TypeResourceExhausted)
                }
            },
        )
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

        struct Work(Vec<Task>);

        impl Drop for Work {
            fn drop(&mut self) {
                while let Some(task) = self.0.pop() {
                    match task {
                        Task::Pair(left, right) => {
                            discard_type_iteratively(left);
                            discard_type_iteratively(right);
                        }
                        Task::Sequence(left, right) => {
                            for ty in left {
                                discard_type_iteratively(ty);
                            }
                            for ty in right {
                                discard_type_iteratively(ty);
                            }
                        }
                    }
                }
            }
        }

        let left = IterativeTypeOwner::new(
            clone_type_with_budget(left, &mut self.type_work)
                .map_err(|()| UnificationFailure::Resource)?,
        );
        let right = clone_type_with_budget(right, &mut self.type_work)
            .map_err(|()| UnificationFailure::Resource)?;
        let mut inserted = Vec::new();
        let result = (|| {
            let mut work = Work(vec![Task::Pair(left.into_inner(), right)]);
            while let Some(task) = work.0.pop() {
                let (left, right) = match task {
                    Task::Pair(left, right) => (left, right),
                    Task::Sequence(mut left_types, mut right_types) => {
                        match (left_types.next(), right_types.next()) {
                            (Some(left), Some(right)) => {
                                work.0.push(Task::Sequence(left_types, right_types));
                                work.0.push(Task::Pair(left, right));
                                continue;
                            }
                            (None, None) => continue,
                            (left, right) => {
                                if let Some(left) = left {
                                    discard_type_iteratively(left);
                                }
                                if let Some(right) = right {
                                    discard_type_iteratively(right);
                                }
                                for ty in left_types {
                                    discard_type_iteratively(ty);
                                }
                                for ty in right_types {
                                    discard_type_iteratively(ty);
                                }
                                return Err(UnificationFailure::Mismatch);
                            }
                        }
                    }
                };
                let zonked_left = self.zonk(&left);
                discard_type_iteratively(left);
                let left = match zonked_left {
                    Ok(left) => left,
                    Err(error) => {
                        discard_type_iteratively(right);
                        return Err(match error {
                            TypeError::Internal(ElaborationFailure::TypeResourceExhausted) => {
                                UnificationFailure::Resource
                            }
                            TypeError::Source(_)
                            | TypeError::Interface(_)
                            | TypeError::Mismatch(_)
                            | TypeError::Internal(_) => UnificationFailure::Invariant,
                        });
                    }
                };
                let zonked_right = self.zonk(&right);
                discard_type_iteratively(right);
                let right = match zonked_right {
                    Ok(right) => right,
                    Err(error) => {
                        discard_type_iteratively(left);
                        return Err(match error {
                            TypeError::Internal(ElaborationFailure::TypeResourceExhausted) => {
                                UnificationFailure::Resource
                            }
                            TypeError::Source(_)
                            | TypeError::Interface(_)
                            | TypeError::Mismatch(_)
                            | TypeError::Internal(_) => UnificationFailure::Invariant,
                        });
                    }
                };
                match (left, right) {
                    (Type::Inference(left), Type::Inference(right)) if left == right => {
                        self.inference_variables
                            .fact(left, &mut self.type_work)
                            .map_err(inference_registry_failure_for_unification)?;
                    }
                    (Type::Inference(variable), ty) | (ty, Type::Inference(variable)) => {
                        let ty = IterativeTypeOwner::new(ty);
                        authenticate_inference_solution_kind(
                            variable,
                            &ty,
                            &self.registry,
                            &self.generated_type_variables,
                            &self.inference_variables,
                            &mut self.type_work,
                        )?;
                        if self.charge_type(&ty).is_err() {
                            return Err(UnificationFailure::Resource);
                        }
                        if type_contains_inference(
                            &ty,
                            variable,
                            &self.inference_solutions,
                            &self.registry,
                            &self.generated_type_variables,
                            &self.inference_variables,
                            &mut self.type_work,
                        )? {
                            return Err(UnificationFailure::Infinite);
                        }
                        if self.type_work.charge(3).is_err()
                            || self.inference_solutions.try_reserve(1).is_err()
                            || self
                                .authenticated_inference_solutions
                                .try_reserve(1)
                                .is_err()
                            || inserted.try_reserve(1).is_err()
                        {
                            return Err(UnificationFailure::Resource);
                        }
                        if let Err(ty) = self
                            .inference_solutions
                            .insert_unique(variable, ty.into_inner())
                        {
                            discard_type_iteratively(ty);
                            return Err(UnificationFailure::Invariant);
                        }
                        if !self.authenticated_inference_solutions.insert(variable) {
                            self.inference_solutions.remove_and_discard(variable);
                            return Err(UnificationFailure::Invariant);
                        }
                        inserted.push(variable);
                    }
                    (Type::Int, Type::Int)
                    | (Type::Bool, Type::Bool)
                    | (Type::Unit, Type::Unit) => {}
                    (Type::Nominal(left), Type::Nominal(right)) if left == right => {}
                    (Type::Variable(left), Type::Variable(right)) if left == right => {}
                    (
                        Type::Application(left_function, left_argument),
                        Type::Application(right_function, right_argument),
                    ) => {
                        work.0.push(Task::Pair(*left_argument, *right_argument));
                        work.0.push(Task::Pair(*left_function, *right_function));
                    }
                    (Type::Tuple(left), Type::Tuple(right)) if left.len() == right.len() => {
                        work.0.push(Task::Sequence(
                            left.into_vec().into_iter(),
                            right.into_vec().into_iter(),
                        ));
                    }
                    (
                        Type::Function(left_domain, left_codomain),
                        Type::Function(right_domain, right_codomain),
                    ) => {
                        work.0.push(Task::Pair(*left_codomain, *right_codomain));
                        work.0.push(Task::Pair(*left_domain, *right_domain));
                    }
                    (left, right) => {
                        discard_type_iteratively(left);
                        discard_type_iteratively(right);
                        return Err(UnificationFailure::Mismatch);
                    }
                }
            }
            Ok(())
        })();
        if result.is_err() {
            for variable in inserted.drain(..).rev() {
                self.inference_solutions.remove_and_discard(variable);
                self.authenticated_inference_solutions.remove(&variable);
            }
        }
        result
    }

    fn expose_expected_function(
        &mut self,
        expected: ProvenancedTypeOwner,
        span: Span,
    ) -> Result<ProvenancedTypeOwner, TypeError> {
        match &expected.ty {
            Type::Function(_, _) => Ok(expected),
            Type::Inference(_) => {
                let expected_ty = IterativeTypeOwner::new(self.zonk(&expected.ty)?);
                if matches!(&*expected_ty, Type::Function(_, _)) {
                    let provenance = if expected.provenance.aligns(&expected_ty) {
                        expected.provenance.clone()
                    } else {
                        self.unknown_provenance(&expected_ty)?
                    };
                    return Ok(ProvenancedTypeOwner::new(ProvenancedType {
                        ty: expected_ty.into_inner(),
                        provenance,
                    }));
                }
                if !matches!(&*expected_ty, Type::Inference(_)) {
                    return Err(function_needs_context(span, None));
                }
                self.type_work
                    .charge(3)
                    .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
                let domain = self.fresh_inference(&Kind::Type, span)?;
                let codomain = self.fresh_inference(&Kind::Type, span)?;
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
                        UnificationFailure::Invariant => invalid_state(),
                    })?;
                let provenance = self.unknown_provenance(&exposed)?;
                Ok(ProvenancedTypeOwner::new(ProvenancedType {
                    ty: exposed,
                    provenance,
                }))
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
                let found = IterativeTypeOwner::new(self.zonk(&operand.ty)?);
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
            Err(UnificationFailure::Invariant) => Err(invalid_state()),
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
                let expected = IterativeTypeOwner::new(self.zonk(expected)?);
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
            Err(UnificationFailure::Invariant) => Err(invalid_state()),
        }
    }

    fn elaborate_module_program(
        &mut self,
        program: &ValidatedInterfaceProgram,
    ) -> Result<TypedNode, TypeError> {
        let mut context = TypeContext::new();
        let mut groups = ElaboratedGroupBuffer(Vec::new());
        groups
            .0
            .try_reserve(program.groups().len())
            .map_err(|_| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
        for group in program.groups() {
            let (members, next_context) = self.elaborate_checked_module_group(group, context)?;
            context = next_context;
            groups
                .0
                .push((ElaboratedBindingBuffer(members), group.span()));
        }
        let mut result = self.elaborate_result(program.result(), &mut context)?;
        let assembly = (|| {
            while let Some((mut members, span)) = groups.0.pop() {
                if members.0.is_empty() {
                    continue;
                }
                let mut core_members = CoreRecursiveMemberBuffer(Vec::new());
                core_members
                    .0
                    .try_reserve(members.0.len())
                    .map_err(|_| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
                members.0.reverse();
                while let Some(member) = members.0.pop() {
                    core_members.0.push((member.binder, member.initializer));
                }
                let result_type = self.clone_type(&result.ty)?;
                result.node = self.builder.recursive_binding(
                    std::mem::take(&mut core_members.0),
                    result.node,
                    result_type,
                    Origin::Generated {
                        cause: Box::new(Origin::Source(span)),
                        reason: GeneratedReason::RecursiveBindingLowering,
                    },
                )?;
            }
            Ok(())
        })();
        if let Err(error) = assembly {
            discard_typed_node(result);
            return Err(error);
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
                    || lowered
                        .scheme
                        .source_binder_parameters()
                        .is_none_or(|parameters| {
                            parameters.len() != method.scheme.type_parameters.len()
                        })
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
                    implementation_method_core_origin(method),
                )?;
                let source_ty = IterativeTypeOwner::new(
                    clone_type_with_budget(&lowered.scheme.value_type, &mut self.type_work)
                        .map_err(|()| {
                            TypeError::Internal(ElaborationFailure::TypeResourceExhausted)
                        })?,
                );
                let provenance =
                    at_span_provenance_with_budget(&source_ty, method.span, &mut self.type_work)
                        .map_err(|()| {
                            TypeError::Internal(ElaborationFailure::TypeResourceExhausted)
                        })?;
                if prepared.context.insert_with_provenance(
                    method.binder,
                    source_ty.into_inner(),
                    provenance,
                )? || prepared.binders.insert(method.binder, binder).is_some()
                {
                    return Err(invalid_state());
                }
                let source_parameters = lowered
                    .scheme
                    .source_binder_parameters()
                    .ok_or_else(invalid_state)?;
                if !same_kinded_type_parameters_with_budget(
                    source_parameters,
                    &method.scheme.type_parameters,
                    &mut self.type_work,
                )
                .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?
                {
                    return Err(invalid_state());
                }
                let source_quantified = clone_kinded_type_parameters_with_budget(
                    source_parameters,
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
        let mut core_type_replacements = Vec::new();
        {
            let lowered = self
                .evidence_lowering
                .as_ref()
                .and_then(|lowering| lowering.implementation_methods.get(&fact.id))
                .ok_or_else(invalid_state)?;
            let source_type_parameters = lowered
                .scheme
                .source_binder_parameters()
                .ok_or_else(invalid_state)?;
            if source_type_parameters.len() != lowered.scheme.binder_parameters().len() {
                return Err(invalid_state());
            }
            self.type_work
                .charge(
                    lowered
                        .scheme
                        .binder_parameters()
                        .len()
                        .checked_mul(2)
                        .ok_or_else(invalid_state)?,
                )
                .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
            core_type_replacements
                .try_reserve_exact(lowered.scheme.binder_parameters().len())
                .map_err(|_| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
            for ((source, _), (core, _)) in source_type_parameters
                .iter()
                .zip(lowered.scheme.binder_parameters())
            {
                if core_type_replacements
                    .iter()
                    .any(|(retained, _)| retained == source)
                {
                    return Err(invalid_state());
                }
                core_type_replacements.push((*source, *core));
            }
        }
        let core_origin = implementation_method_core_origin(fact);
        let evidence = self.enter_lowered_implementation_evidence_scope(fact.id, &core_origin)?;
        let source_ty = self
            .evidence_lowering
            .as_ref()
            .and_then(|lowering| lowering.implementation_methods.get(&fact.id))
            .map(|method| &method.scheme.value_type)
            .ok_or_else(invalid_state)?;
        let function_type = IterativeTypeOwner::new(
            clone_type_with_budget(source_ty, &mut self.type_work)
                .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?,
        );
        let function_provenance = self.at_span_provenance(&function_type, fact.span)?;
        let body_result = self.elaborate_equations(
            &source.equations,
            ProvenancedType {
                provenance: function_provenance,
                ty: function_type.into_inner(),
            },
            &mut prepared.context,
            source.span,
            &core_origin,
        );
        let mut function = TypedNodeOwner::new(match body_result {
            Ok(function) => function,
            Err(error) => {
                self.clear_lowered_evidence_scope(evidence)?;
                self.monomorphic_recursive.remove(&fact.binder);
                return Err(error);
            }
        });
        function = TypedNodeOwner::new(self.wrap_lowered_evidence_scope(
            function.into_inner(),
            evidence,
            &core_origin,
        )?);
        if !core_type_replacements.is_empty() {
            let inference_solutions = &self.inference_solutions;
            let inference_variables = &self.inference_variables;
            let authenticated_solutions = &self.authenticated_inference_solutions;
            let type_work = &mut self.type_work;
            self.builder.rewrite_types_since(rewrite_checkpoint, |ty| {
                let (zonked, _) = zonk_type_with_status_and_inference(
                    ty,
                    inference_solutions,
                    |work| match work {
                        ZonkWork::TypeCells(cells) => type_work
                            .charge(cells)
                            .map_err(|()| BuildError::TypeWorkExceeded),
                        ZonkWork::Inference(identity) => authenticate_zonk_inference_occurrence(
                            identity,
                            inference_variables,
                            inference_solutions,
                            authenticated_solutions,
                            type_work,
                        )
                        .map_err(|failure| match failure {
                            UnificationFailure::Resource => BuildError::TypeWorkExceeded,
                            UnificationFailure::Mismatch
                            | UnificationFailure::Infinite
                            | UnificationFailure::Invariant => BuildError::InvalidPayload,
                        }),
                    },
                )?;
                let renamed = substitute_fresh_type_variables_in_order(
                    &zonked,
                    &core_type_replacements,
                    type_work,
                )
                .map_err(|()| BuildError::TypeWorkExceeded);
                discard_type_iteratively(zonked);
                renamed
            })?;
            let zonked_function_type = IterativeTypeOwner::new(self.zonk(&function.ty)?);
            let renamed_function_type = IterativeTypeOwner::new(
                substitute_fresh_type_variables_in_order(
                    &zonked_function_type,
                    &core_type_replacements,
                    &mut self.type_work,
                )
                .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?,
            );
            function.replace_type(renamed_function_type.into_inner());
        }
        if !self.monomorphic_recursive.remove(&fact.binder) {
            return Err(invalid_state());
        }
        let lowered = self
            .evidence_lowering
            .as_ref()
            .and_then(|lowering| lowering.implementation_methods.get(&fact.id))
            .ok_or_else(invalid_state)?;
        if lowered.scheme.binder_parameters().is_empty() {
            if !same_type(&function.ty, &lowered.scheme.core_scheme) {
                return Err(invalid_state());
            }
            if self
                .builder
                .requires_method_evidence_implementation_owner(fact.id)?
            {
                let application = lowered
                    .application
                    .clone_with_budget(&mut self.type_work)
                    .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
                self.builder.authenticate_method_evidence(
                    function.node,
                    Some(MethodEvidenceOwner::Implementation(fact.id)),
                    None,
                    fact.id.method(),
                    application,
                    MethodEvidenceAnchorRole::ImplementationOwner {
                        implementation: fact.id,
                        binder: fact.binder,
                    },
                    None,
                )?;
            }
        } else {
            let Type::Forall(_, expected_body) = &lowered.scheme.core_scheme else {
                return Err(invalid_state());
            };
            if !same_type(&function.ty, expected_body) {
                return Err(invalid_state());
            }
            let parameters = clone_kinded_type_parameters_with_budget(
                lowered.scheme.binder_parameters(),
                &mut self.type_work,
            )
            .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
            let core_scheme =
                clone_type_with_budget(&lowered.scheme.core_scheme, &mut self.type_work)
                    .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
            let node = self.builder.type_abstraction(
                parameters,
                function.node,
                core_scheme,
                core_origin,
            )?;
            if self
                .builder
                .requires_method_evidence_implementation_owner(fact.id)?
            {
                let application = lowered
                    .application
                    .clone_with_budget(&mut self.type_work)
                    .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
                self.builder.authenticate_method_evidence(
                    node,
                    Some(MethodEvidenceOwner::Implementation(fact.id)),
                    None,
                    fact.id.method(),
                    application,
                    MethodEvidenceAnchorRole::ImplementationOwner {
                        implementation: fact.id,
                        binder: fact.binder,
                    },
                    None,
                )?;
            }
            function.set_node(node);
            let rewritten =
                clone_type_with_budget(&lowered.scheme.core_scheme, &mut self.type_work)
                    .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
            function.replace_type(rewritten);
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
                    let function_type =
                        ProvenancedTypeOwner::new(ProvenancedType::from_resolved_with_budget(
                            &equational.interface.annotation,
                            &mut self.type_work,
                        )?);
                    if !matches!(function_type.ty, Type::Function(_, _)) {
                        return Err(equation_interface_not_function(
                            &equational.interface.annotation,
                            &equational.equations.first().ok_or_else(invalid_state)?.name,
                            &self.registry,
                        ));
                    }
                    (
                        &equational.interface.name,
                        function_type.into_inner(),
                        equational.interface.type_parameters.as_ref(),
                        equational.interface.requirements.as_ref(),
                    )
                }
                ResolvedDefinitionKind::InlineOperational(operational) => {
                    let domain = ProvenancedTypeOwner::new(operational_domain(
                        &operational.header.parameters,
                        operational.header.span,
                        &mut self.type_work,
                    )?);
                    let codomain =
                        ProvenancedTypeOwner::new(ProvenancedType::from_resolved_with_budget(
                            &operational.header.result_type,
                            &mut self.type_work,
                        )?);
                    (
                        &operational.header.name,
                        ProvenancedType::function_with_budget(
                            domain.into_inner(),
                            codomain.into_inner(),
                            Some(operational.header.span),
                            &mut self.type_work,
                        )?,
                        operational.header.type_parameters.as_ref(),
                        operational.header.requirements.as_ref(),
                    )
                }
            };
            let function_type = ProvenancedTypeOwner::new(function_type);
            self.type_work
                .charge(type_parameters.len())
                .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
            let mut quantified = Vec::new();
            quantified
                .try_reserve(type_parameters.len())
                .map_err(|_| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
            for parameter in type_parameters {
                quantified.push((
                    parameter.id,
                    clone_kind_with_budget(&parameter.kind, &mut self.type_work).map_err(|()| {
                        TypeError::Internal(ElaborationFailure::TypeResourceExhausted)
                    })?,
                ));
            }
            let quantified = quantified.into_boxed_slice();
            let binder_body = IterativeTypeOwner::new(self.clone_type(&function_type.ty)?);
            let binder_type = if quantified.is_empty() {
                binder_body
            } else {
                self.type_work
                    .charge(1)
                    .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
                let binder_parameters =
                    clone_kinded_type_parameters_with_budget(&quantified, &mut self.type_work)
                        .map_err(|()| {
                            TypeError::Internal(ElaborationFailure::TypeResourceExhausted)
                        })?
                        .into_boxed_slice();
                IterativeTypeOwner::new(Type::Forall(
                    binder_parameters,
                    Box::new(binder_body.into_inner()),
                ))
            };
            let binder_type = if let Some(checked) = &checked_by_binder {
                let checked = checked.get(&name.id).ok_or_else(invalid_state)?;
                let requirements_match = checked.scheme.requirements.len() == requirements.len()
                    && checked.scheme.requirements.iter().zip(requirements).all(
                        |(checked, resolved)| {
                            checked.id == resolved.id
                                && checked.interface() == resolved.application.interface.id
                                && checked.arguments().len() == resolved.application.arguments.len()
                                && checked
                                    .arguments()
                                    .iter()
                                    .zip(&resolved.application.arguments)
                                    .all(|(checked, resolved)| same_type(checked, &resolved.ty))
                        },
                    );
                if checked.spelling != name.spelling
                    || !same_kinded_type_parameters_with_budget(
                        &checked.scheme.type_parameters,
                        &quantified,
                        &mut self.type_work,
                    )
                    .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?
                    || !same_type(&checked.scheme.value_type, &function_type.ty)
                    || !requirements_match
                {
                    return Err(invalid_state());
                }
                binder_type
            } else {
                binder_type
            };
            let binder_type = if self.purpose == ElaborationPurpose::FinalSynthesis {
                drop(binder_type);
                let lowered = self
                    .evidence_lowering
                    .as_ref()
                    .and_then(|lowering| lowering.global_schemes.get(&name.id))
                    .ok_or_else(invalid_state)?;
                if !same_kinded_type_parameters_with_budget(
                    &lowered.type_parameters,
                    &quantified,
                    &mut self.type_work,
                )
                .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?
                    || !same_type(&lowered.value_type, &function_type.ty)
                {
                    return Err(invalid_state());
                }
                IterativeTypeOwner::new(
                    clone_type_with_budget(&lowered.core_scheme, &mut self.type_work).map_err(
                        |()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted),
                    )?,
                )
            } else {
                binder_type
            };
            let binder = self.builder.resolved_binder(
                name.id,
                binder_type.into_inner(),
                Origin::Generated {
                    cause: Box::new(name.origin.clone()),
                    reason: GeneratedReason::BindingLowering,
                },
            )?;
            let ProvenancedType { ty, provenance } = function_type.into_inner();
            if context.insert_with_provenance(name.id, ty, provenance)?
                || global_binders.insert(name.id, binder).is_some()
            {
                return Err(invalid_state());
            }
            let context_quantified =
                clone_kinded_type_parameters_with_budget(&quantified, &mut self.type_work)
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
                    let function_type =
                        ProvenancedTypeOwner::new(ProvenancedType::from_resolved_with_budget(
                            &equational.interface.annotation,
                            &mut self.type_work,
                        )?);
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
                            function_type.into_inner(),
                            &mut prepared.context,
                            definition.span(),
                        )?,
                    )
                }
                ResolvedDefinitionKind::InlineOperational(operational) => {
                    let domain = ProvenancedTypeOwner::new(operational_domain(
                        &operational.header.parameters,
                        operational.header.span,
                        &mut self.type_work,
                    )?);
                    let codomain =
                        ProvenancedTypeOwner::new(ProvenancedType::from_resolved_with_budget(
                            &operational.header.result_type,
                            &mut self.type_work,
                        )?);
                    let function_type = ProvenancedType::function_with_budget(
                        domain.into_inner(),
                        codomain.into_inner(),
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
        })()
        .map(|(name, function)| (name, TypedNodeOwner::new(function)));
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
            function = TypedNodeOwner::new(self.wrap_lowered_evidence_scope(
                function.into_inner(),
                binders,
                &name.origin,
            )?);
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
                clone_kinded_type_parameters_with_budget(quantified, &mut self.type_work)
                    .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?
                    .into_boxed_slice();
            let scheme_body = self.clone_type(&function.ty)?;
            let scheme =
                IterativeTypeOwner::new(Type::Forall(scheme_parameters, Box::new(scheme_body)));
            let abstraction_parameters =
                clone_kinded_type_parameters_with_budget(quantified, &mut self.type_work)
                    .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
            let node = self.builder.type_abstraction(
                abstraction_parameters,
                function.node,
                scheme.into_inner(),
                Origin::Generated {
                    cause: Box::new(name.origin.clone()),
                    reason: GeneratedReason::TypeChecking,
                },
            )?;
            function.set_node(node);
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
        for (binder, quantified) in std::mem::take(&mut prepared.quantifiers) {
            prepared.context.set_quantified(binder, quantified)?;
        }
        self.monomorphic_recursive.clear();

        let globals = std::mem::take(&mut prepared.globals);
        let context = std::mem::take(&mut prepared.context);
        Ok((globals, context))
    }

    fn elaborate_result(
        &mut self,
        result_expression: &ResolvedExpr,
        context: &mut TypeContext,
    ) -> Result<TypedNode, TypeError> {
        let mut result = TypedNodeOwner::new(self.elaborate_expression_with_context(
            ElaborationTask::Synthesize {
                expression: result_expression,
                cause: Some(SynthesisCause::ProgramResult(result_expression.span)),
            },
            context,
        )?);
        let (zonked_result, result_is_ambiguous) = self.zonk_with_status(&result.ty)?;
        let zonked_result = IterativeTypeOwner::new(zonked_result);
        if result_is_ambiguous {
            return Err(inference_failure(
                TypeReason::AmbiguousType,
                result_expression.span,
                "this result does not determine every inferred type",
            ));
        }
        result.replace_type(zonked_result.into_inner());
        if !result.provenance.aligns(&result.ty) {
            let provenance = self.unknown_provenance(&result.ty)?;
            result.set_provenance(provenance);
        }
        let ambiguous = (0..self.next_inference).find(|identity| {
            !self
                .inference_solutions
                .contains_key(&InferenceVariableId::new(*identity))
        });
        if let Some(identity) = ambiguous {
            let origin = self
                .inference_variables
                .fact(InferenceVariableId::new(identity), &mut self.type_work)
                .map_err(inference_registry_error)?
                .origin;
            return Err(inference_failure(
                TypeReason::AmbiguousType,
                origin,
                "this expression does not determine every inferred type",
            ));
        }
        Ok(result.into_inner())
    }

    fn elaborate_expression_with_context<'a>(
        &mut self,
        initial: ElaborationTask<'a>,
        context: &mut TypeContext,
    ) -> Result<TypedNode, TypeError> {
        let mut tasks = ElaborationTaskBuffer(vec![initial]);
        let mut values = TypedNodeBuffer(Vec::new());
        #[cfg(test)]
        TEST_INITIAL_TYPED_NODES.with(|initial| {
            let mut initial = initial.borrow_mut();
            while let Some(node) = initial.pop() {
                values.push(node);
            }
        });
        let mut declarations = ElaboratedDeclarationBuffer(Vec::new());
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
                            let ty = IterativeTypeOwner::new(ty);
                            let arguments = OwnedTypeBuffer(arguments);
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
                                    let core_scheme = IterativeTypeOwner::new(
                                        self.clone_type(&scheme.core_scheme)?,
                                    );
                                    let variable_ty = self.clone_type(&core_scheme)?;
                                    let mut current = TypedNodeOwner::new(TypedNode {
                                        node: self.builder.variable(
                                            binder,
                                            variable_ty,
                                            occurrence.origin.clone(),
                                        )?,
                                        ty: core_scheme.into_inner(),
                                        provenance: provenance.clone(),
                                    });
                                    let mut current_arguments = OwnedTypeBuffer(Vec::new());
                                    self.type_work.charge(arguments.len()).map_err(|()| {
                                        TypeError::Internal(
                                            ElaborationFailure::TypeResourceExhausted,
                                        )
                                    })?;
                                    current_arguments.try_reserve(arguments.len()).map_err(
                                        |_| {
                                            TypeError::Internal(
                                                ElaborationFailure::TypeResourceExhausted,
                                            )
                                        },
                                    )?;
                                    for argument in arguments.iter() {
                                        current_arguments.push(self.clone_type(argument)?);
                                    }
                                    self.replay_lowered_global_determination(
                                        scheme,
                                        &current_arguments,
                                        occurrence,
                                        &lowering,
                                    )?;
                                    if !arguments.is_empty() {
                                        let core_ty = IterativeTypeOwner::new(
                                            self.instantiate_lowered_core_body(scheme, &arguments)?,
                                        );
                                        let application_ty = self.clone_type(&core_ty)?;
                                        let node = self.builder.type_application(
                                            current.node,
                                            arguments.into_vec(),
                                            application_ty,
                                            occurrence.origin.clone(),
                                        )?;
                                        current.set_node(node);
                                        current.replace_type(core_ty.into_inner());
                                    }
                                    let requirement_count = lowering
                                        .global_schemes
                                        .get(&binder)
                                        .ok_or_else(invalid_state)?
                                        .requirements
                                        .len();
                                    if occurrence.evidence.len() != requirement_count {
                                        return Err(invalid_state());
                                    }
                                    for (requirement_index, slot) in
                                        occurrence.evidence.iter().enumerate()
                                    {
                                        let selection =
                                            slot.selection().ok_or_else(invalid_state)?;
                                        let methods = self.lower_evidence_selection(
                                            selection,
                                            &mut lowering,
                                            &occurrence.origin,
                                            None,
                                            slot.storage_id(),
                                        )?;
                                        let target_requirement = lowering
                                            .global_schemes
                                            .get(&binder)
                                            .and_then(|scheme| {
                                                scheme.requirements.get(requirement_index)
                                            })
                                            .ok_or_else(invalid_state)?;
                                        if methods.len() != target_requirement.methods.len() {
                                            return Err(invalid_state());
                                        }
                                        for (method, target_method) in
                                            methods.iter().zip(&target_requirement.methods)
                                        {
                                            let target_application = self
                                                .instantiate_lowered_source_application(
                                                    lowering
                                                        .global_schemes
                                                        .get(&binder)
                                                        .ok_or_else(invalid_state)?
                                                        .binder_parameters(),
                                                    &target_method.application,
                                                    &current_arguments,
                                                )?;
                                            let canonical_method = lowering
                                                .interface_methods
                                                .get(&target_method.method)
                                                .ok_or_else(invalid_state)?;
                                            current =
                                                TypedNodeOwner::new(self.apply_lowered_argument(
                                                    current.into_inner(),
                                                    method,
                                                    target_requirement.owner,
                                                    target_requirement.id,
                                                    target_method,
                                                    &target_application,
                                                    canonical_method,
                                                    None,
                                                    &occurrence.origin,
                                                    slot.storage_id(),
                                                )?);
                                        }
                                    }
                                    if !same_type(&current.ty, &ty) {
                                        return Err(invalid_state());
                                    }
                                    current.set_provenance(provenance);
                                    Ok(current.into_inner())
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
                                        arguments.into_vec(),
                                        core_ty,
                                        occurrence.origin.clone(),
                                    )?;
                                }
                                values.push(TypedNode {
                                    node,
                                    ty: ty.into_inner(),
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
                                    cause,
                                )?);
                            }
                        }
                    },
                    ResolvedExprKind::Constructor(occurrence) => {
                        let constructor = self
                            .registry
                            .constructor(occurrence.constructor)
                            .ok_or_else(invalid_state)?;
                        let owner = self
                            .registry
                            .nominal(constructor.owner)
                            .ok_or_else(invalid_state)?;
                        if owner.declaration_kind == ResolvedNominalDeclarationKind::Newtype {
                            return Err(invalid_state());
                        }
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
                            Some(IterativeTypeOwner::new(
                                clone_type_with_budget(payload, &mut self.type_work).map_err(
                                    |()| {
                                        TypeError::Internal(
                                            ElaborationFailure::TypeResourceExhausted,
                                        )
                                    },
                                )?,
                            ))
                        } else {
                            None
                        };
                        let mut quantified = Vec::new();
                        quantified.try_reserve(parameter_count).map_err(|_| {
                            TypeError::Internal(ElaborationFailure::TypeResourceExhausted)
                        })?;
                        for parameter in parameters {
                            quantified.push((
                                parameter.id,
                                clone_kind_with_budget(&parameter.kind, &mut self.type_work)
                                    .map_err(|()| {
                                        TypeError::Internal(
                                            ElaborationFailure::TypeResourceExhausted,
                                        )
                                    })?,
                            ));
                        }
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
                            Type::apply_arguments(Type::Nominal(constructor.owner), arguments)
                        };
                        let scheme = IterativeTypeOwner::new(if let Some(payload) = payload {
                            Type::Function(Box::new(payload.into_inner()), Box::new(result))
                        } else {
                            result
                        });
                        let scheme_provenance =
                            self.at_span_provenance(&scheme, declaration_span)?;
                        let fact = TypeFactOwner::new(TypeFact {
                            ty: scheme.into_inner(),
                            provenance: scheme_provenance,
                            quantified: quantified.into_boxed_slice(),
                        });
                        let (ty, arguments) = self.instantiate(&fact, false, current.span)?;
                        let ty = IterativeTypeOwner::new(ty);
                        let arguments = OwnedTypeBuffer(arguments);
                        let TypeFact {
                            ty: fact_ty,
                            provenance: _,
                            quantified,
                        } = fact.into_inner();
                        let fact_ty = IterativeTypeOwner::new(fact_ty);
                        let core_scheme = if quantified.is_empty() {
                            fact_ty.into_inner()
                        } else {
                            self.type_work.charge(1).map_err(|()| {
                                TypeError::Internal(ElaborationFailure::TypeResourceExhausted)
                            })?;
                            Type::Forall(quantified, Box::new(fact_ty.into_inner()))
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
                                arguments.into_vec(),
                                core_ty,
                                occurrence.origin.clone(),
                            )?;
                        }
                        let provenance = self.at_span_provenance(&ty, declaration_span)?;
                        values.push(TypedNode {
                            node,
                            provenance,
                            ty: ty.into_inner(),
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
                            cause: Some(SynthesisCause::Application {
                                whole_span: current.span,
                                argument_span: application.argument.span,
                            }),
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
                        let domain = self.fresh_inference(&Kind::Type, current.span)?;
                        let codomain = self.fresh_inference(&Kind::Type, current.span)?;
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
                        let expected = ProvenancedTypeOwner::new(expected);
                        let expected = self.expose_expected_function(expected, expression.span)?;
                        let (domain_ty, codomain_ty) =
                            clone_function_parts_with_budget(&expected.ty, &mut self.type_work)
                                .map_err(|()| {
                                    TypeError::Internal(ElaborationFailure::TypeResourceExhausted)
                                })?;
                        let domain_ty = IterativeTypeOwner::new(domain_ty);
                        let codomain_ty = IterativeTypeOwner::new(codomain_ty);
                        let (domain_provenance, codomain_provenance) =
                            expected.provenance.function_parts(&expected.ty)?;
                        let domain = ProvenancedType {
                            ty: domain_ty.into_inner(),
                            provenance: domain_provenance,
                        };
                        let codomain = ProvenancedType {
                            ty: codomain_ty.into_inner(),
                            provenance: codomain_provenance,
                        };
                        tasks.push(ElaborationTask::CheckFunction {
                            parameter: &function.pattern,
                            domain,
                            codomain,
                            body: FunctionBody::Block(&function.body),
                            presentation: anonymous_function_origin(expression.span, function),
                            function_type: expected.into_inner(),
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
                    let expected = ProvenancedTypeOwner::new(expected);
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
                            let expected_ty = IterativeTypeOwner::new(self.zonk(&expected.ty)?);
                            let synthesized_ty =
                                IterativeTypeOwner::new(self.zonk(&synthesized.ty)?);
                            return Err(check_mismatch(
                                kind,
                                span,
                                expected_ty.into_inner(),
                                synthesized_ty.into_inner(),
                                expected.provenance.span(),
                                &self.registry,
                            ));
                        }
                        Err(UnificationFailure::Resource) => {
                            return Err(TypeError::Internal(
                                ElaborationFailure::TypeResourceExhausted,
                            ));
                        }
                        Err(UnificationFailure::Invariant) => return Err(invalid_state()),
                    }
                    let TypedNode {
                        node,
                        ty: synthesized_ty,
                        provenance,
                    } = synthesized.into_inner();
                    let ty = IterativeTypeOwner::new(self.zonk_owned(synthesized_ty)?);
                    self.builder
                        .record_type_check(node, expected.provenance.span())?;
                    values.push(TypedNode {
                        node,
                        ty: ty.into_inner(),
                        provenance,
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
                    let origin = OriginOwner::new(origin);
                    let mut pattern = CorePatternOwner::new(pattern);
                    let domain = domain.map(IterativeTypeOwner::new);
                    let ty = IterativeTypeOwner::new(ty);
                    let mut body = values.pop().ok_or_else(invalid_state)?;
                    if let Some(binder) = direct_binder
                        && !context.remove_and_discard(binder)
                    {
                        return Err(invalid_state());
                    }
                    self.remove_pattern_binders(context, &pattern_binders)?;
                    if pattern.0.is_some() {
                        let domain = domain.ok_or_else(invalid_state)?;
                        let pattern_span = pattern.origin.primary_span();
                        let mut matrix = CorePatternMatrixBuffer(vec![vec![
                            pattern.take().ok_or_else(invalid_state)?,
                        ]]);
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
                        let mut pattern = row.pop().ok_or_else(invalid_state)?;
                        if !row.is_empty() {
                            return Err(invalid_state());
                        }
                        let scrutinee_origin = OriginOwner::new(pattern.origin.clone());
                        let arm_origin = OriginOwner::new(pattern.origin.clone());
                        let match_origin = OriginOwner::new(pattern.origin.clone());
                        let core_body_type = IterativeTypeOwner::new(self.clone_type(&body.ty)?);
                        let scrutinee = self.builder.variable(
                            binder.id(),
                            domain.into_inner(),
                            scrutinee_origin.into_inner(),
                        )?;
                        let match_node = self.builder.match_expression(
                            scrutinee,
                            vec![CoreMatchArm::new(
                                pattern.take().ok_or_else(invalid_state)?,
                                body.node,
                                arm_origin.into_inner(),
                            )],
                            core_body_type.into_inner(),
                            match_origin.into_inner(),
                        )?;
                        body.set_node(match_node);
                    }
                    let core_ty = self.clone_type(&ty)?;
                    let node =
                        self.builder
                            .function(binder, body.node, core_ty, origin.into_inner())?;
                    values.push(TypedNode {
                        node,
                        ty: ty.into_inner(),
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
                    let source_function_ty = function.take_type();
                    let mut function_ty =
                        IterativeTypeOwner::new(self.zonk_owned(source_function_ty.into_inner())?);
                    if matches!(&*function_ty, Type::Inference(_)) {
                        self.type_work.charge(3).map_err(|()| {
                            TypeError::Internal(ElaborationFailure::TypeResourceExhausted)
                        })?;
                        let domain = self.fresh_inference(&Kind::Type, function_span)?;
                        let codomain = self.fresh_inference(&Kind::Type, function_span)?;
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
                                UnificationFailure::Invariant => invalid_state(),
                            })?;
                        let zonked = self.zonk(&exposed)?;
                        function_ty.replace(zonked);
                    }
                    let Type::Function(_, _) = &*function_ty else {
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
                    function.replace_type(function_ty.into_inner());
                    let domain = ProvenancedTypeOwner::new(ProvenancedType {
                        ty: domain_ty,
                        provenance: domain_provenance,
                    });
                    let codomain = ProvenancedTypeOwner::new(ProvenancedType {
                        ty: codomain_ty,
                        provenance: codomain_provenance,
                    });
                    tasks.push(ElaborationTask::FinishApplication {
                        whole_span,
                        function_span,
                        argument_span: argument.span,
                        function: function.into_inner(),
                        codomain: codomain.into_inner(),
                    });
                    tasks.push(ElaborationTask::Check {
                        expression: argument,
                        expected: domain.into_inner(),
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
                    let function = TypedNodeOwner::new(function);
                    let codomain = ProvenancedTypeOwner::new(codomain);
                    let argument = values.pop().ok_or_else(invalid_state)?;
                    let core_codomain = IterativeTypeOwner::new(self.clone_type(&codomain.ty)?);
                    let ProvenancedType {
                        ty: codomain_ty,
                        provenance: codomain_provenance,
                    } = codomain.into_inner();
                    let ty = IterativeTypeOwner::new(self.zonk_owned(codomain_ty)?);
                    let provenance = if codomain_provenance.aligns(&ty) {
                        codomain_provenance
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
                        core_codomain.into_inner(),
                        origin,
                    )?;
                    values.push(TypedNode {
                        node,
                        ty: ty.into_inner(),
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
                        left: left.into_inner(),
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
                    let left = TypedNodeOwner::new(left);
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
                    let expected = expected.map(ProvenancedTypeOwner::new);
                    let finish_expected = finish_expected.map(ProvenancedTypeOwner::new);
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
                        expected: finish_expected.map(ProvenancedTypeOwner::into_inner),
                        evidence_marker,
                    });
                    match (expected, binding.annotation.as_ref()) {
                        (Some(expected), Some(annotation)) => {
                            tasks.push(ElaborationTask::Check {
                                expression: &binding.initializer,
                                expected: expected.into_inner(),
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
                    let expected = expected.map(ProvenancedTypeOwner::new);
                    let mut initializer = values.pop().ok_or_else(invalid_state)?;
                    if let Some(marker) = evidence_marker {
                        self.close_evidence_obligations(marker)?;
                    }
                    let mut generalized = Vec::new();
                    if expected.is_none()
                        && matches!(binding.pattern.kind, ResolvedPatternKind::Binder(_))
                        && matches!(binding.initializer.kind, ResolvedExprKind::Function(_))
                    {
                        let inferred = IterativeTypeOwner::new(self.zonk(&initializer.ty)?);
                        let mut variables =
                            collect_unsolved_inference(&inferred, &mut self.type_work).map_err(
                                |()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted),
                            )?;
                        let mut environment_variables = HashSet::new();
                        for fact in context.binders.values() {
                            let ty = IterativeTypeOwner::new(self.zonk(&fact.ty)?);
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
                        let (retained, zonked) =
                            self.generalize_inference_variables(&variables, &initializer.ty)?;
                        generalized = retained;
                        initializer.replace_type(zonked);
                    }
                    let mut binding_type =
                        ProvenancedTypeOwner::new(if let Some(expected) = expected {
                            expected.into_inner()
                        } else {
                            let TypedNode {
                                node,
                                ty,
                                provenance,
                            } = initializer.into_inner();
                            initializer = TypedNodeOwner::new(TypedNode {
                                node,
                                ty: Type::Unit,
                                provenance: TypeProvenance::atom(None),
                            });
                            ProvenancedType { ty, provenance }
                        });
                    let mut binder_ids = Vec::new();
                    let checked = self.check_core_pattern(
                        &binding.pattern,
                        &binding_type.ty,
                        context,
                        &mut binder_ids,
                        GeneratedReason::BindingLowering,
                    )?;
                    let mut pattern = CorePatternOwner::new(Some(checked.pattern));
                    if checked.inference_changed {
                        let rewritten = clone_type_with_budget(&pattern.ty, &mut self.type_work)
                            .map_err(|()| {
                                TypeError::Internal(ElaborationFailure::TypeResourceExhausted)
                            })?;
                        binding_type.replace_type(rewritten);
                        if !binding_type.provenance.aligns(&binding_type.ty) {
                            let provenance = self.unknown_provenance(&binding_type.ty)?;
                            binding_type.set_provenance(provenance);
                        }
                    }
                    let mut matrix = CorePatternMatrixBuffer(vec![vec![
                        pattern.take().ok_or_else(invalid_state)?,
                    ]]);
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
                    match pattern.into_inner() {
                        CorePattern {
                            ty,
                            origin: pattern_origin,
                            kind: CorePatternKind::Binder(mut binder),
                        } => {
                            discard_type_iteratively(ty);
                            discard_origin_iteratively(pattern_origin);
                            let quantified = generalized.into_boxed_slice();
                            let context_quantified = clone_kinded_type_parameters_with_budget(
                                &quantified,
                                &mut self.type_work,
                            )
                            .map_err(|()| {
                                TypeError::Internal(ElaborationFailure::TypeResourceExhausted)
                            })?
                            .into_boxed_slice();
                            let abstraction = if quantified.is_empty() {
                                None
                            } else {
                                self.type_work.charge(1).map_err(|()| {
                                    TypeError::Internal(ElaborationFailure::TypeResourceExhausted)
                                })?;
                                let scheme_body = self.clone_type(&binding_type.ty)?;
                                let scheme = IterativeTypeOwner::new(Type::Forall(
                                    quantified,
                                    Box::new(scheme_body),
                                ));
                                let binder_scheme =
                                    IterativeTypeOwner::new(self.clone_type(&scheme)?);
                                let abstraction_parameters = match &*scheme {
                                    Type::Forall(parameters, _) => {
                                        clone_kinded_type_parameters_with_budget(
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
                                binder.replace_type(binder_scheme.into_inner());
                                let node = self.builder.type_abstraction(
                                    abstraction_parameters,
                                    initializer.node,
                                    scheme.into_inner(),
                                    Origin::Generated {
                                        cause: Box::new(origin.clone()),
                                        reason: GeneratedReason::TypeChecking,
                                    },
                                )?;
                                initializer.set_node(node);
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
                        if context.insert_with_provenance(
                            member.binder.id,
                            expected.ty,
                            expected.provenance,
                        )? {
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
                    let mut initializers = values.split_off(value_start);
                    self.type_work.charge(group.members.len()).map_err(|()| {
                        TypeError::Internal(ElaborationFailure::TypeResourceExhausted)
                    })?;
                    let mut members = Vec::new();
                    members.try_reserve(group.members.len()).map_err(|_| {
                        TypeError::Internal(ElaborationFailure::TypeResourceExhausted)
                    })?;
                    initializers.reverse();
                    for member in &group.members {
                        let initializer = initializers.pop().ok_or_else(invalid_state)?;
                        let TypedNode {
                            node: initializer_node,
                            ty: initializer_ty,
                            provenance: _,
                        } = initializer.into_inner();
                        let binder = self.builder.resolved_binder(
                            member.binder.id,
                            initializer_ty,
                            Origin::Generated {
                                cause: Box::new(member.binder.origin.clone()),
                                reason: GeneratedReason::BindingLowering,
                            },
                        )?;
                        members.push((binder, initializer_node));
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
                    let expected = expected
                        .map(|(expected, kind)| (ProvenancedTypeOwner::new(expected), kind));
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
                        scrutinee: scrutinee.into_inner(),
                        next_arm: 0,
                        matrix,
                        arm_bodies,
                        result_type: expected.map(|(expected, kind)| {
                            let ProvenancedType { ty, provenance } = expected.into_inner();
                            (ty, provenance, kind)
                        }),
                    });
                    self.schedule_match_arm(progress, context, &mut tasks)?;
                }
                ElaborationTask::FinishMatchArm {
                    progress,
                    binders,
                    row,
                    arm_span,
                } => {
                    let mut progress = MatchProgressOwner::new(progress);
                    let row = CorePatternBuffer(row);
                    let body = values.pop().ok_or_else(invalid_state)?;
                    self.remove_pattern_binders(context, &binders)?;
                    let body_node = body.node;
                    if progress.result_type.is_none() {
                        let TypedNode { ty, provenance, .. } = body.into_inner();
                        progress.set_result_type(
                            ProvenancedTypeOwner::new(ProvenancedType { ty, provenance }),
                            CheckKind::General,
                        )?;
                    }
                    progress.push_row(row.into_vec());
                    progress.push_arm_body((body_node, arm_span));
                    self.schedule_match_arm(progress.into_inner(), context, &mut tasks)?;
                }
                ElaborationTask::FinishMatch(progress) => {
                    let mut progress = MatchProgressOwner::new(progress);
                    let Some((result_type, _)) = progress.take_result_type() else {
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
                    let matrix = progress.take_matrix();
                    let arm_bodies = progress.take_arm_bodies();
                    for (row, (body, arm_span)) in matrix.into_sequence().zip(arm_bodies) {
                        let mut row = CorePatternBuffer(row);
                        let mut pattern = row.pop().ok_or_else(invalid_state)?;
                        if !row.is_empty() {
                            return Err(invalid_state());
                        }
                        arms.push(CoreMatchArm::new(
                            pattern.take().ok_or_else(invalid_state)?,
                            body,
                            Origin::Source(arm_span),
                        ));
                    }
                    let core_ty = self.clone_type(&result_type.ty)?;
                    let node = self.builder.match_expression(
                        progress.scrutinee.node,
                        arms,
                        core_ty,
                        Origin::Source(progress.span),
                    )?;
                    let ProvenancedType { ty, provenance } = result_type.into_inner();
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
                    let mut retained_declarations = declarations.split_off(declaration_start);
                    while !retained_declarations.is_empty() {
                        let core_body_type = self.clone_type(&body.ty)?;
                        let declaration = retained_declarations.pop().ok_or_else(invalid_state)?;
                        let node = match declaration.into_inner() {
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
                        body.set_node(node);
                    }
                    for declaration in source_declarations {
                        match declaration {
                            ResolvedLocalDeclaration::Binding(binding) => {
                                let mut ids = Vec::new();
                                collect_pattern_binders(&binding.pattern, &mut ids);
                                for id in ids {
                                    if !context.remove_and_discard(id) {
                                        return Err(invalid_state());
                                    }
                                }
                            }
                            ResolvedLocalDeclaration::Recursive(group) => {
                                for member in &group.members {
                                    if !context.remove_and_discard(member.binder.id) {
                                        return Err(invalid_state());
                                    }
                                }
                            }
                        }
                    }
                    values.push(body.into_inner());
                }
            }
        }
        let result = values.pop().ok_or_else(invalid_state)?;
        if values.is_empty() && result.provenance.aligns(&result.ty) {
            Ok(result.into_inner())
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
        let mut types = OwnedTypeBuffer(Vec::with_capacity(elements.len()));
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
        let ty = IterativeTypeOwner::new(Type::Tuple(types.into_boxed_slice()));
        let core_ty = self.clone_type(&ty)?;
        let node = self.builder.tuple(nodes, core_ty, Origin::Source(span))?;
        Ok(TypedNode {
            node,
            provenance: TypeProvenance::atom(Some(span)),
            ty: ty.into_inner(),
        })
    }

    fn schedule_match_arm<'a>(
        &mut self,
        progress: Box<MatchProgress<'a>>,
        context: &mut TypeContext,
        tasks: &mut ElaborationTaskBuffer<'a>,
    ) -> Result<(), TypeError> {
        let mut progress = MatchProgressOwner::new(progress);
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
            tasks.push(ElaborationTask::FinishMatch(progress.into_inner()));
            return Ok(());
        };

        self.type_work
            .charge(1)
            .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
        let mut row = CorePatternBuffer(Vec::new());
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
        let mut pattern = CorePatternOwner::new(Some(checked.pattern));
        if checked.inference_changed {
            let rewritten = clone_type_with_budget(&pattern.ty, &mut self.type_work)
                .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
            progress.replace_scrutinee_type(rewritten);
            if !progress.scrutinee.provenance.aligns(&progress.scrutinee.ty) {
                let provenance = self.unknown_provenance(&progress.scrutinee.ty)?;
                progress.set_scrutinee_provenance(provenance);
            }
        }
        row.push(pattern.take().ok_or_else(invalid_state)?);
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
        progress.advance_arm();
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
            progress: progress.into_inner(),
            binders,
            row: row.into_vec(),
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
        let (expected, mut inference_changed) = if let Type::Inference(identity) = expected {
            let zonked = self.zonk(expected)?;
            let changed = !matches!(&zonked, Type::Inference(zonked) if *zonked == *identity);
            (zonked, changed)
        } else {
            self.charge_type(expected)?;
            (expected.clone(), false)
        };
        let mut expected = IterativeTypeOwner::new(expected);
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
                    (*expected).clone(),
                    Origin::Generated {
                        cause: Box::new(binder.origin.clone()),
                        reason: binder_reason,
                    },
                )?;
                if context.insert_with_provenance(
                    binder.id,
                    (*expected).clone(),
                    // `charge_pattern_binder_storage` reserves this tree
                    // before the binder and context entries are retained.
                    TypeProvenance::unknown(&expected),
                )? {
                    return Err(invalid_state());
                }
                binders.push(binder.id);
                CorePatternKind::Binder(typed)
            }
            ResolvedPatternKind::Wildcard => CorePatternKind::Wildcard,
            ResolvedPatternKind::Boolean(value) => {
                if matches!(&*expected, Type::Inference(_)) {
                    let refined =
                        self.refine_pattern_expected(&expected, &Type::Bool, pattern.span)?;
                    expected.replace(refined);
                    inference_changed = true;
                } else if !matches!(&*expected, Type::Bool) {
                    return Err(pattern_mismatch(pattern.span, &expected, &self.registry));
                }
                CorePatternKind::Boolean(*value)
            }
            ResolvedPatternKind::Unit => {
                if matches!(&*expected, Type::Inference(_)) {
                    let refined =
                        self.refine_pattern_expected(&expected, &Type::Unit, pattern.span)?;
                    expected.replace(refined);
                    inference_changed = true;
                } else if !matches!(&*expected, Type::Unit) {
                    return Err(pattern_mismatch(pattern.span, &expected, &self.registry));
                }
                CorePatternKind::Unit
            }
            ResolvedPatternKind::Tuple(patterns) => {
                if matches!(&*expected, Type::Inference(_)) {
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
                        types.push(self.fresh_inference(&Kind::Type, pattern.span)?);
                    }
                    let required = Type::Tuple(types.into_boxed_slice());
                    let refined =
                        self.refine_pattern_expected(&expected, &required, pattern.span)?;
                    expected.replace(refined);
                    inference_changed = true;
                }
                let Type::Tuple(types) = &*expected else {
                    return Err(pattern_mismatch(pattern.span, &expected, &self.registry));
                };
                if patterns.len() != types.len() {
                    return Err(pattern_mismatch(pattern.span, &expected, &self.registry));
                }
                let mut checked = CorePatternBuffer(Vec::new());
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
                if rebuild_expected {
                    let zonked = self.zonk(&expected)?;
                    expected.replace(zonked);
                    rebuild_expected = false;
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
                    expected.into_inner(),
                    context,
                    binders,
                    binder_reason,
                    inference_changed,
                );
            }
        };
        debug_assert!(!rebuild_expected);
        Ok(CheckedPattern {
            pattern: CorePattern::new(expected.into_inner(), Origin::Source(pattern.span), kind),
            inference_changed,
        })
    }

    #[allow(clippy::too_many_arguments)]
    fn check_core_constructor_pattern(
        &mut self,
        whole_pattern: &ResolvedPattern,
        constructor: crate::types::ConstructorId,
        payload: Option<&ResolvedPattern>,
        expected: Type,
        context: &mut TypeContext,
        binders: &mut Vec<BinderId>,
        binder_reason: GeneratedReason,
        mut inference_changed: bool,
    ) -> Result<CheckedPattern, TypeError> {
        let mut expected = IterativeTypeOwner::new(expected);
        let Some(info) = self.registry.constructor(constructor) else {
            return Err(invalid_state());
        };
        let owner = self
            .registry
            .nominal(info.owner)
            .ok_or_else(invalid_state)?;
        if owner.declaration_kind == ResolvedNominalDeclarationKind::Newtype {
            return Err(invalid_state());
        }
        let info_owner = info.owner;
        if let Some(payload) = &info.payload {
            charge_type_cells(payload, &mut self.type_work)
                .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
        }
        let declared_payload = info.payload.clone().map(IterativeTypeOwner::new);
        if matches!(&*expected, Type::Inference(_)) {
            let parameter_count = self
                .registry
                .nominal_parameters(info_owner)
                .ok_or_else(invalid_state)?
                .len();
            self.type_work
                .charge(parameter_count.saturating_add(1))
                .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
            let inference_marker = self.inference_variables.len();
            let next_inference = self.next_inference;
            let refinement = (|| {
                let required = IterativeTypeOwner::new(if parameter_count == 0 {
                    Type::Nominal(info_owner)
                } else {
                    let mut arguments = Vec::new();
                    arguments.try_reserve(parameter_count).map_err(|_| {
                        TypeError::Internal(ElaborationFailure::TypeResourceExhausted)
                    })?;
                    let parameters = self
                        .registry
                        .nominal_parameters(info_owner)
                        .ok_or_else(invalid_state)?;
                    for parameter in parameters {
                        arguments.push(allocate_inference_variable(
                            &mut self.next_inference,
                            &mut self.inference_variables,
                            &mut self.type_work,
                            &parameter.kind,
                            whole_pattern.span,
                        )?);
                    }
                    Type::apply_arguments(Type::Nominal(info_owner), arguments)
                });
                self.refine_pattern_expected(&expected, &required, whole_pattern.span)
            })();
            let refined = match refinement {
                Ok(refined) => refined,
                Err(error) => {
                    self.inference_variables.truncate(inference_marker);
                    self.next_inference = next_inference;
                    return Err(error);
                }
            };
            expected.replace(refined);
            inference_changed = true;
        }
        let Some(owner) = expected.outer_nominal() else {
            return Err(pattern_mismatch(
                whole_pattern.span,
                &expected,
                &self.registry,
            ));
        };
        let mut arguments = Vec::new();
        let mut current: &Type = &expected;
        while let Type::Application(function, argument) = current {
            self.type_work
                .charge(1)
                .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
            arguments
                .try_reserve(1)
                .map_err(|_| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
            arguments.push(argument.as_ref());
            current = function;
        }
        arguments.reverse();
        let parameters = self
            .registry
            .nominal_parameters(owner)
            .ok_or_else(invalid_state)?;
        if parameters.len() != arguments.len() {
            return Err(invalid_state());
        }
        let replacements =
            constructor_replacements_with_budget(parameters, &arguments, &mut self.type_work)
                .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
        let payload_type = declared_payload
            .as_ref()
            .map(|payload| {
                substitute_type_variables_with(payload, replacements.as_map(), |cells| {
                    self.type_work.charge(cells)
                })
                .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))
            })
            .transpose()?
            .map(IterativeTypeOwner::new);
        if info_owner != owner {
            return Err(case_error(
                TypeReason::ConstructorOwner,
                whole_pattern.span,
                "this constructor belongs to another nominal type",
                None,
            ));
        }
        let checked_payload = match (payload, payload_type.as_deref()) {
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
                let outcome_inference_changed = outcome.inference_changed;
                let mut outcome_pattern = CorePatternBuffer(vec![outcome.pattern]);
                if outcome_inference_changed {
                    let zonked = self.zonk(&expected)?;
                    expected.replace(zonked);
                    inference_changed = true;
                }
                Some(Box::new(
                    outcome_pattern
                        .pop()
                        .expect("one checked constructor payload pattern")
                        .into_inner(),
                ))
            }
            _ => return Err(constructor_mismatch(whole_pattern.span)),
        };
        Ok(CheckedPattern {
            pattern: CorePattern::new(
                expected.into_inner(),
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
            if !context.remove_and_discard(*binder) {
                return Err(invalid_state());
            }
        }
        Ok(())
    }

    fn schedule_function_check<'a>(
        &mut self,
        context: &mut TypeContext,
        tasks: &mut ElaborationTaskBuffer<'a>,
        binding_start: usize,
        check: FunctionCheck<'a>,
    ) -> Result<(), TypeError> {
        let FunctionCheck {
            parameter,
            domain,
            codomain,
            body,
            presentation,
            function_type,
            body_check,
        } = check;
        let presentation = OriginOwner::new(presentation);
        let mut domain = ProvenancedTypeOwner::new(domain);
        let mut codomain = ProvenancedTypeOwner::new(codomain);
        let mut function_type = ProvenancedTypeOwner::new(function_type);
        let mut pattern_binders = Vec::new();
        let (mut checked_pattern, inference_changed) =
            if matches!(&parameter.kind, ResolvedPatternKind::Binder(_)) {
                (CorePatternOwner::new(None), false)
            } else {
                let checked = self.check_core_pattern(
                    parameter,
                    &domain.ty,
                    context,
                    &mut pattern_binders,
                    GeneratedReason::FunctionLowering,
                )?;
                (
                    CorePatternOwner::new(Some(checked.pattern)),
                    checked.inference_changed,
                )
            };
        if inference_changed {
            let zonked = self.zonk(&domain.ty)?;
            domain.replace_type(zonked);
            if !domain.provenance.aligns(&domain.ty) {
                let provenance = self.unknown_provenance(&domain.ty)?;
                domain.set_provenance(provenance);
            }
            let zonked = self.zonk(&codomain.ty)?;
            codomain.replace_type(zonked);
            if !codomain.provenance.aligns(&codomain.ty) {
                let provenance = self.unknown_provenance(&codomain.ty)?;
                codomain.set_provenance(provenance);
            }
            let zonked = self.zonk(&function_type.ty)?;
            function_type.replace_type(zonked);
            if !function_type.provenance.aligns(&function_type.ty) {
                let provenance = self.unknown_provenance(&function_type.ty)?;
                function_type.set_provenance(provenance);
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
                let context_type = IterativeTypeOwner::new(self.clone_type(&domain.ty)?);
                let ProvenancedType {
                    ty: binder_type,
                    provenance: domain_provenance,
                } = domain.into_inner();
                let binder = self.builder.resolved_binder(
                    source_binder.id,
                    binder_type,
                    Origin::Generated {
                        cause: Box::new(source_binder.origin.clone()),
                        reason: GeneratedReason::FunctionLowering,
                    },
                )?;
                if context.insert_with_provenance(
                    source_binder.id,
                    context_type.into_inner(),
                    domain_provenance,
                )? {
                    return Err(invalid_state());
                }
                (binder, None, None, Some(source_binder.id))
            } else {
                let binder_type = self.clone_type(&domain.ty)?;
                let binder = self.builder.binder(
                    binder_type,
                    Origin::Generated {
                        cause: Box::new(Origin::Source(parameter.span)),
                        reason: GeneratedReason::FunctionLowering,
                    },
                )?;
                let pattern = checked_pattern.take().ok_or_else(invalid_state)?;
                let ProvenancedType {
                    ty: domain_ty,
                    provenance: _,
                } = domain.into_inner();
                (binder, Some(pattern), Some(domain_ty), None)
            };
        let origin = Origin::Generated {
            cause: Box::new(presentation.into_inner()),
            reason: GeneratedReason::FunctionLowering,
        };
        let function_type = function_type.into_inner();
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
                Some((codomain.into_inner(), body_check)),
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
        let function_type = ProvenancedTypeOwner::new(function_type);
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
        let mut remainder = ProvenancedTypeOwner::new(ProvenancedType {
            ty: self.clone_type(&function_type.ty)?,
            provenance: function_type.provenance.clone(),
        });
        self.type_work
            .charge(arity.saturating_mul(2))
            .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
        let mut domains = ProvenancedTypeBuffer(Vec::new());
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
            let (domain, codomain) = remainder.into_inner().into_function_parts()?;
            domains.push(domain);
            remainder = ProvenancedTypeOwner::new(codomain);
        }

        let mut parameters = Vec::new();
        parameters
            .try_reserve(arity)
            .map_err(|_| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
        for domain in domains.iter() {
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
        let mut domain_types = OwnedTypeBuffer(Vec::new());
        domain_types
            .try_reserve(arity)
            .map_err(|_| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
        for domain in domains.iter() {
            domain_types.push(self.clone_type(&domain.ty)?);
        }

        self.type_work
            .charge(equations.len().saturating_mul(2))
            .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
        let mut coverage_matrix = CorePatternMatrixBuffer(Vec::new());
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
            let mut patterns = CorePatternBuffer(Vec::new());
            patterns
                .try_reserve(arity)
                .map_err(|_| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
            for (pattern, domain) in clause.patterns.iter().zip(domains.iter()) {
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
            let body_result = self
                .elaborate_expression_with_context(
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
                )
                .map(TypedNodeOwner::new);
            self.remove_pattern_binders(context, &binder_ids)?;
            let body = body_result?;
            coverage_matrix.push(patterns.into_vec());
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
            let (ty, origin, parameter) = match pattern.into_inner() {
                CorePattern {
                    ty,
                    origin,
                    kind: CorePatternKind::Binder(parameter),
                } => (ty, origin, parameter),
                pattern => {
                    pattern.discard_iteratively();
                    return Err(invalid_state());
                }
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
            for (patterns, (body, clause_span)) in
                coverage_matrix.into_sequence().zip(clause_bodies)
            {
                let mut patterns = CorePatternBuffer(patterns);
                let arm_pattern = if patterns.len() == 1 {
                    patterns.pop().ok_or_else(invalid_state)?.into_inner()
                } else {
                    self.type_work.charge(1).map_err(|()| {
                        TypeError::Internal(ElaborationFailure::TypeResourceExhausted)
                    })?;
                    let mut tuple_domains = OwnedTypeBuffer(Vec::new());
                    tuple_domains.try_reserve(arity).map_err(|_| {
                        TypeError::Internal(ElaborationFailure::TypeResourceExhausted)
                    })?;
                    for domain in domains.iter() {
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
            for (parameter, domain) in parameters.iter().zip(domains.iter()) {
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
                let mut tuple_domains = OwnedTypeBuffer(Vec::new());
                tuple_domains
                    .try_reserve(domain_types.len())
                    .map_err(|_| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
                for domain in domain_types.iter() {
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
        let mut body_type = IterativeTypeOwner::new(self.clone_type(&remainder.ty)?);
        for (parameter, domain) in parameters.into_iter().zip(domains.iter()).rev() {
            self.type_work
                .charge(1)
                .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
            let domain_type = self.clone_type(&domain.ty)?;
            let ty = IterativeTypeOwner::new(Type::Function(
                Box::new(domain_type),
                Box::new(body_type.into_inner()),
            ));
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
        let ProvenancedType {
            ty: original_function_type,
            provenance,
        } = function_type.into_inner();
        discard_type_iteratively(original_function_type);
        Ok(TypedNode {
            node: body_node,
            ty: body_type.into_inner(),
            provenance,
        })
    }

    fn elaborate_operational_function(
        &mut self,
        operational: &crate::resolved::ResolvedInlineOperationalGlobal,
        function_type: ProvenancedType,
        context: &mut TypeContext,
        definition_span: Span,
    ) -> Result<TypedNode, TypeError> {
        let function_type = ProvenancedTypeOwner::new(function_type);
        let (domain_ty, codomain_ty) =
            clone_function_parts_with_budget(&function_type.ty, &mut self.type_work)
                .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
        let domain_ty = IterativeTypeOwner::new(domain_ty);
        let codomain_ty = IterativeTypeOwner::new(codomain_ty);
        let (domain_provenance, codomain_provenance) =
            function_type.provenance.function_parts(&function_type.ty)?;
        let domain = ProvenancedTypeOwner::new(ProvenancedType {
            ty: domain_ty.into_inner(),
            provenance: domain_provenance,
        });
        let codomain = ProvenancedTypeOwner::new(ProvenancedType {
            ty: codomain_ty.into_inner(),
            provenance: codomain_provenance,
        });
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
            let mut elements = CorePatternBuffer(Vec::new());
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
        let mut checked_pattern = CorePatternOwner::new(Some(pattern));
        let pattern = checked_pattern
            .take()
            .expect("one checked operational pattern");
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
                let mut pattern = CorePatternOwner::new(Some(pattern));
                let binder_type = self.clone_type(&domain.ty)?;
                let binder = self
                    .builder
                    .binder(binder_type, Origin::Source(operational.header.span))?;
                (binder, pattern.take())
            }
        };
        let mut retained_pattern = CorePatternOwner::new(retained_pattern);
        let body_result = self
            .elaborate_expression_with_context(
                ElaborationTask::CheckBlock {
                    block: &operational.body,
                    expected: codomain.into_inner(),
                    kind: CheckKind::Definition {
                        result_cause: operational.header.result_type.span,
                    },
                },
                context,
            )
            .map(TypedNodeOwner::new);
        self.remove_pattern_binders(context, &binder_ids)?;
        let mut body = body_result?;
        if let Some(pattern) = retained_pattern.take() {
            let mut matrix = CorePatternMatrixBuffer(vec![vec![pattern]]);
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
            let mut pattern = row.pop().ok_or_else(invalid_state)?;
            if !row.is_empty() {
                return Err(invalid_state());
            }
            let scrutinee_type = self.clone_type(&domain.ty)?;
            let scrutinee = self.builder.variable(
                parameter.id(),
                scrutinee_type,
                Origin::Source(operational.header.span),
            )?;
            let core_body_type = IterativeTypeOwner::new(self.clone_type(&body.ty)?);
            let node = self.builder.match_expression(
                scrutinee,
                vec![CoreMatchArm::new(
                    pattern.take().ok_or_else(invalid_state)?,
                    body.node,
                    Origin::Source(operational.header.span),
                )],
                core_body_type.into_inner(),
                Origin::Source(operational.header.span),
            )?;
            body.set_node(node);
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
        let function_type = function_type.into_inner();
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
    preflight_application_arities(module, budget)?;
    budget
        .charge(module.interfaces().len())
        .map_err(|()| constraint_resource())?;
    let mut checked = Vec::new();
    checked
        .try_reserve(module.interfaces().len())
        .map_err(|_| constraint_resource())?;
    for (source_index, interface) in module.interfaces().iter().enumerate() {
        budget.charge(1).map_err(|()| constraint_resource())?;
        if interface.parameters.is_empty() {
            return Err(invalid_state());
        }
        let determination = match &interface.determination {
            Some(source) => Some(check_determination_key(interface, source, budget)?),
            None => None,
        };
        checked.push(CheckedInterface::new(
            source_index,
            interface.id,
            determination,
        ));
    }

    for (interface, checked_interface) in module.interfaces().iter().zip(&checked) {
        let determinant_positions = checked_interface.determinant_positions();
        for method in &interface.methods {
            budget
                .charge(method.type_parameters.len().saturating_add(1))
                .map_err(|()| constraint_resource())?;
            let invalid_binder_state =
                !method.has_explicit_type_parameters && !method.type_parameters.is_empty();
            let mut missing_parameter = None;
            if let Some(positions) = determinant_positions {
                for position in positions {
                    let parameter = interface
                        .parameters
                        .get(*position)
                        .ok_or_else(invalid_state)?;
                    if !type_contains_variable(&method.annotation.ty, parameter.id, budget)
                        .map_err(|()| constraint_resource())?
                    {
                        missing_parameter = Some(parameter);
                        break;
                    }
                }
            } else {
                for parameter in &interface.parameters {
                    if !type_contains_variable(&method.annotation.ty, parameter.id, budget)
                        .map_err(|()| constraint_resource())?
                    {
                        missing_parameter = Some(parameter);
                        break;
                    }
                }
            }
            if invalid_binder_state || missing_parameter.is_some() {
                let mut diagnostic = Diagnostic::new(
                    InterfaceReason::MethodParameter,
                    SourceLabel::new(
                        method.span,
                        "this method signature must use its interface parameter and only declared type parameters",
                    ),
                );
                diagnostic.related.push(SourceLabel::new(
                    missing_parameter
                        .or_else(|| {
                            determinant_positions
                                .and_then(|positions| positions.first())
                                .and_then(|position| interface.parameters.get(*position))
                        })
                        .or_else(|| interface.parameters.first())
                        .ok_or_else(invalid_state)?
                        .origin
                        .primary_span(),
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
    }
    Ok(checked.into_boxed_slice())
}

fn preflight_application_arities(
    module: &ResolvedModule,
    budget: &mut InterfaceConstraintBudget,
) -> Result<(), TypeError> {
    if module.definitions().is_empty() && module.implementations().is_empty() {
        return Ok(());
    }
    let interface_count = module
        .interfaces()
        .len()
        .checked_add(module.imported_facts().interface_imports().count())
        .ok_or_else(constraint_resource)?;
    budget
        .charge(interface_count)
        .map_err(|()| constraint_resource())?;
    let mut interfaces = HashMap::new();
    interfaces
        .try_reserve(interface_count)
        .map_err(|_| constraint_resource())?;
    for interface in module.interfaces() {
        if interfaces
            .insert(interface.id, (interface.parameters.len(), interface.span))
            .is_some()
        {
            return Err(invalid_state());
        }
    }
    for imported in module.imported_facts().interface_imports() {
        if interfaces
            .insert(
                imported.fact.id,
                (imported.fact.parameters.len(), imported.fact.span),
            )
            .is_some()
        {
            return Err(invalid_state());
        }
    }

    let check = |application: &crate::resolved::ResolvedInterfaceApplication,
                 budget: &mut InterfaceConstraintBudget| {
        budget.charge(1).map_err(|()| constraint_resource())?;
        let (expected, declaration_span) = interfaces
            .get(&application.interface.id)
            .copied()
            .ok_or_else(invalid_state)?;
        check_application_arity_parts(
            expected,
            declaration_span,
            application.arguments.len(),
            application.span,
        )
    };
    for declaration in module.declaration_order() {
        budget.charge(1).map_err(|()| constraint_resource())?;
        match *declaration {
            ResolvedDeclarationIndex::Type(_) | ResolvedDeclarationIndex::Interface(_) => {}
            ResolvedDeclarationIndex::Global(index) => {
                let definition = module.definitions().get(index).ok_or_else(invalid_state)?;
                let requirements = match &definition.kind {
                    ResolvedDefinitionKind::Equational(global) => &global.interface.requirements,
                    ResolvedDefinitionKind::InlineOperational(global) => {
                        &global.header.requirements
                    }
                };
                for requirement in requirements.iter() {
                    check(&requirement.application, budget)?;
                }
            }
            ResolvedDeclarationIndex::Implementation(index) => {
                let implementation = module
                    .implementations()
                    .get(index)
                    .ok_or_else(invalid_state)?;
                check(&implementation.head, budget)?;
                for prerequisite in &implementation.prerequisites {
                    check(&prerequisite.application, budget)?;
                }
            }
        }
    }
    Ok(())
}

fn check_determination_key(
    interface: &crate::resolved::ResolvedInterfaceDeclaration,
    determination: &crate::resolved::ResolvedInterfaceDetermination,
    budget: &mut InterfaceConstraintBudget,
) -> Result<DeterminationKey, TypeError> {
    let structurally_total = crate::resolved::resolved_determination_is_total(
        &interface.parameters,
        determination,
        |work| budget.charge(work),
    )
    .map_err(|()| constraint_resource())?;
    if determination.determinant.parameters.is_empty() {
        return Err(determination_parameter_error(
            determination.determinant.span,
            "the determinant key must contain an interface parameter",
            interface.parameters.first().map(|parameter| {
                (
                    parameter.origin.primary_span(),
                    "an interface parameter is declared here",
                )
            }),
            budget,
        )?);
    }
    if determination.dependent.parameters.is_empty() {
        return Err(determination_parameter_error(
            determination.dependent.span,
            "the dependent complement must contain an interface parameter",
            interface.parameters.first().map(|parameter| {
                (
                    parameter.origin.primary_span(),
                    "an interface parameter is declared here",
                )
            }),
            budget,
        )?);
    }

    let occurrence_count = determination
        .determinant
        .parameters
        .len()
        .checked_add(determination.dependent.parameters.len())
        .ok_or_else(constraint_resource)?;
    budget
        .charge(occurrence_count)
        .map_err(|()| constraint_resource())?;
    let determinant_positions =
        determination_side_positions(&determination.determinant, &interface.parameters, budget)?;
    let dependent_positions =
        determination_side_positions(&determination.dependent, &interface.parameters, budget)?;

    let mut determinant_index = 0;
    let mut dependent_index = 0;
    while determinant_index < determinant_positions.len()
        && dependent_index < dependent_positions.len()
    {
        budget.charge(1).map_err(|()| constraint_resource())?;
        let determinant_position = determinant_positions[determinant_index];
        let dependent_position = dependent_positions[dependent_index];
        match determinant_position.cmp(&dependent_position) {
            std::cmp::Ordering::Less => determinant_index += 1,
            std::cmp::Ordering::Greater => dependent_index += 1,
            std::cmp::Ordering::Equal => {
                let dependent = determination
                    .dependent
                    .parameters
                    .get(dependent_index)
                    .ok_or_else(invalid_state)?;
                let determinant = determination
                    .determinant
                    .parameters
                    .get(determinant_index)
                    .ok_or_else(invalid_state)?;
                return Err(determination_parameter_error(
                    dependent.origin.primary_span(),
                    "this parameter occurs on both sides of the determination",
                    Some((
                        determinant.origin.primary_span(),
                        "the determinant occurrence is here",
                    )),
                    budget,
                )?);
            }
        }
    }

    let covered = determinant_positions
        .len()
        .checked_add(dependent_positions.len())
        .ok_or_else(constraint_resource)?;
    if covered != interface.parameters.len() {
        let mut determinant_index = 0;
        let mut dependent_index = 0;
        let mut missing = None;
        for (position, parameter) in interface.parameters.iter().enumerate() {
            budget.charge(1).map_err(|()| constraint_resource())?;
            if determinant_positions.get(determinant_index) == Some(&position) {
                determinant_index += 1;
            } else if dependent_positions.get(dependent_index) == Some(&position) {
                dependent_index += 1;
            } else {
                missing = Some(parameter);
                break;
            }
        }
        let missing = missing.ok_or_else(invalid_state)?;
        return Err(determination_parameter_error(
            determination.span,
            "this determination does not cover every interface parameter",
            Some((
                missing.origin.primary_span(),
                "this interface parameter is omitted",
            )),
            budget,
        )?);
    }
    if !structurally_total {
        return Err(invalid_state());
    }

    // This charge owns the checked declaration-position vector separately
    // from the already retained source occurrences. A failure still disposes
    // both temporary primitive buffers before checked publication.
    budget
        .charge(determinant_positions.len())
        .map_err(|()| constraint_resource())?;
    Ok(DeterminationKey::new(
        determinant_positions.into_boxed_slice(),
    ))
}

fn determination_side_positions(
    side: &crate::resolved::ResolvedDeterminationSide,
    parameters: &[crate::resolved::ResolvedTypeVariable],
    budget: &mut InterfaceConstraintBudget,
) -> Result<Vec<usize>, TypeError> {
    let mut positions = Vec::new();
    positions
        .try_reserve_exact(side.parameters.len())
        .map_err(|_| constraint_resource())?;
    let mut next_declaration_position = 0;
    let mut previous = None;
    for occurrence in &side.parameters {
        let mut found = None;
        while let Some(parameter) = parameters.get(next_declaration_position) {
            budget.charge(1).map_err(|()| constraint_resource())?;
            let position = next_declaration_position;
            next_declaration_position += 1;
            if parameter.id == occurrence.id {
                found = Some(position);
                break;
            }
        }
        let Some(position) = found else {
            let mut actual = None;
            for (position, parameter) in parameters.iter().enumerate() {
                budget.charge(1).map_err(|()| constraint_resource())?;
                if parameter.id == occurrence.id {
                    actual = Some(position);
                    break;
                }
            }
            let actual = actual.ok_or_else(invalid_state)?;
            let (message, related_message) =
                if previous.is_some_and(|(previous_position, _)| previous_position == actual) {
                    (
                        "this determination parameter is repeated",
                        "the first occurrence on this side is here",
                    )
                } else {
                    (
                        "this determination side does not follow interface declaration order",
                        "the preceding occurrence on this side is here",
                    )
                };
            return Err(determination_parameter_error(
                occurrence.origin.primary_span(),
                message,
                previous.map(
                    |(_, previous): (usize, &crate::resolved::ResolvedDeterminationParameter)| {
                        (previous.origin.primary_span(), related_message)
                    },
                ),
                budget,
            )?);
        };
        positions.push(position);
        previous = Some((position, occurrence));
    }
    Ok(positions)
}

fn determination_parameter_error(
    primary: Span,
    message: &'static str,
    related: Option<(Span, &'static str)>,
    budget: &mut InterfaceConstraintBudget,
) -> Result<TypeError, TypeError> {
    let mut diagnostic = Diagnostic::new(
        InterfaceReason::DeterminationParameter,
        SourceLabel::new(primary, message),
    );
    if let Some((span, message)) = related {
        retain_interface_label(&mut diagnostic, span, message, budget)?;
    }
    Ok(TypeError::Interface(Box::new(diagnostic)))
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
        for requirement in requirements.iter() {
            let interface = checked_interface(
                module,
                checked_interfaces,
                requirement.application.interface.id,
                budget,
            )?
            .ok_or_else(invalid_state)?;
            check_application_arity(
                interface,
                requirement.application.arguments.len(),
                requirement.application.span,
            )?;
        }
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
                    requirement.application.interface.id,
                    budget,
                )?
                .filter(|interface| !interface.is_public());
                if let Some(interface) = private {
                    let mut diagnostic = Diagnostic::new(
                        InterfaceReason::ConstraintPrivateInterface,
                        SourceLabel::new(
                            requirement.application.span,
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
            let mut duplicate = None;
            let mut determination_conflict = None;
            let interface = checked_interface(
                module,
                checked_interfaces,
                requirement.application.interface.id,
                budget,
            )?
            .ok_or_else(invalid_state)?;
            for first in &requirements[..index] {
                budget.charge(1).map_err(|()| constraint_resource())?;
                if first.application.interface.id != requirement.application.interface.id {
                    continue;
                }
                if same_resolved_application_arguments(
                    &first.application.arguments,
                    &requirement.application.arguments,
                    budget,
                )? {
                    duplicate = Some(first);
                    break;
                }
                if let Some(determination) = interface.determination()
                    && same_resolved_application_key(
                        &first.application.arguments,
                        &requirement.application.arguments,
                        determination,
                        budget,
                    )?
                {
                    determination_conflict = Some(first);
                    break;
                }
            }
            if let Some(first) = duplicate {
                let mut diagnostic = Diagnostic::new(
                    InterfaceReason::DuplicateRequirement,
                    SourceLabel::new(
                        requirement.application.span,
                        "this requirement is already declared",
                    ),
                );
                diagnostic.related.push(SourceLabel::new(
                    first.application.span,
                    "the first identical requirement is here",
                ));
                return Err(TypeError::Interface(Box::new(diagnostic)));
            }
            if let Some(first) = determination_conflict {
                budget.charge(2).map_err(|()| constraint_resource())?;
                let mut diagnostic = Diagnostic::new(
                    InterfaceReason::DeterminationConflict,
                    SourceLabel::new(
                        requirement.application.span,
                        "this requirement conflicts with the dependent tuple fixed for the same determinant key",
                    ),
                );
                diagnostic
                    .related
                    .try_reserve(1)
                    .map_err(|_| constraint_resource())?;
                diagnostic.related.push(SourceLabel::new(
                    first.application.span,
                    "this earlier requirement fixes a different dependent tuple for that key",
                ));
                return Err(TypeError::Interface(Box::new(diagnostic)));
            }
        }
        for requirement in requirements.iter() {
            budget.charge(1).map_err(|()| constraint_resource())?;
            let interface = checked_interface(
                module,
                checked_interfaces,
                requirement.application.interface.id,
                budget,
            )?
            .ok_or_else(invalid_state)?;
            let mut absent = None;
            if let Some(determination) = interface.determination() {
                let mut previous_position = None;
                for &position in determination.positions() {
                    budget.charge(1).map_err(|()| constraint_resource())?;
                    if previous_position.is_some_and(|previous| previous >= position) {
                        return Err(invalid_state());
                    }
                    previous_position = Some(position);
                    let argument = requirement
                        .application
                        .arguments
                        .get(position)
                        .ok_or_else(invalid_state)?;
                    absent = first_variable_absent_from_types(&argument.ty, &value_types, budget)
                        .map_err(|()| constraint_resource())?;
                    if absent.is_some() {
                        break;
                    }
                }
            } else {
                for argument in &requirement.application.arguments {
                    absent = first_variable_absent_from_types(&argument.ty, &value_types, budget)
                        .map_err(|()| constraint_resource())?;
                    if absent.is_some() {
                        break;
                    }
                }
            }
            if let Some(variable) = absent {
                let mut diagnostic = Diagnostic::new(
                    InterfaceReason::UndeterminedParameter,
                    SourceLabel::new(
                        requirement.application.span,
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
    registry: &ResolvedRegistry,
    budget: &mut InterfaceConstraintBudget,
    type_work: &mut TypeWorkBudget,
) -> Result<Box<[CheckedImplementation]>, TypeError> {
    for implementation in module.implementations() {
        check_implementation_header(module, checked_interfaces, implementation, budget)?;
    }
    check_effective_implementation_overlap(
        module,
        checked_interfaces,
        registry,
        budget,
        type_work,
    )?;

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
            type_work,
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

    fn interface(self) -> crate::interface::InterfaceId {
        match self {
            Self::Imported(implementation) => implementation.fact.interface(),
            Self::Local(implementation) => implementation.head.interface.id,
        }
    }

    fn argument_count(self) -> usize {
        match self {
            Self::Imported(implementation) => implementation.fact.arguments().len(),
            Self::Local(implementation) => implementation.head.arguments.len(),
        }
    }

    fn argument(self, index: usize) -> Option<&'a Type> {
        match self {
            Self::Imported(implementation) => implementation.fact.arguments().get(index),
            Self::Local(implementation) => implementation
                .head
                .arguments
                .get(index)
                .map(|argument| &argument.ty),
        }
    }

    const fn head_parameters(self) -> &'a [crate::resolved::ResolvedTypeVariable] {
        match self {
            Self::Imported(implementation) => &implementation.fact.head_parameters,
            Self::Local(implementation) => &implementation.head_parameters,
        }
    }

    fn primary_span(self) -> Span {
        match self {
            Self::Imported(implementation) => match implementation.authorization().hops().first() {
                Some(hop) => hop.import_span,
                None => implementation.fact.span,
            },
            Self::Local(implementation) => implementation
                .head
                .arguments
                .first()
                .map_or(implementation.head.span, |argument| argument.span),
        }
    }

    const fn definition_span(self) -> Span {
        match self {
            Self::Imported(implementation) => implementation.fact.span,
            Self::Local(implementation) => implementation.head.span,
        }
    }

    const fn import_route(self) -> &'a [crate::resolved::ImplementationRouteHop] {
        match self {
            Self::Imported(implementation) => implementation.authorization().hops(),
            Self::Local(_) => &[],
        }
    }
}

fn retain_interface_label(
    diagnostic: &mut Diagnostic<InterfaceReason>,
    span: Span,
    message: &'static str,
    budget: &mut InterfaceConstraintBudget,
) -> Result<(), TypeError> {
    budget.charge(1).map_err(|()| constraint_resource())?;
    diagnostic
        .related
        .try_reserve(1)
        .map_err(|_| constraint_resource())?;
    diagnostic.related.push(SourceLabel::new(span, message));
    Ok(())
}

fn check_effective_implementation_overlap(
    module: &ResolvedModule,
    checked_interfaces: &[CheckedInterface],
    registry: &ResolvedRegistry,
    budget: &mut InterfaceConstraintBudget,
    type_work: &mut TypeWorkBudget,
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

    check_effective_implementation_heads(
        registry,
        &effective,
        |interface, budget| {
            let interface = checked_interface(module, checked_interfaces, interface, budget)?
                .ok_or_else(invalid_state)?;
            Ok(interface.determination())
        },
        budget,
        type_work,
    )
}

fn check_effective_implementation_heads<'key, F>(
    registry: &ResolvedRegistry,
    effective: &[ImplementationHeadRef<'_>],
    mut determination_for: F,
    budget: &mut InterfaceConstraintBudget,
    type_work: &mut TypeWorkBudget,
) -> Result<(), TypeError>
where
    F: FnMut(
        InterfaceId,
        &mut InterfaceConstraintBudget,
    ) -> Result<Option<&'key DeterminationKey>, TypeError>,
{
    for (index, implementation) in effective.iter().copied().enumerate() {
        budget.charge(1).map_err(|()| constraint_resource())?;
        for previous in effective[..index].iter().copied() {
            budget.charge(1).map_err(|()| constraint_resource())?;
            if implementation.interface() != previous.interface()
                || implementation.id() == previous.id()
            {
                continue;
            }
            let mut previous_parameters = Vec::new();
            let mut implementation_parameters = Vec::new();
            let combined_parameter_count = previous
                .head_parameters()
                .len()
                .checked_add(implementation.head_parameters().len())
                .ok_or_else(constraint_resource)?;
            budget
                .charge(combined_parameter_count)
                .map_err(|()| constraint_resource())?;
            previous_parameters
                .try_reserve(previous.head_parameters().len())
                .map_err(|_| constraint_resource())?;
            implementation_parameters
                .try_reserve(implementation.head_parameters().len())
                .map_err(|_| constraint_resource())?;
            previous_parameters.extend(
                previous
                    .head_parameters()
                    .iter()
                    .map(|parameter| parameter.id),
            );
            implementation_parameters.extend(
                implementation
                    .head_parameters()
                    .iter()
                    .map(|parameter| parameter.id),
            );
            if previous.argument_count() != implementation.argument_count() {
                return Err(invalid_state());
            }
            let complete_argument_work = previous
                .argument_count()
                .checked_mul(2)
                .ok_or_else(constraint_resource)?;
            budget
                .charge(complete_argument_work)
                .map_err(|()| constraint_resource())?;
            let mut previous_arguments = Vec::new();
            let mut implementation_arguments = Vec::new();
            previous_arguments
                .try_reserve(previous.argument_count())
                .map_err(|_| constraint_resource())?;
            implementation_arguments
                .try_reserve(implementation.argument_count())
                .map_err(|_| constraint_resource())?;
            for position in 0..previous.argument_count() {
                previous_arguments.push(previous.argument(position).ok_or_else(invalid_state)?);
                implementation_arguments.push(
                    implementation
                        .argument(position)
                        .ok_or_else(invalid_state)?,
                );
            }
            let determination = determination_for(implementation.interface(), budget)?;
            let pair_failure = if let Some(determination) = determination {
                let positions = determination.positions();
                let mut previous_position = None;
                for &position in positions {
                    budget.charge(1).map_err(|()| constraint_resource())?;
                    if position >= previous_arguments.len()
                        || previous_position.is_some_and(|previous| previous >= position)
                    {
                        return Err(invalid_state());
                    }
                    previous_position = Some(position);
                }
                let selected_argument_work = positions
                    .len()
                    .checked_mul(2)
                    .ok_or_else(constraint_resource)?;
                budget
                    .charge(selected_argument_work)
                    .map_err(|()| constraint_resource())?;
                let mut previous_key = Vec::new();
                let mut implementation_key = Vec::new();
                previous_key
                    .try_reserve_exact(positions.len())
                    .map_err(|_| constraint_resource())?;
                implementation_key
                    .try_reserve_exact(positions.len())
                    .map_err(|_| constraint_resource())?;
                for &position in positions {
                    previous_key.push(*previous_arguments.get(position).ok_or_else(invalid_state)?);
                    implementation_key.push(
                        *implementation_arguments
                            .get(position)
                            .ok_or_else(invalid_state)?,
                    );
                }
                budget.charge(1).map_err(|()| constraint_resource())?;
                let keys_overlap = map_overlap_result(implementation_application_heads_overlap(
                    registry,
                    InterfaceOperationWork::new(implementation.primary_span(), budget, type_work),
                    &previous_parameters,
                    &previous_key,
                    &implementation_parameters,
                    &implementation_key,
                ))?;
                if !keys_overlap {
                    None
                } else {
                    let complete_heads_overlap =
                        map_overlap_result(implementation_application_heads_overlap(
                            registry,
                            InterfaceOperationWork::new(
                                implementation.primary_span(),
                                budget,
                                type_work,
                            ),
                            &previous_parameters,
                            &previous_arguments,
                            &implementation_parameters,
                            &implementation_arguments,
                        ))?;
                    Some(if complete_heads_overlap {
                        InterfaceReason::ImplOverlap
                    } else {
                        InterfaceReason::ImplDeterminationConflict
                    })
                }
            } else if map_overlap_result(implementation_application_heads_overlap(
                registry,
                InterfaceOperationWork::new(implementation.primary_span(), budget, type_work),
                &previous_parameters,
                &previous_arguments,
                &implementation_parameters,
                &implementation_arguments,
            ))? {
                Some(InterfaceReason::ImplOverlap)
            } else {
                None
            };
            if let Some(pair_failure) = pair_failure {
                let (primary_message, earlier_message) = match pair_failure {
                    InterfaceReason::ImplOverlap => (
                        "this implementation overlaps an earlier available implementation",
                        "the earlier overlapping implementation head is here",
                    ),
                    InterfaceReason::ImplDeterminationConflict => (
                        "this implementation shares a determinant key with an earlier implementation but disagrees on dependents",
                        "the earlier conflicting implementation head is here",
                    ),
                    _ => return Err(invalid_state()),
                };
                let mut diagnostic = Diagnostic::new(
                    pair_failure,
                    SourceLabel::new(implementation.primary_span(), primary_message),
                );
                retain_interface_label(
                    &mut diagnostic,
                    previous.definition_span(),
                    earlier_message,
                    budget,
                )?;
                for hop in previous.import_route() {
                    retain_interface_label(
                        &mut diagnostic,
                        hop.import_span,
                        "the earlier implementation became available through this import",
                        budget,
                    )?;
                }
                let later_route = implementation.import_route();
                if !later_route.is_empty() {
                    retain_interface_label(
                        &mut diagnostic,
                        implementation.definition_span(),
                        "the later implementation is defined here",
                        budget,
                    )?;
                    for hop in &later_route[1..] {
                        retain_interface_label(
                            &mut diagnostic,
                            hop.import_span,
                            "the later implementation became available through this import",
                            budget,
                        )?;
                    }
                }
                return Err(TypeError::Interface(Box::new(diagnostic)));
            }
        }
    }
    Ok(())
}

fn map_overlap_result(result: Result<bool, OverlapFailure>) -> Result<bool, TypeError> {
    match result {
        Ok(overlaps) => Ok(overlaps),
        Err(OverlapFailure::Resource) => Err(constraint_resource()),
        Err(OverlapFailure::TypeResource) => Err(TypeError::Internal(
            ElaborationFailure::TypeResourceExhausted,
        )),
        Err(OverlapFailure::InvalidState) => Err(invalid_state()),
    }
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
    let head_interface = checked_interface(
        module,
        checked_interfaces,
        implementation.head.interface.id,
        budget,
    )?
    .ok_or_else(invalid_state)?;
    check_application_arity(
        head_interface,
        implementation.head.arguments.len(),
        implementation.head.span,
    )?;
    for argument in &implementation.head.arguments {
        budget
            .charge_type(&argument.ty)
            .map_err(|()| constraint_resource())?;
    }
    for prerequisite in &implementation.prerequisites {
        let interface = checked_interface(
            module,
            checked_interfaces,
            prerequisite.application.interface.id,
            budget,
        )?
        .ok_or_else(invalid_state)?;
        check_application_arity(
            interface,
            prerequisite.application.arguments.len(),
            prerequisite.application.span,
        )?;
        for argument in &prerequisite.application.arguments {
            budget
                .charge_type(&argument.ty)
                .map_err(|()| constraint_resource())?;
        }
    }

    check_implementation_prerequisite_relations(
        module,
        checked_interfaces,
        implementation,
        budget,
    )?;

    if selection_key_is_all_bare_variables(head_interface, &implementation.head.arguments, budget)?
    {
        let mut diagnostic = Diagnostic::new(
            InterfaceReason::ImplVariableHead,
            SourceLabel::new(
                implementation.head.span,
                "an implementation selection key cannot contain only bare type variables",
            ),
        );
        retain_interface_label(
            &mut diagnostic,
            implementation.head.interface.origin.primary_span(),
            "this is the implemented interface",
            budget,
        )?;
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
        retain_interface_label(
            &mut diagnostic,
            implementation.head.span,
            "the implementation head determines every prerequisite variable",
            budget,
        )?;
        return Err(TypeError::Interface(Box::new(diagnostic)));
    }

    check_implementation_determination_coverage(module, head_interface, implementation, budget)?;

    let local_interface_owner = implementation.head.interface.id.module() == module.module();
    if !local_interface_owner
        && !selection_key_has_local_outer_nominal(
            head_interface,
            &implementation.head.arguments,
            module.module(),
            budget,
        )?
    {
        let mut diagnostic = Diagnostic::new(
            InterfaceReason::ImplOrphan,
            SourceLabel::new(
                implementation.head.span,
                "this module owns neither the interface nor an outer nominal type in the selection key",
            ),
        );
        retain_interface_label(
            &mut diagnostic,
            implementation.head.interface.origin.primary_span(),
            "the foreign interface is selected here",
            budget,
        )?;
        return Err(TypeError::Interface(Box::new(diagnostic)));
    }

    let head_key = if implementation.prerequisites.is_empty() {
        Vec::new()
    } else {
        collect_selection_key_types(head_interface, &implementation.head.arguments, budget)?
    };
    for prerequisite in &implementation.prerequisites {
        budget
            .charge(prerequisite.application.arguments.len())
            .map_err(|()| constraint_resource())?;
        let mut prerequisite_arguments = Vec::new();
        prerequisite_arguments
            .try_reserve(prerequisite.application.arguments.len())
            .map_err(|_| constraint_resource())?;
        prerequisite_arguments.extend(
            prerequisite
                .application
                .arguments
                .iter()
                .map(|argument| &argument.ty),
        );
        let prerequisite_interface = checked_interface(
            module,
            checked_interfaces,
            prerequisite.application.interface.id,
            budget,
        )?
        .ok_or_else(invalid_state)?;
        let prerequisite_key = collect_selection_key_types(
            prerequisite_interface,
            &prerequisite.application.arguments,
            budget,
        )?;
        if !implementation_prerequisite_selection_key_terminates(
            &prerequisite_arguments,
            &prerequisite_key,
            &head_key,
            budget,
        )
        .map_err(|()| constraint_resource())?
        {
            let mut diagnostic = Diagnostic::new(
                InterfaceReason::ImplPrerequisiteNotDecreasing,
                SourceLabel::new(
                    prerequisite.application.span,
                    "this generic prerequisite does not strictly decrease",
                ),
            );
            retain_interface_label(
                &mut diagnostic,
                implementation.head.span,
                "the prerequisite must decrease pointwise from this head",
                budget,
            )?;
            return Err(TypeError::Interface(Box::new(diagnostic)));
        }
    }
    if implementation.public {
        if let Some(interface) = checked_interface(
            module,
            checked_interfaces,
            implementation.head.interface.id,
            budget,
        )? && !interface.is_public()
        {
            let mut diagnostic = Diagnostic::new(
                InterfaceReason::ImplPrivateInterface,
                SourceLabel::new(
                    implementation.head.interface.origin.primary_span(),
                    "a public implementation cannot expose this private interface",
                ),
            );
            retain_interface_label(
                &mut diagnostic,
                interface.span(),
                "the private interface is declared here",
                budget,
            )?;
            return Err(TypeError::Interface(Box::new(diagnostic)));
        }
        for prerequisite in &implementation.prerequisites {
            if let Some(interface) = checked_interface(
                module,
                checked_interfaces,
                prerequisite.application.interface.id,
                budget,
            )? && !interface.is_public()
            {
                let mut diagnostic = Diagnostic::new(
                    InterfaceReason::ImplPrivateInterface,
                    SourceLabel::new(
                        prerequisite.application.span,
                        "a public implementation cannot expose this private prerequisite",
                    ),
                );
                retain_interface_label(
                    &mut diagnostic,
                    interface.span(),
                    "the private interface is declared here",
                    budget,
                )?;
                return Err(TypeError::Interface(Box::new(diagnostic)));
            }
        }
    }
    Ok(())
}

fn check_implementation_prerequisite_relations(
    module: &ResolvedModule,
    checked_interfaces: &[CheckedInterface],
    implementation: &crate::resolved::ResolvedImplementation,
    budget: &mut InterfaceConstraintBudget,
) -> Result<(), TypeError> {
    for (index, prerequisite) in implementation.prerequisites.iter().enumerate() {
        let interface = checked_interface(
            module,
            checked_interfaces,
            prerequisite.application.interface.id,
            budget,
        )?
        .ok_or_else(invalid_state)?;
        for earlier in &implementation.prerequisites[..index] {
            budget.charge(1).map_err(|()| constraint_resource())?;
            if earlier.application.interface.id != prerequisite.application.interface.id {
                continue;
            }
            if same_resolved_application_arguments(
                &earlier.application.arguments,
                &prerequisite.application.arguments,
                budget,
            )? {
                let mut diagnostic = Diagnostic::new(
                    InterfaceReason::DuplicateRequirement,
                    SourceLabel::new(
                        prerequisite.application.span,
                        "this prerequisite is already declared",
                    ),
                );
                retain_interface_label(
                    &mut diagnostic,
                    earlier.application.span,
                    "the first identical prerequisite is here",
                    budget,
                )?;
                return Err(TypeError::Interface(Box::new(diagnostic)));
            }
            if let Some(determination) = interface.determination()
                && same_resolved_application_key(
                    &earlier.application.arguments,
                    &prerequisite.application.arguments,
                    determination,
                    budget,
                )?
            {
                let mut diagnostic = Diagnostic::new(
                    InterfaceReason::DeterminationConflict,
                    SourceLabel::new(
                        prerequisite.application.span,
                        "this prerequisite conflicts with the dependent tuple fixed for the same determinant key",
                    ),
                );
                retain_interface_label(
                    &mut diagnostic,
                    earlier.application.span,
                    "this earlier prerequisite fixes a different dependent tuple for that key",
                    budget,
                )?;
                return Err(TypeError::Interface(Box::new(diagnostic)));
            }
        }
    }
    Ok(())
}

fn collect_selection_key_types<'a>(
    interface: CheckedInterfaceRef<'_>,
    arguments: &'a [ResolvedType],
    budget: &mut InterfaceConstraintBudget,
) -> Result<Vec<&'a Type>, TypeError> {
    if arguments.len() != interface.parameters().len() {
        return Err(invalid_state());
    }
    let selected_count = interface
        .determination()
        .map_or(arguments.len(), |determination| {
            determination.positions().len()
        });
    let Some(determination) = interface.determination() else {
        budget
            .charge(selected_count)
            .map_err(|()| constraint_resource())?;
        let mut selected = Vec::new();
        selected
            .try_reserve_exact(selected_count)
            .map_err(|_| constraint_resource())?;
        selected.extend(arguments.iter().map(|argument| &argument.ty));
        return Ok(selected);
    };

    let mut previous_position = None;
    for &position in determination.positions() {
        budget.charge(1).map_err(|()| constraint_resource())?;
        if position >= arguments.len()
            || previous_position.is_some_and(|previous| previous >= position)
        {
            return Err(invalid_state());
        }
        previous_position = Some(position);
    }
    budget
        .charge(selected_count)
        .map_err(|()| constraint_resource())?;
    let mut selected = Vec::new();
    selected
        .try_reserve_exact(selected_count)
        .map_err(|_| constraint_resource())?;
    for &position in determination.positions() {
        selected.push(&arguments.get(position).ok_or_else(invalid_state)?.ty);
    }
    Ok(selected)
}

fn selection_key_has_local_outer_nominal(
    interface: CheckedInterfaceRef<'_>,
    arguments: &[ResolvedType],
    module: crate::module::ModuleId,
    budget: &mut InterfaceConstraintBudget,
) -> Result<bool, TypeError> {
    if arguments.len() != interface.parameters().len() {
        return Err(invalid_state());
    }
    let Some(determination) = interface.determination() else {
        for argument in arguments {
            budget.charge(2).map_err(|()| constraint_resource())?;
            if argument
                .ty
                .outer_nominal()
                .is_some_and(|id| id.module() == module)
            {
                return Ok(true);
            }
        }
        return Ok(false);
    };

    let positions = determination.positions();
    let mut previous_position = None;
    for &position in positions {
        budget.charge(1).map_err(|()| constraint_resource())?;
        if position >= arguments.len()
            || previous_position.is_some_and(|previous| previous >= position)
        {
            return Err(invalid_state());
        }
        previous_position = Some(position);
    }
    for &position in positions {
        budget.charge(2).map_err(|()| constraint_resource())?;
        let argument = arguments.get(position).ok_or_else(invalid_state)?;
        if argument
            .ty
            .outer_nominal()
            .is_some_and(|id| id.module() == module)
        {
            return Ok(true);
        }
    }
    Ok(false)
}

fn selection_key_is_all_bare_variables(
    interface: CheckedInterfaceRef<'_>,
    arguments: &[ResolvedType],
    budget: &mut InterfaceConstraintBudget,
) -> Result<bool, TypeError> {
    if arguments.len() != interface.parameters().len() {
        return Err(invalid_state());
    }
    let Some(determination) = interface.determination() else {
        for argument in arguments {
            budget.charge(1).map_err(|()| constraint_resource())?;
            if !matches!(argument.ty, Type::Variable(_)) {
                return Ok(false);
            }
        }
        return Ok(true);
    };

    let positions = determination.positions();
    let mut previous_position = None;
    for &position in positions {
        budget.charge(1).map_err(|()| constraint_resource())?;
        if position >= arguments.len()
            || previous_position.is_some_and(|previous| previous >= position)
        {
            return Err(invalid_state());
        }
        previous_position = Some(position);
    }
    for &position in positions {
        budget.charge(1).map_err(|()| constraint_resource())?;
        let argument = arguments.get(position).ok_or_else(invalid_state)?;
        if !matches!(argument.ty, Type::Variable(_)) {
            return Ok(false);
        }
    }
    Ok(true)
}

fn check_implementation_determination_coverage(
    module: &ResolvedModule,
    interface: CheckedInterfaceRef<'_>,
    implementation: &crate::resolved::ResolvedImplementation,
    budget: &mut InterfaceConstraintBudget,
) -> Result<(), TypeError> {
    let Some(determination) = interface.determination() else {
        return Ok(());
    };
    let arguments = &implementation.head.arguments;
    if arguments.len() != interface.parameters().len() {
        return Err(invalid_state());
    }
    let positions = determination.positions();
    let mut previous_position = None;
    for &position in positions {
        budget.charge(1).map_err(|()| constraint_resource())?;
        if position >= arguments.len()
            || previous_position.is_some_and(|previous| previous >= position)
        {
            return Err(invalid_state());
        }
        previous_position = Some(position);
    }

    let mut key_index = 0;
    for (position, dependent) in arguments.iter().enumerate() {
        budget.charge(1).map_err(|()| constraint_resource())?;
        if positions.get(key_index) == Some(&position) {
            key_index += 1;
            continue;
        }
        let mut absent = None;
        visit_type_variables(&dependent.ty, budget, |variable, budget| {
            let mut occurs_in_key = false;
            for &key_position in positions {
                budget.charge(2)?;
                let key_argument = arguments.get(key_position).ok_or(())?;
                if type_contains_variable(&key_argument.ty, variable, budget)? {
                    occurs_in_key = true;
                    break;
                }
            }
            if !occurs_in_key {
                absent = Some(variable);
                return Ok(true);
            }
            Ok(false)
        })
        .map_err(|()| constraint_resource())?;
        let Some(variable) = absent else {
            continue;
        };

        let mut diagnostic = Diagnostic::new(
            InterfaceReason::ImplDeterminationCoverage,
            SourceLabel::new(
                dependent.span,
                "this dependent argument contains a variable absent from the determinant key",
            ),
        );
        if let Some(parameter) = module.registry().type_variable(variable) {
            retain_interface_label(
                &mut diagnostic,
                parameter.origin.primary_span(),
                "this dependent variable is bound here",
                budget,
            )?;
        }
        for &key_position in positions {
            budget.charge(1).map_err(|()| constraint_resource())?;
            let key_argument = arguments.get(key_position).ok_or_else(invalid_state)?;
            retain_interface_label(
                &mut diagnostic,
                key_argument.span,
                "this determinant-key argument does not contain the dependent variable",
                budget,
            )?;
        }
        return Err(TypeError::Interface(Box::new(diagnostic)));
    }
    if key_index != positions.len() {
        return Err(invalid_state());
    }
    Ok(())
}

fn check_implementation_membership(
    module: &ResolvedModule,
    checked_interfaces: &[CheckedInterface],
    source_index: usize,
    implementation: &crate::resolved::ResolvedImplementation,
    budget: &mut InterfaceConstraintBudget,
    type_work: &mut TypeWorkBudget,
) -> Result<CheckedImplementation, TypeError> {
    let interface = checked_interface(
        module,
        checked_interfaces,
        implementation.head.interface.id,
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
    type_work
        .charge(implementation.head.arguments.len())
        .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
    let mut application_arguments = OwnedTypeBuffer(Vec::new());
    application_arguments
        .try_reserve(implementation.head.arguments.len())
        .map_err(|_| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
    for argument in &implementation.head.arguments {
        application_arguments.push(
            clone_type_with_budget(&argument.ty, type_work)
                .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?,
        );
    }
    Ok(CheckedImplementation::new(
        source_index,
        implementation.id,
        InterfaceApplication::new(
            implementation.head.interface.id,
            application_arguments.into_boxed_slice(),
        ),
        methods.into_boxed_slice(),
    ))
}

#[derive(Clone, Copy)]
enum CheckedInterfaceRef<'a> {
    Local(
        &'a crate::resolved::ResolvedInterfaceDeclaration,
        &'a CheckedInterface,
    ),
    Imported(&'a crate::resolved::CheckedInterfaceFact),
}

impl<'a> CheckedInterfaceRef<'a> {
    const fn id(self) -> crate::interface::InterfaceId {
        match self {
            Self::Local(interface, _) => interface.id,
            Self::Imported(interface) => interface.id,
        }
    }

    const fn is_public(self) -> bool {
        match self {
            Self::Local(interface, _) => interface.public,
            Self::Imported(_) => true,
        }
    }

    const fn parameters(self) -> &'a [crate::resolved::ResolvedTypeVariable] {
        match self {
            Self::Local(interface, _) => &interface.parameters,
            Self::Imported(interface) => &interface.parameters,
        }
    }

    const fn span(self) -> Span {
        match self {
            Self::Local(interface, _) => interface.span,
            Self::Imported(interface) => interface.span,
        }
    }

    fn method_count(self) -> usize {
        match self {
            Self::Local(interface, _) => interface.methods.len(),
            Self::Imported(interface) => interface.methods.len(),
        }
    }

    fn method(self, index: usize) -> Option<CheckedInterfaceMethodRef<'a>> {
        match self {
            Self::Local(interface, _) => interface
                .methods
                .get(index)
                .map(CheckedInterfaceMethodRef::Local),
            Self::Imported(interface) => interface
                .methods
                .get(index)
                .map(CheckedInterfaceMethodRef::Imported),
        }
    }

    const fn determination(self) -> Option<&'a DeterminationKey> {
        match self {
            Self::Local(_, checked) => checked.determination(),
            Self::Imported(interface) => interface.determination(),
        }
    }
}

fn check_application_arity(
    interface: CheckedInterfaceRef<'_>,
    found: usize,
    span: Span,
) -> Result<(), TypeError> {
    check_application_arity_parts(interface.parameters().len(), interface.span(), found, span)
}

fn check_application_arity_parts(
    expected: usize,
    declaration_span: Span,
    found: usize,
    span: Span,
) -> Result<(), TypeError> {
    if found == expected {
        return Ok(());
    }
    let mut diagnostic = Diagnostic::new(
        InterfaceReason::ArgumentCount,
        SourceLabel::new(
            span,
            "this interface application has the wrong number of arguments",
        ),
    );
    diagnostic.related.push(SourceLabel::new(
        declaration_span,
        "the interface parameter list is declared here",
    ));
    Err(TypeError::Interface(Box::new(diagnostic)))
}

fn same_resolved_application_arguments(
    left: &[ResolvedType],
    right: &[ResolvedType],
    budget: &mut InterfaceConstraintBudget,
) -> Result<bool, TypeError> {
    if left.len() != right.len() {
        return Ok(false);
    }
    for (left, right) in left.iter().zip(right) {
        if !same_type_with_constraint_budget(&left.ty, &right.ty, budget)
            .map_err(|()| constraint_resource())?
        {
            return Ok(false);
        }
    }
    Ok(true)
}

fn same_resolved_application_key(
    left: &[ResolvedType],
    right: &[ResolvedType],
    determination: &DeterminationKey,
    budget: &mut InterfaceConstraintBudget,
) -> Result<bool, TypeError> {
    if left.len() != right.len() {
        return Ok(false);
    }
    let mut previous_position = None;
    for &position in determination.positions() {
        budget.charge(1).map_err(|()| constraint_resource())?;
        if position >= left.len() || previous_position.is_some_and(|previous| previous >= position)
        {
            return Err(invalid_state());
        }
        previous_position = Some(position);
        if !same_type_with_constraint_budget(&left[position].ty, &right[position].ty, budget)
            .map_err(|()| constraint_resource())?
        {
            return Ok(false);
        }
    }
    Ok(true)
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

    const fn type_parameters(self) -> &'a [crate::resolved::ResolvedTypeVariable] {
        match self {
            Self::Local(method) => &method.type_parameters,
            Self::Imported(method) => method.authoritative_type_parameters(),
        }
    }

    const fn annotation_span(self) -> Span {
        match self {
            Self::Local(method) => method.annotation.span,
            Self::Imported(method) => method.annotation_span(),
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
    checked_interfaces: &'a [CheckedInterface],
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
            return Ok(Some(CheckedInterfaceRef::Local(interface, checked)));
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

fn is_polymorphic_recursion_error(error: &TypeError) -> bool {
    matches!(
        error,
        TypeError::Source(diagnostic) if diagnostic.reason == TypeReason::PolymorphicRecursion
    )
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
            Type::Tuple(elements) => {
                budget.charge(elements.len())?;
                pending.try_reserve(elements.len()).map_err(|_| ())?;
                pending.extend(elements.iter().rev());
            }
            Type::Application(function, argument) => {
                budget.charge(2)?;
                pending.try_reserve(2).map_err(|_| ())?;
                pending.push(argument);
                pending.push(function);
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

#[derive(Clone, Copy)]
struct NewtypeRepresentationEdge {
    target: usize,
    occurrence: Span,
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
fn check_newtype_representation_cycles(
    resolved: &ResolvedModule,
    type_work: &mut TypeWorkBudget,
) -> Result<(), TypeError> {
    let registry = resolved.registry();
    let vertex_count = registry
        .nominals()
        .iter()
        .filter(|nominal| nominal.declaration_kind == ResolvedNominalDeclarationKind::Newtype)
        .count();
    // The graph owns two retained records per vertex before traversal begins:
    // its declaration index and its identity-to-position index entry.  Charge
    // both before either allocation can retain capacity.
    type_work
        .charge(
            vertex_count
                .checked_mul(2)
                .ok_or_else(|| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?,
        )
        .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
    let mut vertices = Vec::new();
    vertices
        .try_reserve(vertex_count)
        .map_err(|_| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
    let mut vertex_positions = HashMap::new();
    vertex_positions
        .try_reserve(vertex_count)
        .map_err(|_| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
    for (index, nominal) in registry.nominals().iter().enumerate() {
        if nominal.declaration_kind == ResolvedNominalDeclarationKind::Newtype {
            let position = vertices.len();
            vertices.push(index);
            if vertex_positions.insert(nominal.id, position).is_some() {
                return Err(TypeError::Internal(ElaborationFailure::InvalidState));
            }
        }
    }

    // One outer adjacency row is retained for every newtype, including rows
    // with no outgoing representation edge.
    type_work
        .charge(vertex_count)
        .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
    let mut edges = Vec::new();
    edges
        .try_reserve(vertices.len())
        .map_err(|_| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
    for &owner in &vertices {
        type_work
            .charge(1)
            .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
        let nominal = &registry.nominals()[owner];
        let representation = nominal
            .representation
            .as_ref()
            .ok_or_else(|| TypeError::Internal(ElaborationFailure::InvalidState))?;
        let representation_provenance = nominal
            .representation_provenance
            .as_ref()
            .ok_or_else(|| TypeError::Internal(ElaborationFailure::InvalidState))?;
        let mut outgoing = Vec::new();
        let mut pending = Vec::new();
        type_work
            .charge(1)
            .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
        pending
            .try_reserve(1)
            .map_err(|_| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
        pending.push((representation, representation_provenance.root()));
        while let Some((ty, provenance_index)) = pending.pop() {
            type_work
                .charge(1)
                .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
            let provenance = representation_provenance
                .nodes()
                .get(provenance_index)
                .ok_or_else(|| TypeError::Internal(ElaborationFailure::InvalidState))?;
            let provenance_span = match provenance {
                ResolvedTypeProvenanceNode::Fact(span)
                | ResolvedTypeProvenanceNode::Tuple { span, .. }
                | ResolvedTypeProvenanceNode::Function { span, .. }
                | ResolvedTypeProvenanceNode::Application { span, .. } => *span,
            };
            match ty {
                Type::Nominal(identity) => {
                    let Some(target) = vertex_positions.get(identity).copied() else {
                        continue;
                    };
                    type_work.charge(1).map_err(|()| {
                        TypeError::Internal(ElaborationFailure::TypeResourceExhausted)
                    })?;
                    outgoing.try_reserve(1).map_err(|_| {
                        TypeError::Internal(ElaborationFailure::TypeResourceExhausted)
                    })?;
                    outgoing.push(NewtypeRepresentationEdge {
                        target,
                        occurrence: provenance_span,
                    });
                }
                Type::Application(function, argument) | Type::Function(function, argument) => {
                    type_work.charge(2).map_err(|()| {
                        TypeError::Internal(ElaborationFailure::TypeResourceExhausted)
                    })?;
                    pending.try_reserve(2).map_err(|_| {
                        TypeError::Internal(ElaborationFailure::TypeResourceExhausted)
                    })?;
                    let (function_provenance, argument_provenance) = match provenance {
                        ResolvedTypeProvenanceNode::Application {
                            function, argument, ..
                        } => (*function, *argument),
                        ResolvedTypeProvenanceNode::Function {
                            domain, codomain, ..
                        } => (*domain, *codomain),
                        _ => return Err(TypeError::Internal(ElaborationFailure::InvalidState)),
                    };
                    pending.push((argument, argument_provenance));
                    pending.push((function, function_provenance));
                }
                Type::Tuple(elements) => {
                    type_work.charge(elements.len()).map_err(|()| {
                        TypeError::Internal(ElaborationFailure::TypeResourceExhausted)
                    })?;
                    pending.try_reserve(elements.len()).map_err(|_| {
                        TypeError::Internal(ElaborationFailure::TypeResourceExhausted)
                    })?;
                    let ResolvedTypeProvenanceNode::Tuple {
                        elements: provenance_elements,
                        ..
                    } = provenance
                    else {
                        return Err(TypeError::Internal(ElaborationFailure::InvalidState));
                    };
                    if elements.len() != provenance_elements.len() {
                        return Err(TypeError::Internal(ElaborationFailure::InvalidState));
                    }
                    pending.extend(
                        elements
                            .iter()
                            .zip(provenance_elements.iter())
                            .rev()
                            .map(|(element, provenance)| (element, *provenance)),
                    );
                }
                Type::Int | Type::Bool | Type::Unit | Type::Variable(_) => {}
                Type::Inference(_) | Type::Forall(_, _) => {
                    return Err(TypeError::Internal(ElaborationFailure::InvalidState));
                }
            }
        }
        edges.push(outgoing);
    }

    type_work
        .charge(
            vertices
                .len()
                .checked_mul(3)
                .ok_or_else(|| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?,
        )
        .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
    let mut state = Vec::new();
    state
        .try_reserve_exact(vertices.len())
        .map_err(|_| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
    state.resize(vertices.len(), 0_u8);
    let mut stack = Vec::new();
    let mut active_path = Vec::new();
    stack
        .try_reserve(vertices.len())
        .map_err(|_| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
    active_path
        .try_reserve(vertices.len())
        .map_err(|_| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
    for root in 0..vertices.len() {
        if state[root] != 0 {
            continue;
        }
        type_work
            .charge(2)
            .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
        state[root] = 1;
        stack.push((root, 0_usize));
        active_path.push(root);
        while let Some((vertex, edge_index)) = stack.pop() {
            type_work
                .charge(1)
                .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
            let Some(edge) = edges[vertex].get(edge_index).copied() else {
                state[vertex] = 2;
                let completed = active_path
                    .pop()
                    .ok_or_else(|| TypeError::Internal(ElaborationFailure::InvalidState))?;
                if completed != vertex {
                    return Err(TypeError::Internal(ElaborationFailure::InvalidState));
                }
                continue;
            };
            type_work
                .charge(1)
                .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
            stack.push((vertex, edge_index + 1));
            match state[edge.target] {
                0 => {
                    type_work.charge(2).map_err(|()| {
                        TypeError::Internal(ElaborationFailure::TypeResourceExhausted)
                    })?;
                    state[edge.target] = 1;
                    stack.push((edge.target, 0));
                    active_path.push(edge.target);
                }
                1 => {
                    let cycle_start = active_path
                        .iter()
                        .position(|candidate| *candidate == edge.target)
                        .ok_or_else(|| TypeError::Internal(ElaborationFailure::InvalidState))?;
                    let mut diagnostic = Diagnostic::new(
                        TypeReason::NewtypeRecursiveRepresentation,
                        SourceLabel::new(
                            edge.occurrence,
                            "this newtype representation closes a recursive representation cycle",
                        ),
                    );
                    type_work.charge(1).map_err(|()| {
                        TypeError::Internal(ElaborationFailure::TypeResourceExhausted)
                    })?;
                    diagnostic
                        .related
                        .try_reserve(active_path.len() - cycle_start)
                        .map_err(|_| {
                            TypeError::Internal(ElaborationFailure::TypeResourceExhausted)
                        })?;
                    for vertex in &active_path[cycle_start..] {
                        type_work.charge(1).map_err(|()| {
                            TypeError::Internal(ElaborationFailure::TypeResourceExhausted)
                        })?;
                        let declaration = &registry.nominals()[vertices[*vertex]];
                        diagnostic.related.push(SourceLabel::new(
                            declaration.origin.primary_span(),
                            "this declaration participates in the recursive representation cycle",
                        ));
                    }
                    return Err(TypeError::Source(Box::new(diagnostic)));
                }
                2 => {}
                _ => unreachable!("newtype representation traversal state is ternary"),
            }
        }
    }
    Ok(())
}

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
    check_newtype_representation_cycles(&resolved, type_work)?;
    let checked_interfaces = check_interface_declarations(&resolved, constraint_work)?;
    check_global_requirements(&resolved, &checked_interfaces, constraint_work)?;
    let registry = Arc::new(
        resolved
            .registry()
            .checker_view(resolved.imported_facts(), type_work)
            .map_err(resolved_build_error)?,
    );
    let checked_implementations = check_implementation_headers_and_membership(
        &resolved,
        &checked_interfaces,
        &registry,
        constraint_work,
        type_work,
    )?;
    let mut elaborator = Elaborator::for_module_with_registry(
        &resolved,
        registry,
        type_work.clone(),
        coverage_work.clone(),
    )?;
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
            &elaborator.registry,
            &schemes,
            &interface_facts,
            &checked_implementations,
            &mut elaborator.type_work,
            constraint_work,
        )?);
        let (implementation_facts, publication) = elaborator.check_module_bodies(
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
            |slot, checked_method| publication.contains_expected(slot, checked_method),
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
            publication,
        ))
    })();
    *type_work = std::mem::take(&mut elaborator.type_work);
    *coverage_work = std::mem::take(&mut elaborator.coverage_work);
    let (
        schemes,
        checked_implementations,
        interface_facts,
        implementation_facts,
        exports,
        publication,
    ) = result?;
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
    for imported in resolved.imported_facts().implementations() {
        let authorization = imported
            .authorization()
            .clone_with_budget(constraint_work)
            .map_err(|()| constraint_resource())?;
        available_implementations.push(AvailableImplementation::imported(
            imported.fact.id,
            authorization,
        ));
    }
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
    publication
        .publish()
        .map_err(|failure| selection_failure(failure, None))?;
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
    registry: &ResolvedRegistry,
    schemes: &[CheckedGlobalScheme],
    interface_facts: &[CheckedInterfaceFact],
    checked_implementations: &[CheckedImplementation],
    type_work: &mut TypeWorkBudget,
    constraint_work: &mut InterfaceConstraintBudget,
) -> Result<EvidenceSelector, TypeError> {
    let mut selector = EvidenceSelector::new();
    for imported in resolved.imported_facts().interface_imports() {
        selector
            .add_imported_interface_fact(registry, &imported.fact, constraint_work, type_work)
            .map_err(|failure| selection_failure(failure, None))?;
    }
    for interface in interface_facts {
        selector
            .add_interface_fact(registry, interface, constraint_work, type_work)
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
            .add_implementation_fact(registry, imported, constraint_work, type_work)
            .map_err(|failure| selection_failure(failure, None))?;
    }
    for checked in checked_implementations {
        let implementation = resolved
            .implementations()
            .get(checked.source_index)
            .ok_or_else(invalid_state)?;
        selector
            .add_local_implementation(
                registry,
                implementation,
                checked,
                constraint_work,
                type_work,
            )
            .map_err(|failure| selection_failure(failure, None))?;
    }
    Ok(selector)
}

fn clone_checked_type_variables(
    parameters: &[crate::resolved::ResolvedTypeVariable],
    type_work: &mut TypeWorkBudget,
) -> Result<CheckedTypeVariableBuffer, TypeError> {
    type_work
        .charge(parameters.len())
        .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
    let mut cloned = CheckedTypeVariableBuffer(Vec::new());
    cloned
        .try_reserve(parameters.len())
        .map_err(|_| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
    for parameter in parameters {
        cloned.push(
            clone_resolved_type_variable_with_budget(parameter, type_work)
                .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?,
        );
    }
    Ok(cloned)
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
            constraint_work
                .charge(method.type_parameters.len())
                .map_err(|()| constraint_resource())?;
            let method_parameters =
                clone_checked_type_variables(&method.type_parameters, type_work)?;
            let value_type = clone_type_with_budget(&method.annotation.ty, type_work)
                .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
            methods.push(
                CheckedInterfaceMethodFact::with_resolved_binder_authority(
                    method,
                    method_parameters.into_boxed_slice(),
                    value_type,
                    type_work,
                    constraint_work,
                )
                .map_err(|failure| match failure {
                    ResolvedBuildFailure::TypeResource => {
                        TypeError::Internal(ElaborationFailure::TypeResourceExhausted)
                    }
                    ResolvedBuildFailure::ConstraintResource => constraint_resource(),
                    ResolvedBuildFailure::InvalidState => invalid_state(),
                })?,
            );
        }
        let parameters = clone_checked_type_variables(&interface.parameters, type_work)?;
        let determination = token
            .determination()
            .map(|key| key.clone_with_budget(constraint_work))
            .transpose()
            .map_err(|()| constraint_resource())?;
        facts.push(CheckedInterfaceFact::new(
            interface.id,
            interface.spelling.clone(),
            parameters.into_boxed_slice(),
            determination,
            methods.into_boxed_slice(),
            interface.origin.clone(),
            interface.span,
        ));
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
    link_modules_with_budgets(
        modules,
        entry,
        constraint_work,
        &mut TypeWorkBudget::default(),
    )
}

pub(crate) fn link_modules_with_budgets(
    modules: Vec<CheckedModule>,
    entry: crate::module::ModuleId,
    constraint_work: &mut InterfaceConstraintBudget,
    type_work: &mut TypeWorkBudget,
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
            .and_then(|total| {
                module.available_implementations().iter().try_fold(
                    total,
                    |total, implementation| {
                        total.checked_add(implementation.authorization().hops().len())
                    },
                )
            })
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
    let registry = Arc::new(
        ResolvedRegistry::combine_checked(&modules, type_work, constraint_work)
            .map_err(resolved_build_error)?,
    );
    let mut groups = Vec::new();
    groups
        .try_reserve(modules.len())
        .map_err(|_| constraint_resource())?;
    for module in modules {
        groups.push(
            module
                .into_group(constraint_work)
                .map_err(|()| constraint_resource())?,
        );
    }
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
        evidence_marker: Option<PendingObligationMarker>,
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

struct MatchProgressOwner<'a>(Option<Box<MatchProgress<'a>>>);

impl<'a> MatchProgressOwner<'a> {
    fn new(progress: Box<MatchProgress<'a>>) -> Self {
        Self(Some(progress))
    }

    fn into_inner(mut self) -> Box<MatchProgress<'a>> {
        self.0.take().expect("match progress transfers once")
    }

    fn set_result_type(
        &mut self,
        result: ProvenancedTypeOwner,
        kind: CheckKind,
    ) -> Result<(), TypeError> {
        let progress = self.0.as_deref_mut().expect("match progress remains live");
        if progress.result_type.is_some() {
            return Err(invalid_state());
        }
        let ProvenancedType { ty, provenance } = result.into_inner();
        progress.result_type = Some((ty, provenance, kind));
        Ok(())
    }

    fn take_result_type(&mut self) -> Option<(ProvenancedTypeOwner, CheckKind)> {
        self.0
            .as_deref_mut()
            .expect("match progress remains live")
            .result_type
            .take()
            .map(|(ty, provenance, kind)| {
                (
                    ProvenancedTypeOwner::new(ProvenancedType { ty, provenance }),
                    kind,
                )
            })
    }

    fn push_row(&mut self, row: Vec<CorePattern>) {
        self.0
            .as_deref_mut()
            .expect("match progress remains live")
            .matrix
            .push(row);
    }

    fn push_arm_body(&mut self, body: (NodeId, Span)) {
        self.0
            .as_deref_mut()
            .expect("match progress remains live")
            .arm_bodies
            .push(body);
    }

    fn take_matrix(&mut self) -> CorePatternMatrixBuffer {
        CorePatternMatrixBuffer(std::mem::take(
            &mut self
                .0
                .as_deref_mut()
                .expect("match progress remains live")
                .matrix,
        ))
    }

    fn take_arm_bodies(&mut self) -> Vec<(NodeId, Span)> {
        std::mem::take(
            &mut self
                .0
                .as_deref_mut()
                .expect("match progress remains live")
                .arm_bodies,
        )
    }

    fn replace_scrutinee_type(&mut self, ty: Type) {
        replace_type_iteratively(
            &mut self
                .0
                .as_deref_mut()
                .expect("match progress remains live")
                .scrutinee
                .ty,
            ty,
        );
    }

    fn set_scrutinee_provenance(&mut self, provenance: TypeProvenance) {
        self.0
            .as_deref_mut()
            .expect("match progress remains live")
            .scrutinee
            .provenance = provenance;
    }

    fn advance_arm(&mut self) {
        let progress = self.0.as_deref_mut().expect("match progress remains live");
        progress.next_arm = progress
            .next_arm
            .checked_add(1)
            .expect("match arm progress is bounded by the source arm vector");
    }
}

impl<'a> Deref for MatchProgressOwner<'a> {
    type Target = MatchProgress<'a>;

    fn deref(&self) -> &Self::Target {
        self.0.as_deref().expect("match progress remains live")
    }
}

impl Drop for MatchProgressOwner<'_> {
    fn drop(&mut self) {
        if let Some(progress) = self.0.take() {
            discard_match_progress(progress);
        }
    }
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
    Application {
        whole_span: Span,
        argument_span: Span,
    },
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

struct ElaboratedBindingBuffer(Vec<ElaboratedBinding>);

impl Drop for ElaboratedBindingBuffer {
    fn drop(&mut self) {
        for binding in self.0.drain(..) {
            binding.binder.discard_metadata();
        }
    }
}

struct ElaboratedGroupBuffer(Vec<(ElaboratedBindingBuffer, Span)>);

struct CoreRecursiveMemberBuffer(Vec<(TypedBinder, NodeId)>);

impl Drop for CoreRecursiveMemberBuffer {
    fn drop(&mut self) {
        for (binder, _) in self.0.drain(..) {
            binder.discard_metadata();
        }
    }
}

struct PreparedGlobals {
    context: TypeContext,
    globals: Vec<ElaboratedBinding>,
    binders: HashMap<BinderId, TypedBinder>,
    quantifiers: HashMap<BinderId, Box<[(TypeVariableId, Kind)]>>,
}

impl Drop for PreparedGlobals {
    fn drop(&mut self) {
        for binding in self.globals.drain(..) {
            binding.binder.discard_metadata();
        }
        for (_, binder) in self.binders.drain() {
            binder.discard_metadata();
        }
    }
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

struct ElaborationTaskBuffer<'a>(Vec<ElaborationTask<'a>>);

impl<'a> Deref for ElaborationTaskBuffer<'a> {
    type Target = Vec<ElaborationTask<'a>>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<'a> ElaborationTaskBuffer<'a> {
    fn push(&mut self, task: ElaborationTask<'a>) {
        self.0.push(task);
    }

    fn pop(&mut self) -> Option<ElaborationTask<'a>> {
        self.0.pop()
    }
}

impl Drop for ElaborationTaskBuffer<'_> {
    fn drop(&mut self) {
        while let Some(task) = self.0.pop() {
            discard_elaboration_task(task);
        }
    }
}

struct TypedNodeBuffer(Vec<TypedNode>);

impl Deref for TypedNodeBuffer {
    type Target = Vec<TypedNode>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl TypedNodeBuffer {
    fn push(&mut self, node: TypedNode) {
        self.0.push(node);
    }

    fn pop(&mut self) -> Option<TypedNodeOwner> {
        self.0.pop().map(TypedNodeOwner::new)
    }

    fn split_off(&mut self, at: usize) -> Self {
        Self(self.0.split_off(at))
    }

    fn reverse(&mut self) {
        self.0.reverse();
    }
}

impl Drop for TypedNodeBuffer {
    fn drop(&mut self) {
        while let Some(node) = self.0.pop() {
            discard_typed_node(node);
        }
    }
}

struct ElaboratedDeclarationBuffer(Vec<ElaboratedDeclaration>);

struct ElaboratedDeclarationOwner(Option<ElaboratedDeclaration>);

impl ElaboratedDeclarationOwner {
    fn new(declaration: ElaboratedDeclaration) -> Self {
        Self(Some(declaration))
    }

    fn into_inner(mut self) -> ElaboratedDeclaration {
        self.0
            .take()
            .expect("an elaborated declaration transfers once")
    }
}

impl Drop for ElaboratedDeclarationOwner {
    fn drop(&mut self) {
        if let Some(declaration) = self.0.take() {
            discard_elaborated_declaration(declaration);
        }
    }
}

impl Deref for ElaboratedDeclarationBuffer {
    type Target = Vec<ElaboratedDeclaration>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl ElaboratedDeclarationBuffer {
    fn push(&mut self, declaration: ElaboratedDeclaration) {
        self.0.push(declaration);
    }

    fn pop(&mut self) -> Option<ElaboratedDeclarationOwner> {
        self.0.pop().map(ElaboratedDeclarationOwner::new)
    }

    fn split_off(&mut self, at: usize) -> Self {
        Self(self.0.split_off(at))
    }
}

impl Drop for ElaboratedDeclarationBuffer {
    fn drop(&mut self) {
        while let Some(declaration) = self.0.pop() {
            discard_elaborated_declaration(declaration);
        }
    }
}

struct OwnedTypeBuffer(Vec<Type>);

impl Deref for OwnedTypeBuffer {
    type Target = Vec<Type>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl OwnedTypeBuffer {
    fn push(&mut self, ty: Type) {
        self.0.push(ty);
    }

    fn try_reserve(&mut self, additional: usize) -> Result<(), std::collections::TryReserveError> {
        self.0.try_reserve(additional)
    }

    fn into_vec(mut self) -> Vec<Type> {
        std::mem::take(&mut self.0)
    }

    fn into_boxed_slice(mut self) -> Box<[Type]> {
        std::mem::take(&mut self.0).into_boxed_slice()
    }
}

impl Drop for OwnedTypeBuffer {
    fn drop(&mut self) {
        while let Some(ty) = self.0.pop() {
            discard_type_iteratively(ty);
        }
    }
}

struct CorePatternOwner(Option<CorePattern>);

impl CorePatternOwner {
    fn new(pattern: Option<CorePattern>) -> Self {
        Self(pattern)
    }

    fn take(&mut self) -> Option<CorePattern> {
        self.0.take()
    }

    fn into_inner(mut self) -> CorePattern {
        self.0.take().expect("a core pattern transfers once")
    }
}

impl Deref for CorePatternOwner {
    type Target = CorePattern;

    fn deref(&self) -> &Self::Target {
        self.0.as_ref().expect("core pattern remains live")
    }
}

impl Drop for CorePatternOwner {
    fn drop(&mut self) {
        if let Some(pattern) = self.0.take() {
            pattern.discard_iteratively();
        }
    }
}

struct CorePatternBuffer(Vec<CorePattern>);

impl Deref for CorePatternBuffer {
    type Target = Vec<CorePattern>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl CorePatternBuffer {
    fn push(&mut self, pattern: CorePattern) {
        self.0.push(pattern);
    }

    fn pop(&mut self) -> Option<CorePatternOwner> {
        self.0
            .pop()
            .map(|pattern| CorePatternOwner::new(Some(pattern)))
    }

    fn try_reserve(&mut self, additional: usize) -> Result<(), std::collections::TryReserveError> {
        self.0.try_reserve(additional)
    }

    fn into_vec(mut self) -> Vec<CorePattern> {
        std::mem::take(&mut self.0)
    }

    fn into_boxed_slice(mut self) -> Box<[CorePattern]> {
        std::mem::take(&mut self.0).into_boxed_slice()
    }
}

struct CorePatternMatrixBuffer(Vec<Vec<CorePattern>>);

impl Deref for CorePatternMatrixBuffer {
    type Target = Vec<Vec<CorePattern>>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl CorePatternMatrixBuffer {
    fn push(&mut self, row: Vec<CorePattern>) {
        self.0.push(row);
    }

    fn pop(&mut self) -> Option<CorePatternBuffer> {
        self.0.pop().map(CorePatternBuffer)
    }

    fn try_reserve(&mut self, additional: usize) -> Result<(), std::collections::TryReserveError> {
        self.0.try_reserve(additional)
    }

    fn into_sequence(mut self) -> CorePatternRowSequence {
        CorePatternRowSequence(std::mem::take(&mut self.0).into_iter())
    }
}

impl Drop for CorePatternMatrixBuffer {
    fn drop(&mut self) {
        for row in self.0.drain(..) {
            for pattern in row {
                pattern.discard_iteratively();
            }
        }
    }
}

struct CorePatternRowSequence(std::vec::IntoIter<Vec<CorePattern>>);

impl Iterator for CorePatternRowSequence {
    type Item = Vec<CorePattern>;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next()
    }
}

impl Drop for CorePatternRowSequence {
    fn drop(&mut self) {
        for row in self.0.by_ref() {
            for pattern in row {
                pattern.discard_iteratively();
            }
        }
    }
}

struct ProvenancedTypeBuffer(Vec<ProvenancedType>);

impl Deref for ProvenancedTypeBuffer {
    type Target = Vec<ProvenancedType>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl ProvenancedTypeBuffer {
    fn push(&mut self, value: ProvenancedType) {
        self.0.push(value);
    }

    fn try_reserve(&mut self, additional: usize) -> Result<(), std::collections::TryReserveError> {
        self.0.try_reserve(additional)
    }
}

impl Drop for ProvenancedTypeBuffer {
    fn drop(&mut self) {
        for value in self.0.drain(..) {
            discard_provenanced_type(value);
        }
    }
}

struct EvidenceSpecificationBuffer(
    Vec<(
        MethodEvidenceOwner,
        RequirementId,
        MethodId,
        InterfaceApplication,
        Type,
    )>,
);

impl Deref for EvidenceSpecificationBuffer {
    type Target = Vec<(
        MethodEvidenceOwner,
        RequirementId,
        MethodId,
        InterfaceApplication,
        Type,
    )>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl EvidenceSpecificationBuffer {
    fn push(
        &mut self,
        specification: (
            MethodEvidenceOwner,
            RequirementId,
            MethodId,
            InterfaceApplication,
            Type,
        ),
    ) {
        self.0.push(specification);
    }

    fn try_reserve(&mut self, additional: usize) -> Result<(), std::collections::TryReserveError> {
        self.0.try_reserve(additional)
    }

    fn into_sequence(mut self) -> EvidenceSpecificationSequence {
        EvidenceSpecificationSequence(std::mem::take(&mut self.0).into_iter())
    }
}

impl Drop for EvidenceSpecificationBuffer {
    fn drop(&mut self) {
        for (_, _, _, application, ty) in self.0.drain(..) {
            drop(application);
            discard_type_iteratively(ty);
        }
    }
}

struct EvidenceSpecificationSequence(
    std::vec::IntoIter<(
        MethodEvidenceOwner,
        RequirementId,
        MethodId,
        InterfaceApplication,
        Type,
    )>,
);

impl Iterator for EvidenceSpecificationSequence {
    type Item = (
        MethodEvidenceOwner,
        RequirementId,
        MethodId,
        InterfaceApplication,
        Type,
    );

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next()
    }
}

impl Drop for EvidenceSpecificationSequence {
    fn drop(&mut self) {
        for (_, _, _, application, ty) in self.0.by_ref() {
            drop(application);
            discard_type_iteratively(ty);
        }
    }
}

impl Drop for CorePatternBuffer {
    fn drop(&mut self) {
        for pattern in self.0.drain(..) {
            pattern.discard_iteratively();
        }
    }
}

fn discard_provenanced_type(provenanced: ProvenancedType) {
    discard_type_iteratively(provenanced.ty);
    drop(provenanced.provenance);
}

fn discard_typed_node(node: TypedNode) {
    discard_type_iteratively(node.ty);
    drop(node.provenance);
}

fn discard_match_progress(progress: Box<MatchProgress<'_>>) {
    let MatchProgress {
        scrutinee,
        matrix,
        result_type,
        ..
    } = *progress;
    discard_typed_node(scrutinee);
    for row in matrix {
        for pattern in row {
            pattern.discard_iteratively();
        }
    }
    if let Some((ty, provenance, _)) = result_type {
        discard_type_iteratively(ty);
        drop(provenance);
    }
}

fn discard_elaboration_task(task: ElaborationTask<'_>) {
    match task {
        ElaborationTask::Synthesize { .. }
        | ElaborationTask::AfterApplicationFunction { .. }
        | ElaborationTask::AfterLeft { .. }
        | ElaborationTask::CheckRecursiveMember(_)
        | ElaborationTask::BeginRecursiveGroup(_)
        | ElaborationTask::FinishRecursiveGroup { .. }
        | ElaborationTask::FinishBlock { .. } => {}
        ElaborationTask::Check { expected, .. }
        | ElaborationTask::CheckBlock { expected, .. }
        | ElaborationTask::FinishCheck { expected, .. } => {
            discard_provenanced_type(expected);
        }
        ElaborationTask::CheckFunction {
            domain,
            codomain,
            function_type,
            presentation,
            ..
        } => {
            discard_provenanced_type(domain);
            discard_provenanced_type(codomain);
            discard_provenanced_type(function_type);
            discard_origin_iteratively(presentation);
        }
        ElaborationTask::FinishFunction {
            binder,
            pattern,
            domain,
            ty,
            origin,
            ..
        } => {
            binder.discard_metadata();
            if let Some(pattern) = pattern {
                pattern.discard_iteratively();
            }
            if let Some(domain) = domain {
                discard_type_iteratively(domain);
            }
            discard_type_iteratively(ty);
            discard_origin_iteratively(origin);
        }
        ElaborationTask::FinishApplication {
            function, codomain, ..
        } => {
            discard_typed_node(function);
            discard_provenanced_type(codomain);
        }
        ElaborationTask::AfterMatchScrutinee { expected, .. } => {
            if let Some((expected, _)) = expected {
                discard_provenanced_type(expected);
            }
        }
        ElaborationTask::FinishMatchArm { progress, row, .. } => {
            discard_match_progress(progress);
            for pattern in row {
                pattern.discard_iteratively();
            }
        }
        ElaborationTask::FinishMatch(progress) => discard_match_progress(progress),
        ElaborationTask::AfterRight { left, .. } => discard_typed_node(left),
        ElaborationTask::BeginBinding {
            expected,
            finish_expected,
            ..
        } => {
            if let Some(expected) = expected {
                discard_provenanced_type(expected);
            }
            if let Some(expected) = finish_expected {
                discard_provenanced_type(expected);
            }
        }
        ElaborationTask::FinishBinding { expected, .. } => {
            if let Some(expected) = expected {
                discard_provenanced_type(expected);
            }
        }
    }
}

fn discard_elaborated_declaration(declaration: ElaboratedDeclaration) {
    match declaration {
        ElaboratedDeclaration::Binding { binder, origin, .. } => {
            binder.discard_metadata();
            discard_origin_iteratively(origin);
        }
        ElaboratedDeclaration::PatternBinding {
            pattern, origin, ..
        } => {
            pattern.discard_iteratively();
            discard_origin_iteratively(origin);
        }
        ElaboratedDeclaration::Recursive { members, origin } => {
            for (binder, _) in members {
                binder.discard_metadata();
            }
            discard_origin_iteratively(origin);
        }
    }
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
    tasks: &mut ElaborationTaskBuffer<'a>,
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
                    .transpose()?
                    .map(ProvenancedTypeOwner::new);
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
                    expected: expected.map(ProvenancedTypeOwner::into_inner),
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
    let expected = IterativeTypeOwner::new(expected);
    let found = IterativeTypeOwner::new(found);
    match kind {
        CheckKind::General => TypeError::Mismatch(TypeMismatch {
            span,
            expected_display: registry.display_source_type(&expected),
            found_display: registry.display_source_type(&found),
            expected: Box::new(expected.into_inner()),
            found: Box::new(found.into_inner()),
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
            SynthesisCause::Application { whole_span, .. } => (
                whole_span,
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
    tasks: &mut ElaborationTaskBuffer<'a>,
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

fn inference_registry_error(error: InferenceRegistryFailure) -> TypeError {
    match error {
        InferenceRegistryFailure::Resource => {
            TypeError::Internal(ElaborationFailure::TypeResourceExhausted)
        }
        InferenceRegistryFailure::Missing
        | InferenceRegistryFailure::Duplicate
        | InferenceRegistryFailure::Conflict => invalid_state(),
    }
}

fn generated_type_variable_registry_error(
    error: GeneratedTypeVariableRegistryFailure,
) -> TypeError {
    match error {
        GeneratedTypeVariableRegistryFailure::Resource => {
            TypeError::Internal(ElaborationFailure::TypeResourceExhausted)
        }
        GeneratedTypeVariableRegistryFailure::Missing
        | GeneratedTypeVariableRegistryFailure::Duplicate
        | GeneratedTypeVariableRegistryFailure::Conflict => invalid_state(),
    }
}

fn allocate_inference_variable(
    next_inference: &mut u32,
    variables: &mut InferenceVariableRegistry,
    budget: &mut TypeWorkBudget,
    kind: &Kind,
    origin: Span,
) -> Result<Type, TypeError> {
    let identity = InferenceVariableId::new(*next_inference);
    let next = next_inference.checked_add(1).ok_or_else(invalid_state)?;
    variables
        .insert(identity, kind, origin, budget)
        .map_err(inference_registry_error)?;
    *next_inference = next;
    Ok(Type::Inference(identity))
}

fn kind_failure_for_unification(failure: KindFailure) -> UnificationFailure {
    match failure {
        KindFailure::Resource(_) => UnificationFailure::Resource,
        KindFailure::Internal(_) | KindFailure::Source(_) => UnificationFailure::Invariant,
    }
}

fn inference_registry_failure_for_unification(
    failure: InferenceRegistryFailure,
) -> UnificationFailure {
    match failure {
        InferenceRegistryFailure::Resource => UnificationFailure::Resource,
        InferenceRegistryFailure::Missing
        | InferenceRegistryFailure::Duplicate
        | InferenceRegistryFailure::Conflict => UnificationFailure::Invariant,
    }
}

fn generated_type_variable_registry_failure_for_unification(
    failure: GeneratedTypeVariableRegistryFailure,
) -> UnificationFailure {
    match failure {
        GeneratedTypeVariableRegistryFailure::Resource => UnificationFailure::Resource,
        GeneratedTypeVariableRegistryFailure::Missing
        | GeneratedTypeVariableRegistryFailure::Duplicate
        | GeneratedTypeVariableRegistryFailure::Conflict => UnificationFailure::Invariant,
    }
}

fn candidate_kind_environment<'a>(
    candidate: &Type,
    registry: &'a ResolvedRegistry,
    generated_type_variables: &'a GeneratedTypeVariableRegistry,
    inference_variables: &'a InferenceVariableRegistry,
    span: Span,
    budget: &mut TypeWorkBudget,
) -> Result<KindEnvironments<'a>, UnificationFailure> {
    let mut environments = KindEnvironments::new();
    let mut work = Vec::new();

    macro_rules! schedule {
        ($ty:expr) => {{
            // Each retained scan cell is in one-to-one correspondence with
            // one reachable candidate Type cell.
            budget
                .charge(1)
                .map_err(|()| UnificationFailure::Resource)?;
            work.try_reserve(1)
                .map_err(|_| UnificationFailure::Resource)?;
            work.push($ty);
        }};
    }

    schedule!(candidate);
    while let Some(ty) = work.pop() {
        match ty {
            Type::Int | Type::Bool | Type::Unit => {}
            Type::Variable(identity) => {
                budget
                    .charge(1)
                    .map_err(|()| UnificationFailure::Resource)?;
                if environments.contains_declared(*identity) {
                    continue;
                }
                match identity {
                    TypeVariableId::Resolved { .. } => {
                        budget
                            .charge(1)
                            .map_err(|()| UnificationFailure::Resource)?;
                        let parameter = registry
                            .type_variable(*identity)
                            .ok_or(UnificationFailure::Invariant)?;
                        environments
                            .insert_declared(
                                *identity,
                                &parameter.kind,
                                parameter.origin.primary_span(),
                                budget,
                            )
                            .map_err(kind_failure_for_unification)?;
                    }
                    TypeVariableId::Generated(_) => {
                        let fact = generated_type_variables
                            .fact(*identity, budget)
                            .map_err(generated_type_variable_registry_failure_for_unification)?;
                        environments
                            .insert_declared(*identity, &fact.kind, fact.origin, budget)
                            .map_err(kind_failure_for_unification)?;
                    }
                }
            }
            Type::Inference(identity) => {
                budget
                    .charge(1)
                    .map_err(|()| UnificationFailure::Resource)?;
                if environments.contains_inference(*identity) {
                    continue;
                }
                let fact = inference_variables
                    .fact(*identity, budget)
                    .map_err(inference_registry_failure_for_unification)?;
                environments
                    .insert_inference(*identity, &fact.kind, Some(fact.origin), budget, span)
                    .map_err(kind_failure_for_unification)?;
            }
            Type::Nominal(identity) => {
                budget
                    .charge(1)
                    .map_err(|()| UnificationFailure::Resource)?;
                if environments.contains_nominal(*identity) {
                    continue;
                }
                budget
                    .charge(1)
                    .map_err(|()| UnificationFailure::Resource)?;
                match registry
                    .nominal_kind(*identity)
                    .ok_or(UnificationFailure::Invariant)?
                {
                    CanonicalNominalKind::Parameters { parameters, origin } => environments
                        .insert_nominal(*identity, parameters, origin, budget)
                        .map_err(kind_failure_for_unification)?,
                    CanonicalNominalKind::Frozen { kind, origin } => environments
                        .insert_frozen_nominal(*identity, kind, origin, budget)
                        .map_err(kind_failure_for_unification)?,
                }
            }
            Type::Tuple(elements) => {
                for element in elements.iter().rev() {
                    schedule!(element);
                }
            }
            Type::Application(function, argument) | Type::Function(function, argument) => {
                schedule!(argument);
                schedule!(function);
            }
            Type::Forall(_, _) => return Err(UnificationFailure::Invariant),
        }
    }
    Ok(environments)
}

fn authenticate_inference_solution_kind(
    variable: InferenceVariableId,
    candidate: &Type,
    registry: &ResolvedRegistry,
    generated_type_variables: &GeneratedTypeVariableRegistry,
    inference_variables: &InferenceVariableRegistry,
    budget: &mut TypeWorkBudget,
) -> Result<(), UnificationFailure> {
    #[cfg(test)]
    SOLUTION_KIND_AUTHENTICATIONS.with(|count| count.set(count.get().saturating_add(1)));
    let variable_fact = inference_variables
        .fact(variable, budget)
        .map_err(inference_registry_failure_for_unification)?;
    let environments = candidate_kind_environment(
        candidate,
        registry,
        generated_type_variables,
        inference_variables,
        variable_fact.origin,
        budget,
    )?;
    let candidate_kind = environments
        .synthesize_body_free_kind(candidate, variable_fact.origin, budget)
        .map_err(kind_failure_for_unification)?;
    let equal = same_kind_with_budget(&variable_fact.kind, candidate_kind, budget)
        .map_err(|()| UnificationFailure::Resource)?;
    if equal {
        Ok(())
    } else {
        Err(UnificationFailure::Mismatch)
    }
}

fn authenticate_zonk_inference_occurrence(
    identity: InferenceVariableId,
    inference_variables: &InferenceVariableRegistry,
    solutions: &HashMap<InferenceVariableId, Type>,
    authenticated_solutions: &HashSet<InferenceVariableId>,
    budget: &mut TypeWorkBudget,
) -> Result<(), UnificationFailure> {
    inference_variables
        .fact(identity, budget)
        .map_err(inference_registry_failure_for_unification)?;
    if solutions.contains_key(&identity) {
        budget
            .charge(1)
            .map_err(|()| UnificationFailure::Resource)?;
        if !authenticated_solutions.contains(&identity) {
            return Err(UnificationFailure::Invariant);
        }
    }
    Ok(())
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
        ty if ty.outer_nominal().is_some() => {
            let owner = ty.outer_nominal().ok_or_else(invalid_state)?;
            let payload = match &member.initializer.kind {
                ResolvedExprKind::Constructor(occurrence) => {
                    let Some(constructor) = registry.constructor(occurrence.constructor) else {
                        return Err(invalid_state());
                    };
                    if constructor.owner != owner || constructor.payload.is_some() {
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
                    if constructor.owner != owner || constructor.payload.is_none() {
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
        | Type::Nominal(_)
        | Type::Application(_, _)
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

fn implementation_method_core_origin(method: &CheckedImplementationMethodFact) -> Origin {
    // Linked evidence has already authenticated the complete cross-module
    // relation. Core retains only the implementation-local primary cause.
    Origin::Source(method.origin.primary_span())
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
    registry: &ResolvedRegistry,
    budget: &mut TypeWorkBudget,
) -> Result<(), PublicTypeAdmissionError> {
    enum Task<'a> {
        Visit(&'a Type, usize, usize),
        Sequence(std::slice::Iter<'a, Type>, usize),
    }

    let mut work = vec![Task::Visit(ty, 0, 0)];
    while let Some(task) = work.pop() {
        let Task::Visit(ty, depth, applied_arguments) = task else {
            let Task::Sequence(mut remaining, depth) = task else {
                unreachable!("public type admission task is closed")
            };
            if let Some(next) = remaining.next() {
                work.push(Task::Sequence(remaining, depth));
                work.push(Task::Visit(next, depth, 0));
            }
            continue;
        };
        budget
            .charge(1)
            .map_err(|()| PublicTypeAdmissionError::Resource)?;
        match ty {
            Type::Tuple(elements) if applied_arguments == 0 => {
                let child_depth = depth.saturating_add(1);
                if child_depth > CORE_PAYLOAD_DEPTH_LIMIT {
                    return Err(PublicTypeAdmissionError::Invalid);
                }
                work.push(Task::Sequence(elements.iter(), child_depth));
            }
            Type::Tuple(_) => return Err(PublicTypeAdmissionError::Invalid),
            Type::Application(function, argument) => {
                let child_depth = depth.saturating_add(1);
                if child_depth > CORE_PAYLOAD_DEPTH_LIMIT {
                    return Err(PublicTypeAdmissionError::Invalid);
                }
                work.push(Task::Visit(argument, child_depth, 0));
                work.push(Task::Visit(
                    function,
                    depth,
                    applied_arguments.saturating_add(1),
                ));
            }
            Type::Function(domain, codomain) if applied_arguments == 0 => {
                let child_depth = depth.saturating_add(1);
                if child_depth > CORE_PAYLOAD_DEPTH_LIMIT {
                    return Err(PublicTypeAdmissionError::Invalid);
                }
                work.push(Task::Visit(codomain, child_depth, 0));
                work.push(Task::Visit(domain, child_depth, 0));
            }
            Type::Function(_, _) | Type::Inference(_) | Type::Forall(_, _) => {
                return Err(PublicTypeAdmissionError::Invalid);
            }
            Type::Int | Type::Bool | Type::Unit if applied_arguments != 0 => {
                return Err(PublicTypeAdmissionError::Invalid);
            }
            Type::Nominal(id) => {
                let Some(parameters) = registry.nominal_parameters(*id) else {
                    return Err(PublicTypeAdmissionError::Invalid);
                };
                if parameters.len() != applied_arguments {
                    return Err(PublicTypeAdmissionError::Invalid);
                }
            }
            Type::Variable(_) if applied_arguments == 0 => {}
            Type::Variable(_) => return Err(PublicTypeAdmissionError::Invalid),
            Type::Int | Type::Bool | Type::Unit => {}
        }
    }
    Ok(())
}

fn clone_type_with_budget(ty: &Type, budget: &mut TypeWorkBudget) -> Result<Type, ()> {
    charge_type_cells(ty, budget)?;
    Ok(zonk_type(ty, &HashMap::new()))
}

fn retain_method_occurrence_parameters(
    interface_parameters: &[(TypeVariableId, Kind)],
    method_parameters: &[(TypeVariableId, Kind)],
    budget: &mut TypeWorkBudget,
) -> Result<(KindedTypeParameters, KindedTypeParameters), ()> {
    let parameter_count = interface_parameters
        .len()
        .checked_add(method_parameters.len())
        .ok_or(())?;
    budget.charge(parameter_count)?;
    let mut fact_parameters = Vec::new();
    fact_parameters
        .try_reserve(parameter_count)
        .map_err(|_| ())?;
    for (identity, kind) in interface_parameters {
        fact_parameters.push((*identity, clone_kind_with_budget(kind, budget)?));
    }
    for (identity, kind) in method_parameters {
        fact_parameters.push((*identity, clone_kind_with_budget(kind, budget)?));
    }

    // The Core scheme retains a distinct Forall wrapper, binder record, and
    // Kind copy from the elaboration fact above.
    budget.charge(parameter_count.checked_add(1).ok_or(())?)?;
    let mut scheme_parameters = Vec::new();
    scheme_parameters
        .try_reserve(parameter_count)
        .map_err(|_| ())?;
    for (identity, kind) in interface_parameters {
        scheme_parameters.push((*identity, clone_kind_with_budget(kind, budget)?));
    }
    for (identity, kind) in method_parameters {
        scheme_parameters.push((*identity, clone_kind_with_budget(kind, budget)?));
    }

    Ok((
        fact_parameters.into_boxed_slice(),
        scheme_parameters.into_boxed_slice(),
    ))
}

fn same_interface_application_with_budget(
    left: &InterfaceApplication,
    right: &InterfaceApplication,
    budget: &mut TypeWorkBudget,
) -> Result<bool, TypeError> {
    if left.interface() != right.interface() || left.arguments().len() != right.arguments().len() {
        return Ok(false);
    }
    for (left, right) in left.arguments().iter().zip(right.arguments()) {
        if !same_type_with_budget(left, right, budget)
            .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?
        {
            return Ok(false);
        }
    }
    Ok(true)
}

fn clone_scheme_with_budget(fact: &TypeFact, budget: &mut TypeWorkBudget) -> Result<Type, ()> {
    charge_type_cells(&fact.ty, budget)?;
    if fact.quantified.is_empty() {
        return Ok(zonk_type(&fact.ty, &HashMap::new()));
    }
    budget.charge(1)?;
    let quantified = clone_kinded_type_parameters_with_budget(&fact.quantified, budget)?;
    Ok(Type::Forall(
        quantified.into_boxed_slice(),
        Box::new(zonk_type(&fact.ty, &HashMap::new())),
    ))
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
        match ty {
            Type::Function(domain, codomain) | Type::Application(domain, codomain) => {
                work.push(codomain);
                work.push(domain);
            }
            _ => {}
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

fn at_span_provenance_with_budget(
    ty: &Type,
    span: Span,
    budget: &mut TypeWorkBudget,
) -> Result<TypeProvenance, ()> {
    charge_type_provenance_nodes(ty, budget)?;
    Ok(TypeProvenance::at_span(ty, span))
}

fn constructor_replacements_with_budget(
    parameters: &[crate::resolved::ResolvedTypeVariable],
    arguments: &[&Type],
    budget: &mut TypeWorkBudget,
) -> Result<TypeReplacementBuffer, ()> {
    if parameters.len() != arguments.len() {
        return Err(());
    }
    budget.charge(arguments.len())?;
    for argument in arguments {
        charge_type_cells(argument, budget)?;
    }
    let mut replacements = TypeReplacementBuffer::new();
    replacements.try_reserve(arguments.len()).map_err(|_| ())?;
    for (parameter, argument) in parameters.iter().zip(arguments) {
        replacements.try_insert_unique(parameter.id, zonk_type(argument, &HashMap::new()))?;
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
            (
                Type::Application(left_function, left_argument),
                Type::Application(right_function, right_argument),
            ) => {
                work.push(Task::Pair(left_argument, right_argument));
                work.push(Task::Pair(left_function, right_function));
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
    Invariant,
}

#[cfg(test)]
std::thread_local! {
    static ZONK_REBUILD_PENDING_PEAK: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
    static OCCURS_PENDING_PEAK: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
    static SOLUTION_KIND_AUTHENTICATIONS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
    static TEST_INITIAL_TYPED_NODES: std::cell::RefCell<Vec<TypedNode>> = const {
        std::cell::RefCell::new(Vec::new())
    };
}

#[cfg(test)]
fn record_zonk_rebuild_pending(pending: usize) {
    ZONK_REBUILD_PENDING_PEAK.with(|peak| peak.set(peak.get().max(pending)));
}

#[cfg(test)]
fn record_occurs_pending(pending: usize) {
    OCCURS_PENDING_PEAK.with(|peak| peak.set(peak.get().max(pending)));
}

enum ZonkWork {
    TypeCells(usize),
    Inference(InferenceVariableId),
}

#[cfg(test)]
fn zonk_type_with_status<E>(
    ty: &Type,
    solutions: &HashMap<InferenceVariableId, Type>,
    mut charge: impl FnMut(usize) -> Result<(), E>,
) -> Result<(Type, bool), E> {
    zonk_type_with_status_and_inference(ty, solutions, |work| match work {
        ZonkWork::TypeCells(cells) => charge(cells),
        ZonkWork::Inference(_) => Ok(()),
    })
}

fn zonk_type_with_status_and_inference<E>(
    ty: &Type,
    solutions: &HashMap<InferenceVariableId, Type>,
    mut work_charge: impl FnMut(ZonkWork) -> Result<(), E>,
) -> Result<(Type, bool), E> {
    enum ChargeTask<'a> {
        Visit(&'a Type),
        Slice(std::slice::Iter<'a, Type>),
    }

    let mut work = vec![ChargeTask::Visit(ty)];
    let mut unresolved = false;
    while let Some(task) = work.pop() {
        match task {
            ChargeTask::Visit(Type::Inference(identity)) => {
                work_charge(ZonkWork::Inference(*identity))?;
                if let Some(solution) = solutions.get(identity) {
                    work.push(ChargeTask::Visit(solution));
                } else {
                    work_charge(ZonkWork::TypeCells(1))?;
                    unresolved = true;
                }
            }
            ChargeTask::Visit(Type::Tuple(elements)) => {
                work_charge(ZonkWork::TypeCells(1))?;
                work.push(ChargeTask::Slice(elements.iter()));
            }
            ChargeTask::Visit(Type::Application(function, argument)) => {
                work_charge(ZonkWork::TypeCells(1))?;
                work.push(ChargeTask::Visit(argument));
                work.push(ChargeTask::Visit(function));
            }
            ChargeTask::Visit(Type::Function(domain, codomain)) => {
                work_charge(ZonkWork::TypeCells(1))?;
                work.push(ChargeTask::Visit(codomain));
                work.push(ChargeTask::Visit(domain));
            }
            ChargeTask::Visit(Type::Forall(parameters, body)) => {
                work_charge(ZonkWork::TypeCells(1))?;
                for (_, kind) in parameters {
                    work_charge(ZonkWork::TypeCells(1))?;
                    let mut kinds = vec![kind];
                    while let Some(kind) = kinds.pop() {
                        work_charge(ZonkWork::TypeCells(1))?;
                        if let Kind::Arrow(domain, codomain) = kind {
                            kinds.push(codomain);
                            kinds.push(domain);
                        }
                    }
                }
                work.push(ChargeTask::Visit(body));
            }
            ChargeTask::Visit(
                Type::Int | Type::Bool | Type::Unit | Type::Nominal(_) | Type::Variable(_),
            ) => work_charge(ZonkWork::TypeCells(1))?,
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
        FinishApplication,
        FinishFunction,
        FinishForall(Box<[(TypeVariableId, Kind)]>),
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
            Task::Visit(Type::Application(function, argument)) => {
                work.push(Task::FinishApplication);
                work.push(Task::Visit(argument));
                work.push(Task::Visit(function));
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
            Task::FinishApplication => {
                let argument = rebuilt.pop().expect("zonked application argument");
                let function = rebuilt.pop().expect("zonked application function");
                rebuilt.push(Type::Application(Box::new(function), Box::new(argument)));
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
    registry: &ResolvedRegistry,
    generated_type_variables: &GeneratedTypeVariableRegistry,
    inference_variables: &InferenceVariableRegistry,
    budget: &mut TypeWorkBudget,
) -> Result<bool, UnificationFailure> {
    enum Task<'a> {
        Visit(&'a Type),
        Sequence(std::slice::Iter<'a, Type>),
    }

    let mut work = Vec::new();
    let mut visited = HashSet::new();

    macro_rules! schedule {
        ($task:expr) => {{
            budget
                .charge(1)
                .map_err(|()| UnificationFailure::Resource)?;
            work.try_reserve(1)
                .map_err(|_| UnificationFailure::Resource)?;
            work.push($task);
        }};
    }

    schedule!(Task::Visit(ty));
    while let Some(task) = work.pop() {
        #[cfg(test)]
        record_occurs_pending(work.len().saturating_add(1));
        let ty = match task {
            Task::Visit(ty) => ty,
            Task::Sequence(mut remaining) => {
                if let Some(next) = remaining.next() {
                    schedule!(Task::Sequence(remaining));
                    schedule!(Task::Visit(next));
                }
                continue;
            }
        };
        match ty {
            Type::Inference(identity) => {
                inference_variables
                    .fact(*identity, budget)
                    .map_err(inference_registry_failure_for_unification)?;
                if *identity == needle {
                    return Ok(true);
                }
                budget
                    .charge(1)
                    .map_err(|()| UnificationFailure::Resource)?;
                visited
                    .try_reserve(1)
                    .map_err(|_| UnificationFailure::Resource)?;
                if !visited.insert(*identity) {
                    continue;
                }
                if let Some(solution) = solutions.get(identity) {
                    authenticate_inference_solution_kind(
                        *identity,
                        solution,
                        registry,
                        generated_type_variables,
                        inference_variables,
                        budget,
                    )?;
                    schedule!(Task::Visit(solution));
                }
            }
            Type::Tuple(elements) => {
                schedule!(Task::Sequence(elements.iter()));
            }
            Type::Application(function, argument) => {
                schedule!(Task::Visit(argument));
                schedule!(Task::Visit(function));
            }
            Type::Function(domain, codomain) => {
                schedule!(Task::Visit(codomain));
                schedule!(Task::Visit(domain));
            }
            Type::Forall(_, _) => return Err(UnificationFailure::Invariant),
            Type::Int | Type::Bool | Type::Unit | Type::Nominal(_) | Type::Variable(_) => {}
        }
    }
    Ok(false)
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
            Type::Tuple(elements) => {
                work.push(Task::Slice(elements.iter()));
            }
            Type::Application(function, argument) => {
                work.push(Task::Visit(argument));
                work.push(Task::Visit(function));
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
        interface::{EvidenceSelectionBuilder, RequirementOwner},
        module::{ModuleId, ModuleRoots, load_module_graph},
        resolve::{DependencyExports, resolve_module},
        resolved::{
            ImportedFacts, ImportedNominalFact, ImportedTypeAccess, ResolvedExportCandidate,
            ResolvedInterfaceDeclaration, ResolvedInterfaceMethod, ResolvedModuleParts,
            ResolvedNominalType, ResolvedTypeVariable,
        },
        source::{ByteRange, SourceFile},
        types::NominalTypeId,
    };

    static MODULE_FIXTURE_IDS: AtomicU64 = AtomicU64::new(0);

    #[test]
    fn resolved_application_clone_discards_a_deep_first_argument_when_the_second_is_one_short() {
        const DEPTH: usize = 16_384;
        const DEEP_ARGUMENT_CELLS: usize = 1 + 2 * DEPTH;
        const EXACT_TYPE_WORK: usize = DEEP_ARGUMENT_CELLS + 1;

        std::thread::Builder::new()
            .name("resolved-application-partial-clone-owner".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let source = SourceFile::new("resolved-application-clone.ash", "Pair")
                    .expect("the application fixture should fit");
                let span = source
                    .span(ByteRange::new(0, 4).expect("the fixture range is ordered"))
                    .expect("the fixture span should fit");
                let module = ModuleId::from(source.id());
                let interface = InterfaceId::new(module, 0);
                let application = crate::resolved::ResolvedInterfaceApplication {
                    interface: crate::resolved::ResolvedInterfaceOccurrence {
                        id: interface,
                        spelling: "Pair".to_owned(),
                        origin: Origin::Source(span),
                    },
                    arguments: Box::new([
                        ResolvedType {
                            ty: deep_application_type(DEPTH),
                            provenance: ResolvedTypeProvenance::new(
                                vec![ResolvedTypeProvenanceNode::Fact(span)],
                                0,
                            ),
                            origin: Origin::Source(span),
                            span,
                        },
                        ResolvedType {
                            ty: Type::Bool,
                            provenance: ResolvedTypeProvenance::new(
                                vec![ResolvedTypeProvenanceNode::Fact(span)],
                                0,
                            ),
                            origin: Origin::Source(span),
                            span,
                        },
                    ]),
                    span,
                };

                let mut elaborator = Elaborator::new();
                elaborator.type_work = TypeWorkBudget::with_limit(DEEP_ARGUMENT_CELLS);
                assert!(matches!(
                    elaborator.clone_resolved_interface_application(&application),
                    Err(TypeError::Internal(
                        ElaborationFailure::TypeResourceExhausted
                    )),
                ));
                assert_eq!(elaborator.type_work.used(), DEEP_ARGUMENT_CELLS);

                elaborator.type_work = TypeWorkBudget::with_limit(EXACT_TYPE_WORK);
                let cloned = elaborator
                    .clone_resolved_interface_application(&application)
                    .expect("a fresh exact clone budget should retain both arguments");
                assert_eq!(cloned.arguments().len(), 2);
                assert_eq!(elaborator.type_work.used(), EXACT_TYPE_WORK);
                drop(cloned);

                let crate::resolved::ResolvedInterfaceApplication {
                    interface,
                    arguments,
                    ..
                } = application;
                for argument in arguments.into_vec() {
                    argument.discard_iteratively();
                }
                discard_origin_iteratively(interface.origin);
            })
            .expect("the small-stack clone worker should start")
            .join()
            .expect("partial and complete application clones must dismantle iteratively");
    }

    #[test]
    fn checked_parameter_clone_discards_a_deep_origin_on_partial_failure_and_exact_retry() {
        const DEPTH: usize = 16_384;
        // Two vector records, then one record and one Type-kind node per
        // parameter. Four cells therefore retain only the deep first clone.
        const FIRST_PARAMETER_PREFIX: usize = 2 + 1 + 1;
        const EXACT_TYPE_WORK: usize = FIRST_PARAMETER_PREFIX + 1 + 1;

        std::thread::Builder::new()
            .name("checked-parameter-partial-clone-owner".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let source = SourceFile::new("checked-parameter-clone.ash", "Pair")
                    .expect("the parameter fixture should fit");
                let span = source
                    .span(ByteRange::new(0, 4).expect("the fixture range is ordered"))
                    .expect("the fixture span should fit");
                let module = ModuleId::from(source.id());
                let parameters: Box<[ResolvedTypeVariable]> = Box::new([
                    ResolvedTypeVariable {
                        id: TypeVariableId::resolved(module, 0),
                        spelling: "Left".to_owned(),
                        kind: Kind::Type,
                        origin: deep_generated_origin(DEPTH, span),
                    },
                    ResolvedTypeVariable {
                        id: TypeVariableId::resolved(module, 1),
                        spelling: "Right".to_owned(),
                        kind: Kind::Type,
                        origin: Origin::Source(span),
                    },
                ]);

                let mut one_short = TypeWorkBudget::with_limit(FIRST_PARAMETER_PREFIX);
                assert!(matches!(
                    clone_checked_type_variables(&parameters, &mut one_short),
                    Err(TypeError::Internal(
                        ElaborationFailure::TypeResourceExhausted
                    )),
                ));
                assert_eq!(one_short.used(), FIRST_PARAMETER_PREFIX);

                let mut exact = TypeWorkBudget::with_limit(EXACT_TYPE_WORK);
                let cloned = clone_checked_type_variables(&parameters, &mut exact)
                    .expect("a fresh exact parameter budget should retain both records");
                assert_eq!(cloned.len(), 2);
                assert_eq!(exact.used(), EXACT_TYPE_WORK);
                let fact = CheckedInterfaceFact::without_methods_for_test(
                    InterfaceId::new(module, 0),
                    "Pair".to_owned(),
                    cloned.into_boxed_slice(),
                    Origin::Source(span),
                    span,
                );
                drop(fact);
                for parameter in parameters.into_vec() {
                    discard_origin_iteratively(parameter.origin);
                }
            })
            .expect("the small-stack parameter worker should start")
            .join()
            .expect("partial and complete parameter clones must dismantle origins iteratively");
    }

    #[test]
    fn scoped_evidence_binders_dispose_deep_interface_arguments_on_success_and_failure() {
        const DEPTH: usize = 32_768;
        for accepted in [false, true] {
            std::thread::Builder::new()
                .name(format!("scoped-evidence-disposal-{accepted}"))
                .stack_size(256 * 1024)
                .spawn(move || {
                    let source = SourceFile::new("scoped-evidence.ash", "()")
                        .expect("the fixture should fit");
                    let span = source
                        .span(ByteRange::new(0, 2).expect("the range is ordered"))
                        .expect("the span belongs to the fixture");
                    let origin = Origin::Source(span);
                    let module = ModuleId::new(0);
                    let owner = BinderId::resolved(module, 0);
                    let interface = InterfaceId::new(module, 0);
                    let method = MethodId::new(interface, 0);
                    let requirement = RequirementId::new(RequirementOwner::Global(owner), 0);
                    let mut builder = CoreBuilder::new();
                    let binder = builder
                        .binder(Type::Unit, origin)
                        .expect("the evidence binder should fit");
                    let mut interface_argument = Type::Unit;
                    for _ in 0..DEPTH {
                        interface_argument =
                            Type::Function(Box::new(Type::Unit), Box::new(interface_argument));
                    }
                    let scoped = vec![ScopedEvidenceBinder {
                        owner: MethodEvidenceOwner::Global(owner),
                        requirement,
                        method,
                        application: InterfaceApplication::new(
                            interface,
                            Box::new([interface_argument]),
                        ),
                        binder,
                    }];
                    let result = if accepted { Ok(scoped) } else { Err(scoped) };
                    drop(result);
                })
                .expect("the scoped-evidence worker should start")
                .join()
                .expect("both accepted and rejected scope owners must tear down iteratively");
        }
    }

    #[test]
    fn evidence_scope_entry_has_an_exact_carrier_boundary_and_fresh_retry() {
        // One specification reserve, three scope records, one binder Type,
        // and one complete-application vector plus its primitive argument.
        const EXACT_WORK: usize = 1 + 3 + 1 + 2;

        fn enter_with_limit(limit: usize) -> Result<usize, TypeError> {
            let resolved = resolved_module_fixture("evidence-scope-budget.ash", "", "Unit", "()");
            let span = fixture_result(&resolved).span;
            let module = ModuleId::new(902);
            let owner = BinderId::resolved(module, 0);
            let interface = InterfaceId::new(module, 0);
            let method = MethodId::new(interface, 0);
            let requirement = RequirementId::new(RequirementOwner::Global(owner), 0);
            let mut elaborator =
                Elaborator::for_module(&resolved).expect("the fixture namespace should fit");
            elaborator.evidence_lowering = Some(EvidenceLowering {
                interfaces: HashMap::new(),
                interface_methods: HashMap::new(),
                global_schemes: HashMap::new(),
                implementation_methods: HashMap::new(),
                active_binders: HashMap::new(),
            });
            elaborator.type_work = TypeWorkBudget::with_limit(limit);
            let mut specifications = EvidenceSpecificationBuffer(Vec::new());
            elaborator.reserve_evidence_specifications(&mut specifications, 1)?;
            specifications.push((
                MethodEvidenceOwner::Global(owner),
                requirement,
                method,
                InterfaceApplication::new(interface, Box::new([Type::Unit])),
                Type::Unit,
            ));
            let binders = elaborator
                .enter_lowered_evidence_specifications(specifications, &Origin::Source(span))?;
            elaborator.clear_lowered_evidence_scope(binders)?;
            Ok(elaborator.type_work.used())
        }

        assert!(matches!(
            enter_with_limit(EXACT_WORK - 1),
            Err(TypeError::Internal(
                ElaborationFailure::TypeResourceExhausted
            )),
        ));
        for _ in 0..2 {
            assert_eq!(
                enter_with_limit(EXACT_WORK).expect("a fresh exact scope stage should fit"),
                EXACT_WORK,
            );
        }
    }

    #[test]
    fn checked_type_worklist_capacity_has_an_exact_boundary_and_fresh_retry() {
        // Five visited cells and five independently admitted root/child stack
        // slots: Function(Int, Tuple(Bool, Unit)).
        const EXACT_WORK: usize = 5 + 5;

        fn contains_with_limit(limit: usize) -> Result<(bool, usize), TypeError> {
            let resolved = resolved_module_fixture("checked-type-stack.ash", "", "Unit", "()");
            let mut elaborator = Elaborator::for_module(&resolved)
                .expect("the checked-stack fixture namespace should fit");
            elaborator.type_work = TypeWorkBudget::with_limit(limit);
            let ty = Type::Function(
                Box::new(Type::Int),
                Box::new(Type::Tuple(vec![Type::Bool, Type::Unit].into_boxed_slice())),
            );
            let variables = HashSet::from([TypeVariableId::new(91)]);
            let contains = elaborator.type_contains_any_variable(&ty, &variables)?;
            Ok((contains, elaborator.type_work.used()))
        }

        assert!(matches!(
            contains_with_limit(EXACT_WORK - 1),
            Err(TypeError::Internal(
                ElaborationFailure::TypeResourceExhausted
            )),
        ));
        for _ in 0..2 {
            assert_eq!(contains_with_limit(EXACT_WORK), Ok((false, EXACT_WORK)));
        }
    }

    #[test]
    fn lowered_scheme_retains_source_and_core_binder_kinds() {
        let source = TypeVariableId::resolved(ModuleId::new(3), 5);
        let core = TypeVariableId::generated(7);
        let kind = Kind::Arrow(Box::new(Kind::Type), Box::new(Kind::Type));
        let lowered = LoweredScheme {
            source_type_parameters: Some(Box::new([(source, kind.clone())])),
            type_parameters: Box::new([(core, kind.clone())]),
            requirements: Box::new([]),
            value_type: Type::Unit,
            core_scheme: Type::Forall(Box::new([(core, kind)]), Box::new(Type::Unit)),
        };

        let [(retained_source, source_kind)] = lowered
            .source_binder_parameters()
            .expect("the lowered implementation scheme should retain source binders")
        else {
            panic!("the lowered implementation scheme should retain one source binder");
        };
        let [(retained_core, core_kind)] = lowered.binder_parameters() else {
            panic!("the lowered scheme should retain one Core binder");
        };
        assert_eq!((*retained_source, source_kind), (source, core_kind));
        assert_eq!(*retained_core, core);
        assert_eq!(
            core_kind,
            &Kind::Arrow(Box::new(Kind::Type), Box::new(Kind::Type))
        );
    }

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

    struct PublicAuthorizationGraphFixture(PathBuf);

    impl PublicAuthorizationGraphFixture {
        fn create(width: usize) -> Self {
            use std::fmt::Write as _;

            loop {
                let id = MODULE_FIXTURE_IDS.fetch_add(1, Ordering::Relaxed);
                let directory = std::env::temp_dir().join(format!(
                    "ash-public-authorization-graph-{}-{id}",
                    std::process::id(),
                ));
                match fs::create_dir(&directory) {
                    Ok(()) => {
                        let mut base =
                            String::from("pub interface Show<A> {\nshow : A -> A\n}\n\n");
                        for index in 0..width {
                            writeln!(base, "pub type Head{index} = Head{index}")
                                .expect("writing to a String cannot fail");
                            writeln!(
                                base,
                                "pub impl Show<Head{index}> {{\nshow value = value\n}}"
                            )
                            .expect("writing to a String cannot fail");
                        }
                        fs::write(directory.join("base.ash"), base)
                            .expect("the implementation owner should be writable");
                        fs::write(
                            directory.join("facade.ash"),
                            "pub import base (Show, impl Show)\n",
                        )
                        .expect("the implementation facade should be writable");
                        fs::write(
                            directory.join("entry.ash"),
                            concat!(
                                "pub import facade (Show, impl Show)\n",
                                "main : Unit -> Unit\n",
                                "main () = ()\n",
                            ),
                        )
                        .expect("the implementation entry should be writable");
                        return Self(directory);
                    }
                    Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
                    Err(error) => {
                        panic!("the public-authorization graph should be creatable: {error}")
                    }
                }
            }
        }
    }

    impl Drop for PublicAuthorizationGraphFixture {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.0);
        }
    }

    fn link_public_authorization_fixture_with_limit(
        width: usize,
        limit: usize,
    ) -> (Result<ResolvedModuleProgram, TypeError>, usize) {
        let fixture = PublicAuthorizationGraphFixture::create(width);
        let graph = load_module_graph(&fixture.0.join("entry.ash"), &ModuleRoots::empty())
            .expect("the public-authorization graph should load");
        let mut checked = Vec::new();
        for module in graph.modules() {
            let dependencies = module
                .dependencies()
                .iter()
                .map(|edge| {
                    let dependency = checked
                        .iter()
                        .find(|checked: &&CheckedModule| checked.module() == edge.target())
                        .expect("dependencies should check before their importers");
                    DependencyExports::new(edge, dependency.exports())
                        .expect("the loaded edge should match its checked summary")
                })
                .collect::<Vec<_>>();
            let resolved = resolve_module(module, &dependencies)
                .expect("the explicit public implementation graph should resolve");
            checked.push(
                check_module(resolved)
                    .expect("the graph's distinct nominal implementation heads should check"),
            );
        }
        let mut constraint_work = InterfaceConstraintBudget::with_limit(limit);
        let result = link_modules_with_budget(checked, graph.entry(), &mut constraint_work);
        (result, constraint_work.used())
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

    #[test]
    fn newtype_representation_graph_has_an_isolated_retryable_type_work_boundary() {
        fn fixture() -> ResolvedModule {
            resolved_module_fixture(
                "newtype-representation-work.ash",
                "newtype UserId = UserId(Int)",
                "Unit",
                "()",
            )
        }

        let resolved = fixture();
        let mut measured_type_work = TypeWorkBudget::unbounded();
        check_newtype_representation_cycles(&resolved, &mut measured_type_work)
            .expect("the isolated newtype representation graph should check");
        let exact_work = measured_type_work.used();
        assert!(exact_work > 0);

        let mut short_type_work = TypeWorkBudget::with_limit(exact_work - 1);
        let failure = check_newtype_representation_cycles(&resolved, &mut short_type_work)
            .expect_err("one graph work cell short must not admit a graph");
        let TypeError::Internal(failure) = failure else {
            panic!("graph budget exhaustion must remain an internal resource failure");
        };
        assert_eq!(failure.reason_code(), "internal.resource.type-work");

        let mut exact_type_work = TypeWorkBudget::with_limit(exact_work);
        check_newtype_representation_cycles(&resolved, &mut exact_type_work)
            .expect("the exact isolated graph budget should be retryable");
        assert_eq!(exact_type_work.used(), exact_work);

        let ordinary = resolved_module_fixture(
            "ordinary-data-does-not-build-newtype-graph.ash",
            "type UserId = UserId(Int)",
            "Unit",
            "()",
        );
        let mut ordinary_work = TypeWorkBudget::with_limit(0);
        check_newtype_representation_cycles(&ordinary, &mut ordinary_work)
            .expect("ordinary data must not allocate a newtype representation graph");
        assert_eq!(ordinary_work.used(), 0);
    }

    #[test]
    fn newtype_representation_graph_is_stack_safe_for_wide_accepted_and_rejected_modules() {
        const WIDTH: usize = 2_048;

        std::thread::Builder::new()
            .name("newtype-representation-graph-wide".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let declarations = |closes_cycle: bool| {
                    let mut source = String::new();
                    for index in 0..WIDTH {
                        let representation = if index + 1 == WIDTH {
                            if closes_cycle { "N0" } else { "Int" }.to_owned()
                        } else {
                            format!("N{}", index + 1)
                        };
                        source
                            .push_str(&format!("newtype N{index} = N{index}({representation})\n"));
                    }
                    source
                };

                let accepted = resolved_module_fixture(
                    "wide-newtype-graph-accepted.ash",
                    &declarations(false),
                    "Unit",
                    "()",
                );
                check_newtype_representation_cycles(&accepted, &mut TypeWorkBudget::unbounded())
                    .expect("the wide acyclic newtype graph should check");
                drop(accepted);

                let rejected = resolved_module_fixture(
                    "wide-newtype-graph-rejected.ash",
                    &declarations(true),
                    "Unit",
                    "()",
                );
                assert!(matches!(
                    check_newtype_representation_cycles(
                        &rejected,
                        &mut TypeWorkBudget::unbounded(),
                    ),
                    Err(TypeError::Source(error))
                        if error.reason == TypeReason::NewtypeRecursiveRepresentation
                ));
                drop(rejected);
            })
            .expect("wide graph thread should start")
            .join()
            .expect("wide graph checking and teardown must fit the small stack");
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
    fn selected_method_rigidity_has_exact_retryable_traversal_boundary() {
        const EXACT_TYPE_WORK: usize = 1 + 2;

        let resolved =
            resolved_module_fixture("selected-method-rigidity-budget.ash", "", "Unit", "()");
        let span = fixture_result(&resolved).span;
        let method_arguments = [Type::Int];
        let rigid_arguments = [Type::Int];
        let check = MethodRigidityCheck::for_test(
            &method_arguments,
            &rigid_arguments,
            MethodRigiditySite::application(span, span, span),
        );
        let mut elaborator =
            Elaborator::for_module(&resolved).expect("the rigidity fixture should initialize");

        elaborator.type_work = TypeWorkBudget::with_limit(EXACT_TYPE_WORK - 1);
        assert!(matches!(
            elaborator.enforce_selected_method_rigidity(check),
            Err(TypeError::Internal(
                ElaborationFailure::TypeResourceExhausted
            ))
        ));

        elaborator.type_work = TypeWorkBudget::with_limit(EXACT_TYPE_WORK);
        elaborator
            .enforce_selected_method_rigidity(check)
            .expect("the exact traversal and one concrete comparison should fit");
        assert_eq!(elaborator.type_work.used(), EXACT_TYPE_WORK);
    }

    #[test]
    fn module_failure_publishes_no_earlier_occurrence_selection() {
        let resolved = resolved_module_fixture(
            "atomic-occurrence-publication.ash",
            concat!(
                "interface Convert<A> {\nconvert : A -> A\n}\n\n",
                "impl Convert<Int> {\nconvert value = value\n}\n\n",
                "first : Unit -> Int\nfirst () = convert 42\n",
            ),
            "Int",
            "true",
        );
        let ResolvedDefinitionKind::Equational(first) = &resolved.definitions()[0].kind else {
            panic!("the first definition should be equational");
        };
        let ResolvedExprKind::Apply(application) = &first.equations[0].body.kind else {
            panic!("the first body should apply the interface method");
        };
        let ResolvedExprKind::Occurrence(occurrence) = &application.function.kind else {
            panic!("the application function should be the interface method occurrence");
        };
        let [slot] = occurrence.evidence.as_ref() else {
            panic!("the method occurrence should own one evidence slot");
        };
        let handle = slot.handle();

        let error = check_module(resolved)
            .expect_err("the later main result mismatch should reject the complete module");

        assert!(matches!(
            error,
            TypeError::Source(_) | TypeError::Mismatch(_)
        ));
        assert!(
            handle.selection().is_none(),
            "an earlier choice must remain private when a later body rejects the module"
        );
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

    fn deep_application_type(depth: usize) -> Type {
        let mut ty = Type::Int;
        for _ in 0..depth {
            ty = Type::Application(Box::new(ty), Box::new(Type::Unit));
        }
        ty
    }

    fn deep_generated_origin(depth: usize, span: Span) -> Origin {
        let mut origin = Origin::Source(span);
        for _ in 0..depth {
            origin = Origin::Generated {
                cause: Box::new(origin),
                reason: GeneratedReason::FunctionLowering,
            };
        }
        origin
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
        const EXACT_WORK: usize = 2 * WIDTH + 2;
        let parameters = (0..WIDTH)
            .map(|index| {
                (
                    TypeVariableId::new(u32::try_from(index).expect("parameter identity")),
                    Kind::Type,
                )
            })
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
        // A monomorphic private interface retains no method-binder authority.
        // Unconditional arity preflight adds one interface-map cell plus the
        // interface and global declaration visits.
        const EXACT_WORK: usize = 39 + 1 + 2;
        let mut short = InterfaceConstraintBudget::with_limit(EXACT_WORK - 1);

        let failure =
            check_module_with_budget(short_module, &mut type_work, &mut coverage_work, &mut short)
                .expect_err("one missing unit should reject one interface");
        assert_eq!(
            failure,
            TypeError::Internal(ElaborationFailure::ConstraintResourceExhausted)
        );
        assert_eq!(short.used(), EXACT_WORK - 1);

        let mut type_work = TypeWorkBudget::default();
        let mut coverage_work = UsefulnessBudget::default();
        let mut constraint_work = InterfaceConstraintBudget::with_limit(EXACT_WORK);

        check_module_with_budget(
            first,
            &mut type_work,
            &mut coverage_work,
            &mut constraint_work,
        )
        .expect("one interface should fit the exact constraint budget");
        assert_eq!(constraint_work.used(), EXACT_WORK);
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
    fn relational_interface_shape_has_an_exact_declaration_guard_boundary() {
        // Application arity preflight owns one interface-map cell and visits
        // the interface and global declarations once. One interface-vector
        // cell, one declaration cell, and one method cell then precede complete
        // occurrence walks for First (five cells) and absent Second (six).
        const EXACT_WORK: usize = (1 + 2) + 1 + 1 + 1 + 5 + 6;
        let declarations =
            "interface Relational<First, Second> {\nrelational : First -> First\n}\n";

        let short_module = resolved_module_fixture(
            "short-relational-interface-guard.ash",
            declarations,
            "Unit",
            "()",
        );
        let mut short = InterfaceConstraintBudget::with_limit(EXACT_WORK - 1);
        assert_eq!(
            check_interface_declarations(&short_module, &mut short),
            Err(TypeError::Internal(
                ElaborationFailure::ConstraintResourceExhausted
            ))
        );

        let exact_module = resolved_module_fixture(
            "exact-relational-interface-guard.ash",
            declarations,
            "Unit",
            "()",
        );
        for _ in 0..2 {
            let mut exact = InterfaceConstraintBudget::with_limit(EXACT_WORK);
            let error = check_interface_declarations(&exact_module, &mut exact)
                .expect_err("the exact budget should reach the missing-parameter diagnostic");
            let TypeError::Interface(diagnostic) = error else {
                panic!("a missing relational method parameter must remain a source error");
            };
            assert_eq!(diagnostic.reason, InterfaceReason::MethodParameter);
            assert_eq!(exact.used(), EXACT_WORK);
        }
    }

    #[test]
    fn determination_related_label_has_an_exact_retryable_declaration_boundary() {
        // Application arity preflight owns one interface-map cell plus the
        // interface and global declaration visits. Interface admission owns
        // one vector cell and one declaration cell, then two total-partition
        // visits, three source-occurrence cells, three ordered-side visits,
        // and the retained related label on the repeated occurrence.
        const EXACT_WORK: usize = (1 + 2) + 1 + 1 + 2 + 3 + 3 + 1;
        let module = resolved_module_fixture(
            "determination-related-label-budget.ash",
            "interface Bad<A, B> where (A, A) -> B {\nbad : A -> B\n}\n",
            "Unit",
            "()",
        );
        let determination = module.interfaces()[0]
            .determination
            .as_ref()
            .expect("the fixture should retain its source determination");
        assert_eq!(determination.determinant.parameters.len(), 2);
        assert_eq!(determination.dependent.parameters.len(), 1);

        let mut short = InterfaceConstraintBudget::with_limit(EXACT_WORK - 1);
        assert_eq!(
            check_interface_declarations(&module, &mut short),
            Err(TypeError::Internal(
                ElaborationFailure::ConstraintResourceExhausted
            ))
        );
        assert_eq!(short.used(), EXACT_WORK - 1);

        for _ in 0..2 {
            let mut exact = InterfaceConstraintBudget::with_limit(EXACT_WORK);
            let error = check_interface_declarations(&module, &mut exact)
                .expect_err("the exact retry should retain the causal occurrence label");
            let TypeError::Interface(diagnostic) = error else {
                panic!("a repeated determination member must remain a source error");
            };
            assert_eq!(diagnostic.reason, InterfaceReason::DeterminationParameter);
            assert_eq!(diagnostic.related.len(), 1);
            assert_eq!(exact.used(), EXACT_WORK);
            assert_eq!(exact.charge(1), Err(()));
            assert_eq!(determination.determinant.parameters.len(), 2);
            assert_eq!(determination.dependent.parameters.len(), 1);
        }
    }

    #[test]
    fn checked_determinations_retain_exact_private_declaration_positions() {
        let module = resolved_module_fixture(
            "checked-determination-positions.ash",
            concat!(
                "interface Iterable<I, Item> where I -> Item {\n",
                "next : I -> Item\n",
                "}\n\n",
                "interface Decode<Format, Source, Value> where (Format, Source) -> Value {\n",
                "decode : (Format, Source) -> Value\n",
                "}\n\n",
                "interface Lookup<Key, Value, Context> where (Key, Context) -> Value {\n",
                "lookup : (Key, Context) -> Value\n",
                "}\n",
            ),
            "Unit",
            "()",
        );
        let checked =
            check_interface_declarations(&module, &mut InterfaceConstraintBudget::default())
                .expect("all total determinations should reach checked publication");
        let cases: [(&[usize], &[&str], &[&str]); 3] = [
            (&[0], &["I"], &["Item"]),
            (&[0, 1], &["Format", "Source"], &["Value"]),
            (&[0, 2], &["Key", "Context"], &["Value"]),
        ];

        for ((source, token), (expected_positions, expected_key, expected_dependents)) in
            module.interfaces().iter().zip(&checked).zip(cases)
        {
            let positions = token
                .determinant_positions()
                .expect("each fixture interface should retain a determinant key");
            assert_eq!(positions, expected_positions);
            assert_eq!(
                positions
                    .iter()
                    .map(|position| source.parameters[*position].spelling.as_str())
                    .collect::<Vec<_>>(),
                expected_key,
            );

            let mut next_determinant = positions.iter().copied().peekable();
            assert_eq!(
                source
                    .parameters
                    .iter()
                    .enumerate()
                    .filter_map(|(position, parameter)| {
                        if next_determinant.peek() == Some(&position) {
                            next_determinant.next();
                            None
                        } else {
                            Some(parameter.spelling.as_str())
                        }
                    })
                    .collect::<Vec<_>>(),
                expected_dependents,
            );
        }
    }

    #[test]
    fn determination_coverage_has_an_exact_retryable_constraint_boundary() {
        // One determinant-position validation, two ordered argument visits,
        // two dependent-FV traversal cells, one key-position/argument pair,
        // two key-type traversal cells, and three retained-label visits.
        const EXACT_WORK: usize = 1 + 2 + 2 + 2 + 2 + 3;
        let module = resolved_module_fixture(
            "determination-coverage-budget.ash",
            concat!(
                "interface Relation<A, B> where A -> B {\n",
                "relate : A -> Int\n",
                "}\n\n",
                "impl<B> Relation<Int, B> {\n",
                "relate value = 0\n",
                "}\n",
            ),
            "Unit",
            "()",
        );
        let checked =
            check_interface_declarations(&module, &mut InterfaceConstraintBudget::default())
                .expect("the determined interface should admit its key");
        let implementation = &module.implementations()[0];
        let interface = checked_interface(
            &module,
            &checked,
            implementation.head.interface.id,
            &mut InterfaceConstraintBudget::default(),
        )
        .expect("the checked-interface lookup should fit")
        .expect("the implementation interface should be checked");

        let mut short = InterfaceConstraintBudget::with_limit(EXACT_WORK - 1);
        assert_eq!(
            check_implementation_determination_coverage(
                &module,
                interface,
                implementation,
                &mut short,
            ),
            Err(TypeError::Internal(
                ElaborationFailure::ConstraintResourceExhausted
            ))
        );
        assert_eq!(short.used(), EXACT_WORK - 1);
        assert_eq!(implementation.head.arguments.len(), 2);

        let mut exact = InterfaceConstraintBudget::with_limit(EXACT_WORK);
        let error = check_implementation_determination_coverage(
            &module,
            interface,
            implementation,
            &mut exact,
        )
        .expect_err("the exact retry should reach determination coverage");
        assert!(matches!(
            error,
            TypeError::Interface(diagnostic)
                if diagnostic.reason == InterfaceReason::ImplDeterminationCoverage
        ));
        assert_eq!(exact.used(), EXACT_WORK);
        assert_eq!(exact.charge(1), Err(()));
        assert_eq!(implementation.head.arguments.len(), 2);
    }

    #[test]
    fn determined_prerequisite_decrease_has_an_exact_retryable_key_boundary() {
        // Each determinant-key extraction owns one position validation and one
        // selected-argument visit. Retaining both complete prerequisite
        // arguments owns two visits. Complete groundness then visits A and
        // List<A> (eight), while the aligned key component and strict-subterm
        // walk own nine more visits.
        const EXACT_WORK: usize = (1 + 1) + 2 + (1 + 1) + 8 + 9;
        let module = resolved_module_fixture(
            "determined-prerequisite-budget.ash",
            concat!(
                "type List<A> =\nNil\n| Cons(A, List<A>)\n",
                "interface Relation<A, B> where A -> B {\n",
                "relate : A -> Int\n",
                "}\n\n",
                "impl<A> Relation<List<A>, A> where Relation<A, List<A>> {\n",
                "relate value = 0\n",
                "}\n",
            ),
            "Unit",
            "()",
        );
        let checked =
            check_interface_declarations(&module, &mut InterfaceConstraintBudget::default())
                .expect("the determined interface should admit its key");
        let implementation = &module.implementations()[0];
        let interface = checked_interface(
            &module,
            &checked,
            implementation.head.interface.id,
            &mut InterfaceConstraintBudget::default(),
        )
        .expect("the checked-interface lookup should fit")
        .expect("the implementation interface should be checked");
        let prerequisite = &implementation.prerequisites[0];

        let exercise = |budget: &mut InterfaceConstraintBudget| -> Result<bool, TypeError> {
            let head_key =
                collect_selection_key_types(interface, &implementation.head.arguments, budget)?;
            budget
                .charge(prerequisite.application.arguments.len())
                .map_err(|()| constraint_resource())?;
            let mut complete_prerequisite = Vec::new();
            complete_prerequisite
                .try_reserve_exact(prerequisite.application.arguments.len())
                .map_err(|_| constraint_resource())?;
            complete_prerequisite.extend(
                prerequisite
                    .application
                    .arguments
                    .iter()
                    .map(|argument| &argument.ty),
            );
            let prerequisite_key = collect_selection_key_types(
                interface,
                &prerequisite.application.arguments,
                budget,
            )?;
            implementation_prerequisite_selection_key_terminates(
                &complete_prerequisite,
                &prerequisite_key,
                &head_key,
                budget,
            )
            .map_err(|()| constraint_resource())
        };

        let mut short = InterfaceConstraintBudget::with_limit(EXACT_WORK - 1);
        assert_eq!(
            exercise(&mut short),
            Err(TypeError::Internal(
                ElaborationFailure::ConstraintResourceExhausted
            ))
        );
        assert_eq!(short.used(), EXACT_WORK - 1);
        assert_eq!(implementation.head.arguments.len(), 2);
        assert_eq!(prerequisite.application.arguments.len(), 2);

        let mut exact = InterfaceConstraintBudget::with_limit(EXACT_WORK);
        assert_eq!(exercise(&mut exact), Ok(true));
        assert_eq!(exact.used(), EXACT_WORK);
        assert_eq!(exact.charge(1), Err(()));
        assert_eq!(implementation.head.arguments.len(), 2);
        assert_eq!(prerequisite.application.arguments.len(), 2);
    }

    #[test]
    fn selection_key_collection_precharges_slots_before_reserving_and_is_retryable() {
        let no_edge_module = resolved_module_fixture(
            "no-edge-selection-key-storage-budget.ash",
            concat!(
                "interface Pair<A, B> {\n",
                "pair : (A, B) -> Int\n",
                "}\n\n",
                "impl Pair<Int, Bool> {\n",
                "pair value = 0\n",
                "}\n",
            ),
            "Unit",
            "()",
        );
        let no_edge_checked = check_interface_declarations(
            &no_edge_module,
            &mut InterfaceConstraintBudget::default(),
        )
        .expect("the ordinary interface should check");
        let no_edge_implementation = &no_edge_module.implementations()[0];
        let no_edge_interface = checked_interface(
            &no_edge_module,
            &no_edge_checked,
            no_edge_implementation.head.interface.id,
            &mut InterfaceConstraintBudget::default(),
        )
        .expect("the ordinary interface lookup should fit")
        .expect("the ordinary interface should be checked");

        let mut no_edge_short = InterfaceConstraintBudget::with_limit(1);
        assert_eq!(
            collect_selection_key_types(
                no_edge_interface,
                &no_edge_implementation.head.arguments,
                &mut no_edge_short,
            ),
            Err(TypeError::Internal(
                ElaborationFailure::ConstraintResourceExhausted
            ))
        );
        assert_eq!(
            no_edge_short.used(),
            0,
            "the two-slot storage charge is atomic before reserve"
        );
        let mut no_edge_exact = InterfaceConstraintBudget::with_limit(2);
        let no_edge_key = collect_selection_key_types(
            no_edge_interface,
            &no_edge_implementation.head.arguments,
            &mut no_edge_exact,
        )
        .expect("the exact no-edge retry should retain both arguments");
        assert_eq!(no_edge_key, [&Type::Int, &Type::Bool]);
        assert_eq!(no_edge_exact.used(), 2);

        let determined_module = resolved_module_fixture(
            "determined-selection-key-storage-budget.ash",
            concat!(
                "interface Triple<A, B, C> where (A, B) -> C {\n",
                "triple : (A, B) -> Int\n",
                "}\n\n",
                "impl Triple<Int, Bool, Unit> {\n",
                "triple value = 0\n",
                "}\n",
            ),
            "Unit",
            "()",
        );
        let determined_checked = check_interface_declarations(
            &determined_module,
            &mut InterfaceConstraintBudget::default(),
        )
        .expect("the determined interface should check");
        let determined_implementation = &determined_module.implementations()[0];
        let determined_interface = checked_interface(
            &determined_module,
            &determined_checked,
            determined_implementation.head.interface.id,
            &mut InterfaceConstraintBudget::default(),
        )
        .expect("the determined interface lookup should fit")
        .expect("the determined interface should be checked");

        // Two position validations precede one atomic two-slot charge.
        let mut determined_short = InterfaceConstraintBudget::with_limit(3);
        assert_eq!(
            collect_selection_key_types(
                determined_interface,
                &determined_implementation.head.arguments,
                &mut determined_short,
            ),
            Err(TypeError::Internal(
                ElaborationFailure::ConstraintResourceExhausted
            ))
        );
        assert_eq!(determined_short.used(), 2);
        let mut determined_exact = InterfaceConstraintBudget::with_limit(4);
        let determined_key = collect_selection_key_types(
            determined_interface,
            &determined_implementation.head.arguments,
            &mut determined_exact,
        )
        .expect("the exact determined retry should retain both key arguments");
        assert_eq!(determined_key, [&Type::Int, &Type::Bool]);
        assert_eq!(determined_exact.used(), 4);
    }

    #[test]
    fn determined_non_decreasing_header_retains_its_label_at_an_exact_retryable_boundary() {
        // Header staging and complete type authentication own 21 visits; the
        // ordered prerequisite-relation scan owns one interface lookup;
        // variable-head selection owns two; determination coverage owns 13;
        // key/reference staging owns seven; complete-groundness plus the
        // aligned equality comparison own 15; the causal label owns one.
        const EXACT_WORK: usize = 21 + 1 + 2 + 13 + 7 + 15 + 1;
        let module = resolved_module_fixture(
            "determined-non-decreasing-header-budget.ash",
            concat!(
                "type List<A> =\nNil\n| Cons(A, List<A>)\n",
                "interface Relation<A, B> where A -> B {\n",
                "relate : A -> Int\n",
                "}\n\n",
                "impl<A> Relation<List<A>, A> where Relation<List<A>, A> {\n",
                "relate value = 0\n",
                "}\n",
            ),
            "Unit",
            "()",
        );
        let checked =
            check_interface_declarations(&module, &mut InterfaceConstraintBudget::default())
                .expect("the determined interface should admit its key");
        let implementation = &module.implementations()[0];

        let mut short = InterfaceConstraintBudget::with_limit(EXACT_WORK - 1);
        assert_eq!(
            check_implementation_header(&module, &checked, implementation, &mut short),
            Err(TypeError::Internal(
                ElaborationFailure::ConstraintResourceExhausted
            ))
        );
        assert_eq!(short.used(), EXACT_WORK - 1);
        assert_eq!(implementation.head.arguments.len(), 2);
        assert_eq!(implementation.prerequisites.len(), 1);

        let mut exact = InterfaceConstraintBudget::with_limit(EXACT_WORK);
        let error = check_implementation_header(&module, &checked, implementation, &mut exact)
            .expect_err("the exact retry should publish the non-decreasing diagnostic");
        assert!(matches!(
            error,
            TypeError::Interface(diagnostic)
                if diagnostic.reason == InterfaceReason::ImplPrerequisiteNotDecreasing
                    && diagnostic.related.len() == 1
        ));
        assert_eq!(exact.used(), EXACT_WORK);
        assert_eq!(exact.charge(1), Err(()));
        assert_eq!(implementation.head.arguments.len(), 2);
        assert_eq!(implementation.prerequisites.len(), 1);
    }

    #[test]
    fn determined_prerequisite_conflict_has_an_exact_retryable_header_boundary() {
        // Header staging and complete type authentication own 17 visits. Two
        // prerequisite-interface lookups, one pair visit, the four-cell full
        // comparison, the three-cell determinant comparison, and one retained
        // causal label add eleven more visits.
        const EXACT_WORK: usize = 17 + 2 + 1 + 4 + 3 + 1;
        let module = resolved_module_fixture(
            "determined-prerequisite-conflict-budget.ash",
            concat!(
                "interface Relation<Key, Value> where Key -> Value {\n",
                "relate : Key -> Int\n",
                "}\n\n",
                "interface Target<A> {\n",
                "target : A -> A\n",
                "}\n\n",
                "impl Target<Int> where Relation<Int, Bool>, Relation<Int, Unit> {\n",
                "target value = value\n",
                "}\n",
            ),
            "Unit",
            "()",
        );
        let checked =
            check_interface_declarations(&module, &mut InterfaceConstraintBudget::default())
                .expect("both interfaces should admit their declarations");
        let implementation = &module.implementations()[0];

        let mut short = InterfaceConstraintBudget::with_limit(EXACT_WORK - 1);
        assert_eq!(
            check_implementation_header(&module, &checked, implementation, &mut short),
            Err(TypeError::Internal(
                ElaborationFailure::ConstraintResourceExhausted
            ))
        );
        assert_eq!(short.used(), EXACT_WORK - 1);
        assert_eq!(implementation.prerequisites.len(), 2);

        for _ in 0..2 {
            let mut exact = InterfaceConstraintBudget::with_limit(EXACT_WORK);
            let error = check_implementation_header(&module, &checked, implementation, &mut exact)
                .expect_err("the exact retry should publish the prerequisite-key conflict");
            assert!(matches!(
                error,
                TypeError::Interface(diagnostic)
                    if diagnostic.reason == InterfaceReason::DeterminationConflict
                        && diagnostic.related.len() == 1
            ));
            assert_eq!(exact.used(), EXACT_WORK);
            assert_eq!(exact.charge(1), Err(()));
            assert_eq!(implementation.prerequisites.len(), 2);
        }
    }

    #[test]
    fn determined_variable_head_selection_has_an_exact_retryable_boundary() {
        const EXACT_WORK: usize = 1 + 1;
        let module = resolved_module_fixture(
            "determined-variable-head-budget.ash",
            concat!(
                "interface Relation<A, B> where A -> B {\n",
                "relate : A -> Int\n",
                "}\n\n",
                "impl<A> Relation<A, Bool> {\n",
                "relate value = 0\n",
                "}\n",
            ),
            "Unit",
            "()",
        );
        let checked =
            check_interface_declarations(&module, &mut InterfaceConstraintBudget::default())
                .expect("the determined interface should admit its key");
        let implementation = &module.implementations()[0];
        let interface = checked_interface(
            &module,
            &checked,
            implementation.head.interface.id,
            &mut InterfaceConstraintBudget::default(),
        )
        .expect("the checked-interface lookup should fit")
        .expect("the implementation interface should be checked");

        let mut short = InterfaceConstraintBudget::with_limit(EXACT_WORK - 1);
        assert_eq!(
            selection_key_is_all_bare_variables(
                interface,
                &implementation.head.arguments,
                &mut short,
            ),
            Err(TypeError::Internal(
                ElaborationFailure::ConstraintResourceExhausted
            ))
        );
        assert_eq!(short.used(), EXACT_WORK - 1);
        assert_eq!(implementation.head.arguments.len(), 2);

        let mut exact = InterfaceConstraintBudget::with_limit(EXACT_WORK);
        assert_eq!(
            selection_key_is_all_bare_variables(
                interface,
                &implementation.head.arguments,
                &mut exact,
            ),
            Ok(true)
        );
        assert_eq!(exact.used(), EXACT_WORK);
        assert_eq!(exact.charge(1), Err(()));
        assert_eq!(implementation.head.arguments.len(), 2);
    }

    #[test]
    fn determined_orphan_selection_has_an_exact_retryable_boundary() {
        // One determinant-position validation plus the selected argument and
        // its accepted outer-spine visit.
        const EXACT_WORK: usize = 1 + 2;
        let module = resolved_module_fixture(
            "determined-orphan-budget.ash",
            concat!(
                "type Local = Local\n",
                "interface Relation<A, B> where A -> B {\n",
                "relate : A -> Int\n",
                "}\n\n",
                "impl Relation<Int, Local> {\n",
                "relate value = 0\n",
                "}\n",
            ),
            "Unit",
            "()",
        );
        let checked =
            check_interface_declarations(&module, &mut InterfaceConstraintBudget::default())
                .expect("the determined interface should admit its key");
        let implementation = &module.implementations()[0];
        let interface = checked_interface(
            &module,
            &checked,
            implementation.head.interface.id,
            &mut InterfaceConstraintBudget::default(),
        )
        .expect("the checked-interface lookup should fit")
        .expect("the implementation interface should be checked");

        let mut short = InterfaceConstraintBudget::with_limit(EXACT_WORK - 1);
        assert_eq!(
            selection_key_has_local_outer_nominal(
                interface,
                &implementation.head.arguments,
                module.module(),
                &mut short,
            ),
            Err(TypeError::Internal(
                ElaborationFailure::ConstraintResourceExhausted
            ))
        );
        assert_eq!(short.used(), 1, "the two-unit outer-spine visit is atomic");
        assert_eq!(implementation.head.arguments.len(), 2);

        let mut exact = InterfaceConstraintBudget::with_limit(EXACT_WORK);
        assert_eq!(
            selection_key_has_local_outer_nominal(
                interface,
                &implementation.head.arguments,
                module.module(),
                &mut exact,
            ),
            Ok(false)
        );
        assert_eq!(exact.used(), EXACT_WORK);
        assert_eq!(exact.charge(1), Err(()));
        assert_eq!(implementation.head.arguments.len(), 2);
    }

    #[test]
    fn link_retains_public_authorization_tables_at_an_exact_limit() {
        const WIDTH: usize = 8;

        let (measured, exact_limit) =
            link_public_authorization_fixture_with_limit(WIDTH, 1_000_000);
        measured.expect("the generous link budget should measure complete table retention");

        let (short, _) = link_public_authorization_fixture_with_limit(WIDTH, exact_limit - 1);
        let error = short.expect_err("one missing unit should reject linked table retention");
        assert_eq!(
            error,
            TypeError::Internal(ElaborationFailure::ConstraintResourceExhausted)
        );

        let (exact, exact_used) = link_public_authorization_fixture_with_limit(WIDTH, exact_limit);
        let program = exact.expect("the measured link budget should retain every public route");
        assert_eq!(exact_used, exact_limit);
        assert_eq!(program.groups().len(), 3);

        let group_for_route_length = |route_length| {
            program
                .groups()
                .iter()
                .find(|group| {
                    let table = group.public_implementation_authorizations();
                    table.len() == WIDTH
                        && table.iter().all(|authorization| {
                            authorization.authorization().hops().len() == route_length
                        })
                })
                .expect("each dependency layer should retain one uniform lightweight table")
        };
        let base = group_for_route_length(0);
        let facade = group_for_route_length(1);
        let entry = group_for_route_length(2);
        let implementation_ids = |group: &ResolvedModuleGroup| {
            group
                .public_implementation_authorizations()
                .iter()
                .map(|authorization| authorization.id())
                .collect::<Vec<_>>()
        };

        assert_eq!(implementation_ids(facade), implementation_ids(base));
        assert_eq!(implementation_ids(entry), implementation_ids(base));
        assert_eq!(base.implementations().len(), WIDTH);
        assert_eq!(base.implementation_facts().len(), WIDTH);
        assert!(facade.implementations().is_empty());
        assert!(facade.implementation_facts().is_empty());
        assert!(entry.implementations().is_empty());
        assert!(entry.implementation_facts().is_empty());
    }

    #[test]
    fn impl_method_substitution_uses_the_exact_constraint_budget() {
        // The interface and implementation method relation form one complete
        // check-and-freeze boundary. Complete-application staging and matching
        // add eight aligned root cells to the predecessor boundary. Global
        // arity preflight adds one interface-map cell, visits the interface,
        // implementation, and global declarations, and checks the head.
        const EXACT_WORK: usize = 84 + 8 + 1 + 3 + 1;
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
        let mut short = InterfaceConstraintBudget::with_limit(EXACT_WORK - 1);

        let failure =
            check_module_with_budget(short_module, &mut type_work, &mut coverage_work, &mut short)
                .expect_err("one missing unit should reject the method substitution");
        assert_eq!(
            failure,
            TypeError::Internal(ElaborationFailure::ConstraintResourceExhausted)
        );

        let mut type_work = TypeWorkBudget::default();
        let mut coverage_work = UsefulnessBudget::default();
        let mut exact = InterfaceConstraintBudget::with_limit(EXACT_WORK);
        check_module_with_budget(exact_module, &mut type_work, &mut coverage_work, &mut exact)
            .expect("the exact budget should admit one implementation method");

        assert_eq!(exact.used(), EXACT_WORK);
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
                        parameters: vec![ResolvedTypeVariable {
                            id: parameter_id,
                            spelling: "A".to_owned(),
                            kind: crate::types::Kind::Type,
                            origin: Origin::Source(span),
                        }]
                        .into_boxed_slice(),
                        determination: None,
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
                            has_explicit_type_parameters: false,
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
    fn distinct_reexported_implementations_conflict_at_the_first_combined_closure() {
        let source = SourceFile::new("import-overlap.ash", "abcdefghijklmnopqrstuvwx")
            .expect("the overlap span fixture should fit");
        let span = |start, end| {
            source
                .span(ByteRange::new(start, end).expect("the span should be ordered"))
                .expect("the span should belong to the fixture")
        };
        let first_definition = span(0, 2);
        let first_route = span(3, 5);
        let first_route_suffix = span(6, 8);
        let second_definition = span(9, 11);
        let second_route = span(12, 14);
        let second_route_suffix = span(15, 17);
        let module = resolved_module_fixture(
            "overlap-authority.ash",
            "interface Equal<A> {\nequal : (A, A) -> Bool\n}\n",
            "Unit",
            "()",
        );
        let _checked_interfaces =
            check_interface_declarations(&module, &mut InterfaceConstraintBudget::default())
                .expect("the overlap authority interface should check");
        let interface = module.interfaces()[0].id;
        let registry = module
            .registry()
            .checker_view(module.imported_facts(), &mut TypeWorkBudget::default())
            .expect("the overlap authority registry should build");
        let first = crate::resolved::ImportedImplementationFact {
            fact: CheckedImplementationFact {
                id: crate::interface::ImplId::new(ModuleId::new(90), 0),
                application: InterfaceApplication::new(interface, Box::new([Type::Int])),
                head_parameters: Box::new([]),
                prerequisites: Box::new([]),
                methods: Box::new([]),
                origin: Origin::Source(first_definition),
                span: first_definition,
            },
            authorization: crate::resolved::ImplementationAuthorization::from_hops(vec![
                crate::resolved::ImplementationRouteHop {
                    from: ModuleId::new(1),
                    to: ModuleId::new(80),
                    import_span: first_route,
                },
                crate::resolved::ImplementationRouteHop {
                    from: ModuleId::new(80),
                    to: ModuleId::new(90),
                    import_span: first_route_suffix,
                },
            ]),
            public_authorization: None,
        };
        let second = crate::resolved::ImportedImplementationFact {
            fact: CheckedImplementationFact {
                id: crate::interface::ImplId::new(ModuleId::new(10), 0),
                application: InterfaceApplication::new(interface, Box::new([Type::Int])),
                head_parameters: Box::new([]),
                prerequisites: Box::new([]),
                methods: Box::new([]),
                origin: Origin::Source(second_definition),
                span: second_definition,
            },
            authorization: crate::resolved::ImplementationAuthorization::from_hops(vec![
                crate::resolved::ImplementationRouteHop {
                    from: ModuleId::new(1),
                    to: ModuleId::new(20),
                    import_span: second_route,
                },
                crate::resolved::ImplementationRouteHop {
                    from: ModuleId::new(20),
                    to: ModuleId::new(10),
                    import_span: second_route_suffix,
                },
            ]),
            public_authorization: None,
        };
        let effective = [
            ImplementationHeadRef::Imported(&first),
            ImplementationHeadRef::Imported(&second),
        ];

        // Two head visits plus one pair visit and two aligned application-copy
        // cells, then two overlap root cells and four body-free Int environment
        // visits, four structural overlap cells, and five retained route labels.
        const HEAD_AND_PAIR_WORK: usize = 3 + 2;
        const ENVIRONMENT_WORK: usize = 2 + 4;
        const OVERLAP_WORK: usize = 4;
        const ROUTE_LABEL_WORK: usize = 5;
        const EXACT_CONSTRAINT_WORK: usize =
            HEAD_AND_PAIR_WORK + ENVIRONMENT_WORK + OVERLAP_WORK + ROUTE_LABEL_WORK;
        const EXACT_TYPE_WORK: usize = 0;

        let mut short = InterfaceConstraintBudget::with_limit(EXACT_CONSTRAINT_WORK - 1);
        assert_eq!(
            check_effective_implementation_heads(
                &registry,
                &effective,
                |_, _| Ok(None),
                &mut short,
                &mut TypeWorkBudget::with_limit(EXACT_TYPE_WORK),
            ),
            Err(TypeError::Internal(
                ElaborationFailure::ConstraintResourceExhausted
            ))
        );
        assert_eq!(short.used(), EXACT_CONSTRAINT_WORK - 1);

        let mut exact = InterfaceConstraintBudget::with_limit(EXACT_CONSTRAINT_WORK);
        let error = check_effective_implementation_heads(
            &registry,
            &effective,
            |_, _| Ok(None),
            &mut exact,
            &mut TypeWorkBudget::with_limit(EXACT_TYPE_WORK),
        )
        .expect_err("the later retained route should expose the overlap");
        let TypeError::Interface(diagnostic) = error else {
            panic!("the overlap should use an interface diagnostic");
        };
        assert_eq!(diagnostic.primary.span(), second_route);
        assert_eq!(
            diagnostic.primary.message(),
            "this implementation overlaps an earlier available implementation",
        );
        assert_eq!(
            diagnostic
                .related
                .iter()
                .map(|label| (label.span(), label.message()))
                .collect::<Vec<_>>(),
            vec![
                (
                    first_definition,
                    "the earlier overlapping implementation head is here",
                ),
                (
                    first_route,
                    "the earlier implementation became available through this import",
                ),
                (
                    first_route_suffix,
                    "the earlier implementation became available through this import",
                ),
                (
                    second_definition,
                    "the later implementation is defined here"
                ),
                (
                    second_route_suffix,
                    "the later implementation became available through this import",
                ),
            ]
        );
        assert_eq!(exact.used(), EXACT_CONSTRAINT_WORK);
        assert_eq!(exact.charge(1), Err(()));
    }

    #[test]
    fn determined_pair_coherence_has_an_exact_retryable_route_boundary() {
        let source = SourceFile::new("determination-conflict.ash", "abcdefghijklmnopqrstuvwx")
            .expect("the conflict span fixture should fit");
        let span = |start, end| {
            source
                .span(ByteRange::new(start, end).expect("the span should be ordered"))
                .expect("the span should belong to the fixture")
        };
        let first_definition = span(0, 2);
        let first_route = span(3, 5);
        let first_route_suffix = span(6, 8);
        let second_definition = span(9, 11);
        let second_route = span(12, 14);
        let second_route_suffix = span(15, 17);
        let interface = InterfaceId::new(ModuleId::new(70), 0);
        let first = crate::resolved::ImportedImplementationFact {
            fact: CheckedImplementationFact {
                id: ImplId::new(ModuleId::new(90), 0),
                application: InterfaceApplication::new(interface, Box::new([Type::Int, Type::Int])),
                head_parameters: Box::new([]),
                prerequisites: Box::new([]),
                methods: Box::new([]),
                origin: Origin::Source(first_definition),
                span: first_definition,
            },
            authorization: crate::resolved::ImplementationAuthorization::from_hops(vec![
                crate::resolved::ImplementationRouteHop {
                    from: ModuleId::new(1),
                    to: ModuleId::new(80),
                    import_span: first_route,
                },
                crate::resolved::ImplementationRouteHop {
                    from: ModuleId::new(80),
                    to: ModuleId::new(90),
                    import_span: first_route_suffix,
                },
            ]),
            public_authorization: None,
        };
        let second = crate::resolved::ImportedImplementationFact {
            fact: CheckedImplementationFact {
                id: ImplId::new(ModuleId::new(10), 0),
                application: InterfaceApplication::new(
                    interface,
                    Box::new([Type::Int, Type::Bool]),
                ),
                head_parameters: Box::new([]),
                prerequisites: Box::new([]),
                methods: Box::new([]),
                origin: Origin::Source(second_definition),
                span: second_definition,
            },
            authorization: crate::resolved::ImplementationAuthorization::from_hops(vec![
                crate::resolved::ImplementationRouteHop {
                    from: ModuleId::new(1),
                    to: ModuleId::new(20),
                    import_span: second_route,
                },
                crate::resolved::ImplementationRouteHop {
                    from: ModuleId::new(20),
                    to: ModuleId::new(10),
                    import_span: second_route_suffix,
                },
            ]),
            public_authorization: None,
        };
        let effective = [
            ImplementationHeadRef::Imported(&first),
            ImplementationHeadRef::Imported(&second),
        ];
        let determination = DeterminationKey::new(Box::new([0]));

        // Two head visits, one pair, four full-argument copies, one key-position
        // validation, two selected-argument visits, and one key comparison.
        const PAIR_STAGING_WORK: usize = 2 + 1 + 4 + 1 + 2 + 1;
        // The key comparison owns two roots, four environment visits, and four
        // first-order visits. The independent full comparison owns four roots,
        // eight environment visits, and eight first-order visits.
        const KEY_MATCH_WORK: usize = 2 + 4 + 4;
        const FULL_MATCH_WORK: usize = 4 + 8 + 8;
        const ROUTE_LABEL_WORK: usize = 5;
        const EXACT_WORK: usize =
            PAIR_STAGING_WORK + KEY_MATCH_WORK + FULL_MATCH_WORK + ROUTE_LABEL_WORK;

        let mut short = InterfaceConstraintBudget::with_limit(EXACT_WORK - 1);
        assert_eq!(
            check_effective_implementation_heads(
                &ResolvedRegistry::new(Vec::new(), Vec::new()),
                &effective,
                |_, _| Ok(Some(&determination)),
                &mut short,
                &mut TypeWorkBudget::with_limit(0),
            ),
            Err(TypeError::Internal(
                ElaborationFailure::ConstraintResourceExhausted
            ))
        );
        assert_eq!(short.used(), EXACT_WORK - 1);
        assert_eq!(first.fact.arguments(), &[Type::Int, Type::Int]);
        assert_eq!(second.fact.arguments(), &[Type::Int, Type::Bool]);

        let mut exact = InterfaceConstraintBudget::with_limit(EXACT_WORK);
        let error = check_effective_implementation_heads(
            &ResolvedRegistry::new(Vec::new(), Vec::new()),
            &effective,
            |_, _| Ok(Some(&determination)),
            &mut exact,
            &mut TypeWorkBudget::with_limit(0),
        )
        .expect_err("the exact retry should reach the route-rich key conflict");
        let TypeError::Interface(diagnostic) = error else {
            panic!("the key conflict should use an interface diagnostic");
        };
        assert_eq!(
            diagnostic.reason,
            InterfaceReason::ImplDeterminationConflict
        );
        assert_eq!(diagnostic.primary.span(), second_route);
        assert_eq!(diagnostic.related.len(), ROUTE_LABEL_WORK);
        assert_eq!(exact.used(), EXACT_WORK);
        assert_eq!(exact.charge(1), Err(()));
        assert_eq!(first.fact.arguments(), &[Type::Int, Type::Int]);
        assert_eq!(second.fact.arguments(), &[Type::Int, Type::Bool]);
    }

    #[test]
    fn higher_kinded_overlap_caller_preserves_exact_type_resource_classification() {
        // The caller charges two head visits, one pair visit, one copied
        // head-parameter ID, and two aligned application-copy cells. The
        // overlap seam then owns two application roots, 16 canonical
        // environment discovery cells and 26 unification/authentication
        // cells. One retained diagnostic label completes the exact boundary.
        const HEAD_COLLECTION_AND_PAIR_WORK: usize = 4 + 2;
        const CANONICAL_ENVIRONMENT_WORK: usize = 2 + 16;
        const OVERLAP_UNIFICATION_WORK: usize = 26;
        const DIAGNOSTIC_RETENTION_WORK: usize = 1;
        const EXACT_CONSTRAINT_WORK: usize = HEAD_COLLECTION_AND_PAIR_WORK
            + CANONICAL_ENVIRONMENT_WORK
            + OVERLAP_UNIFICATION_WORK
            + DIAGNOSTIC_RETENTION_WORK;
        // One declared-binder DELTA record plus Option's XI record, retained
        // result Kind, parameter Kind, and derived Arrow Kind.
        const DECLARED_ENVIRONMENT_TYPE_WORK: usize = 1;
        const NOMINAL_ENVIRONMENT_TYPE_WORK: usize = 4;
        const EXACT_TYPE_WORK: usize =
            DECLARED_ENVIRONMENT_TYPE_WORK + NOMINAL_ENVIRONMENT_TYPE_WORK;

        let source = SourceFile::new("higher-kinded-overlap-caller.ash", "overlap")
            .expect("the overlap caller source should fit");
        let span = source
            .span(ByteRange::new(0, 7).expect("the overlap caller range is ordered"))
            .expect("the overlap caller span should fit");
        let module = ModuleId::new(95);
        let interface = InterfaceId::new(module, 0);
        let function = TypeVariableId::resolved(module, 0);
        let nominal_parameter = TypeVariableId::resolved(module, 1);
        let option = NominalTypeId::new(module, 0);
        let first_id = ImplId::new(module, 0);
        let second_id = ImplId::new(module, 1);
        let registry = ResolvedRegistry::new(
            vec![ResolvedNominalType {
                representation_provenance: None,
                declaration_kind: crate::resolved::ResolvedNominalDeclarationKind::Data,
                representation: None,
                id: option,
                spelling: "Option".into(),
                constructors: Box::new([]),
                origin: Origin::Source(span),
            }],
            Vec::new(),
        )
        .with_type_parameters(vec![(
            option,
            vec![ResolvedTypeVariable {
                id: nominal_parameter,
                spelling: "A".into(),
                kind: Kind::Type,
                origin: Origin::Source(span),
            }],
        )])
        .with_additional_type_variables([ResolvedTypeVariable {
            id: function,
            spelling: "F".into(),
            kind: Kind::Arrow(Box::new(Kind::Type), Box::new(Kind::Type)),
            origin: Origin::Source(span),
        }]);
        let first_argument =
            Type::Application(Box::new(Type::Variable(function)), Box::new(Type::Int));
        let second_argument =
            Type::Application(Box::new(Type::Nominal(option)), Box::new(Type::Int));
        let first = crate::resolved::ImportedImplementationFact {
            fact: CheckedImplementationFact {
                id: first_id,
                application: InterfaceApplication::new(interface, Box::new([first_argument])),
                head_parameters: vec![ResolvedTypeVariable {
                    id: function,
                    spelling: "F".into(),
                    kind: Kind::Arrow(Box::new(Kind::Type), Box::new(Kind::Type)),
                    origin: Origin::Source(span),
                }]
                .into_boxed_slice(),
                prerequisites: Box::new([]),
                methods: Box::new([]),
                origin: Origin::Source(span),
                span,
            },
            authorization: crate::resolved::ImplementationAuthorization::from_hops(Vec::new()),
            public_authorization: None,
        };
        let second = crate::resolved::ImportedImplementationFact {
            fact: CheckedImplementationFact {
                id: second_id,
                application: InterfaceApplication::new(interface, Box::new([second_argument])),
                head_parameters: Box::new([]),
                prerequisites: Box::new([]),
                methods: Box::new([]),
                origin: Origin::Source(span),
                span,
            },
            authorization: crate::resolved::ImplementationAuthorization::from_hops(Vec::new()),
            public_authorization: None,
        };
        let effective = [
            ImplementationHeadRef::Imported(&first),
            ImplementationHeadRef::Imported(&second),
        ];

        assert_eq!(
            check_effective_implementation_heads(
                &registry,
                &effective,
                |_, _| Ok(None),
                &mut InterfaceConstraintBudget::with_limit(EXACT_CONSTRAINT_WORK),
                &mut TypeWorkBudget::with_limit(EXACT_TYPE_WORK - 1),
            ),
            Err(TypeError::Internal(
                ElaborationFailure::TypeResourceExhausted
            )),
            "the overlap caller must preserve TypeWork ownership"
        );
        assert_eq!(
            first.fact.arguments(),
            &[Type::Application(
                Box::new(Type::Variable(function)),
                Box::new(Type::Int),
            )]
        );
        assert_eq!(
            second.fact.arguments(),
            &[Type::Application(
                Box::new(Type::Nominal(option)),
                Box::new(Type::Int),
            )]
        );

        assert_eq!(
            check_effective_implementation_heads(
                &registry,
                &effective,
                |_, _| Ok(None),
                &mut InterfaceConstraintBudget::with_limit(EXACT_CONSTRAINT_WORK - 1),
                &mut TypeWorkBudget::with_limit(EXACT_TYPE_WORK),
            ),
            Err(TypeError::Internal(
                ElaborationFailure::ConstraintResourceExhausted
            ))
        );

        let mut exact_constraints = InterfaceConstraintBudget::with_limit(EXACT_CONSTRAINT_WORK);
        let mut exact_types = TypeWorkBudget::with_limit(EXACT_TYPE_WORK);
        let error = check_effective_implementation_heads(
            &registry,
            &effective,
            |_, _| Ok(None),
            &mut exact_constraints,
            &mut exact_types,
        )
        .expect_err("the exact budgets should reach the overlap diagnostic");
        assert!(matches!(
            error,
            TypeError::Interface(diagnostic) if diagnostic.reason == InterfaceReason::ImplOverlap
        ));
        assert_eq!(exact_constraints.used(), EXACT_CONSTRAINT_WORK);
        assert_eq!(exact_types.used(), EXACT_TYPE_WORK);
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
                let mut replacements = TypeReplacementBuffer::new();
                replacements
                    .try_insert_unique(TypeVariableId::generated(0), head)
                    .expect("the fresh replacement key is unique");
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
    fn wide_tuple_and_deep_application_zonk_use_their_exact_pending_shapes() {
        const WIDTH: usize = 4_096;
        let source =
            SourceFile::new("wide-zonk-pending.ash", "()").expect("the fixture should fit");
        let owner = crate::types::NominalTypeId::new(source.id(), 0);
        let tuple = Type::Tuple(vec![Type::Int; WIDTH].into_boxed_slice());
        ZONK_REBUILD_PENDING_PEAK.with(|peak| peak.set(0));
        assert_eq!(zonk_type(&tuple, &HashMap::new()), tuple);
        assert!(ZONK_REBUILD_PENDING_PEAK.with(std::cell::Cell::get) <= 3);

        let application = Type::apply_arguments(Type::Nominal(owner), vec![Type::Int; WIDTH]);
        ZONK_REBUILD_PENDING_PEAK.with(|peak| peak.set(0));
        assert_eq!(zonk_type(&application, &HashMap::new()), application);
        assert_eq!(
            ZONK_REBUILD_PENDING_PEAK.with(std::cell::Cell::get),
            WIDTH * 2 + 1,
            "each pending application retains one finish task and one argument visit",
        );
    }

    #[test]
    fn wide_tuple_and_deep_application_occurs_checks_use_exact_pending_shapes() {
        const WIDTH: usize = 4_096;
        let source =
            SourceFile::new("wide-occurs-pending.ash", "()").expect("the fixture should fit");
        let owner = crate::types::NominalTypeId::new(source.id(), 0);
        let needle = InferenceVariableId::new(0);
        let tuple = Type::Tuple(vec![Type::Int; WIDTH].into_boxed_slice());
        let registry = ResolvedRegistry::new(Vec::new(), Vec::new());
        let generated_type_variables = GeneratedTypeVariableRegistry::default();
        let inference_variables = InferenceVariableRegistry::default();
        let mut budget = TypeWorkBudget::unbounded();
        OCCURS_PENDING_PEAK.with(|peak| peak.set(0));
        assert_eq!(
            type_contains_inference(
                &tuple,
                needle,
                &HashMap::new(),
                &registry,
                &generated_type_variables,
                &inference_variables,
                &mut budget,
            ),
            Ok(false)
        );
        assert!(OCCURS_PENDING_PEAK.with(std::cell::Cell::get) <= 2);

        let application = Type::apply_arguments(Type::Nominal(owner), vec![Type::Int; WIDTH]);
        OCCURS_PENDING_PEAK.with(|peak| peak.set(0));
        assert_eq!(
            type_contains_inference(
                &application,
                needle,
                &HashMap::new(),
                &registry,
                &generated_type_variables,
                &inference_variables,
                &mut budget,
            ),
            Ok(false)
        );
        assert_eq!(
            OCCURS_PENDING_PEAK.with(std::cell::Cell::get),
            WIDTH + 1,
            "each left-spine step retains its argument until the function is visited",
        );
    }

    #[test]
    fn deep_application_and_wide_tuple_occurs_resource_boundaries_are_exact_and_atomic() {
        const DEPTH: usize = 32_768;
        const WIDTH: usize = 32_768;
        // One scheduled root plus two scheduled children for every unary
        // application. The root nominal and each argument are visited from
        // those already charged tasks.
        const APPLICATION_WORK: usize = 1 + 2 * DEPTH;
        // One root task, one tuple-sequence task, then one resumed sequence
        // and one element visit for every element.
        const TUPLE_WORK: usize = 2 + 2 * WIDTH;

        std::thread::Builder::new()
            .name("exact-occurs-deep-wide".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let source = SourceFile::new("exact-occurs-deep-wide.ash", "()")
                    .expect("the fixture source should fit");
                let owner = crate::types::NominalTypeId::new(source.id(), 0);
                let needle = InferenceVariableId::new(0);
                let application = IterativeTypeOwner::new(Type::apply_arguments(
                    Type::Nominal(owner),
                    vec![Type::Int; DEPTH],
                ));
                let tuple = Type::Tuple(vec![Type::Int; WIDTH].into_boxed_slice());
                let solutions = HashMap::new();
                let registry = ResolvedRegistry::default();
                let generated = GeneratedTypeVariableRegistry::default();
                let inference = InferenceVariableRegistry::default();

                let mut application_short = TypeWorkBudget::with_limit(APPLICATION_WORK - 1);
                assert_eq!(
                    type_contains_inference(
                        &application,
                        needle,
                        &solutions,
                        &registry,
                        &generated,
                        &inference,
                        &mut application_short,
                    ),
                    Err(UnificationFailure::Resource),
                );
                assert_eq!(application_short.used(), APPLICATION_WORK - 1);
                assert_eq!(application.outer_nominal(), Some(owner));

                let mut application_exact = TypeWorkBudget::with_limit(APPLICATION_WORK);
                assert_eq!(
                    type_contains_inference(
                        &application,
                        needle,
                        &solutions,
                        &registry,
                        &generated,
                        &inference,
                        &mut application_exact,
                    ),
                    Ok(false),
                );
                assert_eq!(application_exact.used(), APPLICATION_WORK);

                let mut tuple_short = TypeWorkBudget::with_limit(TUPLE_WORK - 1);
                assert_eq!(
                    type_contains_inference(
                        &tuple,
                        needle,
                        &solutions,
                        &registry,
                        &generated,
                        &inference,
                        &mut tuple_short,
                    ),
                    Err(UnificationFailure::Resource),
                );
                assert_eq!(tuple_short.used(), TUPLE_WORK - 1);
                assert!(matches!(&tuple, Type::Tuple(elements) if elements.len() == WIDTH));

                let mut tuple_exact = TypeWorkBudget::with_limit(TUPLE_WORK);
                assert_eq!(
                    type_contains_inference(
                        &tuple,
                        needle,
                        &solutions,
                        &registry,
                        &generated,
                        &inference,
                        &mut tuple_exact,
                    ),
                    Ok(false),
                );
                assert_eq!(tuple_exact.used(), TUPLE_WORK);
                assert!(solutions.is_empty());
                assert!(inference.is_empty());
            })
            .expect("the exact occurs-check thread should start")
            .join()
            .expect("all occurs-check paths and inputs should tear down on 256 KiB");
    }

    #[test]
    fn occurs_check_visits_both_application_children() {
        let source =
            SourceFile::new("occurs-children.ash", "()").expect("the fixture source should fit");
        let span = source
            .span(ByteRange::new(0, 2).expect("the range is ordered"))
            .expect("the fixture span should fit");
        let needle = InferenceVariableId::new(0);
        let function_occurrence =
            Type::Application(Box::new(Type::Inference(needle)), Box::new(Type::Unit));
        let argument_occurrence =
            Type::Application(Box::new(Type::Int), Box::new(Type::Inference(needle)));
        let registry = ResolvedRegistry::new(Vec::new(), Vec::new());
        let generated_type_variables = GeneratedTypeVariableRegistry::default();
        let mut inference_variables = InferenceVariableRegistry::default();
        let mut budget = TypeWorkBudget::unbounded();
        inference_variables
            .insert(needle, &Kind::Type, span, &mut budget)
            .expect("the fixed inference fact should register");

        assert_eq!(
            type_contains_inference(
                &function_occurrence,
                needle,
                &HashMap::new(),
                &registry,
                &generated_type_variables,
                &inference_variables,
                &mut budget,
            ),
            Ok(true)
        );
        assert_eq!(
            type_contains_inference(
                &argument_occurrence,
                needle,
                &HashMap::new(),
                &registry,
                &generated_type_variables,
                &inference_variables,
                &mut budget,
            ),
            Ok(true)
        );
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
    fn inferred_anonymous_function_type_precharges_fixed_inference_records() {
        // Predecessor module/expression work (28), fixed Omega Kind retention
        // added to two fresh variables (4), and fused authenticated
        // transactional alias solving plus zonking (19).
        const EXACT_WORK: usize = 28 + 4 + 19;
        let resolved = resolved_module_fixture(
            "inferred-anonymous-function-budget.ash",
            "",
            "A -> A",
            "fn(value) {\nvalue\n}",
        );

        let mut short = Elaborator::for_module(&resolved).expect("the binder namespace should fit");
        let short_setup_work = short.type_work.used();
        short
            .type_work
            .charge(crate::types::TYPE_WORK_LIMIT - short_setup_work - 2)
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
        assert!(short.inference_variables.is_empty());

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
                (TypeVariableId::new(0), Kind::Type),
                (TypeVariableId::new(1), Kind::Type),
                (TypeVariableId::new(2), Kind::Type),
            ]
            .into_boxed_slice(),
        };

        let mut short = TypeWorkBudget::default();
        short
            .charge(crate::types::TYPE_WORK_LIMIT - 10)
            .expect("the fixture leaves one fewer unit than the complete scheme copy");
        assert_eq!(clone_scheme_with_budget(&fact, &mut short), Err(()));

        let mut exact = TypeWorkBudget::default();
        exact
            .charge(crate::types::TYPE_WORK_LIMIT - 11)
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
    fn method_occurrence_parameter_copies_are_exact_atomic_and_stack_safe() {
        const DEPTH: usize = 32_768;
        const KIND_NODES: usize = 2 * DEPTH + 1;
        // Two TypeFact binder records and K + 1 Kind nodes, followed by one
        // Core Forall wrapper, two Core binder records, and the second K + 1
        // Kind-node copy.
        const EXACT_WORK: usize = 2 + KIND_NODES + 1 + 1 + 2 + KIND_NODES + 1;

        fn deep_kind() -> Kind {
            let mut kind = Kind::Type;
            for _ in 0..DEPTH {
                kind = Kind::Arrow(Box::new(Kind::Type), Box::new(kind));
            }
            kind
        }

        std::thread::Builder::new()
            .name("method-occurrence-kind-copies".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let parameter = TypeVariableId::new(0);
                let method_parameter = TypeVariableId::new(1);
                let method_parameters = [(method_parameter, Kind::Type)];
                let interface_parameters = [(parameter, deep_kind())];

                let mut short = TypeWorkBudget::default();
                short
                    .charge(crate::types::TYPE_WORK_LIMIT - (EXACT_WORK - 1))
                    .expect("one-short method-occurrence precharge");
                assert_eq!(
                    retain_method_occurrence_parameters(
                        &interface_parameters,
                        &method_parameters,
                        &mut short,
                    ),
                    Err(())
                );
                assert_eq!(short.used(), crate::types::TYPE_WORK_LIMIT);

                let source_kind = deep_kind();
                let mut exact = TypeWorkBudget::default();
                exact
                    .charge(crate::types::TYPE_WORK_LIMIT - EXACT_WORK)
                    .expect("exact method-occurrence precharge");
                let (fact, scheme) = retain_method_occurrence_parameters(
                    &[(parameter, source_kind.clone())],
                    &method_parameters,
                    &mut exact,
                )
                .expect("both physical binder/Kind sequences fit exactly");
                assert_eq!(fact.len(), 2);
                assert_eq!(scheme.len(), 2);
                assert_eq!(fact[0].0, parameter);
                assert_eq!(scheme[0].0, parameter);
                assert_eq!(fact[0].1, source_kind);
                assert_eq!(scheme[0].1, source_kind);
                assert_eq!(fact[1], (method_parameter, Kind::Type));
                assert_eq!(scheme[1], (method_parameter, Kind::Type));
                assert_eq!(exact.used(), crate::types::TYPE_WORK_LIMIT);
            })
            .expect("small-stack method-occurrence thread")
            .join()
            .expect("partial and complete Kind-copy teardown must remain iterative");
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
    fn rebuilt_application_span_provenance_has_an_exact_stack_safe_node_budget() {
        const DEPTH: usize = 32_768;
        const PROVENANCE_NODES: usize = 2 * DEPTH + 1;

        std::thread::Builder::new()
            .name("application-provenance-budget".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let source = SourceFile::new("application-provenance.ash", "value")
                    .expect("the provenance fixture should fit");
                let span = source
                    .span(ByteRange::new(0, 5).expect("the range should be ordered"))
                    .expect("the range should fit");
                let ty = deep_application_type(DEPTH);

                let mut short = TypeWorkBudget::with_limit(PROVENANCE_NODES - 1);
                assert_eq!(
                    at_span_provenance_with_budget(&ty, span, &mut short),
                    Err(())
                );
                assert_eq!(short.charge(1), Err(()));

                let mut exact = TypeWorkBudget::with_limit(PROVENANCE_NODES);
                let provenance = at_span_provenance_with_budget(&ty, span, &mut exact)
                    .expect("one provenance node per canonical application child should fit");
                assert!(provenance.aligns(&ty));
                assert_eq!(provenance.span(), Some(span));
                assert_eq!(exact.charge(1), Err(()));

                discard_type_iteratively(ty);
            })
            .expect("the provenance-budget thread should start")
            .join()
            .expect("provenance construction and type teardown must fit the small stack");
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
                (TypeVariableId::new(0), Kind::Type),
                (TypeVariableId::new(1), Kind::Type),
                (TypeVariableId::new(2), Kind::Type),
            ]
            .into_boxed_slice(),
        };

        let mut short = Elaborator::new();
        short
            .type_work
            .charge(crate::types::TYPE_WORK_LIMIT - 15)
            .expect("the fixture leaves exactly the retained metadata cost");
        assert_eq!(
            short.instantiate(&fact, false, span),
            Err(TypeError::Internal(
                ElaborationFailure::TypeResourceExhausted
            ))
        );
        assert_eq!(short.next_inference, 0);
        assert_eq!(short.inference_variables.len(), 0);

        let mut exact = Elaborator::new();
        exact
            .type_work
            .charge(crate::types::TYPE_WORK_LIMIT - 16)
            .expect("the fixture leaves metadata plus the substituted result");
        let (instantiated, arguments) = exact
            .instantiate(&fact, false, span)
            .expect("the exact retained allocation cost should fit");
        assert_eq!(instantiated, Type::Unit);
        assert_eq!(arguments.len(), 3);
        assert_eq!(exact.inference_variables.len(), 3);
        assert_eq!(exact.type_work.charge(1), Err(()));
    }

    #[test]
    fn polymorphic_instantiation_registers_fixed_inference_kinds_transactionally() {
        // Two causal-origin slots, two Omega records, four retained Kind nodes,
        // four replacement/argument Type cells, and seven substituted cells.
        const EXACT_WORK: usize = (2 + 2 + 4 + 4) + 7;
        let source =
            SourceFile::new("kinded-instantiate.ash", "()\n").expect("the fixture should fit");
        let span = source
            .span(ByteRange::new(0, 2).expect("the range is ordered"))
            .expect("the complete fixture should form a span");
        let function = TypeVariableId::new(0);
        let argument = TypeVariableId::new(1);
        let function_kind = Kind::Arrow(Box::new(Kind::Type), Box::new(Kind::Type));
        let application = Type::Application(
            Box::new(Type::Variable(function)),
            Box::new(Type::Variable(argument)),
        );
        let fact = TypeFact {
            ty: Type::Function(Box::new(application.clone()), Box::new(application)),
            provenance: TypeProvenance::atom(Some(span)),
            quantified: vec![(function, function_kind.clone()), (argument, Kind::Type)]
                .into_boxed_slice(),
        };

        let mut short = Elaborator::new();
        short.type_work = TypeWorkBudget::with_limit(EXACT_WORK - 1);
        assert_eq!(
            short.instantiate(&fact, false, span),
            Err(TypeError::Internal(
                ElaborationFailure::TypeResourceExhausted
            ))
        );
        assert_eq!(short.next_inference, 0);
        assert!(short.inference_variables.is_empty());

        let mut exact = Elaborator::new();
        exact.type_work = TypeWorkBudget::with_limit(EXACT_WORK);
        let (_, arguments) = exact
            .instantiate(&fact, false, span)
            .expect("the exact kinded instantiation budget should fit");
        let [
            Type::Inference(function_inference),
            Type::Inference(argument_inference),
        ] = arguments.as_slice()
        else {
            panic!("instantiation should publish two inference arguments");
        };
        assert_eq!(exact.type_work.used(), EXACT_WORK);
        let mut lookup_budget = TypeWorkBudget::unbounded();
        assert_eq!(
            exact
                .inference_variables
                .fact(*function_inference, &mut lookup_budget)
                .map(|fact| &fact.kind),
            Ok(&function_kind),
        );
        assert_eq!(
            exact
                .inference_variables
                .fact(*argument_inference, &mut lookup_budget)
                .map(|fact| &fact.kind),
            Ok(&Kind::Type),
        );
        assert_eq!(
            exact
                .inference_variables
                .fact(*function_inference, &mut lookup_budget)
                .map(|fact| fact.origin),
            Ok(span),
        );
    }

    #[test]
    fn inference_kind_registry_rejects_missing_duplicate_and_conflicting_entries() {
        let source = SourceFile::new("omega-invariants.ash", "()\n").expect("source should fit");
        let span = source
            .span(ByteRange::new(0, 2).expect("ordered range"))
            .expect("span should fit");
        let identity = InferenceVariableId::new(0);
        let missing = InferenceVariableId::new(1);
        let mut registry = InferenceVariableRegistry::default();
        let mut budget = TypeWorkBudget::unbounded();

        assert_eq!(
            registry.fact(missing, &mut budget).map(|fact| &fact.kind),
            Err(InferenceRegistryFailure::Missing)
        );
        registry
            .insert(identity, &Kind::Type, span, &mut budget)
            .expect("the first fixed kind should register");
        assert_eq!(
            registry.insert(identity, &Kind::Type, span, &mut budget),
            Err(InferenceRegistryFailure::Duplicate)
        );
        assert_eq!(
            registry.insert(
                identity,
                &Kind::Arrow(Box::new(Kind::Type), Box::new(Kind::Type)),
                span,
                &mut budget,
            ),
            Err(InferenceRegistryFailure::Conflict)
        );
        assert_eq!(
            registry.fact(identity, &mut budget).map(|fact| &fact.kind),
            Ok(&Kind::Type)
        );
        assert_eq!(
            registry.fact(identity, &mut budget).map(|fact| fact.origin),
            Ok(span)
        );
    }

    #[test]
    fn unification_authenticates_fixed_inference_kinds_before_solving() {
        let source = SourceFile::new("unify-kinds.ash", "()\n").expect("source should fit");
        let span = source
            .span(ByteRange::new(0, 2).expect("ordered range"))
            .expect("span should fit");
        let mut elaborator = Elaborator::new();
        let function_kind = Kind::Arrow(Box::new(Kind::Type), Box::new(Kind::Type));
        let function = elaborator
            .fresh_inference(&function_kind, span)
            .expect("the fixed inference fact should register");

        assert_eq!(
            elaborator.unify(&function, &Type::Int),
            Err(UnificationFailure::Mismatch)
        );
        assert!(elaborator.inference_solutions.is_empty());

        let mut missing_same_identity = Elaborator::new();
        let missing = Type::Inference(InferenceVariableId::new(0));
        assert_eq!(
            missing_same_identity.unify(&missing, &missing),
            Err(UnificationFailure::Invariant)
        );

        assert_eq!(
            elaborator.unify(&Type::Inference(InferenceVariableId::new(1)), &Type::Int),
            Err(UnificationFailure::Invariant)
        );
        assert!(elaborator.inference_solutions.is_empty());
    }

    #[test]
    fn determination_conflict_rolls_back_the_complete_dependent_tuple() {
        // A two-dependent rejected tuple transaction costs `6D + 20 = 32`.
        // Conflict reporting then zonks the two-cell key, the three-cell
        // expected tuple, and the three-cell actual tuple plus one unresolved
        // inference authentication: `32 + 2 + 3 + 4 = 41` type units. Three
        // rendered fields and one retained source label cost four constraint
        // units.
        const CONSTRAINT_WORK: usize = 4;
        const TYPE_WORK: usize = 41;
        let run = |constraint_limit, type_limit| {
            let source = SourceFile::new("determination-transaction.ash", "source goal")
                .expect("the fixture source should fit");
            let source_span = source
                .span(ByteRange::new(0, 6).expect("the source range should be ordered"))
                .expect("the source span should fit");
            let obligation_span = source
                .span(ByteRange::new(7, 11).expect("the goal range should be ordered"))
                .expect("the goal span should fit");
            let mut elaborator = Elaborator::new();
            let inference = elaborator
                .fresh_inference(&Kind::Type, obligation_span)
                .expect("the dependent inference variable should register");
            let Type::Inference(identity) = inference else {
                unreachable!()
            };
            elaborator.constraint_work = InterfaceConstraintBudget::with_limit(constraint_limit);
            elaborator.type_work = TypeWorkBudget::with_limit(type_limit);
            let task = ImprovementTask::for_test(
                Box::new([Type::Unit]),
                Box::new([Type::Int, Type::Bool]),
                Box::new([Type::Inference(identity), Type::Int]),
                obligation_span,
                source_span,
            );
            let result = elaborator.apply_improvement_tasks(std::iter::once(task));
            assert!(
                elaborator.inference_solutions.is_empty(),
                "the first dependent must not publish when a later dependent conflicts"
            );
            assert!(elaborator.authenticated_inference_solutions.is_empty());
            (elaborator, result)
        };

        let (constraint_short, result) = run(CONSTRAINT_WORK - 1, TYPE_WORK);
        assert_eq!(
            result,
            Err(TypeError::Internal(
                ElaborationFailure::ConstraintResourceExhausted
            )),
        );
        assert_eq!(constraint_short.constraint_work.used(), CONSTRAINT_WORK - 1);

        let (type_short, result) = run(CONSTRAINT_WORK, TYPE_WORK - 1);
        assert_eq!(
            result,
            Err(TypeError::Internal(
                ElaborationFailure::TypeResourceExhausted
            )),
        );
        assert_eq!(type_short.type_work.used(), TYPE_WORK - 1);

        for _ in 0..2 {
            let (exact, result) = run(CONSTRAINT_WORK, TYPE_WORK);
            assert!(matches!(
                result,
                Err(TypeError::Interface(diagnostic))
                    if diagnostic.reason == InterfaceReason::DeterminationConflict
            ));
            assert_eq!(exact.constraint_work.used(), CONSTRAINT_WORK);
            assert_eq!(exact.type_work.used(), TYPE_WORK);
        }
    }

    #[test]
    fn unification_cache_collision_preserves_preexisting_transaction_state() {
        let source = SourceFile::new("unification-cache-state.ash", "()")
            .expect("the fixture source should fit");
        let span = source
            .span(ByteRange::new(0, 2).expect("the range should be ordered"))
            .expect("the fixture span should fit");
        let mut elaborator = Elaborator::new();
        let retained_binder = elaborator
            .fresh_type_variable(&Kind::Type, span)
            .expect("the preexisting generated binder should register");
        let inference = elaborator
            .fresh_inference(&Kind::Type, span)
            .expect("the fixed inference should register");
        let Type::Inference(identity) = inference else {
            unreachable!()
        };
        assert!(
            elaborator
                .authenticated_inference_solutions
                .insert(identity)
        );
        let generated_len = elaborator.generated_type_variables.len();
        let next_generated = elaborator.next_generated_type_variable;

        assert_eq!(
            elaborator.unify(&inference, &Type::Int),
            Err(UnificationFailure::Invariant)
        );
        assert!(elaborator.inference_solutions.is_empty());
        assert!(
            elaborator
                .authenticated_inference_solutions
                .contains(&identity)
        );
        assert_eq!(elaborator.generated_type_variables.len(), generated_len);
        assert_eq!(elaborator.next_generated_type_variable, next_generated);
        let mut lookup_budget = TypeWorkBudget::unbounded();
        assert_eq!(
            elaborator
                .generated_type_variables
                .fact(retained_binder, &mut lookup_budget)
                .map(|fact| &fact.kind),
            Ok(&Kind::Type)
        );
    }

    #[test]
    fn generated_local_solution_authenticates_from_its_fixed_binder_environment() {
        let source = SourceFile::new("generated-delta.ash", "()\n").expect("source should fit");
        let span = source
            .span(ByteRange::new(0, 2).expect("ordered range"))
            .expect("span should fit");
        let inference = InferenceVariableId::new(0);
        let binder = TypeVariableId::generated(u32::MAX);
        let mut inference_variables = InferenceVariableRegistry::default();
        let mut generated_type_variables = GeneratedTypeVariableRegistry::default();
        let mut budget = TypeWorkBudget::unbounded();
        inference_variables
            .insert(inference, &Kind::Type, span, &mut budget)
            .expect("the inference kind should register");
        generated_type_variables
            .insert(binder, &Kind::Type, span, &mut budget)
            .expect("the generated binder kind should register");

        assert_eq!(
            authenticate_inference_solution_kind(
                inference,
                &Type::Variable(binder),
                &ResolvedRegistry::default(),
                &generated_type_variables,
                &inference_variables,
                &mut budget,
            ),
            Ok(())
        );
    }

    fn checker_view_with_abstract_nominal(
        access: ImportedTypeAccess,
        parameter_kinds: Vec<Kind>,
        span: Span,
    ) -> (ResolvedRegistry, crate::types::NominalTypeId) {
        let module = ModuleId::new(match access {
            ImportedTypeAccess::Hidden => 801,
            ImportedTypeAccess::Opaque => 802,
            ImportedTypeAccess::Transparent => 803,
        });
        let nominal = crate::types::NominalTypeId::new(module, 0);
        let parameters = parameter_kinds
            .into_iter()
            .enumerate()
            .map(|(index, kind)| ResolvedTypeVariable {
                id: TypeVariableId::resolved(
                    module,
                    u32::try_from(index).expect("the parameter index should fit"),
                ),
                spelling: format!("P{index}"),
                kind,
                origin: Origin::Source(span),
            })
            .collect::<Vec<_>>();
        let mut imported = ImportedFacts::default();
        imported
            .merge_nominal(
                ImportedNominalFact {
                    representation_provenance: None,
                    declaration_kind: crate::resolved::ResolvedNominalDeclarationKind::Data,
                    representation: None,
                    id: nominal,
                    parameter_count: parameters.len(),
                    constructor_count: 1,
                    parameters: parameters.into_boxed_slice(),
                    constructors: Box::new([]),
                    access,
                    display_spelling: Some("Abstract".to_owned()),
                    display_is_private: false,
                    origin: Origin::Source(span),
                },
                &mut TypeWorkBudget::unbounded(),
            )
            .expect("the abstract nominal fixture should be unique");
        let registry = ResolvedRegistry::default()
            .checker_view(&imported, &mut TypeWorkBudget::unbounded())
            .expect("the checker view should retain the abstract nominal Kind fact");
        (registry, nominal)
    }

    #[test]
    fn hidden_and_opaque_nominal_solutions_use_body_free_fixed_kinds() {
        let source = SourceFile::new("abstract-solution.ash", "x")
            .expect("the abstract nominal fixture should fit");
        let span = source
            .span(ByteRange::new(0, 1).expect("the occurrence range should be ordered"))
            .expect("the occurrence range should belong to the fixture");

        for access in [ImportedTypeAccess::Hidden, ImportedTypeAccess::Opaque] {
            let (registry, nominal) = checker_view_with_abstract_nominal(access, Vec::new(), span);
            let identity = InferenceVariableId::new(0);
            let mut inference_variables = InferenceVariableRegistry::default();
            let mut budget = TypeWorkBudget::unbounded();
            inference_variables
                .insert(identity, &Kind::Type, span, &mut budget)
                .expect("the fixed Type inference should register");

            assert_eq!(
                authenticate_inference_solution_kind(
                    identity,
                    &Type::Nominal(nominal),
                    &registry,
                    &GeneratedTypeVariableRegistry::default(),
                    &inference_variables,
                    &mut budget,
                ),
                Ok(()),
                "{access:?} nominal identities retain Kind without structural visibility",
            );
        }
    }

    #[test]
    fn abstract_nominal_candidate_authentication_is_exact_and_atomic() {
        // Omega lookup (1), candidate scan/membership/registry lookup (3),
        // transient Xi record plus its Type Kind (2), synthesis task/result
        // records around S(nominal)=1 (2), and final Kind comparison (1).
        const EXACT_WORK: usize = 1 + 3 + 2 + 2 + 1;
        let source = SourceFile::new("abstract-solution-budget.ash", "x")
            .expect("the abstract nominal resource fixture should fit");
        let span = source
            .span(ByteRange::new(0, 1).expect("the occurrence range should be ordered"))
            .expect("the occurrence range should belong to the fixture");
        let (registry, nominal) =
            checker_view_with_abstract_nominal(ImportedTypeAccess::Hidden, Vec::new(), span);
        let identity = InferenceVariableId::new(0);
        let mut inference_variables = InferenceVariableRegistry::default();
        inference_variables
            .insert(
                identity,
                &Kind::Type,
                span,
                &mut TypeWorkBudget::unbounded(),
            )
            .expect("the fixed Type inference should register");
        let candidate = Type::Nominal(nominal);

        let mut short = TypeWorkBudget::with_limit(EXACT_WORK - 1);
        assert_eq!(
            authenticate_inference_solution_kind(
                identity,
                &candidate,
                &registry,
                &GeneratedTypeVariableRegistry::default(),
                &inference_variables,
                &mut short,
            ),
            Err(UnificationFailure::Resource),
        );
        assert_eq!(short.used(), EXACT_WORK - 1);

        let mut exact = TypeWorkBudget::with_limit(EXACT_WORK);
        assert_eq!(
            authenticate_inference_solution_kind(
                identity,
                &candidate,
                &registry,
                &GeneratedTypeVariableRegistry::default(),
                &inference_variables,
                &mut exact,
            ),
            Ok(()),
        );
        assert_eq!(exact.used(), EXACT_WORK);
        assert_eq!(inference_variables.len(), 1);
    }

    #[test]
    fn higher_kinded_abstract_nominal_accepts_a_partial_nominal_argument() {
        let source = SourceFile::new("abstract-higher-kind.ash", "x")
            .expect("the higher-kinded abstract fixture should fit");
        let span = source
            .span(ByteRange::new(0, 1).expect("the occurrence range should be ordered"))
            .expect("the occurrence range should belong to the fixture");
        let option_module = ModuleId::new(800);
        let option = crate::types::NominalTypeId::new(option_module, 0);
        let option_parameter = ResolvedTypeVariable {
            id: TypeVariableId::resolved(option_module, 0),
            spelling: "A".to_owned(),
            kind: Kind::Type,
            origin: Origin::Source(span),
        };
        let base = ResolvedRegistry::new(
            vec![ResolvedNominalType {
                representation_provenance: None,
                declaration_kind: crate::resolved::ResolvedNominalDeclarationKind::Data,
                representation: None,
                id: option,
                spelling: "Option".to_owned(),
                constructors: Box::new([]),
                origin: Origin::Source(span),
            }],
            Vec::new(),
        )
        .with_type_parameters(vec![(option, vec![option_parameter])]);
        let function_kind = Kind::Arrow(Box::new(Kind::Type), Box::new(Kind::Type));
        let abstract_module = ModuleId::new(804);
        let abstract_nominal = crate::types::NominalTypeId::new(abstract_module, 0);
        let mut imported = ImportedFacts::default();
        imported
            .merge_nominal(
                ImportedNominalFact {
                    representation_provenance: None,
                    declaration_kind: crate::resolved::ResolvedNominalDeclarationKind::Data,
                    representation: None,
                    id: abstract_nominal,
                    parameter_count: 1,
                    constructor_count: 1,
                    parameters: Box::new([ResolvedTypeVariable {
                        id: TypeVariableId::resolved(abstract_module, 0),
                        spelling: "F".to_owned(),
                        kind: function_kind.clone(),
                        origin: Origin::Source(span),
                    }]),
                    constructors: Box::new([]),
                    access: ImportedTypeAccess::Hidden,
                    display_spelling: Some("Higher".to_owned()),
                    display_is_private: false,
                    origin: Origin::Source(span),
                },
                &mut TypeWorkBudget::unbounded(),
            )
            .expect("the higher-kinded abstract fact should be unique");
        let registry = base
            .checker_view(&imported, &mut TypeWorkBudget::unbounded())
            .expect("the checker view should retain local and abstract Kind facts");
        let identity = InferenceVariableId::new(0);
        let mut inference_variables = InferenceVariableRegistry::default();
        let mut budget = TypeWorkBudget::unbounded();
        inference_variables
            .insert(identity, &Kind::Type, span, &mut budget)
            .expect("the result inference should register");
        let candidate = Type::Application(
            Box::new(Type::Nominal(abstract_nominal)),
            Box::new(Type::Nominal(option)),
        );

        assert_eq!(
            authenticate_inference_solution_kind(
                identity,
                &candidate,
                &registry,
                &GeneratedTypeVariableRegistry::default(),
                &inference_variables,
                &mut budget,
            ),
            Ok(()),
        );

        let wrong_domain = InferenceVariableId::new(1);
        inference_variables
            .insert(
                wrong_domain,
                &Kind::Arrow(Box::new(Kind::Type), Box::new(Kind::Type)),
                span,
                &mut budget,
            )
            .expect("the incompatible function-kind inference should register");
        assert_eq!(
            authenticate_inference_solution_kind(
                wrong_domain,
                &Type::Nominal(abstract_nominal),
                &registry,
                &GeneratedTypeVariableRegistry::default(),
                &inference_variables,
                &mut budget,
            ),
            Err(UnificationFailure::Mismatch),
            "a well-kinded constructor with the wrong function domain is a mismatch",
        );
    }

    #[test]
    fn generated_binder_registration_is_exact_atomic_and_canonical() {
        // One source-order index lookup, one retained binder record, and the
        // three nodes of `Type -> Type` make the exact insertion boundary five.
        const EXACT_WORK: usize = 1 + 1 + 3;
        let source =
            SourceFile::new("generated-delta-budget.ash", "()\n").expect("source should fit");
        let span = source
            .span(ByteRange::new(0, 2).expect("ordered range"))
            .expect("span should fit");
        let identity = TypeVariableId::generated(u32::MAX);
        let function_kind = Kind::Arrow(Box::new(Kind::Type), Box::new(Kind::Type));

        let mut short = GeneratedTypeVariableRegistry::default();
        let mut short_budget = TypeWorkBudget::with_limit(EXACT_WORK - 1);
        assert_eq!(
            short.insert(identity, &function_kind, span, &mut short_budget),
            Err(GeneratedTypeVariableRegistryFailure::Resource)
        );
        assert_eq!(short.len(), 0, "one-short insertion must not publish");

        let mut exact = GeneratedTypeVariableRegistry::default();
        let mut exact_budget = TypeWorkBudget::with_limit(EXACT_WORK);
        exact
            .insert(identity, &function_kind, span, &mut exact_budget)
            .expect("the exact fixed-kind record should fit");
        assert_eq!(exact_budget.used(), EXACT_WORK);
        let mut lookup_budget = TypeWorkBudget::unbounded();
        assert_eq!(
            exact
                .fact(identity, &mut lookup_budget)
                .map(|fact| &fact.kind),
            Ok(&function_kind)
        );
        assert_eq!(
            exact.insert(identity, &Kind::Type, span, &mut lookup_budget),
            Err(GeneratedTypeVariableRegistryFailure::Conflict)
        );
        assert_eq!(
            exact.insert(identity, &function_kind, span, &mut lookup_budget),
            Err(GeneratedTypeVariableRegistryFailure::Duplicate)
        );
        assert!(matches!(
            exact.fact(TypeVariableId::generated(u32::MAX - 1), &mut lookup_budget),
            Err(GeneratedTypeVariableRegistryFailure::Missing)
        ));
    }

    #[test]
    fn generated_binder_allocation_rolls_back_the_identity_on_one_short() {
        // Type needs one lookup, one binder record, and one retained Kind node.
        const EXACT_WORK: usize = 1 + 1 + 1;
        let source =
            SourceFile::new("generated-delta-allocation.ash", "()\n").expect("source should fit");
        let span = source
            .span(ByteRange::new(0, 2).expect("ordered range"))
            .expect("span should fit");

        let mut short = Elaborator::new();
        short.type_work = TypeWorkBudget::with_limit(EXACT_WORK - 1);
        assert_eq!(
            short.fresh_type_variable(&Kind::Type, span),
            Err(TypeError::Internal(
                ElaborationFailure::TypeResourceExhausted
            ))
        );
        assert_eq!(short.generated_type_variables.len(), 0);
        assert_eq!(short.next_generated_type_variable, u32::MAX);

        let mut exact = Elaborator::new();
        exact.type_work = TypeWorkBudget::with_limit(EXACT_WORK);
        assert_eq!(
            exact.fresh_type_variable(&Kind::Type, span),
            Ok(TypeVariableId::generated(u32::MAX))
        );
        assert_eq!(exact.generated_type_variables.len(), 1);
        assert_eq!(exact.next_generated_type_variable, u32::MAX - 1);
        assert_eq!(exact.type_work.used(), EXACT_WORK);
    }

    #[test]
    fn higher_kinded_generalization_batch_is_exact_and_atomic() {
        // Two source-order batch records in each of three destinations (6),
        // then for each binder an Omega lookup, a Kind copy, and generated
        // Delta lookup/record/Kind retention: 3 + 2|K|, hence 9 + 5.
        // Fused zonking visits the Function and two Application cells (3),
        // then each of four inference occurrences performs an Omega lookup,
        // authenticated-solution lookup, and one-cell solution copy (12).
        const EXACT_WORK: usize = 6 + 9 + 5 + 3 + 12;
        let source = SourceFile::new("generalization-batch-budget.ash", "()")
            .expect("the fixture source should fit");
        let span = source
            .span(ByteRange::new(0, 2).expect("the range should be ordered"))
            .expect("the fixture span should fit");
        let function_kind = Kind::Arrow(Box::new(Kind::Type), Box::new(Kind::Type));
        let make_initializer = |function, argument| {
            let application = Type::Application(Box::new(function), Box::new(argument));
            Type::Function(Box::new(application.clone()), Box::new(application))
        };

        let mut short = Elaborator::new();
        let function = short
            .fresh_inference(&function_kind, span)
            .expect("the function-kinded inference should register");
        let argument = short
            .fresh_inference(&Kind::Type, span)
            .expect("the Type-kinded inference should register");
        let Type::Inference(function_id) = function else {
            unreachable!()
        };
        let Type::Inference(argument_id) = argument else {
            unreachable!()
        };
        let initializer = make_initializer(function, argument);
        short.type_work = TypeWorkBudget::with_limit(EXACT_WORK - 1);
        assert_eq!(
            short.generalize_inference_variables(&[function_id, argument_id], &initializer),
            Err(TypeError::Internal(
                ElaborationFailure::TypeResourceExhausted
            ))
        );
        assert!(short.inference_solutions.is_empty());
        assert!(short.authenticated_inference_solutions.is_empty());
        assert_eq!(short.generated_type_variables.len(), 0);
        assert_eq!(short.next_generated_type_variable, u32::MAX);

        let mut exact = Elaborator::new();
        let function = exact
            .fresh_inference(&function_kind, span)
            .expect("the function-kinded inference should register");
        let argument = exact
            .fresh_inference(&Kind::Type, span)
            .expect("the Type-kinded inference should register");
        let Type::Inference(function_id) = function else {
            unreachable!()
        };
        let Type::Inference(argument_id) = argument else {
            unreachable!()
        };
        exact.type_work = TypeWorkBudget::with_limit(EXACT_WORK);
        let (generalized, zonked) = exact
            .generalize_inference_variables(
                &[function_id, argument_id],
                &make_initializer(function, argument),
            )
            .expect("the complete higher-kinded batch should fit exactly");
        assert_eq!(exact.type_work.used(), EXACT_WORK);
        assert_eq!(generalized.len(), 2);
        assert_eq!(generalized[0].1, function_kind);
        assert_eq!(generalized[1].1, Kind::Type);
        assert!(matches!(zonked, Type::Function(_, _)));
    }

    #[test]
    fn generalization_duplicate_solution_preserves_preexisting_transaction_state() {
        let source = SourceFile::new("generalization-duplicate-state.ash", "()")
            .expect("the fixture source should fit");
        let span = source
            .span(ByteRange::new(0, 2).expect("the range should be ordered"))
            .expect("the fixture span should fit");
        let mut elaborator = Elaborator::new();
        let retained_binder = elaborator
            .fresh_type_variable(&Kind::Type, span)
            .expect("the preexisting generated binder should register");
        let inference = elaborator
            .fresh_inference(&Kind::Type, span)
            .expect("the fixed inference should register");
        let Type::Inference(identity) = inference else {
            unreachable!()
        };
        elaborator
            .inference_solutions
            .insert_unique(identity, Type::Bool)
            .expect("the preexisting solution should be unique");
        assert!(
            elaborator
                .authenticated_inference_solutions
                .insert(identity)
        );
        let generated_len = elaborator.generated_type_variables.len();
        let next_generated = elaborator.next_generated_type_variable;

        assert_eq!(
            elaborator.generalize_inference_variables(&[identity], &Type::Unit),
            Err(TypeError::Internal(ElaborationFailure::InvalidState))
        );
        assert_eq!(
            elaborator.inference_solutions.get(&identity),
            Some(&Type::Bool)
        );
        assert!(
            elaborator
                .authenticated_inference_solutions
                .contains(&identity)
        );
        assert_eq!(elaborator.generated_type_variables.len(), generated_len);
        assert_eq!(elaborator.next_generated_type_variable, next_generated);
        let mut lookup_budget = TypeWorkBudget::unbounded();
        assert_eq!(
            elaborator
                .generated_type_variables
                .fact(retained_binder, &mut lookup_budget)
                .map(|fact| &fact.kind),
            Ok(&Kind::Type)
        );
    }

    #[test]
    fn generalization_cache_collision_rolls_back_only_its_published_prefix() {
        let source = SourceFile::new("generalization-cache-state.ash", "()")
            .expect("the fixture source should fit");
        let span = source
            .span(ByteRange::new(0, 2).expect("the range should be ordered"))
            .expect("the fixture span should fit");
        let mut elaborator = Elaborator::new();
        let retained_binder = elaborator
            .fresh_type_variable(&Kind::Type, span)
            .expect("the preexisting generated binder should register");
        let first = elaborator
            .fresh_inference(&Kind::Type, span)
            .expect("the first inference should register");
        let collision = elaborator
            .fresh_inference(&Kind::Type, span)
            .expect("the collision inference should register");
        let Type::Inference(first) = first else {
            unreachable!()
        };
        let Type::Inference(collision) = collision else {
            unreachable!()
        };
        assert!(
            elaborator
                .authenticated_inference_solutions
                .insert(collision)
        );
        let generated_len = elaborator.generated_type_variables.len();
        let next_generated = elaborator.next_generated_type_variable;

        assert_eq!(
            elaborator.generalize_inference_variables(&[first, collision], &Type::Unit),
            Err(TypeError::Internal(ElaborationFailure::InvalidState))
        );
        assert!(elaborator.inference_solutions.is_empty());
        assert!(
            !elaborator
                .authenticated_inference_solutions
                .contains(&first)
        );
        assert!(
            elaborator
                .authenticated_inference_solutions
                .contains(&collision)
        );
        assert_eq!(elaborator.generated_type_variables.len(), generated_len);
        assert_eq!(elaborator.next_generated_type_variable, next_generated);
        let mut lookup_budget = TypeWorkBudget::unbounded();
        assert_eq!(
            elaborator
                .generated_type_variables
                .fact(retained_binder, &mut lookup_budget)
                .map(|fact| &fact.kind),
            Ok(&Kind::Type)
        );
    }

    #[test]
    fn higher_kinded_unification_rolls_back_a_solution_before_a_late_mismatch() {
        let resolved = resolved_module_fixture(
            "higher-kinded-unification.ash",
            "type Option<A> =\nNone\n| Some(A)\n",
            "Unit",
            "()",
        );
        let span = fixture_result(&resolved).span;
        let option = resolved.registry().nominals()[0].id;
        let function_kind = Kind::Arrow(Box::new(Kind::Type), Box::new(Kind::Type));

        let mut rejected =
            Elaborator::for_module(&resolved).expect("the fixture namespace should fit");
        let function = rejected
            .fresh_inference(&function_kind, span)
            .expect("the higher-kinded inference should register");
        let left = Type::Application(Box::new(function), Box::new(Type::Int));
        let wrong = Type::Application(Box::new(Type::Nominal(option)), Box::new(Type::Bool));
        assert_eq!(
            rejected.unify(&left, &wrong),
            Err(UnificationFailure::Mismatch)
        );
        assert!(
            rejected.inference_solutions.is_empty(),
            "a later argument mismatch must roll back the earlier constructor solution"
        );

        let mut accepted =
            Elaborator::for_module(&resolved).expect("the fixture namespace should fit");
        let function = accepted
            .fresh_inference(&function_kind, span)
            .expect("the higher-kinded inference should register");
        let left = Type::Application(Box::new(function), Box::new(Type::Int));
        let right = Type::Application(Box::new(Type::Nominal(option)), Box::new(Type::Int));
        accepted
            .unify(&left, &right)
            .expect("a partial nominal constructor has the fixed function kind");
        assert_eq!(
            accepted
                .inference_solutions
                .get(&InferenceVariableId::new(0)),
            Some(&Type::Nominal(option))
        );

        let mut late_invariant =
            Elaborator::for_module(&resolved).expect("the fixture namespace should fit");
        let function = late_invariant
            .fresh_inference(&function_kind, span)
            .expect("the higher-kinded inference should register");
        let missing = Type::Inference(InferenceVariableId::new(1));
        let left = Type::Application(Box::new(function), Box::new(missing));
        let right = Type::Application(Box::new(Type::Nominal(option)), Box::new(Type::Int));
        assert_eq!(
            late_invariant.unify(&left, &right),
            Err(UnificationFailure::Invariant)
        );
        assert!(late_invariant.inference_solutions.is_empty());
    }

    #[test]
    fn first_order_unification_does_not_synthesize_a_type_lambda() {
        let source =
            SourceFile::new("no-type-lambda.ash", "()").expect("the fixture source should fit");
        let span = source
            .span(ByteRange::new(0, 2).expect("the range should be ordered"))
            .expect("the fixture span should fit");
        let mut elaborator = Elaborator::new();
        let function = elaborator
            .fresh_inference(
                &Kind::Arrow(Box::new(Kind::Type), Box::new(Kind::Type)),
                span,
            )
            .expect("the fixed higher-kinded inference should register");
        let applied = Type::Application(Box::new(function), Box::new(Type::Int));

        assert_eq!(
            elaborator.unify(&applied, &Type::Bool),
            Err(UnificationFailure::Mismatch),
        );
        assert!(
            elaborator.inference_solutions.is_empty(),
            "first-order unification must not solve F by inventing a type lambda"
        );
        assert!(elaborator.authenticated_inference_solutions.is_empty());
        assert_eq!(elaborator.next_inference, 1);
    }

    #[test]
    fn zonking_authenticates_missing_and_conflicting_fixed_inference_kinds() {
        let source = SourceFile::new("zonk-kinds.ash", "()\n").expect("source should fit");
        let span = source
            .span(ByteRange::new(0, 2).expect("ordered range"))
            .expect("span should fit");

        let mut missing = Elaborator::new();
        assert_eq!(
            missing.zonk(&Type::Inference(InferenceVariableId::new(0))),
            Err(TypeError::Internal(ElaborationFailure::InvalidState))
        );

        let mut conflicting = Elaborator::new();
        let function_kind = Kind::Arrow(Box::new(Kind::Type), Box::new(Kind::Type));
        conflicting
            .fresh_inference(&function_kind, span)
            .expect("the function-kinded inference should register");
        conflicting
            .inference_solutions
            .0
            .insert(InferenceVariableId::new(0), Type::Int);
        assert_eq!(
            conflicting.zonk(&Type::Inference(InferenceVariableId::new(0))),
            Err(TypeError::Internal(ElaborationFailure::InvalidState))
        );
    }

    #[test]
    fn fused_zonk_charges_repeated_inference_occurrences_once_and_atomically() {
        // One Tuple cell plus, for each inference occurrence, one Omega lookup,
        // one authenticated-solution lookup, and one retained solution Type.
        const EXACT_WORK: usize = 1 + 2 * (1 + 1 + 1);
        let source = SourceFile::new("repeated-zonk-auth.ash", "()\n").expect("source should fit");
        let span = source
            .span(ByteRange::new(0, 2).expect("ordered range"))
            .expect("span should fit");
        let identity = InferenceVariableId::new(0);
        let ty = Type::Tuple(
            vec![Type::Inference(identity), Type::Inference(identity)].into_boxed_slice(),
        );
        let mut inference_variables = InferenceVariableRegistry::default();
        let solutions = HashMap::from([(identity, Type::Int)]);
        let authenticated_solutions = HashSet::from([identity]);
        let mut setup_budget = TypeWorkBudget::unbounded();
        inference_variables
            .insert(identity, &Kind::Type, span, &mut setup_budget)
            .expect("the fixed inference kind should register");
        SOLUTION_KIND_AUTHENTICATIONS.with(|count| count.set(0));

        let mut one_short = TypeWorkBudget::with_limit(EXACT_WORK - 1);
        assert_eq!(
            zonk_type_with_status_and_inference(&ty, &solutions, |work| match work {
                ZonkWork::TypeCells(cells) => one_short.charge(cells),
                ZonkWork::Inference(identity) => {
                    authenticate_zonk_inference_occurrence(
                        identity,
                        &inference_variables,
                        &solutions,
                        &authenticated_solutions,
                        &mut one_short,
                    )
                    .map_err(|_| ())
                }
            },),
            Err(())
        );
        assert_eq!(solutions.get(&identity), Some(&Type::Int));
        assert!(authenticated_solutions.contains(&identity));

        let mut exact = TypeWorkBudget::with_limit(EXACT_WORK);
        let (zonked, unresolved) =
            zonk_type_with_status_and_inference(&ty, &solutions, |work| match work {
                ZonkWork::TypeCells(cells) => exact.charge(cells),
                ZonkWork::Inference(identity) => authenticate_zonk_inference_occurrence(
                    identity,
                    &inference_variables,
                    &solutions,
                    &authenticated_solutions,
                    &mut exact,
                )
                .map_err(|_| ()),
            })
            .expect("the exact fused zonk work should fit");

        assert_eq!(
            zonked,
            Type::Tuple(vec![Type::Int, Type::Int].into_boxed_slice())
        );
        assert!(!unresolved);
        assert_eq!(exact.used(), EXACT_WORK);
        assert_eq!(SOLUTION_KIND_AUTHENTICATIONS.with(std::cell::Cell::get), 0);
    }

    #[test]
    fn repeated_elaborator_zonks_reuse_authenticated_solution_kinds() {
        let source =
            SourceFile::new("repeated-elaborator-zonk.ash", "()\n").expect("source should fit");
        let span = source
            .span(ByteRange::new(0, 2).expect("ordered range"))
            .expect("span should fit");
        let mut elaborator = Elaborator::new();
        let inference = elaborator
            .fresh_inference(&Kind::Type, span)
            .expect("the fixed inference kind should register");
        elaborator
            .unify(&inference, &Type::Int)
            .expect("solution publication should authenticate its fixed kind");
        elaborator.type_work = TypeWorkBudget::unbounded();
        SOLUTION_KIND_AUTHENTICATIONS.with(|count| count.set(0));

        assert_eq!(elaborator.zonk(&inference), Ok(Type::Int));
        assert_eq!(elaborator.zonk(&inference), Ok(Type::Int));
        assert_eq!(SOLUTION_KIND_AUTHENTICATIONS.with(std::cell::Cell::get), 0);
    }

    #[test]
    fn reachable_solution_cost_is_independent_of_unrelated_omega_width() {
        const WIDTH: usize = 4_096;
        let source = SourceFile::new("omega-width.ash", "()\n").expect("source should fit");
        let span = source
            .span(ByteRange::new(0, 2).expect("ordered range"))
            .expect("span should fit");

        let mut baseline = Elaborator::new();
        let baseline_target = baseline
            .fresh_inference(&Kind::Type, span)
            .expect("the baseline inference should register");
        baseline.type_work = TypeWorkBudget::unbounded();
        baseline
            .unify(&baseline_target, &Type::Int)
            .expect("the baseline Type solution should fit");
        let baseline_work = baseline.type_work.used();

        let mut wide = Elaborator::new();
        let wide_target = wide
            .fresh_inference(&Kind::Type, span)
            .expect("the target inference should register first");
        for _ in 1..WIDTH {
            wide.fresh_inference(&Kind::Type, span)
                .expect("the unrelated inference fact should register");
        }
        wide.type_work = TypeWorkBudget::unbounded();
        wide.unify(&wide_target, &Type::Int)
            .expect("unrelated Omega facts must not enter the solve environment");

        assert_eq!(wide.type_work.used(), baseline_work);
    }

    #[test]
    fn constructor_pattern_kind_batch_rolls_back_after_a_late_registration_failure() {
        // Initial target zonk (3), constructor batch storage (3), complete
        // function-kinded parameter registration (5), and two of the three
        // Type-kinded registration units: the final Kind node is one short.
        const ONE_SHORT: usize = 3 + 3 + 5 + 2;
        let resolved = resolved_module_fixture(
            "constructor-pattern-omega.ash",
            concat!(
                "type Option<A> =\nNone\n| Some(A)\n",
                "type Higher<F : Type -> Type, A> = Higher\n\n",
                "probe : Higher<Option, Int> -> Unit\n",
                "probe Higher = ()\n",
            ),
            "Unit",
            "()",
        );
        let ResolvedDefinitionKind::Equational(probe) = &resolved.definitions()[0].kind else {
            panic!("the probe should be equational");
        };
        let pattern = &probe.equations[0].patterns[0];
        let span = pattern.span;
        let mut elaborator =
            Elaborator::for_module(&resolved).expect("the fixture namespace should fit");
        let target = elaborator
            .fresh_inference(&Kind::Type, span)
            .expect("the expected-pattern inference should register");
        elaborator.type_work = TypeWorkBudget::with_limit(ONE_SHORT);

        assert!(matches!(
            elaborator.check_core_pattern(
                pattern,
                &target,
                &mut TypeContext::new(),
                &mut Vec::new(),
                GeneratedReason::BindingLowering,
            ),
            Err(TypeError::Internal(
                ElaborationFailure::TypeResourceExhausted
            ))
        ));
        assert_eq!(elaborator.next_inference, 1);
        assert_eq!(elaborator.inference_variables.len(), 1);
        assert!(elaborator.inference_solutions.is_empty());

        let mut accepted =
            Elaborator::for_module(&resolved).expect("the fixture namespace should fit");
        let target = accepted
            .fresh_inference(&Kind::Type, span)
            .expect("the expected-pattern inference should register");
        accepted.type_work = TypeWorkBudget::unbounded();
        let checked = accepted
            .check_core_pattern(
                pattern,
                &target,
                &mut TypeContext::new(),
                &mut Vec::new(),
                GeneratedReason::BindingLowering,
            )
            .expect("the complete constructor pattern should refine");
        checked.pattern.discard_iteratively();
        let mut lookup_budget = TypeWorkBudget::unbounded();
        assert!(matches!(
            &accepted
                .inference_variables
                .fact(InferenceVariableId::new(1), &mut lookup_budget)
                .expect("the first nominal argument should remain registered")
                .kind,
            Kind::Arrow(_, _)
        ));
        assert_eq!(
            &accepted
                .inference_variables
                .fact(InferenceVariableId::new(2), &mut lookup_budget)
                .expect("the second nominal argument should remain registered")
                .kind,
            &Kind::Type
        );
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
            .map(|index| {
                (
                    TypeVariableId::new(u32::try_from(index).expect("parameter identity")),
                    Kind::Type,
                )
            })
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
            .charge(crate::types::TYPE_WORK_LIMIT - (WIDTH * 5 - 1))
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
        assert_eq!(elaborator.inference_variables.len(), 0);
    }

    #[test]
    fn unification_charges_operand_copies_and_solution_metadata_exactly() {
        // One-cell candidate: comparison/copies, one fused zonk pass,
        // fixed-kind synthesis/comparison, occurs scheduling, plus the
        // solution, rollback, and authenticated-solution cache records.
        const EXACT_WORK: usize = 17;
        let source =
            SourceFile::new("scalar-unification.ash", "()").expect("the fixture source should fit");
        let span = source
            .span(ByteRange::new(0, 2).expect("the range is ordered"))
            .expect("the fixture span should fit");

        let mut short = Elaborator::new();
        let inference = short
            .fresh_inference(&Kind::Type, span)
            .expect("the fixed inference should register");
        short.type_work = TypeWorkBudget::with_limit(EXACT_WORK - 1);
        assert_eq!(
            short.unify(&inference, &Type::Int),
            Err(UnificationFailure::Resource)
        );
        assert!(short.inference_solutions.is_empty());

        let mut exact = Elaborator::new();
        let inference = exact
            .fresh_inference(&Kind::Type, span)
            .expect("the fixed inference should register");
        exact.type_work = TypeWorkBudget::with_limit(EXACT_WORK);
        assert_eq!(exact.unify(&inference, &Type::Int), Ok(()));
        assert_eq!(
            exact.inference_solutions,
            HashMap::from([(InferenceVariableId::new(0), Type::Int)])
        );
        assert_eq!(exact.type_work.used(), EXACT_WORK);
    }

    #[test]
    fn wide_unification_resource_boundary_is_exact_and_rolls_back_a_late_mismatch() {
        const WIDTH: usize = 32_768;
        // Concrete-prefix comparison, both operand copies and zonks, the
        // candidate environment and Kind synthesis, the solution copy,
        // occurs tasks, and three transaction records total `8W + 19`.
        const ACCEPTED_WORK: usize = 8 * WIDTH + 19;
        // Two wide tuples with the first left element solved and the last
        // element mismatched reach that stable failure at `6W + 20`.
        const REJECTED_WORK: usize = 6 * WIDTH + 20;
        const { assert!(ACCEPTED_WORK <= crate::types::TYPE_WORK_LIMIT) };

        let source = SourceFile::new("wide-unification-budget.ash", "()")
            .expect("the fixture source should fit");
        let span = source
            .span(ByteRange::new(0, 2).expect("the range should be ordered"))
            .expect("the fixture span should fit");

        std::thread::Builder::new()
            .name("wide-unification-budget".to_owned())
            .stack_size(256 * 1024)
            .spawn(move || {
                let candidate = Type::Tuple(vec![Type::Int; WIDTH].into_boxed_slice());

                let mut accepted_short = Elaborator::new();
                let inference = accepted_short
                    .fresh_inference(&Kind::Type, span)
                    .expect("the inference should register");
                accepted_short.type_work = TypeWorkBudget::with_limit(ACCEPTED_WORK - 1);
                assert_eq!(
                    accepted_short.unify(&inference, &candidate),
                    Err(UnificationFailure::Resource),
                );
                assert_eq!(
                    accepted_short.type_work.used(),
                    ACCEPTED_WORK - 3,
                    "the final three-record transaction charge is atomic",
                );
                assert!(accepted_short.inference_solutions.is_empty());
                assert!(accepted_short.authenticated_inference_solutions.is_empty());

                let mut accepted_exact = Elaborator::new();
                let inference = accepted_exact
                    .fresh_inference(&Kind::Type, span)
                    .expect("the inference should register");
                accepted_exact.type_work = TypeWorkBudget::with_limit(ACCEPTED_WORK);
                assert_eq!(accepted_exact.unify(&inference, &candidate), Ok(()));
                assert_eq!(accepted_exact.type_work.used(), ACCEPTED_WORK);
                let solution = accepted_exact
                    .inference_solutions
                    .get(&InferenceVariableId::new(0))
                    .expect("the accepted inference should retain its solution");
                assert_eq!(solution, &candidate);
                assert!(matches!(
                    solution,
                    Type::Tuple(elements)
                        if elements.len() == WIDTH
                            && elements.iter().all(|element| matches!(element, Type::Int))
                ));
                assert!(matches!(
                    &candidate,
                    Type::Tuple(elements)
                        if elements.len() == WIDTH
                            && elements.iter().all(|element| matches!(element, Type::Int))
                ));
                drop(accepted_exact);

                let late_left = |inference| {
                    let mut elements = vec![Type::Int; WIDTH];
                    elements[0] = inference;
                    Type::Tuple(elements.into_boxed_slice())
                };
                let mut right_elements = vec![Type::Int; WIDTH];
                right_elements[WIDTH - 1] = Type::Bool;
                let right = Type::Tuple(right_elements.into_boxed_slice());
                assert!(matches!(
                    &right,
                    Type::Tuple(elements)
                        if matches!(elements.first(), Some(Type::Int))
                            && matches!(elements.last(), Some(Type::Bool))
                ));

                let mut rejected_short = Elaborator::new();
                let inference = rejected_short
                    .fresh_inference(&Kind::Type, span)
                    .expect("the inference should register");
                let left = late_left(inference);
                assert!(matches!(
                    &left,
                    Type::Tuple(elements)
                        if matches!(elements.first(), Some(Type::Inference(id)) if id.value() == 0)
                            && matches!(elements.last(), Some(Type::Int))
                ));
                rejected_short.type_work = TypeWorkBudget::with_limit(REJECTED_WORK - 1);
                assert_eq!(
                    rejected_short.unify(&left, &right),
                    Err(UnificationFailure::Resource),
                );
                assert_eq!(rejected_short.type_work.used(), REJECTED_WORK - 1);
                assert!(rejected_short.inference_solutions.is_empty());
                assert!(rejected_short.authenticated_inference_solutions.is_empty());

                let mut rejected_exact = Elaborator::new();
                let inference = rejected_exact
                    .fresh_inference(&Kind::Type, span)
                    .expect("the inference should register");
                let left = late_left(inference);
                assert!(matches!(
                    &left,
                    Type::Tuple(elements)
                        if matches!(elements.first(), Some(Type::Inference(id)) if id.value() == 0)
                            && matches!(elements.last(), Some(Type::Int))
                ));
                rejected_exact.type_work = TypeWorkBudget::with_limit(REJECTED_WORK);
                assert_eq!(
                    rejected_exact.unify(&left, &right),
                    Err(UnificationFailure::Mismatch),
                );
                assert_eq!(rejected_exact.type_work.used(), REJECTED_WORK);
                assert!(rejected_exact.inference_solutions.is_empty());
                assert!(rejected_exact.authenticated_inference_solutions.is_empty());
                assert!(matches!(
                    &left,
                    Type::Tuple(elements)
                        if elements.len() == WIDTH
                            && matches!(elements.first(), Some(Type::Inference(id)) if id.value() == 0)
                            && matches!(elements.last(), Some(Type::Int))
                ));
                assert!(matches!(
                    &right,
                    Type::Tuple(elements)
                        if elements.len() == WIDTH
                            && matches!(elements.first(), Some(Type::Int))
                            && matches!(elements.last(), Some(Type::Bool))
                ));
            })
            .expect("the wide-unification thread should start")
            .join()
            .expect("accepted, rejected, and rollback paths should tear down on 256 KiB");
    }

    #[test]
    fn deep_kind_authenticated_unification_has_an_exact_stack_safe_budget() {
        const DEPTH: usize = 32_768;
        const CELLS: usize = 2 * DEPTH + 1;
        // Comparison/copies, fused zonking, local environment+synthesis,
        // occurs work, and transactional solution/cache retention total
        // 9C - 3D + 8. Fusion removes the duplicate C+1 authentication scan,
        // and the shared Kind engine reuses four per-function work cells.
        const EXACT: usize = 9 * CELLS - 3 * DEPTH + 8;

        std::thread::Builder::new()
            .name("deep-unification-budget".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let source = SourceFile::new("deep-unification.ash", "()")
                    .expect("the fixture source should fit");
                let span = source
                    .span(ByteRange::new(0, 2).expect("the range is ordered"))
                    .expect("the fixture span should fit");
                let deep = IterativeTypeOwner::new(nested_function_type(DEPTH));

                let mut one_short = Elaborator::new();
                let inference = one_short
                    .fresh_inference(&Kind::Type, span)
                    .expect("the fixed inference should register");
                one_short.type_work = TypeWorkBudget::with_limit(EXACT - 1);
                assert_eq!(
                    one_short.unify(&inference, &deep),
                    Err(UnificationFailure::Resource)
                );
                assert!(one_short.inference_solutions.is_empty());

                let mut exact = Elaborator::new();
                let inference = exact
                    .fresh_inference(&Kind::Type, span)
                    .expect("the fixed inference should register");
                exact.type_work = TypeWorkBudget::with_limit(EXACT);
                assert_eq!(exact.unify(&inference, &deep), Ok(()));
                assert!(matches!(
                    exact.inference_solutions.get(&InferenceVariableId::new(0)),
                    Some(Type::Function(_, _))
                ));
                assert_eq!(exact.type_work.used(), EXACT);
                drop(exact);
            })
            .expect("the deep-unification thread should start")
            .join()
            .expect("all deep unification paths must dismantle owned copies iteratively");
    }

    #[test]
    fn late_occurs_resource_failure_owns_the_deep_candidate_iteratively() {
        const DEPTH: usize = 32_768;
        const CELLS: usize = 2 * DEPTH + 1;
        // Full solution publication costs 9C - 3D + 8. Three final units retain
        // the solution, rollback entry, and authenticated-solution entry, so
        // `EXACT - 4` exhausts one unit before the occurs traversal completes.
        const EXACT: usize = 9 * CELLS - 3 * DEPTH + 8;
        const LATE_OCCURS_FAILURE: usize = EXACT - 4;

        std::thread::Builder::new()
            .name("late-occurs-candidate-owner".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let source = SourceFile::new("late-occurs-candidate-owner.ash", "()")
                    .expect("the fixture source should fit");
                let span = source
                    .span(ByteRange::new(0, 2).expect("the range is ordered"))
                    .expect("the fixture span should fit");
                let candidate = IterativeTypeOwner::new(nested_function_type(DEPTH));
                let mut elaborator = Elaborator::new();
                let inference = elaborator
                    .fresh_inference(&Kind::Type, span)
                    .expect("the fixed inference should register");
                elaborator.type_work = TypeWorkBudget::with_limit(LATE_OCCURS_FAILURE);

                assert_eq!(
                    elaborator.unify(&inference, &candidate),
                    Err(UnificationFailure::Resource)
                );
                assert!(elaborator.inference_solutions.is_empty());
                assert!(elaborator.authenticated_inference_solutions.is_empty());
                assert_eq!(elaborator.type_work.used(), LATE_OCCURS_FAILURE);
            })
            .expect("the late-occurs worker should start")
            .join()
            .expect("a late occurs failure must dismantle the candidate iteratively");
    }

    #[test]
    fn public_monotype_admission_enforces_the_exact_core_payload_depth() {
        let accepted = nested_function_type(CORE_PAYLOAD_DEPTH_LIMIT);
        let rejected = nested_function_type(CORE_PAYLOAD_DEPTH_LIMIT + 1);
        let mut accepted_budget = TypeWorkBudget::default();
        let mut rejected_budget = TypeWorkBudget::default();

        assert_eq!(
            validate_and_charge_public_monotype(
                &accepted,
                &ResolvedRegistry::default(),
                &mut accepted_budget,
            ),
            Ok(())
        );
        assert_eq!(
            validate_and_charge_public_monotype(
                &rejected,
                &ResolvedRegistry::default(),
                &mut rejected_budget,
            ),
            Err(PublicTypeAdmissionError::Invalid)
        );

        crate::types::discard_type_iteratively(accepted);
        crate::types::discard_type_iteratively(rejected);
    }

    #[test]
    fn public_monotype_admission_preserves_predecessor_nominal_saturation() {
        let source = SourceFile::new("public-saturation.ash", "Wide")
            .expect("the saturation fixture should fit");
        let span = source
            .span(ByteRange::new(0, 4).expect("the range is ordered"))
            .expect("the range belongs to the fixture");
        let owner = crate::types::NominalTypeId::new(ModuleId::new(0), 0);
        let parameters = [0, 1]
            .into_iter()
            .map(|local| ResolvedTypeVariable {
                id: TypeVariableId::resolved(ModuleId::new(0), local),
                spelling: format!("A{local}"),
                kind: crate::types::Kind::Type,
                origin: Origin::Source(span),
            })
            .collect::<Vec<_>>();
        let registry = ResolvedRegistry::new(
            vec![ResolvedNominalType {
                representation_provenance: None,
                declaration_kind: crate::resolved::ResolvedNominalDeclarationKind::Data,
                representation: None,
                id: owner,
                spelling: "Wide".to_owned(),
                constructors: Box::new([]),
                origin: Origin::Source(span),
            }],
            Vec::new(),
        )
        .with_type_parameters(vec![(owner, parameters)]);
        let bare = Type::Nominal(owner);
        let partial = Type::Application(Box::new(Type::Nominal(owner)), Box::new(Type::Int));
        let saturated = Type::Application(Box::new(partial.clone()), Box::new(Type::Bool));
        let malformed_parameter_application = Type::Application(
            Box::new(Type::Variable(TypeVariableId::new(99))),
            Box::new(Type::Unit),
        );

        assert_eq!(
            validate_and_charge_public_monotype(&bare, &registry, &mut TypeWorkBudget::default(),),
            Err(PublicTypeAdmissionError::Invalid),
        );
        assert_eq!(
            validate_and_charge_public_monotype(
                &partial,
                &registry,
                &mut TypeWorkBudget::default(),
            ),
            Err(PublicTypeAdmissionError::Invalid),
        );
        assert_eq!(
            validate_and_charge_public_monotype(
                &saturated,
                &registry,
                &mut TypeWorkBudget::default(),
            ),
            Ok(()),
        );
        assert_eq!(
            validate_and_charge_public_monotype(
                &malformed_parameter_application,
                &registry,
                &mut TypeWorkBudget::default(),
            ),
            Err(PublicTypeAdmissionError::Invalid),
        );
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
            (TypeVariableId::new(0), Kind::Type),
            (TypeVariableId::new(1), Kind::Type),
            (TypeVariableId::new(2), Kind::Type),
        ]
        .into_boxed_slice();
        let ty = Type::Forall(parameters, Box::new(Type::Int));

        let mut short = TypeWorkBudget::default();
        short
            .charge(crate::types::TYPE_WORK_LIMIT - 7)
            .expect("the fixture leaves one fewer cell than the retained clone requires");
        assert_eq!(clone_type_with_budget(&ty, &mut short), Err(()));

        let mut exact = TypeWorkBudget::default();
        exact
            .charge(crate::types::TYPE_WORK_LIMIT - 8)
            .expect("the fixture leaves the wrapper, binder identities, and body");
        assert_eq!(clone_type_with_budget(&ty, &mut exact), Ok(ty));
        assert_eq!(exact.charge(1), Err(()));
    }

    #[test]
    fn function_part_clones_charge_forall_domain_binders() {
        let parameters = vec![
            (TypeVariableId::new(0), Kind::Type),
            (TypeVariableId::new(1), Kind::Type),
            (TypeVariableId::new(2), Kind::Type),
        ]
        .into_boxed_slice();
        let domain = Type::Forall(parameters, Box::new(Type::Int));
        let function = Type::Function(Box::new(domain.clone()), Box::new(Type::Bool));

        let mut short = TypeWorkBudget::default();
        short
            .charge(crate::types::TYPE_WORK_LIMIT - 8)
            .expect("the fixture leaves one fewer cell than both retained children require");
        assert_eq!(
            clone_function_parts_with_budget(&function, &mut short),
            Err(())
        );

        let mut exact = TypeWorkBudget::default();
        exact
            .charge(crate::types::TYPE_WORK_LIMIT - 9)
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
            .set_quantified(
                ids[0],
                vec![(TypeVariableId::new(0), Kind::Type)].into_boxed_slice(),
            )
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
            .map(|index| {
                (
                    TypeVariableId::new(u32::try_from(index).expect("parameter identity")),
                    Kind::Type,
                )
            })
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
    fn mismatch_and_context_owners_discard_application_spines_on_a_small_stack() {
        const DEPTH: usize = 32_768;

        let deep = || {
            let mut ty = Type::Int;
            for _ in 0..DEPTH {
                ty = Type::Application(Box::new(ty), Box::new(Type::Unit));
            }
            ty
        };
        std::thread::Builder::new()
            .name("elaboration-type-owner-disposal".to_owned())
            .stack_size(256 * 1024)
            .spawn(move || {
                let mismatch = TypeMismatch {
                    span: resolved_module_fixture("mismatch-owner.ash", "", "Int", "42").span(),
                    expected: Box::new(deep()),
                    found: Box::new(Type::Unit),
                    expected_display: "Wide<Unit>".to_owned(),
                    found_display: "Unit".to_owned(),
                };
                drop(mismatch);

                let mut context = TypeContext::new();
                context.insert(BinderId::new(0), deep());
                drop(context);
            })
            .expect("the elaboration owner disposal thread should start")
            .join()
            .expect("mismatch and context owners must dismantle types iteratively");
    }

    #[test]
    fn public_context_replacement_discards_the_displaced_deep_fact_on_a_small_stack() {
        const DEPTH: usize = 32_768;

        std::thread::Builder::new()
            .name("context-replacement-disposal".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let mut context = TypeContext::new();
                context.insert(BinderId::new(0), deep_application_type(DEPTH));
                context.insert(BinderId::new(0), Type::Unit);
            })
            .expect("the context-replacement thread should start")
            .join()
            .expect("public context replacement must dismantle the displaced fact iteratively");
    }

    #[test]
    fn successful_pattern_check_transfers_a_deep_type_on_a_small_stack() {
        const DEPTH: usize = 32_768;

        std::thread::Builder::new()
            .name("successful-deep-pattern-check".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let source = SourceFile::new("deep-pattern-success.ash", "_")
                    .expect("the fixture should fit");
                let span = source
                    .span(ByteRange::new(0, 1).expect("the range should be ordered"))
                    .expect("the range should fit");
                let pattern = ResolvedPattern {
                    kind: ResolvedPatternKind::Wildcard,
                    span,
                };
                let expected = deep_application_type(DEPTH);
                let mut elaborator = Elaborator::new();
                elaborator.type_work = TypeWorkBudget::with_limit(usize::MAX);
                let mut context = TypeContext::new();
                let mut binders = Vec::new();

                let checked = elaborator
                    .check_core_pattern(
                        &pattern,
                        &expected,
                        &mut context,
                        &mut binders,
                        GeneratedReason::BindingLowering,
                    )
                    .expect("the wildcard should retain the expected type");
                checked.pattern.discard_iteratively();
                discard_type_iteratively(expected);
            })
            .expect("the successful pattern thread should start")
            .join()
            .expect("a successful pattern check must transfer its deep type safely");
    }

    #[test]
    fn pattern_mismatch_discards_its_deep_owned_expected_type_on_a_small_stack() {
        const DEPTH: usize = 32_768;

        std::thread::Builder::new()
            .name("deep-pattern-mismatch".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let source = SourceFile::new("deep-pattern-mismatch.ash", "true")
                    .expect("the fixture should fit");
                let span = source
                    .span(ByteRange::new(0, 4).expect("the range should be ordered"))
                    .expect("the range should fit");
                let pattern = ResolvedPattern {
                    kind: ResolvedPatternKind::Boolean(true),
                    span,
                };
                let expected = deep_application_type(DEPTH);
                let mut elaborator = Elaborator::new();
                elaborator.type_work = TypeWorkBudget::with_limit(usize::MAX);
                let mut context = TypeContext::new();
                let mut binders = Vec::new();

                assert!(matches!(
                    elaborator.check_core_pattern(
                        &pattern,
                        &expected,
                        &mut context,
                        &mut binders,
                        GeneratedReason::BindingLowering,
                    ),
                    Err(TypeError::Source(diagnostic))
                        if diagnostic.reason == TypeReason::PatternMismatch
                ));
                discard_type_iteratively(expected);
            })
            .expect("the mismatch thread should start")
            .join()
            .expect("a mismatch must dismantle its owned expected type iteratively");
    }

    #[test]
    fn pattern_resource_failure_discards_its_deep_owned_expected_type_on_a_small_stack() {
        const DEPTH: usize = 32_768;
        const DEEP_CELLS: usize = DEPTH * 2 + 1;

        std::thread::Builder::new()
            .name("deep-pattern-resource".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let source = SourceFile::new("deep-pattern-resource.ash", "value")
                    .expect("the fixture should fit");
                let span = source
                    .span(ByteRange::new(0, 5).expect("the range should be ordered"))
                    .expect("the range should fit");
                let pattern = ResolvedPattern {
                    kind: ResolvedPatternKind::Binder(crate::resolved::Binder {
                        id: BinderId::new(0),
                        spelling: "value".to_owned(),
                        origin: Origin::Source(span),
                    }),
                    span,
                };
                let expected = deep_application_type(DEPTH);
                let mut elaborator = Elaborator::new();
                elaborator.type_work = TypeWorkBudget::with_limit(DEEP_CELLS);
                let mut context = TypeContext::new();
                let mut binders = Vec::new();

                assert!(matches!(
                    elaborator.check_core_pattern(
                        &pattern,
                        &expected,
                        &mut context,
                        &mut binders,
                        GeneratedReason::BindingLowering,
                    ),
                    Err(TypeError::Internal(
                        ElaborationFailure::TypeResourceExhausted
                    ))
                ));
                discard_type_iteratively(expected);
            })
            .expect("the resource-failure thread should start")
            .join()
            .expect("a resource failure must dismantle its expected type iteratively");
    }

    #[test]
    fn late_tuple_child_failure_discards_completed_deep_patterns_on_a_small_stack() {
        const DEPTH: usize = 32_768;

        std::thread::Builder::new()
            .name("late-tuple-pattern-failure".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let source = SourceFile::new("late-tuple-pattern.ash", "(_, ())")
                    .expect("the fixture should fit");
                let span = source
                    .span(ByteRange::new(0, 7).expect("the range should be ordered"))
                    .expect("the range should fit");
                let pattern = ResolvedPattern {
                    kind: ResolvedPatternKind::Tuple(vec![
                        ResolvedPattern {
                            kind: ResolvedPatternKind::Wildcard,
                            span,
                        },
                        ResolvedPattern {
                            kind: ResolvedPatternKind::Unit,
                            span,
                        },
                    ]),
                    span,
                };
                let expected =
                    Type::Tuple(vec![deep_application_type(DEPTH), Type::Bool].into_boxed_slice());
                let mut elaborator = Elaborator::new();
                elaborator.type_work = TypeWorkBudget::with_limit(usize::MAX);
                let mut context = TypeContext::new();
                let mut binders = Vec::new();

                assert!(matches!(
                    elaborator.check_core_pattern(
                        &pattern,
                        &expected,
                        &mut context,
                        &mut binders,
                        GeneratedReason::BindingLowering,
                    ),
                    Err(TypeError::Source(diagnostic))
                        if diagnostic.reason == TypeReason::PatternMismatch
                ));
                discard_type_iteratively(expected);
            })
            .expect("the late-child thread should start")
            .join()
            .expect("completed tuple children must be dismantled iteratively after a later error");
    }

    #[test]
    fn successful_polymorphic_inference_solution_owner_drops_on_a_small_stack() {
        const DEPTH: usize = 32_768;

        std::thread::Builder::new()
            .name("successful-inference-solution-disposal".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let source = SourceFile::new("solution-disposal.ash", "()")
                    .expect("the fixture source should fit");
                let span = source
                    .span(ByteRange::new(0, 2).expect("the range is ordered"))
                    .expect("the fixture span should fit");
                let deep = IterativeTypeOwner::new(nested_function_type(DEPTH));
                let mut elaborator = Elaborator::new();
                elaborator.type_work = TypeWorkBudget::with_limit(usize::MAX);
                let inference = elaborator
                    .fresh_inference(&Kind::Type, span)
                    .expect("the fixed inference should register");

                assert_eq!(elaborator.unify(&inference, &deep), Ok(()));
                assert!(
                    elaborator
                        .inference_solutions
                        .contains_key(&InferenceVariableId::new(0))
                );
                drop(elaborator);
            })
            .expect("the inference-solution thread should start")
            .join()
            .expect("a successful deep inference solution must dismantle iteratively");
    }

    #[test]
    fn successful_result_zonk_replaces_a_deep_type_on_a_small_stack() {
        const DEPTH: usize = 32_768;

        std::thread::Builder::new()
            .name("successful-deep-result-zonk".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let resolved = resolved_module_fixture("deep-zonk.ash", "", "Int", "42");
                let span = fixture_result(&resolved).span;
                let binder = BinderId::new(0);
                let expression = ResolvedExpr {
                    kind: ResolvedExprKind::Occurrence(crate::resolved::ResolvedOccurrence {
                        term: crate::resolved::ResolvedTermName::Global(binder),
                        spelling: "deep".to_owned(),
                        origin: Origin::Source(span),
                        import_span: None,
                        evidence: Box::new([]),
                    }),
                    span,
                };
                let mut context = TypeContext::new();
                context.insert(binder, deep_application_type(DEPTH));
                let mut elaborator = Elaborator::for_resolved_expression(&resolved, &expression)
                    .expect("the standalone elaborator should fit");
                elaborator.type_work = TypeWorkBudget::with_limit(usize::MAX);

                let result = elaborator
                    .elaborate_result(&expression, &mut context)
                    .expect("the resolved occurrence should zonk successfully");
                assert!(matches!(result.ty, Type::Application(_, _)));
                result.discard_iteratively();
            })
            .expect("the result-zonk thread should start")
            .join()
            .expect("successful result zonking must dismantle the old type iteratively");
    }

    #[test]
    fn late_expression_failure_drops_pending_and_completed_types_on_a_small_stack() {
        const DEPTH: usize = 32_768;

        std::thread::Builder::new()
            .name("late-expression-work-disposal".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let resolved = resolved_module_fixture(
                    "late-expression-work.ash",
                    "",
                    "Int",
                    "fn(function) {\nfn(value) {\nfunction((value, fn(argument) {\nargument\n}))\n}\n}",
                );
                let ResolvedExprKind::Function(outer) = &fixture_result(&resolved).kind else {
                    panic!("the fixture should retain the outer function");
                };
                let ResolvedPatternKind::Binder(function) = &outer.pattern.kind else {
                    panic!("the outer parameter should be a binder");
                };
                let ResolvedExprKind::Function(inner) = &outer.body.result.kind else {
                    panic!("the fixture should retain the inner function");
                };
                let ResolvedPatternKind::Binder(value) = &inner.pattern.kind else {
                    panic!("the inner parameter should be a binder");
                };
                let application = &inner.body.result;
                assert!(matches!(application.kind, ResolvedExprKind::Apply(_)));

                let function_type = Type::Function(
                    Box::new(Type::Tuple(
                        vec![deep_application_type(DEPTH), Type::Unit].into_boxed_slice(),
                    )),
                    Box::new(deep_application_type(DEPTH)),
                );
                let mut context = TypeContext::new();
                context.insert(function.id, function_type);
                context.insert(value.id, deep_application_type(DEPTH));
                let mut elaborator =
                    Elaborator::for_module(&resolved).expect("the fixture namespace should fit");
                elaborator.type_work = TypeWorkBudget::with_limit(usize::MAX);

                let failure = elaborator
                    .elaborate_expression_with_context(
                        ElaborationTask::Synthesize {
                            expression: application,
                            cause: None,
                        },
                        &mut context,
                    )
                    .expect_err("the unannotated tuple function must fail late");
                assert!(matches!(
                    failure,
                    TypeError::Source(diagnostic)
                        if diagnostic.reason == TypeReason::FunctionNeedsContext
                ));
            })
            .expect("the late-failure thread should start")
            .join()
            .expect("pending and completed expression work must dismantle iteratively");
    }

    #[test]
    fn popped_finish_payloads_are_owned_before_missing_value_errors() {
        const DEPTH: usize = 32_768;

        std::thread::Builder::new()
            .name("popped-finish-payload-ownership".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let resolved =
                    resolved_module_fixture("missing-finish-value.ash", "", "Unit", "()");
                let span = fixture_result(&resolved).span;
                let origin = Origin::Source(span);

                let mut binder_builder = CoreBuilder::new();
                let binder = binder_builder
                    .binder(Type::Unit, origin.clone())
                    .expect("the shallow binder should fit");
                let mut elaborator =
                    Elaborator::for_module(&resolved).expect("the fixture namespace should fit");
                elaborator.type_work = TypeWorkBudget::with_limit(usize::MAX);
                assert!(matches!(
                    elaborator.elaborate_expression_with_context(
                        ElaborationTask::FinishFunction {
                            direct_binder: None,
                            pattern_binders: Vec::new(),
                            binder,
                            pattern: None,
                            domain: Some(deep_application_type(DEPTH)),
                            ty: deep_application_type(DEPTH),
                            origin: origin.clone(),
                            provenance: TypeProvenance::atom(Some(span)),
                        },
                        &mut TypeContext::new(),
                    ),
                    Err(TypeError::Internal(ElaborationFailure::InvalidState)),
                ));

                let expression = crate::resolved::ResolvedMatchExpr {
                    scrutinee: Box::new(ResolvedExpr {
                        kind: ResolvedExprKind::Unit,
                        span,
                    }),
                    arms: Vec::new(),
                };
                let mut elaborator =
                    Elaborator::for_module(&resolved).expect("the fixture namespace should fit");
                elaborator.type_work = TypeWorkBudget::with_limit(usize::MAX);
                assert!(matches!(
                    elaborator.elaborate_expression_with_context(
                        ElaborationTask::AfterMatchScrutinee {
                            expression: &expression,
                            span,
                            expected: Some((
                                ProvenancedType {
                                    ty: deep_application_type(DEPTH),
                                    provenance: TypeProvenance::atom(Some(span)),
                                },
                                CheckKind::General,
                            )),
                        },
                        &mut TypeContext::new(),
                    ),
                    Err(TypeError::Internal(ElaborationFailure::InvalidState)),
                ));
            })
            .expect("the popped-payload thread should start")
            .join()
            .expect("popped task payloads must dismantle iteratively on missing-value errors");
    }

    #[test]
    fn popped_check_function_clone_failure_discards_expected_on_a_small_stack() {
        const DEPTH: usize = 32_768;
        const ONE_DEEP_TYPE: usize = DEPTH * 2 + 1;

        std::thread::Builder::new()
            .name("popped-check-function-owner".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let resolved = resolved_module_fixture(
                    "popped-check-function.ash",
                    "",
                    "Unit -> Unit",
                    "fn(value) {\nvalue\n}",
                );
                let expression = fixture_result(&resolved);
                assert!(matches!(expression.kind, ResolvedExprKind::Function(_)));
                let expected_ty = Type::Function(
                    Box::new(deep_application_type(DEPTH)),
                    Box::new(deep_application_type(DEPTH)),
                );
                let expected = ProvenancedType {
                    provenance: TypeProvenance::unknown(&expected_ty),
                    ty: expected_ty,
                };
                let mut elaborator =
                    Elaborator::for_module(&resolved).expect("the fixture namespace should fit");
                elaborator.type_work = TypeWorkBudget::with_limit(ONE_DEEP_TYPE);

                assert!(matches!(
                    elaborator.elaborate_expression_with_context(
                        ElaborationTask::Check {
                            expression,
                            expected,
                            kind: CheckKind::General,
                        },
                        &mut TypeContext::new(),
                    ),
                    Err(TypeError::Internal(
                        ElaborationFailure::TypeResourceExhausted
                    )),
                ));
            })
            .expect("the popped Check(Function) thread should start")
            .join()
            .expect("a failed function-part clone must dismantle expected iteratively");
    }

    #[test]
    fn popped_check_function_provenance_failure_discards_cloned_parts_on_a_small_stack() {
        const DEPTH: usize = 32_768;

        std::thread::Builder::new()
            .name("popped-check-function-provenance-owner".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let resolved = resolved_module_fixture(
                    "popped-check-function-provenance.ash",
                    "",
                    "Unit -> Unit",
                    "fn(value) {\nvalue\n}",
                );
                let expression = fixture_result(&resolved);
                assert!(matches!(expression.kind, ResolvedExprKind::Function(_)));
                let expected_ty = Type::Function(
                    Box::new(deep_application_type(DEPTH)),
                    Box::new(deep_application_type(DEPTH)),
                );
                let expected = ProvenancedType {
                    ty: expected_ty,
                    provenance: TypeProvenance::atom(Some(expression.span)),
                };
                let mut elaborator =
                    Elaborator::for_module(&resolved).expect("the fixture namespace should fit");
                elaborator.type_work = TypeWorkBudget::with_limit(usize::MAX);

                assert!(matches!(
                    elaborator.elaborate_expression_with_context(
                        ElaborationTask::Check {
                            expression,
                            expected,
                            kind: CheckKind::General,
                        },
                        &mut TypeContext::new(),
                    ),
                    Err(TypeError::Internal(ElaborationFailure::InvalidState)),
                ));
            })
            .expect("the popped Check(Function) provenance thread should start")
            .join()
            .expect("malformed provenance must dismantle cloned function parts iteratively");
    }

    #[test]
    fn schedule_function_failure_discards_presentation_on_a_small_stack() {
        const DEPTH: usize = 32_768;

        std::thread::Builder::new()
            .name("schedule-function-presentation-owner".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let resolved = resolved_module_fixture(
                    "schedule-function-presentation.ash",
                    "",
                    "Unit -> Unit",
                    "fn(value) {\nvalue\n}",
                );
                let expression = fixture_result(&resolved);
                let ResolvedExprKind::Function(function) = &expression.kind else {
                    panic!("the fixture result should be a function");
                };
                let function_ty = Type::Function(Box::new(Type::Unit), Box::new(Type::Unit));
                let mut elaborator =
                    Elaborator::for_module(&resolved).expect("the fixture namespace should fit");
                elaborator.type_work = TypeWorkBudget::with_limit(0);
                let mut tasks = ElaborationTaskBuffer(Vec::new());

                assert!(matches!(
                    elaborator.schedule_function_check(
                        &mut TypeContext::new(),
                        &mut tasks,
                        0,
                        FunctionCheck {
                            parameter: &function.pattern,
                            domain: ProvenancedType {
                                ty: Type::Unit,
                                provenance: TypeProvenance::atom(Some(expression.span)),
                            },
                            codomain: ProvenancedType {
                                ty: Type::Unit,
                                provenance: TypeProvenance::atom(Some(expression.span)),
                            },
                            body: FunctionBody::Block(&function.body),
                            presentation: deep_generated_origin(DEPTH, expression.span),
                            function_type: ProvenancedType {
                                provenance: TypeProvenance::unknown(&function_ty),
                                ty: function_ty,
                            },
                            body_check: CheckKind::General,
                        },
                    ),
                    Err(TypeError::Internal(
                        ElaborationFailure::TypeResourceExhausted
                    )),
                ));
            })
            .expect("the schedule-function presentation thread should start")
            .join()
            .expect("a scheduling failure must dismantle presentation iteratively");
    }

    #[test]
    fn popped_finish_function_failure_discards_origin_on_a_small_stack() {
        const DEPTH: usize = 32_768;

        std::thread::Builder::new()
            .name("popped-finish-function-origin-owner".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let resolved =
                    resolved_module_fixture("popped-finish-origin.ash", "", "Unit", "()");
                let span = fixture_result(&resolved).span;
                let mut binder_builder = CoreBuilder::new();
                let binder = binder_builder
                    .binder(Type::Unit, Origin::Source(span))
                    .expect("the shallow binder should fit");
                let mut elaborator =
                    Elaborator::for_module(&resolved).expect("the fixture namespace should fit");

                assert!(matches!(
                    elaborator.elaborate_expression_with_context(
                        ElaborationTask::FinishFunction {
                            direct_binder: None,
                            pattern_binders: Vec::new(),
                            binder,
                            pattern: None,
                            domain: None,
                            ty: Type::Unit,
                            origin: deep_generated_origin(DEPTH, span),
                            provenance: TypeProvenance::atom(Some(span)),
                        },
                        &mut TypeContext::new(),
                    ),
                    Err(TypeError::Internal(ElaborationFailure::InvalidState)),
                ));
            })
            .expect("the popped FinishFunction origin thread should start")
            .join()
            .expect("a missing body must dismantle the function origin iteratively");
    }

    #[test]
    fn popped_finish_function_clone_failure_discards_pattern_origins_on_a_small_stack() {
        const DEPTH: usize = 32_768;

        std::thread::Builder::new()
            .name("popped-finish-function-pattern-origins".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let resolved =
                    resolved_module_fixture("popped-finish-pattern-origin.ash", "", "Unit", "()");
                let span = fixture_result(&resolved).span;
                let mut elaborator =
                    Elaborator::for_module(&resolved).expect("the fixture namespace should fit");
                let body = elaborator
                    .builder
                    .unit(Type::Unit, Origin::Source(span))
                    .expect("the shallow body should fit");
                let binder = elaborator
                    .builder
                    .binder(Type::Unit, Origin::Source(span))
                    .expect("the shallow binder should fit");
                TEST_INITIAL_TYPED_NODES.with(|initial| {
                    initial.borrow_mut().push(TypedNode {
                        node: body,
                        ty: Type::Unit,
                        provenance: TypeProvenance::atom(Some(span)),
                    });
                });
                elaborator.type_work = TypeWorkBudget::with_limit(0);

                assert!(matches!(
                    elaborator.elaborate_expression_with_context(
                        ElaborationTask::FinishFunction {
                            direct_binder: None,
                            pattern_binders: Vec::new(),
                            binder,
                            pattern: Some(CorePattern::new(
                                Type::Unit,
                                deep_generated_origin(DEPTH, span),
                                CorePatternKind::Wildcard,
                            )),
                            domain: Some(Type::Unit),
                            ty: Type::Unit,
                            origin: Origin::Source(span),
                            provenance: TypeProvenance::atom(Some(span)),
                        },
                        &mut TypeContext::new(),
                    ),
                    Err(TypeError::Internal(
                        ElaborationFailure::TypeResourceExhausted
                    )),
                ));
            })
            .expect("the popped FinishFunction pattern-origin thread should start")
            .join()
            .expect("a clone failure must dismantle cloned pattern origins iteratively");
    }

    #[test]
    fn popped_finish_function_builder_failure_discards_cloned_body_type_on_a_small_stack() {
        const DEPTH: usize = 32_768;

        std::thread::Builder::new()
            .name("popped-finish-function-cloned-body-type".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let resolved =
                    resolved_module_fixture("popped-finish-body-type.ash", "", "Unit", "()");
                let span = fixture_result(&resolved).span;
                let mut elaborator =
                    Elaborator::for_module(&resolved).expect("the fixture namespace should fit");
                let body = elaborator
                    .builder
                    .unit(Type::Unit, Origin::Source(span))
                    .expect("the shallow body should fit");
                let binder = elaborator
                    .builder
                    .binder(Type::Unit, Origin::Source(span))
                    .expect("the shallow binder should fit");
                TEST_INITIAL_TYPED_NODES.with(|initial| {
                    initial.borrow_mut().push(TypedNode {
                        node: body,
                        ty: deep_application_type(DEPTH),
                        provenance: TypeProvenance::atom(Some(span)),
                    });
                });
                elaborator.type_work = TypeWorkBudget::with_limit(usize::MAX);
                let rejected_domain = nested_function_type(CORE_PAYLOAD_DEPTH_LIMIT + 1);

                assert!(matches!(
                    elaborator.elaborate_expression_with_context(
                        ElaborationTask::FinishFunction {
                            direct_binder: None,
                            pattern_binders: Vec::new(),
                            binder,
                            pattern: Some(CorePattern::new(
                                rejected_domain.clone(),
                                Origin::Source(span),
                                CorePatternKind::Wildcard,
                            )),
                            domain: Some(rejected_domain),
                            ty: Type::Unit,
                            origin: Origin::Source(span),
                            provenance: TypeProvenance::atom(Some(span)),
                        },
                        &mut TypeContext::new(),
                    ),
                    Err(TypeError::Internal(ElaborationFailure::Core(
                        BuildError::TypeDepthExceeded
                    ))),
                ));
            })
            .expect("the popped FinishFunction cloned-body thread should start")
            .join()
            .expect("a builder failure must dismantle the cloned body type iteratively");
    }

    #[test]
    fn popped_finish_application_zonk_failure_discards_core_codomain_on_a_small_stack() {
        const DEPTH: usize = 32_768;
        const ONE_DEEP_TYPE: usize = DEPTH * 2 + 1;

        std::thread::Builder::new()
            .name("popped-finish-application-core-codomain".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let resolved =
                    resolved_module_fixture("popped-finish-application.ash", "", "Unit", "()");
                let span = fixture_result(&resolved).span;
                let mut elaborator =
                    Elaborator::for_module(&resolved).expect("the fixture namespace should fit");
                let function_node = elaborator
                    .builder
                    .unit(Type::Unit, Origin::Source(span))
                    .expect("the shallow function stand-in should fit");
                let argument_node = elaborator
                    .builder
                    .unit(Type::Unit, Origin::Source(span))
                    .expect("the shallow argument should fit");
                TEST_INITIAL_TYPED_NODES.with(|initial| {
                    initial.borrow_mut().push(TypedNode {
                        node: argument_node,
                        ty: Type::Unit,
                        provenance: TypeProvenance::atom(Some(span)),
                    });
                });
                let codomain_ty = deep_application_type(DEPTH);
                let codomain = ProvenancedType {
                    provenance: TypeProvenance::unknown(&codomain_ty),
                    ty: codomain_ty,
                };
                elaborator.type_work = TypeWorkBudget::with_limit(usize::MAX);
                elaborator
                    .fresh_inference(&Kind::Type, span)
                    .expect("the test inference fact should register");
                elaborator.type_work = TypeWorkBudget::with_limit(ONE_DEEP_TYPE);

                assert!(matches!(
                    elaborator.elaborate_expression_with_context(
                        ElaborationTask::FinishApplication {
                            whole_span: span,
                            function_span: span,
                            argument_span: span,
                            function: TypedNode {
                                node: function_node,
                                ty: Type::Unit,
                                provenance: TypeProvenance::atom(Some(span)),
                            },
                            codomain,
                        },
                        &mut TypeContext::new(),
                    ),
                    Err(TypeError::Internal(
                        ElaborationFailure::TypeResourceExhausted
                    )),
                ));
            })
            .expect("the popped FinishApplication thread should start")
            .join()
            .expect("a zonk failure must dismantle the cloned Core codomain iteratively");
    }

    #[test]
    fn lowered_evidence_provenance_failure_discards_variable_type_on_a_small_stack() {
        const DEPTH: usize = 32_768;
        const ONE_DEEP_TYPE: usize = DEPTH * 2 + 1;

        std::thread::Builder::new()
            .name("lowered-evidence-variable-type-owner".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let resolved =
                    resolved_module_fixture("lowered-evidence-owner.ash", "", "Unit", "()");
                let span = fixture_result(&resolved).span;
                let module = ModuleId::new(901);
                let interface = InterfaceId::new(module, 0);
                let method = MethodId::new(interface, 0);
                let implementation = ImplId::new(module, 0);
                let implementation_method = ImplMethodId::new(implementation, method);
                let mut selection_builder = EvidenceSelectionBuilder::new();
                let root = selection_builder
                    .push_implementation(
                        implementation,
                        Box::new([]),
                        &[],
                        &[implementation_method],
                        &mut InterfaceConstraintBudget::default(),
                    )
                    .expect("the one-node evidence plan should fit");
                let selection = selection_builder
                    .finish(
                        root,
                        InterfaceApplication::new(interface, Box::new([Type::Unit])),
                    )
                    .expect("the evidence root should exist");
                let mut lowering = EvidenceLowering {
                    interfaces: HashMap::new(),
                    interface_methods: HashMap::from([(
                        method,
                        LoweredInterfaceMethod {
                            interface,
                            parameters: Box::new([TypeVariableId::resolved(module, 0)]),
                            type_parameters: Box::new([]),
                            value_type: Type::Unit,
                            declaration_span: span,
                        },
                    )]),
                    global_schemes: HashMap::new(),
                    implementation_methods: HashMap::from([(
                        implementation_method,
                        LoweredImplementationMethod {
                            binder: BinderId::resolved(module, 0),
                            head_type_parameter_count: 0,
                            application: InterfaceApplication::new(
                                interface,
                                Box::new([Type::Unit]),
                            ),
                            scheme: LoweredScheme {
                                source_type_parameters: Some(Box::new([])),
                                type_parameters: Box::new([]),
                                requirements: Box::new([]),
                                value_type: deep_application_type(DEPTH),
                                core_scheme: deep_application_type(DEPTH),
                            },
                            span,
                        },
                    )]),
                    active_binders: HashMap::new(),
                };
                let mut elaborator =
                    Elaborator::for_module(&resolved).expect("the fixture namespace should fit");
                elaborator.type_work = TypeWorkBudget::with_limit(ONE_DEEP_TYPE * 2);

                let result = elaborator.lower_evidence_selection(
                    &selection,
                    &mut lowering,
                    &Origin::Source(span),
                    None,
                    0,
                );
                assert!(
                    matches!(
                        result,
                        Err(TypeError::Internal(
                            ElaborationFailure::TypeResourceExhausted
                        )),
                    ),
                    "{result:?}"
                );
            })
            .expect("the lowered-evidence thread should start")
            .join()
            .expect("a provenance failure must dismantle the variable type iteratively");
    }

    #[test]
    fn definition_view_lookup_failure_discards_function_and_binder_types_on_a_small_stack() {
        const DEPTH: usize = 32_768;

        std::thread::Builder::new()
            .name("definition-view-type-owners".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let resolved = resolved_module_fixture(
                    "definition-view-owner.ash",
                    "value : Unit -> Unit\nvalue argument = argument\n",
                    "Unit",
                    "()",
                );
                let mut definitions = resolved.definitions()[..1].to_vec();
                let ResolvedDefinitionKind::Equational(global) = &mut definitions[0].kind else {
                    panic!("the fixture definition should be equational");
                };
                global.interface.annotation.ty =
                    Type::Function(Box::new(deep_application_type(DEPTH)), Box::new(Type::Unit));
                let mut elaborator =
                    Elaborator::for_module(&resolved).expect("the fixture namespace should fit");
                elaborator.type_work = TypeWorkBudget::with_limit(usize::MAX);

                assert!(matches!(
                    elaborator.prepare_definition_views(
                        definitions.iter(),
                        Some(&[]),
                        TypeContext::new(),
                    ),
                    Err(TypeError::Internal(ElaborationFailure::InvalidState)),
                ));

                let ResolvedDefinitionKind::Equational(global) = &mut definitions[0].kind else {
                    unreachable!()
                };
                let deep = std::mem::replace(&mut global.interface.annotation.ty, Type::Unit);
                discard_type_iteratively(deep);
            })
            .expect("the definition-view thread should start")
            .join()
            .expect("a checked-view lookup failure must dismantle cloned types iteratively");
    }

    #[test]
    fn operational_provenance_failure_discards_cloned_function_parts_on_a_small_stack() {
        const DEPTH: usize = 32_768;

        std::thread::Builder::new()
            .name("operational-function-part-owners".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let resolved = resolved_module_fixture(
                    "operational-function-part-owner.ash",
                    "fn value(argument : Unit) -> Unit {\nargument\n}\n",
                    "Unit",
                    "()",
                );
                let ResolvedDefinitionKind::InlineOperational(operational) =
                    &resolved.definitions()[0].kind
                else {
                    panic!("the fixture definition should be operational");
                };
                let function_ty = Type::Function(
                    Box::new(deep_application_type(DEPTH)),
                    Box::new(deep_application_type(DEPTH)),
                );
                let function_type = ProvenancedType {
                    ty: function_ty,
                    provenance: TypeProvenance::atom(Some(operational.header.span)),
                };
                let mut elaborator =
                    Elaborator::for_module(&resolved).expect("the fixture namespace should fit");
                elaborator.type_work = TypeWorkBudget::with_limit(usize::MAX);

                assert!(matches!(
                    elaborator.elaborate_operational_function(
                        operational,
                        function_type,
                        &mut TypeContext::new(),
                        operational.header.span,
                    ),
                    Err(TypeError::Internal(ElaborationFailure::InvalidState)),
                ));
            })
            .expect("the operational function-part thread should start")
            .join()
            .expect("malformed provenance must dismantle operational function parts iteratively");
    }

    #[test]
    fn operational_variable_admission_failure_discards_retained_pattern_on_a_small_stack() {
        const DEPTH: usize = 100_000;

        std::thread::Builder::new()
            .name("operational-retained-pattern-owner".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let resolved = resolved_module_fixture(
                    "operational-retained-pattern-owner.ash",
                    "fn value(_ : Unit) -> Unit {\n()\n}\n",
                    "Unit",
                    "()",
                );
                let ResolvedDefinitionKind::InlineOperational(operational) =
                    &resolved.definitions()[0].kind
                else {
                    panic!("the fixture definition should be operational");
                };
                let function_ty =
                    Type::Function(Box::new(deep_application_type(DEPTH)), Box::new(Type::Unit));
                let function_type = ProvenancedType {
                    provenance: TypeProvenance::unknown(&function_ty),
                    ty: function_ty,
                };
                let mut elaborator =
                    Elaborator::for_module(&resolved).expect("the fixture namespace should fit");
                elaborator.type_work = TypeWorkBudget::with_limit(usize::MAX);

                assert!(matches!(
                    elaborator.elaborate_operational_function(
                        operational,
                        function_type,
                        &mut TypeContext::new(),
                        operational.header.span,
                    ),
                    Err(TypeError::Internal(
                        ElaborationFailure::TypeResourceExhausted
                    )),
                ));
            })
            .expect("the operational retained-pattern thread should start")
            .join()
            .expect("a variable admission failure must dismantle the pattern iteratively");
    }

    #[test]
    fn operational_codomain_failure_discards_completed_domain_on_a_small_stack() {
        const DEPTH: usize = 32_768;
        const ONE_DEEP_TYPE: usize = DEPTH * 2 + 1;

        std::thread::Builder::new()
            .name("operational-domain-owner".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let resolved = resolved_module_fixture(
                    "operational-domain-owner.ash",
                    "fn value(argument : Unit) -> Unit {\nargument\n}\n",
                    "Unit",
                    "()",
                );
                let mut definitions = resolved.definitions()[..1].to_vec();
                let ResolvedDefinitionKind::InlineOperational(operational) =
                    &mut definitions[0].kind
                else {
                    panic!("the fixture definition should be operational");
                };
                operational.header.parameters[0].annotation.ty = deep_application_type(DEPTH);
                let mut elaborator =
                    Elaborator::for_module(&resolved).expect("the fixture namespace should fit");
                elaborator.type_work = TypeWorkBudget::with_limit(ONE_DEEP_TYPE + 1);

                assert!(matches!(
                    elaborator.checked_module_schemes(&definitions),
                    Err(TypeError::Internal(
                        ElaborationFailure::TypeResourceExhausted
                    )),
                ));

                let ResolvedDefinitionKind::InlineOperational(operational) =
                    &mut definitions[0].kind
                else {
                    unreachable!()
                };
                let deep = std::mem::replace(
                    &mut operational.header.parameters[0].annotation.ty,
                    Type::Unit,
                );
                discard_type_iteratively(deep);
            })
            .expect("the operational-domain thread should start")
            .join()
            .expect("a codomain failure must dismantle the completed domain iteratively");
    }

    #[test]
    fn nonfunction_definition_rejection_discards_the_resolved_type_on_a_small_stack() {
        const DEPTH: usize = 32_768;

        std::thread::Builder::new()
            .name("nonfunction-definition-owner".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let resolved = resolved_module_fixture(
                    "nonfunction-definition-owner.ash",
                    "value : Unit -> Unit\nvalue argument = argument\n",
                    "Unit",
                    "()",
                );
                let mut definitions = resolved.definitions()[..1].to_vec();
                let ResolvedDefinitionKind::Equational(global) = &mut definitions[0].kind else {
                    panic!("the fixture definition should be equational");
                };
                global.interface.annotation.ty = deep_application_type(DEPTH);
                let mut elaborator =
                    Elaborator::for_module(&resolved).expect("the fixture namespace should fit");
                elaborator.type_work = TypeWorkBudget::with_limit(usize::MAX);

                assert!(matches!(
                    elaborator.prepare_definition_views(
                        definitions.iter(),
                        None,
                        TypeContext::new(),
                    ),
                    Err(TypeError::Source(diagnostic))
                        if diagnostic.reason == TypeReason::EquationInterfaceNotFunction
                ));

                let ResolvedDefinitionKind::Equational(global) = &mut definitions[0].kind else {
                    unreachable!()
                };
                let deep = std::mem::replace(&mut global.interface.annotation.ty, Type::Unit);
                discard_type_iteratively(deep);
            })
            .expect("the nonfunction-definition thread should start")
            .join()
            .expect("a nonfunction rejection must dismantle the resolved type iteratively");
    }

    #[test]
    fn ambiguous_result_discards_the_zonked_type_on_a_small_stack() {
        const DEPTH: usize = 32_768;

        std::thread::Builder::new()
            .name("ambiguous-result-zonk-owner".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let resolved =
                    resolved_module_fixture("ambiguous-result-owner.ash", "", "Unit", "()");
                let span = fixture_result(&resolved).span;
                let binder = BinderId::new(0);
                let expression = ResolvedExpr {
                    kind: ResolvedExprKind::Occurrence(crate::resolved::ResolvedOccurrence {
                        term: crate::resolved::ResolvedTermName::Global(binder),
                        spelling: "ambiguous".to_owned(),
                        origin: Origin::Source(span),
                        import_span: None,
                        evidence: Box::new([]),
                    }),
                    span,
                };
                let mut ambiguous = deep_application_type(DEPTH);
                let Type::Application(_, argument) = &mut ambiguous else {
                    unreachable!()
                };
                discard_type_iteratively(std::mem::replace(
                    argument.as_mut(),
                    Type::Inference(InferenceVariableId::new(0)),
                ));
                let provenance = TypeProvenance::unknown(&ambiguous);
                let mut context = TypeContext::new();
                context.binders.insert(
                    binder,
                    TypeFact {
                        ty: ambiguous,
                        provenance,
                        quantified: Box::new([]),
                    },
                );
                let mut elaborator = Elaborator::for_resolved_expression(&resolved, &expression)
                    .expect("the standalone binder reservation should fit");
                elaborator.type_work = TypeWorkBudget::with_limit(usize::MAX);
                elaborator
                    .fresh_inference(&Kind::Type, span)
                    .expect("the test inference fact should register");

                assert!(matches!(
                    elaborator.elaborate_result(&expression, &mut context),
                    Err(TypeError::Source(diagnostic))
                        if diagnostic.reason == TypeReason::AmbiguousType
                ));
            })
            .expect("the ambiguous-result thread should start")
            .join()
            .expect("an ambiguous result must dismantle the zonked type iteratively");
    }

    #[test]
    fn schedule_function_zonk_failure_discards_the_checked_pattern_on_a_small_stack() {
        const DEPTH: usize = 32_768;

        std::thread::Builder::new()
            .name("schedule-function-checked-pattern-owner".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let resolved = resolved_module_fixture(
                    "schedule-function-checked-pattern.ash",
                    "",
                    "Unit -> Unit",
                    "fn(value) {\nvalue\n}",
                );
                let expression = fixture_result(&resolved);
                let ResolvedExprKind::Function(function) = &expression.kind else {
                    panic!("the fixture result should be a function");
                };
                let parameter = ResolvedPattern {
                    kind: ResolvedPatternKind::Tuple(vec![
                        ResolvedPattern {
                            kind: ResolvedPatternKind::Wildcard,
                            span: expression.span,
                        },
                        ResolvedPattern {
                            kind: ResolvedPatternKind::Boolean(true),
                            span: expression.span,
                        },
                    ]),
                    span: expression.span,
                };
                let make_domain = || {
                    Type::Tuple(
                        vec![
                            deep_application_type(DEPTH),
                            Type::Inference(InferenceVariableId::new(0)),
                        ]
                        .into_boxed_slice(),
                    )
                };

                let calibration_domain = make_domain();
                let mut calibration =
                    Elaborator::for_module(&resolved).expect("the fixture namespace should fit");
                calibration.type_work = TypeWorkBudget::with_limit(usize::MAX);
                calibration
                    .fresh_inference(&Kind::Type, expression.span)
                    .expect("the calibration inference fact should register");
                let mut calibration_binders = Vec::new();
                let checked = calibration
                    .check_core_pattern(
                        &parameter,
                        &calibration_domain,
                        &mut TypeContext::new(),
                        &mut calibration_binders,
                        GeneratedReason::FunctionLowering,
                    )
                    .expect("the tuple pattern should refine its Boolean component");
                assert!(checked.inference_changed);
                checked.pattern.discard_iteratively();
                let exact_check_work = calibration.type_work.used();
                discard_type_iteratively(calibration_domain);

                let domain_ty = make_domain();
                let domain = ProvenancedType {
                    provenance: TypeProvenance::unknown(&domain_ty),
                    ty: domain_ty,
                };
                let function_ty = Type::Function(Box::new(make_domain()), Box::new(Type::Unit));
                let mut elaborator =
                    Elaborator::for_module(&resolved).expect("the fixture namespace should fit");
                elaborator.type_work = TypeWorkBudget::with_limit(usize::MAX);
                elaborator
                    .fresh_inference(&Kind::Type, expression.span)
                    .expect("the test inference fact should register");
                elaborator.type_work = TypeWorkBudget::with_limit(exact_check_work);

                assert!(matches!(
                    elaborator.schedule_function_check(
                        &mut TypeContext::new(),
                        &mut ElaborationTaskBuffer(Vec::new()),
                        0,
                        FunctionCheck {
                            parameter: &parameter,
                            domain,
                            codomain: ProvenancedType {
                                ty: Type::Unit,
                                provenance: TypeProvenance::atom(Some(expression.span)),
                            },
                            body: FunctionBody::Block(&function.body),
                            presentation: Origin::Source(expression.span),
                            function_type: ProvenancedType {
                                provenance: TypeProvenance::unknown(&function_ty),
                                ty: function_ty,
                            },
                            body_check: CheckKind::General,
                        },
                    ),
                    Err(TypeError::Internal(
                        ElaborationFailure::TypeResourceExhausted
                    )),
                ));
            })
            .expect("the schedule-function checked-pattern thread should start")
            .join()
            .expect("a zonk failure must dismantle the checked pattern iteratively");
    }

    #[test]
    fn central_finish_check_success_returns_a_public_deep_typed_node_on_a_small_stack() {
        const DEPTH: usize = 32_768;

        std::thread::Builder::new()
            .name("central-finish-check-success".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let resolved =
                    resolved_module_fixture("central-finish-check.ash", "", "Unit", "()");
                let span = fixture_result(&resolved).span;
                let binder = BinderId::new(0);
                let nominal = crate::types::NominalTypeId::new(resolved.module(), 0);
                let expression = ResolvedExpr {
                    kind: ResolvedExprKind::Occurrence(crate::resolved::ResolvedOccurrence {
                        term: crate::resolved::ResolvedTermName::Global(binder),
                        spelling: "deep".to_owned(),
                        origin: Origin::Source(span),
                        import_span: None,
                        evidence: Box::new([]),
                    }),
                    span,
                };
                let parameters = (0..DEPTH)
                    .map(|index| crate::resolved::ResolvedTypeVariable {
                        id: TypeVariableId::new(
                            u32::try_from(index).expect("the parameter identity should fit"),
                        ),
                        spelling: format!("T{index}"),
                        kind: crate::types::Kind::Type,
                        origin: Origin::Source(span),
                    })
                    .collect::<Vec<_>>();
                let registry = Arc::new(
                    ResolvedRegistry::new(
                        vec![crate::resolved::ResolvedNominalType {
                            representation_provenance: None,
                            declaration_kind: crate::resolved::ResolvedNominalDeclarationKind::Data,
                            representation: None,
                            id: nominal,
                            spelling: "Deep".to_owned(),
                            constructors: Box::new([]),
                            origin: Origin::Source(span),
                        }],
                        Vec::new(),
                    )
                    .with_type_parameters(vec![(nominal, parameters)]),
                );
                let deep = || {
                    Type::apply_arguments(
                        Type::Nominal(nominal),
                        std::iter::repeat_with(|| Type::Unit).take(DEPTH),
                    )
                };
                let expected_ty = deep();
                let mut context = TypeContext::new();
                context.insert(binder, deep());
                let mut elaborator = Elaborator::for_resolved_expression(&resolved, &expression)
                    .expect("the standalone binder reservation should fit");
                let mut builder = CoreBuilder::with_registry(Arc::clone(&registry));
                builder
                    .reserve_resolved_binders([binder])
                    .expect("the standalone binder identity should reserve once");
                elaborator.builder = builder;
                elaborator.registry = registry;
                elaborator.type_work = TypeWorkBudget::with_limit(usize::MAX);

                let result = elaborator
                    .check(&expression, &expected_ty, &context)
                    .expect("the central FinishCheck path should retain the deep result");
                assert!(matches!(result.ty, Type::Application(_, _)));
                result.discard_iteratively();
                discard_type_iteratively(expected_ty);
            })
            .expect("the central FinishCheck thread should start")
            .join()
            .expect("a public deep TypedNode must be safely disposable on the small stack");
    }

    #[test]
    fn late_redundant_match_arm_discards_popped_progress_on_a_small_stack() {
        const DEPTH: usize = 32_768;

        std::thread::Builder::new()
            .name("central-late-match-failure".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let resolved = resolved_module_fixture("central-late-match.ash", "", "Unit", "()");
                let span = fixture_result(&resolved).span;
                let binder = BinderId::new(0);
                let occurrence = || ResolvedExpr {
                    kind: ResolvedExprKind::Occurrence(crate::resolved::ResolvedOccurrence {
                        term: crate::resolved::ResolvedTermName::Global(binder),
                        spelling: "deep".to_owned(),
                        origin: Origin::Source(span),
                        import_span: None,
                        evidence: Box::new([]),
                    }),
                    span,
                };
                let arm = || crate::resolved::ResolvedMatchArm {
                    pattern: ResolvedPattern {
                        kind: ResolvedPatternKind::Wildcard,
                        span,
                    },
                    body: occurrence(),
                    span,
                };
                let expression = ResolvedExpr {
                    kind: ResolvedExprKind::Match(crate::resolved::ResolvedMatchExpr {
                        scrutinee: Box::new(occurrence()),
                        arms: vec![arm(), arm()],
                    }),
                    span,
                };
                let mut context = TypeContext::new();
                context.insert(binder, deep_application_type(DEPTH));
                let mut elaborator = Elaborator::for_resolved_expression(&resolved, &expression)
                    .expect("the standalone binder reservation should fit");
                elaborator.type_work = TypeWorkBudget::with_limit(usize::MAX);

                assert!(matches!(
                    elaborator.elaborate_expression_with_context(
                        ElaborationTask::Synthesize {
                            expression: &expression,
                            cause: None,
                        },
                        &mut context,
                    ),
                    Err(TypeError::Source(diagnostic))
                        if diagnostic.reason == TypeReason::RedundantCase
                ));
            })
            .expect("the central late-match thread should start")
            .join()
            .expect("popped match progress must dismantle completed deep owners iteratively");
    }

    #[test]
    fn constrained_scheme_construction_has_an_exact_stack_safe_type_budget() {
        std::thread::Builder::new()
            .name("constrained-scheme-budget".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                const DEPTH: usize = 10_000;
                // One parameter record, one requirement record, one retained
                // Kind::Type node, one requirement-argument Type node, and the
                // 2 * DEPTH + 1 value-Type nodes.
                const EXACT_WORK: usize = 2 * DEPTH + 5;
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
    fn lowered_requirement_rows_and_replacements_have_an_exact_retryable_type_boundary() {
        // One requirement-row owner + one source value clone + one method-row
        // owner + one replacement-entry owner + one replacement argument +
        // one substituted result + two application cells + one Core value
        // clone + one evidence-function cell + one evidence-domain clone.
        const EXACT_TYPE_WORK: usize = 1 + 1 + 1 + 1 + 1 + 1 + 2 + 1 + 1 + 1;

        let resolved = resolved_module_fixture("lowered-row-budget.ash", "", "Unit", "()");
        let span = fixture_result(&resolved).span;
        let module = ModuleId::new(777);
        let owner = BinderId::resolved(module, 0);
        let interface = InterfaceId::new(module, 0);
        let parameter = TypeVariableId::resolved(module, 0);
        let method = MethodId::new(interface, 0);
        let requirement = RequirementId::new(RequirementOwner::Global(owner), 0);
        let scheme = ConstrainedScheme {
            type_parameters: Box::new([]),
            requirements: Box::new([CheckedRequirement {
                id: requirement,
                application: InterfaceApplication::new(interface, Box::new([Type::Unit])),
                origin: Origin::Source(span),
                span,
            }]),
            value_type: Type::Unit,
        };
        let lowering = EvidenceLowering {
            interfaces: HashMap::from([(
                interface,
                LoweredInterface {
                    methods: Box::new([method]),
                    determination: None,
                },
            )]),
            interface_methods: HashMap::from([(
                method,
                LoweredInterfaceMethod {
                    interface,
                    parameters: Box::new([parameter]),
                    type_parameters: Box::new([]),
                    value_type: Type::Variable(parameter),
                    declaration_span: span,
                },
            )]),
            global_schemes: HashMap::new(),
            implementation_methods: HashMap::new(),
            active_binders: HashMap::new(),
        };
        let mut elaborator =
            Elaborator::for_module(&resolved).expect("the lowering fixture namespace should fit");

        elaborator.type_work = TypeWorkBudget::with_limit(EXACT_TYPE_WORK - 1);
        assert!(matches!(
            elaborator.lower_constrained_scheme(
                &scheme,
                &lowering,
                MethodEvidenceOwner::Global(owner),
                false,
                span,
            ),
            Err(TypeError::Internal(
                ElaborationFailure::TypeResourceExhausted
            )),
        ));

        elaborator.type_work = TypeWorkBudget::with_limit(EXACT_TYPE_WORK);
        let lowered = elaborator
            .lower_constrained_scheme(
                &scheme,
                &lowering,
                MethodEvidenceOwner::Global(owner),
                false,
                span,
            )
            .expect("a fresh exact budget should retry the unpublished lowered scheme");
        assert_eq!(elaborator.type_work.used(), EXACT_TYPE_WORK);
        assert_eq!(lowered.requirements.len(), 1);
        assert_eq!(lowered.requirements[0].methods.len(), 1);
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
        let mut selector = EvidenceSelector::new();
        for scheme in &schemes {
            selector
                .add_scheme(
                    scheme,
                    &mut InterfaceConstraintBudget::default(),
                    &mut elaborator.type_work,
                )
                .expect("the unconstrained global scheme should fit the selector");
        }
        elaborator.selection = Some(selector);
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
