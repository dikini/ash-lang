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
    pattern::{
        UsefulnessBudget, UsefulnessError, display_witness, missing_witness_for_types,
        missing_witness_for_types_with_budget, usefulness_with_budget,
    },
    resolved::{
        BinderId, ResolvedBinding, ResolvedBlock, ResolvedDefinitionKind, ResolvedExpr,
        ResolvedExprKind, ResolvedLocalDeclaration, ResolvedPattern, ResolvedPatternKind,
        ResolvedProgram, ResolvedRecursiveGroup, ResolvedRegistry, ResolvedType,
        ResolvedTypeProvenance, ResolvedTypeProvenanceNode,
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
    /// The general checking rule found structurally unequal types.
    Mismatch(TypeMismatch),
    /// Typed elaboration could not preserve its compiler invariants.
    Internal(ElaborationFailure),
}

impl fmt::Display for TypeError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Source(diagnostic) => formatter.write_str(&diagnostic.render_plain()),
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
                        span: None,
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
                    nodes.push(TypeProvenanceNode::Fact(None));
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

/// The one bidirectional typed elaborator for resolved Mini-Ash syntax.
#[derive(Debug)]
#[must_use]
pub struct Elaborator {
    builder: CoreBuilder,
    registry: Arc<ResolvedRegistry>,
    state: ElaboratorState,
    next_inference: u32,
    inference_origins: Vec<Span>,
    next_generated_type_variable: u32,
    inference_solutions: HashMap<InferenceVariableId, Type>,
    monomorphic_recursive: HashSet<BinderId>,
    type_work: TypeWorkBudget,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ElaboratorState {
    Ready,
    Poisoned,
}

impl Elaborator {
    /// Starts an elaborator for an expression with no resolved binder namespace.
    pub fn new() -> Self {
        let registry = Arc::new(ResolvedRegistry::default());
        Self {
            builder: CoreBuilder::with_registry(Arc::clone(&registry)),
            registry,
            state: ElaboratorState::Ready,
            next_inference: 0,
            inference_origins: Vec::new(),
            next_generated_type_variable: u32::MAX,
            inference_solutions: HashMap::new(),
            monomorphic_recursive: HashSet::new(),
            type_work: TypeWorkBudget::default(),
        }
    }

    /// Starts an elaborator after reserving every resolver-assigned binder.
    ///
    /// # Errors
    ///
    /// Returns a Core construction failure if the complete namespace cannot be
    /// reserved before elaboration starts.
    pub fn for_program(program: &ResolvedProgram) -> Result<Self, ElaborationFailure> {
        let registry = Arc::clone(&program.registry);
        let mut builder = CoreBuilder::with_registry(Arc::clone(&registry));
        builder.reserve_resolved_binders(resolved_binders(program))?;
        Ok(Self {
            builder,
            registry,
            state: ElaboratorState::Ready,
            next_inference: 0,
            inference_origins: Vec::new(),
            next_generated_type_variable: u32::MAX,
            inference_solutions: HashMap::new(),
            monomorphic_recursive: HashSet::new(),
            type_work: TypeWorkBudget::default(),
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
        if self.state == ElaboratorState::Poisoned {
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
        if self.state == ElaboratorState::Poisoned {
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

    /// Elaborates file-wide recursive global definitions and the required result.
    ///
    /// Every declared global monotype enters the typing context before any body
    /// is checked. The resulting functions form one recursive Core group around
    /// the file result.
    ///
    /// # Errors
    ///
    /// Returns a structured source typing error or Core construction failure.
    /// Any failure poisons the elaborator so partially emitted global Core
    /// cannot be selected as a program root.
    pub fn synthesize_program(
        &mut self,
        program: &ResolvedProgram,
    ) -> Result<TypedNode, TypeError> {
        if self.state == ElaboratorState::Poisoned {
            return Err(invalid_state());
        }
        let result = self.elaborate_program(program);
        if result.is_err() {
            self.state = ElaboratorState::Poisoned;
        }
        result
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
        if self.state == ElaboratorState::Poisoned {
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
        let identity = TypeVariableId::new(self.next_generated_type_variable);
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

    fn elaborate_program(&mut self, program: &ResolvedProgram) -> Result<TypedNode, TypeError> {
        let mut context = TypeContext::new();
        let mut globals = Vec::with_capacity(program.definitions.len());
        let mut global_binders = HashMap::with_capacity(program.definitions.len());
        let mut global_quantifiers = Vec::with_capacity(program.definitions.len());

        for definition in &program.definitions {
            let (name, function_type, type_parameters) = match &definition.kind {
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
            global_quantifiers.push((name.id, quantified));
        }

        for definition in &program.definitions {
            let recursive_binder = match &definition.kind {
                ResolvedDefinitionKind::Equational(equational) => equational.interface.name.id,
                ResolvedDefinitionKind::InlineOperational(operational) => {
                    operational.header.name.id
                }
            };
            if !self.monomorphic_recursive.insert(recursive_binder) {
                return Err(invalid_state());
            }
            let (name, mut function) = match &definition.kind {
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
                            &mut context,
                            definition.span,
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
                            &mut context,
                            definition.span,
                        )?,
                    )
                }
            };
            if !self.monomorphic_recursive.remove(&recursive_binder) {
                return Err(invalid_state());
            }
            if !function.provenance.aligns(&function.ty) {
                return Err(invalid_state());
            }
            let binder = global_binders.remove(&name.id).ok_or_else(invalid_state)?;
            let quantified = global_quantifiers
                .iter()
                .find_map(|(binder, quantified)| (*binder == name.id).then_some(quantified))
                .ok_or_else(invalid_state)?;
            if !quantified.is_empty() {
                self.type_work
                    .charge(1)
                    .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
                let scheme_parameters =
                    clone_type_variables_with_budget(quantified, &mut self.type_work)
                        .map_err(|()| {
                            TypeError::Internal(ElaborationFailure::TypeResourceExhausted)
                        })?
                        .into_boxed_slice();
                let scheme_body = self.clone_type(&function.ty)?;
                let scheme = Type::Forall(scheme_parameters, Box::new(scheme_body));
                let abstraction_parameters =
                    clone_type_variables_with_budget(quantified, &mut self.type_work).map_err(
                        |()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted),
                    )?;
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
            globals.push(ElaboratedBinding {
                binder,
                initializer: function.node,
            });
        }

        for (binder, quantified) in global_quantifiers {
            context.set_quantified(binder, quantified)?;
        }
        self.monomorphic_recursive.clear();

        let mut result = self.elaborate_expression_with_context(
            ElaborationTask::Synthesize {
                expression: &program.result,
                cause: Some(SynthesisCause::ProgramResult(program.result.span)),
            },
            &mut context,
        )?;
        let (zonked_result, result_is_ambiguous) = self.zonk_with_status(&result.ty)?;
        if result_is_ambiguous {
            return Err(inference_failure(
                TypeReason::AmbiguousType,
                program.result.span,
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
        if !globals.is_empty() {
            let members = globals
                .into_iter()
                .map(|global| (global.binder, global.initializer))
                .collect();
            let core_result_type = self.clone_type(&result.ty)?;
            let node = self.builder.recursive_binding(
                members,
                result.node,
                core_result_type,
                Origin::Generated {
                    cause: Box::new(Origin::Source(program.span)),
                    reason: GeneratedReason::RecursiveBindingLowering,
                },
            )?;
            result = TypedNode {
                node,
                ty: result.ty,
                provenance: result.provenance,
            };
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
                    ResolvedExprKind::Occurrence(occurrence) => {
                        let fact = context.fact(occurrence.binder).ok_or_else(invalid_state)?;
                        let rigid = self.monomorphic_recursive.contains(&occurrence.binder);
                        let (ty, arguments) = self.instantiate(fact, rigid, current.span)?;
                        let provenance = fact.provenance.clone();
                        let scheme =
                            clone_scheme_with_budget(fact, &mut self.type_work).map_err(|()| {
                                TypeError::Internal(ElaborationFailure::TypeResourceExhausted)
                            })?;
                        let mut node = self.builder.variable(
                            occurrence.binder,
                            scheme,
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
                        values.push(TypedNode {
                            node,
                            ty,
                            provenance,
                        });
                    }
                    ResolvedExprKind::Constructor(occurrence) => {
                        let constructor = self
                            .registry
                            .constructor(occurrence.constructor)
                            .ok_or_else(invalid_state)?;
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
                        let fact = TypeFact {
                            ty: scheme,
                            provenance: TypeProvenance::atom(None),
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
                        let provenance = self.unknown_provenance(&ty)?;
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
                                if self.monomorphic_recursive.contains(&occurrence.binder)
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
                        if let Some(witness) = missing_witness_for_types(
                            &matrix,
                            std::slice::from_ref(&domain),
                            &self.registry,
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
                ElaborationTask::FinishBinding { binding, expected } => {
                    let mut initializer = values.pop().ok_or_else(invalid_state)?;
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
                    if let Some(witness) = missing_witness_for_types(
                        &matrix,
                        std::slice::from_ref(&binding_type.ty),
                        &self.registry,
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
                        coverage_budget: UsefulnessBudget::default(),
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
                &mut progress.coverage_budget,
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
            &mut progress.coverage_budget,
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
        let Some(first) = equational.equations.first() else {
            return Err(invalid_state());
        };
        let arity = first.patterns.len();
        if arity == 0
            || equational
                .equations
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
                    cause: Box::new(equational_origin(definition_span, equational)),
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
            .charge(equational.equations.len().saturating_mul(2))
            .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
        let mut coverage_matrix = Vec::new();
        coverage_matrix
            .try_reserve(equational.equations.len())
            .map_err(|_| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
        let mut coverage_budget = UsefulnessBudget::default();
        let mut clause_bodies = Vec::new();
        clause_bodies
            .try_reserve(equational.equations.len())
            .map_err(|_| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))?;
        for clause in &equational.equations {
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
                &mut coverage_budget,
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
            &mut coverage_budget,
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
                    cause: Box::new(equational_origin(definition_span, equational)),
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
            if let Some(witness) = missing_witness_for_types(
                &matrix,
                std::slice::from_ref(&domain.ty),
                &self.registry,
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
    FinishBinding {
        binding: &'a ResolvedBinding,
        expected: Option<ProvenancedType>,
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
    coverage_budget: UsefulnessBudget,
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
                tasks.push(ElaborationTask::FinishBinding {
                    binding,
                    expected: finish_expected,
                });
                match (expected, binding.annotation.as_ref()) {
                    (Some(expected), Some(annotation)) => tasks.push(ElaborationTask::Check {
                        expression: &binding.initializer,
                        expected,
                        kind: CheckKind::BindingInitializer {
                            initializer_span: binding.initializer.span,
                            annotation_span: annotation.span,
                        },
                    }),
                    (None, None) => tasks.push(ElaborationTask::Synthesize {
                        expression: &binding.initializer,
                        cause: Some(SynthesisCause::Binding(binding.span)),
                    }),
                    _ => return Err(invalid_state()),
                }
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
    equation_name: &crate::resolved::ResolvedOccurrence,
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
        ResolvedExprKind::Occurrence(occurrence) if recursive.contains(&occurrence.binder) => {
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
            ResolvedExprKind::Occurrence(occurrence) if recursive.contains(&occurrence.binder) => {
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

fn resolved_binders(program: &ResolvedProgram) -> Vec<BinderId> {
    let mut binders = Vec::new();
    let mut expressions = vec![&program.result];
    for definition in &program.definitions {
        match &definition.kind {
            ResolvedDefinitionKind::Equational(equational) => {
                binders.push(equational.interface.name.id);
                for equation in &equational.equations {
                    for pattern in &equation.patterns {
                        collect_pattern_binders(pattern, &mut binders);
                    }
                    expressions.push(&equation.body);
                }
            }
            ResolvedDefinitionKind::InlineOperational(operational) => {
                binders.push(operational.header.name.id);
                for parameter in &operational.header.parameters {
                    collect_pattern_binders(&parameter.pattern, &mut binders);
                }
                expressions.push(&operational.body.result);
                for declaration in &operational.body.declarations {
                    collect_resolved_declaration(declaration, &mut binders, &mut expressions);
                }
            }
        }
    }
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
                    collect_resolved_declaration(declaration, &mut binders, &mut expressions);
                }
            }
            ResolvedExprKind::Function(function) => {
                collect_pattern_binders(&function.pattern, &mut binders);
                expressions.push(&function.body.result);
                for declaration in &function.body.declarations {
                    collect_resolved_declaration(declaration, &mut binders, &mut expressions);
                }
            }
            ResolvedExprKind::Tuple(elements) => expressions.extend(elements),
            ResolvedExprKind::Match(match_expression) => {
                expressions.push(&match_expression.scrutinee);
                for arm in &match_expression.arms {
                    collect_pattern_binders(&arm.pattern, &mut binders);
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
    binders
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
    use super::*;
    use crate::{
        lexer::lex,
        parser::{parse, project},
        resolve::resolve,
        source::{ByteRange, SourceFile},
    };

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
    fn ordinary_match_precharges_retained_arm_and_matrix_storage() {
        let source = SourceFile::new(
            "ordinary-match-budget.ash",
            "match true {\ntrue => 1\nfalse => 0\n}\n",
        )
        .expect("the fixture should fit");
        let tree = parse(lex(&source).expect("the fixture should lex"));
        let surface = project(&source, &tree).expect("the fixture should project");
        let resolved = resolve(&surface).expect("the fixture should resolve");
        let mut short =
            Elaborator::for_program(&resolved).expect("the binder namespace should fit");
        short
            .type_work
            .charge(crate::types::TYPE_WORK_LIMIT - 13)
            .expect("the fixture leaves one fewer unit than complete match storage requires");

        assert_eq!(
            short.elaborate_expression_with_context(
                ElaborationTask::Synthesize {
                    expression: &resolved.result,
                    cause: None,
                },
                &mut TypeContext::new(),
            ),
            Err(TypeError::Internal(
                ElaborationFailure::TypeResourceExhausted
            ))
        );

        let mut exact =
            Elaborator::for_program(&resolved).expect("the binder namespace should fit");
        exact
            .type_work
            .charge(crate::types::TYPE_WORK_LIMIT - 14)
            .expect("the fixture leaves type copies plus both progress and Core arm storage");
        let typed = exact
            .elaborate_expression_with_context(
                ElaborationTask::Synthesize {
                    expression: &resolved.result,
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
        let source = SourceFile::new(
            "resolved-type-copy.ash",
            "identity : Int -> Bool\nidentity value = false\n\n0\n",
        )
        .expect("the fixture should fit");
        let tree = parse(lex(&source).expect("the fixture should lex"));
        let surface = project(&source, &tree).expect("the fixture should project");
        let resolved = resolve(&surface).expect("the fixture should resolve");
        let ResolvedDefinitionKind::Equational(equational) = &resolved.definitions[0].kind else {
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
        let source = SourceFile::new(
            "tuple-operational-domain-budget.ash",
            "fn choose(left: Int, right: Bool) -> Int {\nleft\n}\n\nchoose(42, false)\n",
        )
        .expect("the fixture should fit");
        let tree = parse(lex(&source).expect("the fixture should lex"));
        let surface = project(&source, &tree).expect("the fixture should project");
        let resolved = resolve(&surface).expect("the fixture should resolve");
        let ResolvedDefinitionKind::InlineOperational(operational) = &resolved.definitions[0].kind
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
        let source = SourceFile::new("wide-occurrence-budget.ash", "fn(value) {\nvalue\n}\n")
            .expect("the fixture should fit");
        let tree = parse(lex(&source).expect("the fixture should lex"));
        let surface = project(&source, &tree).expect("the fixture should project");
        let resolved = resolve(&surface).expect("the fixture should resolve");
        let ResolvedExprKind::Function(function) = &resolved.result.kind else {
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
            Elaborator::for_program(&resolved).expect("the binder namespace should fit");
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
        let source = SourceFile::new(
            "unresolved-finish.ash",
            "{\nlet _ = fn(value) {\nvalue\n}\n()\n}\n",
        )
        .expect("the fixture should fit");
        let tree = parse(lex(&source).expect("the fixture should lex"));
        let surface = project(&source, &tree).expect("the fixture should project");
        let resolved = resolve(&surface).expect("the fixture should resolve");
        let mut elaborator =
            Elaborator::for_program(&resolved).expect("the binder namespace should fit");
        let typed = elaborator
            .synthesize(&resolved.result, &TypeContext::new())
            .expect("standalone synthesis defers whole-program ambiguity");

        assert!(matches!(
            elaborator.finish(typed.node),
            Err(ElaborationFailure::Core(BuildError::InvalidPayload))
        ));
    }

    #[test]
    fn public_synthesis_rejects_unresolved_inference_before_context_clone() {
        let source = SourceFile::new(
            "external-inference-finish.ash",
            "identity : Int -> Int\nidentity value = value\n\nidentity\n",
        )
        .expect("the fixture should fit");
        let tree = parse(lex(&source).expect("the fixture should lex"));
        let surface = project(&source, &tree).expect("the fixture should project");
        let resolved = resolve(&surface).expect("the fixture should resolve");
        let ResolvedExprKind::Occurrence(occurrence) = &resolved.result.kind else {
            panic!("the result should be a resolved occurrence");
        };
        let mut context = TypeContext::new();
        context.insert(
            occurrence.binder,
            Type::Inference(InferenceVariableId::new(999)),
        );
        let mut elaborator =
            Elaborator::for_program(&resolved).expect("the binder namespace should fit");
        TYPE_CONTEXT_CLONES.with(|clones| clones.set(0));

        assert_eq!(
            elaborator.synthesize(&resolved.result, &context),
            Err(TypeError::Internal(ElaborationFailure::InvalidState))
        );
        TYPE_CONTEXT_CLONES.with(|clones| assert_eq!(clones.get(), 0));
    }

    #[test]
    fn public_context_inference_cannot_alias_a_fresh_private_solution() {
        let source = SourceFile::new(
            "external-inference-collision.ash",
            "external : Int -> Int\nexternal value = value\n\n{\nlet increment = fn(value) {\nvalue + 1\n}\nexternal\n}\n",
        )
        .expect("the fixture should fit");
        let tree = parse(lex(&source).expect("the fixture should lex"));
        let surface = project(&source, &tree).expect("the fixture should project");
        let resolved = resolve(&surface).expect("the fixture should resolve");
        let ResolvedExprKind::Block(block) = &resolved.result.kind else {
            panic!("the result should be a block");
        };
        let ResolvedExprKind::Occurrence(occurrence) = &block.result.kind else {
            panic!("the block result should be a resolved occurrence");
        };
        let mut context = TypeContext::new();
        context.insert(
            occurrence.binder,
            Type::Inference(InferenceVariableId::new(0)),
        );
        let mut elaborator =
            Elaborator::for_program(&resolved).expect("the binder namespace should fit");

        assert_eq!(
            elaborator.synthesize(&resolved.result, &context),
            Err(TypeError::Internal(ElaborationFailure::InvalidState))
        );
    }

    #[test]
    fn public_synthesis_charges_a_wide_context_type_before_context_clone() {
        let source = SourceFile::new(
            "external-wide-context.ash",
            "identity : Int -> Int\nidentity value = value\n\nidentity\n",
        )
        .expect("the fixture should fit");
        let tree = parse(lex(&source).expect("the fixture should lex"));
        let surface = project(&source, &tree).expect("the fixture should project");
        let resolved = resolve(&surface).expect("the fixture should resolve");
        let ResolvedExprKind::Occurrence(occurrence) = &resolved.result.kind else {
            panic!("the result should be a resolved occurrence");
        };
        let mut context = TypeContext::new();
        context.insert(
            occurrence.binder,
            Type::Tuple(vec![Type::Int; crate::types::TYPE_WORK_LIMIT].into_boxed_slice()),
        );
        let mut elaborator =
            Elaborator::for_program(&resolved).expect("the binder namespace should fit");
        TYPE_CONTEXT_CLONES.with(|clones| clones.set(0));

        assert_eq!(
            elaborator.synthesize(&resolved.result, &context),
            Err(TypeError::Internal(
                ElaborationFailure::TypeResourceExhausted
            ))
        );
        TYPE_CONTEXT_CLONES.with(|clones| assert_eq!(clones.get(), 0));
    }

    #[test]
    fn public_context_resource_precedes_invalid_type_independent_of_insertion_order() {
        let source =
            SourceFile::new("public-context-order.ash", "42\n").expect("the fixture should fit");
        let tree = parse(lex(&source).expect("the fixture should lex"));
        let surface = project(&source, &tree).expect("the fixture should project");
        let resolved = resolve(&surface).expect("the fixture should resolve");

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
                elaborator.synthesize(&resolved.result, &context),
                Err(TypeError::Internal(
                    ElaborationFailure::TypeResourceExhausted
                ))
            );
            TYPE_CONTEXT_CLONES.with(|clones| assert_eq!(clones.get(), 0));
        }
    }

    #[test]
    fn public_context_resource_precedes_invalid_quantification() {
        let source = SourceFile::new("public-context-quantification.ash", "42\n")
            .expect("the fixture should fit");
        let tree = parse(lex(&source).expect("the fixture should lex"));
        let surface = project(&source, &tree).expect("the fixture should project");
        let resolved = resolve(&surface).expect("the fixture should resolve");
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
            elaborator.synthesize(&resolved.result, &context),
            Err(TypeError::Internal(
                ElaborationFailure::TypeResourceExhausted
            ))
        );
        TYPE_CONTEXT_CLONES.with(|clones| assert_eq!(clones.get(), 0));
    }

    #[test]
    fn public_check_rejects_inference_in_the_expected_type() {
        let source = SourceFile::new("external-expected-inference.ash", "42\n")
            .expect("the fixture should fit");
        let tree = parse(lex(&source).expect("the fixture should lex"));
        let surface = project(&source, &tree).expect("the fixture should project");
        let resolved = resolve(&surface).expect("the fixture should resolve");
        let mut elaborator = Elaborator::new();

        assert_eq!(
            elaborator.check(
                &resolved.result,
                &Type::Inference(InferenceVariableId::new(0)),
                &TypeContext::new(),
            ),
            Err(TypeError::Internal(ElaborationFailure::InvalidState))
        );
    }

    #[test]
    fn public_check_rejects_wide_higher_rank_expected_type_before_clone() {
        let source = SourceFile::new("external-higher-rank.ash", "fn(value) {\n42\n}\n")
            .expect("the fixture should fit");
        let tree = parse(lex(&source).expect("the fixture should lex"));
        let surface = project(&source, &tree).expect("the fixture should project");
        let resolved = resolve(&surface).expect("the fixture should resolve");
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
            elaborator.check(&resolved.result, &expected, &TypeContext::new()),
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
                let source = SourceFile::new("external-deep-type.ash", "42\n")
                    .expect("the fixture should fit");
                let tree = parse(lex(&source).expect("the fixture should lex"));
                let surface = project(&source, &tree).expect("the fixture should project");
                let resolved = resolve(&surface).expect("the fixture should resolve");

                let expected = nested_function_type(DEPTH);
                let mut checking = Elaborator::new();
                let check_result = checking.check(&resolved.result, &expected, &TypeContext::new());
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
                let synthesize_result = synthesizing.synthesize(&resolved.result, &context);
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
        let source = SourceFile::new("mismatched-provenance.ash", "fn(value) {\n    value\n}\n")
            .expect("test source should fit");
        let lexed = lex(&source).expect("test source should lex");
        let tree = parse(lexed);
        let surface = project(&source, &tree).expect("test source should project");
        let program = resolve(&surface).expect("test source should resolve");
        let ResolvedExprKind::Function(function) = &program.result.kind else {
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
        let mut elaborator =
            Elaborator::for_program(&program).expect("binder reservation should fit");

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
        text.push_str("f31 42\n");
        let source = SourceFile::new("sequential-globals.ash", text).expect("source should fit");
        let lexed = lex(&source).expect("test source should lex");
        let tree = parse(lexed);
        let surface = project(&source, &tree).expect("test source should project");
        let program = resolve(&surface).expect("test source should resolve");
        let mut elaborator =
            Elaborator::for_program(&program).expect("binder reservation should fit");
        TYPE_CONTEXT_CLONES.with(|clones| clones.set(0));

        elaborator
            .synthesize_program(&program)
            .expect("recursive globals should elaborate");

        TYPE_CONTEXT_CLONES.with(|clones| assert_eq!(clones.get(), 0));
    }

    #[test]
    fn successful_function_work_restores_parameter_and_block_scopes() {
        let source = SourceFile::new(
            "restored-function-scope.ash",
            "fn(parameter) {\n    let local = parameter\n    local\n}\n",
        )
        .expect("source should fit");
        let lexed = lex(&source).expect("test source should lex");
        let tree = parse(lexed);
        let surface = project(&source, &tree).expect("test source should project");
        let program = resolve(&surface).expect("test source should resolve");
        let mut elaborator =
            Elaborator::for_program(&program).expect("binder reservation should fit");
        let mut context = TypeContext::new();
        let expected =
            ProvenancedType::unknown(Type::Function(Box::new(Type::Int), Box::new(Type::Int)));

        elaborator
            .elaborate_expression_with_context(
                ElaborationTask::Check {
                    expression: &program.result,
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
