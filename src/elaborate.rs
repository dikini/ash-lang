//! Bidirectional typed elaboration from resolved surface syntax to pure Core.

use std::{
    collections::{HashMap, HashSet},
    error::Error,
    fmt,
    sync::Arc,
};

use crate::{
    core::{
        BuildError, CoreBuilder, CoreMatchArm, CorePattern, CorePatternKind, NodeId, Primitive,
        TypedBinder, UnvalidatedProgram,
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
        ResolvedTypeProvenanceNode,
    },
    source::{GeneratedReason, Origin, Span},
    types::{
        InferenceVariableId, Type, TypeVariableId, TypeWorkBudget, charge_type_cells, same_type,
        substitute_type_variables,
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
struct TypeProvenance {
    nodes: Arc<[TypeProvenanceNode]>,
    root: usize,
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
        Self {
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
        Self {
            nodes: nodes.into(),
            root,
        }
    }

    fn span(&self) -> Option<Span> {
        match self.nodes.get(self.root) {
            Some(TypeProvenanceNode::Fact(span) | TypeProvenanceNode::Function { span, .. }) => {
                *span
            }
            None => None,
        }
    }

    fn aligns(&self, ty: &Type) -> bool {
        let mut work = vec![(ty, self.root)];
        while let Some((current, node)) = work.pop() {
            match (current, self.nodes.get(node)) {
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
                    work.push((codomain, *codomain_node));
                    work.push((domain, *domain_node));
                }
                _ => return false,
            }
        }
        true
    }

    fn child(&self, node: usize) -> Result<Self, TypeError> {
        if self.nodes.get(node).is_none() {
            return Err(invalid_state());
        }
        Ok(Self {
            nodes: Arc::clone(&self.nodes),
            root: node,
        })
    }

    fn function_parts(&self, ty: &Type) -> Result<(Self, Self), TypeError> {
        let Type::Function(_, _) = ty else {
            return Err(invalid_state());
        };
        let Some(TypeProvenanceNode::Function {
            domain, codomain, ..
        }) = self.nodes.get(self.root)
        else {
            return Err(invalid_state());
        };
        Ok((self.child(*domain)?, self.child(*codomain)?))
    }
}

impl ProvenancedType {
    fn unknown(ty: Type) -> Self {
        let provenance = TypeProvenance::unknown(&ty);
        Self { ty, provenance }
    }

    fn from_resolved(resolved: &ResolvedType) -> Self {
        let nodes = resolved
            .provenance
            .nodes()
            .iter()
            .map(|node| match node {
                ResolvedTypeProvenanceNode::Fact(span)
                | ResolvedTypeProvenanceNode::Tuple { span, .. }
                | ResolvedTypeProvenanceNode::Application { span, .. } => {
                    TypeProvenanceNode::Fact(Some(*span))
                }
                ResolvedTypeProvenanceNode::Function {
                    span,
                    domain,
                    codomain,
                } => TypeProvenanceNode::Function {
                    span: Some(*span),
                    domain: *domain,
                    codomain: *codomain,
                },
            })
            .collect::<Vec<_>>()
            .into();
        Self {
            ty: resolved.ty.clone(),
            provenance: TypeProvenance {
                nodes,
                root: resolved.provenance.root(),
            },
        }
    }

    fn function(domain: Self, codomain: Self, span: Option<Span>) -> Result<Self, TypeError> {
        if !domain.provenance.aligns(&domain.ty) || !codomain.provenance.aligns(&codomain.ty) {
            return Err(invalid_state());
        }
        let mut nodes =
            Vec::with_capacity(domain.provenance.nodes.len() + codomain.provenance.nodes.len() + 1);
        nodes.extend(domain.provenance.nodes.iter().copied());
        let domain_root = domain.provenance.root;
        let offset = nodes.len();
        nodes.extend(
            codomain
                .provenance
                .nodes
                .iter()
                .copied()
                .map(|node| match node {
                    TypeProvenanceNode::Fact(span) => TypeProvenanceNode::Fact(span),
                    TypeProvenanceNode::Function {
                        span,
                        domain,
                        codomain,
                    } => TypeProvenanceNode::Function {
                        span,
                        domain: domain + offset,
                        codomain: codomain + offset,
                    },
                }),
        );
        let codomain_root = codomain.provenance.root + offset;
        nodes.push(TypeProvenanceNode::Function {
            span,
            domain: domain_root,
            codomain: codomain_root,
        });
        let root = nodes.len() - 1;
        Ok(Self {
            ty: Type::Function(Box::new(domain.ty), Box::new(codomain.ty)),
            provenance: TypeProvenance {
                nodes: nodes.into(),
                root,
            },
        })
    }

    fn function_parts(&self) -> Result<(Self, Self), TypeError> {
        let Type::Function(domain, codomain) = &self.ty else {
            return Err(invalid_state());
        };
        let (domain_provenance, codomain_provenance) = self.provenance.function_parts(&self.ty)?;
        Ok((
            Self {
                ty: domain.as_ref().clone(),
                provenance: domain_provenance,
            },
            Self {
                ty: codomain.as_ref().clone(),
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
    /// integer, or a structured internal failure when Core construction fails.
    /// The failing call preserves that original error and poisons this
    /// elaborator; later synthesis, checking, and completion return an internal
    /// invalid-state error so partially emitted Core cannot escape.
    pub fn synthesize(
        &mut self,
        expression: &ResolvedExpr,
        context: &TypeContext,
    ) -> Result<TypedNode, TypeError> {
        if self.state == ElaboratorState::Poisoned {
            return Err(invalid_state());
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
    /// Returns the synthesis failure, or [`TypeError::Mismatch`] when the
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
        let mut context = context.clone();
        let result = self.elaborate_expression_with_context(
            ElaborationTask::Check {
                expression,
                expected: ProvenancedType::unknown(expected.clone()),
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
        let solutions = &self.inference_solutions;
        let type_work = &mut self.type_work;
        self.builder.rewrite_types(|ty| {
            charge_type_cells(ty, type_work).map_err(|()| BuildError::TypeWorkExceeded)?;
            let zonked = zonk_type(ty, solutions);
            if contains_unsolved_inference(&zonked) {
                Err(BuildError::InvalidPayload)
            } else {
                Ok(zonked)
            }
        })?;
        self.builder.finish(root).map_err(Into::into)
    }

    fn fresh_inference(&mut self) -> Result<Type, TypeError> {
        let identity = InferenceVariableId::new(self.next_inference);
        self.next_inference = self
            .next_inference
            .checked_add(1)
            .ok_or_else(invalid_state)?;
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
    ) -> Result<(Type, Vec<Type>), TypeError> {
        self.charge_type(&fact.ty)?;
        if fact.quantified.is_empty() {
            return Ok((fact.ty.clone(), Vec::new()));
        }
        let mut replacements = HashMap::with_capacity(fact.quantified.len());
        let mut arguments = Vec::with_capacity(fact.quantified.len());
        for binder in &fact.quantified {
            let argument = if rigid {
                Type::Variable(*binder)
            } else {
                self.fresh_inference()?
            };
            replacements.insert(*binder, argument.clone());
            arguments.push(argument);
        }
        Ok((
            substitute_type_variables(&fact.ty, &replacements),
            arguments,
        ))
    }

    fn zonk(&mut self, ty: &Type) -> Result<Type, TypeError> {
        self.charge_type(ty)?;
        Ok(zonk_type(ty, &self.inference_solutions))
    }

    fn charge_type(&mut self, ty: &Type) -> Result<(), TypeError> {
        charge_type_cells(ty, &mut self.type_work)
            .map_err(|()| TypeError::Internal(ElaborationFailure::TypeResourceExhausted))
    }

    fn unify(&mut self, left: &Type, right: &Type) -> Result<(), UnificationFailure> {
        let mut work = vec![(left.clone(), right.clone())];
        while let Some((left, right)) = work.pop() {
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
                    self.inference_solutions.insert(variable, ty);
                }
                (Type::Int, Type::Int) | (Type::Bool, Type::Bool) | (Type::Unit, Type::Unit) => {}
                (Type::Nominal(left), Type::Nominal(right)) if left == right => {}
                (Type::Variable(left), Type::Variable(right)) if left == right => {}
                (Type::AppliedNominal(left_id, left), Type::AppliedNominal(right_id, right))
                    if left_id == right_id && left.len() == right.len() =>
                {
                    work.extend(left.into_vec().into_iter().zip(right.into_vec()));
                }
                (Type::Tuple(left), Type::Tuple(right)) if left.len() == right.len() => {
                    work.extend(left.into_vec().into_iter().zip(right.into_vec()));
                }
                (
                    Type::Function(left_domain, left_codomain),
                    Type::Function(right_domain, right_codomain),
                ) => {
                    work.push((*left_codomain, *right_codomain));
                    work.push((*left_domain, *right_domain));
                }
                _ => return Err(UnificationFailure::Mismatch),
            }
        }
        Ok(())
    }

    fn elaborate_program(&mut self, program: &ResolvedProgram) -> Result<TypedNode, TypeError> {
        let mut context = TypeContext::new();
        let mut globals = Vec::with_capacity(program.definitions.len());
        let mut global_binders = HashMap::with_capacity(program.definitions.len());
        let mut global_quantifiers = Vec::with_capacity(program.definitions.len());

        for definition in &program.definitions {
            let (name, function_type, type_parameters) = match &definition.kind {
                ResolvedDefinitionKind::Equational(equational) => {
                    let function_type =
                        ProvenancedType::from_resolved(&equational.interface.annotation);
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
                    )?;
                    let codomain = ProvenancedType::from_resolved(&operational.header.result_type);
                    (
                        &operational.header.name,
                        ProvenancedType::function(domain, codomain, Some(operational.header.span))?,
                        operational.header.type_parameters.as_ref(),
                    )
                }
            };
            let quantified = type_parameters
                .iter()
                .map(|parameter| parameter.id)
                .collect::<Vec<_>>()
                .into_boxed_slice();
            let binder_type = if quantified.is_empty() {
                function_type.ty.clone()
            } else {
                Type::Forall(quantified.clone(), Box::new(function_type.ty.clone()))
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
            context.set_quantified(name.id, quantified.clone())?;
            global_quantifiers.push((name.id, quantified));
            self.monomorphic_recursive.insert(name.id);
        }

        for definition in &program.definitions {
            let (name, mut function) = match &definition.kind {
                ResolvedDefinitionKind::Equational(equational) => {
                    let function_type =
                        ProvenancedType::from_resolved(&equational.interface.annotation);
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
                    let function_type = ProvenancedType::function(
                        operational_domain(
                            &operational.header.parameters,
                            operational.header.span,
                        )?,
                        ProvenancedType::from_resolved(&operational.header.result_type),
                        Some(operational.header.span),
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
            if !function.provenance.aligns(&function.ty) {
                return Err(invalid_state());
            }
            let binder = global_binders.remove(&name.id).ok_or_else(invalid_state)?;
            let quantified = global_quantifiers
                .iter()
                .find_map(|(binder, quantified)| (*binder == name.id).then_some(quantified))
                .ok_or_else(invalid_state)?;
            if !quantified.is_empty() {
                let scheme = Type::Forall(quantified.clone(), Box::new(function.ty.clone()));
                function.node = self.builder.type_abstraction(
                    quantified.to_vec(),
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
        if contains_unsolved_inference(&self.zonk(&result.ty)?) {
            return Err(inference_failure(
                TypeReason::AmbiguousType,
                program.result.span,
                "this result does not determine every inferred type",
            ));
        }
        if !globals.is_empty() {
            let members = globals
                .into_iter()
                .map(|global| (global.binder, global.initializer))
                .collect();
            let node = self.builder.recursive_binding(
                members,
                result.node,
                result.ty.clone(),
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
                        let fact = context
                            .fact(occurrence.binder)
                            .cloned()
                            .ok_or_else(invalid_state)?;
                        let rigid = self.monomorphic_recursive.contains(&occurrence.binder);
                        let (ty, arguments) = self.instantiate(&fact, rigid)?;
                        let provenance = fact.provenance.clone();
                        let scheme = if fact.quantified.is_empty() {
                            fact.ty.clone()
                        } else {
                            Type::Forall(fact.quantified.clone(), Box::new(fact.ty.clone()))
                        };
                        let mut node = self.builder.variable(
                            occurrence.binder,
                            scheme,
                            occurrence.origin.clone(),
                        )?;
                        if !arguments.is_empty() {
                            node = self.builder.type_application(
                                node,
                                arguments,
                                ty.clone(),
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
                        let result = if parameters.is_empty() {
                            Type::Nominal(constructor.owner)
                        } else {
                            Type::AppliedNominal(
                                constructor.owner,
                                parameters
                                    .iter()
                                    .map(|parameter| Type::Variable(parameter.id))
                                    .collect::<Vec<_>>()
                                    .into_boxed_slice(),
                            )
                        };
                        let scheme = constructor
                            .payload
                            .as_ref()
                            .map_or(result.clone(), |payload| {
                                Type::Function(Box::new(payload.clone()), Box::new(result))
                            });
                        let fact = TypeFact {
                            ty: scheme,
                            provenance: TypeProvenance::atom(None),
                            quantified: parameters
                                .iter()
                                .map(|parameter| parameter.id)
                                .collect::<Vec<_>>()
                                .into_boxed_slice(),
                        };
                        let (ty, arguments) = self.instantiate(&fact, false)?;
                        let core_scheme = if fact.quantified.is_empty() {
                            fact.ty.clone()
                        } else {
                            Type::Forall(fact.quantified.clone(), Box::new(fact.ty.clone()))
                        };
                        let mut node = self.builder.constructor(
                            occurrence.constructor,
                            core_scheme,
                            occurrence.origin.clone(),
                        )?;
                        if !arguments.is_empty() {
                            node = self.builder.type_application(
                                node,
                                arguments,
                                ty.clone(),
                                occurrence.origin.clone(),
                            )?;
                        }
                        values.push(TypedNode {
                            node,
                            provenance: TypeProvenance::unknown(&ty),
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
                        schedule_block(block, None, cause, &mut tasks, declarations.len())?;
                    }
                    ResolvedExprKind::Function(_) => {
                        if !matches!(cause, Some(SynthesisCause::Binding(_))) {
                            return Err(function_needs_context(current.span, cause));
                        }
                        let domain = self.fresh_inference()?;
                        let codomain = self.fresh_inference()?;
                        let expected = ProvenancedType::unknown(Type::Function(
                            Box::new(domain),
                            Box::new(codomain),
                        ));
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
                        if !matches!(expected.ty, Type::Function(_, _)) {
                            return Err(function_needs_context(expression.span, None));
                        }
                        let (domain, codomain) = expected.function_parts()?;
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
                    let expected_ty = expected.ty.clone();
                    let found_ty = synthesized.ty.clone();
                    match self.unify(&found_ty, &expected_ty) {
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
                                self.zonk(&expected_ty)?,
                                self.zonk(&found_ty)?,
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
                    self.builder
                        .record_type_check(synthesized.node, expected.provenance.span())?;
                    values.push(TypedNode {
                        ty: self.zonk(&synthesized.ty)?,
                        ..synthesized
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
                    pattern_binders,
                    binder,
                    pattern,
                    domain,
                    ty,
                    origin,
                    provenance,
                } => {
                    let mut body = values.pop().ok_or_else(invalid_state)?;
                    self.remove_pattern_binders(context, &pattern_binders)?;
                    if let Some(pattern) = pattern {
                        let matrix = vec![vec![pattern.clone()]];
                        if let Some(witness) = missing_witness_for_types(
                            &matrix,
                            std::slice::from_ref(&domain),
                            &self.registry,
                        )? {
                            return Err(case_error(
                                TypeReason::RefutableFunctionDomain,
                                pattern.origin.primary_span(),
                                "this function pattern is not exhaustive",
                                Some(display_witness(&witness, &self.registry)),
                            ));
                        }
                        let scrutinee =
                            self.builder
                                .variable(binder.id(), domain, pattern.origin.clone())?;
                        let match_node = self.builder.match_expression(
                            scrutinee,
                            vec![CoreMatchArm::new(
                                pattern.clone(),
                                body.node,
                                pattern.origin.clone(),
                            )],
                            body.ty.clone(),
                            pattern.origin.clone(),
                        )?;
                        body.node = match_node;
                    }
                    let node = self
                        .builder
                        .function(binder, body.node, ty.clone(), origin)?;
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
                    let mut function_ty = self.zonk(&function.ty)?;
                    if matches!(function_ty, Type::Inference(_)) {
                        let domain = self.fresh_inference()?;
                        let codomain = self.fresh_inference()?;
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
                    let Type::Function(domain, codomain) = function_ty.clone() else {
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
                        TypeProvenance::unknown(&function_ty)
                    };
                    let (domain_provenance, codomain_provenance) =
                        provenance.function_parts(&function_ty)?;
                    function.ty = function_ty;
                    let domain = ProvenancedType {
                        ty: domain.as_ref().clone(),
                        provenance: domain_provenance,
                    };
                    let codomain = ProvenancedType {
                        ty: codomain.as_ref().clone(),
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
                    let origin = Origin::Related {
                        primary: Box::new(Origin::Source(whole_span)),
                        related: vec![function_span, argument_span],
                    };
                    let node = self.builder.application(
                        function.node,
                        argument.node,
                        codomain.ty.clone(),
                        origin,
                    )?;
                    let ty = self.zonk(&codomain.ty)?;
                    let provenance = if codomain.provenance.aligns(&ty) {
                        codomain.provenance
                    } else {
                        TypeProvenance::unknown(&ty)
                    };
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
                    require_integer(&left, left_span, operator_span, &self.registry)?;
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
                    require_integer(&right, right_span, operator_span, &self.registry)?;
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
                        && matches!(binding.initializer.kind, ResolvedExprKind::Function(_))
                    {
                        let inferred = self.zonk(&initializer.ty)?;
                        self.charge_type(&inferred)?;
                        let mut variables = Vec::new();
                        collect_unsolved_inference(&inferred, &mut variables);
                        let environment_types = context
                            .binders
                            .values()
                            .map(|fact| fact.ty.clone())
                            .collect::<Vec<_>>();
                        let mut environment_variables = Vec::new();
                        for ty in environment_types {
                            let ty = self.zonk(&ty)?;
                            self.charge_type(&ty)?;
                            collect_unsolved_inference(&ty, &mut environment_variables);
                        }
                        variables.retain(|variable| !environment_variables.contains(variable));
                        for variable in variables {
                            let binder = self.fresh_type_variable()?;
                            self.inference_solutions
                                .insert(variable, Type::Variable(binder));
                            generalized.push(binder);
                        }
                        initializer.ty = self.zonk(&initializer.ty)?;
                    }
                    let binding_type = expected.unwrap_or_else(|| ProvenancedType {
                        ty: initializer.ty.clone(),
                        provenance: initializer.provenance.clone(),
                    });
                    let mut binder_ids = Vec::new();
                    let mut pattern = self.check_core_pattern(
                        &binding.pattern,
                        &binding_type.ty,
                        context,
                        &mut binder_ids,
                        GeneratedReason::BindingLowering,
                    )?;
                    let matrix = vec![vec![pattern.clone()]];
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
                    let origin = binding_origin(binding);
                    match &mut pattern.kind {
                        CorePatternKind::Binder(binder) => {
                            let quantified = generalized.into_boxed_slice();
                            context.set_quantified(binder.id(), quantified.clone())?;
                            if !quantified.is_empty() {
                                let scheme = Type::Forall(
                                    quantified.clone(),
                                    Box::new(binding_type.ty.clone()),
                                );
                                binder.replace_type(scheme.clone());
                                initializer.node = self.builder.type_abstraction(
                                    quantified.to_vec(),
                                    initializer.node,
                                    scheme,
                                    Origin::Generated {
                                        cause: Box::new(origin.clone()),
                                        reason: GeneratedReason::TypeChecking,
                                    },
                                )?;
                            }
                            declarations.push(ElaboratedDeclaration::Binding {
                                binder: binder.clone(),
                                initializer: initializer.node,
                                origin,
                            });
                        }
                        _ => declarations.push(ElaboratedDeclaration::PatternBinding {
                            pattern,
                            initializer: initializer.node,
                            origin,
                        }),
                    }
                }
                ElaborationTask::BeginRecursiveGroup(group) => {
                    for member in &group.members {
                        validate_recursive_member(group, member, &self.registry)?;
                    }
                    let expected_types = group
                        .members
                        .iter()
                        .map(|member| ProvenancedType::from_resolved(&member.annotation))
                        .collect::<Vec<_>>();
                    let mut members = Vec::with_capacity(group.members.len());
                    for (member, expected) in group.members.iter().zip(&expected_types) {
                        let binder = self.builder.resolved_binder(
                            member.binder.id,
                            expected.ty.clone(),
                            Origin::Generated {
                                cause: Box::new(member.binder.origin.clone()),
                                reason: GeneratedReason::BindingLowering,
                            },
                        )?;
                        if context
                            .insert_with_provenance(
                                member.binder.id,
                                expected.ty.clone(),
                                expected.provenance.clone(),
                            )?
                            .is_some()
                        {
                            return Err(invalid_state());
                        }
                        members.push(ElaboratedRecursiveMemberSeed { binder });
                    }
                    tasks.push(ElaborationTask::FinishRecursiveGroup { group, members });
                    for (member, expected) in group.members.iter().zip(expected_types).rev() {
                        tasks.push(ElaborationTask::Check {
                            expression: &member.initializer,
                            expected,
                            kind: CheckKind::BindingInitializer {
                                initializer_span: member.initializer.span,
                                annotation_span: member.annotation.span,
                            },
                        });
                    }
                }
                ElaborationTask::FinishRecursiveGroup { group, members } => {
                    if members.len() != group.members.len() || values.len() < members.len() {
                        return Err(invalid_state());
                    }
                    let value_start = values.len() - members.len();
                    let initializers = values.split_off(value_start);
                    let members = members
                        .into_iter()
                        .zip(initializers)
                        .map(|(member, initializer)| (member.binder, initializer.node))
                        .collect();
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
                    let progress = Box::new(MatchProgress {
                        expression,
                        span,
                        scrutinee,
                        next_arm: 0,
                        matrix: Vec::new(),
                        coverage_budget: UsefulnessBudget::default(),
                        arms: Vec::with_capacity(expression.arms.len()),
                        result_type: expected
                            .map(|(expected, kind)| (expected.ty, expected.provenance, kind)),
                    });
                    self.schedule_match_arm(progress, context, &mut tasks)?;
                }
                ElaborationTask::FinishMatchArm {
                    mut progress,
                    binders,
                    pattern,
                    row,
                    arm_span,
                } => {
                    let body_result = values.pop().ok_or_else(invalid_state);
                    self.remove_pattern_binders(context, &binders)?;
                    let body = body_result?;
                    progress.result_type.get_or_insert_with(|| {
                        (body.ty.clone(), body.provenance.clone(), CheckKind::General)
                    });
                    progress.matrix.push(row);
                    progress.arms.push(CoreMatchArm::new(
                        pattern,
                        body.node,
                        Origin::Source(arm_span),
                    ));
                    self.schedule_match_arm(progress, context, &mut tasks)?;
                }
                ElaborationTask::FinishMatch(progress) => {
                    let Some((ty, provenance, _)) = progress.result_type else {
                        return Err(invalid_state());
                    };
                    let node = self.builder.match_expression(
                        progress.scrutinee.node,
                        progress.arms,
                        ty.clone(),
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
                        let node = match declaration {
                            ElaboratedDeclaration::Binding {
                                binder,
                                initializer,
                                origin,
                            } => self.builder.binding(
                                binder,
                                initializer,
                                body.node,
                                body.ty.clone(),
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
                                body.ty.clone(),
                                origin,
                            )?,
                            ElaboratedDeclaration::Recursive { members, origin } => self
                                .builder
                                .recursive_binding(members, body.node, body.ty.clone(), origin)?,
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
        let node = self
            .builder
            .tuple(nodes, ty.clone(), Origin::Source(span))?;
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

        let mut binders = Vec::new();
        let pattern = self.check_core_pattern(
            &arm.pattern,
            &progress.scrutinee.ty,
            context,
            &mut binders,
            GeneratedReason::BindingLowering,
        )?;
        let row = vec![pattern.clone()];
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
            ElaborationTask::Check {
                expression: &arm.body,
                expected: ProvenancedType {
                    ty: ty.clone(),
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
            pattern,
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
    ) -> Result<CorePattern, TypeError> {
        let kind = match &pattern.kind {
            ResolvedPatternKind::Binder(binder) => {
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
                        TypeProvenance::unknown(expected),
                    )?
                    .is_some()
                {
                    return Err(invalid_state());
                }
                binders.push(binder.id);
                CorePatternKind::Binder(typed)
            }
            ResolvedPatternKind::Wildcard => CorePatternKind::Wildcard,
            ResolvedPatternKind::Boolean(value) if matches!(expected, Type::Bool) => {
                CorePatternKind::Boolean(*value)
            }
            ResolvedPatternKind::Unit if matches!(expected, Type::Unit) => CorePatternKind::Unit,
            ResolvedPatternKind::Tuple(patterns) => {
                let Type::Tuple(types) = expected else {
                    return Err(pattern_mismatch(pattern.span, expected, &self.registry));
                };
                if patterns.len() != types.len() {
                    return Err(pattern_mismatch(pattern.span, expected, &self.registry));
                }
                let mut checked = Vec::with_capacity(patterns.len());
                for (pattern, ty) in patterns.iter().zip(types) {
                    checked.push(self.check_core_pattern(
                        pattern,
                        ty,
                        context,
                        binders,
                        binder_reason,
                    )?);
                }
                CorePatternKind::Tuple(checked.into_boxed_slice())
            }
            ResolvedPatternKind::Constructor {
                constructor,
                payload,
                ..
            } => {
                let (owner, arguments): (_, &[Type]) = match expected {
                    Type::Nominal(owner) => (*owner, &[]),
                    Type::AppliedNominal(owner, arguments) => (*owner, arguments),
                    _ => return Err(pattern_mismatch(pattern.span, expected, &self.registry)),
                };
                let Some(info) = self.registry.constructor(*constructor) else {
                    return Err(invalid_state());
                };
                let info_owner = info.owner;
                let declared_payload = info.payload.clone();
                let parameters = self
                    .registry
                    .nominal_parameters(owner)
                    .ok_or_else(invalid_state)?;
                if parameters.len() != arguments.len() {
                    return Err(invalid_state());
                }
                let replacements = parameters
                    .iter()
                    .zip(arguments)
                    .map(|(parameter, argument)| (parameter.id, argument.clone()))
                    .collect::<HashMap<_, _>>();
                let payload_type = declared_payload
                    .as_ref()
                    .map(|payload| {
                        self.charge_type(payload)?;
                        Ok::<Type, TypeError>(substitute_type_variables(payload, &replacements))
                    })
                    .transpose()?;
                if info_owner != owner {
                    return Err(case_error(
                        TypeReason::ConstructorOwner,
                        pattern.span,
                        "this constructor belongs to another nominal type",
                        None,
                    ));
                }
                let checked_payload = match (payload.as_deref(), payload_type.as_ref()) {
                    (None, None) => None,
                    (Some(pattern), Some(ty)) => Some(Box::new(self.check_core_pattern(
                        pattern,
                        ty,
                        context,
                        binders,
                        binder_reason,
                    )?)),
                    _ => return Err(constructor_mismatch(pattern.span)),
                };
                CorePatternKind::Constructor {
                    constructor: *constructor,
                    payload: checked_payload,
                }
            }
            _ => return Err(pattern_mismatch(pattern.span, expected, &self.registry)),
        };
        Ok(CorePattern::new(
            expected.clone(),
            Origin::Source(pattern.span),
            kind,
        ))
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
            domain,
            codomain,
            body,
            presentation,
            function_type,
            body_check,
        } = check;
        let mut pattern_binders = Vec::new();
        let pattern = self.check_core_pattern(
            parameter,
            &domain.ty,
            context,
            &mut pattern_binders,
            GeneratedReason::FunctionLowering,
        )?;
        let (parameter_binder, retained_pattern) = match &pattern.kind {
            CorePatternKind::Binder(binder) => (binder.clone(), None),
            _ => (
                self.builder.binder(
                    domain.ty.clone(),
                    Origin::Generated {
                        cause: Box::new(Origin::Source(parameter.span)),
                        reason: GeneratedReason::FunctionLowering,
                    },
                )?,
                Some(pattern),
            ),
        };
        if !structurally_equal(
            &function_type.ty,
            &Type::Function(Box::new(domain.ty.clone()), Box::new(codomain.ty.clone())),
        ) || !function_type.provenance.aligns(&function_type.ty)
        {
            return Err(invalid_state());
        }
        let origin = Origin::Generated {
            cause: Box::new(presentation),
            reason: GeneratedReason::FunctionLowering,
        };
        tasks.push(ElaborationTask::FinishFunction {
            pattern_binders,
            binder: parameter_binder,
            pattern: retained_pattern,
            domain: domain.ty,
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
        let mut remainder = function_type.clone();
        let mut domains = Vec::with_capacity(arity);
        for _ in 0..arity {
            if !matches!(remainder.ty, Type::Function(_, _)) {
                return Err(case_error(
                    TypeReason::EquationArity,
                    definition_span,
                    "the equation has more patterns than the declared arrows",
                    None,
                ));
            }
            let (domain, codomain) = remainder.function_parts()?;
            domains.push(domain);
            remainder = codomain;
        }

        let mut parameters = Vec::with_capacity(arity);
        for domain in &domains {
            parameters.push(self.builder.binder(
                domain.ty.clone(),
                Origin::Generated {
                    cause: Box::new(equational_origin(definition_span, equational)),
                    reason: GeneratedReason::FunctionLowering,
                },
            )?);
        }

        let mut coverage_matrix = Vec::new();
        let mut coverage_budget = UsefulnessBudget::default();
        let mut arms = Vec::with_capacity(equational.equations.len());
        for clause in &equational.equations {
            let mut binder_ids = Vec::new();
            let mut patterns = Vec::with_capacity(arity);
            for (pattern, domain) in clause.patterns.iter().zip(&domains) {
                patterns.push(self.check_core_pattern(
                    pattern,
                    &domain.ty,
                    context,
                    &mut binder_ids,
                    GeneratedReason::FunctionLowering,
                )?);
            }
            if usefulness_with_budget(
                &coverage_matrix,
                &patterns,
                &domains
                    .iter()
                    .map(|domain| domain.ty.clone())
                    .collect::<Vec<_>>(),
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
            let body_result = self.elaborate_expression_with_context(
                ElaborationTask::Check {
                    expression: &clause.body,
                    expected: remainder.clone(),
                    kind: CheckKind::Definition {
                        result_cause: remainder.provenance.span().unwrap_or(definition_span),
                    },
                },
                context,
            );
            self.remove_pattern_binders(context, &binder_ids)?;
            let body = body_result?;
            let arm_pattern = if patterns.len() == 1 {
                patterns[0].clone()
            } else {
                CorePattern::new(
                    Type::Tuple(
                        domains
                            .iter()
                            .map(|domain| domain.ty.clone())
                            .collect::<Vec<_>>()
                            .into_boxed_slice(),
                    ),
                    Origin::Source(clause.span),
                    CorePatternKind::Tuple(patterns.clone().into_boxed_slice()),
                )
            };
            coverage_matrix.push(patterns);
            arms.push(CoreMatchArm::new(
                arm_pattern,
                body.node,
                Origin::Source(clause.span),
            ));
        }
        let domain_types = domains
            .iter()
            .map(|domain| domain.ty.clone())
            .collect::<Vec<_>>();
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

        let direct_binder = if arity == 1 && arms.len() == 1 {
            match &arms[0].pattern().kind {
                CorePatternKind::Binder(binder) => Some(binder.clone()),
                _ => None,
            }
        } else {
            None
        };
        let mut body_node = if let Some(parameter) = direct_binder.clone() {
            parameters[0] = parameter;
            arms[0].body()
        } else {
            let mut arguments = Vec::with_capacity(parameters.len());
            for (parameter, domain) in parameters.iter().zip(&domains) {
                arguments.push(self.builder.variable(
                    parameter.id(),
                    domain.ty.clone(),
                    Origin::Source(definition_span),
                )?);
            }
            let scrutinee = if arguments.len() == 1 {
                arguments[0]
            } else {
                let ty = Type::Tuple(domain_types.clone().into_boxed_slice());
                self.builder
                    .tuple(arguments, ty, Origin::Source(definition_span))?
            };
            self.builder.match_expression(
                scrutinee,
                arms,
                remainder.ty.clone(),
                Origin::Source(definition_span),
            )?
        };
        let mut body_type = remainder.ty.clone();
        for (parameter, domain) in parameters.iter().zip(&domains).rev() {
            let ty = Type::Function(Box::new(domain.ty.clone()), Box::new(body_type));
            body_node = self.builder.function(
                parameter.clone(),
                body_node,
                ty.clone(),
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
        let (domain, codomain) = function_type.function_parts()?;
        let mut binder_ids = Vec::new();
        let pattern = if operational.header.parameters.len() == 1 {
            self.check_core_pattern(
                &operational.header.parameters[0].pattern,
                &domain.ty,
                context,
                &mut binder_ids,
                GeneratedReason::FunctionLowering,
            )?
        } else {
            let Type::Tuple(types) = &domain.ty else {
                return Err(invalid_state());
            };
            if types.len() != operational.header.parameters.len() {
                return Err(invalid_state());
            }
            let mut elements = Vec::with_capacity(types.len());
            for (parameter, ty) in operational.header.parameters.iter().zip(types) {
                elements.push(self.check_core_pattern(
                    &parameter.pattern,
                    ty,
                    context,
                    &mut binder_ids,
                    GeneratedReason::FunctionLowering,
                )?);
            }
            CorePattern::new(
                domain.ty.clone(),
                Origin::Source(operational.header.span),
                CorePatternKind::Tuple(elements.into_boxed_slice()),
            )
        };
        let (parameter, retained_pattern) = match &pattern.kind {
            CorePatternKind::Binder(binder) => (binder.clone(), None),
            _ => (
                self.builder
                    .binder(domain.ty.clone(), Origin::Source(operational.header.span))?,
                Some(pattern),
            ),
        };
        let body_expression = ResolvedExpr {
            kind: ResolvedExprKind::Block(operational.body.clone()),
            span: operational.body.span,
        };
        let body_result = self.elaborate_expression_with_context(
            ElaborationTask::Check {
                expression: &body_expression,
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
            let matrix = vec![vec![pattern.clone()]];
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
            let scrutinee = self.builder.variable(
                parameter.id(),
                domain.ty.clone(),
                Origin::Source(operational.header.span),
            )?;
            body.node = self.builder.match_expression(
                scrutinee,
                vec![CoreMatchArm::new(
                    pattern,
                    body.node,
                    Origin::Source(operational.header.span),
                )],
                body.ty.clone(),
                Origin::Source(operational.header.span),
            )?;
        }
        let node = self.builder.function(
            parameter,
            body.node,
            function_type.ty.clone(),
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
        pattern_binders: Vec<BinderId>,
        binder: TypedBinder,
        pattern: Option<CorePattern>,
        domain: Type,
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
        pattern: CorePattern,
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
    BeginRecursiveGroup(&'a ResolvedRecursiveGroup),
    FinishRecursiveGroup {
        group: &'a ResolvedRecursiveGroup,
        members: Vec<ElaboratedRecursiveMemberSeed>,
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
    arms: Vec<CoreMatchArm>,
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

struct ElaboratedBinding {
    binder: TypedBinder,
    initializer: NodeId,
}

struct ElaboratedRecursiveMemberSeed {
    binder: TypedBinder,
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
) -> Result<ProvenancedType, TypeError> {
    match parameters {
        [] => Err(invalid_state()),
        [parameter] => Ok(ProvenancedType::from_resolved(&parameter.annotation)),
        parameters => {
            let ty = Type::Tuple(
                parameters
                    .iter()
                    .map(|parameter| parameter.annotation.ty.clone())
                    .collect::<Vec<_>>()
                    .into_boxed_slice(),
            );
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
                    .map(ProvenancedType::from_resolved);
                tasks.push(ElaborationTask::FinishBinding {
                    binding,
                    expected: expected.clone(),
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
            expected_display: registry.display_type(&expected),
            found_display: registry.display_type(&found),
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
                diagnostic.expected = Some(registry.display_type(&expected));
                diagnostic.found = Some(registry.display_type(&found));
                return TypeError::Source(Box::new(diagnostic));
            }
            let expected = registry.display_type(&expected);
            let found = registry.display_type(&found);
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
            let expected = registry.display_type(&expected);
            let found = registry.display_type(&found);
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
            let expected = registry.display_type(&expected);
            let found = registry.display_type(&found);
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
    diagnostic.found = Some(registry.display_type(found));
    TypeError::Source(Box::new(diagnostic))
}

fn equation_interface_not_function(
    annotation: &ResolvedType,
    equation_name: &crate::resolved::ResolvedOccurrence,
    registry: &ResolvedRegistry,
) -> TypeError {
    let found = registry.display_type(&annotation.ty);
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

fn require_integer(
    operand: &TypedNode,
    operand_span: Span,
    operator_span: Span,
    registry: &ResolvedRegistry,
) -> Result<(), TypeError> {
    if structurally_equal(&operand.ty, &Type::Int) {
        return Ok(());
    }
    let mut diagnostic = Diagnostic::new(
        TypeReason::OperatorOperand,
        SourceLabel::new(operand_span, "this operand is not an Int"),
    );
    diagnostic.related.push(SourceLabel::new(
        operator_span,
        "this primitive operator requires Int operands",
    ));
    diagnostic.expected = Some(Type::Int.to_string());
    diagnostic.found = Some(registry.display_type(&operand.ty));
    Err(TypeError::Source(Box::new(diagnostic)))
}

fn invalid_state() -> TypeError {
    TypeError::Internal(ElaborationFailure::InvalidState)
}

fn pattern_mismatch(span: Span, expected: &Type, registry: &ResolvedRegistry) -> TypeError {
    let mut diagnostic = Diagnostic::new(
        TypeReason::PatternMismatch,
        SourceLabel::new(span, "this pattern does not match its expected type"),
    );
    diagnostic.expected = Some(registry.display_type(expected));
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
enum UnificationFailure {
    Mismatch,
    Infinite,
    Resource,
}

fn zonk_type(ty: &Type, solutions: &HashMap<InferenceVariableId, Type>) -> Type {
    enum Task<'a> {
        Visit(&'a Type),
        FinishTuple(usize),
        FinishApplied(crate::types::NominalTypeId, usize),
        FinishFunction,
        FinishForall(Box<[TypeVariableId]>),
    }

    let mut work = vec![Task::Visit(ty)];
    let mut rebuilt = Vec::new();
    while let Some(task) = work.pop() {
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
                work.extend(elements.iter().rev().map(Task::Visit));
            }
            Task::Visit(Type::AppliedNominal(owner, arguments)) => {
                work.push(Task::FinishApplied(*owner, arguments.len()));
                work.extend(arguments.iter().rev().map(Task::Visit));
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
    let mut work = vec![ty];
    let mut visited = HashSet::new();
    while let Some(ty) = work.pop() {
        match ty {
            Type::Inference(identity) if *identity == needle => return true,
            Type::Inference(identity) if visited.insert(*identity) => {
                if let Some(solution) = solutions.get(identity) {
                    work.push(solution);
                }
            }
            Type::Tuple(elements) | Type::AppliedNominal(_, elements) => {
                work.extend(elements.iter());
            }
            Type::Function(domain, codomain) => {
                work.push(codomain);
                work.push(domain);
            }
            Type::Forall(_, body) => work.push(body),
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

fn collect_unsolved_inference(ty: &Type, output: &mut Vec<InferenceVariableId>) {
    let mut work = vec![ty];
    while let Some(ty) = work.pop() {
        match ty {
            Type::Inference(identity) if !output.contains(identity) => output.push(*identity),
            Type::Tuple(elements) | Type::AppliedNominal(_, elements) => {
                work.extend(elements.iter().rev());
            }
            Type::Function(domain, codomain) => {
                work.push(codomain);
                work.push(domain);
            }
            Type::Forall(_, body) => work.push(body),
            Type::Int
            | Type::Bool
            | Type::Unit
            | Type::Nominal(_)
            | Type::Variable(_)
            | Type::Inference(_) => {}
        }
    }
}

fn contains_unsolved_inference(ty: &Type) -> bool {
    let mut variables = Vec::new();
    collect_unsolved_inference(ty, &mut variables);
    !variables.is_empty()
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
        source::SourceFile,
    };

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
                        .function_parts()
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
