//! Bidirectional typed elaboration from resolved surface syntax to pure Core.

use std::{collections::HashMap, error::Error, fmt, sync::Arc};

use crate::{
    core::{BuildError, CoreBuilder, NodeId, Primitive, TypedBinder, UnvalidatedProgram},
    diagnostic::{Diagnostic, SourceLabel},
    resolved::{
        Binder, BinderId, ResolvedBinding, ResolvedBlock, ResolvedDefinitionKind, ResolvedExpr,
        ResolvedExprKind, ResolvedProgram,
    },
    source::{GeneratedReason, Origin, Span},
    surface::{SurfaceType, SurfaceTypeKind},
    types::Type,
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
        }
    }
}

/// A structural mismatch produced by the general checking rule.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TypeMismatch {
    span: Span,
    expected: Type,
    found: Type,
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
}

impl fmt::Display for ElaborationFailure {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Core(error) => write!(formatter, "typed Core construction failed: {error}"),
            Self::InvalidState => formatter.write_str("typed elaboration state is inconsistent"),
        }
    }
}

impl Error for ElaborationFailure {}

impl From<BuildError> for ElaborationFailure {
    fn from(error: BuildError) -> Self {
        Self::Core(error)
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
                mismatch.expected, mismatch.found
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
                Type::Int | Type::Bool | Type::Unit => {
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
                (Type::Int | Type::Bool | Type::Unit, Some(TypeProvenanceNode::Fact(_))) => {}
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

    fn from_surface(surface: &SurfaceType) -> Result<Self, TypeError> {
        lower_surface_type(surface)
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
            .insert(binder, TypeFact { ty, provenance })
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
        Ok(self.binders.insert(binder, TypeFact { ty, provenance }))
    }

    fn fact(&self, binder: BinderId) -> Option<&TypeFact> {
        self.binders.get(&binder)
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
    state: ElaboratorState,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ElaboratorState {
    Ready,
    Poisoned,
}

impl Elaborator {
    /// Starts an elaborator for an expression with no resolved binder namespace.
    pub fn new() -> Self {
        Self {
            builder: CoreBuilder::new(),
            state: ElaboratorState::Ready,
        }
    }

    /// Starts an elaborator after reserving every resolver-assigned binder.
    ///
    /// # Errors
    ///
    /// Returns a Core construction failure if the complete namespace cannot be
    /// reserved before elaboration starts.
    pub fn for_program(program: &ResolvedProgram) -> Result<Self, ElaborationFailure> {
        let mut builder = CoreBuilder::new();
        builder.reserve_resolved_binders(resolved_binders(program))?;
        Ok(Self {
            builder,
            state: ElaboratorState::Ready,
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

    /// Elaborates sequential global definitions and the required file result.
    ///
    /// Definitions are checked in source order and enter the typing context
    /// only after their complete initializer. The resulting function values are
    /// folded right-to-left into nonrecursive Core bindings around the result.
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
    pub fn finish(self, root: NodeId) -> Result<UnvalidatedProgram, ElaborationFailure> {
        if self.state == ElaboratorState::Poisoned {
            return Err(ElaborationFailure::InvalidState);
        }
        self.builder.finish(root).map_err(Into::into)
    }

    fn elaborate_program(&mut self, program: &ResolvedProgram) -> Result<TypedNode, TypeError> {
        let mut context = TypeContext::new();
        let mut globals = Vec::with_capacity(program.definitions.len());

        for definition in &program.definitions {
            let (name, parameter, function_type, body, presentation, result_cause) =
                match &definition.kind {
                    ResolvedDefinitionKind::Equational(equational) => {
                        let interface_type =
                            ProvenancedType::from_surface(&equational.interface.annotation)?;
                        if !matches!(interface_type.ty, Type::Function(_, _)) {
                            return Err(equation_interface_not_function(
                                &equational.interface.annotation,
                                &equational.equation.name,
                            ));
                        }
                        let (_, codomain) = interface_type.function_parts()?;
                        let result_cause = codomain
                            .provenance
                            .span()
                            .unwrap_or(equational.interface.annotation.span);
                        (
                            &equational.interface.name,
                            &equational.equation.binder,
                            interface_type,
                            FunctionBody::Expression(&equational.equation.body),
                            equational_origin(definition.span, equational),
                            result_cause,
                        )
                    }
                    ResolvedDefinitionKind::InlineOperational(operational) => {
                        let domain = ProvenancedType::from_surface(
                            &operational.header.parameter.annotation,
                        )?;
                        let codomain =
                            ProvenancedType::from_surface(&operational.header.result_type)?;
                        let function_type = ProvenancedType::function(
                            domain,
                            codomain,
                            Some(operational.header.span),
                        )?;
                        (
                            &operational.header.name,
                            &operational.header.parameter.binder,
                            function_type,
                            FunctionBody::Block(&operational.body),
                            operational_origin(definition.span, operational),
                            operational.header.result_type.span,
                        )
                    }
                };
            let (domain, codomain) = function_type.function_parts()?;
            let function = self.elaborate_expression_with_context(
                ElaborationTask::CheckFunction {
                    parameter,
                    domain,
                    codomain,
                    body,
                    presentation,
                    function_type: function_type.clone(),
                    body_check: CheckKind::Definition { result_cause },
                },
                &mut context,
            )?;
            if !structurally_equal(&function.ty, &function_type.ty)
                || !function.provenance.aligns(&function.ty)
            {
                return Err(invalid_state());
            }
            let binder = self.builder.resolved_binder(
                name.id,
                function_type.ty.clone(),
                Origin::Generated {
                    cause: Box::new(name.origin.clone()),
                    reason: GeneratedReason::BindingLowering,
                },
            )?;
            if context
                .insert_with_provenance(name.id, function_type.ty, function_type.provenance)?
                .is_some()
            {
                return Err(invalid_state());
            }
            globals.push(ElaboratedBinding {
                binder,
                initializer: function.node,
                origin: global_binding_origin(definition),
            });
        }

        let mut result = self.elaborate_expression_with_context(
            ElaborationTask::Synthesize {
                expression: &program.result,
                cause: Some(SynthesisCause::ProgramResult(program.result.span)),
            },
            &mut context,
        )?;
        for global in globals.into_iter().rev() {
            let node = self.builder.binding(
                global.binder,
                global.initializer,
                result.node,
                result.ty.clone(),
                global.origin,
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
        let mut bindings = Vec::new();
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
                        let ty = fact.ty.clone();
                        let provenance = fact.provenance.clone();
                        let node = self.builder.variable(
                            occurrence.binder,
                            ty.clone(),
                            occurrence.origin.clone(),
                        )?;
                        values.push(TypedNode {
                            node,
                            ty,
                            provenance,
                        });
                    }
                    ResolvedExprKind::Apply(application) => {
                        tasks.push(ElaborationTask::AfterApplicationFunction {
                            whole_span: current.span,
                            function_span: application.function.span,
                            argument: &application.argument,
                        });
                        tasks.push(ElaborationTask::Synthesize {
                            expression: &application.function,
                            cause: Some(SynthesisCause::Application(current.span)),
                        });
                    }
                    ResolvedExprKind::Block(block) => {
                        schedule_block(block, None, cause, &mut tasks, bindings.len())?;
                    }
                    ResolvedExprKind::Function(_) => {
                        return Err(function_needs_context(current.span, cause));
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
                            parameter: &function.parameter,
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
                            bindings.len(),
                        )?;
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
                    if !structurally_equal(&synthesized.ty, &expected.ty) {
                        return Err(check_mismatch(
                            kind,
                            span,
                            expected.ty,
                            synthesized.ty,
                            expected.provenance.span(),
                        ));
                    }
                    values.push(synthesized);
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
                    schedule_function_check(
                        &mut self.builder,
                        context,
                        &mut tasks,
                        bindings.len(),
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
                    parameter,
                    binder,
                    ty,
                    origin,
                    provenance,
                } => {
                    let body = values.pop().ok_or_else(invalid_state)?;
                    if context.binders.remove(&parameter).is_none() {
                        return Err(invalid_state());
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
                } => {
                    let function = values.pop().ok_or_else(invalid_state)?;
                    let Type::Function(domain, codomain) = &function.ty else {
                        return Err(not_applicable(function_span, whole_span, &function.ty));
                    };
                    let (domain_provenance, codomain_provenance) =
                        function.provenance.function_parts(&function.ty)?;
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
                    values.push(TypedNode {
                        node,
                        ty: codomain.ty,
                        provenance: codomain.provenance,
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
                    require_integer(&left, left_span, operator_span)?;
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
                    require_integer(&right, right_span, operator_span)?;
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
                    let initializer = values.pop().ok_or_else(invalid_state)?;
                    let binding_type = expected.unwrap_or_else(|| ProvenancedType {
                        ty: initializer.ty.clone(),
                        provenance: initializer.provenance.clone(),
                    });
                    let ty = binding_type.ty.clone();
                    let binder_origin = Origin::Generated {
                        cause: Box::new(binding.binder.origin.clone()),
                        reason: GeneratedReason::BindingLowering,
                    };
                    let binder = self.builder.resolved_binder(
                        binding.binder.id,
                        ty.clone(),
                        binder_origin,
                    )?;
                    if context
                        .insert_with_provenance(binding.binder.id, ty, binding_type.provenance)?
                        .is_some()
                    {
                        return Err(invalid_state());
                    }
                    bindings.push(ElaboratedBinding {
                        binder,
                        initializer: initializer.node,
                        origin: binding_origin(binding),
                    });
                }
                ElaborationTask::FinishBlock {
                    bindings: source_bindings,
                    binding_start,
                } => {
                    let mut body = values.pop().ok_or_else(invalid_state)?;
                    if binding_start > bindings.len()
                        || bindings.len() - binding_start != source_bindings.len()
                    {
                        return Err(invalid_state());
                    }
                    for binding in bindings.drain(binding_start..).rev() {
                        let node = self.builder.binding(
                            binding.binder,
                            binding.initializer,
                            body.node,
                            body.ty.clone(),
                            binding.origin,
                        )?;
                        body = TypedNode {
                            node,
                            ty: body.ty,
                            provenance: body.provenance,
                        };
                    }
                    for binding in source_bindings {
                        if context.binders.remove(&binding.binder.id).is_none() {
                            return Err(invalid_state());
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
        parameter: &'a Binder,
        domain: ProvenancedType,
        codomain: ProvenancedType,
        body: FunctionBody<'a>,
        presentation: Origin,
        function_type: ProvenancedType,
        body_check: CheckKind,
    },
    FinishFunction {
        parameter: BinderId,
        binder: TypedBinder,
        ty: Type,
        origin: Origin,
        provenance: TypeProvenance,
    },
    AfterApplicationFunction {
        whole_span: Span,
        function_span: Span,
        argument: &'a ResolvedExpr,
    },
    FinishApplication {
        whole_span: Span,
        function_span: Span,
        argument_span: Span,
        function: TypedNode,
        codomain: ProvenancedType,
    },
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
    FinishBlock {
        bindings: &'a [ResolvedBinding],
        binding_start: usize,
    },
}

#[derive(Clone, Copy)]
enum FunctionBody<'a> {
    Expression(&'a ResolvedExpr),
    Block(&'a ResolvedBlock),
}

#[derive(Clone, Copy)]
enum CheckKind {
    General,
    Argument {
        function_span: Span,
        whole_span: Span,
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
    ProgramResult(Span),
    Application(Span),
    Operator(Span),
}

struct FunctionCheck<'a> {
    parameter: &'a Binder,
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
    origin: Origin,
}

fn schedule_block<'a>(
    block: &'a ResolvedBlock,
    expected: Option<(ProvenancedType, CheckKind)>,
    synthesis_cause: Option<SynthesisCause>,
    tasks: &mut Vec<ElaborationTask<'a>>,
    binding_start: usize,
) -> Result<(), TypeError> {
    tasks.push(ElaborationTask::FinishBlock {
        bindings: &block.bindings,
        binding_start,
    });
    if let Some((expected, kind)) = expected {
        tasks.push(ElaborationTask::Check {
            expression: &block.result,
            expected,
            kind,
        });
    } else {
        tasks.push(ElaborationTask::Synthesize {
            expression: &block.result,
            cause: synthesis_cause,
        });
    }
    for binding in block.bindings.iter().rev() {
        let expected = binding
            .annotation
            .as_ref()
            .map(lower_surface_type)
            .transpose()?;
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
    Ok(())
}

fn schedule_function_check<'a>(
    builder: &mut CoreBuilder,
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
    let parameter_binder = builder.resolved_binder(
        parameter.id,
        domain.ty.clone(),
        Origin::Generated {
            cause: Box::new(parameter.origin.clone()),
            reason: GeneratedReason::FunctionLowering,
        },
    )?;
    if context
        .insert_with_provenance(parameter.id, domain.ty.clone(), domain.provenance.clone())?
        .is_some()
    {
        return Err(invalid_state());
    }
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
        parameter: parameter.id,
        binder: parameter_binder,
        ty: function_type.ty,
        origin,
        provenance: function_type.provenance,
    });
    match body {
        FunctionBody::Expression(expression) => tasks.push(ElaborationTask::Check {
            expression,
            expected: codomain,
            kind: body_check,
        }),
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

fn check_mismatch(
    kind: CheckKind,
    span: Span,
    expected: Type,
    found: Type,
    expected_cause: Option<Span>,
) -> TypeError {
    match kind {
        CheckKind::General => TypeError::Mismatch(TypeMismatch {
            span,
            expected,
            found,
        }),
        CheckKind::Argument {
            function_span,
            whole_span,
        } => {
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
            diagnostic.expected = Some(expected.to_string());
            diagnostic.found = Some(found.to_string());
            TypeError::Source(Box::new(diagnostic))
        }
        CheckKind::Definition { result_cause } => {
            let mut diagnostic = Diagnostic::new(
                TypeReason::DefinitionResult,
                SourceLabel::new(span, "this function body has the wrong result type"),
            );
            diagnostic.related.push(SourceLabel::new(
                expected_cause.unwrap_or(result_cause),
                "the function interface requires this result type",
            ));
            diagnostic.expected = Some(expected.to_string());
            diagnostic.found = Some(found.to_string());
            TypeError::Source(Box::new(diagnostic))
        }
        CheckKind::BindingInitializer {
            initializer_span,
            annotation_span,
        } => {
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
            diagnostic.expected = Some(expected.to_string());
            diagnostic.found = Some(found.to_string());
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
            SynthesisCause::Binding(span) => (
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

fn not_applicable(function_span: Span, whole_span: Span, found: &Type) -> TypeError {
    let mut diagnostic = Diagnostic::new(
        TypeReason::NotApplicable,
        SourceLabel::new(function_span, "this expression is not a function"),
    );
    diagnostic.related.push(SourceLabel::new(
        whole_span,
        "this application requires a function here",
    ));
    diagnostic.expected = Some("function".to_owned());
    diagnostic.found = Some(found.to_string());
    TypeError::Source(Box::new(diagnostic))
}

fn equation_interface_not_function(
    annotation: &SurfaceType,
    equation_name: &crate::resolved::ResolvedOccurrence,
) -> TypeError {
    let found = lower_surface_type(annotation)
        .map(|ty| ty.ty.to_string())
        .unwrap_or_else(|_| "invalid type".to_owned());
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
    diagnostic.found = Some(operand.ty.to_string());
    Err(TypeError::Source(Box::new(diagnostic)))
}

fn invalid_state() -> TypeError {
    TypeError::Internal(ElaborationFailure::InvalidState)
}

fn lower_surface_type(surface: &SurfaceType) -> Result<ProvenancedType, TypeError> {
    enum Task<'a> {
        Visit(&'a SurfaceType),
        Function(Span),
    }

    let mut tasks = vec![Task::Visit(surface)];
    let mut types = Vec::new();
    while let Some(task) = tasks.pop() {
        match task {
            Task::Visit(current) => match &current.kind {
                SurfaceTypeKind::Int => types.push(ProvenancedType {
                    ty: Type::Int,
                    provenance: TypeProvenance::atom(Some(current.span)),
                }),
                SurfaceTypeKind::Bool => types.push(ProvenancedType {
                    ty: Type::Bool,
                    provenance: TypeProvenance::atom(Some(current.span)),
                }),
                SurfaceTypeKind::Unit => types.push(ProvenancedType {
                    ty: Type::Unit,
                    provenance: TypeProvenance::atom(Some(current.span)),
                }),
                SurfaceTypeKind::Function(function) => {
                    tasks.push(Task::Function(current.span));
                    tasks.push(Task::Visit(&function.codomain));
                    tasks.push(Task::Visit(&function.domain));
                }
            },
            Task::Function(span) => {
                let codomain = types.pop().ok_or_else(invalid_state)?;
                let domain = types.pop().ok_or_else(invalid_state)?;
                types.push(ProvenancedType::function(domain, codomain, Some(span))?);
            }
        }
    }
    let ty = types.pop().ok_or_else(invalid_state)?;
    if types.is_empty() {
        Ok(ty)
    } else {
        Err(invalid_state())
    }
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

fn global_binding_origin(definition: &crate::resolved::ResolvedDefinition) -> Origin {
    Origin::Generated {
        cause: Box::new(Origin::Source(definition.span)),
        reason: GeneratedReason::BindingLowering,
    }
}

fn equational_origin(
    definition_span: Span,
    equational: &crate::resolved::ResolvedEquationalGlobal,
) -> Origin {
    Origin::Related {
        primary: Box::new(Origin::Source(equational.equation.span)),
        related: vec![
            definition_span,
            equational.interface.span,
            equational.interface.annotation.span,
        ],
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
            operational.header.parameter.annotation.span,
            operational.header.result_type.span,
        ],
    }
}

fn anonymous_function_origin(
    expression_span: Span,
    function: &crate::resolved::ResolvedFunctionExpr,
) -> Origin {
    Origin::Related {
        primary: Box::new(Origin::Source(expression_span)),
        related: vec![function.parameter.origin.primary_span(), function.body.span],
    }
}

/// Applies the structural type-equality rule without inference or coercion.
#[must_use]
pub fn structurally_equal(left: &Type, right: &Type) -> bool {
    let mut work = vec![(left, right)];
    while let Some((left, right)) = work.pop() {
        match (left, right) {
            (Type::Int, Type::Int) | (Type::Bool, Type::Bool) | (Type::Unit, Type::Unit) => {}
            (
                Type::Function(left_domain, left_codomain),
                Type::Function(right_domain, right_codomain),
            ) => {
                work.push((left_codomain, right_codomain));
                work.push((left_domain, right_domain));
            }
            _ => return false,
        }
    }
    true
}

fn resolved_binders(program: &ResolvedProgram) -> Vec<BinderId> {
    let mut binders = Vec::new();
    let mut expressions = vec![&program.result];
    for definition in &program.definitions {
        match &definition.kind {
            ResolvedDefinitionKind::Equational(equational) => {
                binders.push(equational.interface.name.id);
                binders.push(equational.equation.binder.id);
                expressions.push(&equational.equation.body);
            }
            ResolvedDefinitionKind::InlineOperational(operational) => {
                binders.push(operational.header.name.id);
                binders.push(operational.header.parameter.binder.id);
                expressions.push(&operational.body.result);
                for binding in &operational.body.bindings {
                    binders.push(binding.binder.id);
                    expressions.push(&binding.initializer);
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
                for binding in &block.bindings {
                    binders.push(binding.binder.id);
                    expressions.push(&binding.initializer);
                }
            }
            ResolvedExprKind::Function(function) => {
                binders.push(function.parameter.id);
                expressions.push(&function.body.result);
                for binding in &function.body.bindings {
                    binders.push(binding.binder.id);
                    expressions.push(&binding.initializer);
                }
            }
            ResolvedExprKind::Integer(_)
            | ResolvedExprKind::Boolean(_)
            | ResolvedExprKind::Unit
            | ResolvedExprKind::Occurrence(_) => {}
        }
    }
    binders
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
        let mut context = TypeContext::new();
        context.binders.insert(
            function.parameter.id,
            TypeFact {
                ty: Type::Function(Box::new(Type::Int), Box::new(Type::Int)),
                provenance: TypeProvenance::atom(None),
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
    fn sequential_global_elaboration_does_not_clone_the_growing_context() {
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
            .expect("sequential globals should elaborate");

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
