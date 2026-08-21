//! Bidirectional typed elaboration from resolved surface syntax to pure Core.

use std::{collections::HashMap, error::Error, fmt};

use crate::{
    core::{BuildError, CoreBuilder, NodeId, Primitive, TypedBinder, UnvalidatedProgram},
    diagnostic::{Diagnostic, SourceLabel},
    resolved::{
        BinderId, ResolvedBinding, ResolvedDefinitionKind, ResolvedExpr, ResolvedExprKind,
        ResolvedProgram,
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
}

impl fmt::Display for TypeReason {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::OperatorOperand => formatter.write_str("type.operator-operand"),
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

/// An accepted expression family not yet implemented by this retained increment.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PendingFeature {
    /// Unary applications.
    Application,
    /// Anonymous functions.
    Function,
    /// Anonymous functions reached through an expected-type checking request.
    FunctionChecking,
    /// File-level definitions.
    Definition,
}

impl fmt::Display for PendingFeature {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(match self {
            Self::Application => "application elaboration",
            Self::Function => "function elaboration",
            Self::FunctionChecking => "function checking",
            Self::Definition => "definition elaboration",
        })
    }
}

/// A compiler-owned elaboration failure, distinct from rejected Ash source.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ElaborationFailure {
    /// Core construction could not represent the requested node.
    Core(BuildError),
    /// The accepted feature belongs to a later implementation increment.
    Pending(PendingFeature),
    /// The explicit elaboration work stack lost an invariant.
    InvalidState,
}

impl fmt::Display for ElaborationFailure {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Core(error) => write!(formatter, "typed Core construction failed: {error}"),
            Self::Pending(feature) => write!(formatter, "pending Mini-Ash feature: {feature}"),
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
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct TypeContext {
    binders: HashMap<BinderId, Type>,
}

impl TypeContext {
    /// Creates an empty typing context.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Adds or replaces one resolved binder type.
    pub fn insert(&mut self, binder: BinderId, ty: Type) -> Option<Type> {
        self.binders.insert(binder, ty)
    }

    /// Returns the monotype assigned to a resolved binder.
    #[must_use]
    pub fn lookup(&self, binder: BinderId) -> Option<&Type> {
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
    /// integer, or a structured internal failure when this increment does not
    /// yet implement an accepted expression family or Core construction fails.
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
        let result = self.elaborate_expression(ElaborationTask::Synthesize(expression), context);
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
        let result = self.elaborate_expression(
            ElaborationTask::Check {
                expression,
                expected: expected.clone(),
            },
            context,
        );
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

    fn elaborate_expression<'a>(
        &mut self,
        initial: ElaborationTask<'a>,
        context: &TypeContext,
    ) -> Result<TypedNode, TypeError> {
        let mut tasks = vec![initial];
        let mut values = Vec::new();
        let mut bindings = Vec::new();
        let mut context = context.clone();
        while let Some(task) = tasks.pop() {
            match task {
                ElaborationTask::Synthesize(current) => match &current.kind {
                    ResolvedExprKind::Integer(value) => {
                        let ty = Type::Int;
                        let node = self.builder.integer(
                            value.clone(),
                            ty.clone(),
                            Origin::Source(current.span),
                        )?;
                        values.push(TypedNode { node, ty });
                    }
                    ResolvedExprKind::Boolean(value) => {
                        let ty = Type::Bool;
                        let node = self.builder.boolean(
                            *value,
                            ty.clone(),
                            Origin::Source(current.span),
                        )?;
                        values.push(TypedNode { node, ty });
                    }
                    ResolvedExprKind::Unit => {
                        let ty = Type::Unit;
                        let node = self
                            .builder
                            .unit(ty.clone(), Origin::Source(current.span))?;
                        values.push(TypedNode { node, ty });
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
                        let ty = context
                            .lookup(occurrence.binder)
                            .cloned()
                            .ok_or_else(invalid_state)?;
                        let node = self.builder.variable(
                            occurrence.binder,
                            ty.clone(),
                            occurrence.origin.clone(),
                        )?;
                        values.push(TypedNode { node, ty });
                    }
                    ResolvedExprKind::Apply(_) => return pending(PendingFeature::Application),
                    ResolvedExprKind::Block(block) => {
                        let binding_start = bindings.len();
                        tasks.push(ElaborationTask::FinishBlock {
                            bindings: &block.bindings,
                            binding_start,
                        });
                        tasks.push(ElaborationTask::Synthesize(&block.result));
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
                            if let Some(expected) = expected {
                                tasks.push(ElaborationTask::Check {
                                    expression: &binding.initializer,
                                    expected,
                                });
                            } else {
                                tasks.push(ElaborationTask::Synthesize(&binding.initializer));
                            }
                        }
                    }
                    ResolvedExprKind::Function(_) => return pending(PendingFeature::Function),
                },
                ElaborationTask::Check {
                    expression,
                    expected,
                } => {
                    if matches!(expression.kind, ResolvedExprKind::Function(_)) {
                        return pending(PendingFeature::FunctionChecking);
                    }
                    tasks.push(ElaborationTask::FinishCheck {
                        span: expression.span,
                        expected,
                    });
                    tasks.push(ElaborationTask::Synthesize(expression));
                }
                ElaborationTask::FinishCheck { span, expected } => {
                    let synthesized = values.pop().ok_or_else(invalid_state)?;
                    if !structurally_equal(&synthesized.ty, &expected) {
                        return Err(TypeError::Mismatch(TypeMismatch {
                            span,
                            expected,
                            found: synthesized.ty,
                        }));
                    }
                    values.push(synthesized);
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
                    tasks.push(ElaborationTask::Synthesize(right));
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
                    values.push(TypedNode { node, ty });
                }
                ElaborationTask::FinishBinding { binding, expected } => {
                    let initializer = values.pop().ok_or_else(invalid_state)?;
                    let ty = expected.unwrap_or_else(|| initializer.ty.clone());
                    let binder_origin = Origin::Generated {
                        cause: Box::new(binding.binder.origin.clone()),
                        reason: GeneratedReason::BindingLowering,
                    };
                    let binder = self.builder.resolved_binder(
                        binding.binder.id,
                        ty.clone(),
                        binder_origin,
                    )?;
                    if context.insert(binding.binder.id, ty).is_some() {
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
                        body = TypedNode { node, ty: body.ty };
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
        if values.is_empty() {
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
    Synthesize(&'a ResolvedExpr),
    Check {
        expression: &'a ResolvedExpr,
        expected: Type,
    },
    FinishCheck {
        span: Span,
        expected: Type,
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
        expected: Option<Type>,
    },
    FinishBlock {
        bindings: &'a [ResolvedBinding],
        binding_start: usize,
    },
}

struct ElaboratedBinding {
    binder: TypedBinder,
    initializer: NodeId,
    origin: Origin,
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
    tasks.push(ElaborationTask::Synthesize(&binary.left));
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

fn pending(feature: PendingFeature) -> Result<TypedNode, TypeError> {
    Err(TypeError::Internal(ElaborationFailure::Pending(feature)))
}

fn lower_surface_type(surface: &SurfaceType) -> Result<Type, TypeError> {
    enum Task<'a> {
        Visit(&'a SurfaceType),
        Function,
    }

    let mut tasks = vec![Task::Visit(surface)];
    let mut types = Vec::new();
    while let Some(task) = tasks.pop() {
        match task {
            Task::Visit(current) => match &current.kind {
                SurfaceTypeKind::Int => types.push(Type::Int),
                SurfaceTypeKind::Bool => types.push(Type::Bool),
                SurfaceTypeKind::Unit => types.push(Type::Unit),
                SurfaceTypeKind::Function(function) => {
                    tasks.push(Task::Function);
                    tasks.push(Task::Visit(&function.codomain));
                    tasks.push(Task::Visit(&function.domain));
                }
            },
            Task::Function => {
                let codomain = types.pop().ok_or_else(invalid_state)?;
                let domain = types.pop().ok_or_else(invalid_state)?;
                types.push(Type::Function(Box::new(domain), Box::new(codomain)));
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
