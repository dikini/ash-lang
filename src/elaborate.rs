//! Bidirectional typed elaboration from resolved surface syntax to pure Core.

use std::{collections::HashMap, error::Error, fmt};

use crate::{
    core::{BuildError, CoreBuilder, NodeId, Primitive, UnvalidatedProgram},
    diagnostic::{Diagnostic, SourceLabel},
    resolved::{BinderId, ResolvedDefinitionKind, ResolvedExpr, ResolvedExprKind, ResolvedProgram},
    source::{Origin, Span},
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
    /// Resolved variable occurrences.
    Variable,
    /// Unary applications.
    Application,
    /// Sequential blocks and their bindings.
    Block,
    /// Anonymous functions.
    Function,
    /// File-level definitions.
    Definition,
}

impl fmt::Display for PendingFeature {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(match self {
            Self::Variable => "variable elaboration",
            Self::Application => "application elaboration",
            Self::Block => "block elaboration",
            Self::Function => "function elaboration",
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
        _context: &TypeContext,
    ) -> Result<TypedNode, TypeError> {
        if self.state == ElaboratorState::Poisoned {
            return Err(invalid_state());
        }
        let result = self.synthesize_primitive(expression);
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
        let synthesized = self.synthesize(expression, context)?;
        if structurally_equal(&synthesized.ty, expected) {
            Ok(synthesized)
        } else {
            self.state = ElaboratorState::Poisoned;
            Err(TypeError::Mismatch(TypeMismatch {
                span: expression.span,
                expected: expected.clone(),
                found: synthesized.ty,
            }))
        }
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

    fn synthesize_primitive(&mut self, expression: &ResolvedExpr) -> Result<TypedNode, TypeError> {
        let mut tasks = vec![SynthesisTask::Visit(expression)];
        let mut values = Vec::new();
        while let Some(task) = tasks.pop() {
            match task {
                SynthesisTask::Visit(current) => match &current.kind {
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
                    ResolvedExprKind::Occurrence(_) => return pending(PendingFeature::Variable),
                    ResolvedExprKind::Apply(_) => return pending(PendingFeature::Application),
                    ResolvedExprKind::Block(_) => return pending(PendingFeature::Block),
                    ResolvedExprKind::Function(_) => return pending(PendingFeature::Function),
                },
                SynthesisTask::AfterLeft {
                    primitive,
                    whole_span,
                    operator_span,
                    right,
                    left_span,
                } => {
                    let left = values.pop().ok_or_else(invalid_state)?;
                    require_integer(&left, left_span, operator_span)?;
                    tasks.push(SynthesisTask::AfterRight {
                        primitive,
                        whole_span,
                        operator_span,
                        left,
                        right_span: right.span,
                    });
                    tasks.push(SynthesisTask::Visit(right));
                }
                SynthesisTask::AfterRight {
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

enum SynthesisTask<'a> {
    Visit(&'a ResolvedExpr),
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
}

fn schedule_left<'a>(
    primitive: Primitive,
    whole_span: Span,
    binary: &'a crate::resolved::ResolvedBinaryExpr,
    tasks: &mut Vec<SynthesisTask<'a>>,
) {
    tasks.push(SynthesisTask::AfterLeft {
        primitive,
        whole_span,
        operator_span: binary.operator_span,
        right: &binary.right,
        left_span: binary.left.span,
    });
    tasks.push(SynthesisTask::Visit(&binary.left));
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
