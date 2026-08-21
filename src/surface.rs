//! Recovery-free, source-spanned syntax passed from parsing to resolution.

use crate::{integer::Integer, source::Span};

/// One parsed Mini-Ash source file.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SurfaceProgram {
    /// Sequential global definitions.
    pub definitions: Vec<SurfaceDefinition>,
    /// The required final result expression.
    pub result: SurfaceExpr,
    /// The complete accepted source span.
    pub span: Span,
}

/// A source global definition and its presentation-specific payload.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SurfaceDefinition {
    /// The definition presentation.
    pub kind: SurfaceDefinitionKind,
    /// The complete definition span.
    pub span: Span,
}

/// The closed Mini-Ash global-definition family.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SurfaceDefinitionKind {
    /// An external interface followed by an equation.
    Equational(EquationalGlobal),
    /// An inline operational function definition.
    InlineOperational(InlineOperationalGlobal),
}

/// The source structure retained for an equational global.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct EquationalGlobal {
    /// The separately written external interface.
    pub interface: SurfaceExternalInterface,
    /// The binder-only equation.
    pub equation: SurfaceEquation,
}

/// One external name and type interface.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SurfaceExternalInterface {
    /// The declared global name.
    pub name: SurfaceName,
    /// The declared type.
    pub annotation: SurfaceType,
    /// The complete interface span.
    pub span: Span,
}

/// One equation head and body.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SurfaceEquation {
    /// The name repeated by the equation head.
    pub name: SurfaceName,
    /// The equation's one binder.
    pub binder: SurfaceBinder,
    /// The equation body.
    pub body: SurfaceExpr,
    /// The complete equation span.
    pub span: Span,
}

/// The source structure retained for an inline operational global.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct InlineOperationalGlobal {
    /// The complete source header before the body.
    pub header: SurfaceInlineOperationalHeader,
    /// The operational body.
    pub body: SurfaceBlock,
}

/// The header of an inline operational global.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SurfaceInlineOperationalHeader {
    /// The global function name.
    pub name: SurfaceName,
    /// The one typed parameter.
    pub parameter: SurfaceTypedBinder,
    /// The declared result type.
    pub result_type: SurfaceType,
    /// The complete header span, excluding the body.
    pub span: Span,
}

/// A source expression.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SurfaceExpr {
    /// The expression payload.
    pub kind: SurfaceExprKind,
    /// The complete expression span.
    pub span: Span,
}

/// The closed expression family accepted by Mini-Ash.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SurfaceExprKind {
    /// An arbitrary-precision integer literal.
    Integer(Integer),
    /// A Boolean literal.
    Boolean(bool),
    /// The unit value.
    Unit,
    /// An unresolved source name.
    Name(SurfaceName),
    /// Strict unary application.
    Apply(ApplicationExpr),
    /// Integer multiplication.
    Multiply(BinaryExpr),
    /// Integer addition.
    Add(BinaryExpr),
    /// Integer equality.
    Equal(BinaryExpr),
    /// A sequential block.
    Block(SurfaceBlock),
    /// An anonymous unary function.
    Function(FunctionExpr),
}

/// A binary source expression.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct BinaryExpr {
    /// The left operand.
    pub left: Box<SurfaceExpr>,
    /// The right operand.
    pub right: Box<SurfaceExpr>,
    /// The exact source span of the binary operator token.
    pub operator_span: Span,
}

/// A unary application expression.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ApplicationExpr {
    /// The function position.
    pub function: Box<SurfaceExpr>,
    /// The argument position.
    pub argument: Box<SurfaceExpr>,
}

/// A sequential block expression.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SurfaceBlock {
    /// Sequential local bindings.
    pub bindings: Vec<SurfaceBinding>,
    /// The block's required result expression.
    pub result: Box<SurfaceExpr>,
    /// The complete braced span.
    pub span: Span,
}

/// One immutable local binding.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SurfaceBinding {
    /// The introduced binder.
    pub binder: SurfaceBinder,
    /// Its optional type annotation.
    pub annotation: Option<SurfaceType>,
    /// The initializer expression.
    pub initializer: SurfaceExpr,
    /// The complete binding span.
    pub span: Span,
}

/// An anonymous function expression.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FunctionExpr {
    /// The function's one binder.
    pub parameter: SurfaceBinder,
    /// The braced body.
    pub body: SurfaceBlock,
}

/// An unresolved source name and its exact span.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SurfaceName {
    /// The source spelling.
    pub text: String,
    /// The exact name span.
    pub span: Span,
}

/// A binder retained separately from later binder identity.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SurfaceBinder {
    /// The source spelling and span.
    pub name: SurfaceName,
    /// The complete binder span.
    pub span: Span,
}

/// One binder with a source type annotation.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SurfaceTypedBinder {
    /// The introduced binder.
    pub binder: SurfaceBinder,
    /// Its required type.
    pub annotation: SurfaceType,
    /// The complete typed-binder span.
    pub span: Span,
}

/// A source type.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SurfaceType {
    /// The type payload.
    pub kind: SurfaceTypeKind,
    /// The complete accepted type span.
    pub span: Span,
}

/// The closed Mini-Ash type family.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SurfaceTypeKind {
    /// Arbitrary-precision integers.
    Int,
    /// Boolean values.
    Bool,
    /// The unit value.
    Unit,
    /// A unary function type.
    Function(FunctionType),
}

/// A unary function type.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FunctionType {
    /// The parameter type.
    pub domain: Box<SurfaceType>,
    /// The result type.
    pub codomain: Box<SurfaceType>,
}
