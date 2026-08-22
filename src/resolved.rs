//! Name-resolved, source-spanned syntax passed to typed elaboration.

use std::sync::Arc;

use crate::{
    integer::Integer,
    source::{Origin, Span},
    types::{ConstructorId, NominalTypeId, Type},
};

/// Identifies one binding within a resolved program.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct BinderId(u32);

impl BinderId {
    pub(crate) const fn new(value: u32) -> Self {
        Self(value)
    }

    /// Returns the resolver-assigned numeric identity.
    #[must_use]
    pub const fn value(self) -> u32 {
        self.0
    }
}

/// A resolved definition site.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Binder {
    /// Stable identity assigned by the resolver.
    pub id: BinderId,
    /// Exact source spelling.
    pub spelling: String,
    /// Causal source provenance for the definition site.
    pub origin: Origin,
}

/// A resolved occurrence site.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResolvedOccurrence {
    /// Identity of the definition selected by lexical scope.
    pub binder: BinderId,
    /// Exact source spelling at this occurrence.
    pub spelling: String,
    /// Causal source provenance for the occurrence site.
    pub origin: Origin,
}

/// One resolved Mini-Ash source file.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResolvedProgram {
    /// Immutable nominal and constructor registry.
    pub registry: Arc<ResolvedRegistry>,
    /// Resolved global definitions in source order.
    pub definitions: Vec<ResolvedDefinition>,
    /// Required final result expression.
    pub result: ResolvedExpr,
    /// Complete accepted source span.
    pub span: Span,
}

/// Immutable resolved metadata for one source file.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResolvedRegistry {
    nominals: Box<[ResolvedNominalType]>,
    constructors: Box<[ResolvedConstructor]>,
}

impl ResolvedRegistry {
    /// Constructs one closed registry after two-pass resolution.
    #[must_use]
    pub fn new(nominals: Vec<ResolvedNominalType>, constructors: Vec<ResolvedConstructor>) -> Self {
        Self {
            nominals: nominals.into_boxed_slice(),
            constructors: constructors.into_boxed_slice(),
        }
    }

    /// Returns nominal declarations in source order.
    #[must_use]
    pub fn nominals(&self) -> &[ResolvedNominalType] {
        &self.nominals
    }

    /// Returns constructors in file and declaration order.
    #[must_use]
    pub fn constructors(&self) -> &[ResolvedConstructor] {
        &self.constructors
    }
}

/// Resolved metadata for one nominal declaration.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResolvedNominalType {
    /// Stable source-order identity.
    pub id: NominalTypeId,
    /// Exact declaration spelling.
    pub spelling: String,
    /// Constructor identities in declaration order.
    pub constructors: Box<[ConstructorId]>,
    /// Declaration provenance.
    pub origin: Origin,
}

/// Resolved metadata for one constructor declaration.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResolvedConstructor {
    /// Stable constructor identity.
    pub id: ConstructorId,
    /// Owning nominal identity.
    pub owner: NominalTypeId,
    /// Exact constructor spelling.
    pub spelling: String,
    /// Zero or one semantic payload type.
    pub payload: Option<Type>,
    /// Declaration provenance.
    pub origin: Origin,
}

/// One fully resolved type occurrence.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResolvedType {
    /// Resolved structural or nominal type.
    pub ty: Type,
    /// Stack-safe provenance aligned with every structural type component.
    pub provenance: ResolvedTypeProvenance,
    /// Causal source provenance.
    pub origin: Origin,
    /// Complete source occurrence span.
    pub span: Span,
}

/// Shareable arena-shaped provenance for one resolved type occurrence.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResolvedTypeProvenance {
    nodes: Arc<[ResolvedTypeProvenanceNode]>,
    root: usize,
}

/// One node in a resolved type-provenance arena.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ResolvedTypeProvenanceNode {
    /// An atomic or nominal type occurrence.
    Fact(Span),
    /// A tuple occurrence and its element provenance roots.
    Tuple { span: Span, elements: Box<[usize]> },
    /// A function occurrence and its component provenance roots.
    Function {
        span: Span,
        domain: usize,
        codomain: usize,
    },
}

impl ResolvedTypeProvenance {
    /// Builds an admitted provenance arena from source-ordered nodes.
    #[must_use]
    pub(crate) fn new(nodes: Vec<ResolvedTypeProvenanceNode>, root: usize) -> Self {
        Self {
            nodes: nodes.into(),
            root,
        }
    }

    /// Returns the complete source span of this provenance view.
    #[must_use]
    pub fn span(&self) -> Option<Span> {
        self.nodes.get(self.root).map(|node| match node {
            ResolvedTypeProvenanceNode::Fact(span)
            | ResolvedTypeProvenanceNode::Tuple { span, .. }
            | ResolvedTypeProvenanceNode::Function { span, .. } => *span,
        })
    }

    /// Returns views of a function domain and codomain.
    #[must_use]
    pub fn function_parts(&self) -> Option<(Self, Self)> {
        let ResolvedTypeProvenanceNode::Function {
            domain, codomain, ..
        } = self.nodes.get(self.root)?
        else {
            return None;
        };
        Some((self.view(*domain)?, self.view(*codomain)?))
    }

    /// Returns tuple element views in source order.
    #[must_use]
    pub fn tuple_elements(&self) -> Option<Vec<Self>> {
        let ResolvedTypeProvenanceNode::Tuple { elements, .. } = self.nodes.get(self.root)? else {
            return None;
        };
        elements.iter().map(|root| self.view(*root)).collect()
    }

    fn view(&self, root: usize) -> Option<Self> {
        self.nodes.get(root)?;
        Some(Self {
            nodes: Arc::clone(&self.nodes),
            root,
        })
    }

    pub(crate) fn nodes(&self) -> &[ResolvedTypeProvenanceNode] {
        &self.nodes
    }

    pub(crate) const fn root(&self) -> usize {
        self.root
    }
}

/// One resolved global definition.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResolvedDefinition {
    /// Presentation-specific definition payload.
    pub kind: ResolvedDefinitionKind,
    /// Complete definition span.
    pub span: Span,
}

/// The closed resolved global-definition family.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ResolvedDefinitionKind {
    /// An external interface followed by an equation.
    Equational(ResolvedEquationalGlobal),
    /// An inline operational function definition.
    InlineOperational(ResolvedInlineOperationalGlobal),
}

/// A resolved equational global.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResolvedEquationalGlobal {
    /// Separately written external interface.
    pub interface: ResolvedExternalInterface,
    /// Nonempty contiguous clause group.
    pub equations: Vec<ResolvedEquation>,
    /// First clause retained while existing elaboration consumers migrate.
    pub equation: ResolvedEquation,
}

/// A resolved external interface.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResolvedExternalInterface {
    /// Global definition site.
    pub name: Binder,
    /// Declared resolved type.
    pub annotation: ResolvedType,
    /// Complete interface span.
    pub span: Span,
}

/// A resolved equation.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResolvedEquation {
    /// Repeated global name in the equation head.
    pub name: ResolvedOccurrence,
    /// Patterns consuming successive arrow domains.
    pub patterns: Vec<ResolvedPattern>,
    /// First domain binder retained while function Core migrates to patterns.
    pub binder: Binder,
    /// Resolved equation body.
    pub body: ResolvedExpr,
    /// Complete equation span.
    pub span: Span,
}

/// A resolved inline operational global.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResolvedInlineOperationalGlobal {
    /// Complete operational header.
    pub header: ResolvedInlineOperationalHeader,
    /// Resolved braced body.
    pub body: ResolvedBlock,
}

/// A resolved inline operational header.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResolvedInlineOperationalHeader {
    /// Global definition site.
    pub name: Binder,
    /// Nonempty typed operational parameter vector.
    pub parameters: Vec<ResolvedTypedPattern>,
    /// First parameter retained while existing elaboration consumers migrate.
    pub parameter: ResolvedTypedBinder,
    /// Declared result type.
    pub result_type: ResolvedType,
    /// Complete header span, excluding the body.
    pub span: Span,
}

/// A resolved binder with a source type annotation.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResolvedTypedBinder {
    /// Resolved definition site.
    pub binder: Binder,
    /// Required source type.
    pub annotation: ResolvedType,
    /// Complete typed-binder span.
    pub span: Span,
}

/// One resolved pattern with a resolved type annotation.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResolvedTypedPattern {
    /// Resolved pattern.
    pub pattern: ResolvedPattern,
    /// Required resolved type.
    pub annotation: ResolvedType,
    /// Complete source span.
    pub span: Span,
}

/// One resolved pattern.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResolvedPattern {
    /// Resolved pattern payload.
    pub kind: ResolvedPatternKind,
    /// Complete pattern span.
    pub span: Span,
}

/// The closed resolved pattern family.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ResolvedPatternKind {
    /// A stable binder definition.
    Binder(Binder),
    /// A nonbinding wildcard.
    Wildcard,
    /// A Boolean literal pattern.
    Boolean(bool),
    /// Unit.
    Unit,
    /// A structural tuple pattern.
    Tuple(Vec<ResolvedPattern>),
    /// A constructor identity and optional payload pattern.
    Constructor {
        /// Resolved constructor identity.
        constructor: ConstructorId,
        /// Original spelling and source provenance.
        occurrence: ResolvedConstructorOccurrence,
        /// Optional payload pattern.
        payload: Option<Box<ResolvedPattern>>,
    },
}

/// A resolved sequential block.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResolvedBlock {
    /// Ordered resolved local declarations.
    pub declarations: Vec<ResolvedLocalDeclaration>,
    /// Required block result expression.
    pub result: Box<ResolvedExpr>,
    /// Complete braced span.
    pub span: Span,
}

/// The closed resolved local-declaration family.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ResolvedLocalDeclaration {
    /// A sequential nonrecursive binding.
    Binding(Box<ResolvedBinding>),
    /// A simultaneous recursive function binding group.
    Recursive(ResolvedRecursiveGroup),
}

/// One resolved simultaneous recursive binding group.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResolvedRecursiveGroup {
    /// Members in source order.
    pub members: Vec<ResolvedRecursiveMember>,
    /// Complete recursive group span.
    pub span: Span,
}

/// One resolved recursive group member.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResolvedRecursiveMember {
    /// The `let rec` or `and` delimiter introducing this member.
    pub introducer_span: Span,
    /// Introduced definition site.
    pub binder: Binder,
    /// Required declared monotype.
    pub annotation: ResolvedType,
    /// Initializer resolved in the simultaneous group scope.
    pub initializer: ResolvedExpr,
    /// Complete member span.
    pub span: Span,
}

/// A resolved immutable local binding.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResolvedBinding {
    /// Introduced irrefutable pattern.
    pub pattern: ResolvedPattern,
    /// First binder retained while binding Core migrates to patterns.
    pub binder: Binder,
    /// Optional source type annotation.
    pub annotation: Option<ResolvedType>,
    /// Initializer resolved in the incoming scope.
    pub initializer: ResolvedExpr,
    /// Complete binding span.
    pub span: Span,
}

/// A resolved expression.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResolvedExpr {
    /// Resolved expression payload.
    pub kind: ResolvedExprKind,
    /// Complete expression span.
    pub span: Span,
}

/// The closed resolved expression family.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ResolvedExprKind {
    /// An arbitrary-precision integer literal.
    Integer(Integer),
    /// A Boolean literal.
    Boolean(bool),
    /// The unit value.
    Unit,
    /// A resolved name occurrence.
    Occurrence(ResolvedOccurrence),
    /// A resolved constructor term occurrence.
    Constructor(ResolvedConstructorOccurrence),
    /// A strict structural tuple.
    Tuple(Vec<ResolvedExpr>),
    /// Strict unary application.
    Apply(ResolvedApplicationExpr),
    /// Integer addition.
    Add(ResolvedBinaryExpr),
    /// Integer multiplication.
    Multiply(ResolvedBinaryExpr),
    /// Integer equality.
    Equal(ResolvedBinaryExpr),
    /// A sequential block expression.
    Block(ResolvedBlock),
    /// An anonymous unary function.
    Function(ResolvedFunctionExpr),
    /// A structured match.
    Match(ResolvedMatchExpr),
}

/// One resolved constructor occurrence.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResolvedConstructorOccurrence {
    /// Stable constructor identity.
    pub constructor: ConstructorId,
    /// Exact source spelling.
    pub spelling: String,
    /// Causal source provenance.
    pub origin: Origin,
}

/// A resolved structured match.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResolvedMatchExpr {
    /// Resolved scrutinee.
    pub scrutinee: Box<ResolvedExpr>,
    /// Source-ordered arms.
    pub arms: Vec<ResolvedMatchArm>,
}

/// One resolved match arm.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResolvedMatchArm {
    /// Resolved arm pattern.
    pub pattern: ResolvedPattern,
    /// Resolved arm body.
    pub body: ResolvedExpr,
    /// Complete arm span.
    pub span: Span,
}

/// A resolved unary application.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResolvedApplicationExpr {
    /// Resolved function position.
    pub function: Box<ResolvedExpr>,
    /// Resolved argument position.
    pub argument: Box<ResolvedExpr>,
}

/// A resolved binary expression.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResolvedBinaryExpr {
    /// Resolved left operand.
    pub left: Box<ResolvedExpr>,
    /// Resolved right operand.
    pub right: Box<ResolvedExpr>,
    /// Exact source span of the operator token.
    pub operator_span: Span,
}

/// A resolved anonymous function expression.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResolvedFunctionExpr {
    /// First binder retained while function Core migrates to patterns.
    pub parameter: Binder,
    /// Unary domain pattern.
    pub pattern: ResolvedPattern,
    /// Resolved braced body.
    pub body: ResolvedBlock,
}
