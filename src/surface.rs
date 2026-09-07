//! Recovery-free, source-spanned syntax passed from parsing to resolution.

use crate::{integer::Integer, source::Span};

/// One parsed Ash module source.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SurfaceModule {
    /// Imports in source order.
    pub imports: Vec<SurfaceImport>,
    /// Cross-family declaration order using category-local indices.
    pub declaration_order: Vec<SurfaceDeclarationIndex>,
    /// Nominal type declarations in source order.
    pub type_declarations: Vec<SurfaceTypeDeclaration>,
    /// Interface declarations in source order.
    pub interfaces: Vec<SurfaceInterfaceDeclaration>,
    /// Effect declarations in source order.
    pub effects: Vec<SurfaceEffectDeclaration>,
    /// Implementation declarations in source order.
    pub implementations: Vec<SurfaceImplementation>,
    /// Global definitions in source order.
    pub definitions: Vec<SurfaceDefinition>,
    /// The complete accepted source span.
    pub span: Span,
}

/// One source declaration's category and category-local position.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SurfaceDeclarationIndex {
    /// A nominal type declaration.
    Type(usize),
    /// An interface declaration.
    Interface(usize),
    /// An effect declaration.
    Effect(usize),
    /// A global definition.
    Global(usize),
    /// An implementation declaration.
    Implementation(usize),
}

/// One source import declaration.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SurfaceImport {
    /// Whether this targeted import re-exports its selected channels.
    pub public: bool,
    /// The relative or named-root module path.
    pub path: SurfaceModulePath,
    /// The qualified alias or targeted name and implementation channels selected by the import.
    pub selection: SurfaceImportSelection,
    /// The complete import declaration span.
    pub span: Span,
}

/// A source module path.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SurfaceModulePath {
    /// A path resolved from the importing module's directory.
    Relative(Vec<SurfaceName>),
    /// A path resolved from a configured named root.
    Absolute {
        /// The configured root name, excluding the leading `@`.
        root: SurfaceName,
        /// The nonempty path beneath the named root.
        segments: Vec<SurfaceName>,
    },
}

/// The channels selected from an import dependency.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SurfaceImportSelection {
    /// The dependency's public namespaces under one module alias.
    Qualified {
        /// The local module alias.
        alias: SurfaceName,
    },
    /// Independent selected public name and implementation channels without module qualification.
    Targeted(Vec<SurfaceImportItem>),
}

/// One selected import channel.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SurfaceImportItem {
    /// A source spelling selected from the dependency's public namespaces.
    Name {
        /// The selected dependency spelling bound in the importing source.
        name: SurfaceName,
        /// The replacement local spelling, when present.
        alias: Option<SurfaceName>,
        /// The complete selector item span.
        span: Span,
    },
    /// Public implementations selected by one dependency interface spelling.
    Implementation {
        /// The dependency interface spelling; this channel binds no source name and controls
        /// implementation availability.
        interface: SurfaceName,
        /// The complete selector item span.
        span: Span,
    },
}

/// Source visibility for one nominal type declaration.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SurfaceTypeVisibility {
    /// Neither the nominal name nor its constructors are exported.
    Private,
    /// The nominal name is exported, but its constructors are hidden.
    PublicOpaque,
    /// The nominal name and its complete constructor set are exported.
    PublicTransparent,
}

/// The source declaration kind for one nominal type declaration.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SurfaceNominalDeclarationKind {
    /// An ordinary allocating nominal data declaration.
    Data,
    /// A representation-preserving nominal declaration.
    Newtype,
}

/// One source nominal type declaration.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SurfaceTypeDeclaration {
    /// Whether this declaration is ordinary data or a representation-preserving newtype.
    pub declaration_kind: SurfaceNominalDeclarationKind,
    /// The declaration's module export mode.
    pub visibility: SurfaceTypeVisibility,
    /// The declared type spelling.
    pub name: SurfaceName,
    /// Ordered type parameters.
    pub parameters: Vec<SurfaceTypeParameter>,
    /// Its nonempty constructor list.
    pub constructors: Vec<SurfaceConstructorDeclaration>,
    /// The complete declaration span.
    pub span: Span,
}

/// One source constructor declaration.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SurfaceConstructorDeclaration {
    /// The constructor spelling.
    pub name: SurfaceName,
    /// Zero or more syntactic fields.
    pub fields: Vec<SurfaceType>,
    /// The complete constructor span.
    pub span: Span,
}

/// One method-only interface declaration.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SurfaceInterfaceDeclaration {
    /// Whether the interface and its methods are exported.
    pub public: bool,
    /// The declared interface spelling.
    pub name: SurfaceName,
    /// The interface's nonempty ordered type parameters.
    pub parameters: Box<[SurfaceTypeParameter]>,
    /// The optional source determination edge.
    pub determination: Option<SurfaceInterfaceDetermination>,
    /// The nonempty ordered method signatures.
    pub methods: Vec<SurfaceInterfaceMethod>,
    /// The complete interface declaration span.
    pub span: Span,
}

/// One optional source determination edge on an interface declaration.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SurfaceInterfaceDetermination {
    /// The determinant side before `->`.
    pub determinant: SurfaceDeterminationSide,
    /// The dependent side after `->`.
    pub dependent: SurfaceDeterminationSide,
    /// The complete `where` determination span.
    pub span: Span,
}

/// One nonempty source-ordered side of an interface determination.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SurfaceDeterminationSide {
    /// Interface-parameter names in written order.
    pub parameters: Box<[SurfaceName]>,
    /// The complete side span, including parentheses when present.
    pub span: Span,
}

/// One signature-only interface method declaration.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SurfaceInterfaceMethod {
    /// The file-wide method spelling.
    pub name: SurfaceName,
    /// The optional explicit ordered method-local type parameters.
    pub type_parameters: Option<Vec<SurfaceTypeParameter>>,
    /// The declared source value type.
    pub annotation: SurfaceType,
    /// The complete method signature span.
    pub span: Span,
}

/// One module-owned effect API declaration.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SurfaceEffectDeclaration {
    /// Whether the complete effect API is exported.
    pub public: bool,
    /// The declared effect spelling.
    pub name: SurfaceName,
    /// Ordered ordinary type parameters.
    pub parameters: Vec<SurfaceTypeParameter>,
    /// Nonempty operations in declaration order.
    pub operations: Vec<SurfaceEffectOperation>,
    /// The complete declaration span.
    pub span: Span,
}

/// One signature-only operation local to its owning effect.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SurfaceEffectOperation {
    /// The effect-local operation spelling.
    pub name: SurfaceName,
    /// The declared source value type.
    pub annotation: SurfaceType,
    /// The complete operation signature span.
    pub span: Span,
}

/// One source implementation declaration with flat method equations.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SurfaceImplementation {
    /// Whether the anonymous implementation fact is exported.
    pub public: bool,
    /// The optional complete explicit type-parameter list.
    pub type_parameters: Option<Vec<SurfaceTypeParameter>>,
    /// The complete implemented interface application.
    pub head: SurfaceInterfaceApplication,
    /// Ordered implementation prerequisites.
    pub prerequisites: Vec<SurfaceRequirement>,
    /// Flat method equations in source order.
    pub equations: Vec<SurfaceEquation>,
    /// The complete implementation declaration span.
    pub span: Span,
}

/// A source global definition and its presentation-specific payload.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SurfaceDefinition {
    /// Whether the global is exported from its defining module.
    pub public: bool,
    /// The definition presentation.
    pub kind: SurfaceDefinitionKind,
    /// The complete definition span.
    pub span: Span,
}

/// The closed Ash global-definition family.
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
    /// The nonempty contiguous clause group.
    pub equations: Vec<SurfaceEquation>,
}

/// One external name and type interface.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SurfaceExternalInterface {
    /// The declared global name.
    pub name: SurfaceName,
    /// The optional complete explicit type-parameter list.
    pub type_parameters: Option<Vec<SurfaceTypeParameter>>,
    /// The declared type.
    pub annotation: SurfaceType,
    /// Ordered explicit interface requirements.
    pub requirements: Vec<SurfaceRequirement>,
    /// The complete interface span.
    pub span: Span,
}

/// One equation head and body.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SurfaceEquation {
    /// The name repeated by the equation head.
    pub name: SurfaceName,
    /// Patterns consuming successive arrow domains.
    pub patterns: Vec<SurfacePattern>,
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
    /// The optional complete explicit type-parameter list.
    pub type_parameters: Option<Vec<SurfaceTypeParameter>>,
    /// The nonempty operational parameter vector.
    pub parameters: Vec<SurfaceTypedPattern>,
    /// The declared result type.
    pub result_type: SurfaceType,
    /// The optional explicit effect row on the result computation.
    pub result_effects: Option<SurfaceEffectRow>,
    /// Ordered explicit interface requirements.
    pub requirements: Vec<SurfaceRequirement>,
    /// The complete header span, excluding the body.
    pub span: Span,
}

/// One complete source interface application outside the ordinary type algebra.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SurfaceInterfaceApplication {
    /// The unqualified or module-qualified interface reference.
    pub interface: SurfaceReference,
    /// The nonempty ordered type arguments.
    pub arguments: Box<[SurfaceType]>,
    /// The complete interface application span.
    pub span: Span,
}

/// One explicit interface requirement outside the ordinary type algebra.
pub type SurfaceRequirement = SurfaceInterfaceApplication;

/// A source expression.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SurfaceExpr {
    /// The expression payload.
    pub kind: SurfaceExprKind,
    /// The complete expression span.
    pub span: Span,
}

/// The closed Ash expression family.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SurfaceExprKind {
    /// An arbitrary-precision integer literal.
    Integer(Integer),
    /// A Boolean literal.
    Boolean(bool),
    /// The unit value.
    Unit,
    /// An unresolved unqualified or module-qualified source name.
    Name(SurfaceReference),
    /// A strict structural tuple.
    Tuple(Vec<SurfaceExpr>),
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
    /// A structured total match.
    Match(SurfaceMatchExpr),
    /// An operation request with a primary operand.
    Perform(SurfacePerformExpr),
    /// A lexical handler for one exact effect instance.
    Handle(SurfaceHandleExpr),
    /// A resume request owned by the nearest operation clause.
    Resume(Box<SurfaceExpr>),
    /// A parsed acquisition, pending resource identity and lifetime checking.
    Resource(Box<SurfaceResourceExpr>),
    /// An empty-chain scope, pending hook API and effect checking.
    Hook(Box<SurfaceHookExpr>),
    /// A scoped transformer, pending hook API and lifetime checking.
    Registration(Box<SurfaceRegistrationExpr>),
    /// Nullary consumption of the nearest clause's captured continuation.
    Discard,
}

/// Source ownership of one builtin cell acquisition.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SurfaceResourceExpr {
    /// The uppercase rigid identity binder, scoped only over `body`.
    pub identity: SurfaceName,
    /// The ordinary handle binder, scoped only over `body`.
    pub handle: SurfaceName,
    /// The primary initializer evaluated in the preceding scope.
    pub initializer: SurfaceExpr,
    /// The block owned by this acquisition.
    pub body: SurfaceBlock,
}

/// Source ownership of one empty-chain hook scope.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SurfaceHookExpr {
    /// The exact written target; this form introduces no source binder.
    pub effect: SurfaceEffectInstance,
    /// The block owned by this scope.
    pub body: SurfaceBlock,
}

/// Source ownership of one scoped hook registration.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SurfaceRegistrationExpr {
    /// The exact written target; this form introduces no source binder.
    pub effect: SurfaceEffectInstance,
    /// The primary transformer evaluated in the preceding context.
    pub transformer: SurfaceExpr,
    /// The block executed with the registration active.
    pub body: SurfaceBlock,
}

/// One explicit source operation request.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SurfacePerformExpr {
    pub effect: SurfaceReference,
    pub arguments: Vec<SurfaceType>,
    pub operation: SurfaceName,
    pub operand: Box<SurfaceExpr>,
}

/// One lexical source handler.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SurfaceHandleExpr {
    pub body: Box<SurfaceExpr>,
    pub effect: SurfaceEffectInstance,
    pub clauses: Vec<SurfaceHandlerClause>,
}

/// One source-ordered handler operation clause.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SurfaceHandlerClause {
    pub operation: SurfaceName,
    pub pattern: SurfacePattern,
    pub body: SurfaceExpr,
    pub span: Span,
}

/// A structured match expression.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SurfaceMatchExpr {
    /// The scrutinee evaluated once.
    pub scrutinee: Box<SurfaceExpr>,
    /// Source-ordered arms.
    pub arms: Vec<SurfaceMatchArm>,
}

/// One source match arm.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SurfaceMatchArm {
    /// The arm pattern.
    pub pattern: SurfacePattern,
    /// The selected body.
    pub body: SurfaceExpr,
    /// The complete arm span.
    pub span: Span,
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
    /// Ordered local declarations.
    pub declarations: Vec<SurfaceLocalDeclaration>,
    /// The block's required result expression.
    pub result: Box<SurfaceExpr>,
    /// The complete braced span.
    pub span: Span,
}

/// The closed Ash local-declaration family.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SurfaceLocalDeclaration {
    /// Exact methods supplied to the following lexical remainder.
    Evidence(Box<SurfaceLexicalEvidence>),
    /// A sequential nonrecursive binding.
    Binding(Box<SurfaceBinding>),
    /// A simultaneous recursive binding group.
    Recursive(SurfaceRecursiveGroup),
    /// A private nominal representation declaration.
    Newtype(SurfaceTypeDeclaration),
}

/// One sequential exact interface evidence declaration.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SurfaceLexicalEvidence {
    /// Complete interface application.
    pub application: SurfaceInterfaceApplication,
    /// Supplied equations in source order.
    pub equations: Vec<SurfaceEquation>,
    /// Complete declaration span.
    pub span: Span,
}

/// One simultaneous local recursive binding group.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SurfaceRecursiveGroup {
    /// Members in source order.
    pub members: Vec<SurfaceRecursiveMember>,
    /// The complete group from `let` through its final initializer.
    pub span: Span,
}

/// One source member of a recursive binding group.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SurfaceRecursiveMember {
    /// The `let rec` or `and` delimiter introducing this member.
    pub introducer_span: Span,
    /// The introduced binder.
    pub binder: SurfaceBinder,
    /// The required declared monotype.
    pub annotation: SurfaceType,
    /// The initializer expression.
    pub initializer: SurfaceExpr,
    /// The member from its binder through its initializer.
    pub span: Span,
}

/// One immutable local binding.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SurfaceBinding {
    /// The irrefutable source pattern.
    pub pattern: SurfacePattern,
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
    /// The unary domain pattern; comma syntax forms one tuple pattern.
    pub parameter: SurfacePattern,
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

/// One declaration-level source type parameter.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SurfaceTypeParameter {
    /// The source spelling and exact name span.
    pub name: SurfaceName,
    /// The optional explicit kind annotation.
    pub kind: Option<SurfaceKind>,
    /// The complete parameter span, including its annotation when present.
    pub span: Span,
}

/// One source kind.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SurfaceKind {
    /// The kind payload.
    pub kind: SurfaceKindKind,
    /// The complete kind span, including grouping delimiters when present.
    pub span: Span,
}

/// The closed source kind family.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SurfaceKindKind {
    /// The kind of ordinary value types.
    Type,
    /// The kind of computation effect rows.
    EffectRow,
    /// A right-associated kind function.
    Function {
        /// The argument kind.
        domain: Box<SurfaceKind>,
        /// The result kind.
        codomain: Box<SurfaceKind>,
    },
}

/// An unresolved source reference, with qualification retained structurally.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SurfaceReference {
    /// A name resolved in the current lexical and imported namespaces.
    Unqualified(SurfaceName),
    /// A member selected through one imported module alias.
    Qualified(SurfaceQualifiedName),
}

impl SurfaceReference {
    /// Returns the referenced member spelling.
    #[must_use]
    pub const fn member(&self) -> &SurfaceName {
        match self {
            Self::Unqualified(name) => name,
            Self::Qualified(name) => &name.member,
        }
    }

    /// Returns the module alias for a qualified reference.
    #[must_use]
    pub const fn qualifier(&self) -> Option<&SurfaceName> {
        match self {
            Self::Unqualified(_) => None,
            Self::Qualified(name) => Some(&name.qualifier),
        }
    }

    /// Returns the complete reference span.
    #[must_use]
    pub const fn span(&self) -> Span {
        match self {
            Self::Unqualified(name) => name.span,
            Self::Qualified(name) => name.span,
        }
    }
}

/// One module-qualified source reference.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SurfaceQualifiedName {
    /// The imported module alias before the dot.
    pub qualifier: SurfaceName,
    /// The selected member after the dot.
    pub member: SurfaceName,
    /// The complete qualifier, dot, and member span.
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

/// One pattern with a source type annotation.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SurfaceTypedPattern {
    /// The source pattern.
    pub pattern: SurfacePattern,
    /// Its required type.
    pub annotation: SurfaceType,
    /// The complete typed-pattern span.
    pub span: Span,
}

/// One source pattern and its complete span.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SurfacePattern {
    /// The pattern payload.
    pub kind: SurfacePatternKind,
    /// The complete pattern span.
    pub span: Span,
}

/// The closed source pattern family.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SurfacePatternKind {
    /// An ordinary binding pattern.
    Binder(SurfaceBinder),
    /// A nonbinding wildcard.
    Wildcard,
    /// A Boolean literal pattern.
    Boolean(bool),
    /// The unit pattern.
    Unit,
    /// A structural tuple pattern.
    Tuple(Vec<SurfacePattern>),
    /// A nominal constructor pattern with an optional semantic payload.
    Constructor {
        /// The unresolved unqualified or module-qualified constructor reference.
        name: SurfaceReference,
        /// Its optional payload pattern.
        payload: Option<Box<SurfacePattern>>,
    },
}

/// A source type.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SurfaceType {
    /// The type payload.
    pub kind: SurfaceTypeKind,
    /// The complete accepted type span.
    pub span: Span,
}

/// The closed Ash type family.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SurfaceTypeKind {
    /// Arbitrary-precision integers.
    Int,
    /// Boolean values.
    Bool,
    /// The unit value.
    Unit,
    /// An unresolved unqualified or module-qualified nominal type reference.
    Named(SurfaceReference),
    /// A named type constructor applied to one or more arguments.
    Application {
        /// The unqualified or module-qualified type-constructor reference.
        constructor: SurfaceReference,
        /// Nonempty arguments in source order.
        arguments: Vec<SurfaceType>,
    },
    /// A structural tuple with at least two elements.
    Tuple(Vec<SurfaceType>),
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
    /// The explicitly written latent row on this codomain, when present.
    pub effects: Option<SurfaceEffectRow>,
}

/// One written effect row on a computation codomain.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SurfaceEffectRow {
    /// Known effect instances in source order.
    pub effects: Vec<SurfaceEffectInstance>,
    /// The optional open tail parameter.
    pub tail: Option<SurfaceName>,
    /// The complete braced row span.
    pub span: Span,
}

/// One unresolved effect instance and its ordinary type arguments.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SurfaceEffectInstance {
    /// The unqualified or module-qualified effect reference.
    pub effect: SurfaceReference,
    /// Ordered written arguments.
    pub arguments: Vec<SurfaceType>,
    /// The complete instance span.
    pub span: Span,
}
