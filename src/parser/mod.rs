//! Event-producing recursive-descent parsing and checked surface projection.

#[cfg(test)]
mod checkpoint_tests;
mod cst;
mod event;
mod expression;
mod grammar;
mod project;

use std::fmt;
use std::ops::Deref;

pub use crate::syntax_resource::{ResourceFailure, SYNTAX_WORK_LIMIT};
pub use cst::{ConcreteElement, ConcreteNode, ConcreteTree, InternalReason};
pub use event::Event;
#[cfg(test)]
pub(crate) use project::G1_CAPTURE_OBSERVER;
pub(crate) use project::module_span_from_checkpoint;
#[cfg(test)]
pub(crate) use project::project_declaration_expansions;
#[allow(unused_imports)]
pub(crate) use project::project_declaration_invocation;
pub(crate) use project::project_module_header;
#[cfg(test)]
pub(crate) use project::project_module_retaining_templates;
pub(crate) use project::structural_weight as source_structural_weight;
pub(crate) use project::{
    DeclarationExpansionFailure, QuoteProjection, project_declaration_expansions_with_quotes,
};
pub use project::{ProjectionError, project_module};

use crate::{
    diagnostic::{Diagnostic, SourceLabel},
    lexer::{Lexed, TokenKind},
    source::{SourceFile, Span},
    surface::SurfaceImport,
    syntax_resource::SyntaxBudget,
};

/// Conservative, replaceable protection for source structural nesting.
///
/// Groups, parenthesized types, arrows, operators/application, blocks, and
/// functions contribute. Fixed concrete scaffolding such as program, global,
/// interface, `Type`, and `AtomicType` wrappers does not. This is an
/// implementation resource budget, not an Ash language nesting restriction;
/// later fully iterative representations may replace it.
pub const STRUCTURAL_DEPTH_LIMIT: usize = 128;

pub(super) const PATTERN_STRUCTURAL_WEIGHT: usize = 8;
pub(super) const MATCH_STRUCTURAL_WEIGHT: usize = 32;

/// The grammar role of one concrete node.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum NodeKind {
    /// A complete declarations-only module source.
    Module,
    /// One source import declaration.
    ImportDeclaration,
    /// A relative or named-root dotted module path.
    ModulePath,
    /// One selected public spelling and its optional local alias.
    ImportItem,
    /// One public syntax declaration.
    SyntaxDeclaration,
    /// One named syntax capture or fixed subject-name binding.
    SyntaxCapture,
    /// The complete matcher in an extended declaration syntax header.
    SyntaxMatcherSequence,
    /// A parenthesized or braced matcher group.
    SyntaxMatcherGroup,
    /// A matcher repetition and its operator.
    SyntaxMatcherRepeat,
    /// A matched group in a declaration syntax invocation.
    SyntaxMatchedGroup,
    /// A matched repetition in a declaration syntax invocation.
    SyntaxMatchedRepeat,
    /// One iteration of a matched repetition.
    SyntaxMatchedIteration,
    /// The balanced token contents of an expression syntax template.
    TemplateBody,
    /// One imported expression syntax invocation.
    SyntaxInvocation,
    /// One imported declaration syntax invocation, awaiting expansion.
    DeclarationSyntaxInvocation,
    /// One protected declaration fragment at a module declaration boundary.
    DeclarationFragment,
    /// One identifier or expression captured by an invocation.
    SyntaxArgument,
    /// One passive source-authored foreign library.
    ForeignLibrary,
    /// One structured foreign member.
    ForeignMember,

    /// A nominal type declaration.
    TypeDeclaration,
    /// A representation-preserving nominal declaration.
    NewtypeDeclaration,
    /// A written deriving clause awaiting consumption with its subject.
    DerivingClause,
    /// One nonempty declaration-level type-parameter list.
    TypeParameters,
    /// One declaration-level type parameter and its optional kind annotation.
    TypeParameter,
    /// One constructor declaration under a nominal type.
    ConstructorDeclaration,
    /// A method-only interface declaration.
    InterfaceDeclaration,
    /// One module-owned effect API declaration.
    EffectDeclaration,
    /// One signature-only effect operation.
    EffectOperation,
    /// One signature-only method in an interface.
    InterfaceMethod,
    /// One trailing nonempty `where` clause.
    WhereClause,
    /// One interface reference applied to its single type argument.
    InterfaceApplication,
    /// One implementation declaration with flat method equations.
    ImplementationDeclaration,
    /// A sequential exact evidence declaration.
    LexicalEvidenceDeclaration,
    /// An equational global definition.
    EquationalGlobal,
    /// An external name and type interface.
    ExternalInterface,
    /// An equation head and body.
    Equation,
    /// An inline operational global definition.
    InlineOperationalGlobal,
    /// The source header of an inline operational global.
    InlineOperationalHeader,
    /// A braced sequential expression.
    Block,
    /// A local immutable binding.
    LocalBinding,
    /// A simultaneous local recursive binding group.
    RecursiveBindingGroup,
    /// One member of a recursive binding group.
    RecursiveBindingMember,
    /// An anonymous function expression.
    FunctionExpression,
    /// A structured match expression.
    MatchExpression,
    /// A lexical effect handler expression.
    HandlerExpression,
    /// One handler operation clause.
    HandlerClause,
    /// A loose-prefix resume expression.
    ResumeExpression,
    /// One builtin cell acquisition with an identity binder and scoped body.
    ResourceExpression,
    /// One lexical region owner with an optional explicit allocator pair.
    RegionExpression,
    /// Selection of an existing live allocation owner.
    RegionSelectionExpression,
    /// A module-owned experimental resource assembly.
    ResourceDefinition,
    /// Experimental assembly field or clause block.
    ResourceField,
    /// One optional declaration-level resource family template.
    ResourceFamily,
    /// One qualified resource acquisition with a scoped identity binder.
    ProviderResourceExpression,
    /// An empty-chain hook scope with an exact effect target and block body.
    HookExpression,
    /// A registration with an exact target, primary transformer, and block body.
    RegistrationExpression,
    /// A cleanup action expression followed by its owned block body.
    CleanupExpression,
    /// A primary-precedence operation request.
    PerformExpression,
    /// One effect-qualified operation reference.
    OperationReference,
    /// One line-delimited match arm.
    MatchArm,
    /// The non-associative equality layer.
    EqualityExpression,
    /// The additive layer.
    AdditiveExpression,
    /// The multiplicative layer.
    MultiplicativeExpression,
    /// The juxtaposed-application layer.
    ApplicationExpression,
    /// An integer, Boolean, name, unit, or grouped expression.
    PrimaryExpression,
    /// A grouped expression.
    ParenthesizedExpression,
    /// A structural tuple expression.
    TupleExpression,
    /// One expression quote and its delimited expression syntax.
    SyntaxQuote,
    /// One executable escape and its ordinary Ash block.
    SyntaxEscape,
    /// A splice owned by the enclosing macro template.
    TemplateSplice,
    /// A lexical macro-capture read inside escaped code.
    EscapeCaptureRead,
    /// An ordinary variable hole inside an expression quote.
    QuoteHole,
    /// A typed or untyped binding pattern.
    Pattern,
    /// A parenthesized structural tuple pattern.
    TuplePattern,
    /// A nominal constructor pattern.
    ConstructorPattern,
    /// A wildcard pattern.
    WildcardPattern,
    /// A Boolean pattern.
    BooleanPattern,
    /// The unit pattern.
    UnitPattern,
    /// A binder-only source form.
    Binder,
    /// A binder with a type annotation.
    TypedBinder,
    /// A pattern with a type annotation.
    TypedPattern,
    /// A right-associated type.
    Type,
    /// One written closed or open effect row.
    EffectRow,
    /// One effect instance in a written row.
    EffectInstance,
    /// A right-associated kind.
    Kind,
    /// A grouped kind.
    ParenthesizedKind,
    /// An atomic type.
    AtomicType,
    /// A grouped type.
    ParenthesizedType,
    /// A structural tuple type.
    TupleType,
    /// A module-qualified type or constructor occurrence.
    QualifiedName,
    /// Rejected syntax retained until projection fails.
    Error,
}

/// A grammar form that was required at a recovery point.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ExpectedForm {
    /// A final or nested expression.
    Expression,
    /// An expression operand.
    Operand,
    /// A source identifier.
    Identifier,
    /// A source type.
    Type,
    /// An effect row.
    EffectRow,
    /// A source kind.
    Kind,
    /// A source pattern.
    Pattern,
    /// One interface type parameter.
    InterfaceParameter,
    /// A signature-only interface method.
    InterfaceMethod,
    /// A signature-only operation in an effect declaration.
    EffectOperation,
    /// An interface application in a constraint or impl head.
    InterfaceApplication,
    /// An implementation method equation.
    ImplementationMethod,
    /// `,`.
    Comma,
    /// `(`.
    LeftParen,
    /// `)`.
    RightParen,
    /// `{`.
    LeftBrace,
    /// `}`.
    RightBrace,
    /// `>`.
    Greater,
    /// `:`.
    Colon,
    /// `=`.
    Equal,
    /// `->`.
    Arrow,
    /// `=>`.
    FatArrow,
    /// A logical line boundary.
    LineEnd,
    /// End of input.
    EndOfFile,
}

impl ExpectedForm {
    /// Stable grammar category retained independently of localized wording.
    pub(crate) const fn diagnostic_name(self) -> &'static str {
        match self {
            Self::Expression => "expression",
            Self::Operand => "operand",
            Self::Identifier => "identifier",
            Self::Type => "type",
            Self::EffectRow => "effect-row",
            Self::Kind => "kind",
            Self::Pattern => "pattern",
            Self::InterfaceParameter => "interface-parameter",
            Self::InterfaceMethod => "interface-method",
            Self::EffectOperation => "effect-operation",
            Self::InterfaceApplication => "interface-application",
            Self::ImplementationMethod => "implementation-method",
            Self::Comma => "comma",
            Self::LeftParen => "left-paren",
            Self::RightParen => "right-paren",
            Self::LeftBrace => "left-brace",
            Self::RightBrace => "right-brace",
            Self::Greater => "greater",
            Self::Colon => "colon",
            Self::Equal => "equal",
            Self::Arrow => "arrow",
            Self::FatArrow => "fat-arrow",
            Self::LineEnd => "line-end",
            Self::EndOfFile => "end-of-file",
        }
    }
}

/// A parser-owned reason retained independently from rendering.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ParseReason {
    /// A grammar form was absent.
    ExpectedForm,
    /// An operand was absent after an operator.
    ExpectedOperand,
    /// A parenthesized expression, type, or kind was not closed.
    UnclosedGroup,
    /// Equality was repeated despite being non-associative.
    RepeatedEquality,
    /// A recursive delimiter is not followed by a member.
    ExpectedRecursiveMember,
    /// `and` appears outside a recursive binding group.
    UnexpectedAnd,
    /// Semicolons are excluded from this increment.
    Semicolon,
    /// Tokens remain where the selected grammar requires another boundary.
    UnexpectedToken,
    /// A template splice names no capture in its matcher.
    UnknownTemplateCapture,
    /// A template repetition has no repeated capture at its scope.
    RepetitionMissingDriver,
    /// Repetition drivers have different lengths in the current iteration.
    RepetitionLengthMismatch,
    /// A one-or-more template repetition received an empty driver.
    RepetitionEmpty,
    /// A matcher repetition can meet its following syntax in two ways.
    MatcherRepetitionAmbiguous,
    /// A one-or-more matcher repetition has no first iteration.
    MatcherRepetitionEmpty,
    /// A matcher separator is not followed by another iteration.
    MatcherTrailingSeparator,
}

/// A parser recovery fact retained independently from rendered prose.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ParseContext {
    /// Recovery synchronized at an owning grammar boundary.
    Synchronization {
        /// The kind of grammar boundary used for synchronization.
        boundary: SynchronizationBoundary,
        /// The exact boundary token span.
        span: Span,
    },
}

/// A grammar boundary used to resume parsing after a local failure.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SynchronizationBoundary {
    /// A logical line boundary owned by an equation or binding.
    LogicalLineEnd,
    /// A comma separating declaration-level type parameters.
    TypeParameterSeparator,
    /// The closing `>` of a declaration-level type-parameter list.
    TypeParameterListClosing,
    /// The `=` following a nominal declaration's type parameters.
    TypeDeclarationEqual,
    /// The `:` following an equational global's type parameters.
    EquationalGlobalColon,
    /// The `:` following an interface method's type parameters.
    InterfaceMethodColon,
    /// The `(` following an operational global's type parameters.
    OperationalParameterOpeningParen,
    /// The interface application following an implementation's type parameters.
    ImplementationInterfaceHead,
    /// The opening brace owned by an interface declaration.
    InterfaceBodyOpeningBrace,
    /// The opening brace owned by an implementation declaration.
    ImplementationBodyOpeningBrace,
    /// The opening brace owned by an operational global.
    OperationalBodyOpeningBrace,
    /// The closing brace owned by the current block.
    BlockClosingBrace,
    /// The closing brace owned by the current interface declaration.
    InterfaceClosingBrace,
    /// The closing brace owned by the current implementation declaration.
    ImplementationClosingBrace,
    /// The closing parenthesis owned by the current grouped expression.
    ParenthesisClosing,
    /// End of input owned by the current module or incomplete nested form.
    EndOfFile,
}

impl SynchronizationBoundary {
    pub(crate) const fn diagnostic_name(self) -> &'static str {
        match self {
            Self::LogicalLineEnd => "logical-line-end",
            Self::TypeParameterSeparator => "type-parameter-separator",
            Self::TypeParameterListClosing => "type-parameter-list-closing",
            Self::TypeDeclarationEqual => "type-declaration-equal",
            Self::EquationalGlobalColon => "equational-global-colon",
            Self::InterfaceMethodColon => "interface-method-colon",
            Self::OperationalParameterOpeningParen => "operational-parameter-opening-paren",
            Self::ImplementationInterfaceHead => "implementation-interface-head",
            Self::InterfaceBodyOpeningBrace => "interface-body-opening-brace",
            Self::ImplementationBodyOpeningBrace => "implementation-body-opening-brace",
            Self::OperationalBodyOpeningBrace => "operational-body-opening-brace",
            Self::BlockClosingBrace => "block-closing-brace",
            Self::InterfaceClosingBrace => "interface-closing-brace",
            Self::ImplementationClosingBrace => "implementation-closing-brace",
            Self::ParenthesisClosing => "parenthesis-closing",
            Self::EndOfFile => "end-of-file",
        }
    }
}

/// One structured parser diagnostic and its parser-specific recovery facts.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ParseDiagnostic {
    diagnostic: Diagnostic<ParseReason>,
    expected_form: Option<ExpectedForm>,
    found_token: Option<FoundToken>,
    recovery_position: Option<Span>,
    /// Structured completion or synchronization facts.
    pub context: Vec<ParseContext>,
}

impl ParseDiagnostic {
    fn new(
        diagnostic: Diagnostic<ParseReason>,
        expected_form: Option<ExpectedForm>,
        found_token: Option<FoundToken>,
        recovery_position: Option<Span>,
    ) -> Self {
        Self {
            diagnostic,
            expected_form,
            found_token,
            recovery_position,
            context: Vec::new(),
        }
    }

    /// Returns the required grammar form, independently of legacy wording.
    #[must_use]
    pub const fn expected_form(&self) -> Option<ExpectedForm> {
        self.expected_form
    }

    /// Returns the encountered token category or fixed source spelling.
    #[must_use]
    pub const fn found_token(&self) -> Option<FoundToken> {
        self.found_token
    }

    /// Returns the immediate recovery position, not a later synchronization.
    #[must_use]
    pub const fn recovery_position(&self) -> Option<Span> {
        self.recovery_position
    }
}

/// A token description that separates grammar categories from Ash spellings.
/// No identifier or literal payload is copied into this diagnostic fact.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum FoundToken {
    /// An ordinary identifier.
    Identifier,
    /// An uppercase identifier.
    UpperIdentifier,
    /// An integer literal.
    Integer,
    /// An experimental string literal; the payload remains in the token.
    StringLiteral,
    /// Fixed punctuation, keyword or builtin type spelling.
    Spelling(&'static str),
    /// A logical line boundary.
    LineEnd,
    /// End of input.
    EndOfFile,
}

impl FoundToken {
    /// Grammar category or fixed Ash spelling, never an English description.
    pub(crate) const fn diagnostic_name(self) -> &'static str {
        match self {
            Self::Identifier => "identifier",
            Self::UpperIdentifier => "uppercase-identifier",
            Self::Integer => "integer",
            Self::StringLiteral => "string-literal",
            Self::Spelling(spelling) => spelling,
            Self::LineEnd => "line-end",
            Self::EndOfFile => "end-of-file",
        }
    }
}

impl Deref for ParseDiagnostic {
    type Target = Diagnostic<ParseReason>;

    fn deref(&self) -> &Self::Target {
        &self.diagnostic
    }
}

impl fmt::Display for ParseReason {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(match self {
            Self::ExpectedForm => "parse.expected-form",
            Self::ExpectedOperand => "parse.expected-operand",
            Self::UnclosedGroup => "parse.unclosed-group",
            Self::RepeatedEquality => "parse.repeated-equality",
            Self::ExpectedRecursiveMember => "parse.expected-recursive-member",
            Self::UnexpectedAnd => "parse.unexpected-and",
            Self::Semicolon => "parse.semicolon",
            Self::UnexpectedToken => "parse.unexpected-token",
            Self::UnknownTemplateCapture => "parse.unknown-template-capture",
            Self::RepetitionMissingDriver => "parse.repetition-missing-driver",
            Self::RepetitionLengthMismatch => "parse.repetition-length-mismatch",
            Self::RepetitionEmpty => "parse.repetition-empty",
            Self::MatcherRepetitionAmbiguous => "parse.matcher-repetition-ambiguous",
            Self::MatcherRepetitionEmpty => "parse.matcher-repetition-empty",
            Self::MatcherTrailingSeparator => "parse.matcher-trailing-separator",
        })
    }
}

impl ParseDiagnostic {
    pub(crate) fn message(&self) -> Option<crate::message::Message<'_>> {
        use crate::message::Message;
        Some(match self.reason {
            ParseReason::ExpectedForm => Message::parse_expected(self.expected_form?),
            ParseReason::ExpectedOperand => Message::parse_operand(),
            ParseReason::UnclosedGroup => Message::parse_unclosed_group(),
            ParseReason::RepeatedEquality => Message::parse_repeated_equality(),
            ParseReason::ExpectedRecursiveMember => Message::parse_recursive_member(),
            ParseReason::UnexpectedAnd => Message::parse_unexpected_and(),
            ParseReason::Semicolon => Message::parse_semicolon(),
            ParseReason::UnexpectedToken => Message::parse_unexpected_token(),
            ParseReason::UnknownTemplateCapture => {
                Message::parse_unknown_template_capture(self.found.as_deref()?)
            }
            ParseReason::RepetitionMissingDriver => Message::parse_repetition_missing_driver(),
            ParseReason::RepetitionLengthMismatch => Message::parse_repetition_length_mismatch(),
            ParseReason::RepetitionEmpty => Message::parse_repetition_empty(),
            ParseReason::MatcherRepetitionAmbiguous => {
                Message::parse_matcher_repetition_ambiguous()
            }
            ParseReason::MatcherRepetitionEmpty => Message::parse_matcher_repetition_empty(),
            ParseReason::MatcherTrailingSeparator => Message::parse_matcher_trailing_separator(),
        })
    }

    pub(crate) const fn primary_relationship(&self) -> &'static str {
        match self.diagnostic.reason {
            ParseReason::ExpectedForm => "expected_form",
            ParseReason::ExpectedOperand => "operator",
            ParseReason::UnclosedGroup => "opening_group",
            ParseReason::RepeatedEquality => "repeated_equality",
            ParseReason::ExpectedRecursiveMember => "expected_recursive_member",
            ParseReason::UnknownTemplateCapture => "unknown_template_capture",
            ParseReason::RepetitionMissingDriver => "repetition_missing_driver",
            ParseReason::RepetitionLengthMismatch => "repetition_length_mismatch",
            ParseReason::RepetitionEmpty => "repetition_empty",
            ParseReason::MatcherRepetitionAmbiguous => "matcher_repetition_ambiguous",
            ParseReason::MatcherRepetitionEmpty => "matcher_repetition_empty",
            ParseReason::MatcherTrailingSeparator => "matcher_trailing_separator",
            ParseReason::UnexpectedAnd | ParseReason::Semicolon | ParseReason::UnexpectedToken => {
                "unexpected_token"
            }
        }
    }
}

/// Parses one complete lexer result into an error-bearing concrete tree.
///
/// Template bodies are retained as balanced syntax. Their contents are parsed
/// after capture substitution, when the relevant syntax imports are known.
#[must_use]
pub fn parse(lexed: Lexed) -> ConcreteTree {
    let (tokens, lexical_diagnostics, syntax_budget, lexical_resource_failure) = lexed.into_parts();
    parse_parts(
        tokens,
        lexical_diagnostics,
        syntax_budget,
        lexical_resource_failure,
    )
    .0
}

pub(crate) fn parse_with_budget(lexed: Lexed, syntax_budget: &mut SyntaxBudget) -> ConcreteTree {
    let (tokens, lexical_diagnostics, _, lexical_resource_failure) = lexed.into_parts();
    let (tree, retained_budget) = parse_parts(
        tokens,
        lexical_diagnostics,
        syntax_budget.clone(),
        lexical_resource_failure,
    );
    *syntax_budget = retained_budget;
    tree
}

pub(crate) fn parse_with_budget_and_header(
    source: &SourceFile,
    lexed: Lexed,
    syntax_budget: &mut SyntaxBudget,
) -> (ConcreteTree, Result<Vec<SurfaceImport>, ProjectionError>) {
    let (tokens, lexical_diagnostics, _, lexical_failure) = lexed.into_parts();
    if let Some(failure) = lexical_failure {
        return (
            cst::resource_limited(tokens, lexical_diagnostics, Vec::new(), failure),
            Err(ProjectionError::ResourceLimit(failure)),
        );
    }
    let (checkpoint, retained_budget) =
        parse_module_header(tokens, lexical_diagnostics, syntax_budget.clone());
    let imports = project_module_header(source, &checkpoint);
    let (tree, retained_budget) = finish_module_from_checkpoint(checkpoint, retained_budget);
    *syntax_budget = retained_budget;
    (tree, imports)
}

/// Parser-issued token order for one generated declaration. These coordinates
/// are separate from the diagnostic origins supplied for generated syntax.
#[derive(Debug, Eq, PartialEq)]
pub(crate) struct ParsedParameterOrder {
    invocation: Span,
    occurrence_extent: bool,
    declaration: std::ops::Range<usize>,
    name: crate::surface::SurfaceName,
    span: Span,
    parameters: Box<[ParsedParameterOccurrence]>,
}

#[derive(Debug, Eq, PartialEq)]
pub(crate) struct ParsedParameterOccurrence {
    name: crate::surface::SurfaceName,
    tokens: std::ops::Range<usize>,
}

impl ParsedParameterOrder {
    pub(crate) fn invocation(&self) -> Span {
        self.invocation
    }
    pub(crate) fn occurrence_extent(&self) -> bool {
        self.occurrence_extent
    }
    pub(crate) fn declaration(&self) -> &std::ops::Range<usize> {
        &self.declaration
    }
    pub(crate) fn name(&self) -> &crate::surface::SurfaceName {
        &self.name
    }
    pub(crate) fn span(&self) -> Span {
        self.span
    }
    pub(crate) fn parameters(&self) -> &[ParsedParameterOccurrence] {
        &self.parameters
    }
}

impl ParsedParameterOccurrence {
    pub(crate) fn name(&self) -> &crate::surface::SurfaceName {
        &self.name
    }
    pub(crate) fn tokens(&self) -> &std::ops::Range<usize> {
        &self.tokens
    }
}

/// A failure while parsing a transformer result with protected fragments.
#[derive(Clone, Debug)]
pub(crate) enum MacroParseFailure {
    Syntax {
        diagnostics: Vec<ParseDiagnostic>,
        resource: Option<ResourceFailure>,
    },
    Invalid,
}

pub(crate) fn repetition_failure(reason: ParseReason, span: Span) -> MacroParseFailure {
    let diagnostic = Diagnostic::new(reason, SourceLabel::new(span, primary_message(reason)));
    MacroParseFailure::Syntax {
        diagnostics: vec![ParseDiagnostic::new(diagnostic, None, None, None)],
        resource: None,
    }
}

pub(crate) const UNKNOWN_TEMPLATE_CAPTURE_LABEL: &str =
    "the template splice has no matching capture";

pub(crate) fn unknown_template_capture(name: &crate::surface::SurfaceName) -> MacroParseFailure {
    let reason = ParseReason::UnknownTemplateCapture;
    let primary = SourceLabel::new(name.span, primary_message(reason))
        .with_location_preserving_span(name.diagnostic.as_deref());
    let mut diagnostic = Diagnostic::new(reason, primary);
    diagnostic.found = Some(format!("${}", name.text));
    MacroParseFailure::Syntax {
        diagnostics: vec![ParseDiagnostic::new(diagnostic, None, None, None)],
        resource: None,
    }
}

// The expansion path will connect this syntax-only handoff separately.
#[allow(dead_code)]
pub(crate) fn parse_macro_declarations(
    source: &SourceFile,
    invocation: Span,
    construction: Option<(Span, usize)>,
    output: Vec<crate::syntax::MacroOutputNode>,
    contexts: &crate::syntax::SyntaxContexts,
    frame: Option<&std::sync::Arc<crate::syntax::ExpansionFrame>>,
) -> Result<crate::surface::SurfaceModule, MacroParseFailure> {
    parse_macro_declarations_inner(
        source,
        invocation,
        construction,
        output,
        contexts,
        &[],
        frame,
    )
}

pub(crate) fn parse_declaration_template_admission(
    source: &SourceFile,
    invocation: Span,
    output: Vec<crate::syntax::MacroOutputNode>,
    contexts: &crate::syntax::SyntaxContexts,
    placeholders: &[crate::surface::SurfaceName],
    budget: &mut SyntaxBudget,
) -> Result<(), MacroParseFailure> {
    parse_declaration_template_admission_inner(
        source,
        invocation,
        output,
        contexts,
        placeholders,
        MacroOutputPosition::StagedDeclarations,
        budget,
    )
}

pub(crate) fn parse_quote_declaration_template_admission(
    source: &SourceFile,
    invocation: Span,
    output: Vec<crate::syntax::MacroOutputNode>,
    contexts: &crate::syntax::SyntaxContexts,
    placeholders: &[crate::surface::SurfaceName],
    budget: &mut SyntaxBudget,
) -> Result<(), MacroParseFailure> {
    parse_declaration_template_admission_inner(
        source,
        invocation,
        output,
        contexts,
        placeholders,
        MacroOutputPosition::QuoteTemplateAdmission,
        budget,
    )
}

fn parse_declaration_template_admission_inner(
    source: &SourceFile,
    invocation: Span,
    output: Vec<crate::syntax::MacroOutputNode>,
    contexts: &crate::syntax::SyntaxContexts,
    placeholders: &[crate::surface::SurfaceName],
    position: MacroOutputPosition,
    budget: &mut SyntaxBudget,
) -> Result<(), MacroParseFailure> {
    let parsed = parse_macro_tree_inner(
        source,
        invocation,
        output,
        contexts,
        placeholders,
        position,
        budget,
    )?;
    project::validate_declaration_template(source, invocation, &parsed, contexts, budget).map_err(
        |failure| match failure {
            project::DeclarationExpansionFailure::Syntax {
                diagnostics,
                resource,
            } => MacroParseFailure::Syntax {
                diagnostics,
                resource,
            },
            project::DeclarationExpansionFailure::Projection(ProjectionError::ResourceLimit(
                resource,
            )) => macro_resource_failure(resource),
            project::DeclarationExpansionFailure::Projection(_) => MacroParseFailure::Invalid,
        },
    )
}

fn parse_macro_declarations_inner(
    source: &SourceFile,
    invocation: Span,
    construction: Option<(Span, usize)>,
    output: Vec<crate::syntax::MacroOutputNode>,
    contexts: &crate::syntax::SyntaxContexts,
    placeholders: &[crate::surface::SurfaceName],
    frame: Option<&std::sync::Arc<crate::syntax::ExpansionFrame>>,
) -> Result<crate::surface::SurfaceModule, MacroParseFailure> {
    let parsed = parse_macro_tree(
        source,
        invocation,
        output,
        contexts,
        placeholders,
        MacroOutputPosition::Declarations,
    )?;
    project::project_macro_declarations(
        source,
        invocation,
        construction,
        &parsed.tree,
        &parsed.original_nodes,
        &parsed.admission_identifiers,
        frame,
    )
    .map_err(|_| MacroParseFailure::Invalid)
}

pub(crate) fn parse_macro_expression(
    source: &SourceFile,
    invocation: Span,
    construction: Option<(Span, usize)>,
    output: Vec<crate::syntax::MacroOutputNode>,
    contexts: &crate::syntax::SyntaxContexts,
    frame: Option<&std::sync::Arc<crate::syntax::ExpansionFrame>>,
) -> Result<crate::surface::SurfaceExpr, MacroParseFailure> {
    parse_macro_expression_inner(
        source,
        invocation,
        construction,
        output,
        contexts,
        &[],
        frame,
    )
}

pub(crate) fn parse_macro_expression_budgeted(
    source: &SourceFile,
    invocation: Span,
    construction: Option<(Span, usize)>,
    output: Vec<crate::syntax::MacroOutputNode>,
    contexts: &crate::syntax::SyntaxContexts,
    frame: Option<&std::sync::Arc<crate::syntax::ExpansionFrame>>,
    budget: &mut SyntaxBudget,
) -> Result<crate::surface::SurfaceExpr, MacroParseFailure> {
    let parsed = parse_macro_tree_with_expression_scratch(
        source,
        invocation,
        output,
        contexts,
        &[],
        MacroOutputPosition::Expression,
        false,
        true,
        budget,
    )?;
    project::project_macro_expression_budgeted(
        source,
        invocation,
        construction,
        &parsed,
        contexts,
        frame,
        0,
        budget,
        None,
    )
    .map_err(|failure| match failure {
        project::DeclarationExpansionFailure::Syntax {
            diagnostics,
            resource,
        } => MacroParseFailure::Syntax {
            diagnostics,
            resource,
        },
        project::DeclarationExpansionFailure::Projection(ProjectionError::ResourceLimit(
            resource,
        )) => macro_resource_failure(resource),
        project::DeclarationExpansionFailure::Projection(_) => MacroParseFailure::Invalid,
    })
}

// Reproject real output tokens with the admitted quote owner and graph counter.
#[allow(clippy::too_many_arguments)]
pub(crate) fn parse_macro_expression_with_quotes(
    source: &SourceFile,
    invocation: Span,
    output: Vec<crate::syntax::MacroOutputNode>,
    contexts: &crate::syntax::SyntaxContexts,
    frame: &std::sync::Arc<crate::syntax::ExpansionFrame>,
    budget: &mut SyntaxBudget,
    next_ordinal: &mut usize,
    introduction: usize,
) -> Result<crate::syntax::ExpandedExpression, MacroParseFailure> {
    let quotes = std::cell::RefCell::new(QuoteProjection {
        introduction,
        next_ordinal: *next_ordinal,
        sites: Vec::new(),
    });
    let result = (|| {
        let parsed = parse_macro_tree_with_expression_scratch(
            source,
            invocation,
            output,
            contexts,
            &[],
            MacroOutputPosition::Expression,
            false,
            true,
            budget,
        )?;
        project::project_macro_expression_budgeted(
            source,
            invocation,
            None,
            &parsed,
            contexts,
            Some(frame),
            0,
            budget,
            Some(&quotes),
        )
        .map_err(|failure| match failure {
            project::DeclarationExpansionFailure::Syntax {
                diagnostics,
                resource,
            } => MacroParseFailure::Syntax {
                diagnostics,
                resource,
            },
            project::DeclarationExpansionFailure::Projection(ProjectionError::ResourceLimit(
                resource,
            )) => macro_resource_failure(resource),
            project::DeclarationExpansionFailure::Projection(_) => MacroParseFailure::Invalid,
        })
    })();
    let quotes = quotes.into_inner();
    *next_ordinal = quotes.next_ordinal;
    result.map(|expression| crate::syntax::ExpandedExpression {
        expression,
        quote_sites: quotes.sites,
    })
}

pub(crate) fn parse_macro_expression_fragment(
    source: &SourceFile,
    invocation: Span,
    output: Vec<crate::syntax::MacroOutputNode>,
    contexts: &crate::syntax::SyntaxContexts,
    frame: &std::sync::Arc<crate::syntax::ExpansionFrame>,
    budget: &mut SyntaxBudget,
) -> Result<crate::surface::SurfaceExpressionCapture, MacroParseFailure> {
    let (contents, contains_protected_type, _) =
        crate::syntax::copy_fragment_output_with_type(&output, budget)?;
    let parsed = parse_macro_tree_with_expression_scratch(
        source,
        invocation,
        output,
        contexts,
        &[],
        MacroOutputPosition::HostExpressionFragment,
        false,
        true,
        budget,
    )?;
    let mut expression = project::project_macro_expression_budgeted(
        source,
        invocation,
        None,
        &parsed,
        contexts,
        Some(frame),
        1,
        budget,
        None,
    )
    .map_err(|failure| match failure {
        project::DeclarationExpansionFailure::Syntax {
            diagnostics,
            resource,
        } => MacroParseFailure::Syntax {
            diagnostics,
            resource,
        },
        project::DeclarationExpansionFailure::Projection(ProjectionError::ResourceLimit(
            resource,
        )) => macro_resource_failure(resource),
        project::DeclarationExpansionFailure::Projection(_) => MacroParseFailure::Invalid,
    })?;
    expression.span = invocation;
    budget
        .charge_units(contents.len())
        .map_err(macro_resource_failure)?;
    budget
        .charge_units(contents.len())
        .map_err(macro_resource_failure)?;
    budget.charge().map_err(macro_resource_failure)?;
    Ok(crate::surface::SurfaceExpressionCapture {
        expression,
        contents: contents.into(),
        contains_protected_type,
        quote_sites: Default::default(),
    })
}

pub(crate) fn parse_macro_type(
    source: &SourceFile,
    invocation: Span,
    output: Vec<crate::syntax::MacroOutputNode>,
    contexts: &crate::syntax::SyntaxContexts,
    frame: &std::sync::Arc<crate::syntax::ExpansionFrame>,
    budget: &mut SyntaxBudget,
) -> Result<crate::surface::SurfaceTypeCapture, MacroParseFailure> {
    let (contents, _, contains_expression) =
        crate::syntax::copy_fragment_output_with_type(&output, budget)?;
    let parsed = parse_macro_tree_with_expression_scratch(
        source,
        invocation,
        output,
        contexts,
        &[],
        MacroOutputPosition::Type,
        false,
        contains_expression,
        budget,
    )?;
    let ty = project::project_macro_type(source, invocation, &parsed, frame, budget).map_err(
        |failure| match failure {
            project::DeclarationExpansionFailure::Syntax {
                diagnostics,
                resource,
            } => MacroParseFailure::Syntax {
                diagnostics,
                resource,
            },
            project::DeclarationExpansionFailure::Projection(ProjectionError::ResourceLimit(
                resource,
            )) => macro_resource_failure(resource),
            project::DeclarationExpansionFailure::Projection(_) => MacroParseFailure::Invalid,
        },
    )?;
    budget
        .charge_units(contents.len())
        .map_err(macro_resource_failure)?;
    // Vec-to-Arc conversion allocates a new slice and moves each element.
    budget
        .charge_units(contents.len())
        .map_err(macro_resource_failure)?;
    budget.charge().map_err(macro_resource_failure)?;
    Ok(crate::surface::SurfaceTypeCapture {
        ty,
        contents: contents.into(),
    })
}

pub(crate) fn parse_macro_pattern(
    source: &SourceFile,
    invocation: Span,
    output: Vec<crate::syntax::MacroOutputNode>,
    contexts: &crate::syntax::SyntaxContexts,
    frame: &std::sync::Arc<crate::syntax::ExpansionFrame>,
    budget: &mut SyntaxBudget,
) -> Result<crate::surface::SurfacePatternCapture, MacroParseFailure> {
    let (contents, _, contains_expression) =
        crate::syntax::copy_fragment_output_with_type(&output, budget)?;
    let parsed = parse_macro_tree_with_expression_scratch(
        source,
        invocation,
        output,
        contexts,
        &[],
        MacroOutputPosition::Pattern,
        false,
        contains_expression,
        budget,
    )?;
    let pattern = project::project_macro_pattern(source, invocation, &parsed, frame, budget)
        .map_err(|failure| match failure {
            project::DeclarationExpansionFailure::Syntax {
                diagnostics,
                resource,
            } => MacroParseFailure::Syntax {
                diagnostics,
                resource,
            },
            project::DeclarationExpansionFailure::Projection(ProjectionError::ResourceLimit(
                resource,
            )) => macro_resource_failure(resource),
            project::DeclarationExpansionFailure::Projection(_) => MacroParseFailure::Invalid,
        })?;
    budget
        .charge_units(contents.len())
        .map_err(macro_resource_failure)?;
    budget
        .charge_units(contents.len())
        .map_err(macro_resource_failure)?;
    budget.charge().map_err(macro_resource_failure)?;
    Ok(crate::surface::SurfacePatternCapture {
        pattern,
        contents: contents.into(),
    })
}

pub(crate) fn parse_template_admission(
    source: &SourceFile,
    invocation: Span,
    output: Vec<crate::syntax::MacroOutputNode>,
    contexts: &crate::syntax::SyntaxContexts,
    placeholders: &[crate::surface::SurfaceName],
) -> Result<crate::surface::SurfaceExpr, MacroParseFailure> {
    parse_macro_expression_inner(
        source,
        invocation,
        None,
        output,
        contexts,
        placeholders,
        None,
    )
}

fn parse_macro_expression_inner(
    source: &SourceFile,
    invocation: Span,
    construction: Option<(Span, usize)>,
    output: Vec<crate::syntax::MacroOutputNode>,
    contexts: &crate::syntax::SyntaxContexts,
    placeholders: &[crate::surface::SurfaceName],
    frame: Option<&std::sync::Arc<crate::syntax::ExpansionFrame>>,
) -> Result<crate::surface::SurfaceExpr, MacroParseFailure> {
    let parsed = parse_macro_tree(
        source,
        invocation,
        output,
        contexts,
        placeholders,
        MacroOutputPosition::Expression,
    )?;
    project::project_macro_expression(
        source,
        invocation,
        construction,
        &parsed.tree,
        &parsed.original_nodes,
        &parsed.admission_identifiers,
        frame,
    )
    .map_err(|_| MacroParseFailure::Invalid)
}

#[derive(Clone, Copy)]
enum MacroOutputPosition {
    Expression,
    HostExpressionFragment,
    Type,
    Pattern,
    Declarations,
    StagedDeclarations,
    // Same admission grammar, with actual placeholder comparisons charged.
    QuoteTemplateAdmission,
}

impl MacroOutputPosition {
    fn is_declarations(self) -> bool {
        matches!(
            self,
            Self::Declarations | Self::StagedDeclarations | Self::QuoteTemplateAdmission
        )
    }
}

struct ParsedMacroTree {
    tree: ConcreteTree,
    original_nodes: std::collections::HashMap<usize, crate::syntax::MacroOutputNode>,
    admission_identifiers: std::collections::HashSet<usize>,
}

fn parse_macro_tree(
    source: &SourceFile,
    invocation: Span,
    output: Vec<crate::syntax::MacroOutputNode>,
    contexts: &crate::syntax::SyntaxContexts,
    placeholders: &[crate::surface::SurfaceName],
    position: MacroOutputPosition,
) -> Result<ParsedMacroTree, MacroParseFailure> {
    let mut budget = SyntaxBudget::default();
    parse_macro_tree_inner(
        source,
        invocation,
        output,
        contexts,
        placeholders,
        position,
        &mut budget,
    )
}

fn parse_macro_tree_inner(
    source: &SourceFile,
    invocation: Span,
    output: Vec<crate::syntax::MacroOutputNode>,
    contexts: &crate::syntax::SyntaxContexts,
    placeholders: &[crate::surface::SurfaceName],
    position: MacroOutputPosition,
    budget: &mut SyntaxBudget,
) -> Result<ParsedMacroTree, MacroParseFailure> {
    parse_macro_tree_selected(
        source,
        invocation,
        output,
        contexts,
        placeholders,
        position,
        false,
        budget,
    )
}

// Scratch selection and borrowed inputs remain separate at this parser boundary.
#[allow(clippy::too_many_arguments)]
fn parse_macro_tree_selected(
    source: &SourceFile,
    invocation: Span,
    output: Vec<crate::syntax::MacroOutputNode>,
    contexts: &crate::syntax::SyntaxContexts,
    placeholders: &[crate::surface::SurfaceName],
    position: MacroOutputPosition,
    pattern_scratch: bool,
    budget: &mut SyntaxBudget,
) -> Result<ParsedMacroTree, MacroParseFailure> {
    parse_macro_tree_with_expression_scratch(
        source,
        invocation,
        output,
        contexts,
        placeholders,
        position,
        pattern_scratch,
        false,
        budget,
    )
}

// Scratch selection and borrowed inputs remain separate at this parser boundary.
#[allow(clippy::too_many_arguments)]
fn parse_macro_tree_with_expression_scratch(
    source: &SourceFile,
    invocation: Span,
    output: Vec<crate::syntax::MacroOutputNode>,
    contexts: &crate::syntax::SyntaxContexts,
    placeholders: &[crate::surface::SurfaceName],
    position: MacroOutputPosition,
    pattern_scratch: bool,
    expression_scratch: bool,
    budget: &mut SyntaxBudget,
) -> Result<ParsedMacroTree, MacroParseFailure> {
    use crate::source::ByteRange;
    use crate::syntax::MacroOutputNode;
    let type_output = matches!(
        position,
        MacroOutputPosition::Type | MacroOutputPosition::Pattern
    );
    let fragment_scratch = type_output || pattern_scratch || expression_scratch;
    let budgeted = type_output
        || expression_scratch
        || matches!(
            position,
            MacroOutputPosition::StagedDeclarations | MacroOutputPosition::QuoteTemplateAdmission
        );
    if budgeted {
        charge_staged_output_with_expression_scratch(
            &output,
            contexts,
            type_output,
            pattern_scratch,
            expression_scratch,
            budget,
        )?;
    }
    let start = invocation.range().start();
    let anchor = source
        .span(ByteRange::new(start, start).map_err(|_| MacroParseFailure::Invalid)?)
        .map_err(|_| MacroParseFailure::Invalid)?;
    let end = u32::try_from(source.text().len()).map_err(|_| MacroParseFailure::Invalid)?;
    let eof = source
        .span(ByteRange::new(end, end).map_err(|_| MacroParseFailure::Invalid)?)
        .map_err(|_| MacroParseFailure::Invalid)?;
    let mut tokens = Vec::new();
    let mut original_nodes = std::collections::HashMap::new();
    let mut admission_identifiers = std::collections::HashSet::new();
    let mut syntax_selections = std::collections::HashMap::new();
    let mut syntax_spellings = std::collections::HashMap::new();
    let mut fragment_count = 0usize;
    let mut forwarded_declarations = 0usize;
    if fragment_scratch && !output.is_empty() {
        budget
            .charge_units(output.len())
            .map_err(macro_resource_failure)?;
    }
    let mut pieces = output.into_iter().rev().collect::<Vec<_>>();
    macro_rules! reserve_pieces {
        ($count:expr) => {{
            let count = $count;
            if fragment_scratch && count != 0 {
                let live = pieces.len();
                let requested = live.checked_add(count).unwrap_or(usize::MAX);
                if requested > pieces.capacity() {
                    budget
                        .charge_units(requested.checked_add(live).unwrap_or(usize::MAX))
                        .map_err(macro_resource_failure)?;
                    pieces.reserve_exact(count);
                }
            }
        }};
    }
    while let Some(piece) = pieces.pop() {
        let forwarded = matches!(&piece, MacroOutputNode::ForwardedExpression(_, _));
        let kind = match piece {
            MacroOutputNode::Expression(expression, origin)
            | MacroOutputNode::ForwardedExpression(expression, origin) => {
                if type_output && !expression_scratch {
                    return Err(MacroParseFailure::Invalid);
                }
                original_nodes.insert(
                    tokens.len(),
                    if forwarded {
                        MacroOutputNode::ForwardedExpression(expression, origin)
                    } else {
                        MacroOutputNode::Expression(expression, origin)
                    },
                );
                let name = format!("__ash_fragment_{fragment_count}");
                fragment_count += 1;
                TokenKind::Identifier(name)
            }
            MacroOutputNode::ForwardedType(capture, origin) => {
                if !position.is_declarations()
                    && !type_output
                    && !matches!(position, MacroOutputPosition::HostExpressionFragment)
                {
                    return Err(MacroParseFailure::Invalid);
                }
                original_nodes.insert(
                    tokens.len(),
                    MacroOutputNode::ForwardedType(capture, origin),
                );
                TokenKind::IntType
            }
            MacroOutputNode::ForwardedPattern(capture, origin) => {
                if !position.is_declarations()
                    && !type_output
                    && !matches!(position, MacroOutputPosition::HostExpressionFragment)
                {
                    return Err(MacroParseFailure::Invalid);
                }
                original_nodes.insert(
                    tokens.len(),
                    MacroOutputNode::ForwardedPattern(capture, origin),
                );
                TokenKind::Wildcard
            }
            MacroOutputNode::ForwardedDeclaration(capture, origin) => {
                if !position.is_declarations() {
                    return Err(MacroParseFailure::Invalid);
                }
                original_nodes.insert(
                    tokens.len(),
                    MacroOutputNode::ForwardedDeclaration(capture, origin),
                );
                forwarded_declarations += 1;
                if budgeted {
                    let digits = fragment_count
                        .checked_ilog10()
                        .map_or(1, |n| n as usize + 1);
                    budget
                        .charge_units("__ash_declaration_fragment_".len().saturating_add(digits))
                        .map_err(macro_resource_failure)?;
                }
                let name = format!("__ash_declaration_fragment_{fragment_count}");
                fragment_count += 1;
                TokenKind::Identifier(name)
            }
            MacroOutputNode::Identifier(identifier, origin) => {
                let mut admission_identifier = false;
                for name in placeholders {
                    if matches!(position, MacroOutputPosition::QuoteTemplateAdmission) {
                        budget
                            .charge_units(
                                name.text.len().min(identifier.text.len()).saturating_add(1),
                            )
                            .map_err(macro_resource_failure)?;
                    }
                    if name == &identifier {
                        admission_identifier = true;
                        break;
                    }
                }
                if admission_identifier {
                    admission_identifiers.insert(tokens.len());
                }
                original_nodes.insert(
                    tokens.len(),
                    MacroOutputNode::Identifier(identifier.clone(), origin),
                );
                if let Some(selection) = contexts.select(&identifier) {
                    syntax_selections.insert(tokens.len(), selection.clone());
                }
                syntax_spellings.insert(
                    tokens.len(),
                    std::sync::Arc::<str>::from(identifier.text.as_str()),
                );
                let uppercase = identifier
                    .text
                    .as_bytes()
                    .first()
                    .is_some_and(u8::is_ascii_uppercase);
                let spelling = identifier.text.clone();
                if uppercase {
                    TokenKind::UpperIdentifier(spelling)
                } else {
                    TokenKind::Identifier(spelling)
                }
            }
            MacroOutputNode::Token(kind, spelling, origin) => {
                syntax_spellings.insert(tokens.len(), std::sync::Arc::clone(&spelling));
                original_nodes.insert(
                    tokens.len(),
                    MacroOutputNode::Token(kind.clone(), spelling, origin),
                );
                kind
            }
            MacroOutputNode::Group(delimiter, children, origin) => {
                original_nodes.insert(
                    tokens.len(),
                    MacroOutputNode::Group(delimiter.clone(), Vec::new(), origin.clone()),
                );
                let (open, close) = match delimiter {
                    crate::syntax::MacroDelimiter::Parentheses => {
                        (TokenKind::LeftParen, TokenKind::RightParen)
                    }
                    crate::syntax::MacroDelimiter::Braces => {
                        (TokenKind::LeftBrace, TokenKind::RightBrace)
                    }
                };
                let close_spelling = match close {
                    TokenKind::RightParen => ")",
                    TokenKind::RightBrace => "}",
                    _ => unreachable!(),
                };
                reserve_pieces!(1);
                pieces.push(MacroOutputNode::Token(close, close_spelling.into(), origin));
                reserve_pieces!(children.len());
                pieces.extend(children.into_iter().rev());
                open
            }
            MacroOutputNode::Splice(_)
            | MacroOutputNode::TemplateRepeat(_)
            | MacroOutputNode::TemplateEscape(_) => {
                return Err(MacroParseFailure::Invalid);
            }
        };
        tokens.push(crate::lexer::Token { kind, span: anchor });
    }
    let mut diagnostic_spans = original_nodes
        .iter()
        .map(|(index, node)| {
            let origin = match node {
                MacroOutputNode::Expression(_, origin)
                | MacroOutputNode::ForwardedExpression(_, origin)
                | MacroOutputNode::ForwardedType(_, origin)
                | MacroOutputNode::ForwardedPattern(_, origin)
                | MacroOutputNode::ForwardedDeclaration(_, origin)
                | MacroOutputNode::Identifier(_, origin)
                | MacroOutputNode::Token(_, _, origin)
                | MacroOutputNode::Group(_, _, origin) => origin,
                MacroOutputNode::Splice(_)
                | MacroOutputNode::TemplateRepeat(_)
                | MacroOutputNode::TemplateEscape(_) => unreachable!(),
            };
            (*index, origin.primary())
        })
        .collect::<std::collections::HashMap<_, _>>();
    // The end of structured declaration output also ends its final logical line.
    if position.is_declarations()
        && tokens
            .last()
            .is_some_and(|token| token.kind != TokenKind::LineEnd)
    {
        diagnostic_spans.insert(tokens.len(), invocation);
        tokens.push(crate::lexer::Token {
            kind: TokenKind::LineEnd,
            span: anchor,
        });
    }
    diagnostic_spans.insert(tokens.len(), invocation);
    tokens.push(crate::lexer::Token {
        kind: TokenKind::EndOfFile,
        span: eof,
    });
    let mut parser = Parser {
        tokens: &tokens,
        position: 0,
        events: Vec::new(),
        diagnostics: Vec::new(),
        pending_recoveries: Vec::new(),
        recovered_expression_group_boundary: false,
        nesting_depth: 0,
        resource_failure: None,
        syntax_budget: budget.clone(),
        syntax_work_exhausted: false,
        in_template: false,
        quote_mode: QuoteMode::Ordinary,
        saw_quote_or_escape: false,
        syntax: &[],
        syntax_source: Some(source),
        syntax_selections: Some(&syntax_selections),
        syntax_spellings: Some(&syntax_spellings),
        diagnostic_spans: Some(&diagnostic_spans),
        admission_identifiers: Some(&admission_identifiers),
        declaration_output_nodes: (position.is_declarations()
            || matches!(
                position,
                MacroOutputPosition::Pattern | MacroOutputPosition::HostExpressionFragment
            ))
        .then_some(&original_nodes),
        syntax_stops: Vec::new(),
    };
    parser.start(NodeKind::Module);
    match position {
        MacroOutputPosition::Expression | MacroOutputPosition::HostExpressionFragment => {
            grammar::expression(&mut parser);
            if !parser.at(&TokenKind::EndOfFile) {
                parser.error_at_current(ParseReason::UnexpectedToken);
            }
        }
        MacroOutputPosition::Type => {
            grammar::type_expression(&mut parser);
            if !parser.at(&TokenKind::EndOfFile) {
                parser.error_at_current(ParseReason::UnexpectedToken);
            }
        }
        MacroOutputPosition::Pattern => {
            grammar::pattern(&mut parser);
            if !parser.at(&TokenKind::EndOfFile) {
                parser.error_at_current(ParseReason::UnexpectedToken);
            }
        }
        MacroOutputPosition::Declarations
        | MacroOutputPosition::StagedDeclarations
        | MacroOutputPosition::QuoteTemplateAdmission => grammar::module_body(&mut parser),
    }
    if !parser.diagnostics.is_empty() || parser.resource_failure.is_some() {
        *budget = parser.syntax_budget.clone();
        return Err(MacroParseFailure::Syntax {
            diagnostics: parser.diagnostics,
            resource: parser.resource_failure,
        });
    }
    if matches!(
        position,
        MacroOutputPosition::Expression
            | MacroOutputPosition::HostExpressionFragment
            | MacroOutputPosition::Type
            | MacroOutputPosition::Pattern
    ) {
        let _ = parser.bump();
        parser.finish();
    }
    *budget = parser.syntax_budget.clone();
    if budgeted {
        // The event-built tree and token-coverage table retain another copy of
        // this structure; reserve it before building them.
        budget
            .charge_units(parser.events.len())
            .and_then(|()| budget.charge_units(tokens.len()))
            .map_err(macro_resource_failure)?;
    }
    let Parser {
        events,
        diagnostics,
        resource_failure,
        saw_quote_or_escape,
        ..
    } = parser;
    let tree = cst::build(tokens, Vec::new(), diagnostics, events, resource_failure);
    if forwarded_declarations != 0 {
        let root = tree.root.as_ref().ok_or(MacroParseFailure::Invalid)?;
        if budgeted {
            budget
                .charge_units(root.children.len())
                .map_err(macro_resource_failure)?;
        }
        let mut actual_declarations = 0;
        for child in &root.children {
            if let ConcreteElement::Node(node) = child
                && node.kind == NodeKind::DeclarationFragment
            {
                let [ConcreteElement::Token(index)] = node.children.as_slice() else {
                    return Err(MacroParseFailure::Invalid);
                };
                if !matches!(
                    original_nodes.get(index),
                    Some(MacroOutputNode::ForwardedDeclaration(_, _))
                ) {
                    return Err(MacroParseFailure::Invalid);
                }
                actual_declarations += 1;
            }
        }
        if actual_declarations != forwarded_declarations {
            return Err(MacroParseFailure::Invalid);
        }
    }
    if saw_quote_or_escape {
        check_completed_quote_depth(&tree, budget).map_err(macro_resource_failure)?;
    }
    Ok(ParsedMacroTree {
        tree,
        original_nodes,
        admission_identifiers,
    })
}

fn macro_resource_failure(resource: ResourceFailure) -> MacroParseFailure {
    MacroParseFailure::Syntax {
        diagnostics: Vec::new(),
        resource: Some(resource),
    }
}

/// Reserve adapter storage before converting an identifier-only output tree.
#[cfg(test)]
fn charge_staged_output(
    output: &[crate::syntax::MacroOutputNode],
    contexts: &crate::syntax::SyntaxContexts,
    type_scratch: bool,
    pattern_scratch: bool,
    budget: &mut SyntaxBudget,
) -> Result<(), MacroParseFailure> {
    charge_staged_output_with_expression_scratch(
        output,
        contexts,
        type_scratch,
        pattern_scratch,
        false,
        budget,
    )
}

fn charge_staged_output_with_expression_scratch(
    output: &[crate::syntax::MacroOutputNode],
    contexts: &crate::syntax::SyntaxContexts,
    type_scratch: bool,
    pattern_scratch: bool,
    expression_scratch: bool,
    budget: &mut SyntaxBudget,
) -> Result<(), MacroParseFailure> {
    use crate::syntax::MacroOutputNode;
    budget
        .charge_units(output.len())
        .map_err(macro_resource_failure)?;
    budget
        .charge_units(output.len())
        .map_err(macro_resource_failure)?;
    let selected_scratch = type_scratch || pattern_scratch || expression_scratch;
    if selected_scratch && !output.is_empty() {
        budget
            .charge_units(output.len())
            .map_err(macro_resource_failure)?;
    }
    let mut pending = output.iter().map(|node| (node, 0usize)).collect::<Vec<_>>();
    while let Some((node, depth)) = pending.pop() {
        // Piece, token, original-node entry, spelling entry, diagnostic entry.
        budget.charge_units(5).map_err(macro_resource_failure)?;
        match node {
            MacroOutputNode::Identifier(name, _) => {
                if selected_scratch {
                    crate::syntax::charge_type_name_copy(name, depth, budget)
                        .map_err(macro_resource_failure)?;
                } else {
                    crate::syntax::charge_name(name, budget).map_err(macro_resource_failure)?;
                }
                // The token spelling and its shared syntax spelling are separate copies.
                budget
                    .charge_units(name.text.len())
                    .map_err(macro_resource_failure)?;
                budget
                    .charge_units(name.text.len())
                    .map_err(macro_resource_failure)?;
                contexts
                    .charge_selection_search(&name.text, name.introduction, budget)
                    .map_err(macro_resource_failure)?;
                contexts
                    .charge_selection_search(&name.text, name.introduction, budget)
                    .map_err(macro_resource_failure)?;
                if let Some(selection) = contexts.select(name) {
                    let charge_selection = |budget: &mut SyntaxBudget| {
                        if expression_scratch {
                            crate::syntax::charge_selected_expression(selection, budget)
                        } else {
                            crate::syntax::charge_selected(selection, budget)
                        }
                    };
                    charge_selection(budget).map_err(macro_resource_failure)?;
                    // An invocation's inherited stop indices are depth-bounded.
                    budget
                        .charge_units(STRUCTURAL_DEPTH_LIMIT)
                        .map_err(macro_resource_failure)?;
                    // The expression matcher and its literal stops may be
                    // cloned by the ordinary generated-expression parser.
                    if selection.declaration.category
                        == crate::surface::SurfaceSyntaxCategory::Expression
                    {
                        charge_selection(budget).map_err(macro_resource_failure)?;
                        charge_selection(budget).map_err(macro_resource_failure)?;
                        charge_selection(budget).map_err(macro_resource_failure)?;
                    }
                }
            }
            MacroOutputNode::Token(kind, spelling, _) => {
                budget
                    .charge_units(spelling.len())
                    .map_err(macro_resource_failure)?;
                crate::syntax::charge_type_token_copy(kind, budget)
                    .map_err(macro_resource_failure)?;
            }
            MacroOutputNode::Group(_, children, origin) => {
                if depth >= STRUCTURAL_DEPTH_LIMIT {
                    return Err(macro_resource_failure(ResourceFailure::StructuralDepth {
                        limit: STRUCTURAL_DEPTH_LIMIT,
                    }));
                }
                if selected_scratch {
                    crate::syntax::charge_type_origin_copy(origin, depth + 1, budget)
                        .map_err(macro_resource_failure)?;
                }
                // A group adds a synthetic closing token and pending child entries.
                budget.charge_units(5).map_err(macro_resource_failure)?;
                budget
                    .charge_units(STRUCTURAL_DEPTH_LIMIT)
                    .map_err(macro_resource_failure)?;
                budget
                    .charge_units(children.len())
                    .map_err(macro_resource_failure)?;
                budget
                    .charge_units(children.len())
                    .map_err(macro_resource_failure)?;
                if selected_scratch && !children.is_empty() {
                    let live = pending.len();
                    let requested = live.saturating_add(children.len());
                    if requested > pending.capacity() {
                        budget
                            .charge_units(requested.saturating_add(live))
                            .map_err(macro_resource_failure)?;
                        pending.reserve_exact(children.len());
                    }
                }
                pending.extend(children.iter().map(|child| (child, depth + 1)));
            }
            // The adapter moves this preflighted capture into original_nodes;
            // the piece, placeholder token and map entry are reserved above.
            MacroOutputNode::ForwardedType(_, _) => {}
            MacroOutputNode::ForwardedDeclaration(_, origin) => {
                crate::syntax::charge_type_origin(origin, depth, budget)
                    .map_err(macro_resource_failure)?;
            }
            MacroOutputNode::Expression(capture, origin)
            | MacroOutputNode::ForwardedExpression(capture, origin) => {
                if matches!(node, MacroOutputNode::Expression(..)) && !expression_scratch {
                    return Err(MacroParseFailure::Invalid);
                }
                let child = crate::syntax::type_depth(depth, 1).map_err(macro_resource_failure)?;
                crate::syntax::charge_type_origin(origin, child, budget)
                    .map_err(macro_resource_failure)?;
                let bridge = if expression_scratch {
                    crate::syntax::charge_new_expression_retention(capture, depth, budget)
                } else {
                    crate::syntax::charge_expression_retention(capture, depth, budget)
                }
                .map_err(macro_resource_failure)?
                .ok_or(MacroParseFailure::Invalid)?;
                if expression_scratch && bridge {
                    return Err(MacroParseFailure::Invalid);
                }
            }
            MacroOutputNode::ForwardedPattern(capture, origin) => {
                let child = crate::syntax::type_depth(depth, 1).map_err(macro_resource_failure)?;
                crate::syntax::charge_type_origin(origin, child, budget)
                    .map_err(macro_resource_failure)?;
                let bridge = if selected_scratch {
                    crate::syntax::charge_new_pattern_retention(capture, depth, budget)
                } else {
                    crate::syntax::charge_pattern_retention(capture, depth, budget)
                }
                .map_err(macro_resource_failure)?
                .ok_or(MacroParseFailure::Invalid)?;
                if selected_scratch && bridge {
                    return Err(MacroParseFailure::Invalid);
                }
            }
            MacroOutputNode::Splice(_)
            | MacroOutputNode::TemplateRepeat(_)
            | MacroOutputNode::TemplateEscape(_) => {
                return Err(MacroParseFailure::Invalid);
            }
        }
    }
    // Type output has only EOF; declaration output may also need a line end.
    budget
        .charge_units(if type_scratch { 2 } else { 4 })
        .map_err(macro_resource_failure)
}

fn parse_parts(
    tokens: Vec<crate::lexer::Token>,
    lexical_diagnostics: Vec<Diagnostic<crate::lexer::LexReason>>,
    syntax_budget: SyntaxBudget,
    lexical_resource_failure: Option<ResourceFailure>,
) -> (ConcreteTree, SyntaxBudget) {
    if let Some(resource_failure) = lexical_resource_failure {
        return (
            cst::resource_limited(tokens, lexical_diagnostics, Vec::new(), resource_failure),
            syntax_budget,
        );
    }

    let (checkpoint, syntax_budget) =
        parse_module_header(tokens, lexical_diagnostics, syntax_budget);
    finish_module_from_checkpoint(checkpoint, syntax_budget)
}

/// Retained parser state at the boundary between a module's header and body.
///
/// The token stream and lexical diagnostics remain with their parser state;
/// the graph-wide budget remains with the caller. The event stream still has
/// its module node open and can only be finished once.
pub(crate) struct ParserCheckpoint {
    tokens: Vec<crate::lexer::Token>,
    lexical_diagnostics: Vec<Diagnostic<crate::lexer::LexReason>>,
    position: usize,
    events: Vec<Event>,
    diagnostics: Vec<ParseDiagnostic>,
    pending_recoveries: Vec<usize>,
    recovered_expression_group_boundary: bool,
    nesting_depth: usize,
    resource_failure: Option<ResourceFailure>,
    syntax_work_exhausted: bool,
}

impl ParserCheckpoint {
    pub(crate) fn lexical_diagnostics(&self) -> &[Diagnostic<crate::lexer::LexReason>] {
        &self.lexical_diagnostics
    }

    pub(crate) fn parse_diagnostics(&self) -> &[ParseDiagnostic] {
        &self.diagnostics
    }

    pub(crate) const fn resource_failure(&self) -> Option<ResourceFailure> {
        self.resource_failure
    }
}

pub(crate) fn parse_module_header(
    tokens: Vec<crate::lexer::Token>,
    lexical_diagnostics: Vec<Diagnostic<crate::lexer::LexReason>>,
    syntax_budget: SyntaxBudget,
) -> (ParserCheckpoint, SyntaxBudget) {
    let (
        position,
        events,
        diagnostics,
        pending_recoveries,
        recovered_expression_group_boundary,
        nesting_depth,
        resource_failure,
        syntax_work_exhausted,
        syntax_budget,
    ) = {
        let mut parser = Parser {
            tokens: &tokens,
            position: 0,
            events: Vec::new(),
            diagnostics: Vec::new(),
            pending_recoveries: Vec::new(),
            recovered_expression_group_boundary: false,
            nesting_depth: 0,
            resource_failure: None,
            syntax_budget,
            syntax_work_exhausted: false,
            in_template: false,
            quote_mode: QuoteMode::Ordinary,
            saw_quote_or_escape: false,
            syntax: &[],
            syntax_source: None,
            syntax_selections: None,
            syntax_spellings: None,
            diagnostic_spans: None,
            admission_identifiers: None,
            declaration_output_nodes: None,
            syntax_stops: Vec::new(),
        };
        grammar::module_header(&mut parser);
        (
            parser.position,
            parser.events,
            parser.diagnostics,
            parser.pending_recoveries,
            parser.recovered_expression_group_boundary,
            parser.nesting_depth,
            parser.resource_failure,
            parser.syntax_work_exhausted,
            parser.syntax_budget,
        )
    };
    let checkpoint = ParserCheckpoint {
        tokens,
        lexical_diagnostics,
        position,
        events,
        diagnostics,
        pending_recoveries,
        recovered_expression_group_boundary,
        nesting_depth,
        resource_failure,
        syntax_work_exhausted,
    };
    (checkpoint, syntax_budget)
}

pub(crate) fn finish_module_from_checkpoint(
    checkpoint: ParserCheckpoint,
    syntax_budget: SyntaxBudget,
) -> (ConcreteTree, SyntaxBudget) {
    finish_module_from_checkpoint_with_syntax(checkpoint, syntax_budget, None, &[])
}

pub(crate) fn finish_module_from_checkpoint_with_syntax(
    checkpoint: ParserCheckpoint,
    syntax_budget: SyntaxBudget,
    source: Option<&SourceFile>,
    syntax: &[crate::syntax::SelectedSyntax],
) -> (ConcreteTree, SyntaxBudget) {
    let ParserCheckpoint {
        tokens,
        lexical_diagnostics,
        position,
        events,
        diagnostics,
        pending_recoveries,
        recovered_expression_group_boundary,
        nesting_depth,
        resource_failure,
        syntax_work_exhausted,
    } = checkpoint;
    let mut parser = Parser {
        tokens: &tokens,
        position,
        events,
        diagnostics,
        pending_recoveries,
        recovered_expression_group_boundary,
        nesting_depth,
        resource_failure,
        syntax_budget,
        syntax_work_exhausted,
        in_template: false,
        quote_mode: QuoteMode::Ordinary,
        saw_quote_or_escape: false,
        syntax,
        syntax_source: source,
        syntax_selections: None,
        syntax_spellings: None,
        diagnostic_spans: None,
        admission_identifiers: None,
        declaration_output_nodes: None,
        syntax_stops: Vec::new(),
    };
    grammar::module_body(&mut parser);
    let Parser {
        events,
        diagnostics,
        resource_failure,
        syntax_work_exhausted,
        mut syntax_budget,
        saw_quote_or_escape,
        ..
    } = parser;
    if syntax_work_exhausted {
        return (
            cst::resource_limited(
                tokens,
                lexical_diagnostics,
                diagnostics,
                resource_failure.expect("syntax exhaustion records its resource failure"),
            ),
            syntax_budget,
        );
    }
    let mut tree = cst::build(
        tokens,
        lexical_diagnostics,
        diagnostics,
        events,
        resource_failure,
    );
    if saw_quote_or_escape
        && let Err(failure) = check_completed_quote_depth(&tree, &mut syntax_budget)
    {
        drop(tree.root.take());
        tree.events.clear();
        tree.resource_failure = Some(failure);
    }
    (tree, syntax_budget)
}

// Quote depth must compose with its surrounding tree before that tree is
// exposed. Projection independently validates trees at its own boundary.
fn check_completed_quote_depth(
    tree: &ConcreteTree,
    budget: &mut SyntaxBudget,
) -> Result<(), ResourceFailure> {
    if !tree.lexical_diagnostics.is_empty()
        || !tree.parse_diagnostics.is_empty()
        || tree.malformed.is_some()
        || tree.resource_failure.is_some()
    {
        return Ok(());
    }
    let Some(root) = tree.root.as_ref() else {
        return Ok(());
    };
    budget.charge()?;
    let mut pending = vec![(root, 0_usize)];
    while let Some((node, depth)) = pending.pop() {
        budget.charge()?;
        if node.kind == NodeKind::SyntaxEscape {
            // Reserve both immediate children before the shape classification.
            budget.charge_units(2)?;
        }
        if matches!(
            node.kind,
            NodeKind::Pattern
                | NodeKind::AtomicType
                | NodeKind::EffectInstance
                | NodeKind::InterfaceApplication
                | NodeKind::OperationReference
                | NodeKind::Type
                | NodeKind::Kind
        ) {
            // structural_weight may stop early; reserve its worst-case child scan.
            budget.charge_units(node.children.len())?;
        }
        let depth = depth.saturating_add(source_structural_weight(node));
        if depth > STRUCTURAL_DEPTH_LIMIT {
            return Err(ResourceFailure::StructuralDepth {
                limit: STRUCTURAL_DEPTH_LIMIT,
            });
        }
        for child in &node.children {
            budget.charge()?;
            if let ConcreteElement::Node(child) = child {
                budget.charge()?;
                pending.push((child, depth));
            }
        }
    }
    Ok(())
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum QuoteMode {
    Ordinary,
    Template,
    Escape,
    Quote,
}

pub(crate) struct Parser<'tokens> {
    tokens: &'tokens [crate::lexer::Token],
    position: usize,
    events: Vec<Event>,
    diagnostics: Vec<ParseDiagnostic>,
    pending_recoveries: Vec<usize>,
    recovered_expression_group_boundary: bool,
    nesting_depth: usize,
    resource_failure: Option<ResourceFailure>,
    syntax_budget: SyntaxBudget,
    syntax_work_exhausted: bool,
    in_template: bool,
    quote_mode: QuoteMode,
    saw_quote_or_escape: bool,
    syntax: &'tokens [crate::syntax::SelectedSyntax],
    syntax_source: Option<&'tokens SourceFile>,
    syntax_selections:
        Option<&'tokens std::collections::HashMap<usize, crate::syntax::SelectedSyntax>>,
    syntax_spellings: Option<&'tokens std::collections::HashMap<usize, std::sync::Arc<str>>>,
    diagnostic_spans: Option<&'tokens std::collections::HashMap<usize, Span>>,
    admission_identifiers: Option<&'tokens std::collections::HashSet<usize>>,
    declaration_output_nodes:
        Option<&'tokens std::collections::HashMap<usize, crate::syntax::MacroOutputNode>>,
    syntax_stops: Vec<(TokenKind, String, usize)>,
}

impl Parser<'_> {
    fn at_forwarded_declaration(&self) -> bool {
        matches!(
            self.declaration_output_nodes
                .and_then(|nodes| nodes.get(&self.position)),
            Some(crate::syntax::MacroOutputNode::ForwardedDeclaration(_, _))
        )
    }

    fn is_admission_identifier(&self) -> bool {
        self.nth_is_admission_identifier(0)
    }

    fn nth_is_admission_identifier(&self, distance: usize) -> bool {
        self.position.checked_add(distance).is_some_and(|position| {
            self.admission_identifiers
                .is_some_and(|indices| indices.contains(&position))
        })
    }

    fn at_upper_identifier(&self) -> bool {
        self.is_admission_identifier()
            || matches!(self.current(), Some(TokenKind::UpperIdentifier(_)))
    }

    fn at_syntax_name(&self) -> bool {
        self.selected_syntax().is_some()
    }

    fn selected_syntax(&self) -> Option<&crate::syntax::SelectedSyntax> {
        self.selected_syntax_in_category(crate::surface::SurfaceSyntaxCategory::Expression)
    }

    fn selected_declaration_syntax(&self) -> Option<&crate::syntax::SelectedSyntax> {
        self.selected_syntax_in_category(crate::surface::SurfaceSyntaxCategory::Declaration)
    }

    fn selected_syntax_in_category(
        &self,
        category: crate::surface::SurfaceSyntaxCategory,
    ) -> Option<&crate::syntax::SelectedSyntax> {
        let selection = if let Some(selections) = self.syntax_selections {
            selections.get(&self.position)
        } else {
            let Some(TokenKind::Identifier(name)) = self.current() else {
                return None;
            };
            self.syntax.iter().find(|syntax| syntax.name == *name)
        };
        selection.filter(|syntax| syntax.declaration.category == category)
    }

    fn at_syntax_literal(&self, kind: &TokenKind, spelling: &str) -> bool {
        self.nth_syntax_literal(0, kind, spelling)
    }

    fn nth_syntax_literal(&self, distance: usize, kind: &TokenKind, spelling: &str) -> bool {
        let Some(position) = self.position.checked_add(distance) else {
            return false;
        };
        let Some(token) = self.tokens.get(position) else {
            return false;
        };
        if token.kind != *kind {
            return false;
        }
        if let Some(spellings) = self.syntax_spellings {
            return spellings
                .get(&position)
                .is_some_and(|found| found.as_ref() == spelling);
        }
        let Some(source) = self.syntax_source else {
            return false;
        };
        let range = token.span.range();
        source
            .text()
            .get(range.start() as usize..range.end() as usize)
            == Some(spelling)
    }

    fn at_syntax_stop(&self) -> bool {
        self.nth_at_syntax_stop(0)
    }

    fn nth_at_syntax_stop(&self, distance: usize) -> bool {
        self.nth_at_syntax_stop_in_depth(distance, self.nesting_depth)
    }

    fn nth_at_syntax_stop_in_depth(&self, distance: usize, level: usize) -> bool {
        self.syntax_stops.iter().any(|(kind, spelling, depth)| {
            *depth == level && self.nth_syntax_literal(distance, kind, spelling)
        })
    }
    fn start(&mut self, kind: NodeKind) {
        self.saw_quote_or_escape |= matches!(kind, NodeKind::SyntaxQuote | NodeKind::SyntaxEscape);
        let _ = self.retain_event(Event::Start(kind));
    }

    fn finish(&mut self) {
        let _ = self.retain_event(Event::Finish);
    }

    fn event_position(&self) -> usize {
        self.events.len()
    }

    fn insert_start(&mut self, position: usize, kind: NodeKind) -> bool {
        if position > self.events.len() {
            return false;
        }
        if !self.charge_event() {
            return false;
        }
        self.events.insert(position, Event::Start(kind));
        true
    }

    fn current(&self) -> Option<&TokenKind> {
        self.tokens.get(self.position).map(|token| &token.kind)
    }

    fn nth(&self, distance: usize) -> Option<&TokenKind> {
        self.position
            .checked_add(distance)
            .and_then(|index| self.tokens.get(index))
            .map(|token| &token.kind)
    }

    fn at(&self, expected: &TokenKind) -> bool {
        self.current()
            .is_some_and(|kind| same_variant(kind, expected))
    }

    fn bump(&mut self) -> bool {
        if self.position >= self.tokens.len() {
            return false;
        }
        let retained = self.retain_event(Event::Token(self.position));
        self.position += 1;
        retained
    }

    fn expect(&mut self, kind: &TokenKind, expected: ExpectedForm) -> bool {
        if self.resource_failure.is_some() {
            return false;
        }
        if self.at(kind) {
            return self.bump();
        }
        self.report(ParseReason::ExpectedForm, expected);
        false
    }

    fn report(&mut self, reason: ParseReason, expected: ExpectedForm) {
        if self.resource_failure.is_some() {
            return;
        }
        let Some(at) = self.current_span() else {
            let _ = self.retain_event(Event::Error(reason));
            return;
        };
        let _ = self.report_at(reason, expected, at, None);
    }

    fn report_at(
        &mut self,
        reason: ParseReason,
        expected: ExpectedForm,
        primary: Span,
        related: Option<Span>,
    ) -> Option<usize> {
        if self.resource_failure.is_some() {
            return None;
        }
        let at = self.current_span().unwrap_or(primary);
        if !self.retain_event(Event::Error(reason))
            || !self.retain_event(Event::Missing { expected, at })
        {
            return None;
        }
        let mut diagnostic =
            Diagnostic::new(reason, SourceLabel::new(primary, primary_message(reason)));
        if let Some(related) = related {
            diagnostic.related.push(SourceLabel::new(
                related,
                "recovery continues from this source position",
            ));
        }
        diagnostic.expected = Some(expected_name(expected).into());
        diagnostic.found = self.current().map(token_name).map(str::to_owned);
        let index = self.diagnostics.len();
        self.diagnostics.push(ParseDiagnostic::new(
            diagnostic,
            Some(expected),
            self.current().map(retained_token),
            related,
        ));
        Some(index)
    }

    fn error_at_current(&mut self, reason: ParseReason) {
        if self.resource_failure.is_some() {
            return;
        }
        if !self.retain_event(Event::Error(reason)) {
            return;
        }
        let Some(at) = self.current_span() else {
            return;
        };
        let mut diagnostic = Diagnostic::new(reason, SourceLabel::new(at, primary_message(reason)));
        diagnostic.found = self.current().map(token_name).map(str::to_owned);
        self.diagnostics.push(ParseDiagnostic::new(
            diagnostic,
            None,
            self.current().map(retained_token),
            None,
        ));
    }

    fn error_at_span(&mut self, reason: ParseReason, span: Span) {
        if self.resource_failure.is_some() || !self.retain_event(Event::Error(reason)) {
            return;
        }
        let diagnostic = Diagnostic::new(reason, SourceLabel::new(span, primary_message(reason)));
        self.diagnostics
            .push(ParseDiagnostic::new(diagnostic, None, None, None));
    }

    fn current_span(&self) -> Option<Span> {
        if let Some(spans) = self.diagnostic_spans
            && let Some(span) = spans.get(&self.position)
        {
            return Some(*span);
        }
        self.tokens
            .get(self.position)
            .or_else(|| self.tokens.last())
            .map(|token| token.span)
    }

    fn pending_recovery_count(&self) -> usize {
        self.pending_recoveries.len()
    }

    fn mark_recovered_expression_group_boundary(&mut self) {
        self.recovered_expression_group_boundary = true;
    }

    fn take_recovered_expression_group_boundary(&mut self) -> bool {
        std::mem::take(&mut self.recovered_expression_group_boundary)
    }

    fn mark_pending_recovery(&mut self, diagnostic_index: usize) {
        self.pending_recoveries.push(diagnostic_index);
    }

    fn resolve_pending_recoveries_since(
        &mut self,
        start: usize,
        boundary: SynchronizationBoundary,
        span: Span,
    ) {
        if self.resource_failure.is_some() {
            self.pending_recoveries.truncate(start);
            return;
        }
        for index in self.pending_recoveries.iter().skip(start).copied() {
            if let Some(diagnostic) = self.diagnostics.get_mut(index) {
                diagnostic
                    .diagnostic
                    .related
                    .push(SourceLabel::new(span, synchronization_message(boundary)));
                diagnostic
                    .context
                    .push(ParseContext::Synchronization { boundary, span });
            }
        }
        self.pending_recoveries.truncate(start);
    }

    fn resolve_pending_at_current(&mut self, start: usize, boundary: SynchronizationBoundary) {
        if self.resource_failure.is_some() {
            self.pending_recoveries.truncate(start);
            return;
        }
        if let Some(span) = self.current_span() {
            self.resolve_pending_recoveries_since(start, boundary, span);
        }
    }

    fn consume_rest(&mut self) {
        if self.position >= self.tokens.len() {
            return;
        }
        self.start(NodeKind::Error);
        while self.bump() {}
        self.finish();
    }

    fn enter_structure(&mut self) -> bool {
        self.enter_structures(1)
    }

    fn enter_structures(&mut self, weight: usize) -> bool {
        let Some(depth) = self.nesting_depth.checked_add(weight) else {
            self.fail_structural_depth();
            return false;
        };
        if depth > STRUCTURAL_DEPTH_LIMIT {
            self.fail_structural_depth();
            return false;
        }
        self.nesting_depth = depth;
        true
    }

    fn leave_structure(&mut self) {
        self.nesting_depth = self.nesting_depth.saturating_sub(1);
    }

    fn leave_structures(&mut self, weight: usize) {
        self.nesting_depth = self.nesting_depth.saturating_sub(weight);
    }

    fn permits_expression_depth(&mut self, expression_depth: usize) -> bool {
        if self
            .nesting_depth
            .checked_add(expression_depth)
            .is_some_and(|depth| depth <= STRUCTURAL_DEPTH_LIMIT)
        {
            true
        } else {
            self.fail_structural_depth();
            false
        }
    }

    fn fail_structural_depth(&mut self) {
        self.resource_failure
            .get_or_insert(ResourceFailure::StructuralDepth {
                limit: STRUCTURAL_DEPTH_LIMIT,
            });
    }

    fn retain_event(&mut self, event: Event) -> bool {
        if !self.charge_event() {
            return false;
        }
        self.events.push(event);
        true
    }

    fn charge_event(&mut self) -> bool {
        if self.syntax_work_exhausted {
            return false;
        }
        if let Err(resource_failure) = self.syntax_budget.charge() {
            self.resource_failure.get_or_insert(resource_failure);
            self.syntax_work_exhausted = true;
            return false;
        }
        true
    }

    fn charge_matcher_work(&mut self, units: usize) -> bool {
        if self.syntax_work_exhausted {
            return false;
        }
        if let Err(failure) = self.syntax_budget.charge_units(units) {
            self.resource_failure.get_or_insert(failure);
            self.syntax_work_exhausted = true;
            return false;
        }
        true
    }

    fn charge_declaration_matcher(&mut self) -> bool {
        let mut budget = self.syntax_budget.clone();
        let result = (|| {
            if self.syntax_selections.is_some() {
                budget.charge_units(3)?;
            } else if let Some(TokenKind::Identifier(name)) = self.current() {
                for selected in self.syntax {
                    // This scan and the two subsequent matcher lookups.
                    budget.charge_units(3)?;
                    let bytes = name.len().min(selected.name.len());
                    budget.charge_units(bytes)?;
                    budget.charge_units(bytes)?;
                    budget.charge_units(bytes)?;
                    if selected.name == *name {
                        break;
                    }
                }
            }
            if let Some(selected) = self.selected_declaration_syntax() {
                crate::syntax::charge_selected(selected, &mut budget)?;
                crate::syntax::charge_selected(selected, &mut budget)?;
                crate::syntax::charge_selected(selected, &mut budget)?;
            }
            budget.charge_units(self.syntax_stops.len())
        })();
        self.syntax_budget = budget;
        if let Err(resource_failure) = result {
            self.resource_failure.get_or_insert(resource_failure);
            self.syntax_work_exhausted = true;
            return false;
        }
        true
    }
}

const fn synchronization_message(boundary: SynchronizationBoundary) -> &'static str {
    match boundary {
        SynchronizationBoundary::LogicalLineEnd => "parsing resumes at this logical line boundary",
        SynchronizationBoundary::TypeParameterSeparator => {
            "parsing resumes at this type parameter separator"
        }
        SynchronizationBoundary::TypeParameterListClosing => {
            "parsing resumes at this type parameter list closing delimiter"
        }
        SynchronizationBoundary::TypeDeclarationEqual => {
            "parsing resumes at this nominal declaration equals sign"
        }
        SynchronizationBoundary::EquationalGlobalColon => {
            "parsing resumes at this equational global colon"
        }
        SynchronizationBoundary::InterfaceMethodColon => {
            "parsing resumes at this interface method colon"
        }
        SynchronizationBoundary::OperationalParameterOpeningParen => {
            "parsing resumes at this operational parameter opening parenthesis"
        }
        SynchronizationBoundary::ImplementationInterfaceHead => {
            "parsing resumes at this implementation interface head"
        }
        SynchronizationBoundary::InterfaceBodyOpeningBrace => {
            "parsing resumes at this interface body opening brace"
        }
        SynchronizationBoundary::ImplementationBodyOpeningBrace => {
            "parsing resumes at this implementation body opening brace"
        }
        SynchronizationBoundary::OperationalBodyOpeningBrace => {
            "parsing resumes at this operational body opening brace"
        }
        SynchronizationBoundary::BlockClosingBrace => "parsing resumes at this block closing brace",
        SynchronizationBoundary::InterfaceClosingBrace => {
            "parsing resumes at this interface closing brace"
        }
        SynchronizationBoundary::ImplementationClosingBrace => {
            "parsing resumes at this implementation closing brace"
        }
        SynchronizationBoundary::ParenthesisClosing => {
            "parsing resumes at this closing parenthesis"
        }
        SynchronizationBoundary::EndOfFile => "parsing stops at end of input",
    }
}

fn same_variant(left: &TokenKind, right: &TokenKind) -> bool {
    std::mem::discriminant(left) == std::mem::discriminant(right)
}

fn retained_token(kind: &TokenKind) -> FoundToken {
    match kind {
        TokenKind::Identifier(_) => FoundToken::Identifier,
        TokenKind::UpperIdentifier(_) => FoundToken::UpperIdentifier,
        TokenKind::Wildcard => FoundToken::Spelling("_"),
        TokenKind::Integer(_) => FoundToken::Integer,
        TokenKind::StringLiteral(_) => FoundToken::StringLiteral,
        TokenKind::True => FoundToken::Spelling("true"),
        TokenKind::False => FoundToken::Spelling("false"),
        TokenKind::Fn => FoundToken::Spelling("fn"),
        TokenKind::Let => FoundToken::Spelling("let"),
        TokenKind::Rec => FoundToken::Spelling("rec"),
        TokenKind::And => FoundToken::Spelling("and"),
        TokenKind::Type => FoundToken::Spelling("type"),
        TokenKind::Newtype => FoundToken::Spelling("newtype"),
        TokenKind::Effect => FoundToken::Spelling("effect"),
        TokenKind::Match => FoundToken::Spelling("match"),
        TokenKind::Perform => FoundToken::Spelling("perform"),
        TokenKind::Handle => FoundToken::Spelling("handle"),
        TokenKind::With => FoundToken::Spelling("with"),
        TokenKind::Resume => FoundToken::Spelling("resume"),
        TokenKind::Resource => FoundToken::Spelling("resource"),
        TokenKind::Region => FoundToken::Spelling("region"),
        TokenKind::Using => FoundToken::Spelling("using"),
        TokenKind::Hook => FoundToken::Spelling("hook"),
        TokenKind::Register => FoundToken::Spelling("register"),
        TokenKind::Cleanup => FoundToken::Spelling("cleanup"),
        TokenKind::Discard => FoundToken::Spelling("discard"),
        TokenKind::Retain => FoundToken::Spelling("retain"),
        TokenKind::Import => FoundToken::Spelling("import"),
        TokenKind::SyntaxKeyword => FoundToken::Spelling("syntax"),
        TokenKind::As => FoundToken::Spelling("as"),
        TokenKind::Pub => FoundToken::Spelling("pub"),
        TokenKind::Opaque => FoundToken::Spelling("opaque"),
        TokenKind::Interface => FoundToken::Spelling("interface"),
        TokenKind::Impl => FoundToken::Spelling("impl"),
        TokenKind::Where => FoundToken::Spelling("where"),
        TokenKind::IntType => FoundToken::Spelling("Int"),
        TokenKind::BytesType => FoundToken::Spelling("Bytes"),
        TokenKind::StringType => FoundToken::Spelling("String"),
        TokenKind::BoolType => FoundToken::Spelling("Bool"),
        TokenKind::UnitType => FoundToken::Spelling("Unit"),
        TokenKind::LeftParen => FoundToken::Spelling("("),
        TokenKind::RightParen => FoundToken::Spelling(")"),
        TokenKind::LeftBrace => FoundToken::Spelling("{"),
        TokenKind::RightBrace => FoundToken::Spelling("}"),
        TokenKind::Colon => FoundToken::Spelling(":"),
        TokenKind::Equal => FoundToken::Spelling("="),
        TokenKind::EqualEqual => FoundToken::Spelling("=="),
        TokenKind::Plus => FoundToken::Spelling("+"),
        TokenKind::Star => FoundToken::Spelling("*"),
        TokenKind::Arrow => FoundToken::Spelling("->"),
        TokenKind::FatArrow => FoundToken::Spelling("=>"),
        TokenKind::Pipe => FoundToken::Spelling("|"),
        TokenKind::Bang => FoundToken::Spelling("!"),
        TokenKind::Comma => FoundToken::Spelling(","),
        TokenKind::Less => FoundToken::Spelling("<"),
        TokenKind::Greater => FoundToken::Spelling(">"),
        TokenKind::Semicolon => FoundToken::Spelling(";"),
        TokenKind::At => FoundToken::Spelling("@"),
        TokenKind::Dollar => FoundToken::Spelling("$"),
        TokenKind::Dot => FoundToken::Spelling("."),
        TokenKind::LineEnd => FoundToken::LineEnd,
        TokenKind::EndOfFile => FoundToken::EndOfFile,
    }
}

fn token_name(kind: &TokenKind) -> &'static str {
    match retained_token(kind) {
        FoundToken::Identifier => "identifier",
        FoundToken::UpperIdentifier => "uppercase identifier",
        FoundToken::Integer => "integer",
        FoundToken::StringLiteral => "string literal",
        FoundToken::Spelling(spelling) => spelling,
        FoundToken::LineEnd => "line end",
        FoundToken::EndOfFile => "end of input",
    }
}

const fn primary_message(reason: ParseReason) -> &'static str {
    match reason {
        ParseReason::ExpectedForm => "required syntax is missing",
        ParseReason::ExpectedOperand => "the operator requires a right operand",
        ParseReason::UnclosedGroup => "the opening parenthesis is not closed",
        ParseReason::RepeatedEquality => "equality is non-associative",
        ParseReason::ExpectedRecursiveMember => {
            "the recursive delimiter requires another binding member"
        }
        ParseReason::UnexpectedAnd => "and is only accepted within a recursive binding group",
        ParseReason::Semicolon => "semicolons are not available in Ash",
        ParseReason::UnexpectedToken => "token is not accepted at this grammar position",
        ParseReason::UnknownTemplateCapture => UNKNOWN_TEMPLATE_CAPTURE_LABEL,
        ParseReason::RepetitionMissingDriver => "the repetition has no capture driver",
        ParseReason::RepetitionLengthMismatch => "repetition driver lengths differ",
        ParseReason::RepetitionEmpty => "a one-or-more repetition has no values",
        ParseReason::MatcherRepetitionAmbiguous => {
            "the matcher repetition has an ambiguous boundary"
        }
        ParseReason::MatcherRepetitionEmpty => "the matcher repetition requires an iteration",
        ParseReason::MatcherTrailingSeparator => "the matcher separator has no following iteration",
    }
}

const fn expected_name(expected: ExpectedForm) -> &'static str {
    match expected {
        ExpectedForm::Expression => "an expression",
        ExpectedForm::Operand => "an operand",
        ExpectedForm::Identifier => "an identifier",
        ExpectedForm::Type => "a type",
        ExpectedForm::EffectRow => "an effect row",
        ExpectedForm::Kind => "a kind",
        ExpectedForm::Pattern => "a pattern",
        ExpectedForm::InterfaceParameter => "one interface type parameter",
        ExpectedForm::InterfaceMethod => "an interface method signature",
        ExpectedForm::EffectOperation => "an effect operation signature",
        ExpectedForm::InterfaceApplication => "an interface application",
        ExpectedForm::ImplementationMethod => "an implementation method equation",
        ExpectedForm::Comma => ",",
        ExpectedForm::LeftParen => "(",
        ExpectedForm::RightParen => ")",
        ExpectedForm::LeftBrace => "{",
        ExpectedForm::RightBrace => "}",
        ExpectedForm::Greater => ">",
        ExpectedForm::Colon => ":",
        ExpectedForm::Equal => "=",
        ExpectedForm::Arrow => "->",
        ExpectedForm::FatArrow => "=>",
        ExpectedForm::LineEnd => "a logical line end",
        ExpectedForm::EndOfFile => "end of input",
    }
}
