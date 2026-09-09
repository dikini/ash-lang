//! Event-producing recursive-descent parsing and checked surface projection.

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
pub use project::{ProjectionError, project_module};

use crate::{
    diagnostic::{Diagnostic, SourceLabel},
    lexer::{Lexed, TokenKind},
    source::Span,
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
    /// A nominal type declaration.
    TypeDeclaration,
    /// A representation-preserving nominal declaration.
    NewtypeDeclaration,
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
/// No identifier or integer payload is copied into this diagnostic fact.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum FoundToken {
    /// An ordinary identifier.
    Identifier,
    /// An uppercase identifier.
    UpperIdentifier,
    /// An integer literal.
    Integer,
    /// Fixed punctuation, keyword or builtin type spelling.
    Spelling(&'static str),
    /// A logical line boundary.
    LineEnd,
    /// End of input.
    EndOfFile,
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
        })
    }
}

/// Parses one complete lexer result into an error-bearing concrete tree.
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

    let (events, diagnostics, resource_failure, syntax_work_exhausted, syntax_budget) = {
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
        };
        grammar::module(&mut parser);
        (
            parser.events,
            parser.diagnostics,
            parser.resource_failure,
            parser.syntax_work_exhausted,
            parser.syntax_budget,
        )
    };
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
    (
        cst::build(
            tokens,
            lexical_diagnostics,
            diagnostics,
            events,
            resource_failure,
        ),
        syntax_budget,
    )
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
}

impl Parser<'_> {
    fn start(&mut self, kind: NodeKind) {
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

    fn current_span(&self) -> Option<Span> {
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
        TokenKind::Hook => FoundToken::Spelling("hook"),
        TokenKind::Register => FoundToken::Spelling("register"),
        TokenKind::Cleanup => FoundToken::Spelling("cleanup"),
        TokenKind::Discard => FoundToken::Spelling("discard"),
        TokenKind::Import => FoundToken::Spelling("import"),
        TokenKind::As => FoundToken::Spelling("as"),
        TokenKind::Pub => FoundToken::Spelling("pub"),
        TokenKind::Opaque => FoundToken::Spelling("opaque"),
        TokenKind::Interface => FoundToken::Spelling("interface"),
        TokenKind::Impl => FoundToken::Spelling("impl"),
        TokenKind::Where => FoundToken::Spelling("where"),
        TokenKind::IntType => FoundToken::Spelling("Int"),
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
