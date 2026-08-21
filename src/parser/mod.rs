//! Event-producing recursive-descent parsing and checked surface projection.

mod cst;
mod event;
mod expression;
mod grammar;
mod project;

use std::fmt;
use std::ops::Deref;

pub use cst::{ConcreteElement, ConcreteNode, ConcreteTree, InternalReason};
pub use event::Event;
pub use project::{ProjectionError, project};

use crate::{
    diagnostic::{Diagnostic, SourceLabel},
    lexer::{Lexed, TokenKind},
    source::Span,
};

/// Conservative, replaceable protection for source structural nesting.
///
/// Groups, parenthesized types, arrows, operators/application, blocks, and
/// functions contribute. Fixed concrete scaffolding such as program, global,
/// interface, `Type`, and `AtomicType` wrappers does not. This is an
/// implementation resource budget, not an Ash language nesting restriction;
/// later fully iterative representations may replace it.
pub const STRUCTURAL_DEPTH_LIMIT: usize = 128;

/// A non-syntactic implementation resource failure.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ResourceFailure {
    /// Constructing another nested syntax layer would exceed the safe budget.
    StructuralDepth {
        /// The active implementation budget.
        limit: usize,
    },
}

/// The grammar role of one concrete node.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum NodeKind {
    /// A complete source file.
    Program,
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
    /// A binder-only source form.
    Binder,
    /// A binder with a type annotation.
    TypedBinder,
    /// A right-associated type.
    Type,
    /// An atomic type.
    AtomicType,
    /// A grouped type.
    ParenthesizedType,
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
    /// `(`.
    LeftParen,
    /// `)`.
    RightParen,
    /// `{`.
    LeftBrace,
    /// `}`.
    RightBrace,
    /// `:`.
    Colon,
    /// `=`.
    Equal,
    /// `->`.
    Arrow,
    /// A logical line boundary.
    LineEnd,
    /// End of input.
    EndOfFile,
}

/// A parser-owned reason retained independently from rendering.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ParseReason {
    /// The file has no required final result expression.
    ExpectedResult,
    /// A grammar form was absent.
    ExpectedForm,
    /// An operand was absent after an operator.
    ExpectedOperand,
    /// A parenthesized expression or type was not closed.
    UnclosedGroup,
    /// Equality was repeated despite being non-associative.
    RepeatedEquality,
    /// Tuple syntax is excluded from this increment.
    TupleSyntax,
    /// Match syntax is excluded from this increment.
    MatchSyntax,
    /// A function header contains more than one parameter.
    MultipleParameters,
    /// An equation contains more than one binder.
    MultipleBinders,
    /// A polymorphic header is excluded from this increment.
    PolymorphicHeader,
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
    /// Parsing completed one global before discovering the missing file result.
    PrecedingGlobalComplete {
        /// The first source token of the completed global.
        starting_at: Span,
        /// The final source token of the completed global.
        ending_at: Span,
        /// The logical line boundary consumed after the completed global.
        line_end: Span,
    },
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
    /// The closing brace owned by the current block.
    BlockClosingBrace,
    /// The closing parenthesis owned by the current grouped expression.
    ParenthesisClosing,
    /// End of input owned by the current program or incomplete nested form.
    EndOfFile,
}

/// One structured parser diagnostic and its parser-specific recovery facts.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ParseDiagnostic {
    diagnostic: Diagnostic<ParseReason>,
    /// Structured completion or synchronization facts.
    pub context: Vec<ParseContext>,
}

impl ParseDiagnostic {
    fn new(diagnostic: Diagnostic<ParseReason>) -> Self {
        Self {
            diagnostic,
            context: Vec::new(),
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
            Self::ExpectedResult => "parse.expected-result",
            Self::ExpectedForm => "parse.expected-form",
            Self::ExpectedOperand => "parse.expected-operand",
            Self::UnclosedGroup => "parse.unclosed-group",
            Self::RepeatedEquality => "parse.repeated-equality",
            Self::TupleSyntax => "parse.tuple-syntax",
            Self::MatchSyntax => "parse.match-syntax",
            Self::MultipleParameters => "parse.multiple-parameters",
            Self::MultipleBinders => "parse.multiple-binders",
            Self::PolymorphicHeader => "parse.polymorphic-header",
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
    let (events, diagnostics, resource_failure) = {
        let mut parser = Parser {
            tokens: &lexed.tokens,
            position: 0,
            events: Vec::new(),
            diagnostics: Vec::new(),
            pending_recoveries: Vec::new(),
            nesting_depth: 0,
            resource_failure: None,
        };
        grammar::program(&mut parser);
        (parser.events, parser.diagnostics, parser.resource_failure)
    };
    cst::build(
        lexed.tokens,
        lexed.diagnostics,
        diagnostics,
        events,
        resource_failure,
    )
}

pub(crate) struct Parser<'tokens> {
    tokens: &'tokens [crate::lexer::Token],
    position: usize,
    events: Vec<Event>,
    diagnostics: Vec<ParseDiagnostic>,
    pending_recoveries: Vec<usize>,
    nesting_depth: usize,
    resource_failure: Option<ResourceFailure>,
}

impl Parser<'_> {
    fn start(&mut self, kind: NodeKind) {
        self.events.push(Event::Start(kind));
    }

    fn finish(&mut self) {
        self.events.push(Event::Finish);
    }

    fn event_position(&self) -> usize {
        self.events.len()
    }

    fn insert_start(&mut self, position: usize, kind: NodeKind) -> bool {
        if position > self.events.len() {
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
        self.events.push(Event::Token(self.position));
        self.position += 1;
        true
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
            self.events.push(Event::Error(reason));
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
        self.events.push(Event::Error(reason));
        self.events.push(Event::Missing { expected, at });
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
        self.diagnostics.push(ParseDiagnostic::new(diagnostic));
        Some(index)
    }

    fn error_at_current(&mut self, reason: ParseReason) {
        if self.resource_failure.is_some() {
            return;
        }
        self.events.push(Event::Error(reason));
        let Some(at) = self.current_span() else {
            return;
        };
        let mut diagnostic = Diagnostic::new(reason, SourceLabel::new(at, primary_message(reason)));
        diagnostic.found = self.current().map(token_name).map(str::to_owned);
        self.diagnostics.push(ParseDiagnostic::new(diagnostic));
    }

    fn current_span(&self) -> Option<Span> {
        self.tokens
            .get(self.position)
            .or_else(|| self.tokens.last())
            .map(|token| token.span)
    }

    fn previous_span(&self) -> Option<Span> {
        self.position
            .checked_sub(1)
            .and_then(|position| self.tokens.get(position))
            .map(|token| token.span)
    }

    fn report_expected_result(&mut self, preceding_global: Option<(Span, Span, Span)>) {
        let before = self.diagnostics.len();
        self.report(ParseReason::ExpectedResult, ExpectedForm::Expression);
        if let (Some((starting_at, ending_at, line_end)), Some(diagnostic)) =
            (preceding_global, self.diagnostics.get_mut(before))
        {
            diagnostic
                .context
                .push(ParseContext::PrecedingGlobalComplete {
                    starting_at,
                    ending_at,
                    line_end,
                });
        }
    }

    fn pending_recovery_count(&self) -> usize {
        self.pending_recoveries.len()
    }

    fn diagnostic_count(&self) -> usize {
        self.diagnostics.len()
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
        if self.nesting_depth >= STRUCTURAL_DEPTH_LIMIT {
            self.fail_structural_depth();
            return false;
        }
        self.nesting_depth += 1;
        true
    }

    fn leave_structure(&mut self) {
        self.nesting_depth = self.nesting_depth.saturating_sub(1);
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
}

const fn synchronization_message(boundary: SynchronizationBoundary) -> &'static str {
    match boundary {
        SynchronizationBoundary::LogicalLineEnd => "parsing resumes at this logical line boundary",
        SynchronizationBoundary::BlockClosingBrace => "parsing resumes at this block closing brace",
        SynchronizationBoundary::ParenthesisClosing => {
            "parsing resumes at this closing parenthesis"
        }
        SynchronizationBoundary::EndOfFile => "parsing stops at end of input",
    }
}

fn same_variant(left: &TokenKind, right: &TokenKind) -> bool {
    std::mem::discriminant(left) == std::mem::discriminant(right)
}

fn token_name(kind: &TokenKind) -> &'static str {
    match kind {
        TokenKind::Identifier(_) => "identifier",
        TokenKind::Integer(_) => "integer",
        TokenKind::True => "true",
        TokenKind::False => "false",
        TokenKind::Fn => "fn",
        TokenKind::Let => "let",
        TokenKind::Rec => "rec",
        TokenKind::And => "and",
        TokenKind::IntType => "Int",
        TokenKind::BoolType => "Bool",
        TokenKind::UnitType => "Unit",
        TokenKind::LeftParen => "(",
        TokenKind::RightParen => ")",
        TokenKind::LeftBrace => "{",
        TokenKind::RightBrace => "}",
        TokenKind::Colon => ":",
        TokenKind::Equal => "=",
        TokenKind::EqualEqual => "==",
        TokenKind::Plus => "+",
        TokenKind::Star => "*",
        TokenKind::Arrow => "->",
        TokenKind::Comma => ",",
        TokenKind::Semicolon => ";",
        TokenKind::LineEnd => "line end",
        TokenKind::EndOfFile => "end of input",
    }
}

const fn primary_message(reason: ParseReason) -> &'static str {
    match reason {
        ParseReason::ExpectedResult => "the file requires a final result expression",
        ParseReason::ExpectedForm => "required syntax is missing",
        ParseReason::ExpectedOperand => "the operator requires a right operand",
        ParseReason::UnclosedGroup => "the opening parenthesis is not closed",
        ParseReason::RepeatedEquality => "equality is non-associative",
        ParseReason::TupleSyntax => "tuple syntax is not available in Mini-Ash",
        ParseReason::MatchSyntax => "match syntax is not available in Mini-Ash",
        ParseReason::MultipleParameters => "Mini-Ash functions have one parameter",
        ParseReason::MultipleBinders => "Mini-Ash equations have one binder",
        ParseReason::PolymorphicHeader => "polymorphic headers are not available in Mini-Ash",
        ParseReason::ExpectedRecursiveMember => {
            "the recursive delimiter requires another binding member"
        }
        ParseReason::UnexpectedAnd => "and is only accepted within a recursive binding group",
        ParseReason::Semicolon => "semicolons are not available in Mini-Ash",
        ParseReason::UnexpectedToken => "token is not accepted at this grammar position",
    }
}

const fn expected_name(expected: ExpectedForm) -> &'static str {
    match expected {
        ExpectedForm::Expression => "an expression",
        ExpectedForm::Operand => "an operand",
        ExpectedForm::Identifier => "an identifier",
        ExpectedForm::Type => "a type",
        ExpectedForm::LeftParen => "(",
        ExpectedForm::RightParen => ")",
        ExpectedForm::LeftBrace => "{",
        ExpectedForm::RightBrace => "}",
        ExpectedForm::Colon => ":",
        ExpectedForm::Equal => "=",
        ExpectedForm::Arrow => "->",
        ExpectedForm::LineEnd => "a logical line end",
        ExpectedForm::EndOfFile => "end of input",
    }
}
