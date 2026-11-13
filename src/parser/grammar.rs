//! Closed assembly of the grammar forms accepted by this parser dialect.

#[path = "foreign_grammar.rs"]
mod foreign;

use crate::lexer::TokenKind;

use super::{
    ExpectedForm, NodeKind, ParseReason, Parser, QuoteMode, SynchronizationBoundary, expression,
};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum GlobalDefinitionForm {
    Equational,
    InlineOperational,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum ExpressionPrefixForm {
    Block,
    Function,
    Match,
    Handler,
    Resume,
    Resource,
    Region,
    RegionSelection,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum PrimaryForm {
    Integer,
    String,
    Boolean,
    Identifier,
    Qualified,
    UpperIdentifier,
    Parenthesized,
    SyntaxQuote,
    Perform,
    Discard,
    Retain,
    Hook,
    Registration,
    Cleanup,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum AtomicTypeForm {
    Int,
    Bytes,
    String,
    Bool,
    Unit,
    Nominal,
    Parenthesized,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum PatternForm {
    Binder,
    Wildcard,
    Boolean,
    Constructor,
    Parenthesized,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum OperatorToken {
    EqualEqual,
    Plus,
    Star,
    #[cfg(test)]
    MockSemicolon,
}

impl OperatorToken {
    pub(super) fn matches(self, kind: &TokenKind) -> bool {
        let selected = matches!(
            (self, kind),
            (Self::EqualEqual, TokenKind::EqualEqual)
                | (Self::Plus, TokenKind::Plus)
                | (Self::Star, TokenKind::Star)
        );
        #[cfg(test)]
        {
            selected || matches!((self, kind), (Self::MockSemicolon, TokenKind::Semicolon))
        }
        #[cfg(not(test))]
        {
            selected
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum Associativity {
    Left,
    NonAssociative,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct InfixDescriptor {
    pub(super) token: OperatorToken,
    pub(super) precedence: u8,
    pub(super) associativity: Associativity,
    pub(super) result: NodeKind,
}

impl InfixDescriptor {
    pub(super) const fn binding_powers(self) -> (u8, u8) {
        match self.associativity {
            Associativity::Left | Associativity::NonAssociative => {
                (self.precedence, self.precedence.saturating_add(1))
            }
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct ApplicationDescriptor {
    pub(super) left_binding_power: u8,
    pub(super) right_binding_power: u8,
    pub(super) result: NodeKind,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct ExpressionDialect {
    pub(super) primary_forms: &'static [PrimaryForm],
    pub(super) infix: &'static [InfixDescriptor],
    pub(super) application: ApplicationDescriptor,
}

pub(super) struct ParserDialect {
    global_definitions: &'static [GlobalDefinitionForm],
    expression_prefixes: &'static [ExpressionPrefixForm],
    pub(super) expression: ExpressionDialect,
    pattern_forms: &'static [PatternForm],
    atomic_types: &'static [AtomicTypeForm],
}

/// The sole closed assembly of syntax forms selected for Ash modules.
const CURRENT_ASH_DIALECT: ParserDialect = ParserDialect {
    global_definitions: &[
        GlobalDefinitionForm::Equational,
        GlobalDefinitionForm::InlineOperational,
    ],
    expression_prefixes: &[
        ExpressionPrefixForm::Block,
        ExpressionPrefixForm::Function,
        ExpressionPrefixForm::Match,
        ExpressionPrefixForm::Handler,
        ExpressionPrefixForm::Resume,
        ExpressionPrefixForm::Resource,
        ExpressionPrefixForm::Region,
        ExpressionPrefixForm::RegionSelection,
    ],
    expression: ExpressionDialect {
        primary_forms: &[
            PrimaryForm::Integer,
            PrimaryForm::String,
            PrimaryForm::Boolean,
            PrimaryForm::Identifier,
            PrimaryForm::Qualified,
            PrimaryForm::UpperIdentifier,
            PrimaryForm::Parenthesized,
            PrimaryForm::SyntaxQuote,
            PrimaryForm::Perform,
            PrimaryForm::Discard,
            PrimaryForm::Retain,
            PrimaryForm::Hook,
            PrimaryForm::Registration,
            PrimaryForm::Cleanup,
        ],
        infix: &[
            InfixDescriptor {
                token: OperatorToken::EqualEqual,
                precedence: 10,
                associativity: Associativity::NonAssociative,
                result: NodeKind::EqualityExpression,
            },
            InfixDescriptor {
                token: OperatorToken::Plus,
                precedence: 20,
                associativity: Associativity::Left,
                result: NodeKind::AdditiveExpression,
            },
            InfixDescriptor {
                token: OperatorToken::Star,
                precedence: 30,
                associativity: Associativity::Left,
                result: NodeKind::MultiplicativeExpression,
            },
        ],
        application: ApplicationDescriptor {
            left_binding_power: 40,
            right_binding_power: 41,
            result: NodeKind::ApplicationExpression,
        },
    },
    pattern_forms: &[
        PatternForm::Binder,
        PatternForm::Wildcard,
        PatternForm::Boolean,
        PatternForm::Constructor,
        PatternForm::Parenthesized,
    ],
    atomic_types: &[
        AtomicTypeForm::Int,
        AtomicTypeForm::Bytes,
        AtomicTypeForm::String,
        AtomicTypeForm::Bool,
        AtomicTypeForm::Unit,
        AtomicTypeForm::Nominal,
        AtomicTypeForm::Parenthesized,
    ],
};

pub(super) const fn selected_dialect() -> &'static ParserDialect {
    &CURRENT_ASH_DIALECT
}

pub(super) fn module_header(parser: &mut Parser<'_>) {
    parser.start(NodeKind::Module);
    while parser.at(&TokenKind::Import)
        || (parser.at(&TokenKind::Pub) && parser.nth(1) == Some(&TokenKind::Import))
    {
        import_declaration(parser);
        if !parser.expect(&TokenKind::LineEnd, ExpectedForm::LineEnd) {
            break;
        }
    }
}

pub(super) fn module_body(parser: &mut Parser<'_>) {
    let mut declaration_boundary_failed = false;
    while starts_module_declaration(parser) {
        let frame = parser.selected_declaration_syntax().and_then(|selected| {
            parser
                .current_span()
                .map(|invocation| (invocation, selected.declaration.span))
        });
        let diagnostic_start = parser.diagnostics.len();
        let declaration_outcome = module_declaration(parser);
        let recovered_to_end = declaration_outcome == TypeParametersOutcome::RecoveredToEndOfFile
            && parser.at(&TokenKind::EndOfFile);
        let line_end = recovered_to_end || expect_declaration_line_end(parser);
        if parser.diagnostics.len() > diagnostic_start
            && let Some((invocation, definition)) = frame
        {
            let frame = std::sync::Arc::new(crate::syntax::ExpansionFrame {
                invocation,
                definition,
            });
            for diagnostic in &mut parser.diagnostics[diagnostic_start..] {
                diagnostic
                    .diagnostic
                    .primary
                    .inherit_frames(std::slice::from_ref(&frame));
            }
        }
        if recovered_to_end {
            continue;
        }
        if !line_end {
            declaration_boundary_failed = true;
            break;
        }
    }
    if parser.at(&TokenKind::EndOfFile) {
        let _ = parser.bump();
    } else if declaration_boundary_failed {
        parser.consume_rest();
    } else {
        if parser.at(&TokenKind::Semicolon) {
            parser.error_at_current(ParseReason::Semicolon);
        } else if parser.at(&TokenKind::And) {
            parser.error_at_current(ParseReason::UnexpectedAnd);
        } else {
            parser.error_at_current(ParseReason::UnexpectedToken);
        }
        parser.consume_rest();
    }
    parser.finish();
}

/// Parse exactly one module declaration without expanding it.
pub(super) fn declaration_fragment(parser: &mut Parser<'_>) {
    if starts_module_declaration(parser) {
        let outcome = module_declaration(parser);
        let recovered_to_end = outcome == TypeParametersOutcome::RecoveredToEndOfFile
            && parser.at(&TokenKind::EndOfFile);
        if !recovered_to_end {
            let _ = expect_declaration_line_end(parser);
        }
    } else {
        parser.error_at_current(ParseReason::UnexpectedToken);
    }
    if !parser.at(&TokenKind::EndOfFile) {
        parser.error_at_current(ParseReason::UnexpectedToken);
        parser.consume_rest();
    }
    if parser.at(&TokenKind::EndOfFile) {
        let _ = parser.bump();
    }
    parser.finish();
}

fn expect_declaration_line_end(parser: &mut Parser<'_>) -> bool {
    let recovered_group = parser.take_recovered_expression_group_boundary();
    if recovered_group && parser.at(&TokenKind::EndOfFile) {
        true
    } else {
        parser.expect(&TokenKind::LineEnd, ExpectedForm::LineEnd)
    }
}

fn import_declaration(parser: &mut Parser<'_>) {
    parser.start(NodeKind::ImportDeclaration);
    let public = parser.at(&TokenKind::Pub);
    if public {
        let _ = parser.bump();
    }
    let _ = parser.expect(&TokenKind::Import, ExpectedForm::Identifier);
    module_path(parser);
    if parser.at(&TokenKind::As) {
        if public {
            reject_import_line(parser, ExpectedForm::LeftParen);
        } else {
            let _ = parser.bump();
            expect_upper_identifier(parser);
        }
    } else if parser.at(&TokenKind::LeftParen) {
        let _ = parser.bump();
        let mut complete = import_item(parser, public);
        while complete && parser.at(&TokenKind::Comma) {
            let _ = parser.bump();
            complete = import_item(parser, public);
        }
        if complete {
            let _ = parser.expect(&TokenKind::RightParen, ExpectedForm::RightParen);
        }
    } else {
        let expected = if public {
            ExpectedForm::LeftParen
        } else {
            ExpectedForm::Identifier
        };
        if public {
            reject_import_line(parser, expected);
        } else {
            parser.report(ParseReason::ExpectedForm, expected);
        }
    }
    parser.finish();
}

fn module_path(parser: &mut Parser<'_>) {
    parser.start(NodeKind::ModulePath);
    let builtin_syntax = parser.at(&TokenKind::At)
        && matches!(parser.nth(1), Some(TokenKind::Identifier(name)) if name == "builtin")
        && parser.nth(2) == Some(&TokenKind::Dot)
        && matches!(parser.nth(3), Some(TokenKind::Identifier(name)) if name == "compiler")
        && parser.nth(4) == Some(&TokenKind::Dot)
        && parser.nth(5) == Some(&TokenKind::SyntaxKeyword)
        && parser.nth(6) != Some(&TokenKind::Dot);
    if builtin_syntax {
        for _ in 0..6 {
            let _ = parser.bump();
        }
        parser.finish();
        return;
    }
    let absolute = parser.at(&TokenKind::At);
    if absolute {
        let _ = parser.bump();
    }
    expect_lower_identifier(parser);
    if absolute {
        let _ = parser.expect(&TokenKind::Dot, ExpectedForm::Identifier);
        expect_lower_identifier(parser);
    }
    while parser.at(&TokenKind::Dot) {
        let _ = parser.bump();
        expect_lower_identifier(parser);
    }
    parser.finish();
}

fn import_item(parser: &mut Parser<'_>, public: bool) -> bool {
    parser.start(NodeKind::ImportItem);
    if parser.at(&TokenKind::SyntaxKeyword) {
        if public {
            reject_import_line(parser, ExpectedForm::Identifier);
            parser.finish();
            return false;
        }
        let _ = parser.bump();
        expect_syntax_name(parser);
        if parser.at(&TokenKind::As) {
            let _ = parser.bump();
            expect_syntax_name(parser);
        }
    } else if parser.at(&TokenKind::Impl) {
        let _ = parser.bump();
        if !parser.at_upper_identifier() {
            reject_import_line(parser, ExpectedForm::Identifier);
            parser.finish();
            return false;
        }
        let _ = parser.bump();
        if parser.at(&TokenKind::As) {
            reject_import_line(parser, ExpectedForm::RightParen);
            parser.finish();
            return false;
        }
    } else {
        expect_import_name(parser);
        if parser.at(&TokenKind::As) {
            let _ = parser.bump();
            expect_import_name(parser);
        }
    }
    parser.finish();
    true
}

fn reject_import_line(parser: &mut Parser<'_>, expected: ExpectedForm) {
    parser.start(NodeKind::Error);
    let recovery_start = parser.pending_recovery_count();
    if let Some(primary) = parser.current_span()
        && let Some(diagnostic) =
            parser.report_at(ParseReason::ExpectedForm, expected, primary, None)
    {
        parser.mark_pending_recovery(diagnostic);
    }
    while !matches!(
        parser.current(),
        Some(TokenKind::LineEnd | TokenKind::EndOfFile) | None
    ) {
        let _ = parser.bump();
    }
    if parser.at(&TokenKind::LineEnd) {
        parser.resolve_pending_at_current(recovery_start, SynchronizationBoundary::LogicalLineEnd);
    } else {
        parser.resolve_pending_at_current(recovery_start, SynchronizationBoundary::EndOfFile);
    }
    parser.finish();
}

fn expect_import_name(parser: &mut Parser<'_>) {
    if matches!(
        parser.current(),
        Some(TokenKind::Identifier(_) | TokenKind::UpperIdentifier(_))
    ) {
        let _ = parser.bump();
    } else {
        parser.report(ParseReason::ExpectedForm, ExpectedForm::Identifier);
    }
}

fn expect_declaration_metaname(parser: &mut Parser<'_>) {
    if parser
        .current()
        .and_then(super::declaration_metaname)
        .is_some()
    {
        let _ = parser.bump();
    } else {
        parser.report(ParseReason::ExpectedForm, ExpectedForm::Identifier);
    }
}

fn expect_lower_identifier(parser: &mut Parser<'_>) {
    if matches!(parser.current(), Some(TokenKind::Identifier(_))) {
        let _ = parser.bump();
    } else {
        parser.report(ParseReason::ExpectedForm, ExpectedForm::Identifier);
    }
}

fn expect_syntax_name(parser: &mut Parser<'_>) {
    if matches!(parser.current(), Some(TokenKind::Identifier(name)) if name.as_bytes().first().is_some_and(u8::is_ascii_lowercase))
    {
        let _ = parser.bump();
    } else {
        parser.report(ParseReason::ExpectedForm, ExpectedForm::Identifier);
    }
}

fn expect_upper_identifier(parser: &mut Parser<'_>) {
    if parser.at_upper_identifier() {
        let _ = parser.bump();
    } else {
        parser.report(ParseReason::ExpectedForm, ExpectedForm::Identifier);
    }
}

fn starts_module_declaration(parser: &Parser<'_>) -> bool {
    parser.at_forwarded_declaration()
        || parser.selected_declaration_syntax().is_some()
        || foreign::starts_library(parser)
        || parser.at(&TokenKind::Type)
        || parser.at(&TokenKind::Newtype)
        || parser.at(&TokenKind::Resource)
        || parser.at(&TokenKind::Effect)
        || parser.at(&TokenKind::Interface)
        || parser.at(&TokenKind::Impl)
        || starts_global(parser)
        || parser.at(&TokenKind::Pub)
            && matches!(
                parser.nth(1),
                Some(
                    TokenKind::Resource
                        | TokenKind::Type
                        | TokenKind::Newtype
                        | TokenKind::Effect
                        | TokenKind::Opaque
                        | TokenKind::Interface
                        | TokenKind::Impl
                        | TokenKind::Fn
                        | TokenKind::SyntaxKeyword
                        | TokenKind::Identifier(_)
                )
            )
}

fn module_declaration(parser: &mut Parser<'_>) -> TypeParametersOutcome {
    if parser.at_forwarded_declaration() {
        parser.start(NodeKind::DeclarationFragment);
        let _ = parser.bump();
        parser.finish();
        TypeParametersOutcome::Complete
    } else if parser.selected_declaration_syntax().is_some() {
        if !parser.charge_declaration_matcher() {
            return TypeParametersOutcome::Complete;
        }
        let matcher = parser
            .selected_declaration_syntax()
            .expect("the selected declaration syntax has a matcher")
            .declaration
            .matcher
            .clone();
        syntax_invocation(parser, NodeKind::DeclarationSyntaxInvocation, &matcher);
        TypeParametersOutcome::Complete
    } else if starts_syntax_declaration(parser) {
        syntax_declaration(parser);
        TypeParametersOutcome::Complete
    } else if foreign::starts_library(parser) {
        foreign::library(parser)
    } else if parser.at(&TokenKind::Resource)
        || parser.at(&TokenKind::Pub) && parser.nth(1) == Some(&TokenKind::Resource)
    {
        resource_definition(parser)
    } else if starts_newtype_declaration(parser) {
        newtype_declaration(parser, true)
    } else if parser.at(&TokenKind::Type)
        || parser.at(&TokenKind::Pub)
            && matches!(parser.nth(1), Some(TokenKind::Type | TokenKind::Opaque))
    {
        type_declaration(parser)
    } else if parser.at(&TokenKind::Interface)
        || parser.at(&TokenKind::Pub) && matches!(parser.nth(1), Some(TokenKind::Interface))
    {
        interface_declaration(parser)
    } else if parser.at(&TokenKind::Effect)
        || parser.at(&TokenKind::Pub) && matches!(parser.nth(1), Some(TokenKind::Effect))
    {
        effect_declaration(parser)
    } else if parser.at(&TokenKind::Impl)
        || parser.at(&TokenKind::Pub) && matches!(parser.nth(1), Some(TokenKind::Impl))
    {
        implementation_declaration(parser)
    } else {
        global_definition(parser)
    }
}

fn starts_syntax_declaration(parser: &Parser<'_>) -> bool {
    parser.at(&TokenKind::Pub) && parser.nth(1) == Some(&TokenKind::SyntaxKeyword)
}

fn syntax_declaration(parser: &mut Parser<'_>) {
    parser.start(NodeKind::SyntaxDeclaration);
    let _ = parser.bump(); // pub
    let _ = parser.bump(); // syntax
    let declaration = matches!(parser.current(), Some(TokenKind::Identifier(name)) if name == "declaration")
        && parser.nth(1) == Some(&TokenKind::Colon)
        && parser.nth(2) == Some(&TokenKind::LeftParen);
    let derive = matches!(parser.current(), Some(TokenKind::Identifier(name)) if name == "derive")
        && parser.nth(1) == Some(&TokenKind::Colon)
        && parser.nth(2) == Some(&TokenKind::LeftParen);
    if declaration || derive {
        let _ = parser.bump(); // declaration or derive
        let _ = parser.bump(); // :
        let _ = parser.bump(); // (
        expect_syntax_name(parser);
        let _ = parser.expect(&TokenKind::RightParen, ExpectedForm::RightParen);
    } else {
        expect_syntax_name(parser);
    }
    if derive {
        if parser.at(&TokenKind::Dollar) {
            parser.start(NodeKind::SyntaxCapture);
            let _ = parser.bump();
            expect_syntax_name(parser);
            let _ = parser.expect(&TokenKind::Colon, ExpectedForm::Colon);
            if matches!(parser.current(), Some(TokenKind::Identifier(name)) if name == "ident") {
                let _ = parser.bump();
            } else {
                parser.report(ParseReason::ExpectedForm, ExpectedForm::Identifier);
            }
            parser.finish();
        }
        if !matches!(
            parser.current(),
            Some(TokenKind::FatArrow | TokenKind::LineEnd | TokenKind::EndOfFile) | None
        ) {
            parser.report(ParseReason::ExpectedForm, ExpectedForm::FatArrow);
            while !matches!(
                parser.current(),
                Some(TokenKind::FatArrow | TokenKind::LineEnd | TokenKind::EndOfFile) | None
            ) {
                let _ = parser.bump();
            }
        }
        syntax_declaration_body(parser, false, true);
        parser.finish();
        return;
    }
    let matcher_start = parser.event_position();
    let mut names = std::collections::HashSet::new();
    let mut previous_capture = false;
    let mut final_expression = false;
    while !matches!(
        parser.current(),
        Some(TokenKind::FatArrow | TokenKind::LineEnd | TokenKind::EndOfFile) | None
    ) {
        if declaration
            && (matches!(
                parser.current(),
                Some(TokenKind::LeftParen | TokenKind::LeftBrace)
            ) || parser.at(&TokenKind::Dollar) && parser.nth(1) == Some(&TokenKind::LeftParen))
        {
            let length = parser.events.len();
            let extra = length
                .checked_sub(matcher_start)
                .and_then(|shifted| {
                    shifted.checked_add(if length == parser.events.capacity() {
                        length
                    } else {
                        0
                    })
                })
                .and_then(|units| units.checked_add(3))
                .unwrap_or(usize::MAX);
            if !parser.charge_matcher_work(extra)
                || !parser.insert_start(matcher_start, NodeKind::SyntaxMatcherSequence)
            {
                break;
            }
            // The flat prefix has already used the legacy HashSet. Move it once
            // to a deterministic extended-header accumulator, paying the
            // table walk, destination slots and moved String values first. Twice
            // the reported capacity is a conservative bucket-walk reservation.
            let names_work = names
                .capacity()
                .saturating_mul(2)
                .saturating_add(names.len().saturating_mul(2));
            if !parser.charge_matcher_work(names_work) {
                break;
            }
            let mut extended_names = Vec::with_capacity(names.len());
            extended_names.extend(std::mem::take(&mut names));
            let _ =
                syntax_matcher_items(parser, &mut extended_names, None, false, previous_capture);
            parser.finish();
            break;
        }
        if parser.at(&TokenKind::Dollar) {
            parser.start(NodeKind::SyntaxCapture);
            if previous_capture {
                parser.report(ParseReason::ExpectedForm, ExpectedForm::Identifier);
            }
            let _ = parser.bump();
            let name = if declaration {
                parser.current().and_then(super::declaration_metaname)
            } else {
                match parser.current() {
                    Some(TokenKind::Identifier(name)) => Some(name.as_str()),
                    _ => None,
                }
            };
            if name.is_some_and(|name| !names.insert(name.to_owned())) {
                parser.report(ParseReason::ExpectedForm, ExpectedForm::Identifier);
            }
            if declaration {
                expect_declaration_metaname(parser);
            } else {
                expect_lower_identifier(parser);
            }
            let _ = parser.expect(&TokenKind::Colon, ExpectedForm::Colon);
            final_expression =
                matches!(parser.current(), Some(TokenKind::Identifier(name)) if name == "expr");
            if matches!(parser.current(), Some(TokenKind::Identifier(name)) if name == "expr" || name == "ident" || declaration && (name == "pattern" || name == "declaration"))
                || declaration && parser.at(&TokenKind::Type)
            {
                let _ = parser.bump();
            } else {
                parser.report(ParseReason::ExpectedForm, ExpectedForm::Identifier);
            }
            parser.finish();
            previous_capture = true;
        } else {
            if matches!(
                parser.current(),
                Some(
                    TokenKind::LeftParen
                        | TokenKind::RightParen
                        | TokenKind::LeftBrace
                        | TokenKind::RightBrace
                )
            ) {
                parser.report(ParseReason::ExpectedForm, ExpectedForm::FatArrow);
            }
            let _ = parser.bump();
            previous_capture = false;
            final_expression = false;
        }
    }
    if !declaration && (!previous_capture || !final_expression || names.is_empty()) {
        parser.report(ParseReason::ExpectedForm, ExpectedForm::Identifier);
    }
    syntax_declaration_body(parser, declaration, declaration);
    parser.finish();
}

// FIRST keeps the actual capture category, since the accepted starts of a
// declaration, type, pattern and expression are not the Identifier starts.
#[derive(Clone, Copy)]
enum MatcherStart {
    Literal(usize),
    Capture(crate::surface::SurfaceSyntaxCaptureKind),
}

fn capture_can_start_with(
    kind: crate::surface::SurfaceSyntaxCaptureKind,
    token: &TokenKind,
) -> bool {
    use crate::surface::SurfaceSyntaxCaptureKind as Kind;
    match kind {
        Kind::Identifier => matches!(
            token,
            TokenKind::Identifier(_) | TokenKind::UpperIdentifier(_)
        ),
        Kind::Declaration => matches!(token, TokenKind::LeftBrace),
        Kind::Type => matches!(
            token,
            TokenKind::UpperIdentifier(_)
                | TokenKind::IntType
                | TokenKind::BytesType
                | TokenKind::StringType
                | TokenKind::BoolType
                | TokenKind::UnitType
                | TokenKind::LeftParen
        ),
        Kind::Pattern => matches!(
            token,
            TokenKind::Identifier(_)
                | TokenKind::UpperIdentifier(_)
                | TokenKind::Wildcard
                | TokenKind::True
                | TokenKind::False
                | TokenKind::LeftParen
        ),
        Kind::Expression => matches!(
            token,
            TokenKind::Identifier(_)
                | TokenKind::UpperIdentifier(_)
                | TokenKind::Integer(_)
                | TokenKind::StringLiteral(_)
                | TokenKind::True
                | TokenKind::False
                | TokenKind::LeftParen
                | TokenKind::LeftBrace
                | TokenKind::Fn
                | TokenKind::Match
                | TokenKind::Perform
                | TokenKind::Handle
                | TokenKind::Resume
                | TokenKind::Resource
                | TokenKind::Region
                | TokenKind::Using
                | TokenKind::SyntaxKeyword
                | TokenKind::Discard
                | TokenKind::Retain
                | TokenKind::Hook
                | TokenKind::Register
                | TokenKind::Cleanup
        ),
    }
}

fn push_matcher_start(
    parser: &mut Parser<'_>,
    starts: &mut Vec<MatcherStart>,
    start: MatcherStart,
) -> bool {
    let growth = if starts.len() == starts.capacity() {
        starts.len().saturating_mul(2).saturating_add(1)
    } else {
        0
    };
    if !parser.charge_matcher_work(growth.saturating_add(1)) {
        return false;
    }
    starts.reserve_exact(1);
    starts.push(start);
    true
}

fn matcher_starts_overlap(
    parser: &mut Parser<'_>,
    left: MatcherStart,
    right: MatcherStart,
) -> bool {
    let (left, right) = match (left, right) {
        (MatcherStart::Literal(left), MatcherStart::Literal(right)) => (left, right),
        (MatcherStart::Capture(left), MatcherStart::Capture(right)) => {
            use crate::surface::SurfaceSyntaxCaptureKind as Kind;
            if !parser.charge_matcher_work(1) {
                return false;
            }
            return !matches!(
                (left, right),
                (
                    Kind::Declaration,
                    Kind::Identifier | Kind::Type | Kind::Pattern
                ) | (
                    Kind::Identifier | Kind::Type | Kind::Pattern,
                    Kind::Declaration
                )
            );
        }
        (MatcherStart::Capture(kind), MatcherStart::Literal(index))
        | (MatcherStart::Literal(index), MatcherStart::Capture(kind)) => {
            if !parser.charge_matcher_work(1) {
                return false;
            }
            return capture_can_start_with(kind, &parser.tokens[index].kind);
        }
    };
    let left_token = &parser.tokens[left];
    let right_token = &parser.tokens[right];
    let left_range = left_token.span.range();
    let right_range = right_token.span.range();
    let work = ((left_range.end() - left_range.start()) as usize)
        .saturating_add((right_range.end() - right_range.start()) as usize);
    if !parser.charge_matcher_work(work.saturating_add(2)) {
        return false;
    }
    if parser.tokens[left].kind != parser.tokens[right].kind {
        return false;
    }
    // Brace-group line ends are logical tokens, independent of LF or CRLF.
    if parser.tokens[left].kind == TokenKind::LineEnd {
        return true;
    }
    if let Some(source) = parser.syntax_source {
        let text = source.text();
        return text
            .get(left_range.start() as usize..left_range.end() as usize)
            .zip(text.get(right_range.start() as usize..right_range.end() as usize))
            .is_some_and(|(a, b)| a == b);
    }
    // A standalone token-only parse has no spelling for decoded values. Its
    // extended child is still refused by the unbudgeted source projector.
    !matches!(
        parser.tokens[left].kind,
        TokenKind::Integer(_) | TokenKind::StringLiteral(_)
    )
}

type MatcherStarts = Vec<MatcherStart>;
type PendingMatcherRepeats = Vec<(MatcherStarts, Option<usize>, bool)>;

fn matcher_pending_overlap(
    parser: &mut Parser<'_>,
    pending: &PendingMatcherRepeats,
    following: &[MatcherStart],
) -> Option<bool> {
    for (starts, separator, star) in pending {
        if !parser.charge_matcher_work(1) {
            return None;
        }
        for following in following {
            if !parser.charge_matcher_work(1) {
                return None;
            }
            if let Some(separator) = separator {
                let overlaps =
                    matcher_starts_overlap(parser, MatcherStart::Literal(*separator), *following);
                if parser.resource_failure.is_some() {
                    return None;
                }
                if overlaps {
                    return Some(true);
                }
            }
            if separator.is_none() || *star {
                for start in starts {
                    if !parser.charge_matcher_work(1) {
                        return None;
                    }
                    let overlaps = matcher_starts_overlap(parser, *start, *following);
                    if parser.resource_failure.is_some() {
                        return None;
                    }
                    if overlaps {
                        return Some(true);
                    }
                }
            }
        }
    }
    Some(false)
}

fn reserve_pending_matchers(
    parser: &mut Parser<'_>,
    pending: &mut PendingMatcherRepeats,
    additional: usize,
) -> bool {
    let needed = pending.len().saturating_add(additional);
    let growth = if needed > pending.capacity() {
        pending.len().saturating_add(needed)
    } else {
        0
    };
    if !parser.charge_matcher_work(growth.saturating_add(additional)) {
        return false;
    }
    pending.reserve_exact(additional);
    true
}

// Parses the remainder of an extended declaration matcher. The tuple returned
// by this walk contains nullable, first/last capture, FIRST and pending repeats.
fn syntax_matcher_items(
    parser: &mut Parser<'_>,
    names: &mut Vec<String>,
    closing: Option<TokenKind>,
    braces: bool,
    mut previous_capture: bool,
) -> (bool, bool, bool, MatcherStarts, PendingMatcherRepeats) {
    let mut nullable = true;
    let mut first_capture = false;
    let mut first = Vec::new();
    // A pending repeat can meet a later item through nullable intervening items.
    // Each entry owns its temporary FIRST list, separator token, and star flag.
    let mut pending = PendingMatcherRepeats::new();
    loop {
        if parser.resource_failure.is_some()
            || closing.as_ref().is_some_and(|end| parser.at(end))
            || matches!(
                parser.current(),
                Some(TokenKind::FatArrow | TokenKind::EndOfFile) | None
            )
            || parser.at(&TokenKind::LineEnd) && !braces
        {
            break;
        }
        if !parser.charge_matcher_work(1) {
            break;
        }
        let part_start = parser.position;
        let part_nullable;
        let part_first_capture;
        let part_last_capture;
        let mut part_first = Vec::new();
        let mut part_pending = PendingMatcherRepeats::new();
        let mut repeat = None;
        if parser.at(&TokenKind::Dollar) && parser.nth(1) == Some(&TokenKind::LeftParen) {
            if !parser.enter_structure() {
                break;
            }
            if !parser.charge_matcher_work(3) {
                parser.leave_structure();
                break;
            }
            parser.start(NodeKind::SyntaxMatcherRepeat);
            let _ = parser.bump(); // $
            let _ = parser.bump(); // (
            let (body_nullable, body_first_capture, body_last_capture, body_first, body_pending) =
                syntax_matcher_items(parser, names, Some(TokenKind::RightParen), false, false);
            let _ = parser.expect(&TokenKind::RightParen, ExpectedForm::RightParen);
            let mut separator = None;
            if !matches!(parser.current(), Some(TokenKind::Star | TokenKind::Plus)) {
                if matches!(
                    parser.current(),
                    Some(
                        TokenKind::Dollar
                            | TokenKind::FatArrow
                            | TokenKind::LineEnd
                            | TokenKind::LeftParen
                            | TokenKind::RightParen
                            | TokenKind::LeftBrace
                            | TokenKind::RightBrace
                            | TokenKind::EndOfFile
                    ) | None
                ) {
                    parser.report(ParseReason::ExpectedForm, ExpectedForm::Identifier);
                } else {
                    separator = Some(parser.position);
                    let _ = parser.bump();
                }
            }
            part_nullable = parser.at(&TokenKind::Star);
            if matches!(parser.current(), Some(TokenKind::Star | TokenKind::Plus)) {
                let _ = parser.bump();
            } else {
                parser.report(ParseReason::ExpectedForm, ExpectedForm::Identifier);
            }
            if body_nullable {
                parser.report(ParseReason::ExpectedForm, ExpectedForm::Identifier);
            }
            let separator_start = separator.map(MatcherStart::Literal);
            let cycle_follow = if separator.is_some() {
                std::slice::from_ref(separator_start.as_ref().unwrap())
            } else {
                body_first.as_slice()
            };
            let cycle_overlap = matcher_pending_overlap(parser, &body_pending, cycle_follow);
            if cycle_overlap == Some(true) {
                let span = parser.tokens[separator.unwrap_or(part_start)].span;
                parser.error_at_span(ParseReason::MatcherRepetitionAmbiguous, span);
            }
            parser.finish();
            parser.leave_structure();
            if cycle_overlap.is_none() {
                break;
            }
            part_first = body_first;
            part_pending = body_pending;
            part_first_capture = body_first_capture;
            part_last_capture = body_last_capture;
            repeat = Some((separator, part_nullable));
        } else if matches!(
            parser.current(),
            Some(TokenKind::LeftParen | TokenKind::LeftBrace)
        ) {
            let is_brace = parser.at(&TokenKind::LeftBrace);
            if !push_matcher_start(parser, &mut part_first, MatcherStart::Literal(part_start)) {
                break;
            }
            if !parser.enter_structure() {
                break;
            }
            if !parser.charge_matcher_work(3) {
                parser.leave_structure();
                break;
            }
            parser.start(NodeKind::SyntaxMatcherGroup);
            let _ = parser.bump();
            let end = if is_brace {
                TokenKind::RightBrace
            } else {
                TokenKind::RightParen
            };
            let _ = syntax_matcher_items(parser, names, Some(end.clone()), is_brace, false);
            let expected = if is_brace {
                ExpectedForm::RightBrace
            } else {
                ExpectedForm::RightParen
            };
            let _ = parser.expect(&end, expected);
            parser.finish();
            parser.leave_structure();
            part_nullable = false;
            part_first_capture = false;
            part_last_capture = false;
        } else if parser.at(&TokenKind::Dollar) {
            parser.start(NodeKind::SyntaxCapture);
            let _ = parser.bump();
            let index = parser.position;
            let length = parser
                .current()
                .and_then(super::declaration_metaname)
                .map(str::len);
            if let Some(length) = length {
                let mut duplicate = false;
                for existing in names.iter() {
                    if !parser.charge_matcher_work(existing.len().min(length).saturating_add(1)) {
                        break;
                    }
                    let found = super::declaration_metaname(&parser.tokens[index].kind)
                        .expect("the metaname was checked above");
                    duplicate |= existing == found;
                }
                if parser.resource_failure.is_some() {
                    parser.finish();
                    break;
                }
                if duplicate {
                    parser.report(ParseReason::ExpectedForm, ExpectedForm::Identifier);
                } else {
                    let growth = if names.len() == names.capacity() {
                        names.len().saturating_mul(2).saturating_add(1)
                    } else {
                        0
                    };
                    if !parser.charge_matcher_work(length.saturating_add(growth).saturating_add(1))
                    {
                        parser.finish();
                        break;
                    }
                    names.reserve_exact(1);
                    let name = super::declaration_metaname(&parser.tokens[index].kind)
                        .expect("the metaname was checked above")
                        .to_owned();
                    names.push(name);
                }
            }
            expect_declaration_metaname(parser);
            let _ = parser.expect(&TokenKind::Colon, ExpectedForm::Colon);
            let kind = match parser.current() {
                Some(TokenKind::Identifier(name)) if name == "expr" => {
                    Some(crate::surface::SurfaceSyntaxCaptureKind::Expression)
                }
                Some(TokenKind::Identifier(name)) if name == "ident" => {
                    Some(crate::surface::SurfaceSyntaxCaptureKind::Identifier)
                }
                Some(TokenKind::Identifier(name)) if name == "pattern" => {
                    Some(crate::surface::SurfaceSyntaxCaptureKind::Pattern)
                }
                Some(TokenKind::Identifier(name)) if name == "declaration" => {
                    Some(crate::surface::SurfaceSyntaxCaptureKind::Declaration)
                }
                Some(TokenKind::Type) => Some(crate::surface::SurfaceSyntaxCaptureKind::Type),
                _ => None,
            };
            if let Some(kind) = kind {
                if !push_matcher_start(parser, &mut part_first, MatcherStart::Capture(kind)) {
                    parser.finish();
                    break;
                }
                let _ = parser.bump();
            } else {
                parser.report(ParseReason::ExpectedForm, ExpectedForm::Identifier);
            }
            parser.finish();
            part_nullable = false;
            part_first_capture = true;
            part_last_capture = true;
        } else if matches!(
            parser.current(),
            Some(TokenKind::RightParen | TokenKind::RightBrace)
        ) {
            parser.report(ParseReason::ExpectedForm, ExpectedForm::Identifier);
            break;
        } else {
            if !push_matcher_start(parser, &mut part_first, MatcherStart::Literal(part_start)) {
                break;
            }
            let _ = parser.bump();
            part_nullable = false;
            part_first_capture = false;
            part_last_capture = false;
        }

        let Some(follow_overlap) = matcher_pending_overlap(parser, &pending, &part_first) else {
            break;
        };
        let ambiguous = previous_capture && part_first_capture || follow_overlap;
        if ambiguous {
            let span = parser.tokens[part_start].span;
            if follow_overlap {
                parser.error_at_span(ParseReason::MatcherRepetitionAmbiguous, span);
            } else {
                let _ = parser.report_at(
                    ParseReason::ExpectedForm,
                    ExpectedForm::Identifier,
                    span,
                    None,
                );
            }
        }
        if nullable {
            first_capture |= part_first_capture;
            for start in &part_first {
                if !push_matcher_start(parser, &mut first, *start) {
                    break;
                }
            }
        }
        nullable &= part_nullable;
        previous_capture = if part_nullable {
            previous_capture || part_last_capture
        } else {
            part_last_capture
        };
        if !part_nullable {
            pending.clear();
        }
        if !part_pending.is_empty() {
            if !reserve_pending_matchers(parser, &mut pending, part_pending.len()) {
                break;
            }
            pending.append(&mut part_pending);
        }
        if let Some((separator, star)) = repeat {
            // Cloning these token indices and retaining one pending entry are
            // temporary grammar work, paid before their Vec allocations.
            if !parser.charge_matcher_work(part_first.len().saturating_mul(2)) {
                break;
            }
            let starts = part_first.clone();
            if !reserve_pending_matchers(parser, &mut pending, 1) {
                break;
            }
            pending.push((starts, separator, star));
        }
    }
    (nullable, first_capture, previous_capture, first, pending)
}

fn syntax_declaration_body(parser: &mut Parser<'_>, declaration: bool, generators: bool) {
    let _ = parser.expect(&TokenKind::FatArrow, ExpectedForm::FatArrow);
    if parser.at(&TokenKind::Using) {
        let _ = parser.bump();
        expect_lower_identifier(parser);
    } else {
        template_body(parser, declaration, generators);
        if generators && parser.at(&TokenKind::With) {
            template_generator_clause(parser);
        }
    }
}

fn template_body(parser: &mut Parser<'_>, declaration: bool, generators: bool) {
    parser.start(NodeKind::TemplateBody);
    if !parser.expect(&TokenKind::LeftBrace, ExpectedForm::LeftBrace) {
        parser.finish();
        return;
    }
    if !parser.enter_structure() {
        parser.consume_rest();
        parser.finish();
        return;
    }
    let mode = if declaration {
        QuoteMode::DeclarationTemplate
    } else {
        QuoteMode::Template
    };
    let previous_mode = std::mem::replace(&mut parser.quote_mode, mode);
    let mut closing = vec![(TokenKind::RightBrace, false)];
    while let Some((expected, repetition)) = closing.last().cloned() {
        if parser.at(&TokenKind::SyntaxKeyword) && parser.nth(1) == Some(&TokenKind::LeftBrace) {
            syntax_quote(parser);
        } else if parser.at(&TokenKind::Dollar) && parser.nth(1) == Some(&TokenKind::LeftBrace) {
            syntax_escape(parser);
        } else if parser.at(&expected) {
            let _ = parser.bump();
            closing.pop();
            parser.leave_structure();
            if repetition {
                if !matches!(parser.current(), Some(TokenKind::Star | TokenKind::Plus))
                    && matches!(parser.nth(1), Some(TokenKind::Star | TokenKind::Plus))
                {
                    let _ = parser.bump(); // Optional repetition separator.
                }
                if matches!(parser.current(), Some(TokenKind::Star | TokenKind::Plus)) {
                    let _ = parser.bump();
                    if generators
                        && parser.at(&TokenKind::With)
                        && parser.nth(1) == Some(&TokenKind::LeftBrace)
                    {
                        template_generator_clause(parser);
                    }
                }
            }
        } else if matches!(
            parser.current(),
            Some(TokenKind::LeftBrace | TokenKind::LeftParen)
        ) {
            let (end, repetition) = if parser.at(&TokenKind::LeftBrace) {
                (TokenKind::RightBrace, false)
            } else {
                (
                    TokenKind::RightParen,
                    parser.position > 0
                        && parser.tokens[parser.position - 1].kind == TokenKind::Dollar,
                )
            };
            if !parser.enter_structure() {
                parser.consume_rest();
                break;
            }
            closing.push((end, repetition));
            let _ = parser.bump();
        } else if matches!(
            parser.current(),
            Some(TokenKind::RightBrace | TokenKind::RightParen | TokenKind::EndOfFile) | None
        ) {
            parser.report(
                ParseReason::ExpectedForm,
                if expected == TokenKind::RightBrace {
                    ExpectedForm::RightBrace
                } else {
                    ExpectedForm::RightParen
                },
            );
            break;
        } else {
            let _ = parser.bump();
        }
    }
    while closing.pop().is_some() {
        parser.leave_structure();
    }
    parser.quote_mode = previous_mode;
    parser.finish();
}

fn template_generator_clause(parser: &mut Parser<'_>) {
    parser.start(NodeKind::TemplateGeneratorClause);
    let _ = parser.bump(); // with
    if !parser.expect(&TokenKind::LeftBrace, ExpectedForm::LeftBrace) {
        parser.finish();
        return;
    }
    if !parser.enter_structure() {
        parser.consume_rest();
        parser.finish();
        return;
    }
    if parser.at(&TokenKind::LineEnd) {
        let _ = parser.bump();
    }
    if parser.at(&TokenKind::RightBrace) {
        parser.report(ParseReason::ExpectedForm, ExpectedForm::Identifier);
    }
    while !matches!(
        parser.current(),
        Some(TokenKind::RightBrace | TokenKind::EndOfFile) | None
    ) && parser.resource_failure.is_none()
    {
        parser.start(NodeKind::TemplateGenerator);
        let _ = parser.expect(&TokenKind::Dollar, ExpectedForm::Identifier);
        if matches!(
            parser.current(),
            Some(TokenKind::Identifier(_) | TokenKind::UpperIdentifier(_))
        ) {
            let _ = parser.bump();
        } else {
            parser.report(ParseReason::ExpectedForm, ExpectedForm::Identifier);
        }
        if matches!(parser.current(), Some(TokenKind::Identifier(name)) if name == "from") {
            let _ = parser.bump();
        } else {
            parser.report(ParseReason::ExpectedForm, ExpectedForm::Identifier);
        }
        parser.start(NodeKind::TemplateGeneratorSeed);
        let previous_mode = std::mem::replace(&mut parser.quote_mode, QuoteMode::GeneratorSeed);
        if parser.charge_matcher_work(4) {
            let stop = TokenKind::Identifier("step".to_owned());
            if push_structured_stop(parser, &stop, "step") {
                expression(parser);
                let _ = parser.syntax_stops.pop();
            }
        }
        parser.quote_mode = previous_mode;
        parser.finish();
        if matches!(parser.current(), Some(TokenKind::Identifier(name)) if name == "step") {
            let _ = parser.bump();
        } else {
            parser.report(ParseReason::ExpectedForm, ExpectedForm::Identifier);
        }
        if parser.at_upper_identifier() {
            qualified_name(parser, false);
        } else {
            expect_syntax_name(parser);
        }
        parser.finish();
        if parser.at(&TokenKind::LineEnd) {
            let _ = parser.bump();
        } else if !parser.at(&TokenKind::RightBrace) {
            parser.report(ParseReason::ExpectedForm, ExpectedForm::LineEnd);
            break;
        }
    }
    let _ = parser.expect(&TokenKind::RightBrace, ExpectedForm::RightBrace);
    parser.leave_structure();
    parser.finish();
}

pub(super) fn syntax_quote(parser: &mut Parser<'_>) {
    parser.start(NodeKind::SyntaxQuote);
    let _ = parser.bump(); // syntax
    if !parser.expect(&TokenKind::LeftBrace, ExpectedForm::LeftBrace) {
        parser.finish();
        return;
    }
    if !parser.enter_structure() {
        parser.consume_rest();
        parser.finish();
        return;
    }
    let mode = match parser.quote_mode {
        QuoteMode::Template => QuoteMode::Template,
        QuoteMode::DeclarationTemplate => QuoteMode::DeclarationTemplate,
        QuoteMode::Ordinary | QuoteMode::GeneratorSeed | QuoteMode::Escape | QuoteMode::Quote => {
            QuoteMode::Quote
        }
    };
    let previous_mode = std::mem::replace(&mut parser.quote_mode, mode);
    if parser.at(&TokenKind::LineEnd) {
        let _ = parser.bump();
    }
    expression(parser);
    if parser.at(&TokenKind::LineEnd) {
        let _ = parser.bump();
    }
    let _ = parser.expect(&TokenKind::RightBrace, ExpectedForm::RightBrace);
    parser.quote_mode = previous_mode;
    parser.leave_structure();
    parser.finish();
}

pub(super) fn syntax_escape(parser: &mut Parser<'_>) {
    parser.start(NodeKind::SyntaxEscape);
    let _ = parser.bump(); // $
    let previous_mode = std::mem::replace(&mut parser.quote_mode, QuoteMode::Escape);
    if parser.nth(1) == Some(&TokenKind::LineEnd) {
        block(parser);
    } else if parser.enter_structure() {
        let _ = parser.bump(); // {
        let recovery_start = parser.pending_recovery_count();
        expression(parser);
        if parser.at(&TokenKind::RightBrace) {
            parser.resolve_pending_at_current(
                recovery_start,
                SynchronizationBoundary::BlockClosingBrace,
            );
        } else if parser.at(&TokenKind::EndOfFile) {
            parser.resolve_pending_at_current(recovery_start, SynchronizationBoundary::EndOfFile);
        }
        let _ = parser.expect(&TokenKind::RightBrace, ExpectedForm::RightBrace);
        parser.leave_structure();
    } else {
        parser.consume_rest();
    }
    parser.quote_mode = previous_mode;
    parser.finish();
}

pub(super) fn quote_hole(parser: &mut Parser<'_>) {
    let kind = match parser.quote_mode {
        QuoteMode::Template | QuoteMode::DeclarationTemplate | QuoteMode::GeneratorSeed => {
            NodeKind::TemplateSplice
        }
        QuoteMode::Escape => NodeKind::EscapeCaptureRead,
        QuoteMode::Quote => NodeKind::QuoteHole,
        QuoteMode::Ordinary => unreachable!("ordinary Ash has no quote holes"),
    };
    parser.start(kind);
    let _ = parser.bump(); // $
    if parser.quote_mode == QuoteMode::DeclarationTemplate
        && parser
            .current()
            .and_then(super::declaration_metaname)
            .is_some()
        || matches!(parser.current(), Some(TokenKind::Identifier(_)))
        || parser.quote_mode != QuoteMode::Quote
            && matches!(parser.current(), Some(TokenKind::UpperIdentifier(_)))
    {
        let _ = parser.bump();
    } else {
        parser.report(ParseReason::ExpectedForm, ExpectedForm::Identifier);
    }
    parser.finish();
}

fn starts_newtype_declaration(parser: &Parser<'_>) -> bool {
    parser.at(&TokenKind::Newtype)
        || parser.at(&TokenKind::Pub)
            && (parser.nth(1) == Some(&TokenKind::Newtype)
                || parser.nth(1) == Some(&TokenKind::Opaque)
                    && parser.nth(2) == Some(&TokenKind::Newtype))
}

#[derive(Clone, Copy)]
enum HeaderRecoveryBoundary {
    LineEnd,
    OpeningBrace(SynchronizationBoundary),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum TypeParameterOwnerBoundary {
    TypeDeclaration,
    EquationalGlobal,
    OperationalGlobal,
    Implementation,
    Interface,
    InterfaceMethod,
    Effect,
}

fn effect_declaration(parser: &mut Parser<'_>) -> TypeParametersOutcome {
    parser.start(NodeKind::EffectDeclaration);
    if parser.at(&TokenKind::Pub) {
        let _ = parser.bump();
    }
    let _ = parser.expect(&TokenKind::Effect, ExpectedForm::Identifier);
    let recovery_start = parser.pending_recovery_count();
    if parser.at_upper_identifier() {
        let _ = parser.bump();
        if parser.at(&TokenKind::Less) {
            let outcome = type_parameters(parser, TypeParameterOwnerBoundary::Effect);
            if outcome.stops_declaration() {
                parser.finish();
                return outcome;
            }
        }
    } else {
        report_pending_expected(parser, ExpectedForm::Identifier);
    }
    recover_pending_header(
        parser,
        recovery_start,
        HeaderRecoveryBoundary::OpeningBrace(SynchronizationBoundary::InterfaceBodyOpeningBrace),
    );
    if !declaration_body_starts(
        parser,
        SynchronizationBoundary::InterfaceBodyOpeningBrace,
        SynchronizationBoundary::InterfaceClosingBrace,
    ) {
        parser.finish();
        return TypeParametersOutcome::Complete;
    }
    let _ = parser.bump();
    let _ = parser.expect(&TokenKind::LineEnd, ExpectedForm::LineEnd);
    let mut has_operation = false;
    loop {
        if matches!(parser.current(), Some(TokenKind::Identifier(_))) {
            has_operation = true;
            effect_operation(parser);
        } else if matches!(
            parser.current(),
            Some(TokenKind::RightBrace | TokenKind::EndOfFile)
        ) {
            break;
        } else {
            has_operation = true;
            recover_effect_operation(parser);
        }
        if parser.at(&TokenKind::LineEnd) {
            let _ = parser.bump();
        }
    }
    if !has_operation {
        parser.report(ParseReason::ExpectedForm, ExpectedForm::EffectOperation);
    }
    let _ = parser.expect(&TokenKind::RightBrace, ExpectedForm::RightBrace);
    parser.finish();
    TypeParametersOutcome::Complete
}

fn effect_operation(parser: &mut Parser<'_>) {
    parser.start(NodeKind::EffectOperation);
    let recovery_start = parser.pending_recovery_count();
    binder(parser);
    if !parser.at(&TokenKind::Colon) {
        report_pending_expected(parser, ExpectedForm::Colon);
        consume_to_line_or_brace(parser);
    } else {
        let _ = parser.bump();
        if starts_type(parser) {
            type_expression(parser);
        } else {
            report_pending_expected(parser, ExpectedForm::Type);
            consume_to_line_or_brace(parser);
        }
    }
    resolve_line_eof_or_brace(
        parser,
        recovery_start,
        SynchronizationBoundary::InterfaceClosingBrace,
    );
    parser.finish();
}

fn recover_effect_operation(parser: &mut Parser<'_>) {
    parser.start(NodeKind::Error);
    let recovery_start = parser.pending_recovery_count();
    report_pending_expected(parser, ExpectedForm::EffectOperation);
    consume_to_line_or_brace(parser);
    resolve_line_eof_or_brace(
        parser,
        recovery_start,
        SynchronizationBoundary::InterfaceClosingBrace,
    );
    parser.finish();
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum TypeParametersOutcome {
    Complete,
    RecoveredToOwnerOrCloser,
    RecoveredToLineEnd,
    RecoveredToEndOfFile,
}

impl TypeParametersOutcome {
    const fn stops_declaration(self) -> bool {
        matches!(self, Self::RecoveredToLineEnd | Self::RecoveredToEndOfFile)
    }
}

fn report_pending_expected(parser: &mut Parser<'_>, expected: ExpectedForm) {
    if let Some(primary) = parser.current_span()
        && let Some(diagnostic) =
            parser.report_at(ParseReason::ExpectedForm, expected, primary, None)
    {
        parser.mark_pending_recovery(diagnostic);
    }
}

fn at_header_boundary(parser: &Parser<'_>, boundary: HeaderRecoveryBoundary) -> bool {
    match boundary {
        HeaderRecoveryBoundary::LineEnd => parser.at(&TokenKind::LineEnd),
        HeaderRecoveryBoundary::OpeningBrace(_) => parser.at(&TokenKind::LeftBrace),
    }
}

fn recover_pending_header(
    parser: &mut Parser<'_>,
    recovery_start: usize,
    boundary: HeaderRecoveryBoundary,
) {
    if parser.pending_recovery_count() == recovery_start {
        return;
    }
    if !at_header_boundary(parser, boundary)
        && !matches!(
            parser.current(),
            Some(TokenKind::LineEnd | TokenKind::EndOfFile) | None
        )
    {
        parser.start(NodeKind::Error);
        while !at_header_boundary(parser, boundary)
            && !matches!(
                parser.current(),
                Some(TokenKind::LineEnd | TokenKind::EndOfFile) | None
            )
        {
            let _ = parser.bump();
        }
        parser.finish();
    }
    if parser.at(&TokenKind::LineEnd) {
        parser.resolve_pending_at_current(recovery_start, SynchronizationBoundary::LogicalLineEnd);
    } else if parser.at(&TokenKind::EndOfFile) {
        parser.resolve_pending_at_current(recovery_start, SynchronizationBoundary::EndOfFile);
    } else if at_header_boundary(parser, boundary)
        && let HeaderRecoveryBoundary::OpeningBrace(synchronization) = boundary
    {
        parser.resolve_pending_at_current(recovery_start, synchronization);
    }
}

fn header_boundary_expected(boundary: HeaderRecoveryBoundary) -> ExpectedForm {
    match boundary {
        HeaderRecoveryBoundary::LineEnd => ExpectedForm::LineEnd,
        HeaderRecoveryBoundary::OpeningBrace(_) => ExpectedForm::LeftBrace,
    }
}

fn declaration_body_starts(
    parser: &mut Parser<'_>,
    opening: SynchronizationBoundary,
    closing: SynchronizationBoundary,
) -> bool {
    if parser.at(&TokenKind::LeftBrace) {
        return true;
    }

    let recovery_start = parser.pending_recovery_count();
    report_pending_expected(parser, ExpectedForm::LeftBrace);
    if parser.at(&TokenKind::LineEnd) && parser.nth(1) == Some(&TokenKind::LeftBrace) {
        consume_rejected_braced_body(parser, recovery_start, closing);
        return false;
    }

    recover_pending_header(
        parser,
        recovery_start,
        HeaderRecoveryBoundary::OpeningBrace(opening),
    );
    parser.at(&TokenKind::LeftBrace)
}

fn consume_rejected_braced_body(
    parser: &mut Parser<'_>,
    recovery_start: usize,
    closing: SynchronizationBoundary,
) {
    parser.start(NodeKind::Error);
    let _ = parser.bump();
    let mut depth = 0_usize;
    loop {
        match parser.current() {
            Some(TokenKind::LeftBrace) => {
                depth = depth.saturating_add(1);
                let _ = parser.bump();
            }
            Some(TokenKind::RightBrace) if depth == 1 => {
                parser.resolve_pending_at_current(recovery_start, closing);
                let _ = parser.bump();
                break;
            }
            Some(TokenKind::RightBrace) if depth > 1 => {
                depth -= 1;
                let _ = parser.bump();
            }
            Some(TokenKind::EndOfFile) | None => {
                parser
                    .resolve_pending_at_current(recovery_start, SynchronizationBoundary::EndOfFile);
                break;
            }
            Some(_) => {
                let _ = parser.bump();
            }
        }
    }
    parser.finish();
}

fn implementation_declaration(parser: &mut Parser<'_>) -> TypeParametersOutcome {
    parser.start(NodeKind::ImplementationDeclaration);
    if parser.at(&TokenKind::Pub) {
        let _ = parser.bump();
    }
    let _ = parser.expect(&TokenKind::Impl, ExpectedForm::InterfaceApplication);
    if parser.at(&TokenKind::Less) {
        let outcome = type_parameters(parser, TypeParameterOwnerBoundary::Implementation);
        if outcome.stops_declaration() {
            parser.finish();
            return outcome;
        }
    }
    let head_recovery_start = parser.pending_recovery_count();
    let _ = interface_application(parser);
    if parser.pending_recovery_count() > head_recovery_start
        && !matches!(
            parser.current(),
            Some(
                TokenKind::Where | TokenKind::LeftBrace | TokenKind::LineEnd | TokenKind::EndOfFile
            )
        )
    {
        parser.start(NodeKind::Error);
        while !matches!(
            parser.current(),
            Some(
                TokenKind::Where | TokenKind::LeftBrace | TokenKind::LineEnd | TokenKind::EndOfFile
            ) | None
        ) {
            let _ = parser.bump();
        }
        parser.finish();
    }
    if parser.at(&TokenKind::Where) {
        where_clause(
            parser,
            HeaderRecoveryBoundary::OpeningBrace(
                SynchronizationBoundary::ImplementationBodyOpeningBrace,
            ),
        );
    }
    recover_pending_header(
        parser,
        head_recovery_start,
        HeaderRecoveryBoundary::OpeningBrace(
            SynchronizationBoundary::ImplementationBodyOpeningBrace,
        ),
    );
    if !declaration_body_starts(
        parser,
        SynchronizationBoundary::ImplementationBodyOpeningBrace,
        SynchronizationBoundary::ImplementationClosingBrace,
    ) {
        parser.finish();
        return TypeParametersOutcome::Complete;
    }
    let _ = parser.bump();
    let _ = parser.expect(&TokenKind::LineEnd, ExpectedForm::LineEnd);

    loop {
        if matches!(parser.current(), Some(TokenKind::Identifier(_))) {
            equation(parser, SynchronizationBoundary::ImplementationClosingBrace);
        } else if matches!(
            parser.current(),
            Some(TokenKind::RightBrace | TokenKind::EndOfFile)
        ) {
            break;
        } else {
            recover_implementation_method(parser);
        }
        if parser.at(&TokenKind::LineEnd) {
            let _ = parser.bump();
        }
    }
    let _ = parser.expect(&TokenKind::RightBrace, ExpectedForm::RightBrace);
    parser.finish();
    TypeParametersOutcome::Complete
}

fn lexical_evidence_declaration(parser: &mut Parser<'_>) {
    parser.start(NodeKind::LexicalEvidenceDeclaration);
    let _ = parser.bump();
    let _ = interface_application(parser);
    if !declaration_body_starts(
        parser,
        SynchronizationBoundary::ImplementationBodyOpeningBrace,
        SynchronizationBoundary::ImplementationClosingBrace,
    ) {
        parser.finish();
        return;
    }
    let _ = parser.bump();
    let _ = parser.expect(&TokenKind::LineEnd, ExpectedForm::LineEnd);
    while !matches!(
        parser.current(),
        Some(TokenKind::RightBrace | TokenKind::EndOfFile) | None
    ) {
        if matches!(parser.current(), Some(TokenKind::Identifier(_))) {
            equation(parser, SynchronizationBoundary::ImplementationClosingBrace);
        } else {
            recover_implementation_method(parser);
        }
        if parser.at(&TokenKind::LineEnd) {
            let _ = parser.bump();
        }
    }
    let _ = parser.expect(&TokenKind::RightBrace, ExpectedForm::RightBrace);
    parser.finish();
}

fn recover_implementation_method(parser: &mut Parser<'_>) {
    parser.start(NodeKind::Error);
    let recovery_start = parser.pending_recovery_count();
    if let Some(primary) = parser.current_span()
        && let Some(diagnostic) = parser.report_at(
            ParseReason::ExpectedForm,
            ExpectedForm::ImplementationMethod,
            primary,
            None,
        )
    {
        parser.mark_pending_recovery(diagnostic);
    }

    consume_to_line_or_brace(parser);
    resolve_line_eof_or_brace(
        parser,
        recovery_start,
        SynchronizationBoundary::ImplementationClosingBrace,
    );
    parser.finish();
}

fn consume_to_line_or_brace(parser: &mut Parser<'_>) {
    let mut nested_braces = 0_usize;
    loop {
        match parser.current() {
            Some(TokenKind::LeftBrace) => {
                nested_braces = nested_braces.saturating_add(1);
                let _ = parser.bump();
            }
            Some(TokenKind::RightBrace) if nested_braces == 0 => break,
            Some(TokenKind::RightBrace) => {
                nested_braces = nested_braces.saturating_sub(1);
                let _ = parser.bump();
            }
            Some(TokenKind::LineEnd) if nested_braces == 0 => break,
            Some(TokenKind::EndOfFile) | None => break,
            Some(_) => {
                let _ = parser.bump();
            }
        }
    }
}

fn interface_declaration(parser: &mut Parser<'_>) -> TypeParametersOutcome {
    parser.start(NodeKind::InterfaceDeclaration);
    if parser.at(&TokenKind::Pub) {
        let _ = parser.bump();
    }
    let _ = parser.expect(&TokenKind::Interface, ExpectedForm::Identifier);
    let parameter_recovery_start = parser.pending_recovery_count();
    if parser.at_upper_identifier() {
        let _ = parser.bump();
        let outcome = if parser.at(&TokenKind::Less) {
            type_parameters(parser, TypeParameterOwnerBoundary::Interface)
        } else {
            report_pending_expected(parser, ExpectedForm::InterfaceParameter);
            TypeParametersOutcome::Complete
        };
        if outcome.stops_declaration() {
            parser.finish();
            return outcome;
        }
    } else {
        report_pending_expected(parser, ExpectedForm::Identifier);
    }
    if parser.at(&TokenKind::Where) {
        interface_determination(parser);
    }
    recover_pending_header(
        parser,
        parameter_recovery_start,
        HeaderRecoveryBoundary::OpeningBrace(SynchronizationBoundary::InterfaceBodyOpeningBrace),
    );
    if !declaration_body_starts(
        parser,
        SynchronizationBoundary::InterfaceBodyOpeningBrace,
        SynchronizationBoundary::InterfaceClosingBrace,
    ) {
        parser.finish();
        return TypeParametersOutcome::Complete;
    }
    let _ = parser.bump();
    let _ = parser.expect(&TokenKind::LineEnd, ExpectedForm::LineEnd);

    let mut has_body_line = false;
    loop {
        if matches!(parser.current(), Some(TokenKind::Identifier(_))) {
            has_body_line = true;
            interface_method(parser);
        } else if matches!(
            parser.current(),
            Some(TokenKind::RightBrace | TokenKind::EndOfFile)
        ) {
            break;
        } else {
            has_body_line = true;
            recover_interface_method(parser);
        }
        if parser.at(&TokenKind::LineEnd) {
            let _ = parser.bump();
        }
    }
    if !has_body_line {
        parser.report(ParseReason::ExpectedForm, ExpectedForm::InterfaceMethod);
    }
    let _ = parser.expect(&TokenKind::RightBrace, ExpectedForm::RightBrace);
    parser.finish();
    TypeParametersOutcome::Complete
}

fn recover_interface_method(parser: &mut Parser<'_>) {
    parser.start(NodeKind::Error);
    let recovery_start = parser.pending_recovery_count();
    if let Some(primary) = parser.current_span()
        && let Some(diagnostic) = parser.report_at(
            ParseReason::ExpectedForm,
            ExpectedForm::InterfaceMethod,
            primary,
            None,
        )
    {
        parser.mark_pending_recovery(diagnostic);
    }
    consume_to_line_or_brace(parser);
    resolve_line_eof_or_brace(
        parser,
        recovery_start,
        SynchronizationBoundary::InterfaceClosingBrace,
    );
    parser.finish();
}

fn interface_determination(parser: &mut Parser<'_>) {
    let _ = parser.bump();
    if !determination_side(parser) {
        return;
    }
    if !parser.at(&TokenKind::Arrow) {
        report_pending_expected(parser, ExpectedForm::Arrow);
        return;
    }
    let _ = parser.bump();
    let _ = determination_side(parser);
}

fn determination_side(parser: &mut Parser<'_>) -> bool {
    if parser.at_upper_identifier() {
        let _ = parser.bump();
        return true;
    }
    if !parser.at(&TokenKind::LeftParen) {
        report_pending_expected(parser, ExpectedForm::Identifier);
        return false;
    }

    let _ = parser.bump();
    if !parser.at_upper_identifier() {
        report_pending_expected(parser, ExpectedForm::Identifier);
        return false;
    }
    let _ = parser.bump();
    while parser.at(&TokenKind::Comma) {
        let _ = parser.bump();
        if !parser.at_upper_identifier() {
            report_pending_expected(parser, ExpectedForm::Identifier);
            return false;
        }
        let _ = parser.bump();
    }
    if !parser.at(&TokenKind::RightParen) {
        report_pending_expected(parser, ExpectedForm::RightParen);
        return false;
    }
    let _ = parser.bump();
    true
}

fn interface_method(parser: &mut Parser<'_>) {
    parser.start(NodeKind::InterfaceMethod);
    let recovery_start = parser.pending_recovery_count();
    binder(parser);
    if parser.at(&TokenKind::Less) {
        let outcome = type_parameters(parser, TypeParameterOwnerBoundary::InterfaceMethod);
        if outcome.stops_declaration() {
            parser.finish();
            return;
        }
    }
    if !parser.at(&TokenKind::Colon) {
        report_pending_expected(parser, ExpectedForm::Colon);
        consume_to_line_or_brace(parser);
        resolve_line_eof_or_brace(
            parser,
            recovery_start,
            SynchronizationBoundary::InterfaceClosingBrace,
        );
        parser.finish();
        return;
    }
    let _ = parser.bump();
    if !starts_type(parser) {
        report_pending_expected(parser, ExpectedForm::Type);
        consume_to_line_or_brace(parser);
        resolve_line_eof_or_brace(
            parser,
            recovery_start,
            SynchronizationBoundary::InterfaceClosingBrace,
        );
        parser.finish();
        return;
    }
    type_expression(parser);
    if !matches!(
        parser.current(),
        Some(TokenKind::LineEnd | TokenKind::RightBrace | TokenKind::EndOfFile)
    ) {
        parser.start(NodeKind::Error);
        if let Some(primary) = parser.current_span()
            && let Some(diagnostic) = parser.report_at(
                ParseReason::ExpectedForm,
                ExpectedForm::LineEnd,
                primary,
                None,
            )
        {
            parser.mark_pending_recovery(diagnostic);
        }
        consume_to_line_or_brace(parser);
        parser.finish();
    }
    resolve_line_eof_or_brace(
        parser,
        recovery_start,
        SynchronizationBoundary::InterfaceClosingBrace,
    );
    parser.finish();
}

fn where_clause(parser: &mut Parser<'_>, boundary: HeaderRecoveryBoundary) {
    parser.start(NodeKind::WhereClause);
    let recovery_start = parser.pending_recovery_count();
    let _ = parser.bump();
    let mut application_valid = interface_application(parser);
    while application_valid {
        if parser.at(&TokenKind::Comma) {
            let _ = parser.bump();
            application_valid = interface_application(parser);
        } else if parser.at_upper_identifier() {
            report_pending_expected(parser, ExpectedForm::Comma);
            application_valid = interface_application(parser);
        } else {
            break;
        }
    }
    if parser.pending_recovery_count() == recovery_start
        && !at_header_boundary(parser, boundary)
        && !matches!(
            parser.current(),
            Some(TokenKind::LineEnd | TokenKind::EndOfFile) | None
        )
    {
        report_pending_expected(parser, header_boundary_expected(boundary));
    }
    recover_pending_header(parser, recovery_start, boundary);
    parser.finish();
}

fn interface_application(parser: &mut Parser<'_>) -> bool {
    parser.start(NodeKind::InterfaceApplication);
    let recovery_start = parser.pending_recovery_count();
    if parser.at_upper_identifier() {
        if parser
            .nth(1)
            .is_some_and(|kind| matches!(kind, TokenKind::Dot))
        {
            parser.start(NodeKind::QualifiedName);
            let _ = parser.bump();
            let _ = parser.bump();
            if parser.at_upper_identifier() {
                let _ = parser.bump();
            } else {
                report_pending_expected(parser, ExpectedForm::InterfaceApplication);
                parser.finish();
                parser.finish();
                return false;
            }
            parser.finish();
        } else {
            let _ = parser.bump();
        }
        if !parser.at(&TokenKind::Less) {
            report_pending_expected(parser, ExpectedForm::InterfaceApplication);
            parser.finish();
            return false;
        }
        let _ = parser.bump();
        let mut arguments_valid = if starts_type(parser) || parser.at(&TokenKind::LeftBrace) {
            application_argument(parser);
            true
        } else {
            report_pending_expected(parser, ExpectedForm::InterfaceApplication);
            false
        };
        while parser.at(&TokenKind::Comma) {
            let _ = parser.bump();
            if starts_type(parser) || parser.at(&TokenKind::LeftBrace) {
                application_argument(parser);
            } else {
                report_pending_expected(parser, ExpectedForm::InterfaceApplication);
                arguments_valid = false;
                break;
            }
        }
        if parser.at(&TokenKind::Greater) {
            let _ = parser.bump();
        } else {
            if arguments_valid {
                report_pending_expected(parser, ExpectedForm::InterfaceApplication);
            }
            while !matches!(
                parser.current(),
                Some(
                    TokenKind::Greater
                        | TokenKind::Where
                        | TokenKind::LeftBrace
                        | TokenKind::LineEnd
                        | TokenKind::EndOfFile
                ) | None
            ) {
                let _ = parser.bump();
            }
            if parser.at(&TokenKind::Greater) {
                let _ = parser.bump();
            }
        }
    } else {
        report_pending_expected(parser, ExpectedForm::InterfaceApplication);
    }
    parser.finish();
    parser.pending_recovery_count() == recovery_start
}

fn type_declaration(parser: &mut Parser<'_>) -> TypeParametersOutcome {
    parser.start(NodeKind::TypeDeclaration);
    if parser.at(&TokenKind::Pub) {
        let _ = parser.bump();
        if parser.at(&TokenKind::Opaque) {
            let _ = parser.bump();
        }
    }
    let _ = parser.expect(&TokenKind::Type, ExpectedForm::Type);
    if parser.at_upper_identifier() {
        let _ = parser.bump();
    } else {
        parser.report(ParseReason::ExpectedForm, ExpectedForm::Identifier);
    }
    if parser.at(&TokenKind::Less) {
        let outcome = type_parameters(parser, TypeParameterOwnerBoundary::TypeDeclaration);
        if outcome.stops_declaration() {
            parser.finish();
            return outcome;
        }
    }
    let _ = parser.expect(&TokenKind::Equal, ExpectedForm::Equal);
    if parser.at(&TokenKind::LineEnd) {
        let _ = parser.bump();
    }
    constructor_declaration(parser);
    while parser.at(&TokenKind::LineEnd)
        && parser
            .nth(1)
            .is_some_and(|kind| matches!(kind, TokenKind::Pipe))
    {
        let _ = parser.bump();
        let _ = parser.bump();
        constructor_declaration(parser);
    }
    deriving_clause(parser);
    parser.finish();
    TypeParametersOutcome::Complete
}

fn newtype_declaration(parser: &mut Parser<'_>, module_level: bool) -> TypeParametersOutcome {
    parser.start(NodeKind::NewtypeDeclaration);
    if parser.at(&TokenKind::Pub) {
        let _ = parser.bump();
        if parser.at(&TokenKind::Opaque) {
            let _ = parser.bump();
        }
    }
    let _ = parser.expect(&TokenKind::Newtype, ExpectedForm::Type);
    if parser.at_upper_identifier() {
        let _ = parser.bump();
    } else {
        parser.report(ParseReason::ExpectedForm, ExpectedForm::Identifier);
    }
    if parser.at(&TokenKind::Less) {
        let outcome = type_parameters(parser, TypeParameterOwnerBoundary::TypeDeclaration);
        if outcome.stops_declaration() {
            parser.finish();
            return outcome;
        }
    }
    let _ = parser.expect(&TokenKind::Equal, ExpectedForm::Equal);
    newtype_constructor_declaration(parser);
    while parser.at(&TokenKind::LineEnd)
        && parser
            .nth(1)
            .is_some_and(|kind| matches!(kind, TokenKind::Pipe))
    {
        let _ = parser.bump();
        reject_newtype_extra_constructor(parser);
    }
    if parser.at(&TokenKind::Pipe) {
        reject_newtype_extra_constructor(parser);
    }
    if module_level {
        deriving_clause(parser);
    }
    parser.finish();
    TypeParametersOutcome::Complete
}

fn deriving_clause(parser: &mut Parser<'_>) {
    if !parser.at(&TokenKind::LineEnd)
        || !matches!(parser.nth(1), Some(TokenKind::Identifier(name)) if name == "deriving")
        || parser.nth(2) != Some(&TokenKind::LeftParen)
    {
        return;
    }
    let _ = parser.bump(); // line end belongs to the subject
    parser.start(NodeKind::DerivingClause);
    let _ = parser.bump(); // deriving
    let _ = parser.bump(); // (
    expect_syntax_name(parser);
    while parser.at(&TokenKind::Comma) {
        let _ = parser.bump();
        if parser.at(&TokenKind::RightParen) {
            break;
        }
        expect_syntax_name(parser);
    }
    let _ = parser.expect(&TokenKind::RightParen, ExpectedForm::RightParen);
    parser.finish();
}

fn newtype_constructor_declaration(parser: &mut Parser<'_>) {
    parser.start(NodeKind::ConstructorDeclaration);
    if parser.at_upper_identifier() {
        let _ = parser.bump();
    } else {
        parser.report(ParseReason::ExpectedForm, ExpectedForm::Identifier);
        parser.finish();
        return;
    }
    let opening = parser.current_span();
    if !parser.expect(&TokenKind::LeftParen, ExpectedForm::LeftParen) {
        parser.finish();
        return;
    }
    type_expression(parser);
    if parser.at(&TokenKind::Comma) {
        reject_newtype_constructor_tail(parser);
    } else if parser.at(&TokenKind::RightParen) {
        let _ = parser.bump();
    } else {
        expression::report_unclosed_group(parser, opening);
    }
    parser.finish();
}

fn reject_newtype_extra_constructor(parser: &mut Parser<'_>) {
    parser.start(NodeKind::Error);
    let recovery_start = parser.pending_recovery_count();
    if let Some(primary) = parser.current_span()
        && let Some(diagnostic) = parser.report_at(
            ParseReason::ExpectedForm,
            ExpectedForm::LineEnd,
            primary,
            None,
        )
    {
        parser.mark_pending_recovery(diagnostic);
    }
    while !matches!(
        parser.current(),
        Some(TokenKind::LineEnd | TokenKind::EndOfFile) | None
    ) {
        let _ = parser.bump();
    }
    if parser.at(&TokenKind::LineEnd) {
        parser.resolve_pending_at_current(recovery_start, SynchronizationBoundary::LogicalLineEnd);
    } else {
        parser.resolve_pending_at_current(recovery_start, SynchronizationBoundary::EndOfFile);
    }
    parser.finish();
}

fn reject_newtype_constructor_tail(parser: &mut Parser<'_>) {
    parser.start(NodeKind::Error);
    let recovery_start = parser.pending_recovery_count();
    if let Some(primary) = parser.current_span()
        && let Some(diagnostic) = parser.report_at(
            ParseReason::ExpectedForm,
            ExpectedForm::RightParen,
            primary,
            None,
        )
    {
        parser.mark_pending_recovery(diagnostic);
    }
    while !matches!(
        parser.current(),
        Some(TokenKind::RightParen | TokenKind::LineEnd | TokenKind::EndOfFile) | None
    ) {
        let _ = parser.bump();
    }
    if parser.at(&TokenKind::RightParen) {
        parser.resolve_pending_at_current(
            recovery_start,
            SynchronizationBoundary::ParenthesisClosing,
        );
        let _ = parser.bump();
    } else if parser.at(&TokenKind::LineEnd) {
        parser.resolve_pending_at_current(recovery_start, SynchronizationBoundary::LogicalLineEnd);
    } else {
        parser.resolve_pending_at_current(recovery_start, SynchronizationBoundary::EndOfFile);
    }
    parser.finish();
}

fn constructor_declaration(parser: &mut Parser<'_>) {
    parser.start(NodeKind::ConstructorDeclaration);
    if parser.at_upper_identifier() {
        let _ = parser.bump();
    } else {
        parser.report(ParseReason::ExpectedForm, ExpectedForm::Identifier);
    }
    if parser.at(&TokenKind::LeftParen) {
        let opening = parser.current_span();
        let _ = parser.bump();
        type_expression(parser);
        while parser.at(&TokenKind::Comma) {
            let _ = parser.bump();
            type_expression(parser);
        }
        if parser.at(&TokenKind::RightParen) {
            let _ = parser.bump();
        } else {
            expression::report_unclosed_group(parser, opening);
        }
    }
    parser.finish();
}

fn starts_global(parser: &Parser<'_>) -> bool {
    global_definition_form(parser).is_some()
}

fn global_definition(parser: &mut Parser<'_>) -> TypeParametersOutcome {
    match global_definition_form(parser) {
        Some(GlobalDefinitionForm::Equational) => equational_global(parser),
        Some(GlobalDefinitionForm::InlineOperational) => inline_operational_global(parser),
        None => {
            parser.report(ParseReason::UnexpectedToken, ExpectedForm::Expression);
            TypeParametersOutcome::Complete
        }
    }
}

fn global_definition_form(parser: &Parser<'_>) -> Option<GlobalDefinitionForm> {
    let offset = usize::from(parser.at(&TokenKind::Pub));
    selected_dialect()
        .global_definitions
        .iter()
        .copied()
        .find(|form| match form {
            GlobalDefinitionForm::Equational => matches!(
                (parser.nth(offset), parser.nth(offset.saturating_add(1))),
                (
                    Some(TokenKind::Identifier(_)),
                    Some(TokenKind::Colon | TokenKind::Less)
                )
            ),
            GlobalDefinitionForm::InlineOperational => matches!(
                (parser.nth(offset), parser.nth(offset.saturating_add(1))),
                (Some(TokenKind::Fn), Some(TokenKind::Identifier(_)))
            ),
        })
}

fn equational_global(parser: &mut Parser<'_>) -> TypeParametersOutcome {
    parser.start(NodeKind::EquationalGlobal);
    if parser.at(&TokenKind::Pub) {
        let _ = parser.bump();
    }
    parser.start(NodeKind::ExternalInterface);
    let name = match parser.current() {
        Some(TokenKind::Identifier(name)) => Some(name.clone()),
        _ => None,
    };
    binder(parser);
    if parser.at(&TokenKind::Less) {
        let outcome = type_parameters(parser, TypeParameterOwnerBoundary::EquationalGlobal);
        if outcome.stops_declaration() {
            parser.finish();
            parser.finish();
            return outcome;
        }
    }
    let _ = parser.expect(&TokenKind::Colon, ExpectedForm::Colon);
    type_expression(parser);
    if parser.at(&TokenKind::Where) {
        where_clause(parser, HeaderRecoveryBoundary::LineEnd);
    }
    parser.finish();
    expect_header_line_end(parser);

    equation(parser, SynchronizationBoundary::BlockClosingBrace);
    while parser.at(&TokenKind::LineEnd)
        && name
            .as_deref()
            .is_some_and(|name| looks_like_equation(parser, name))
    {
        let _ = parser.bump();
        equation(parser, SynchronizationBoundary::BlockClosingBrace);
    }
    parser.finish();
    TypeParametersOutcome::Complete
}

fn expect_header_line_end(parser: &mut Parser<'_>) {
    if parser.at(&TokenKind::LineEnd) {
        let _ = parser.bump();
        return;
    }

    parser.start(NodeKind::Error);
    let recovery_start = parser.pending_recovery_count();
    if let Some(primary) = parser.current_span()
        && let Some(diagnostic) = parser.report_at(
            ParseReason::ExpectedForm,
            ExpectedForm::LineEnd,
            primary,
            None,
        )
    {
        parser.mark_pending_recovery(diagnostic);
    }
    while !matches!(
        parser.current(),
        Some(TokenKind::LineEnd | TokenKind::EndOfFile) | None
    ) {
        let _ = parser.bump();
    }
    if parser.at(&TokenKind::LineEnd) {
        parser.resolve_pending_at_current(recovery_start, SynchronizationBoundary::LogicalLineEnd);
        let _ = parser.bump();
    } else {
        parser.resolve_pending_at_current(recovery_start, SynchronizationBoundary::EndOfFile);
    }
    parser.finish();
}

fn looks_like_equation(parser: &Parser<'_>, expected: &str) -> bool {
    if !matches!(
        parser.nth(1),
        Some(TokenKind::Identifier(actual)) if actual == expected
    ) {
        return false;
    }
    let mut offset = 2;
    let mut depth = 0_u32;
    loop {
        match parser.nth(offset) {
            Some(TokenKind::LeftParen) => depth = depth.saturating_add(1),
            Some(TokenKind::RightParen) if depth > 0 => depth -= 1,
            Some(TokenKind::Equal) if depth == 0 => return true,
            Some(TokenKind::LineEnd | TokenKind::EndOfFile) if depth == 0 => return false,
            Some(_) => {}
            None => return false,
        }
        offset = offset.saturating_add(1);
    }
}

fn equation(parser: &mut Parser<'_>, closing_brace: SynchronizationBoundary) {
    parser.start(NodeKind::Equation);
    let recovery_start = parser.pending_recovery_count();
    binder(parser);
    if !starts_pattern(parser) {
        report_pending_expected(parser, ExpectedForm::Pattern);
        consume_to_line_or_brace(parser);
        resolve_line_eof_or_brace(parser, recovery_start, closing_brace);
        parser.finish();
        return;
    }
    while starts_pattern(parser) {
        pattern(parser);
    }
    if !parser.at(&TokenKind::Equal) {
        report_pending_expected(parser, ExpectedForm::Equal);
        consume_to_line_or_brace(parser);
        resolve_line_eof_or_brace(parser, recovery_start, closing_brace);
        parser.finish();
        return;
    }
    let _ = parser.bump();
    if !starts_expression(parser) {
        report_pending_expected(parser, ExpectedForm::Expression);
        consume_to_line_or_brace(parser);
        resolve_line_eof_or_brace(parser, recovery_start, closing_brace);
        parser.finish();
        return;
    }
    expression(parser);
    if !matches!(
        parser.current(),
        Some(TokenKind::LineEnd | TokenKind::RightBrace | TokenKind::EndOfFile)
    ) {
        if parser.at(&TokenKind::Semicolon) {
            parser.error_at_current(ParseReason::Semicolon);
        } else if parser.at(&TokenKind::And) {
            parser.error_at_current(ParseReason::UnexpectedAnd);
        } else {
            report_pending_expected(parser, ExpectedForm::LineEnd);
        }
        consume_to_line_or_brace(parser);
    }
    resolve_line_eof_or_brace(parser, recovery_start, closing_brace);
    parser.finish();
}

fn inline_operational_global(parser: &mut Parser<'_>) -> TypeParametersOutcome {
    parser.start(NodeKind::InlineOperationalGlobal);
    if parser.at(&TokenKind::Pub) {
        let _ = parser.bump();
    }
    parser.start(NodeKind::InlineOperationalHeader);
    let _ = parser.bump();
    binder(parser);
    if parser.at(&TokenKind::Less) {
        let outcome = type_parameters(parser, TypeParameterOwnerBoundary::OperationalGlobal);
        if outcome.stops_declaration() {
            parser.finish();
            parser.finish();
            return outcome;
        }
    }
    let _ = parser.expect(&TokenKind::LeftParen, ExpectedForm::LeftParen);
    typed_pattern(parser);
    while parser.at(&TokenKind::Comma) {
        let _ = parser.bump();
        typed_pattern(parser);
    }
    let _ = parser.expect(&TokenKind::RightParen, ExpectedForm::RightParen);
    let _ = parser.expect(&TokenKind::Arrow, ExpectedForm::Arrow);
    computation_type(parser);
    if parser.at(&TokenKind::Where) {
        where_clause(
            parser,
            HeaderRecoveryBoundary::OpeningBrace(
                SynchronizationBoundary::OperationalBodyOpeningBrace,
            ),
        );
    }
    parser.finish();
    if !declaration_body_starts(
        parser,
        SynchronizationBoundary::OperationalBodyOpeningBrace,
        SynchronizationBoundary::BlockClosingBrace,
    ) {
        parser.finish();
        return TypeParametersOutcome::Complete;
    }
    block(parser);
    parser.finish();
    TypeParametersOutcome::Complete
}

pub(super) fn expression(parser: &mut Parser<'_>) {
    if parser.at_syntax_stop() {
        parser.report(ParseReason::ExpectedForm, ExpectedForm::Expression);
        return;
    }
    if parser.at_syntax_name() {
        let matcher = parser
            .selected_syntax()
            .expect("the selected syntax name has a matcher")
            .declaration
            .matcher
            .clone();
        syntax_invocation(parser, NodeKind::SyntaxInvocation, &matcher);
        return;
    }
    match expression_prefix_form(parser) {
        Some(ExpressionPrefixForm::Block) => block_expression(parser),
        Some(ExpressionPrefixForm::Function) => function_expression(parser),
        Some(ExpressionPrefixForm::Match) => match_expression(parser),
        Some(ExpressionPrefixForm::Handler) => handler_expression(parser),
        Some(ExpressionPrefixForm::Resume) => resume_expression(parser),
        Some(ExpressionPrefixForm::Resource) => resource_expression(parser),
        Some(ExpressionPrefixForm::Region) => region_expression(parser),
        Some(ExpressionPrefixForm::RegionSelection) => region_selection_expression(parser),

        None => expression::operator_expression(parser),
    }
}

fn syntax_invocation(
    parser: &mut Parser<'_>,
    kind: NodeKind,
    matcher: &[crate::surface::SurfaceSyntaxMatcherPart],
) {
    parser.start(kind);
    let _ = parser.bump();
    let outer_depth = parser.nesting_depth;
    if parser.enter_structure() {
        let inherited = parser
            .syntax_stops
            .iter()
            .enumerate()
            .filter_map(|(index, (_, _, depth))| (*depth == outer_depth).then_some(index))
            .collect::<Vec<_>>();
        for index in &inherited {
            parser.syntax_stops[*index].2 += 1;
        }
        for (index, part) in matcher.iter().enumerate() {
            match part {
                crate::surface::SurfaceSyntaxMatcherPart::Literal { kind, spelling } => {
                    if !parser.at_syntax_literal(kind, spelling) {
                        parser.report(ParseReason::ExpectedForm, ExpectedForm::Identifier);
                        break;
                    }
                    let _ = parser.bump();
                }
                crate::surface::SurfaceSyntaxMatcherPart::Capture { kind, .. } => {
                    parser.start(NodeKind::SyntaxArgument);
                    match kind {
                        crate::surface::SurfaceSyntaxCaptureKind::Expression
                        | crate::surface::SurfaceSyntaxCaptureKind::Type
                        | crate::surface::SurfaceSyntaxCaptureKind::Pattern => {
                            let mut added_stops = 0;
                            if !push_matcher_follow_stops(
                                parser,
                                &matcher[index + 1..],
                                0,
                                &mut added_stops,
                            ) {
                                for _ in 0..added_stops {
                                    let _ = parser.syntax_stops.pop();
                                }
                                parser.finish();
                                break;
                            }
                            match kind {
                                crate::surface::SurfaceSyntaxCaptureKind::Expression => {
                                    expression(parser)
                                }
                                crate::surface::SurfaceSyntaxCaptureKind::Type => {
                                    if parser.at_syntax_stop() {
                                        parser
                                            .report(ParseReason::ExpectedForm, ExpectedForm::Type);
                                    } else {
                                        type_expression(parser);
                                    }
                                }
                                crate::surface::SurfaceSyntaxCaptureKind::Pattern => {
                                    if parser.at_syntax_stop() {
                                        parser.report(
                                            ParseReason::ExpectedForm,
                                            ExpectedForm::Pattern,
                                        );
                                    } else {
                                        pattern(parser);
                                    }
                                }
                                crate::surface::SurfaceSyntaxCaptureKind::Identifier
                                | crate::surface::SurfaceSyntaxCaptureKind::Declaration => {
                                    unreachable!()
                                }
                            }
                            for _ in 0..added_stops {
                                let _ = parser.syntax_stops.pop();
                            }
                        }
                        crate::surface::SurfaceSyntaxCaptureKind::Identifier => {
                            if matches!(
                                parser.current(),
                                Some(TokenKind::Identifier(_) | TokenKind::UpperIdentifier(_))
                            ) {
                                let _ = parser.bump();
                            } else {
                                parser.report(ParseReason::ExpectedForm, ExpectedForm::Identifier);
                            }
                        }
                        crate::surface::SurfaceSyntaxCaptureKind::Declaration => {
                            declaration_capture(parser);
                        }
                    }
                    parser.finish();
                }
                crate::surface::SurfaceSyntaxMatcherPart::Container(_)
                | crate::surface::SurfaceSyntaxMatcherPart::LineEnd => {
                    let _ = match_structured_items(parser, &matcher[index..]);
                    break;
                }
            }
        }
        for index in inherited {
            parser.syntax_stops[index].2 -= 1;
        }
        parser.leave_structure();
    } else {
        parser.consume_rest();
    }
    parser.finish();
}

fn structured_literal(parser: &mut Parser<'_>, kind: &TokenKind, spelling: &str) -> bool {
    let found = parser.tokens.get(parser.position).map_or(0, |token| {
        let range = token.span.range();
        (range.end() - range.start()) as usize
    });
    if !parser.charge_matcher_work(spelling.len().saturating_add(found).saturating_add(3)) {
        return false;
    }
    parser.at_syntax_literal(kind, spelling)
}

fn push_matcher_follow_stops(
    parser: &mut Parser<'_>,
    parts: &[crate::surface::SurfaceSyntaxMatcherPart],
    depth: usize,
    added: &mut usize,
) -> bool {
    use crate::surface::{SurfaceMatcherContainerKind, SurfaceSyntaxMatcherPart};
    for part in parts {
        if !parser.charge_matcher_work(1) {
            return false;
        }
        match part {
            SurfaceSyntaxMatcherPart::Literal { kind, spelling } => {
                if !push_structured_stop(parser, kind, spelling) {
                    return false;
                }
                *added += 1;
                break;
            }
            SurfaceSyntaxMatcherPart::Container(container) => match &container.kind {
                SurfaceMatcherContainerKind::Group { braces } => {
                    let (kind, spelling) = if *braces {
                        (&TokenKind::LeftBrace, "{")
                    } else {
                        (&TokenKind::LeftParen, "(")
                    };
                    if !push_structured_stop(parser, kind, spelling) {
                        return false;
                    }
                    *added += 1;
                    break;
                }
                SurfaceMatcherContainerKind::Repeat { one_or_more, .. } => {
                    let Some(next) = depth.checked_add(1).filter(|next| {
                        parser.nesting_depth.saturating_add(*next) <= super::STRUCTURAL_DEPTH_LIMIT
                    }) else {
                        parser.fail_structural_depth();
                        return false;
                    };
                    if !push_matcher_follow_stops(parser, &container.body, next, added) {
                        return false;
                    }
                    if *one_or_more {
                        break;
                    }
                }
            },
            SurfaceSyntaxMatcherPart::Capture { .. } | SurfaceSyntaxMatcherPart::LineEnd => {
                break;
            }
        }
    }
    true
}

fn structured_starts(
    parser: &mut Parser<'_>,
    parts: &[crate::surface::SurfaceSyntaxMatcherPart],
) -> bool {
    structured_starts_at(parser, parts, parser.nesting_depth)
}

fn structured_starts_at(
    parser: &mut Parser<'_>,
    parts: &[crate::surface::SurfaceSyntaxMatcherPart],
    depth: usize,
) -> bool {
    use crate::surface::{
        SurfaceMatcherContainerKind, SurfaceSyntaxCaptureKind, SurfaceSyntaxMatcherPart,
    };
    for part in parts {
        if !parser.charge_matcher_work(1) {
            return false;
        }
        match part {
            SurfaceSyntaxMatcherPart::Literal { kind, spelling } => {
                return structured_literal(parser, kind, spelling);
            }
            SurfaceSyntaxMatcherPart::LineEnd => return parser.at(&TokenKind::LineEnd),
            SurfaceSyntaxMatcherPart::Capture { kind, .. } => {
                return match kind {
                    SurfaceSyntaxCaptureKind::Identifier => matches!(
                        parser.current(),
                        Some(TokenKind::Identifier(_) | TokenKind::UpperIdentifier(_))
                    ),
                    SurfaceSyntaxCaptureKind::Expression => starts_expression(parser),
                    SurfaceSyntaxCaptureKind::Type => starts_type(parser),
                    SurfaceSyntaxCaptureKind::Pattern => starts_pattern(parser),
                    SurfaceSyntaxCaptureKind::Declaration => parser.at(&TokenKind::LeftBrace),
                };
            }
            SurfaceSyntaxMatcherPart::Container(container) => match &container.kind {
                SurfaceMatcherContainerKind::Group { braces } => {
                    return parser.at(if *braces {
                        &TokenKind::LeftBrace
                    } else {
                        &TokenKind::LeftParen
                    });
                }
                SurfaceMatcherContainerKind::Repeat { one_or_more, .. } => {
                    let Some(next) = depth
                        .checked_add(1)
                        .filter(|value| *value <= super::STRUCTURAL_DEPTH_LIMIT)
                    else {
                        parser.fail_structural_depth();
                        return false;
                    };
                    if !parser.charge_matcher_work(1) {
                        return false;
                    }
                    if structured_starts_at(parser, &container.body, next) {
                        return true;
                    }
                    if parser.resource_failure.is_some() {
                        return false;
                    }
                    if *one_or_more {
                        return false;
                    }
                }
            },
        }
    }
    false
}

fn push_structured_stop(parser: &mut Parser<'_>, kind: &TokenKind, spelling: &str) -> bool {
    let live = parser.syntax_stops.len();
    let growth = if live == parser.syntax_stops.capacity() {
        live.saturating_mul(2).saturating_add(1)
    } else {
        0
    };
    if !parser.charge_matcher_work(
        growth
            .saturating_add(spelling.len().saturating_mul(2))
            .saturating_add(1),
    ) {
        return false;
    }
    parser.syntax_stops.reserve_exact(1);
    parser
        .syntax_stops
        .push((kind.clone(), spelling.to_owned(), parser.nesting_depth));
    true
}

fn match_structured_items(
    parser: &mut Parser<'_>,
    parts: &[crate::surface::SurfaceSyntaxMatcherPart],
) -> bool {
    use crate::surface::{
        SurfaceMatcherContainerKind, SurfaceSyntaxCaptureKind, SurfaceSyntaxMatcherPart,
    };
    for (index, part) in parts.iter().enumerate() {
        if !parser.charge_matcher_work(1) {
            return false;
        }
        match part {
            SurfaceSyntaxMatcherPart::Literal { kind, spelling } => {
                if !structured_literal(parser, kind, spelling) {
                    parser.report(ParseReason::ExpectedForm, ExpectedForm::Identifier);
                    return false;
                }
                let _ = parser.bump();
            }
            SurfaceSyntaxMatcherPart::LineEnd => {
                if !parser.expect(&TokenKind::LineEnd, ExpectedForm::Identifier) {
                    return false;
                }
            }
            SurfaceSyntaxMatcherPart::Capture { kind, .. } => {
                parser.start(NodeKind::SyntaxArgument);
                let mut added_stops = 0;
                if !push_matcher_follow_stops(parser, &parts[index + 1..], 0, &mut added_stops) {
                    for _ in 0..added_stops {
                        let _ = parser.syntax_stops.pop();
                    }
                    parser.finish();
                    return false;
                }
                let accepted = match kind {
                    SurfaceSyntaxCaptureKind::Identifier => {
                        if matches!(
                            parser.current(),
                            Some(TokenKind::Identifier(_) | TokenKind::UpperIdentifier(_))
                        ) {
                            let _ = parser.bump();
                            true
                        } else {
                            parser.report(ParseReason::ExpectedForm, ExpectedForm::Identifier);
                            false
                        }
                    }
                    SurfaceSyntaxCaptureKind::Expression => {
                        let accepted = starts_expression(parser);
                        expression(parser);
                        accepted
                    }
                    SurfaceSyntaxCaptureKind::Type => {
                        let accepted = starts_type(parser) && !parser.at_syntax_stop();
                        if accepted {
                            type_expression(parser);
                        } else {
                            parser.report(ParseReason::ExpectedForm, ExpectedForm::Type);
                        }
                        accepted
                    }
                    SurfaceSyntaxCaptureKind::Pattern => {
                        let accepted = starts_pattern(parser) && !parser.at_syntax_stop();
                        if accepted {
                            pattern(parser);
                        } else {
                            parser.report(ParseReason::ExpectedForm, ExpectedForm::Pattern);
                        }
                        accepted
                    }
                    SurfaceSyntaxCaptureKind::Declaration => {
                        let accepted = parser.at(&TokenKind::LeftBrace);
                        declaration_capture(parser);
                        accepted
                    }
                };
                for _ in 0..added_stops {
                    let _ = parser.syntax_stops.pop();
                }
                parser.finish();
                if !accepted {
                    return false;
                }
            }
            SurfaceSyntaxMatcherPart::Container(container) => {
                if !parser.enter_structure() {
                    return false;
                }
                if !parser.charge_matcher_work(3) {
                    parser.leave_structure();
                    return false;
                }
                let accepted = match &container.kind {
                    SurfaceMatcherContainerKind::Group { braces } => {
                        parser.start(NodeKind::SyntaxMatchedGroup);
                        let (open, close, expected) = if *braces {
                            (
                                TokenKind::LeftBrace,
                                TokenKind::RightBrace,
                                ExpectedForm::RightBrace,
                            )
                        } else {
                            (
                                TokenKind::LeftParen,
                                TokenKind::RightParen,
                                ExpectedForm::RightParen,
                            )
                        };
                        let open_ok = parser.expect(&open, ExpectedForm::Identifier);
                        let body_ok = open_ok && match_structured_items(parser, &container.body);
                        let close_ok = body_ok && parser.expect(&close, expected);
                        parser.finish();
                        close_ok
                    }
                    SurfaceMatcherContainerKind::Repeat {
                        one_or_more,
                        separator,
                    } => {
                        parser.start(NodeKind::SyntaxMatchedRepeat);
                        let mut count = 0usize;
                        let mut success = true;
                        let mut added_stops = 0;
                        if let Some((kind, spelling)) = separator {
                            if push_structured_stop(parser, kind, spelling) {
                                added_stops += 1;
                            } else {
                                success = false;
                            }
                        } else if !push_matcher_follow_stops(
                            parser,
                            &container.body,
                            0,
                            &mut added_stops,
                        ) {
                            success = false;
                        }
                        if !push_matcher_follow_stops(
                            parser,
                            &parts[index + 1..],
                            0,
                            &mut added_stops,
                        ) {
                            success = false;
                        }
                        while success && structured_starts(parser, &container.body) {
                            if !parser.charge_matcher_work(4) {
                                success = false;
                                break;
                            }
                            let previous = parser.position;
                            parser.start(NodeKind::SyntaxMatchedIteration);
                            let body_ok = match_structured_items(parser, &container.body);
                            parser.finish();
                            if !body_ok || parser.position == previous {
                                success = false;
                                break;
                            }
                            count += 1;
                            if let Some((kind, spelling)) = separator {
                                if !structured_literal(parser, kind, spelling) {
                                    break;
                                }
                                let separator_span = parser.current_span();
                                let _ = parser.bump();
                                if !structured_starts(parser, &container.body) {
                                    if let Some(span) = separator_span {
                                        parser.error_at_span(
                                            ParseReason::MatcherTrailingSeparator,
                                            span,
                                        );
                                    }
                                    success = false;
                                    break;
                                }
                            }
                        }
                        if *one_or_more && count == 0 {
                            parser.error_at_current(ParseReason::MatcherRepetitionEmpty);
                            success = false;
                        }
                        for _ in 0..added_stops {
                            let _ = parser.syntax_stops.pop();
                        }
                        parser.finish();
                        success && parser.resource_failure.is_none()
                    }
                };
                parser.leave_structure();
                if !accepted {
                    return false;
                }
            }
        }
    }
    true
}

fn declaration_capture(parser: &mut Parser<'_>) {
    if !parser.expect(&TokenKind::LeftBrace, ExpectedForm::LeftBrace) {
        return;
    }
    if !parser.enter_structure() {
        parser.consume_rest();
        return;
    }
    while parser.at(&TokenKind::LineEnd) {
        let _ = parser.bump();
    }
    if parser.selected_declaration_syntax().is_some()
        || starts_syntax_declaration(parser)
        || parser.at(&TokenKind::Resource)
        || parser.at(&TokenKind::Pub) && parser.nth(1) == Some(&TokenKind::Resource)
        || !starts_module_declaration(parser)
    {
        parser.report(ParseReason::ExpectedForm, ExpectedForm::Identifier);
    } else {
        let _ = module_declaration(parser);
    }
    while parser.at(&TokenKind::LineEnd) {
        let _ = parser.bump();
    }
    let _ = parser.expect(&TokenKind::RightBrace, ExpectedForm::RightBrace);
    parser.leave_structure();
}

fn expression_prefix_form(parser: &Parser<'_>) -> Option<ExpressionPrefixForm> {
    selected_dialect()
        .expression_prefixes
        .iter()
        .copied()
        .find(|form| match form {
            ExpressionPrefixForm::Block => parser.at(&TokenKind::LeftBrace),
            ExpressionPrefixForm::Function => parser.at(&TokenKind::Fn),
            ExpressionPrefixForm::Match => parser.at(&TokenKind::Match),
            ExpressionPrefixForm::Handler => parser.at(&TokenKind::Handle),
            ExpressionPrefixForm::Resume => parser.at(&TokenKind::Resume),
            ExpressionPrefixForm::Resource => parser.at(&TokenKind::Resource),
            ExpressionPrefixForm::Region => parser.at(&TokenKind::Region),
            ExpressionPrefixForm::RegionSelection => parser.at(&TokenKind::Using),
        })
}

fn resume_expression(parser: &mut Parser<'_>) {
    parser.start(NodeKind::ResumeExpression);
    let _ = parser.bump();
    expression(parser);
    parser.finish();
}

fn resource_expression(parser: &mut Parser<'_>) {
    if matches!(parser.nth(1), Some(TokenKind::UpperIdentifier(_))) {
        parser.start(NodeKind::ProviderResourceExpression);
        let _ = parser.bump();
        parser.start(NodeKind::EffectInstance);
        if parser.nth(1) == Some(&TokenKind::Dot) {
            qualified_name(parser, true);
        } else {
            expect_upper_identifier(parser);
        }
        if parser.at(&TokenKind::Less) {
            type_arguments(parser);
        } else {
            parser.report(ParseReason::ExpectedForm, ExpectedForm::Type);
        }
        parser.finish();
        binder(parser);
        let _ = parser.expect(&TokenKind::Equal, ExpectedForm::Equal);
        expression::primary_expression(parser);
        block(parser);
        parser.finish();
        return;
    }
    parser.start(NodeKind::ResourceExpression);
    let _ = parser.bump();
    if matches!(parser.current(), Some(TokenKind::Identifier(name)) if name == "cell") {
        let _ = parser.bump();
    } else {
        parser.report(ParseReason::ExpectedForm, ExpectedForm::Identifier);
    }
    let _ = parser.expect(&TokenKind::Less, ExpectedForm::Type);
    expect_upper_identifier(parser);
    let _ = parser.expect(&TokenKind::Greater, ExpectedForm::Greater);
    binder(parser);
    let _ = parser.expect(&TokenKind::Equal, ExpectedForm::Equal);
    expression::primary_expression(parser);
    block(parser);
    parser.finish();
}

fn region_expression(parser: &mut Parser<'_>) {
    parser.start(NodeKind::RegionExpression);
    let _ = parser.bump();
    let _ = parser.expect(&TokenKind::Less, ExpectedForm::Type);
    expect_upper_identifier(parser);
    let _ = parser.expect(&TokenKind::Greater, ExpectedForm::Greater);
    binder(parser);
    if parser.at(&TokenKind::Equal) {
        let _ = parser.bump();
        expression::primary_expression(parser);
    }
    block(parser);
    parser.finish();
}

fn region_selection_expression(parser: &mut Parser<'_>) {
    parser.start(NodeKind::RegionSelectionExpression);
    let _ = parser.bump();
    expression::primary_expression(parser);
    block(parser);
    parser.finish();
}

fn handler_expression(parser: &mut Parser<'_>) {
    parser.start(NodeKind::HandlerExpression);
    let _ = parser.bump();
    expression(parser);
    let _ = parser.expect(&TokenKind::With, ExpectedForm::Expression);
    effect_instance(parser);
    if parser.at(&TokenKind::Using) {
        let _ = parser.bump();
        expression::primary_expression(parser);
    }
    let _ = parser.expect(&TokenKind::LeftBrace, ExpectedForm::LeftBrace);
    let _ = parser.expect(&TokenKind::LineEnd, ExpectedForm::LineEnd);
    if matches!(
        parser.current(),
        Some(TokenKind::RightBrace | TokenKind::EndOfFile)
    ) {
        parser.report(ParseReason::ExpectedForm, ExpectedForm::Identifier);
    }
    while !matches!(
        parser.current(),
        Some(TokenKind::RightBrace | TokenKind::EndOfFile)
    ) {
        parser.start(NodeKind::HandlerClause);
        binder(parser);
        pattern(parser);
        let _ = parser.expect(&TokenKind::FatArrow, ExpectedForm::FatArrow);
        expression(parser);
        parser.finish();
        if parser.at(&TokenKind::LineEnd) {
            let _ = parser.bump();
        } else {
            break;
        }
    }
    let _ = parser.expect(&TokenKind::RightBrace, ExpectedForm::RightBrace);
    parser.finish();
}

pub(super) fn hook_expression(parser: &mut Parser<'_>) {
    parser.start(NodeKind::HookExpression);
    let _ = parser.bump();
    effect_instance(parser);
    block(parser);
    parser.finish();
}

pub(super) fn registration_expression(parser: &mut Parser<'_>) {
    parser.start(NodeKind::RegistrationExpression);
    // A primary transformer can nest another registration before any block.
    if !parser.enter_structure() {
        parser.consume_rest();
        parser.finish();
        return;
    }
    let _ = parser.bump();
    effect_instance(parser);
    expression::primary_expression(parser);
    block(parser);
    parser.leave_structure();
    parser.finish();
}

pub(super) fn cleanup_expression(parser: &mut Parser<'_>) {
    parser.start(NodeKind::CleanupExpression);
    // Initializers can nest cleanup before entering any body block.
    if !parser.enter_structure() {
        parser.consume_rest();
        parser.finish();
        return;
    }
    let _ = parser.bump();
    expression(parser);
    block(parser);
    parser.leave_structure();
    parser.finish();
}

pub(super) fn perform_expression(parser: &mut Parser<'_>) {
    parser.start(NodeKind::PerformExpression);
    let _ = parser.bump();
    parser.start(NodeKind::OperationReference);
    if parser.nth(1) == Some(&TokenKind::Dot)
        && (matches!(parser.nth(2), Some(TokenKind::UpperIdentifier(_)))
            || (parser.nth_is_admission_identifier(2)
                && matches!(parser.nth(3), Some(TokenKind::Dot | TokenKind::Less))))
    {
        qualified_name(parser, true);
    } else {
        expect_upper_identifier(parser);
    }
    if parser.at(&TokenKind::Less) {
        type_arguments(parser);
    }
    let _ = parser.expect(&TokenKind::Dot, ExpectedForm::Identifier);
    expect_lower_identifier(parser);
    parser.finish();
    if expression::starts_primary(parser) {
        expression::primary_expression(parser);
    } else {
        parser.report(ParseReason::ExpectedOperand, ExpectedForm::Operand);
    }
    parser.finish();
}

fn match_expression(parser: &mut Parser<'_>) {
    parser.start(NodeKind::MatchExpression);
    if !parser.enter_structures(super::MATCH_STRUCTURAL_WEIGHT) {
        parser.consume_rest();
        parser.finish();
        return;
    }
    let _ = parser.bump();
    expression(parser);
    let _ = parser.expect(&TokenKind::LeftBrace, ExpectedForm::LeftBrace);
    let _ = parser.expect(&TokenKind::LineEnd, ExpectedForm::LineEnd);
    if matches!(
        parser.current(),
        Some(TokenKind::RightBrace | TokenKind::EndOfFile)
    ) {
        parser.report(ParseReason::ExpectedForm, ExpectedForm::Pattern);
    }
    while !matches!(
        parser.current(),
        Some(TokenKind::RightBrace | TokenKind::EndOfFile)
    ) {
        match_arm(parser);
        if parser.at(&TokenKind::LineEnd) {
            let _ = parser.bump();
        } else {
            break;
        }
    }
    let _ = parser.expect(&TokenKind::RightBrace, ExpectedForm::RightBrace);
    parser.leave_structures(super::MATCH_STRUCTURAL_WEIGHT);
    parser.finish();
}

fn match_arm(parser: &mut Parser<'_>) {
    parser.start(NodeKind::MatchArm);
    let recovery_start = parser.pending_recovery_count();
    pattern(parser);
    if parser.at(&TokenKind::FatArrow) {
        let _ = parser.bump();
    } else if let Some(primary) = parser.current_span()
        && let Some(diagnostic) = parser.report_at(
            ParseReason::ExpectedForm,
            ExpectedForm::FatArrow,
            primary,
            None,
        )
    {
        parser.mark_pending_recovery(diagnostic);
    }
    expression(parser);
    resolve_line_or_eof(parser, recovery_start);
    parser.finish();
}

fn block_expression(parser: &mut Parser<'_>) {
    block(parser);
}

fn block(parser: &mut Parser<'_>) {
    parser.start(NodeKind::Block);
    if !parser.enter_structure() {
        parser.consume_rest();
        parser.finish();
        return;
    }
    let _ = parser.expect(&TokenKind::LeftBrace, ExpectedForm::LeftBrace);
    let _ = parser.expect(&TokenKind::LineEnd, ExpectedForm::LineEnd);
    loop {
        if parser.at(&TokenKind::Let) {
            if parser
                .nth(1)
                .is_some_and(|kind| matches!(kind, TokenKind::Rec))
            {
                recursive_binding_group(parser);
            } else {
                local_binding(parser);
            }
            let _ = parser.expect(&TokenKind::LineEnd, ExpectedForm::LineEnd);
        } else if parser.at(&TokenKind::Newtype) {
            newtype_declaration(parser, false);
            let _ = parser.expect(&TokenKind::LineEnd, ExpectedForm::LineEnd);
        } else if parser.at(&TokenKind::With) {
            lexical_evidence_declaration(parser);
            let _ = parser.expect(&TokenKind::LineEnd, ExpectedForm::LineEnd);
        } else if parser.at(&TokenKind::And) {
            rejected_stray_and(parser);
            if parser.at(&TokenKind::LineEnd) {
                let _ = parser.bump();
            }
        } else {
            break;
        }
    }
    let recovery_start = parser.pending_recovery_count();
    if starts_expression(parser) {
        expression(parser);
    } else {
        parser.report(ParseReason::ExpectedForm, ExpectedForm::Expression);
    }
    if parser.at(&TokenKind::LineEnd) {
        let _ = parser.bump();
    }
    if parser.at(&TokenKind::RightBrace) {
        parser
            .resolve_pending_at_current(recovery_start, SynchronizationBoundary::BlockClosingBrace);
    } else if parser.at(&TokenKind::EndOfFile) {
        parser.resolve_pending_at_current(recovery_start, SynchronizationBoundary::EndOfFile);
    }
    let _ = parser.expect(&TokenKind::RightBrace, ExpectedForm::RightBrace);
    parser.leave_structure();
    parser.finish();
}

fn recursive_binding_group(parser: &mut Parser<'_>) {
    parser.start(NodeKind::RecursiveBindingGroup);
    let _ = parser.bump();
    let _ = parser.expect(&TokenKind::Rec, ExpectedForm::Identifier);
    recursive_binding_member(parser);
    while parser.at(&TokenKind::LineEnd)
        && parser
            .nth(1)
            .is_some_and(|kind| matches!(kind, TokenKind::And))
    {
        let _ = parser.bump();
        let _ = parser.bump();
        recursive_binding_member(parser);
    }
    parser.finish();
}

fn recursive_binding_member(parser: &mut Parser<'_>) {
    parser.start(NodeKind::RecursiveBindingMember);
    let recovery_start = parser.pending_recovery_count();
    let splice = parser.in_template && parser.at(&TokenKind::Dollar);
    if !splice && !matches!(parser.current(), Some(TokenKind::Identifier(_))) {
        if let Some(primary) = parser.current_span()
            && let Some(diagnostic) = parser.report_at(
                ParseReason::ExpectedRecursiveMember,
                ExpectedForm::Identifier,
                primary,
                None,
            )
        {
            parser.mark_pending_recovery(diagnostic);
        }
        resolve_line_or_eof(parser, recovery_start);
        parser.finish();
        return;
    }
    if splice {
        parser.start(NodeKind::Binder);
        let _ = parser.bump();
        expect_lower_identifier(parser);
        parser.finish();
    } else {
        binder(parser);
    }
    if parser.at(&TokenKind::Colon) {
        let _ = parser.bump();
        type_expression(parser);
    } else if let Some(primary) = parser.current_span()
        && let Some(diagnostic) = parser.report_at(
            ParseReason::ExpectedForm,
            ExpectedForm::Colon,
            primary,
            None,
        )
    {
        parser.mark_pending_recovery(diagnostic);
    }
    let _ = parser.expect(&TokenKind::Equal, ExpectedForm::Equal);
    if starts_expression(parser) {
        expression(parser);
    } else if let Some(primary) = parser.current_span()
        && let Some(diagnostic) = parser.report_at(
            ParseReason::ExpectedForm,
            ExpectedForm::Expression,
            primary,
            None,
        )
    {
        parser.mark_pending_recovery(diagnostic);
    }
    resolve_line_or_eof(parser, recovery_start);
    parser.finish();
}

fn rejected_stray_and(parser: &mut Parser<'_>) {
    parser.start(NodeKind::Error);
    parser.error_at_current(ParseReason::UnexpectedAnd);
    while !matches!(
        parser.current(),
        Some(TokenKind::LineEnd | TokenKind::RightBrace | TokenKind::EndOfFile)
    ) {
        let _ = parser.bump();
    }
    parser.finish();
}

fn local_binding(parser: &mut Parser<'_>) {
    parser.start(NodeKind::LocalBinding);
    let _ = parser.bump();
    pattern(parser);
    if parser.at(&TokenKind::Colon) {
        let _ = parser.bump();
        type_expression(parser);
    }
    let _ = parser.expect(&TokenKind::Equal, ExpectedForm::Equal);
    let recovery_start = parser.pending_recovery_count();
    expression(parser);
    resolve_line_or_eof(parser, recovery_start);
    parser.finish();
}

fn resolve_line_or_eof(parser: &mut Parser<'_>, recovery_start: usize) {
    resolve_line_eof_or_brace(
        parser,
        recovery_start,
        SynchronizationBoundary::BlockClosingBrace,
    );
}

fn resolve_line_eof_or_brace(
    parser: &mut Parser<'_>,
    recovery_start: usize,
    closing_brace: SynchronizationBoundary,
) {
    if parser.at(&TokenKind::LineEnd) {
        parser.resolve_pending_at_current(recovery_start, SynchronizationBoundary::LogicalLineEnd);
    } else if parser.at(&TokenKind::EndOfFile) {
        parser.resolve_pending_at_current(recovery_start, SynchronizationBoundary::EndOfFile);
    } else if parser.at(&TokenKind::RightBrace) {
        parser.resolve_pending_at_current(recovery_start, closing_brace);
    }
}

fn function_expression(parser: &mut Parser<'_>) {
    parser.start(NodeKind::FunctionExpression);
    if !parser.enter_structure() {
        parser.consume_rest();
        parser.finish();
        return;
    }
    let _ = parser.bump();
    let _ = parser.expect(&TokenKind::LeftParen, ExpectedForm::LeftParen);
    pattern(parser);
    while parser.at(&TokenKind::Comma) {
        let _ = parser.bump();
        pattern(parser);
    }
    let _ = parser.expect(&TokenKind::RightParen, ExpectedForm::RightParen);
    block(parser);
    parser.leave_structure();
    parser.finish();
}

fn binder(parser: &mut Parser<'_>) {
    parser.start(NodeKind::Binder);
    if matches!(parser.current(), Some(TokenKind::Identifier(_))) {
        let _ = parser.bump();
    } else {
        parser.report(ParseReason::ExpectedForm, ExpectedForm::Identifier);
    }
    parser.finish();
}

fn type_parameters(
    parser: &mut Parser<'_>,
    owner: TypeParameterOwnerBoundary,
) -> TypeParametersOutcome {
    parser.start(NodeKind::TypeParameters);
    let _ = parser.bump();
    let recovery_start = parser.pending_recovery_count();
    let mut recovered = !type_parameter(parser, owner);
    resolve_type_parameter_recovery_at_delimiter(parser, recovery_start);
    while parser.at(&TokenKind::Comma) {
        let _ = parser.bump();
        recovered |= !type_parameter(parser, owner);
        resolve_type_parameter_recovery_at_delimiter(parser, recovery_start);
    }
    let outcome = if parser.at(&TokenKind::Greater) {
        let _ = parser.bump();
        if recovered {
            TypeParametersOutcome::RecoveredToOwnerOrCloser
        } else {
            TypeParametersOutcome::Complete
        }
    } else {
        report_pending_expected(parser, ExpectedForm::Greater);
        recover_type_parameters(parser, recovery_start, owner)
    };
    parser.finish();
    outcome
}

fn resolve_type_parameter_recovery_at_delimiter(parser: &mut Parser<'_>, recovery_start: usize) {
    let boundary = if parser.at(&TokenKind::Comma) {
        Some(SynchronizationBoundary::TypeParameterSeparator)
    } else if parser.at(&TokenKind::Greater) {
        Some(SynchronizationBoundary::TypeParameterListClosing)
    } else {
        None
    };
    if let Some(boundary) = boundary {
        parser.resolve_pending_at_current(recovery_start, boundary);
    }
}

fn recover_type_parameters(
    parser: &mut Parser<'_>,
    recovery_start: usize,
    owner: TypeParameterOwnerBoundary,
) -> TypeParametersOutcome {
    if !at_type_parameter_owner(parser, owner)
        && !matches!(
            parser.current(),
            Some(TokenKind::Greater | TokenKind::LineEnd | TokenKind::EndOfFile) | None
        )
    {
        parser.start(NodeKind::Error);
        while !at_type_parameter_owner(parser, owner)
            && !matches!(
                parser.current(),
                Some(TokenKind::Greater | TokenKind::LineEnd | TokenKind::EndOfFile) | None
            )
        {
            let _ = parser.bump();
        }
        parser.finish();
    }

    if parser.at(&TokenKind::Greater) {
        parser.resolve_pending_at_current(
            recovery_start,
            SynchronizationBoundary::TypeParameterListClosing,
        );
        let _ = parser.bump();
        TypeParametersOutcome::RecoveredToOwnerOrCloser
    } else if at_type_parameter_owner(parser, owner) {
        parser.resolve_pending_at_current(recovery_start, type_parameter_owner_boundary(owner));
        TypeParametersOutcome::RecoveredToOwnerOrCloser
    } else if parser.at(&TokenKind::LineEnd) {
        parser.resolve_pending_at_current(recovery_start, SynchronizationBoundary::LogicalLineEnd);
        TypeParametersOutcome::RecoveredToLineEnd
    } else {
        parser.resolve_pending_at_current(recovery_start, SynchronizationBoundary::EndOfFile);
        TypeParametersOutcome::RecoveredToEndOfFile
    }
}

fn at_type_parameter_owner(parser: &Parser<'_>, owner: TypeParameterOwnerBoundary) -> bool {
    match owner {
        TypeParameterOwnerBoundary::TypeDeclaration => parser.at(&TokenKind::Equal),
        TypeParameterOwnerBoundary::EquationalGlobal => parser.at(&TokenKind::Colon),
        TypeParameterOwnerBoundary::OperationalGlobal => parser.at(&TokenKind::LeftParen),
        TypeParameterOwnerBoundary::Implementation => {
            starts_implementation_interface_application(parser)
        }
        TypeParameterOwnerBoundary::Interface => parser.at(&TokenKind::LeftBrace),
        TypeParameterOwnerBoundary::InterfaceMethod => parser.at(&TokenKind::Colon),
        TypeParameterOwnerBoundary::Effect => parser.at(&TokenKind::LeftBrace),
    }
}

fn starts_implementation_interface_application(parser: &Parser<'_>) -> bool {
    parser.at_upper_identifier()
        && (parser.nth(1) == Some(&TokenKind::Less)
            || matches!(
                (parser.nth(1), parser.nth(2), parser.nth(3)),
                (
                    Some(TokenKind::Dot),
                    Some(TokenKind::UpperIdentifier(_)),
                    Some(TokenKind::Less)
                )
            ))
}

const fn type_parameter_owner_boundary(
    owner: TypeParameterOwnerBoundary,
) -> SynchronizationBoundary {
    match owner {
        TypeParameterOwnerBoundary::TypeDeclaration => {
            SynchronizationBoundary::TypeDeclarationEqual
        }
        TypeParameterOwnerBoundary::EquationalGlobal => {
            SynchronizationBoundary::EquationalGlobalColon
        }
        TypeParameterOwnerBoundary::OperationalGlobal => {
            SynchronizationBoundary::OperationalParameterOpeningParen
        }
        TypeParameterOwnerBoundary::Implementation => {
            SynchronizationBoundary::ImplementationInterfaceHead
        }
        TypeParameterOwnerBoundary::Interface => SynchronizationBoundary::InterfaceBodyOpeningBrace,
        TypeParameterOwnerBoundary::InterfaceMethod => {
            SynchronizationBoundary::InterfaceMethodColon
        }
        TypeParameterOwnerBoundary::Effect => SynchronizationBoundary::InterfaceBodyOpeningBrace,
    }
}

fn type_parameter(parser: &mut Parser<'_>, owner: TypeParameterOwnerBoundary) -> bool {
    parser.start(NodeKind::TypeParameter);
    let mut complete = if parser.at_upper_identifier() {
        let _ = parser.bump();
        true
    } else {
        report_pending_expected(parser, ExpectedForm::Identifier);
        if !at_type_parameter_owner(parser, owner)
            && !matches!(
                parser.current(),
                Some(
                    TokenKind::Colon
                        | TokenKind::Comma
                        | TokenKind::Greater
                        | TokenKind::LineEnd
                        | TokenKind::EndOfFile
                ) | None
            )
        {
            let _ = parser.bump();
        }
        false
    };
    if parser.at(&TokenKind::Colon) {
        let _ = parser.bump();
        complete &= kind_expression(parser, owner);
    }
    parser.finish();
    complete
}

fn kind_expression(parser: &mut Parser<'_>, owner: TypeParameterOwnerBoundary) -> bool {
    parser.start(NodeKind::Kind);
    let mut complete = kind_atom(parser, owner);
    if parser.at(&TokenKind::Arrow) {
        let _ = parser.bump();
        if parser.enter_structure() {
            complete &= kind_expression(parser, owner);
            parser.leave_structure();
        } else {
            parser.consume_rest();
            complete = false;
        }
    }
    parser.finish();
    complete
}

fn kind_atom(parser: &mut Parser<'_>, owner: TypeParameterOwnerBoundary) -> bool {
    if at_kind_owner(parser, owner) {
        report_pending_expected(parser, ExpectedForm::Kind);
        return false;
    }
    match parser.current() {
        Some(TokenKind::UpperIdentifier(name)) if name == "Type" || name == "EffectRow" => {
            let _ = parser.bump();
            true
        }
        Some(TokenKind::LeftParen) => {
            parser.start(NodeKind::ParenthesizedKind);
            let opening = parser.current_span();
            let _ = parser.bump();
            let mut complete = if parser.enter_structure() {
                let nested_complete = kind_expression(parser, owner);
                parser.leave_structure();
                nested_complete
            } else {
                parser.consume_rest();
                parser.finish();
                return false;
            };
            if parser.at(&TokenKind::RightParen) {
                let _ = parser.bump();
            } else {
                report_pending_unclosed_kind_group(parser, opening);
                complete = false;
            }
            parser.finish();
            complete
        }
        _ => {
            report_pending_expected(parser, ExpectedForm::Kind);
            if !at_type_parameter_owner(parser, owner)
                && !matches!(
                    parser.current(),
                    Some(
                        TokenKind::Arrow
                            | TokenKind::Comma
                            | TokenKind::Greater
                            | TokenKind::RightParen
                            | TokenKind::LineEnd
                            | TokenKind::EndOfFile
                    ) | None
                )
            {
                let _ = parser.bump();
            }
            false
        }
    }
}

fn at_kind_owner(parser: &Parser<'_>, owner: TypeParameterOwnerBoundary) -> bool {
    match owner {
        TypeParameterOwnerBoundary::OperationalGlobal if parser.at(&TokenKind::LeftParen) => {
            !matches!(
                parser.nth(1),
                Some(TokenKind::UpperIdentifier(name)) if name == "Type"
            ) && parser.nth(1) != Some(&TokenKind::LeftParen)
        }
        TypeParameterOwnerBoundary::Implementation => {
            !matches!(
                parser.current(),
                Some(TokenKind::UpperIdentifier(name)) if name == "Type"
            ) && starts_implementation_interface_application(parser)
        }
        TypeParameterOwnerBoundary::Effect => parser.at(&TokenKind::LeftBrace),
        _ => at_type_parameter_owner(parser, owner),
    }
}

fn report_pending_unclosed_kind_group(
    parser: &mut Parser<'_>,
    opening: Option<crate::source::Span>,
) {
    let primary = opening.or_else(|| parser.current_span());
    if let Some(primary) = primary
        && let Some(diagnostic) = parser.report_at(
            ParseReason::UnclosedGroup,
            ExpectedForm::RightParen,
            primary,
            parser.current_span(),
        )
    {
        parser.mark_pending_recovery(diagnostic);
    }
}

pub(super) fn pattern(parser: &mut Parser<'_>) {
    pattern_inner(parser, false);
}

fn pattern_inner(parser: &mut Parser<'_>, allow_juxtaposed_payload: bool) {
    parser.start(NodeKind::Pattern);
    if parser.declaration_output_nodes.is_some()
        && matches!(
            parser
                .declaration_output_nodes
                .and_then(|nodes| nodes.get(&parser.position)),
            Some(
                crate::syntax::MacroOutputNode::Expression(_, _)
                    | crate::syntax::MacroOutputNode::ForwardedExpression(_, _)
                    | crate::syntax::MacroOutputNode::ForwardedType(_, _)
                    | crate::syntax::MacroOutputNode::ForwardedDeclaration(_, _)
            )
        )
    {
        parser.report(ParseReason::ExpectedForm, ExpectedForm::Pattern);
        let _ = parser.bump();
        parser.finish();
        return;
    }
    if parser.in_template && parser.at(&TokenKind::Dollar) {
        let _ = parser.bump();
        expect_lower_identifier(parser);
        parser.finish();
        return;
    }
    let form = pattern_form(parser);
    let outer_depth = parser.nesting_depth;
    let owns_structure = matches!(
        form,
        Some(PatternForm::Constructor | PatternForm::Parenthesized)
    );
    if owns_structure && !parser.enter_structures(super::PATTERN_STRUCTURAL_WEIGHT) {
        parser.consume_rest();
        parser.finish();
        return;
    }
    match form {
        Some(PatternForm::Binder)
            if starts_lowercase_qualification(parser) && !parser.nth_at_syntax_stop(1) =>
        {
            reject_lowercase_qualification(parser);
        }
        Some(PatternForm::Binder) => binder(parser),
        Some(PatternForm::Wildcard) => {
            parser.start(NodeKind::WildcardPattern);
            let _ = parser.bump();
            parser.finish();
        }
        Some(PatternForm::Boolean) => {
            parser.start(NodeKind::BooleanPattern);
            let _ = parser.bump();
            parser.finish();
        }
        Some(PatternForm::Constructor) => {
            constructor_pattern(parser, allow_juxtaposed_payload, outer_depth)
        }
        Some(PatternForm::Parenthesized) => parenthesized_pattern(parser),
        None => parser.report(ParseReason::ExpectedForm, ExpectedForm::Pattern),
    }
    if owns_structure {
        parser.leave_structures(super::PATTERN_STRUCTURAL_WEIGHT);
    }
    parser.finish();
}

fn pattern_form(parser: &Parser<'_>) -> Option<PatternForm> {
    if parser.is_admission_identifier()
        && matches!(parser.nth(1), Some(TokenKind::Dot | TokenKind::LeftParen))
    {
        return Some(PatternForm::Constructor);
    }
    selected_dialect()
        .pattern_forms
        .iter()
        .copied()
        .find(|form| {
            matches!(
                (form, parser.current()),
                (PatternForm::Binder, Some(TokenKind::Identifier(_)))
                    | (PatternForm::Wildcard, Some(TokenKind::Wildcard))
                    | (
                        PatternForm::Boolean,
                        Some(TokenKind::True | TokenKind::False)
                    )
                    | (
                        PatternForm::Constructor,
                        Some(TokenKind::UpperIdentifier(_))
                    )
                    | (PatternForm::Parenthesized, Some(TokenKind::LeftParen))
            )
        })
}

fn starts_pattern(parser: &Parser<'_>) -> bool {
    (parser.in_template && parser.at(&TokenKind::Dollar)) || pattern_form(parser).is_some()
}

fn constructor_pattern(
    parser: &mut Parser<'_>,
    allow_juxtaposed_payload: bool,
    outer_depth: usize,
) {
    parser.start(NodeKind::ConstructorPattern);
    if !parser.nth_at_syntax_stop_in_depth(1, outer_depth)
        && parser
            .nth(1)
            .is_some_and(|kind| matches!(kind, TokenKind::Dot))
    {
        qualified_name(parser, true);
    } else {
        let _ = parser.bump();
    }
    if parser.at(&TokenKind::LeftParen) {
        let _ = parser.bump();
        let tuple_start = parser.event_position();
        pattern(parser);
        if parser.at(&TokenKind::Comma) {
            let _ = parser.insert_start(tuple_start, NodeKind::TuplePattern);
            while parser.at(&TokenKind::Comma) {
                let _ = parser.bump();
                pattern(parser);
            }
            parser.finish();
        }
        let _ = parser.expect(&TokenKind::RightParen, ExpectedForm::RightParen);
    } else if allow_juxtaposed_payload && starts_pattern(parser) {
        pattern_inner(parser, true);
    }
    parser.finish();
}

fn parenthesized_pattern(parser: &mut Parser<'_>) {
    let _ = parser.bump();
    if parser.at(&TokenKind::RightParen) {
        parser.start(NodeKind::UnitPattern);
        let _ = parser.bump();
        parser.finish();
        return;
    }
    let tuple_start = parser.event_position();
    pattern_inner(parser, true);
    if parser.at(&TokenKind::Comma) {
        let _ = parser.insert_start(tuple_start, NodeKind::TuplePattern);
        while parser.at(&TokenKind::Comma) {
            let _ = parser.bump();
            pattern(parser);
        }
        parser.finish();
    }
    let _ = parser.expect(&TokenKind::RightParen, ExpectedForm::RightParen);
}

fn typed_pattern(parser: &mut Parser<'_>) {
    parser.start(NodeKind::TypedPattern);
    pattern(parser);
    let _ = parser.expect(&TokenKind::Colon, ExpectedForm::Colon);
    type_expression(parser);
    parser.finish();
}

pub(super) fn type_expression(parser: &mut Parser<'_>) {
    parser.start(NodeKind::Type);
    if parser.at_forwarded_declaration() {
        parser.report(ParseReason::ExpectedForm, ExpectedForm::Type);
        let _ = parser.bump();
        parser.finish();
        return;
    }
    if parser.at_syntax_stop() {
        parser.report(ParseReason::ExpectedForm, ExpectedForm::Type);
        parser.finish();
        return;
    }
    atomic_type(parser);
    if parser.at(&TokenKind::Arrow) && !parser.at_syntax_stop() {
        let _ = parser.bump();
        let outer_depth = parser.nesting_depth;
        if parser.enter_structure() {
            let inherited = parser
                .syntax_stops
                .iter()
                .enumerate()
                .filter_map(|(index, (_, _, depth))| (*depth == outer_depth).then_some(index))
                .collect::<Vec<_>>();
            for index in &inherited {
                parser.syntax_stops[*index].2 += 1;
            }
            type_expression(parser);
            for index in inherited {
                parser.syntax_stops[index].2 -= 1;
            }
            parser.leave_structure();
        } else {
            parser.consume_rest();
        }
        if parser.at(&TokenKind::Bang) && !parser.at_syntax_stop() {
            let _ = parser.bump();
            effect_row(parser);
        }
    }
    parser.finish();
}

fn computation_type(parser: &mut Parser<'_>) {
    type_expression(parser);
    if parser.at(&TokenKind::Bang) {
        let _ = parser.bump();
        effect_row(parser);
    }
}

fn effect_row(parser: &mut Parser<'_>) {
    parser.start(NodeKind::EffectRow);
    let _ = parser.expect(&TokenKind::LeftBrace, ExpectedForm::EffectRow);
    if parser.at(&TokenKind::Pipe) {
        let _ = parser.bump();
        expect_upper_identifier(parser);
    } else if parser.at_upper_identifier() {
        effect_instance(parser);
        while parser.at(&TokenKind::Comma) {
            let _ = parser.bump();
            effect_instance(parser);
        }
        if parser.at(&TokenKind::Pipe) {
            let _ = parser.bump();
            expect_upper_identifier(parser);
        }
    }
    let _ = parser.expect(&TokenKind::RightBrace, ExpectedForm::EffectRow);
    parser.finish();
}

fn effect_instance(parser: &mut Parser<'_>) {
    parser.start(NodeKind::EffectInstance);
    if parser
        .nth(1)
        .is_some_and(|kind| matches!(kind, TokenKind::Dot))
    {
        qualified_name(parser, true);
    } else {
        expect_upper_identifier(parser);
    }
    if parser.at(&TokenKind::Less) {
        type_arguments(parser);
    }
    parser.finish();
}

fn starts_type(parser: &Parser<'_>) -> bool {
    atomic_type_form(parser).is_some() || starts_lowercase_qualification(parser)
}

fn atomic_type(parser: &mut Parser<'_>) {
    parser.start(NodeKind::AtomicType);
    if starts_lowercase_qualification(parser) {
        reject_lowercase_qualification(parser);
    } else {
        match atomic_type_form(parser) {
            Some(
                AtomicTypeForm::Int
                | AtomicTypeForm::Bytes
                | AtomicTypeForm::String
                | AtomicTypeForm::Bool
                | AtomicTypeForm::Unit,
            ) => {
                let _ = parser.bump();
                if parser.at(&TokenKind::Less) && !parser.at_syntax_stop() {
                    parser.error_at_current(ParseReason::UnexpectedToken);
                    type_arguments(parser);
                }
            }
            Some(AtomicTypeForm::Nominal) => {
                if !parser.nth_at_syntax_stop(1)
                    && parser
                        .nth(1)
                        .is_some_and(|kind| matches!(kind, TokenKind::Dot))
                {
                    qualified_name(parser, true);
                } else {
                    let _ = parser.bump();
                }
                if parser.at(&TokenKind::Less) && !parser.at_syntax_stop() {
                    type_arguments(parser);
                }
            }
            Some(AtomicTypeForm::Parenthesized) => parenthesized_type(parser),
            _ => parser.report(ParseReason::ExpectedForm, ExpectedForm::Type),
        }
    }
    parser.finish();
}

fn type_arguments(parser: &mut Parser<'_>) {
    // An enclosing matcher literal cannot stop inside a complete type argument list.
    let stops = std::mem::take(&mut parser.syntax_stops);
    let _ = parser.bump();
    application_argument(parser);
    while parser.at(&TokenKind::Comma) {
        let _ = parser.bump();
        application_argument(parser);
    }
    let _ = parser.expect(&TokenKind::Greater, ExpectedForm::Type);
    debug_assert!(parser.syntax_stops.is_empty());
    parser.syntax_stops = stops;
}

fn application_argument(parser: &mut Parser<'_>) {
    if parser.at(&TokenKind::LeftBrace) {
        if parser.enter_structure() {
            effect_row(parser);
            parser.leave_structure();
        } else {
            parser.consume_rest();
        }
    } else {
        type_expression(parser);
    }
}

fn atomic_type_form(parser: &Parser<'_>) -> Option<AtomicTypeForm> {
    if parser.is_admission_identifier() {
        return Some(AtomicTypeForm::Nominal);
    }
    selected_dialect()
        .atomic_types
        .iter()
        .copied()
        .find(|form| {
            matches!(
                (form, parser.current()),
                (AtomicTypeForm::Int, Some(TokenKind::IntType))
                    | (AtomicTypeForm::Bytes, Some(TokenKind::BytesType))
                    | (AtomicTypeForm::String, Some(TokenKind::StringType))
                    | (AtomicTypeForm::Bool, Some(TokenKind::BoolType))
                    | (AtomicTypeForm::Unit, Some(TokenKind::UnitType))
                    | (AtomicTypeForm::Nominal, Some(TokenKind::UpperIdentifier(_)))
                    | (AtomicTypeForm::Parenthesized, Some(TokenKind::LeftParen))
            )
        })
}

pub(super) fn qualified_name(parser: &mut Parser<'_>, uppercase_member: bool) {
    parser.start(NodeKind::QualifiedName);
    expect_upper_identifier(parser);
    let _ = parser.expect(&TokenKind::Dot, ExpectedForm::Identifier);
    if uppercase_member {
        expect_upper_identifier(parser);
    } else {
        expect_import_name(parser);
    }
    parser.finish();
}

pub(super) fn starts_lowercase_qualification(parser: &Parser<'_>) -> bool {
    !parser.is_admission_identifier()
        && matches!(parser.current(), Some(TokenKind::Identifier(_)))
        && parser
            .nth(1)
            .is_some_and(|kind| matches!(kind, TokenKind::Dot))
}

pub(super) fn reject_lowercase_qualification(parser: &mut Parser<'_>) {
    parser.start(NodeKind::Error);
    parser.error_at_current(ParseReason::UnexpectedToken);
    let _ = parser.bump();
    let _ = parser.bump();
    if matches!(
        parser.current(),
        Some(TokenKind::Identifier(_) | TokenKind::UpperIdentifier(_))
    ) {
        let _ = parser.bump();
    }
    parser.finish();
}

fn parenthesized_type(parser: &mut Parser<'_>) {
    parser.start(NodeKind::ParenthesizedType);
    let opening = parser.current_span();
    let _ = parser.bump();
    if parser.enter_structure() {
        let tuple_start = parser.event_position();
        type_expression(parser);
        if parser.at(&TokenKind::Comma) {
            let _ = parser.insert_start(tuple_start, NodeKind::TupleType);
            while parser.at(&TokenKind::Comma) {
                let _ = parser.bump();
                type_expression(parser);
            }
            parser.finish();
        }
        parser.leave_structure();
    } else {
        parser.consume_rest();
        parser.finish();
        return;
    }
    if parser.at(&TokenKind::RightParen) {
        let _ = parser.bump();
    } else {
        expression::report_unclosed_group(parser, opening);
    }
    parser.finish();
}

fn starts_expression(parser: &Parser<'_>) -> bool {
    !parser.at_syntax_stop()
        && (parser.at_syntax_name()
            || expression_prefix_form(parser).is_some()
            || expression::starts_primary(parser))
}

fn resource_field_word(parser: &mut Parser<'_>, word: &str) {
    if matches!(parser.current(), Some(TokenKind::Identifier(name)) if name == word) {
        let _ = parser.bump();
    } else {
        parser.report(ParseReason::ExpectedForm, ExpectedForm::Identifier);
    }
}

fn resource_handlers(parser: &mut Parser<'_>) {
    binder(parser);
    resource_handlers_body(parser);
}

fn resource_handlers_body(parser: &mut Parser<'_>) {
    let _ = parser.expect(&TokenKind::LeftBrace, ExpectedForm::LeftBrace);
    let _ = parser.expect(&TokenKind::LineEnd, ExpectedForm::LineEnd);
    if parser.at(&TokenKind::RightBrace) {
        parser.report(ParseReason::ExpectedForm, ExpectedForm::Identifier);
    }
    while !matches!(
        parser.current(),
        Some(TokenKind::RightBrace | TokenKind::EndOfFile)
    ) {
        parser.start(NodeKind::HandlerClause);
        binder(parser);
        pattern(parser);
        let _ = parser.expect(&TokenKind::FatArrow, ExpectedForm::FatArrow);
        expression(parser);
        parser.finish();
        if !parser.at(&TokenKind::LineEnd) {
            break;
        }
        let _ = parser.bump();
    }
    let _ = parser.expect(&TokenKind::RightBrace, ExpectedForm::RightBrace);
}

fn resource_family(parser: &mut Parser<'_>) -> bool {
    parser.start(NodeKind::ResourceFamily);
    resource_field_word(parser, "family");
    parser.start(NodeKind::TypeParameters);
    let _ = parser.expect(&TokenKind::Less, ExpectedForm::Type);
    let _ = type_parameter(parser, TypeParameterOwnerBoundary::Effect);
    let _ = parser.expect(&TokenKind::Greater, ExpectedForm::Greater);
    parser.finish();
    if parser.at(&TokenKind::Where) {
        where_clause(
            parser,
            HeaderRecoveryBoundary::OpeningBrace(
                SynchronizationBoundary::InterfaceBodyOpeningBrace,
            ),
        );
    } else {
        parser.report(
            ParseReason::ExpectedForm,
            ExpectedForm::InterfaceApplication,
        );
    }
    let _ = parser.expect(&TokenKind::LeftBrace, ExpectedForm::LeftBrace);
    let _ = parser.expect(&TokenKind::LineEnd, ExpectedForm::LineEnd);
    for word in ["provider", "effect", "interpret", "handlers"] {
        parser.start(NodeKind::ResourceField);
        if word == "effect" {
            let _ = parser.expect(&TokenKind::Effect, ExpectedForm::Identifier);
        } else {
            resource_field_word(parser, word);
        }
        match word {
            "provider" => {
                let _ = interface_application(parser);
            }
            "effect" | "interpret" => effect_instance(parser),
            "handlers" => resource_handlers(parser),
            _ => unreachable!(),
        }
        parser.finish();
        if word == "handlers" && parser.at(&TokenKind::RightBrace) {
            break;
        }
        if !parser.expect(&TokenKind::LineEnd, ExpectedForm::LineEnd) {
            break;
        }
    }
    let _ = parser.expect(&TokenKind::RightBrace, ExpectedForm::RightBrace);
    parser.finish();
    parser.expect(&TokenKind::LineEnd, ExpectedForm::LineEnd)
}

fn resource_definition(parser: &mut Parser<'_>) -> TypeParametersOutcome {
    parser.start(NodeKind::ResourceDefinition);
    if parser.at(&TokenKind::Pub) {
        let _ = parser.bump();
    }
    let _ = parser.expect(&TokenKind::Resource, ExpectedForm::Identifier);
    expect_upper_identifier(parser);
    if !parser.at(&TokenKind::Less) {
        parser.report(ParseReason::ExpectedForm, ExpectedForm::Type);
    } else {
        let _ = type_parameters(parser, TypeParameterOwnerBoundary::Effect);
    }
    let _ = parser.expect(&TokenKind::LeftBrace, ExpectedForm::LeftBrace);
    let _ = parser.expect(&TokenKind::LineEnd, ExpectedForm::LineEnd);

    for word in [
        "input",
        "state",
        "result",
        "provider",
        "effect",
        "interpret",
        "acquire",
        "finish",
        "handlers",
    ] {
        if word == "acquire"
            && matches!(parser.current(), Some(TokenKind::Identifier(name)) if name == "family")
            && !resource_family(parser)
        {
            break;
        }
        parser.start(NodeKind::ResourceField);
        if word == "effect" {
            let _ = parser.expect(&TokenKind::Effect, ExpectedForm::Identifier);
        } else {
            resource_field_word(parser, word);
        }
        match word {
            "input" | "state" => type_expression(parser),
            "result" => {
                type_expression(parser);
                resource_field_word(parser, "for");
                if parser.at(&TokenKind::Less) {
                    parser.start(NodeKind::TypeParameters);
                    let _ = parser.bump();
                    let _ = type_parameter(parser, TypeParameterOwnerBoundary::Effect);
                    let _ = parser.expect(&TokenKind::Greater, ExpectedForm::Greater);
                    parser.finish();
                } else {
                    parser.report(ParseReason::ExpectedForm, ExpectedForm::Type);
                }
            }
            "provider" => {
                let _ = interface_application(parser);
            }
            "effect" | "interpret" => effect_instance(parser),
            "acquire" | "finish" => {
                binder(parser);
                let _ = parser.expect(&TokenKind::FatArrow, ExpectedForm::FatArrow);
                expression(parser);
            }
            "handlers" => resource_handlers(parser),
            _ => unreachable!(),
        }
        parser.finish();
        if word == "handlers" && parser.at(&TokenKind::RightBrace) {
            break;
        }
        if !parser.expect(&TokenKind::LineEnd, ExpectedForm::LineEnd) {
            break;
        }
    }
    let _ = parser.expect(&TokenKind::RightBrace, ExpectedForm::RightBrace);
    parser.finish();
    TypeParametersOutcome::Complete
}

#[cfg(test)]
mod tests {
    use crate::{
        lexer::{lex, lex_with_budget},
        parser::{Event, ResourceFailure, parse_with_budget},
        source::{ByteRange, SourceFile},
        surface::{SurfaceExpr, SurfaceExprKind, SurfaceExpressionCapture, SurfaceName},
        syntax::{
            DiagnosticLocation, ExpansionFrame, MacroDelimiter, MacroOrigin, MacroOutputNode,
            SyntaxContexts,
        },
        syntax_resource::SyntaxBudget,
    };

    use super::*;

    #[test]
    fn fixed_generator_definition_graph_parses_with_owned_clauses() {
        let source = SourceFile::new(
            "generators/forms.ash",
            include_str!(concat!(
                env!("CARGO_MANIFEST_DIR"),
                "/docs/design/macros/fixtures/generators/forms.ash"
            )),
        )
        .unwrap();
        let tree = super::super::parse(lex(&source).unwrap());
        assert!(tree.lexical_diagnostics().is_empty());
        assert_eq!(tree.resource_failure(), None);
        assert!(
            tree.parse_diagnostics().is_empty(),
            "{:?}",
            tree.parse_diagnostics()
        );
    }

    #[test]
    fn extended_matcher_insertion_prepays_shift_and_full_event_growth() {
        struct Observation {
            events: Vec<Event>,
            diagnostics: Vec<super::super::ParseDiagnostic>,
            failure: Option<ResourceFailure>,
            consumed: usize,
            header_paid: usize,
            initial_len: usize,
            insertion_len: usize,
            capacity: usize,
        }

        fn run(source: &SourceFile, prefix_len: usize, limit: usize, full: bool) -> Observation {
            let mut budget = SyntaxBudget::with_limit(limit);
            budget.charge_units(17).unwrap();
            let lexed = lex_with_budget(source, &mut budget).unwrap();
            let (tokens, lexical, _, failure) = lexed.into_parts();
            assert!(failure.is_none() && lexical.is_empty());
            let (checkpoint, budget) = super::super::parse_module_header(tokens, lexical, budget);
            let super::super::ParserCheckpoint {
                tokens,
                position,
                events,
                diagnostics,
                pending_recoveries,
                recovered_expression_group_boundary,
                nesting_depth,
                resource_failure,
                syntax_work_exhausted,
                ..
            } = checkpoint;
            assert!(resource_failure.is_none() && diagnostics.is_empty());
            assert!(
                events
                    .iter()
                    .any(|event| matches!(event, Event::Start(NodeKind::ImportDeclaration)))
            );
            let header_paid = budget.consumed();
            let initial_len = events.len();
            let insertion_len = initial_len + 8 + prefix_len;
            let capacity = insertion_len + usize::from(!full);
            let mut controlled = Vec::with_capacity(capacity);
            controlled.extend(events);
            assert_eq!(controlled.capacity(), capacity);
            let mut parser = Parser {
                tokens: &tokens,
                position,
                events: controlled,
                diagnostics,
                pending_recoveries,
                recovered_expression_group_boundary,
                nesting_depth,
                resource_failure,
                syntax_budget: budget,
                syntax_work_exhausted,
                in_template: false,
                quote_mode: super::super::QuoteMode::Ordinary,
                saw_quote_or_escape: false,
                syntax: &[],
                syntax_source: Some(source),
                syntax_selections: None,
                syntax_spellings: None,
                diagnostic_spans: None,
                admission_identifiers: None,
                declaration_output_nodes: None,
                syntax_stops: Vec::new(),
            };
            syntax_declaration(&mut parser);
            let capacity = parser.events.capacity();
            Observation {
                events: parser.events,
                diagnostics: parser.diagnostics,
                failure: parser.resource_failure,
                consumed: parser.syntax_budget.consumed(),
                header_paid,
                initial_len,
                insertion_len,
                capacity,
            }
        }

        for prefix_len in [0, 64] {
            let prefix = (0..prefix_len)
                .map(|index| format!("word{index} "))
                .collect::<String>();
            let source = SourceFile::new(
                "event-insertion.ash",
                format!("import dependency as D\npub syntax declaration: (sink) {prefix}( $value:ident ) => {{}}\n"),
            ).unwrap();
            let baseline = run(&source, prefix_len, super::super::SYNTAX_WORK_LIMIT, true);
            assert_eq!(baseline.failure, None);
            assert!(baseline.diagnostics.is_empty());
            let matcher_start = baseline.initial_len + 8;
            assert_eq!(baseline.insertion_len, matcher_start + prefix_len);
            assert_eq!(
                baseline.events[matcher_start],
                Event::Start(NodeKind::SyntaxMatcherSequence)
            );
            let mut prefix_events = baseline.events[..matcher_start].to_vec();
            prefix_events.extend_from_slice(
                &baseline.events[matcher_start + 1..matcher_start + 1 + prefix_len],
            );
            assert_eq!(prefix_events.len(), baseline.insertion_len);
            let before = baseline.header_paid + 8 + prefix_len;
            for full in [true, false] {
                let extra = prefix_len + if full { baseline.insertion_len } else { 0 } + 3;
                let short = run(&source, prefix_len, before + extra - 1, full);
                assert_eq!(
                    short.failure,
                    Some(ResourceFailure::SyntaxWork {
                        limit: before + extra - 1
                    })
                );
                assert_eq!(short.consumed, before);
                assert_eq!(short.capacity, short.insertion_len + usize::from(!full));
                assert_eq!(short.events, prefix_events);
                let exact = run(&source, prefix_len, before + extra, full);
                assert_eq!(
                    exact.failure,
                    Some(ResourceFailure::SyntaxWork {
                        limit: before + extra
                    })
                );
                assert_eq!(exact.consumed, before + extra);
                assert_eq!(exact.capacity, exact.insertion_len + usize::from(!full));
                assert_eq!(exact.events, prefix_events);
                let with_start = run(&source, prefix_len, before + extra + 1, full);
                assert_eq!(
                    with_start.failure,
                    Some(ResourceFailure::SyntaxWork {
                        limit: before + extra + 1
                    })
                );
                assert_eq!(with_start.consumed, before + extra + 1);
                let mut expected = prefix_events.clone();
                expected.insert(matcher_start, Event::Start(NodeKind::SyntaxMatcherSequence));
                assert_eq!(with_start.events, expected);
            }
        }
    }

    #[test]
    fn forged_equal_token_kinds_still_compare_distinct_source_spelling() {
        // This component input deliberately changes a lexer token: the current
        // source lexer has no known valid decoded-equal spelling aliases.
        let source = SourceFile::new(
            "forged-matcher.ash",
            "pub syntax declaration: (sink) $( item ) \"a\"* \"b\" => {}\n",
        )
        .unwrap();
        let mut lexed = lex(&source).unwrap();
        let indices = lexed
            .tokens
            .iter()
            .enumerate()
            .filter_map(|(index, token)| {
                matches!(token.kind, TokenKind::StringLiteral(_)).then_some(index)
            })
            .collect::<Vec<_>>();
        let [first, second] = indices.as_slice() else {
            panic!("expected two string tokens");
        };
        assert_ne!(lexed.tokens[*first].kind, lexed.tokens[*second].kind);
        lexed.tokens[*second].kind = lexed.tokens[*first].kind.clone();
        let (tokens, lexical, budget, failure) = lexed.into_parts();
        assert!(failure.is_none());
        let (checkpoint, budget) = super::super::parse_module_header(tokens, lexical, budget);
        let (tree, _) = super::super::finish_module_from_checkpoint_with_syntax(
            checkpoint,
            budget,
            Some(&source),
            &[],
        );
        assert!(
            tree.parse_diagnostics().is_empty(),
            "{:?}",
            tree.parse_diagnostics()
        );
        assert_eq!(tree.resource_failure(), None);
        eprintln!("component only: equal forged token kinds, distinct source spelling");
    }

    mod mock_nested_feature {
        #[derive(Clone, Copy)]
        pub struct MockNested;

        pub const fn parse(_node: MockNested) -> &'static str {
            "mock nested parser"
        }
    }

    #[derive(Clone, Copy)]
    enum ShadowPrefixForm {
        Existing(ExpressionPrefixForm),
        Mock(mock_nested_feature::MockNested),
    }

    const SHADOW_PREFIX_ASSEMBLY: &[ShadowPrefixForm] = &[
        ShadowPrefixForm::Existing(ExpressionPrefixForm::Block),
        ShadowPrefixForm::Existing(ExpressionPrefixForm::Function),
        ShadowPrefixForm::Mock(mock_nested_feature::MockNested),
    ];

    const fn dispatch_shadow_prefix(form: ShadowPrefixForm) -> &'static str {
        match form {
            ShadowPrefixForm::Existing(ExpressionPrefixForm::Block) => "block parser",
            ShadowPrefixForm::Existing(ExpressionPrefixForm::Function) => "function parser",
            ShadowPrefixForm::Existing(ExpressionPrefixForm::Match) => "match parser",
            ShadowPrefixForm::Existing(ExpressionPrefixForm::Handler) => "handler parser",
            ShadowPrefixForm::Existing(ExpressionPrefixForm::Resume) => "resume parser",
            ShadowPrefixForm::Existing(ExpressionPrefixForm::Resource) => "resource parser",
            ShadowPrefixForm::Existing(ExpressionPrefixForm::Region) => "region parser",
            ShadowPrefixForm::Existing(ExpressionPrefixForm::RegionSelection) => {
                "region selection parser"
            }

            ShadowPrefixForm::Mock(node) => mock_nested_feature::parse(node),
        }
    }

    #[test]
    fn a_mock_nested_form_changes_its_parser_and_closed_prefix_assembly_not_infix() {
        assert_eq!(SHADOW_PREFIX_ASSEMBLY.len(), 3);
        assert_eq!(
            dispatch_shadow_prefix(SHADOW_PREFIX_ASSEMBLY[2]),
            "mock nested parser"
        );
        assert_eq!(
            selected_dialect().expression.infix,
            &[
                InfixDescriptor {
                    token: OperatorToken::EqualEqual,
                    precedence: 10,
                    associativity: Associativity::NonAssociative,
                    result: NodeKind::EqualityExpression,
                },
                InfixDescriptor {
                    token: OperatorToken::Plus,
                    precedence: 20,
                    associativity: Associativity::Left,
                    result: NodeKind::AdditiveExpression,
                },
                InfixDescriptor {
                    token: OperatorToken::Star,
                    precedence: 30,
                    associativity: Associativity::Left,
                    result: NodeKind::MultiplicativeExpression,
                },
            ]
        );
    }

    #[test]
    fn a_block_without_its_result_reports_an_expected_expression() {
        let source = SourceFile::new("missing-block-result.ash", "main : Unit\nmain () = {\n}\n")
            .expect("the parser fixture should fit");
        let tree = super::super::parse(lex(&source).expect("the parser fixture should lex"));

        let diagnostic = tree
            .parse_diagnostics()
            .iter()
            .find(|diagnostic| diagnostic.expected.as_deref() == Some("an expression"))
            .expect("the missing block result should require an expression");
        assert_eq!(diagnostic.reason, ParseReason::ExpectedForm);
    }

    #[test]
    fn newtype_declaration_consumes_exact_cumulative_syntax_work_and_retries_cleanly() {
        let source = SourceFile::new("newtype-resource.ash", "newtype Exact = Exact(Int)\n")
            .expect("the parser fixture should fit");
        let baseline = super::super::parse(lex(&source).expect("the parser fixture should lex"));
        // One syntax unit per retained token and parser event.
        const TOKEN_WORK: usize = 9;
        const EVENT_WORK: usize = 19;
        const EXACT_WORK: usize = TOKEN_WORK + EVENT_WORK;
        assert_eq!(
            (baseline.tokens().len(), baseline.events().len()),
            (TOKEN_WORK, EVENT_WORK),
        );
        let exact_work = EXACT_WORK;

        assert!(
            baseline.parse_diagnostics().is_empty(),
            "{:?}",
            baseline.parse_diagnostics()
        );
        assert!(exact_work > baseline.tokens().len());

        let exact = parse_newtype_with_limit(&source, exact_work);
        assert_eq!(exact.resource_failure(), None);
        assert!(
            exact
                .events()
                .iter()
                .any(|event| matches!(event, Event::Start(NodeKind::NewtypeDeclaration)))
        );

        let one_short_limit = exact_work - 1;
        let one_short = parse_newtype_with_limit(&source, one_short_limit);
        assert_eq!(
            one_short.resource_failure(),
            Some(ResourceFailure::SyntaxWork {
                limit: one_short_limit
            })
        );
        assert!(one_short.root().is_none());

        let retry = parse_newtype_with_limit(&source, exact_work);
        assert_eq!(retry.resource_failure(), None);
        assert_eq!(retry.tokens().len(), baseline.tokens().len());
        assert_eq!(retry.events().len(), baseline.events().len());
    }

    #[test]
    fn r1_source_header_and_clause_share_the_exact_syntax_allowance() {
        for (text, scout_work) in [
            (
                "pub syntax derive: (marker) $target:ident => {\ntype Item = Item\n}\n",
                17,
            ),
            ("type Item = Item\nderiving (first, second, first,)\n", 0),
            ("newtype Item = Item(Int)\nderiving (first,)\n", 0),
        ] {
            let source = SourceFile::new("derive-work.ash", text).unwrap();
            let baseline = super::super::parse(lex(&source).unwrap());
            assert!(baseline.parse_diagnostics().is_empty(), "{text:?}");
            let exact_work = baseline.tokens().len() + baseline.events().len() + scout_work;
            let parse_at = |limit| {
                let mut budget = SyntaxBudget::with_limit(limit);
                let lexed = lex_with_budget(&source, &mut budget).unwrap();
                let tree = parse_with_budget(lexed, &mut budget);
                (tree, budget.consumed())
            };
            let (short, short_used) = parse_at(exact_work - 1);
            assert_eq!(
                short.resource_failure(),
                Some(ResourceFailure::SyntaxWork {
                    limit: exact_work - 1
                }),
                "{text:?}"
            );
            assert!(short.root().is_none());
            assert!(short_used < exact_work);
            for _ in 0..2 {
                let (exact, exact_used) = parse_at(exact_work);
                assert_eq!(exact.resource_failure(), None);
                assert_eq!(exact.tokens(), baseline.tokens());
                assert_eq!(exact.events(), baseline.events());
                assert_eq!(exact_used, exact_work);
            }
        }
    }

    #[test]
    fn r1_derive_nested_quote_uses_the_prespent_source_budget_and_retries() {
        let source = SourceFile::new(
            "derive-quote-resource.ash",
            "pub syntax derive: (marker) $target:ident => {\n\
             $target () = syntax { ${ syntax { $local } } + $target }\n\
             sibling () = syntax { ${ $target } + $target }\n\
             }\n",
        )
        .unwrap();
        let parse_at = |limit| {
            let mut budget = SyntaxBudget::with_limit(limit);
            budget.charge_units(17).unwrap();
            let lexed = lex_with_budget(&source, &mut budget).unwrap();
            let tree = parse_with_budget(lexed, &mut budget);
            (tree, budget.consumed())
        };
        let (baseline, used) = parse_at(100_000);
        assert_eq!(baseline.resource_failure(), None);
        assert!(baseline.parse_diagnostics().is_empty());
        assert!(used > 17 + baseline.tokens().len() + baseline.events().len());
        assert!(
            baseline
                .events()
                .iter()
                .any(|event| matches!(event, Event::Start(NodeKind::SyntaxEscape)))
        );
        let (short, _) = parse_at(used - 1);
        assert_eq!(
            short.resource_failure(),
            Some(ResourceFailure::SyntaxWork { limit: used - 1 })
        );
        assert!(short.root().is_none());
        for _ in 0..2 {
            let (exact, consumed) = parse_at(used);
            assert_eq!(consumed, used);
            assert_eq!(exact, baseline);
        }
    }

    #[test]
    fn local_newtype_declaration_consumes_exact_cumulative_syntax_work_and_retries_cleanly() {
        let source = SourceFile::new(
            "local-newtype-resource.ash",
            "main : Unit -> Int\nmain () = {\nnewtype Exact = Exact(Int)\nlet answer = 1\nanswer\n}\n",
        )
        .expect("the parser fixture should fit");
        let baseline = super::super::parse(lex(&source).expect("the parser fixture should lex"));
        let exact_work = baseline.tokens().len() + baseline.events().len();

        assert!(
            baseline.parse_diagnostics().is_empty(),
            "{:?}",
            baseline.parse_diagnostics()
        );
        let exact = parse_newtype_with_limit(&source, exact_work);
        assert_eq!(exact.resource_failure(), None);
        assert!(
            exact
                .events()
                .iter()
                .any(|event| matches!(event, Event::Start(NodeKind::NewtypeDeclaration)))
        );

        let one_short_limit = exact_work - 1;
        let one_short = parse_newtype_with_limit(&source, one_short_limit);
        assert_eq!(
            one_short.resource_failure(),
            Some(ResourceFailure::SyntaxWork {
                limit: one_short_limit
            })
        );
        assert!(one_short.root().is_none());

        let retry = parse_newtype_with_limit(&source, exact_work);
        assert_eq!(retry.resource_failure(), None);
        assert_eq!(retry.tokens().len(), baseline.tokens().len());
        assert_eq!(retry.events().len(), baseline.events().len());
    }

    fn parse_newtype_with_limit(source: &SourceFile, limit: usize) -> super::super::ConcreteTree {
        let mut budget = SyntaxBudget::with_limit(limit);
        let lexed = lex_with_budget(source, &mut budget).expect("limited lexing should fit spans");
        parse_with_budget(lexed, &mut budget)
    }

    #[test]
    fn quote_tree_work_is_charged_before_return_and_retries_at_the_exact_limit() {
        let source = SourceFile::new(
            "quote-resource.ash",
            "main : Unit -> Int\nmain () = syntax { 0 + 1 }\n",
        )
        .unwrap();
        let parse_at = |limit| {
            let mut budget = SyntaxBudget::with_limit(limit);
            let lexed = lex_with_budget(&source, &mut budget).unwrap();
            let tree = parse_with_budget(lexed, &mut budget);
            (tree, budget.consumed())
        };
        let (baseline, used) = parse_at(10_000);
        assert_eq!(baseline.resource_failure(), None);
        assert!(baseline.parse_diagnostics().is_empty());
        // The completed-tree walk reserves a conservative child-scan bound.
        assert!(used > baseline.tokens().len() + baseline.events().len());

        let (short, _) = parse_at(used - 1);
        assert_eq!(
            short.resource_failure(),
            Some(ResourceFailure::SyntaxWork { limit: used - 1 })
        );
        assert!(short.root().is_none());
        for _ in 0..2 {
            let (exact, consumed) = parse_at(used);
            assert_eq!(exact, baseline);
            assert_eq!(consumed, used);
        }
    }

    #[test]
    fn quote_free_template_keeps_its_flat_shape_and_work_cost() {
        let source = SourceFile::new(
            "ordinary-template.ash",
            "pub syntax repeat $value:expr => {\n$( $value ),*\n}\n",
        )
        .unwrap();
        let mut budget = SyntaxBudget::with_limit(10_000);
        let lexed = lex_with_budget(&source, &mut budget).unwrap();
        let tree = parse_with_budget(lexed, &mut budget);
        assert_eq!(tree.resource_failure(), None);
        assert!(tree.parse_diagnostics().is_empty());
        // The file-level Pub/Syntax header scout pays two visits.
        let exact_work = tree.tokens().len() + tree.events().len() + 2;
        assert_eq!(budget.consumed(), exact_work);
        assert!(!tree.events().iter().any(|event| matches!(
            event,
            Event::Start(
                NodeKind::SyntaxQuote
                    | NodeKind::SyntaxEscape
                    | NodeKind::TemplateSplice
                    | NodeKind::EscapeCaptureRead
                    | NodeKind::QuoteHole
            )
        )));
        let parse_at = |limit| {
            let mut budget = SyntaxBudget::with_limit(limit);
            let lexed = lex_with_budget(&source, &mut budget).unwrap();
            let parsed = parse_with_budget(lexed, &mut budget);
            (parsed, budget.consumed())
        };
        let (short, short_used) = parse_at(exact_work - 1);
        assert_eq!(
            short.resource_failure(),
            Some(ResourceFailure::SyntaxWork {
                limit: exact_work - 1
            })
        );
        assert!(short.root().is_none());
        assert!(short_used < exact_work);
        for _ in 0..2 {
            let (exact, consumed) = parse_at(exact_work);
            assert_eq!(exact.resource_failure(), None);
            assert_eq!(exact.tokens(), tree.tokens());
            assert_eq!(exact.events(), tree.events());
            assert_eq!(consumed, exact_work);
        }
    }

    #[test]
    fn quote_tree_check_reserves_its_walk_and_fails_before_a_pending_push() {
        let source = SourceFile::new(
            "quote-walk.ash",
            "main : Unit -> Int\nmain () = syntax { 0 + 1 }\n",
        )
        .unwrap();
        let tree = super::super::parse(lex(&source).unwrap());
        let mut nodes = vec![tree.root().unwrap()];
        let mut expected = 1; // Initial worklist entry.
        while let Some(node) = nodes.pop() {
            let children = node.children.iter().filter_map(|child| match child {
                super::super::ConcreteElement::Node(child) => Some(child),
                _ => None,
            });
            expected += 1 + node.children.len() + children.clone().count();
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
                expected += node.children.len();
            }
            nodes.extend(children);
        }
        let mut exact = SyntaxBudget::with_limit(expected);
        assert_eq!(
            super::super::check_completed_quote_depth(&tree, &mut exact),
            Ok(())
        );
        assert_eq!(exact.consumed(), expected);
        let mut short = SyntaxBudget::with_limit(expected - 1);
        assert_eq!(
            super::super::check_completed_quote_depth(&tree, &mut short),
            Err(ResourceFailure::SyntaxWork {
                limit: expected - 1
            })
        );

        let tiny = super::super::cst::build(
            Vec::new(),
            Vec::new(),
            Vec::new(),
            vec![
                Event::Start(NodeKind::SyntaxQuote),
                Event::Start(NodeKind::QuoteHole),
                Event::Finish,
                Event::Finish,
            ],
            None,
        );
        let mut before_push = SyntaxBudget::with_limit(3);
        assert_eq!(
            super::super::check_completed_quote_depth(&tiny, &mut before_push),
            Err(ResourceFailure::SyntaxWork { limit: 3 })
        );
        assert_eq!(before_push.consumed(), 3);
        let mut enough = SyntaxBudget::with_limit(5);
        assert_eq!(
            super::super::check_completed_quote_depth(&tiny, &mut enough),
            Ok(())
        );
        assert_eq!(enough.consumed(), 5);
    }

    #[test]
    fn inline_escape_shape_weight_is_reserved_before_inspection() {
        use super::super::{ConcreteElement, ConcreteNode, ConcreteTree};

        let block = || ConcreteNode {
            kind: NodeKind::Block,
            children: Vec::new(),
        };
        let multiline = ConcreteNode {
            kind: NodeKind::SyntaxEscape,
            children: vec![ConcreteElement::Token(0), ConcreteElement::Node(block())],
        };
        assert_eq!(super::super::source_structural_weight(&multiline), 0);
        let inline = ConcreteNode {
            kind: NodeKind::SyntaxEscape,
            children: vec![
                ConcreteElement::Token(0),
                ConcreteElement::Token(1),
                ConcreteElement::Node(block()),
                ConcreteElement::Token(2),
            ],
        };
        assert_eq!(super::super::source_structural_weight(&inline), 1);
        assert_eq!(super::super::source_structural_weight(&block()), 1);
        let unknown = ConcreteNode {
            kind: NodeKind::SyntaxEscape,
            children: Vec::new(),
        };
        assert_eq!(super::super::source_structural_weight(&unknown), 1);

        let tree = ConcreteTree {
            root: Some(inline),
            tokens: Vec::new(),
            events: Vec::new(),
            lexical_diagnostics: Vec::new(),
            parse_diagnostics: Vec::new(),
            malformed: None,
            resource_failure: None,
        };
        let mut before_inspection = SyntaxBudget::with_limit(3);
        assert_eq!(
            super::super::check_completed_quote_depth(&tree, &mut before_inspection),
            Err(ResourceFailure::SyntaxWork { limit: 3 })
        );
        assert_eq!(before_inspection.consumed(), 2);
        let mut exact = SyntaxBudget::with_limit(10);
        assert_eq!(
            super::super::check_completed_quote_depth(&tree, &mut exact),
            Ok(())
        );
        assert_eq!(exact.consumed(), 10);
    }

    #[test]
    fn inline_escape_source_uses_one_shared_budget_and_retries() {
        let source = SourceFile::new(
            "inline-resource.ash",
            "main : Unit -> Int\nmain () = syntax { ${ 0 + 1 } }\n",
        )
        .unwrap();
        let parse_at = |limit| {
            let mut budget = SyntaxBudget::with_limit(limit);
            let lexed = lex_with_budget(&source, &mut budget).unwrap();
            let tree = parse_with_budget(lexed, &mut budget);
            (tree, budget.consumed())
        };
        let (baseline, used) = parse_at(10_000);
        assert_eq!(baseline.resource_failure(), None);
        assert!(
            baseline.parse_diagnostics().is_empty(),
            "{:?}",
            baseline.parse_diagnostics()
        );
        assert!(
            baseline
                .events()
                .iter()
                .any(|event| { matches!(event, Event::Start(NodeKind::SyntaxEscape)) })
        );
        let (short, _) = parse_at(used - 1);
        assert_eq!(
            short.resource_failure(),
            Some(ResourceFailure::SyntaxWork { limit: used - 1 })
        );
        assert!(short.root().is_none());
        let (retry, consumed) = parse_at(used);
        assert_eq!(consumed, used);
        assert_eq!(retry, baseline);
    }

    fn structured_quote_fixture(source: &SourceFile) -> Vec<MacroOutputNode> {
        let lexed = lex(source).unwrap();
        let mut groups = vec![(None, Vec::new())];
        for token in &lexed.tokens {
            match &token.kind {
                TokenKind::LeftParen | TokenKind::LeftBrace => {
                    let delimiter = if token.kind == TokenKind::LeftParen {
                        MacroDelimiter::Parentheses
                    } else {
                        MacroDelimiter::Braces
                    };
                    groups.push((Some((delimiter, token.span)), Vec::new()));
                }
                TokenKind::RightParen | TokenKind::RightBrace => {
                    let (opening, children) = groups.pop().unwrap();
                    let (delimiter, start) = opening.unwrap();
                    let origin = start.cover(token.span).unwrap().into();
                    groups
                        .last_mut()
                        .unwrap()
                        .1
                        .push(MacroOutputNode::Group(delimiter, children, origin));
                }
                TokenKind::EndOfFile => {}
                TokenKind::Identifier(text) | TokenKind::UpperIdentifier(text) => {
                    let name = SurfaceName {
                        text: text.clone(),
                        span: token.span,
                        introduction: 0,
                        introduced_at: None,
                        written: true,
                        diagnostic: None,
                    };
                    groups
                        .last_mut()
                        .unwrap()
                        .1
                        .push(MacroOutputNode::Identifier(name, token.span.into()));
                }
                _ => {
                    let range = token.span.range();
                    let spelling = &source.text()[range.start() as usize..range.end() as usize];
                    groups.last_mut().unwrap().1.push(MacroOutputNode::Token(
                        token.kind.clone(),
                        spelling.into(),
                        token.span.into(),
                    ));
                }
            }
        }
        assert_eq!(groups.len(), 1);
        groups.pop().unwrap().1
    }

    #[test]
    fn structured_quote_tree_uses_the_staging_budget_and_composed_depth() {
        let text = |outer: usize| {
            format!(
                "probe : Unit -> Int\nprobe () = (syntax {{ $part{} }}){}\n",
                " + 1".repeat(60),
                " + 1".repeat(outer)
            )
        };
        for (outer, expected_depth_failure) in [(66, false), (67, true)] {
            let source = SourceFile::new("structured-quote.ash", text(outer)).unwrap();
            let end = u32::try_from(source.text().len()).unwrap();
            let invocation = source.span(ByteRange::new(0, end).unwrap()).unwrap();
            let mut output = structured_quote_fixture(&source);
            let quote_start = u32::try_from(source.text().find("syntax").unwrap()).unwrap();
            let definition = source
                .span(ByteRange::new(quote_start, quote_start + 6).unwrap())
                .unwrap();
            let frame = std::sync::Arc::new(ExpansionFrame {
                invocation,
                definition,
            });
            let mut expected = None;
            let mut pending = vec![output.as_mut_slice()];
            while let Some(nodes) = pending.pop() {
                for node in nodes {
                    match node {
                        MacroOutputNode::Group(_, children, _) => pending.push(children),
                        MacroOutputNode::Identifier(name, origin) if name.text == "part" => {
                            let combined = MacroOrigin::combined(
                                vec![name.span.into(), definition.into()],
                                std::sync::Arc::clone(&frame),
                            )
                            .unwrap();
                            let mut diagnostic = DiagnosticLocation::new(combined.clone());
                            diagnostic.add_frame(&frame);
                            name.introduction = 1;
                            name.introduced_at = Some(invocation);
                            name.written = false;
                            name.diagnostic = Some(Box::new(diagnostic));
                            *origin = combined.clone();
                            expected = Some((name.clone(), combined));
                        }
                        _ => {}
                    }
                }
            }
            let (expected_name, expected_origin) = expected.expect("one quote hole is present");
            let contexts = SyntaxContexts::new(&[], &[vec![]], &[Some(0)]);
            let parse_at = |limit| {
                let mut budget = SyntaxBudget::with_limit(limit);
                let parsed = super::super::parse_macro_tree_inner(
                    &source,
                    invocation,
                    output.clone(),
                    &contexts,
                    &[],
                    super::super::MacroOutputPosition::StagedDeclarations,
                    &mut budget,
                );
                (parsed, budget.consumed())
            };
            let (parsed, used) = parse_at(100_000);
            if expected_depth_failure {
                assert!(matches!(
                    parsed,
                    Err(super::super::MacroParseFailure::Syntax {
                        resource: Some(ResourceFailure::StructuralDepth { .. }),
                        ..
                    })
                ));
                continue;
            }
            let parsed = parsed.expect("the structured quote at the boundary parses");
            assert!(
                parsed
                    .tree
                    .events()
                    .iter()
                    .any(|event| { matches!(event, Event::Start(NodeKind::SyntaxQuote)) })
            );
            let assert_hole = |tree: &super::super::ParsedMacroTree| {
                let (name, origin) = tree
                    .original_nodes
                    .values()
                    .find_map(|node| match node {
                        MacroOutputNode::Identifier(name, origin) if name.text == "part" => {
                            Some((name, origin))
                        }
                        _ => None,
                    })
                    .expect("the quote hole identifier must retain its original node");
                assert_eq!(name, &expected_name);
                assert_eq!(name.diagnostic, expected_name.diagnostic);
                assert_eq!(origin, &expected_origin);
                assert_eq!(origin.primary(), name.span);
            };
            assert_hole(&parsed);
            assert!(matches!(
                parse_at(used - 1).0,
                Err(super::super::MacroParseFailure::Syntax {
                    resource: Some(ResourceFailure::SyntaxWork { .. }),
                    ..
                })
            ));
            let (retry, consumed) = parse_at(used);
            let retry = retry.expect("the same exact budget succeeds after a short attempt");
            assert_eq!(consumed, used);
            assert_eq!(retry.tree, parsed.tree);
            assert_eq!(retry.original_nodes, parsed.original_nodes);
            assert_eq!(retry.admission_identifiers, parsed.admission_identifiers);
            assert_hole(&retry);
        }
    }

    #[test]
    fn inline_escape_structured_nested_block_uses_shared_budget_and_depth() {
        for (inner, over) in [(123, false), (124, true)] {
            let text = format!(
                "probe : Unit -> Int\nprobe () = (syntax {{ ${{ {{\n1{}\n}} }} }}) + 1\n",
                " + 1".repeat(inner)
            );
            let source = SourceFile::new("structured-inline-block.ash", text).unwrap();
            let end = u32::try_from(source.text().len()).unwrap();
            let invocation = source.span(ByteRange::new(0, end).unwrap()).unwrap();
            let output = structured_quote_fixture(&source);
            let contexts = SyntaxContexts::new(&[], &[], &[]);
            let parse_at = |limit| {
                let mut budget = SyntaxBudget::with_limit(limit);
                let result = super::super::parse_macro_tree_inner(
                    &source,
                    invocation,
                    output.clone(),
                    &contexts,
                    &[],
                    super::super::MacroOutputPosition::StagedDeclarations,
                    &mut budget,
                );
                (result, budget.consumed())
            };
            let (parsed, used) = parse_at(100_000);
            if over {
                assert!(matches!(
                    parsed,
                    Err(super::super::MacroParseFailure::Syntax {
                        resource: Some(ResourceFailure::StructuralDepth {
                            limit: super::super::STRUCTURAL_DEPTH_LIMIT
                        }),
                        ..
                    })
                ));
                continue;
            }
            let parsed = parsed.expect("the structured inline tree at depth 128 must parse");
            let mut pending = vec![parsed.tree.root().unwrap()];
            let mut quotes = 0;
            let mut escapes = 0;
            let mut blocks = 0;
            let mut additions = 0;
            while let Some(node) = pending.pop() {
                quotes += usize::from(node.kind == NodeKind::SyntaxQuote);
                escapes += usize::from(node.kind == NodeKind::SyntaxEscape);
                blocks += usize::from(node.kind == NodeKind::Block);
                additions += usize::from(node.kind == NodeKind::AdditiveExpression);
                pending.extend(node.children.iter().filter_map(|child| match child {
                    super::super::ConcreteElement::Node(child) => Some(child),
                    _ => None,
                }));
            }
            assert_eq!((quotes, escapes, blocks, additions), (1, 1, 1, 124));
            assert!(
                parsed
                    .original_nodes
                    .values()
                    .any(|node| matches!(node, MacroOutputNode::Token(TokenKind::Dollar, _, _)))
            );
            assert!(matches!(
                parse_at(used - 1).0,
                Err(super::super::MacroParseFailure::Syntax {
                    resource: Some(ResourceFailure::SyntaxWork { .. }),
                    ..
                })
            ));
            let (retry, consumed) = parse_at(used);
            let retry = retry.expect("the same exact budget must retry successfully");
            assert_eq!(consumed, used);
            assert_eq!(retry.tree, parsed.tree);
            assert_eq!(retry.original_nodes, parsed.original_nodes);
        }
    }

    #[test]
    fn quote_declaration_admission_uses_the_existing_budget_and_resource_channel() {
        let text = |outer: usize| {
            format!(
                "probe : Unit -> Int\nprobe () = (syntax {{ $part{} }}){}\n",
                " + 1".repeat(60),
                " + 1".repeat(outer)
            )
        };
        let source = SourceFile::new("quote-admission.ash", text(66)).unwrap();
        let end = u32::try_from(source.text().len()).unwrap();
        let invocation = source.span(ByteRange::new(0, end).unwrap()).unwrap();
        let output = structured_quote_fixture(&source);
        let contexts = SyntaxContexts::new(&[], &[], &[]);
        let admit = |limit| {
            let mut budget = SyntaxBudget::with_limit(limit);
            budget.charge_units(7).unwrap();
            let result = super::super::parse_declaration_template_admission(
                &source,
                invocation,
                output.clone(),
                &contexts,
                &[],
                &mut budget,
            );
            (result, budget.consumed())
        };

        let mut parse_budget = SyntaxBudget::with_limit(100_000);
        parse_budget.charge_units(7).unwrap();
        let parsed = super::super::parse_macro_tree_inner(
            &source,
            invocation,
            output.clone(),
            &contexts,
            &[],
            super::super::MacroOutputPosition::StagedDeclarations,
            &mut parse_budget,
        )
        .expect("the boundary quote parses before composed admission checks its owner");
        assert!(
            parsed
                .tree
                .events()
                .iter()
                .any(|event| matches!(event, Event::Start(NodeKind::SyntaxQuote)))
        );
        let (result, used) = admit(100_000);
        assert!(matches!(
            result,
            Err(super::super::MacroParseFailure::Syntax {
                resource: Some(ResourceFailure::StructuralDepth {
                    limit: super::super::STRUCTURAL_DEPTH_LIMIT
                }),
                ..
            })
        ));
        assert!(used > parse_budget.consumed());
        assert!(matches!(
            admit(used - 1).0,
            Err(super::super::MacroParseFailure::Syntax {
                resource: Some(ResourceFailure::SyntaxWork { .. }),
                ..
            })
        ));
        for _ in 0..2 {
            let (result, consumed) = admit(used);
            assert!(matches!(
                result,
                Err(super::super::MacroParseFailure::Syntax {
                    resource: Some(ResourceFailure::StructuralDepth {
                        limit: super::super::STRUCTURAL_DEPTH_LIMIT
                    }),
                    ..
                })
            ));
            assert_eq!(consumed, used);
        }

        let over = SourceFile::new("quote-admission-over.ash", text(67)).unwrap();
        let end = u32::try_from(over.text().len()).unwrap();
        let span = over.span(ByteRange::new(0, end).unwrap()).unwrap();
        let mut budget = SyntaxBudget::with_limit(100_000);
        assert!(matches!(
            super::super::parse_declaration_template_admission(
                &over,
                span,
                structured_quote_fixture(&over),
                &contexts,
                &[],
                &mut budget,
            ),
            Err(super::super::MacroParseFailure::Syntax {
                resource: Some(ResourceFailure::StructuralDepth {
                    limit: super::super::STRUCTURAL_DEPTH_LIMIT
                }),
                ..
            })
        ));
    }

    #[test]
    fn quote_tree_keeps_a_protected_expression_on_the_existing_declaration_path() {
        let source = SourceFile::new(
            "protected-quote.ash",
            "probe : Unit -> Int\nprobe () = syntax { 1 }\n",
        )
        .unwrap();
        let end = u32::try_from(source.text().len()).unwrap();
        let invocation = source.span(ByteRange::new(0, end).unwrap()).unwrap();
        let mut output = structured_quote_fixture(&source);
        let mut expected = None;
        let mut pending = vec![output.as_mut_slice()];
        while let Some(nodes) = pending.pop() {
            for node in nodes {
                match node {
                    MacroOutputNode::Group(_, children, _) => pending.push(children),
                    MacroOutputNode::Token(TokenKind::Integer(value), spelling, origin) => {
                        let token = MacroOutputNode::Token(
                            TokenKind::Integer(value.clone()),
                            std::sync::Arc::clone(spelling),
                            origin.clone(),
                        );
                        let protected = MacroOutputNode::ForwardedExpression(
                            SurfaceExpressionCapture {
                                contains_protected_type: false,
                                quote_sites: Default::default(),
                                expression: SurfaceExpr {
                                    kind: SurfaceExprKind::Integer(value.clone()),
                                    span: origin.primary(),
                                    diagnostic: Some(Box::new(DiagnosticLocation::new(
                                        origin.clone(),
                                    ))),
                                },
                                contents: std::sync::Arc::from([token]),
                            },
                            origin.clone(),
                        );
                        *node = protected.clone();
                        expected = Some(protected);
                    }
                    _ => {}
                }
            }
        }
        let expected = expected.expect("one protected expression is present");
        let mut budget = SyntaxBudget::with_limit(10_000);
        let parsed = super::super::parse_macro_tree_inner(
            &source,
            invocation,
            output,
            &SyntaxContexts::new(&[], &[], &[]),
            &[],
            super::super::MacroOutputPosition::Declarations,
            &mut budget,
        )
        .expect("the existing declaration path accepts a protected expression");
        assert!(
            parsed
                .tree
                .events()
                .iter()
                .any(|event| { matches!(event, Event::Start(NodeKind::SyntaxQuote)) })
        );
        assert!(parsed.original_nodes.values().any(|node| node == &expected));
    }

    #[test]
    fn hook_scopes_charge_exact_syntax_work_before_retention_and_retry() {
        for expression in [
            "hook Adjust {\n3\n}",
            "register Adjust increment {\n3\n}",
            "register Api.Adjust<Int> (factory 1) {\nhook Api.Adjust<Int> {\n3\n}\n}",
        ] {
            let source = SourceFile::new(
                "hook-work.ash",
                format!("main : Unit -> Int\nmain () = {expression}\n"),
            )
            .unwrap();
            let baseline = super::super::parse(lex(&source).unwrap());
            super::super::project_module(&source, &baseline).unwrap();
            // The owning syntax ledger charges one unit for each retained
            // token and event, including both scope nodes and their targets.
            let exact_work = baseline.tokens().len() + baseline.events().len();
            let parse_at = |limit| {
                let mut budget = SyntaxBudget::with_limit(limit);
                let lexed = lex_with_budget(&source, &mut budget).unwrap();
                parse_with_budget(lexed, &mut budget)
            };
            let short = parse_at(exact_work - 1);
            assert_eq!(
                short.resource_failure(),
                Some(ResourceFailure::SyntaxWork {
                    limit: exact_work - 1
                })
            );
            assert!(short.root().is_none());
            for _ in 0..2 {
                let exact = parse_at(exact_work);
                assert_eq!(exact.resource_failure(), None);
                assert_eq!(exact.events(), baseline.events());
                super::super::project_module(&source, &exact).unwrap();
            }
        }
    }
}
