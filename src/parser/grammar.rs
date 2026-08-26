//! Closed assembly of the grammar forms accepted by this parser dialect.

use crate::lexer::TokenKind;

use super::{ExpectedForm, NodeKind, ParseReason, Parser, SynchronizationBoundary, expression};

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
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum PrimaryForm {
    Integer,
    Boolean,
    Identifier,
    Qualified,
    UpperIdentifier,
    Parenthesized,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum AtomicTypeForm {
    Int,
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
    ],
    expression: ExpressionDialect {
        primary_forms: &[
            PrimaryForm::Integer,
            PrimaryForm::Boolean,
            PrimaryForm::Identifier,
            PrimaryForm::Qualified,
            PrimaryForm::UpperIdentifier,
            PrimaryForm::Parenthesized,
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
        AtomicTypeForm::Bool,
        AtomicTypeForm::Unit,
        AtomicTypeForm::Nominal,
        AtomicTypeForm::Parenthesized,
    ],
};

pub(super) const fn selected_dialect() -> &'static ParserDialect {
    &CURRENT_ASH_DIALECT
}

pub(super) fn module(parser: &mut Parser<'_>) {
    parser.start(NodeKind::Module);
    while parser.at(&TokenKind::Import)
        || (parser.at(&TokenKind::Pub) && parser.nth(1) == Some(&TokenKind::Import))
    {
        import_declaration(parser);
        if !parser.expect(&TokenKind::LineEnd, ExpectedForm::LineEnd) {
            break;
        }
    }
    while starts_module_declaration(parser) {
        module_declaration(parser);
        if !expect_declaration_line_end(parser) {
            break;
        }
    }
    if parser.at(&TokenKind::EndOfFile) {
        let _ = parser.bump();
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

fn expect_declaration_line_end(parser: &mut Parser<'_>) -> bool {
    let recovered_expression_group = parser.take_recovered_expression_group_boundary();
    if recovered_expression_group && parser.at(&TokenKind::EndOfFile) {
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
        let mut complete = import_item(parser);
        while complete && parser.at(&TokenKind::Comma) {
            let _ = parser.bump();
            complete = import_item(parser);
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

fn import_item(parser: &mut Parser<'_>) -> bool {
    parser.start(NodeKind::ImportItem);
    if parser.at(&TokenKind::Impl) {
        let _ = parser.bump();
        if !matches!(parser.current(), Some(TokenKind::UpperIdentifier(_))) {
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

fn expect_lower_identifier(parser: &mut Parser<'_>) {
    if matches!(parser.current(), Some(TokenKind::Identifier(_))) {
        let _ = parser.bump();
    } else {
        parser.report(ParseReason::ExpectedForm, ExpectedForm::Identifier);
    }
}

fn expect_upper_identifier(parser: &mut Parser<'_>) {
    if matches!(parser.current(), Some(TokenKind::UpperIdentifier(_))) {
        let _ = parser.bump();
    } else {
        parser.report(ParseReason::ExpectedForm, ExpectedForm::Identifier);
    }
}

fn starts_module_declaration(parser: &Parser<'_>) -> bool {
    parser.at(&TokenKind::Type)
        || parser.at(&TokenKind::Interface)
        || parser.at(&TokenKind::Impl)
        || starts_global(parser)
        || parser.at(&TokenKind::Pub)
            && matches!(
                parser.nth(1),
                Some(
                    TokenKind::Type
                        | TokenKind::Opaque
                        | TokenKind::Interface
                        | TokenKind::Impl
                        | TokenKind::Fn
                        | TokenKind::Identifier(_)
                )
            )
}

fn module_declaration(parser: &mut Parser<'_>) {
    if parser.at(&TokenKind::Type)
        || parser.at(&TokenKind::Pub)
            && matches!(parser.nth(1), Some(TokenKind::Type | TokenKind::Opaque))
    {
        type_declaration(parser);
    } else if parser.at(&TokenKind::Interface)
        || parser.at(&TokenKind::Pub) && matches!(parser.nth(1), Some(TokenKind::Interface))
    {
        interface_declaration(parser);
    } else if parser.at(&TokenKind::Impl)
        || parser.at(&TokenKind::Pub) && matches!(parser.nth(1), Some(TokenKind::Impl))
    {
        implementation_declaration(parser);
    } else {
        global_definition(parser);
    }
}

#[derive(Clone, Copy)]
enum HeaderRecoveryBoundary {
    LineEnd,
    OpeningBrace(SynchronizationBoundary),
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

fn implementation_declaration(parser: &mut Parser<'_>) {
    parser.start(NodeKind::ImplementationDeclaration);
    if parser.at(&TokenKind::Pub) {
        let _ = parser.bump();
    }
    let _ = parser.expect(&TokenKind::Impl, ExpectedForm::InterfaceApplication);
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
        return;
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

fn interface_declaration(parser: &mut Parser<'_>) {
    parser.start(NodeKind::InterfaceDeclaration);
    if parser.at(&TokenKind::Pub) {
        let _ = parser.bump();
    }
    let _ = parser.expect(&TokenKind::Interface, ExpectedForm::Identifier);
    let parameter_recovery_start = parser.pending_recovery_count();
    if matches!(parser.current(), Some(TokenKind::UpperIdentifier(_))) {
        let _ = parser.bump();
        interface_parameter(parser);
    } else {
        report_pending_expected(parser, ExpectedForm::Identifier);
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
        return;
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

fn interface_parameter(parser: &mut Parser<'_>) {
    if !parser.at(&TokenKind::Less) {
        report_pending_expected(parser, ExpectedForm::InterfaceParameter);
        return;
    }
    let _ = parser.bump();
    let parameter_present = if matches!(parser.current(), Some(TokenKind::UpperIdentifier(_))) {
        let _ = parser.bump();
        true
    } else {
        report_pending_expected(parser, ExpectedForm::InterfaceParameter);
        false
    };
    if parser.at(&TokenKind::Greater) {
        let _ = parser.bump();
        return;
    }
    if parameter_present {
        report_pending_expected(parser, ExpectedForm::InterfaceParameter);
    }
    while !matches!(
        parser.current(),
        Some(TokenKind::Greater | TokenKind::LeftBrace | TokenKind::LineEnd | TokenKind::EndOfFile)
            | None
    ) {
        let _ = parser.bump();
    }
    if parser.at(&TokenKind::Greater) {
        let _ = parser.bump();
    }
}

fn interface_method(parser: &mut Parser<'_>) {
    parser.start(NodeKind::InterfaceMethod);
    let recovery_start = parser.pending_recovery_count();
    binder(parser);
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
        } else if matches!(parser.current(), Some(TokenKind::UpperIdentifier(_))) {
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
    if matches!(parser.current(), Some(TokenKind::UpperIdentifier(_))) {
        if parser
            .nth(1)
            .is_some_and(|kind| matches!(kind, TokenKind::Dot))
        {
            parser.start(NodeKind::QualifiedName);
            let _ = parser.bump();
            let _ = parser.bump();
            if matches!(parser.current(), Some(TokenKind::UpperIdentifier(_))) {
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
        let argument_valid = if starts_type(parser) {
            type_expression(parser);
            true
        } else {
            report_pending_expected(parser, ExpectedForm::InterfaceApplication);
            false
        };
        if parser.at(&TokenKind::Greater) {
            let _ = parser.bump();
        } else {
            if argument_valid {
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

fn type_declaration(parser: &mut Parser<'_>) {
    parser.start(NodeKind::TypeDeclaration);
    if parser.at(&TokenKind::Pub) {
        let _ = parser.bump();
        if parser.at(&TokenKind::Opaque) {
            let _ = parser.bump();
        }
    }
    let _ = parser.expect(&TokenKind::Type, ExpectedForm::Type);
    if matches!(parser.current(), Some(TokenKind::UpperIdentifier(_))) {
        let _ = parser.bump();
    } else {
        parser.report(ParseReason::ExpectedForm, ExpectedForm::Identifier);
    }
    if parser.at(&TokenKind::Less) {
        let _ = parser.bump();
        if matches!(parser.current(), Some(TokenKind::UpperIdentifier(_))) {
            let _ = parser.bump();
            while parser.at(&TokenKind::Comma) {
                let _ = parser.bump();
                if matches!(parser.current(), Some(TokenKind::UpperIdentifier(_))) {
                    let _ = parser.bump();
                } else {
                    parser.report(ParseReason::ExpectedForm, ExpectedForm::Identifier);
                    break;
                }
            }
        } else {
            parser.report(ParseReason::ExpectedForm, ExpectedForm::Identifier);
        }
        let _ = parser.expect(&TokenKind::Greater, ExpectedForm::Type);
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
    parser.finish();
}

fn constructor_declaration(parser: &mut Parser<'_>) {
    parser.start(NodeKind::ConstructorDeclaration);
    if matches!(parser.current(), Some(TokenKind::UpperIdentifier(_))) {
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

fn global_definition(parser: &mut Parser<'_>) {
    match global_definition_form(parser) {
        Some(GlobalDefinitionForm::Equational) => equational_global(parser),
        Some(GlobalDefinitionForm::InlineOperational) => inline_operational_global(parser),
        None => parser.report(ParseReason::UnexpectedToken, ExpectedForm::Expression),
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
                (Some(TokenKind::Identifier(_)), Some(TokenKind::Colon))
            ),
            GlobalDefinitionForm::InlineOperational => matches!(
                (parser.nth(offset), parser.nth(offset.saturating_add(1))),
                (Some(TokenKind::Fn), Some(TokenKind::Identifier(_)))
            ),
        })
}

fn equational_global(parser: &mut Parser<'_>) {
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

fn inline_operational_global(parser: &mut Parser<'_>) {
    parser.start(NodeKind::InlineOperationalGlobal);
    if parser.at(&TokenKind::Pub) {
        let _ = parser.bump();
    }
    parser.start(NodeKind::InlineOperationalHeader);
    let _ = parser.bump();
    binder(parser);
    reject_polymorphic_header(parser);
    let _ = parser.expect(&TokenKind::LeftParen, ExpectedForm::LeftParen);
    typed_pattern(parser);
    while parser.at(&TokenKind::Comma) {
        let _ = parser.bump();
        typed_pattern(parser);
    }
    let _ = parser.expect(&TokenKind::RightParen, ExpectedForm::RightParen);
    let _ = parser.expect(&TokenKind::Arrow, ExpectedForm::Arrow);
    type_expression(parser);
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
        return;
    }
    block(parser);
    parser.finish();
}

pub(super) fn expression(parser: &mut Parser<'_>) {
    match expression_prefix_form(parser) {
        Some(ExpressionPrefixForm::Block) => block_expression(parser),
        Some(ExpressionPrefixForm::Function) => function_expression(parser),
        Some(ExpressionPrefixForm::Match) => match_expression(parser),
        None => expression::operator_expression(parser),
    }
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
        })
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
    if !matches!(parser.current(), Some(TokenKind::Identifier(_))) {
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
    binder(parser);
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

fn reject_polymorphic_header(parser: &mut Parser<'_>) {
    if !parser.at(&TokenKind::Less) {
        return;
    }
    parser.error_at_current(ParseReason::PolymorphicHeader);
    while !matches!(
        parser.current(),
        Some(TokenKind::LeftParen | TokenKind::LineEnd | TokenKind::EndOfFile)
    ) {
        let _ = parser.bump();
    }
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

fn pattern(parser: &mut Parser<'_>) {
    pattern_inner(parser, false);
}

fn pattern_inner(parser: &mut Parser<'_>, allow_juxtaposed_payload: bool) {
    parser.start(NodeKind::Pattern);
    let form = pattern_form(parser);
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
        Some(PatternForm::Binder) if starts_lowercase_qualification(parser) => {
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
        Some(PatternForm::Constructor) => constructor_pattern(parser, allow_juxtaposed_payload),
        Some(PatternForm::Parenthesized) => parenthesized_pattern(parser),
        None => parser.report(ParseReason::ExpectedForm, ExpectedForm::Pattern),
    }
    if owns_structure {
        parser.leave_structures(super::PATTERN_STRUCTURAL_WEIGHT);
    }
    parser.finish();
}

fn pattern_form(parser: &Parser<'_>) -> Option<PatternForm> {
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
    pattern_form(parser).is_some()
}

fn constructor_pattern(parser: &mut Parser<'_>, allow_juxtaposed_payload: bool) {
    parser.start(NodeKind::ConstructorPattern);
    if parser
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

fn type_expression(parser: &mut Parser<'_>) {
    parser.start(NodeKind::Type);
    atomic_type(parser);
    if parser.at(&TokenKind::Arrow) {
        let _ = parser.bump();
        if parser.enter_structure() {
            type_expression(parser);
            parser.leave_structure();
        } else {
            parser.consume_rest();
        }
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
            Some(AtomicTypeForm::Int | AtomicTypeForm::Bool | AtomicTypeForm::Unit) => {
                let _ = parser.bump();
                if parser.at(&TokenKind::Less) {
                    parser.error_at_current(ParseReason::UnexpectedToken);
                    type_arguments(parser);
                }
            }
            Some(AtomicTypeForm::Nominal) => {
                if parser
                    .nth(1)
                    .is_some_and(|kind| matches!(kind, TokenKind::Dot))
                {
                    qualified_name(parser, true);
                } else {
                    let _ = parser.bump();
                }
                if parser.at(&TokenKind::Less) {
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
    let _ = parser.bump();
    type_expression(parser);
    while parser.at(&TokenKind::Comma) {
        let _ = parser.bump();
        type_expression(parser);
    }
    let _ = parser.expect(&TokenKind::Greater, ExpectedForm::Type);
}

fn atomic_type_form(parser: &Parser<'_>) -> Option<AtomicTypeForm> {
    selected_dialect()
        .atomic_types
        .iter()
        .copied()
        .find(|form| {
            matches!(
                (form, parser.current()),
                (AtomicTypeForm::Int, Some(TokenKind::IntType))
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
    matches!(parser.current(), Some(TokenKind::Identifier(_)))
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
    expression_prefix_form(parser).is_some() || expression::starts_primary(parser)
}

#[cfg(test)]
mod tests {
    use crate::{lexer::lex, source::SourceFile};

    use super::*;

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
}
