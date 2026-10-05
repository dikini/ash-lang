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
    Handler,
    Resume,
    Resource,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum PrimaryForm {
    Integer,
    Boolean,
    Identifier,
    Qualified,
    UpperIdentifier,
    Parenthesized,
    Perform,
    Discard,
    Hook,
    Registration,
    Cleanup,
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
        ExpressionPrefixForm::Handler,
        ExpressionPrefixForm::Resume,
        ExpressionPrefixForm::Resource,
    ],
    expression: ExpressionDialect {
        primary_forms: &[
            PrimaryForm::Integer,
            PrimaryForm::Boolean,
            PrimaryForm::Identifier,
            PrimaryForm::Qualified,
            PrimaryForm::UpperIdentifier,
            PrimaryForm::Parenthesized,
            PrimaryForm::Perform,
            PrimaryForm::Discard,
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
    let mut declaration_boundary_failed = false;
    while starts_module_declaration(parser) {
        let declaration_outcome = module_declaration(parser);
        if declaration_outcome == TypeParametersOutcome::RecoveredToEndOfFile
            && parser.at(&TokenKind::EndOfFile)
        {
            continue;
        }
        if !expect_declaration_line_end(parser) {
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
                        | TokenKind::Identifier(_)
                )
            )
}

fn module_declaration(parser: &mut Parser<'_>) -> TypeParametersOutcome {
    if parser.at(&TokenKind::Resource)
        || parser.at(&TokenKind::Pub) && parser.nth(1) == Some(&TokenKind::Resource)
    {
        resource_definition(parser)
    } else if starts_newtype_declaration(parser) {
        newtype_declaration(parser)
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
    if matches!(parser.current(), Some(TokenKind::UpperIdentifier(_))) {
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
    if matches!(parser.current(), Some(TokenKind::UpperIdentifier(_))) {
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
    if matches!(parser.current(), Some(TokenKind::UpperIdentifier(_))) {
        let _ = parser.bump();
        return true;
    }
    if !parser.at(&TokenKind::LeftParen) {
        report_pending_expected(parser, ExpectedForm::Identifier);
        return false;
    }

    let _ = parser.bump();
    if !matches!(parser.current(), Some(TokenKind::UpperIdentifier(_))) {
        report_pending_expected(parser, ExpectedForm::Identifier);
        return false;
    }
    let _ = parser.bump();
    while parser.at(&TokenKind::Comma) {
        let _ = parser.bump();
        if !matches!(parser.current(), Some(TokenKind::UpperIdentifier(_))) {
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
    if matches!(parser.current(), Some(TokenKind::UpperIdentifier(_))) {
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
    parser.finish();
    TypeParametersOutcome::Complete
}

fn newtype_declaration(parser: &mut Parser<'_>) -> TypeParametersOutcome {
    parser.start(NodeKind::NewtypeDeclaration);
    if parser.at(&TokenKind::Pub) {
        let _ = parser.bump();
        if parser.at(&TokenKind::Opaque) {
            let _ = parser.bump();
        }
    }
    let _ = parser.expect(&TokenKind::Newtype, ExpectedForm::Type);
    if matches!(parser.current(), Some(TokenKind::UpperIdentifier(_))) {
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
    parser.finish();
    TypeParametersOutcome::Complete
}

fn newtype_constructor_declaration(parser: &mut Parser<'_>) {
    parser.start(NodeKind::ConstructorDeclaration);
    if matches!(parser.current(), Some(TokenKind::UpperIdentifier(_))) {
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
    match expression_prefix_form(parser) {
        Some(ExpressionPrefixForm::Block) => block_expression(parser),
        Some(ExpressionPrefixForm::Function) => function_expression(parser),
        Some(ExpressionPrefixForm::Match) => match_expression(parser),
        Some(ExpressionPrefixForm::Handler) => handler_expression(parser),
        Some(ExpressionPrefixForm::Resume) => resume_expression(parser),
        Some(ExpressionPrefixForm::Resource) => resource_expression(parser),
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
            ExpressionPrefixForm::Handler => parser.at(&TokenKind::Handle),
            ExpressionPrefixForm::Resume => parser.at(&TokenKind::Resume),
            ExpressionPrefixForm::Resource => parser.at(&TokenKind::Resource),
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
        let _ = parser.expect(&TokenKind::Less, ExpectedForm::Type);
        parser.start(NodeKind::Type);
        parser.start(NodeKind::AtomicType);
        expect_upper_identifier(parser);
        parser.finish();
        parser.finish();
        while parser.at(&TokenKind::Comma) {
            let _ = parser.bump();
            application_argument(parser);
        }
        let _ = parser.expect(&TokenKind::Greater, ExpectedForm::Greater);
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
    if matches!(parser.current(), Some(TokenKind::Identifier(name)) if name == "cell" || name == "native_buffer")
    {
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

fn handler_expression(parser: &mut Parser<'_>) {
    parser.start(NodeKind::HandlerExpression);
    let _ = parser.bump();
    expression(parser);
    let _ = parser.expect(&TokenKind::With, ExpectedForm::Expression);
    effect_instance(parser);
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
        && matches!(parser.nth(2), Some(TokenKind::UpperIdentifier(_)))
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
            newtype_declaration(parser);
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
    matches!(parser.current(), Some(TokenKind::UpperIdentifier(_)))
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
    let mut complete = if matches!(parser.current(), Some(TokenKind::UpperIdentifier(_))) {
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
        if parser.at(&TokenKind::Bang) {
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
    } else if matches!(parser.current(), Some(TokenKind::UpperIdentifier(_))) {
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
    application_argument(parser);
    while parser.at(&TokenKind::Comma) {
        let _ = parser.bump();
        application_argument(parser);
    }
    let _ = parser.expect(&TokenKind::Greater, ExpectedForm::Type);
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

fn resource_field_word(parser: &mut Parser<'_>, word: &str) {
    if matches!(parser.current(), Some(TokenKind::Identifier(name)) if name == word) {
        let _ = parser.bump();
    } else {
        parser.report(ParseReason::ExpectedForm, ExpectedForm::Identifier);
    }
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
            "handlers" => {
                binder(parser);
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
        source::SourceFile,
        syntax_resource::SyntaxBudget,
    };

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
            ShadowPrefixForm::Existing(ExpressionPrefixForm::Handler) => "handler parser",
            ShadowPrefixForm::Existing(ExpressionPrefixForm::Resume) => "resume parser",
            ShadowPrefixForm::Existing(ExpressionPrefixForm::Resource) => "resource parser",
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
