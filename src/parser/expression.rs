//! The closed operator table and expression-precedence parser.

use crate::lexer::TokenKind;

use super::{
    ExpectedForm, NodeKind, ParseReason, Parser, SynchronizationBoundary,
    grammar::{self, Associativity, ExpressionDialect, InfixDescriptor, PrimaryForm},
};

#[derive(Clone, Copy)]
struct CompletedExpression {
    start_event: usize,
    depth: usize,
}

pub(super) fn operator_expression(parser: &mut Parser<'_>) {
    operator_expression_with(parser, &grammar::selected_dialect().expression);
}

fn operator_expression_with(parser: &mut Parser<'_>, dialect: &ExpressionDialect) {
    let _ = parse_precedence(parser, dialect, 0);
}

fn parse_precedence(
    parser: &mut Parser<'_>,
    dialect: &ExpressionDialect,
    minimum_binding_power: u8,
) -> CompletedExpression {
    let mut left = parse_primary(parser, dialect.primary_forms);
    let mut consumed_non_associative = None;

    loop {
        if starts_primary_in(parser, dialect.primary_forms)
            && dialect.application.left_binding_power >= minimum_binding_power
        {
            let right = parse_precedence(parser, dialect, dialect.application.right_binding_power);
            let depth = left.depth.max(right.depth).saturating_add(1);
            if !parser.permits_expression_depth(depth) {
                parser.consume_rest();
                return left;
            }
            let _ = parser.insert_start(left.start_event, dialect.application.result);
            parser.finish();
            left.depth = depth;
            continue;
        }

        let Some(descriptor) = current_infix(parser, dialect.infix) else {
            break;
        };
        let (left_binding_power, right_binding_power) = descriptor.binding_powers();
        if left_binding_power < minimum_binding_power {
            break;
        }
        if consumed_non_associative == Some(descriptor.precedence) {
            consume_repeated_non_associative(parser, dialect, descriptor);
            continue;
        }

        let operator = parser.current_span();
        let _ = parser.bump();
        let right = if starts_primary_in(parser, dialect.primary_forms) {
            Some(parse_precedence(parser, dialect, right_binding_power))
        } else {
            report_missing_operand(parser, operator);
            None
        };
        let depth = left
            .depth
            .max(right.map_or(0, |expression| expression.depth))
            .saturating_add(1);
        if !parser.permits_expression_depth(depth) {
            parser.consume_rest();
            return left;
        }
        let _ = parser.insert_start(left.start_event, descriptor.result);
        parser.finish();
        if descriptor.associativity == Associativity::NonAssociative {
            consumed_non_associative = Some(descriptor.precedence);
        }
        left = CompletedExpression {
            start_event: left.start_event,
            depth,
        };
    }
    left
}

fn parse_primary(parser: &mut Parser<'_>, forms: &[PrimaryForm]) -> CompletedExpression {
    let start_event = parser.event_position();
    parser.start(NodeKind::PrimaryExpression);
    match primary_form(parser, forms) {
        Some(
            PrimaryForm::Integer
            | PrimaryForm::Boolean
            | PrimaryForm::Identifier
            | PrimaryForm::UpperIdentifier,
        ) => {
            let _ = parser.bump();
        }
        Some(PrimaryForm::Qualified) => grammar::qualified_name(parser, false),
        Some(PrimaryForm::Parenthesized) => parse_parenthesized(parser),
        _ => parser.report(ParseReason::ExpectedOperand, ExpectedForm::Operand),
    }
    parser.finish();
    CompletedExpression {
        start_event,
        depth: 0,
    }
}

fn parse_parenthesized(parser: &mut Parser<'_>) {
    parser.start(NodeKind::ParenthesizedExpression);
    let opening = parser.current_span();
    let _ = parser.bump();
    if parser.at(&TokenKind::RightParen) {
        let _ = parser.bump();
        parser.finish();
        return;
    }
    let recovery_start = parser.pending_recovery_count();
    if !parser.enter_structure() {
        parser.consume_rest();
        parser.finish();
        return;
    }
    let tuple_start = parser.event_position();
    grammar::expression(parser);
    parser.leave_structure();
    if parser.at(&TokenKind::Comma) {
        let _ = parser.insert_start(tuple_start, NodeKind::TupleExpression);
        while parser.at(&TokenKind::Comma) {
            let _ = parser.bump();
            if parser.enter_structure() {
                grammar::expression(parser);
                parser.leave_structure();
            } else {
                parser.consume_rest();
                break;
            }
        }
        parser.finish();
    }
    if parser.at(&TokenKind::RightParen) {
        parser.resolve_pending_at_current(
            recovery_start,
            SynchronizationBoundary::ParenthesisClosing,
        );
        let _ = parser.bump();
    } else {
        if parser.at(&TokenKind::RightBrace) {
            parser.resolve_pending_at_current(
                recovery_start,
                SynchronizationBoundary::BlockClosingBrace,
            );
        } else if parser.at(&TokenKind::EndOfFile) {
            parser.resolve_pending_at_current(recovery_start, SynchronizationBoundary::EndOfFile);
        }
        report_unclosed_group(parser, opening);
    }
    parser.finish();
}

fn current_infix<'a>(
    parser: &Parser<'_>,
    descriptors: &'a [InfixDescriptor],
) -> Option<&'a InfixDescriptor> {
    let current = parser.current()?;
    descriptors
        .iter()
        .find(|descriptor| descriptor.token.matches(current))
}

pub(super) fn starts_primary(parser: &Parser<'_>) -> bool {
    starts_primary_in(parser, grammar::selected_dialect().expression.primary_forms)
}

fn starts_primary_in(parser: &Parser<'_>, forms: &[PrimaryForm]) -> bool {
    primary_form(parser, forms).is_some()
}

fn primary_form(parser: &Parser<'_>, forms: &[PrimaryForm]) -> Option<PrimaryForm> {
    forms
        .iter()
        .copied()
        .find(|form| match (form, parser.current()) {
            (PrimaryForm::Integer, Some(TokenKind::Integer(_)))
            | (PrimaryForm::Boolean, Some(TokenKind::True | TokenKind::False))
            | (PrimaryForm::Identifier, Some(TokenKind::Identifier(_)))
            | (PrimaryForm::UpperIdentifier, Some(TokenKind::UpperIdentifier(_)))
            | (PrimaryForm::Parenthesized, Some(TokenKind::LeftParen)) => true,
            (PrimaryForm::Qualified, Some(TokenKind::UpperIdentifier(_))) => {
                parser
                    .nth(1)
                    .is_some_and(|kind| matches!(kind, TokenKind::Dot))
                    && parser.nth(2).is_some_and(|kind| {
                        matches!(
                            kind,
                            TokenKind::Identifier(_) | TokenKind::UpperIdentifier(_)
                        )
                    })
            }
            _ => false,
        })
}

fn consume_repeated_non_associative(
    parser: &mut Parser<'_>,
    dialect: &ExpressionDialect,
    descriptor: &InfixDescriptor,
) {
    parser.start(NodeKind::Error);
    parser.error_at_current(ParseReason::RepeatedEquality);
    let _ = parser.bump();
    let (_, right_binding_power) = descriptor.binding_powers();
    if starts_primary_in(parser, dialect.primary_forms) {
        let _ = parse_precedence(parser, dialect, right_binding_power);
    } else {
        report_missing_operand(parser, parser.current_span());
    }
    parser.finish();
}

fn report_missing_operand(parser: &mut Parser<'_>, operator: Option<crate::source::Span>) {
    if let Some(operator) = operator {
        let waits_for_owner = matches!(
            parser.current(),
            Some(
                TokenKind::LineEnd
                    | TokenKind::RightBrace
                    | TokenKind::RightParen
                    | TokenKind::EndOfFile
            )
        );
        let related = (!waits_for_owner).then(|| parser.current_span()).flatten();
        let diagnostic = parser.report_at(
            ParseReason::ExpectedOperand,
            ExpectedForm::Operand,
            operator,
            related,
        );
        if let (true, Some(diagnostic)) = (waits_for_owner, diagnostic) {
            parser.mark_pending_recovery(diagnostic);
        }
    } else {
        parser.report(ParseReason::ExpectedOperand, ExpectedForm::Operand);
    }
}

pub(super) fn report_unclosed_group(parser: &mut Parser<'_>, opening: Option<crate::source::Span>) {
    if let Some(opening) = opening {
        parser.report_at(
            ParseReason::UnclosedGroup,
            ExpectedForm::RightParen,
            opening,
            parser.current_span(),
        );
    } else {
        parser.report(ParseReason::UnclosedGroup, ExpectedForm::RightParen);
    }
}

#[cfg(test)]
mod tests {
    use crate::{lexer::lex, source::SourceFile};

    use super::*;
    use crate::parser::Event;
    use crate::parser::grammar::{
        ApplicationDescriptor, Associativity, ExpressionDialect, InfixDescriptor, OperatorToken,
    };

    const PRIMARIES: &[PrimaryForm] = &[
        PrimaryForm::Integer,
        PrimaryForm::Boolean,
        PrimaryForm::Identifier,
        PrimaryForm::Parenthesized,
    ];

    const APPLICATION: ApplicationDescriptor = ApplicationDescriptor {
        left_binding_power: 40,
        right_binding_power: 41,
        result: NodeKind::ApplicationExpression,
    };

    mod mock_operator_feature {
        use super::*;

        pub const DESCRIPTOR: InfixDescriptor = InfixDescriptor {
            token: OperatorToken::MockSemicolon,
            precedence: 25,
            associativity: Associativity::Left,
            result: NodeKind::EqualityExpression,
        };
    }

    fn parse_probe(
        source_text: &str,
        infix: &'static [InfixDescriptor],
    ) -> (Vec<NodeKind>, Vec<ParseReason>) {
        let source = SourceFile::new("descriptor.ash", source_text)
            .expect("the descriptor fixture should fit");
        let lexed = lex(&source).expect("the descriptor fixture should lex");
        let dialect = ExpressionDialect {
            primary_forms: PRIMARIES,
            infix,
            application: APPLICATION,
        };
        let mut parser = Parser {
            tokens: &lexed.tokens,
            position: 0,
            events: Vec::new(),
            diagnostics: Vec::new(),
            pending_recoveries: Vec::new(),
            nesting_depth: 0,
            resource_failure: None,
            syntax_budget: crate::syntax_resource::SyntaxBudget::default(),
            syntax_work_exhausted: false,
        };

        operator_expression_with(&mut parser, &dialect);
        let starts = parser
            .events
            .iter()
            .filter_map(|event| match event {
                Event::Start(kind) => Some(*kind),
                _ => None,
            })
            .collect();
        let reasons = parser
            .diagnostics
            .iter()
            .map(|diagnostic| diagnostic.reason)
            .collect();
        (starts, reasons)
    }

    #[test]
    fn descriptors_determine_result_nodes_and_associativity() {
        const LEFT: &[InfixDescriptor] = &[InfixDescriptor {
            token: OperatorToken::Plus,
            precedence: 10,
            associativity: Associativity::Left,
            result: NodeKind::MultiplicativeExpression,
        }];
        const NON_ASSOCIATIVE: &[InfixDescriptor] = &[InfixDescriptor {
            token: OperatorToken::Plus,
            precedence: 10,
            associativity: Associativity::NonAssociative,
            result: NodeKind::MultiplicativeExpression,
        }];

        let (left, left_reasons) = parse_probe("1 + 2 + 3", LEFT);
        let (non_associative, non_associative_reasons) = parse_probe("1 + 2 + 3", NON_ASSOCIATIVE);

        assert_eq!(
            left,
            vec![
                NodeKind::MultiplicativeExpression,
                NodeKind::MultiplicativeExpression,
                NodeKind::PrimaryExpression,
                NodeKind::PrimaryExpression,
                NodeKind::PrimaryExpression,
            ]
        );
        assert_eq!(
            non_associative,
            vec![
                NodeKind::MultiplicativeExpression,
                NodeKind::PrimaryExpression,
                NodeKind::PrimaryExpression,
                NodeKind::Error,
                NodeKind::PrimaryExpression,
            ]
        );
        assert!(left_reasons.is_empty());
        assert_eq!(non_associative_reasons, vec![ParseReason::RepeatedEquality]);
    }

    #[test]
    fn a_mock_operator_changes_only_its_feature_and_closed_operator_table() {
        const MOCK_OPERATOR_TABLE: &[InfixDescriptor] = &[mock_operator_feature::DESCRIPTOR];
        let (starts, reasons) = parse_probe("1 ; 2", MOCK_OPERATOR_TABLE);
        assert!(reasons.is_empty());
        assert_eq!(starts[0], NodeKind::EqualityExpression);

        let (production_starts, production_reasons) =
            parse_probe("1 + 2", grammar::selected_dialect().expression.infix);
        assert!(production_reasons.is_empty());
        assert_eq!(production_starts[0], NodeKind::AdditiveExpression);
    }
}
