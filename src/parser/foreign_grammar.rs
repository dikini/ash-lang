//! Foreign contract grammar; words remain contextual inside their declarations.

use super::*;

pub(super) fn starts_library(parser: &Parser<'_>) -> bool {
    let offset = usize::from(parser.at(&TokenKind::Pub));
    let library = offset
        + 1
        + usize::from(
            matches!(parser.nth(offset + 1), Some(TokenKind::Identifier(word)) if word == "checked"),
        );
    matches!(parser.nth(offset), Some(TokenKind::Identifier(word)) if word == "foreign")
        && matches!(parser.nth(library), Some(TokenKind::Identifier(word)) if word == "library")
        && matches!(parser.nth(library + 1), Some(TokenKind::UpperIdentifier(_)))
        && parser.nth(library + 2) == Some(&TokenKind::LeftBrace)
}

fn at_word(parser: &Parser<'_>, word: &str) -> bool {
    matches!(parser.current(), Some(TokenKind::Identifier(found)) if found == word)
}

fn word(parser: &mut Parser<'_>, expected: &str) -> bool {
    if at_word(parser, expected) {
        parser.bump()
    } else {
        parser.report(ParseReason::ExpectedForm, ExpectedForm::Identifier);
        false
    }
}

fn integer(parser: &mut Parser<'_>) {
    parser.start(NodeKind::ForeignInteger);
    if parser.at(&TokenKind::Minus) {
        let _ = parser.bump();
    }
    if matches!(parser.current(), Some(TokenKind::Integer(_))) {
        let _ = parser.bump();
    } else {
        parser.report(ParseReason::ExpectedForm, ExpectedForm::Operand);
    }
    parser.finish();
}

fn reference(parser: &mut Parser<'_>) {
    parser.start(NodeKind::ForeignReference);
    expect_upper_identifier(parser);
    if parser.at(&TokenKind::Dot) {
        let _ = parser.bump();
        expect_upper_identifier(parser);
    }
    parser.finish();
}

fn source_position(parser: &mut Parser<'_>) {
    parser.start(NodeKind::ForeignSourcePosition);
    integer(parser);
    while parser.at(&TokenKind::Dot) {
        let _ = parser.bump();
        integer(parser);
    }
    parser.finish();
}

fn native_position(parser: &mut Parser<'_>) {
    parser.start(NodeKind::ForeignNativePosition);
    if at_word(parser, "result") {
        let _ = parser.bump();
    } else {
        integer(parser);
    }
    parser.finish();
}

fn parameters(parser: &mut Parser<'_>) {
    if parser.at(&TokenKind::Less) {
        let _ = type_parameters(parser, TypeParameterOwnerBoundary::Effect);
    }
}

fn required_parameters(parser: &mut Parser<'_>) {
    if parser.at(&TokenKind::Less) {
        parameters(parser);
    } else {
        parser.report(ParseReason::ExpectedForm, ExpectedForm::Type);
    }
}

fn comma_list(parser: &mut Parser<'_>, item: fn(&mut Parser<'_>)) {
    item(parser);
    while parser.at(&TokenKind::Comma) {
        let _ = parser.bump();
        item(parser);
    }
}

pub(super) fn library(parser: &mut Parser<'_>) -> TypeParametersOutcome {
    parser.start(NodeKind::ForeignLibrary);
    if parser.at(&TokenKind::Pub) {
        let _ = parser.bump();
    }
    let _ = word(parser, "foreign");
    if at_word(parser, "checked") {
        let _ = parser.bump();
    }
    let _ = word(parser, "library");
    expect_upper_identifier(parser);
    let _ = parser.expect(&TokenKind::LeftBrace, ExpectedForm::LeftBrace);
    let _ = parser.expect(&TokenKind::LineEnd, ExpectedForm::LineEnd);
    loop {
        if !member(parser) {
            break;
        }
        if parser.at(&TokenKind::RightBrace) {
            break;
        }
        if !parser.expect(&TokenKind::LineEnd, ExpectedForm::LineEnd)
            || parser.at(&TokenKind::RightBrace)
        {
            break;
        }
    }
    let _ = parser.expect(&TokenKind::RightBrace, ExpectedForm::RightBrace);
    parser.finish();
    TypeParametersOutcome::Complete
}

fn string(parser: &mut Parser<'_>) {
    if matches!(parser.current(), Some(TokenKind::StringLiteral(_))) {
        let _ = parser.bump();
    } else {
        parser.report(ParseReason::ExpectedForm, ExpectedForm::Operand);
    }
}

fn member(parser: &mut Parser<'_>) -> bool {
    parser.start(NodeKind::ForeignMember);
    let result = if at_word(parser, "profile") {
        let _ = parser.bump();
        string(parser);
        true
    } else if at_word(parser, "repr") {
        let _ = parser.bump();
        expect_upper_identifier(parser);
        let _ = parser.expect(&TokenKind::Equal, ExpectedForm::Equal);
        representation(parser);
        true
    } else if at_word(parser, "const") || at_word(parser, "sentinel") {
        let sentinel = at_word(parser, "sentinel");
        let _ = parser.bump();
        expect_upper_identifier(parser);
        let _ = parser.expect(&TokenKind::Colon, ExpectedForm::Colon);
        reference(parser);
        let _ = parser.expect(&TokenKind::Equal, ExpectedForm::Equal);
        if sentinel {
            let _ = word(parser, "all_bits_one");
        } else {
            integer(parser);
        }
        true
    } else if at_word(parser, "owner") {
        owner(parser);
        true
    } else if at_word(parser, "access") {
        access(parser);
        true
    } else if at_word(parser, "symbol") {
        symbol(parser);
        true
    } else {
        parser.report(ParseReason::ExpectedForm, ExpectedForm::Identifier);
        false
    };
    parser.finish();
    result
}

fn representation(parser: &mut Parser<'_>) {
    parser.start(NodeKind::ForeignRepresentation);
    if at_word(parser, "signed") || at_word(parser, "unsigned") {
        let _ = parser.bump();
        let _ = parser.expect(&TokenKind::LeftParen, ExpectedForm::LeftParen);
        integer(parser);
        let _ = parser.expect(&TokenKind::RightParen, ExpectedForm::RightParen);
    } else if at_word(parser, "size_t")
        || at_word(parser, "bytes")
        || at_word(parser, "function_address")
        || parser.at(&TokenKind::Opaque)
    {
        let _ = parser.bump();
    } else {
        parser.report(ParseReason::ExpectedForm, ExpectedForm::Identifier);
    }
    parser.finish();
}

fn line(parser: &mut Parser<'_>) {
    let _ = parser.expect(&TokenKind::LineEnd, ExpectedForm::LineEnd);
}

fn close(parser: &mut Parser<'_>) {
    if parser.at(&TokenKind::LineEnd) {
        let _ = parser.bump();
    }
    let _ = parser.expect(&TokenKind::RightBrace, ExpectedForm::RightBrace);
}

fn owner(parser: &mut Parser<'_>) {
    let _ = word(parser, "owner");
    expect_upper_identifier(parser);
    required_parameters(parser);
    let _ = parser.expect(&TokenKind::LeftBrace, ExpectedForm::LeftBrace);
    line(parser);
    let _ = word(parser, "representation");
    reference(parser);
    line(parser);
    let _ = word(parser, "owned");
    expect_upper_identifier(parser);
    line(parser);
    if at_word(parser, "retains") {
        let _ = parser.bump();
        comma_list(parser, expect_upper_identifier);
        line(parser);
    }
    let _ = word(parser, "teardown");
    reference(parser);
    close(parser);
}

fn access(parser: &mut Parser<'_>) {
    let _ = word(parser, "access");
    expect_upper_identifier(parser);
    required_parameters(parser);
    let _ = parser.expect(&TokenKind::LeftBrace, ExpectedForm::LeftBrace);
    line(parser);
    let _ = word(parser, "window");
    expect_upper_identifier(parser);
    line(parser);
    let _ = word(parser, "owner");
    type_expression(parser);
    line(parser);
    let _ = word(parser, "extent");
    if at_word(parser, "bytes") || at_word(parser, "nul") {
        let _ = parser.bump();
    } else {
        parser.report(ParseReason::ExpectedForm, ExpectedForm::Identifier);
    }
    line(parser);
    let _ = word(parser, "preserves");
    comma_list(parser, reference);
    close(parser);
}

fn abi_representation(parser: &mut Parser<'_>) {
    parser.start(NodeKind::ForeignAbiRepresentation);
    if at_word(parser, "void") {
        let _ = parser.bump();
    } else if at_word(parser, "pointer") {
        let _ = parser.bump();
        let _ = parser.expect(&TokenKind::LeftParen, ExpectedForm::LeftParen);
        reference(parser);
        let _ = parser.expect(&TokenKind::RightParen, ExpectedForm::RightParen);
    } else {
        reference(parser);
    }
    parser.finish();
}

fn abi_operand(parser: &mut Parser<'_>) {
    parser.start(NodeKind::ForeignAbiOperand);
    if at_word(parser, "out") {
        let _ = parser.bump();
        let _ = parser.expect(&TokenKind::LeftParen, ExpectedForm::LeftParen);
        abi_representation(parser);
        let _ = parser.expect(&TokenKind::RightParen, ExpectedForm::RightParen);
    } else {
        abi_representation(parser);
    }
    parser.finish();
}

fn symbol(parser: &mut Parser<'_>) {
    let _ = word(parser, "symbol");
    expect_upper_identifier(parser);
    parameters(parser);
    let _ = parser.expect(&TokenKind::Colon, ExpectedForm::Colon);
    type_expression(parser);
    let _ = parser.expect(&TokenKind::LeftBrace, ExpectedForm::LeftBrace);
    line(parser);
    let _ = word(parser, "name");
    string(parser);
    line(parser);
    let _ = word(parser, "abi");
    let _ = parser.expect(&TokenKind::LeftParen, ExpectedForm::LeftParen);
    if !parser.at(&TokenKind::RightParen) {
        comma_list(parser, abi_operand);
    }
    let _ = parser.expect(&TokenKind::RightParen, ExpectedForm::RightParen);
    let _ = parser.expect(&TokenKind::Arrow, ExpectedForm::Arrow);
    abi_representation(parser);
    line(parser);
    loop {
        if !contract(parser) || parser.at(&TokenKind::RightBrace) {
            break;
        }
        if !parser.expect(&TokenKind::LineEnd, ExpectedForm::LineEnd)
            || parser.at(&TokenKind::RightBrace)
        {
            break;
        }
    }
    let _ = parser.expect(&TokenKind::RightBrace, ExpectedForm::RightBrace);
}

fn contract(parser: &mut Parser<'_>) -> bool {
    parser.start(NodeKind::ForeignCallContract);
    let result = if at_word(parser, "destruction_operand") {
        let _ = parser.bump();
        native_position(parser);
        let _ = word(parser, "from");
        source_position(parser);
        let _ = word(parser, "scalar");
        true
    } else if at_word(parser, "operand") {
        let _ = parser.bump();
        native_position(parser);
        let _ = word(parser, "from");
        if at_word(parser, "constant") {
            let _ = parser.bump();
            reference(parser);
        } else if at_word(parser, "null") {
            let _ = parser.bump();
        } else {
            source_position(parser);
            operand_role(parser);
        }
        true
    } else if at_word(parser, "output") {
        let _ = parser.bump();
        native_position(parser);
        let _ = parser.expect(&TokenKind::As, ExpectedForm::Identifier);
        output_role(parser);
        true
    } else if at_word(parser, "outcome") {
        let _ = parser.bump();
        outcome_test(parser);
        let _ = parser.expect(&TokenKind::LeftBrace, ExpectedForm::LeftBrace);
        if !parser.at(&TokenKind::RightBrace) {
            comma_list(parser, outcome_fact);
        }
        let _ = parser.expect(&TokenKind::RightBrace, ExpectedForm::RightBrace);
        true
    } else if at_word(parser, "retained_dependents") {
        let _ = parser.bump();
        let _ = word(parser, "block");
        true
    } else {
        parser.report(ParseReason::ExpectedForm, ExpectedForm::Identifier);
        false
    };
    parser.finish();
    result
}

fn discipline(parser: &mut Parser<'_>) {
    parser.start(NodeKind::ForeignInputDiscipline);
    if at_word(parser, "call_borrow") || at_word(parser, "copy") {
        let _ = parser.bump();
    } else {
        parser.report(ParseReason::ExpectedForm, ExpectedForm::Identifier);
    }
    parser.finish();
}

fn operand_role(parser: &mut Parser<'_>) {
    parser.start(NodeKind::ForeignOperandRole);
    if at_word(parser, "bytes") {
        let _ = parser.bump();
        let _ = parser.expect(&TokenKind::LeftParen, ExpectedForm::LeftParen);
        source_position(parser);
        let _ = parser.expect(&TokenKind::RightParen, ExpectedForm::RightParen);
        discipline(parser);
    } else if at_word(parser, "nul") {
        let _ = parser.bump();
        discipline(parser);
    } else if ["scalar", "current", "enclosing", "view", "sentinel"]
        .iter()
        .any(|word| at_word(parser, word))
    {
        let _ = parser.bump();
    } else {
        parser.report(ParseReason::ExpectedForm, ExpectedForm::Identifier);
    }
    parser.finish();
}

fn output_role(parser: &mut Parser<'_>) {
    parser.start(NodeKind::ForeignOutputRole);
    if at_word(parser, "scalar") {
        let _ = parser.bump();
    } else if at_word(parser, "owner") || at_word(parser, "view") {
        let view = at_word(parser, "view");
        let _ = parser.bump();
        let _ = parser.expect(&TokenKind::LeftParen, ExpectedForm::LeftParen);
        type_expression(parser);
        if view && parser.at(&TokenKind::Comma) {
            let _ = parser.bump();
            comma_list(parser, source_position);
        }
        let _ = parser.expect(&TokenKind::RightParen, ExpectedForm::RightParen);
    } else if at_word(parser, "extent_of") || at_word(parser, "offset_into") {
        let extent = at_word(parser, "extent_of");
        let _ = parser.bump();
        let _ = parser.expect(&TokenKind::LeftParen, ExpectedForm::LeftParen);
        source_position(parser);
        if extent {
            while parser.at(&TokenKind::Comma) {
                let _ = parser.bump();
                source_position(parser);
            }
        }
        let _ = parser.expect(&TokenKind::RightParen, ExpectedForm::RightParen);
    } else {
        parser.report(ParseReason::ExpectedForm, ExpectedForm::Identifier);
    }
    parser.finish();
}

fn outcome_test(parser: &mut Parser<'_>) {
    parser.start(NodeKind::ForeignOutcomeTest);
    if at_word(parser, "otherwise") {
        let _ = parser.bump();
    } else {
        outcome_atom(parser);
        while parser.at(&TokenKind::And) {
            let _ = parser.bump();
            outcome_atom(parser);
        }
    }
    parser.finish();
}

fn outcome_atom(parser: &mut Parser<'_>) {
    parser.start(NodeKind::ForeignOutcomeAtom);
    native_position(parser);
    if parser.at(&TokenKind::EqualEqual) {
        let _ = parser.bump();
        reference(parser);
    } else if at_word(parser, "null") || at_word(parser, "nonnull") {
        let _ = parser.bump();
    } else {
        parser.report(ParseReason::ExpectedForm, ExpectedForm::Identifier);
    }
    parser.finish();
}

fn outcome_fact(parser: &mut Parser<'_>) {
    parser.start(NodeKind::ForeignOutcomeFact);
    if at_word(parser, "readable") || at_word(parser, "unreadable") {
        let _ = parser.bump();
        native_position(parser);
    } else if at_word(parser, "consumed") || at_word(parser, "retained") {
        let _ = parser.bump();
        source_position(parser);
    } else if at_word(parser, "initialized_bytes") {
        let _ = parser.bump();
        native_position(parser);
        let _ = word(parser, "from");
        source_position(parser);
    } else {
        parser.report(ParseReason::ExpectedForm, ExpectedForm::Identifier);
    }
    parser.finish();
}

#[cfg(test)]
mod tests {
    use crate::{
        lexer::lex_with_budget,
        parser::{ResourceFailure, parse_with_budget, project_module},
        source::SourceFile,
        syntax_resource::SyntaxBudget,
    };

    #[test]
    fn foreign_grammar_uses_the_shared_exact_syntax_budget_and_fresh_retry() {
        let source = SourceFile::new("foreign-budget.ash", "foreign library Native {\n    profile \"x86_64-unknown-linux-gnu\"\n    repr CInt = signed(32)\n    const Negative : CInt = -1\n}\n").unwrap();
        let parse_with_limit = |limit| {
            let mut budget = SyntaxBudget::with_limit(limit);
            let lexed = lex_with_budget(&source, &mut budget).unwrap();
            parse_with_budget(lexed, &mut budget)
        };
        let measured = parse_with_limit(crate::syntax_resource::SYNTAX_WORK_LIMIT);
        let exact_work = measured.tokens().len() + measured.events().len();
        let exact = parse_with_limit(exact_work);
        assert!(project_module(&source, &exact).is_ok());
        let short = parse_with_limit(exact_work - 1);
        assert_eq!(
            short.resource_failure(),
            Some(ResourceFailure::SyntaxWork {
                limit: exact_work - 1
            })
        );
        assert!(project_module(&source, &short).is_err());
        assert!(project_module(&source, &parse_with_limit(exact_work)).is_ok());
    }
}
