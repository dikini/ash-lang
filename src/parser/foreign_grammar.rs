//! Signature and link-name grammar for passive libraries.
use super::*;
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
pub(super) fn library(parser: &mut Parser<'_>) -> TypeParametersOutcome {
    parser.start(NodeKind::ForeignLibrary);
    if parser.at(&TokenKind::Pub) {
        let _ = parser.bump();
    }
    let _ = word(parser, "foreign");
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
pub(super) fn starts_library(parser: &Parser<'_>) -> bool {
    let offset = usize::from(parser.at(&TokenKind::Pub));
    matches!(parser.nth(offset),Some(TokenKind::Identifier(word)) if word=="foreign")
        && matches!(parser.nth(offset+1),Some(TokenKind::Identifier(word)) if word=="library")
        && matches!(parser.nth(offset + 2), Some(TokenKind::UpperIdentifier(_)))
        && parser.nth(offset + 3) == Some(&TokenKind::LeftBrace)
}
fn member(parser: &mut Parser<'_>) -> bool {
    parser.start(NodeKind::ForeignMember);
    let result = if at_word(parser, "profile") {
        let _ = parser.bump();
        string(parser);
        true
    } else if at_word(parser, "symbol") {
        let _ = parser.bump();
        expect_upper_identifier(parser);
        let _ = parser.expect(&TokenKind::Colon, ExpectedForm::Colon);
        type_expression(parser);
        let _ = parser.expect(&TokenKind::LeftBrace, ExpectedForm::LeftBrace);
        if parser.at(&TokenKind::LineEnd) {
            let _ = parser.bump();
        }
        let _ = word(parser, "name");
        string(parser);
        if parser.at(&TokenKind::LineEnd) {
            let _ = parser.bump();
        }
        let _ = parser.expect(&TokenKind::RightBrace, ExpectedForm::RightBrace);
        true
    } else {
        parser.report(ParseReason::ExpectedForm, ExpectedForm::Identifier);
        false
    };
    parser.finish();
    result
}
