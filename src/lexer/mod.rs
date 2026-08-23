//! Delimiter-aware lexical analysis for the Ash token family.

mod token;

pub use token::{Token, TokenKind};

use std::fmt;

use crate::{
    diagnostic::{Diagnostic, SourceLabel},
    integer::Integer,
    source::{ByteRange, SourceError, SourceFile, Span},
    syntax_resource::{ResourceFailure, SyntaxBudget},
};

/// A lexical failure retained independently from its eventual rendering.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum LexReason {
    /// A carriage return was not followed by a line feed.
    BareCarriageReturn,
    /// The source contains a UTF-8 byte order mark.
    ByteOrderMark,
    /// An identifier contains a non-ASCII character.
    UnicodeIdentifier,
    /// The source uses comment syntax excluded from Ash.
    Comment,
    /// A minus sign prefixes decimal digits.
    NegativeLiteral,
    /// A digit sequence does not match the accepted decimal grammar.
    InvalidIntegerLiteral,
    /// An ASCII word does not match a reserved word or identifier grammar.
    InvalidIdentifier,
    /// No Ash token begins with the source character.
    UnknownCharacter,
}

impl LexReason {
    const fn primary_message(self) -> &'static str {
        match self {
            Self::BareCarriageReturn => "bare carriage return is not a line break",
            Self::ByteOrderMark => "byte order marks are not accepted",
            Self::UnicodeIdentifier => "identifiers use ASCII characters",
            Self::Comment => "comments are not available in Ash",
            Self::NegativeLiteral => "negative integer literals are not available in Ash",
            Self::InvalidIntegerLiteral => "integer literal does not match the decimal grammar",
            Self::InvalidIdentifier => "word is not an ASCII identifier or reserved word",
            Self::UnknownCharacter => "character does not begin an Ash token",
        }
    }

    const fn expected(self) -> Option<&'static str> {
        match self {
            Self::BareCarriageReturn => Some("an LF or CRLF line break"),
            Self::UnicodeIdentifier | Self::InvalidIdentifier => {
                Some("an ASCII identifier matching [a-z_][a-zA-Z0-9_]*")
            }
            Self::NegativeLiteral => Some("a nonnegative decimal integer"),
            Self::InvalidIntegerLiteral => Some("0 or a nonzero digit followed by ASCII digits"),
            Self::ByteOrderMark | Self::Comment | Self::UnknownCharacter => None,
        }
    }
}

impl fmt::Display for LexReason {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(match self {
            Self::BareCarriageReturn => "lex.bare-carriage-return",
            Self::ByteOrderMark => "lex.byte-order-mark",
            Self::UnicodeIdentifier => "lex.unicode-identifier",
            Self::Comment => "lex.comment",
            Self::NegativeLiteral => "lex.negative-literal",
            Self::InvalidIntegerLiteral => "lex.invalid-integer-literal",
            Self::InvalidIdentifier => "lex.invalid-identifier",
            Self::UnknownCharacter => "lex.unknown-character",
        })
    }
}

/// The complete token stream and any independently structured lexical errors.
///
/// Invalid source is represented by diagnostics instead of widening the closed
/// [`TokenKind`] family with error tokens. The parser can retain every token
/// the lexer did produce, but semantic projection must not proceed when these
/// diagnostics are present.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Lexed {
    /// Tokens available to the parser, including end of input.
    pub tokens: Vec<Token>,
    /// Lexical errors encountered while making progress through the source.
    pub diagnostics: Vec<Diagnostic<LexReason>>,
    syntax_budget: SyntaxBudget,
    resource_failure: Option<ResourceFailure>,
}

impl Lexed {
    /// Returns a non-syntactic implementation resource failure, if any.
    #[must_use]
    pub const fn resource_failure(&self) -> Option<ResourceFailure> {
        self.resource_failure
    }

    pub(crate) fn into_parts(
        self,
    ) -> (
        Vec<Token>,
        Vec<Diagnostic<LexReason>>,
        SyntaxBudget,
        Option<ResourceFailure>,
    ) {
        (
            self.tokens,
            self.diagnostics,
            self.syntax_budget,
            self.resource_failure,
        )
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum DelimiterContext {
    File,
    Paren,
    Brace,
}

impl DelimiterContext {
    const fn emits_line_end(self) -> bool {
        matches!(self, Self::File | Self::Brace)
    }
}

/// Lexes one admitted source file.
///
/// # Errors
///
/// Returns a source-model error only if the admitted source's stored invariants
/// cannot produce checked token spans.
pub fn lex(source: &SourceFile) -> Result<Lexed, SourceError> {
    let text = source.text();
    let bytes = text.as_bytes();
    let mut offset = 0;
    let mut tokens = Vec::new();
    let mut diagnostics = Vec::new();
    let mut contexts = vec![DelimiterContext::File];
    let mut logical_line_has_token = false;
    let mut syntax_budget = SyntaxBudget::default();

    macro_rules! charge_syntax {
        () => {
            if let Err(resource_failure) = syntax_budget.charge() {
                return Ok(Lexed {
                    tokens,
                    diagnostics,
                    syntax_budget,
                    resource_failure: Some(resource_failure),
                });
            }
        };
    }

    while offset < bytes.len() {
        let start = offset;
        let newline_width = match bytes[offset] {
            b'\n' => Some(1),
            b'\r' if bytes.get(offset + 1) == Some(&b'\n') => Some(2),
            _ => None,
        };
        if let Some(width) = newline_width {
            offset += width;
            let emits_line_end = contexts
                .last()
                .is_some_and(|context| context.emits_line_end());
            if emits_line_end && logical_line_has_token {
                charge_syntax!();
                tokens.push(Token {
                    kind: TokenKind::LineEnd,
                    span: checked_span(source, start, offset)?,
                });
                logical_line_has_token = false;
            }
            continue;
        }

        if matches!(bytes[offset], b' ' | b'\t') {
            offset += 1;
            continue;
        }

        // Charge the lexical output before any token payload or diagnostic is
        // retained. Every remaining branch emits exactly one such output.
        charge_syntax!();

        if bytes[offset] == b'\r' {
            offset += 1;
            record_diagnostic(
                source,
                &mut diagnostics,
                LexReason::BareCarriageReturn,
                start,
                offset,
                &text[start..offset],
            )?;
            continue;
        }
        if text[offset..].starts_with('\u{feff}') {
            offset += '\u{feff}'.len_utf8();
            record_diagnostic(
                source,
                &mut diagnostics,
                LexReason::ByteOrderMark,
                start,
                offset,
                &text[start..offset],
            )?;
            continue;
        }
        if text[offset..].starts_with("//") {
            offset = scan_line_comment(text, offset);
            record_diagnostic(
                source,
                &mut diagnostics,
                LexReason::Comment,
                start,
                offset,
                &text[start..offset],
            )?;
            continue;
        }
        if text[offset..].starts_with("/*") {
            offset = scan_block_comment(text, offset);
            record_diagnostic(
                source,
                &mut diagnostics,
                LexReason::Comment,
                start,
                offset,
                &text[start..offset],
            )?;
            continue;
        }
        if bytes[offset] == b'-' && bytes.get(offset + 1).is_some_and(u8::is_ascii_digit) {
            offset += 2;
            while offset < bytes.len() && bytes[offset].is_ascii_digit() {
                offset += 1;
            }
            record_diagnostic(
                source,
                &mut diagnostics,
                LexReason::NegativeLiteral,
                start,
                offset,
                &text[start..offset],
            )?;
            continue;
        }

        let kind = match bytes[offset] {
            b'a'..=b'z' | b'A'..=b'Z' | b'_' => {
                offset = scan_identifier_like(text, start);
                let word = &text[start..offset];
                let reason = if word.is_ascii() {
                    LexReason::InvalidIdentifier
                } else {
                    LexReason::UnicodeIdentifier
                };
                let kind = word.is_ascii().then(|| classify_word(word)).flatten();
                let Some(kind) = kind else {
                    record_diagnostic(source, &mut diagnostics, reason, start, offset, word)?;
                    continue;
                };
                kind
            }
            b'0'..=b'9' => {
                offset += 1;
                while offset < bytes.len() && bytes[offset].is_ascii_digit() {
                    offset += 1;
                }
                let literal = &text[start..offset];
                let Ok(integer) = Integer::parse_decimal(literal) else {
                    record_diagnostic(
                        source,
                        &mut diagnostics,
                        LexReason::InvalidIntegerLiteral,
                        start,
                        offset,
                        literal,
                    )?;
                    continue;
                };
                TokenKind::Integer(integer)
            }
            b'(' => single(&mut offset, TokenKind::LeftParen),
            b')' => single(&mut offset, TokenKind::RightParen),
            b'{' => single(&mut offset, TokenKind::LeftBrace),
            b'}' => single(&mut offset, TokenKind::RightBrace),
            b'@' => single(&mut offset, TokenKind::At),
            b'.' => single(&mut offset, TokenKind::Dot),
            b':' => single(&mut offset, TokenKind::Colon),
            b'+' => single(&mut offset, TokenKind::Plus),
            b'*' => single(&mut offset, TokenKind::Star),
            b',' => single(&mut offset, TokenKind::Comma),
            b'<' => single(&mut offset, TokenKind::Less),
            b'>' => single(&mut offset, TokenKind::Greater),
            b'|' => single(&mut offset, TokenKind::Pipe),
            b';' => single(&mut offset, TokenKind::Semicolon),
            b'=' if bytes.get(offset + 1) == Some(&b'=') => {
                offset += 2;
                TokenKind::EqualEqual
            }
            b'=' if bytes.get(offset + 1) == Some(&b'>') => {
                offset += 2;
                TokenKind::FatArrow
            }
            b'=' => single(&mut offset, TokenKind::Equal),
            b'-' if bytes.get(offset + 1) == Some(&b'>') => {
                offset += 2;
                TokenKind::Arrow
            }
            _ => {
                let Some(character) = text[offset..].chars().next() else {
                    return Err(SourceError::InvalidLineState);
                };
                if !character.is_ascii() && character.is_alphabetic() {
                    offset = scan_identifier_like(text, start);
                    record_diagnostic(
                        source,
                        &mut diagnostics,
                        LexReason::UnicodeIdentifier,
                        start,
                        offset,
                        &text[start..offset],
                    )?;
                    continue;
                }
                offset += character.len_utf8();
                record_diagnostic(
                    source,
                    &mut diagnostics,
                    LexReason::UnknownCharacter,
                    start,
                    offset,
                    &text[start..offset],
                )?;
                continue;
            }
        };
        update_delimiter_contexts(&mut contexts, &kind);
        logical_line_has_token = true;
        tokens.push(Token {
            kind,
            span: checked_span(source, start, offset)?,
        });
    }

    charge_syntax!();
    tokens.push(Token {
        kind: TokenKind::EndOfFile,
        span: checked_span(source, offset, offset)?,
    });

    Ok(Lexed {
        tokens,
        diagnostics,
        syntax_budget,
        resource_failure: None,
    })
}

fn record_diagnostic(
    source: &SourceFile,
    diagnostics: &mut Vec<Diagnostic<LexReason>>,
    reason: LexReason,
    start: usize,
    end: usize,
    found: &str,
) -> Result<(), SourceError> {
    let span = checked_span(source, start, end)?;
    let mut diagnostic = Diagnostic::new(reason, SourceLabel::new(span, reason.primary_message()));
    diagnostic.expected = reason.expected().map(str::to_owned);
    diagnostic.found = Some(found.to_owned());
    diagnostics.push(diagnostic);
    Ok(())
}

fn scan_line_comment(text: &str, start: usize) -> usize {
    text[start..]
        .find(['\r', '\n'])
        .map_or(text.len(), |relative| start + relative)
}

fn scan_block_comment(text: &str, start: usize) -> usize {
    text[start + 2..]
        .find("*/")
        .map_or(text.len(), |relative| start + 2 + relative + 2)
}

fn scan_identifier_like(text: &str, start: usize) -> usize {
    let mut end = start;
    for (relative, character) in text[start..].char_indices() {
        if character == '_' || character.is_alphanumeric() {
            end = start + relative + character.len_utf8();
        } else {
            break;
        }
    }
    end
}

fn update_delimiter_contexts(contexts: &mut Vec<DelimiterContext>, kind: &TokenKind) {
    match kind {
        TokenKind::LeftParen => contexts.push(DelimiterContext::Paren),
        TokenKind::LeftBrace => contexts.push(DelimiterContext::Brace),
        TokenKind::RightParen if contexts.last() == Some(&DelimiterContext::Paren) => {
            let _ = contexts.pop();
        }
        TokenKind::RightBrace if contexts.last() == Some(&DelimiterContext::Brace) => {
            let _ = contexts.pop();
        }
        _ => {}
    }
}

fn single(offset: &mut usize, kind: TokenKind) -> TokenKind {
    *offset += 1;
    kind
}

fn classify_word(word: &str) -> Option<TokenKind> {
    let reserved = match word {
        "true" => Some(TokenKind::True),
        "false" => Some(TokenKind::False),
        "fn" => Some(TokenKind::Fn),
        "let" => Some(TokenKind::Let),
        "rec" => Some(TokenKind::Rec),
        "and" => Some(TokenKind::And),
        "type" => Some(TokenKind::Type),
        "match" => Some(TokenKind::Match),
        "import" => Some(TokenKind::Import),
        "as" => Some(TokenKind::As),
        "pub" => Some(TokenKind::Pub),
        "opaque" => Some(TokenKind::Opaque),
        "_" => Some(TokenKind::Wildcard),
        "Int" => Some(TokenKind::IntType),
        "Bool" => Some(TokenKind::BoolType),
        "Unit" => Some(TokenKind::UnitType),
        _ => None,
    };
    reserved.or_else(|| match word.as_bytes().first() {
        Some(first) if first.is_ascii_lowercase() || *first == b'_' => {
            Some(TokenKind::Identifier(word.into()))
        }
        Some(first) if first.is_ascii_uppercase() => Some(TokenKind::UpperIdentifier(word.into())),
        _ => None,
    })
}

fn checked_span(source: &SourceFile, start: usize, end: usize) -> Result<Span, SourceError> {
    let start = u32::try_from(start).map_err(|_| SourceError::TextTooLarge)?;
    let end = u32::try_from(end).map_err(|_| SourceError::TextTooLarge)?;
    let range = ByteRange::new(start, end).map_err(|_| SourceError::InvalidLineState)?;
    source.span(range)
}
