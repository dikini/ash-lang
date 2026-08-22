//! Tokens owned by the Mini-Ash lexical layer.

use crate::{integer::Integer, source::Span};

/// One lexical token and its exact source span.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Token {
    /// The token's lexical meaning.
    pub kind: TokenKind,
    /// The exact source bytes covered by the token.
    pub span: Span,
}

/// The complete token family available to the Mini-Ash parser.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum TokenKind {
    /// An ASCII identifier.
    Identifier(String),
    /// An ASCII uppercase-starting type or constructor identifier.
    UpperIdentifier(String),
    /// The reserved wildcard spelling `_`.
    Wildcard,
    /// An arbitrary-precision decimal integer literal.
    Integer(Integer),
    /// The `true` reserved word.
    True,
    /// The `false` reserved word.
    False,
    /// The `fn` reserved word.
    Fn,
    /// The `let` reserved word.
    Let,
    /// The `rec` reserved word.
    Rec,
    /// The `and` reserved word.
    And,
    /// The `type` reserved word.
    Type,
    /// The `match` reserved word.
    Match,
    /// The `Int` type name.
    IntType,
    /// The `Bool` type name.
    BoolType,
    /// The `Unit` type name.
    UnitType,
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
    /// `==`.
    EqualEqual,
    /// `+`.
    Plus,
    /// `*`.
    Star,
    /// `->`.
    Arrow,
    /// `=>`.
    FatArrow,
    /// `|`.
    Pipe,
    /// `,`, separating tuple elements, parameters, and constructor fields.
    Comma,
    /// `;`, retained so the parser can reject excluded semicolon syntax.
    Semicolon,
    /// A logical line boundary.
    LineEnd,
    /// The zero-width end of the source file.
    EndOfFile,
}
