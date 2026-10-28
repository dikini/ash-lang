//! Tokens owned by the Ash lexical layer.

use crate::{integer::Integer, source::Span};

/// One lexical token and its exact source span.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Token {
    /// The token's lexical meaning.
    pub kind: TokenKind,
    /// The exact source bytes covered by the token.
    pub span: Span,
}

/// The complete token family available to the Ash parser.
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
    /// An experimental UTF-8 string literal with decoded escapes.
    StringLiteral(String),
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
    /// The `newtype` reserved word.
    Newtype,
    /// The `effect` reserved word.
    Effect,
    /// The `match` reserved word.
    Match,
    /// The `perform` reserved word.
    Perform,
    /// The `handle` reserved word.
    Handle,
    /// The `with` reserved word.
    With,
    /// The `resume` reserved word.
    Resume,
    /// Scoped acquisition of the builtin cell resource.
    Resource,
    /// The `region` lexical allocation-owner declaration.
    Region,
    /// The `using` lexical allocation-selection expression.
    Using,
    /// The `hook` reserved word.
    Hook,
    /// The `register` reserved word.
    Register,
    /// The `cleanup` reserved word.
    Cleanup,
    /// The `discard` reserved word.
    Discard,
    /// Clause-scoped transfer of a captured continuation.
    Retain,
    /// The `import` reserved word.
    Import,
    /// The `as` reserved word.
    As,
    /// The `pub` reserved word.
    Pub,
    /// The `opaque` reserved word.
    Opaque,
    /// The `interface` reserved word.
    Interface,
    /// The `impl` reserved word.
    Impl,
    /// The `where` reserved word.
    Where,
    /// The `Int` type name.
    IntType,
    /// The experimental `Bytes` type name.
    BytesType,
    /// The experimental `String` type name.
    StringType,
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
    /// `@`, introducing a named module root.
    At,
    /// `.`, separating module path segments and qualified names.
    Dot,
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
    /// `!`.
    Bang,
    /// `,`, separating tuple elements, parameters, and constructor fields.
    Comma,
    /// `<`, opening a type argument list.
    Less,
    /// `>`, closing a type argument list.
    Greater,
    /// `;`, retained so the parser can reject excluded semicolon syntax.
    Semicolon,
    /// A logical line boundary.
    LineEnd,
    /// The zero-width end of the source file.
    EndOfFile,
}
