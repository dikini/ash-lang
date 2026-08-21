//! Parser events retained as the construction boundary for concrete syntax.

use crate::source::Span;

use super::{ExpectedForm, NodeKind, ParseReason};

/// One parser action in source order.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Event {
    /// Begins a concrete node.
    Start(NodeKind),
    /// Retains the token at this index in the lexer's complete stream.
    Token(usize),
    /// Records a required form absent from the token stream.
    Missing {
        /// The required syntactic form.
        expected: ExpectedForm,
        /// The zero-width or recovery-point span.
        at: Span,
    },
    /// Records a structured parse failure inside the concrete tree.
    Error(ParseReason),
    /// Finishes the most recently started concrete node.
    Finish,
}
