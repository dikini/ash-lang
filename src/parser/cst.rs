//! Token-complete concrete syntax built from parser events.

use crate::{
    diagnostic::Diagnostic,
    lexer::{LexReason, Token},
    source::Span,
};

use super::{Event, ExpectedForm, NodeKind, ParseDiagnostic, ParseReason, ResourceFailure};

/// One child retained in an error-bearing concrete syntax node.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ConcreteElement {
    /// A nested concrete node.
    Node(ConcreteNode),
    /// An index into [`ConcreteTree::tokens`].
    Token(usize),
    /// A required form absent from the token stream.
    Missing {
        /// The required syntactic form.
        expected: ExpectedForm,
        /// The source point at which it was required.
        at: Span,
    },
    /// A parse error retained at its grammar location.
    Error(ParseReason),
}

/// One concrete syntax node.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ConcreteNode {
    /// The grammar role of this node.
    pub kind: NodeKind,
    /// Ordered token, node, and recovery children.
    pub children: Vec<ConcreteElement>,
}

impl Drop for ConcreteNode {
    fn drop(&mut self) {
        let mut pending = std::mem::take(&mut self.children);
        while let Some(element) = pending.pop() {
            if let ConcreteElement::Node(mut child) = element {
                pending.append(&mut child.children);
            }
        }
    }
}

/// Why an event stream cannot describe one complete concrete tree.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum InternalReason {
    /// A finish event had no corresponding start event.
    UnexpectedFinish,
    /// One or more start events were not finished.
    UnclosedNode,
    /// The stream produced no root or more than one root.
    InvalidRootCount,
    /// A token index was outside the retained token stream.
    TokenOutOfRange,
    /// A token was retained more than once.
    DuplicateToken,
    /// A lexer token was omitted from the concrete tree.
    MissingToken,
    /// Retained token spans do not follow source order.
    TokenOutOfOrder,
    /// Concrete children did not have the shape required for projection.
    UnexpectedShape,
    /// A projected span attempted to join different source files.
    ForeignSpan,
    /// A projected span could not be represented by the source model.
    InvalidSpan,
}

/// The parser's lossless token boundary and error-bearing tree.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ConcreteTree {
    pub(crate) root: Option<ConcreteNode>,
    pub(crate) tokens: Vec<Token>,
    pub(crate) events: Vec<Event>,
    pub(crate) lexical_diagnostics: Vec<Diagnostic<LexReason>>,
    pub(crate) parse_diagnostics: Vec<ParseDiagnostic>,
    pub(crate) malformed: Option<InternalReason>,
    pub(crate) resource_failure: Option<ResourceFailure>,
}

impl ConcreteTree {
    /// Returns the concrete root when event construction produced exactly one.
    #[must_use]
    pub const fn root(&self) -> Option<&ConcreteNode> {
        self.root.as_ref()
    }

    /// Returns the complete lexer token stream, including end of input.
    #[must_use]
    pub fn tokens(&self) -> &[Token] {
        &self.tokens
    }

    /// Returns the event stream that constructed this tree.
    #[must_use]
    pub fn events(&self) -> &[Event] {
        &self.events
    }

    /// Returns lexical diagnostics preserved as a hard semantic boundary.
    #[must_use]
    pub fn lexical_diagnostics(&self) -> &[Diagnostic<LexReason>] {
        &self.lexical_diagnostics
    }

    /// Returns structured parser diagnostics.
    #[must_use]
    pub fn parse_diagnostics(&self) -> &[ParseDiagnostic] {
        &self.parse_diagnostics
    }

    /// Returns a non-syntactic implementation resource failure, if any.
    #[must_use]
    pub const fn resource_failure(&self) -> Option<ResourceFailure> {
        self.resource_failure
    }
}

pub(crate) fn build(
    tokens: Vec<Token>,
    lexical_diagnostics: Vec<Diagnostic<LexReason>>,
    parse_diagnostics: Vec<ParseDiagnostic>,
    events: Vec<Event>,
    resource_failure: Option<ResourceFailure>,
) -> ConcreteTree {
    let mut stack: Vec<ConcreteNode> = Vec::new();
    let mut roots = Vec::new();
    let mut malformed = None;
    let mut seen = vec![false; tokens.len()];
    let mut last_token_index = None;

    for event in &events {
        match event {
            Event::Start(kind) => stack.push(ConcreteNode {
                kind: *kind,
                children: Vec::new(),
            }),
            Event::Token(index) => {
                if *index >= tokens.len() {
                    malformed.get_or_insert(InternalReason::TokenOutOfRange);
                } else if seen[*index] {
                    malformed.get_or_insert(InternalReason::DuplicateToken);
                } else if last_token_index.is_some_and(|last| *index < last) {
                    malformed.get_or_insert(InternalReason::TokenOutOfOrder);
                } else {
                    seen[*index] = true;
                }
                last_token_index = Some(*index);
                if let Some(node) = stack.last_mut() {
                    node.children.push(ConcreteElement::Token(*index));
                } else {
                    malformed.get_or_insert(InternalReason::InvalidRootCount);
                }
            }
            Event::Missing { expected, at } => {
                if let Some(node) = stack.last_mut() {
                    node.children.push(ConcreteElement::Missing {
                        expected: *expected,
                        at: *at,
                    });
                } else {
                    malformed.get_or_insert(InternalReason::InvalidRootCount);
                }
            }
            Event::Error(reason) => {
                if let Some(node) = stack.last_mut() {
                    node.children.push(ConcreteElement::Error(*reason));
                } else {
                    malformed.get_or_insert(InternalReason::InvalidRootCount);
                }
            }
            Event::Finish => {
                let Some(node) = stack.pop() else {
                    malformed.get_or_insert(InternalReason::UnexpectedFinish);
                    continue;
                };
                if let Some(parent) = stack.last_mut() {
                    parent.children.push(ConcreteElement::Node(node));
                } else {
                    roots.push(node);
                }
            }
        }
    }

    if !stack.is_empty() {
        malformed.get_or_insert(InternalReason::UnclosedNode);
    }
    if seen.iter().any(|was_seen| !was_seen) {
        malformed.get_or_insert(InternalReason::MissingToken);
    }
    let root = if roots.len() == 1 {
        roots.pop()
    } else {
        malformed.get_or_insert(InternalReason::InvalidRootCount);
        None
    };

    ConcreteTree {
        root,
        tokens,
        events,
        lexical_diagnostics,
        parse_diagnostics,
        malformed,
        resource_failure,
    }
}

pub(crate) fn resource_limited(
    tokens: Vec<Token>,
    lexical_diagnostics: Vec<Diagnostic<LexReason>>,
    parse_diagnostics: Vec<ParseDiagnostic>,
    resource_failure: ResourceFailure,
) -> ConcreteTree {
    ConcreteTree {
        root: None,
        tokens,
        events: Vec::new(),
        lexical_diagnostics,
        parse_diagnostics,
        malformed: None,
        resource_failure: Some(resource_failure),
    }
}

#[cfg(test)]
mod tests {
    use crate::{lexer::lex, source::SourceFile};

    use super::*;

    fn tokens(text: &str) -> Vec<Token> {
        let source = SourceFile::new("events.ash", text).expect("the event fixture should fit");
        lex(&source).expect("the event fixture should lex").tokens
    }

    fn malformed(tokens: Vec<Token>, events: Vec<Event>) -> Option<InternalReason> {
        build(tokens, Vec::new(), Vec::new(), events, None).malformed
    }

    #[test]
    fn event_builder_rejects_unexpected_finish_and_unclosed_nodes() {
        assert_eq!(
            malformed(Vec::new(), vec![Event::Finish]),
            Some(InternalReason::UnexpectedFinish)
        );
        assert_eq!(
            malformed(Vec::new(), vec![Event::Start(NodeKind::Module)]),
            Some(InternalReason::UnclosedNode)
        );
    }

    #[test]
    fn event_builder_rejects_no_root_and_multiple_roots() {
        assert_eq!(
            malformed(Vec::new(), Vec::new()),
            Some(InternalReason::InvalidRootCount)
        );
        assert_eq!(
            malformed(
                Vec::new(),
                vec![
                    Event::Start(NodeKind::Module),
                    Event::Finish,
                    Event::Start(NodeKind::Module),
                    Event::Finish,
                ],
            ),
            Some(InternalReason::InvalidRootCount)
        );
    }

    #[test]
    fn event_builder_rejects_out_of_range_duplicate_missing_and_out_of_order_tokens() {
        assert_eq!(
            malformed(
                Vec::new(),
                vec![
                    Event::Start(NodeKind::Module),
                    Event::Token(0),
                    Event::Finish,
                ],
            ),
            Some(InternalReason::TokenOutOfRange)
        );
        assert_eq!(
            malformed(
                tokens(""),
                vec![
                    Event::Start(NodeKind::Module),
                    Event::Token(0),
                    Event::Token(0),
                    Event::Finish,
                ],
            ),
            Some(InternalReason::DuplicateToken)
        );
        assert_eq!(
            malformed(
                tokens("1"),
                vec![
                    Event::Start(NodeKind::Module),
                    Event::Token(0),
                    Event::Finish,
                ],
            ),
            Some(InternalReason::MissingToken)
        );
        assert_eq!(
            malformed(
                tokens("1"),
                vec![
                    Event::Start(NodeKind::Module),
                    Event::Token(1),
                    Event::Token(0),
                    Event::Finish,
                ],
            ),
            Some(InternalReason::TokenOutOfOrder)
        );
    }

    #[test]
    fn deeply_malformed_concrete_nodes_drop_iteratively() {
        std::thread::scope(|scope| {
            std::thread::Builder::new()
                .stack_size(64 * 1024)
                .spawn_scoped(scope, || {
                    let mut node = ConcreteNode {
                        kind: NodeKind::Module,
                        children: Vec::new(),
                    };
                    for _ in 0..4_096 {
                        node = ConcreteNode {
                            kind: NodeKind::PrimaryExpression,
                            children: vec![ConcreteElement::Node(node)],
                        };
                    }
                    drop(node);
                })
                .expect("the small-stack drop test should start")
                .join()
                .expect("iterative concrete drop should not overflow");
        });
    }
}
