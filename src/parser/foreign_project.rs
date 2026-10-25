//! Complete shape validation and passive foreign declaration projection.
use super::*;
use crate::surface::*;
fn word(shape: &mut ShapeCursor<'_>, expected: &str) -> Result<(), ProjectionError> {
    shape.token_matching(|kind| matches!(kind, TokenKind::Identifier(found) if found == expected))
}
fn upper(shape: &mut ShapeCursor<'_>) -> Result<(), ProjectionError> {
    shape.token_matching(|kind| matches!(kind, TokenKind::UpperIdentifier(_)))
}
fn head_word<'a>(node: &'a ConcreteNode, tokens: &'a [Token]) -> Result<&'a str, ProjectionError> {
    match node.children.first() {
        Some(ConcreteElement::Token(index)) => match &tokens
            .get(*index)
            .ok_or(ProjectionError::MalformedTree(
                InternalReason::TokenOutOfRange,
            ))?
            .kind
        {
            TokenKind::Identifier(word) => Ok(word),
            _ => malformed(InternalReason::UnexpectedShape),
        },
        _ => malformed(InternalReason::UnexpectedShape),
    }
}
fn first_name(node: &ConcreteNode, tokens: &[Token]) -> Result<SurfaceName, ProjectionError> {
    direct_tokens(node, tokens)
        .find(|token| matches!(token.kind, TokenKind::UpperIdentifier(_)))
        .map(surface_name)
        .transpose()?
        .ok_or(ProjectionError::MalformedTree(
            InternalReason::UnexpectedShape,
        ))
}
fn literal_string(
    node: &ConcreteNode,
    tokens: &[Token],
) -> Result<SurfaceForeignString, ProjectionError> {
    for token in direct_tokens(node, tokens) {
        if let TokenKind::StringLiteral(value) = &token.kind {
            return Ok(SurfaceForeignString {
                value: value.clone(),
                span: token.span,
            });
        }
    }
    malformed(InternalReason::UnexpectedShape)
}
pub(super) fn validate_shape(node: &ConcreteNode, tokens: &[Token]) -> Result<(), ProjectionError> {
    let mut shape = ShapeCursor::new(node, tokens);
    match node.kind {
        NodeKind::ForeignLibrary => {
            shape.optional_token(&TokenKind::Pub)?;
            word(&mut shape, "foreign")?;
            word(&mut shape, "library")?;
            upper(&mut shape)?;
            shape.token(&TokenKind::LeftBrace)?;
            shape.token(&TokenKind::LineEnd)?;
            shape.node(NodeKind::ForeignMember)?;
            while shape.peek_token_is(&TokenKind::LineEnd) {
                shape.token(&TokenKind::LineEnd)?;
                if shape.peek_node_is(NodeKind::ForeignMember) {
                    shape.node(NodeKind::ForeignMember)?;
                } else {
                    break;
                }
            }
            shape.token(&TokenKind::RightBrace)?;
        }
        NodeKind::ForeignMember => match head_word(node, tokens)? {
            "profile" => {
                word(&mut shape, "profile")?;
                shape.token_matching(|kind| matches!(kind, TokenKind::StringLiteral(_)))?;
            }
            "symbol" => {
                word(&mut shape, "symbol")?;
                upper(&mut shape)?;
                shape.token(&TokenKind::Colon)?;
                shape.node(NodeKind::Type)?;
                shape.token(&TokenKind::LeftBrace)?;
                shape.optional_token(&TokenKind::LineEnd)?;
                word(&mut shape, "name")?;
                shape.token_matching(|kind| matches!(kind, TokenKind::StringLiteral(_)))?;
                shape.optional_token(&TokenKind::LineEnd)?;
                shape.token(&TokenKind::RightBrace)?;
            }
            _ => return malformed(InternalReason::UnexpectedShape),
        },
        _ => return malformed(InternalReason::UnexpectedShape),
    }
    shape.finish()
}
pub(super) fn library(
    source: &SourceFile,
    node: &ConcreteNode,
    tokens: &[Token],
) -> Result<SurfaceForeignLibrary, ProjectionError> {
    require_kind(node, NodeKind::ForeignLibrary)?;
    Ok(SurfaceForeignLibrary {
        public: direct_tokens(node, tokens).any(|t| t.kind == TokenKind::Pub),
        name: first_name(node, tokens)?,
        members: child_nodes(node)
            .map(|node| member(source, node, tokens))
            .collect::<Result<Vec<_>, _>>()?,
        span: node_span(source, node, tokens)?,
    })
}
fn member(
    source: &SourceFile,
    node: &ConcreteNode,
    tokens: &[Token],
) -> Result<SurfaceForeignMember, ProjectionError> {
    require_kind(node, NodeKind::ForeignMember)?;
    let span = node_span(source, node, tokens)?;
    Ok(match head_word(node, tokens)? {
        "profile" => SurfaceForeignMember::Profile(SurfaceForeignProfile {
            target: literal_string(node, tokens)?,
            span,
        }),
        "symbol" => SurfaceForeignMember::Symbol(Box::new(SurfaceForeignSymbol {
            name: first_name(node, tokens)?,
            ty: project_type(source, only_child_of_kind(node, NodeKind::Type)?, tokens)?,
            native_name: literal_string(node, tokens)?,
            span,
        })),
        _ => return malformed(InternalReason::UnexpectedShape),
    })
}
