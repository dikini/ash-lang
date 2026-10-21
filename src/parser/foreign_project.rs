//! Strict concrete-shape checking and explicit foreign contract projection.

use super::*;
use crate::surface::*;

fn word(shape: &mut ShapeCursor<'_>, expected: &str) -> Result<(), ProjectionError> {
    shape.token_matching(|kind| matches!(kind, TokenKind::Identifier(found) if found == expected))
}

fn words(shape: &mut ShapeCursor<'_>, choices: &[&str]) -> Result<(), ProjectionError> {
    shape.token_matching(
        |kind| matches!(kind, TokenKind::Identifier(found) if choices.contains(&found.as_str())),
    )
}

fn upper(shape: &mut ShapeCursor<'_>) -> Result<(), ProjectionError> {
    shape.token_matching(|kind| matches!(kind, TokenKind::UpperIdentifier(_)))
}

fn at_word(shape: &ShapeCursor<'_>, expected: &str) -> bool {
    matches!(shape.children.get(shape.position), Some(ConcreteElement::Token(index))
        if shape.tokens.get(*index).is_some_and(|token| matches!(&token.kind, TokenKind::Identifier(word) if word == expected)))
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

fn optional_parameters(shape: &mut ShapeCursor<'_>) -> Result<(), ProjectionError> {
    if shape.peek_node_is(NodeKind::TypeParameters) {
        shape.node(NodeKind::TypeParameters)?;
    }
    Ok(())
}

fn list(shape: &mut ShapeCursor<'_>, kind: NodeKind) -> Result<(), ProjectionError> {
    shape.node(kind)?;
    while shape.peek_token_is(&TokenKind::Comma) {
        shape.token(&TokenKind::Comma)?;
        shape.node(kind)?;
    }
    Ok(())
}

fn closing(shape: &mut ShapeCursor<'_>) -> Result<(), ProjectionError> {
    shape.optional_token(&TokenKind::LineEnd)?;
    shape.token(&TokenKind::RightBrace)
}

pub(super) fn validate_shape(node: &ConcreteNode, tokens: &[Token]) -> Result<(), ProjectionError> {
    let mut shape = ShapeCursor::new(node, tokens);
    match node.kind {
        NodeKind::ForeignLibrary => {
            shape.optional_token(&TokenKind::Pub)?;
            word(&mut shape, "foreign")?;
            if at_word(&shape, "checked") {
                word(&mut shape, "checked")?;
            }
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
        NodeKind::ForeignMember => {
            let role = head_word(node, tokens)?;
            word(&mut shape, role)?;
            match role {
                "profile" => {
                    shape.token_matching(|kind| matches!(kind, TokenKind::StringLiteral(_)))?
                }
                "assumption" => {
                    upper(&mut shape)?;
                    shape.token_matching(|kind| matches!(kind, TokenKind::StringLiteral(_)))?;
                }
                "repr" => {
                    upper(&mut shape)?;
                    shape.token(&TokenKind::Equal)?;
                    shape.node(NodeKind::ForeignRepresentation)?;
                }
                "const" | "sentinel" => {
                    upper(&mut shape)?;
                    shape.token(&TokenKind::Colon)?;
                    shape.node(NodeKind::ForeignReference)?;
                    shape.token(&TokenKind::Equal)?;
                    if role == "const" {
                        shape.node(NodeKind::ForeignInteger)?;
                    } else {
                        word(&mut shape, "all_bits_one")?;
                    }
                }
                "owner" => {
                    upper(&mut shape)?;
                    shape.node(NodeKind::TypeParameters)?;
                    shape.token(&TokenKind::LeftBrace)?;
                    shape.token(&TokenKind::LineEnd)?;
                    word(&mut shape, "representation")?;
                    shape.node(NodeKind::ForeignReference)?;
                    shape.token(&TokenKind::LineEnd)?;
                    word(&mut shape, "owned")?;
                    upper(&mut shape)?;
                    shape.token(&TokenKind::LineEnd)?;
                    while at_word(&shape, "host") {
                        word(&mut shape, "host")?;
                        upper(&mut shape)?;
                        shape.token(&TokenKind::LineEnd)?;
                    }
                    if at_word(&shape, "retains") {
                        word(&mut shape, "retains")?;
                        upper(&mut shape)?;
                        while shape.peek_token_is(&TokenKind::Comma) {
                            shape.token(&TokenKind::Comma)?;
                            upper(&mut shape)?;
                        }
                        shape.token(&TokenKind::LineEnd)?;
                    }
                    word(&mut shape, "teardown")?;
                    shape.node(NodeKind::ForeignReference)?;
                    closing(&mut shape)?;
                }
                "access" => {
                    upper(&mut shape)?;
                    shape.node(NodeKind::TypeParameters)?;
                    shape.token(&TokenKind::LeftBrace)?;
                    shape.token(&TokenKind::LineEnd)?;
                    word(&mut shape, "window")?;
                    upper(&mut shape)?;
                    shape.token(&TokenKind::LineEnd)?;
                    word(&mut shape, "owner")?;
                    shape.node(NodeKind::Type)?;
                    shape.token(&TokenKind::LineEnd)?;
                    word(&mut shape, "extent")?;
                    words(&mut shape, &["bytes", "nul"])?;
                    shape.token(&TokenKind::LineEnd)?;
                    word(&mut shape, "preserves")?;
                    list(&mut shape, NodeKind::ForeignReference)?;
                    closing(&mut shape)?;
                }
                "symbol" => {
                    upper(&mut shape)?;
                    optional_parameters(&mut shape)?;
                    shape.token(&TokenKind::Colon)?;
                    shape.node(NodeKind::Type)?;
                    shape.token(&TokenKind::LeftBrace)?;
                    shape.token(&TokenKind::LineEnd)?;
                    word(&mut shape, "name")?;
                    shape.token_matching(|kind| matches!(kind, TokenKind::StringLiteral(_)))?;
                    shape.token(&TokenKind::LineEnd)?;
                    word(&mut shape, "abi")?;
                    shape.token(&TokenKind::LeftParen)?;
                    if shape.peek_node_is(NodeKind::ForeignAbiOperand) {
                        list(&mut shape, NodeKind::ForeignAbiOperand)?;
                    }
                    shape.token(&TokenKind::RightParen)?;
                    shape.token(&TokenKind::Arrow)?;
                    shape.node(NodeKind::ForeignAbiRepresentation)?;
                    shape.token(&TokenKind::LineEnd)?;
                    shape.node(NodeKind::ForeignCallContract)?;
                    while shape.peek_token_is(&TokenKind::LineEnd) {
                        shape.token(&TokenKind::LineEnd)?;
                        if shape.peek_node_is(NodeKind::ForeignCallContract) {
                            shape.node(NodeKind::ForeignCallContract)?;
                        } else {
                            break;
                        }
                    }
                    shape.token(&TokenKind::RightBrace)?;
                }
                _ => return malformed(InternalReason::UnexpectedShape),
            }
        }
        NodeKind::ForeignInteger => {
            shape.optional_token(&TokenKind::Minus)?;
            shape.token_matching(|kind| matches!(kind, TokenKind::Integer(_)))?;
        }
        NodeKind::ForeignReference => {
            upper(&mut shape)?;
            if shape.peek_token_is(&TokenKind::Dot) {
                shape.token(&TokenKind::Dot)?;
                upper(&mut shape)?;
            }
        }
        NodeKind::ForeignRepresentation => {
            if shape.peek_token_is(&TokenKind::Opaque) {
                shape.token(&TokenKind::Opaque)?;
            } else if at_word(&shape, "signed") || at_word(&shape, "unsigned") {
                words(&mut shape, &["signed", "unsigned"])?;
                shape.token(&TokenKind::LeftParen)?;
                shape.node(NodeKind::ForeignInteger)?;
                shape.token(&TokenKind::RightParen)?;
            } else {
                words(&mut shape, &["size_t", "bytes", "function_address"])?;
            }
        }
        NodeKind::ForeignSourcePosition => {
            shape.node(NodeKind::ForeignInteger)?;
            while shape.peek_token_is(&TokenKind::Dot) {
                shape.token(&TokenKind::Dot)?;
                shape.node(NodeKind::ForeignInteger)?;
            }
        }
        NodeKind::ForeignNativePosition => {
            if at_word(&shape, "result") {
                word(&mut shape, "result")?;
            } else {
                shape.node(NodeKind::ForeignInteger)?;
            }
        }
        NodeKind::ForeignAbiOperand => {
            if at_word(&shape, "out") {
                word(&mut shape, "out")?;
                shape.token(&TokenKind::LeftParen)?;
                shape.node(NodeKind::ForeignAbiRepresentation)?;
                shape.token(&TokenKind::RightParen)?;
            } else {
                shape.node(NodeKind::ForeignAbiRepresentation)?;
            }
        }
        NodeKind::ForeignAbiRepresentation => {
            if at_word(&shape, "void") {
                word(&mut shape, "void")?;
            } else if at_word(&shape, "pointer") {
                word(&mut shape, "pointer")?;
                shape.token(&TokenKind::LeftParen)?;
                shape.node(NodeKind::ForeignReference)?;
                shape.token(&TokenKind::RightParen)?;
            } else {
                shape.node(NodeKind::ForeignReference)?;
            }
        }
        NodeKind::ForeignCallContract => {
            let role = head_word(node, tokens)?;
            word(&mut shape, role)?;
            match role {
                "host" => upper(&mut shape)?,
                "assumes" => {
                    shape.token(&TokenKind::LeftBrace)?;
                    if shape.peek_node_is(NodeKind::ForeignReference) {
                        list(&mut shape, NodeKind::ForeignReference)?;
                    }
                    shape.token(&TokenKind::RightBrace)?;
                }
                "destruction_operand" => {
                    shape.node(NodeKind::ForeignNativePosition)?;
                    word(&mut shape, "from")?;
                    shape.node(NodeKind::ForeignSourcePosition)?;
                    word(&mut shape, "scalar")?;
                }
                "operand" => {
                    shape.node(NodeKind::ForeignNativePosition)?;
                    word(&mut shape, "from")?;
                    if at_word(&shape, "constant") {
                        word(&mut shape, "constant")?;
                        shape.node(NodeKind::ForeignReference)?;
                    } else if at_word(&shape, "null") {
                        word(&mut shape, "null")?;
                    } else {
                        shape.node(NodeKind::ForeignSourcePosition)?;
                        shape.node(NodeKind::ForeignOperandRole)?;
                    }
                }
                "output" => {
                    shape.node(NodeKind::ForeignNativePosition)?;
                    shape.token(&TokenKind::As)?;
                    shape.node(NodeKind::ForeignOutputRole)?;
                }
                "outcome" => {
                    shape.node(NodeKind::ForeignOutcomeTest)?;
                    shape.token(&TokenKind::LeftBrace)?;
                    if shape.peek_node_is(NodeKind::ForeignOutcomeFact) {
                        list(&mut shape, NodeKind::ForeignOutcomeFact)?;
                    }
                    shape.token(&TokenKind::RightBrace)?;
                }
                "retained_dependents" => word(&mut shape, "block")?,
                _ => return malformed(InternalReason::UnexpectedShape),
            }
        }
        NodeKind::ForeignInputDiscipline => words(&mut shape, &["call_borrow", "copy"])?,
        NodeKind::ForeignOperandRole => {
            let role = head_word(node, tokens)?;
            word(&mut shape, role)?;
            match role {
                "bytes" => {
                    shape.token(&TokenKind::LeftParen)?;
                    shape.node(NodeKind::ForeignSourcePosition)?;
                    shape.token(&TokenKind::RightParen)?;
                    shape.node(NodeKind::ForeignInputDiscipline)?;
                }
                "nul" => shape.node(NodeKind::ForeignInputDiscipline)?,
                "scalar" | "current" | "enclosing" | "view" | "sentinel" => {}
                _ => return malformed(InternalReason::UnexpectedShape),
            }
        }
        NodeKind::ForeignOutputRole => {
            let role = head_word(node, tokens)?;
            word(&mut shape, role)?;
            match role {
                "scalar" => {}
                "owner" | "view" => {
                    shape.token(&TokenKind::LeftParen)?;
                    shape.node(NodeKind::Type)?;
                    if role == "view" && shape.peek_token_is(&TokenKind::Comma) {
                        shape.token(&TokenKind::Comma)?;
                        list(&mut shape, NodeKind::ForeignSourcePosition)?;
                    }
                    shape.token(&TokenKind::RightParen)?;
                }
                "extent_of" | "offset_into" => {
                    shape.token(&TokenKind::LeftParen)?;
                    shape.node(NodeKind::ForeignSourcePosition)?;
                    if role == "extent_of" {
                        while shape.peek_token_is(&TokenKind::Comma) {
                            shape.token(&TokenKind::Comma)?;
                            shape.node(NodeKind::ForeignSourcePosition)?;
                        }
                    }
                    shape.token(&TokenKind::RightParen)?;
                }
                _ => return malformed(InternalReason::UnexpectedShape),
            }
        }
        NodeKind::ForeignOutcomeTest => {
            if at_word(&shape, "otherwise") {
                word(&mut shape, "otherwise")?;
            } else {
                shape.node(NodeKind::ForeignOutcomeAtom)?;
                while shape.peek_token_is(&TokenKind::And) {
                    shape.token(&TokenKind::And)?;
                    shape.node(NodeKind::ForeignOutcomeAtom)?;
                }
            }
        }
        NodeKind::ForeignOutcomeAtom => {
            shape.node(NodeKind::ForeignNativePosition)?;
            if shape.peek_token_is(&TokenKind::EqualEqual) {
                shape.token(&TokenKind::EqualEqual)?;
                shape.node(NodeKind::ForeignReference)?;
            } else {
                words(&mut shape, &["null", "nonnull"])?;
            }
        }
        NodeKind::ForeignOutcomeFact => {
            let role = head_word(node, tokens)?;
            word(&mut shape, role)?;
            match role {
                "readable" | "unreadable" => shape.node(NodeKind::ForeignNativePosition)?,
                "consumed" | "retained" => shape.node(NodeKind::ForeignSourcePosition)?,
                "initialized_bytes" => {
                    shape.node(NodeKind::ForeignNativePosition)?;
                    word(&mut shape, "from")?;
                    shape.node(NodeKind::ForeignSourcePosition)?;
                }
                _ => return malformed(InternalReason::UnexpectedShape),
            }
        }
        _ => return malformed(InternalReason::UnexpectedShape),
    }
    shape.finish()
}

fn named_tokens(
    node: &ConcreteNode,
    tokens: &[Token],
) -> Result<Vec<SurfaceName>, ProjectionError> {
    direct_tokens(node, tokens)
        .filter(|token| matches!(token.kind, TokenKind::UpperIdentifier(_)))
        .map(surface_name)
        .collect()
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

fn keyword_span(
    node: &ConcreteNode,
    tokens: &[Token],
    word: &str,
) -> Result<Span, ProjectionError> {
    direct_tokens(node, tokens)
        .find(|token| matches!(&token.kind, TokenKind::Identifier(found) if found == word))
        .map(|token| token.span)
        .ok_or(ProjectionError::MalformedTree(
            InternalReason::UnexpectedShape,
        ))
}

fn integer(
    source: &SourceFile,
    node: &ConcreteNode,
    tokens: &[Token],
) -> Result<SurfaceForeignInteger, ProjectionError> {
    require_kind(node, NodeKind::ForeignInteger)?;
    let magnitude = direct_tokens(node, tokens)
        .find_map(|token| match &token.kind {
            TokenKind::Integer(value) => Some(value.clone()),
            _ => None,
        })
        .ok_or(ProjectionError::MalformedTree(
            InternalReason::UnexpectedShape,
        ))?;
    Ok(SurfaceForeignInteger {
        negative: direct_tokens(node, tokens).any(|token| token.kind == TokenKind::Minus),
        magnitude,
        span: node_span(source, node, tokens)?,
    })
}

fn reference(
    source: &SourceFile,
    node: &ConcreteNode,
    tokens: &[Token],
) -> Result<SurfaceForeignReference, ProjectionError> {
    require_kind(node, NodeKind::ForeignReference)?;
    let mut names = named_tokens(node, tokens)?.into_iter();
    let first = names.next().ok_or(ProjectionError::MalformedTree(
        InternalReason::UnexpectedShape,
    ))?;
    let (module, name) = if let Some(second) = names.next() {
        (Some(first), second)
    } else {
        (None, first)
    };
    if names.next().is_some() {
        return malformed(InternalReason::UnexpectedShape);
    }
    Ok(SurfaceForeignReference {
        module,
        name,
        span: node_span(source, node, tokens)?,
    })
}

fn position(
    source: &SourceFile,
    node: &ConcreteNode,
    tokens: &[Token],
) -> Result<SurfaceForeignSourcePosition, ProjectionError> {
    require_kind(node, NodeKind::ForeignSourcePosition)?;
    let components = child_nodes(node)
        .map(|child| integer(source, child, tokens))
        .collect::<Result<Vec<_>, _>>()?;
    Ok(SurfaceForeignSourcePosition {
        components,
        span: node_span(source, node, tokens)?,
    })
}

fn native_position(
    source: &SourceFile,
    node: &ConcreteNode,
    tokens: &[Token],
) -> Result<SurfaceForeignNativePosition, ProjectionError> {
    require_kind(node, NodeKind::ForeignNativePosition)?;
    if let Some(child) = optional_child_of_kind(node, NodeKind::ForeignInteger)? {
        Ok(SurfaceForeignNativePosition::Argument(integer(
            source, child, tokens,
        )?))
    } else {
        Ok(SurfaceForeignNativePosition::Result(keyword_span(
            node, tokens, "result",
        )?))
    }
}

fn representation(
    source: &SourceFile,
    node: &ConcreteNode,
    tokens: &[Token],
) -> Result<SurfaceForeignRepresentation, ProjectionError> {
    require_kind(node, NodeKind::ForeignRepresentation)?;
    let span = node_span(source, node, tokens)?;
    if direct_tokens(node, tokens).any(|token| token.kind == TokenKind::Opaque) {
        return Ok(SurfaceForeignRepresentation::Opaque(span));
    }
    Ok(match head_word(node, tokens)? {
        "signed" => SurfaceForeignRepresentation::Signed(integer(
            source,
            only_child_of_kind(node, NodeKind::ForeignInteger)?,
            tokens,
        )?),
        "unsigned" => SurfaceForeignRepresentation::Unsigned(integer(
            source,
            only_child_of_kind(node, NodeKind::ForeignInteger)?,
            tokens,
        )?),
        "size_t" => SurfaceForeignRepresentation::SizeT(span),
        "bytes" => SurfaceForeignRepresentation::Bytes(span),
        "function_address" => SurfaceForeignRepresentation::FunctionAddress(span),
        _ => return malformed(InternalReason::UnexpectedShape),
    })
}

fn abi_representation(
    source: &SourceFile,
    node: &ConcreteNode,
    tokens: &[Token],
) -> Result<SurfaceForeignAbiRepresentation, ProjectionError> {
    require_kind(node, NodeKind::ForeignAbiRepresentation)?;
    let span = node_span(source, node, tokens)?;
    if let Some(reference_node) = optional_child_of_kind(node, NodeKind::ForeignReference)? {
        let representation = reference(source, reference_node, tokens)?;
        if direct_tokens(node, tokens).next().is_some() {
            Ok(SurfaceForeignAbiRepresentation::Pointer {
                representation,
                span,
            })
        } else {
            Ok(SurfaceForeignAbiRepresentation::Member(representation))
        }
    } else {
        Ok(SurfaceForeignAbiRepresentation::Void(span))
    }
}

pub(super) fn library(
    source: &SourceFile,
    node: &ConcreteNode,
    tokens: &[Token],
) -> Result<SurfaceForeignLibrary, ProjectionError> {
    require_kind(node, NodeKind::ForeignLibrary)?;
    Ok(SurfaceForeignLibrary {
        public: direct_tokens(node, tokens).any(|token| token.kind == TokenKind::Pub),
        checked: direct_tokens(node, tokens)
            .find(|token| matches!(&token.kind, TokenKind::Identifier(word) if word == "checked"))
            .map(|token| token.span),
        name: first_name(node, tokens)?,
        members: child_nodes(node)
            .map(|child| member(source, child, tokens))
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
    let role = head_word(node, tokens)?;
    if role == "profile" {
        return Ok(SurfaceForeignMember::Profile(SurfaceForeignProfile {
            target: literal_string(node, tokens)?,
            span,
        }));
    }
    let name = first_name(node, tokens)?;
    Ok(match role {
        "assumption" => SurfaceForeignMember::Assumption(SurfaceForeignAssumption {
            name,
            description: literal_string(node, tokens)?,
            span,
        }),
        "repr" => SurfaceForeignMember::Representation(SurfaceForeignRepresentationDeclaration {
            name,
            representation: representation(
                source,
                only_child_of_kind(node, NodeKind::ForeignRepresentation)?,
                tokens,
            )?,
            span,
        }),
        "const" => SurfaceForeignMember::Constant(SurfaceForeignConstant {
            name,
            representation: reference(
                source,
                only_child_of_kind(node, NodeKind::ForeignReference)?,
                tokens,
            )?,
            value: integer(
                source,
                only_child_of_kind(node, NodeKind::ForeignInteger)?,
                tokens,
            )?,
            span,
        }),
        "sentinel" => SurfaceForeignMember::Sentinel(SurfaceForeignSentinel {
            name,
            representation: reference(
                source,
                only_child_of_kind(node, NodeKind::ForeignReference)?,
                tokens,
            )?,
            bits: keyword_span(node, tokens, "all_bits_one")?,
            span,
        }),
        "owner" => {
            let mut names = named_tokens(node, tokens)?.into_iter();
            let _ = names.next();
            let owned = names.next().ok_or(ProjectionError::MalformedTree(
                InternalReason::UnexpectedShape,
            ))?;
            let host_count = direct_tokens(node, tokens)
                .filter(
                    |token| matches!(&token.kind, TokenKind::Identifier(word) if word == "host"),
                )
                .count();
            let host_bindings = names.by_ref().take(host_count).collect();
            let references = child_nodes(node)
                .filter(|child| child.kind == NodeKind::ForeignReference)
                .collect::<Vec<_>>();
            let [repr, teardown] = references.as_slice() else {
                return malformed(InternalReason::UnexpectedShape);
            };
            SurfaceForeignMember::Owner(Box::new(SurfaceForeignOwner {
                name,
                host_bindings,
                parameters: project_optional_type_parameters(source, node, tokens)?
                    .unwrap_or_default(),
                representation: reference(source, repr, tokens)?,
                owned,
                retains: names.collect(),
                teardown: reference(source, teardown, tokens)?,
                span,
            }))
        }
        "access" => {
            let window = named_tokens(node, tokens)?.into_iter().nth(1).ok_or(
                ProjectionError::MalformedTree(InternalReason::UnexpectedShape),
            )?;
            let extent = if let Ok(span) = keyword_span(node, tokens, "bytes") {
                SurfaceForeignExtent::Bytes(span)
            } else {
                SurfaceForeignExtent::Nul(keyword_span(node, tokens, "nul")?)
            };
            SurfaceForeignMember::Access(Box::new(SurfaceForeignAccess {
                name,
                parameters: project_optional_type_parameters(source, node, tokens)?
                    .unwrap_or_default(),
                window,
                owner: project_type(source, only_child_of_kind(node, NodeKind::Type)?, tokens)?,
                extent,
                preserves: child_nodes(node)
                    .filter(|child| child.kind == NodeKind::ForeignReference)
                    .map(|child| reference(source, child, tokens))
                    .collect::<Result<Vec<_>, _>>()?,
                span,
            }))
        }
        "symbol" => {
            let mut host_bindings = Vec::new();
            let mut assumption_sets = Vec::new();
            let mut contracts = Vec::new();
            for child in
                child_nodes(node).filter(|child| child.kind == NodeKind::ForeignCallContract)
            {
                match head_word(child, tokens)? {
                    "host" => host_bindings.push(first_name(child, tokens)?),
                    "assumes" => assumption_sets.push(SurfaceForeignAssumptionSet {
                        references: child_nodes(child)
                            .map(|reference_node| reference(source, reference_node, tokens))
                            .collect::<Result<Vec<_>, _>>()?,
                        span: node_span(source, child, tokens)?,
                    }),
                    _ => contracts.push(contract(source, child, tokens)?),
                }
            }
            SurfaceForeignMember::Symbol(Box::new(SurfaceForeignSymbol {
                name,
                host_bindings,
                assumption_sets,
                parameters: project_optional_type_parameters(source, node, tokens)?
                    .unwrap_or_default(),
                ty: project_type(source, only_child_of_kind(node, NodeKind::Type)?, tokens)?,
                native_name: literal_string(node, tokens)?,
                abi_operands: child_nodes(node)
                    .filter(|child| child.kind == NodeKind::ForeignAbiOperand)
                    .map(|child| {
                        Ok(SurfaceForeignAbiOperand {
                            output: direct_tokens(child, tokens).next().is_some(),
                            representation: abi_representation(
                                source,
                                only_child_of_kind(child, NodeKind::ForeignAbiRepresentation)?,
                                tokens,
                            )?,
                            span: node_span(source, child, tokens)?,
                        })
                    })
                    .collect::<Result<Vec<_>, ProjectionError>>()?,
                abi_result: abi_representation(
                    source,
                    only_child_of_kind(node, NodeKind::ForeignAbiRepresentation)?,
                    tokens,
                )?,
                contracts,
                span,
            }))
        }
        _ => return malformed(InternalReason::UnexpectedShape),
    })
}

fn discipline(
    node: &ConcreteNode,
    tokens: &[Token],
) -> Result<SurfaceForeignInputDiscipline, ProjectionError> {
    let token = only_direct_token(node, tokens)?;
    match &token.kind {
        TokenKind::Identifier(word) if word == "call_borrow" => {
            Ok(SurfaceForeignInputDiscipline::CallBorrow(token.span))
        }
        TokenKind::Identifier(word) if word == "copy" => {
            Ok(SurfaceForeignInputDiscipline::Copy(token.span))
        }
        _ => malformed(InternalReason::UnexpectedShape),
    }
}

fn operand_role(
    source: &SourceFile,
    node: &ConcreteNode,
    tokens: &[Token],
) -> Result<SurfaceForeignOperandRole, ProjectionError> {
    let kind = match head_word(node, tokens)? {
        "scalar" => SurfaceForeignOperandRoleKind::Scalar,
        "current" => SurfaceForeignOperandRoleKind::Current,
        "enclosing" => SurfaceForeignOperandRoleKind::Enclosing,
        "view" => SurfaceForeignOperandRoleKind::View,
        "sentinel" => SurfaceForeignOperandRoleKind::Sentinel,
        "nul" => SurfaceForeignOperandRoleKind::Nul(discipline(
            only_child_of_kind(node, NodeKind::ForeignInputDiscipline)?,
            tokens,
        )?),
        "bytes" => SurfaceForeignOperandRoleKind::Bytes {
            extent: position(
                source,
                only_child_of_kind(node, NodeKind::ForeignSourcePosition)?,
                tokens,
            )?,
            discipline: discipline(
                only_child_of_kind(node, NodeKind::ForeignInputDiscipline)?,
                tokens,
            )?,
        },
        _ => return malformed(InternalReason::UnexpectedShape),
    };
    Ok(SurfaceForeignOperandRole {
        kind,
        span: node_span(source, node, tokens)?,
    })
}

fn output_role(
    source: &SourceFile,
    node: &ConcreteNode,
    tokens: &[Token],
) -> Result<SurfaceForeignOutputRole, ProjectionError> {
    let source_positions = || {
        child_nodes(node)
            .filter(|child| child.kind == NodeKind::ForeignSourcePosition)
            .map(|child| position(source, child, tokens))
            .collect::<Result<Vec<_>, _>>()
    };
    let kind = match head_word(node, tokens)? {
        "scalar" => SurfaceForeignOutputRoleKind::Scalar,
        "owner" => SurfaceForeignOutputRoleKind::Owner(project_type(
            source,
            only_child_of_kind(node, NodeKind::Type)?,
            tokens,
        )?),
        "view" => SurfaceForeignOutputRoleKind::View {
            ty: project_type(source, only_child_of_kind(node, NodeKind::Type)?, tokens)?,
            keys: source_positions()?,
        },
        "extent_of" => {
            let mut positions = source_positions()?.into_iter();
            let view = positions.next().ok_or(ProjectionError::MalformedTree(
                InternalReason::UnexpectedShape,
            ))?;
            SurfaceForeignOutputRoleKind::ExtentOf {
                view,
                keys: positions.collect(),
            }
        }
        "offset_into" => SurfaceForeignOutputRoleKind::OffsetInto(position(
            source,
            only_child_of_kind(node, NodeKind::ForeignSourcePosition)?,
            tokens,
        )?),
        _ => return malformed(InternalReason::UnexpectedShape),
    };
    Ok(SurfaceForeignOutputRole {
        kind,
        span: node_span(source, node, tokens)?,
    })
}

fn outcome_test(
    source: &SourceFile,
    node: &ConcreteNode,
    tokens: &[Token],
) -> Result<SurfaceForeignOutcomeTest, ProjectionError> {
    if let Ok(span) = keyword_span(node, tokens, "otherwise") {
        return Ok(SurfaceForeignOutcomeTest::Otherwise(span));
    }
    Ok(SurfaceForeignOutcomeTest::All(
        child_nodes(node)
            .map(|child| {
                let condition = if let Some(reference_node) =
                    optional_child_of_kind(child, NodeKind::ForeignReference)?
                {
                    SurfaceForeignOutcomeCondition::Equal(reference(
                        source,
                        reference_node,
                        tokens,
                    )?)
                } else if let Ok(span) = keyword_span(child, tokens, "null") {
                    SurfaceForeignOutcomeCondition::Null(span)
                } else {
                    SurfaceForeignOutcomeCondition::NonNull(keyword_span(child, tokens, "nonnull")?)
                };
                Ok(SurfaceForeignOutcomeAtom {
                    position: native_position(
                        source,
                        only_child_of_kind(child, NodeKind::ForeignNativePosition)?,
                        tokens,
                    )?,
                    condition,
                    span: node_span(source, child, tokens)?,
                })
            })
            .collect::<Result<Vec<_>, ProjectionError>>()?,
    ))
}

fn outcome_fact(
    source: &SourceFile,
    node: &ConcreteNode,
    tokens: &[Token],
) -> Result<SurfaceForeignOutcomeFact, ProjectionError> {
    let kind = match head_word(node, tokens)? {
        "readable" => SurfaceForeignOutcomeFactKind::Readable(native_position(
            source,
            only_child_of_kind(node, NodeKind::ForeignNativePosition)?,
            tokens,
        )?),
        "unreadable" => SurfaceForeignOutcomeFactKind::Unreadable(native_position(
            source,
            only_child_of_kind(node, NodeKind::ForeignNativePosition)?,
            tokens,
        )?),
        "consumed" => SurfaceForeignOutcomeFactKind::Consumed(position(
            source,
            only_child_of_kind(node, NodeKind::ForeignSourcePosition)?,
            tokens,
        )?),
        "retained" => SurfaceForeignOutcomeFactKind::Retained(position(
            source,
            only_child_of_kind(node, NodeKind::ForeignSourcePosition)?,
            tokens,
        )?),
        "initialized_bytes" => SurfaceForeignOutcomeFactKind::InitializedBytes {
            position: native_position(
                source,
                only_child_of_kind(node, NodeKind::ForeignNativePosition)?,
                tokens,
            )?,
            extent: position(
                source,
                only_child_of_kind(node, NodeKind::ForeignSourcePosition)?,
                tokens,
            )?,
        },
        _ => return malformed(InternalReason::UnexpectedShape),
    };
    Ok(SurfaceForeignOutcomeFact {
        kind,
        span: node_span(source, node, tokens)?,
    })
}

fn contract(
    source: &SourceFile,
    node: &ConcreteNode,
    tokens: &[Token],
) -> Result<SurfaceForeignContract, ProjectionError> {
    let span = node_span(source, node, tokens)?;
    Ok(match head_word(node, tokens)? {
        "destruction_operand" => SurfaceForeignContract::DestructionOperand {
            position: native_position(
                source,
                only_child_of_kind(node, NodeKind::ForeignNativePosition)?,
                tokens,
            )?,
            source: position(
                source,
                only_child_of_kind(node, NodeKind::ForeignSourcePosition)?,
                tokens,
            )?,
            span,
        },
        "operand" => {
            let operand_source =
                if let Some(ref_node) = optional_child_of_kind(node, NodeKind::ForeignReference)? {
                    SurfaceForeignOperandSource::Constant(reference(source, ref_node, tokens)?)
                } else if let Some(pos_node) =
                    optional_child_of_kind(node, NodeKind::ForeignSourcePosition)?
                {
                    SurfaceForeignOperandSource::Source {
                        position: position(source, pos_node, tokens)?,
                        role: operand_role(
                            source,
                            only_child_of_kind(node, NodeKind::ForeignOperandRole)?,
                            tokens,
                        )?,
                    }
                } else {
                    SurfaceForeignOperandSource::Null(keyword_span(node, tokens, "null")?)
                };
            SurfaceForeignContract::Operand {
                position: native_position(
                    source,
                    only_child_of_kind(node, NodeKind::ForeignNativePosition)?,
                    tokens,
                )?,
                source: operand_source,
                span,
            }
        }
        "output" => SurfaceForeignContract::Output {
            position: native_position(
                source,
                only_child_of_kind(node, NodeKind::ForeignNativePosition)?,
                tokens,
            )?,
            role: output_role(
                source,
                only_child_of_kind(node, NodeKind::ForeignOutputRole)?,
                tokens,
            )?,
            span,
        },
        "outcome" => SurfaceForeignContract::Outcome {
            test: outcome_test(
                source,
                only_child_of_kind(node, NodeKind::ForeignOutcomeTest)?,
                tokens,
            )?,
            facts: child_nodes(node)
                .filter(|child| child.kind == NodeKind::ForeignOutcomeFact)
                .map(|child| outcome_fact(source, child, tokens))
                .collect::<Result<Vec<_>, _>>()?,
            span,
        },
        "retained_dependents" => SurfaceForeignContract::RetainedDependentsBlock { span },
        _ => return malformed(InternalReason::UnexpectedShape),
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{lexer::lex, parser::parse};

    const SOURCE: &str = "foreign library Native {\n    profile \"x86_64-unknown-linux-gnu\"\n    repr CInt = signed(32)\n    symbol Abs : Int -> Int {\n        name \"abs\"\n        abi (CInt) -> CInt\n        operand 0 from 0 scalar\n        output result as scalar\n        outcome otherwise { readable result }\n    }\n}\n";

    fn find(node: &mut ConcreteNode, kind: NodeKind) -> Option<&mut ConcreteNode> {
        if node.kind == kind {
            return Some(node);
        }
        for child in &mut node.children {
            if let ConcreteElement::Node(child) = child
                && let Some(found) = find(child, kind)
            {
                return Some(found);
            }
        }
        None
    }

    #[test]
    fn projection_rejects_foreign_cst_role_transplants_with_complete_token_coverage() {
        for (actual, wrong) in [
            (
                NodeKind::ForeignSourcePosition,
                NodeKind::ForeignNativePosition,
            ),
            (
                NodeKind::ForeignOperandRole,
                NodeKind::ForeignInputDiscipline,
            ),
            (NodeKind::ForeignOutcomeFact, NodeKind::ForeignCallContract),
            (
                NodeKind::ForeignRepresentation,
                NodeKind::ForeignAbiRepresentation,
            ),
        ] {
            let source = SourceFile::new("foreign-shape.ash", SOURCE).unwrap();
            let mut tree = parse(lex(&source).unwrap());
            assert!(project_module(&source, &tree).is_ok());
            find(tree.root.as_mut().unwrap(), actual).unwrap().kind = wrong;
            assert_eq!(
                project_module(&source, &tree),
                Err(ProjectionError::MalformedTree(
                    InternalReason::UnexpectedShape
                ))
            );
        }
    }
}
