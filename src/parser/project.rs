//! Projection from recovery-free concrete syntax to spanned surface syntax.

use crate::{
    lexer::{Token, TokenKind},
    source::{ByteRange, SourceFile, Span},
    surface::{
        ApplicationExpr, BinaryExpr, EquationalGlobal, FunctionExpr, FunctionType,
        InlineOperationalGlobal, SurfaceBinder, SurfaceBinding, SurfaceBlock,
        SurfaceConstructorDeclaration, SurfaceDeclarationIndex, SurfaceDefinition,
        SurfaceDefinitionKind, SurfaceDeterminationSide, SurfaceEffectDeclaration,
        SurfaceEffectInstance, SurfaceEffectOperation, SurfaceEffectRow, SurfaceEquation,
        SurfaceExpr, SurfaceExprKind, SurfaceExternalInterface, SurfaceHandleExpr,
        SurfaceHandlerClause, SurfaceImplementation, SurfaceImport, SurfaceImportItem,
        SurfaceImportSelection, SurfaceInlineOperationalHeader, SurfaceInterfaceDeclaration,
        SurfaceInterfaceDetermination, SurfaceInterfaceMethod, SurfaceKind, SurfaceKindKind,
        SurfaceLocalDeclaration, SurfaceMatchArm, SurfaceMatchExpr, SurfaceModule,
        SurfaceModulePath, SurfaceName, SurfaceNominalDeclarationKind, SurfacePattern,
        SurfacePatternKind, SurfacePerformExpr, SurfaceQualifiedName, SurfaceRecursiveGroup,
        SurfaceRecursiveMember, SurfaceReference, SurfaceRequirement, SurfaceType,
        SurfaceTypeDeclaration, SurfaceTypeKind, SurfaceTypeParameter, SurfaceTypeVisibility,
        SurfaceTypedPattern,
    },
};

use super::{
    ConcreteElement, ConcreteNode, ConcreteTree, InternalReason, NodeKind, ResourceFailure,
};

/// Why concrete syntax cannot cross the surface projection boundary.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ProjectionError {
    /// Parsing exceeded a replaceable implementation resource budget.
    ResourceLimit(ResourceFailure),
    /// Lexical or parse recovery information remains in the tree.
    RecoveryNodesPresent,
    /// The event-built tree violates an internal structural invariant.
    MalformedTree(InternalReason),
}

impl ProjectionError {
    pub(crate) const fn reason_code(self) -> &'static str {
        match self {
            Self::ResourceLimit(resource) => resource.reason_code(),
            Self::RecoveryNodesPresent => "internal.projection.recovery-nodes",
            Self::MalformedTree(_) => "internal.projection.malformed-tree",
        }
    }

    pub(crate) fn message(self, path: &str) -> crate::message::Message<'_> {
        use crate::message::Message;
        match self {
            Self::ResourceLimit(ResourceFailure::StructuralDepth { limit }) => {
                Message::syntax_depth(path, limit)
            }
            Self::ResourceLimit(ResourceFailure::SyntaxWork { limit }) => {
                Message::syntax_work(path, limit)
            }
            Self::RecoveryNodesPresent => Message::projection_recovery(path),
            Self::MalformedTree(cause) => Message::projection_malformed(path, cause),
        }
    }

    pub(crate) fn message_without_path(self) -> crate::message::Message<'static> {
        use crate::message::Message;
        match self {
            Self::ResourceLimit(ResourceFailure::StructuralDepth { limit }) => {
                Message::syntax_depth_unlocated(limit)
            }
            Self::ResourceLimit(ResourceFailure::SyntaxWork { limit }) => {
                Message::syntax_work_unlocated(limit)
            }
            Self::RecoveryNodesPresent => Message::projection_recovery_unlocated(),
            Self::MalformedTree(cause) => Message::projection_malformed_unlocated(cause),
        }
    }
}

/// Projects a complete, recovery-free module tree to surface syntax.
///
/// # Errors
///
/// Returns [`ProjectionError::ResourceLimit`] when parsing exceeded a
/// replaceable implementation resource budget. Returns
/// [`ProjectionError::RecoveryNodesPresent`] whenever lexical or parse
/// diagnostics, missing forms, or error events remain. Returns
/// [`ProjectionError::MalformedTree`] for incomplete or inconsistent concrete
/// structure.
pub fn project_module(
    source: &SourceFile,
    tree: &ConcreteTree,
) -> Result<SurfaceModule, ProjectionError> {
    let (root, tokens) = validated_root(source, tree)?;
    project_surface_module(source, root, tokens)
}

fn validated_root<'tree>(
    source: &SourceFile,
    tree: &'tree ConcreteTree,
) -> Result<(&'tree ConcreteNode, &'tree [Token]), ProjectionError> {
    if let Some(failure) = tree.resource_failure {
        return Err(ProjectionError::ResourceLimit(failure));
    }
    if tree
        .root
        .as_ref()
        .is_some_and(source_structural_depth_exceeds_budget)
    {
        return Err(ProjectionError::ResourceLimit(
            ResourceFailure::StructuralDepth {
                limit: super::STRUCTURAL_DEPTH_LIMIT,
            },
        ));
    }
    validate_tokens(source, &tree.tokens)?;
    if !tree.lexical_diagnostics.is_empty()
        || !tree.parse_diagnostics.is_empty()
        || tree.root.as_ref().is_some_and(has_recovery)
    {
        return Err(ProjectionError::RecoveryNodesPresent);
    }
    if let Some(reason) = tree.malformed {
        return Err(ProjectionError::MalformedTree(reason));
    }
    let root = tree.root.as_ref().ok_or(ProjectionError::MalformedTree(
        InternalReason::InvalidRootCount,
    ))?;
    validate_node_shape(root, &tree.tokens)?;
    validate_concrete_token_coverage(root, tree.tokens.len())?;
    Ok((root, &tree.tokens))
}

fn validate_concrete_token_coverage(
    root: &ConcreteNode,
    token_count: usize,
) -> Result<(), ProjectionError> {
    let mut seen = vec![false; token_count];
    let mut previous = None;
    let mut pending = root.children.iter().rev().collect::<Vec<_>>();
    while let Some(element) = pending.pop() {
        match element {
            ConcreteElement::Node(node) => pending.extend(node.children.iter().rev()),
            ConcreteElement::Token(index) => {
                if *index >= token_count {
                    return malformed(InternalReason::TokenOutOfRange);
                }
                if seen[*index] {
                    return malformed(InternalReason::DuplicateToken);
                }
                if previous.is_some_and(|previous| *index < previous) {
                    return malformed(InternalReason::TokenOutOfOrder);
                }
                seen[*index] = true;
                previous = Some(*index);
            }
            ConcreteElement::Missing { .. } | ConcreteElement::Error(_) => {}
        }
    }
    if seen.iter().any(|seen| !seen) {
        return malformed(InternalReason::MissingToken);
    }
    Ok(())
}

fn source_structural_depth_exceeds_budget(root: &ConcreteNode) -> bool {
    let mut pending = vec![(root, 0_usize)];
    while let Some((node, depth)) = pending.pop() {
        let depth = depth.saturating_add(structural_weight(node));
        if depth > super::STRUCTURAL_DEPTH_LIMIT {
            return true;
        }
        for child in &node.children {
            if let ConcreteElement::Node(child) = child {
                pending.push((child, depth));
            }
        }
    }
    false
}

fn structural_weight(node: &ConcreteNode) -> usize {
    match node.kind {
        NodeKind::Block
        | NodeKind::RegistrationExpression
        | NodeKind::CleanupExpression
        | NodeKind::FunctionExpression
        | NodeKind::EqualityExpression
        | NodeKind::AdditiveExpression
        | NodeKind::MultiplicativeExpression
        | NodeKind::ApplicationExpression
        | NodeKind::ParenthesizedExpression
        | NodeKind::ParenthesizedType
        | NodeKind::ParenthesizedKind => 1,
        NodeKind::Pattern
            if child_nodes(node).any(|child| {
                matches!(
                    child.kind,
                    NodeKind::ConstructorPattern | NodeKind::TuplePattern | NodeKind::Pattern
                )
            }) =>
        {
            super::PATTERN_STRUCTURAL_WEIGHT
        }
        NodeKind::MatchExpression | NodeKind::HandlerExpression => super::MATCH_STRUCTURAL_WEIGHT,
        NodeKind::AtomicType
        | NodeKind::EffectInstance
        | NodeKind::InterfaceApplication
        | NodeKind::OperationReference
            if child_nodes(node).any(|child| child.kind == NodeKind::EffectRow) =>
        {
            1
        }
        NodeKind::Type if child_nodes(node).any(|child| child.kind == NodeKind::Type) => 1,
        NodeKind::Kind if child_nodes(node).any(|child| child.kind == NodeKind::Kind) => 1,
        _ => 0,
    }
}

fn validate_tokens(source: &SourceFile, tokens: &[Token]) -> Result<(), ProjectionError> {
    let mut previous_end = 0;
    let mut eof_count = 0;
    for (index, token) in tokens.iter().enumerate() {
        if token.span.source() != source.id() {
            return malformed(InternalReason::ForeignSpan);
        }
        source
            .span(token.span.range())
            .map_err(|_| ProjectionError::MalformedTree(InternalReason::InvalidSpan))?;
        if token.kind == TokenKind::EndOfFile {
            eof_count += 1;
            let source_end = u32::try_from(source.text().len())
                .map_err(|_| ProjectionError::MalformedTree(InternalReason::InvalidSpan))?;
            if index + 1 != tokens.len()
                || token.span.range().start() != source_end
                || token.span.range().end() != source_end
            {
                return malformed(InternalReason::InvalidSpan);
            }
        }
        if token.span.range().start() < previous_end {
            return malformed(InternalReason::TokenOutOfOrder);
        }
        previous_end = token.span.range().end();
    }
    if eof_count != 1 {
        return malformed(InternalReason::InvalidSpan);
    }
    Ok(())
}

fn validate_node_shape(node: &ConcreteNode, tokens: &[Token]) -> Result<(), ProjectionError> {
    let mut pending = vec![node];
    while let Some(node) = pending.pop() {
        validate_shallow_shape(node, tokens)?;
        pending.extend(child_nodes(node));
    }
    Ok(())
}

fn validate_shallow_shape(node: &ConcreteNode, tokens: &[Token]) -> Result<(), ProjectionError> {
    let mut shape = ShapeCursor::new(node, tokens);
    match node.kind {
        NodeKind::Module => {
            while shape.peek_node_is(NodeKind::ImportDeclaration) {
                shape.node(NodeKind::ImportDeclaration)?;
                shape.token(&TokenKind::LineEnd)?;
            }
            while shape.peek_node_is(NodeKind::TypeDeclaration)
                || shape.peek_node_is(NodeKind::NewtypeDeclaration)
                || shape.peek_node_is(NodeKind::InterfaceDeclaration)
                || shape.peek_node_is(NodeKind::ResourceDefinition)
                || shape.peek_node_is(NodeKind::EffectDeclaration)
                || shape.peek_node_is(NodeKind::ImplementationDeclaration)
                || shape.peek_node_is(NodeKind::EquationalGlobal)
                || shape.peek_node_is(NodeKind::InlineOperationalGlobal)
            {
                shape.any_node()?;
                shape.token(&TokenKind::LineEnd)?;
            }
            shape.token(&TokenKind::EndOfFile)?;
        }
        NodeKind::ImportDeclaration => {
            let public = shape.peek_token_is(&TokenKind::Pub);
            if public {
                shape.token(&TokenKind::Pub)?;
            }
            shape.token(&TokenKind::Import)?;
            shape.node(NodeKind::ModulePath)?;
            if shape.peek_token_is(&TokenKind::As) {
                if public {
                    return malformed(InternalReason::UnexpectedShape);
                }
                shape.token(&TokenKind::As)?;
                shape.token_matching(|kind| matches!(kind, TokenKind::UpperIdentifier(_)))?;
            } else {
                shape.token(&TokenKind::LeftParen)?;
                shape.node(NodeKind::ImportItem)?;
                while shape.peek_token_is(&TokenKind::Comma) {
                    shape.token(&TokenKind::Comma)?;
                    shape.node(NodeKind::ImportItem)?;
                }
                shape.token(&TokenKind::RightParen)?;
            }
        }
        NodeKind::ModulePath => {
            let absolute = shape.peek_token_is(&TokenKind::At);
            if absolute {
                shape.token(&TokenKind::At)?;
            }
            shape.token_matching(|kind| matches!(kind, TokenKind::Identifier(_)))?;
            if absolute {
                shape.token(&TokenKind::Dot)?;
                shape.token_matching(|kind| matches!(kind, TokenKind::Identifier(_)))?;
            }
            while shape.peek_token_is(&TokenKind::Dot) {
                shape.token(&TokenKind::Dot)?;
                shape.token_matching(|kind| matches!(kind, TokenKind::Identifier(_)))?;
            }
        }
        NodeKind::ImportItem => {
            if shape.peek_token_is(&TokenKind::Impl) {
                shape.token(&TokenKind::Impl)?;
                shape.token_matching(|kind| matches!(kind, TokenKind::UpperIdentifier(_)))?;
            } else {
                shape.token_matching(|kind| {
                    matches!(
                        kind,
                        TokenKind::Identifier(_) | TokenKind::UpperIdentifier(_)
                    )
                })?;
                if shape.peek_token_is(&TokenKind::As) {
                    shape.token(&TokenKind::As)?;
                    shape.token_matching(|kind| {
                        matches!(
                            kind,
                            TokenKind::Identifier(_) | TokenKind::UpperIdentifier(_)
                        )
                    })?;
                }
            }
        }
        NodeKind::TypeDeclaration => {
            if shape.peek_token_is(&TokenKind::Pub) {
                shape.token(&TokenKind::Pub)?;
                shape.optional_token(&TokenKind::Opaque)?;
            }
            shape.token(&TokenKind::Type)?;
            shape.token_matching(|kind| matches!(kind, TokenKind::UpperIdentifier(_)))?;
            if shape.peek_node_is(NodeKind::TypeParameters) {
                shape.node(NodeKind::TypeParameters)?;
            }
            shape.token(&TokenKind::Equal)?;
            shape.optional_token(&TokenKind::LineEnd)?;
            shape.node(NodeKind::ConstructorDeclaration)?;
            while shape.peek_token_is(&TokenKind::LineEnd) {
                shape.token(&TokenKind::LineEnd)?;
                shape.token(&TokenKind::Pipe)?;
                shape.node(NodeKind::ConstructorDeclaration)?;
            }
        }
        NodeKind::NewtypeDeclaration => {
            if shape.peek_token_is(&TokenKind::Pub) {
                shape.token(&TokenKind::Pub)?;
                shape.optional_token(&TokenKind::Opaque)?;
            }
            shape.token(&TokenKind::Newtype)?;
            shape.token_matching(|kind| matches!(kind, TokenKind::UpperIdentifier(_)))?;
            if shape.peek_node_is(NodeKind::TypeParameters) {
                shape.node(NodeKind::TypeParameters)?;
            }
            shape.token(&TokenKind::Equal)?;
            shape.node(NodeKind::ConstructorDeclaration)?;
        }
        NodeKind::TypeParameters => {
            shape.token(&TokenKind::Less)?;
            shape.node(NodeKind::TypeParameter)?;
            while shape.peek_token_is(&TokenKind::Comma) {
                shape.token(&TokenKind::Comma)?;
                shape.node(NodeKind::TypeParameter)?;
            }
            shape.token(&TokenKind::Greater)?;
        }
        NodeKind::TypeParameter => {
            shape.token_matching(|kind| matches!(kind, TokenKind::UpperIdentifier(_)))?;
            if shape.peek_token_is(&TokenKind::Colon) {
                shape.token(&TokenKind::Colon)?;
                shape.node(NodeKind::Kind)?;
            }
        }
        NodeKind::ConstructorDeclaration => {
            shape.token_matching(|kind| matches!(kind, TokenKind::UpperIdentifier(_)))?;
            if shape.peek_token_is(&TokenKind::LeftParen) {
                shape.token(&TokenKind::LeftParen)?;
                shape.node(NodeKind::Type)?;
                while shape.peek_token_is(&TokenKind::Comma) {
                    shape.token(&TokenKind::Comma)?;
                    shape.node(NodeKind::Type)?;
                }
                shape.token(&TokenKind::RightParen)?;
            }
        }
        NodeKind::InterfaceDeclaration => {
            shape.optional_token(&TokenKind::Pub)?;
            shape.token(&TokenKind::Interface)?;
            shape.token_matching(|kind| matches!(kind, TokenKind::UpperIdentifier(_)))?;
            shape.node(NodeKind::TypeParameters)?;
            if shape.peek_token_is(&TokenKind::Where) {
                shape.token(&TokenKind::Where)?;
                validate_determination_side(&mut shape)?;
                shape.token(&TokenKind::Arrow)?;
                validate_determination_side(&mut shape)?;
            }
            shape.token(&TokenKind::LeftBrace)?;
            shape.token(&TokenKind::LineEnd)?;
            shape.node(NodeKind::InterfaceMethod)?;
            while shape.peek_token_is(&TokenKind::LineEnd) {
                shape.token(&TokenKind::LineEnd)?;
                if shape.peek_node_is(NodeKind::InterfaceMethod) {
                    shape.node(NodeKind::InterfaceMethod)?;
                }
            }
            shape.token(&TokenKind::RightBrace)?;
        }
        NodeKind::InterfaceMethod => {
            shape.node(NodeKind::Binder)?;
            if shape.peek_node_is(NodeKind::TypeParameters) {
                shape.node(NodeKind::TypeParameters)?;
            }
            shape.token(&TokenKind::Colon)?;
            shape.node(NodeKind::Type)?;
        }
        NodeKind::EffectDeclaration => {
            shape.optional_token(&TokenKind::Pub)?;
            shape.token(&TokenKind::Effect)?;
            shape.token_matching(|kind| matches!(kind, TokenKind::UpperIdentifier(_)))?;
            if shape.peek_node_is(NodeKind::TypeParameters) {
                shape.node(NodeKind::TypeParameters)?;
            }
            shape.token(&TokenKind::LeftBrace)?;
            shape.token(&TokenKind::LineEnd)?;
            shape.node(NodeKind::EffectOperation)?;
            while shape.peek_token_is(&TokenKind::LineEnd) {
                shape.token(&TokenKind::LineEnd)?;
                if shape.peek_node_is(NodeKind::EffectOperation) {
                    shape.node(NodeKind::EffectOperation)?;
                }
            }
            shape.token(&TokenKind::RightBrace)?;
        }
        NodeKind::EffectOperation => {
            shape.node(NodeKind::Binder)?;
            shape.token(&TokenKind::Colon)?;
            shape.node(NodeKind::Type)?;
        }
        NodeKind::WhereClause => {
            shape.token(&TokenKind::Where)?;
            shape.node(NodeKind::InterfaceApplication)?;
            while shape.peek_token_is(&TokenKind::Comma) {
                shape.token(&TokenKind::Comma)?;
                shape.node(NodeKind::InterfaceApplication)?;
            }
        }
        NodeKind::InterfaceApplication => {
            if shape.peek_node_is(NodeKind::QualifiedName) {
                validate_qualified_interface_name(
                    shape.peek_node().ok_or(ProjectionError::MalformedTree(
                        InternalReason::UnexpectedShape,
                    ))?,
                    tokens,
                )?;
                shape.node(NodeKind::QualifiedName)?;
            } else {
                shape.token_matching(|kind| matches!(kind, TokenKind::UpperIdentifier(_)))?;
            }
            shape.token(&TokenKind::Less)?;
            shape.owner_argument()?;
            while shape.peek_token_is(&TokenKind::Comma) {
                shape.token(&TokenKind::Comma)?;
                shape.owner_argument()?;
            }
            shape.token(&TokenKind::Greater)?;
        }
        NodeKind::LexicalEvidenceDeclaration => {
            shape.token(&TokenKind::With)?;
            shape.node(NodeKind::InterfaceApplication)?;
            shape.token(&TokenKind::LeftBrace)?;
            shape.token(&TokenKind::LineEnd)?;
            if shape.peek_node_is(NodeKind::Equation) {
                shape.node(NodeKind::Equation)?;
                while shape.peek_token_is(&TokenKind::LineEnd) {
                    shape.token(&TokenKind::LineEnd)?;
                    if shape.peek_node_is(NodeKind::Equation) {
                        shape.node(NodeKind::Equation)?;
                    } else {
                        break;
                    }
                }
            }
            shape.token(&TokenKind::RightBrace)?;
        }
        NodeKind::ImplementationDeclaration => {
            shape.optional_token(&TokenKind::Pub)?;
            shape.token(&TokenKind::Impl)?;
            if shape.peek_node_is(NodeKind::TypeParameters) {
                shape.node(NodeKind::TypeParameters)?;
            }
            shape.node(NodeKind::InterfaceApplication)?;
            if shape.peek_node_is(NodeKind::WhereClause) {
                shape.node(NodeKind::WhereClause)?;
            }
            shape.token(&TokenKind::LeftBrace)?;
            shape.token(&TokenKind::LineEnd)?;
            if shape.peek_node_is(NodeKind::Equation) {
                shape.node(NodeKind::Equation)?;
                while shape.peek_token_is(&TokenKind::LineEnd) {
                    shape.token(&TokenKind::LineEnd)?;
                    if shape.peek_node_is(NodeKind::Equation) {
                        shape.node(NodeKind::Equation)?;
                    } else {
                        break;
                    }
                }
            }
            shape.token(&TokenKind::RightBrace)?;
        }
        NodeKind::EquationalGlobal => {
            shape.optional_token(&TokenKind::Pub)?;
            shape.node(NodeKind::ExternalInterface)?;
            shape.token(&TokenKind::LineEnd)?;
            shape.node(NodeKind::Equation)?;
            while shape.peek_token_is(&TokenKind::LineEnd) {
                shape.token(&TokenKind::LineEnd)?;
                shape.node(NodeKind::Equation)?;
            }
        }
        NodeKind::ExternalInterface => {
            shape.node(NodeKind::Binder)?;
            if shape.peek_node_is(NodeKind::TypeParameters) {
                shape.node(NodeKind::TypeParameters)?;
            }
            shape.token(&TokenKind::Colon)?;
            shape.node(NodeKind::Type)?;
            if shape.peek_node_is(NodeKind::WhereClause) {
                shape.node(NodeKind::WhereClause)?;
            }
        }
        NodeKind::Equation => {
            shape.node(NodeKind::Binder)?;
            shape.node(NodeKind::Pattern)?;
            while shape.peek_node_is(NodeKind::Pattern) {
                shape.node(NodeKind::Pattern)?;
            }
            shape.token(&TokenKind::Equal)?;
            shape.expression()?;
        }
        NodeKind::InlineOperationalGlobal => {
            shape.optional_token(&TokenKind::Pub)?;
            shape.node(NodeKind::InlineOperationalHeader)?;
            shape.node(NodeKind::Block)?;
        }
        NodeKind::InlineOperationalHeader => {
            shape.token(&TokenKind::Fn)?;
            shape.node(NodeKind::Binder)?;
            if shape.peek_node_is(NodeKind::TypeParameters) {
                shape.node(NodeKind::TypeParameters)?;
            }
            shape.token(&TokenKind::LeftParen)?;
            shape.node(NodeKind::TypedPattern)?;
            while shape.peek_token_is(&TokenKind::Comma) {
                shape.token(&TokenKind::Comma)?;
                shape.node(NodeKind::TypedPattern)?;
            }
            shape.token(&TokenKind::RightParen)?;
            shape.token(&TokenKind::Arrow)?;
            shape.node(NodeKind::Type)?;
            if shape.peek_token_is(&TokenKind::Bang) {
                shape.token(&TokenKind::Bang)?;
                shape.node(NodeKind::EffectRow)?;
            }
            if shape.peek_node_is(NodeKind::WhereClause) {
                shape.node(NodeKind::WhereClause)?;
            }
        }
        NodeKind::Block => {
            shape.token(&TokenKind::LeftBrace)?;
            shape.token(&TokenKind::LineEnd)?;
            while shape.peek_node_is(NodeKind::LocalBinding)
                || shape.peek_node_is(NodeKind::RecursiveBindingGroup)
                || shape.peek_node_is(NodeKind::NewtypeDeclaration)
                || shape.peek_node_is(NodeKind::LexicalEvidenceDeclaration)
            {
                shape.any_node()?;
                shape.token(&TokenKind::LineEnd)?;
            }
            shape.expression()?;
            shape.optional_token(&TokenKind::LineEnd)?;
            shape.token(&TokenKind::RightBrace)?;
        }
        NodeKind::LocalBinding => {
            shape.token(&TokenKind::Let)?;
            shape.node(NodeKind::Pattern)?;
            if shape.peek_token_is(&TokenKind::Colon) {
                shape.token(&TokenKind::Colon)?;
                shape.node(NodeKind::Type)?;
            }
            shape.token(&TokenKind::Equal)?;
            shape.expression()?;
        }
        NodeKind::RecursiveBindingGroup => {
            shape.token(&TokenKind::Let)?;
            shape.token(&TokenKind::Rec)?;
            shape.node(NodeKind::RecursiveBindingMember)?;
            while shape.peek_token_is(&TokenKind::LineEnd) {
                shape.token(&TokenKind::LineEnd)?;
                shape.token(&TokenKind::And)?;
                shape.node(NodeKind::RecursiveBindingMember)?;
            }
        }
        NodeKind::RecursiveBindingMember => {
            shape.node(NodeKind::Binder)?;
            shape.token(&TokenKind::Colon)?;
            shape.node(NodeKind::Type)?;
            shape.token(&TokenKind::Equal)?;
            shape.expression()?;
        }
        NodeKind::FunctionExpression => {
            shape.token(&TokenKind::Fn)?;
            shape.token(&TokenKind::LeftParen)?;
            shape.node(NodeKind::Pattern)?;
            while shape.peek_token_is(&TokenKind::Comma) {
                shape.token(&TokenKind::Comma)?;
                shape.node(NodeKind::Pattern)?;
            }
            shape.token(&TokenKind::RightParen)?;
            shape.node(NodeKind::Block)?;
        }
        NodeKind::MatchExpression => {
            shape.token(&TokenKind::Match)?;
            shape.expression()?;
            shape.token(&TokenKind::LeftBrace)?;
            shape.token(&TokenKind::LineEnd)?;
            shape.node(NodeKind::MatchArm)?;
            while shape.peek_token_is(&TokenKind::LineEnd) {
                shape.token(&TokenKind::LineEnd)?;
                if shape.peek_node_is(NodeKind::MatchArm) {
                    shape.node(NodeKind::MatchArm)?;
                }
            }
            shape.token(&TokenKind::RightBrace)?;
        }
        NodeKind::MatchArm => {
            shape.node(NodeKind::Pattern)?;
            shape.token(&TokenKind::FatArrow)?;
            shape.expression()?;
        }
        NodeKind::HandlerExpression => {
            shape.token(&TokenKind::Handle)?;
            shape.expression()?;
            shape.token(&TokenKind::With)?;
            shape.node(NodeKind::EffectInstance)?;
            shape.token(&TokenKind::LeftBrace)?;
            shape.token(&TokenKind::LineEnd)?;
            shape.node(NodeKind::HandlerClause)?;
            while shape.peek_token_is(&TokenKind::LineEnd) {
                shape.token(&TokenKind::LineEnd)?;
                if shape.peek_node_is(NodeKind::HandlerClause) {
                    shape.node(NodeKind::HandlerClause)?;
                }
            }
            shape.token(&TokenKind::RightBrace)?;
        }
        NodeKind::HandlerClause => {
            shape.node(NodeKind::Binder)?;
            shape.node(NodeKind::Pattern)?;
            shape.token(&TokenKind::FatArrow)?;
            shape.expression()?;
        }
        NodeKind::ResumeExpression => {
            shape.token(&TokenKind::Resume)?;
            shape.expression()?;
        }
        NodeKind::ResourceDefinition => {
            if shape.peek_token_is(&TokenKind::Pub) {
                shape.token(&TokenKind::Pub)?;
            }
            shape.token(&TokenKind::Resource)?;
            shape.token_matching(|kind| matches!(kind, TokenKind::UpperIdentifier(_)))?;
            shape.node(NodeKind::TypeParameters)?;
            shape.token(&TokenKind::LeftBrace)?;
            shape.token(&TokenKind::LineEnd)?;
            for index in 0..9 {
                shape.node(NodeKind::ResourceField)?;
                if index < 8 || shape.peek_token_is(&TokenKind::LineEnd) {
                    shape.token(&TokenKind::LineEnd)?;
                }
            }
            shape.token(&TokenKind::RightBrace)?;
        }
        NodeKind::ResourceField => {
            let word = direct_tokens(node, tokens)
                .next()
                .ok_or(ProjectionError::MalformedTree(
                    InternalReason::UnexpectedShape,
                ))?;
            let TokenKind::Identifier(word) = &word.kind else {
                shape.token(&TokenKind::Effect)?;
                shape.node(NodeKind::EffectInstance)?;
                return shape.finish();
            };
            shape.token_matching(|kind| matches!(kind, TokenKind::Identifier(_)))?;
            match word.as_str() {
                "input" | "state" => {
                    shape.node(NodeKind::Type)?;
                }
                "result" => {
                    shape.node(NodeKind::Type)?;
                    shape.token_matching(
                        |kind| matches!(kind, TokenKind::Identifier(word) if word == "for"),
                    )?;
                    shape.node(NodeKind::TypeParameters)?;
                }
                "provider" => {
                    shape.node(NodeKind::InterfaceApplication)?;
                }
                "interpret" => {
                    shape.node(NodeKind::EffectInstance)?;
                }
                "acquire" | "finish" => {
                    shape.node(NodeKind::Binder)?;
                    shape.token(&TokenKind::FatArrow)?;
                    shape.expression()?;
                }
                "handlers" => {
                    shape.node(NodeKind::Binder)?;
                    shape.token(&TokenKind::LeftBrace)?;
                    shape.token(&TokenKind::LineEnd)?;
                    while shape.peek_node_is(NodeKind::HandlerClause) {
                        shape.node(NodeKind::HandlerClause)?;
                        if shape.peek_token_is(&TokenKind::LineEnd) {
                            shape.token(&TokenKind::LineEnd)?;
                        }
                    }
                    shape.token(&TokenKind::RightBrace)?;
                }
                _ => return malformed(InternalReason::UnexpectedShape),
            }
        }
        NodeKind::ProviderResourceExpression => {
            shape.token(&TokenKind::Resource)?;
            shape.node(NodeKind::EffectInstance)?;
            shape.node(NodeKind::Binder)?;
            shape.token(&TokenKind::Equal)?;
            shape.node(NodeKind::PrimaryExpression)?;
            shape.node(NodeKind::Block)?;
        }
        NodeKind::ResourceExpression => {
            shape.token(&TokenKind::Resource)?;
            shape.token_matching(
                |kind| matches!(kind, TokenKind::Identifier(name) if name == "cell" || name == "native_buffer"),
            )?;
            shape.token(&TokenKind::Less)?;
            shape.token_matching(|kind| matches!(kind, TokenKind::UpperIdentifier(_)))?;
            shape.token(&TokenKind::Greater)?;
            shape.node(NodeKind::Binder)?;
            shape.token(&TokenKind::Equal)?;
            shape.node(NodeKind::PrimaryExpression)?;
            shape.node(NodeKind::Block)?;
        }
        NodeKind::HookExpression => {
            shape.token(&TokenKind::Hook)?;
            shape.node(NodeKind::EffectInstance)?;
            shape.node(NodeKind::Block)?;
        }
        NodeKind::RegistrationExpression => {
            shape.token(&TokenKind::Register)?;
            shape.node(NodeKind::EffectInstance)?;
            shape.node(NodeKind::PrimaryExpression)?;
            shape.node(NodeKind::Block)?;
        }
        NodeKind::CleanupExpression => {
            shape.token(&TokenKind::Cleanup)?;
            shape.expression()?;
            shape.node(NodeKind::Block)?;
        }
        NodeKind::PerformExpression => {
            shape.token(&TokenKind::Perform)?;
            shape.node(NodeKind::OperationReference)?;
            shape.node(NodeKind::PrimaryExpression)?;
        }
        NodeKind::OperationReference => {
            if shape.peek_node_is(NodeKind::QualifiedName) {
                shape.node(NodeKind::QualifiedName)?;
            } else {
                shape.token_matching(|kind| matches!(kind, TokenKind::UpperIdentifier(_)))?;
            }
            if shape.peek_token_is(&TokenKind::Less) {
                shape.token(&TokenKind::Less)?;
                shape.owner_argument()?;
                while shape.peek_token_is(&TokenKind::Comma) {
                    shape.token(&TokenKind::Comma)?;
                    shape.owner_argument()?;
                }
                shape.token(&TokenKind::Greater)?;
            }
            shape.token(&TokenKind::Dot)?;
            shape.token_matching(|kind| matches!(kind, TokenKind::Identifier(_)))?;
        }
        NodeKind::EqualityExpression => shape.binary(&TokenKind::EqualEqual)?,
        NodeKind::AdditiveExpression => shape.binary(&TokenKind::Plus)?,
        NodeKind::MultiplicativeExpression => shape.binary(&TokenKind::Star)?,
        NodeKind::ApplicationExpression => {
            shape.expression()?;
            shape.expression()?;
        }
        NodeKind::PrimaryExpression => {
            if shape.peek_node_is(NodeKind::ParenthesizedExpression) {
                shape.node(NodeKind::ParenthesizedExpression)?;
            } else if shape.peek_node_is(NodeKind::PerformExpression) {
                shape.node(NodeKind::PerformExpression)?;
            } else if shape.peek_node_is(NodeKind::HookExpression) {
                shape.node(NodeKind::HookExpression)?;
            } else if shape.peek_node_is(NodeKind::RegistrationExpression) {
                shape.node(NodeKind::RegistrationExpression)?;
            } else if shape.peek_node_is(NodeKind::CleanupExpression) {
                shape.node(NodeKind::CleanupExpression)?;
            } else if shape.peek_node_is(NodeKind::QualifiedName) {
                shape.node(NodeKind::QualifiedName)?;
            } else {
                shape.token_matching(|kind| {
                    matches!(
                        kind,
                        TokenKind::Integer(_)
                            | TokenKind::Discard
                            | TokenKind::True
                            | TokenKind::False
                            | TokenKind::Identifier(_)
                            | TokenKind::UpperIdentifier(_)
                    )
                })?;
            }
        }
        NodeKind::ParenthesizedExpression => {
            shape.token(&TokenKind::LeftParen)?;
            if !shape.peek_token_is(&TokenKind::RightParen) {
                if shape.peek_node_is(NodeKind::TupleExpression) {
                    shape.node(NodeKind::TupleExpression)?;
                } else {
                    shape.expression()?;
                }
            }
            shape.token(&TokenKind::RightParen)?;
        }
        NodeKind::TupleExpression => {
            shape.expression()?;
            shape.token(&TokenKind::Comma)?;
            shape.expression()?;
            while shape.peek_token_is(&TokenKind::Comma) {
                shape.token(&TokenKind::Comma)?;
                shape.expression()?;
            }
        }
        NodeKind::Pattern => {
            if shape.peek_token_is(&TokenKind::LeftParen) {
                shape.token(&TokenKind::LeftParen)?;
                if shape.peek_node_is(NodeKind::UnitPattern) {
                    shape.node(NodeKind::UnitPattern)?;
                } else if shape.peek_node_is(NodeKind::TuplePattern) {
                    shape.node(NodeKind::TuplePattern)?;
                    shape.token(&TokenKind::RightParen)?;
                } else {
                    shape.node(NodeKind::Pattern)?;
                    shape.token(&TokenKind::RightParen)?;
                }
            } else {
                shape.any_node()?;
            }
        }
        NodeKind::TuplePattern => {
            shape.node(NodeKind::Pattern)?;
            shape.token(&TokenKind::Comma)?;
            shape.node(NodeKind::Pattern)?;
            while shape.peek_token_is(&TokenKind::Comma) {
                shape.token(&TokenKind::Comma)?;
                shape.node(NodeKind::Pattern)?;
            }
        }
        NodeKind::ConstructorPattern => {
            if shape.peek_node_is(NodeKind::QualifiedName) {
                shape.node(NodeKind::QualifiedName)?;
            } else {
                shape.token_matching(|kind| matches!(kind, TokenKind::UpperIdentifier(_)))?;
            }
            if shape.peek_token_is(&TokenKind::LeftParen) {
                shape.token(&TokenKind::LeftParen)?;
                if shape.peek_node_is(NodeKind::TuplePattern) {
                    shape.node(NodeKind::TuplePattern)?;
                } else {
                    shape.node(NodeKind::Pattern)?;
                }
                shape.token(&TokenKind::RightParen)?;
            } else if shape.peek_node_is(NodeKind::Pattern) {
                shape.node(NodeKind::Pattern)?;
            }
        }
        NodeKind::WildcardPattern => shape.token(&TokenKind::Wildcard)?,
        NodeKind::BooleanPattern => {
            shape.token_matching(|kind| matches!(kind, TokenKind::True | TokenKind::False))?
        }
        NodeKind::UnitPattern => shape.token(&TokenKind::RightParen)?,
        NodeKind::Binder => {
            shape.token_matching(|kind| matches!(kind, TokenKind::Identifier(_)))?
        }
        NodeKind::TypedBinder => {
            shape.node(NodeKind::Binder)?;
            shape.token(&TokenKind::Colon)?;
            shape.node(NodeKind::Type)?;
        }
        NodeKind::TypedPattern => {
            shape.node(NodeKind::Pattern)?;
            shape.token(&TokenKind::Colon)?;
            shape.node(NodeKind::Type)?;
        }
        NodeKind::Type => {
            shape.node(NodeKind::AtomicType)?;
            if shape.peek_token_is(&TokenKind::Arrow) {
                shape.token(&TokenKind::Arrow)?;
                shape.node(NodeKind::Type)?;
                if shape.peek_token_is(&TokenKind::Bang) {
                    shape.token(&TokenKind::Bang)?;
                    shape.node(NodeKind::EffectRow)?;
                }
            }
        }
        NodeKind::EffectRow => {
            shape.token(&TokenKind::LeftBrace)?;
            if shape.peek_token_is(&TokenKind::Pipe) {
                shape.token(&TokenKind::Pipe)?;
                shape.token_matching(|kind| matches!(kind, TokenKind::UpperIdentifier(_)))?;
            } else if shape.peek_node_is(NodeKind::EffectInstance) {
                shape.node(NodeKind::EffectInstance)?;
                while shape.peek_token_is(&TokenKind::Comma) {
                    shape.token(&TokenKind::Comma)?;
                    shape.node(NodeKind::EffectInstance)?;
                }
                if shape.peek_token_is(&TokenKind::Pipe) {
                    shape.token(&TokenKind::Pipe)?;
                    shape.token_matching(|kind| matches!(kind, TokenKind::UpperIdentifier(_)))?;
                }
            }
            shape.token(&TokenKind::RightBrace)?;
        }
        NodeKind::EffectInstance => {
            if shape.peek_node_is(NodeKind::QualifiedName) {
                shape.node(NodeKind::QualifiedName)?;
            } else {
                shape.token_matching(|kind| matches!(kind, TokenKind::UpperIdentifier(_)))?;
            }
            if shape.peek_token_is(&TokenKind::Less) {
                shape.token(&TokenKind::Less)?;
                shape.owner_argument()?;
                while shape.peek_token_is(&TokenKind::Comma) {
                    shape.token(&TokenKind::Comma)?;
                    shape.owner_argument()?;
                }
                shape.token(&TokenKind::Greater)?;
            }
        }
        NodeKind::Kind => {
            if shape.peek_node_is(NodeKind::ParenthesizedKind) {
                shape.node(NodeKind::ParenthesizedKind)?;
            } else {
                shape.token_matching(
                    |kind| matches!(kind, TokenKind::UpperIdentifier(name) if name == "Type" || name == "EffectRow"),
                )?;
            }
            if shape.peek_token_is(&TokenKind::Arrow) {
                shape.token(&TokenKind::Arrow)?;
                shape.node(NodeKind::Kind)?;
            }
        }
        NodeKind::ParenthesizedKind => {
            shape.token(&TokenKind::LeftParen)?;
            shape.node(NodeKind::Kind)?;
            shape.token(&TokenKind::RightParen)?;
        }
        NodeKind::AtomicType => {
            if shape.peek_node_is(NodeKind::ParenthesizedType) {
                shape.node(NodeKind::ParenthesizedType)?;
            } else {
                if shape.peek_node_is(NodeKind::QualifiedName) {
                    shape.node(NodeKind::QualifiedName)?;
                } else {
                    shape.token_matching(|kind| {
                        matches!(
                            kind,
                            TokenKind::IntType
                                | TokenKind::BoolType
                                | TokenKind::UnitType
                                | TokenKind::UpperIdentifier(_)
                        )
                    })?;
                }
                if shape.peek_token_is(&TokenKind::Less) {
                    shape.token(&TokenKind::Less)?;
                    shape.owner_argument()?;
                    while shape.peek_token_is(&TokenKind::Comma) {
                        shape.token(&TokenKind::Comma)?;
                        shape.owner_argument()?;
                    }
                    shape.token(&TokenKind::Greater)?;
                }
            }
        }
        NodeKind::ParenthesizedType => {
            shape.token(&TokenKind::LeftParen)?;
            if shape.peek_node_is(NodeKind::TupleType) {
                shape.node(NodeKind::TupleType)?;
            } else {
                shape.node(NodeKind::Type)?;
            }
            shape.token(&TokenKind::RightParen)?;
        }
        NodeKind::TupleType => {
            shape.node(NodeKind::Type)?;
            shape.token(&TokenKind::Comma)?;
            shape.node(NodeKind::Type)?;
            while shape.peek_token_is(&TokenKind::Comma) {
                shape.token(&TokenKind::Comma)?;
                shape.node(NodeKind::Type)?;
            }
        }
        NodeKind::QualifiedName => {
            shape.token_matching(|kind| matches!(kind, TokenKind::UpperIdentifier(_)))?;
            shape.token(&TokenKind::Dot)?;
            shape.token_matching(|kind| {
                matches!(
                    kind,
                    TokenKind::Identifier(_) | TokenKind::UpperIdentifier(_)
                )
            })?;
        }
        NodeKind::Error => return malformed(InternalReason::UnexpectedShape),
    }
    shape.finish()
}

fn validate_determination_side(shape: &mut ShapeCursor<'_>) -> Result<(), ProjectionError> {
    if shape.peek_token_is(&TokenKind::LeftParen) {
        shape.token(&TokenKind::LeftParen)?;
        shape.token_matching(|kind| matches!(kind, TokenKind::UpperIdentifier(_)))?;
        while shape.peek_token_is(&TokenKind::Comma) {
            shape.token(&TokenKind::Comma)?;
            shape.token_matching(|kind| matches!(kind, TokenKind::UpperIdentifier(_)))?;
        }
        shape.token(&TokenKind::RightParen)
    } else {
        shape.token_matching(|kind| matches!(kind, TokenKind::UpperIdentifier(_)))
    }
}

fn validate_qualified_interface_name(
    node: &ConcreteNode,
    tokens: &[Token],
) -> Result<(), ProjectionError> {
    require_kind(node, NodeKind::QualifiedName)?;
    let mut shape = ShapeCursor::new(node, tokens);
    shape.token_matching(|kind| matches!(kind, TokenKind::UpperIdentifier(_)))?;
    shape.token(&TokenKind::Dot)?;
    shape.token_matching(|kind| matches!(kind, TokenKind::UpperIdentifier(_)))?;
    shape.finish()
}

struct ShapeCursor<'a> {
    children: &'a [ConcreteElement],
    tokens: &'a [Token],
    position: usize,
}

impl<'a> ShapeCursor<'a> {
    fn new(node: &'a ConcreteNode, tokens: &'a [Token]) -> Self {
        Self {
            children: &node.children,
            tokens,
            position: 0,
        }
    }

    fn peek_node_is(&self, kind: NodeKind) -> bool {
        matches!(self.children.get(self.position), Some(ConcreteElement::Node(node)) if node.kind == kind)
    }

    fn peek_node(&self) -> Option<&ConcreteNode> {
        match self.children.get(self.position) {
            Some(ConcreteElement::Node(node)) => Some(node),
            Some(
                ConcreteElement::Token(_)
                | ConcreteElement::Missing { .. }
                | ConcreteElement::Error(_),
            )
            | None => None,
        }
    }

    fn peek_token_is(&self, kind: &TokenKind) -> bool {
        matches!(self.children.get(self.position), Some(ConcreteElement::Token(index)) if self.tokens.get(*index).is_some_and(|token| same_token_variant(&token.kind, kind)))
    }

    fn node(&mut self, kind: NodeKind) -> Result<(), ProjectionError> {
        let Some(ConcreteElement::Node(node)) = self.children.get(self.position) else {
            return malformed(InternalReason::UnexpectedShape);
        };
        require_kind(node, kind)?;
        self.position += 1;
        Ok(())
    }

    fn owner_argument(&mut self) -> Result<(), ProjectionError> {
        if self.peek_node_is(NodeKind::EffectRow) {
            self.node(NodeKind::EffectRow)
        } else {
            self.node(NodeKind::Type)
        }
    }

    fn any_node(&mut self) -> Result<(), ProjectionError> {
        let Some(ConcreteElement::Node(_)) = self.children.get(self.position) else {
            return malformed(InternalReason::UnexpectedShape);
        };
        self.position += 1;
        Ok(())
    }

    fn expression(&mut self) -> Result<(), ProjectionError> {
        let Some(ConcreteElement::Node(node)) = self.children.get(self.position) else {
            return malformed(InternalReason::UnexpectedShape);
        };
        if !is_expression_kind(node.kind) {
            return malformed(InternalReason::UnexpectedShape);
        }
        self.position += 1;
        Ok(())
    }

    fn token(&mut self, kind: &TokenKind) -> Result<(), ProjectionError> {
        if !self.peek_token_is(kind) {
            return malformed(InternalReason::UnexpectedShape);
        }
        self.position += 1;
        Ok(())
    }

    fn optional_token(&mut self, kind: &TokenKind) -> Result<(), ProjectionError> {
        if self.peek_token_is(kind) {
            self.position += 1;
        }
        Ok(())
    }

    fn token_matching(
        &mut self,
        predicate: impl FnOnce(&TokenKind) -> bool,
    ) -> Result<(), ProjectionError> {
        let matches = match self.children.get(self.position) {
            Some(ConcreteElement::Token(index)) => self
                .tokens
                .get(*index)
                .is_some_and(|token| predicate(&token.kind)),
            _ => false,
        };
        if matches {
            self.position += 1;
            Ok(())
        } else {
            malformed(InternalReason::UnexpectedShape)
        }
    }

    fn binary(&mut self, operator: &TokenKind) -> Result<(), ProjectionError> {
        self.expression()?;
        self.token(operator)?;
        self.expression()
    }

    fn finish(self) -> Result<(), ProjectionError> {
        if self.position == self.children.len() {
            Ok(())
        } else {
            malformed(InternalReason::UnexpectedShape)
        }
    }
}

fn project_surface_module(
    source: &SourceFile,
    node: &ConcreteNode,
    tokens: &[Token],
) -> Result<SurfaceModule, ProjectionError> {
    require_kind(node, NodeKind::Module)?;
    let mut imports = Vec::new();
    let mut declaration_order = Vec::new();
    let mut type_declarations = Vec::new();
    let mut interfaces = Vec::new();
    let mut effects = Vec::new();
    let mut implementations = Vec::new();
    let mut resources = Vec::new();
    let mut definitions = Vec::new();
    for child in child_nodes(node) {
        match child.kind {
            NodeKind::ImportDeclaration => imports.push(project_import(source, child, tokens)?),
            NodeKind::TypeDeclaration => {
                declaration_order.push(SurfaceDeclarationIndex::Type(type_declarations.len()));
                type_declarations.push(project_type_declaration(source, child, tokens)?);
            }
            NodeKind::NewtypeDeclaration => {
                declaration_order.push(SurfaceDeclarationIndex::Type(type_declarations.len()));
                type_declarations.push(project_newtype_declaration(source, child, tokens)?);
            }
            NodeKind::InterfaceDeclaration => {
                declaration_order.push(SurfaceDeclarationIndex::Interface(interfaces.len()));
                interfaces.push(project_interface_declaration(source, child, tokens)?);
            }
            NodeKind::ResourceDefinition => {
                declaration_order.push(SurfaceDeclarationIndex::Resource(resources.len()));
                resources.push(project_resource_definition(source, child, tokens)?);
            }
            NodeKind::EffectDeclaration => {
                declaration_order.push(SurfaceDeclarationIndex::Effect(effects.len()));
                effects.push(project_effect_declaration(source, child, tokens)?);
            }
            NodeKind::ImplementationDeclaration => {
                declaration_order.push(SurfaceDeclarationIndex::Implementation(
                    implementations.len(),
                ));
                implementations.push(project_implementation(source, child, tokens)?);
            }
            NodeKind::EquationalGlobal | NodeKind::InlineOperationalGlobal => {
                declaration_order.push(SurfaceDeclarationIndex::Global(definitions.len()));
                definitions.push(project_definition(source, child, tokens)?);
            }
            _ => return malformed(InternalReason::UnexpectedShape),
        }
    }
    Ok(SurfaceModule {
        imports,
        declaration_order,
        type_declarations,
        interfaces,
        effects,
        implementations,
        definitions,
        resources,
        span: node_span(source, node, tokens)?,
    })
}

fn project_effect_declaration(
    source: &SourceFile,
    node: &ConcreteNode,
    tokens: &[Token],
) -> Result<SurfaceEffectDeclaration, ProjectionError> {
    require_kind(node, NodeKind::EffectDeclaration)?;
    let public = direct_tokens(node, tokens).any(|token| token.kind == TokenKind::Pub);
    let name = direct_tokens(node, tokens)
        .find(|token| matches!(token.kind, TokenKind::UpperIdentifier(_)))
        .map(surface_name)
        .transpose()?
        .ok_or(ProjectionError::MalformedTree(
            InternalReason::UnexpectedShape,
        ))?;
    let parameters = project_optional_type_parameters(source, node, tokens)?.unwrap_or_default();
    let operations = child_nodes(node)
        .filter(|child| child.kind == NodeKind::EffectOperation)
        .map(|operation| project_effect_operation(source, operation, tokens))
        .collect::<Result<Vec<_>, _>>()?;
    if operations.is_empty() {
        return malformed(InternalReason::UnexpectedShape);
    }
    Ok(SurfaceEffectDeclaration {
        public,
        name,
        parameters,
        operations,
        span: node_span(source, node, tokens)?,
    })
}

fn project_effect_operation(
    source: &SourceFile,
    node: &ConcreteNode,
    tokens: &[Token],
) -> Result<SurfaceEffectOperation, ProjectionError> {
    require_kind(node, NodeKind::EffectOperation)?;
    Ok(SurfaceEffectOperation {
        name: project_binder(only_child_of_kind(node, NodeKind::Binder)?, tokens)?.name,
        annotation: project_type(source, only_child_of_kind(node, NodeKind::Type)?, tokens)?,
        span: node_span(source, node, tokens)?,
    })
}

fn project_implementation(
    source: &SourceFile,
    node: &ConcreteNode,
    tokens: &[Token],
) -> Result<SurfaceImplementation, ProjectionError> {
    require_kind(node, NodeKind::ImplementationDeclaration)?;
    let head = project_interface_application(
        source,
        only_child_of_kind(node, NodeKind::InterfaceApplication)?,
        tokens,
    )?;
    let equations = child_nodes(node)
        .filter(|child| child.kind == NodeKind::Equation)
        .map(|equation| project_equation(source, equation, tokens))
        .collect::<Result<Vec<_>, _>>()?;
    Ok(SurfaceImplementation {
        public: direct_tokens(node, tokens).any(|token| token.kind == TokenKind::Pub),
        type_parameters: project_optional_type_parameters(source, node, tokens)?,
        head,
        prerequisites: project_requirements(source, node, tokens)?,
        equations,
        span: node_span(source, node, tokens)?,
    })
}

fn project_interface_declaration(
    source: &SourceFile,
    node: &ConcreteNode,
    tokens: &[Token],
) -> Result<SurfaceInterfaceDeclaration, ProjectionError> {
    require_kind(node, NodeKind::InterfaceDeclaration)?;
    let public = direct_tokens(node, tokens).any(|token| token.kind == TokenKind::Pub);
    let mut names = direct_tokens(node, tokens)
        .filter(|token| matches!(token.kind, TokenKind::UpperIdentifier(_)));
    let name = surface_name(names.next().ok_or(ProjectionError::MalformedTree(
        InternalReason::UnexpectedShape,
    ))?)?;
    let parameters = project_optional_type_parameters(source, node, tokens)?.ok_or(
        ProjectionError::MalformedTree(InternalReason::UnexpectedShape),
    )?;
    let determination = project_interface_determination(node, tokens)?;
    let methods = child_nodes(node)
        .filter(|child| child.kind == NodeKind::InterfaceMethod)
        .map(|method| project_interface_method(source, method, tokens))
        .collect::<Result<Vec<_>, _>>()?;
    if methods.is_empty() {
        return malformed(InternalReason::UnexpectedShape);
    }
    Ok(SurfaceInterfaceDeclaration {
        public,
        name,
        parameters: parameters.into_boxed_slice(),
        determination,
        methods,
        span: node_span(source, node, tokens)?,
    })
}

fn project_interface_determination(
    node: &ConcreteNode,
    tokens: &[Token],
) -> Result<Option<SurfaceInterfaceDetermination>, ProjectionError> {
    let direct = direct_tokens(node, tokens).collect::<Vec<_>>();
    let Some(where_index) = direct
        .iter()
        .position(|token| token.kind == TokenKind::Where)
    else {
        return Ok(None);
    };
    let arrow_index = direct
        .iter()
        .position(|token| token.kind == TokenKind::Arrow)
        .ok_or(ProjectionError::MalformedTree(
            InternalReason::UnexpectedShape,
        ))?;
    let brace_index = direct
        .iter()
        .position(|token| token.kind == TokenKind::LeftBrace)
        .ok_or(ProjectionError::MalformedTree(
            InternalReason::UnexpectedShape,
        ))?;
    if where_index >= arrow_index || arrow_index >= brace_index {
        return malformed(InternalReason::UnexpectedShape);
    }
    let determinant = project_determination_side(&direct[where_index + 1..arrow_index])?;
    let dependent = project_determination_side(&direct[arrow_index + 1..brace_index])?;
    let span = direct[where_index]
        .span
        .cover(dependent.span)
        .ok_or(ProjectionError::MalformedTree(InternalReason::ForeignSpan))?;
    Ok(Some(SurfaceInterfaceDetermination {
        determinant,
        dependent,
        span,
    }))
}

fn project_determination_side(
    tokens: &[&Token],
) -> Result<SurfaceDeterminationSide, ProjectionError> {
    let first = tokens.first().ok_or(ProjectionError::MalformedTree(
        InternalReason::UnexpectedShape,
    ))?;
    let last = tokens.last().ok_or(ProjectionError::MalformedTree(
        InternalReason::UnexpectedShape,
    ))?;
    let parameters = tokens
        .iter()
        .filter(|token| matches!(token.kind, TokenKind::UpperIdentifier(_)))
        .map(|token| surface_name(token))
        .collect::<Result<Vec<_>, _>>()?;
    if parameters.is_empty() {
        return malformed(InternalReason::UnexpectedShape);
    }
    let span = first
        .span
        .cover(last.span)
        .ok_or(ProjectionError::MalformedTree(InternalReason::ForeignSpan))?;
    Ok(SurfaceDeterminationSide {
        parameters: parameters.into_boxed_slice(),
        span,
    })
}

fn project_interface_method(
    source: &SourceFile,
    node: &ConcreteNode,
    tokens: &[Token],
) -> Result<SurfaceInterfaceMethod, ProjectionError> {
    require_kind(node, NodeKind::InterfaceMethod)?;
    let binder = only_child_of_kind(node, NodeKind::Binder)?;
    Ok(SurfaceInterfaceMethod {
        name: project_binder(binder, tokens)?.name,
        type_parameters: project_optional_type_parameters(source, node, tokens)?,
        annotation: project_type(source, only_child_of_kind(node, NodeKind::Type)?, tokens)?,
        span: node_span(source, node, tokens)?,
    })
}

fn project_import(
    source: &SourceFile,
    node: &ConcreteNode,
    tokens: &[Token],
) -> Result<SurfaceImport, ProjectionError> {
    require_kind(node, NodeKind::ImportDeclaration)?;
    let path_node = only_child_of_kind(node, NodeKind::ModulePath)?;
    let mut path_names = direct_tokens(path_node, tokens)
        .filter_map(|token| match &token.kind {
            TokenKind::Identifier(text) => Some(SurfaceName {
                text: text.clone(),
                span: token.span,
            }),
            _ => None,
        })
        .collect::<Vec<_>>();
    let absolute = direct_tokens(path_node, tokens).any(|token| token.kind == TokenKind::At);
    let path = if absolute {
        if path_names.len() < 2 {
            return malformed(InternalReason::UnexpectedShape);
        }
        let root = path_names.remove(0);
        SurfaceModulePath::Absolute {
            root,
            segments: path_names,
        }
    } else {
        if path_names.is_empty() {
            return malformed(InternalReason::UnexpectedShape);
        }
        SurfaceModulePath::Relative(path_names)
    };

    let items = child_nodes(node)
        .filter(|child| child.kind == NodeKind::ImportItem)
        .map(|item| project_import_item(source, item, tokens))
        .collect::<Result<Vec<_>, _>>()?;
    let public = direct_tokens(node, tokens).any(|token| token.kind == TokenKind::Pub);
    let selection = if direct_tokens(node, tokens).any(|token| token.kind == TokenKind::LeftParen) {
        SurfaceImportSelection::Targeted(items)
    } else {
        if public {
            return malformed(InternalReason::UnexpectedShape);
        }
        let alias_token = direct_tokens(node, tokens)
            .find(|token| matches!(token.kind, TokenKind::UpperIdentifier(_)))
            .ok_or(ProjectionError::MalformedTree(
                InternalReason::UnexpectedShape,
            ))?;
        SurfaceImportSelection::Qualified {
            alias: surface_name(alias_token)?,
        }
    };
    Ok(SurfaceImport {
        public,
        path,
        selection,
        span: node_span(source, node, tokens)?,
    })
}

fn project_import_item(
    source: &SourceFile,
    node: &ConcreteNode,
    tokens: &[Token],
) -> Result<SurfaceImportItem, ProjectionError> {
    require_kind(node, NodeKind::ImportItem)?;
    if direct_tokens(node, tokens).any(|token| token.kind == TokenKind::Impl) {
        let interface = direct_tokens(node, tokens)
            .find(|token| matches!(token.kind, TokenKind::UpperIdentifier(_)))
            .ok_or(ProjectionError::MalformedTree(
                InternalReason::UnexpectedShape,
            ))?;
        return Ok(SurfaceImportItem::Implementation {
            interface: surface_name(interface)?,
            span: node_span(source, node, tokens)?,
        });
    }
    let mut names = direct_tokens(node, tokens).filter(|token| {
        matches!(
            token.kind,
            TokenKind::Identifier(_) | TokenKind::UpperIdentifier(_)
        )
    });
    let name = surface_name(names.next().ok_or(ProjectionError::MalformedTree(
        InternalReason::UnexpectedShape,
    ))?)?;
    let alias = names.next().map(surface_name).transpose()?;
    if names.next().is_some() {
        return malformed(InternalReason::UnexpectedShape);
    }
    Ok(SurfaceImportItem::Name {
        name,
        alias,
        span: node_span(source, node, tokens)?,
    })
}

fn project_type_declaration(
    source: &SourceFile,
    node: &ConcreteNode,
    tokens: &[Token],
) -> Result<SurfaceTypeDeclaration, ProjectionError> {
    project_nominal_declaration(source, node, tokens, SurfaceNominalDeclarationKind::Data)
}

fn project_newtype_declaration(
    source: &SourceFile,
    node: &ConcreteNode,
    tokens: &[Token],
) -> Result<SurfaceTypeDeclaration, ProjectionError> {
    project_nominal_declaration(source, node, tokens, SurfaceNominalDeclarationKind::Newtype)
}

fn project_nominal_declaration(
    source: &SourceFile,
    node: &ConcreteNode,
    tokens: &[Token],
    declaration_kind: SurfaceNominalDeclarationKind,
) -> Result<SurfaceTypeDeclaration, ProjectionError> {
    match declaration_kind {
        SurfaceNominalDeclarationKind::Data => require_kind(node, NodeKind::TypeDeclaration)?,
        SurfaceNominalDeclarationKind::Newtype => require_kind(node, NodeKind::NewtypeDeclaration)?,
    }
    let public = direct_tokens(node, tokens).any(|token| token.kind == TokenKind::Pub);
    let opaque = direct_tokens(node, tokens).any(|token| token.kind == TokenKind::Opaque);
    let visibility = match (public, opaque) {
        (false, false) => SurfaceTypeVisibility::Private,
        (true, false) => SurfaceTypeVisibility::PublicTransparent,
        (true, true) => SurfaceTypeVisibility::PublicOpaque,
        (false, true) => return malformed(InternalReason::UnexpectedShape),
    };
    let mut names = direct_tokens(node, tokens)
        .filter(|token| matches!(token.kind, TokenKind::UpperIdentifier(_)));
    let name_token = names.next().ok_or(ProjectionError::MalformedTree(
        InternalReason::UnexpectedShape,
    ))?;
    let TokenKind::UpperIdentifier(name) = &name_token.kind else {
        return malformed(InternalReason::UnexpectedShape);
    };
    let constructors = child_nodes(node)
        .filter(|child| child.kind == NodeKind::ConstructorDeclaration)
        .map(|constructor| project_constructor_declaration(source, constructor, tokens))
        .collect::<Result<Vec<_>, _>>()?;
    if constructors.is_empty() {
        return malformed(InternalReason::UnexpectedShape);
    }
    if declaration_kind == SurfaceNominalDeclarationKind::Newtype
        && !matches!(constructors.as_slice(), [constructor] if constructor.fields.len() == 1)
    {
        return malformed(InternalReason::UnexpectedShape);
    }
    if names.next().is_some() {
        return malformed(InternalReason::UnexpectedShape);
    }
    let parameters = project_optional_type_parameters(source, node, tokens)?.unwrap_or_default();
    Ok(SurfaceTypeDeclaration {
        declaration_kind,
        visibility,
        name: SurfaceName {
            text: name.clone(),
            span: name_token.span,
        },
        parameters,
        constructors,
        span: node_span(source, node, tokens)?,
    })
}

fn project_constructor_declaration(
    source: &SourceFile,
    node: &ConcreteNode,
    tokens: &[Token],
) -> Result<SurfaceConstructorDeclaration, ProjectionError> {
    require_kind(node, NodeKind::ConstructorDeclaration)?;
    let name_token = direct_tokens(node, tokens)
        .find(|token| matches!(token.kind, TokenKind::UpperIdentifier(_)))
        .ok_or(ProjectionError::MalformedTree(
            InternalReason::UnexpectedShape,
        ))?;
    let TokenKind::UpperIdentifier(name) = &name_token.kind else {
        return malformed(InternalReason::UnexpectedShape);
    };
    let fields = child_nodes(node)
        .filter(|child| child.kind == NodeKind::Type)
        .map(|field| project_type(source, field, tokens))
        .collect::<Result<Vec<_>, _>>()?;
    Ok(SurfaceConstructorDeclaration {
        name: SurfaceName {
            text: name.clone(),
            span: name_token.span,
        },
        fields,
        span: node_span(source, node, tokens)?,
    })
}

fn project_definition(
    source: &SourceFile,
    node: &ConcreteNode,
    tokens: &[Token],
) -> Result<SurfaceDefinition, ProjectionError> {
    let public = direct_tokens(node, tokens).any(|token| token.kind == TokenKind::Pub);
    let kind = match node.kind {
        NodeKind::EquationalGlobal => {
            let interface = only_child_of_kind(node, NodeKind::ExternalInterface)?;
            let interface_binder = only_child_of_kind(interface, NodeKind::Binder)?;
            let interface_name = project_binder(interface_binder, tokens)?.name;
            let interface_type = project_type(
                source,
                only_child_of_kind(interface, NodeKind::Type)?,
                tokens,
            )?;
            let requirements = project_requirements(source, interface, tokens)?;
            let equations = child_nodes(node)
                .filter(|child| child.kind == NodeKind::Equation)
                .map(|equation| project_equation(source, equation, tokens))
                .collect::<Result<Vec<_>, _>>()?;
            SurfaceDefinitionKind::Equational(EquationalGlobal {
                interface: SurfaceExternalInterface {
                    name: interface_name,
                    type_parameters: project_optional_type_parameters(source, interface, tokens)?,
                    annotation: interface_type,
                    requirements,
                    span: node_span(source, interface, tokens)?,
                },
                equations,
            })
        }
        NodeKind::InlineOperationalGlobal => {
            let header = only_child_of_kind(node, NodeKind::InlineOperationalHeader)?;
            let name = project_binder(only_child_of_kind(header, NodeKind::Binder)?, tokens)?.name;
            let parameters = child_nodes(header)
                .filter(|child| child.kind == NodeKind::TypedPattern)
                .map(|parameter| project_typed_pattern(source, parameter, tokens))
                .collect::<Result<Vec<_>, _>>()?;
            let result_type =
                project_type(source, only_child_of_kind(header, NodeKind::Type)?, tokens)?;
            let result_effects = optional_child_of_kind(header, NodeKind::EffectRow)?
                .map(|row| project_effect_row(source, row, tokens))
                .transpose()?;
            let requirements = project_requirements(source, header, tokens)?;
            let body = project_block(source, only_child_of_kind(node, NodeKind::Block)?, tokens)?;
            SurfaceDefinitionKind::InlineOperational(InlineOperationalGlobal {
                header: SurfaceInlineOperationalHeader {
                    name,
                    type_parameters: project_optional_type_parameters(source, header, tokens)?,
                    parameters,
                    result_type,
                    result_effects,
                    requirements,
                    span: node_span(source, header, tokens)?,
                },
                body,
            })
        }
        _ => return malformed(InternalReason::UnexpectedShape),
    };
    Ok(SurfaceDefinition {
        public,
        kind,
        span: node_span(source, node, tokens)?,
    })
}

fn project_equation(
    source: &SourceFile,
    equation: &ConcreteNode,
    tokens: &[Token],
) -> Result<SurfaceEquation, ProjectionError> {
    let pending = project_equation_head(source, equation, tokens)?;
    let body = project_expression(source, expression_child(equation)?, tokens)?;
    Ok(SurfaceEquation {
        name: pending.name,
        patterns: pending.patterns,
        body,
        span: pending.span,
    })
}

fn project_equation_head(
    source: &SourceFile,
    equation: &ConcreteNode,
    tokens: &[Token],
) -> Result<PendingEquation, ProjectionError> {
    require_kind(equation, NodeKind::Equation)?;
    let name = project_binder(only_child_of_kind(equation, NodeKind::Binder)?, tokens)?.name;
    let patterns = child_nodes(equation)
        .filter(|child| child.kind == NodeKind::Pattern)
        .map(|pattern| project_pattern(source, pattern, tokens))
        .collect::<Result<Vec<_>, _>>()?;
    Ok(PendingEquation {
        name,
        patterns,
        span: node_span(source, equation, tokens)?,
    })
}

fn project_requirements(
    source: &SourceFile,
    owner: &ConcreteNode,
    tokens: &[Token],
) -> Result<Vec<SurfaceRequirement>, ProjectionError> {
    let Some(clause) = optional_child_of_kind(owner, NodeKind::WhereClause)? else {
        return Ok(Vec::new());
    };
    child_nodes(clause)
        .filter(|child| child.kind == NodeKind::InterfaceApplication)
        .map(|application| project_interface_application(source, application, tokens))
        .collect()
}

fn project_interface_application(
    source: &SourceFile,
    node: &ConcreteNode,
    tokens: &[Token],
) -> Result<SurfaceRequirement, ProjectionError> {
    require_kind(node, NodeKind::InterfaceApplication)?;
    let interface = if let Some(qualified) = optional_child_of_kind(node, NodeKind::QualifiedName)?
    {
        SurfaceReference::Qualified(project_qualified_name(source, qualified, tokens)?)
    } else {
        let name = direct_tokens(node, tokens)
            .find(|token| matches!(token.kind, TokenKind::UpperIdentifier(_)))
            .ok_or(ProjectionError::MalformedTree(
                InternalReason::UnexpectedShape,
            ))?;
        SurfaceReference::Unqualified(surface_name(name)?)
    };
    let arguments = child_nodes(node)
        .filter(|child| matches!(child.kind, NodeKind::Type | NodeKind::EffectRow))
        .map(|argument| project_type(source, argument, tokens))
        .collect::<Result<Vec<_>, _>>()?;
    if arguments.is_empty() {
        return malformed(InternalReason::UnexpectedShape);
    }
    Ok(SurfaceRequirement {
        interface,
        arguments: arguments.into_boxed_slice(),
        span: node_span(source, node, tokens)?,
    })
}

fn project_expression(
    source: &SourceFile,
    node: &ConcreteNode,
    tokens: &[Token],
) -> Result<SurfaceExpr, ProjectionError> {
    let mut tasks = vec![ExpressionTask::Visit(node)];
    let mut projected = Vec::new();
    while let Some(task) = tasks.pop() {
        match task {
            ExpressionTask::Visit(node) => match node.kind {
                NodeKind::Block => {
                    schedule_block(source, node, tokens, &mut tasks)?;
                }
                NodeKind::FunctionExpression => {
                    let mut parameters = child_nodes(node)
                        .filter(|child| child.kind == NodeKind::Pattern)
                        .map(|pattern| project_pattern(source, pattern, tokens))
                        .collect::<Result<Vec<_>, _>>()?;
                    let parameter = if parameters.len() == 1 {
                        parameters.pop().ok_or(ProjectionError::MalformedTree(
                            InternalReason::UnexpectedShape,
                        ))?
                    } else {
                        let first = parameters.first().ok_or(ProjectionError::MalformedTree(
                            InternalReason::UnexpectedShape,
                        ))?;
                        let last = parameters.last().ok_or(ProjectionError::MalformedTree(
                            InternalReason::UnexpectedShape,
                        ))?;
                        SurfacePattern {
                            span: join_spans(source, first.span, last.span)?,
                            kind: SurfacePatternKind::Tuple(parameters),
                        }
                    };
                    let body = only_child_of_kind(node, NodeKind::Block)?;
                    tasks.push(ExpressionTask::FinishFunction {
                        parameter,
                        span: node_span(source, node, tokens)?,
                    });
                    tasks.push(ExpressionTask::Visit(body));
                }
                NodeKind::EqualityExpression => schedule_binary(
                    node,
                    tokens,
                    &TokenKind::EqualEqual,
                    SurfaceExprKind::Equal,
                    &mut tasks,
                )?,
                NodeKind::AdditiveExpression => schedule_binary(
                    node,
                    tokens,
                    &TokenKind::Plus,
                    SurfaceExprKind::Add,
                    &mut tasks,
                )?,
                NodeKind::MultiplicativeExpression => schedule_binary(
                    node,
                    tokens,
                    &TokenKind::Star,
                    SurfaceExprKind::Multiply,
                    &mut tasks,
                )?,
                NodeKind::ApplicationExpression => {
                    let (function, argument) = expression_pair(node)?;
                    tasks.push(ExpressionTask::FinishApplication);
                    tasks.push(ExpressionTask::Visit(argument));
                    tasks.push(ExpressionTask::Visit(function));
                }
                NodeKind::TupleExpression => {
                    let elements = child_nodes(node)
                        .filter(|child| is_expression_kind(child.kind))
                        .collect::<Vec<_>>();
                    if elements.len() < 2 {
                        return malformed(InternalReason::UnexpectedShape);
                    }
                    tasks.push(ExpressionTask::FinishTuple {
                        count: elements.len(),
                        span: node_span(source, node, tokens)?,
                    });
                    tasks.extend(elements.into_iter().rev().map(ExpressionTask::Visit));
                }
                NodeKind::MatchExpression => {
                    let scrutinee = expression_child(node)?;
                    let arms = child_nodes(node)
                        .filter(|child| child.kind == NodeKind::MatchArm)
                        .map(|arm| {
                            Ok((
                                project_pattern(
                                    source,
                                    only_child_of_kind(arm, NodeKind::Pattern)?,
                                    tokens,
                                )?,
                                expression_child(arm)?,
                                node_span(source, arm, tokens)?,
                            ))
                        })
                        .collect::<Result<Vec<_>, ProjectionError>>()?;
                    if arms.is_empty() {
                        return malformed(InternalReason::UnexpectedShape);
                    }
                    tasks.push(ExpressionTask::FinishMatch {
                        arms: arms
                            .iter()
                            .map(|(pattern, _, span)| (pattern.clone(), *span))
                            .collect(),
                        span: node_span(source, node, tokens)?,
                    });
                    tasks.extend(
                        arms.into_iter()
                            .rev()
                            .map(|(_, body, _)| ExpressionTask::Visit(body)),
                    );
                    tasks.push(ExpressionTask::Visit(scrutinee));
                }
                NodeKind::PerformExpression => {
                    let reference = only_child_of_kind(node, NodeKind::OperationReference)?;
                    let (effect, arguments, operation) =
                        project_operation_reference(source, reference, tokens)?;
                    let operand = expression_child(node)?;
                    tasks.push(ExpressionTask::FinishPerform {
                        effect,
                        arguments,
                        operation,
                        span: node_span(source, node, tokens)?,
                    });
                    tasks.push(ExpressionTask::Visit(operand));
                }
                NodeKind::ResumeExpression => {
                    let value = expression_child(node)?;
                    tasks.push(ExpressionTask::FinishResume(node_span(
                        source, node, tokens,
                    )?));
                    tasks.push(ExpressionTask::Visit(value));
                }
                NodeKind::ProviderResourceExpression => {
                    let family = project_effect_instance(
                        source,
                        only_child_of_kind(node, NodeKind::EffectInstance)?,
                        tokens,
                    )?;
                    let Some(argument) = family.arguments.first() else {
                        return malformed(InternalReason::UnexpectedShape);
                    };
                    let SurfaceTypeKind::Named(SurfaceReference::Unqualified(identity)) =
                        &argument.kind
                    else {
                        return malformed(InternalReason::UnexpectedShape);
                    };
                    let identity = identity.clone();
                    let mut arguments = family.arguments;
                    let _ = arguments.remove(0);
                    let arguments = if arguments.is_empty() {
                        None
                    } else {
                        Some(arguments)
                    };
                    let handle =
                        project_binder(only_child_of_kind(node, NodeKind::Binder)?, tokens)?;
                    tasks.push(ExpressionTask::FinishProviderResource {
                        identity,
                        arguments,
                        family: family.effect,
                        handle: handle.name,
                        span: node_span(source, node, tokens)?,
                    });
                    tasks.push(ExpressionTask::Visit(only_child_of_kind(
                        node,
                        NodeKind::Block,
                    )?));
                    tasks.push(ExpressionTask::Visit(only_child_of_kind(
                        node,
                        NodeKind::PrimaryExpression,
                    )?));
                }
                NodeKind::ResourceExpression => {
                    let identity = direct_tokens(node, tokens)
                        .find(|token| matches!(token.kind, TokenKind::UpperIdentifier(_)))
                        .ok_or(ProjectionError::MalformedTree(
                            InternalReason::UnexpectedShape,
                        ))?;
                    let handle =
                        project_binder(only_child_of_kind(node, NodeKind::Binder)?, tokens)?;
                    tasks.push(ExpressionTask::FinishResource {
                        kind: match direct_tokens(node, tokens).find_map(|token| {
                            if let TokenKind::Identifier(name) = &token.kind {
                                Some(name.as_str())
                            } else {
                                None
                            }
                        }) {
                            Some("cell") => crate::surface::SurfaceResourceKind::Cell,
                            Some("native_buffer") => {
                                crate::surface::SurfaceResourceKind::NativeBuffer
                            }
                            _ => return malformed(InternalReason::UnexpectedShape),
                        },
                        identity: surface_name(identity)?,
                        handle: handle.name,
                        span: node_span(source, node, tokens)?,
                    });
                    tasks.push(ExpressionTask::Visit(only_child_of_kind(
                        node,
                        NodeKind::Block,
                    )?));
                    tasks.push(ExpressionTask::Visit(only_child_of_kind(
                        node,
                        NodeKind::PrimaryExpression,
                    )?));
                }
                NodeKind::CleanupExpression => {
                    let mut children = child_nodes(node);
                    let action = children.next().ok_or(ProjectionError::MalformedTree(
                        InternalReason::UnexpectedShape,
                    ))?;
                    let body = children.next().ok_or(ProjectionError::MalformedTree(
                        InternalReason::UnexpectedShape,
                    ))?;
                    tasks.push(ExpressionTask::FinishCleanup(node_span(
                        source, node, tokens,
                    )?));
                    tasks.push(ExpressionTask::Visit(body));
                    tasks.push(ExpressionTask::Visit(action));
                }
                NodeKind::HookExpression | NodeKind::RegistrationExpression => {
                    let effect = project_effect_instance(
                        source,
                        only_child_of_kind(node, NodeKind::EffectInstance)?,
                        tokens,
                    )?;
                    let span = node_span(source, node, tokens)?;
                    tasks.push(if node.kind == NodeKind::HookExpression {
                        ExpressionTask::FinishHook { effect, span }
                    } else {
                        ExpressionTask::FinishRegistration { effect, span }
                    });
                    tasks.push(ExpressionTask::Visit(only_child_of_kind(
                        node,
                        NodeKind::Block,
                    )?));
                    if node.kind == NodeKind::RegistrationExpression {
                        tasks.push(ExpressionTask::Visit(only_child_of_kind(
                            node,
                            NodeKind::PrimaryExpression,
                        )?));
                    }
                }
                NodeKind::HandlerExpression => {
                    let body = expression_child(node)?;
                    let effect = project_effect_instance(
                        source,
                        only_child_of_kind(node, NodeKind::EffectInstance)?,
                        tokens,
                    )?;
                    let clauses = child_nodes(node)
                        .filter(|child| child.kind == NodeKind::HandlerClause)
                        .map(|clause| {
                            let operation = project_binder(
                                only_child_of_kind(clause, NodeKind::Binder)?,
                                tokens,
                            )?
                            .name;
                            let pattern = project_pattern(
                                source,
                                only_child_of_kind(clause, NodeKind::Pattern)?,
                                tokens,
                            )?;
                            Ok((
                                operation,
                                pattern,
                                expression_child(clause)?,
                                node_span(source, clause, tokens)?,
                            ))
                        })
                        .collect::<Result<Vec<_>, ProjectionError>>()?;
                    tasks.push(ExpressionTask::FinishHandle {
                        effect,
                        clauses: clauses
                            .iter()
                            .map(|(operation, pattern, _, span)| {
                                (operation.clone(), pattern.clone(), *span)
                            })
                            .collect(),
                        span: node_span(source, node, tokens)?,
                    });
                    tasks.extend(
                        clauses
                            .into_iter()
                            .rev()
                            .map(|(_, _, body, _)| ExpressionTask::Visit(body)),
                    );
                    tasks.push(ExpressionTask::Visit(body));
                }
                NodeKind::PrimaryExpression => {
                    if let Some(group) =
                        optional_child_of_kind(node, NodeKind::ParenthesizedExpression)?
                    {
                        schedule_group(source, group, tokens, &mut tasks, &mut projected)?;
                    } else if let Some(perform) =
                        optional_child_of_kind(node, NodeKind::PerformExpression)?
                    {
                        tasks.push(ExpressionTask::Visit(perform));
                    } else if let Some(hook) =
                        optional_child_of_kind(node, NodeKind::HookExpression)?
                    {
                        tasks.push(ExpressionTask::Visit(hook));
                    } else if let Some(registration) =
                        optional_child_of_kind(node, NodeKind::RegistrationExpression)?
                    {
                        tasks.push(ExpressionTask::Visit(registration));
                    } else if let Some(cleanup) =
                        optional_child_of_kind(node, NodeKind::CleanupExpression)?
                    {
                        tasks.push(ExpressionTask::Visit(cleanup));
                    } else if let Some(name) =
                        optional_child_of_kind(node, NodeKind::QualifiedName)?
                    {
                        let name = project_qualified_name(source, name, tokens)?;
                        projected.push(SurfaceExpr {
                            span: name.span,
                            kind: SurfaceExprKind::Name(SurfaceReference::Qualified(name)),
                        });
                    } else {
                        projected.push(project_primitive(node, tokens)?);
                    }
                }
                NodeKind::ParenthesizedExpression => {
                    schedule_group(source, node, tokens, &mut tasks, &mut projected)?;
                }
                _ => return malformed(InternalReason::UnexpectedShape),
            },
            ExpressionTask::FinishBinary {
                make_kind,
                operator_span,
            } => {
                let (left, right) = take_expression_pair(&mut projected)?;
                let span = join_spans(source, left.span, right.span)?;
                projected.push(SurfaceExpr {
                    kind: make_kind(BinaryExpr {
                        left: Box::new(left),
                        right: Box::new(right),
                        operator_span,
                    }),
                    span,
                });
            }
            ExpressionTask::FinishApplication => {
                let (function, argument) = take_expression_pair(&mut projected)?;
                let span = join_spans(source, function.span, argument.span)?;
                projected.push(SurfaceExpr {
                    kind: SurfaceExprKind::Apply(ApplicationExpr {
                        function: Box::new(function),
                        argument: Box::new(argument),
                    }),
                    span,
                });
            }
            ExpressionTask::FinishTuple { count, span } => {
                let split =
                    projected
                        .len()
                        .checked_sub(count)
                        .ok_or(ProjectionError::MalformedTree(
                            InternalReason::UnexpectedShape,
                        ))?;
                let elements = projected.split_off(split);
                projected.push(SurfaceExpr {
                    kind: SurfaceExprKind::Tuple(elements),
                    span,
                });
            }
            ExpressionTask::FinishMatch { arms, span } => {
                let required = arms.len().saturating_add(1);
                let split =
                    projected
                        .len()
                        .checked_sub(required)
                        .ok_or(ProjectionError::MalformedTree(
                            InternalReason::UnexpectedShape,
                        ))?;
                let mut expressions = projected.split_off(split).into_iter();
                let scrutinee = expressions.next().ok_or(ProjectionError::MalformedTree(
                    InternalReason::UnexpectedShape,
                ))?;
                let projected_arms = arms
                    .into_iter()
                    .map(|(pattern, arm_span)| {
                        let body = expressions.next().ok_or(ProjectionError::MalformedTree(
                            InternalReason::UnexpectedShape,
                        ))?;
                        Ok(SurfaceMatchArm {
                            pattern,
                            body,
                            span: arm_span,
                        })
                    })
                    .collect::<Result<Vec<_>, ProjectionError>>()?;
                if expressions.next().is_some() {
                    return malformed(InternalReason::UnexpectedShape);
                }
                projected.push(SurfaceExpr {
                    kind: SurfaceExprKind::Match(SurfaceMatchExpr {
                        scrutinee: Box::new(scrutinee),
                        arms: projected_arms,
                    }),
                    span,
                });
            }
            ExpressionTask::FinishPerform {
                effect,
                arguments,
                operation,
                span,
            } => {
                let operand = projected.pop().ok_or(ProjectionError::MalformedTree(
                    InternalReason::UnexpectedShape,
                ))?;
                projected.push(SurfaceExpr {
                    kind: SurfaceExprKind::Perform(SurfacePerformExpr {
                        effect,
                        arguments,
                        operation,
                        operand: Box::new(operand),
                    }),
                    span,
                });
            }
            ExpressionTask::FinishResume(span) => {
                let value = projected.pop().ok_or(ProjectionError::MalformedTree(
                    InternalReason::UnexpectedShape,
                ))?;
                projected.push(SurfaceExpr {
                    kind: SurfaceExprKind::Resume(Box::new(value)),
                    span,
                });
            }
            ExpressionTask::FinishProviderResource {
                family,
                identity,
                arguments,
                handle,
                span,
            } => {
                let (initializer, body) = take_expression_pair(&mut projected)?;
                let SurfaceExprKind::Block(body) = body.kind else {
                    return malformed(InternalReason::UnexpectedShape);
                };
                projected.push(SurfaceExpr {
                    kind: SurfaceExprKind::ProviderResource(Box::new(
                        crate::surface::SurfaceProviderResourceExpr {
                            family,
                            identity,
                            arguments,
                            handle,
                            initializer,
                            body,
                        },
                    )),
                    span,
                });
            }
            ExpressionTask::FinishResource {
                kind,
                identity,
                handle,
                span,
            } => {
                let (initializer, body) = take_expression_pair(&mut projected)?;
                let SurfaceExprKind::Block(body) = body.kind else {
                    return malformed(InternalReason::UnexpectedShape);
                };
                projected.push(SurfaceExpr {
                    kind: SurfaceExprKind::Resource(Box::new(
                        crate::surface::SurfaceResourceExpr {
                            kind,
                            identity,
                            handle,
                            initializer,
                            body,
                        },
                    )),
                    span,
                });
            }
            ExpressionTask::FinishHook { effect, span } => {
                let body = projected.pop().ok_or(ProjectionError::MalformedTree(
                    InternalReason::UnexpectedShape,
                ))?;
                let SurfaceExprKind::Block(body) = body.kind else {
                    return malformed(InternalReason::UnexpectedShape);
                };
                projected.push(SurfaceExpr {
                    kind: SurfaceExprKind::Hook(Box::new(crate::surface::SurfaceHookExpr {
                        effect,
                        body,
                    })),
                    span,
                });
            }
            ExpressionTask::FinishCleanup(span) => {
                let (action, body) = take_expression_pair(&mut projected)?;
                let SurfaceExprKind::Block(body) = body.kind else {
                    return malformed(InternalReason::UnexpectedShape);
                };
                projected.push(SurfaceExpr {
                    kind: SurfaceExprKind::Cleanup(Box::new(crate::surface::SurfaceCleanupExpr {
                        action,
                        body,
                    })),
                    span,
                });
            }
            ExpressionTask::FinishRegistration { effect, span } => {
                let (transformer, body) = take_expression_pair(&mut projected)?;
                let SurfaceExprKind::Block(body) = body.kind else {
                    return malformed(InternalReason::UnexpectedShape);
                };
                projected.push(SurfaceExpr {
                    kind: SurfaceExprKind::Registration(Box::new(
                        crate::surface::SurfaceRegistrationExpr {
                            effect,
                            transformer,
                            body,
                        },
                    )),
                    span,
                });
            }
            ExpressionTask::FinishHandle {
                effect,
                clauses,
                span,
            } => {
                let split = projected
                    .len()
                    .checked_sub(clauses.len().saturating_add(1))
                    .ok_or(ProjectionError::MalformedTree(
                        InternalReason::UnexpectedShape,
                    ))?;
                let mut expressions = projected.split_off(split).into_iter();
                let body = expressions.next().ok_or(ProjectionError::MalformedTree(
                    InternalReason::UnexpectedShape,
                ))?;
                let clauses = clauses
                    .into_iter()
                    .map(|(operation, pattern, clause_span)| {
                        Ok(SurfaceHandlerClause {
                            operation,
                            pattern,
                            body: expressions.next().ok_or(ProjectionError::MalformedTree(
                                InternalReason::UnexpectedShape,
                            ))?,
                            span: clause_span,
                        })
                    })
                    .collect::<Result<Vec<_>, ProjectionError>>()?;
                projected.push(SurfaceExpr {
                    kind: SurfaceExprKind::Handle(SurfaceHandleExpr {
                        body: Box::new(body),
                        effect,
                        clauses,
                    }),
                    span,
                });
            }
            ExpressionTask::FinishBlock { declarations, span } => {
                let required = declarations
                    .iter()
                    .map(PendingLocalDeclaration::initializer_count)
                    .sum::<usize>()
                    .saturating_add(1);
                let split =
                    projected
                        .len()
                        .checked_sub(required)
                        .ok_or(ProjectionError::MalformedTree(
                            InternalReason::UnexpectedShape,
                        ))?;
                let mut expressions = projected.split_off(split).into_iter();
                let mut projected_declarations = Vec::with_capacity(declarations.len());
                for declaration in declarations {
                    match declaration {
                        PendingLocalDeclaration::Binding(binding) => {
                            let initializer = expressions.next().ok_or(
                                ProjectionError::MalformedTree(InternalReason::UnexpectedShape),
                            )?;
                            projected_declarations.push(SurfaceLocalDeclaration::Binding(
                                Box::new(SurfaceBinding {
                                    pattern: binding.pattern,
                                    annotation: binding.annotation,
                                    initializer,
                                    span: binding.span,
                                }),
                            ));
                        }
                        PendingLocalDeclaration::Recursive(group) => {
                            let mut members = Vec::with_capacity(group.members.len());
                            for member in group.members {
                                let initializer = expressions.next().ok_or(
                                    ProjectionError::MalformedTree(InternalReason::UnexpectedShape),
                                )?;
                                members.push(SurfaceRecursiveMember {
                                    introducer_span: member.introducer_span,
                                    binder: member.binder,
                                    annotation: member.annotation,
                                    initializer,
                                    span: member.span,
                                });
                            }
                            projected_declarations.push(SurfaceLocalDeclaration::Recursive(
                                SurfaceRecursiveGroup {
                                    members,
                                    span: group.span,
                                },
                            ));
                        }
                        PendingLocalDeclaration::Newtype(newtype) => {
                            projected_declarations.push(SurfaceLocalDeclaration::Newtype(newtype));
                        }
                        PendingLocalDeclaration::Evidence(evidence) => {
                            let mut equations = Vec::with_capacity(evidence.equations.len());
                            for equation in evidence.equations {
                                equations.push(SurfaceEquation {
                                    name: equation.name,
                                    patterns: equation.patterns,
                                    body: expressions.next().ok_or(
                                        ProjectionError::MalformedTree(
                                            InternalReason::UnexpectedShape,
                                        ),
                                    )?,
                                    span: equation.span,
                                });
                            }
                            projected_declarations.push(SurfaceLocalDeclaration::Evidence(
                                Box::new(crate::surface::SurfaceLexicalEvidence {
                                    application: evidence.application,
                                    equations,
                                    span: evidence.span,
                                }),
                            ));
                        }
                    }
                }
                let result = expressions.next().ok_or(ProjectionError::MalformedTree(
                    InternalReason::UnexpectedShape,
                ))?;
                if expressions.next().is_some() {
                    return malformed(InternalReason::UnexpectedShape);
                }
                projected.push(SurfaceExpr {
                    kind: SurfaceExprKind::Block(SurfaceBlock {
                        declarations: projected_declarations,
                        result: Box::new(result),
                        span,
                    }),
                    span,
                });
            }
            ExpressionTask::FinishFunction { parameter, span } => {
                let body = projected.pop().ok_or(ProjectionError::MalformedTree(
                    InternalReason::UnexpectedShape,
                ))?;
                let SurfaceExprKind::Block(body) = body.kind else {
                    return malformed(InternalReason::UnexpectedShape);
                };
                projected.push(SurfaceExpr {
                    kind: SurfaceExprKind::Function(FunctionExpr { parameter, body }),
                    span,
                });
            }
            ExpressionTask::ApplyGroupingSpan(span) => {
                let Some(expression) = projected.last_mut() else {
                    return malformed(InternalReason::UnexpectedShape);
                };
                expression.span = span;
            }
        }
    }
    if projected.len() != 1 {
        return malformed(InternalReason::UnexpectedShape);
    }
    projected.pop().ok_or(ProjectionError::MalformedTree(
        InternalReason::UnexpectedShape,
    ))
}

enum ExpressionTask<'a> {
    Visit(&'a ConcreteNode),
    FinishBinary {
        make_kind: fn(BinaryExpr) -> SurfaceExprKind,
        operator_span: Span,
    },
    FinishApplication,
    FinishPerform {
        effect: SurfaceReference,
        arguments: Vec<SurfaceType>,
        operation: SurfaceName,
        span: Span,
    },
    FinishResume(Span),
    FinishCleanup(Span),
    FinishProviderResource {
        family: SurfaceReference,
        identity: SurfaceName,
        arguments: Option<Vec<SurfaceType>>,
        handle: SurfaceName,
        span: Span,
    },
    FinishResource {
        kind: crate::surface::SurfaceResourceKind,
        identity: SurfaceName,
        handle: SurfaceName,
        span: Span,
    },
    FinishHook {
        effect: SurfaceEffectInstance,
        span: Span,
    },
    FinishRegistration {
        effect: SurfaceEffectInstance,
        span: Span,
    },
    FinishHandle {
        effect: SurfaceEffectInstance,
        clauses: Vec<(SurfaceName, SurfacePattern, Span)>,
        span: Span,
    },
    FinishTuple {
        count: usize,
        span: Span,
    },
    FinishMatch {
        arms: Vec<(SurfacePattern, Span)>,
        span: Span,
    },
    FinishBlock {
        declarations: Vec<PendingLocalDeclaration>,
        span: Span,
    },
    FinishFunction {
        parameter: SurfacePattern,
        span: Span,
    },
    ApplyGroupingSpan(Span),
}

enum PendingLocalDeclaration {
    Evidence(Box<PendingLexicalEvidence>),
    Binding(Box<PendingBinding>),
    Recursive(PendingRecursiveGroup),
    Newtype(SurfaceTypeDeclaration),
}

impl PendingLocalDeclaration {
    fn initializer_count(&self) -> usize {
        match self {
            Self::Binding(_) => 1,
            Self::Recursive(group) => group.members.len(),
            Self::Evidence(source) => source.equations.len(),
            Self::Newtype(_) => 0,
        }
    }
}

struct PendingBinding {
    pattern: SurfacePattern,
    annotation: Option<SurfaceType>,
    span: Span,
}

struct PendingEquation {
    name: SurfaceName,
    patterns: Vec<SurfacePattern>,
    span: Span,
}

struct PendingLexicalEvidence {
    application: crate::surface::SurfaceInterfaceApplication,
    equations: Vec<PendingEquation>,
    span: Span,
}

struct PendingRecursiveGroup {
    members: Vec<PendingRecursiveMember>,
    span: Span,
}

struct PendingRecursiveMember {
    introducer_span: Span,
    binder: SurfaceBinder,
    annotation: SurfaceType,
    span: Span,
}

fn schedule_block<'a>(
    source: &SourceFile,
    node: &'a ConcreteNode,
    tokens: &[Token],
    tasks: &mut Vec<ExpressionTask<'a>>,
) -> Result<(), ProjectionError> {
    require_kind(node, NodeKind::Block)?;
    let mut declarations = Vec::new();
    let mut initializers = Vec::new();
    let mut result = None;
    for child in child_nodes(node) {
        if child.kind == NodeKind::LocalBinding {
            let pattern = project_pattern(
                source,
                only_child_of_kind(child, NodeKind::Pattern)?,
                tokens,
            )?;
            let annotation = optional_child_of_kind(child, NodeKind::Type)?
                .map(|annotation| project_type(source, annotation, tokens))
                .transpose()?;
            declarations.push(PendingLocalDeclaration::Binding(Box::new(PendingBinding {
                pattern,
                annotation,
                span: node_span(source, child, tokens)?,
            })));
            initializers.push(expression_child(child)?);
        } else if child.kind == NodeKind::RecursiveBindingGroup {
            let mut introducers = direct_tokens(child, tokens);
            let let_token = introducers.next().ok_or(ProjectionError::MalformedTree(
                InternalReason::UnexpectedShape,
            ))?;
            let rec_token = introducers.next().ok_or(ProjectionError::MalformedTree(
                InternalReason::UnexpectedShape,
            ))?;
            if !matches!(let_token.kind, TokenKind::Let)
                || !matches!(rec_token.kind, TokenKind::Rec)
            {
                return malformed(InternalReason::UnexpectedShape);
            }
            let first_introducer = join_spans(source, let_token.span, rec_token.span)?;
            let mut member_introducers = std::iter::once(first_introducer).chain(
                introducers
                    .filter(|token| matches!(token.kind, TokenKind::And))
                    .map(|token| token.span),
            );
            let mut members = Vec::new();
            for member in child_nodes(child) {
                if member.kind != NodeKind::RecursiveBindingMember {
                    return malformed(InternalReason::UnexpectedShape);
                }
                members.push(PendingRecursiveMember {
                    introducer_span: member_introducers.next().ok_or(
                        ProjectionError::MalformedTree(InternalReason::UnexpectedShape),
                    )?,
                    binder: project_binder(only_child_of_kind(member, NodeKind::Binder)?, tokens)?,
                    annotation: project_type(
                        source,
                        only_child_of_kind(member, NodeKind::Type)?,
                        tokens,
                    )?,
                    span: node_span(source, member, tokens)?,
                });
                initializers.push(expression_child(member)?);
            }
            if member_introducers.next().is_some() {
                return malformed(InternalReason::UnexpectedShape);
            }
            declarations.push(PendingLocalDeclaration::Recursive(PendingRecursiveGroup {
                members,
                span: node_span(source, child, tokens)?,
            }));
        } else if child.kind == NodeKind::LexicalEvidenceDeclaration {
            let mut equations = Vec::new();
            for equation in child_nodes(child).filter(|node| node.kind == NodeKind::Equation) {
                equations.push(project_equation_head(source, equation, tokens)?);
                initializers.push(expression_child(equation)?);
            }
            declarations.push(PendingLocalDeclaration::Evidence(Box::new(
                PendingLexicalEvidence {
                    application: project_interface_application(
                        source,
                        only_child_of_kind(child, NodeKind::InterfaceApplication)?,
                        tokens,
                    )?,
                    equations,
                    span: node_span(source, child, tokens)?,
                },
            )));
        } else if child.kind == NodeKind::NewtypeDeclaration {
            declarations.push(PendingLocalDeclaration::Newtype(
                project_newtype_declaration(source, child, tokens)?,
            ));
        } else if is_expression_kind(child.kind) {
            if result.replace(child).is_some() {
                return malformed(InternalReason::UnexpectedShape);
            }
        } else {
            return malformed(InternalReason::UnexpectedShape);
        }
    }
    let result = result.ok_or(ProjectionError::MalformedTree(
        InternalReason::UnexpectedShape,
    ))?;
    tasks.push(ExpressionTask::FinishBlock {
        declarations,
        span: node_span(source, node, tokens)?,
    });
    tasks.push(ExpressionTask::Visit(result));
    for initializer in initializers.into_iter().rev() {
        tasks.push(ExpressionTask::Visit(initializer));
    }
    Ok(())
}

fn schedule_binary<'a>(
    node: &'a ConcreteNode,
    tokens: &[Token],
    operator_kind: &TokenKind,
    make_kind: fn(BinaryExpr) -> SurfaceExprKind,
    tasks: &mut Vec<ExpressionTask<'a>>,
) -> Result<(), ProjectionError> {
    let (left, right) = expression_pair(node)?;
    let mut operators =
        direct_tokens(node, tokens).filter(|token| same_token_variant(&token.kind, operator_kind));
    let operator_span = operators
        .next()
        .ok_or(ProjectionError::MalformedTree(
            InternalReason::UnexpectedShape,
        ))?
        .span;
    if operators.next().is_some() {
        return malformed(InternalReason::UnexpectedShape);
    }
    tasks.push(ExpressionTask::FinishBinary {
        make_kind,
        operator_span,
    });
    tasks.push(ExpressionTask::Visit(right));
    tasks.push(ExpressionTask::Visit(left));
    Ok(())
}

fn expression_pair(node: &ConcreteNode) -> Result<(&ConcreteNode, &ConcreteNode), ProjectionError> {
    let mut operands = child_nodes(node).filter(|child| is_expression_kind(child.kind));
    let left = operands.next().ok_or(ProjectionError::MalformedTree(
        InternalReason::UnexpectedShape,
    ))?;
    let right = operands.next().ok_or(ProjectionError::MalformedTree(
        InternalReason::UnexpectedShape,
    ))?;
    if operands.next().is_some() {
        return malformed(InternalReason::UnexpectedShape);
    }
    Ok((left, right))
}

fn take_expression_pair(
    projected: &mut Vec<SurfaceExpr>,
) -> Result<(SurfaceExpr, SurfaceExpr), ProjectionError> {
    let right = projected.pop().ok_or(ProjectionError::MalformedTree(
        InternalReason::UnexpectedShape,
    ))?;
    let left = projected.pop().ok_or(ProjectionError::MalformedTree(
        InternalReason::UnexpectedShape,
    ))?;
    Ok((left, right))
}

fn schedule_group<'a>(
    source: &SourceFile,
    node: &'a ConcreteNode,
    tokens: &[Token],
    tasks: &mut Vec<ExpressionTask<'a>>,
    projected: &mut Vec<SurfaceExpr>,
) -> Result<(), ProjectionError> {
    let span = node_span(source, node, tokens)?;
    let mut expressions = child_nodes(node).filter(|child| is_expression_kind(child.kind));
    if let Some(expression) = expressions.next() {
        if expressions.next().is_some() {
            return malformed(InternalReason::UnexpectedShape);
        }
        tasks.push(ExpressionTask::ApplyGroupingSpan(span));
        tasks.push(ExpressionTask::Visit(expression));
    } else {
        projected.push(SurfaceExpr {
            kind: SurfaceExprKind::Unit,
            span,
        });
    }
    Ok(())
}

fn project_primitive(
    node: &ConcreteNode,
    tokens: &[Token],
) -> Result<SurfaceExpr, ProjectionError> {
    let token = only_direct_token(node, tokens)?;
    let kind = match &token.kind {
        TokenKind::Integer(value) => SurfaceExprKind::Integer(value.clone()),
        TokenKind::True => SurfaceExprKind::Boolean(true),
        TokenKind::False => SurfaceExprKind::Boolean(false),
        TokenKind::Discard => SurfaceExprKind::Discard,
        TokenKind::Identifier(text) => {
            SurfaceExprKind::Name(SurfaceReference::Unqualified(SurfaceName {
                text: text.clone(),
                span: token.span,
            }))
        }
        TokenKind::UpperIdentifier(text) => {
            SurfaceExprKind::Name(SurfaceReference::Unqualified(SurfaceName {
                text: text.clone(),
                span: token.span,
            }))
        }
        _ => return malformed(InternalReason::UnexpectedShape),
    };
    Ok(SurfaceExpr {
        kind,
        span: token.span,
    })
}

fn project_block(
    source: &SourceFile,
    node: &ConcreteNode,
    tokens: &[Token],
) -> Result<SurfaceBlock, ProjectionError> {
    let expression = project_expression(source, node, tokens)?;
    let SurfaceExprKind::Block(block) = expression.kind else {
        return malformed(InternalReason::UnexpectedShape);
    };
    Ok(block)
}

fn project_binder(node: &ConcreteNode, tokens: &[Token]) -> Result<SurfaceBinder, ProjectionError> {
    require_kind(node, NodeKind::Binder)?;
    let token = only_direct_token(node, tokens)?;
    let TokenKind::Identifier(text) = &token.kind else {
        return malformed(InternalReason::UnexpectedShape);
    };
    let name = SurfaceName {
        text: text.clone(),
        span: token.span,
    };
    Ok(SurfaceBinder {
        name,
        span: token.span,
    })
}

fn surface_name(token: &Token) -> Result<SurfaceName, ProjectionError> {
    let text = match &token.kind {
        TokenKind::Identifier(text) | TokenKind::UpperIdentifier(text) => text.clone(),
        _ => return malformed(InternalReason::UnexpectedShape),
    };
    Ok(SurfaceName {
        text,
        span: token.span,
    })
}

fn project_qualified_name(
    source: &SourceFile,
    node: &ConcreteNode,
    tokens: &[Token],
) -> Result<SurfaceQualifiedName, ProjectionError> {
    require_kind(node, NodeKind::QualifiedName)?;
    let mut names = direct_tokens(node, tokens).filter(|token| {
        matches!(
            token.kind,
            TokenKind::Identifier(_) | TokenKind::UpperIdentifier(_)
        )
    });
    let qualifier = surface_name(names.next().ok_or(ProjectionError::MalformedTree(
        InternalReason::UnexpectedShape,
    ))?)?;
    let member = surface_name(names.next().ok_or(ProjectionError::MalformedTree(
        InternalReason::UnexpectedShape,
    ))?)?;
    if names.next().is_some() {
        return malformed(InternalReason::UnexpectedShape);
    }
    Ok(SurfaceQualifiedName {
        qualifier,
        member,
        span: node_span(source, node, tokens)?,
    })
}

fn project_typed_pattern(
    source: &SourceFile,
    node: &ConcreteNode,
    tokens: &[Token],
) -> Result<SurfaceTypedPattern, ProjectionError> {
    require_kind(node, NodeKind::TypedPattern)?;
    let pattern = project_pattern(source, only_child_of_kind(node, NodeKind::Pattern)?, tokens)?;
    let annotation = project_type(source, only_child_of_kind(node, NodeKind::Type)?, tokens)?;
    Ok(SurfaceTypedPattern {
        pattern,
        annotation,
        span: node_span(source, node, tokens)?,
    })
}

fn project_pattern(
    source: &SourceFile,
    node: &ConcreteNode,
    tokens: &[Token],
) -> Result<SurfacePattern, ProjectionError> {
    require_kind(node, NodeKind::Pattern)?;
    let span = node_span(source, node, tokens)?;
    let kind = if let Some(binder) = optional_child_of_kind(node, NodeKind::Binder)? {
        SurfacePatternKind::Binder(project_binder(binder, tokens)?)
    } else if optional_child_of_kind(node, NodeKind::WildcardPattern)?.is_some() {
        SurfacePatternKind::Wildcard
    } else if let Some(boolean) = optional_child_of_kind(node, NodeKind::BooleanPattern)? {
        let token = only_direct_token(boolean, tokens)?;
        SurfacePatternKind::Boolean(matches!(token.kind, TokenKind::True))
    } else if optional_child_of_kind(node, NodeKind::UnitPattern)?.is_some() {
        SurfacePatternKind::Unit
    } else if let Some(tuple) = optional_child_of_kind(node, NodeKind::TuplePattern)? {
        SurfacePatternKind::Tuple(project_pattern_children(source, tuple, tokens)?)
    } else if let Some(constructor) = optional_child_of_kind(node, NodeKind::ConstructorPattern)? {
        let name = if let Some(qualified) =
            optional_child_of_kind(constructor, NodeKind::QualifiedName)?
        {
            SurfaceReference::Qualified(project_qualified_name(source, qualified, tokens)?)
        } else {
            let token = direct_tokens(constructor, tokens)
                .find(|token| matches!(token.kind, TokenKind::UpperIdentifier(_)))
                .ok_or(ProjectionError::MalformedTree(
                    InternalReason::UnexpectedShape,
                ))?;
            SurfaceReference::Unqualified(surface_name(token)?)
        };
        let payload = if let Some(tuple) =
            optional_child_of_kind(constructor, NodeKind::TuplePattern)?
        {
            Some(Box::new(SurfacePattern {
                kind: SurfacePatternKind::Tuple(project_pattern_children(source, tuple, tokens)?),
                span: node_span(source, tuple, tokens)?,
            }))
        } else {
            optional_child_of_kind(constructor, NodeKind::Pattern)?
                .map(|payload| project_pattern(source, payload, tokens).map(Box::new))
                .transpose()?
        };
        SurfacePatternKind::Constructor { name, payload }
    } else if let Some(inner) = optional_child_of_kind(node, NodeKind::Pattern)? {
        let mut inner = project_pattern(source, inner, tokens)?;
        inner.span = span;
        return Ok(inner);
    } else {
        return malformed(InternalReason::UnexpectedShape);
    };
    Ok(SurfacePattern { kind, span })
}

fn project_pattern_children(
    source: &SourceFile,
    node: &ConcreteNode,
    tokens: &[Token],
) -> Result<Vec<SurfacePattern>, ProjectionError> {
    let patterns = child_nodes(node)
        .filter(|child| child.kind == NodeKind::Pattern)
        .map(|pattern| project_pattern(source, pattern, tokens))
        .collect::<Result<Vec<_>, _>>()?;
    if patterns.len() < 2 {
        return malformed(InternalReason::UnexpectedShape);
    }
    Ok(patterns)
}

fn project_optional_type_parameters(
    source: &SourceFile,
    owner: &ConcreteNode,
    tokens: &[Token],
) -> Result<Option<Vec<SurfaceTypeParameter>>, ProjectionError> {
    optional_child_of_kind(owner, NodeKind::TypeParameters)?
        .map(|parameters| {
            let projected = child_nodes(parameters)
                .filter(|child| child.kind == NodeKind::TypeParameter)
                .map(|parameter| project_type_parameter(source, parameter, tokens))
                .collect::<Result<Vec<_>, _>>()?;
            if projected.is_empty() {
                return malformed(InternalReason::UnexpectedShape);
            }
            Ok(projected)
        })
        .transpose()
}

fn project_type_parameter(
    source: &SourceFile,
    node: &ConcreteNode,
    tokens: &[Token],
) -> Result<SurfaceTypeParameter, ProjectionError> {
    require_kind(node, NodeKind::TypeParameter)?;
    let name = surface_name(
        direct_tokens(node, tokens)
            .find(|token| matches!(token.kind, TokenKind::UpperIdentifier(_)))
            .ok_or(ProjectionError::MalformedTree(
                InternalReason::UnexpectedShape,
            ))?,
    )?;
    let kind = optional_child_of_kind(node, NodeKind::Kind)?
        .map(|kind| project_kind(source, kind, tokens))
        .transpose()?;
    Ok(SurfaceTypeParameter {
        name,
        kind,
        span: node_span(source, node, tokens)?,
    })
}

fn project_kind(
    source: &SourceFile,
    node: &ConcreteNode,
    tokens: &[Token],
) -> Result<SurfaceKind, ProjectionError> {
    require_kind(node, NodeKind::Kind)?;
    let span = node_span(source, node, tokens)?;
    let domain = if let Some(group) = optional_child_of_kind(node, NodeKind::ParenthesizedKind)? {
        let nested = only_child_of_kind(group, NodeKind::Kind)?;
        let mut projected = project_kind(source, nested, tokens)?;
        projected.span = node_span(source, group, tokens)?;
        projected
    } else {
        let token = direct_tokens(node, tokens)
            .find(|token| matches!(token.kind, TokenKind::UpperIdentifier(_)))
            .ok_or(ProjectionError::MalformedTree(
                InternalReason::UnexpectedShape,
            ))?;
        let kind = match &token.kind {
            TokenKind::UpperIdentifier(name) if name == "Type" => SurfaceKindKind::Type,
            TokenKind::UpperIdentifier(name) if name == "EffectRow" => SurfaceKindKind::EffectRow,
            _ => return malformed(InternalReason::UnexpectedShape),
        };
        SurfaceKind {
            kind,
            span: token.span,
        }
    };
    if let Some(codomain) = optional_child_of_kind(node, NodeKind::Kind)? {
        Ok(SurfaceKind {
            kind: SurfaceKindKind::Function {
                domain: Box::new(domain),
                codomain: Box::new(project_kind(source, codomain, tokens)?),
            },
            span,
        })
    } else {
        Ok(domain)
    }
}

fn project_type(
    source: &SourceFile,
    node: &ConcreteNode,
    tokens: &[Token],
) -> Result<SurfaceType, ProjectionError> {
    let mut tasks = vec![TypeTask::VisitType(node)];
    let mut projected = Vec::new();
    while let Some(task) = tasks.pop() {
        match task {
            TypeTask::VisitType(node) => {
                if node.kind == NodeKind::EffectRow {
                    let instances = child_nodes(node)
                        .filter(|child| child.kind == NodeKind::EffectInstance)
                        .collect::<Vec<_>>();
                    let tail = direct_tokens(node, tokens)
                        .filter(|token| matches!(token.kind, TokenKind::UpperIdentifier(_)))
                        .last()
                        .map(surface_name)
                        .transpose()?;
                    let mut shapes = Vec::new();
                    let mut arguments = Vec::new();
                    for instance in instances {
                        let qualified = optional_child_of_kind(instance, NodeKind::QualifiedName)?
                            .map(|name| project_qualified_name(source, name, tokens))
                            .transpose()?;
                        let effect = if let Some(name) = qualified {
                            SurfaceReference::Qualified(name)
                        } else {
                            let token = direct_tokens(instance, tokens)
                                .find(|token| matches!(token.kind, TokenKind::UpperIdentifier(_)))
                                .ok_or(ProjectionError::MalformedTree(
                                    InternalReason::UnexpectedShape,
                                ))?;
                            SurfaceReference::Unqualified(surface_name(token)?)
                        };
                        let start = arguments.len();
                        arguments.extend(child_nodes(instance).filter(|child| {
                            matches!(child.kind, NodeKind::Type | NodeKind::EffectRow)
                        }));
                        shapes.push((
                            effect,
                            arguments.len() - start,
                            node_span(source, instance, tokens)?,
                        ));
                    }
                    tasks.push(TypeTask::FinishRow {
                        shapes,
                        tail,
                        span: node_span(source, node, tokens)?,
                    });
                    tasks.extend(arguments.into_iter().rev().map(TypeTask::VisitType));
                    continue;
                }
                require_kind(node, NodeKind::Type)?;
                let atomic = only_child_of_kind(node, NodeKind::AtomicType)?;
                if let Some(codomain) = optional_child_of_kind(node, NodeKind::Type)? {
                    let effects = optional_child_of_kind(node, NodeKind::EffectRow)?;
                    tasks.push(TypeTask::FinishFunction {
                        span: node_span(source, node, tokens)?,
                        has_effects: effects.is_some(),
                    });
                    if let Some(row) = effects {
                        tasks.push(TypeTask::VisitType(row));
                    }
                    tasks.push(TypeTask::VisitType(codomain));
                    tasks.push(TypeTask::VisitAtomic(atomic));
                } else {
                    tasks.push(TypeTask::VisitAtomic(atomic));
                }
            }
            TypeTask::VisitAtomic(node) => {
                require_kind(node, NodeKind::AtomicType)?;
                if let Some(group) = optional_child_of_kind(node, NodeKind::ParenthesizedType)? {
                    if let Some(tuple) = optional_child_of_kind(group, NodeKind::TupleType)? {
                        let elements = child_nodes(tuple)
                            .filter(|child| child.kind == NodeKind::Type)
                            .collect::<Vec<_>>();
                        if elements.len() < 2 {
                            return malformed(InternalReason::UnexpectedShape);
                        }
                        tasks.push(TypeTask::FinishTuple {
                            count: elements.len(),
                            span: node_span(source, group, tokens)?,
                        });
                        tasks.extend(elements.into_iter().rev().map(TypeTask::VisitType));
                    } else {
                        let nested = only_child_of_kind(group, NodeKind::Type)?;
                        tasks.push(TypeTask::ApplyGroupingSpan(node_span(
                            source, group, tokens,
                        )?));
                        tasks.push(TypeTask::VisitType(nested));
                    }
                } else {
                    let arguments = child_nodes(node)
                        .filter(|child| matches!(child.kind, NodeKind::Type | NodeKind::EffectRow))
                        .collect::<Vec<_>>();
                    let qualified = optional_child_of_kind(node, NodeKind::QualifiedName)?
                        .map(|name| project_qualified_name(source, name, tokens))
                        .transpose()?;
                    if arguments.is_empty() {
                        if let Some(name) = qualified {
                            projected.push(SurfaceType {
                                span: name.span,
                                kind: SurfaceTypeKind::Named(SurfaceReference::Qualified(name)),
                            });
                        } else {
                            projected.push(project_atomic_primitive(node, tokens)?);
                        }
                    } else {
                        let constructor = if let Some(name) = qualified {
                            SurfaceReference::Qualified(name)
                        } else {
                            let token = direct_tokens(node, tokens)
                                .find(|token| matches!(token.kind, TokenKind::UpperIdentifier(_)))
                                .ok_or(ProjectionError::MalformedTree(
                                    InternalReason::UnexpectedShape,
                                ))?;
                            SurfaceReference::Unqualified(surface_name(token)?)
                        };
                        tasks.push(TypeTask::FinishApplication {
                            constructor,
                            count: arguments.len(),
                            span: node_span(source, node, tokens)?,
                        });
                        tasks.extend(arguments.into_iter().rev().map(TypeTask::VisitType));
                    }
                }
            }
            TypeTask::FinishRow { shapes, tail, span } => {
                let count = shapes.iter().map(|(_, count, _)| *count).sum::<usize>();
                let split =
                    projected
                        .len()
                        .checked_sub(count)
                        .ok_or(ProjectionError::MalformedTree(
                            InternalReason::UnexpectedShape,
                        ))?;
                let mut arguments = projected.split_off(split).into_iter();
                let effects = shapes
                    .into_iter()
                    .map(|(effect, count, span)| SurfaceEffectInstance {
                        effect,
                        arguments: arguments.by_ref().take(count).collect(),
                        span,
                    })
                    .collect();
                projected.push(SurfaceType {
                    kind: SurfaceTypeKind::RowArgument(SurfaceEffectRow {
                        effects,
                        tail,
                        span,
                    }),
                    span,
                });
            }
            TypeTask::FinishFunction { span, has_effects } => {
                let effects = if has_effects {
                    let Some(SurfaceType {
                        kind: SurfaceTypeKind::RowArgument(row),
                        ..
                    }) = projected.pop()
                    else {
                        return malformed(InternalReason::UnexpectedShape);
                    };
                    Some(row)
                } else {
                    None
                };
                let codomain = projected.pop().ok_or(ProjectionError::MalformedTree(
                    InternalReason::UnexpectedShape,
                ))?;
                let domain = projected.pop().ok_or(ProjectionError::MalformedTree(
                    InternalReason::UnexpectedShape,
                ))?;
                projected.push(SurfaceType {
                    kind: SurfaceTypeKind::Function(FunctionType {
                        domain: Box::new(domain),
                        codomain: Box::new(codomain),
                        effects,
                    }),
                    span,
                });
            }
            TypeTask::FinishTuple { count, span } => {
                let split =
                    projected
                        .len()
                        .checked_sub(count)
                        .ok_or(ProjectionError::MalformedTree(
                            InternalReason::UnexpectedShape,
                        ))?;
                let elements = projected.split_off(split);
                projected.push(SurfaceType {
                    kind: SurfaceTypeKind::Tuple(elements),
                    span,
                });
            }
            TypeTask::ApplyGroupingSpan(span) => {
                let Some(projected) = projected.last_mut() else {
                    return malformed(InternalReason::UnexpectedShape);
                };
                projected.span = span;
            }
            TypeTask::FinishApplication {
                constructor,
                count,
                span,
            } => {
                let split =
                    projected
                        .len()
                        .checked_sub(count)
                        .ok_or(ProjectionError::MalformedTree(
                            InternalReason::UnexpectedShape,
                        ))?;
                let arguments = projected.split_off(split);
                projected.push(SurfaceType {
                    kind: SurfaceTypeKind::Application {
                        constructor,
                        arguments,
                    },
                    span,
                });
            }
        }
    }
    if projected.len() != 1 {
        return malformed(InternalReason::UnexpectedShape);
    }
    projected.pop().ok_or(ProjectionError::MalformedTree(
        InternalReason::UnexpectedShape,
    ))
}

fn project_effect_row(
    source: &SourceFile,
    node: &ConcreteNode,
    tokens: &[Token],
) -> Result<SurfaceEffectRow, ProjectionError> {
    require_kind(node, NodeKind::EffectRow)?;
    let SurfaceType {
        kind: SurfaceTypeKind::RowArgument(row),
        ..
    } = project_type(source, node, tokens)?
    else {
        return malformed(InternalReason::UnexpectedShape);
    };
    Ok(row)
}

fn project_effect_instance(
    source: &SourceFile,
    instance: &ConcreteNode,
    tokens: &[Token],
) -> Result<SurfaceEffectInstance, ProjectionError> {
    require_kind(instance, NodeKind::EffectInstance)?;
    let qualified = optional_child_of_kind(instance, NodeKind::QualifiedName)?
        .map(|name| project_qualified_name(source, name, tokens))
        .transpose()?;
    let effect = if let Some(name) = qualified {
        SurfaceReference::Qualified(name)
    } else {
        let token = direct_tokens(instance, tokens)
            .find(|token| matches!(token.kind, TokenKind::UpperIdentifier(_)))
            .ok_or(ProjectionError::MalformedTree(
                InternalReason::UnexpectedShape,
            ))?;
        SurfaceReference::Unqualified(surface_name(token)?)
    };
    let arguments = child_nodes(instance)
        .filter(|child| matches!(child.kind, NodeKind::Type | NodeKind::EffectRow))
        .map(|argument| project_type(source, argument, tokens))
        .collect::<Result<Vec<_>, _>>()?;
    Ok(SurfaceEffectInstance {
        effect,
        arguments,
        span: node_span(source, instance, tokens)?,
    })
}

fn project_operation_reference(
    source: &SourceFile,
    node: &ConcreteNode,
    tokens: &[Token],
) -> Result<(SurfaceReference, Vec<SurfaceType>, SurfaceName), ProjectionError> {
    require_kind(node, NodeKind::OperationReference)?;
    let effect = if let Some(qualified) = optional_child_of_kind(node, NodeKind::QualifiedName)? {
        SurfaceReference::Qualified(project_qualified_name(source, qualified, tokens)?)
    } else {
        let token = direct_tokens(node, tokens)
            .find(|token| matches!(token.kind, TokenKind::UpperIdentifier(_)))
            .ok_or(ProjectionError::MalformedTree(
                InternalReason::UnexpectedShape,
            ))?;
        SurfaceReference::Unqualified(surface_name(token)?)
    };
    let arguments = child_nodes(node)
        .filter(|child| matches!(child.kind, NodeKind::Type | NodeKind::EffectRow))
        .map(|argument| project_type(source, argument, tokens))
        .collect::<Result<Vec<_>, _>>()?;
    let operation = direct_tokens(node, tokens)
        .find(|token| matches!(token.kind, TokenKind::Identifier(_)))
        .ok_or(ProjectionError::MalformedTree(
            InternalReason::UnexpectedShape,
        ))?;
    Ok((effect, arguments, surface_name(operation)?))
}

enum TypeTask<'a> {
    VisitType(&'a ConcreteNode),
    VisitAtomic(&'a ConcreteNode),
    FinishFunction {
        span: Span,
        has_effects: bool,
    },
    FinishRow {
        shapes: Vec<(SurfaceReference, usize, Span)>,
        tail: Option<SurfaceName>,
        span: Span,
    },
    FinishTuple {
        count: usize,
        span: Span,
    },
    FinishApplication {
        constructor: SurfaceReference,
        count: usize,
        span: Span,
    },
    ApplyGroupingSpan(Span),
}

fn project_atomic_primitive(
    node: &ConcreteNode,
    tokens: &[Token],
) -> Result<SurfaceType, ProjectionError> {
    let token = only_direct_token(node, tokens)?;
    let kind = match token.kind {
        TokenKind::IntType => SurfaceTypeKind::Int,
        TokenKind::BoolType => SurfaceTypeKind::Bool,
        TokenKind::UnitType => SurfaceTypeKind::Unit,
        TokenKind::UpperIdentifier(ref text) => {
            SurfaceTypeKind::Named(SurfaceReference::Unqualified(SurfaceName {
                text: text.clone(),
                span: token.span,
            }))
        }
        _ => return malformed(InternalReason::UnexpectedShape),
    };
    Ok(SurfaceType {
        kind,
        span: token.span,
    })
}

fn has_recovery(node: &ConcreteNode) -> bool {
    let mut pending = vec![node];
    while let Some(node) = pending.pop() {
        for child in &node.children {
            match child {
                ConcreteElement::Missing { .. } | ConcreteElement::Error(_) => return true,
                ConcreteElement::Node(child) => pending.push(child),
                ConcreteElement::Token(_) => {}
            }
        }
    }
    false
}

fn child_nodes(node: &ConcreteNode) -> impl Iterator<Item = &ConcreteNode> {
    node.children.iter().filter_map(|child| match child {
        ConcreteElement::Node(node) => Some(node),
        _ => None,
    })
}

fn only_child_of_kind(
    node: &ConcreteNode,
    kind: NodeKind,
) -> Result<&ConcreteNode, ProjectionError> {
    child_of_kind_at(node, kind, 0, 1)
}

fn child_of_kind_at(
    node: &ConcreteNode,
    kind: NodeKind,
    index: usize,
    expected_count: usize,
) -> Result<&ConcreteNode, ProjectionError> {
    let mut matching = child_nodes(node).filter(|child| child.kind == kind);
    let selected = matching.nth(index);
    let actual_count = index.saturating_add(1).saturating_add(matching.count());
    if actual_count != expected_count {
        return malformed(InternalReason::UnexpectedShape);
    }
    selected.ok_or(ProjectionError::MalformedTree(
        InternalReason::UnexpectedShape,
    ))
}

fn optional_child_of_kind(
    node: &ConcreteNode,
    kind: NodeKind,
) -> Result<Option<&ConcreteNode>, ProjectionError> {
    let mut matching = child_nodes(node).filter(|child| child.kind == kind);
    let first = matching.next();
    if matching.next().is_some() {
        return malformed(InternalReason::UnexpectedShape);
    }
    Ok(first)
}

fn expression_child(node: &ConcreteNode) -> Result<&ConcreteNode, ProjectionError> {
    let mut matching = child_nodes(node).filter(|child| is_expression_kind(child.kind));
    let expression = matching.next();
    if matching.next().is_some() {
        return malformed(InternalReason::UnexpectedShape);
    }
    expression.ok_or(ProjectionError::MalformedTree(
        InternalReason::UnexpectedShape,
    ))
}

const fn is_expression_kind(kind: NodeKind) -> bool {
    matches!(
        kind,
        NodeKind::Block
            | NodeKind::FunctionExpression
            | NodeKind::MatchExpression
            | NodeKind::HandlerExpression
            | NodeKind::ResumeExpression
            | NodeKind::ProviderResourceExpression
            | NodeKind::ResourceExpression
            | NodeKind::HookExpression
            | NodeKind::RegistrationExpression
            | NodeKind::CleanupExpression
            | NodeKind::PerformExpression
            | NodeKind::TupleExpression
            | NodeKind::EqualityExpression
            | NodeKind::AdditiveExpression
            | NodeKind::MultiplicativeExpression
            | NodeKind::ApplicationExpression
            | NodeKind::PrimaryExpression
            | NodeKind::ParenthesizedExpression
    )
}

fn only_direct_token<'a>(
    node: &ConcreteNode,
    tokens: &'a [Token],
) -> Result<&'a Token, ProjectionError> {
    let mut indices = node.children.iter().filter_map(|child| match child {
        ConcreteElement::Token(index) => Some(*index),
        _ => None,
    });
    let index = indices.next().ok_or(ProjectionError::MalformedTree(
        InternalReason::UnexpectedShape,
    ))?;
    if indices.next().is_some() {
        return malformed(InternalReason::UnexpectedShape);
    }
    tokens.get(index).ok_or(ProjectionError::MalformedTree(
        InternalReason::TokenOutOfRange,
    ))
}

fn direct_tokens<'a>(
    node: &'a ConcreteNode,
    tokens: &'a [Token],
) -> impl Iterator<Item = &'a Token> {
    node.children.iter().filter_map(|child| match child {
        ConcreteElement::Token(index) => tokens.get(*index),
        _ => None,
    })
}

fn same_token_variant(left: &TokenKind, right: &TokenKind) -> bool {
    std::mem::discriminant(left) == std::mem::discriminant(right)
}

fn node_span(
    source: &SourceFile,
    node: &ConcreteNode,
    tokens: &[Token],
) -> Result<Span, ProjectionError> {
    let first = descendant_edge_span(node, tokens, false)?;
    let last = descendant_edge_span(node, tokens, true)?;
    join_spans(source, first, last)
}

fn descendant_edge_span(
    node: &ConcreteNode,
    tokens: &[Token],
    from_back: bool,
) -> Result<Span, ProjectionError> {
    let mut current = node;
    loop {
        let child = if from_back {
            current.children.last()
        } else {
            current.children.first()
        }
        .ok_or(ProjectionError::MalformedTree(
            InternalReason::UnexpectedShape,
        ))?;
        match child {
            ConcreteElement::Node(child) => current = child,
            ConcreteElement::Token(index) => {
                return tokens.get(*index).map(|token| token.span).ok_or(
                    ProjectionError::MalformedTree(InternalReason::TokenOutOfRange),
                );
            }
            ConcreteElement::Missing { .. } | ConcreteElement::Error(_) => {
                return Err(ProjectionError::RecoveryNodesPresent);
            }
        }
    }
}

fn join_spans(source: &SourceFile, first: Span, last: Span) -> Result<Span, ProjectionError> {
    if first.source() != source.id() || last.source() != source.id() {
        return malformed(InternalReason::ForeignSpan);
    }
    let range = ByteRange::new(first.range().start(), last.range().end())
        .map_err(|_| ProjectionError::MalformedTree(InternalReason::InvalidSpan))?;
    source
        .span(range)
        .map_err(|_| ProjectionError::MalformedTree(InternalReason::InvalidSpan))
}

fn require_kind(node: &ConcreteNode, kind: NodeKind) -> Result<(), ProjectionError> {
    if node.kind == kind {
        Ok(())
    } else {
        malformed(InternalReason::UnexpectedShape)
    }
}

fn malformed<T>(reason: InternalReason) -> Result<T, ProjectionError> {
    Err(ProjectionError::MalformedTree(reason))
}

fn project_resource_definition(
    source: &SourceFile,
    node: &ConcreteNode,
    tokens: &[Token],
) -> Result<crate::surface::SurfaceResourceDefinition, ProjectionError> {
    let fields = child_nodes(node)
        .filter(|child| child.kind == NodeKind::ResourceField)
        .collect::<Vec<_>>();
    let [
        input,
        state,
        result,
        provider,
        provided,
        interpreted,
        acquire,
        finish,
        handlers,
    ] = fields.as_slice()
    else {
        return malformed(InternalReason::UnexpectedShape);
    };
    let answer_parameters = project_optional_type_parameters(source, result, tokens)?.ok_or(
        ProjectionError::MalformedTree(InternalReason::UnexpectedShape),
    )?;
    let [answer] = answer_parameters.as_slice() else {
        return malformed(InternalReason::UnexpectedShape);
    };
    let project_field_type =
        |field| project_type(source, only_child_of_kind(field, NodeKind::Type)?, tokens);
    let project_field_binder = |field| {
        project_binder(only_child_of_kind(field, NodeKind::Binder)?, tokens)
            .map(|binder| binder.name)
    };
    let clauses = child_nodes(handlers)
        .filter(|child| child.kind == NodeKind::HandlerClause)
        .map(|clause| {
            Ok(SurfaceHandlerClause {
                operation: project_field_binder(clause)?,
                pattern: project_pattern(
                    source,
                    only_child_of_kind(clause, NodeKind::Pattern)?,
                    tokens,
                )?,
                body: project_expression(source, expression_child(clause)?, tokens)?,
                span: node_span(source, clause, tokens)?,
            })
        })
        .collect::<Result<Vec<_>, ProjectionError>>()?;
    Ok(crate::surface::SurfaceResourceDefinition {
        public: direct_tokens(node, tokens).any(|token| token.kind == TokenKind::Pub),
        name: surface_name(
            direct_tokens(node, tokens)
                .find(|token| matches!(token.kind, TokenKind::UpperIdentifier(_)))
                .ok_or(ProjectionError::MalformedTree(
                    InternalReason::UnexpectedShape,
                ))?,
        )?,
        parameters: project_optional_type_parameters(source, node, tokens)?.ok_or(
            ProjectionError::MalformedTree(InternalReason::UnexpectedShape),
        )?,
        input: project_field_type(input)?,
        state: project_field_type(state)?,
        result: project_field_type(result)?,
        answer: answer.clone(),
        provider: project_interface_application(
            source,
            only_child_of_kind(provider, NodeKind::InterfaceApplication)?,
            tokens,
        )?,
        provided: project_effect_instance(
            source,
            only_child_of_kind(provided, NodeKind::EffectInstance)?,
            tokens,
        )?,
        interpreted: project_effect_instance(
            source,
            only_child_of_kind(interpreted, NodeKind::EffectInstance)?,
            tokens,
        )?,
        acquire_binder: project_field_binder(acquire)?,
        acquire: project_expression(source, expression_child(acquire)?, tokens)?,
        finish_binder: project_field_binder(finish)?,
        finish: project_expression(source, expression_child(finish)?, tokens)?,
        handlers_binder: project_field_binder(handlers)?,
        handlers: clauses,
        span: node_span(source, node, tokens)?,
    })
}

#[cfg(test)]
mod tests {
    use crate::{
        lexer::lex,
        parser::{ResourceFailure, STRUCTURAL_DEPTH_LIMIT, parse},
        source::SourceFile,
    };

    use super::*;

    fn parsed(text: &str) -> (SourceFile, ConcreteTree) {
        let source = SourceFile::new("shape.ash", format!("main : Unit\nmain () = {text}\n"))
            .expect("the shape fixture should fit");
        let lexed = lex(&source).expect("the shape fixture should lex");
        (source, parse(lexed))
    }

    fn find_node_mut(node: &mut ConcreteNode, kind: NodeKind) -> Option<&mut ConcreteNode> {
        if node.kind == kind {
            return Some(node);
        }
        node.children.iter_mut().find_map(|child| match child {
            ConcreteElement::Node(child) => find_node_mut(child, kind),
            ConcreteElement::Token(_)
            | ConcreteElement::Missing { .. }
            | ConcreteElement::Error(_) => None,
        })
    }

    #[test]
    fn cleanup_projection_rejects_missing_duplicate_and_reordered_parts() {
        for mutation in 0..3 {
            let (source, mut tree) = parsed("cleanup action {\n42\n}");
            let root = tree.root.as_mut().expect("parsed root");
            let cleanup =
                find_node_mut(root, NodeKind::CleanupExpression).expect("cleanup expression");
            // The checked shape is exactly keyword, action expression, body block.
            match mutation {
                0 => {
                    cleanup.children.remove(1);
                }
                1 => {
                    cleanup.children.push(cleanup.children[1].clone());
                }
                _ => cleanup.children.swap(1, 2),
            }
            assert!(project_module(&source, &tree).is_err());
        }
    }

    #[test]
    fn projection_rejects_duplicate_children_hidden_by_first_match_lookup() {
        let (source, mut tree) = parsed("fn(value) {\nvalue\n}");
        let root = tree.root.as_mut().expect("the parser produced one root");
        let function = find_node_mut(root, NodeKind::FunctionExpression)
            .expect("the fixture contains a function expression");
        let pattern = function
            .children
            .iter()
            .find_map(|child| match child {
                ConcreteElement::Node(child) if child.kind == NodeKind::Pattern => {
                    Some(child.clone())
                }
                _ => None,
            })
            .expect("the function has a pattern");
        function.children.push(ConcreteElement::Node(pattern));

        assert_eq!(
            project_module(&source, &tree),
            Err(ProjectionError::MalformedTree(
                InternalReason::UnexpectedShape
            ))
        );
    }

    #[test]
    fn projection_rejects_an_unexpected_child_hidden_by_token_lookup() {
        let (source, mut tree) = parsed("value");
        let root = tree.root.as_mut().expect("the parser produced one root");
        let primary = find_node_mut(root, NodeKind::PrimaryExpression)
            .expect("the fixture contains a primary expression");
        primary.children.push(ConcreteElement::Node(ConcreteNode {
            kind: NodeKind::AtomicType,
            children: Vec::new(),
        }));

        assert_eq!(
            project_module(&source, &tree),
            Err(ProjectionError::MalformedTree(
                InternalReason::UnexpectedShape
            ))
        );
    }

    #[test]
    fn projection_rejects_a_recovery_free_public_qualified_import_shape() {
        let source = SourceFile::new("shape.ash", "pub import equality as Equality\n")
            .expect("the public qualified import fixture should fit");
        let mut tree = parse(lex(&source).expect("the fixture should lex"));
        let root = tree.root.as_mut().expect("the parser produced one root");
        let import = find_node_mut(root, NodeKind::ImportDeclaration)
            .expect("the fixture contains one import declaration");
        let recovery = import
            .children
            .iter()
            .position(|child| matches!(child, ConcreteElement::Node(node) if node.kind == NodeKind::Error))
            .expect("the parser rejects the public qualified form");
        let ConcreteElement::Node(mut recovery) = import.children.remove(recovery) else {
            panic!("the rejected suffix is retained as one error node");
        };
        import.children.extend(
            std::mem::take(&mut recovery.children)
                .into_iter()
                .filter(|child| matches!(child, ConcreteElement::Token(_))),
        );
        tree.parse_diagnostics.clear();

        assert_eq!(
            project_module(&source, &tree),
            Err(ProjectionError::MalformedTree(
                InternalReason::UnexpectedShape
            ))
        );
    }

    #[test]
    fn projection_revalidates_duplicate_token_coverage_in_the_concrete_tree() {
        let (source, mut tree) = parsed("1 + 2");
        let root = tree.root.as_mut().expect("the parser produced one root");
        let addition = find_node_mut(root, NodeKind::AdditiveExpression)
            .expect("the fixture contains an addition");
        let right = addition
            .children
            .iter_mut()
            .filter_map(|child| match child {
                ConcreteElement::Node(child) if is_expression_kind(child.kind) => Some(child),
                _ => None,
            })
            .nth(1)
            .expect("the addition has a right operand");
        let ConcreteElement::Token(index) = &mut right.children[0] else {
            panic!("the right primitive contains a token");
        };
        *index = 0;

        assert_eq!(
            project_module(&source, &tree),
            Err(ProjectionError::MalformedTree(
                InternalReason::DuplicateToken
            ))
        );
    }

    #[test]
    fn implementation_shape_requires_logical_lines_between_equations() {
        let source = SourceFile::new(
            "shape.ash",
            "impl Equal<Int> {\nequal left = left\nequal right = right\n}\n",
        )
        .expect("the implementation fixture should fit");
        let mut tree = parse(lex(&source).expect("the implementation fixture should lex"));
        let tokens = tree.tokens().to_vec();
        let root = tree.root.as_mut().expect("the parser produced one root");
        let implementation = find_node_mut(root, NodeKind::ImplementationDeclaration)
            .expect("the fixture contains an implementation");
        let separator = implementation
            .children
            .windows(3)
            .position(|children| {
                matches!(children[0], ConcreteElement::Node(ref node) if node.kind == NodeKind::Equation)
                    && matches!(children[1], ConcreteElement::Token(index) if tokens[index].kind == TokenKind::LineEnd)
                    && matches!(children[2], ConcreteElement::Node(ref node) if node.kind == NodeKind::Equation)
            })
            .map(|index| index + 1)
            .expect("the method equations have a logical-line separator");
        implementation.children.remove(separator);

        assert_eq!(
            validate_node_shape(implementation, &tokens),
            Err(ProjectionError::MalformedTree(
                InternalReason::UnexpectedShape
            ))
        );
    }

    #[test]
    fn interface_application_shape_requires_an_uppercase_qualified_member() {
        let source = SourceFile::new("shape.ash", "impl Library.Equal<Int> {\n}\n")
            .expect("the qualified implementation fixture should fit");
        let mut tree = parse(lex(&source).expect("the qualified fixture should lex"));
        let member_index = {
            let root = tree.root.as_mut().expect("the parser produced one root");
            let qualified = find_node_mut(root, NodeKind::QualifiedName)
                .expect("the fixture contains a qualified interface reference");
            qualified
                .children
                .iter()
                .filter_map(|child| match child {
                    ConcreteElement::Token(index) => Some(*index),
                    _ => None,
                })
                .nth(2)
                .expect("the qualified reference has a member token")
        };
        tree.tokens[member_index].kind = TokenKind::Identifier("equal".into());

        assert_eq!(
            project_module(&source, &tree),
            Err(ProjectionError::MalformedTree(
                InternalReason::UnexpectedShape
            ))
        );
    }

    #[test]
    fn projection_rejects_over_budget_malformed_depth_before_recursive_validation() {
        let (source, mut tree) = parsed("value");
        let mut nested = ConcreteNode {
            kind: NodeKind::ParenthesizedType,
            children: Vec::new(),
        };
        for _ in 0..4_096 {
            nested = ConcreteNode {
                kind: NodeKind::ParenthesizedType,
                children: vec![ConcreteElement::Node(nested)],
            };
        }
        tree.root
            .as_mut()
            .expect("the parser produced one root")
            .children
            .push(ConcreteElement::Node(nested));

        assert_eq!(
            project_module(&source, &tree),
            Err(ProjectionError::ResourceLimit(
                ResourceFailure::StructuralDepth {
                    limit: STRUCTURAL_DEPTH_LIMIT
                }
            ))
        );
    }

    fn nested_group_tree(depth: usize) -> (SourceFile, ConcreteTree) {
        parsed(&format!("{}1{}", "(".repeat(depth), ")".repeat(depth)))
    }

    #[test]
    fn recovery_scan_fits_the_small_stack_at_the_structural_budget() {
        std::thread::scope(|scope| {
            std::thread::Builder::new()
                .stack_size(256 * 1024)
                .spawn_scoped(scope, || {
                    let (_source, tree) = nested_group_tree(STRUCTURAL_DEPTH_LIMIT);
                    assert!(!has_recovery(tree.root().expect("the tree has one root")));
                })
                .expect("the recovery-scan thread should start")
                .join()
                .expect("the recovery scan should fit the small stack");
        });
    }

    #[test]
    fn exact_shape_validation_fits_the_small_stack_at_the_structural_budget() {
        std::thread::scope(|scope| {
            std::thread::Builder::new()
                .stack_size(256 * 1024)
                .spawn_scoped(scope, || {
                    let (_source, tree) = nested_group_tree(STRUCTURAL_DEPTH_LIMIT);
                    validate_node_shape(tree.root().expect("the tree has one root"), tree.tokens())
                        .expect("the tree shape is exact");
                })
                .expect("the shape-validation thread should start")
                .join()
                .expect("shape validation should fit the small stack");
        });
    }

    #[test]
    fn surface_projection_fits_the_small_stack_at_the_structural_budget() {
        std::thread::scope(|scope| {
            std::thread::Builder::new()
                .stack_size(256 * 1024)
                .spawn_scoped(scope, || {
                    let (source, tree) = nested_group_tree(STRUCTURAL_DEPTH_LIMIT);
                    project_surface_module(
                        &source,
                        tree.root().expect("the tree has one root"),
                        tree.tokens(),
                    )
                    .expect("surface projection should succeed");
                })
                .expect("the surface-projection thread should start")
                .join()
                .expect("surface projection should fit the small stack");
        });
    }
}
