//! Projection from recovery-free concrete syntax to spanned surface syntax.

use crate::{
    lexer::{Token, TokenKind},
    source::{ByteRange, SourceFile, Span},
    surface::{
        ApplicationExpr, BinaryExpr, EquationalGlobal, FunctionExpr, FunctionType,
        InlineOperationalGlobal, SurfaceBinder, SurfaceBinding, SurfaceBlock,
        SurfaceConstructorDeclaration, SurfaceDefinition, SurfaceDefinitionKind, SurfaceEquation,
        SurfaceExpr, SurfaceExprKind, SurfaceExternalInterface, SurfaceInlineOperationalHeader,
        SurfaceLocalDeclaration, SurfaceMatchArm, SurfaceMatchExpr, SurfaceName, SurfacePattern,
        SurfacePatternKind, SurfaceProgram, SurfaceRecursiveGroup, SurfaceRecursiveMember,
        SurfaceType, SurfaceTypeDeclaration, SurfaceTypeKind, SurfaceTypedPattern,
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

/// Projects a complete, recovery-free concrete tree to surface syntax.
///
/// # Errors
///
/// Returns [`ProjectionError::ResourceLimit`] when parsing exceeded the
/// replaceable implementation depth budget. Returns
/// [`ProjectionError::RecoveryNodesPresent`] whenever lexical or parse
/// diagnostics, missing forms, or error events remain. Returns
/// [`ProjectionError::MalformedTree`] for incomplete or inconsistent concrete
/// structure.
pub fn project(
    source: &SourceFile,
    tree: &ConcreteTree,
) -> Result<SurfaceProgram, ProjectionError> {
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
    project_program(source, root, &tree.tokens)
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
        | NodeKind::FunctionExpression
        | NodeKind::EqualityExpression
        | NodeKind::AdditiveExpression
        | NodeKind::MultiplicativeExpression
        | NodeKind::ApplicationExpression
        | NodeKind::ParenthesizedExpression
        | NodeKind::ParenthesizedType => 1,
        NodeKind::Type if child_nodes(node).any(|child| child.kind == NodeKind::Type) => 1,
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
        NodeKind::Program => {
            while shape.peek_node_is(NodeKind::TypeDeclaration) {
                shape.node(NodeKind::TypeDeclaration)?;
                shape.token(&TokenKind::LineEnd)?;
            }
            while shape.peek_node_is(NodeKind::EquationalGlobal)
                || shape.peek_node_is(NodeKind::InlineOperationalGlobal)
            {
                shape.any_node()?;
                shape.token(&TokenKind::LineEnd)?;
            }
            shape.expression()?;
            shape.optional_token(&TokenKind::LineEnd)?;
            shape.token(&TokenKind::EndOfFile)?;
        }
        NodeKind::TypeDeclaration => {
            shape.token(&TokenKind::Type)?;
            shape.token_matching(|kind| matches!(kind, TokenKind::UpperIdentifier(_)))?;
            shape.token(&TokenKind::Equal)?;
            shape.optional_token(&TokenKind::LineEnd)?;
            shape.node(NodeKind::ConstructorDeclaration)?;
            while shape.peek_token_is(&TokenKind::LineEnd) {
                shape.token(&TokenKind::LineEnd)?;
                shape.token(&TokenKind::Pipe)?;
                shape.node(NodeKind::ConstructorDeclaration)?;
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
        NodeKind::EquationalGlobal => {
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
            shape.token(&TokenKind::Colon)?;
            shape.node(NodeKind::Type)?;
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
            shape.node(NodeKind::InlineOperationalHeader)?;
            shape.node(NodeKind::Block)?;
        }
        NodeKind::InlineOperationalHeader => {
            shape.token(&TokenKind::Fn)?;
            shape.node(NodeKind::Binder)?;
            shape.token(&TokenKind::LeftParen)?;
            shape.node(NodeKind::TypedPattern)?;
            while shape.peek_token_is(&TokenKind::Comma) {
                shape.token(&TokenKind::Comma)?;
                shape.node(NodeKind::TypedPattern)?;
            }
            shape.token(&TokenKind::RightParen)?;
            shape.token(&TokenKind::Arrow)?;
            shape.node(NodeKind::Type)?;
        }
        NodeKind::Block => {
            shape.token(&TokenKind::LeftBrace)?;
            shape.token(&TokenKind::LineEnd)?;
            while shape.peek_node_is(NodeKind::LocalBinding)
                || shape.peek_node_is(NodeKind::RecursiveBindingGroup)
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
            } else {
                shape.token_matching(|kind| {
                    matches!(
                        kind,
                        TokenKind::Integer(_)
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
            shape.token_matching(|kind| matches!(kind, TokenKind::UpperIdentifier(_)))?;
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
            }
        }
        NodeKind::AtomicType => {
            if shape.peek_node_is(NodeKind::ParenthesizedType) {
                shape.node(NodeKind::ParenthesizedType)?;
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
        NodeKind::Error => return malformed(InternalReason::UnexpectedShape),
    }
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

fn project_program(
    source: &SourceFile,
    node: &ConcreteNode,
    tokens: &[Token],
) -> Result<SurfaceProgram, ProjectionError> {
    require_kind(node, NodeKind::Program)?;
    let mut type_declarations = Vec::new();
    let mut definitions = Vec::new();
    let mut result = None;
    for child in child_nodes(node) {
        match child.kind {
            NodeKind::TypeDeclaration => {
                type_declarations.push(project_type_declaration(source, child, tokens)?);
            }
            NodeKind::EquationalGlobal | NodeKind::InlineOperationalGlobal => {
                definitions.push(project_definition(source, child, tokens)?);
            }
            kind if is_expression_kind(kind) => {
                if result.is_some() {
                    return malformed(InternalReason::UnexpectedShape);
                }
                result = Some(project_expression(source, child, tokens)?);
            }
            NodeKind::Error => return malformed(InternalReason::UnexpectedShape),
            _ => return malformed(InternalReason::UnexpectedShape),
        }
    }
    let result = result.ok_or(ProjectionError::MalformedTree(
        InternalReason::UnexpectedShape,
    ))?;
    Ok(SurfaceProgram {
        type_declarations,
        definitions,
        result,
        span: node_span(source, node, tokens)?,
    })
}

fn project_type_declaration(
    source: &SourceFile,
    node: &ConcreteNode,
    tokens: &[Token],
) -> Result<SurfaceTypeDeclaration, ProjectionError> {
    require_kind(node, NodeKind::TypeDeclaration)?;
    let name_token = direct_tokens(node, tokens)
        .find(|token| matches!(token.kind, TokenKind::UpperIdentifier(_)))
        .ok_or(ProjectionError::MalformedTree(
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
    Ok(SurfaceTypeDeclaration {
        name: SurfaceName {
            text: name.clone(),
            span: name_token.span,
        },
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
            let equations = child_nodes(node)
                .filter(|child| child.kind == NodeKind::Equation)
                .map(|equation| {
                    let name =
                        project_binder(only_child_of_kind(equation, NodeKind::Binder)?, tokens)?
                            .name;
                    let patterns = child_nodes(equation)
                        .filter(|child| child.kind == NodeKind::Pattern)
                        .map(|pattern| project_pattern(source, pattern, tokens))
                        .collect::<Result<Vec<_>, _>>()?;
                    let body = project_expression(source, expression_child(equation)?, tokens)?;
                    Ok(SurfaceEquation {
                        name,
                        patterns,
                        body,
                        span: node_span(source, equation, tokens)?,
                    })
                })
                .collect::<Result<Vec<_>, ProjectionError>>()?;
            SurfaceDefinitionKind::Equational(EquationalGlobal {
                interface: SurfaceExternalInterface {
                    name: interface_name,
                    annotation: interface_type,
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
            let body = project_block(source, only_child_of_kind(node, NodeKind::Block)?, tokens)?;
            SurfaceDefinitionKind::InlineOperational(InlineOperationalGlobal {
                header: SurfaceInlineOperationalHeader {
                    name,
                    parameters,
                    result_type,
                    span: node_span(source, header, tokens)?,
                },
                body,
            })
        }
        _ => return malformed(InternalReason::UnexpectedShape),
    };
    Ok(SurfaceDefinition {
        kind,
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
                NodeKind::PrimaryExpression => {
                    if let Some(group) =
                        optional_child_of_kind(node, NodeKind::ParenthesizedExpression)?
                    {
                        schedule_group(source, group, tokens, &mut tasks, &mut projected)?;
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
                                SurfaceBinding {
                                    pattern: binding.pattern,
                                    annotation: binding.annotation,
                                    initializer,
                                    span: binding.span,
                                },
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
    Binding(PendingBinding),
    Recursive(PendingRecursiveGroup),
}

impl PendingLocalDeclaration {
    fn initializer_count(&self) -> usize {
        match self {
            Self::Binding(_) => 1,
            Self::Recursive(group) => group.members.len(),
        }
    }
}

struct PendingBinding {
    pattern: SurfacePattern,
    annotation: Option<SurfaceType>,
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
            declarations.push(PendingLocalDeclaration::Binding(PendingBinding {
                pattern,
                annotation,
                span: node_span(source, child, tokens)?,
            }));
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
        TokenKind::Identifier(text) => SurfaceExprKind::Name(SurfaceName {
            text: text.clone(),
            span: token.span,
        }),
        TokenKind::UpperIdentifier(text) => SurfaceExprKind::Name(SurfaceName {
            text: text.clone(),
            span: token.span,
        }),
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
        let name_token = direct_tokens(constructor, tokens)
            .find(|token| matches!(token.kind, TokenKind::UpperIdentifier(_)))
            .ok_or(ProjectionError::MalformedTree(
                InternalReason::UnexpectedShape,
            ))?;
        let TokenKind::UpperIdentifier(name) = &name_token.kind else {
            return malformed(InternalReason::UnexpectedShape);
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
        SurfacePatternKind::Constructor {
            name: SurfaceName {
                text: name.clone(),
                span: name_token.span,
            },
            payload,
        }
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
                require_kind(node, NodeKind::Type)?;
                let atomic = only_child_of_kind(node, NodeKind::AtomicType)?;
                if let Some(codomain) = optional_child_of_kind(node, NodeKind::Type)? {
                    tasks.push(TypeTask::FinishFunction(node_span(source, node, tokens)?));
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
                    projected.push(project_atomic_primitive(node, tokens)?);
                }
            }
            TypeTask::FinishFunction(span) => {
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
        }
    }
    if projected.len() != 1 {
        return malformed(InternalReason::UnexpectedShape);
    }
    projected.pop().ok_or(ProjectionError::MalformedTree(
        InternalReason::UnexpectedShape,
    ))
}

enum TypeTask<'a> {
    VisitType(&'a ConcreteNode),
    VisitAtomic(&'a ConcreteNode),
    FinishFunction(Span),
    FinishTuple { count: usize, span: Span },
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
        TokenKind::UpperIdentifier(ref text) => SurfaceTypeKind::Named(SurfaceName {
            text: text.clone(),
            span: token.span,
        }),
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

#[cfg(test)]
mod tests {
    use crate::{
        lexer::lex,
        parser::{ResourceFailure, STRUCTURAL_DEPTH_LIMIT, parse},
        source::SourceFile,
    };

    use super::*;

    fn parsed(text: &str) -> (SourceFile, ConcreteTree) {
        let source = SourceFile::new("shape.ash", text).expect("the shape fixture should fit");
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
            project(&source, &tree),
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
            project(&source, &tree),
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
            project(&source, &tree),
            Err(ProjectionError::MalformedTree(
                InternalReason::DuplicateToken
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
            project(&source, &tree),
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
                    project_program(
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
