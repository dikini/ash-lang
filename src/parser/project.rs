//! Projection from recovery-free concrete syntax to spanned surface syntax.

#[path = "foreign_project.rs"]
mod foreign;

use crate::{
    lexer::{Token, TokenKind},
    source::{ByteRange, SourceFile, Span},
    surface::{
        ApplicationExpr, BinaryExpr, EquationalGlobal, FunctionExpr, FunctionType,
        InlineOperationalGlobal, SurfaceBinder, SurfaceBinding, SurfaceBlock,
        SurfaceConstructorDeclaration, SurfaceDeclarationIndex, SurfaceDefinition,
        SurfaceDefinitionKind, SurfaceDeterminationSide, SurfaceEffectDeclaration,
        SurfaceEffectInstance, SurfaceEffectOperation, SurfaceEffectRow, SurfaceEquation,
        SurfaceExpr, SurfaceExprKind, SurfaceExpressionCapture, SurfaceExternalInterface,
        SurfaceHandleExpr, SurfaceHandlerClause, SurfaceIdentifierCapture, SurfaceImplementation,
        SurfaceImport, SurfaceImportItem, SurfaceImportSelection, SurfaceInlineOperationalHeader,
        SurfaceInterfaceDeclaration, SurfaceInterfaceDetermination, SurfaceInterfaceMethod,
        SurfaceKind, SurfaceKindKind, SurfaceLocalDeclaration, SurfaceMatchArm, SurfaceMatchExpr,
        SurfaceModule, SurfaceModulePath, SurfaceName, SurfaceNominalDeclarationKind,
        SurfacePattern, SurfacePatternKind, SurfacePerformExpr, SurfaceQualifiedName,
        SurfaceRecursiveGroup, SurfaceRecursiveMember, SurfaceReference, SurfaceRequirement,
        SurfaceSyntaxCapture, SurfaceSyntaxCaptureKind, SurfaceSyntaxCategory,
        SurfaceSyntaxDeclaration, SurfaceSyntaxImplementation, SurfaceSyntaxMatcherPart,
        SurfaceType, SurfaceTypeDeclaration, SurfaceTypeKind, SurfaceTypeParameter,
        SurfaceTypeVisibility, SurfaceTypedPattern,
    },
};

use super::{
    ConcreteElement, ConcreteNode, ConcreteTree, InternalReason, NodeKind, ParserCheckpoint,
    ResourceFailure, cst,
};

// The parser and projector share token indices. Structured output attaches
// original names and fragments to those indices without changing lexer tokens.
struct ProjectionTokens<'a> {
    tokens: &'a [Token],
    originals: Option<&'a std::collections::HashMap<usize, crate::syntax::MacroOutputNode>>,
    occurrence: Option<Span>,
    construction: Option<(Span, usize)>,
    construction_extents: bool,
    admission_identifiers: Option<&'a std::collections::HashSet<usize>>,
    frame: Option<&'a std::sync::Arc<crate::syntax::ExpansionFrame>>,
    name_frame: Option<&'a std::sync::Arc<crate::syntax::ExpansionFrame>>,
    preserve_name_diagnostic: bool,
}

impl<'a> ProjectionTokens<'a> {
    fn source(tokens: &'a [Token]) -> Self {
        Self {
            tokens,
            originals: None,
            occurrence: None,
            construction: None,
            construction_extents: false,
            admission_identifiers: None,
            frame: None,
            name_frame: None,
            preserve_name_diagnostic: false,
        }
    }

    fn for_construction(&self) -> Self {
        Self {
            tokens: self.tokens,
            originals: self.originals,
            occurrence: self.occurrence,
            construction: self.construction,
            construction_extents: true,
            admission_identifiers: self.admission_identifiers,
            frame: self.frame,
            name_frame: self.name_frame,
            preserve_name_diagnostic: self.preserve_name_diagnostic,
        }
    }

    fn for_node_construction(&self, node: &ConcreteNode) -> Self {
        let mut construction = self.for_construction();
        if construction.construction.is_some() {
            let mut pending = node.children.iter().collect::<Vec<_>>();
            while let Some(element) = pending.pop() {
                match element {
                    ConcreteElement::Node(child) => pending.extend(&child.children),
                    ConcreteElement::Token(index)
                        if self
                            .projection_token(*index)
                            .and_then(|token| self.original_span(token))
                            .is_none() =>
                    {
                        construction.construction = None;
                        break;
                    }
                    _ => {}
                }
            }
        }
        construction
    }

    fn original_span(&self, token: ProjectionToken<'_>) -> Option<Span> {
        use crate::syntax::MacroOutputNode;
        let (bound, introduction) = self.construction?;
        let origin = match token.original? {
            MacroOutputNode::Identifier(name, origin) if name.introduction == introduction => {
                origin
            }
            MacroOutputNode::Token(_, _, origin) | MacroOutputNode::Group(_, _, origin) => origin,
            MacroOutputNode::Identifier(_, _)
            | MacroOutputNode::Expression(_, _)
            | MacroOutputNode::ForwardedExpression(_, _)
            | MacroOutputNode::Splice(_) => return None,
        };
        let crate::syntax::MacroOrigin::Source(span) = origin else {
            return None;
        };
        (bound.cover(*span) == Some(bound)).then_some(*span)
    }
}

impl std::ops::Deref for ProjectionTokens<'_> {
    type Target = [Token];

    fn deref(&self) -> &Self::Target {
        self.tokens
    }
}

#[derive(Clone, Copy)]
struct ProjectionToken<'a> {
    token: &'a Token,
    // Generated tokens retain their grammar coordinates in `token`.
    span: Span,
    original: Option<&'a crate::syntax::MacroOutputNode>,
    admission_identifier: bool,
    name_frame: Option<&'a std::sync::Arc<crate::syntax::ExpansionFrame>>,
    preserve_name_diagnostic: bool,
}

impl ProjectionToken<'_> {
    fn is_upper_identifier(&self) -> bool {
        self.admission_identifier || matches!(self.kind, TokenKind::UpperIdentifier(_))
    }
}

impl std::ops::Deref for ProjectionToken<'_> {
    type Target = Token;

    fn deref(&self) -> &Self::Target {
        self.token
    }
}

trait ProjectionTokenSource {
    fn projection_token(&self, index: usize) -> Option<ProjectionToken<'_>>;
}

impl ProjectionTokenSource for [Token] {
    fn projection_token(&self, index: usize) -> Option<ProjectionToken<'_>> {
        self.get(index).map(|token| ProjectionToken {
            token,
            span: token.span,
            original: None,
            admission_identifier: false,
            name_frame: None,
            preserve_name_diagnostic: false,
        })
    }
}

impl ProjectionTokenSource for ProjectionTokens<'_> {
    fn projection_token(&self, index: usize) -> Option<ProjectionToken<'_>> {
        self.tokens.get(index).map(|token| ProjectionToken {
            token,
            span: self.occurrence.unwrap_or(token.span),
            original: self.originals.and_then(|originals| originals.get(&index)),
            admission_identifier: self
                .admission_identifiers
                .is_some_and(|indices| indices.contains(&index)),
            name_frame: self.name_frame,
            preserve_name_diagnostic: self.preserve_name_diagnostic,
        })
    }
}

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
/// This context-free API also checks expression template syntax using capture
/// placeholders, without imported syntax matchers. Declaration headers and
/// bodies are retained without declaration-template admission. The module
/// driver checks expression templates with the selected matchers before
/// resolving their bodies.
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
    let module = project_module_retaining_templates(source, tree)?;
    let contexts = crate::syntax::SyntaxContexts::new(&[], &[], &[]);
    for declaration in &module.syntax_declarations {
        if declaration.category == SurfaceSyntaxCategory::Declaration {
            continue;
        }
        crate::syntax::validate_template_syntax(declaration, source, &contexts).map_err(
            |failure| match failure {
                super::MacroParseFailure::Syntax {
                    resource: Some(failure),
                    ..
                } => ProjectionError::ResourceLimit(failure),
                super::MacroParseFailure::Syntax { .. } => ProjectionError::RecoveryNodesPresent,
                super::MacroParseFailure::Invalid => {
                    ProjectionError::MalformedTree(InternalReason::UnexpectedShape)
                }
            },
        )?;
    }
    Ok(module)
}

pub(crate) fn project_module_retaining_templates(
    source: &SourceFile,
    tree: &ConcreteTree,
) -> Result<SurfaceModule, ProjectionError> {
    let (root, tokens) = validated_root(source, tree)?;
    project_surface_module(source, root, &ProjectionTokens::source(tokens))
}

/// Projects the retained fixed header while the module body is still unparsed.
pub(crate) fn project_module_header(
    source: &SourceFile,
    checkpoint: &ParserCheckpoint,
) -> Result<Vec<SurfaceImport>, ProjectionError> {
    if let Some(failure) = checkpoint.resource_failure {
        return Err(ProjectionError::ResourceLimit(failure));
    }
    validate_tokens(source, &checkpoint.tokens)?;
    let consumed =
        checkpoint
            .tokens
            .get(..checkpoint.position)
            .ok_or(ProjectionError::MalformedTree(
                InternalReason::TokenOutOfRange,
            ))?;
    let header_end = consumed.last().map_or(0, |token| token.span.range().end());
    if !checkpoint.diagnostics.is_empty()
        || checkpoint
            .lexical_diagnostics
            .iter()
            .any(|diagnostic| diagnostic.primary.span().range().start() < header_end)
    {
        return Err(ProjectionError::RecoveryNodesPresent);
    }
    let root = cst::build_header(consumed.len(), &checkpoint.events)
        .map_err(ProjectionError::MalformedTree)?;
    if has_recovery(&root) {
        return Err(ProjectionError::RecoveryNodesPresent);
    }
    require_kind(&root, NodeKind::Module)?;
    let mut shape = ShapeCursor::new(&root, &checkpoint.tokens);
    let mut imports = Vec::new();
    let projection_tokens = ProjectionTokens::source(&checkpoint.tokens);
    while let Some(node) = shape.peek_node() {
        validate_node_shape(node, &checkpoint.tokens)?;
        imports.push(project_import(source, node, &projection_tokens)?);
        shape.node(NodeKind::ImportDeclaration)?;
        shape.token(&TokenKind::LineEnd)?;
    }
    shape.finish()?;
    Ok(imports)
}

pub(crate) fn module_span_from_checkpoint(
    source: &SourceFile,
    checkpoint: &ParserCheckpoint,
) -> Result<Span, ProjectionError> {
    validate_tokens(source, &checkpoint.tokens)?;
    let first = checkpoint
        .tokens
        .first()
        .ok_or(ProjectionError::MalformedTree(InternalReason::InvalidSpan))?;
    let last = checkpoint
        .tokens
        .last()
        .ok_or(ProjectionError::MalformedTree(InternalReason::InvalidSpan))?;
    join_spans(source, first.span, last.span)
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

pub(crate) fn structural_weight(node: &ConcreteNode) -> usize {
    match node.kind {
        NodeKind::Block
        | NodeKind::RegionExpression
        | NodeKind::RegionSelectionExpression
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
    validate_node_shape_with_admission(node, tokens, None)
}

fn validate_node_shape_with_admission(
    node: &ConcreteNode,
    tokens: &[Token],
    admission: Option<&std::collections::HashSet<usize>>,
) -> Result<(), ProjectionError> {
    let mut pending = vec![node];
    while let Some(node) = pending.pop() {
        validate_shallow_shape(node, tokens, admission)?;
        pending.extend(child_nodes(node));
    }
    Ok(())
}

fn validate_shallow_shape(
    node: &ConcreteNode,
    tokens: &[Token],
    admission: Option<&std::collections::HashSet<usize>>,
) -> Result<(), ProjectionError> {
    let mut shape = ShapeCursor::with_admission(node, tokens, admission);
    match node.kind {
        NodeKind::ForeignLibrary | NodeKind::ForeignMember => {
            return foreign::validate_shape(node, tokens);
        }
        NodeKind::Module => {
            while shape.peek_node_is(NodeKind::ImportDeclaration) {
                shape.node(NodeKind::ImportDeclaration)?;
                shape.token(&TokenKind::LineEnd)?;
            }
            while shape.peek_node_is(NodeKind::ForeignLibrary)
                || shape.peek_node_is(NodeKind::TypeDeclaration)
                || shape.peek_node_is(NodeKind::NewtypeDeclaration)
                || shape.peek_node_is(NodeKind::InterfaceDeclaration)
                || shape.peek_node_is(NodeKind::ResourceDefinition)
                || shape.peek_node_is(NodeKind::EffectDeclaration)
                || shape.peek_node_is(NodeKind::ImplementationDeclaration)
                || shape.peek_node_is(NodeKind::SyntaxDeclaration)
                || shape.peek_node_is(NodeKind::DeclarationSyntaxInvocation)
                || shape.peek_node_is(NodeKind::EquationalGlobal)
                || shape.peek_node_is(NodeKind::InlineOperationalGlobal)
            {
                shape.any_node()?;
                shape.token(&TokenKind::LineEnd)?;
            }
            shape.token(&TokenKind::EndOfFile)?;
        }
        NodeKind::SyntaxDeclaration => {
            shape.token(&TokenKind::Pub)?;
            shape.token(&TokenKind::SyntaxKeyword)?;
            let declaration = is_declaration_syntax(node, tokens);
            if declaration {
                shape.token_matching(
                    |kind| matches!(kind, TokenKind::Identifier(name) if name == "declaration"),
                )?;
                shape.token(&TokenKind::Colon)?;
                shape.token(&TokenKind::LeftParen)?;
                shape.token_matching(|kind| matches!(kind, TokenKind::Identifier(name) if name.as_bytes().first().is_some_and(u8::is_ascii_lowercase)))?;
                shape.token(&TokenKind::RightParen)?;
            } else {
                shape.token_matching(|kind| matches!(kind, TokenKind::Identifier(_)))?;
            }
            while !shape.peek_token_is(&TokenKind::FatArrow) {
                if shape.peek_node_is(NodeKind::SyntaxCapture) {
                    if !declaration
                        && shape.peek_node().is_some_and(|capture| {
                            direct_tokens(capture, tokens)
                                .any(|token| matches!(token.kind, TokenKind::UpperIdentifier(_)))
                        })
                    {
                        return malformed(InternalReason::UnexpectedShape);
                    }
                    shape.node(NodeKind::SyntaxCapture)?;
                } else {
                    shape.token_matching(|kind| {
                        !matches!(
                            kind,
                            TokenKind::Dollar
                                | TokenKind::LeftParen
                                | TokenKind::RightParen
                                | TokenKind::LeftBrace
                                | TokenKind::RightBrace
                                | TokenKind::LineEnd
                                | TokenKind::EndOfFile
                                | TokenKind::FatArrow
                        )
                    })?;
                }
            }
            shape.token(&TokenKind::FatArrow)?;
            if shape.peek_token_is(&TokenKind::Using) {
                shape.token(&TokenKind::Using)?;
                shape.token_matching(|kind| matches!(kind, TokenKind::Identifier(_)))?;
            } else {
                shape.node(NodeKind::TemplateBody)?;
            }
        }
        NodeKind::TemplateBody => {
            let mut closing = Vec::new();
            for element in &node.children {
                let ConcreteElement::Token(index) = element else {
                    return malformed(InternalReason::UnexpectedShape);
                };
                let kind = &tokens
                    .get(*index)
                    .ok_or(ProjectionError::MalformedTree(
                        InternalReason::TokenOutOfRange,
                    ))?
                    .kind;
                match kind {
                    TokenKind::LeftBrace => closing.push(TokenKind::RightBrace),
                    TokenKind::LeftParen => closing.push(TokenKind::RightParen),
                    TokenKind::RightBrace | TokenKind::RightParen => {
                        if closing.pop().as_ref() != Some(kind) {
                            return malformed(InternalReason::UnexpectedShape);
                        }
                    }
                    TokenKind::EndOfFile => return malformed(InternalReason::UnexpectedShape),
                    _ => {}
                }
                if closing.is_empty()
                    && index
                        != match node.children.last() {
                            Some(ConcreteElement::Token(last)) => last,
                            _ => return malformed(InternalReason::UnexpectedShape),
                        }
                {
                    return malformed(InternalReason::UnexpectedShape);
                }
            }
            if !closing.is_empty()
                || !matches!(node.children.first(), Some(ConcreteElement::Token(index)) if tokens.get(*index).is_some_and(|token| token.kind == TokenKind::LeftBrace))
            {
                return malformed(InternalReason::UnexpectedShape);
            }
            return Ok(());
        }
        NodeKind::SyntaxCapture => {
            shape.token(&TokenKind::Dollar)?;
            shape.token_matching(|kind| {
                matches!(
                    kind,
                    TokenKind::Identifier(_) | TokenKind::UpperIdentifier(_)
                )
            })?;
            shape.token(&TokenKind::Colon)?;
            shape.token_matching(
                |kind| matches!(kind, TokenKind::Identifier(name) if name == "expr" || name == "ident"),
            )?;
        }
        NodeKind::SyntaxInvocation | NodeKind::DeclarationSyntaxInvocation => {
            shape.token_matching(|kind| matches!(kind, TokenKind::Identifier(_)))?;
            while shape.position < shape.children.len() {
                if shape.peek_node_is(NodeKind::SyntaxArgument) {
                    shape.node(NodeKind::SyntaxArgument)?;
                } else {
                    shape.token_matching(|kind| {
                        !matches!(kind, TokenKind::EndOfFile | TokenKind::LineEnd)
                    })?;
                }
            }
        }
        NodeKind::SyntaxArgument => {
            if shape.peek_node().is_some() {
                shape.expression()?;
            } else {
                shape.token_matching(|kind| {
                    matches!(
                        kind,
                        TokenKind::Identifier(_) | TokenKind::UpperIdentifier(_)
                    )
                })?;
            }
        }
        NodeKind::ImportDeclaration => {
            let public = shape.peek_token_is(&TokenKind::Pub);
            if public {
                shape.token(&TokenKind::Pub)?;
                if child_nodes(node)
                    .filter(|child| child.kind == NodeKind::ImportItem)
                    .any(|item| is_syntax_import_item(item, tokens))
                {
                    return malformed(InternalReason::UnexpectedShape);
                }
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
            if is_builtin_syntax_path(node, tokens) {
                shape.token(&TokenKind::At)?;
                shape.token_matching(
                    |kind| matches!(kind, TokenKind::Identifier(name) if name == "builtin"),
                )?;
                shape.token(&TokenKind::Dot)?;
                shape.token_matching(
                    |kind| matches!(kind, TokenKind::Identifier(name) if name == "compiler"),
                )?;
                shape.token(&TokenKind::Dot)?;
                shape.token(&TokenKind::SyntaxKeyword)?;
                return shape.finish();
            }
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
            if is_syntax_import_item(node, tokens) {
                shape.token(&TokenKind::SyntaxKeyword)?;
                shape.token_matching(|kind| matches!(kind, TokenKind::Identifier(name) if name.as_bytes().first().is_some_and(u8::is_ascii_lowercase)))?;
                if shape.peek_token_is(&TokenKind::As) {
                    shape.token(&TokenKind::As)?;
                    shape.token_matching(|kind| matches!(kind, TokenKind::Identifier(name) if name.as_bytes().first().is_some_and(u8::is_ascii_lowercase)))?;
                }
            } else if shape.peek_token_is(&TokenKind::Impl) {
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
                    admission,
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
            if shape.peek_token_is(&TokenKind::Using) {
                shape.token(&TokenKind::Using)?;
                shape.node(NodeKind::PrimaryExpression)?;
            }
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
                if index == 6 && shape.peek_node_is(NodeKind::ResourceFamily) {
                    shape.node(NodeKind::ResourceFamily)?;
                    shape.token(&TokenKind::LineEnd)?;
                }
                shape.node(NodeKind::ResourceField)?;
                if index < 8 || shape.peek_token_is(&TokenKind::LineEnd) {
                    shape.token(&TokenKind::LineEnd)?;
                }
            }
            shape.token(&TokenKind::RightBrace)?;
        }
        NodeKind::ResourceFamily => {
            shape.token_matching(
                |kind| matches!(kind, TokenKind::Identifier(word) if word == "family"),
            )?;
            shape.node(NodeKind::TypeParameters)?;
            shape.node(NodeKind::WhereClause)?;
            shape.token(&TokenKind::LeftBrace)?;
            shape.token(&TokenKind::LineEnd)?;
            for (index, role) in ["provider", "effect", "interpret", "handlers"]
                .into_iter()
                .enumerate()
            {
                let field = shape.peek_node().ok_or(ProjectionError::MalformedTree(
                    InternalReason::UnexpectedShape,
                ))?;
                let matches_role =
                    direct_tokens(field, tokens)
                        .next()
                        .is_some_and(|token| match &token.kind {
                            TokenKind::Effect => role == "effect",
                            TokenKind::Identifier(word) => role != "effect" && word == role,
                            _ => false,
                        });
                if !matches_role {
                    return malformed(InternalReason::UnexpectedShape);
                }
                shape.node(NodeKind::ResourceField)?;
                if index < 3 || shape.peek_token_is(&TokenKind::LineEnd) {
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
                    shape.node(NodeKind::HandlerClause)?;
                    while shape.peek_token_is(&TokenKind::LineEnd) {
                        shape.token(&TokenKind::LineEnd)?;
                        if !shape.peek_node_is(NodeKind::HandlerClause) {
                            break;
                        }
                        shape.node(NodeKind::HandlerClause)?;
                    }
                    shape.token(&TokenKind::RightBrace)?;
                }
                _ => return malformed(InternalReason::UnexpectedShape),
            }
        }

        NodeKind::ProviderResourceExpression => {
            shape.token(&TokenKind::Resource)?;
            let instance = only_child_of_kind(node, NodeKind::EffectInstance)?;
            if !direct_tokens(instance, tokens).any(|token| token.kind == TokenKind::Less) {
                return malformed(InternalReason::UnexpectedShape);
            }
            shape.node(NodeKind::EffectInstance)?;
            shape.node(NodeKind::Binder)?;
            shape.token(&TokenKind::Equal)?;
            shape.node(NodeKind::PrimaryExpression)?;
            shape.node(NodeKind::Block)?;
        }
        NodeKind::RegionExpression => {
            shape.token(&TokenKind::Region)?;
            shape.token(&TokenKind::Less)?;
            shape.token_matching(|kind| matches!(kind, TokenKind::UpperIdentifier(_)))?;
            shape.token(&TokenKind::Greater)?;
            shape.node(NodeKind::Binder)?;
            if shape.peek_token_is(&TokenKind::Equal) {
                shape.token(&TokenKind::Equal)?;
                shape.node(NodeKind::PrimaryExpression)?;
            }
            shape.node(NodeKind::Block)?;
        }
        NodeKind::RegionSelectionExpression => {
            shape.token(&TokenKind::Using)?;
            shape.node(NodeKind::PrimaryExpression)?;
            shape.node(NodeKind::Block)?;
        }
        NodeKind::ResourceExpression => {
            shape.token(&TokenKind::Resource)?;
            shape.token_matching(
                |kind| matches!(kind, TokenKind::Identifier(name) if name == "cell"),
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
            if shape.peek_token_is(&TokenKind::Dollar) {
                shape.token(&TokenKind::Dollar)?;
                shape.token_matching(|kind| matches!(kind, TokenKind::Identifier(_)))?;
            } else if shape.peek_node_is(NodeKind::ParenthesizedExpression) {
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
                            | TokenKind::StringLiteral(_)
                            | TokenKind::Discard
                            | TokenKind::Retain
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
            if shape.peek_token_is(&TokenKind::Dollar) {
                shape.token(&TokenKind::Dollar)?;
                shape.token_matching(|kind| matches!(kind, TokenKind::Identifier(_)))?;
            } else if shape.peek_token_is(&TokenKind::LeftParen) {
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
            if shape.peek_token_is(&TokenKind::Dollar) {
                shape.token(&TokenKind::Dollar)?;
            }
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
                                | TokenKind::BytesType
                                | TokenKind::StringType
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
    admission: Option<&std::collections::HashSet<usize>>,
) -> Result<(), ProjectionError> {
    require_kind(node, NodeKind::QualifiedName)?;
    let mut shape = ShapeCursor::with_admission(node, tokens, admission);
    shape.token_matching(|kind| matches!(kind, TokenKind::UpperIdentifier(_)))?;
    shape.token(&TokenKind::Dot)?;
    shape.token_matching(|kind| matches!(kind, TokenKind::UpperIdentifier(_)))?;
    shape.finish()
}

struct ShapeCursor<'a> {
    children: &'a [ConcreteElement],
    tokens: &'a [Token],
    position: usize,
    admission: Option<&'a std::collections::HashSet<usize>>,
}

impl<'a> ShapeCursor<'a> {
    fn new(node: &'a ConcreteNode, tokens: &'a [Token]) -> Self {
        Self::with_admission(node, tokens, None)
    }

    fn with_admission(
        node: &'a ConcreteNode,
        tokens: &'a [Token],
        admission: Option<&'a std::collections::HashSet<usize>>,
    ) -> Self {
        Self {
            children: &node.children,
            tokens,
            position: 0,
            admission,
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
        predicate: impl Fn(&TokenKind) -> bool,
    ) -> Result<(), ProjectionError> {
        let matches = match self.children.get(self.position) {
            Some(ConcreteElement::Token(index)) => self.tokens.get(*index).is_some_and(|token| {
                predicate(&token.kind)
                    || self
                        .admission
                        .is_some_and(|indices| indices.contains(index))
                        && match &token.kind {
                            TokenKind::Identifier(name) => {
                                predicate(&TokenKind::UpperIdentifier(name.clone()))
                            }
                            TokenKind::UpperIdentifier(name) => {
                                predicate(&TokenKind::Identifier(name.clone()))
                            }
                            _ => false,
                        }
            }),
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
    tokens: &ProjectionTokens<'_>,
) -> Result<SurfaceModule, ProjectionError> {
    require_kind(node, NodeKind::Module)?;
    let mut imports = Vec::new();
    let mut syntax_declarations = Vec::new();
    let mut foreign_libraries = Vec::new();
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
            NodeKind::SyntaxDeclaration => {
                let declaration = is_declaration_syntax(child, tokens);
                let name = direct_tokens(child, tokens)
                    .nth(if declaration { 5 } else { 2 })
                    .ok_or(ProjectionError::MalformedTree(
                        InternalReason::UnexpectedShape,
                    ))?;
                let mut matcher = Vec::new();
                let mut prefix = 0;
                for element in &child.children {
                    match element {
                        ConcreteElement::Token(index) => {
                            let token = tokens.get(*index).ok_or(
                                ProjectionError::MalformedTree(InternalReason::TokenOutOfRange),
                            )?;
                            if prefix < if declaration { 7 } else { 3 } {
                                prefix += 1;
                            } else if token.kind == TokenKind::FatArrow {
                                break;
                            } else {
                                let range = token.span.range();
                                let spelling = source
                                    .text()
                                    .get(range.start() as usize..range.end() as usize)
                                    .ok_or(ProjectionError::MalformedTree(
                                        InternalReason::InvalidSpan,
                                    ))?;
                                matcher.push(SurfaceSyntaxMatcherPart::Literal {
                                    kind: token.kind.clone(),
                                    spelling: spelling.to_owned(),
                                });
                            }
                        }
                        ConcreteElement::Node(capture)
                            if capture.kind == NodeKind::SyntaxCapture =>
                        {
                            let names = direct_tokens(capture, tokens)
                                .filter(|token| {
                                    matches!(
                                        token.kind,
                                        TokenKind::Identifier(_) | TokenKind::UpperIdentifier(_)
                                    )
                                })
                                .collect::<Vec<_>>();
                            if names.len() != 2 {
                                return malformed(InternalReason::UnexpectedShape);
                            }
                            let kind = match &names[1].kind {
                                TokenKind::Identifier(kind) if kind == "expr" => {
                                    SurfaceSyntaxCaptureKind::Expression
                                }
                                TokenKind::Identifier(kind) if kind == "ident" => {
                                    SurfaceSyntaxCaptureKind::Identifier
                                }
                                _ => return malformed(InternalReason::UnexpectedShape),
                            };
                            matcher.push(SurfaceSyntaxMatcherPart::Capture {
                                name: surface_name(names[0])?,
                                kind,
                            });
                        }
                        _ => return malformed(InternalReason::UnexpectedShape),
                    }
                }
                let (implementation, template_contents) = if let Some(block) =
                    child_nodes(child).find(|node| node.kind == NodeKind::TemplateBody)
                {
                    let mut contents =
                        capture_contents(source, block, tokens, &Default::default())?;
                    if declaration {
                        contents = match contents.pop() {
                            Some(crate::syntax::MacroOutputNode::Group(
                                crate::syntax::MacroDelimiter::Braces,
                                mut children,
                                _,
                            )) if contents.is_empty() => {
                                if matches!(
                                    children.first(),
                                    Some(crate::syntax::MacroOutputNode::Token(
                                        TokenKind::LineEnd,
                                        _,
                                        _
                                    ))
                                ) {
                                    children.remove(0);
                                }
                                children
                            }
                            _ => return malformed(InternalReason::UnexpectedShape),
                        };
                    }
                    (SurfaceSyntaxImplementation::Template, Some(contents.into()))
                } else {
                    let mut after_arrow = direct_tokens(child, tokens)
                        .skip_while(|token| token.kind != TokenKind::FatArrow)
                        .skip(1);
                    if after_arrow.next().map(|token| &token.token.kind) != Some(&TokenKind::Using)
                    {
                        return malformed(InternalReason::UnexpectedShape);
                    }
                    let transformer = after_arrow.next().ok_or(ProjectionError::MalformedTree(
                        InternalReason::UnexpectedShape,
                    ))?;
                    if after_arrow.next().is_some() {
                        return malformed(InternalReason::UnexpectedShape);
                    }
                    (
                        SurfaceSyntaxImplementation::Transformer(surface_name(transformer)?),
                        None,
                    )
                };
                syntax_declarations.push(SurfaceSyntaxDeclaration {
                    category: if declaration {
                        SurfaceSyntaxCategory::Declaration
                    } else {
                        SurfaceSyntaxCategory::Expression
                    },
                    name: surface_name(name)?,
                    matcher,
                    implementation,
                    template_contents,
                    span: node_span(source, child, tokens)?,
                });
            }
            NodeKind::ForeignLibrary => {
                declaration_order.push(SurfaceDeclarationIndex::ForeignLibrary(
                    foreign_libraries.len(),
                ));
                foreign_libraries.push(foreign::library(source, child, tokens)?);
            }
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
        syntax_declarations,
        foreign_libraries,
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
    tokens: &ProjectionTokens<'_>,
) -> Result<SurfaceEffectDeclaration, ProjectionError> {
    require_kind(node, NodeKind::EffectDeclaration)?;
    let public = direct_tokens(node, tokens).any(|token| token.kind == TokenKind::Pub);
    let name = direct_tokens(node, tokens)
        .find(ProjectionToken::is_upper_identifier)
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
    tokens: &ProjectionTokens<'_>,
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
    tokens: &ProjectionTokens<'_>,
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
    tokens: &ProjectionTokens<'_>,
) -> Result<SurfaceInterfaceDeclaration, ProjectionError> {
    require_kind(node, NodeKind::InterfaceDeclaration)?;
    let public = direct_tokens(node, tokens).any(|token| token.kind == TokenKind::Pub);
    let mut names = direct_tokens(node, tokens).filter(ProjectionToken::is_upper_identifier);
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
    tokens: &ProjectionTokens<'_>,
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
    tokens: &[ProjectionToken<'_>],
) -> Result<SurfaceDeterminationSide, ProjectionError> {
    let first = tokens.first().ok_or(ProjectionError::MalformedTree(
        InternalReason::UnexpectedShape,
    ))?;
    let last = tokens.last().ok_or(ProjectionError::MalformedTree(
        InternalReason::UnexpectedShape,
    ))?;
    let parameters = tokens
        .iter()
        .filter(|token| token.is_upper_identifier())
        .map(|token| surface_name(*token))
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
    tokens: &ProjectionTokens<'_>,
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
    tokens: &ProjectionTokens<'_>,
) -> Result<SurfaceImport, ProjectionError> {
    require_kind(node, NodeKind::ImportDeclaration)?;
    let path_node = only_child_of_kind(node, NodeKind::ModulePath)?;
    let mut path_names = direct_tokens(path_node, tokens)
        .filter_map(|token| {
            let text = match &token.kind {
                TokenKind::Identifier(text) => text.clone(),
                TokenKind::SyntaxKeyword => "syntax".to_owned(),
                _ => return None,
            };
            Some(SurfaceName {
                text,
                span: token.span,
                introduction: 0,
                introduced_at: None,
                written: true,
                diagnostic: None,
            })
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
            .find(ProjectionToken::is_upper_identifier)
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
    tokens: &ProjectionTokens<'_>,
) -> Result<SurfaceImportItem, ProjectionError> {
    require_kind(node, NodeKind::ImportItem)?;
    if direct_tokens(node, tokens).any(|token| token.kind == TokenKind::Impl) {
        let interface = direct_tokens(node, tokens)
            .find(ProjectionToken::is_upper_identifier)
            .ok_or(ProjectionError::MalformedTree(
                InternalReason::UnexpectedShape,
            ))?;
        return Ok(SurfaceImportItem::Implementation {
            interface: surface_name(interface)?,
            span: node_span(source, node, tokens)?,
        });
    }
    let syntax = is_syntax_import_item(node, tokens);
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
    let span = node_span(source, node, tokens)?;
    Ok(if syntax {
        SurfaceImportItem::Syntax { name, alias, span }
    } else {
        SurfaceImportItem::Name { name, alias, span }
    })
}

fn is_syntax_import_item<T: ProjectionTokenSource + ?Sized>(
    node: &ConcreteNode,
    tokens: &T,
) -> bool {
    matches!(
        direct_tokens(node, tokens)
            .next()
            .map(|token| &token.token.kind),
        Some(TokenKind::SyntaxKeyword)
    )
}

fn is_declaration_syntax<T: ProjectionTokenSource + ?Sized>(
    node: &ConcreteNode,
    tokens: &T,
) -> bool {
    let mut direct = direct_tokens(node, tokens).skip(2);
    matches!(direct.next().map(|token| &token.token.kind), Some(TokenKind::Identifier(name)) if name == "declaration")
        && matches!(
            direct.next().map(|token| &token.token.kind),
            Some(TokenKind::Colon)
        )
        && matches!(
            direct.next().map(|token| &token.token.kind),
            Some(TokenKind::LeftParen)
        )
}

fn is_builtin_syntax_path<T: ProjectionTokenSource + ?Sized>(
    node: &ConcreteNode,
    tokens: &T,
) -> bool {
    let mut direct = direct_tokens(node, tokens);
    matches!(
        direct.next().map(|token| &token.token.kind),
        Some(TokenKind::At)
    ) && matches!(direct.next().map(|token| &token.token.kind), Some(TokenKind::Identifier(name)) if name == "builtin")
        && matches!(
            direct.next().map(|token| &token.token.kind),
            Some(TokenKind::Dot)
        )
        && matches!(direct.next().map(|token| &token.token.kind), Some(TokenKind::Identifier(name)) if name == "compiler")
        && matches!(
            direct.next().map(|token| &token.token.kind),
            Some(TokenKind::Dot)
        )
        && matches!(
            direct.next().map(|token| &token.token.kind),
            Some(TokenKind::SyntaxKeyword)
        )
        && direct.next().is_none()
}

fn project_type_declaration(
    source: &SourceFile,
    node: &ConcreteNode,
    tokens: &ProjectionTokens<'_>,
) -> Result<SurfaceTypeDeclaration, ProjectionError> {
    project_nominal_declaration(source, node, tokens, SurfaceNominalDeclarationKind::Data)
}

fn project_newtype_declaration(
    source: &SourceFile,
    node: &ConcreteNode,
    tokens: &ProjectionTokens<'_>,
) -> Result<SurfaceTypeDeclaration, ProjectionError> {
    project_nominal_declaration(source, node, tokens, SurfaceNominalDeclarationKind::Newtype)
}

fn project_nominal_declaration(
    source: &SourceFile,
    node: &ConcreteNode,
    tokens: &ProjectionTokens<'_>,
    declaration_kind: SurfaceNominalDeclarationKind,
) -> Result<SurfaceTypeDeclaration, ProjectionError> {
    let construction_tokens = tokens.for_node_construction(node);
    let tokens = &construction_tokens;
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
    let mut names = direct_tokens(node, tokens).filter(ProjectionToken::is_upper_identifier);
    let name_token = names.next().ok_or(ProjectionError::MalformedTree(
        InternalReason::UnexpectedShape,
    ))?;
    if !name_token.is_upper_identifier() {
        return malformed(InternalReason::UnexpectedShape);
    }
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
    let name = surface_name(name_token)?;
    let span = node_span(source, node, tokens)?;
    let generated_parameters = if let Some(invocation) = tokens.occurrence
        && !parameters.is_empty()
    {
        let parameter_node = only_child_of_kind(node, NodeKind::TypeParameters)?;
        let occurrences = child_nodes(parameter_node)
            .filter(|child| child.kind == NodeKind::TypeParameter)
            .zip(&parameters)
            .map(|(node, parameter)| {
                Ok(super::ParsedParameterOccurrence {
                    name: parameter.name.clone(),
                    tokens: descendant_edge_index(node, false)?
                        ..descendant_edge_index(node, true)? + 1,
                })
            })
            .collect::<Result<Vec<_>, ProjectionError>>()?;
        Some(std::sync::Arc::new(super::ParsedParameterOrder {
            invocation,
            occurrence_extent: tokens.construction.is_none(),
            declaration: descendant_edge_index(node, false)?
                ..descendant_edge_index(node, true)? + 1,
            name: name.clone(),
            span,
            parameters: occurrences.into_boxed_slice(),
        }))
    } else {
        None
    };
    Ok(SurfaceTypeDeclaration {
        declaration_kind,
        visibility,
        name,
        parameters,
        constructors,
        span,
        generated_parameters,
    })
}

fn project_constructor_declaration(
    source: &SourceFile,
    node: &ConcreteNode,
    tokens: &ProjectionTokens<'_>,
) -> Result<SurfaceConstructorDeclaration, ProjectionError> {
    require_kind(node, NodeKind::ConstructorDeclaration)?;
    let name_token = direct_tokens(node, tokens)
        .find(ProjectionToken::is_upper_identifier)
        .ok_or(ProjectionError::MalformedTree(
            InternalReason::UnexpectedShape,
        ))?;
    if !name_token.is_upper_identifier() {
        return malformed(InternalReason::UnexpectedShape);
    }
    let fields = child_nodes(node)
        .filter(|child| child.kind == NodeKind::Type)
        .map(|field| project_type(source, field, tokens))
        .collect::<Result<Vec<_>, _>>()?;
    Ok(SurfaceConstructorDeclaration {
        name: surface_name(name_token)?,
        fields,
        span: node_span(source, node, tokens)?,
    })
}

fn project_definition(
    source: &SourceFile,
    node: &ConcreteNode,
    tokens: &ProjectionTokens<'_>,
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
    tokens: &ProjectionTokens<'_>,
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
    tokens: &ProjectionTokens<'_>,
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
    tokens: &ProjectionTokens<'_>,
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
    tokens: &ProjectionTokens<'_>,
) -> Result<SurfaceRequirement, ProjectionError> {
    require_kind(node, NodeKind::InterfaceApplication)?;
    let interface = if let Some(qualified) = optional_child_of_kind(node, NodeKind::QualifiedName)?
    {
        SurfaceReference::Qualified(project_qualified_name(source, qualified, tokens)?)
    } else {
        let name = direct_tokens(node, tokens)
            .find(ProjectionToken::is_upper_identifier)
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
    tokens: &ProjectionTokens<'_>,
) -> Result<SurfaceExpr, ProjectionError> {
    let empty = std::collections::HashMap::new();
    project_expression_with_fragments(source, node, tokens, tokens.originals.unwrap_or(&empty))
}

fn project_syntax_identifier_capture(
    argument: &ConcreteNode,
    tokens: &ProjectionTokens<'_>,
    originals: &std::collections::HashMap<usize, crate::syntax::MacroOutputNode>,
) -> Result<SurfaceIdentifierCapture, ProjectionError> {
    let index = argument
        .children
        .iter()
        .find_map(|child| match child {
            ConcreteElement::Token(index) => Some(*index),
            _ => None,
        })
        .ok_or(ProjectionError::MalformedTree(
            InternalReason::UnexpectedShape,
        ))?;
    match originals.get(&index) {
        Some(crate::syntax::MacroOutputNode::Identifier(name, origin)) => {
            Ok(SurfaceIdentifierCapture {
                name: name.clone(),
                origin: origin.clone(),
            })
        }
        _ => {
            let name = surface_name(only_direct_token(argument, tokens)?)?;
            Ok(SurfaceIdentifierCapture {
                origin: name.span.into(),
                name,
            })
        }
    }
}

fn project_syntax_expression_capture(
    expression: SurfaceExpr,
    contents: Vec<crate::syntax::MacroOutputNode>,
) -> SurfaceExpressionCapture {
    if let [crate::syntax::MacroOutputNode::ForwardedExpression(original, _)] = contents.as_slice()
    {
        original.clone()
    } else {
        SurfaceExpressionCapture {
            expression,
            contents: contents.into(),
        }
    }
}

fn capture_contents(
    source: &SourceFile,
    node: &ConcreteNode,
    tokens: &ProjectionTokens<'_>,
    originals: &std::collections::HashMap<usize, crate::syntax::MacroOutputNode>,
) -> Result<Vec<crate::syntax::MacroOutputNode>, ProjectionError> {
    use crate::syntax::{MacroDelimiter, MacroOutputNode};

    fn sequence(
        source: &SourceFile,
        indices: &[usize],
        position: &mut usize,
        tokens: &ProjectionTokens<'_>,
        originals: &std::collections::HashMap<usize, MacroOutputNode>,
        closing: Option<TokenKind>,
    ) -> Result<Vec<MacroOutputNode>, ProjectionError> {
        let mut output = Vec::new();
        while let Some(&index) = indices.get(*position) {
            let token = tokens.get(index).ok_or(ProjectionError::MalformedTree(
                InternalReason::TokenOutOfRange,
            ))?;
            if closing
                .as_ref()
                .is_some_and(|kind| same_token_variant(kind, &token.kind))
            {
                *position += 1;
                return Ok(output);
            }
            *position += 1;
            if matches!(token.kind, TokenKind::LeftParen | TokenKind::LeftBrace) {
                let (delimiter, end) = if matches!(token.kind, TokenKind::LeftParen) {
                    (MacroDelimiter::Parentheses, TokenKind::RightParen)
                } else {
                    (MacroDelimiter::Braces, TokenKind::RightBrace)
                };
                let children = sequence(source, indices, position, tokens, originals, Some(end))?;
                let close = indices
                    .get(position.saturating_sub(1))
                    .and_then(|index| tokens.get(*index))
                    .ok_or(ProjectionError::MalformedTree(
                        InternalReason::UnexpectedShape,
                    ))?;
                let origin = match originals.get(&index) {
                    Some(MacroOutputNode::Group(_, _, origin)) => origin.clone(),
                    _ => join_spans(source, token.span, close.span)?.into(),
                };
                output.push(MacroOutputNode::Group(delimiter, children, origin));
            } else if matches!(token.kind, TokenKind::Dollar) {
                let next = indices
                    .get(*position)
                    .and_then(|index| tokens.projection_token(*index))
                    .ok_or(ProjectionError::MalformedTree(
                        InternalReason::UnexpectedShape,
                    ))?;
                *position += 1;
                output.push(MacroOutputNode::Splice(surface_name(next)?));
            } else if let Some(original) = originals.get(&index) {
                output.push(original.clone());
            } else if matches!(
                token.kind,
                TokenKind::Identifier(_) | TokenKind::UpperIdentifier(_)
            ) {
                let name = surface_name(tokens.projection_token(index).ok_or(
                    ProjectionError::MalformedTree(InternalReason::TokenOutOfRange),
                )?)?;
                output.push(MacroOutputNode::Identifier(name, token.span.into()));
            } else {
                let start = usize::try_from(token.span.range().start())
                    .map_err(|_| ProjectionError::MalformedTree(InternalReason::InvalidSpan))?;
                let end = usize::try_from(token.span.range().end())
                    .map_err(|_| ProjectionError::MalformedTree(InternalReason::InvalidSpan))?;
                let spelling = source
                    .text()
                    .get(start..end)
                    .ok_or(ProjectionError::MalformedTree(InternalReason::InvalidSpan))?;
                output.push(MacroOutputNode::Token(
                    token.kind.clone(),
                    spelling.into(),
                    token.span.into(),
                ));
            }
        }
        if closing.is_some() {
            return malformed(InternalReason::UnexpectedShape);
        }
        Ok(output)
    }

    let mut indices = Vec::new();
    let mut pending = node.children.iter().rev().collect::<Vec<_>>();
    while let Some(element) = pending.pop() {
        match element {
            ConcreteElement::Node(child) => pending.extend(child.children.iter().rev()),
            ConcreteElement::Token(index) => indices.push(*index),
            ConcreteElement::Missing { .. } | ConcreteElement::Error(_) => {
                return Err(ProjectionError::RecoveryNodesPresent);
            }
        }
    }
    sequence(source, &indices, &mut 0, tokens, originals, None)
}

fn validated_macro_root<'tree>(
    source: &SourceFile,
    tree: &'tree ConcreteTree,
) -> Result<&'tree ConcreteNode, ProjectionError> {
    if tree.resource_failure.is_some()
        || tree.malformed.is_some()
        || !tree.lexical_diagnostics.is_empty()
        || !tree.parse_diagnostics.is_empty()
    {
        return Err(ProjectionError::RecoveryNodesPresent);
    }
    validate_tokens(source, &tree.tokens)?;
    let root = tree
        .root
        .as_ref()
        .ok_or(ProjectionError::RecoveryNodesPresent)?;
    if has_recovery(root) || source_structural_depth_exceeds_budget(root) {
        return Err(ProjectionError::RecoveryNodesPresent);
    }
    validate_concrete_token_coverage(root, tree.tokens.len())?;
    Ok(root)
}

/// One selected invocation projected from its position in an ordered module tree.
#[allow(dead_code)]
pub(crate) struct ProjectedDeclarationInvocation {
    pub(crate) selection: crate::syntax::SelectedSyntax,
    pub(crate) name: SurfaceName,
    pub(crate) captures: Vec<SurfaceSyntaxCapture>,
    pub(crate) span: Span,
}

/// Project a declaration invocation in the module's existing child order.
///
/// `contexts` must retain the same selections and introduction-to-owner/import
/// mapping used to parse this tree. Matching spelling and matcher shape do not
/// establish selection identity.
#[allow(dead_code)]
pub(crate) fn project_declaration_invocation(
    source: &SourceFile,
    tree: &ConcreteTree,
    node: &ConcreteNode,
    contexts: &crate::syntax::SyntaxContexts,
) -> Result<ProjectedDeclarationInvocation, ProjectionError> {
    let (root, raw_tokens) = validated_root(source, tree)?;
    let tokens = ProjectionTokens::source(raw_tokens);
    project_declaration_invocation_from_tokens(source, root, node, &tokens, contexts)
}

/// Project a structured-output invocation in the existing child order.
///
/// `contexts` must retain the same selections and introduction-to-owner/import
/// mapping used to parse this tree. Matching spelling and matcher shape do not
/// establish selection identity.
#[allow(dead_code)]
pub(super) fn project_macro_declaration_invocation(
    source: &SourceFile,
    invocation: Span,
    construction: Option<(Span, usize)>,
    parsed: &super::ParsedMacroTree,
    node: &ConcreteNode,
    contexts: &crate::syntax::SyntaxContexts,
    frame: Option<&std::sync::Arc<crate::syntax::ExpansionFrame>>,
) -> Result<ProjectedDeclarationInvocation, ProjectionError> {
    let root = validated_macro_root(source, &parsed.tree)?;
    validate_node_shape_with_admission(
        root,
        &parsed.tree.tokens,
        Some(&parsed.admission_identifiers),
    )?;
    let tokens = ProjectionTokens {
        tokens: &parsed.tree.tokens,
        originals: Some(&parsed.original_nodes),
        occurrence: Some(invocation),
        construction,
        construction_extents: false,
        admission_identifiers: Some(&parsed.admission_identifiers),
        frame,
        name_frame: frame,
        preserve_name_diagnostic: true,
    };
    project_declaration_invocation_from_tokens(source, root, node, &tokens, contexts)
}

fn project_declaration_invocation_from_tokens(
    source: &SourceFile,
    root: &ConcreteNode,
    node: &ConcreteNode,
    tokens: &ProjectionTokens<'_>,
    contexts: &crate::syntax::SyntaxContexts,
) -> Result<ProjectedDeclarationInvocation, ProjectionError> {
    if node.kind != NodeKind::DeclarationSyntaxInvocation
        || !child_nodes(root).any(|child| std::ptr::eq(child, node))
    {
        return malformed(InternalReason::UnexpectedShape);
    }
    let mut children = node.children.iter();
    let Some(ConcreteElement::Token(index)) = children.next() else {
        return malformed(InternalReason::UnexpectedShape);
    };
    let name = surface_name(tokens.projection_token(*index).ok_or(
        ProjectionError::MalformedTree(InternalReason::TokenOutOfRange),
    )?)?;
    let selection = contexts
        .select(&name)
        .filter(|selected| selected.declaration.category == SurfaceSyntaxCategory::Declaration)
        .ok_or(ProjectionError::MalformedTree(
            InternalReason::UnexpectedShape,
        ))?
        .clone();
    let empty = std::collections::HashMap::new();
    let originals = tokens.originals.unwrap_or(&empty);
    let mut captures = Vec::new();
    for part in &selection.declaration.matcher {
        match (part, children.next()) {
            (
                SurfaceSyntaxMatcherPart::Literal { kind, spelling },
                Some(ConcreteElement::Token(index)),
            ) => {
                let token = tokens.get(*index).ok_or(ProjectionError::MalformedTree(
                    InternalReason::TokenOutOfRange,
                ))?;
                let range = token.span.range();
                let actual = match originals.get(index) {
                    Some(crate::syntax::MacroOutputNode::Token(_, spelling, _)) => {
                        Some(spelling.as_ref())
                    }
                    Some(crate::syntax::MacroOutputNode::Identifier(name, _)) => {
                        Some(name.text.as_str())
                    }
                    _ => source
                        .text()
                        .get(range.start() as usize..range.end() as usize),
                };
                if &token.kind != kind || actual != Some(spelling.as_str()) {
                    return malformed(InternalReason::UnexpectedShape);
                }
            }
            (
                SurfaceSyntaxMatcherPart::Capture { kind, .. },
                Some(ConcreteElement::Node(argument)),
            ) if argument.kind == NodeKind::SyntaxArgument => match kind {
                SurfaceSyntaxCaptureKind::Identifier => {
                    captures.push(SurfaceSyntaxCapture::Identifier(
                        project_syntax_identifier_capture(argument, tokens, originals)?,
                    ));
                }
                SurfaceSyntaxCaptureKind::Expression => {
                    let expression = child_nodes(argument)
                        .find(|child| is_expression_kind(child.kind))
                        .ok_or(ProjectionError::MalformedTree(
                            InternalReason::UnexpectedShape,
                        ))?;
                    let contents = capture_contents(source, expression, tokens, originals)?;
                    let expression =
                        project_expression_with_fragments(source, expression, tokens, originals)?;
                    captures.push(SurfaceSyntaxCapture::Expression(
                        project_syntax_expression_capture(expression, contents),
                    ));
                }
            },
            _ => return malformed(InternalReason::UnexpectedShape),
        }
    }
    if children.next().is_some() {
        return malformed(InternalReason::UnexpectedShape);
    }
    Ok(ProjectedDeclarationInvocation {
        selection,
        name,
        captures,
        span: node_span(source, node, tokens)?,
    })
}

pub(super) fn project_macro_declarations(
    source: &SourceFile,
    invocation: Span,
    construction: Option<(Span, usize)>,
    tree: &ConcreteTree,
    original_nodes: &std::collections::HashMap<usize, crate::syntax::MacroOutputNode>,
    admission_identifiers: &std::collections::HashSet<usize>,
    frame: Option<&std::sync::Arc<crate::syntax::ExpansionFrame>>,
) -> Result<SurfaceModule, ProjectionError> {
    let root = validated_macro_root(source, tree)?;
    validate_node_shape_with_admission(root, &tree.tokens, Some(admission_identifiers))?;
    if child_nodes(root).any(|child| {
        matches!(
            child.kind,
            NodeKind::ImportDeclaration | NodeKind::SyntaxDeclaration
        )
    }) {
        return malformed(InternalReason::UnexpectedShape);
    }
    let tokens = ProjectionTokens {
        tokens: &tree.tokens,
        originals: Some(original_nodes),
        occurrence: Some(invocation),
        construction,
        construction_extents: false,
        admission_identifiers: Some(admission_identifiers),
        frame,
        name_frame: frame,
        preserve_name_diagnostic: true,
    };
    project_surface_module(source, root, &tokens)
}

pub(super) fn project_macro_expression(
    source: &SourceFile,
    invocation: Span,
    construction: Option<(Span, usize)>,
    tree: &ConcreteTree,
    original_nodes: &std::collections::HashMap<usize, crate::syntax::MacroOutputNode>,
    admission_identifiers: &std::collections::HashSet<usize>,
    frame: Option<&std::sync::Arc<crate::syntax::ExpansionFrame>>,
) -> Result<SurfaceExpr, ProjectionError> {
    let root = validated_macro_root(source, tree)?;
    let expression = expression_child(root)?;
    validate_node_shape_with_admission(expression, &tree.tokens, Some(admission_identifiers))?;
    let tokens = ProjectionTokens {
        tokens: &tree.tokens,
        originals: Some(original_nodes),
        occurrence: Some(invocation),
        construction,
        construction_extents: false,
        admission_identifiers: Some(admission_identifiers),
        frame,
        name_frame: None,
        preserve_name_diagnostic: false,
    };
    project_expression_with_fragments(source, expression, &tokens, original_nodes)
}

fn project_expression_with_fragments(
    source: &SourceFile,
    node: &ConcreteNode,
    tokens: &ProjectionTokens<'_>,
    original_nodes: &std::collections::HashMap<usize, crate::syntax::MacroOutputNode>,
) -> Result<SurfaceExpr, ProjectionError> {
    let mut tasks = vec![ExpressionTask::Visit(node)];
    let mut projected = Vec::new();
    while let Some(task) = tasks.pop() {
        if let (ExpressionTask::Visit(node), Some(frame)) = (&task, tokens.frame) {
            let original = node.children.iter().find_map(|child| match child {
                ConcreteElement::Token(index) => original_nodes.get(index),
                _ => None,
            });
            let (cause, capture, token_cause) = match original {
                Some(crate::syntax::MacroOutputNode::Expression(_, origin)) => {
                    (Some(origin.clone()), true, false)
                }
                Some(crate::syntax::MacroOutputNode::ForwardedExpression(_, _)) => {
                    (None, true, false)
                }
                Some(crate::syntax::MacroOutputNode::Token(_, _, origin)) => {
                    (Some(origin.clone()), false, true)
                }
                Some(crate::syntax::MacroOutputNode::Identifier(_, origin))
                | Some(crate::syntax::MacroOutputNode::Group(_, _, origin)) => {
                    (Some(origin.clone()), false, false)
                }
                _ => (None, false, false),
            };
            tasks.push(ExpressionTask::FinishDiagnostic {
                cause,
                capture,
                token_cause,
                frame: std::sync::Arc::clone(frame),
            });
        }
        match task {
            ExpressionTask::Visit(node) => match node.kind {
                NodeKind::SyntaxInvocation => {
                    let index = node
                        .children
                        .iter()
                        .find_map(|child| match child {
                            ConcreteElement::Token(index) => Some(*index),
                            _ => None,
                        })
                        .ok_or(ProjectionError::MalformedTree(
                            InternalReason::UnexpectedShape,
                        ))?;
                    let name = match original_nodes.get(&index) {
                        Some(crate::syntax::MacroOutputNode::Identifier(name, _)) => name.clone(),
                        _ => surface_name(tokens.projection_token(index).ok_or(
                            ProjectionError::MalformedTree(InternalReason::TokenOutOfRange),
                        )?)?,
                    };
                    let mut captures = Vec::new();
                    let mut expressions = Vec::new();
                    let mut contents = Vec::new();
                    for argument in
                        child_nodes(node).filter(|child| child.kind == NodeKind::SyntaxArgument)
                    {
                        if let Some(expression) =
                            child_nodes(argument).find(|child| is_expression_kind(child.kind))
                        {
                            captures.push(None);
                            expressions.push(expression);
                            contents.push(capture_contents(
                                source,
                                expression,
                                tokens,
                                original_nodes,
                            )?);
                        } else {
                            captures.push(Some(project_syntax_identifier_capture(
                                argument,
                                tokens,
                                original_nodes,
                            )?));
                        }
                    }
                    tasks.push(ExpressionTask::FinishSyntaxInvocation {
                        name,
                        captures,
                        contents,
                        span: node_span(source, node, tokens)?,
                    });
                    tasks.extend(expressions.into_iter().rev().map(ExpressionTask::Visit));
                }
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
                            diagnostic: None,
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
                    source,
                    node,
                    tokens,
                    &TokenKind::EqualEqual,
                    SurfaceExprKind::Equal,
                    &mut tasks,
                )?,
                NodeKind::AdditiveExpression => schedule_binary(
                    source,
                    node,
                    tokens,
                    &TokenKind::Plus,
                    SurfaceExprKind::Add,
                    &mut tasks,
                )?,
                NodeKind::MultiplicativeExpression => schedule_binary(
                    source,
                    node,
                    tokens,
                    &TokenKind::Star,
                    SurfaceExprKind::Multiply,
                    &mut tasks,
                )?,
                NodeKind::ApplicationExpression => {
                    let (function, argument) = expression_pair(node)?;
                    tasks.push(ExpressionTask::FinishApplication(node_span(
                        source, node, tokens,
                    )?));
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
                    let handle =
                        project_binder(only_child_of_kind(node, NodeKind::Binder)?, tokens)?;
                    tasks.push(ExpressionTask::FinishProviderResource {
                        arguments: family.arguments,
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
                NodeKind::RegionExpression => {
                    let identity = direct_tokens(node, tokens)
                        .find(ProjectionToken::is_upper_identifier)
                        .ok_or(ProjectionError::MalformedTree(
                            InternalReason::UnexpectedShape,
                        ))?;
                    let handle =
                        project_binder(only_child_of_kind(node, NodeKind::Binder)?, tokens)?;
                    let provider = optional_child_of_kind(node, NodeKind::PrimaryExpression)?;
                    tasks.push(ExpressionTask::FinishRegion {
                        identity: surface_name(identity)?,
                        handle: handle.name,
                        has_provider: provider.is_some(),
                        span: node_span(source, node, tokens)?,
                    });
                    tasks.push(ExpressionTask::Visit(only_child_of_kind(
                        node,
                        NodeKind::Block,
                    )?));
                    if let Some(provider) = provider {
                        tasks.push(ExpressionTask::Visit(provider));
                    }
                }
                NodeKind::RegionSelectionExpression => {
                    tasks.push(ExpressionTask::FinishRegionSelection(node_span(
                        source, node, tokens,
                    )?));
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
                        .find(ProjectionToken::is_upper_identifier)
                        .ok_or(ProjectionError::MalformedTree(
                            InternalReason::UnexpectedShape,
                        ))?;
                    let handle =
                        project_binder(only_child_of_kind(node, NodeKind::Binder)?, tokens)?;
                    tasks.push(ExpressionTask::FinishResource {
                        kind: match direct_tokens(node, tokens).find_map(|token| {
                            if let TokenKind::Identifier(name) = &token.token.kind {
                                Some(name.as_str())
                            } else {
                                None
                            }
                        }) {
                            Some("cell") => crate::surface::SurfaceResourceKind::Cell,
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
                    let mut operands =
                        child_nodes(node).filter(|child| is_expression_kind(child.kind));
                    let body = operands.next().ok_or(ProjectionError::MalformedTree(
                        InternalReason::UnexpectedShape,
                    ))?;
                    let store = if direct_tokens(node, tokens)
                        .any(|token| token.kind == TokenKind::Using)
                    {
                        Some(operands.next().ok_or(ProjectionError::MalformedTree(
                            InternalReason::UnexpectedShape,
                        ))?)
                    } else {
                        None
                    };
                    if operands.next().is_some() {
                        return malformed(InternalReason::UnexpectedShape);
                    }
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
                        has_store: store.is_some(),
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
                    if let Some(store) = store {
                        tasks.push(ExpressionTask::Visit(store));
                    }
                }
                NodeKind::PrimaryExpression => {
                    if let [ConcreteElement::Token(index)] = node.children.as_slice()
                        && let Some(
                            crate::syntax::MacroOutputNode::Expression(capture, _)
                            | crate::syntax::MacroOutputNode::ForwardedExpression(capture, _),
                        ) = original_nodes.get(index)
                    {
                        projected.push(capture.expression.clone());
                    } else if let Some(group) =
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
                        let reference = SurfaceReference::Qualified(name);
                        projected.push(SurfaceExpr {
                            diagnostic: reference.diagnostic_location(),
                            span: reference.span(),
                            kind: SurfaceExprKind::Name(reference),
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
            ExpressionTask::FinishSyntaxInvocation {
                name,
                captures,
                contents,
                span,
            } => {
                let count = captures.iter().filter(|capture| capture.is_none()).count();
                let split =
                    projected
                        .len()
                        .checked_sub(count)
                        .ok_or(ProjectionError::MalformedTree(
                            InternalReason::UnexpectedShape,
                        ))?;
                let mut expressions = projected.split_off(split).into_iter();
                let mut contents = contents.into_iter();
                let captures = captures
                    .into_iter()
                    .map(|capture| match capture {
                        Some(name) => Ok(SurfaceSyntaxCapture::Identifier(name)),
                        None => {
                            let expression = expressions.next().ok_or(
                                ProjectionError::MalformedTree(InternalReason::UnexpectedShape),
                            )?;
                            let contents = contents.next().ok_or(
                                ProjectionError::MalformedTree(InternalReason::UnexpectedShape),
                            )?;
                            Ok(SurfaceSyntaxCapture::Expression(
                                project_syntax_expression_capture(expression, contents),
                            ))
                        }
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                projected.push(SurfaceExpr {
                    diagnostic: None,
                    kind: SurfaceExprKind::SyntaxInvocation { name, captures },
                    span,
                });
            }
            ExpressionTask::FinishBinary {
                make_kind,
                operator_span,
                span,
            } => {
                let (left, right) = take_expression_pair(&mut projected)?;
                projected.push(SurfaceExpr {
                    diagnostic: None,
                    kind: make_kind(BinaryExpr {
                        left: Box::new(left),
                        right: Box::new(right),
                        operator_span,
                    }),
                    span,
                });
            }
            ExpressionTask::FinishApplication(span) => {
                let (function, argument) = take_expression_pair(&mut projected)?;
                projected.push(SurfaceExpr {
                    diagnostic: None,
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
                    diagnostic: None,
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
                    diagnostic: None,
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
                    diagnostic: None,
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
                    diagnostic: None,
                    kind: SurfaceExprKind::Resume(Box::new(value)),
                    span,
                });
            }

            ExpressionTask::FinishProviderResource {
                family,
                arguments,
                handle,
                span,
            } => {
                let (initializer, body) = take_expression_pair(&mut projected)?;
                let SurfaceExprKind::Block(body) = body.kind else {
                    return malformed(InternalReason::UnexpectedShape);
                };
                projected.push(SurfaceExpr {
                    diagnostic: None,
                    kind: SurfaceExprKind::ProviderResource(Box::new(
                        crate::surface::SurfaceProviderResourceExpr {
                            family,
                            arguments,
                            handle,
                            initializer,
                            body,
                        },
                    )),
                    span,
                });
            }
            ExpressionTask::FinishRegion {
                identity,
                handle,
                has_provider,
                span,
            } => {
                let body = projected.pop().ok_or(ProjectionError::MalformedTree(
                    InternalReason::UnexpectedShape,
                ))?;
                let SurfaceExprKind::Block(body) = body.kind else {
                    return malformed(InternalReason::UnexpectedShape);
                };
                let provider = if has_provider {
                    Some(projected.pop().ok_or(ProjectionError::MalformedTree(
                        InternalReason::UnexpectedShape,
                    ))?)
                } else {
                    None
                };
                projected.push(SurfaceExpr {
                    diagnostic: None,
                    kind: SurfaceExprKind::Region(Box::new(crate::surface::SurfaceRegionExpr {
                        identity,
                        handle,
                        provider,
                        body,
                    })),
                    span,
                });
            }
            ExpressionTask::FinishRegionSelection(span) => {
                let (region, body) = take_expression_pair(&mut projected)?;
                let SurfaceExprKind::Block(body) = body.kind else {
                    return malformed(InternalReason::UnexpectedShape);
                };
                projected.push(SurfaceExpr {
                    diagnostic: None,
                    kind: SurfaceExprKind::RegionSelection(Box::new(
                        crate::surface::SurfaceRegionSelectionExpr { region, body },
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
                    diagnostic: None,
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
                    diagnostic: None,
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
                    diagnostic: None,
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
                    diagnostic: None,
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
                has_store,
                clauses,
                span,
            } => {
                let split = projected
                    .len()
                    .checked_sub(clauses.len().saturating_add(1 + usize::from(has_store)))
                    .ok_or(ProjectionError::MalformedTree(
                        InternalReason::UnexpectedShape,
                    ))?;
                let mut expressions = projected.split_off(split).into_iter();
                let store = if has_store {
                    Some(Box::new(expressions.next().ok_or(
                        ProjectionError::MalformedTree(InternalReason::UnexpectedShape),
                    )?))
                } else {
                    None
                };
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
                    diagnostic: None,
                    kind: SurfaceExprKind::Handle(SurfaceHandleExpr {
                        body: Box::new(body),
                        effect,
                        store,
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
                                    binder_splice: member.binder_splice,
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
                    diagnostic: None,
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
                    diagnostic: None,
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
            ExpressionTask::FinishDiagnostic {
                cause,
                capture,
                token_cause,
                frame,
            } => {
                let expression = projected.last_mut().ok_or(ProjectionError::MalformedTree(
                    InternalReason::UnexpectedShape,
                ))?;
                let span = expression.span;
                let location = expression.diagnostic.get_or_insert_with(|| {
                    let mut location = crate::syntax::DiagnosticLocation::new(if capture {
                        span.into()
                    } else {
                        cause.clone().unwrap_or_else(|| span.into())
                    });
                    location.token_cause = token_cause;
                    Box::new(location)
                });
                if capture && let Some(cause) = cause {
                    location.related.push(cause);
                }
                location.captured_expression |= capture;
                location.add_frame(&frame);
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
    FinishDiagnostic {
        cause: Option<crate::syntax::MacroOrigin>,
        capture: bool,
        token_cause: bool,
        frame: std::sync::Arc<crate::syntax::ExpansionFrame>,
    },
    FinishSyntaxInvocation {
        name: SurfaceName,
        captures: Vec<Option<SurfaceIdentifierCapture>>,
        contents: Vec<Vec<crate::syntax::MacroOutputNode>>,
        span: Span,
    },
    FinishBinary {
        make_kind: fn(BinaryExpr) -> SurfaceExprKind,
        operator_span: Span,
        span: Span,
    },
    FinishApplication(Span),
    FinishPerform {
        effect: SurfaceReference,
        arguments: Vec<SurfaceType>,
        operation: SurfaceName,
        span: Span,
    },
    FinishResume(Span),
    FinishCleanup(Span),
    FinishRegion {
        identity: SurfaceName,
        handle: SurfaceName,
        has_provider: bool,
        span: Span,
    },
    FinishRegionSelection(Span),

    FinishProviderResource {
        family: SurfaceReference,
        arguments: Vec<SurfaceType>,
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
        has_store: bool,
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
    binder_splice: bool,
    annotation: SurfaceType,
    span: Span,
}

fn schedule_block<'a>(
    source: &SourceFile,
    node: &'a ConcreteNode,
    tokens: &ProjectionTokens<'_>,
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
                let (binder, binder_splice) = project_recursive_binder(
                    only_child_of_kind(member, NodeKind::Binder)?,
                    tokens,
                )?;
                members.push(PendingRecursiveMember {
                    introducer_span: member_introducers.next().ok_or(
                        ProjectionError::MalformedTree(InternalReason::UnexpectedShape),
                    )?,
                    binder,
                    binder_splice,
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
    source: &SourceFile,
    node: &'a ConcreteNode,
    tokens: &ProjectionTokens<'_>,
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
        span: node_span(source, node, tokens)?,
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
    tokens: &ProjectionTokens<'_>,
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
            diagnostic: None,
            kind: SurfaceExprKind::Unit,
            span,
        });
    }
    Ok(())
}

fn project_primitive(
    node: &ConcreteNode,
    tokens: &ProjectionTokens<'_>,
) -> Result<SurfaceExpr, ProjectionError> {
    let mut direct = direct_tokens(node, tokens);
    if direct
        .next()
        .is_some_and(|token| token.kind == TokenKind::Dollar)
    {
        let name = surface_name(direct.next().ok_or(ProjectionError::MalformedTree(
            InternalReason::UnexpectedShape,
        ))?)?;
        if direct.next().is_some() {
            return malformed(InternalReason::UnexpectedShape);
        }
        return Ok(SurfaceExpr {
            diagnostic: None,
            span: name.span,
            kind: SurfaceExprKind::TemplateSplice(name),
        });
    }
    let token = only_direct_token(node, tokens)?;
    let kind = match &token.kind {
        TokenKind::Integer(value) => SurfaceExprKind::Integer(value.clone()),
        TokenKind::StringLiteral(value) => SurfaceExprKind::String(value.clone()),
        TokenKind::True => SurfaceExprKind::Boolean(true),
        TokenKind::False => SurfaceExprKind::Boolean(false),
        TokenKind::Discard => SurfaceExprKind::Discard,
        TokenKind::Retain => SurfaceExprKind::Retain,
        TokenKind::Identifier(_) | TokenKind::UpperIdentifier(_) => {
            SurfaceExprKind::Name(SurfaceReference::Unqualified(surface_name(token)?))
        }
        _ => return malformed(InternalReason::UnexpectedShape),
    };
    Ok(SurfaceExpr {
        diagnostic: None,
        kind,
        span: token.span,
    })
}

fn project_block(
    source: &SourceFile,
    node: &ConcreteNode,
    tokens: &ProjectionTokens<'_>,
) -> Result<SurfaceBlock, ProjectionError> {
    let expression = project_expression(source, node, tokens)?;
    let SurfaceExprKind::Block(block) = expression.kind else {
        return malformed(InternalReason::UnexpectedShape);
    };
    Ok(block)
}

fn project_binder(
    node: &ConcreteNode,
    tokens: &ProjectionTokens<'_>,
) -> Result<SurfaceBinder, ProjectionError> {
    require_kind(node, NodeKind::Binder)?;
    let token = only_direct_token(node, tokens)?;
    let TokenKind::Identifier(_) = &token.kind else {
        return malformed(InternalReason::UnexpectedShape);
    };
    let name = surface_name(token)?;
    Ok(SurfaceBinder {
        name,
        span: token.span,
    })
}

fn project_recursive_binder(
    node: &ConcreteNode,
    tokens: &ProjectionTokens<'_>,
) -> Result<(SurfaceBinder, bool), ProjectionError> {
    let mut direct = direct_tokens(node, tokens);
    let Some(first) = direct.next() else {
        return malformed(InternalReason::UnexpectedShape);
    };
    if !matches!(first.kind, TokenKind::Dollar) {
        return project_binder(node, tokens).map(|binder| (binder, false));
    }
    let token = direct.next().ok_or(ProjectionError::MalformedTree(
        InternalReason::UnexpectedShape,
    ))?;
    if direct.next().is_some() || !matches!(token.kind, TokenKind::Identifier(_)) {
        return malformed(InternalReason::UnexpectedShape);
    }
    Ok((
        SurfaceBinder {
            name: surface_name(token)?,
            span: token.span,
        },
        true,
    ))
}

fn surface_name(token: ProjectionToken<'_>) -> Result<SurfaceName, ProjectionError> {
    match token.original {
        Some(crate::syntax::MacroOutputNode::Identifier(name, origin)) => {
            let mut name = name.clone();
            let mut diagnostic = crate::syntax::DiagnosticLocation::new(origin.clone());
            if token.preserve_name_diagnostic
                && let Some(previous) = &name.diagnostic
            {
                if previous.primary == diagnostic.primary {
                    diagnostic.related.extend(previous.related.iter().cloned());
                    for frame in &previous.frames {
                        diagnostic.add_frame(frame);
                    }
                } else {
                    diagnostic.add_cause(previous);
                }
                diagnostic.token_cause = previous.token_cause;
                diagnostic.captured_expression = previous.captured_expression;
            }
            if let Some(frame) = token.name_frame {
                diagnostic.add_frame(frame);
            }
            name.diagnostic = Some(Box::new(diagnostic));
            return Ok(name);
        }
        Some(
            crate::syntax::MacroOutputNode::Expression(_, _)
            | crate::syntax::MacroOutputNode::ForwardedExpression(_, _),
        ) => {
            return malformed(InternalReason::UnexpectedShape);
        }
        _ => {}
    }
    let text = match &token.kind {
        TokenKind::Identifier(text) | TokenKind::UpperIdentifier(text) => text.clone(),
        _ => return malformed(InternalReason::UnexpectedShape),
    };
    Ok(SurfaceName {
        text,
        span: token.span,
        introduction: 0,
        introduced_at: None,
        written: true,
        diagnostic: None,
    })
}

fn project_qualified_name(
    source: &SourceFile,
    node: &ConcreteNode,
    tokens: &ProjectionTokens<'_>,
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
    tokens: &ProjectionTokens<'_>,
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
    tokens: &ProjectionTokens<'_>,
) -> Result<SurfacePattern, ProjectionError> {
    require_kind(node, NodeKind::Pattern)?;
    let span = node_span(source, node, tokens)?;
    let diagnostic = project_pattern_diagnostic(node, tokens, span)?;
    let kind = if direct_tokens(node, tokens)
        .next()
        .is_some_and(|token| token.kind == TokenKind::Dollar)
    {
        let name = direct_tokens(node, tokens)
            .nth(1)
            .ok_or(ProjectionError::MalformedTree(
                InternalReason::UnexpectedShape,
            ))?;
        SurfacePatternKind::TemplateSplice(surface_name(name)?)
    } else if let Some(binder) = optional_child_of_kind(node, NodeKind::Binder)? {
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
                .find(ProjectionToken::is_upper_identifier)
                .ok_or(ProjectionError::MalformedTree(
                    InternalReason::UnexpectedShape,
                ))?;
            SurfaceReference::Unqualified(surface_name(token)?)
        };
        let payload = if let Some(tuple) =
            optional_child_of_kind(constructor, NodeKind::TuplePattern)?
        {
            Some(Box::new(SurfacePattern {
                diagnostic: project_pattern_diagnostic(
                    tuple,
                    tokens,
                    node_span(source, tuple, tokens)?,
                )?,
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
    Ok(SurfacePattern {
        kind,
        span,
        diagnostic,
    })
}

fn project_pattern_diagnostic(
    node: &ConcreteNode,
    tokens: &ProjectionTokens<'_>,
    span: Span,
) -> Result<Option<Box<crate::syntax::DiagnosticLocation>>, ProjectionError> {
    let Some(frame) = tokens.frame else {
        return Ok(None);
    };
    let index = descendant_edge_index(node, false)?;
    let origin = match tokens.originals.and_then(|originals| originals.get(&index)) {
        Some(crate::syntax::MacroOutputNode::Token(_, _, origin))
        | Some(crate::syntax::MacroOutputNode::Identifier(_, origin))
        | Some(crate::syntax::MacroOutputNode::Group(_, _, origin)) => origin.clone(),
        _ => span.into(),
    };
    let mut location = crate::syntax::DiagnosticLocation::new(origin);
    location.add_frame(frame);
    Ok(Some(Box::new(location)))
}

fn project_pattern_children(
    source: &SourceFile,
    node: &ConcreteNode,
    tokens: &ProjectionTokens<'_>,
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
    tokens: &ProjectionTokens<'_>,
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
    tokens: &ProjectionTokens<'_>,
) -> Result<SurfaceTypeParameter, ProjectionError> {
    require_kind(node, NodeKind::TypeParameter)?;
    let name = surface_name(
        direct_tokens(node, tokens)
            .find(ProjectionToken::is_upper_identifier)
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
    tokens: &ProjectionTokens<'_>,
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
            .find(ProjectionToken::is_upper_identifier)
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
    tokens: &ProjectionTokens<'_>,
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
                        .filter(ProjectionToken::is_upper_identifier)
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
                                .find(ProjectionToken::is_upper_identifier)
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
                                diagnostic: None,
                            });
                        } else {
                            projected.push(project_atomic_primitive(node, tokens)?);
                        }
                    } else {
                        let constructor = if let Some(name) = qualified {
                            SurfaceReference::Qualified(name)
                        } else {
                            let token = direct_tokens(node, tokens)
                                .find(ProjectionToken::is_upper_identifier)
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
                    diagnostic: None,
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
                    diagnostic: None,
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
                    diagnostic: None,
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
                    diagnostic: None,
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
    tokens: &ProjectionTokens<'_>,
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
    tokens: &ProjectionTokens<'_>,
) -> Result<SurfaceEffectInstance, ProjectionError> {
    require_kind(instance, NodeKind::EffectInstance)?;
    let qualified = optional_child_of_kind(instance, NodeKind::QualifiedName)?
        .map(|name| project_qualified_name(source, name, tokens))
        .transpose()?;
    let effect = if let Some(name) = qualified {
        SurfaceReference::Qualified(name)
    } else {
        let token = direct_tokens(instance, tokens)
            .find(ProjectionToken::is_upper_identifier)
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
    tokens: &ProjectionTokens<'_>,
) -> Result<(SurfaceReference, Vec<SurfaceType>, SurfaceName), ProjectionError> {
    require_kind(node, NodeKind::OperationReference)?;
    let effect = if let Some(qualified) = optional_child_of_kind(node, NodeKind::QualifiedName)? {
        SurfaceReference::Qualified(project_qualified_name(source, qualified, tokens)?)
    } else {
        let token = direct_tokens(node, tokens)
            .find(ProjectionToken::is_upper_identifier)
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
        .filter(|token| matches!(token.kind, TokenKind::Identifier(_)))
        .last()
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
    tokens: &ProjectionTokens<'_>,
) -> Result<SurfaceType, ProjectionError> {
    let token = only_direct_token(node, tokens)?;
    let kind = match token.kind {
        TokenKind::IntType => SurfaceTypeKind::Int,
        TokenKind::BytesType => SurfaceTypeKind::Bytes,
        TokenKind::StringType => SurfaceTypeKind::String,
        TokenKind::BoolType => SurfaceTypeKind::Bool,
        TokenKind::UnitType => SurfaceTypeKind::Unit,
        TokenKind::UpperIdentifier(_) | TokenKind::Identifier(_) if token.is_upper_identifier() => {
            SurfaceTypeKind::Named(SurfaceReference::Unqualified(surface_name(token)?))
        }
        _ => return malformed(InternalReason::UnexpectedShape),
    };
    let diagnostic = if matches!(kind, SurfaceTypeKind::Named(_)) {
        None
    } else if let (Some(crate::syntax::MacroOutputNode::Token(_, _, origin)), Some(frame)) =
        (token.original, tokens.frame)
    {
        let mut location = crate::syntax::DiagnosticLocation::new(origin.clone());
        location.add_frame(frame);
        Some(Box::new(location))
    } else {
        None
    };
    Ok(SurfaceType {
        kind,
        span: if tokens.construction_extents && tokens.construction.is_some() {
            tokens
                .original_span(token)
                .ok_or(ProjectionError::MalformedTree(InternalReason::InvalidSpan))?
        } else {
            tokens.occurrence.unwrap_or(token.span)
        },
        diagnostic,
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
            | NodeKind::SyntaxInvocation
            | NodeKind::FunctionExpression
            | NodeKind::MatchExpression
            | NodeKind::HandlerExpression
            | NodeKind::ResumeExpression
            | NodeKind::ProviderResourceExpression
            | NodeKind::ResourceExpression
            | NodeKind::RegionExpression
            | NodeKind::RegionSelectionExpression
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

fn only_direct_token<'a, T: ProjectionTokenSource + ?Sized>(
    node: &ConcreteNode,
    tokens: &'a T,
) -> Result<ProjectionToken<'a>, ProjectionError> {
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
    tokens
        .projection_token(index)
        .ok_or(ProjectionError::MalformedTree(
            InternalReason::TokenOutOfRange,
        ))
}

fn direct_tokens<'a, T: ProjectionTokenSource + ?Sized>(
    node: &'a ConcreteNode,
    tokens: &'a T,
) -> impl Iterator<Item = ProjectionToken<'a>> {
    node.children.iter().filter_map(|child| match child {
        ConcreteElement::Token(index) => tokens.projection_token(*index),
        _ => None,
    })
}

fn same_token_variant(left: &TokenKind, right: &TokenKind) -> bool {
    std::mem::discriminant(left) == std::mem::discriminant(right)
}

fn node_span(
    source: &SourceFile,
    node: &ConcreteNode,
    tokens: &ProjectionTokens<'_>,
) -> Result<Span, ProjectionError> {
    if tokens.construction_extents && tokens.construction.is_some() {
        let mut pending = node.children.iter().rev().collect::<Vec<_>>();
        let mut extent: Option<Span> = None;
        while let Some(element) = pending.pop() {
            match element {
                ConcreteElement::Node(child) => pending.extend(child.children.iter().rev()),
                ConcreteElement::Token(index) => {
                    let span = tokens
                        .projection_token(*index)
                        .and_then(|token| tokens.original_span(token))
                        .ok_or(ProjectionError::MalformedTree(InternalReason::InvalidSpan))?;
                    extent = Some(match extent {
                        Some(previous) => previous
                            .cover(span)
                            .ok_or(ProjectionError::MalformedTree(InternalReason::ForeignSpan))?,
                        None => span,
                    });
                }
                ConcreteElement::Missing { .. } | ConcreteElement::Error(_) => {
                    return Err(ProjectionError::RecoveryNodesPresent);
                }
            }
        }
        return extent.ok_or(ProjectionError::MalformedTree(
            InternalReason::UnexpectedShape,
        ));
    }
    if let Some(occurrence) = tokens.occurrence {
        return Ok(occurrence);
    }
    let first = descendant_edge_span(node, tokens, false)?;
    let last = descendant_edge_span(node, tokens, true)?;
    join_spans(source, first, last)
}

fn descendant_edge_span(
    node: &ConcreteNode,
    tokens: &[Token],
    from_back: bool,
) -> Result<Span, ProjectionError> {
    let index = descendant_edge_index(node, from_back)?;
    tokens
        .get(index)
        .map(|token| token.span)
        .ok_or(ProjectionError::MalformedTree(
            InternalReason::TokenOutOfRange,
        ))
}

fn descendant_edge_index(node: &ConcreteNode, from_back: bool) -> Result<usize, ProjectionError> {
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
            ConcreteElement::Token(index) => return Ok(*index),
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
    tokens: &ProjectionTokens<'_>,
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
    let clauses = project_resource_handler_clauses(source, handlers, tokens)?;
    Ok(crate::surface::SurfaceResourceDefinition {
        public: direct_tokens(node, tokens).any(|token| token.kind == TokenKind::Pub),
        name: surface_name(
            direct_tokens(node, tokens)
                .find(ProjectionToken::is_upper_identifier)
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
        family: optional_child_of_kind(node, NodeKind::ResourceFamily)?
            .map(|family| project_resource_family(source, family, tokens))
            .transpose()?,
        acquire_binder: project_field_binder(acquire)?,
        acquire: project_expression(source, expression_child(acquire)?, tokens)?,
        finish_binder: project_field_binder(finish)?,
        finish: project_expression(source, expression_child(finish)?, tokens)?,
        handlers_binder: project_field_binder(handlers)?,
        handlers: clauses,
        span: node_span(source, node, tokens)?,
    })
}

fn project_resource_handler_clauses(
    source: &SourceFile,
    handlers: &ConcreteNode,
    tokens: &ProjectionTokens<'_>,
) -> Result<Vec<SurfaceHandlerClause>, ProjectionError> {
    child_nodes(handlers)
        .filter(|child| child.kind == NodeKind::HandlerClause)
        .map(|clause| {
            Ok(SurfaceHandlerClause {
                operation: project_binder(only_child_of_kind(clause, NodeKind::Binder)?, tokens)?
                    .name,
                pattern: project_pattern(
                    source,
                    only_child_of_kind(clause, NodeKind::Pattern)?,
                    tokens,
                )?,
                body: project_expression(source, expression_child(clause)?, tokens)?,
                span: node_span(source, clause, tokens)?,
            })
        })
        .collect()
}

fn project_resource_family(
    source: &SourceFile,
    node: &ConcreteNode,
    tokens: &ProjectionTokens<'_>,
) -> Result<crate::surface::SurfaceResourceFamily, ProjectionError> {
    let fields = child_nodes(node)
        .filter(|child| child.kind == NodeKind::ResourceField)
        .collect::<Vec<_>>();
    let [provider, provided, interpreted, handlers] = fields.as_slice() else {
        return malformed(InternalReason::UnexpectedShape);
    };
    let parameters = project_optional_type_parameters(source, node, tokens)?.ok_or(
        ProjectionError::MalformedTree(InternalReason::UnexpectedShape),
    )?;
    let [parameter] = parameters.as_slice() else {
        return malformed(InternalReason::UnexpectedShape);
    };
    Ok(crate::surface::SurfaceResourceFamily {
        parameter: parameter.clone(),
        requirements: project_requirements(source, node, tokens)?,
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
        handlers_binder: project_binder(only_child_of_kind(handlers, NodeKind::Binder)?, tokens)?
            .name,
        handlers: project_resource_handler_clauses(source, handlers, tokens)?,
        span: node_span(source, node, tokens)?,
    })
}

#[cfg(test)]
mod tests {
    use crate::{
        lexer::lex,
        parser::{
            ExpectedForm, FoundToken, ParseReason, ResourceFailure, STRUCTURAL_DEPTH_LIMIT, parse,
        },
        source::SourceFile,
    };

    use super::*;

    fn parsed(text: &str) -> (SourceFile, ConcreteTree) {
        let source = SourceFile::new("shape.ash", format!("main : Unit\nmain () = {text}\n"))
            .expect("the shape fixture should fit");
        let lexed = lex(&source).expect("the shape fixture should lex");
        (source, parse(lexed))
    }

    fn structured_declarations(
        text: &str,
    ) -> (
        SourceFile,
        ConcreteTree,
        Vec<crate::syntax::MacroOutputNode>,
    ) {
        let source = SourceFile::new("handwritten.ash", text).unwrap();
        let tree = parse(lex(&source).unwrap());
        let (root, raw_tokens) = validated_root(&source, &tree).unwrap();
        let mut output = capture_contents(
            &source,
            root,
            &ProjectionTokens::source(raw_tokens),
            &std::collections::HashMap::new(),
        )
        .unwrap();
        assert!(matches!(
            output.pop(),
            Some(crate::syntax::MacroOutputNode::Token(
                TokenKind::EndOfFile,
                _,
                _
            ))
        ));
        (source, tree, output)
    }

    fn output_definition_name(definition: &SurfaceDefinition) -> &SurfaceName {
        match &definition.kind {
            SurfaceDefinitionKind::Equational(global) => &global.interface.name,
            SurfaceDefinitionKind::InlineOperational(global) => &global.header.name,
        }
    }

    #[test]
    fn declaration_template_admission_uses_category_correct_placeholders() {
        let contexts = crate::syntax::SyntaxContexts::new(&[], &[], &[]);
        for text in [
            "pub syntax declaration: (make_type) $name:ident => {\n    pub type $name = $name\n}\n",
            "pub syntax declaration: (make_value) $name:ident for $value:expr => {\n    pub $name : Unit -> Int\n    $name () = $value\n}\n",
            "pub syntax declaration: (empty) => {}\n",
        ] {
            let source = SourceFile::new("template.ash", text).unwrap();
            let tree = parse(lex(&source).unwrap());
            let module = project_module_retaining_templates(&source, &tree).unwrap();
            crate::syntax::validate_template_syntax(
                &module.syntax_declarations[0],
                &source,
                &contexts,
            )
            .expect(text);
        }

        let source = SourceFile::new(
            "unbound.ash",
            "pub syntax declaration: (bad) $name:ident => {\n    pub $missing : Unit -> Int\n    $missing () = 42\n}\n",
        )
        .unwrap();
        let tree = parse(lex(&source).unwrap());
        let module = project_module_retaining_templates(&source, &tree).unwrap();
        assert!(matches!(
            crate::syntax::validate_template_syntax(
                &module.syntax_declarations[0],
                &source,
                &contexts
            ),
            Err(crate::parser::MacroParseFailure::Invalid)
        ));
    }

    #[test]
    fn declaration_template_keeps_its_structured_contents_without_outer_braces() {
        use crate::syntax::MacroOutputNode;

        let source = SourceFile::new(
            "template.ash",
            "pub syntax declaration: (make) $name:ident => {\n    pub $name : Unit -> Int\n    $name () = 42\n}\n",
        )
        .unwrap();
        let tree = parse(lex(&source).unwrap());
        let module = project_module_retaining_templates(&source, &tree).unwrap();
        let declaration = &module.syntax_declarations[0];
        assert_eq!(declaration.category, SurfaceSyntaxCategory::Declaration);
        let contents = declaration.template_contents.as_ref().unwrap();
        let Some(MacroOutputNode::Token(TokenKind::Pub, _, origin)) = contents.first() else {
            panic!("the declaration contents start inside the template delimiters");
        };
        let origin = origin.primary();
        let range = origin.range();
        assert_eq!(origin.source(), source.id());
        assert_eq!(
            &source.text()[range.start() as usize..range.end() as usize],
            "pub"
        );
        assert!(
            matches!(contents.get(1), Some(MacroOutputNode::Splice(name))
            if name.text == "name" && name.span.source() == source.id())
        );
    }

    #[test]
    fn declaration_invocation_handoff_preserves_structured_contexts_and_origins() {
        use crate::syntax::{
            DiagnosticLocation, ExpansionFrame, MacroDelimiter, MacroOrigin, MacroOutputNode,
            SelectedSyntax, SyntaxContexts,
        };

        let owner = SourceFile::new(
            "owner.ash",
            "pub syntax declaration: (make) $name:ident from $value:expr => {}\n",
        )
        .unwrap();
        let owner_tree = parse(lex(&owner).unwrap());
        let owner_module = project_module_retaining_templates(&owner, &owner_tree).unwrap();
        let declaration = owner_module.syntax_declarations[0].clone();
        let caller = SourceFile::new("caller.ash", "invoke").unwrap();
        let invocation = caller.span(ByteRange::new(0, 6).unwrap()).unwrap();
        let written = SourceFile::new("earlier.ash", "make chosen from ()").unwrap();
        let span = |start, end| written.span(ByteRange::new(start, end).unwrap()).unwrap();
        let earlier_frame = std::sync::Arc::new(ExpansionFrame {
            invocation: span(0, 4),
            definition: declaration.span,
        });
        let current_frame = std::sync::Arc::new(ExpansionFrame {
            invocation,
            definition: declaration.span,
        });
        let mut diagnostic = DiagnosticLocation::new(MacroOrigin::Source(span(0, 4)));
        diagnostic.add_frame(&earlier_frame);
        let make_name = SurfaceName {
            text: "make".into(),
            span: span(0, 4),
            introduction: 1,
            introduced_at: Some(span(0, 4)),
            written: false,
            diagnostic: Some(Box::new(diagnostic)),
        };
        let captured = SurfaceName {
            text: "chosen".into(),
            span: span(5, 11),
            introduction: 7,
            introduced_at: Some(span(5, 11)),
            written: false,
            diagnostic: None,
        };
        let literal = SurfaceName {
            text: "from".into(),
            span: span(12, 16),
            introduction: 1,
            introduced_at: Some(span(0, 4)),
            written: false,
            diagnostic: None,
        };
        let value = SurfaceExpressionCapture {
            expression: SurfaceExpr {
                diagnostic: None,
                kind: SurfaceExprKind::Unit,
                span: span(17, 19),
            },
            contents: std::sync::Arc::from([MacroOutputNode::Group(
                MacroDelimiter::Parentheses,
                Vec::new(),
                MacroOrigin::Source(span(17, 19)),
            )]),
        };
        let selected = SelectedSyntax {
            name: "make".into(),
            declaration,
            owner: 42,
            import_span: span(0, 4),
        };
        let contexts = SyntaxContexts::new(&[], &[vec![selected.clone()]], &[Some(0)]);
        let output = vec![
            MacroOutputNode::Identifier(make_name, MacroOrigin::Source(span(0, 4))),
            MacroOutputNode::Identifier(captured.clone(), MacroOrigin::Source(span(5, 11))),
            MacroOutputNode::Identifier(literal, MacroOrigin::Source(span(12, 16))),
            MacroOutputNode::ForwardedExpression(value.clone(), MacroOrigin::Source(span(17, 19))),
        ];
        let parsed = super::super::parse_macro_tree(
            &caller,
            invocation,
            output,
            &contexts,
            &[],
            super::super::MacroOutputPosition::Declarations,
        )
        .unwrap();
        let root = parsed.tree.root().unwrap();
        let node = child_nodes(root)
            .find(|node| node.kind == NodeKind::DeclarationSyntaxInvocation)
            .unwrap();
        let matched = project_macro_declaration_invocation(
            &caller,
            invocation,
            None,
            &parsed,
            node,
            &contexts,
            Some(&current_frame),
        )
        .unwrap();
        assert_eq!(matched.name.introduction, 1);
        assert_eq!(matched.selection.owner, 42);
        assert_eq!(matched.selection.import_span, selected.import_span);
        assert_eq!(matched.span, invocation);
        let frames = &matched.name.diagnostic.as_ref().unwrap().frames;
        assert!(
            frames
                .iter()
                .any(|frame| std::sync::Arc::ptr_eq(frame, &earlier_frame))
        );
        assert!(
            frames
                .iter()
                .any(|frame| std::sync::Arc::ptr_eq(frame, &current_frame))
        );
        let [
            SurfaceSyntaxCapture::Identifier(name),
            SurfaceSyntaxCapture::Expression(expression),
        ] = matched.captures.as_slice()
        else {
            panic!("the selected matcher retains both captured categories");
        };
        assert_eq!(name.name.introduction, 7);
        assert_eq!(name.name.span, captured.span);
        assert_eq!(name.origin, MacroOrigin::Source(span(5, 11)));
        assert!(std::sync::Arc::ptr_eq(
            &expression.contents,
            &value.contents
        ));
        assert_eq!(expression.expression.span, value.expression.span);
    }

    #[test]
    fn structured_declaration_output_parses_i01_and_i07_controls() {
        for text in [
            include_str!("../../docs/design/macros/fixtures/declarations/control_01.ash"),
            include_str!("../../docs/design/macros/fixtures/declarations/control_07.ash"),
        ] {
            let (source, tree, output) = structured_declarations(text);
            let expected = project_module(&source, &tree).unwrap();
            let caller = SourceFile::new("invocation.ash", "invoke").unwrap();
            let invocation = caller.span(ByteRange::new(0, 6).unwrap()).unwrap();
            let contexts = crate::syntax::SyntaxContexts::new(&[], &[], &[]);
            let actual = super::super::parse_macro_declarations(
                &caller, invocation, None, output, &contexts, None,
            )
            .expect("complete structured declarations project");
            assert!(actual.imports.is_empty() && actual.syntax_declarations.is_empty());
            assert_eq!(actual.declaration_order, expected.declaration_order);
            assert_eq!(
                actual.type_declarations.len(),
                expected.type_declarations.len()
            );
            for (actual, expected) in actual
                .type_declarations
                .iter()
                .zip(&expected.type_declarations)
            {
                assert_eq!(actual.name, expected.name);
                assert_eq!(actual.name.span.source(), source.id());
                assert_eq!(actual.span, invocation);
            }
            assert_eq!(actual.definitions.len(), expected.definitions.len());
            for (actual, expected) in actual.definitions.iter().zip(&expected.definitions) {
                assert_eq!(
                    output_definition_name(actual),
                    output_definition_name(expected)
                );
                assert_eq!(output_definition_name(actual).span.source(), source.id());
                assert_eq!(actual.span, invocation);
            }
            if let [nominal] = actual.type_declarations.as_slice() {
                assert!(nominal.visibility == SurfaceTypeVisibility::PublicTransparent);
                assert_eq!(nominal.constructors[0].name.text, "Red");
                assert!(matches!(
                    nominal.constructors[0].fields[0].kind,
                    SurfaceTypeKind::Int
                ));
            } else {
                let SurfaceDefinitionKind::Equational(identity) = &actual.definitions[0].kind
                else {
                    panic!("expected the equational identity");
                };
                let SurfaceTypeKind::Function(annotation) = &identity.interface.annotation.kind
                else {
                    panic!("expected the identity function type");
                };
                assert!(matches!(annotation.domain.kind, SurfaceTypeKind::Int));
                assert!(matches!(annotation.codomain.kind, SurfaceTypeKind::Int));
                let SurfaceDefinitionKind::InlineOperational(inline) = &actual.definitions[1].kind
                else {
                    panic!("expected the inline global");
                };
                assert!(matches!(
                    inline.header.result_type.kind,
                    SurfaceTypeKind::Int
                ));
            }
        }
    }

    #[test]
    fn structured_declaration_output_preserves_other_ordinary_declaration_forms() {
        use crate::syntax::{MacroOutputNode, SyntaxContexts};

        let caller = SourceFile::new("invocation.ash", "invoke").unwrap();
        let invocation = caller.span(ByteRange::new(0, 6).unwrap()).unwrap();
        let contexts = SyntaxContexts::new(&[], &[], &[]);
        for text in [
            include_str!("../../docs/design/macros/fixtures/declarations/control_02.ash"),
            include_str!("../../docs/design/macros/fixtures/declarations/control_03.ash"),
            include_str!("../../docs/design/macros/fixtures/declarations/control_04.ash"),
            include_str!("../../docs/design/macros/fixtures/declarations/control_05.ash"),
            include_str!("../../docs/design/macros/fixtures/declarations/control_06.ash"),
        ] {
            let (source, tree, mut output) = structured_declarations(text);
            let expected = project_module(&source, &tree).unwrap();
            if !expected.imports.is_empty() {
                let line_end = output
                    .iter()
                    .position(|node| {
                        matches!(node, MacroOutputNode::Token(TokenKind::LineEnd, _, _))
                    })
                    .unwrap();
                output.drain(..=line_end);
            }
            let actual = super::super::parse_macro_declarations(
                &caller, invocation, None, output, &contexts, None,
            )
            .expect("ordinary declarations project without their source imports");
            assert_eq!(actual.declaration_order, expected.declaration_order);
            for (actual, expected) in actual
                .type_declarations
                .iter()
                .zip(&expected.type_declarations)
            {
                assert_eq!(actual.name, expected.name);
            }
            for (actual, expected) in actual.interfaces.iter().zip(&expected.interfaces) {
                assert_eq!(actual.name, expected.name);
            }
            for (actual, expected) in actual.effects.iter().zip(&expected.effects) {
                assert_eq!(actual.name, expected.name);
            }
            for (actual, expected) in actual
                .foreign_libraries
                .iter()
                .zip(&expected.foreign_libraries)
            {
                assert_eq!(actual.name, expected.name);
                let (
                    crate::surface::SurfaceForeignMember::Symbol(actual),
                    crate::surface::SurfaceForeignMember::Symbol(expected),
                ) = (&actual.members[1], &expected.members[1])
                else {
                    panic!("expected the fixture's foreign symbol");
                };
                assert_eq!(actual.name, expected.name);
            }
        }
    }

    #[test]
    fn structured_declaration_output_preserves_expression_fragments_and_contexts() {
        use crate::syntax::{MacroOrigin, MacroOutputNode, SyntaxContexts};

        let (source, _, output) = structured_declarations(include_str!(
            "../../docs/design/macros/fixtures/declarations/control_07.ash"
        ));
        let (captured_source, captured_tree) = parsed("40 + 2");
        let captured = project_module(&captured_source, &captured_tree).unwrap();
        let SurfaceDefinitionKind::Equational(captured) = &captured.definitions[0].kind else {
            panic!("expected a captured expression");
        };
        let expression = captured.equations[0].body.clone();
        let capture = SurfaceExpressionCapture {
            expression: expression.clone(),
            contents: std::sync::Arc::from([]),
        };
        let caller = SourceFile::new("invocation.ash", "invoke").unwrap();
        let invocation = caller.span(ByteRange::new(0, 6).unwrap()).unwrap();
        let contexts = SyntaxContexts::new(&[], &[], &[]);
        for forwarded in [false, true] {
            let mut output = output.clone();
            let binder = output
                .iter_mut()
                .find_map(|node| match node {
                    MacroOutputNode::Identifier(name, _) if name.text == "id" => Some(name),
                    _ => None,
                })
                .unwrap();
            let original_span = binder.span;
            binder.introduction = 3;
            binder.introduced_at = Some(invocation);
            binder.written = false;
            let index = output
                .iter()
                .rposition(|node| {
                    matches!(
                        node, MacroOutputNode::Identifier(name, _) if name.text == "value"
                    )
                })
                .unwrap();
            output[index] = if forwarded {
                MacroOutputNode::ForwardedExpression(capture.clone(), expression.span.into())
            } else {
                MacroOutputNode::Expression(capture.clone(), expression.span.into())
            };
            let actual = super::super::parse_macro_declarations(
                &caller, invocation, None, output, &contexts, None,
            )
            .expect("structured declarations retain protected expressions");
            let SurfaceDefinitionKind::Equational(global) = &actual.definitions[0].kind else {
                panic!("expected the first equation");
            };
            assert_eq!(global.equations[0].body, expression);
            let name = &global.interface.name;
            assert_eq!(name.span, original_span);
            assert_eq!(name.span.source(), source.id());
            assert_eq!(name.introduction, 3);
            assert_eq!(name.introduced_at, Some(invocation));
            assert!(!name.written);
            assert!(
                matches!(name.diagnostic.as_deref().map(|location| &location.primary),
                Some(MacroOrigin::Source(span)) if *span == original_span)
            );
        }
        let mut inline_output = output;
        let children = inline_output
            .iter_mut()
            .find_map(|node| match node {
                MacroOutputNode::Group(crate::syntax::MacroDelimiter::Braces, children, _) => {
                    Some(children)
                }
                _ => None,
            })
            .expect("the inline global has a body group");
        let result = children
            .iter()
            .position(|node| {
                matches!(
                    node, MacroOutputNode::Identifier(name, _) if name.text == "value"
                )
            })
            .unwrap();
        children[result] = MacroOutputNode::Expression(capture, expression.span.into());
        let actual = super::super::parse_macro_declarations(
            &caller,
            invocation,
            None,
            inline_output,
            &contexts,
            None,
        )
        .expect("inline declarations retain nested protected expressions");
        let SurfaceDefinitionKind::InlineOperational(inline) = &actual.definitions[1].kind else {
            panic!("expected the inline global");
        };
        assert_eq!(*inline.body.result, expression);
    }

    #[test]
    fn structured_declaration_names_retain_the_expansion_frame() {
        let (source, _, output) = structured_declarations(include_str!(
            "../../docs/design/macros/fixtures/declarations/control_01.ash"
        ));
        let caller = SourceFile::new("invocation.ash", "invoke").unwrap();
        let invocation = caller.span(ByteRange::new(0, 6).unwrap()).unwrap();
        let definition = source.span(ByteRange::new(0, 26).unwrap()).unwrap();
        let frame = std::sync::Arc::new(crate::syntax::ExpansionFrame {
            invocation,
            definition,
        });
        let contexts = crate::syntax::SyntaxContexts::new(&[], &[], &[]);
        let actual = super::super::parse_macro_declarations(
            &caller,
            invocation,
            None,
            output,
            &contexts,
            Some(&frame),
        )
        .unwrap();
        let name = &actual.type_declarations[0].name;
        let location = name.diagnostic.as_ref().expect("name retains an origin");
        assert!(
            location
                .frames
                .iter()
                .any(|found| std::sync::Arc::ptr_eq(found, &frame))
        );
    }

    #[test]
    fn structured_declaration_names_preserve_prior_frames_and_related_causes() {
        use crate::syntax::{
            DiagnosticLocation, ExpansionFrame, MacroOrigin, MacroOutputNode, SyntaxContexts,
        };

        let text = include_str!("../../docs/design/macros/fixtures/declarations/control_01.ash");
        let (definition_source, _, mut first_output) = structured_declarations(text);
        let first_caller = SourceFile::new("first-invocation.ash", "first").unwrap();
        let first_span = first_caller.span(ByteRange::new(0, 5).unwrap()).unwrap();
        let definition = definition_source
            .span(ByteRange::new(0, 26).unwrap())
            .unwrap();
        let earlier_frame = std::sync::Arc::new(ExpansionFrame {
            invocation: first_span,
            definition,
        });
        let contexts = SyntaxContexts::new(&[], &[], &[]);
        let first_name = first_output
            .iter_mut()
            .find_map(|node| match node {
                MacroOutputNode::Identifier(name, _) if name.text == "Color" => Some(name),
                _ => None,
            })
            .unwrap();
        first_name.introduction = 4;
        first_name.introduced_at = Some(first_span);
        first_name.written = false;
        let first = super::super::parse_macro_declarations(
            &first_caller,
            first_span,
            None,
            first_output,
            &contexts,
            Some(&earlier_frame),
        )
        .unwrap();
        let mut forwarded = first.type_declarations[0].name.clone();
        let earlier = forwarded
            .diagnostic
            .as_mut()
            .expect("the earlier parser retained an origin");
        assert!(
            earlier
                .frames
                .iter()
                .any(|frame| std::sync::Arc::ptr_eq(frame, &earlier_frame))
        );
        let related_source = SourceFile::new("construction.ash", "cause").unwrap();
        let related_span = related_source.span(ByteRange::new(0, 5).unwrap()).unwrap();
        let related = MacroOrigin::Source(related_span);
        earlier.add_cause(&DiagnosticLocation::new(related.clone()));
        earlier.token_cause = true;
        earlier.captured_expression = true;
        let earlier_primary = earlier.primary.clone();

        let (_, _, output) = structured_declarations(text);
        let current_caller = SourceFile::new("current-invocation.ash", "current").unwrap();
        let current_span = current_caller.span(ByteRange::new(0, 7).unwrap()).unwrap();
        let current_frame = std::sync::Arc::new(ExpansionFrame {
            invocation: current_span,
            definition,
        });
        for (frame, origin) in [
            (Some(&current_frame), MacroOrigin::Source(current_span)),
            (None, MacroOrigin::Source(current_span)),
            (Some(&earlier_frame), earlier_primary.clone()),
        ] {
            let mut output = output.clone();
            let node = output
                .iter_mut()
                .find(|node| {
                    matches!(
                        node, MacroOutputNode::Identifier(name, _) if name.text == "Color"
                    )
                })
                .unwrap();
            *node = MacroOutputNode::Identifier(forwarded.clone(), origin.clone());
            let projected = super::super::parse_macro_declarations(
                &current_caller,
                current_span,
                None,
                output,
                &contexts,
                frame,
            )
            .unwrap();
            let name = &projected.type_declarations[0].name;
            assert_eq!(name.text, "Color");
            assert_eq!(name.span, forwarded.span);
            assert_eq!(name.introduction, 4);
            assert_eq!(name.introduced_at, Some(first_span));
            assert!(!name.written);
            let location = name
                .diagnostic
                .as_ref()
                .expect("the forwarded name retains diagnostics");
            assert!(
                location
                    .frames
                    .iter()
                    .any(|frame| std::sync::Arc::ptr_eq(frame, &earlier_frame)),
                "earlier frame lost"
            );
            if let Some(frame) = frame {
                assert!(
                    location
                        .frames
                        .iter()
                        .any(|found| std::sync::Arc::ptr_eq(found, frame)),
                    "current frame lost"
                );
            }
            assert_eq!(
                location.frames.len(),
                if frame == Some(&current_frame) { 2 } else { 1 }
            );
            if origin != earlier_primary {
                assert!(
                    location.related.contains(&earlier_primary),
                    "earlier primary origin lost"
                );
            } else {
                assert!(
                    !location.related.contains(&earlier_primary),
                    "identical primary was duplicated"
                );
            }
            assert!(
                location.related.contains(&related),
                "related construction cause lost"
            );
            assert_eq!(location.primary, origin);
            assert!(location.token_cause && location.captured_expression);
        }
    }

    #[test]
    fn structured_impl_output_accepts_end_after_its_final_group() {
        use crate::syntax::{MacroDelimiter, MacroOutputNode, SyntaxContexts};

        let (_, _, output) = structured_declarations(include_str!(
            "../../docs/design/macros/fixtures/declarations/control_04.ash"
        ));
        let start = output
            .iter()
            .position(|node| matches!(node, MacroOutputNode::Token(TokenKind::Impl, _, _)))
            .unwrap();
        let end = start
            + output[start..]
                .iter()
                .position(|node| matches!(node, MacroOutputNode::Token(TokenKind::LineEnd, _, _)))
                .unwrap();
        let fragment = output[start..end].to_vec();
        assert!(matches!(
            fragment.last(),
            Some(MacroOutputNode::Group(MacroDelimiter::Braces, _, _))
        ));
        let caller = SourceFile::new("invocation.ash", "invoke").unwrap();
        let invocation = caller.span(ByteRange::new(0, 6).unwrap()).unwrap();
        let contexts = SyntaxContexts::new(&[], &[], &[]);
        let actual = super::super::parse_macro_declarations(
            &caller, invocation, None, fragment, &contexts, None,
        )
        .expect("a complete final declaration does not need a trailing node");
        assert_eq!(
            actual.declaration_order,
            [SurfaceDeclarationIndex::Implementation(0)]
        );
        assert_eq!(actual.implementations.len(), 1);
        for text in [
            include_str!("../../docs/design/macros/fixtures/declarations/control_01.ash"),
            include_str!("../../docs/design/macros/fixtures/declarations/control_07.ash"),
        ] {
            let (_, _, mut output) = structured_declarations(text);
            assert!(matches!(
                output.pop(),
                Some(MacroOutputNode::Token(TokenKind::LineEnd, _, _))
            ));
            super::super::parse_macro_declarations(
                &caller, invocation, None, output, &contexts, None,
            )
            .expect("the final logical boundary also works after multiple declarations");
        }
    }

    #[test]
    fn structured_output_still_rejects_missing_internal_boundaries_and_incomplete_types() {
        use crate::syntax::{MacroOutputNode, SyntaxContexts};

        let caller = SourceFile::new("invocation.ash", "invoke").unwrap();
        let invocation = caller.span(ByteRange::new(0, 6).unwrap()).unwrap();
        let contexts = SyntaxContexts::new(&[], &[], &[]);
        let (_, _, mut missing_separator) = structured_declarations(include_str!(
            "../../docs/design/macros/fixtures/declarations/control_01.ash"
        ));
        let first_end = missing_separator
            .iter()
            .position(|node| matches!(node, MacroOutputNode::Token(TokenKind::LineEnd, _, _)))
            .unwrap();
        missing_separator.remove(first_end);
        let (_, _, mut incomplete) = structured_declarations(include_str!(
            "../../docs/design/macros/fixtures/declarations/control_07.ash"
        ));
        let arrow = incomplete
            .iter()
            .position(|node| matches!(node, MacroOutputNode::Token(TokenKind::Arrow, _, _)))
            .unwrap();
        incomplete.remove(arrow + 1);
        assert!(matches!(
            incomplete.pop(),
            Some(MacroOutputNode::Token(TokenKind::LineEnd, _, _))
        ));
        for output in [missing_separator, incomplete] {
            let failure = super::super::parse_macro_declarations(
                &caller, invocation, None, output, &contexts, None,
            )
            .unwrap_err();
            assert!(
                matches!(failure, super::super::MacroParseFailure::Syntax { diagnostics, .. }
                if !diagnostics.is_empty())
            );
        }
    }

    #[test]
    fn structured_declaration_output_rejects_incomplete_i01_and_i07_forms() {
        use crate::syntax::{MacroOutputNode, SyntaxContexts};

        let caller = SourceFile::new("invocation.ash", "invoke").unwrap();
        let invocation = caller.span(ByteRange::new(0, 6).unwrap()).unwrap();
        let contexts = SyntaxContexts::new(&[], &[], &[]);
        let (_, _, mut i01) = structured_declarations(include_str!(
            "../../docs/design/macros/fixtures/declarations/control_01.ash"
        ));
        let constructor = i01
            .iter()
            .position(|node| {
                matches!(
                    node, MacroOutputNode::Identifier(name, _) if name.text == "Red"
                )
            })
            .unwrap();
        i01.remove(constructor);
        let (_, _, mut i07) = structured_declarations(include_str!(
            "../../docs/design/macros/fixtures/declarations/control_07.ash"
        ));
        let arrow = i07
            .iter()
            .position(|node| matches!(node, MacroOutputNode::Token(TokenKind::Arrow, _, _)))
            .unwrap();
        assert!(matches!(
            i07[arrow + 1],
            MacroOutputNode::Token(TokenKind::IntType, _, _)
        ));
        i07.remove(arrow + 1);
        for output in [i01, i07] {
            let failure = super::super::parse_macro_declarations(
                &caller, invocation, None, output, &contexts, None,
            )
            .unwrap_err();
            assert!(
                matches!(failure, super::super::MacroParseFailure::Syntax { diagnostics, .. }
                if !diagnostics.is_empty())
            );
        }
    }

    #[test]
    fn structured_declaration_output_rejects_forbidden_and_trailing_forms() {
        use crate::syntax::{MacroOutputNode, SyntaxContexts};

        let caller = SourceFile::new("invocation.ash", "invoke").unwrap();
        let invocation = caller.span(ByteRange::new(0, 6).unwrap()).unwrap();
        let contexts = SyntaxContexts::new(&[], &[], &[]);
        for text in [
            "import forms as Forms\n",
            "pub syntax declaration: (generated) => {}\n",
        ] {
            let (_, _, output) = structured_declarations(text);
            assert!(
                super::super::parse_macro_declarations(
                    &caller, invocation, None, output, &contexts, None,
                )
                .is_err(),
                "accepted {text:?}"
            );
        }
        let (_, _, mut output) = structured_declarations(include_str!(
            "../../docs/design/macros/fixtures/declarations/control_01.ash"
        ));
        output.push(MacroOutputNode::Token(
            TokenKind::Semicolon,
            ";".into(),
            invocation.into(),
        ));
        assert!(
            super::super::parse_macro_declarations(
                &caller, invocation, None, output, &contexts, None,
            )
            .is_err()
        );
        let empty = super::super::parse_macro_declarations(
            &caller,
            invocation,
            None,
            Vec::new(),
            &contexts,
            None,
        )
        .expect("empty declaration output is accepted");
        assert!(empty.declaration_order.is_empty());
    }

    #[test]
    fn structured_declaration_projection_refuses_recovery_even_without_diagnostics() {
        let source = SourceFile::new("recovery.ash", "pub type Color =\n").unwrap();
        let mut tree = parse(lex(&source).unwrap());
        assert!(!tree.parse_diagnostics().is_empty());
        tree.parse_diagnostics.clear();
        let invocation = source.span(ByteRange::new(0, 3).unwrap()).unwrap();
        assert_eq!(
            project_macro_declarations(
                &source,
                invocation,
                None,
                &tree,
                &std::collections::HashMap::new(),
                &std::collections::HashSet::new(),
                None,
            ),
            Err(ProjectionError::RecoveryNodesPresent),
        );
    }

    #[test]
    fn declaration_projection_preserves_protected_expression_fragments() {
        let (captured_source, captured_tree) = parsed("40 + 2");
        let captured_module = project_module(&captured_source, &captured_tree).unwrap();
        let SurfaceDefinitionKind::Equational(captured) = &captured_module.definitions[0].kind
        else {
            panic!("expected the captured expression's equation");
        };
        let expression = captured.equations[0].body.clone();
        let capture = SurfaceExpressionCapture {
            expression: expression.clone(),
            contents: std::sync::Arc::from([]),
        };

        let (source, tree) = parsed("placeholder");
        let (root, raw_tokens) = validated_root(&source, &tree).unwrap();
        let index = raw_tokens
            .iter()
            .position(
                |token| matches!(&token.kind, TokenKind::Identifier(name) if name == "placeholder"),
            )
            .unwrap();
        let originals = std::collections::HashMap::from([(
            index,
            crate::syntax::MacroOutputNode::Expression(capture, expression.span.into()),
        )]);
        let tokens = ProjectionTokens {
            tokens: raw_tokens,
            originals: Some(&originals),
            occurrence: Some(source.span(ByteRange::new(0, 4).unwrap()).unwrap()),
            construction: None,
            construction_extents: false,
            admission_identifiers: None,
            frame: None,
            name_frame: None,
            preserve_name_diagnostic: false,
        };
        let projected = project_surface_module(&source, root, &tokens).unwrap();
        let SurfaceDefinitionKind::Equational(global) = &projected.definitions[0].kind else {
            panic!("expected the projected equation");
        };
        assert_eq!(global.equations[0].body, expression);
    }

    #[test]
    fn generated_construction_extents_preserve_occurrence_and_literal_proof() {
        use crate::syntax::{MacroOutputNode, SyntaxContexts};

        fn introduce(nodes: &mut [MacroOutputNode], invocation: Span) {
            for node in nodes {
                match node {
                    MacroOutputNode::Identifier(name, _) => {
                        name.introduction = 3;
                        name.introduced_at = Some(invocation);
                    }
                    MacroOutputNode::Group(_, children, _) => introduce(children, invocation),
                    _ => {}
                }
            }
        }

        fn capture_name(nodes: &mut [MacroOutputNode]) -> bool {
            for node in nodes {
                match node {
                    MacroOutputNode::Identifier(name, _) if name.text == "Token" => {
                        name.introduction = 2;
                        return true;
                    }
                    MacroOutputNode::Group(_, children, _) => {
                        if capture_name(children) {
                            return true;
                        }
                    }
                    _ => {}
                }
            }
            false
        }

        let owner = SourceFile::new(
            "owner.ash",
            "pub syntax make $x:expr => {\nnewtype Token = Token(Int)\n42\n}\n",
        )
        .unwrap();
        let tree = parse(lex(&owner).unwrap());
        let module = project_module(&owner, &tree).unwrap();
        let declaration = &module.syntax_declarations[0];
        let caller = SourceFile::new("caller.ash", "invoke").unwrap();
        let invocation = caller.span(ByteRange::new(0, 6).unwrap()).unwrap();
        let mut contents = declaration.template_contents.as_ref().unwrap().to_vec();
        introduce(&mut contents, invocation);
        let contexts = SyntaxContexts::new(&[], &[], &[]);
        let parse = |construction, contents| {
            crate::parser::parse_macro_expression(
                &caller,
                invocation,
                construction,
                contents,
                &contexts,
                None,
            )
        };

        let literal = parse(Some((declaration.span, 3)), contents.clone())
            .expect("literal construction keeps definition extents");
        let SurfaceExprKind::Block(block) = &literal.kind else {
            panic!("the output is a block");
        };
        let [SurfaceLocalDeclaration::Newtype(nominal)] = block.declarations.as_slice() else {
            panic!("the block has one newtype");
        };
        assert_eq!(nominal.span.source(), owner.id());
        assert_eq!(nominal.name.introduction, 3);
        let procedural = parse(None, contents.clone()).expect("procedural construction projects");
        let SurfaceExprKind::Block(block) = &procedural.kind else {
            panic!("the output is a block");
        };
        let [SurfaceLocalDeclaration::Newtype(nominal)] = block.declarations.as_slice() else {
            panic!("the block has one newtype");
        };
        assert_eq!(nominal.span, invocation);
        assert_eq!(nominal.constructors[0].span, invocation);
        assert_eq!(nominal.name.introduction, 3);
        assert_eq!(nominal.constructors[0].fields[0].span, invocation);
        assert_eq!(nominal.name.span.source(), owner.id());
        assert!(capture_name(&mut contents));
        let captured = parse(Some((declaration.span, 3)), contents)
            .expect("a captured name uses the occurrence rather than literal construction extents");
        let SurfaceExprKind::Block(block) = &captured.kind else {
            panic!("the output is a block");
        };
        let [SurfaceLocalDeclaration::Newtype(nominal)] = block.declarations.as_slice() else {
            panic!("the block has one newtype");
        };
        assert_eq!(nominal.span, invocation);
        assert_eq!(nominal.constructors[0].span, invocation);
        assert_eq!(nominal.name.introduction, 2);
    }

    #[test]
    fn resource_instance_projection_rechecks_actual_argument_shape() {
        let source = SourceFile::new(
            "resource-instance-shape.ash",
            "main : Unit -> Int\nmain () = resource Lib.Test<R> state = 0 {\n    42\n}\n",
        )
        .expect("fixture source");
        let mut tree = parse(lex(&source).expect("fixture lexes"));
        assert!(
            tree.parse_diagnostics().is_empty(),
            "{:?}",
            tree.parse_diagnostics()
        );
        assert!(project_module(&source, &tree).is_ok());
        let instance = find_node_mut(
            tree.root.as_mut().expect("fixture root"),
            NodeKind::EffectInstance,
        )
        .expect("fixture instance");
        instance.children.retain(|child| {
            matches!(child,
            ConcreteElement::Node(name) if name.kind == NodeKind::QualifiedName)
        });
        assert_eq!(
            project_module(&source, &tree),
            Err(ProjectionError::MalformedTree(
                InternalReason::UnexpectedShape
            ))
        );
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

    const RESOURCE_FAMILY_SHAPE: &str = "pub resource Arena<R> {
input ArenaConfig
state Native.ArenaState<R>
result Provider.Scope<InitError, FinishError, T> for <T>
provider ArenaProvider<R>
effect ArenaOps<R>
interpret Native.Arena<R>
family<T> where Native.Layout<T> {
provider StorageProvider<R, T>
effect StorageOps<R, T>
interpret Native.Storage<R, T>
handlers state {
allocate operand => resume operand
load operand => resume operand
}
}
acquire config => perform Native.Arena<R>.acquire config
finish state => perform Native.Arena<R>.finish state
handlers state {
usage arena => resume arena
}
}
";

    #[test]
    fn family_projection_rejects_recovery_free_field_role_mutations() {
        for field_slot in [1, 2] {
            let source = SourceFile::new("family-shape.ash", RESOURCE_FAMILY_SHAPE)
                .expect("the family fixture should fit");
            let mut tree = parse(lex(&source).expect("the family fixture should lex"));
            assert!(tree.parse_diagnostics.is_empty());
            let keyword = {
                let root = tree.root.as_mut().expect("the fixture has a root");
                let family = find_node_mut(root, NodeKind::ResourceFamily)
                    .expect("the fixture has a family");
                let field = child_nodes(family)
                    .filter(|child| child.kind == NodeKind::ResourceField)
                    .nth(field_slot)
                    .expect("the family has the selected effect field");
                let ConcreteElement::Token(index) = &field.children[0] else {
                    panic!("the resource field starts with its keyword");
                };
                *index
            };
            tree.tokens[keyword].kind = if field_slot == 1 {
                TokenKind::Identifier("interpret".into())
            } else {
                TokenKind::Effect
            };
            let root = tree.root.as_ref().expect("the fixture still has its root");
            assert!(!has_recovery(root));
            assert_eq!(validate_tokens(&source, &tree.tokens), Ok(()));
            assert_eq!(
                validate_concrete_token_coverage(root, tree.tokens.len()),
                Ok(())
            );

            assert_eq!(
                project_module(&source, &tree),
                Err(ProjectionError::MalformedTree(
                    InternalReason::UnexpectedShape
                ))
            );
        }
    }

    #[test]
    fn family_projection_rejects_empty_handlers_after_expected_recovery_is_removed() {
        let text = RESOURCE_FAMILY_SHAPE.replace(
            "allocate operand => resume operand\nload operand => resume operand\n",
            "",
        );
        let source = SourceFile::new("empty-family-handlers.ash", text)
            .expect("the empty family fixture should fit");
        let mut tree = parse(lex(&source).expect("the empty family fixture should lex"));
        assert_eq!(tree.parse_diagnostics.len(), 1);
        assert_eq!(
            tree.parse_diagnostics[0].expected_form(),
            Some(ExpectedForm::Identifier)
        );
        assert_eq!(
            tree.parse_diagnostics[0].found_token(),
            Some(FoundToken::Spelling("}"))
        );
        let root = tree.root.as_mut().expect("the fixture has a root");
        let family =
            find_node_mut(root, NodeKind::ResourceFamily).expect("the fixture has a family");
        let handlers = family
            .children
            .iter_mut()
            .filter_map(|child| match child {
                ConcreteElement::Node(child) if child.kind == NodeKind::ResourceField => {
                    Some(child)
                }
                _ => None,
            })
            .nth(3)
            .expect("the family has a handlers field");
        let mut errors = 0;
        let mut missing = 0;
        // Remove only the empty-handler report and its zero-token markers.
        handlers.children.retain(|child| match child {
            ConcreteElement::Error(ParseReason::ExpectedForm) => {
                errors += 1;
                false
            }
            ConcreteElement::Missing {
                expected: ExpectedForm::Identifier,
                ..
            } => {
                missing += 1;
                false
            }
            _ => true,
        });
        assert_eq!((errors, missing), (1, 1));
        tree.parse_diagnostics.clear();
        let root = tree.root.as_ref().expect("the fixture still has its root");
        assert!(!has_recovery(root));
        assert_eq!(validate_tokens(&source, &tree.tokens), Ok(()));
        assert_eq!(
            validate_concrete_token_coverage(root, tree.tokens.len()),
            Ok(())
        );

        assert_eq!(
            project_module(&source, &tree),
            Err(ProjectionError::MalformedTree(
                InternalReason::UnexpectedShape
            ))
        );
    }

    #[test]
    fn family_projection_rejects_a_missing_handler_separator_with_complete_token_coverage() {
        let source = SourceFile::new("family-separator.ash", RESOURCE_FAMILY_SHAPE)
            .expect("the family fixture should fit");
        let mut tree = parse(lex(&source).expect("the family fixture should lex"));
        assert!(tree.parse_diagnostics.is_empty());
        let removed = {
            let tokens = &tree.tokens;
            let root = tree.root.as_mut().expect("the fixture has a root");
            let family =
                find_node_mut(root, NodeKind::ResourceFamily).expect("the fixture has a family");
            let handlers = family
                .children
                .iter_mut()
                .filter_map(|child| match child {
                    ConcreteElement::Node(child) if child.kind == NodeKind::ResourceField => {
                        Some(child)
                    }
                    _ => None,
                })
                .nth(3)
                .expect("the family has a handlers field");
            let separator = handlers
                .children
                .windows(3)
                .position(|children| {
                    matches!(&children[0], ConcreteElement::Node(node) if node.kind == NodeKind::HandlerClause)
                        && matches!(&children[1], ConcreteElement::Token(index) if tokens[*index].kind == TokenKind::LineEnd)
                        && matches!(&children[2], ConcreteElement::Node(node) if node.kind == NodeKind::HandlerClause)
                })
                .map(|index| index + 1)
                .expect("the family clauses have a separator");
            let ConcreteElement::Token(index) = handlers.children.remove(separator) else {
                panic!("the separator is a retained token");
            };
            index
        };
        // Remove both representations and reindex every retained token, so a
        // coverage failure cannot mask the missing logical-line shape.
        assert_eq!(tree.tokens.remove(removed).kind, TokenKind::LineEnd);
        let mut pending = vec![tree.root.as_mut().expect("the fixture still has its root")];
        while let Some(node) = pending.pop() {
            for child in &mut node.children {
                match child {
                    ConcreteElement::Node(child) => pending.push(child),
                    ConcreteElement::Token(index) => {
                        assert_ne!(*index, removed);
                        if *index > removed {
                            *index -= 1;
                        }
                    }
                    _ => {}
                }
            }
        }
        let root = tree.root.as_ref().expect("the fixture still has its root");
        assert!(!has_recovery(root));
        assert_eq!(validate_tokens(&source, &tree.tokens), Ok(()));
        assert_eq!(
            validate_concrete_token_coverage(root, tree.tokens.len()),
            Ok(())
        );

        assert_eq!(
            project_module(&source, &tree),
            Err(ProjectionError::MalformedTree(
                InternalReason::UnexpectedShape
            ))
        );
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
                        &ProjectionTokens::source(tree.tokens()),
                    )
                    .expect("surface projection should succeed");
                })
                .expect("the surface-projection thread should start")
                .join()
                .expect("surface projection should fit the small stack");
        });
    }
}
