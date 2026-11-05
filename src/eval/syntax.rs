//! Compiler syntax services for one checked Ash transformer invocation.

use std::{collections::HashMap, sync::Arc};

use super::{
    HeapCell, RuntimeFailure, Value, allocate_heap, borrowed_bytes, read_integer, resolve_location,
};
use crate::eval::value::{CompilerSyntaxHandle, CompilerSyntaxHandleKind};
use crate::{
    core::{NodeId, validate::ValidatedMacroEntry},
    lexer::TokenKind,
    resolved::BinderId,
    source::{SourceFile, Span},
    surface::{SurfaceExpressionCapture, SurfaceName, SurfaceSyntaxCapture},
    syntax::{MacroDelimiter, MacroOrigin, MacroOutputNode, SyntaxContexts, TransformerOutput},
    types::{ConstructorId, EffectId, OperationId, TypeWorkBudget},
};

#[derive(Debug)]
struct SyntaxToken {
    kind: TokenKind,
    spelling: Arc<str>,
}

#[derive(Debug)]
pub(super) struct SyntaxHost {
    pub(super) occurrence: NodeId,
    pub(super) binder: BinderId,
    pub(super) ops: EffectId,
    pub(super) started: bool,
    pub(super) steps_left: usize,
    invocation: Arc<()>,
    invocation_span: Span,
    source: SourceFile,
    definition_span: Span,
    caller: SurfaceName,
    introduction: usize,
    contexts: Arc<SyntaxContexts>,
    fresh_count: usize,
    captures: Vec<SurfaceSyntaxCapture>,
    expressions: Vec<SurfaceExpressionCapture>,
    identifiers: Vec<SurfaceName>,
    origins: Vec<MacroOrigin>,
    parse_failures: Vec<(
        Vec<crate::parser::ParseDiagnostic>,
        Option<crate::parser::ResourceFailure>,
    )>,
    tokens: Vec<SyntaxToken>,
    constructors: HashMap<String, ConstructorId>,
    operations: HashMap<OperationId, String>,
}

impl SyntaxHost {
    pub(super) fn new(
        entry: &ValidatedMacroEntry,
        captures: &[SurfaceSyntaxCapture],
        invocation_span: Span,
        source: &SourceFile,
        definition_span: Span,
        caller: &SurfaceName,
        introduction: usize,
        contexts: Arc<SyntaxContexts>,
    ) -> Result<Self, RuntimeFailure> {
        let registry = entry.program.registry();
        let mut constructors = HashMap::new();
        for constructor in registry
            .constructors()
            .iter()
            .filter(|constructor| constructor.id.owner().module() == entry.syntax_module)
        {
            if constructors
                .insert(constructor.spelling.clone(), constructor.id)
                .is_some()
            {
                return Err(RuntimeFailure::InvalidControlState);
            }
        }
        let effect = registry
            .effects()
            .iter()
            .find(|effect| effect.id == entry.ops)
            .ok_or(RuntimeFailure::InvalidControlState)?;
        let operations = effect
            .operations
            .iter()
            .map(|operation| (operation.id, operation.spelling.clone()))
            .collect();
        Ok(Self {
            occurrence: entry.occurrence,
            binder: entry.binder,
            ops: entry.ops,
            started: false,
            steps_left: 1_000_000,
            invocation: Arc::new(()),
            invocation_span,
            source: source.clone(),
            definition_span,
            caller: caller.clone(),
            introduction,
            contexts,
            fresh_count: 0,
            captures: captures.to_vec(),
            expressions: Vec::new(),
            identifiers: Vec::new(),
            origins: Vec::new(),
            parse_failures: Vec::new(),
            tokens: Vec::new(),
            constructors,
            operations,
        })
    }

    pub(super) fn input(&self) -> Value {
        self.handle(CompilerSyntaxHandleKind::Input)
    }

    pub(super) fn fresh_count(&self) -> usize {
        self.fresh_count
    }

    fn handle(&self, kind: CompilerSyntaxHandleKind) -> Value {
        Value::CompilerSyntaxHandle(CompilerSyntaxHandle {
            invocation: Arc::clone(&self.invocation),
            kind,
        })
    }

    fn admitted_handle(&self, value: &Value) -> Result<CompilerSyntaxHandleKind, RuntimeFailure> {
        let Value::CompilerSyntaxHandle(handle) = value else {
            return Err(RuntimeFailure::InvalidControlState);
        };
        if !Arc::ptr_eq(&handle.invocation, &self.invocation) {
            return Err(RuntimeFailure::InvalidControlState);
        }
        Ok(handle.kind)
    }

    fn issue_origin(&mut self, origin: MacroOrigin) -> Value {
        let index = self.origins.len();
        self.origins.push(origin);
        self.handle(CompilerSyntaxHandleKind::Origin(index))
    }

    fn admitted_origin(&self, value: &Value) -> Result<&MacroOrigin, RuntimeFailure> {
        let CompilerSyntaxHandleKind::Origin(index) = self.admitted_handle(value)? else {
            return Err(RuntimeFailure::InvalidControlState);
        };
        self.origins
            .get(index)
            .ok_or(RuntimeFailure::InvalidControlState)
    }

    fn read_origins<'a>(
        &self,
        mut origins: &'a Value,
        heap: &'a [HeapCell],
        mut remaining_spans: usize,
    ) -> Result<Vec<MacroOrigin>, RuntimeFailure> {
        let mut inputs = Vec::new();
        loop {
            let (tag, payload) = constructor_fields(origins, heap)?;
            if tag == self.constructor("NoOrigins")? && payload.is_none() {
                return Ok(inputs);
            }
            if tag != self.constructor("MoreOrigins")? {
                return Err(RuntimeFailure::InvalidControlState);
            }
            let (origin, rest) = pair(payload.ok_or(RuntimeFailure::InvalidControlState)?, heap)?;
            let origin = self.admitted_origin(origin)?;
            remaining_spans = remaining_spans
                .checked_sub(origin.span_count())
                .ok_or(RuntimeFailure::ResourceCapacity)?;
            inputs.push(origin.clone());
            origins = rest;
        }
    }

    fn constructor(&self, name: &str) -> Result<ConstructorId, RuntimeFailure> {
        self.constructors
            .get(name)
            .copied()
            .ok_or(RuntimeFailure::InvalidControlState)
    }

    fn construct(
        &self,
        heap: &mut Vec<HeapCell>,
        name: &str,
        payload: Option<Value>,
    ) -> Result<Value, RuntimeFailure> {
        let id = self.constructor(name)?;
        Ok(Value::Location(allocate_heap(
            heap,
            HeapCell::Constructor(id, payload),
        )?))
    }

    pub(super) fn request(
        &mut self,
        operation: OperationId,
        argument: Value,
        heap: &mut Vec<HeapCell>,
        work: &mut TypeWorkBudget,
    ) -> Result<Value, RuntimeFailure> {
        let operation = self
            .operations
            .get(&operation)
            .cloned()
            .ok_or(RuntimeFailure::InvalidControlState)?;
        match operation.as_str() {
            "invocation_origin" | "definition_origin" => {
                if !matches!(
                    self.admitted_handle(&argument)?,
                    CompilerSyntaxHandleKind::Input
                ) {
                    return Err(RuntimeFailure::InvalidControlState);
                }
                let origin = if operation == "invocation_origin" {
                    self.invocation_span
                } else {
                    self.definition_span
                };
                Ok(self.issue_origin(origin.into()))
            }
            "capture" => {
                let (input, index) = pair(&argument, heap)?;
                if !matches!(
                    self.admitted_handle(input)?,
                    CompilerSyntaxHandleKind::Input
                ) {
                    return Err(RuntimeFailure::InvalidControlState);
                }
                let index = read_integer(index, heap, work)?.to_usize();
                match index.and_then(|index| self.captures.get(index)).cloned() {
                    Some(SurfaceSyntaxCapture::Expression(expression)) => {
                        let index = self.expressions.len();
                        self.expressions.push(expression);
                        let fragment = self.handle(CompilerSyntaxHandleKind::Expression(index));
                        let capture = self.construct(heap, "ExpressionCapture", Some(fragment))?;
                        self.construct(heap, "Captured", Some(capture))
                    }
                    Some(SurfaceSyntaxCapture::Identifier(name)) => {
                        let origin = self.issue_origin(name.span.into());
                        let index = self.identifiers.len();
                        self.identifiers.push(name);
                        let identifier = self.handle(CompilerSyntaxHandleKind::Identifier(index));
                        let fields = vec![identifier, origin].into_boxed_slice();
                        let fields = Value::Location(allocate_heap(heap, HeapCell::Tuple(fields))?);
                        let capture = self.construct(heap, "IdentifierCapture", Some(fields))?;
                        self.construct(heap, "Captured", Some(capture))
                    }
                    None => self.construct(heap, "MissingCapture", None),
                }
            }
            "make_token" => {
                let (kind, spelling) = pair(&argument, heap)?;
                let (tag, payload) = constructor_fields(kind, heap)?;
                let (spelling, is_string) = borrowed_bytes(spelling, heap, work)?;
                let spelling = std::str::from_utf8(spelling)
                    .map_err(|_| RuntimeFailure::InvalidControlState)?;
                let token = if is_string && payload.is_none() {
                    token_from_spelling(spelling)?
                } else {
                    None
                };
                let Some(token) = token.filter(|token| {
                    token_kind_name(token)
                        .and_then(|name| self.constructors.get(name))
                        .is_some_and(|expected| *expected == tag)
                }) else {
                    return self.construct(heap, "InvalidToken", None);
                };
                let index = self.tokens.len();
                self.tokens.push(SyntaxToken {
                    kind: token,
                    spelling: Arc::from(spelling),
                });
                let token = self.handle(CompilerSyntaxHandleKind::Token(index));
                self.construct(heap, "MadeToken", Some(token))
            }
            "identifier_spelling" => {
                let CompilerSyntaxHandleKind::Identifier(index) =
                    self.admitted_handle(&argument)?
                else {
                    return Err(RuntimeFailure::InvalidControlState);
                };
                let name = self
                    .identifiers
                    .get(index)
                    .ok_or(RuntimeFailure::InvalidControlState)?;
                Ok(Value::String(Arc::from(name.text.as_str())))
            }
            "fresh_identifier" | "definition_identifier" | "caller_identifier" => {
                let (input, spelling, origin) = triple(&argument, heap)?;
                if !matches!(
                    self.admitted_handle(input)?,
                    CompilerSyntaxHandleKind::Input
                ) {
                    return Err(RuntimeFailure::InvalidControlState);
                }
                let origin = self.admitted_origin(origin)?.primary();
                let (spelling, is_string) = borrowed_bytes(spelling, heap, work)?;
                let spelling = std::str::from_utf8(spelling)
                    .map_err(|_| RuntimeFailure::InvalidControlState)?;
                if !is_string
                    || !matches!(
                        single_token(spelling)?,
                        Some(TokenKind::Identifier(_) | TokenKind::UpperIdentifier(_))
                    )
                {
                    return self.construct(heap, "InvalidIdentifier", None);
                }
                let (introduction, introduced_at) = match operation.as_str() {
                    "fresh_identifier" => {
                        self.fresh_count = self
                            .fresh_count
                            .checked_add(1)
                            .ok_or(RuntimeFailure::HeapCapacity)?;
                        (
                            self.introduction
                                .checked_add(self.fresh_count)
                                .ok_or(RuntimeFailure::HeapCapacity)?,
                            Some(self.invocation_span),
                        )
                    }
                    "definition_identifier" => (self.introduction, Some(self.invocation_span)),
                    _ => (self.caller.introduction, self.caller.introduced_at),
                };
                let index = self.identifiers.len();
                self.identifiers.push(SurfaceName {
                    text: spelling.to_owned(),
                    span: origin,
                    introduction,
                    introduced_at,
                });
                let identifier = self.handle(CompilerSyntaxHandleKind::Identifier(index));
                self.construct(heap, "MadeIdentifier", Some(identifier))
            }
            "combine_origins" => {
                let (input, origins) = pair(&argument, heap)?;
                if !matches!(
                    self.admitted_handle(input)?,
                    CompilerSyntaxHandleKind::Input
                ) {
                    return Err(RuntimeFailure::InvalidControlState);
                }
                // Reserve the invocation and definition frames added by this
                // combination before admitting its ordered inputs.
                let inputs =
                    self.read_origins(origins, heap, crate::syntax::MAX_ORIGIN_SPANS - 2)?;
                if inputs.is_empty() {
                    return self.construct(heap, "MissingOrigins", None);
                }
                let origin =
                    MacroOrigin::combined(inputs, self.invocation_span, self.definition_span)
                        .ok_or(RuntimeFailure::ResourceCapacity)?;
                let combined = self.issue_origin(origin);
                self.construct(heap, "Combined", Some(combined))
            }
            "parse_expression" => {
                let (input, syntax) = pair(&argument, heap)?;
                if !matches!(
                    self.admitted_handle(input)?,
                    CompilerSyntaxHandleKind::Input
                ) {
                    return Err(RuntimeFailure::InvalidControlState);
                }
                let output = self.transfer_syntax(syntax, heap, 0)?;
                let contents = output.clone().into();
                match crate::syntax::admit_transformer_output(
                    &self.source,
                    self.invocation_span,
                    output,
                    &self.contexts,
                ) {
                    Ok(expression) => {
                        let index = self.expressions.len();
                        self.expressions.push(SurfaceExpressionCapture {
                            expression,
                            contents,
                        });
                        let fragment = self.handle(CompilerSyntaxHandleKind::Expression(index));
                        self.construct(heap, "Parsed", Some(fragment))
                    }
                    Err(crate::parser::MacroParseFailure::Syntax {
                        diagnostics,
                        resource,
                    }) => {
                        let index = self.parse_failures.len();
                        self.parse_failures.push((diagnostics, resource));
                        let failure = self.handle(CompilerSyntaxHandleKind::ParseFailure(index));
                        self.construct(heap, "ParseRejected", Some(failure))
                    }
                    Err(crate::parser::MacroParseFailure::Invalid) => {
                        Err(RuntimeFailure::InvalidControlState)
                    }
                }
            }
            "expression_syntax" => {
                let CompilerSyntaxHandleKind::Expression(index) =
                    self.admitted_handle(&argument)?
                else {
                    return Err(RuntimeFailure::InvalidControlState);
                };
                let contents = Arc::clone(
                    &self
                        .expressions
                        .get(index)
                        .ok_or(RuntimeFailure::InvalidControlState)?
                        .contents,
                );
                self.syntax_value(&contents, heap, 0)
            }
            "token_kind" => {
                let CompilerSyntaxHandleKind::Token(index) = self.admitted_handle(&argument)?
                else {
                    return Err(RuntimeFailure::InvalidControlState);
                };
                let token = self
                    .tokens
                    .get(index)
                    .ok_or(RuntimeFailure::InvalidControlState)?;
                let name =
                    token_kind_name(&token.kind).ok_or(RuntimeFailure::InvalidControlState)?;
                self.construct(heap, name, None)
            }
            "token_spelling" => {
                let CompilerSyntaxHandleKind::Token(index) = self.admitted_handle(&argument)?
                else {
                    return Err(RuntimeFailure::InvalidControlState);
                };
                let token = self
                    .tokens
                    .get(index)
                    .ok_or(RuntimeFailure::InvalidControlState)?;
                Ok(Value::String(Arc::clone(&token.spelling)))
            }
            _ => Err(RuntimeFailure::InvalidControlState),
        }
    }

    pub(super) fn transfer(
        &self,
        result: &Value,
        heap: &[HeapCell],
        work: &mut TypeWorkBudget,
    ) -> Result<TransformerOutput, RuntimeFailure> {
        let (tag, syntax) = constructor_fields(result, heap)?;
        if tag == self.constructor("Expanded")? {
            return self
                .transfer_syntax(syntax.ok_or(RuntimeFailure::InvalidControlState)?, heap, 0)
                .map(TransformerOutput::Expanded);
        }
        if tag != self.constructor("Rejected")? {
            return Err(RuntimeFailure::InvalidControlState);
        }
        let (tag, fields) =
            constructor_fields(syntax.ok_or(RuntimeFailure::InvalidControlState)?, heap)?;
        if tag == self.constructor("SyntaxDiagnostic")? {
            let CompilerSyntaxHandleKind::ParseFailure(index) =
                self.admitted_handle(fields.ok_or(RuntimeFailure::InvalidControlState)?)?
            else {
                return Err(RuntimeFailure::InvalidControlState);
            };
            let (diagnostics, resource) = self
                .parse_failures
                .get(index)
                .ok_or(RuntimeFailure::InvalidControlState)?;
            return Ok(TransformerOutput::SyntaxRejected(
                crate::driver::SyntaxParseFailure {
                    diagnostics: diagnostics.clone(),
                    resource: *resource,
                    invocation: self.invocation_span,
                    definition: self.definition_span,
                },
            ));
        }
        if tag != self.constructor("MacroDiagnostic")? {
            return Err(RuntimeFailure::InvalidControlState);
        }
        let (message, primary, related) =
            triple(fields.ok_or(RuntimeFailure::InvalidControlState)?, heap)?;
        let (message, is_string) = borrowed_bytes(message, heap, work)?;
        if !is_string {
            return Err(RuntimeFailure::InvalidControlState);
        }
        let message = std::str::from_utf8(message)
            .map_err(|_| RuntimeFailure::InvalidControlState)?
            .to_owned();
        let primary = self.admitted_origin(primary)?.clone();
        // Rejection reports retain both the primary and every related cause,
        // plus the enclosing invocation and definition frames.
        let remaining = crate::syntax::MAX_ORIGIN_SPANS
            .checked_sub(primary.span_count())
            .and_then(|remaining| remaining.checked_sub(2))
            .ok_or(RuntimeFailure::ResourceCapacity)?;
        let related = self.read_origins(related, heap, remaining)?;
        Ok(TransformerOutput::Rejected(
            crate::driver::SyntaxExpansionFailure {
                message,
                primary,
                related,
                invocation: self.invocation_span,
                definition: self.definition_span,
            },
        ))
    }

    fn transfer_syntax(
        &self,
        syntax: &Value,
        heap: &[HeapCell],
        depth: usize,
    ) -> Result<Vec<MacroOutputNode>, RuntimeFailure> {
        if depth > crate::parser::STRUCTURAL_DEPTH_LIMIT {
            return Err(RuntimeFailure::ResourceCapacity);
        }
        let (tag, nodes) = constructor_fields(syntax, heap)?;
        if tag != self.constructor("Syntax")? {
            return Err(RuntimeFailure::InvalidControlState);
        }
        let mut nodes = nodes.ok_or(RuntimeFailure::InvalidControlState)?;
        let mut output = Vec::new();
        loop {
            if output.len() >= 65_536 {
                return Err(RuntimeFailure::HeapCapacity);
            }
            let (tag, payload) = constructor_fields(nodes, heap)?;
            if tag == self.constructor("NoNodes")? && payload.is_none() {
                return Ok(output);
            }
            if tag != self.constructor("MoreNodes")? {
                return Err(RuntimeFailure::InvalidControlState);
            }
            let (node, rest) = pair(payload.ok_or(RuntimeFailure::InvalidControlState)?, heap)?;
            let (tag, payload) = constructor_fields(node, heap)?;
            let payload = payload.ok_or(RuntimeFailure::InvalidControlState)?;
            if tag == self.constructor("GroupNode")? {
                let (delimiter, syntax, origin) = triple(payload, heap)?;
                let (delimiter, extra) = constructor_fields(delimiter, heap)?;
                if extra.is_some() {
                    return Err(RuntimeFailure::InvalidControlState);
                }
                let delimiter = if delimiter == self.constructor("Parentheses")? {
                    MacroDelimiter::Parentheses
                } else if delimiter == self.constructor("Braces")? {
                    MacroDelimiter::Braces
                } else {
                    return Err(RuntimeFailure::InvalidControlState);
                };
                let origin = self.admitted_origin(origin)?.clone();
                let children = self.transfer_syntax(syntax, heap, depth + 1)?;
                output.push(MacroOutputNode::Group(delimiter, children, origin));
            } else {
                let (value, origin) = pair(payload, heap)?;
                let origin = self.admitted_origin(origin)?.clone();
                if tag == self.constructor("ExpressionNode")? {
                    let CompilerSyntaxHandleKind::Expression(index) =
                        self.admitted_handle(value)?
                    else {
                        return Err(RuntimeFailure::InvalidControlState);
                    };
                    let expression = self
                        .expressions
                        .get(index)
                        .ok_or(RuntimeFailure::InvalidControlState)?;
                    output.push(MacroOutputNode::Expression(expression.clone(), origin));
                } else if tag == self.constructor("IdentifierNode")? {
                    let CompilerSyntaxHandleKind::Identifier(index) =
                        self.admitted_handle(value)?
                    else {
                        return Err(RuntimeFailure::InvalidControlState);
                    };
                    let name = self
                        .identifiers
                        .get(index)
                        .ok_or(RuntimeFailure::InvalidControlState)?;
                    output.push(MacroOutputNode::Identifier(name.clone(), origin));
                } else if tag == self.constructor("TokenNode")? {
                    let CompilerSyntaxHandleKind::Token(index) = self.admitted_handle(value)?
                    else {
                        return Err(RuntimeFailure::InvalidControlState);
                    };
                    let token = self
                        .tokens
                        .get(index)
                        .ok_or(RuntimeFailure::InvalidControlState)?;
                    output.push(MacroOutputNode::Token(
                        token.kind.clone(),
                        Arc::clone(&token.spelling),
                        origin,
                    ));
                } else {
                    return Err(RuntimeFailure::InvalidControlState);
                }
            }
            nodes = rest;
        }
    }

    fn syntax_value(
        &mut self,
        nodes: &[MacroOutputNode],
        heap: &mut Vec<HeapCell>,
        depth: usize,
    ) -> Result<Value, RuntimeFailure> {
        if depth > crate::parser::STRUCTURAL_DEPTH_LIMIT {
            return Err(RuntimeFailure::ResourceCapacity);
        }
        let mut rest = self.construct(heap, "NoNodes", None)?;
        for node in nodes.iter().rev() {
            let (constructor, fields) = match node {
                MacroOutputNode::Expression(expression, origin)
                | MacroOutputNode::ForwardedExpression(expression, origin) => {
                    let index = self.expressions.len();
                    self.expressions.push(expression.clone());
                    (
                        "ExpressionNode",
                        vec![
                            self.handle(CompilerSyntaxHandleKind::Expression(index)),
                            self.issue_origin(origin.clone()),
                        ],
                    )
                }
                MacroOutputNode::Identifier(name, origin) => {
                    let index = self.identifiers.len();
                    self.identifiers.push(name.clone());
                    (
                        "IdentifierNode",
                        vec![
                            self.handle(CompilerSyntaxHandleKind::Identifier(index)),
                            self.issue_origin(origin.clone()),
                        ],
                    )
                }
                MacroOutputNode::Token(kind, spelling, origin) => {
                    let index = self.tokens.len();
                    self.tokens.push(SyntaxToken {
                        kind: kind.clone(),
                        spelling: Arc::clone(spelling),
                    });
                    (
                        "TokenNode",
                        vec![
                            self.handle(CompilerSyntaxHandleKind::Token(index)),
                            self.issue_origin(origin.clone()),
                        ],
                    )
                }
                MacroOutputNode::Group(delimiter, children, origin) => {
                    let delimiter = match delimiter {
                        MacroDelimiter::Parentheses => "Parentheses",
                        MacroDelimiter::Braces => "Braces",
                    };
                    let delimiter = self.construct(heap, delimiter, None)?;
                    let children = self.syntax_value(children, heap, depth + 1)?;
                    (
                        "GroupNode",
                        vec![delimiter, children, self.issue_origin(origin.clone())],
                    )
                }
                MacroOutputNode::Splice(_) => return Err(RuntimeFailure::InvalidControlState),
            };
            let fields = Value::Location(allocate_heap(
                heap,
                HeapCell::Tuple(fields.into_boxed_slice()),
            )?);
            let node = self.construct(heap, constructor, Some(fields))?;
            let pair = Value::Location(allocate_heap(
                heap,
                HeapCell::Tuple(vec![node, rest].into_boxed_slice()),
            )?);
            rest = self.construct(heap, "MoreNodes", Some(pair))?;
        }
        self.construct(heap, "Syntax", Some(rest))
    }
}

// This vocabulary is shared with the canonical Ash TokenKind declaration.
// Identifiers and delimiters have separate structured representations.
fn token_kind_name(kind: &TokenKind) -> Option<&'static str> {
    Some(match kind {
        TokenKind::Wildcard => "Wildcard",
        TokenKind::Integer(_) => "IntegerLiteral",
        TokenKind::StringLiteral(_) => "StringLiteral",
        TokenKind::True => "True",
        TokenKind::False => "False",
        TokenKind::Fn => "Fn",
        TokenKind::Let => "Let",
        TokenKind::Rec => "Rec",
        TokenKind::And => "And",
        TokenKind::Type => "Type",
        TokenKind::Newtype => "Newtype",
        TokenKind::Effect => "Effect",
        TokenKind::Match => "Match",
        TokenKind::Perform => "Perform",
        TokenKind::Handle => "Handle",
        TokenKind::With => "With",
        TokenKind::Resume => "Resume",
        TokenKind::Resource => "Resource",
        TokenKind::Region => "Region",
        TokenKind::Using => "Using",
        TokenKind::Hook => "Hook",
        TokenKind::Register => "Register",
        TokenKind::Cleanup => "Cleanup",
        TokenKind::Discard => "Discard",
        TokenKind::Retain => "Retain",
        TokenKind::Import => "Import",
        TokenKind::As => "As",
        TokenKind::Pub => "Pub",
        TokenKind::Opaque => "Opaque",
        TokenKind::Interface => "Interface",
        TokenKind::Impl => "Impl",
        TokenKind::Where => "Where",
        TokenKind::IntType => "IntType",
        TokenKind::BytesType => "BytesType",
        TokenKind::StringType => "StringType",
        TokenKind::BoolType => "BoolType",
        TokenKind::UnitType => "UnitType",
        TokenKind::At => "At",
        TokenKind::Dot => "Dot",
        TokenKind::Colon => "Colon",
        TokenKind::Equal => "Equal",
        TokenKind::EqualEqual => "EqualEqual",
        TokenKind::Plus => "Plus",
        TokenKind::Star => "Star",
        TokenKind::Arrow => "Arrow",
        TokenKind::FatArrow => "FatArrow",
        TokenKind::Pipe => "Pipe",
        TokenKind::Bang => "Bang",
        TokenKind::Comma => "Comma",
        TokenKind::Less => "Less",
        TokenKind::Greater => "Greater",
        TokenKind::LineEnd => "LineEnd",
        TokenKind::Identifier(_)
        | TokenKind::UpperIdentifier(_)
        | TokenKind::LeftParen
        | TokenKind::RightParen
        | TokenKind::LeftBrace
        | TokenKind::RightBrace
        | TokenKind::Dollar
        | TokenKind::Semicolon
        | TokenKind::EndOfFile => return None,
    })
}

fn token_from_spelling(spelling: &str) -> Result<Option<TokenKind>, RuntimeFailure> {
    Ok(single_token(spelling)?.filter(|kind| token_kind_name(kind).is_some()))
}

fn single_token(spelling: &str) -> Result<Option<TokenKind>, RuntimeFailure> {
    if matches!(spelling, "\n" | "\r\n") {
        return Ok(Some(TokenKind::LineEnd));
    }
    let source = crate::source::SourceFile::new("<syntax-token>", spelling.to_owned())
        .map_err(|_| RuntimeFailure::HeapCapacity)?;
    let lexed = crate::lexer::lex(&source).map_err(|_| RuntimeFailure::InvalidControlState)?;
    if lexed.resource_failure().is_some() {
        return Err(RuntimeFailure::ResourceCapacity);
    }
    if !lexed.diagnostics.is_empty() {
        return Ok(None);
    }
    let [token, eof] = lexed.tokens.as_slice() else {
        return Ok(None);
    };
    if !matches!(eof.kind, TokenKind::EndOfFile)
        || token.span.range().start() != 0
        || usize::try_from(token.span.range().end()).ok() != Some(spelling.len())
    {
        return Ok(None);
    }
    Ok(Some(token.kind.clone()))
}

fn location(value: &Value, heap: &[HeapCell]) -> Result<usize, RuntimeFailure> {
    let location = match value {
        Value::Location(location) => *location,
        Value::Data(value) => value.root(),
        _ => return Err(RuntimeFailure::InvalidControlState),
    };
    resolve_location(heap, location)
}

fn constructor_fields<'a>(
    value: &'a Value,
    heap: &'a [HeapCell],
) -> Result<(ConstructorId, Option<&'a Value>), RuntimeFailure> {
    heap.get(location(value, heap)?)
        .and_then(HeapCell::constructor_fields)
        .ok_or(RuntimeFailure::InvalidControlState)
}

fn triple<'a>(
    value: &'a Value,
    heap: &'a [HeapCell],
) -> Result<(&'a Value, &'a Value, &'a Value), RuntimeFailure> {
    let [first, second, third] = heap
        .get(location(value, heap)?)
        .and_then(HeapCell::tuple_fields)
        .ok_or(RuntimeFailure::InvalidControlState)?
    else {
        return Err(RuntimeFailure::InvalidControlState);
    };
    Ok((first, second, third))
}

fn pair<'a>(
    value: &'a Value,
    heap: &'a [HeapCell],
) -> Result<(&'a Value, &'a Value), RuntimeFailure> {
    let [first, second] = heap
        .get(location(value, heap)?)
        .and_then(HeapCell::tuple_fields)
        .ok_or(RuntimeFailure::InvalidControlState)?
    else {
        return Err(RuntimeFailure::InvalidControlState);
    };
    Ok((first, second))
}

#[cfg(test)]
mod tests {
    use super::{token_from_spelling, token_kind_name};

    #[test]
    fn token_vocabulary_matches_canonical_declarations_and_lexer() {
        let cases = [
            ("Wildcard", "_"),
            ("IntegerLiteral", "42"),
            ("StringLiteral", r#""ash\n""#),
            ("True", "true"),
            ("False", "false"),
            ("Fn", "fn"),
            ("Let", "let"),
            ("Rec", "rec"),
            ("And", "and"),
            ("Type", "type"),
            ("Newtype", "newtype"),
            ("Effect", "effect"),
            ("Match", "match"),
            ("Perform", "perform"),
            ("Handle", "handle"),
            ("With", "with"),
            ("Resume", "resume"),
            ("Resource", "resource"),
            ("Region", "region"),
            ("Using", "using"),
            ("Hook", "hook"),
            ("Register", "register"),
            ("Cleanup", "cleanup"),
            ("Discard", "discard"),
            ("Retain", "retain"),
            ("Import", "import"),
            ("As", "as"),
            ("Pub", "pub"),
            ("Opaque", "opaque"),
            ("Interface", "interface"),
            ("Impl", "impl"),
            ("Where", "where"),
            ("IntType", "Int"),
            ("BytesType", "Bytes"),
            ("StringType", "String"),
            ("BoolType", "Bool"),
            ("UnitType", "Unit"),
            ("At", "@"),
            ("Dot", "."),
            ("Colon", ":"),
            ("Equal", "="),
            ("EqualEqual", "=="),
            ("Plus", "+"),
            ("Star", "*"),
            ("Arrow", "->"),
            ("FatArrow", "=>"),
            ("Pipe", "|"),
            ("Bang", "!"),
            ("Comma", ","),
            ("Less", "<"),
            ("Greater", ">"),
            ("LineEnd", "\n"),
        ];
        let source = crate::source::SourceFile::new(
            "@builtin.compiler.syntax",
            crate::module::compiler_syntax_builtin_source_text().to_owned(),
        )
        .unwrap();
        let tree = crate::parser::parse(crate::lexer::lex(&source).unwrap());
        let module = crate::parser::project_module(&source, &tree).unwrap();
        let declared = module
            .type_declarations
            .iter()
            .find(|declaration| declaration.name.text == "TokenKind")
            .unwrap()
            .constructors
            .iter()
            .map(|constructor| constructor.name.text.as_str())
            .collect::<Vec<_>>();
        assert_eq!(
            declared,
            cases.iter().map(|(name, _)| *name).collect::<Vec<_>>()
        );
        for (name, spelling) in cases {
            let token = token_from_spelling(spelling).unwrap().unwrap();
            assert_eq!(token_kind_name(&token), Some(name), "{spelling:?}");
        }
        assert_eq!(
            token_kind_name(&token_from_spelling("\r\n").unwrap().unwrap()),
            Some("LineEnd")
        );
        for spelling in [
            "", "name", "Name", "(", ")", "{", "}", "$", ";", "01", "-1", " +", "+ ",
        ] {
            assert!(
                token_from_spelling(spelling).unwrap().is_none(),
                "{spelling:?}"
            );
        }
    }
}
