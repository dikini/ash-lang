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
    source::SourceFile,
    surface::{
        SurfaceDeclarationCapture, SurfaceExpressionCapture, SurfaceName, SurfaceSyntaxCapture,
    },
    syntax::{
        ExpansionFrame, MacroDelimiter, MacroOrigin, MacroOutputNode, SyntaxContexts,
        TransformerOutput,
    },
    types::{ConstructorId, EffectId, OperationId, TypeWorkBudget},
};

#[derive(Debug)]
struct SyntaxToken {
    kind: TokenKind,
    spelling: Arc<str>,
}

// In the current lexer, a bare CR produces the largest combined primary and
// expected diagnostic text per consumed byte: 40 + 24 bytes. Other
// diagnostics consume enough bytes to remain within this same bound.
const SCALAR_DIAGNOSTIC_TEXT_PER_BYTE: usize = 64;

fn syntax_failure(failure: crate::syntax_resource::ResourceFailure) -> RuntimeFailure {
    RuntimeFailure::Report(crate::eval::RuntimeFailureReport {
        primary: crate::eval::RuntimeFailureSummary {
            reason: failure.reason_code(),
            resource: None,
        },
        teardown: None,
        cleanup: crate::eval::CleanupStatus::Unknown,
    })
}

fn check_declaration_contents(
    contents: &[MacroOutputNode],
    budget: &mut crate::syntax_resource::SyntaxBudget,
) -> Result<(), RuntimeFailure> {
    // The capture retains one Arc layer before any delimiter groups.
    budget
        .charge_units(contents.len())
        .map_err(syntax_failure)?;
    let mut pending = contents
        .iter()
        .map(|node| (node, 1usize))
        .collect::<Vec<_>>();
    while let Some((node, depth)) = pending.pop() {
        budget.charge().map_err(syntax_failure)?;
        match node {
            MacroOutputNode::Identifier(name, origin) => {
                crate::syntax::charge_type_name_inspection(name, depth, budget)
                    .map_err(syntax_failure)?;
                crate::syntax::charge_type_origin(origin, depth, budget).map_err(syntax_failure)?;
            }
            MacroOutputNode::Token(_, _, origin) => {
                crate::syntax::charge_type_origin(origin, depth, budget).map_err(syntax_failure)?;
            }
            MacroOutputNode::Group(_, children, origin) => {
                let depth = crate::syntax::type_depth(depth, 1).map_err(syntax_failure)?;
                crate::syntax::charge_type_origin(origin, depth, budget).map_err(syntax_failure)?;
                budget
                    .charge_units(children.len())
                    .map_err(syntax_failure)?;
                pending.extend(children.iter().map(|child| (child, depth)));
            }
            _ => return Err(RuntimeFailure::InvalidControlState),
        }
    }
    Ok(())
}

#[derive(Debug)]
pub(super) struct SyntaxHost<'inv> {
    pub(super) occurrence: NodeId,
    pub(super) binder: BinderId,
    pub(super) ops: EffectId,
    pub(super) started: bool,
    pub(super) steps_left: usize,
    invocation: Arc<()>,
    frame: Arc<ExpansionFrame>,
    source: SourceFile,
    caller: SurfaceName,
    introduction: usize,
    contexts: Arc<SyntaxContexts>,
    syntax_work: Option<&'inv mut crate::syntax_resource::SyntaxBudget>,
    fresh_count: usize,
    captures: Vec<SurfaceSyntaxCapture>,
    expressions: Vec<SurfaceExpressionCapture>,
    declarations: Vec<SurfaceDeclarationCapture>,
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

impl<'inv> SyntaxHost<'inv> {
    pub(super) fn new(
        entry: &ValidatedMacroEntry,
        captures: &[SurfaceSyntaxCapture],
        source: &SourceFile,
        caller: &SurfaceName,
        introduction: usize,
        contexts: Arc<SyntaxContexts>,
        frame: Arc<ExpansionFrame>,
        mut syntax_work: Option<&'inv mut crate::syntax_resource::SyntaxBudget>,
    ) -> Result<Self, RuntimeFailure> {
        if let Some(budget) = syntax_work.as_deref_mut() {
            budget
                .charge_units(captures.len())
                .map_err(syntax_failure)?;
            for capture in captures {
                budget.charge().map_err(syntax_failure)?;
                match capture {
                    SurfaceSyntaxCapture::Declaration(capture) => {
                        check_declaration_contents(&capture.contents, budget)?;
                    }
                    SurfaceSyntaxCapture::Identifier(capture) => {
                        crate::syntax::charge_type_name_inspection(&capture.name, 0, budget)
                            .map_err(syntax_failure)?;
                        crate::syntax::charge_type_origin(&capture.origin, 0, budget)
                            .map_err(syntax_failure)?;
                    }
                    _ => return Err(RuntimeFailure::InvalidControlState),
                }
            }
        }
        let registry = entry.program.registry();
        if let Some(budget) = syntax_work.as_deref_mut() {
            budget
                .charge_units(registry.constructors().len())
                .map_err(syntax_failure)?;
        }
        let mut constructors = HashMap::new();
        for constructor in registry
            .constructors()
            .iter()
            .filter(|constructor| constructor.id.owner().module() == entry.syntax_module)
        {
            if let Some(budget) = syntax_work.as_deref_mut() {
                budget.charge().map_err(syntax_failure)?;
                budget
                    .charge_units(constructor.spelling.len())
                    .map_err(syntax_failure)?;
            }
            if constructors
                .insert(constructor.spelling.clone(), constructor.id)
                .is_some()
            {
                return Err(RuntimeFailure::InvalidControlState);
            }
        }
        let effect = if let Some(budget) = syntax_work.as_deref_mut() {
            let mut found = None;
            for effect in registry.effects() {
                budget.charge().map_err(syntax_failure)?;
                if effect.id == entry.ops {
                    found = Some(effect);
                    break;
                }
            }
            found.ok_or(RuntimeFailure::InvalidControlState)?
        } else {
            registry
                .effects()
                .iter()
                .find(|effect| effect.id == entry.ops)
                .ok_or(RuntimeFailure::InvalidControlState)?
        };
        let operations = if let Some(budget) = syntax_work.as_deref_mut() {
            let mut operations = HashMap::new();
            for operation in effect.operations.iter() {
                budget.charge_units(2).map_err(syntax_failure)?;
                budget
                    .charge_units(operation.spelling.len())
                    .map_err(syntax_failure)?;
                operations.insert(operation.id, operation.spelling.clone());
            }
            operations
        } else {
            effect
                .operations
                .iter()
                .map(|operation| (operation.id, operation.spelling.clone()))
                .collect()
        };
        if let Some(budget) = syntax_work.as_deref_mut() {
            // Invocation Arc and Input handle; retained frame and contexts;
            // the host's capture and diagnostic storage.
            budget.charge_units(6).map_err(syntax_failure)?;
            budget
                .charge_units(source.snapshot_work().unwrap_or(usize::MAX))
                .map_err(syntax_failure)?;
            crate::syntax::charge_type_name_copy(caller, 0, budget).map_err(syntax_failure)?;
        }
        Ok(Self {
            occurrence: entry.occurrence,
            binder: entry.binder,
            ops: entry.ops,
            started: false,
            steps_left: 1_000_000,
            invocation: Arc::new(()),
            frame,
            source: source.clone(),
            caller: caller.clone(),
            introduction,
            contexts,
            fresh_count: 0,
            captures: {
                let mut copied = Vec::with_capacity(captures.len());
                for capture in captures {
                    if syntax_work.is_none()
                        && matches!(capture, SurfaceSyntaxCapture::Declaration(_))
                    {
                        return Err(RuntimeFailure::InvalidControlState);
                    }
                    if let Some(budget) = syntax_work.as_deref_mut() {
                        match capture {
                            SurfaceSyntaxCapture::Declaration(_) => {
                                budget.charge().map_err(syntax_failure)?;
                            }
                            SurfaceSyntaxCapture::Identifier(capture) => {
                                crate::syntax::charge_type_name_copy(&capture.name, 0, budget)
                                    .map_err(syntax_failure)?;
                                crate::syntax::charge_type_origin_copy(&capture.origin, 0, budget)
                                    .map_err(syntax_failure)?;
                            }
                            _ => return Err(RuntimeFailure::InvalidControlState),
                        }
                    }
                    copied.push(capture.clone());
                }
                copied
            },
            syntax_work,
            expressions: Vec::new(),
            declarations: Vec::new(),
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

    fn charge(&mut self, units: usize) -> Result<(), RuntimeFailure> {
        if let Some(budget) = self.syntax_work.as_deref_mut() {
            budget.charge_units(units).map_err(syntax_failure)?;
        }
        Ok(())
    }

    fn charge_origin(&mut self, origin: &MacroOrigin, depth: usize) -> Result<(), RuntimeFailure> {
        if let Some(budget) = self.syntax_work.as_deref_mut() {
            crate::syntax::charge_type_origin_copy(origin, depth, budget)
                .map_err(syntax_failure)?;
        }
        Ok(())
    }

    fn utf8<'a>(&mut self, bytes: &'a [u8]) -> Result<&'a str, RuntimeFailure> {
        self.charge(bytes.len())?;
        #[cfg(test)]
        {
            let count = super::machine_test_hooks::SCALAR_UTF8_SCANS.get();
            super::machine_test_hooks::SCALAR_UTF8_SCANS.set(count + 1);
        }
        std::str::from_utf8(bytes).map_err(|_| RuntimeFailure::InvalidControlState)
    }

    fn issue_origin(&mut self, origin: MacroOrigin) -> Result<Value, RuntimeFailure> {
        self.charge(2)?;
        let index = self.origins.len();
        self.origins.push(origin);
        Ok(self.handle(CompilerSyntaxHandleKind::Origin(index)))
    }

    fn copy_origin(&mut self, value: &Value, depth: usize) -> Result<MacroOrigin, RuntimeFailure> {
        let CompilerSyntaxHandleKind::Origin(index) = self.admitted_handle(value)? else {
            return Err(RuntimeFailure::InvalidControlState);
        };
        let origin = self
            .origins
            .get(index)
            .ok_or(RuntimeFailure::InvalidControlState)?;
        if let Some(budget) = self.syntax_work.as_deref_mut() {
            crate::syntax::charge_type_origin_copy(origin, depth, budget)
                .map_err(syntax_failure)?;
        }
        Ok(origin.clone())
    }

    fn primary_origin(&mut self, value: &Value) -> Result<crate::source::Span, RuntimeFailure> {
        let CompilerSyntaxHandleKind::Origin(index) = self.admitted_handle(value)? else {
            return Err(RuntimeFailure::InvalidControlState);
        };
        let mut origin = self
            .origins
            .get(index)
            .ok_or(RuntimeFailure::InvalidControlState)?;
        let Some(budget) = self.syntax_work.as_deref_mut() else {
            return Ok(origin.primary());
        };
        loop {
            budget.charge().map_err(syntax_failure)?;
            match origin {
                MacroOrigin::Source(span) => return Ok(*span),
                MacroOrigin::Combined { inputs, .. } => {
                    origin = inputs.first().ok_or(RuntimeFailure::InvalidControlState)?;
                }
            }
        }
    }

    fn read_origins<'a>(
        &mut self,
        mut origins: &'a Value,
        heap: &'a [HeapCell],
        mut remaining_spans: usize,
    ) -> Result<Vec<MacroOrigin>, RuntimeFailure> {
        let mut inputs = Vec::new();
        loop {
            self.charge(1)?;
            let (tag, payload) = constructor_fields(origins, heap)?;
            if tag == self.constructor("NoOrigins")? && payload.is_none() {
                return Ok(inputs);
            }
            if tag != self.constructor("MoreOrigins")? {
                return Err(RuntimeFailure::InvalidControlState);
            }
            let (origin, rest) = pair(payload.ok_or(RuntimeFailure::InvalidControlState)?, heap)?;
            let CompilerSyntaxHandleKind::Origin(index) = self.admitted_handle(origin)? else {
                return Err(RuntimeFailure::InvalidControlState);
            };
            let origin = self
                .origins
                .get(index)
                .ok_or(RuntimeFailure::InvalidControlState)?;
            remaining_spans = remaining_spans
                .checked_sub(origin.span_count())
                .ok_or(RuntimeFailure::ResourceCapacity)?;
            if let Some(budget) = self.syntax_work.as_deref_mut() {
                budget.charge().map_err(syntax_failure)?;
                crate::syntax::charge_type_origin_copy(origin, 0, budget)
                    .map_err(syntax_failure)?;
            }
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
        &mut self,
        heap: &mut Vec<HeapCell>,
        name: &str,
        payload: Option<Value>,
    ) -> Result<Value, RuntimeFailure> {
        let id = self.constructor(name)?;
        self.charge(1)?;
        Ok(Value::Location(allocate_heap(
            heap,
            HeapCell::Constructor(id, payload),
        )?))
    }

    fn single_token(&mut self, spelling: &str) -> Result<Option<TokenKind>, RuntimeFailure> {
        let Some(budget) = self.syntax_work.as_deref_mut() else {
            return single_token(spelling);
        };
        if matches!(spelling, "\n" | "\r\n") {
            return Ok(Some(TokenKind::LineEnd));
        }
        // Reserve this newline count scan, source text/path and line-index
        // storage, and SourceFile's own text scan before constructing it.
        budget
            .charge_units(spelling.len())
            .map_err(syntax_failure)?;
        let lines = spelling
            .bytes()
            .filter(|byte| *byte == b'\n')
            .count()
            .saturating_add(1);
        budget
            .charge_units(spelling.len())
            .map_err(syntax_failure)?;
        budget
            .charge_units(spelling.len())
            .map_err(syntax_failure)?;
        budget
            .charge_units("<syntax-token>".len())
            .map_err(syntax_failure)?;
        budget.charge_units(lines).map_err(syntax_failure)?;
        let source = SourceFile::new("<syntax-token>", spelling.to_owned())
            .map_err(|_| RuntimeFailure::HeapCapacity)?;
        // Eight spelling-length scans cover the outer lexer, token scanning,
        // identifier checks and decimal normalization. Two further lengths
        // cover temporary decoded and found text, and one covers delimiter
        // context entries. Lexical output slots are separately charged by
        // lex_with_budget.
        for _ in 0..11 {
            budget
                .charge_units(spelling.len())
                .map_err(syntax_failure)?;
        }
        // Diagnostic spans consume disjoint input. This bound covers both
        // primary and expected strings before the lexer constructs them.
        budget
            .charge_units(
                spelling
                    .len()
                    .checked_mul(SCALAR_DIAGNOSTIC_TEXT_PER_BYTE)
                    .unwrap_or(usize::MAX),
            )
            .map_err(syntax_failure)?;
        budget.charge().map_err(syntax_failure)?;
        #[cfg(test)]
        {
            let count = super::machine_test_hooks::SCALAR_LEX_STARTS.get();
            super::machine_test_hooks::SCALAR_LEX_STARTS.set(count + 1);
        }
        let lexed = crate::lexer::lex_with_budget(&source, budget)
            .map_err(|_| RuntimeFailure::InvalidControlState)?;
        if let Some(failure) = lexed.resource_failure() {
            return Err(syntax_failure(failure));
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
        crate::syntax::charge_type_token_copy(&token.kind, budget).map_err(syntax_failure)?;
        Ok(Some(token.kind.clone()))
    }

    pub(super) fn request(
        &mut self,
        operation: OperationId,
        argument: Value,
        heap: &mut Vec<HeapCell>,
        work: &mut TypeWorkBudget,
    ) -> Result<Value, RuntimeFailure> {
        #[cfg(test)]
        {
            let requests = super::machine_test_hooks::SYNTAX_REQUESTS.get();
            super::machine_test_hooks::SYNTAX_REQUESTS.set(requests + 1);
        }
        let operation = self
            .operations
            .get(&operation)
            .ok_or(RuntimeFailure::InvalidControlState)?;
        if let Some(budget) = self.syntax_work.as_deref_mut() {
            budget.charge().map_err(syntax_failure)?;
            budget
                .charge_units(operation.len())
                .map_err(syntax_failure)?;
        }
        let operation = operation.clone();
        match operation.as_str() {
            "invocation_origin" | "definition_origin" => {
                if !matches!(
                    self.admitted_handle(&argument)?,
                    CompilerSyntaxHandleKind::Input
                ) {
                    return Err(RuntimeFailure::InvalidControlState);
                }
                let origin = if operation == "invocation_origin" {
                    self.frame.invocation
                } else {
                    self.frame.definition
                };
                self.issue_origin(origin.into())
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
                let capture = index.and_then(|index| self.captures.get(index));
                if let Some(SurfaceSyntaxCapture::Declaration(declaration)) = capture {
                    let Some(budget) = self.syntax_work.as_deref_mut() else {
                        return Err(RuntimeFailure::InvalidControlState);
                    };
                    // Storage slot, retained contents Arc, and issued handle.
                    budget.charge_units(3).map_err(syntax_failure)?;
                    let declaration = declaration.clone();
                    let index = self.declarations.len();
                    self.declarations.push(declaration);
                    #[cfg(test)]
                    {
                        let count = super::machine_test_hooks::DECLARATION_CAPTURES.get();
                        super::machine_test_hooks::DECLARATION_CAPTURES.set(count + 1);
                    }
                    let handle = self.handle(CompilerSyntaxHandleKind::Declaration(index));
                    let capture = self.construct(heap, "DeclarationCapture", Some(handle))?;
                    return self.construct(heap, "Captured", Some(capture));
                }
                if let (Some(budget), Some(SurfaceSyntaxCapture::Identifier(capture))) =
                    (self.syntax_work.as_deref_mut(), capture)
                {
                    crate::syntax::charge_type_name_copy(&capture.name, 0, budget)
                        .map_err(syntax_failure)?;
                    crate::syntax::charge_type_origin_copy(&capture.origin, 0, budget)
                        .map_err(syntax_failure)?;
                    // Identifier slot and handle, plus tuple fields and cell.
                    budget.charge_units(5).map_err(syntax_failure)?;
                }
                match capture.cloned() {
                    Some(SurfaceSyntaxCapture::Expression(expression)) => {
                        let index = self.expressions.len();
                        self.expressions.push(expression);
                        let fragment = self.handle(CompilerSyntaxHandleKind::Expression(index));
                        let capture = self.construct(heap, "ExpressionCapture", Some(fragment))?;
                        self.construct(heap, "Captured", Some(capture))
                    }
                    Some(SurfaceSyntaxCapture::Identifier(capture)) => {
                        let origin = self.issue_origin(capture.origin)?;
                        let index = self.identifiers.len();
                        self.identifiers.push(capture.name);
                        let identifier = self.handle(CompilerSyntaxHandleKind::Identifier(index));
                        let fields = vec![identifier, origin].into_boxed_slice();
                        let fields = Value::Location(allocate_heap(heap, HeapCell::Tuple(fields))?);
                        let capture = self.construct(heap, "IdentifierCapture", Some(fields))?;
                        self.construct(heap, "Captured", Some(capture))
                    }
                    Some(
                        SurfaceSyntaxCapture::Type(_)
                        | SurfaceSyntaxCapture::Pattern(_)
                        | SurfaceSyntaxCapture::Declaration(_),
                    ) => Err(RuntimeFailure::InvalidControlState),
                    None => self.construct(heap, "MissingCapture", None),
                }
            }
            "make_token" => {
                let (kind, spelling) = pair(&argument, heap)?;
                let (tag, payload) = constructor_fields(kind, heap)?;
                let (spelling, is_string) = borrowed_bytes(spelling, heap, work)?;
                let spelling = self.utf8(spelling)?;
                let token = if is_string && payload.is_none() {
                    if self.syntax_work.is_some() {
                        self.single_token(spelling)?
                            .filter(|kind| token_kind_name(kind).is_some())
                    } else {
                        token_from_spelling(spelling)?
                    }
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
                self.charge(2)?;
                self.charge(spelling.len())?;
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
                if let Some(budget) = self.syntax_work.as_deref_mut() {
                    budget.charge().map_err(syntax_failure)?;
                    budget
                        .charge_units(name.text.len())
                        .map_err(syntax_failure)?;
                }
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
                let origin = self.primary_origin(origin)?;
                let (spelling, is_string) = borrowed_bytes(spelling, heap, work)?;
                let spelling = self.utf8(spelling)?;
                if !is_string
                    || !matches!(
                        self.single_token(spelling)?,
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
                            Some(self.frame.invocation),
                        )
                    }
                    "definition_identifier" => (self.introduction, Some(self.frame.invocation)),
                    _ => (self.caller.introduction, self.caller.introduced_at),
                };
                let index = self.identifiers.len();
                self.charge(2)?;
                self.charge(spelling.len())?;
                self.identifiers.push(SurfaceName {
                    text: spelling.to_owned(),
                    span: origin,
                    introduction,
                    introduced_at,
                    written: false,
                    diagnostic: None,
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
                if let Some(budget) = self.syntax_work.as_deref_mut() {
                    // Combination visits and retains the inputs and frame.
                    budget.charge_units(2).map_err(syntax_failure)?;
                    budget.charge_units(inputs.len()).map_err(syntax_failure)?;
                    budget.charge_units(inputs.len()).map_err(syntax_failure)?;
                    for origin in &inputs {
                        crate::syntax::charge_type_origin(origin, 1, budget)
                            .map_err(syntax_failure)?;
                    }
                }
                let origin = MacroOrigin::combined(inputs, Arc::clone(&self.frame))
                    .ok_or(RuntimeFailure::ResourceCapacity)?;
                let combined = self.issue_origin(origin)?;
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
                if self.syntax_work.is_some() {
                    return Err(RuntimeFailure::InvalidControlState);
                }
                let output = self.transfer_syntax(syntax, heap, 0)?;
                let contents = output.clone().into();
                match crate::syntax::admit_transformer_output(
                    &self.source,
                    output,
                    &self.contexts,
                    &self.frame,
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
                if self.syntax_work.is_some() {
                    return Err(RuntimeFailure::InvalidControlState);
                }
                let contents = Arc::clone(
                    &self
                        .expressions
                        .get(index)
                        .ok_or(RuntimeFailure::InvalidControlState)?
                        .contents,
                );
                self.syntax_value(&contents, heap, 0)
            }
            "declaration_syntax" => {
                let CompilerSyntaxHandleKind::Declaration(index) =
                    self.admitted_handle(&argument)?
                else {
                    return Err(RuntimeFailure::InvalidControlState);
                };
                let declaration = self
                    .declarations
                    .get(index)
                    .ok_or(RuntimeFailure::InvalidControlState)?;
                let Some(budget) = self.syntax_work.as_deref_mut() else {
                    return Err(RuntimeFailure::InvalidControlState);
                };
                budget.charge().map_err(syntax_failure)?;
                let contents = Arc::clone(&declaration.contents);
                #[cfg(test)]
                {
                    let count = super::machine_test_hooks::DECLARATION_UNWRAPS.get();
                    super::machine_test_hooks::DECLARATION_UNWRAPS.set(count + 1);
                }
                self.syntax_value(&contents, heap, 1)
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
                if let Some(budget) = self.syntax_work.as_deref_mut() {
                    budget.charge().map_err(syntax_failure)?;
                }
                Ok(Value::String(Arc::clone(&token.spelling)))
            }
            _ => Err(RuntimeFailure::InvalidControlState),
        }
    }

    pub(super) fn transfer(
        &mut self,
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
                    invocation: self.frame.invocation,
                    definition: self.frame.definition,
                    teardown: None,
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
        let message = self.utf8(message)?;
        self.charge(message.len())?;
        let message = message.to_owned();
        let primary = self.copy_origin(primary, 0)?;
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
                invocation: self.frame.invocation,
                definition: self.frame.definition,
                teardown: None,
            },
        ))
    }

    fn transfer_syntax(
        &mut self,
        syntax: &Value,
        heap: &[HeapCell],
        depth: usize,
    ) -> Result<Vec<MacroOutputNode>, RuntimeFailure> {
        if self.syntax_work.is_some() {
            crate::syntax::type_depth(depth, 0).map_err(syntax_failure)?;
        } else if depth > crate::parser::STRUCTURAL_DEPTH_LIMIT {
            return Err(RuntimeFailure::ResourceCapacity);
        }
        let (tag, nodes) = constructor_fields(syntax, heap)?;
        if tag != self.constructor("Syntax")? {
            return Err(RuntimeFailure::InvalidControlState);
        }
        let mut nodes = nodes.ok_or(RuntimeFailure::InvalidControlState)?;
        let mut output = Vec::new();
        let mut groups: Vec<(&Value, Vec<MacroOutputNode>, MacroDelimiter, MacroOrigin)> =
            Vec::new();
        loop {
            self.charge(1)?;
            if output.len() >= 65_536 {
                return Err(RuntimeFailure::HeapCapacity);
            }
            let (tag, payload) = constructor_fields(nodes, heap)?;
            if tag == self.constructor("NoNodes")? && payload.is_none() {
                let Some((rest, mut parent, delimiter, origin)) = groups.pop() else {
                    return Ok(output);
                };
                #[cfg(test)]
                {
                    let completed = super::machine_test_hooks::TRANSFER_GROUPS_COMPLETED.get();
                    super::machine_test_hooks::TRANSFER_GROUPS_COMPLETED.set(completed + 1);
                }
                self.charge(1)?;
                parent.push(MacroOutputNode::Group(delimiter, output, origin));
                output = parent;
                nodes = rest;
                continue;
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
                let origin_depth = depth.saturating_add(groups.len()).saturating_add(1);
                let origin = self.copy_origin(origin, origin_depth)?;
                if self.syntax_work.is_some() {
                    crate::syntax::type_depth(depth.saturating_add(groups.len()), 1)
                        .map_err(syntax_failure)?;
                } else if depth + groups.len() >= crate::parser::STRUCTURAL_DEPTH_LIMIT {
                    return Err(RuntimeFailure::ResourceCapacity);
                }
                let (tag, children) = constructor_fields(syntax, heap)?;
                if tag != self.constructor("Syntax")? {
                    return Err(RuntimeFailure::InvalidControlState);
                }
                let children = children.ok_or(RuntimeFailure::InvalidControlState)?;
                self.charge(1)?;
                groups
                    .try_reserve(1)
                    .map_err(|_| RuntimeFailure::HeapCapacity)?;
                groups.push((rest, output, delimiter, origin));
                output = Vec::new();
                nodes = children;
                continue;
            } else {
                if self.syntax_work.is_some() {
                    self.charge(4)?;
                    if [
                        "ExpressionNode",
                        "TypeNode",
                        "PatternNode",
                        "DeclarationNode",
                    ]
                    .iter()
                    .any(|name| self.constructors.get(*name) == Some(&tag))
                    {
                        return Err(RuntimeFailure::InvalidControlState);
                    }
                }
                let (value, origin) = pair(payload, heap)?;
                let origin = self.copy_origin(origin, depth.saturating_add(groups.len()))?;
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
                    if let Some(budget) = self.syntax_work.as_deref_mut() {
                        budget.charge().map_err(syntax_failure)?;
                        crate::syntax::charge_type_name_copy(
                            name,
                            depth.saturating_add(groups.len()),
                            budget,
                        )
                        .map_err(syntax_failure)?;
                    }
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
                    if let Some(budget) = self.syntax_work.as_deref_mut() {
                        // Output slot and spelling Arc retention.
                        budget.charge_units(2).map_err(syntax_failure)?;
                        crate::syntax::charge_type_token_copy(&token.kind, budget)
                            .map_err(syntax_failure)?;
                    }
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
        if self.syntax_work.is_some() {
            crate::syntax::type_depth(depth, 0).map_err(syntax_failure)?;
        } else if depth > crate::parser::STRUCTURAL_DEPTH_LIMIT {
            return Err(RuntimeFailure::ResourceCapacity);
        }
        let mut groups = Vec::new();
        let mut nodes = nodes.iter().rev();
        let mut rest = self.construct(heap, "NoNodes", None)?;
        loop {
            self.charge(1)?;
            let (constructor, fields) = match nodes.next() {
                Some(MacroOutputNode::Expression(expression, origin))
                | Some(MacroOutputNode::ForwardedExpression(expression, origin)) => {
                    if self.syntax_work.is_some() {
                        return Err(RuntimeFailure::InvalidControlState);
                    }
                    let index = self.expressions.len();
                    self.expressions.push(expression.clone());
                    (
                        "ExpressionNode",
                        vec![
                            self.handle(CompilerSyntaxHandleKind::Expression(index)),
                            self.issue_origin(origin.clone())?,
                        ],
                    )
                }
                Some(MacroOutputNode::Identifier(name, origin)) => {
                    if let Some(budget) = self.syntax_work.as_deref_mut() {
                        crate::syntax::charge_type_name_copy(
                            name,
                            depth.saturating_add(groups.len()),
                            budget,
                        )
                        .map_err(syntax_failure)?;
                    }
                    self.charge_origin(origin, depth.saturating_add(groups.len()))?;
                    // Identifier slot and handle; two tuple fields.
                    self.charge(4)?;
                    let index = self.identifiers.len();
                    self.identifiers.push(name.clone());
                    (
                        "IdentifierNode",
                        vec![
                            self.handle(CompilerSyntaxHandleKind::Identifier(index)),
                            self.issue_origin(origin.clone())?,
                        ],
                    )
                }
                Some(MacroOutputNode::Token(kind, spelling, origin)) => {
                    if let Some(budget) = self.syntax_work.as_deref_mut() {
                        crate::syntax::charge_type_token_copy(kind, budget)
                            .map_err(syntax_failure)?;
                    }
                    self.charge_origin(origin, depth.saturating_add(groups.len()))?;
                    // Token slot, spelling Arc, handle and two tuple fields.
                    self.charge(5)?;
                    let index = self.tokens.len();
                    self.tokens.push(SyntaxToken {
                        kind: kind.clone(),
                        spelling: Arc::clone(spelling),
                    });
                    (
                        "TokenNode",
                        vec![
                            self.handle(CompilerSyntaxHandleKind::Token(index)),
                            self.issue_origin(origin.clone())?,
                        ],
                    )
                }
                Some(MacroOutputNode::Group(delimiter, children, origin)) => {
                    let delimiter = match delimiter {
                        MacroDelimiter::Parentheses => "Parentheses",
                        MacroDelimiter::Braces => "Braces",
                    };
                    let delimiter = self.construct(heap, delimiter, None)?;
                    if self.syntax_work.is_some() {
                        crate::syntax::type_depth(depth.saturating_add(groups.len()), 1)
                            .map_err(syntax_failure)?;
                    } else if depth + groups.len() >= crate::parser::STRUCTURAL_DEPTH_LIMIT {
                        return Err(RuntimeFailure::ResourceCapacity);
                    }
                    self.charge(1)?;
                    groups
                        .try_reserve(1)
                        .map_err(|_| RuntimeFailure::HeapCapacity)?;
                    groups.push((nodes, rest, delimiter, origin));
                    nodes = children.iter().rev();
                    rest = self.construct(heap, "NoNodes", None)?;
                    continue;
                }
                Some(
                    MacroOutputNode::Splice(_)
                    | MacroOutputNode::ForwardedType(_, _)
                    | MacroOutputNode::ForwardedPattern(_, _),
                ) => {
                    return Err(RuntimeFailure::InvalidControlState);
                }
                None => {
                    let children = self.construct(heap, "Syntax", Some(rest))?;
                    let Some((parent, parent_rest, delimiter, origin)) = groups.pop() else {
                        return Ok(children);
                    };
                    nodes = parent;
                    rest = parent_rest;
                    self.charge_origin(
                        origin,
                        depth.saturating_add(groups.len()).saturating_add(1),
                    )?;
                    self.charge(3)?;
                    (
                        "GroupNode",
                        vec![delimiter, children, self.issue_origin(origin.clone())?],
                    )
                }
            };
            self.charge(1)?;
            let fields = Value::Location(allocate_heap(
                heap,
                HeapCell::Tuple(fields.into_boxed_slice()),
            )?);
            let node = self.construct(heap, constructor, Some(fields))?;
            self.charge(3)?;
            let pair = Value::Location(allocate_heap(
                heap,
                HeapCell::Tuple(vec![node, rest].into_boxed_slice()),
            )?);
            rest = self.construct(heap, "MoreNodes", Some(pair))?;
        }
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
        TokenKind::SyntaxKeyword => "SyntaxKeyword",
        TokenKind::Dollar => "Dollar",
        TokenKind::Identifier(_)
        | TokenKind::UpperIdentifier(_)
        | TokenKind::LeftParen
        | TokenKind::RightParen
        | TokenKind::LeftBrace
        | TokenKind::RightBrace
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

    struct DeclarationHostFixture {
        entry: crate::core::validate::ValidatedMacroEntry,
        source: crate::source::SourceFile,
        caller: crate::surface::SurfaceName,
        frame: std::sync::Arc<crate::syntax::ExpansionFrame>,
        contexts: std::sync::Arc<crate::syntax::SyntaxContexts>,
        capture: crate::types::OperationId,
        unwrap: crate::types::OperationId,
        parse_expression: crate::types::OperationId,
        expression_syntax: crate::types::OperationId,
        constructors: std::collections::HashMap<String, crate::types::ConstructorId>,
    }

    impl DeclarationHostFixture {
        fn new() -> Self {
            use crate::{
                core::{EffectCoreBuilder, validate::ValidatedMacroEntry, validate_effect},
                module::ModuleId,
                resolved::{
                    BinderId, ResolvedConstructor, ResolvedEffectDeclaration,
                    ResolvedEffectOperation, ResolvedNominalDeclarationKind, ResolvedNominalType,
                    ResolvedRegistry, ResolvedType, ResolvedTypeProvenance,
                    ResolvedTypeProvenanceNode,
                },
                source::{ByteRange, Origin, SourceFile},
                surface::SurfaceName,
                syntax::{ExpansionFrame, SyntaxContexts},
                types::{ConstructorId, EffectId, NominalTypeId, OperationId, Type},
            };
            use std::sync::Arc;

            let source = SourceFile::new("component.ash", "type Item = Item\n").unwrap();
            let span = source.span(ByteRange::new(5, 9).unwrap()).unwrap();
            let module = ModuleId::new(0);
            let owner = NominalTypeId::new(module, 0);
            let names = [
                "Captured",
                "DeclarationCapture",
                "IdentifierCapture",
                "MissingCapture",
                "Syntax",
                "NoNodes",
                "MoreNodes",
                "GroupNode",
                "Parentheses",
                "Braces",
                "IdentifierNode",
                "TokenNode",
                "ExpressionNode",
                "TypeNode",
                "PatternNode",
                "DeclarationNode",
                "Expanded",
            ];
            let constructors = names
                .iter()
                .enumerate()
                .map(|(index, name)| ((*name).to_owned(), ConstructorId::new(owner, index as u32)))
                .collect::<std::collections::HashMap<_, _>>();
            let nominal = ResolvedNominalType {
                id: owner,
                declaration_kind: ResolvedNominalDeclarationKind::Data,
                spelling: "FixtureSyntax".into(),
                constructors: names.iter().map(|name| constructors[*name]).collect(),
                representation: None,
                representation_provenance: None,
                origin: Origin::Source(source.span(ByteRange::new(0, 17).unwrap()).unwrap()),
            };
            let members = names
                .iter()
                .enumerate()
                .map(|(index, name)| ResolvedConstructor {
                    id: constructors[*name],
                    owner,
                    spelling: (*name).into(),
                    payload: (!matches!(
                        *name,
                        "NoNodes" | "Parentheses" | "Braces" | "MissingCapture"
                    ))
                    .then_some(Type::Unit),
                    origin: Origin::Source(
                        source
                            .span(ByteRange::new(index as u32, index as u32 + 1).unwrap())
                            .unwrap(),
                    ),
                })
                .collect();
            let ops = EffectId::new(module, 0);
            let operation_names = [
                "capture",
                "declaration_syntax",
                "parse_expression",
                "expression_syntax",
            ];
            let operations = operation_names
                .iter()
                .enumerate()
                .map(|(index, name)| ResolvedEffectOperation {
                    id: OperationId::new(ops, index as u32),
                    spelling: (*name).into(),
                    annotation: ResolvedType {
                        ty: Type::Function(Box::new(Type::Unit), Box::new(Type::Unit)),
                        provenance: ResolvedTypeProvenance::new(
                            vec![ResolvedTypeProvenanceNode::Fact(span)],
                            0,
                        ),
                        origin: Origin::Source(span),
                        span,
                    },
                    origin: Origin::Source(span),
                    span,
                })
                .collect::<Vec<_>>();
            let registry = ResolvedRegistry::new(vec![nominal], members).with_effects(vec![
                ResolvedEffectDeclaration {
                    id: ops,
                    public: false,
                    spelling: "Ops".into(),
                    parameters: Box::new([]),
                    operations: operations.into_boxed_slice(),
                    native_contract: None,
                    origin: Origin::Source(span),
                    span,
                },
            ]);
            let mut builder = EffectCoreBuilder::with_effect_registry(Arc::new(registry));
            let occurrence = builder.unit(Type::Unit, Origin::Source(span)).unwrap();
            let program = validate_effect(builder.finish(occurrence).unwrap(), &[&source]).unwrap();
            Self {
                entry: ValidatedMacroEntry {
                    program,
                    occurrence,
                    binder: BinderId::new(0),
                    syntax_module: module,
                    ops,
                },
                source,
                caller: SurfaceName {
                    text: "Item".into(),
                    span,
                    introduction: 0,
                    introduced_at: None,
                    written: true,
                    diagnostic: None,
                },
                frame: Arc::new(ExpansionFrame {
                    invocation: span,
                    definition: span,
                }),
                contexts: Arc::new(SyntaxContexts::new(&[], &[], &[])),
                capture: OperationId::new(ops, 0),
                unwrap: OperationId::new(ops, 1),
                parse_expression: OperationId::new(ops, 2),
                expression_syntax: OperationId::new(ops, 3),
                constructors,
            }
        }

        fn host<'a>(
            &self,
            captures: &[crate::surface::SurfaceSyntaxCapture],
            budget: &'a mut crate::syntax_resource::SyntaxBudget,
        ) -> Result<super::SyntaxHost<'a>, super::RuntimeFailure> {
            super::SyntaxHost::new(
                &self.entry,
                captures,
                &self.source,
                &self.caller,
                0,
                std::sync::Arc::clone(&self.contexts),
                std::sync::Arc::clone(&self.frame),
                Some(budget),
            )
        }
    }

    fn scalar_host<'a>(
        budget: &'a mut crate::syntax_resource::SyntaxBudget,
    ) -> super::SyntaxHost<'a> {
        use crate::{
            core::CoreBuilder,
            module::ModuleId,
            resolved::BinderId,
            source::{ByteRange, Origin, SourceFile},
            surface::SurfaceName,
            syntax::{ExpansionFrame, SyntaxContexts},
            types::{EffectId, Type},
        };
        use std::{collections::HashMap, sync::Arc};

        let source = SourceFile::new("scalar.ash", "name").unwrap();
        let span = source.span(ByteRange::new(0, 4).unwrap()).unwrap();
        let occurrence = CoreBuilder::new()
            .unit(Type::Unit, Origin::Source(span))
            .unwrap();
        super::SyntaxHost {
            occurrence,
            binder: BinderId::new(0),
            ops: EffectId::new(ModuleId::new(0), 0),
            started: false,
            steps_left: 100,
            invocation: Arc::new(()),
            frame: Arc::new(ExpansionFrame {
                invocation: span,
                definition: span,
            }),
            source,
            caller: SurfaceName {
                text: "name".into(),
                span,
                introduction: 0,
                introduced_at: None,
                written: true,
                diagnostic: None,
            },
            introduction: 0,
            contexts: Arc::new(SyntaxContexts::new(&[], &[], &[])),
            syntax_work: Some(budget),
            fresh_count: 0,
            captures: Vec::new(),
            expressions: Vec::new(),
            declarations: Vec::new(),
            identifiers: Vec::new(),
            origins: Vec::new(),
            parse_failures: Vec::new(),
            tokens: Vec::new(),
            constructors: HashMap::new(),
            operations: HashMap::new(),
        }
    }

    #[test]
    fn declaration_scalar_lex_reserves_before_temporary_payload_and_retries() {
        use super::super::machine_test_hooks as hooks;
        use crate::{eval::RuntimeFailure, lexer::TokenKind, syntax_resource::SyntaxBudget};

        for spelling in [format!("\"{}\"", "a".repeat(120)), "9".repeat(120)] {
            let length = spelling.len();
            let before_lex = 3 * length + "<syntax-token>".len() + 1 + 75 * length + 1;
            hooks::reset();
            let mut short = SyntaxBudget::with_limit(before_lex - 1);
            let mut host = scalar_host(&mut short);
            let failure = host.single_token(&spelling).unwrap_err();
            assert!(matches!(failure, RuntimeFailure::Report(report)
                if report.primary.reason_code() == "internal.resource.syntax-work"
                    && report.primary.resource().is_none()));
            assert_eq!(hooks::SCALAR_LEX_STARTS.get(), 0);
            drop(host);

            hooks::reset();
            let mut measured = SyntaxBudget::default();
            let mut host = scalar_host(&mut measured);
            let token = host.single_token(&spelling).unwrap().unwrap();
            assert!(matches!(
                token,
                TokenKind::StringLiteral(_) | TokenKind::Integer(_)
            ));
            assert_eq!(hooks::SCALAR_LEX_STARTS.get(), 1);
            drop(host);
            let used = measured.consumed();
            assert!(used > before_lex);

            hooks::reset();
            let mut short = SyntaxBudget::with_limit(used - 1);
            let mut host = scalar_host(&mut short);
            assert!(
                matches!(host.single_token(&spelling), Err(RuntimeFailure::Report(report))
                if report.primary.reason_code() == "internal.resource.syntax-work")
            );
            assert_eq!(hooks::SCALAR_LEX_STARTS.get(), 1);
            drop(host);

            hooks::reset();
            let mut exact = SyntaxBudget::with_limit(used);
            let mut host = scalar_host(&mut exact);
            assert!(host.single_token(&spelling).unwrap().is_some());
            drop(host);
            assert_eq!(exact.consumed(), used);
        }
        hooks::reset();
        eprintln!("string and integer: pre-lex refusal, late one-short refusal, exact retry");
    }

    #[test]
    fn declaration_scalar_utf8_reserves_before_the_scan() {
        use super::super::machine_test_hooks as hooks;
        use crate::{eval::RuntimeFailure, syntax_resource::SyntaxBudget};

        let bytes = "name λ".as_bytes();
        hooks::reset();
        let mut short = SyntaxBudget::with_limit(bytes.len() - 1);
        let mut host = scalar_host(&mut short);
        assert!(
            matches!(host.utf8(bytes), Err(RuntimeFailure::Report(report))
            if report.primary.reason_code() == "internal.resource.syntax-work"
                && report.primary.resource().is_none())
        );
        assert_eq!(hooks::SCALAR_UTF8_SCANS.get(), 0);
        drop(host);

        let mut exact = SyntaxBudget::with_limit(bytes.len());
        let mut host = scalar_host(&mut exact);
        let text = host.utf8(bytes).unwrap();
        assert_eq!(text, "name λ");
        assert_eq!(text.as_ptr(), bytes.as_ptr());
        assert_eq!(hooks::SCALAR_UTF8_SCANS.get(), 1);
        drop(host);
        assert_eq!(exact.consumed(), bytes.len());
        hooks::reset();
        eprintln!("UTF-8 one-short refuses before scan; exact returns borrowed text");
    }

    #[test]
    fn declaration_contents_preflight_checks_real_depth_and_drop_on_small_stack() {
        use crate::{
            eval::RuntimeFailure,
            lexer::TokenKind,
            source::{ByteRange, SourceFile},
            syntax::{MacroDelimiter, MacroOutputNode},
            syntax_resource::SyntaxBudget,
        };
        use std::sync::Arc;

        std::thread::Builder::new()
            .stack_size(512 * 1024)
            .spawn(|| {
                let source = SourceFile::new("depth.ash", "true").unwrap();
                let span = source.span(ByteRange::new(0, 4).unwrap()).unwrap();
                let packet = |groups: usize| {
                    let mut node =
                        MacroOutputNode::Token(TokenKind::True, Arc::from("true"), span.into());
                    for _ in 0..groups {
                        node = MacroOutputNode::Group(
                            MacroDelimiter::Parentheses,
                            vec![node],
                            span.into(),
                        );
                    }
                    Arc::<[MacroOutputNode]>::from(vec![node])
                };

                let accepted = packet(127);
                eprintln!("constructed real declaration contents at depth 128 on 512 KiB");
                let retained = Arc::strong_count(&accepted);
                let mut measured = SyntaxBudget::default();
                super::check_declaration_contents(&accepted, &mut measured).unwrap();
                let total = measured.consumed();
                assert_eq!(Arc::strong_count(&accepted), retained);
                let mut short = SyntaxBudget::with_limit(total - 1);
                assert!(matches!(
                    super::check_declaration_contents(&accepted, &mut short),
                    Err(RuntimeFailure::Report(report))
                        if report.primary.reason_code() == "internal.resource.syntax-work"
                            && report.primary.resource().is_none()
                ));
                assert_eq!(Arc::strong_count(&accepted), retained);
                let mut exact = SyntaxBudget::with_limit(total);
                super::check_declaration_contents(&accepted, &mut exact).unwrap();
                assert_eq!(exact.consumed(), total);
                eprintln!("depth 128 accepted, exact/short/retry on borrowed contents");
                drop(accepted);
                eprintln!("depth 128 contents dropped on 512 KiB");

                let refused = packet(128);
                eprintln!("constructed real declaration contents at depth 129 on 512 KiB");
                let retained = Arc::strong_count(&refused);
                let mut budget = SyntaxBudget::default();
                assert!(matches!(
                    super::check_declaration_contents(&refused, &mut budget),
                    Err(RuntimeFailure::Report(report))
                        if report.primary.reason_code() == "internal.resource.structural-depth"
                            && report.primary.resource().is_none()
                ));
                assert_eq!(Arc::strong_count(&refused), retained);
                eprintln!("depth 129 refused before retention on 512 KiB");
                drop(refused);
                eprintln!("depth 129 contents dropped on 512 KiB");
            })
            .unwrap()
            .join()
            .unwrap();
    }

    #[test]
    fn declaration_host_roundtrips_composed_depth_on_small_stack() {
        use super::{HeapCell, RuntimeFailure, Value, allocate_heap, constructor_fields};
        use crate::{
            integer::Integer,
            surface::{SurfaceDeclarationCapture, SurfaceSyntaxCapture},
            syntax::{
                DiagnosticLocation, MacroDelimiter, MacroOrigin, MacroOutputNode, TransformerOutput,
            },
            syntax_resource::SyntaxBudget,
            types::TypeWorkBudget,
        };
        use std::sync::Arc;

        std::thread::Builder::new()
            .stack_size(512 * 1024)
            .spawn(|| {
                let fixture = DeclarationHostFixture::new();
                let packet = |groups: usize| {
                    let combined = MacroOrigin::combined(
                        vec![fixture.caller.span.into()], Arc::clone(&fixture.frame),
                    ).unwrap();
                    let MacroOrigin::Combined { inputs, .. } = &combined else { unreachable!() };
                    let weak = Arc::downgrade(inputs);
                    let mut name = fixture.caller.clone();
                    name.diagnostic = Some(Box::new(DiagnosticLocation::new(combined)));
                    let mut node = MacroOutputNode::Identifier(name, fixture.caller.span.into());
                    for _ in 0..groups {
                        node = MacroOutputNode::Group(MacroDelimiter::Parentheses, vec![node], fixture.caller.span.into());
                    }
                    (Arc::<[MacroOutputNode]>::from(vec![node]), weak)
                };

                // Capture Arc layer + 125 groups + name location + Combined input = 128.
                let (original, weak) = packet(125);
                eprintln!("constructed depth-128 declaration, diagnostic and origin on 512 KiB");
                let captures = [SurfaceSyntaxCapture::Declaration(SurfaceDeclarationCapture {
                    contents: Arc::clone(&original),
                })];
                let initial = Arc::strong_count(&original);
                let mut budget = SyntaxBudget::default();
                let mut host = fixture.host(&captures, &mut budget).unwrap();
                assert_eq!(Arc::strong_count(&original), initial + 1);
                let mut heap = Vec::new();
                let argument = Value::Location(allocate_heap(
                    &mut heap,
                    HeapCell::Tuple(vec![host.input(), Value::integer(Integer::from_i64(0))].into()),
                ).unwrap());
                let captured = host.request(fixture.capture, argument, &mut heap, &mut TypeWorkBudget::unbounded()).unwrap();
                let (_, capture) = constructor_fields(&captured, &heap).unwrap();
                let (_, fragment) = constructor_fields(capture.unwrap(), &heap).unwrap();
                let fragment = fragment.unwrap().clone();
                assert_eq!(Arc::strong_count(&original), initial + 2);
                let syntax = host.request(fixture.unwrap, fragment, &mut heap, &mut TypeWorkBudget::unbounded()).unwrap();
                eprintln!("actual capture and declaration_syntax unwrap completed at depth 128");
                let expanded = Value::Location(allocate_heap(
                    &mut heap,
                    HeapCell::Constructor(fixture.constructors["Expanded"], Some(syntax)),
                ).unwrap());
                let TransformerOutput::Expanded(output) = host.transfer(&expanded, &heap, &mut TypeWorkBudget::unbounded()).unwrap() else {
                    panic!("the host transfers owned syntax");
                };
                let mut nodes = output.as_slice();
                for _ in 0..125 {
                    let [MacroOutputNode::Group(_, children, _)] = nodes else { panic!("group retained") };
                    nodes = children;
                }
                assert!(matches!(nodes, [MacroOutputNode::Identifier(name, _)] if name.diagnostic.is_some()));
                eprintln!("actual host transfer completed with depth-128 metadata");
                drop(host);
                drop(heap);
                assert_eq!(Arc::strong_count(&original), initial);
                drop(captures);
                drop(original);
                assert!(weak.upgrade().is_some(), "the transferred output owns its origin inputs");
                drop(output);
                assert!(weak.upgrade().is_none(), "the final output owner released the origin inputs");
                eprintln!("host, capture, output and final aliased origin owner dropped on 512 KiB");

                let (too_deep, weak) = packet(126);
                let captures = [SurfaceSyntaxCapture::Declaration(SurfaceDeclarationCapture {
                    contents: Arc::clone(&too_deep),
                })];
                let before = Arc::strong_count(&too_deep);
                let mut budget = SyntaxBudget::default();
                assert!(matches!(fixture.host(&captures, &mut budget),
                    Err(RuntimeFailure::Report(report))
                        if report.primary.reason_code() == "internal.resource.structural-depth"
                            && report.primary.resource().is_none()));
                assert_eq!(Arc::strong_count(&too_deep), before);
                eprintln!("depth-129 composed declaration refused before host retention");
                drop(captures);
                drop(too_deep);
                assert!(weak.upgrade().is_none());
                eprintln!("refused declaration and final aliased origin owner dropped on 512 KiB");
            })
            .unwrap()
            .join()
            .unwrap();
    }

    #[test]
    fn declaration_host_component_charges_each_phase_and_resumes_staging() {
        use super::{HeapCell, RuntimeFailure, Value, allocate_heap, constructor_fields};
        use crate::{
            integer::Integer,
            lexer::TokenKind,
            parser::{MacroParseFailure, parse_declaration_template_admission},
            source::ByteRange,
            surface::{SurfaceDeclarationCapture, SurfaceSyntaxCapture},
            syntax::{MacroOutputNode, TransformerOutput},
            syntax_resource::{ResourceFailure, SyntaxBudget},
            types::TypeWorkBudget,
        };
        use std::sync::Arc;

        #[derive(Debug)]
        enum Failure {
            Host(&'static str, RuntimeFailure),
            Parse(MacroParseFailure),
        }

        fn run(
            fixture: &DeclarationHostFixture,
            captures: &[SurfaceSyntaxCapture],
            limit: usize,
        ) -> (Result<[usize; 5], Failure>, usize) {
            let mut budget = SyntaxBudget::with_limit(limit);
            budget.charge_units(17).unwrap();
            let result = (|| {
                let mut host = fixture
                    .host(captures, &mut budget)
                    .map_err(|e| Failure::Host("constructor", e))?;
                let mut phases = [0; 5];
                phases[0] = host.syntax_work.as_ref().unwrap().consumed();
                let mut heap = Vec::new();
                let argument = Value::Location(
                    allocate_heap(
                        &mut heap,
                        HeapCell::Tuple(
                            vec![host.input(), Value::integer(Integer::from_i64(0))].into(),
                        ),
                    )
                    .unwrap(),
                );
                let captured = host
                    .request(
                        fixture.capture,
                        argument,
                        &mut heap,
                        &mut TypeWorkBudget::unbounded(),
                    )
                    .map_err(|e| Failure::Host("capture", e))?;
                phases[1] = host.syntax_work.as_ref().unwrap().consumed();
                let (_, capture) = constructor_fields(&captured, &heap).unwrap();
                let (_, fragment) = constructor_fields(capture.unwrap(), &heap).unwrap();
                let syntax = host
                    .request(
                        fixture.unwrap,
                        fragment.unwrap().clone(),
                        &mut heap,
                        &mut TypeWorkBudget::unbounded(),
                    )
                    .map_err(|e| Failure::Host("unwrap", e))?;
                phases[2] = host.syntax_work.as_ref().unwrap().consumed();
                let result = Value::Location(
                    allocate_heap(
                        &mut heap,
                        HeapCell::Constructor(fixture.constructors["Expanded"], Some(syntax)),
                    )
                    .unwrap(),
                );
                let TransformerOutput::Expanded(output) = host
                    .transfer(&result, &heap, &mut TypeWorkBudget::unbounded())
                    .map_err(|e| Failure::Host("transfer", e))?
                else {
                    panic!("expanded output")
                };
                phases[3] = host.syntax_work.as_ref().unwrap().consumed();
                drop(host);
                drop(heap);
                parse_declaration_template_admission(
                    &fixture.source,
                    fixture.caller.span,
                    output,
                    &fixture.contexts,
                    &[],
                    &mut budget,
                )
                .map_err(Failure::Parse)?;
                phases[4] = budget.consumed();
                Ok(phases)
            })();
            (result, budget.consumed())
        }

        let fixture = DeclarationHostFixture::new();
        let span = |start, end| {
            fixture
                .source
                .span(ByteRange::new(start, end).unwrap())
                .unwrap()
        };
        let mut second = fixture.caller.clone();
        second.span = span(12, 16);
        let original: Arc<[MacroOutputNode]> = Arc::from([
            MacroOutputNode::Token(TokenKind::Type, Arc::from("type"), span(0, 4).into()),
            MacroOutputNode::Identifier(fixture.caller.clone(), span(5, 9).into()),
            MacroOutputNode::Token(TokenKind::Equal, Arc::from("="), span(10, 11).into()),
            MacroOutputNode::Identifier(second, span(12, 16).into()),
            MacroOutputNode::Token(TokenKind::LineEnd, Arc::from("\n"), span(16, 17).into()),
        ]);
        let captures = [SurfaceSyntaxCapture::Declaration(
            SurfaceDeclarationCapture {
                contents: Arc::clone(&original),
            },
        )];
        let retained = Arc::strong_count(&original);
        let (measured, total) = run(
            &fixture,
            &captures,
            crate::syntax_resource::SYNTAX_WORK_LIMIT,
        );
        let measured = measured.unwrap();
        assert_eq!(total, measured[4]);
        assert!(measured.windows(2).all(|phase| phase[0] < phase[1]));
        let mut refusals = Vec::new();
        for (index, phase) in ["constructor", "capture", "unwrap", "transfer", "parse"]
            .iter()
            .enumerate()
        {
            let limit = measured[index] - 1;
            let (failure, paid) = run(&fixture, &captures, limit);
            let failure = failure.expect_err("the reached phase is one unit short");
            let prefix = if index == 0 { 17 } else { measured[index - 1] };
            assert!(
                paid >= prefix && paid <= limit,
                "{phase}: paid {paid}, prefix {prefix}, limit {limit}"
            );
            if *phase == "parse" {
                assert!(
                    paid > prefix,
                    "the late refusal retained additional staging work"
                );
            }
            refusals.push((*phase, prefix, paid, limit));
            match (phase, failure) {
                (
                    &"parse",
                    Failure::Parse(MacroParseFailure::Syntax {
                        resource: Some(ResourceFailure::SyntaxWork { limit: seen }),
                        ..
                    }),
                ) => assert_eq!(seen, limit),
                (_, Failure::Host(seen, RuntimeFailure::Report(report))) => {
                    assert_eq!(seen, *phase);
                    assert_eq!(
                        report.primary.reason_code(),
                        "internal.resource.syntax-work"
                    );
                    assert!(report.primary.resource().is_none());
                }
                (_, failure) => panic!("unexpected {phase} failure: {failure:?}"),
            }
            assert_eq!(Arc::strong_count(&original), retained);
        }
        let (exact, paid) = run(&fixture, &captures, measured[4]);
        let exact = exact.unwrap();
        assert_eq!(paid, measured[4]);
        assert_eq!(exact, measured);
        let (retry, paid) = run(&fixture, &captures, measured[4]);
        let retry = retry.unwrap();
        assert_eq!(paid, measured[4]);
        assert_eq!(retry, measured);
        assert_eq!(Arc::strong_count(&original), retained);
        eprintln!(
            "component pre-spent 17; phase totals {measured:?}; refused (phase, prefix, paid, limit) {refusals:?}; exact and retry"
        );
    }

    #[test]
    fn declaration_host_refuses_foreign_handles_and_protected_bridges_before_copy() {
        use super::{HeapCell, RuntimeFailure, Value, allocate_heap, constructor_fields};
        use crate::{
            eval::value::CompilerSyntaxHandleKind,
            integer::Integer,
            surface::{
                SurfaceDeclarationCapture, SurfaceExpr, SurfaceExprKind, SurfaceExpressionCapture,
                SurfacePattern, SurfacePatternCapture, SurfacePatternKind, SurfaceSyntaxCapture,
                SurfaceType, SurfaceTypeCapture, SurfaceTypeKind,
            },
            syntax::{MacroOrigin, MacroOutputNode},
            syntax_resource::SyntaxBudget,
            types::TypeWorkBudget,
        };
        use std::sync::Arc;

        let fixture = DeclarationHostFixture::new();
        let span = fixture.caller.span;
        let nested: Arc<[MacroOutputNode]> = Arc::from([]);
        let expression = SurfaceExpressionCapture {
            expression: SurfaceExpr {
                kind: SurfaceExprKind::Unit,
                span,
                diagnostic: None,
            },
            contents: Arc::clone(&nested),
        };
        let unsupported = [
            SurfaceSyntaxCapture::Expression(expression.clone()),
            SurfaceSyntaxCapture::Type(SurfaceTypeCapture {
                ty: SurfaceType {
                    kind: SurfaceTypeKind::Int,
                    span,
                    diagnostic: None,
                },
                contents: Arc::clone(&nested),
            }),
            SurfaceSyntaxCapture::Pattern(SurfacePatternCapture {
                pattern: SurfacePattern {
                    kind: SurfacePatternKind::Wildcard,
                    span,
                    diagnostic: None,
                },
                contents: Arc::clone(&nested),
            }),
        ];
        let before = Arc::strong_count(&nested);
        for capture in &unsupported {
            let mut budget = SyntaxBudget::default();
            assert!(matches!(
                fixture.host(std::slice::from_ref(capture), &mut budget),
                Err(RuntimeFailure::InvalidControlState)
            ));
            assert_eq!(Arc::strong_count(&nested), before);
        }
        let nested_packet: Arc<[MacroOutputNode]> =
            Arc::from([MacroOutputNode::Expression(expression, span.into())]);
        let invalid = [SurfaceSyntaxCapture::Declaration(
            SurfaceDeclarationCapture {
                contents: Arc::clone(&nested_packet),
            },
        )];
        let retained = Arc::strong_count(&nested_packet);
        let mut budget = SyntaxBudget::default();
        assert!(matches!(
            fixture.host(&invalid, &mut budget),
            Err(RuntimeFailure::InvalidControlState)
        ));
        assert_eq!(Arc::strong_count(&nested_packet), retained);
        assert_eq!(Arc::strong_count(&nested), before);

        let contents: Arc<[MacroOutputNode]> = Arc::from([]);
        let captures = [SurfaceSyntaxCapture::Declaration(
            SurfaceDeclarationCapture {
                contents: Arc::clone(&contents),
            },
        )];
        let mut budget = SyntaxBudget::default();
        let mut host = fixture.host(&captures, &mut budget).unwrap();
        let mut heap = Vec::new();
        let argument = Value::Location(
            allocate_heap(
                &mut heap,
                HeapCell::Tuple(vec![host.input(), Value::integer(Integer::from_i64(0))].into()),
            )
            .unwrap(),
        );
        let captured = host
            .request(
                fixture.capture,
                argument,
                &mut heap,
                &mut TypeWorkBudget::unbounded(),
            )
            .unwrap();
        let (_, capture) = constructor_fields(&captured, &heap).unwrap();
        let (_, fragment) = constructor_fields(capture.unwrap(), &heap).unwrap();
        let fragment = fragment.unwrap().clone();
        let mut other_budget = SyntaxBudget::default();
        let other = fixture.host(&captures, &mut other_budget).unwrap();
        let foreign = other.handle(CompilerSyntaxHandleKind::Declaration(0));
        let stale = {
            let mut stale_budget = SyntaxBudget::default();
            let stale_host = fixture.host(&captures, &mut stale_budget).unwrap();
            stale_host.handle(CompilerSyntaxHandleKind::Declaration(0))
        };
        let retained = Arc::strong_count(&contents);
        for invalid in [
            foreign,
            stale,
            host.input(),
            host.handle(CompilerSyntaxHandleKind::Declaration(999)),
        ] {
            assert!(matches!(
                host.request(
                    fixture.unwrap,
                    invalid,
                    &mut heap,
                    &mut TypeWorkBudget::unbounded()
                ),
                Err(RuntimeFailure::InvalidControlState)
            ));
            assert_eq!(Arc::strong_count(&contents), retained);
        }
        let syntax = host
            .request(
                fixture.unwrap,
                fragment.clone(),
                &mut heap,
                &mut TypeWorkBudget::unbounded(),
            )
            .unwrap();
        host.request(
            fixture.unwrap,
            fragment,
            &mut heap,
            &mut TypeWorkBudget::unbounded(),
        )
        .unwrap();
        assert_eq!(Arc::strong_count(&contents), retained);
        let bridge = Value::Location(
            allocate_heap(
                &mut heap,
                HeapCell::Tuple(vec![host.input(), syntax].into()),
            )
            .unwrap(),
        );
        let heap_before = heap.len();
        let paid_before = host.syntax_work.as_ref().unwrap().consumed();
        let expressions_before = host.expressions.len();
        let failures_before = host.parse_failures.len();
        assert!(matches!(
            host.request(
                fixture.parse_expression,
                bridge,
                &mut heap,
                &mut TypeWorkBudget::unbounded()
            ),
            Err(RuntimeFailure::InvalidControlState)
        ));
        assert_eq!(heap.len(), heap_before);
        assert_eq!(
            host.syntax_work.as_ref().unwrap().consumed() - paid_before,
            1 + "parse_expression".len()
        );
        assert_eq!(host.expressions.len(), expressions_before);
        assert_eq!(host.parse_failures.len(), failures_before);
        // This valid indexed expression is deliberately seeded only for the
        // component guard check; it is not admitted on the declaration route.
        host.expressions.push(SurfaceExpressionCapture {
            expression: SurfaceExpr {
                kind: SurfaceExprKind::Unit,
                span,
                diagnostic: None,
            },
            contents: Arc::clone(&nested),
        });
        let nested_retained = Arc::strong_count(&nested);
        let paid_before = host.syntax_work.as_ref().unwrap().consumed();
        assert!(matches!(
            host.request(
                fixture.expression_syntax,
                host.handle(CompilerSyntaxHandleKind::Expression(0)),
                &mut heap,
                &mut TypeWorkBudget::unbounded()
            ),
            Err(RuntimeFailure::InvalidControlState)
        ));
        assert_eq!(
            host.syntax_work.as_ref().unwrap().consumed() - paid_before,
            1 + "expression_syntax".len()
        );
        assert_eq!(Arc::strong_count(&nested), nested_retained);

        let combined =
            MacroOrigin::combined(vec![span.into()], Arc::clone(&fixture.frame)).unwrap();
        let MacroOrigin::Combined { inputs, .. } = &combined else {
            unreachable!()
        };
        let origin = host.issue_origin(combined.clone()).unwrap();
        let retained = Arc::strong_count(inputs);
        for protected in [
            "ExpressionNode",
            "TypeNode",
            "PatternNode",
            "DeclarationNode",
        ] {
            let fields = Value::Location(
                allocate_heap(
                    &mut heap,
                    HeapCell::Tuple(vec![Value::Unit, origin.clone()].into()),
                )
                .unwrap(),
            );
            let node = Value::Location(
                allocate_heap(
                    &mut heap,
                    HeapCell::Constructor(fixture.constructors[protected], Some(fields)),
                )
                .unwrap(),
            );
            let empty = Value::Location(
                allocate_heap(
                    &mut heap,
                    HeapCell::Constructor(fixture.constructors["NoNodes"], None),
                )
                .unwrap(),
            );
            let pair = Value::Location(
                allocate_heap(&mut heap, HeapCell::Tuple(vec![node, empty].into())).unwrap(),
            );
            let nodes = Value::Location(
                allocate_heap(
                    &mut heap,
                    HeapCell::Constructor(fixture.constructors["MoreNodes"], Some(pair)),
                )
                .unwrap(),
            );
            let syntax = Value::Location(
                allocate_heap(
                    &mut heap,
                    HeapCell::Constructor(fixture.constructors["Syntax"], Some(nodes)),
                )
                .unwrap(),
            );
            let paid_before = host.syntax_work.as_ref().unwrap().consumed();
            assert!(matches!(
                host.transfer_syntax(&syntax, &heap, 0),
                Err(RuntimeFailure::InvalidControlState)
            ));
            assert_eq!(
                host.syntax_work.as_ref().unwrap().consumed() - paid_before,
                5,
                "{protected}: loop and tag check precede origin copy"
            );
            assert_eq!(Arc::strong_count(inputs), retained);
        }
        eprintln!(
            "Some-route protected carriers and bridges refused before copy; foreign/stale/wrong handles refused; valid handle remains reusable"
        );
    }

    #[test]
    fn declaration_scalar_reservation_grows_with_real_payloads() {
        use crate::syntax_resource::SyntaxBudget;

        for spelling in [
            ("\"a\"".to_owned(), format!("\"{}\"", "a".repeat(120))),
            ("9".to_owned(), "9".repeat(120)),
        ] {
            let mut small = SyntaxBudget::default();
            assert!(
                scalar_host(&mut small)
                    .single_token(&spelling.0)
                    .unwrap()
                    .is_some()
            );
            let mut large = SyntaxBudget::default();
            assert!(
                scalar_host(&mut large)
                    .single_token(&spelling.1)
                    .unwrap()
                    .is_some()
            );
            assert!(large.consumed() > small.consumed());
        }
    }

    #[test]
    fn declaration_scalar_diagnostic_bound_tracks_the_lexer() {
        use crate::{
            lexer::{LexReason, lex},
            source::SourceFile,
            syntax_resource::SyntaxBudget,
        };
        // The lexer currently has no emitting branch for InvalidIdentifier or
        // NegativeLiteral. Revisit these minima when scanner progress or
        // diagnostic emission changes; a new reason must update this match.
        let minimum_span = |reason| match reason {
            LexReason::BareCarriageReturn
            | LexReason::UnterminatedString
            | LexReason::UnknownCharacter => 1,
            LexReason::UnicodeIdentifier
            | LexReason::Comment
            | LexReason::NegativeLiteral
            | LexReason::InvalidIntegerLiteral
            | LexReason::InvalidIdentifier => 2,
            LexReason::ByteOrderMark | LexReason::InvalidStringCharacter => 3,
            LexReason::InvalidStringEscape => 4,
        };
        for (spelling, reason) in [
            ("\r", LexReason::BareCarriageReturn),
            ("\u{feff}", LexReason::ByteOrderMark),
            ("λ", LexReason::UnicodeIdentifier),
            ("//", LexReason::Comment),
            ("01", LexReason::InvalidIntegerLiteral),
            ("\"\\z\"", LexReason::InvalidStringEscape),
            ("\"", LexReason::UnterminatedString),
            ("\"\n\"", LexReason::InvalidStringCharacter),
            ("?", LexReason::UnknownCharacter),
        ] {
            let source = SourceFile::new("lex-bound.ash", spelling).unwrap();
            let lexed = lex(&source).unwrap();
            let [diagnostic] = lexed.diagnostics.as_slice() else {
                panic!("one diagnostic for {spelling:?}");
            };
            assert_eq!(diagnostic.reason, reason);
            let range = diagnostic.primary.span().range();
            let span_bytes = usize::try_from(range.end() - range.start()).unwrap();
            assert!(span_bytes >= minimum_span(reason));
            let retained_text = diagnostic.primary.message().len()
                + diagnostic.expected.as_ref().map_or(0, String::len);
            assert!(retained_text <= super::SCALAR_DIAGNOSTIC_TEXT_PER_BYTE * minimum_span(reason));
            assert!(diagnostic.found.as_ref().unwrap().len() <= span_bytes);
            if reason == LexReason::BareCarriageReturn {
                assert_eq!(retained_text, super::SCALAR_DIAGNOSTIC_TEXT_PER_BYTE);
            }
            let mut budget = SyntaxBudget::default();
            assert!(
                scalar_host(&mut budget)
                    .single_token(spelling)
                    .unwrap()
                    .is_none()
            );
        }
        let repeated = "\r".repeat(8);
        let source = SourceFile::new("lex-bound.ash", repeated.clone()).unwrap();
        let diagnostics = lex(&source).unwrap().diagnostics;
        assert_eq!(diagnostics.len(), repeated.len());
        assert_eq!(
            diagnostics
                .iter()
                .map(|diagnostic| diagnostic.primary.message().len()
                    + diagnostic.expected.as_ref().map_or(0, String::len))
                .sum::<usize>(),
            super::SCALAR_DIAGNOSTIC_TEXT_PER_BYTE * repeated.len()
        );
        eprintln!(
            "CR reaches 64 bytes; quote, Unicode and other reachable diagnostic text stays bounded"
        );
    }

    #[test]
    fn d5_host_refuses_declaration_before_its_constructor_and_request_clone() {
        use super::{HeapCell, RuntimeFailure, SyntaxHost, Value, allocate_heap};
        use crate::{
            core::{EffectCoreBuilder, validate::ValidatedMacroEntry, validate_effect},
            integer::Integer,
            module::ModuleId,
            resolved::{
                BinderId, ResolvedEffectDeclaration, ResolvedEffectOperation, ResolvedRegistry,
                ResolvedType, ResolvedTypeProvenance, ResolvedTypeProvenanceNode,
            },
            source::{ByteRange, Origin, SourceFile},
            surface::{
                SurfaceDeclarationCapture, SurfaceExpr, SurfaceExprKind, SurfaceExpressionCapture,
                SurfaceName, SurfaceSyntaxCapture,
            },
            syntax::{ExpansionFrame, MacroOutputNode, SyntaxContexts},
            types::{EffectId, OperationId, Type, TypeWorkBudget},
        };
        use std::{collections::HashMap, sync::Arc};

        std::thread::Builder::new()
            .stack_size(512 * 1024)
            .spawn(|| {
                let source = SourceFile::new("host.ash", "name").unwrap();
                let span = source.span(ByteRange::new(0, 4).unwrap()).unwrap();
                let module = ModuleId::new(0);
                let ops = EffectId::new(module, 0);
                let operation = OperationId::new(ops, 0);
                let registry =
                    ResolvedRegistry::default().with_effects(vec![ResolvedEffectDeclaration {
                        id: ops,
                        public: false,
                        spelling: "Ops".into(),
                        parameters: Box::new([]),
                        operations: Box::new([ResolvedEffectOperation {
                            id: operation,
                            spelling: "capture".into(),
                            annotation: ResolvedType {
                                ty: Type::Function(Box::new(Type::Unit), Box::new(Type::Unit)),
                                provenance: ResolvedTypeProvenance::new(
                                    vec![ResolvedTypeProvenanceNode::Fact(span)],
                                    0,
                                ),
                                origin: Origin::Source(span),
                                span,
                            },
                            origin: Origin::Source(span),
                            span,
                        }]),
                        native_contract: None,
                        origin: Origin::Source(span),
                        span,
                    }]);
                let mut builder = EffectCoreBuilder::with_effect_registry(Arc::new(registry));
                let occurrence = builder.unit(Type::Unit, Origin::Source(span)).unwrap();
                let program =
                    validate_effect(builder.finish(occurrence).unwrap(), &[&source]).unwrap();
                let entry = ValidatedMacroEntry {
                    program,
                    occurrence,
                    binder: BinderId::new(0),
                    syntax_module: module,
                    ops,
                };
                let name = SurfaceName {
                    text: "name".into(),
                    span,
                    introduction: 0,
                    introduced_at: None,
                    written: true,
                    diagnostic: None,
                };
                let frame = Arc::new(ExpansionFrame {
                    invocation: span,
                    definition: span,
                });
                let contexts = Arc::new(SyntaxContexts::new(&[], &[], &[]));
                let mut expression = SurfaceExpr {
                    kind: SurfaceExprKind::Unit,
                    span,
                    diagnostic: None,
                };
                for _ in 0..48 {
                    expression = SurfaceExpr {
                        kind: SurfaceExprKind::Resume(Box::new(expression)),
                        span,
                        diagnostic: None,
                    };
                }
                let supported = SurfaceSyntaxCapture::Expression(SurfaceExpressionCapture {
                    expression,
                    contents: Arc::from([]),
                });
                let contents: Arc<[MacroOutputNode]> = Arc::from([]);
                let declaration = SurfaceSyntaxCapture::Declaration(SurfaceDeclarationCapture {
                    contents: Arc::clone(&contents),
                });
                let captures = vec![supported, declaration];
                let retained = Arc::strong_count(&contents);
                let host = SyntaxHost::new(
                    &entry,
                    &captures[..1],
                    &source,
                    &name,
                    0,
                    Arc::clone(&contexts),
                    Arc::clone(&frame),
                    None,
                )
                .expect("the same entry constructs a host with the supported nested expression");
                eprintln!("D5 host nested-prefix constructed on 512 KiB");
                drop(host);
                eprintln!("D5 host nested-prefix dropped on 512 KiB");
                for slice in [&captures[1..], &captures[..]] {
                    assert!(matches!(
                        SyntaxHost::new(
                            &entry,
                            slice,
                            &source,
                            &name,
                            0,
                            Arc::clone(&contexts),
                            Arc::clone(&frame),
                            None,
                        ),
                        Err(RuntimeFailure::InvalidControlState)
                    ));
                }
                eprintln!("D5 host late Declaration refused and prefix dropped on 512 KiB");
                assert_eq!(Arc::strong_count(&contents), retained);

                // Constructor admission makes this state unreachable in the ordinary host.
                let captures = vec![captures.into_iter().last().unwrap()];
                let mut host = SyntaxHost {
                    occurrence,
                    binder: BinderId::new(0),
                    ops,
                    started: false,
                    steps_left: 100,
                    invocation: Arc::new(()),
                    frame,
                    source,
                    caller: name,
                    introduction: 0,
                    contexts,
                    syntax_work: None,
                    fresh_count: 0,
                    captures,
                    expressions: Vec::new(),
                    declarations: Vec::new(),
                    identifiers: Vec::new(),
                    origins: Vec::new(),
                    parse_failures: Vec::new(),
                    tokens: Vec::new(),
                    constructors: HashMap::new(),
                    operations: [(operation, "capture".into())].into_iter().collect(),
                };
                let input = host.input();
                let mut heap = Vec::new();
                let fields = vec![input, Value::integer(Integer::from_i64(0))].into_boxed_slice();
                let argument =
                    Value::Location(allocate_heap(&mut heap, HeapCell::Tuple(fields)).unwrap());
                assert!(matches!(
                    host.request(
                        operation,
                        argument,
                        &mut heap,
                        &mut TypeWorkBudget::unbounded()
                    ),
                    Err(RuntimeFailure::InvalidControlState)
                ));
            })
            .unwrap()
            .join()
            .unwrap();
    }

    #[test]
    fn syntax_host_checks_invocation_and_nominal_identity() {
        use super::{
            HeapCell, RuntimeFailure, SyntaxHost, Value, allocate_heap, constructor_fields,
        };
        use crate::{
            core::CoreBuilder,
            eval::value::CompilerSyntaxHandleKind,
            integer::Integer,
            lexer::TokenKind,
            module::ModuleId,
            resolved::BinderId,
            source::{ByteRange, Origin, SourceFile},
            surface::{
                SurfaceExpr, SurfaceExprKind, SurfaceExpressionCapture, SurfaceIdentifierCapture,
                SurfaceName, SurfacePattern, SurfacePatternCapture, SurfacePatternKind,
                SurfaceReference, SurfaceSyntaxCapture, SurfaceType, SurfaceTypeCapture,
                SurfaceTypeKind,
            },
            syntax::{
                ExpansionFrame, MacroDelimiter, MacroOrigin, MacroOutputNode, SyntaxContexts,
                TransformerOutput,
            },
            types::{ConstructorId, EffectId, NominalTypeId, OperationId, Type, TypeWorkBudget},
        };
        use std::{collections::HashMap, sync::Arc};

        let source = SourceFile::new("syntax-host.ash", "name").unwrap();
        let span = source.span(ByteRange::new(0, 4).unwrap()).unwrap();
        let occurrence = CoreBuilder::new()
            .unit(Type::Unit, Origin::Source(span))
            .unwrap();
        let module = ModuleId::new(0);
        let ops = EffectId::new(module, 0);
        let capture = OperationId::new(ops, 0);
        let fresh_identifier = OperationId::new(ops, 1);
        let expression_syntax = OperationId::new(ops, 2);
        let owner = NominalTypeId::new(module, 0);
        let constructors: HashMap<String, ConstructorId> = [
            ("Captured".into(), ConstructorId::new(owner, 0)),
            ("IdentifierCapture".into(), ConstructorId::new(owner, 1)),
            ("MissingCapture".into(), ConstructorId::new(owner, 2)),
            ("Expanded".into(), ConstructorId::new(owner, 3)),
            ("Rejected".into(), ConstructorId::new(owner, 4)),
            ("Syntax".into(), ConstructorId::new(owner, 5)),
            ("NoNodes".into(), ConstructorId::new(owner, 6)),
            ("ExpressionCapture".into(), ConstructorId::new(owner, 7)),
            ("MadeIdentifier".into(), ConstructorId::new(owner, 8)),
            ("MoreNodes".into(), ConstructorId::new(owner, 9)),
            ("GroupNode".into(), ConstructorId::new(owner, 10)),
            ("IdentifierNode".into(), ConstructorId::new(owner, 11)),
            ("TokenNode".into(), ConstructorId::new(owner, 12)),
            ("ExpressionNode".into(), ConstructorId::new(owner, 13)),
            ("Parentheses".into(), ConstructorId::new(owner, 14)),
        ]
        .into_iter()
        .collect();
        let name = SurfaceName {
            text: "name".into(),
            span,
            introduction: 0,
            introduced_at: None,
            written: true,
            diagnostic: None,
        };
        let make_host = || SyntaxHost {
            occurrence,
            binder: BinderId::new(0),
            ops,
            started: false,
            steps_left: 100,
            invocation: Arc::new(()),
            frame: Arc::new(ExpansionFrame {
                invocation: span,
                definition: span,
            }),
            source: source.clone(),
            caller: name.clone(),
            introduction: 0,
            contexts: Arc::new(SyntaxContexts::new(&[], &[], &[])),
            syntax_work: None,
            fresh_count: 0,
            captures: vec![SurfaceSyntaxCapture::Identifier(SurfaceIdentifierCapture {
                name: name.clone(),
                origin: span.into(),
            })],
            expressions: Vec::new(),
            declarations: Vec::new(),
            identifiers: Vec::new(),
            origins: Vec::new(),
            parse_failures: Vec::new(),
            tokens: Vec::new(),
            constructors: constructors.clone(),
            operations: [
                (capture, "capture".into()),
                (fresh_identifier, "fresh_identifier".into()),
                (expression_syntax, "expression_syntax".into()),
            ]
            .into_iter()
            .collect(),
        };
        let mut host = make_host();
        let mut foreign = make_host();
        let foreign_input = foreign.input();
        let stale_input = {
            let finished = make_host();
            finished.input()
        };
        let mut heap = Vec::new();
        let request = |host: &mut SyntaxHost, input, index, heap: &mut Vec<HeapCell>| {
            let fields = vec![input, Value::integer(Integer::from_i64(index))].into_boxed_slice();
            let argument = Value::Location(allocate_heap(heap, HeapCell::Tuple(fields)).unwrap());
            host.request(capture, argument, heap, &mut TypeWorkBudget::unbounded())
        };

        let mut unsupported = make_host();
        unsupported.captures = vec![
            SurfaceSyntaxCapture::Type(SurfaceTypeCapture {
                ty: SurfaceType {
                    kind: SurfaceTypeKind::Int,
                    span,
                    diagnostic: None,
                },
                contents: Arc::from([]),
            }),
            SurfaceSyntaxCapture::Pattern(SurfacePatternCapture {
                pattern: SurfacePattern {
                    kind: SurfacePatternKind::Wildcard,
                    span,
                    diagnostic: None,
                },
                contents: Arc::from([]),
            }),
        ];
        let unsupported_input = unsupported.input();
        for index in [0, 1] {
            assert!(matches!(
                request(
                    &mut unsupported,
                    unsupported_input.clone(),
                    index,
                    &mut heap
                ),
                Err(RuntimeFailure::InvalidControlState)
            ));
        }
        let [
            SurfaceSyntaxCapture::Type(ty),
            SurfaceSyntaxCapture::Pattern(pattern),
        ] = unsupported.captures.as_slice()
        else {
            panic!("expected the protected capture categories");
        };
        let forwarded = [
            MacroOutputNode::ForwardedType(ty.clone(), span.into()),
            MacroOutputNode::ForwardedPattern(pattern.clone(), span.into()),
        ];
        for node in forwarded {
            assert!(matches!(
                unsupported.syntax_value(&[node], &mut heap, 0),
                Err(RuntimeFailure::InvalidControlState)
            ));
        }

        let input = host.input();
        let captured = request(&mut host, input.clone(), 0, &mut heap).unwrap();
        let (tag, payload) = constructor_fields(&captured, &heap).unwrap();
        assert_eq!(tag, constructors["Captured"]);
        assert_eq!(
            constructor_fields(payload.unwrap(), &heap).unwrap().0,
            constructors["IdentifierCapture"]
        );
        let missing = request(&mut host, input, -1, &mut heap).unwrap();
        let (tag, payload) = constructor_fields(&missing, &heap).unwrap();
        assert_eq!(tag, constructors["MissingCapture"]);
        assert!(payload.is_none());
        for input in [foreign_input, stale_input] {
            assert!(matches!(
                request(&mut host, input, 0, &mut heap),
                Err(RuntimeFailure::InvalidControlState)
            ));
        }
        let nodes = host.construct(&mut heap, "NoNodes", None).unwrap();
        let syntax = host.construct(&mut heap, "Syntax", Some(nodes)).unwrap();
        let valid_result = host
            .construct(&mut heap, "Expanded", Some(syntax.clone()))
            .unwrap();
        assert!(matches!(
            host.transfer(&valid_result, &heap, &mut TypeWorkBudget::unbounded()),
            Ok(crate::syntax::TransformerOutput::Expanded(nodes)) if nodes.is_empty()
        ));
        let foreign_owner = NominalTypeId::new(ModuleId::new(1), 0);
        let foreign_expanded = ConstructorId::new(foreign_owner, 3);
        let foreign_result = Value::Location(
            allocate_heap(
                &mut heap,
                HeapCell::Constructor(foreign_expanded, Some(syntax)),
            )
            .unwrap(),
        );
        assert!(matches!(
            host.transfer(&foreign_result, &heap, &mut TypeWorkBudget::unbounded()),
            Err(RuntimeFailure::InvalidControlState)
        ));

        fn two_identifier_result(
            host: &mut SyntaxHost,
            heap: &mut Vec<HeapCell>,
            first: Value,
            second: Value,
            origin: Value,
        ) -> Value {
            let empty = host.construct(heap, "NoNodes", None).unwrap();
            let second_fields = Value::Location(
                allocate_heap(heap, HeapCell::Tuple(vec![second, origin.clone()].into())).unwrap(),
            );
            let second_node = host
                .construct(heap, "IdentifierNode", Some(second_fields))
                .unwrap();
            let second_pair = Value::Location(
                allocate_heap(heap, HeapCell::Tuple(vec![second_node, empty].into())).unwrap(),
            );
            let tail = host
                .construct(heap, "MoreNodes", Some(second_pair))
                .unwrap();
            let first_fields = Value::Location(
                allocate_heap(heap, HeapCell::Tuple(vec![first, origin].into())).unwrap(),
            );
            let first_node = host
                .construct(heap, "IdentifierNode", Some(first_fields))
                .unwrap();
            let first_pair = Value::Location(
                allocate_heap(heap, HeapCell::Tuple(vec![first_node, tail].into())).unwrap(),
            );
            let nodes = host.construct(heap, "MoreNodes", Some(first_pair)).unwrap();
            let syntax = host.construct(heap, "Syntax", Some(nodes)).unwrap();
            host.construct(heap, "Expanded", Some(syntax)).unwrap()
        }

        let foreign_input = foreign.input();
        let foreign_capture = request(&mut foreign, foreign_input, 0, &mut heap).unwrap();
        let (_, foreign_capture) = constructor_fields(&foreign_capture, &heap).unwrap();
        let (_, foreign_fields) = constructor_fields(foreign_capture.unwrap(), &heap).unwrap();
        let (foreign_identifier, _) = super::pair(foreign_fields.unwrap(), &heap).unwrap();
        let foreign_identifier = foreign_identifier.clone();
        let local_identifier = host.handle(CompilerSyntaxHandleKind::Identifier(0));
        assert!(matches!(
            host.admitted_handle(&local_identifier),
            Ok(CompilerSyntaxHandleKind::Identifier(0))
        ));
        assert!(matches!(
            foreign.admitted_handle(&foreign_identifier),
            Ok(CompilerSyntaxHandleKind::Identifier(0))
        ));
        assert_eq!(host.identifiers.len(), 1);
        assert_eq!(foreign.identifiers.len(), 1);
        let local_origin = host.issue_origin(span.into()).unwrap();
        let valid = two_identifier_result(
            &mut host,
            &mut heap,
            local_identifier.clone(),
            local_identifier.clone(),
            local_origin.clone(),
        );
        let TransformerOutput::Expanded(valid_output) = host
            .transfer(&valid, &heap, &mut TypeWorkBudget::unbounded())
            .unwrap()
        else {
            panic!("the local identifier output should transfer");
        };
        assert_eq!(
            valid_output,
            vec![
                MacroOutputNode::Identifier(name.clone(), span.into()),
                MacroOutputNode::Identifier(name.clone(), span.into()),
            ]
        );
        let foreign_result = two_identifier_result(
            &mut host,
            &mut heap,
            local_identifier,
            foreign_identifier,
            local_origin,
        );
        assert!(matches!(
            host.transfer(&foreign_result, &heap, &mut TypeWorkBudget::unbounded()),
            Err(RuntimeFailure::InvalidControlState)
        ));

        // Unwrapping exposes the captured outer contents, while preserving
        // nested fragments, their contexts and their complete origin trees.
        let first = source.span(ByteRange::new(0, 1).unwrap()).unwrap();
        let second = source.span(ByteRange::new(1, 4).unwrap()).unwrap();
        let combined =
            MacroOrigin::combined(vec![first.into(), second.into()], Arc::clone(&host.frame))
                .unwrap();
        let origin = host.issue_origin(combined.clone()).unwrap();
        let fields = Value::Location(
            allocate_heap(
                &mut heap,
                HeapCell::Tuple(
                    vec![host.input(), Value::String(Arc::from("name")), origin].into(),
                ),
            )
            .unwrap(),
        );
        let made = host
            .request(
                fresh_identifier,
                fields,
                &mut heap,
                &mut TypeWorkBudget::unbounded(),
            )
            .unwrap();
        let (tag, identifier) = constructor_fields(&made, &heap).unwrap();
        assert_eq!(tag, constructors["MadeIdentifier"]);
        let CompilerSyntaxHandleKind::Identifier(index) =
            host.admitted_handle(identifier.unwrap()).unwrap()
        else {
            panic!("fresh identifier handle")
        };
        let introduced = host.identifiers[index].clone();
        assert_eq!(introduced.text, name.text);
        assert_ne!(introduced.introduction, name.introduction);
        assert!(!introduced.written && name.written);

        let expression = SurfaceExpr {
            kind: SurfaceExprKind::Name(SurfaceReference::Unqualified(name.clone())),
            span,
            diagnostic: None,
        };
        let protected = SurfaceExpressionCapture {
            expression,
            contents: vec![MacroOutputNode::Identifier(name.clone(), combined.clone())].into(),
        };
        let protected_contents = Arc::clone(&protected.contents);
        let contents = vec![MacroOutputNode::Group(
            MacroDelimiter::Parentheses,
            vec![
                MacroOutputNode::Identifier(introduced, combined.clone()),
                MacroOutputNode::Token(TokenKind::Plus, Arc::from("+"), first.into()),
                MacroOutputNode::Expression(protected, combined.clone()),
            ],
            combined,
        )];
        let expression = crate::syntax::admit_transformer_output(
            &source,
            contents.clone(),
            &host.contexts,
            &host.frame,
        )
        .expect("the mixed captured syntax is an expression");
        let original = SurfaceExpressionCapture {
            expression,
            contents: contents.into(),
        };
        host.captures
            .push(SurfaceSyntaxCapture::Expression(original.clone()));
        let input = host.input();
        let capture = request(&mut host, input, 1, &mut heap).unwrap();
        let (tag, capture) = constructor_fields(&capture, &heap).unwrap();
        assert_eq!(tag, constructors["Captured"]);
        let (tag, fragment) = constructor_fields(capture.unwrap(), &heap).unwrap();
        assert_eq!(tag, constructors["ExpressionCapture"]);
        let fragment = fragment.unwrap().clone();
        let CompilerSyntaxHandleKind::Expression(index) = host.admitted_handle(&fragment).unwrap()
        else {
            panic!("captured expression handle")
        };
        assert!(Arc::ptr_eq(
            &host.expressions[index].contents,
            &original.contents
        ));
        let syntax = host
            .request(
                expression_syntax,
                fragment,
                &mut heap,
                &mut TypeWorkBudget::unbounded(),
            )
            .unwrap();
        let result = host.construct(&mut heap, "Expanded", Some(syntax)).unwrap();
        let TransformerOutput::Expanded(output) = host
            .transfer(&result, &heap, &mut TypeWorkBudget::unbounded())
            .unwrap()
        else {
            panic!("expanded syntax")
        };
        assert_eq!(output.as_slice(), original.contents.as_ref());
        let [MacroOutputNode::Group(_, children, MacroOrigin::Combined { frame, .. })] =
            output.as_slice()
        else {
            panic!("the group and combined origin survive")
        };
        assert!(Arc::ptr_eq(frame, &host.frame));
        let MacroOutputNode::Expression(nested, _) = &children[2] else {
            panic!("the nested expression stays protected")
        };
        assert!(Arc::ptr_eq(&nested.contents, &protected_contents));
        let SurfaceSyntaxCapture::Expression(retained) = &host.captures[1] else {
            panic!("the original capture is retained")
        };
        assert!(Arc::ptr_eq(&retained.contents, &original.contents));
    }

    fn s3_overflow(entry: &str) -> crate::driver::FileFailure {
        use crate::{
            driver::{RunConfiguration, compile_path},
            module::ModuleRoots,
        };

        compile_path(RunConfiguration {
            entry: std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"))
                .join("tests/fixtures/surface-macros/s3-transfer")
                .join(entry),
            roots: ModuleRoots::empty(),
        })
        .expect_err("over-depth structured output must not be published")
    }

    #[test]
    fn s3_final_transfer_depth_failure_closes_the_host_root() {
        use super::super::machine_test_hooks as hooks;
        use crate::driver::PipelineFailure;

        hooks::reset();
        let failure = s3_overflow("entry_overflow.ash");
        let Some(PipelineFailure::SyntaxRuntime(error)) = failure.pipeline_failure() else {
            panic!("expected the final transfer failure: {failure:?}");
        };
        assert_eq!(error.cause().reason_code(), "runtime.resource-capacity");
        assert_eq!(hooks::TRANSFER_ATTEMPTS.get(), 1);
        assert_eq!(hooks::TRANSFER_FAILURES.get(), 1);
        assert_eq!(hooks::TRANSFER_GROUPS_COMPLETED.get(), 5);
        assert_eq!(hooks::ROOT_CLOSES.get(), 1);
        assert_eq!(hooks::ACTIVE_ROOT_DROPS.get(), 0);
        assert_eq!(hooks::TRANSFORMER_DROPS.get(), 1);
        hooks::reset();
    }

    #[test]
    fn s3_parse_service_depth_failure_disposes_the_active_host_root() {
        use super::super::machine_test_hooks as hooks;
        use crate::driver::PipelineFailure;

        hooks::reset();
        let failure = s3_overflow("entry_parse_overflow.ash");
        let Some(PipelineFailure::SyntaxRuntime(error)) = failure.pipeline_failure() else {
            panic!("expected the parse-service transfer failure: {failure:?}");
        };
        assert_eq!(error.cause().reason_code(), "runtime.resource-capacity");
        assert_eq!(hooks::TRANSFER_ATTEMPTS.get(), 0);
        assert_eq!(hooks::TRANSFER_FAILURES.get(), 0);
        assert_eq!(hooks::TRANSFER_GROUPS_COMPLETED.get(), 4);
        assert_eq!(hooks::ROOT_CLOSES.get(), 0);
        assert_eq!(hooks::ACTIVE_ROOT_DROPS.get(), 1);
        assert_eq!(hooks::TRANSFORMER_DROPS.get(), 1);
        hooks::reset();
    }

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
            ("SyntaxKeyword", "syntax"),
            ("Dollar", "$"),
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
            "", "name", "Name", "(", ")", "{", "}", ";", "01", "-1", " +", "+ ",
        ] {
            assert!(
                token_from_spelling(spelling).unwrap().is_none(),
                "{spelling:?}"
            );
        }
    }
}
