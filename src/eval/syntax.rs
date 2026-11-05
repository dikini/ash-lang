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
    source::Span,
    surface::SurfaceSyntaxCapture,
    syntax::MacroOutputNode,
    types::{ConstructorId, EffectId, OperationId, TypeWorkBudget},
};

#[derive(Debug)]
pub(super) struct SyntaxHost {
    pub(super) occurrence: NodeId,
    pub(super) binder: BinderId,
    pub(super) ops: EffectId,
    pub(super) started: bool,
    pub(super) steps_left: usize,
    invocation: Arc<()>,
    invocation_span: Span,
    captures: Vec<SurfaceSyntaxCapture>,
    tokens: Vec<TokenKind>,
    constructors: HashMap<String, ConstructorId>,
    operations: HashMap<OperationId, String>,
}

impl SyntaxHost {
    pub(super) fn new(
        entry: &ValidatedMacroEntry,
        captures: &[SurfaceSyntaxCapture],
        invocation_span: Span,
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
            captures: captures.to_vec(),
            tokens: Vec::new(),
            constructors,
            operations,
        })
    }

    pub(super) fn input(&self) -> Value {
        self.handle(CompilerSyntaxHandleKind::Input)
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
            .map(String::as_str)
            .ok_or(RuntimeFailure::InvalidControlState)?;
        match operation {
            "invocation_origin" => {
                if !matches!(
                    self.admitted_handle(&argument)?,
                    CompilerSyntaxHandleKind::Input
                ) {
                    return Err(RuntimeFailure::InvalidControlState);
                }
                Ok(self.handle(CompilerSyntaxHandleKind::Origin(self.invocation_span)))
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
                match index
                    .and_then(|index| self.captures.get(index).map(|capture| (index, capture)))
                {
                    Some((index, SurfaceSyntaxCapture::Expression(_))) => {
                        let fragment = self.handle(CompilerSyntaxHandleKind::Expression(index));
                        let capture = self.construct(heap, "ExpressionCapture", Some(fragment))?;
                        self.construct(heap, "Captured", Some(capture))
                    }
                    Some((_, SurfaceSyntaxCapture::Identifier(_))) => {
                        Err(RuntimeFailure::InvalidControlState)
                    }
                    None => self.construct(heap, "MissingCapture", None),
                }
            }
            "make_token" => {
                let (kind, spelling) = pair(&argument, heap)?;
                let (tag, payload) = constructor_fields(kind, heap)?;
                let (spelling, is_string) = borrowed_bytes(spelling, heap, work)?;
                let valid = tag == self.constructor("Plus")?
                    && payload.is_none()
                    && is_string
                    && spelling == b"+";
                if !valid {
                    return self.construct(heap, "InvalidToken", None);
                }
                let index = self.tokens.len();
                self.tokens.push(TokenKind::Plus);
                let token = self.handle(CompilerSyntaxHandleKind::Token(index));
                self.construct(heap, "MadeToken", Some(token))
            }
            _ => Err(RuntimeFailure::InvalidControlState),
        }
    }

    pub(super) fn transfer(
        &self,
        result: &Value,
        heap: &[HeapCell],
    ) -> Result<Vec<MacroOutputNode>, RuntimeFailure> {
        let (tag, syntax) = constructor_fields(result, heap)?;
        if tag != self.constructor("Expanded")? {
            return Err(RuntimeFailure::InvalidControlState);
        }
        let (tag, nodes) =
            constructor_fields(syntax.ok_or(RuntimeFailure::InvalidControlState)?, heap)?;
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
            let (value, origin) = pair(payload.ok_or(RuntimeFailure::InvalidControlState)?, heap)?;
            let CompilerSyntaxHandleKind::Origin(origin) = self.admitted_handle(origin)? else {
                return Err(RuntimeFailure::InvalidControlState);
            };
            if tag == self.constructor("ExpressionNode")? {
                let CompilerSyntaxHandleKind::Expression(index) = self.admitted_handle(value)?
                else {
                    return Err(RuntimeFailure::InvalidControlState);
                };
                let Some(SurfaceSyntaxCapture::Expression(expression)) = self.captures.get(index)
                else {
                    return Err(RuntimeFailure::InvalidControlState);
                };
                output.push(MacroOutputNode::Expression(expression.clone(), origin));
            } else if tag == self.constructor("TokenNode")? {
                let CompilerSyntaxHandleKind::Token(index) = self.admitted_handle(value)? else {
                    return Err(RuntimeFailure::InvalidControlState);
                };
                let token = self
                    .tokens
                    .get(index)
                    .ok_or(RuntimeFailure::InvalidControlState)?;
                output.push(MacroOutputNode::Token(token.clone(), origin));
            } else {
                return Err(RuntimeFailure::InvalidControlState);
            }
            nodes = rest;
        }
    }
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
