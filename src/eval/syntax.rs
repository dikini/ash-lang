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
        SurfaceDeclarationCapture, SurfaceExpressionCapture, SurfaceName, SurfacePatternCapture,
        SurfaceSyntaxCapture, SurfaceTypeCapture,
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

fn reserve_type_push<T>(
    values: &mut Vec<T>,
    budget: Option<&mut crate::syntax_resource::SyntaxBudget>,
    selected: bool,
) -> Result<(), RuntimeFailure> {
    let live = values.len();
    if selected && live == values.capacity() {
        let requested = live.saturating_add(1);
        budget
            .expect("selected Type accounting owns a budget")
            .charge_units(requested.saturating_add(live))
            .map_err(syntax_failure)?;
        values
            .try_reserve_exact(1)
            .map_err(|_| RuntimeFailure::HeapCapacity)?;
    }
    Ok(())
}

fn type_retention_failure(failure: crate::parser::MacroParseFailure) -> RuntimeFailure {
    match failure {
        crate::parser::MacroParseFailure::Syntax {
            resource: Some(failure),
            ..
        } => syntax_failure(failure),
        _ => RuntimeFailure::InvalidControlState,
    }
}

fn require_unbridged_charge(
    result: Result<Option<bool>, crate::syntax_resource::ResourceFailure>,
) -> Result<(), RuntimeFailure> {
    if result.map_err(syntax_failure)? == Some(false) {
        Ok(())
    } else {
        Err(RuntimeFailure::InvalidControlState)
    }
}

fn check_declaration_contents(
    contents: &[MacroOutputNode],
    budget: &mut crate::syntax_resource::SyntaxBudget,
) -> Result<(), RuntimeFailure> {
    check_declaration_contents_at(contents, 0, budget)
}

fn check_declaration_contents_at(
    contents: &[MacroOutputNode],
    prefix: usize,
    budget: &mut crate::syntax_resource::SyntaxBudget,
) -> Result<(), RuntimeFailure> {
    // The capture retains one Arc layer before any delimiter groups.
    let prefix = crate::syntax::type_depth(prefix, 1).map_err(syntax_failure)?;
    budget
        .charge_units(contents.len())
        .map_err(syntax_failure)?;
    let mut pending = contents
        .iter()
        .map(|node| (node, prefix))
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
                let live = pending.len();
                let requested = live.saturating_add(children.len());
                if requested > pending.capacity() {
                    budget
                        .charge_units(requested.saturating_add(live))
                        .map_err(syntax_failure)?;
                    pending.reserve_exact(children.len());
                }
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
    contexts: Option<Arc<SyntaxContexts>>,
    syntax_work: Option<&'inv mut crate::syntax_resource::SyntaxBudget>,
    quote_sites: Arc<[crate::syntax::PreparedQuoteSite]>,
    staged_owners: Option<&'inv mut Vec<crate::syntax::SyntaxOwner>>,
    type_accounting: bool,
    fresh_count: usize,
    captures: Vec<SurfaceSyntaxCapture>,
    expressions: Vec<SurfaceExpressionCapture>,
    declarations: Vec<SurfaceDeclarationCapture>,
    types: Vec<SurfaceTypeCapture>,
    patterns: Vec<SurfacePatternCapture>,
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
    #[cfg(test)]
    #[allow(clippy::too_many_arguments)]
    pub(super) fn new(
        entry: &ValidatedMacroEntry,
        captures: &[SurfaceSyntaxCapture],
        source: &SourceFile,
        caller: &SurfaceName,
        introduction: usize,
        contexts: Arc<SyntaxContexts>,
        frame: Arc<ExpansionFrame>,
        syntax_work: Option<&'inv mut crate::syntax_resource::SyntaxBudget>,
    ) -> Result<Self, RuntimeFailure> {
        let mut contexts = Some(contexts);
        Self::new_with_owners(
            entry,
            captures,
            source,
            caller,
            introduction,
            &mut contexts,
            frame,
            syntax_work,
            None,
        )
    }

    // Keep invocation inputs separate so their borrows and ownership stay explicit.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn new_with_owners(
        entry: &ValidatedMacroEntry,
        captures: &[SurfaceSyntaxCapture],
        source: &SourceFile,
        caller: &SurfaceName,
        introduction: usize,
        contexts: &mut Option<Arc<SyntaxContexts>>,
        frame: Arc<ExpansionFrame>,
        mut syntax_work: Option<&'inv mut crate::syntax_resource::SyntaxBudget>,
        staged_owners: Option<&'inv mut Vec<crate::syntax::SyntaxOwner>>,
    ) -> Result<Self, RuntimeFailure> {
        if syntax_work.is_none()
            && captures
                .iter()
                .any(|capture| matches!(capture, SurfaceSyntaxCapture::Repeated(_)))
        {
            return Err(RuntimeFailure::InvalidControlState);
        }
        let mut has_declaration = false;
        if let Some(budget) = syntax_work.as_deref_mut() {
            budget
                .charge_units(captures.len())
                .map_err(syntax_failure)?;
            for capture in captures {
                budget.charge().map_err(syntax_failure)?;
                match capture {
                    SurfaceSyntaxCapture::Declaration(capture) => {
                        has_declaration = true;
                        check_declaration_contents(&capture.contents, budget)?;
                    }
                    SurfaceSyntaxCapture::Identifier(capture) => {
                        crate::syntax::charge_type_name_inspection(&capture.name, 0, budget)
                            .map_err(syntax_failure)?;
                        crate::syntax::charge_type_origin(&capture.origin, 0, budget)
                            .map_err(syntax_failure)?;
                    }
                    SurfaceSyntaxCapture::Type(capture) => {
                        crate::syntax::charge_new_type_retention(capture, 0, budget)
                            .map_err(type_retention_failure)?;
                    }
                    SurfaceSyntaxCapture::Pattern(capture) => {
                        require_unbridged_charge(crate::syntax::charge_new_pattern_retention(
                            capture, 0, budget,
                        ))?;
                    }
                    SurfaceSyntaxCapture::Expression(capture) => {
                        require_unbridged_charge(crate::syntax::charge_new_expression_retention(
                            capture, 0, budget,
                        ))?;
                    }
                    _ => return Err(RuntimeFailure::InvalidControlState),
                }
            }
        }
        let type_accounting = syntax_work.is_some() && !has_declaration;
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
            // Invocation Arc and Input handle; retained frame, contexts, and
            // quote sites; the host's capture and diagnostic storage.
            budget.charge_units(7).map_err(syntax_failure)?;
            budget
                .charge_units(source.snapshot_work().unwrap_or(usize::MAX))
                .map_err(syntax_failure)?;
            crate::syntax::charge_type_name_copy(caller, 0, budget).map_err(syntax_failure)?;
        }
        let captures = {
            let mut copied = Vec::with_capacity(captures.len());
            for capture in captures {
                if syntax_work.is_none() && matches!(capture, SurfaceSyntaxCapture::Declaration(_))
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
                        SurfaceSyntaxCapture::Type(capture) => {
                            crate::syntax::charge_new_type_copy(&capture.ty, 1, false, budget)
                                .map_err(syntax_failure)?;
                        }
                        SurfaceSyntaxCapture::Pattern(capture) => {
                            require_unbridged_charge(crate::syntax::charge_new_pattern_copy(
                                &capture.pattern,
                                1,
                                false,
                                budget,
                            ))?;
                        }
                        SurfaceSyntaxCapture::Expression(capture) => {
                            require_unbridged_charge(crate::syntax::charge_new_expression_copy(
                                &capture.expression,
                                1,
                                false,
                                budget,
                            ))?;
                        }
                        _ => return Err(RuntimeFailure::InvalidControlState),
                    }
                }
                copied.push(capture.clone());
            }
            copied
        };
        let contexts = contexts.take().ok_or(RuntimeFailure::InvalidControlState)?;
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
            contexts: Some(contexts),
            quote_sites: Arc::clone(&entry.quote_sites),
            staged_owners,
            fresh_count: 0,
            captures,
            syntax_work,
            type_accounting,
            expressions: Vec::new(),
            declarations: Vec::new(),
            types: Vec::new(),
            patterns: Vec::new(),
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

    pub(super) fn take_contexts(&mut self) -> Option<Arc<SyntaxContexts>> {
        self.contexts.take()
    }

    pub(super) fn fresh_count(&self) -> usize {
        if self.staged_owners.is_some() {
            0
        } else {
            self.fresh_count
        }
    }

    fn issue_context_owner(
        &mut self,
        owner: Option<usize>,
        declaration: crate::source::Span,
        import_span: crate::source::Span,
    ) -> Result<usize, RuntimeFailure> {
        let contexts = self
            .contexts
            .as_mut()
            .and_then(Arc::get_mut)
            .ok_or(RuntimeFailure::InvalidControlState)?;
        let staged = self
            .staged_owners
            .as_deref_mut()
            .ok_or(RuntimeFailure::InvalidControlState)?;
        let live = contexts.owner_count();
        let next = live.checked_add(1).ok_or(RuntimeFailure::HeapCapacity)?;
        if staged.len() != live {
            return Err(RuntimeFailure::InvalidControlState);
        }
        let contexts_growth = if live == contexts.owner_capacity() {
            live.saturating_mul(2).saturating_add(1)
        } else {
            0
        };
        let staged_growth = if live == staged.capacity() {
            live.saturating_mul(2).saturating_add(1)
        } else {
            0
        };
        self.syntax_work
            .as_deref_mut()
            .ok_or(RuntimeFailure::InvalidControlState)?
            .charge_units(
                contexts_growth
                    .saturating_add(staged_growth)
                    .saturating_add(2),
            )
            .map_err(syntax_failure)?;
        if live == contexts.owner_capacity() {
            contexts
                .reserve_owner()
                .map_err(|()| RuntimeFailure::HeapCapacity)?;
        }
        if live == staged.capacity() {
            staged
                .try_reserve_exact(1)
                .map_err(|_| RuntimeFailure::HeapCapacity)?;
        }
        contexts.push_owner(owner);
        staged.push(crate::syntax::SyntaxOwner {
            owner,
            declaration,
            import_span,
        });
        Ok(next)
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

    // Prepay the known literal copy and the generated constructor/tuple storage
    // before the ordinary application evaluates any of its operands.
    pub(super) fn reach_quote(&mut self, node: NodeId) -> Result<(), RuntimeFailure> {
        for index in 0..self.quote_sites.len() {
            self.charge(1)?;
            if self.quote_sites[index].nodes.application != node {
                continue;
            }
            #[cfg(test)]
            super::machine_test_hooks::QUOTE_REACHES
                .set(super::machine_test_hooks::QUOTE_REACHES.get() + 1);
            if self.staged_owners.is_none() || self.syntax_work.is_none() {
                return Err(RuntimeFailure::InvalidControlState);
            }
            self.charge(1)?;
            let template = Arc::clone(&self.quote_sites[index].nodes.template);
            let budget = self
                .syntax_work
                .as_deref_mut()
                .ok_or(RuntimeFailure::InvalidControlState)?;
            // One empty list, one payload tuple and constructor each, and a
            // closure, pair and constructor for each nonempty list link.
            let storage = template
                .holes
                .checked_mul(3)
                .and_then(|n| n.checked_add(4))
                .ok_or(RuntimeFailure::ResourceCapacity)?;
            budget.charge_units(storage).map_err(syntax_failure)?;
            budget
                .charge_units(template.contents.len())
                .map_err(syntax_failure)?;
            let mut pending = Vec::new();
            for item in template.contents.iter().rev() {
                reserve_type_push(&mut pending, Some(&mut *budget), true)?;
                pending.push((item, 1_usize));
            }
            while let Some((item, depth)) = pending.pop() {
                budget.charge().map_err(syntax_failure)?;
                match item {
                    MacroOutputNode::Identifier(name, origin) => {
                        crate::syntax::charge_type_name_copy(name, depth, budget)
                            .map_err(syntax_failure)?;
                        crate::syntax::charge_type_origin_copy(origin, depth, budget)
                            .map_err(syntax_failure)?;
                    }
                    MacroOutputNode::Token(kind, _, origin) => {
                        crate::syntax::charge_type_token_copy(kind, budget)
                            .map_err(syntax_failure)?;
                        budget.charge().map_err(syntax_failure)?;
                        crate::syntax::charge_type_origin_copy(origin, depth, budget)
                            .map_err(syntax_failure)?;
                    }
                    MacroOutputNode::Group(_, children, origin) => {
                        let child = crate::syntax::type_depth(depth, 1).map_err(syntax_failure)?;
                        crate::syntax::charge_type_origin_copy(origin, child, budget)
                            .map_err(syntax_failure)?;
                        budget
                            .charge_units(children.len())
                            .map_err(syntax_failure)?;
                        for item in children.iter().rev() {
                            reserve_type_push(&mut pending, Some(&mut *budget), true)?;
                            pending.push((item, child));
                        }
                    }
                    MacroOutputNode::Splice(_) => {}
                    _ => return Err(RuntimeFailure::InvalidControlState),
                }
            }
            return Ok(());
        }
        Ok(())
    }

    pub(super) fn finish_quote(
        &mut self,
        node: NodeId,
        value: &Value,
        heap: &[HeapCell],
        work: &mut TypeWorkBudget,
    ) -> Result<Option<Value>, RuntimeFailure> {
        let mut selected = None;
        for index in 0..self.quote_sites.len() {
            self.charge(1)?;
            if self.quote_sites[index].nodes.constructor_result == node {
                selected = Some(index);
                break;
            }
        }
        let Some(index) = selected else {
            return Ok(None);
        };
        self.charge(2)?;
        let site = &self.quote_sites[index];
        let expected_constructor = site.nodes.constructor;
        let owner = site.owner;
        let template = Arc::clone(&site.nodes.template);
        let source = Arc::clone(&site.source);
        let (constructor, payload) = constructor_fields(value, heap)?;
        if constructor != expected_constructor
            || !constructor.owner().module().is_builtin_compiler_syntax()
        {
            return Err(RuntimeFailure::InvalidControlState);
        }
        let (ordinal, mut list) = pair(payload.ok_or(RuntimeFailure::InvalidControlState)?, heap)?;
        if read_integer(ordinal, heap, work)?.to_usize() != Some(template.ordinal) {
            return Err(RuntimeFailure::InvalidControlState);
        }
        let empty = self.constructor("NoQuoteHoles")?;
        let more = self.constructor("MoreQuoteHoles")?;
        self.charge(template.holes)?;
        let mut holes = Vec::new();
        holes
            .try_reserve_exact(template.holes)
            .map_err(|_| RuntimeFailure::HeapCapacity)?;
        loop {
            self.charge(1)?;
            let (constructor, payload) = constructor_fields(list, heap)?;
            if constructor == empty && payload.is_none() {
                break;
            }
            if constructor != more || holes.len() == template.holes {
                return Err(RuntimeFailure::InvalidControlState);
            }
            let (value, tail) = pair(payload.ok_or(RuntimeFailure::InvalidControlState)?, heap)?;
            let CompilerSyntaxHandleKind::Expression(fragment) = self.admitted_handle(value)?
            else {
                return Err(RuntimeFailure::InvalidControlState);
            };
            if self.expressions.get(fragment).is_none() {
                return Err(RuntimeFailure::InvalidControlState);
            }
            holes.push(fragment);
            list = tail;
        }
        if holes.len() != template.holes {
            return Err(RuntimeFailure::InvalidControlState);
        }
        let introduction =
            self.issue_context_owner(Some(owner), template.origin, template.origin)?;
        let output = self.fill_quote_contents(&template, introduction, &holes)?;
        let capture = crate::parser::parse_macro_expression_fragment(
            &source,
            template.origin,
            output,
            self.contexts
                .as_deref()
                .ok_or(RuntimeFailure::InvalidControlState)?,
            &self.frame,
            self.syntax_work
                .as_deref_mut()
                .ok_or(RuntimeFailure::InvalidControlState)?,
        )
        .map_err(type_retention_failure)?;
        self.charge(2)?;
        reserve_type_push(&mut self.expressions, self.syntax_work.as_deref_mut(), true)?;
        let result = self.expressions.len();
        self.expressions.push(capture);
        #[cfg(test)]
        {
            let completions = super::machine_test_hooks::QUOTE_COMPLETIONS.get();
            if completions == 0 {
                super::machine_test_hooks::FIRST_QUOTE_COMPLETION_WORK
                    .set(self.syntax_work.as_deref().map(|budget| budget.consumed()));
            }
            super::machine_test_hooks::QUOTE_COMPLETIONS.set(completions + 1);
        }
        Ok(Some(
            self.handle(CompilerSyntaxHandleKind::Expression(result)),
        ))
    }

    fn fill_quote_contents(
        &mut self,
        template: &crate::syntax::QuoteTemplate,
        introduction: usize,
        holes: &[usize],
    ) -> Result<Vec<MacroOutputNode>, RuntimeFailure> {
        struct Group<'a> {
            nodes: std::slice::Iter<'a, MacroOutputNode>,
            output: Vec<MacroOutputNode>,
            delimiter: MacroDelimiter,
            origin: &'a MacroOrigin,
        }
        let mut nodes = template.contents.iter();
        let mut output = Vec::with_capacity(template.contents.len());
        let mut groups: Vec<Group<'_>> = Vec::new();
        let mut next_hole = 0_usize;
        loop {
            let node = match nodes.next() {
                Some(MacroOutputNode::Group(delimiter, children, origin)) => {
                    reserve_type_push(&mut groups, self.syntax_work.as_deref_mut(), true)?;
                    let child_output = Vec::with_capacity(children.len());
                    groups.push(Group {
                        nodes,
                        output: std::mem::replace(&mut output, child_output),
                        delimiter: delimiter.clone(),
                        origin,
                    });
                    nodes = children.iter();
                    continue;
                }
                Some(MacroOutputNode::Identifier(name, origin)) => {
                    let mut name = name.clone();
                    name.introduction = introduction;
                    name.introduced_at = Some(self.frame.invocation);
                    name.written = false;
                    MacroOutputNode::Identifier(name, origin.clone())
                }
                Some(MacroOutputNode::Token(kind, spelling, origin)) => {
                    MacroOutputNode::Token(kind.clone(), Arc::clone(spelling), origin.clone())
                }
                Some(MacroOutputNode::Splice(name)) => {
                    let index = *holes
                        .get(next_hole)
                        .ok_or(RuntimeFailure::InvalidControlState)?;
                    next_hole += 1;
                    let capture = self
                        .expressions
                        .get(index)
                        .ok_or(RuntimeFailure::InvalidControlState)?;
                    let depth = groups.len().saturating_add(1);
                    let budget = self
                        .syntax_work
                        .as_deref_mut()
                        .ok_or(RuntimeFailure::InvalidControlState)?;
                    require_unbridged_charge(crate::syntax::charge_new_expression_retention(
                        capture, depth, budget,
                    ))?;
                    require_unbridged_charge(crate::syntax::charge_new_expression_copy(
                        &capture.expression,
                        crate::syntax::type_depth(depth, 1).map_err(syntax_failure)?,
                        false,
                        budget,
                    ))?;
                    MacroOutputNode::ForwardedExpression(capture.clone(), name.span.into())
                }
                Some(_) => return Err(RuntimeFailure::InvalidControlState),
                None => {
                    let Some(group) = groups.pop() else {
                        if next_hole != holes.len() {
                            return Err(RuntimeFailure::InvalidControlState);
                        }
                        return Ok(output);
                    };
                    let result =
                        MacroOutputNode::Group(group.delimiter, output, group.origin.clone());
                    output = group.output;
                    nodes = group.nodes;
                    result
                }
            };
            output.push(node);
        }
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
        self.issue_origin_inner(origin, self.type_accounting)
    }

    fn issue_origin_inner(
        &mut self,
        origin: MacroOrigin,
        type_accounting: bool,
    ) -> Result<Value, RuntimeFailure> {
        self.charge(2)?;
        reserve_type_push(
            &mut self.origins,
            self.syntax_work.as_deref_mut(),
            type_accounting,
        )?;
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
            reserve_type_push(
                &mut inputs,
                self.syntax_work.as_deref_mut(),
                self.type_accounting,
            )?;
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
                    .saturating_mul(SCALAR_DIAGNOSTIC_TEXT_PER_BYTE),
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
                if matches!(capture, Some(SurfaceSyntaxCapture::Repeated(_))) {
                    return Err(RuntimeFailure::InvalidControlState);
                }
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
                if let (Some(budget), Some(SurfaceSyntaxCapture::Type(capture))) =
                    (self.syntax_work.as_deref_mut(), capture)
                {
                    crate::syntax::charge_new_type_retention(capture, 0, budget)
                        .map_err(type_retention_failure)?;
                    crate::syntax::charge_new_type_copy(&capture.ty, 1, false, budget)
                        .map_err(syntax_failure)?;
                    budget.charge_units(2).map_err(syntax_failure)?; // arena slot and handle
                    let live = self.types.len();
                    if live == self.types.capacity() {
                        let requested = live.saturating_add(1);
                        budget
                            .charge_units(requested.saturating_add(live))
                            .map_err(syntax_failure)?;
                        self.types.reserve_exact(1);
                    }
                    let capture = capture.clone();
                    let index = self.types.len();
                    self.types.push(capture);
                    let fragment = self.handle(CompilerSyntaxHandleKind::Type(index));
                    let capture = self.construct(heap, "TypeCapture", Some(fragment))?;
                    return self.construct(heap, "Captured", Some(capture));
                }
                if let (Some(budget), Some(SurfaceSyntaxCapture::Expression(capture))) =
                    (self.syntax_work.as_deref_mut(), capture)
                {
                    require_unbridged_charge(crate::syntax::charge_new_expression_retention(
                        capture, 0, budget,
                    ))?;
                    require_unbridged_charge(crate::syntax::charge_new_expression_copy(
                        &capture.expression,
                        1,
                        false,
                        budget,
                    ))?;
                    budget.charge_units(2).map_err(syntax_failure)?;
                    let live = self.expressions.len();
                    if live == self.expressions.capacity() {
                        let requested = live.saturating_add(1);
                        budget
                            .charge_units(requested.saturating_add(live))
                            .map_err(syntax_failure)?;
                        self.expressions.reserve_exact(1);
                    }
                    let capture = capture.clone();
                    let index = self.expressions.len();
                    self.expressions.push(capture);
                    let fragment = self.handle(CompilerSyntaxHandleKind::Expression(index));
                    let capture = self.construct(heap, "ExpressionCapture", Some(fragment))?;
                    return self.construct(heap, "Captured", Some(capture));
                }
                if let (Some(budget), Some(SurfaceSyntaxCapture::Pattern(capture))) =
                    (self.syntax_work.as_deref_mut(), capture)
                {
                    require_unbridged_charge(crate::syntax::charge_new_pattern_retention(
                        capture, 0, budget,
                    ))?;
                    require_unbridged_charge(crate::syntax::charge_new_pattern_copy(
                        &capture.pattern,
                        1,
                        false,
                        budget,
                    ))?;
                    budget.charge_units(2).map_err(syntax_failure)?;
                    let live = self.patterns.len();
                    if live == self.patterns.capacity() {
                        let requested = live.saturating_add(1);
                        budget
                            .charge_units(requested.saturating_add(live))
                            .map_err(syntax_failure)?;
                        self.patterns.reserve_exact(1);
                    }
                    let capture = capture.clone();
                    let index = self.patterns.len();
                    self.patterns.push(capture);
                    let fragment = self.handle(CompilerSyntaxHandleKind::Pattern(index));
                    let capture = self.construct(heap, "PatternCapture", Some(fragment))?;
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
                        reserve_type_push(
                            &mut self.identifiers,
                            self.syntax_work.as_deref_mut(),
                            self.type_accounting,
                        )?;
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
                        | SurfaceSyntaxCapture::Declaration(_)
                        | SurfaceSyntaxCapture::Repeated(_),
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
                reserve_type_push(
                    &mut self.tokens,
                    self.syntax_work.as_deref_mut(),
                    self.type_accounting,
                )?;
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
                        let introduction = if self.staged_owners.is_some() {
                            self.issue_context_owner(
                                None,
                                self.frame.definition,
                                self.frame.invocation,
                            )?
                        } else {
                            self.introduction
                                .checked_add(self.fresh_count)
                                .ok_or(RuntimeFailure::HeapCapacity)?
                        };
                        (introduction, Some(self.frame.invocation))
                    }
                    "definition_identifier" => (self.introduction, Some(self.frame.invocation)),
                    _ => (self.caller.introduction, self.caller.introduced_at),
                };
                let index = self.identifiers.len();
                self.charge(2)?;
                self.charge(spelling.len())?;
                reserve_type_push(
                    &mut self.identifiers,
                    self.syntax_work.as_deref_mut(),
                    self.type_accounting,
                )?;
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
                    let output = self.transfer_syntax_inner(syntax, heap, 0, true)?;
                    let result = crate::parser::parse_macro_expression_fragment(
                        &self.source,
                        self.frame.invocation,
                        output,
                        self.contexts
                            .as_deref()
                            .ok_or(RuntimeFailure::InvalidControlState)?,
                        &self.frame,
                        self.syntax_work
                            .as_deref_mut()
                            .expect("the Expression route owns a budget"),
                    );
                    return match result {
                        Ok(capture) => {
                            self.charge(2)?;
                            let live = self.expressions.len();
                            if live == self.expressions.capacity() {
                                let requested = live.saturating_add(1);
                                self.charge(requested.saturating_add(live))?;
                                self.expressions.reserve_exact(1);
                            }
                            let index = self.expressions.len();
                            self.expressions.push(capture);
                            let fragment = self.handle(CompilerSyntaxHandleKind::Expression(index));
                            self.construct(heap, "Parsed", Some(fragment))
                        }
                        Err(crate::parser::MacroParseFailure::Syntax {
                            diagnostics,
                            resource,
                        }) => {
                            self.charge(2)?;
                            let live = self.parse_failures.len();
                            if live == self.parse_failures.capacity() {
                                let requested = live.saturating_add(1);
                                self.charge(requested.saturating_add(live))?;
                                self.parse_failures.reserve_exact(1);
                            }
                            let index = self.parse_failures.len();
                            self.parse_failures.push((diagnostics, resource));
                            let failure =
                                self.handle(CompilerSyntaxHandleKind::ParseFailure(index));
                            self.construct(heap, "ParseRejected", Some(failure))
                        }
                        Err(crate::parser::MacroParseFailure::Invalid) => {
                            Err(RuntimeFailure::InvalidControlState)
                        }
                    };
                }
                let output = self.transfer_syntax(syntax, heap, 0)?;
                let contents = output.clone().into();
                match crate::syntax::admit_transformer_output(
                    &self.source,
                    output,
                    self.contexts
                        .as_deref()
                        .ok_or(RuntimeFailure::InvalidControlState)?,
                    &self.frame,
                ) {
                    Ok(expression) => {
                        let index = self.expressions.len();
                        self.expressions.push(SurfaceExpressionCapture {
                            contains_protected_type: false,
                            quote_sites: Default::default(),
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
            "parse_type" => {
                let (input, syntax) = pair(&argument, heap)?;
                if !matches!(
                    self.admitted_handle(input)?,
                    CompilerSyntaxHandleKind::Input
                ) || self.syntax_work.is_none()
                {
                    return Err(RuntimeFailure::InvalidControlState);
                }
                let output = self.transfer_syntax_inner(syntax, heap, 0, true)?;
                let result = crate::parser::parse_macro_type(
                    &self.source,
                    self.frame.invocation,
                    output,
                    self.contexts
                        .as_deref()
                        .ok_or(RuntimeFailure::InvalidControlState)?,
                    &self.frame,
                    self.syntax_work
                        .as_deref_mut()
                        .expect("the Type route owns a budget"),
                );
                match result {
                    Ok(capture) => {
                        self.charge(2)?; // arena slot and issued handle
                        let live = self.types.len();
                        if live == self.types.capacity() {
                            let requested = live.saturating_add(1);
                            self.charge(requested.saturating_add(live))?;
                            self.types.reserve_exact(1);
                        }
                        let index = self.types.len();
                        self.types.push(capture);
                        let fragment = self.handle(CompilerSyntaxHandleKind::Type(index));
                        self.construct(heap, "ParsedType", Some(fragment))
                    }
                    Err(crate::parser::MacroParseFailure::Syntax {
                        diagnostics,
                        resource,
                    }) => {
                        self.charge(2)?; // failure slot and issued handle
                        let live = self.parse_failures.len();
                        if live == self.parse_failures.capacity() {
                            let requested = live.saturating_add(1);
                            self.charge(requested.saturating_add(live))?;
                            self.parse_failures.reserve_exact(1);
                        }
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
            "parse_pattern" => {
                let (input, syntax) = pair(&argument, heap)?;
                if !matches!(
                    self.admitted_handle(input)?,
                    CompilerSyntaxHandleKind::Input
                ) || self.syntax_work.is_none()
                {
                    return Err(RuntimeFailure::InvalidControlState);
                }
                let output = self.transfer_syntax_inner(syntax, heap, 0, true)?;
                let result = crate::parser::parse_macro_pattern(
                    &self.source,
                    self.frame.invocation,
                    output,
                    self.contexts
                        .as_deref()
                        .ok_or(RuntimeFailure::InvalidControlState)?,
                    &self.frame,
                    self.syntax_work
                        .as_deref_mut()
                        .expect("the Pattern route owns a budget"),
                );
                match result {
                    Ok(capture) => {
                        self.charge(2)?; // arena slot and issued handle
                        let live = self.patterns.len();
                        if live == self.patterns.capacity() {
                            let requested = live.saturating_add(1);
                            self.charge(requested.saturating_add(live))?;
                            self.patterns.reserve_exact(1);
                        }
                        let index = self.patterns.len();
                        self.patterns.push(capture);
                        let fragment = self.handle(CompilerSyntaxHandleKind::Pattern(index));
                        self.construct(heap, "ParsedPattern", Some(fragment))
                    }
                    Err(crate::parser::MacroParseFailure::Syntax {
                        diagnostics,
                        resource,
                    }) => {
                        self.charge(2)?; // failure slot and issued handle
                        let live = self.parse_failures.len();
                        if live == self.parse_failures.capacity() {
                            let requested = live.saturating_add(1);
                            self.charge(requested.saturating_add(live))?;
                            self.parse_failures.reserve_exact(1);
                        }
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
                if let Some(budget) = self.syntax_work.as_deref_mut() {
                    let capture = self
                        .expressions
                        .get(index)
                        .ok_or(RuntimeFailure::InvalidControlState)?;
                    budget.charge().map_err(syntax_failure)?;
                    let contents = Arc::clone(&capture.contents);
                    return self.syntax_value_inner(&contents, heap, 1, true);
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
            "type_syntax" => {
                let CompilerSyntaxHandleKind::Type(index) = self.admitted_handle(&argument)? else {
                    return Err(RuntimeFailure::InvalidControlState);
                };
                let capture = self
                    .types
                    .get(index)
                    .ok_or(RuntimeFailure::InvalidControlState)?;
                let Some(budget) = self.syntax_work.as_deref_mut() else {
                    return Err(RuntimeFailure::InvalidControlState);
                };
                budget.charge().map_err(syntax_failure)?;
                let contents = Arc::clone(&capture.contents);
                self.syntax_value_inner(&contents, heap, 1, true)
            }
            "pattern_syntax" => {
                let CompilerSyntaxHandleKind::Pattern(index) = self.admitted_handle(&argument)?
                else {
                    return Err(RuntimeFailure::InvalidControlState);
                };
                let capture = self
                    .patterns
                    .get(index)
                    .ok_or(RuntimeFailure::InvalidControlState)?;
                let Some(budget) = self.syntax_work.as_deref_mut() else {
                    return Err(RuntimeFailure::InvalidControlState);
                };
                budget.charge().map_err(syntax_failure)?;
                let contents = Arc::clone(&capture.contents);
                self.syntax_value_inner(&contents, heap, 1, true)
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
            let type_accounting = self.type_accounting
                || !self.types.is_empty()
                || !self.patterns.is_empty()
                || (self.syntax_work.is_some() && !self.declarations.is_empty())
                || (self.syntax_work.is_some() && !self.expressions.is_empty());
            return self
                .transfer_syntax_inner(
                    syntax.ok_or(RuntimeFailure::InvalidControlState)?,
                    heap,
                    0,
                    type_accounting,
                )
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
                .get_mut(index)
                .ok_or(RuntimeFailure::InvalidControlState)?;
            let diagnostics = if self.syntax_work.is_some() {
                std::mem::take(diagnostics)
            } else {
                diagnostics.clone()
            };
            return Ok(TransformerOutput::SyntaxRejected(
                crate::driver::SyntaxParseFailure {
                    diagnostics,
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
                invocation_location: None,
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
        self.transfer_syntax_inner(syntax, heap, depth, self.type_accounting)
    }

    fn transfer_syntax_inner(
        &mut self,
        syntax: &Value,
        heap: &[HeapCell],
        depth: usize,
        type_accounting: bool,
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
                reserve_type_push(
                    &mut parent,
                    self.syntax_work.as_deref_mut(),
                    type_accounting,
                )?;
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
                reserve_type_push(
                    &mut groups,
                    self.syntax_work.as_deref_mut(),
                    type_accounting,
                )?;
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
                }
                let (value, origin) = pair(payload, heap)?;
                if self.syntax_work.is_some()
                    && self.constructors.get("DeclarationNode") == Some(&tag)
                {
                    let CompilerSyntaxHandleKind::Declaration(index) =
                        self.admitted_handle(value)?
                    else {
                        return Err(RuntimeFailure::InvalidControlState);
                    };
                    if self.declarations.get(index).is_none() {
                        return Err(RuntimeFailure::InvalidControlState);
                    }
                    let prefix = depth.saturating_add(groups.len());
                    let origin = self.copy_origin(origin, prefix)?;
                    let capture = &self.declarations[index];
                    let budget = self
                        .syntax_work
                        .as_deref_mut()
                        .expect("the declaration route owns a budget");
                    check_declaration_contents_at(&capture.contents, prefix, budget)?;
                    budget.charge_units(2).map_err(syntax_failure)?; // retained Arc and output slot
                    reserve_type_push(&mut output, Some(budget), true)?;
                    let capture = capture.clone();
                    output.push(MacroOutputNode::ForwardedDeclaration(capture, origin));
                    nodes = rest;
                    continue;
                }
                if self.syntax_work.is_some() && tag == self.constructor("TypeNode")? {
                    let CompilerSyntaxHandleKind::Type(index) = self.admitted_handle(value)? else {
                        return Err(RuntimeFailure::InvalidControlState);
                    };
                    if self.types.get(index).is_none() {
                        return Err(RuntimeFailure::InvalidControlState);
                    }
                    let prefix = depth.saturating_add(groups.len());
                    let origin = self.copy_origin(origin, prefix)?;
                    let capture = &self.types[index];
                    let budget = self
                        .syntax_work
                        .as_deref_mut()
                        .expect("the Type route owns a budget");
                    crate::syntax::charge_new_type_retention(capture, prefix, budget)
                        .map_err(type_retention_failure)?;
                    crate::syntax::charge_new_type_copy(
                        &capture.ty,
                        crate::syntax::type_depth(prefix, 1).map_err(syntax_failure)?,
                        false,
                        budget,
                    )
                    .map_err(syntax_failure)?;
                    budget.charge().map_err(syntax_failure)?; // output slot
                    reserve_type_push(&mut output, Some(budget), type_accounting)?;
                    output.push(MacroOutputNode::ForwardedType(capture.clone(), origin));
                    nodes = rest;
                    continue;
                }
                if self.syntax_work.is_some() && self.constructors.get("PatternNode") == Some(&tag)
                {
                    let CompilerSyntaxHandleKind::Pattern(index) = self.admitted_handle(value)?
                    else {
                        return Err(RuntimeFailure::InvalidControlState);
                    };
                    if self.patterns.get(index).is_none() {
                        return Err(RuntimeFailure::InvalidControlState);
                    }
                    let prefix = depth.saturating_add(groups.len());
                    let origin = self.copy_origin(origin, prefix)?;
                    let capture = &self.patterns[index];
                    let budget = self
                        .syntax_work
                        .as_deref_mut()
                        .expect("the Pattern route owns a budget");
                    require_unbridged_charge(crate::syntax::charge_new_pattern_retention(
                        capture, prefix, budget,
                    ))?;
                    require_unbridged_charge(crate::syntax::charge_new_pattern_copy(
                        &capture.pattern,
                        crate::syntax::type_depth(prefix, 1).map_err(syntax_failure)?,
                        false,
                        budget,
                    ))?;
                    budget.charge().map_err(syntax_failure)?;
                    reserve_type_push(&mut output, Some(budget), type_accounting)?;
                    output.push(MacroOutputNode::ForwardedPattern(capture.clone(), origin));
                    nodes = rest;
                    continue;
                }
                if self.syntax_work.is_some()
                    && self.constructors.get("ExpressionNode") == Some(&tag)
                {
                    let CompilerSyntaxHandleKind::Expression(index) =
                        self.admitted_handle(value)?
                    else {
                        return Err(RuntimeFailure::InvalidControlState);
                    };
                    if self.expressions.get(index).is_none() {
                        return Err(RuntimeFailure::InvalidControlState);
                    }
                    let prefix = depth.saturating_add(groups.len());
                    let origin = self.copy_origin(origin, prefix)?;
                    let capture = &self.expressions[index];
                    let budget = self
                        .syntax_work
                        .as_deref_mut()
                        .expect("the Expression route owns a budget");
                    require_unbridged_charge(crate::syntax::charge_new_expression_retention(
                        capture, prefix, budget,
                    ))?;
                    require_unbridged_charge(crate::syntax::charge_new_expression_copy(
                        &capture.expression,
                        crate::syntax::type_depth(prefix, 1).map_err(syntax_failure)?,
                        false,
                        budget,
                    ))?;
                    budget.charge().map_err(syntax_failure)?;
                    reserve_type_push(&mut output, Some(budget), type_accounting)?;
                    output.push(MacroOutputNode::Expression(capture.clone(), origin));
                    nodes = rest;
                    continue;
                }
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
                    reserve_type_push(
                        &mut output,
                        self.syntax_work.as_deref_mut(),
                        type_accounting,
                    )?;
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
                    reserve_type_push(
                        &mut output,
                        self.syntax_work.as_deref_mut(),
                        type_accounting,
                    )?;
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
                    reserve_type_push(
                        &mut output,
                        self.syntax_work.as_deref_mut(),
                        type_accounting,
                    )?;
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
        self.syntax_value_inner(nodes, heap, depth, self.type_accounting)
    }

    fn syntax_value_inner(
        &mut self,
        nodes: &[MacroOutputNode],
        heap: &mut Vec<HeapCell>,
        depth: usize,
        type_accounting: bool,
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
                    let selected = self.syntax_work.is_some();
                    if let Some(budget) = self.syntax_work.as_deref_mut() {
                        let prefix = depth.saturating_add(groups.len());
                        require_unbridged_charge(crate::syntax::charge_new_expression_retention(
                            expression, prefix, budget,
                        ))?;
                        require_unbridged_charge(crate::syntax::charge_new_expression_copy(
                            &expression.expression,
                            crate::syntax::type_depth(prefix, 1).map_err(syntax_failure)?,
                            false,
                            budget,
                        ))?;
                        budget.charge_units(4).map_err(syntax_failure)?;
                        self.charge_origin(origin, prefix)?;
                        let live = self.expressions.len();
                        if live == self.expressions.capacity() {
                            let requested = live.saturating_add(1);
                            self.charge(requested.saturating_add(live))?;
                            self.expressions.reserve_exact(1);
                        }
                    }
                    let index = self.expressions.len();
                    self.expressions.push(expression.clone());
                    (
                        "ExpressionNode",
                        vec![
                            self.handle(CompilerSyntaxHandleKind::Expression(index)),
                            self.issue_origin_inner(origin.clone(), type_accounting || selected)?,
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
                    reserve_type_push(
                        &mut self.identifiers,
                        self.syntax_work.as_deref_mut(),
                        type_accounting,
                    )?;
                    self.identifiers.push(name.clone());
                    (
                        "IdentifierNode",
                        vec![
                            self.handle(CompilerSyntaxHandleKind::Identifier(index)),
                            self.issue_origin_inner(origin.clone(), type_accounting)?,
                        ],
                    )
                }
                Some(MacroOutputNode::ForwardedType(capture, origin)) => {
                    let prefix = depth.saturating_add(groups.len());
                    let Some(budget) = self.syntax_work.as_deref_mut() else {
                        return Err(RuntimeFailure::InvalidControlState);
                    };
                    crate::syntax::charge_new_type_retention(capture, prefix, budget)
                        .map_err(type_retention_failure)?;
                    crate::syntax::charge_new_type_copy(
                        &capture.ty,
                        crate::syntax::type_depth(prefix, 1).map_err(syntax_failure)?,
                        false,
                        budget,
                    )
                    .map_err(syntax_failure)?;
                    budget.charge_units(4).map_err(syntax_failure)?;
                    self.charge_origin(origin, prefix)?;
                    let live = self.types.len();
                    if live == self.types.capacity() {
                        let requested = live.saturating_add(1);
                        self.charge(requested.saturating_add(live))?;
                        self.types.reserve_exact(1);
                    }
                    let index = self.types.len();
                    self.types.push(capture.clone());
                    (
                        "TypeNode",
                        vec![
                            self.handle(CompilerSyntaxHandleKind::Type(index)),
                            self.issue_origin_inner(origin.clone(), type_accounting)?,
                        ],
                    )
                }
                Some(MacroOutputNode::ForwardedPattern(capture, origin)) => {
                    let prefix = depth.saturating_add(groups.len());
                    let Some(budget) = self.syntax_work.as_deref_mut() else {
                        return Err(RuntimeFailure::InvalidControlState);
                    };
                    require_unbridged_charge(crate::syntax::charge_new_pattern_retention(
                        capture, prefix, budget,
                    ))?;
                    require_unbridged_charge(crate::syntax::charge_new_pattern_copy(
                        &capture.pattern,
                        crate::syntax::type_depth(prefix, 1).map_err(syntax_failure)?,
                        false,
                        budget,
                    ))?;
                    budget.charge_units(4).map_err(syntax_failure)?;
                    self.charge_origin(origin, prefix)?;
                    let live = self.patterns.len();
                    if live == self.patterns.capacity() {
                        let requested = live.saturating_add(1);
                        self.charge(requested.saturating_add(live))?;
                        self.patterns.reserve_exact(1);
                    }
                    let index = self.patterns.len();
                    self.patterns.push(capture.clone());
                    (
                        "PatternNode",
                        vec![
                            self.handle(CompilerSyntaxHandleKind::Pattern(index)),
                            self.issue_origin_inner(origin.clone(), type_accounting)?,
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
                    reserve_type_push(
                        &mut self.tokens,
                        self.syntax_work.as_deref_mut(),
                        type_accounting,
                    )?;
                    self.tokens.push(SyntaxToken {
                        kind: kind.clone(),
                        spelling: Arc::clone(spelling),
                    });
                    (
                        "TokenNode",
                        vec![
                            self.handle(CompilerSyntaxHandleKind::Token(index)),
                            self.issue_origin_inner(origin.clone(), type_accounting)?,
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
                    reserve_type_push(
                        &mut groups,
                        self.syntax_work.as_deref_mut(),
                        type_accounting,
                    )?;
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
                    | MacroOutputNode::ForwardedDeclaration(_, _)
                    | MacroOutputNode::TemplateRepeat(_)
                    | MacroOutputNode::TemplateEscape(_),
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
                        vec![
                            delimiter,
                            children,
                            self.issue_origin_inner(origin.clone(), type_accounting)?,
                        ],
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
            Self::with_source("component.ash", "type Item = Item\n")
        }

        fn with_source(path: &str, text: &str) -> Self {
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

            let source = SourceFile::new(path, text).unwrap();
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
                    quote_sites: Arc::from([]),
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
            contexts: Some(Arc::new(SyntaxContexts::new(&[], &[], &[]))),
            syntax_work: Some(budget),
            quote_sites: Arc::from([]),
            staged_owners: None,
            type_accounting: false,
            fresh_count: 0,
            captures: Vec::new(),
            expressions: Vec::new(),
            declarations: Vec::new(),
            types: Vec::new(),
            patterns: Vec::new(),
            identifiers: Vec::new(),
            origins: Vec::new(),
            parse_failures: Vec::new(),
            tokens: Vec::new(),
            constructors: HashMap::new(),
            operations: HashMap::new(),
        }
    }

    #[test]
    fn pattern_syntax_rejects_foreign_stale_wrong_and_out_of_range_handles() {
        use super::{RuntimeFailure, Value};
        use crate::{
            eval::value::CompilerSyntaxHandleKind,
            surface::{SurfacePattern, SurfacePatternCapture, SurfacePatternKind},
            syntax::MacroOutputNode,
            syntax_resource::SyntaxBudget,
            types::{OperationId, TypeWorkBudget},
        };
        use std::sync::Arc;

        let fixture = DeclarationHostFixture::new();
        let contents: Arc<[MacroOutputNode]> = Arc::from([]);
        let capture = SurfacePatternCapture {
            pattern: SurfacePattern {
                kind: SurfacePatternKind::Wildcard,
                span: fixture.caller.span,
                diagnostic: None,
            },
            contents: Arc::clone(&contents),
        };
        let mut budget = SyntaxBudget::default();
        let mut host = fixture.host(&[], &mut budget).unwrap();
        let operation = OperationId::new(host.ops, 40);
        host.operations.insert(operation, "pattern_syntax".into());
        host.patterns.push(capture.clone());
        let local = host.handle(CompilerSyntaxHandleKind::Pattern(0));

        let mut foreign_budget = SyntaxBudget::default();
        let mut foreign = fixture.host(&[], &mut foreign_budget).unwrap();
        foreign.patterns.push(capture.clone());
        let foreign_handle = foreign.handle(CompilerSyntaxHandleKind::Pattern(0));
        let stale_handle = {
            let mut stale_budget = SyntaxBudget::default();
            let mut stale = fixture.host(&[], &mut stale_budget).unwrap();
            stale.patterns.push(capture);
            stale.handle(CompilerSyntaxHandleKind::Pattern(0))
        };
        let invalid = [
            foreign_handle,
            stale_handle,
            host.handle(CompilerSyntaxHandleKind::Type(0)),
            host.handle(CompilerSyntaxHandleKind::Pattern(1)),
            Value::Unit,
        ];
        let mut heap = Vec::new();
        let retained = Arc::strong_count(&contents);
        for handle in invalid {
            assert!(matches!(
                host.request(
                    operation,
                    handle,
                    &mut heap,
                    &mut TypeWorkBudget::unbounded()
                ),
                Err(RuntimeFailure::InvalidControlState)
            ));
            assert_eq!(host.patterns.len(), 1);
            assert_eq!(Arc::strong_count(&contents), retained);
            assert!(heap.is_empty());
        }
        for _ in 0..2 {
            host.request(
                operation,
                local.clone(),
                &mut heap,
                &mut TypeWorkBudget::unbounded(),
            )
            .expect("a local Pattern handle is reusable");
            assert_eq!(Arc::strong_count(&contents), retained);
        }
    }

    #[test]
    fn type_host_origin_arena_prepays_growth_before_issuance() {
        use crate::{
            eval::RuntimeFailure,
            surface::{SurfaceDeclarationCapture, SurfaceIdentifierCapture, SurfaceSyntaxCapture},
            syntax_resource::SyntaxBudget,
        };
        use std::sync::Arc;

        let fixture = DeclarationHostFixture::new();
        let identifier = SurfaceSyntaxCapture::Identifier(SurfaceIdentifierCapture {
            name: fixture.caller.clone(),
            origin: fixture.caller.span.into(),
        });
        let captures = [identifier.clone()];
        let mut measured = SyntaxBudget::default();
        measured.charge_units(17).unwrap();
        let mut host = fixture.host(&captures, &mut measured).unwrap();
        let before = host.syntax_work.as_deref().unwrap().consumed();
        assert_eq!(host.origins.capacity(), 0);
        host.issue_origin(fixture.caller.span.into()).unwrap();
        assert_eq!(host.syntax_work.as_deref().unwrap().consumed() - before, 3);
        assert_eq!(host.origins.capacity(), 1);
        let before = host.syntax_work.as_deref().unwrap().consumed();
        host.issue_origin(fixture.caller.span.into()).unwrap();
        assert_eq!(host.syntax_work.as_deref().unwrap().consumed() - before, 5);
        assert_eq!(host.origins.len(), 2);
        drop(host);

        let mut short = SyntaxBudget::with_limit(before - 1);
        short.charge_units(17).unwrap();
        let mut host = fixture.host(&captures, &mut short).unwrap();
        assert!(matches!(
            host.issue_origin(fixture.caller.span.into()),
            Err(RuntimeFailure::Report(report))
                if report.primary.reason_code() == "internal.resource.syntax-work"
        ));
        assert!(host.origins.is_empty());
        assert_eq!(host.origins.capacity(), 0);
        drop(host);

        for _ in 0..2 {
            let mut exact = SyntaxBudget::with_limit(before);
            exact.charge_units(17).unwrap();
            let mut host = fixture.host(&captures, &mut exact).unwrap();
            host.issue_origin(fixture.caller.span.into()).unwrap();
            assert_eq!(host.origins.len(), 1);
            drop(host);
            assert_eq!(exact.consumed(), before);
        }

        let declarations = [
            SurfaceSyntaxCapture::Declaration(SurfaceDeclarationCapture {
                contents: Arc::from([]),
            }),
            identifier,
        ];
        let mut legacy = SyntaxBudget::default();
        let mut host = fixture.host(&declarations, &mut legacy).unwrap();
        let before = host.syntax_work.as_deref().unwrap().consumed();
        host.issue_origin(fixture.caller.span.into()).unwrap();
        assert_eq!(host.syntax_work.as_deref().unwrap().consumed() - before, 2);
    }

    #[test]
    fn type_host_value_and_transfer_pay_each_reached_buffer() {
        use super::{HeapCell, RuntimeFailure, SyntaxHost};
        use crate::{
            lexer::TokenKind,
            surface::{SurfaceDeclarationCapture, SurfaceIdentifierCapture, SurfaceSyntaxCapture},
            syntax::{MacroDelimiter, MacroOrigin, MacroOutputNode},
            syntax_resource::SyntaxBudget,
        };
        use std::sync::Arc;

        fn host<'a>(
            fixture: &DeclarationHostFixture,
            declaration: bool,
            budget: &'a mut SyntaxBudget,
        ) -> SyntaxHost<'a> {
            let identifier = SurfaceSyntaxCapture::Identifier(SurfaceIdentifierCapture {
                name: fixture.caller.clone(),
                origin: fixture.caller.span.into(),
            });
            let captures = if declaration {
                vec![
                    SurfaceSyntaxCapture::Declaration(SurfaceDeclarationCapture {
                        contents: Arc::from([]),
                    }),
                    identifier,
                ]
            } else {
                vec![identifier]
            };
            fixture.host(&captures, budget).unwrap()
        }

        fn measure(
            fixture: &DeclarationHostFixture,
            declaration: bool,
            packet: &[MacroOutputNode],
        ) -> (usize, usize) {
            let mut budget = SyntaxBudget::default();
            let mut host = host(fixture, declaration, &mut budget);
            let mut heap = Vec::<HeapCell>::new();
            let start = host.syntax_work.as_deref().unwrap().consumed();
            let syntax = host.syntax_value(packet, &mut heap, 0).unwrap();
            let after_value = host.syntax_work.as_deref().unwrap().consumed();
            let transferred = host.transfer_syntax(&syntax, &heap, 0).unwrap();
            let after_transfer = host.syntax_work.as_deref().unwrap().consumed();
            assert_eq!(transferred, packet);
            (after_value - start, after_transfer - after_value)
        }

        let fixture = DeclarationHostFixture::new();
        let origin: MacroOrigin = fixture.caller.span.into();
        let nested = vec![MacroOutputNode::Group(
            MacroDelimiter::Parentheses,
            vec![MacroOutputNode::Group(
                MacroDelimiter::Braces,
                vec![MacroOutputNode::Token(
                    TokenKind::IntType,
                    "Int".into(),
                    origin.clone(),
                )],
                origin.clone(),
            )],
            origin.clone(),
        )];
        let selected = measure(&fixture, false, &nested);
        let legacy = measure(&fixture, true, &nested);
        // Value construction pays Group stack 1+3, Token arena 1 and Origin
        // arena 1+3+5. Transfer pays Group stack 1+3 and three output Vecs 1 each.
        assert_eq!(selected.0 - legacy.0, 14);
        assert_eq!(selected.1 - legacy.1, 7);

        // A popped continuation is reused by the next sibling. The second
        // output and Origin pushes still grow their own distinct buffers.
        let siblings = vec![
            MacroOutputNode::Group(MacroDelimiter::Parentheses, Vec::new(), origin.clone()),
            MacroOutputNode::Group(MacroDelimiter::Braces, Vec::new(), origin),
        ];
        let selected_siblings = measure(&fixture, false, &siblings);
        let legacy_siblings = measure(&fixture, true, &siblings);
        assert_eq!(selected_siblings.0 - legacy_siblings.0, 5);
        assert_eq!(selected_siblings.1 - legacy_siblings.1, 5);
        assert_eq!(measure(&fixture, false, &[]), measure(&fixture, true, &[]));

        // These synthetic budgets isolate each real host operation. Earlier
        // paid local state may exist on failure; no partial Syntax/output is returned.
        for (limit, success) in [
            (selected.0 - 1, false),
            (selected.0, true),
            (selected.0, true),
        ] {
            let mut budget = SyntaxBudget::default();
            let mut host = host(&fixture, false, &mut budget);
            *host.syntax_work.as_deref_mut().unwrap() = SyntaxBudget::with_limit(17 + limit);
            host.syntax_work
                .as_deref_mut()
                .unwrap()
                .charge_units(17)
                .unwrap();
            let result = host.syntax_value(&nested, &mut Vec::new(), 0);
            if success {
                assert!(result.is_ok());
                assert_eq!(host.syntax_work.as_deref().unwrap().consumed(), 17 + limit);
            } else {
                assert!(matches!(result, Err(RuntimeFailure::Report(report))
                    if report.primary.reason_code() == "internal.resource.syntax-work"));
            }
        }
        for (limit, success) in [
            (selected.1 - 1, false),
            (selected.1, true),
            (selected.1, true),
        ] {
            let mut budget = SyntaxBudget::default();
            let mut host = host(&fixture, false, &mut budget);
            let mut heap = Vec::new();
            let syntax = host.syntax_value(&nested, &mut heap, 0).unwrap();
            *host.syntax_work.as_deref_mut().unwrap() = SyntaxBudget::with_limit(17 + limit);
            host.syntax_work
                .as_deref_mut()
                .unwrap()
                .charge_units(17)
                .unwrap();
            let result = host.transfer_syntax(&syntax, &heap, 0);
            if success {
                assert_eq!(result.unwrap(), nested);
                assert_eq!(host.syntax_work.as_deref().unwrap().consumed(), 17 + limit);
            } else {
                assert!(matches!(result, Err(RuntimeFailure::Report(report))
                    if report.primary.reason_code() == "internal.resource.syntax-work"));
            }
        }
    }

    #[test]
    fn type_services_keep_declaration_and_none_host_accounting_separate() {
        use super::{HeapCell, RuntimeFailure, SyntaxHost, Value, allocate_heap};
        use crate::{
            integer::Integer,
            lexer::TokenKind,
            module::ModuleId,
            surface::{SurfaceDeclarationCapture, SurfaceIdentifierCapture, SurfaceSyntaxCapture},
            syntax::{MacroOutputNode, TransformerOutput},
            syntax_resource::SyntaxBudget,
            types::{ConstructorId, NominalTypeId, OperationId, TypeWorkBudget},
        };
        use std::sync::Arc;

        fn trial(
            fixture: &DeclarationHostFixture,
            selected: bool,
            parse_first: bool,
        ) -> (usize, usize, usize, usize) {
            let identifier = SurfaceSyntaxCapture::Identifier(SurfaceIdentifierCapture {
                name: fixture.caller.clone(),
                origin: fixture.caller.span.into(),
            });
            let captures = if selected {
                vec![identifier]
            } else {
                vec![
                    SurfaceSyntaxCapture::Declaration(SurfaceDeclarationCapture {
                        contents: Arc::from([]),
                    }),
                    identifier,
                ]
            };
            let mut budget = SyntaxBudget::default();
            let mut host = fixture.host(&captures, &mut budget).unwrap();
            let parse = OperationId::new(host.ops, 4);
            let make_token = OperationId::new(host.ops, 5);
            host.operations.insert(parse, "parse_type".into());
            host.operations.insert(make_token, "make_token".into());
            let owner = NominalTypeId::new(ModuleId::new(0), 0);
            for (index, name) in (100u32..).zip([
                "ParsedType",
                "ParseRejected",
                "IntType",
                "MadeToken",
                "NoOrigins",
                "MoreOrigins",
            ]) {
                host.constructors
                    .insert(name.into(), ConstructorId::new(owner, index));
            }
            let span = host.frame.invocation;
            let packet = [MacroOutputNode::Token(
                TokenKind::IntType,
                "Int".into(),
                span.into(),
            )];
            let mut heap = Vec::<HeapCell>::new();
            let syntax = host.syntax_value(&packet, &mut heap, 0).unwrap();
            if parse_first {
                let fields = Value::Location(
                    allocate_heap(
                        &mut heap,
                        HeapCell::Tuple(vec![host.input(), syntax.clone()].into_boxed_slice()),
                    )
                    .unwrap(),
                );
                host.request(parse, fields, &mut heap, &mut TypeWorkBudget::unbounded())
                    .unwrap();
                assert_eq!(host.types.len(), 1);
            }

            let index = if selected { 0 } else { 1 };
            let fields = Value::Location(
                allocate_heap(
                    &mut heap,
                    HeapCell::Tuple(
                        vec![host.input(), Value::integer(Integer::from_i64(index))]
                            .into_boxed_slice(),
                    ),
                )
                .unwrap(),
            );
            let start = host.syntax_work.as_deref().unwrap().consumed();
            host.request(
                fixture.capture,
                fields,
                &mut heap,
                &mut TypeWorkBudget::unbounded(),
            )
            .unwrap();
            let capture_cost = host.syntax_work.as_deref().unwrap().consumed() - start;

            let kind = host.construct(&mut heap, "IntType", None).unwrap();
            let fields = Value::Location(
                allocate_heap(
                    &mut heap,
                    HeapCell::Tuple(vec![kind, Value::String(Arc::from("Int"))].into_boxed_slice()),
                )
                .unwrap(),
            );
            let start = host.syntax_work.as_deref().unwrap().consumed();
            host.request(
                make_token,
                fields,
                &mut heap,
                &mut TypeWorkBudget::unbounded(),
            )
            .unwrap();
            let token_cost = host.syntax_work.as_deref().unwrap().consumed() - start;

            let first = host.issue_origin(span.into()).unwrap();
            let second = host.issue_origin(span.into()).unwrap();
            let mut origins = host.construct(&mut heap, "NoOrigins", None).unwrap();
            for origin in [first, second] {
                let fields = Value::Location(
                    allocate_heap(
                        &mut heap,
                        HeapCell::Tuple(vec![origin, origins].into_boxed_slice()),
                    )
                    .unwrap(),
                );
                origins = host
                    .construct(&mut heap, "MoreOrigins", Some(fields))
                    .unwrap();
            }
            let start = host.syntax_work.as_deref().unwrap().consumed();
            assert_eq!(host.read_origins(&origins, &heap, 10).unwrap().len(), 2);
            let origins_cost = host.syntax_work.as_deref().unwrap().consumed() - start;

            let expanded = host
                .construct(&mut heap, "Expanded", Some(syntax.clone()))
                .unwrap();
            let start = host.syntax_work.as_deref().unwrap().consumed();
            assert_eq!(host.transfer_syntax(&syntax, &heap, 0).unwrap(), packet);
            let direct = host.syntax_work.as_deref().unwrap().consumed() - start;
            let start = host.syntax_work.as_deref().unwrap().consumed();
            let TransformerOutput::Expanded(output) = host
                .transfer(&expanded, &heap, &mut TypeWorkBudget::unbounded())
                .unwrap()
            else {
                panic!("expected Expanded");
            };
            assert_eq!(output, packet);
            let expanded_cost = host.syntax_work.as_deref().unwrap().consumed() - start;
            (
                capture_cost,
                token_cost,
                origins_cost,
                expanded_cost - direct,
            )
        }

        let fixture = DeclarationHostFixture::new();
        let legacy = trial(&fixture, false, false);
        let after_type = trial(&fixture, false, true);
        assert_eq!(
            (legacy.0, legacy.1, legacy.2),
            (after_type.0, after_type.1, after_type.2)
        );
        assert_eq!(legacy.3, 0);
        assert_eq!(after_type.3, 1);
        let selected = trial(&fixture, true, false);
        assert_eq!(selected.0 - legacy.0, 4); // Origin growth 2+1 and Identifier initial slot.
        assert_eq!(selected.1 - legacy.1, 3); // Token growth 2+1.
        assert_eq!(selected.2 - legacy.2, 4); // Related-origin buffer 1, then 2+1.
        assert_eq!(selected.3, 0);

        let captures = [SurfaceSyntaxCapture::Identifier(SurfaceIdentifierCapture {
            name: fixture.caller.clone(),
            origin: fixture.caller.span.into(),
        })];
        let mut host = SyntaxHost::new(
            &fixture.entry,
            &captures,
            &fixture.source,
            &fixture.caller,
            0,
            Arc::clone(&fixture.contexts),
            Arc::clone(&fixture.frame),
            None,
        )
        .unwrap();
        let parse = OperationId::new(host.ops, 4);
        host.operations.insert(parse, "parse_type".into());
        let packet = [MacroOutputNode::Token(
            TokenKind::IntType,
            "Int".into(),
            fixture.frame.invocation.into(),
        )];
        let mut heap = Vec::new();
        let syntax = host.syntax_value(&packet, &mut heap, 0).unwrap();
        assert_eq!(host.transfer_syntax(&syntax, &heap, 0).unwrap(), packet);
        let fields = Value::Location(
            allocate_heap(
                &mut heap,
                HeapCell::Tuple(vec![host.input(), syntax].into_boxed_slice()),
            )
            .unwrap(),
        );
        assert!(matches!(
            host.request(parse, fields, &mut heap, &mut TypeWorkBudget::unbounded()),
            Err(RuntimeFailure::InvalidControlState)
        ));
    }

    #[test]
    fn expression_services_keep_declaration_and_none_host_accounting_separate() {
        use super::{HeapCell, SyntaxHost, Value, allocate_heap};
        use crate::{
            integer::Integer,
            lexer::TokenKind,
            module::ModuleId,
            surface::{SurfaceDeclarationCapture, SurfaceIdentifierCapture, SurfaceSyntaxCapture},
            syntax::{MacroOutputNode, TransformerOutput},
            syntax_resource::SyntaxBudget,
            types::{ConstructorId, NominalTypeId, OperationId, TypeWorkBudget},
        };
        use std::sync::Arc;

        fn trial(
            fixture: &DeclarationHostFixture,
            selected: bool,
            parse_first: bool,
        ) -> (usize, usize, usize, usize) {
            let identifier = SurfaceSyntaxCapture::Identifier(SurfaceIdentifierCapture {
                name: fixture.caller.clone(),
                origin: fixture.caller.span.into(),
            });
            let captures = if selected {
                vec![identifier]
            } else {
                vec![
                    SurfaceSyntaxCapture::Declaration(SurfaceDeclarationCapture {
                        contents: Arc::from([]),
                    }),
                    identifier,
                ]
            };
            let mut budget = SyntaxBudget::default();
            let mut host = fixture.host(&captures, &mut budget).unwrap();
            let parse = OperationId::new(host.ops, 4);
            let make_token = OperationId::new(host.ops, 5);
            host.operations.insert(parse, "parse_expression".into());
            host.operations.insert(make_token, "make_token".into());
            let owner = NominalTypeId::new(ModuleId::new(0), 0);
            for (index, name) in (100u32..).zip([
                "Parsed",
                "ParseRejected",
                "IntType",
                "MadeToken",
                "NoOrigins",
                "MoreOrigins",
            ]) {
                host.constructors
                    .insert(name.into(), ConstructorId::new(owner, index));
            }
            let span = host.frame.invocation;
            let packet = [MacroOutputNode::Token(
                TokenKind::Integer(Integer::from_i64(1)),
                "1".into(),
                span.into(),
            )];
            let mut heap = Vec::<HeapCell>::new();
            let syntax = host.syntax_value(&packet, &mut heap, 0).unwrap();
            if parse_first {
                let fields = Value::Location(
                    allocate_heap(
                        &mut heap,
                        HeapCell::Tuple(vec![host.input(), syntax.clone()].into_boxed_slice()),
                    )
                    .unwrap(),
                );
                host.request(parse, fields, &mut heap, &mut TypeWorkBudget::unbounded())
                    .unwrap();
                assert_eq!(host.expressions.len(), 1);
            }

            let index = if selected { 0 } else { 1 };
            let fields = Value::Location(
                allocate_heap(
                    &mut heap,
                    HeapCell::Tuple(
                        vec![host.input(), Value::integer(Integer::from_i64(index))]
                            .into_boxed_slice(),
                    ),
                )
                .unwrap(),
            );
            let start = host.syntax_work.as_deref().unwrap().consumed();
            host.request(
                fixture.capture,
                fields,
                &mut heap,
                &mut TypeWorkBudget::unbounded(),
            )
            .unwrap();
            let capture_cost = host.syntax_work.as_deref().unwrap().consumed() - start;

            let kind = host.construct(&mut heap, "IntType", None).unwrap();
            let fields = Value::Location(
                allocate_heap(
                    &mut heap,
                    HeapCell::Tuple(vec![kind, Value::String(Arc::from("Int"))].into_boxed_slice()),
                )
                .unwrap(),
            );
            let start = host.syntax_work.as_deref().unwrap().consumed();
            host.request(
                make_token,
                fields,
                &mut heap,
                &mut TypeWorkBudget::unbounded(),
            )
            .unwrap();
            let token_cost = host.syntax_work.as_deref().unwrap().consumed() - start;

            let first = host.issue_origin(span.into()).unwrap();
            let second = host.issue_origin(span.into()).unwrap();
            let mut origins = host.construct(&mut heap, "NoOrigins", None).unwrap();
            for origin in [first, second] {
                let fields = Value::Location(
                    allocate_heap(
                        &mut heap,
                        HeapCell::Tuple(vec![origin, origins].into_boxed_slice()),
                    )
                    .unwrap(),
                );
                origins = host
                    .construct(&mut heap, "MoreOrigins", Some(fields))
                    .unwrap();
            }
            let start = host.syntax_work.as_deref().unwrap().consumed();
            assert_eq!(host.read_origins(&origins, &heap, 10).unwrap().len(), 2);
            let origins_cost = host.syntax_work.as_deref().unwrap().consumed() - start;

            let expanded = host
                .construct(&mut heap, "Expanded", Some(syntax.clone()))
                .unwrap();
            let start = host.syntax_work.as_deref().unwrap().consumed();
            assert_eq!(host.transfer_syntax(&syntax, &heap, 0).unwrap(), packet);
            let direct = host.syntax_work.as_deref().unwrap().consumed() - start;
            let start = host.syntax_work.as_deref().unwrap().consumed();
            let TransformerOutput::Expanded(output) = host
                .transfer(&expanded, &heap, &mut TypeWorkBudget::unbounded())
                .unwrap()
            else {
                panic!("expected Expanded");
            };
            assert_eq!(output, packet);
            let expanded_cost = host.syntax_work.as_deref().unwrap().consumed() - start;
            (
                capture_cost,
                token_cost,
                origins_cost,
                expanded_cost - direct,
            )
        }

        let fixture = DeclarationHostFixture::new();
        let legacy = trial(&fixture, false, false);
        let after_expression = trial(&fixture, false, true);
        assert_eq!(
            (legacy.0, legacy.1, legacy.2),
            (after_expression.0, after_expression.1, after_expression.2)
        );
        assert_eq!(legacy.3, 0);
        assert_eq!(after_expression.3, 1);
        let selected = trial(&fixture, true, false);
        assert_eq!(selected.0 - legacy.0, 4); // Origin growth 2+1 and Identifier initial slot.
        assert_eq!(selected.1 - legacy.1, 3); // Token growth 2+1.
        assert_eq!(selected.2 - legacy.2, 4); // Related-origin buffer 1, then 2+1.
        assert_eq!(selected.3, 0);

        let captures = [SurfaceSyntaxCapture::Identifier(SurfaceIdentifierCapture {
            name: fixture.caller.clone(),
            origin: fixture.caller.span.into(),
        })];
        let mut host = SyntaxHost::new(
            &fixture.entry,
            &captures,
            &fixture.source,
            &fixture.caller,
            0,
            Arc::clone(&fixture.contexts),
            Arc::clone(&fixture.frame),
            None,
        )
        .unwrap();
        let parse = OperationId::new(host.ops, 4);
        host.operations.insert(parse, "parse_expression".into());
        let packet = [MacroOutputNode::Token(
            TokenKind::Integer(Integer::from_i64(1)),
            "1".into(),
            fixture.frame.invocation.into(),
        )];
        let mut heap = Vec::new();
        let syntax = host.syntax_value(&packet, &mut heap, 0).unwrap();
        assert_eq!(host.transfer_syntax(&syntax, &heap, 0).unwrap(), packet);
        let fields = Value::Location(
            allocate_heap(
                &mut heap,
                HeapCell::Tuple(vec![host.input(), syntax.clone()].into_boxed_slice()),
            )
            .unwrap(),
        );
        let owner = NominalTypeId::new(ModuleId::new(0), 0);
        host.constructors
            .insert("Parsed".into(), ConstructorId::new(owner, 100));
        host.request(parse, fields, &mut heap, &mut TypeWorkBudget::unbounded())
            .unwrap();
        assert_eq!(host.expressions.len(), 1);
        assert!(!host.type_accounting);
        let expanded = host
            .construct(&mut heap, "Expanded", Some(syntax.clone()))
            .unwrap();
        let TransformerOutput::Expanded(output) = host
            .transfer(&expanded, &heap, &mut TypeWorkBudget::unbounded())
            .unwrap()
        else {
            panic!("expected Expanded");
        };
        assert_eq!(output, packet);
    }

    #[test]
    fn pattern_services_keep_declaration_and_none_host_accounting_separate() {
        use super::{HeapCell, RuntimeFailure, SyntaxHost, Value, allocate_heap};
        use crate::{
            integer::Integer,
            lexer::TokenKind,
            module::ModuleId,
            surface::{SurfaceDeclarationCapture, SurfaceIdentifierCapture, SurfaceSyntaxCapture},
            syntax::{MacroOutputNode, TransformerOutput},
            syntax_resource::SyntaxBudget,
            types::{ConstructorId, NominalTypeId, OperationId, TypeWorkBudget},
        };
        use std::sync::Arc;

        fn trial(
            fixture: &DeclarationHostFixture,
            selected: bool,
            parse_first: bool,
        ) -> (usize, usize, usize, usize) {
            let identifier = SurfaceSyntaxCapture::Identifier(SurfaceIdentifierCapture {
                name: fixture.caller.clone(),
                origin: fixture.caller.span.into(),
            });
            let captures = if selected {
                vec![identifier]
            } else {
                vec![
                    SurfaceSyntaxCapture::Declaration(SurfaceDeclarationCapture {
                        contents: Arc::from([]),
                    }),
                    identifier,
                ]
            };
            let mut budget = SyntaxBudget::default();
            let mut host = fixture.host(&captures, &mut budget).unwrap();
            let parse = OperationId::new(host.ops, 4);
            let make_token = OperationId::new(host.ops, 5);
            host.operations.insert(parse, "parse_pattern".into());
            host.operations.insert(make_token, "make_token".into());
            let owner = NominalTypeId::new(ModuleId::new(0), 0);
            for (index, name) in (100u32..).zip([
                "ParsedPattern",
                "ParseRejected",
                "IntType",
                "MadeToken",
                "NoOrigins",
                "MoreOrigins",
            ]) {
                host.constructors
                    .insert(name.into(), ConstructorId::new(owner, index));
            }
            let span = host.frame.invocation;
            let packet = [MacroOutputNode::Token(
                TokenKind::Wildcard,
                "_".into(),
                span.into(),
            )];
            let mut heap = Vec::<HeapCell>::new();
            let syntax = host.syntax_value(&packet, &mut heap, 0).unwrap();
            if parse_first {
                let fields = Value::Location(
                    allocate_heap(
                        &mut heap,
                        HeapCell::Tuple(vec![host.input(), syntax.clone()].into_boxed_slice()),
                    )
                    .unwrap(),
                );
                host.request(parse, fields, &mut heap, &mut TypeWorkBudget::unbounded())
                    .unwrap();
                assert_eq!(host.patterns.len(), 1);
            }

            let index = if selected { 0 } else { 1 };
            let fields = Value::Location(
                allocate_heap(
                    &mut heap,
                    HeapCell::Tuple(
                        vec![host.input(), Value::integer(Integer::from_i64(index))]
                            .into_boxed_slice(),
                    ),
                )
                .unwrap(),
            );
            let start = host.syntax_work.as_deref().unwrap().consumed();
            host.request(
                fixture.capture,
                fields,
                &mut heap,
                &mut TypeWorkBudget::unbounded(),
            )
            .unwrap();
            let capture_cost = host.syntax_work.as_deref().unwrap().consumed() - start;

            let kind = host.construct(&mut heap, "IntType", None).unwrap();
            let fields = Value::Location(
                allocate_heap(
                    &mut heap,
                    HeapCell::Tuple(vec![kind, Value::String(Arc::from("Int"))].into_boxed_slice()),
                )
                .unwrap(),
            );
            let start = host.syntax_work.as_deref().unwrap().consumed();
            host.request(
                make_token,
                fields,
                &mut heap,
                &mut TypeWorkBudget::unbounded(),
            )
            .unwrap();
            let token_cost = host.syntax_work.as_deref().unwrap().consumed() - start;

            let first = host.issue_origin(span.into()).unwrap();
            let second = host.issue_origin(span.into()).unwrap();
            let mut origins = host.construct(&mut heap, "NoOrigins", None).unwrap();
            for origin in [first, second] {
                let fields = Value::Location(
                    allocate_heap(
                        &mut heap,
                        HeapCell::Tuple(vec![origin, origins].into_boxed_slice()),
                    )
                    .unwrap(),
                );
                origins = host
                    .construct(&mut heap, "MoreOrigins", Some(fields))
                    .unwrap();
            }
            let start = host.syntax_work.as_deref().unwrap().consumed();
            assert_eq!(host.read_origins(&origins, &heap, 10).unwrap().len(), 2);
            let origins_cost = host.syntax_work.as_deref().unwrap().consumed() - start;

            let expanded = host
                .construct(&mut heap, "Expanded", Some(syntax.clone()))
                .unwrap();
            let start = host.syntax_work.as_deref().unwrap().consumed();
            assert_eq!(host.transfer_syntax(&syntax, &heap, 0).unwrap(), packet);
            let direct = host.syntax_work.as_deref().unwrap().consumed() - start;
            let start = host.syntax_work.as_deref().unwrap().consumed();
            let TransformerOutput::Expanded(output) = host
                .transfer(&expanded, &heap, &mut TypeWorkBudget::unbounded())
                .unwrap()
            else {
                panic!("expected Expanded");
            };
            assert_eq!(output, packet);
            let expanded_cost = host.syntax_work.as_deref().unwrap().consumed() - start;
            (
                capture_cost,
                token_cost,
                origins_cost,
                expanded_cost - direct,
            )
        }

        let fixture = DeclarationHostFixture::new();
        let legacy = trial(&fixture, false, false);
        let after_pattern = trial(&fixture, false, true);
        assert_eq!(
            (legacy.0, legacy.1, legacy.2),
            (after_pattern.0, after_pattern.1, after_pattern.2)
        );
        assert_eq!(legacy.3, 0);
        assert_eq!(after_pattern.3, 1);
        let selected = trial(&fixture, true, false);
        assert_eq!(selected.0 - legacy.0, 4); // Origin growth 2+1 and Identifier initial slot.
        assert_eq!(selected.1 - legacy.1, 3); // Token growth 2+1.
        assert_eq!(selected.2 - legacy.2, 4); // Related-origin buffer 1, then 2+1.
        assert_eq!(selected.3, 0);

        let captures = [SurfaceSyntaxCapture::Identifier(SurfaceIdentifierCapture {
            name: fixture.caller.clone(),
            origin: fixture.caller.span.into(),
        })];
        let mut host = SyntaxHost::new(
            &fixture.entry,
            &captures,
            &fixture.source,
            &fixture.caller,
            0,
            Arc::clone(&fixture.contexts),
            Arc::clone(&fixture.frame),
            None,
        )
        .unwrap();
        let parse = OperationId::new(host.ops, 4);
        host.operations.insert(parse, "parse_pattern".into());
        let packet = [MacroOutputNode::Token(
            TokenKind::Wildcard,
            "_".into(),
            fixture.frame.invocation.into(),
        )];
        let mut heap = Vec::new();
        let syntax = host.syntax_value(&packet, &mut heap, 0).unwrap();
        assert_eq!(host.transfer_syntax(&syntax, &heap, 0).unwrap(), packet);
        let fields = Value::Location(
            allocate_heap(
                &mut heap,
                HeapCell::Tuple(vec![host.input(), syntax].into_boxed_slice()),
            )
            .unwrap(),
        );
        assert!(matches!(
            host.request(parse, fields, &mut heap, &mut TypeWorkBudget::unbounded()),
            Err(RuntimeFailure::InvalidControlState)
        ));
    }

    #[test]
    fn expression_fragment_categories_and_eof_return_authenticated_failures() {
        use super::{HeapCell, Value, allocate_heap, constructor_fields};
        use crate::{
            eval::value::CompilerSyntaxHandleKind,
            integer::Integer,
            lexer::TokenKind,
            module::ModuleId,
            parser::{ExpectedForm, FoundToken, ParseReason},
            surface::{
                SurfaceExpr, SurfaceExprKind, SurfaceExpressionCapture, SurfacePattern,
                SurfacePatternCapture, SurfacePatternKind, SurfaceType, SurfaceTypeCapture,
                SurfaceTypeKind,
            },
            syntax::MacroOutputNode,
            syntax_resource::SyntaxBudget,
            types::{ConstructorId, NominalTypeId, OperationId, TypeWorkBudget},
        };
        use std::sync::Arc;

        let mut budget = SyntaxBudget::default();
        let mut host = scalar_host(&mut budget);
        let expression_op = OperationId::new(host.ops, 0);
        let type_op = OperationId::new(host.ops, 1);
        let pattern_op = OperationId::new(host.ops, 2);
        host.operations
            .insert(expression_op, "parse_expression".into());
        host.operations.insert(type_op, "parse_type".into());
        host.operations.insert(pattern_op, "parse_pattern".into());
        let owner = NominalTypeId::new(ModuleId::new(0), 0);
        for (index, name) in (0u32..).zip([
            "Syntax",
            "NoNodes",
            "MoreNodes",
            "GroupNode",
            "Parentheses",
            "PatternNode",
            "TypeNode",
            "TokenNode",
            "IdentifierNode",
            "ExpressionNode",
            "ParseRejected",
        ]) {
            host.constructors
                .insert(name.into(), ConstructorId::new(owner, index));
        }
        let span = host.caller.span;
        let ty = MacroOutputNode::ForwardedType(
            SurfaceTypeCapture {
                ty: SurfaceType {
                    kind: SurfaceTypeKind::Int,
                    span,
                    diagnostic: None,
                },
                contents: Arc::from([]),
            },
            span.into(),
        );
        let pattern = MacroOutputNode::ForwardedPattern(
            SurfacePatternCapture {
                pattern: SurfacePattern {
                    kind: SurfacePatternKind::Wildcard,
                    span,
                    diagnostic: None,
                },
                contents: Arc::from([]),
            },
            span.into(),
        );
        let expression = SurfaceExpressionCapture {
            contains_protected_type: false,
            quote_sites: Default::default(),
            expression: SurfaceExpr {
                kind: SurfaceExprKind::Unit,
                span,
                diagnostic: None,
            },
            contents: Arc::from([]),
        };
        let literal = || {
            MacroOutputNode::Token(
                TokenKind::Integer(Integer::from_i64(1)),
                "1".into(),
                span.into(),
            )
        };
        let cases = [
            (
                expression_op,
                vec![ty],
                ParseReason::ExpectedOperand,
                Some(ExpectedForm::Operand),
                Some(FoundToken::Spelling("Int")),
            ),
            (
                expression_op,
                vec![pattern],
                ParseReason::ExpectedOperand,
                Some(ExpectedForm::Operand),
                Some(FoundToken::Spelling("_")),
            ),
            (
                type_op,
                vec![MacroOutputNode::Expression(expression.clone(), span.into())],
                ParseReason::ExpectedForm,
                Some(ExpectedForm::Type),
                Some(FoundToken::Identifier),
            ),
            (
                pattern_op,
                vec![MacroOutputNode::ForwardedExpression(
                    expression.clone(),
                    span.into(),
                )],
                ParseReason::ExpectedForm,
                Some(ExpectedForm::Pattern),
                Some(FoundToken::Identifier),
            ),
            (
                expression_op,
                vec![
                    literal(),
                    MacroOutputNode::Token(TokenKind::LineEnd, "\n".into(), span.into()),
                ],
                ParseReason::UnexpectedToken,
                None,
                Some(FoundToken::LineEnd),
            ),
        ];
        let mut heap = Vec::<HeapCell>::new();
        for (case, (operation, nodes, reason, expected, found)) in cases.into_iter().enumerate() {
            eprintln!("expression category case {case}");
            let syntax = host.syntax_value_inner(&nodes, &mut heap, 0, true).unwrap();
            let before = (
                host.expressions.len(),
                host.types.len(),
                host.patterns.len(),
                host.parse_failures.len(),
            );
            let fields = Value::Location(
                allocate_heap(
                    &mut heap,
                    HeapCell::Tuple(vec![host.input(), syntax].into_boxed_slice()),
                )
                .unwrap(),
            );
            let result = host
                .request(
                    operation,
                    fields,
                    &mut heap,
                    &mut TypeWorkBudget::unbounded(),
                )
                .unwrap();
            let (tag, Some(handle)) = constructor_fields(&result, &heap).unwrap() else {
                panic!("expected ParseRejected")
            };
            assert_eq!(tag, host.constructor("ParseRejected").unwrap());
            assert_eq!(
                (
                    host.expressions.len(),
                    host.types.len(),
                    host.patterns.len(),
                    host.parse_failures.len()
                ),
                (before.0, before.1, before.2, before.3 + 1)
            );
            let CompilerSyntaxHandleKind::ParseFailure(index) =
                host.admitted_handle(handle).unwrap()
            else {
                panic!("expected failure handle")
            };
            let (diagnostics, resource) = &host.parse_failures[index];
            assert!(resource.is_none());
            assert_eq!(diagnostics[0].reason, reason);
            assert_eq!(diagnostics[0].expected_form(), expected);
            assert_eq!(diagnostics[0].found_token(), found);
            assert_eq!(diagnostics[0].primary.span(), span);
        }

        // Host transfer uses Expression; the parser also receives retained
        // Template ForwardedExpression originals through its existing copier.
        for forwarded in [false, true] {
            let node = if forwarded {
                MacroOutputNode::ForwardedExpression(expression.clone(), span.into())
            } else {
                MacroOutputNode::Expression(expression.clone(), span.into())
            };
            for pattern in [false, true] {
                let mut budget = SyntaxBudget::default();
                let failure = if pattern {
                    crate::parser::parse_macro_pattern(
                        &host.source,
                        span,
                        vec![node.clone()],
                        host.contexts.as_deref().unwrap(),
                        &host.frame,
                        &mut budget,
                    )
                    .unwrap_err()
                } else {
                    crate::parser::parse_macro_type(
                        &host.source,
                        span,
                        vec![node.clone()],
                        host.contexts.as_deref().unwrap(),
                        &host.frame,
                        &mut budget,
                    )
                    .unwrap_err()
                };
                let crate::parser::MacroParseFailure::Syntax {
                    diagnostics,
                    resource: None,
                } = failure
                else {
                    panic!("expected category diagnostic")
                };
                assert_eq!(
                    diagnostics[0].expected_form(),
                    Some(if pattern {
                        ExpectedForm::Pattern
                    } else {
                        ExpectedForm::Type
                    })
                );
            }
        }
    }

    #[test]
    fn fragment_category_and_end_of_input_failures_keep_their_diagnostics() {
        use super::{HeapCell, Value, allocate_heap, constructor_fields};
        use crate::{
            eval::value::CompilerSyntaxHandleKind,
            lexer::TokenKind,
            module::ModuleId,
            parser::{ExpectedForm, FoundToken, ParseReason},
            surface::{
                SurfacePattern, SurfacePatternCapture, SurfacePatternKind, SurfaceType,
                SurfaceTypeCapture, SurfaceTypeKind,
            },
            syntax::{MacroDelimiter, MacroOutputNode},
            syntax_resource::SyntaxBudget,
            types::{ConstructorId, NominalTypeId, OperationId, TypeWorkBudget},
        };
        use std::sync::Arc;

        let mut budget = SyntaxBudget::default();
        let mut host = scalar_host(&mut budget);
        let pattern_op = OperationId::new(host.ops, 0);
        let type_op = OperationId::new(host.ops, 1);
        host.operations.insert(pattern_op, "parse_pattern".into());
        host.operations.insert(type_op, "parse_type".into());
        let owner = NominalTypeId::new(ModuleId::new(0), 0);
        for (index, name) in (0u32..).zip([
            "Syntax",
            "NoNodes",
            "MoreNodes",
            "GroupNode",
            "Parentheses",
            "PatternNode",
            "TypeNode",
            "TokenNode",
            "IdentifierNode",
            "ExpressionNode",
            "ParsedPattern",
            "ParsedType",
            "ParseRejected",
        ]) {
            host.constructors
                .insert(name.into(), ConstructorId::new(owner, index));
        }
        let span = host.caller.span;
        let pattern = || {
            MacroOutputNode::ForwardedPattern(
                SurfacePatternCapture {
                    pattern: SurfacePattern {
                        kind: SurfacePatternKind::Wildcard,
                        span,
                        diagnostic: None,
                    },
                    contents: Arc::from([]),
                },
                span.into(),
            )
        };
        let ty = || {
            MacroOutputNode::ForwardedType(
                SurfaceTypeCapture {
                    ty: SurfaceType {
                        kind: SurfaceTypeKind::Int,
                        span,
                        diagnostic: None,
                    },
                    contents: Arc::from([]),
                },
                span.into(),
            )
        };
        let grouped =
            |node| MacroOutputNode::Group(MacroDelimiter::Parentheses, vec![node], span.into());
        let token =
            |kind, text: &'static str| MacroOutputNode::Token(kind, Arc::from(text), span.into());
        let cases = [
            (
                type_op,
                vec![grouped(pattern())],
                ParseReason::ExpectedForm,
                Some(ExpectedForm::Type),
                Some(FoundToken::Spelling("_")),
            ),
            (
                pattern_op,
                vec![grouped(ty())],
                ParseReason::ExpectedForm,
                Some(ExpectedForm::Pattern),
                Some(FoundToken::Spelling("Int")),
            ),
            (
                pattern_op,
                vec![
                    token(TokenKind::Wildcard, "_"),
                    token(TokenKind::Wildcard, "_"),
                ],
                ParseReason::UnexpectedToken,
                None,
                Some(FoundToken::Spelling("_")),
            ),
            (
                type_op,
                vec![
                    token(TokenKind::IntType, "Int"),
                    token(TokenKind::IntType, "Int"),
                ],
                ParseReason::UnexpectedToken,
                None,
                Some(FoundToken::Spelling("Int")),
            ),
            (
                pattern_op,
                vec![
                    token(TokenKind::Wildcard, "_"),
                    token(TokenKind::LineEnd, "\n"),
                ],
                ParseReason::UnexpectedToken,
                None,
                Some(FoundToken::LineEnd),
            ),
            (
                type_op,
                vec![
                    token(TokenKind::IntType, "Int"),
                    token(TokenKind::LineEnd, "\n"),
                ],
                ParseReason::UnexpectedToken,
                None,
                Some(FoundToken::LineEnd),
            ),
        ];
        let mut heap = Vec::<HeapCell>::new();
        for (operation, output, reason, expected, found) in cases {
            let syntax = host
                .syntax_value_inner(&output, &mut heap, 0, true)
                .unwrap();
            let before = (
                host.types.len(),
                host.patterns.len(),
                host.parse_failures.len(),
            );
            let argument = Value::Location(
                allocate_heap(
                    &mut heap,
                    HeapCell::Tuple(vec![host.input(), syntax].into_boxed_slice()),
                )
                .unwrap(),
            );
            let result = host
                .request(
                    operation,
                    argument,
                    &mut heap,
                    &mut TypeWorkBudget::unbounded(),
                )
                .unwrap();
            let (tag, Some(handle)) = constructor_fields(&result, &heap).unwrap() else {
                panic!("expected rejection")
            };
            assert_eq!(tag, host.constructor("ParseRejected").unwrap());
            assert_eq!(
                (
                    host.types.len(),
                    host.patterns.len(),
                    host.parse_failures.len()
                ),
                (before.0, before.1, before.2 + 1)
            );
            let CompilerSyntaxHandleKind::ParseFailure(index) =
                host.admitted_handle(handle).unwrap()
            else {
                panic!("expected failure handle")
            };
            let (diagnostics, resource) = &host.parse_failures[index];
            assert!(resource.is_none());
            assert!(!diagnostics.is_empty());
            let diagnostic = &diagnostics[0];
            assert_eq!(diagnostic.reason, reason);
            assert_eq!(diagnostic.expected_form(), expected);
            assert_eq!(diagnostic.found_token(), found);
            assert_eq!(diagnostic.primary.span(), span);
        }
    }

    #[test]
    fn expression_host_nested_issued_fragments_obey_retained_depth_on_a_512k_stack() {
        const CHILD: &str = "ASH_EXPRESSION_AST_512K_CHILD";
        if std::env::var_os(CHILD).is_none() {
            let output = std::process::Command::new(std::env::current_exe().unwrap())
                .args([
                    "--exact",
                    "eval::machine::syntax::tests::expression_host_nested_issued_fragments_obey_retained_depth_on_a_512k_stack",
                    "--nocapture", "--test-threads=1",
                ])
                .env(CHILD, "1")
                .output().unwrap();
            print!("{}", String::from_utf8_lossy(&output.stdout));
            let stderr = String::from_utf8_lossy(&output.stderr);
            eprint!("{stderr}");
            assert!(
                output.status.success(),
                "512 KiB child failed: {}",
                output.status
            );
            for marker in [
                "expression stack: adjacent input refused before issuance",
                "expression stack: future owner accepts 128 and refuses 129",
                "expression stack: returned metadata preserved",
                "expression stack: deep unwrap retained contents",
                "expression stack: final contents alias dropped",
                "expression stack: parsed AST reached validated intake and capture",
                "expression stack: parsed owned AST copy boundary and aliases checked",
            ] {
                assert!(stderr.contains(marker), "missing marker {marker}");
            }
            return;
        }
        std::thread::Builder::new()
            .stack_size(512 * 1024)
            .spawn(|| {
                use super::{
                    HeapCell, RuntimeFailure, SyntaxHost, Value, allocate_heap, constructor_fields,
                };
                use crate::{
                    eval::value::CompilerSyntaxHandleKind,
                    integer::Integer,
                    lexer::TokenKind,
                    module::ModuleId,
                    parser::ResourceFailure,
                    surface::{SurfaceExprKind, SurfaceSyntaxCapture},
                    syntax::{MacroOutputNode, charge_new_expression_retention},
                    syntax_resource::SyntaxBudget,
                    types::{ConstructorId, NominalTypeId, OperationId, TypeWorkBudget},
                };
                use std::sync::Arc;

                fn tuple(heap: &mut Vec<HeapCell>, fields: Vec<Value>) -> Value {
                    Value::Location(
                        allocate_heap(heap, HeapCell::Tuple(fields.into_boxed_slice())).unwrap(),
                    )
                }
                fn node(
                    host: &mut SyntaxHost<'_>,
                    heap: &mut Vec<HeapCell>,
                    tag: &str,
                    fields: Vec<Value>,
                ) -> Value {
                    let payload = tuple(heap, fields);
                    host.construct(heap, tag, Some(payload)).unwrap()
                }
                fn syntax(
                    host: &mut SyntaxHost<'_>,
                    heap: &mut Vec<HeapCell>,
                    values: Vec<Value>,
                ) -> Value {
                    let mut nodes = host.construct(heap, "NoNodes", None).unwrap();
                    for value in values.into_iter().rev() {
                        let pair = tuple(heap, vec![value, nodes]);
                        nodes = host.construct(heap, "MoreNodes", Some(pair)).unwrap();
                    }
                    host.construct(heap, "Syntax", Some(nodes)).unwrap()
                }
                fn parse(
                    host: &mut SyntaxHost<'_>,
                    heap: &mut Vec<HeapCell>,
                    op: OperationId,
                    syntax: Value,
                ) -> Result<Value, RuntimeFailure> {
                    let input = tuple(heap, vec![host.input(), syntax]);
                    host.request(op, input, heap, &mut TypeWorkBudget::unbounded())
                }

                let mut budget = SyntaxBudget::default();
                let mut host = scalar_host(&mut budget);
                host.type_accounting = true;
                let parse_op = OperationId::new(host.ops, 0);
                let unwrap_op = OperationId::new(host.ops, 1);
                host.operations.insert(parse_op, "parse_expression".into());
                host.operations
                    .insert(unwrap_op, "expression_syntax".into());
                let owner = NominalTypeId::new(ModuleId::new(0), 0);
                for (index, name) in (0u32..).zip([
                    "Syntax",
                    "NoNodes",
                    "MoreNodes",
                    "GroupNode",
                    "Parentheses",
                    "PatternNode",
                    "TypeNode",
                    "TokenNode",
                    "IdentifierNode",
                    "ExpressionNode",
                    "Parsed",
                    "ParseRejected",
                ]) {
                    host.constructors
                        .insert(name.into(), ConstructorId::new(owner, index));
                }
                let span = host.caller.span;
                let mut heap = Vec::new();
                let raw = MacroOutputNode::Token(
                    TokenKind::Integer(Integer::from_i64(1)),
                    "1".into(),
                    span.into(),
                );
                let input = host.syntax_value_inner(&[raw], &mut heap, 0, true).unwrap();
                let seed = parse(&mut host, &mut heap, parse_op, input).unwrap();
                let (tag, Some(seed)) = constructor_fields(&seed, &heap).unwrap() else {
                    panic!("expected seed")
                };
                assert_eq!(tag, host.constructor("Parsed").unwrap());
                let mut last = seed.clone();
                let mut previous = None;
                let origin = host.issue_origin(span.into()).unwrap();
                let mut accepted = 0usize;
                let mut refused = false;
                for _ in 0..128 {
                    let protected = node(
                        &mut host,
                        &mut heap,
                        "ExpressionNode",
                        vec![last.clone(), origin.clone()],
                    );
                    let inner = syntax(&mut host, &mut heap, vec![protected]);
                    let delimiter = host.construct(&mut heap, "Parentheses", None).unwrap();
                    let group = node(
                        &mut host,
                        &mut heap,
                        "GroupNode",
                        vec![delimiter, inner, origin.clone()],
                    );
                    let input = syntax(&mut host, &mut heap, vec![group]);
                    let before = host.expressions.len();
                    let result = match parse(&mut host, &mut heap, parse_op, input) {
                        Ok(result) => result,
                        Err(RuntimeFailure::Report(report))
                            if report.primary.reason_code() == "internal.resource.structural-depth" =>
                        {
                            assert_eq!(host.expressions.len(), before);
                            refused = true;
                            break;
                        }
                        other => panic!("unexpected result: {other:?}"),
                    };
                    let (tag, Some(handle)) = constructor_fields(&result, &heap).unwrap() else {
                        panic!("expected service result")
                    };
                    if tag == host.constructor("ParseRejected").unwrap() {
                        let CompilerSyntaxHandleKind::ParseFailure(index) =
                            host.admitted_handle(handle).unwrap()
                        else {
                            panic!("expected failure handle")
                        };
                        assert_eq!(
                            host.parse_failures[index].1,
                            Some(ResourceFailure::StructuralDepth { limit: 128 })
                        );
                        assert_eq!(host.expressions.len(), before);
                        refused = true;
                        break;
                    }
                    assert_eq!(tag, host.constructor("Parsed").unwrap());
                    previous = Some(last.clone());
                    last = handle.clone();
                    accepted += 1;
                    let CompilerSyntaxHandleKind::Expression(index) =
                        host.admitted_handle(handle).unwrap()
                    else {
                        panic!("expected Expression handle")
                    };
                    if accepted == 1 {
                        let location = host.expressions[index]
                            .expression
                            .diagnostic
                            .as_deref()
                            .expect("the returned capture keeps its diagnostic location");
                        assert_eq!(location.primary.primary(), span);
                        assert!(location.related.iter().any(|cause| cause.primary() == span));
                        assert!(location.captured_expression);
                        assert!(
                            location
                                .frames
                                .iter()
                                .any(|frame| Arc::ptr_eq(frame, &host.frame))
                        );
                        eprintln!("expression stack: returned metadata preserved");
                    }
                    assert_eq!(
                        charge_new_expression_retention(
                            &host.expressions[index],
                            0,
                            &mut SyntaxBudget::default()
                        )
                        .unwrap(),
                        Some(false)
                    );
                }
                assert!(
                    accepted == 42 && refused,
                    "accepted={accepted}, refused={refused}"
                );
                assert_eq!(2 + 3 * accepted, 128);
                eprintln!(
                    "expression stack: adjacent input refused before issuance after {accepted} wrappers"
                );
                let CompilerSyntaxHandleKind::Expression(index) =
                    host.admitted_handle(&last).unwrap()
                else {
                    panic!("expected Expression handle")
                };
                assert!(matches!(
                    charge_new_expression_retention(
                        &host.expressions[index],
                        1,
                        &mut SyntaxBudget::default(),
                    ),
                    Err(ResourceFailure::StructuralDepth { limit: 128 })
                ));
                let previous = previous.expect("the preceding issued capture exists");
                for (groups, succeeds) in [(1usize, true), (2, false)] {
                    let protected = node(
                        &mut host,
                        &mut heap,
                        "ExpressionNode",
                        vec![previous.clone(), origin.clone()],
                    );
                    let mut input = syntax(&mut host, &mut heap, vec![protected]);
                    for _ in 0..groups {
                        let delimiter = host.construct(&mut heap, "Parentheses", None).unwrap();
                        let group = node(
                            &mut host,
                            &mut heap,
                            "GroupNode",
                            vec![delimiter, input, origin.clone()],
                        );
                        input = syntax(&mut host, &mut heap, vec![group]);
                    }
                    let transferred = host.transfer_syntax_inner(&input, &heap, 0, true).unwrap();
                    let copy = crate::syntax::copy_fragment_output_with_type(
                        &transferred,
                        &mut SyntaxBudget::default(),
                    );
                    if succeeds {
                        drop(copy.unwrap());
                    } else {
                        assert!(matches!(
                            copy,
                            Err(crate::parser::MacroParseFailure::Syntax {
                                resource: Some(ResourceFailure::StructuralDepth { limit: 128 }),
                                ..
                            })
                        ));
                    }
                    drop(transferred);
                    let before = host.expressions.len();
                    let result = parse(&mut host, &mut heap, parse_op, input).unwrap();
                    let (tag, Some(handle)) = constructor_fields(&result, &heap).unwrap() else {
                        panic!("expected Expression service result")
                    };
                    if succeeds {
                        assert_eq!(tag, host.constructor("Parsed").unwrap());
                        assert_eq!(host.expressions.len(), before + 1);
                    } else {
                        assert_eq!(tag, host.constructor("ParseRejected").unwrap());
                        assert_eq!(host.expressions.len(), before);
                        let CompilerSyntaxHandleKind::ParseFailure(index) =
                            host.admitted_handle(handle).unwrap()
                        else {
                            panic!("expected failure handle")
                        };
                        assert_eq!(
                            host.parse_failures[index].1,
                            Some(ResourceFailure::StructuralDepth { limit: 128 })
                        );
                    }
                }
                eprintln!("expression stack: future owner accepts 128 and refuses 129");
                let alias = Arc::clone(&host.expressions[index].contents);
                let weak = Arc::downgrade(&alias);
                let unwrapped = host
                    .request(unwrap_op, last, &mut heap, &mut TypeWorkBudget::unbounded())
                    .unwrap();
                let returned = host
                    .transfer_syntax_inner(&unwrapped, &heap, 0, true)
                    .unwrap();
                let [MacroOutputNode::Group(_, _, _)] = returned.as_slice() else {
                    panic!("expected original group")
                };
                eprintln!("expression stack: deep unwrap retained contents");
                drop(returned);
                drop(heap);
                drop(host);
                assert_eq!(Arc::strong_count(&alias), 1);
                drop(alias);
                assert!(weak.upgrade().is_none());
                eprintln!("expression stack: final contents alias dropped");

                // These are parser-built Resume ASTs, not nested contents
                // wrappers. Their leaf diagnostic adds one retained edge.
                for (height, succeeds) in [(124usize, true), (125, false)] {
                    let mut budget = SyntaxBudget::default();
                    let mut host = scalar_host(&mut budget);
                    host.type_accounting = true;
                    let parse_op = OperationId::new(host.ops, 0);
                    let unwrap_op = OperationId::new(host.ops, 1);
                    host.operations.insert(parse_op, "parse_expression".into());
                    host.operations.insert(unwrap_op, "expression_syntax".into());
                    let owner = NominalTypeId::new(ModuleId::new(0), 0);
                    for (index, name) in (0u32..).zip([
                        "Syntax", "NoNodes", "MoreNodes", "GroupNode", "Parentheses",
                        "PatternNode", "TypeNode", "TokenNode", "IdentifierNode",
                        "ExpressionNode", "Parsed", "ParseRejected",
                    ]) {
                        host.constructors.insert(name.into(), ConstructorId::new(owner, index));
                    }
                    let span = host.caller.span;
                    let mut raw = (0..height)
                        .map(|_| MacroOutputNode::Token(TokenKind::Resume, "resume".into(), span.into()))
                        .collect::<Vec<_>>();
                    raw.push(MacroOutputNode::Token(
                        TokenKind::Integer(Integer::from_i64(1)), "1".into(), span.into(),
                    ));
                    let mut heap = Vec::new();
                    let input = host.syntax_value_inner(&raw, &mut heap, 0, true).unwrap();
                    let parsed = parse(&mut host, &mut heap, parse_op, input).unwrap();
                    let (tag, Some(handle)) = constructor_fields(&parsed, &heap).unwrap() else {
                        panic!("expected the raw Expression result")
                    };
                    assert_eq!(tag, host.constructor("Parsed").unwrap());
                    let handle = handle.clone();
                    let CompilerSyntaxHandleKind::Expression(index) = host.admitted_handle(&handle).unwrap() else {
                        panic!("expected an Expression handle")
                    };
                    let mut expression = &host.expressions[index].expression;
                    for _ in 0..height {
                        let SurfaceExprKind::Resume(value) = &expression.kind else {
                            panic!("expected parsed Resume AST")
                        };
                        expression = value;
                    }
                    assert!(matches!(expression.kind, SurfaceExprKind::Integer(_)));
                    assert!(expression.diagnostic.is_some());
                    let alias = Arc::clone(&host.expressions[index].contents);
                    let weak = Arc::downgrade(&alias);
                    // Move the parsed capture into a validated Some host and
                    // issue it through the real capture service.
                    assert_eq!(index + 1, host.expressions.len());
                    let source_capture = host.expressions.pop().unwrap();
                    let captures = [SurfaceSyntaxCapture::Expression(source_capture)];
                    let fixture = DeclarationHostFixture::new();
                    let mut intake_budget = SyntaxBudget::default();
                    let mut intake = SyntaxHost::new(
                        &fixture.entry, &captures, &host.source, &host.caller, 0,
                        Arc::clone(host.contexts.as_ref().unwrap()), Arc::clone(&host.frame), Some(&mut intake_budget),
                    ).unwrap();
                    assert_eq!(Arc::strong_count(&alias), 3);
                    intake.constructors.insert(
                        "ExpressionCapture".into(),
                        ConstructorId::new(fixture.constructors["Expanded"].owner(), 100),
                    );
                    let mut intake_heap = Vec::new();
                    let input = tuple(&mut intake_heap, vec![intake.input(), Value::integer(Integer::from_i64(0))]);
                    let result = intake.request(fixture.capture, input, &mut intake_heap, &mut TypeWorkBudget::unbounded()).unwrap();
                    let (tag, Some(capture)) = constructor_fields(&result, &intake_heap).unwrap() else {
                        panic!("expected Captured")
                    };
                    assert_eq!(tag, intake.constructor("Captured").unwrap());
                    let (tag, Some(intake_handle)) = constructor_fields(capture, &intake_heap).unwrap() else {
                        panic!("expected ExpressionCapture")
                    };
                    assert_eq!(tag, intake.constructor("ExpressionCapture").unwrap());
                    let intake_handle = intake_handle.clone();
                    assert_eq!(intake.expressions.len(), 1);
                    assert_eq!(Arc::strong_count(&alias), 4);
                    let intake_syntax = intake.request(fixture.expression_syntax, intake_handle, &mut intake_heap, &mut TypeWorkBudget::unbounded()).unwrap();
                    let output = intake.transfer_syntax_inner(&intake_syntax, &intake_heap, 0, true).unwrap();
                    assert_eq!(output.len(), height + 1);
                    drop(output);
                    drop(intake_heap);
                    drop(intake);
                    let [SurfaceSyntaxCapture::Expression(source_capture)] = captures else {
                        unreachable!()
                    };
                    host.expressions.push(source_capture);
                    assert_eq!(Arc::strong_count(&alias), 2);
                    let unwrapped = host.request(unwrap_op, handle.clone(), &mut heap, &mut TypeWorkBudget::unbounded()).unwrap();
                    let unwrapped = host.transfer_syntax_inner(&unwrapped, &heap, 0, true).unwrap();
                    assert_eq!(unwrapped.len(), height + 1);
                    drop(unwrapped);
                    let origin = host.issue_origin(span.into()).unwrap();
                    let protected = node(&mut host, &mut heap, "ExpressionNode", vec![handle, origin]);
                    let input = syntax(&mut host, &mut heap, vec![protected]);
                    let transferred = host.transfer_syntax_inner(&input, &heap, 0, true).unwrap();
                    assert!(matches!(transferred.as_slice(), [MacroOutputNode::Expression(..)]));
                    let copy = crate::syntax::copy_fragment_output_with_type(&transferred, &mut SyntaxBudget::default());
                    if succeeds {
                        drop(copy.unwrap());
                    } else {
                        assert!(matches!(copy, Err(crate::parser::MacroParseFailure::Syntax {
                            resource: Some(ResourceFailure::StructuralDepth { limit: 128 }), ..
                        })));
                    }
                    drop(transferred);
                    let before = host.expressions.len();
                    let result = parse(&mut host, &mut heap, parse_op, input).unwrap();
                    let (tag, Some(handle)) = constructor_fields(&result, &heap).unwrap() else {
                        panic!("expected protected Expression result")
                    };
                    if succeeds {
                        assert_eq!(tag, host.constructor("Parsed").unwrap());
                        assert_eq!(host.expressions.len(), before + 1);
                    } else {
                        assert_eq!(tag, host.constructor("ParseRejected").unwrap());
                        assert_eq!(host.expressions.len(), before);
                        let CompilerSyntaxHandleKind::ParseFailure(index) = host.admitted_handle(handle).unwrap() else {
                            panic!("expected a failure handle")
                        };
                        assert_eq!(host.parse_failures[index].1, Some(ResourceFailure::StructuralDepth { limit: 128 }));
                    }
                    drop(raw);
                    drop(heap);
                    drop(host);
                    assert_eq!(Arc::strong_count(&alias), 1);
                    drop(alias);
                    assert!(weak.upgrade().is_none());
                }
                eprintln!("expression stack: parsed AST reached validated intake and capture");
                eprintln!("expression stack: parsed owned AST copy boundary and aliases checked");
            })
            .unwrap()
            .join()
            .unwrap();
    }

    #[test]
    fn pattern_host_nested_issued_fragments_obey_retained_depth_on_a_512k_stack() {
        const CHILD: &str = "ASH_PATTERN_AST_512K_CHILD";
        if std::env::var_os(CHILD).is_none() {
            let output = std::process::Command::new(std::env::current_exe().unwrap())
                .args([
                    "--exact",
                    "eval::machine::syntax::tests::pattern_host_nested_issued_fragments_obey_retained_depth_on_a_512k_stack",
                    "--nocapture",
                    "--test-threads=1",
                ])
                .env(CHILD, "1")
                .output()
                .unwrap();
            print!("{}", String::from_utf8_lossy(&output.stdout));
            let stderr = String::from_utf8_lossy(&output.stderr);
            eprint!("{stderr}");
            assert!(
                output.status.success(),
                "512 KiB child failed: {}",
                output.status
            );
            for marker in [
                "pattern stack: returned owner reaches 128",
                "pattern stack: adjacent wrapper refused before issuance",
                "pattern stack: deep unwrap and reparse preserved the binder",
                "pattern stack: future owner accepts 128 and refuses 129",
                "pattern stack: final PatternNode transferred",
                "pattern stack: final contents alias dropped",
            ] {
                assert!(stderr.contains(marker), "missing marker {marker}");
            }
            return;
        }
        std::thread::Builder::new()
            .stack_size(512 * 1024)
            .spawn(|| {
                use super::{
                    HeapCell, RuntimeFailure, SyntaxHost, Value, allocate_heap, constructor_fields,
                };
                use crate::{
                    eval::value::CompilerSyntaxHandleKind,
                    module::ModuleId,
                    parser::ResourceFailure,
                    surface::SurfacePatternKind,
                    syntax::{MacroOutputNode, TransformerOutput, charge_new_pattern_retention},
                    syntax_resource::SyntaxBudget,
                    types::{ConstructorId, NominalTypeId, OperationId, TypeWorkBudget},
                };
                use std::sync::Arc;

                fn tuple(heap: &mut Vec<HeapCell>, fields: Vec<Value>) -> Value {
                    Value::Location(
                        allocate_heap(heap, HeapCell::Tuple(fields.into_boxed_slice())).unwrap(),
                    )
                }
                fn node(
                    host: &mut SyntaxHost<'_>,
                    heap: &mut Vec<HeapCell>,
                    tag: &str,
                    fields: Vec<Value>,
                ) -> Value {
                    let payload = tuple(heap, fields);
                    host.construct(heap, tag, Some(payload)).unwrap()
                }
                fn syntax(
                    host: &mut SyntaxHost<'_>,
                    heap: &mut Vec<HeapCell>,
                    values: Vec<Value>,
                ) -> Value {
                    let mut nodes = host.construct(heap, "NoNodes", None).unwrap();
                    for value in values.into_iter().rev() {
                        let pair = tuple(heap, vec![value, nodes]);
                        nodes = host.construct(heap, "MoreNodes", Some(pair)).unwrap();
                    }
                    host.construct(heap, "Syntax", Some(nodes)).unwrap()
                }
                fn parse(
                    host: &mut SyntaxHost<'_>,
                    heap: &mut Vec<HeapCell>,
                    operation: OperationId,
                    syntax: Value,
                ) -> Result<Value, RuntimeFailure> {
                    let input = tuple(heap, vec![host.input(), syntax]);
                    host.request(operation, input, heap, &mut TypeWorkBudget::unbounded())
                }

                let mut budget = SyntaxBudget::default();
                let mut host = scalar_host(&mut budget);
                host.type_accounting = true;
                let parse_op = OperationId::new(host.ops, 0);
                let unwrap_op = OperationId::new(host.ops, 1);
                host.operations.insert(parse_op, "parse_pattern".into());
                host.operations.insert(unwrap_op, "pattern_syntax".into());
                let owner = NominalTypeId::new(ModuleId::new(0), 0);
                for (index, name) in (0u32..).zip([
                    "Syntax",
                    "NoNodes",
                    "MoreNodes",
                    "GroupNode",
                    "Parentheses",
                    "PatternNode",
                    "TypeNode",
                    "TokenNode",
                    "IdentifierNode",
                    "ExpressionNode",
                    "ParsedPattern",
                    "ParseRejected",
                    "Expanded",
                ]) {
                    host.constructors
                        .insert(name.into(), ConstructorId::new(owner, index));
                }
                let span = host.caller.span;
                let mut heap = Vec::new();
                let binder = MacroOutputNode::Identifier(host.caller.clone(), span.into());
                let input = host
                    .syntax_value_inner(&[binder], &mut heap, 0, true)
                    .unwrap();
                let seed = parse(&mut host, &mut heap, parse_op, input).unwrap();
                let (tag, payload) = constructor_fields(&seed, &heap).unwrap();
                assert_eq!(tag, host.constructor("ParsedPattern").unwrap());
                let mut last = payload.unwrap().clone();
                let mut constructor = host.caller.clone();
                constructor.text = "Wrap".into();
                let packet = MacroOutputNode::Identifier(constructor, span.into());
                host.syntax_value_inner(&[packet], &mut heap, 0, true)
                    .unwrap();
                let wrap = host.handle(CompilerSyntaxHandleKind::Identifier(
                    host.identifiers.len() - 1,
                ));
                let origin = host.issue_origin(span.into()).unwrap();
                let mut accepted = 0usize;
                let mut refused = false;
                let mut penultimate = None;
                for layers in 1..=128 {
                    let before = host.patterns.len();
                    let protected = node(
                        &mut host,
                        &mut heap,
                        "PatternNode",
                        vec![last.clone(), origin.clone()],
                    );
                    let inner = syntax(&mut host, &mut heap, vec![protected]);
                    let delimiter = host.construct(&mut heap, "Parentheses", None).unwrap();
                    let group = node(
                        &mut host,
                        &mut heap,
                        "GroupNode",
                        vec![delimiter, inner, origin.clone()],
                    );
                    let name = node(
                        &mut host,
                        &mut heap,
                        "IdentifierNode",
                        vec![wrap.clone(), origin.clone()],
                    );
                    let input = syntax(&mut host, &mut heap, vec![name, group]);
                    let result = match parse(&mut host, &mut heap, parse_op, input) {
                        Ok(result) => result,
                        Err(RuntimeFailure::Report(report)) => {
                            assert_eq!(
                                report.primary.reason_code(),
                                "internal.resource.structural-depth"
                            );
                            assert_eq!(host.patterns.len(), before);
                            refused = true;
                            break;
                        }
                        Err(error) => panic!("unexpected Pattern request failure: {error:?}"),
                    };
                    let (tag, payload) = constructor_fields(&result, &heap).unwrap();
                    let value = payload.unwrap().clone();
                    if tag == host.constructor("ParsedPattern").unwrap() {
                        assert_eq!(host.patterns.len(), before + 1);
                        penultimate = Some(last.clone());
                        last = value;
                        accepted = layers;
                        let capture = host.patterns.last().unwrap();
                        assert_eq!(
                            charge_new_pattern_retention(capture, 0, &mut SyntaxBudget::default())
                                .unwrap(),
                            Some(false)
                        );
                        let mut current = &capture.pattern;
                        for _ in 0..layers {
                            let SurfacePatternKind::Constructor {
                                payload: Some(child),
                                ..
                            } = &current.kind
                            else {
                                panic!("missing constructor layer");
                            };
                            current = child;
                        }
                        assert!(matches!(current.kind, SurfacePatternKind::Binder(_)));
                        if layers == 1 {
                            host.request(
                                unwrap_op,
                                last.clone(),
                                &mut heap,
                                &mut TypeWorkBudget::unbounded(),
                            )
                            .unwrap();
                        }
                    } else {
                        assert_eq!(tag, host.constructor("ParseRejected").unwrap());
                        assert_eq!(host.patterns.len(), before);
                        let CompilerSyntaxHandleKind::ParseFailure(index) =
                            host.admitted_handle(&value).unwrap()
                        else {
                            panic!("expected failure handle");
                        };
                        assert_eq!(
                            host.parse_failures[index].1,
                            Some(ResourceFailure::StructuralDepth { limit: 128 })
                        );
                        refused = true;
                        break;
                    }
                }
                assert!(refused);
                assert_eq!(accepted, 42);
                let CompilerSyntaxHandleKind::Pattern(last_index) =
                    host.admitted_handle(&last).unwrap()
                else {
                    panic!("expected the last Pattern handle");
                };
                let previous = penultimate.unwrap();
                let CompilerSyntaxHandleKind::Pattern(previous_index) =
                    host.admitted_handle(&previous).unwrap()
                else {
                    panic!("expected the preceding Pattern handle");
                };
                let previous_contents = Arc::clone(&host.patterns[previous_index].contents);
                let unwrapped = host
                    .request(
                        unwrap_op,
                        last.clone(),
                        &mut heap,
                        &mut TypeWorkBudget::unbounded(),
                    )
                    .unwrap();
                let returned = host
                    .transfer_syntax_inner(&unwrapped, &heap, 0, true)
                    .unwrap();
                let [
                    MacroOutputNode::Identifier(_, _),
                    MacroOutputNode::Group(_, children, _),
                ] = returned.as_slice()
                else {
                    panic!("expected the unwrapped constructor and group");
                };
                let [MacroOutputNode::ForwardedPattern(inner, _)] = children.as_slice() else {
                    panic!("expected the preceding protected Pattern");
                };
                assert!(Arc::ptr_eq(&inner.contents, &previous_contents));
                let reparsed = parse(&mut host, &mut heap, parse_op, unwrapped).unwrap();
                let (tag, Some(handle)) = constructor_fields(&reparsed, &heap).unwrap() else {
                    panic!("expected the reparsed Pattern handle");
                };
                assert_eq!(tag, host.constructor("ParsedPattern").unwrap());
                let CompilerSyntaxHandleKind::Pattern(index) =
                    host.admitted_handle(handle).unwrap()
                else {
                    panic!("expected a Pattern handle");
                };
                let mut current = &host.patterns[index].pattern;
                for _ in 0..accepted {
                    let SurfacePatternKind::Constructor {
                        payload: Some(child),
                        ..
                    } = &current.kind
                    else {
                        panic!("missing a reparsed constructor layer");
                    };
                    current = child;
                }
                let SurfacePatternKind::Binder(binder) = &current.kind else {
                    panic!("expected the reparsed binder");
                };
                assert_eq!(binder.name.text, host.caller.text);
                assert_eq!(binder.name.span, host.caller.span);
                assert_eq!(binder.name.introduction, host.caller.introduction);
                assert_eq!(binder.name.introduced_at, host.caller.introduced_at);
                assert_eq!(binder.name.written, host.caller.written);
                let diagnostic = binder.name.diagnostic.as_ref().unwrap();
                assert_eq!(diagnostic.primary.primary(), host.caller.span);
                assert!(
                    diagnostic
                        .frames
                        .iter()
                        .any(|frame| Arc::ptr_eq(frame, &host.frame))
                );
                drop(returned);
                eprintln!("pattern stack: deep unwrap and reparse preserved the binder");

                // The preceding capture's retained path is 125. One group and
                // the new capture's two owners reach 128; two groups reach 129.
                for (groups, succeeds) in [(1usize, true), (2, false)] {
                    let protected = node(
                        &mut host,
                        &mut heap,
                        "PatternNode",
                        vec![previous.clone(), origin.clone()],
                    );
                    let mut input = syntax(&mut host, &mut heap, vec![protected]);
                    for _ in 0..groups {
                        let delimiter = host.construct(&mut heap, "Parentheses", None).unwrap();
                        let group = node(
                            &mut host,
                            &mut heap,
                            "GroupNode",
                            vec![delimiter, input, origin.clone()],
                        );
                        input = syntax(&mut host, &mut heap, vec![group]);
                    }
                    // Both inputs pass transfer; the adjacent refusal belongs
                    // to the subsequent future-contents copy preflight.
                    let transferred = host.transfer_syntax_inner(&input, &heap, 0, true).unwrap();
                    let copy = crate::syntax::copy_fragment_output(
                        &transferred,
                        &mut SyntaxBudget::default(),
                    );
                    if succeeds {
                        drop(copy.unwrap());
                    } else {
                        assert!(matches!(
                            copy,
                            Err(crate::parser::MacroParseFailure::Syntax {
                                resource: Some(ResourceFailure::StructuralDepth { limit: 128 }),
                                ..
                            })
                        ));
                    }
                    drop(transferred);
                    let before = host.patterns.len();
                    let result = parse(&mut host, &mut heap, parse_op, input).unwrap();
                    let (tag, Some(handle)) = constructor_fields(&result, &heap).unwrap() else {
                        panic!("expected a Pattern service result");
                    };
                    if succeeds {
                        assert_eq!(tag, host.constructor("ParsedPattern").unwrap());
                        assert_eq!(host.patterns.len(), before + 1);
                        let CompilerSyntaxHandleKind::Pattern(index) =
                            host.admitted_handle(handle).unwrap()
                        else {
                            panic!("expected a Pattern handle");
                        };
                        assert_eq!(
                            charge_new_pattern_retention(
                                &host.patterns[index],
                                0,
                                &mut SyntaxBudget::default(),
                            )
                            .unwrap(),
                            Some(false)
                        );
                        assert!(matches!(
                            charge_new_pattern_retention(
                                &host.patterns[index],
                                1,
                                &mut SyntaxBudget::default(),
                            ),
                            Err(ResourceFailure::StructuralDepth { limit: 128 })
                        ));
                    } else {
                        assert_eq!(tag, host.constructor("ParseRejected").unwrap());
                        assert_eq!(host.patterns.len(), before);
                        let CompilerSyntaxHandleKind::ParseFailure(index) =
                            host.admitted_handle(handle).unwrap()
                        else {
                            panic!("expected a failure handle");
                        };
                        assert_eq!(
                            host.parse_failures[index].1,
                            Some(ResourceFailure::StructuralDepth { limit: 128 })
                        );
                    }
                }
                drop(previous_contents);
                eprintln!("pattern stack: future owner accepts 128 and refuses 129");
                let capture = &host.patterns[last_index];
                assert!(matches!(
                    charge_new_pattern_retention(capture, 1, &mut SyntaxBudget::default()),
                    Err(ResourceFailure::StructuralDepth { limit: 128 })
                ));
                let alias = Arc::clone(&capture.contents);
                let weak = Arc::downgrade(&alias);
                eprintln!("pattern stack: returned owner reaches 128");
                eprintln!(
                    "pattern stack: adjacent wrapper refused before issuance ({accepted} accepted)"
                );
                let protected = node(&mut host, &mut heap, "PatternNode", vec![last, origin]);
                let output = syntax(&mut host, &mut heap, vec![protected]);
                let expanded = host.construct(&mut heap, "Expanded", Some(output)).unwrap();
                let TransformerOutput::Expanded(nodes) = host
                    .transfer(&expanded, &heap, &mut TypeWorkBudget::unbounded())
                    .unwrap()
                else {
                    panic!("expected Expanded");
                };
                let [MacroOutputNode::ForwardedPattern(capture, _)] = nodes.as_slice() else {
                    panic!("expected forwarded Pattern");
                };
                assert!(Arc::ptr_eq(&capture.contents, &alias));
                eprintln!("pattern stack: final PatternNode transferred");
                drop(nodes);
                drop(heap);
                drop(host);
                assert_eq!(Arc::strong_count(&alias), 1);
                drop(alias);
                assert!(weak.upgrade().is_none());
                eprintln!("pattern stack: final contents alias dropped");
            })
            .unwrap()
            .join()
            .unwrap();
    }

    #[test]
    fn pattern_host_raw_result_obeys_composed_depth_on_a_512k_stack() {
        const CHILD: &str = "ASH_PATTERN_RAW_AST_512K_CHILD";
        if std::env::var_os(CHILD).is_none() {
            let output = std::process::Command::new(std::env::current_exe().unwrap())
                .args([
                    "--exact",
                    "eval::machine::syntax::tests::pattern_host_raw_result_obeys_composed_depth_on_a_512k_stack",
                    "--nocapture",
                    "--test-threads=1",
                ])
                .env(CHILD, "1")
                .output()
                .unwrap();
            print!("{}", String::from_utf8_lossy(&output.stdout));
            let stderr = String::from_utf8_lossy(&output.stderr);
            eprint!("{stderr}");
            assert!(
                output.status.success(),
                "512 KiB child failed: {}",
                output.status
            );
            for marker in [
                "raw Pattern stack: 15 groups preserve returned binder metadata",
                "raw Pattern stack: 16 groups refused without Pattern issuance",
            ] {
                assert!(stderr.contains(marker), "missing marker {marker}");
            }
            return;
        }
        std::thread::Builder::new()
            .stack_size(512 * 1024)
            .spawn(|| {
                use super::{HeapCell, Value, allocate_heap, constructor_fields};
                use crate::{
                    module::ModuleId,
                    parser::{ResourceFailure, STRUCTURAL_DEPTH_LIMIT},
                    source::{ByteRange, SourceFile},
                    surface::SurfacePatternKind,
                    syntax::{
                        DiagnosticLocation, ExpansionFrame, MacroDelimiter, MacroOrigin,
                        MacroOutputNode, charge_new_pattern_retention,
                    },
                    syntax_resource::SyntaxBudget,
                    types::{ConstructorId, NominalTypeId, OperationId, TypeWorkBudget},
                };
                use std::sync::Arc;

                for layers in [15usize, 16] {
                    let mut budget = SyntaxBudget::default();
                    let mut host = scalar_host(&mut budget);
                    let parse = OperationId::new(host.ops, 0);
                    host.operations.insert(parse, "parse_pattern".into());
                    let owner = NominalTypeId::new(ModuleId::new(0), 0);
                    for (index, name) in (0u32..).zip([
                        "Syntax",
                        "NoNodes",
                        "MoreNodes",
                        "GroupNode",
                        "Parentheses",
                        "PatternNode",
                        "TypeNode",
                        "TokenNode",
                        "IdentifierNode",
                        "ExpressionNode",
                        "ParsedPattern",
                        "ParseRejected",
                    ]) {
                        host.constructors
                            .insert(name.into(), ConstructorId::new(owner, index));
                    }
                    let text = format!("{}value{}", "(".repeat(layers), ")".repeat(layers));
                    let source = SourceFile::new("raw-deep-pattern.ash", text).unwrap();
                    let whole = source
                        .span(ByteRange::new(0, source.text().len() as u32).unwrap())
                        .unwrap();
                    let leaf = source
                        .span(ByteRange::new(layers as u32, layers as u32 + 5).unwrap())
                        .unwrap();
                    let previous = Arc::new(ExpansionFrame {
                        invocation: leaf,
                        definition: whole,
                    });
                    let combined = MacroOrigin::combined(
                        vec![leaf.into(), whole.into()],
                        Arc::clone(&previous),
                    )
                    .unwrap();
                    let mut name = host.caller.clone();
                    name.text = "value".into();
                    name.span = leaf;
                    let mut prior = DiagnosticLocation::new(combined.clone());
                    prior.related.push(whole.into());
                    prior.frames.push(Arc::clone(&previous));
                    name.diagnostic = Some(Box::new(prior));
                    let mut raw = vec![MacroOutputNode::Identifier(name, leaf.into())];
                    for depth in (0..layers).rev() {
                        let span = source
                            .span(
                                ByteRange::new(depth as u32, (source.text().len() - depth) as u32)
                                    .unwrap(),
                            )
                            .unwrap();
                        raw = vec![MacroOutputNode::Group(
                            MacroDelimiter::Parentheses,
                            raw,
                            span.into(),
                        )];
                    }
                    host.source = source;
                    host.frame = Arc::new(ExpansionFrame {
                        invocation: whole,
                        definition: leaf,
                    });
                    host.caller.span = whole;
                    let mut heap = Vec::<HeapCell>::new();
                    let syntax = host.syntax_value_inner(&raw, &mut heap, 0, true).unwrap();
                    let fields = Value::Location(
                        allocate_heap(
                            &mut heap,
                            HeapCell::Tuple(vec![host.input(), syntax].into_boxed_slice()),
                        )
                        .unwrap(),
                    );
                    let parsed = host
                        .request(parse, fields, &mut heap, &mut TypeWorkBudget::unbounded())
                        .unwrap();
                    let (tag, Some(_)) = constructor_fields(&parsed, &heap).unwrap() else {
                        panic!("expected a raw Pattern service result");
                    };
                    assert_eq!(
                        1 + layers * 8,
                        if layers == 15 {
                            121
                        } else {
                            STRUCTURAL_DEPTH_LIMIT + 1
                        }
                    );
                    if layers == 15 {
                        assert_eq!(tag, host.constructor("ParsedPattern").unwrap());
                        assert_eq!(host.patterns.len(), 1);
                        let capture = host.patterns.last().unwrap();
                        assert_eq!(
                            charge_new_pattern_retention(capture, 0, &mut SyntaxBudget::default())
                                .unwrap(),
                            Some(false)
                        );
                        let SurfacePatternKind::Binder(binder) = &capture.pattern.kind else {
                            panic!("expected the returned binder");
                        };
                        assert_eq!(binder.name.text, "value");
                        assert_eq!(binder.name.span, leaf);
                        assert_eq!(binder.name.introduction, 0);
                        assert_eq!(binder.name.introduced_at, None);
                        assert!(binder.name.written);
                        let diagnostic = binder.name.diagnostic.as_ref().unwrap();
                        assert_eq!(diagnostic.primary, MacroOrigin::Source(leaf));
                        assert_eq!(diagnostic.related, [combined, whole.into()]);
                        assert_eq!(diagnostic.frames.len(), 2);
                        assert!(Arc::ptr_eq(&diagnostic.frames[0], &previous));
                        assert!(Arc::ptr_eq(&diagnostic.frames[1], &host.frame));
                        let alias = Arc::clone(&capture.contents);
                        let weak = Arc::downgrade(&alias);
                        eprintln!("raw Pattern stack: 15 groups preserve returned binder metadata");
                        drop(heap);
                        drop(host);
                        drop(raw);
                        assert_eq!(Arc::strong_count(&alias), 1);
                        drop(alias);
                        assert!(weak.upgrade().is_none());
                    } else {
                        assert_eq!(tag, host.constructor("ParseRejected").unwrap());
                        assert!(host.patterns.is_empty());
                        assert_eq!(
                            host.parse_failures.last().unwrap().1,
                            Some(ResourceFailure::StructuralDepth {
                                limit: STRUCTURAL_DEPTH_LIMIT
                            })
                        );
                        eprintln!("raw Pattern stack: 16 groups refused without Pattern issuance");
                        drop(heap);
                        drop(host);
                        drop(raw);
                    }
                }
            })
            .unwrap()
            .join()
            .unwrap();
    }

    #[test]
    fn type_host_parsed_function_ast_roundtrips_on_a_512k_stack() {
        const CHILD: &str = "ASH_TYPE_AST_512K_CHILD";
        if std::env::var_os(CHILD).is_none() {
            let output = std::process::Command::new(std::env::current_exe().unwrap())
                .args([
                    "--exact",
                    "eval::machine::syntax::tests::type_host_parsed_function_ast_roundtrips_on_a_512k_stack",
                    "--nocapture",
                    "--test-threads=1",
                ])
                .env(CHILD, "1")
                .output()
                .unwrap();
            print!("{}", String::from_utf8_lossy(&output.stdout));
            let stderr = String::from_utf8_lossy(&output.stderr);
            eprint!("{stderr}");
            assert!(
                output.status.success(),
                "512 KiB child failed: {}",
                output.status
            );
            for marker in [
                "type AST stack: parsed 126 function layers",
                "type AST stack: unwrapped and transferred parsed AST",
                "type AST stack: host and final contents alias dropped",
                "type AST stack: captured and restored composed-128 AST",
                "type AST stack: returned capture retention fits within 128",
                "type AST stack: protected service accepted retained 124",
                "type AST stack: protected service refused 125 without issuance",
                "type AST stack: pre-copy and post-copy shortages cleaned up",
                "type AST stack: refused composed-129 AST",
                "type AST stack: capture and protected final aliases dropped",
            ] {
                assert!(stderr.contains(marker), "missing marker {marker}");
            }
            return;
        }

        std::thread::Builder::new()
            .stack_size(512 * 1024)
            .spawn(|| {
                use super::{HeapCell, SyntaxHost, Value, allocate_heap, constructor_fields};
                use crate::{
                    lexer::{TokenKind, lex},
                    module::ModuleId,
                    source::{ByteRange, SourceFile},
                    surface::SurfaceTypeKind,
                    syntax::{ExpansionFrame, MacroOutputNode, TransformerOutput},
                    syntax_resource::SyntaxBudget,
                    types::{ConstructorId, NominalTypeId, OperationId, TypeWorkBudget},
                };
                use std::sync::Arc;

                let mut budget = SyntaxBudget::default();
                let mut host = scalar_host(&mut budget);
                let parse = OperationId::new(host.ops, 0);
                let unwrap = OperationId::new(host.ops, 1);
                host.operations.insert(parse, "parse_type".into());
                host.operations.insert(unwrap, "type_syntax".into());
                let owner = NominalTypeId::new(ModuleId::new(0), 0);
                for (index, name) in (0u32..).zip([
                    "Syntax",
                    "NoNodes",
                    "MoreNodes",
                    "GroupNode",
                    "TypeNode",
                    "TokenNode",
                    "IdentifierNode",
                    "ExpressionNode",
                    "ParsedType",
                    "ParseRejected",
                    "Expanded",
                ]) {
                    host.constructors
                        .insert(name.into(), ConstructorId::new(owner, index));
                }
                let text = format!("{}Int", "Int -> ".repeat(126));
                let source = SourceFile::new("deep-type.ash", text).unwrap();
                let lexed = lex(&source).unwrap();
                assert!(lexed.diagnostics.is_empty());
                let span = source
                    .span(ByteRange::new(0, source.text().len() as u32).unwrap())
                    .unwrap();
                host.source = source.clone();
                host.frame = Arc::new(ExpansionFrame {
                    invocation: span,
                    definition: span,
                });
                host.caller.span = span;
                let raw = lexed
                    .tokens
                    .into_iter()
                    .filter(|token| token.kind != TokenKind::EndOfFile)
                    .map(|token| {
                        let range = token.span.range();
                        let spelling = &source.text()[range.start() as usize..range.end() as usize];
                        MacroOutputNode::Token(token.kind, spelling.into(), token.span.into())
                    })
                    .collect::<Vec<_>>();
                let mut heap = Vec::<HeapCell>::new();
                let syntax = host.syntax_value(&raw, &mut heap, 0).unwrap();
                let input = Value::Location(
                    allocate_heap(
                        &mut heap,
                        HeapCell::Tuple(vec![host.input(), syntax].into_boxed_slice()),
                    )
                    .unwrap(),
                );
                eprintln!("type AST stack phase: parse 126 function layers");
                let parsed = host
                    .request(parse, input, &mut heap, &mut TypeWorkBudget::unbounded())
                    .unwrap();
                let (tag, Some(handle)) = constructor_fields(&parsed, &heap).unwrap() else {
                    panic!("expected ParsedType");
                };
                assert_eq!(tag, host.constructor("ParsedType").unwrap());
                let handle = handle.clone();
                let mut current = &host.types[0].ty;
                for _ in 0..126 {
                    let SurfaceTypeKind::Function(function) = &current.kind else {
                        panic!("expected parsed function layer");
                    };
                    assert!(matches!(function.domain.kind, SurfaceTypeKind::Int));
                    current = &function.codomain;
                }
                assert!(matches!(current.kind, SurfaceTypeKind::Int));
                eprintln!("type AST stack: parsed 126 function layers");
                let alias = Arc::clone(&host.types[0].contents);
                let weak = Arc::downgrade(&alias);
                let unwrapped = host
                    .request(
                        unwrap,
                        handle.clone(),
                        &mut heap,
                        &mut TypeWorkBudget::unbounded(),
                    )
                    .unwrap();
                let unwrapped_output = host
                    .transfer_syntax_inner(&unwrapped, &heap, 0, true)
                    .unwrap();
                assert_eq!(unwrapped_output.len(), raw.len());
                drop(unwrapped_output);

                let origin = host.issue_origin(span.into()).unwrap();
                let fields = Value::Location(
                    allocate_heap(
                        &mut heap,
                        HeapCell::Tuple(vec![handle, origin].into_boxed_slice()),
                    )
                    .unwrap(),
                );
                let node = host.construct(&mut heap, "TypeNode", Some(fields)).unwrap();
                let end = host.construct(&mut heap, "NoNodes", None).unwrap();
                let fields = Value::Location(
                    allocate_heap(
                        &mut heap,
                        HeapCell::Tuple(vec![node, end].into_boxed_slice()),
                    )
                    .unwrap(),
                );
                let nodes = host
                    .construct(&mut heap, "MoreNodes", Some(fields))
                    .unwrap();
                let syntax = host.construct(&mut heap, "Syntax", Some(nodes)).unwrap();
                let expanded = host.construct(&mut heap, "Expanded", Some(syntax)).unwrap();
                let output = host
                    .transfer(&expanded, &heap, &mut TypeWorkBudget::unbounded())
                    .unwrap();
                let TransformerOutput::Expanded(nodes) = output else {
                    panic!("expected Expanded");
                };
                let [MacroOutputNode::ForwardedType(capture, _)] = nodes.as_slice() else {
                    panic!("expected transferred TypeNode");
                };
                assert!(Arc::ptr_eq(&capture.contents, &alias));
                eprintln!("type AST stack: unwrapped and transferred parsed AST");
                drop(heap);
                drop(host);
                drop(raw);
                drop(nodes);
                assert_eq!(Arc::strong_count(&alias), 1);
                drop(alias);
                assert!(weak.upgrade().is_none());
                eprintln!("type AST stack: host and final contents alias dropped");
                // Exercise the Type capture and protected restoration with a
                // separately lexed and parsed function AST. Each primitive's
                // actual DiagnosticLocation adds one retained depth level.
                for layers in [124usize, 125] {
                    use crate::{
                        integer::Integer,
                        parser::{MacroParseFailure, ResourceFailure, STRUCTURAL_DEPTH_LIMIT},
                        surface::SurfaceSyntaxCapture,
                    };
                    let text = format!("{}Int", "Int -> ".repeat(layers));
                    let fixture = DeclarationHostFixture::with_source("deep-captured.ash", &text);
                    let lexed = lex(&fixture.source).unwrap();
                    assert!(lexed.diagnostics.is_empty());
                    let raw = lexed
                        .tokens
                        .into_iter()
                        .filter(|token| token.kind != TokenKind::EndOfFile)
                        .map(|token| {
                            let range = token.span.range();
                            let spelling = &fixture.source.text()
                                [range.start() as usize..range.end() as usize];
                            MacroOutputNode::Token(token.kind, spelling.into(), token.span.into())
                        })
                        .collect();
                    let mut budget = SyntaxBudget::default();
                    budget.charge_units(17).unwrap();
                    let capture = crate::parser::parse_macro_type(
                        &fixture.source,
                        fixture.frame.invocation,
                        raw,
                        &fixture.contexts,
                        &fixture.frame,
                        &mut budget,
                    )
                    .unwrap();
                    let mut current = &capture.ty;
                    for _ in 0..layers {
                        let SurfaceTypeKind::Function(function) = &current.kind else {
                            panic!("expected parsed function layer");
                        };
                        current = &function.codomain;
                    }
                    assert!(matches!(current.kind, SurfaceTypeKind::Int));
                    assert!(current.diagnostic.is_some());
                    let source_alias = Arc::clone(&capture.contents);
                    let source_weak = Arc::downgrade(&source_alias);
                    let captures = [SurfaceSyntaxCapture::Type(capture)];
                    let mut host = fixture.host(&captures, &mut budget).unwrap();
                    let unwrap = OperationId::new(host.ops, 4);
                    let parse = OperationId::new(host.ops, 5);
                    host.operations.insert(unwrap, "type_syntax".into());
                    host.operations.insert(parse, "parse_type".into());
                    let owner = NominalTypeId::new(ModuleId::new(0), 0);
                    for (index, name) in
                        (100u32..).zip(["TypeCapture", "ParsedType", "ParseRejected"])
                    {
                        host.constructors
                            .insert(name.into(), ConstructorId::new(owner, index));
                    }
                    let mut heap = Vec::<HeapCell>::new();
                    let fields = Value::Location(
                        allocate_heap(
                            &mut heap,
                            HeapCell::Tuple(
                                vec![host.input(), Value::integer(Integer::from_i64(0))]
                                    .into_boxed_slice(),
                            ),
                        )
                        .unwrap(),
                    );
                    let captured = host
                        .request(
                            fixture.capture,
                            fields,
                            &mut heap,
                            &mut TypeWorkBudget::unbounded(),
                        )
                        .unwrap();
                    let (tag, Some(value)) = constructor_fields(&captured, &heap).unwrap() else {
                        panic!("expected Captured");
                    };
                    assert_eq!(tag, host.constructor("Captured").unwrap());
                    let (tag, Some(value)) = constructor_fields(value, &heap).unwrap() else {
                        panic!("expected TypeCapture");
                    };
                    assert_eq!(tag, host.constructor("TypeCapture").unwrap());
                    let unwrapped = host
                        .request(
                            unwrap,
                            value.clone(),
                            &mut heap,
                            &mut TypeWorkBudget::unbounded(),
                        )
                        .unwrap();
                    let fields = Value::Location(
                        allocate_heap(
                            &mut heap,
                            HeapCell::Tuple(vec![host.input(), unwrapped].into_boxed_slice()),
                        )
                        .unwrap(),
                    );
                    let parsed = host
                        .request(parse, fields, &mut heap, &mut TypeWorkBudget::unbounded())
                        .unwrap();
                    let (tag, Some(handle)) = constructor_fields(&parsed, &heap).unwrap() else {
                        panic!("expected ParsedType");
                    };
                    assert_eq!(tag, host.constructor("ParsedType").unwrap());
                    let handle = handle.clone();
                    let alias = Arc::clone(&host.types.last().unwrap().contents);
                    let weak = Arc::downgrade(&alias);
                    assert!(!Arc::ptr_eq(&source_alias, &alias));
                    let origin = host.issue_origin(fixture.frame.invocation.into()).unwrap();
                    let fields = Value::Location(
                        allocate_heap(
                            &mut heap,
                            HeapCell::Tuple(vec![handle, origin].into_boxed_slice()),
                        )
                        .unwrap(),
                    );
                    let node = host.construct(&mut heap, "TypeNode", Some(fields)).unwrap();
                    let end = host.construct(&mut heap, "NoNodes", None).unwrap();
                    let fields = Value::Location(
                        allocate_heap(
                            &mut heap,
                            HeapCell::Tuple(vec![node, end].into_boxed_slice()),
                        )
                        .unwrap(),
                    );
                    let nodes = host
                        .construct(&mut heap, "MoreNodes", Some(fields))
                        .unwrap();
                    let syntax = host.construct(&mut heap, "Syntax", Some(nodes)).unwrap();
                    let expanded = host
                        .construct(&mut heap, "Expanded", Some(syntax.clone()))
                        .unwrap();
                    {
                        let types_before = host.types.len();
                        let fields = Value::Location(
                            allocate_heap(
                                &mut heap,
                                HeapCell::Tuple(vec![host.input(), syntax].into_boxed_slice()),
                            )
                            .unwrap(),
                        );
                        let issued = host
                            .request(parse, fields, &mut heap, &mut TypeWorkBudget::unbounded())
                            .unwrap();
                        let (tag, Some(_)) = constructor_fields(&issued, &heap).unwrap() else {
                            panic!("expected a protected service result");
                        };
                        if layers == 124 {
                            assert_eq!(tag, host.constructor("ParsedType").unwrap());
                            assert_eq!(host.types.len(), types_before + 1);
                            let mut retained = SyntaxBudget::default();
                            crate::syntax::charge_new_type_retention(
                                host.types.last().unwrap(),
                                0,
                                &mut retained,
                            )
                            .expect("issued Type capture must fit the retention limit");
                            eprintln!("type AST stack: protected service accepted retained 124");
                        } else {
                            assert_eq!(tag, host.constructor("ParseRejected").unwrap());
                            assert_eq!(host.types.len(), types_before);
                            let (_, resource) = host.parse_failures.last().unwrap();
                            assert_eq!(
                                *resource,
                                Some(ResourceFailure::StructuralDepth {
                                    limit: STRUCTURAL_DEPTH_LIMIT
                                })
                            );
                            eprintln!(
                                "type AST stack: protected service refused 125 without issuance"
                            );
                        }
                    }
                    let make_output = |host: &mut SyntaxHost<'_>| {
                        let TransformerOutput::Expanded(nodes) = host
                            .transfer(&expanded, &heap, &mut TypeWorkBudget::unbounded())
                            .unwrap()
                        else {
                            panic!("expected Expanded");
                        };
                        nodes
                    };
                    let baseline = Arc::strong_count(&alias);
                    let nodes = make_output(&mut host);
                    let result = crate::parser::parse_macro_type(
                        &fixture.source,
                        fixture.frame.invocation,
                        nodes,
                        &fixture.contexts,
                        &fixture.frame,
                        host.syntax_work.as_deref_mut().unwrap(),
                    );
                    if layers == 124 {
                        assert_eq!(3 + layers + 1, STRUCTURAL_DEPTH_LIMIT);
                        let restored = result.unwrap();
                        let [MacroOutputNode::ForwardedType(contents, _)] =
                            restored.contents.as_ref()
                        else {
                            panic!("expected protected contents");
                        };
                        assert!(Arc::ptr_eq(&contents.contents, &alias));
                        let mut current = &restored.ty;
                        for _ in 0..layers {
                            let SurfaceTypeKind::Function(function) = &current.kind else {
                                panic!("expected restored function layer");
                            };
                            current = &function.codomain;
                        }
                        assert!(current.diagnostic.is_some());
                        let mut retained = SyntaxBudget::default();
                        retained.charge_units(17).unwrap();
                        crate::syntax::charge_new_type_retention(&restored, 0, &mut retained)
                            .expect("returned Type capture must fit the retention limit");
                        eprintln!("type AST stack: returned capture retention fits within 128");
                        drop(restored);
                        assert_eq!(Arc::strong_count(&alias), baseline);
                        eprintln!("type AST stack: captured and restored composed-128 AST");

                        let nodes = make_output(&mut host);
                        let mut measured = SyntaxBudget::default();
                        let copied =
                            crate::syntax::copy_fragment_output(&nodes, &mut measured).unwrap();
                        let copy_cost = measured.consumed();
                        drop(copied);
                        let mut short = SyntaxBudget::with_limit(copy_cost - 1);
                        assert!(matches!(
                            crate::syntax::copy_fragment_output(&nodes, &mut short),
                            Err(MacroParseFailure::Syntax {
                                resource: Some(ResourceFailure::SyntaxWork { .. }),
                                ..
                            })
                        ));
                        for _ in 0..2 {
                            let mut exact = SyntaxBudget::with_limit(copy_cost);
                            drop(crate::syntax::copy_fragment_output(&nodes, &mut exact).unwrap());
                            assert_eq!(exact.consumed(), copy_cost);
                        }
                        drop(nodes);
                        assert_eq!(Arc::strong_count(&alias), baseline);
                        let nodes = make_output(&mut host);
                        let mut short = SyntaxBudget::with_limit(copy_cost);
                        assert!(matches!(
                            crate::parser::parse_macro_type(
                                &fixture.source,
                                fixture.frame.invocation,
                                nodes,
                                &fixture.contexts,
                                &fixture.frame,
                                &mut short,
                            ),
                            Err(MacroParseFailure::Syntax {
                                resource: Some(ResourceFailure::SyntaxWork { .. }),
                                ..
                            })
                        ));
                        assert_eq!(short.consumed(), copy_cost);
                        assert_eq!(Arc::strong_count(&alias), baseline);
                        let nodes = make_output(&mut host);
                        let mut measured = SyntaxBudget::default();
                        let restored = crate::parser::parse_macro_type(
                            &fixture.source,
                            fixture.frame.invocation,
                            nodes,
                            &fixture.contexts,
                            &fixture.frame,
                            &mut measured,
                        )
                        .unwrap();
                        let parse_cost = measured.consumed();
                        drop(restored);
                        for (limit, success) in [
                            (parse_cost - 1, false),
                            (parse_cost, true),
                            (parse_cost, true),
                        ] {
                            let nodes = make_output(&mut host);
                            let mut budget = SyntaxBudget::with_limit(limit);
                            let result = crate::parser::parse_macro_type(
                                &fixture.source,
                                fixture.frame.invocation,
                                nodes,
                                &fixture.contexts,
                                &fixture.frame,
                                &mut budget,
                            );
                            if success {
                                drop(result.unwrap());
                                assert_eq!(budget.consumed(), parse_cost);
                            } else {
                                assert!(matches!(
                                    result,
                                    Err(MacroParseFailure::Syntax {
                                        resource: Some(ResourceFailure::SyntaxWork { .. }),
                                        ..
                                    })
                                ));
                            }
                            assert_eq!(Arc::strong_count(&alias), baseline);
                        }
                        let token = lex(&fixture.source).unwrap().tokens.remove(0);
                        let mut nodes = make_output(&mut host);
                        nodes.push(MacroOutputNode::Token(
                            token.kind,
                            "Int".into(),
                            token.span.into(),
                        ));
                        let mut budget = SyntaxBudget::default();
                        assert!(matches!(
                            crate::parser::parse_macro_type(
                                &fixture.source,
                                fixture.frame.invocation,
                                nodes,
                                &fixture.contexts,
                                &fixture.frame,
                                &mut budget,
                            ),
                            Err(MacroParseFailure::Syntax { diagnostics, resource: None })
                                if !diagnostics.is_empty()
                        ));
                        assert_eq!(Arc::strong_count(&alias), baseline);
                        eprintln!("type AST stack: pre-copy and post-copy shortages cleaned up");
                    } else {
                        assert_eq!(3 + layers + 1, STRUCTURAL_DEPTH_LIMIT + 1);
                        assert!(matches!(
                            result,
                            Err(MacroParseFailure::Syntax {
                                resource: Some(ResourceFailure::StructuralDepth {
                                    limit: STRUCTURAL_DEPTH_LIMIT
                                }),
                                ..
                            })
                        ));
                        assert_eq!(Arc::strong_count(&alias), baseline);
                        eprintln!("type AST stack: refused composed-129 AST");
                    }
                    drop(heap);
                    drop(host);
                    drop(captures);
                    assert_eq!(Arc::strong_count(&source_alias), 1);
                    drop(source_alias);
                    assert!(source_weak.upgrade().is_none());
                    assert_eq!(Arc::strong_count(&alias), 1);
                    drop(alias);
                    assert!(weak.upgrade().is_none());
                }
                eprintln!("type AST stack: capture and protected final aliases dropped");
            })
            .unwrap()
            .join()
            .unwrap();
    }

    #[test]
    fn type_host_raw_function_result_obeys_retained_depth_on_a_512k_stack() {
        const CHILD: &str = "ASH_TYPE_RAW_AST_512K_CHILD";
        if std::env::var_os(CHILD).is_none() {
            let output = std::process::Command::new(std::env::current_exe().unwrap())
                .args([
                    "--exact",
                    "eval::machine::syntax::tests::type_host_raw_function_result_obeys_retained_depth_on_a_512k_stack",
                    "--nocapture",
                    "--test-threads=1",
                ])
                .env(CHILD, "1")
                .output()
                .unwrap();
            print!("{}", String::from_utf8_lossy(&output.stdout));
            let stderr = String::from_utf8_lossy(&output.stderr);
            eprint!("{stderr}");
            assert!(
                output.status.success(),
                "512 KiB child failed: {}",
                output.status
            );
            for marker in [
                "raw Type AST stack: 126 function layers fit returned retention",
                "raw Type AST stack: service refused 127 without issuance",
            ] {
                assert!(stderr.contains(marker), "missing marker {marker}");
            }
            return;
        }
        std::thread::Builder::new()
            .stack_size(512 * 1024)
            .spawn(|| {
                use super::{HeapCell, Value, allocate_heap, constructor_fields};
                use crate::{
                    lexer::{TokenKind, lex},
                    module::ModuleId,
                    parser::{ResourceFailure, STRUCTURAL_DEPTH_LIMIT},
                    source::{ByteRange, SourceFile},
                    surface::SurfaceTypeKind,
                    syntax::{ExpansionFrame, MacroOutputNode},
                    syntax_resource::SyntaxBudget,
                    types::{ConstructorId, NominalTypeId, OperationId, TypeWorkBudget},
                };
                use std::sync::Arc;

                for layers in [126usize, 127] {
                    let mut budget = SyntaxBudget::default();
                    let mut host = scalar_host(&mut budget);
                    let parse = OperationId::new(host.ops, 0);
                    host.operations.insert(parse, "parse_type".into());
                    let owner = NominalTypeId::new(ModuleId::new(0), 0);
                    for (index, name) in (0u32..).zip([
                        "Syntax",
                        "NoNodes",
                        "MoreNodes",
                        "GroupNode",
                        "TypeNode",
                        "TokenNode",
                        "IdentifierNode",
                        "ExpressionNode",
                        "ParsedType",
                        "ParseRejected",
                    ]) {
                        host.constructors
                            .insert(name.into(), ConstructorId::new(owner, index));
                    }
                    let text = format!("{}Int", "Int -> ".repeat(layers));
                    let source = SourceFile::new("raw-deep-type.ash", text).unwrap();
                    let lexed = lex(&source).unwrap();
                    assert!(lexed.diagnostics.is_empty());
                    let span = source
                        .span(ByteRange::new(0, source.text().len() as u32).unwrap())
                        .unwrap();
                    host.source = source.clone();
                    host.frame = Arc::new(ExpansionFrame {
                        invocation: span,
                        definition: span,
                    });
                    host.caller.span = span;
                    let raw = lexed
                        .tokens
                        .into_iter()
                        .filter(|token| token.kind != TokenKind::EndOfFile)
                        .map(|token| {
                            let range = token.span.range();
                            let spelling =
                                &source.text()[range.start() as usize..range.end() as usize];
                            MacroOutputNode::Token(token.kind, spelling.into(), token.span.into())
                        })
                        .collect::<Vec<_>>();
                    let mut heap = Vec::<HeapCell>::new();
                    let syntax = host.syntax_value(&raw, &mut heap, 0).unwrap();
                    let fields = Value::Location(
                        allocate_heap(
                            &mut heap,
                            HeapCell::Tuple(vec![host.input(), syntax].into_boxed_slice()),
                        )
                        .unwrap(),
                    );
                    let parsed = host
                        .request(parse, fields, &mut heap, &mut TypeWorkBudget::unbounded())
                        .unwrap();
                    let (tag, Some(_)) = constructor_fields(&parsed, &heap).unwrap() else {
                        panic!("expected a raw Type service result");
                    };
                    assert_eq!(
                        1 + layers + 1,
                        STRUCTURAL_DEPTH_LIMIT + usize::from(layers == 127)
                    );
                    if layers == 126 {
                        assert_eq!(tag, host.constructor("ParsedType").unwrap());
                        assert_eq!(host.types.len(), 1);
                        let capture = host.types.last().unwrap();
                        let mut current = &capture.ty;
                        for _ in 0..layers {
                            let SurfaceTypeKind::Function(function) = &current.kind else {
                                panic!("expected parsed function layer");
                            };
                            current = &function.codomain;
                        }
                        assert!(current.diagnostic.is_some());
                        let mut retained = SyntaxBudget::default();
                        crate::syntax::charge_new_type_retention(capture, 0, &mut retained)
                            .expect("raw returned Type capture must fit the retention limit");
                        eprintln!("raw Type AST stack: 126 function layers fit returned retention");
                        let alias = Arc::clone(&capture.contents);
                        let weak = Arc::downgrade(&alias);
                        drop(heap);
                        drop(host);
                        drop(raw);
                        assert_eq!(Arc::strong_count(&alias), 1);
                        drop(alias);
                        assert!(weak.upgrade().is_none());
                    } else {
                        assert_eq!(tag, host.constructor("ParseRejected").unwrap());
                        assert!(host.types.is_empty());
                        let (_, resource) = host.parse_failures.last().unwrap();
                        assert_eq!(
                            *resource,
                            Some(ResourceFailure::StructuralDepth {
                                limit: STRUCTURAL_DEPTH_LIMIT
                            })
                        );
                        eprintln!("raw Type AST stack: service refused 127 without issuance");
                        drop(heap);
                        drop(host);
                        drop(raw);
                    }
                }
            })
            .unwrap()
            .join()
            .unwrap();
    }

    #[test]
    fn type_capture_arena_reserves_growth_before_clone() {
        use super::{HeapCell, RuntimeFailure, SyntaxHost, Value, allocate_heap};
        use crate::{
            integer::Integer,
            module::ModuleId,
            surface::{SurfaceSyntaxCapture, SurfaceType, SurfaceTypeCapture, SurfaceTypeKind},
            syntax::MacroOutputNode,
            syntax_resource::SyntaxBudget,
            types::{ConstructorId, NominalTypeId, OperationId, TypeWorkBudget},
        };
        use std::sync::Arc;

        // This synthetic host state isolates arena accounting; the imported
        // public graph supplies the separate checked-host evidence.
        fn host<'a>(
            budget: &'a mut SyntaxBudget,
        ) -> (SyntaxHost<'a>, Arc<[MacroOutputNode]>, OperationId) {
            let mut host = scalar_host(budget);
            let span = host.caller.span;
            let contents: Arc<[MacroOutputNode]> = Arc::from([]);
            host.captures
                .push(SurfaceSyntaxCapture::Type(SurfaceTypeCapture {
                    ty: SurfaceType {
                        kind: SurfaceTypeKind::Int,
                        span,
                        diagnostic: None,
                    },
                    contents: Arc::clone(&contents),
                }));
            let operation = OperationId::new(host.ops, 0);
            host.operations.insert(operation, "capture".into());
            let owner = NominalTypeId::new(ModuleId::new(0), 0);
            host.constructors
                .insert("TypeCapture".into(), ConstructorId::new(owner, 0));
            host.constructors
                .insert("Captured".into(), ConstructorId::new(owner, 1));
            (host, contents, operation)
        }

        fn capture(
            host: &mut SyntaxHost<'_>,
            operation: OperationId,
            heap: &mut Vec<HeapCell>,
        ) -> Result<Value, RuntimeFailure> {
            let fields =
                vec![host.input(), Value::integer(Integer::from_i64(0))].into_boxed_slice();
            let argument = Value::Location(allocate_heap(heap, HeapCell::Tuple(fields)).unwrap());
            host.request(operation, argument, heap, &mut TypeWorkBudget::unbounded())
        }

        let mut measured = SyntaxBudget::default();
        measured.charge_units(17).unwrap();
        let (mut measured_host, contents, operation) = host(&mut measured);
        let base = Arc::strong_count(&contents);
        let mut heap = Vec::new();
        capture(&mut measured_host, operation, &mut heap).unwrap();
        let first = measured_host.syntax_work.as_deref().unwrap().consumed();
        assert_eq!(measured_host.types.len(), 1);
        assert_eq!(Arc::strong_count(&contents), base + 1);
        capture(&mut measured_host, operation, &mut heap).unwrap();
        let total = measured_host.syntax_work.as_deref().unwrap().consumed();
        assert_eq!(measured_host.types.len(), 2);
        assert_eq!(Arc::strong_count(&contents), base + 2);
        drop(measured_host);

        // The second push requests two slots and moves one live entry. Two
        // later constructor charges occur after that reservation and clone.
        let growth_limit = total - 3;
        assert!(growth_limit > first);
        let mut short = SyntaxBudget::with_limit(growth_limit);
        short.charge_units(17).unwrap();
        let (mut short_host, contents, operation) = host(&mut short);
        let base = Arc::strong_count(&contents);
        let mut heap = Vec::new();
        capture(&mut short_host, operation, &mut heap).unwrap();
        assert!(matches!(
            capture(&mut short_host, operation, &mut heap),
            Err(RuntimeFailure::Report(report))
                if report.primary.reason == "internal.resource.syntax-work"
        ));
        assert_eq!(short_host.types.len(), 1);
        assert_eq!(Arc::strong_count(&contents), base + 1);
        assert_eq!(
            short_host.syntax_work.as_deref().unwrap().consumed(),
            total - 5
        );
        drop(short_host);

        for _ in 0..2 {
            let mut exact = SyntaxBudget::with_limit(total);
            exact.charge_units(17).unwrap();
            let (mut exact_host, _, operation) = host(&mut exact);
            let mut heap = Vec::new();
            capture(&mut exact_host, operation, &mut heap).unwrap();
            capture(&mut exact_host, operation, &mut heap).unwrap();
            assert_eq!(exact_host.types.len(), 2);
            assert_eq!(exact_host.syntax_work.as_deref().unwrap().consumed(), total);
        }
    }

    #[test]
    fn type_parse_success_and_failure_arenas_pay_before_growth() {
        use super::{
            HeapCell, RuntimeFailure, SyntaxHost, Value, allocate_heap, constructor_fields,
        };
        use crate::{
            module::ModuleId,
            syntax::MacroOutputNode,
            syntax_resource::SyntaxBudget,
            types::{ConstructorId, NominalTypeId, OperationId, TypeWorkBudget},
        };

        fn host(budget: &mut SyntaxBudget) -> (SyntaxHost<'_>, OperationId) {
            let mut host = scalar_host(budget);
            let operation = OperationId::new(host.ops, 0);
            host.operations.insert(operation, "parse_type".into());
            let owner = NominalTypeId::new(ModuleId::new(0), 0);
            for (index, name) in (0u32..).zip([
                "Syntax",
                "NoNodes",
                "MoreNodes",
                "GroupNode",
                "TypeNode",
                "ExpressionNode",
                "IdentifierNode",
                "TokenNode",
                "ParsedType",
                "ParseRejected",
            ]) {
                host.constructors
                    .insert(name.into(), ConstructorId::new(owner, index));
            }
            (host, operation)
        }

        fn input_syntax(host: &mut SyntaxHost<'_>, heap: &mut Vec<HeapCell>, valid: bool) -> Value {
            let nodes = if valid {
                vec![MacroOutputNode::Token(
                    crate::lexer::TokenKind::IntType,
                    "Int".into(),
                    host.frame.invocation.into(),
                )]
            } else {
                Vec::new()
            };
            host.syntax_value(&nodes, heap, 0).unwrap()
        }

        fn parse_type(
            host: &mut SyntaxHost<'_>,
            operation: OperationId,
            syntax: &Value,
            heap: &mut Vec<HeapCell>,
        ) -> Result<Value, RuntimeFailure> {
            let fields = vec![host.input(), syntax.clone()].into_boxed_slice();
            let argument = Value::Location(allocate_heap(heap, HeapCell::Tuple(fields)).unwrap());
            host.request(operation, argument, heap, &mut TypeWorkBudget::unbounded())
        }

        // Synthetic constructors exercise the real parser and arenas. The
        // separate imported test checks the validated public host graph.
        for valid in [true, false] {
            let mut measured = SyntaxBudget::default();
            measured.charge_units(17).unwrap();
            let (mut measured_host, operation) = host(&mut measured);
            let mut heap = Vec::new();
            let syntax = input_syntax(&mut measured_host, &mut heap, valid);
            for expected_len in 1..=2 {
                let result = parse_type(&mut measured_host, operation, &syntax, &mut heap).unwrap();
                let (tag, _) = constructor_fields(&result, &heap).unwrap();
                assert_eq!(
                    tag,
                    measured_host
                        .constructor(if valid { "ParsedType" } else { "ParseRejected" })
                        .unwrap()
                );
                assert_eq!(
                    if valid {
                        measured_host.types.len()
                    } else {
                        measured_host.parse_failures.len()
                    },
                    expected_len
                );
            }
            let total = measured_host.syntax_work.as_deref().unwrap().consumed();
            drop(measured_host);

            // The second push reserves two requested slots plus one live
            // move; constructing ParsedType/ParseRejected costs one more.
            let mut short = SyntaxBudget::with_limit(total - 2);
            short.charge_units(17).unwrap();
            let (mut short_host, operation) = host(&mut short);
            let mut heap = Vec::new();
            let syntax = input_syntax(&mut short_host, &mut heap, valid);
            parse_type(&mut short_host, operation, &syntax, &mut heap).unwrap();
            assert!(matches!(
                parse_type(&mut short_host, operation, &syntax, &mut heap),
                Err(RuntimeFailure::Report(report))
                    if report.primary.reason == "internal.resource.syntax-work"
            ));
            assert_eq!(
                if valid {
                    short_host.types.len()
                } else {
                    short_host.parse_failures.len()
                },
                1
            );
            assert_eq!(
                short_host.syntax_work.as_deref().unwrap().consumed(),
                total - 4
            );
            drop(short_host);

            for _ in 0..2 {
                let mut exact = SyntaxBudget::with_limit(total);
                exact.charge_units(17).unwrap();
                let (mut exact_host, operation) = host(&mut exact);
                let mut heap = Vec::new();
                let syntax = input_syntax(&mut exact_host, &mut heap, valid);
                parse_type(&mut exact_host, operation, &syntax, &mut heap).unwrap();
                parse_type(&mut exact_host, operation, &syntax, &mut heap).unwrap();
                assert_eq!(exact_host.syntax_work.as_deref().unwrap().consumed(), total);
            }
        }
    }

    #[test]
    fn type_syntax_issuance_arena_refuses_before_copy_and_retries() {
        use super::{HeapCell, RuntimeFailure, SyntaxHost};
        use crate::{
            module::ModuleId,
            surface::{SurfaceType, SurfaceTypeCapture, SurfaceTypeKind},
            syntax::MacroOutputNode,
            syntax_resource::SyntaxBudget,
            types::{ConstructorId, NominalTypeId},
        };
        use std::sync::Arc;

        fn host(budget: &mut SyntaxBudget) -> SyntaxHost<'_> {
            let mut host = scalar_host(budget);
            let owner = NominalTypeId::new(ModuleId::new(0), 0);
            for (index, name) in (0u32..).zip(["NoNodes", "Syntax", "TypeNode", "MoreNodes"]) {
                host.constructors
                    .insert(name.into(), ConstructorId::new(owner, index));
            }
            host
        }

        fn capture_nodes(host: &SyntaxHost<'_>) -> (Vec<MacroOutputNode>, Arc<[MacroOutputNode]>) {
            let span = host.frame.invocation;
            let contents: Arc<[MacroOutputNode]> = Arc::from([]);
            (
                vec![MacroOutputNode::ForwardedType(
                    SurfaceTypeCapture {
                        ty: SurfaceType {
                            kind: SurfaceTypeKind::Int,
                            span,
                            diagnostic: None,
                        },
                        contents: Arc::clone(&contents),
                    },
                    span.into(),
                )],
                contents,
            )
        }

        let mut measured = SyntaxBudget::default();
        measured.charge_units(17).unwrap();
        let mut measured_host = host(&mut measured);
        let (nodes, contents) = capture_nodes(&measured_host);
        let base = Arc::strong_count(&contents);
        let mut heap: Vec<HeapCell> = Vec::new();
        measured_host.syntax_value(&nodes, &mut heap, 0).unwrap();
        assert_eq!(measured_host.types.len(), 1);
        assert_eq!(Arc::strong_count(&contents), base + 1);
        measured_host.syntax_value(&nodes, &mut heap, 0).unwrap();
        assert_eq!(measured_host.types.len(), 2);
        assert_eq!(Arc::strong_count(&contents), base + 2);
        let total = measured_host.syntax_work.as_deref().unwrap().consumed();
        drop(measured_host);

        // Two requested slots plus one live move are paid before the second
        // capture clone; ten later units build the returned Syntax value.
        let mut short = SyntaxBudget::with_limit(total - 11);
        short.charge_units(17).unwrap();
        let mut short_host = host(&mut short);
        let (nodes, contents) = capture_nodes(&short_host);
        let base = Arc::strong_count(&contents);
        let mut heap = Vec::new();
        short_host.syntax_value(&nodes, &mut heap, 0).unwrap();
        assert!(matches!(
            short_host.syntax_value(&nodes, &mut heap, 0),
            Err(RuntimeFailure::Report(report))
                if report.primary.reason == "internal.resource.syntax-work"
        ));
        assert_eq!(short_host.types.len(), 1);
        assert_eq!(Arc::strong_count(&contents), base + 1);
        assert_eq!(
            short_host.syntax_work.as_deref().unwrap().consumed(),
            total - 13
        );
        drop(short_host);

        for _ in 0..2 {
            let mut exact = SyntaxBudget::with_limit(total);
            exact.charge_units(17).unwrap();
            let mut exact_host = host(&mut exact);
            let (nodes, _) = capture_nodes(&exact_host);
            let mut heap = Vec::new();
            exact_host.syntax_value(&nodes, &mut heap, 0).unwrap();
            exact_host.syntax_value(&nodes, &mut heap, 0).unwrap();
            assert_eq!(exact_host.types.len(), 2);
            assert_eq!(exact_host.syntax_work.as_deref().unwrap().consumed(), total);
        }
    }

    #[test]
    fn expression_capture_arena_reserves_growth_before_clone() {
        use super::{HeapCell, RuntimeFailure, SyntaxHost, Value, allocate_heap};
        use crate::{
            integer::Integer,
            module::ModuleId,
            surface::{
                SurfaceExpr, SurfaceExprKind, SurfaceExpressionCapture, SurfaceSyntaxCapture,
            },
            syntax::MacroOutputNode,
            syntax_resource::SyntaxBudget,
            types::{ConstructorId, NominalTypeId, OperationId, TypeWorkBudget},
        };
        use std::sync::Arc;

        // This synthetic host state isolates arena accounting; the imported
        // public graph supplies the separate checked-host evidence.
        fn host<'a>(
            budget: &'a mut SyntaxBudget,
        ) -> (SyntaxHost<'a>, Arc<[MacroOutputNode]>, OperationId) {
            let mut host = scalar_host(budget);
            let span = host.caller.span;
            let contents: Arc<[MacroOutputNode]> = Arc::from([]);
            host.captures
                .push(SurfaceSyntaxCapture::Expression(SurfaceExpressionCapture {
                    contains_protected_type: false,
                    quote_sites: Default::default(),
                    expression: SurfaceExpr {
                        kind: SurfaceExprKind::Unit,
                        span,
                        diagnostic: None,
                    },
                    contents: Arc::clone(&contents),
                }));
            let operation = OperationId::new(host.ops, 0);
            host.operations.insert(operation, "capture".into());
            let owner = NominalTypeId::new(ModuleId::new(0), 0);
            host.constructors
                .insert("ExpressionCapture".into(), ConstructorId::new(owner, 0));
            host.constructors
                .insert("Captured".into(), ConstructorId::new(owner, 1));
            (host, contents, operation)
        }

        fn capture(
            host: &mut SyntaxHost<'_>,
            operation: OperationId,
            heap: &mut Vec<HeapCell>,
        ) -> Result<Value, RuntimeFailure> {
            let fields =
                vec![host.input(), Value::integer(Integer::from_i64(0))].into_boxed_slice();
            let argument = Value::Location(allocate_heap(heap, HeapCell::Tuple(fields)).unwrap());
            host.request(operation, argument, heap, &mut TypeWorkBudget::unbounded())
        }

        let mut measured = SyntaxBudget::default();
        measured.charge_units(17).unwrap();
        let (mut measured_host, contents, operation) = host(&mut measured);
        let base = Arc::strong_count(&contents);
        let mut heap = Vec::new();
        capture(&mut measured_host, operation, &mut heap).unwrap();
        let first = measured_host.syntax_work.as_deref().unwrap().consumed();
        assert_eq!(measured_host.expressions.len(), 1);
        assert_eq!(Arc::strong_count(&contents), base + 1);
        capture(&mut measured_host, operation, &mut heap).unwrap();
        let total = measured_host.syntax_work.as_deref().unwrap().consumed();
        assert_eq!(measured_host.expressions.len(), 2);
        assert_eq!(Arc::strong_count(&contents), base + 2);
        drop(measured_host);

        // The first insertion needs one arena slot before the two constructors.
        let mut initial_short = SyntaxBudget::with_limit(first - 3);
        initial_short.charge_units(17).unwrap();
        let (mut initial_host, contents, operation) = host(&mut initial_short);
        let base = Arc::strong_count(&contents);
        assert!(matches!(
            capture(&mut initial_host, operation, &mut Vec::new()),
            Err(RuntimeFailure::Report(report))
                if report.primary.reason == "internal.resource.syntax-work"
        ));
        assert!(initial_host.expressions.is_empty());
        assert_eq!(Arc::strong_count(&contents), base);
        assert_eq!(
            initial_host.syntax_work.as_deref().unwrap().consumed(),
            first - 3
        );
        drop(initial_host);

        // An already allocated two-slot arena omits the initial 1 and the
        // later 2+1 growth charge, while still copying both captures.
        let mut spare = SyntaxBudget::default();
        spare.charge_units(17).unwrap();
        let (mut spare_host, contents, operation) = host(&mut spare);
        spare_host.expressions.reserve_exact(2);
        let base = Arc::strong_count(&contents);
        let mut heap = Vec::new();
        capture(&mut spare_host, operation, &mut heap).unwrap();
        capture(&mut spare_host, operation, &mut heap).unwrap();
        assert_eq!(spare_host.expressions.len(), 2);
        assert_eq!(Arc::strong_count(&contents), base + 2);
        assert_eq!(
            spare_host.syntax_work.as_deref().unwrap().consumed() + 4,
            total
        );
        drop(spare_host);

        // The second push requests two slots and moves one live entry. Two
        // later constructor charges occur after that reservation and clone.
        let growth_limit = total - 3;
        assert!(growth_limit > first);
        let mut short = SyntaxBudget::with_limit(growth_limit);
        short.charge_units(17).unwrap();
        let (mut short_host, contents, operation) = host(&mut short);
        let base = Arc::strong_count(&contents);
        let mut heap = Vec::new();
        capture(&mut short_host, operation, &mut heap).unwrap();
        assert!(matches!(
            capture(&mut short_host, operation, &mut heap),
            Err(RuntimeFailure::Report(report))
                if report.primary.reason == "internal.resource.syntax-work"
        ));
        assert_eq!(short_host.expressions.len(), 1);
        assert_eq!(Arc::strong_count(&contents), base + 1);
        assert_eq!(
            short_host.syntax_work.as_deref().unwrap().consumed(),
            total - 5
        );
        drop(short_host);

        for _ in 0..2 {
            let mut exact = SyntaxBudget::with_limit(total);
            exact.charge_units(17).unwrap();
            let (mut exact_host, _, operation) = host(&mut exact);
            let mut heap = Vec::new();
            capture(&mut exact_host, operation, &mut heap).unwrap();
            capture(&mut exact_host, operation, &mut heap).unwrap();
            assert_eq!(exact_host.expressions.len(), 2);
            assert_eq!(exact_host.syntax_work.as_deref().unwrap().consumed(), total);
        }
    }

    #[test]
    fn expression_parse_success_and_failure_arenas_pay_before_growth() {
        use super::{
            HeapCell, RuntimeFailure, SyntaxHost, Value, allocate_heap, constructor_fields,
        };
        use crate::{
            module::ModuleId,
            syntax::MacroOutputNode,
            syntax_resource::SyntaxBudget,
            types::{ConstructorId, NominalTypeId, OperationId, TypeWorkBudget},
        };

        fn host(budget: &mut SyntaxBudget) -> (SyntaxHost<'_>, OperationId) {
            let mut host = scalar_host(budget);
            let operation = OperationId::new(host.ops, 0);
            host.operations.insert(operation, "parse_expression".into());
            let owner = NominalTypeId::new(ModuleId::new(0), 0);
            for (index, name) in (0u32..).zip([
                "Syntax",
                "NoNodes",
                "MoreNodes",
                "GroupNode",
                "TypeNode",
                "PatternNode",
                "ExpressionNode",
                "IdentifierNode",
                "TokenNode",
                "Parsed",
                "ParseRejected",
            ]) {
                host.constructors
                    .insert(name.into(), ConstructorId::new(owner, index));
            }
            (host, operation)
        }

        fn input_syntax(host: &mut SyntaxHost<'_>, heap: &mut Vec<HeapCell>, valid: bool) -> Value {
            let nodes = if valid {
                vec![MacroOutputNode::Token(
                    crate::lexer::TokenKind::Integer(crate::integer::Integer::from_i64(1)),
                    "1".into(),
                    host.frame.invocation.into(),
                )]
            } else {
                Vec::new()
            };
            host.syntax_value(&nodes, heap, 0).unwrap()
        }

        fn parse_expression(
            host: &mut SyntaxHost<'_>,
            operation: OperationId,
            syntax: &Value,
            heap: &mut Vec<HeapCell>,
        ) -> Result<Value, RuntimeFailure> {
            let fields = vec![host.input(), syntax.clone()].into_boxed_slice();
            let argument = Value::Location(allocate_heap(heap, HeapCell::Tuple(fields)).unwrap());
            host.request(operation, argument, heap, &mut TypeWorkBudget::unbounded())
        }

        // Synthetic constructors exercise the real parser and arenas. The
        // separate imported test checks the validated public host graph.
        for valid in [true, false] {
            let mut measured = SyntaxBudget::default();
            measured.charge_units(17).unwrap();
            let (mut measured_host, operation) = host(&mut measured);
            let mut heap = Vec::new();
            let syntax = input_syntax(&mut measured_host, &mut heap, valid);
            let mut first = 0;
            for expected_len in 1..=2 {
                let result =
                    parse_expression(&mut measured_host, operation, &syntax, &mut heap).unwrap();
                let (tag, _) = constructor_fields(&result, &heap).unwrap();
                assert_eq!(
                    tag,
                    measured_host
                        .constructor(if valid { "Parsed" } else { "ParseRejected" })
                        .unwrap()
                );
                assert_eq!(
                    if valid {
                        measured_host.expressions.len()
                    } else {
                        measured_host.parse_failures.len()
                    },
                    expected_len
                );
                if expected_len == 1 {
                    first = measured_host.syntax_work.as_deref().unwrap().consumed();
                }
            }
            let total = measured_host.syntax_work.as_deref().unwrap().consumed();
            drop(measured_host);

            let mut initial_short = SyntaxBudget::with_limit(first - 2);
            initial_short.charge_units(17).unwrap();
            let (mut initial_host, operation) = host(&mut initial_short);
            let mut heap = Vec::new();
            let syntax = input_syntax(&mut initial_host, &mut heap, valid);
            assert!(matches!(
                parse_expression(&mut initial_host, operation, &syntax, &mut heap),
                Err(RuntimeFailure::Report(report))
                    if report.primary.reason == "internal.resource.syntax-work"
            ));
            assert!(initial_host.expressions.is_empty());
            assert!(initial_host.parse_failures.is_empty());
            assert_eq!(
                initial_host.syntax_work.as_deref().unwrap().consumed(),
                first - 2
            );
            drop(initial_host);

            let mut spare = SyntaxBudget::default();
            spare.charge_units(17).unwrap();
            let (mut spare_host, operation) = host(&mut spare);
            if valid {
                spare_host.expressions.reserve_exact(2);
            } else {
                spare_host.parse_failures.reserve_exact(2);
            }
            let mut heap = Vec::new();
            let syntax = input_syntax(&mut spare_host, &mut heap, valid);
            parse_expression(&mut spare_host, operation, &syntax, &mut heap).unwrap();
            parse_expression(&mut spare_host, operation, &syntax, &mut heap).unwrap();
            assert_eq!(
                spare_host.syntax_work.as_deref().unwrap().consumed() + 4,
                total
            );
            drop(spare_host);

            // The second push reserves two requested slots plus one live
            // move; constructing Parsed/ParseRejected costs one more.
            let mut short = SyntaxBudget::with_limit(total - 2);
            short.charge_units(17).unwrap();
            let (mut short_host, operation) = host(&mut short);
            let mut heap = Vec::new();
            let syntax = input_syntax(&mut short_host, &mut heap, valid);
            parse_expression(&mut short_host, operation, &syntax, &mut heap).unwrap();
            assert!(matches!(
                parse_expression(&mut short_host, operation, &syntax, &mut heap),
                Err(RuntimeFailure::Report(report))
                    if report.primary.reason == "internal.resource.syntax-work"
            ));
            assert_eq!(
                if valid {
                    short_host.expressions.len()
                } else {
                    short_host.parse_failures.len()
                },
                1
            );
            assert_eq!(
                short_host.syntax_work.as_deref().unwrap().consumed(),
                total - 4
            );
            drop(short_host);

            for _ in 0..2 {
                let mut exact = SyntaxBudget::with_limit(total);
                exact.charge_units(17).unwrap();
                let (mut exact_host, operation) = host(&mut exact);
                let mut heap = Vec::new();
                let syntax = input_syntax(&mut exact_host, &mut heap, valid);
                parse_expression(&mut exact_host, operation, &syntax, &mut heap).unwrap();
                parse_expression(&mut exact_host, operation, &syntax, &mut heap).unwrap();
                assert_eq!(exact_host.syntax_work.as_deref().unwrap().consumed(), total);
            }
        }
    }

    #[test]
    fn expression_syntax_issuance_arena_refuses_before_copy_and_retries() {
        use super::{HeapCell, RuntimeFailure, SyntaxHost};
        use crate::{
            module::ModuleId,
            surface::{SurfaceExpr, SurfaceExprKind, SurfaceExpressionCapture},
            syntax::MacroOutputNode,
            syntax_resource::SyntaxBudget,
            types::{ConstructorId, NominalTypeId},
        };
        use std::sync::Arc;

        fn host(budget: &mut SyntaxBudget) -> SyntaxHost<'_> {
            let mut host = scalar_host(budget);
            let owner = NominalTypeId::new(ModuleId::new(0), 0);
            for (index, name) in (0u32..).zip(["NoNodes", "Syntax", "ExpressionNode", "MoreNodes"])
            {
                host.constructors
                    .insert(name.into(), ConstructorId::new(owner, index));
            }
            // Isolate Expression arena growth from origin-buffer growth.
            host.origins.reserve_exact(2);
            host
        }

        fn capture_nodes(host: &SyntaxHost<'_>) -> (Vec<MacroOutputNode>, Arc<[MacroOutputNode]>) {
            let span = host.frame.invocation;
            let contents: Arc<[MacroOutputNode]> = Arc::from([]);
            (
                vec![MacroOutputNode::ForwardedExpression(
                    SurfaceExpressionCapture {
                        contains_protected_type: false,
                        quote_sites: Default::default(),
                        expression: SurfaceExpr {
                            kind: SurfaceExprKind::Unit,
                            span,
                            diagnostic: None,
                        },
                        contents: Arc::clone(&contents),
                    },
                    span.into(),
                )],
                contents,
            )
        }

        let mut measured = SyntaxBudget::default();
        measured.charge_units(17).unwrap();
        let mut measured_host = host(&mut measured);
        let (nodes, contents) = capture_nodes(&measured_host);
        let base = Arc::strong_count(&contents);
        let mut heap: Vec<HeapCell> = Vec::new();
        measured_host.syntax_value(&nodes, &mut heap, 0).unwrap();
        let first = measured_host.syntax_work.as_deref().unwrap().consumed();
        assert_eq!(measured_host.expressions.len(), 1);
        assert_eq!(Arc::strong_count(&contents), base + 1);
        measured_host.syntax_value(&nodes, &mut heap, 0).unwrap();
        assert_eq!(measured_host.expressions.len(), 2);
        assert_eq!(Arc::strong_count(&contents), base + 2);
        let total = measured_host.syntax_work.as_deref().unwrap().consumed();
        drop(measured_host);

        let mut initial_short = SyntaxBudget::with_limit(first - 11);
        initial_short.charge_units(17).unwrap();
        let mut initial_host = host(&mut initial_short);
        let (nodes, contents) = capture_nodes(&initial_host);
        let base = Arc::strong_count(&contents);
        assert!(matches!(
            initial_host.syntax_value(&nodes, &mut Vec::new(), 0),
            Err(RuntimeFailure::Report(report))
                if report.primary.reason == "internal.resource.syntax-work"
        ));
        assert!(initial_host.expressions.is_empty());
        assert_eq!(Arc::strong_count(&contents), base);
        assert_eq!(
            initial_host.syntax_work.as_deref().unwrap().consumed(),
            first - 11
        );
        drop(initial_host);

        let mut spare = SyntaxBudget::default();
        spare.charge_units(17).unwrap();
        let mut spare_host = host(&mut spare);
        spare_host.expressions.reserve_exact(2);
        let (nodes, contents) = capture_nodes(&spare_host);
        let base = Arc::strong_count(&contents);
        let mut heap = Vec::new();
        spare_host.syntax_value(&nodes, &mut heap, 0).unwrap();
        spare_host.syntax_value(&nodes, &mut heap, 0).unwrap();
        assert_eq!(Arc::strong_count(&contents), base + 2);
        assert_eq!(
            spare_host.syntax_work.as_deref().unwrap().consumed() + 4,
            total
        );
        drop(spare_host);

        // Two requested slots plus one live move are paid before the second
        // capture clone; ten later units build the returned Syntax value.
        let mut short = SyntaxBudget::with_limit(total - 11);
        short.charge_units(17).unwrap();
        let mut short_host = host(&mut short);
        let (nodes, contents) = capture_nodes(&short_host);
        let base = Arc::strong_count(&contents);
        let mut heap = Vec::new();
        short_host.syntax_value(&nodes, &mut heap, 0).unwrap();
        assert!(matches!(
            short_host.syntax_value(&nodes, &mut heap, 0),
            Err(RuntimeFailure::Report(report))
                if report.primary.reason == "internal.resource.syntax-work"
        ));
        assert_eq!(short_host.expressions.len(), 1);
        assert_eq!(Arc::strong_count(&contents), base + 1);
        assert_eq!(
            short_host.syntax_work.as_deref().unwrap().consumed(),
            total - 13
        );
        drop(short_host);

        for _ in 0..2 {
            let mut exact = SyntaxBudget::with_limit(total);
            exact.charge_units(17).unwrap();
            let mut exact_host = host(&mut exact);
            let (nodes, _) = capture_nodes(&exact_host);
            let mut heap = Vec::new();
            exact_host.syntax_value(&nodes, &mut heap, 0).unwrap();
            exact_host.syntax_value(&nodes, &mut heap, 0).unwrap();
            assert_eq!(exact_host.expressions.len(), 2);
            assert_eq!(exact_host.syntax_work.as_deref().unwrap().consumed(), total);
        }
    }

    #[test]
    fn pattern_capture_arena_reserves_growth_before_clone() {
        use super::{HeapCell, RuntimeFailure, SyntaxHost, Value, allocate_heap};
        use crate::{
            integer::Integer,
            module::ModuleId,
            surface::{
                SurfacePattern, SurfacePatternCapture, SurfacePatternKind, SurfaceSyntaxCapture,
            },
            syntax::MacroOutputNode,
            syntax_resource::SyntaxBudget,
            types::{ConstructorId, NominalTypeId, OperationId, TypeWorkBudget},
        };
        use std::sync::Arc;

        // This synthetic host state isolates arena accounting; the imported
        // public graph supplies the separate checked-host evidence.
        fn host<'a>(
            budget: &'a mut SyntaxBudget,
        ) -> (SyntaxHost<'a>, Arc<[MacroOutputNode]>, OperationId) {
            let mut host = scalar_host(budget);
            let span = host.caller.span;
            let contents: Arc<[MacroOutputNode]> = Arc::from([]);
            host.captures
                .push(SurfaceSyntaxCapture::Pattern(SurfacePatternCapture {
                    pattern: SurfacePattern {
                        kind: SurfacePatternKind::Wildcard,
                        span,
                        diagnostic: None,
                    },
                    contents: Arc::clone(&contents),
                }));
            let operation = OperationId::new(host.ops, 0);
            host.operations.insert(operation, "capture".into());
            let owner = NominalTypeId::new(ModuleId::new(0), 0);
            host.constructors
                .insert("PatternCapture".into(), ConstructorId::new(owner, 0));
            host.constructors
                .insert("Captured".into(), ConstructorId::new(owner, 1));
            (host, contents, operation)
        }

        fn capture(
            host: &mut SyntaxHost<'_>,
            operation: OperationId,
            heap: &mut Vec<HeapCell>,
        ) -> Result<Value, RuntimeFailure> {
            let fields =
                vec![host.input(), Value::integer(Integer::from_i64(0))].into_boxed_slice();
            let argument = Value::Location(allocate_heap(heap, HeapCell::Tuple(fields)).unwrap());
            host.request(operation, argument, heap, &mut TypeWorkBudget::unbounded())
        }

        let mut measured = SyntaxBudget::default();
        measured.charge_units(17).unwrap();
        let (mut measured_host, contents, operation) = host(&mut measured);
        let base = Arc::strong_count(&contents);
        let mut heap = Vec::new();
        capture(&mut measured_host, operation, &mut heap).unwrap();
        let first = measured_host.syntax_work.as_deref().unwrap().consumed();
        assert_eq!(measured_host.patterns.len(), 1);
        assert_eq!(Arc::strong_count(&contents), base + 1);
        capture(&mut measured_host, operation, &mut heap).unwrap();
        let total = measured_host.syntax_work.as_deref().unwrap().consumed();
        assert_eq!(measured_host.patterns.len(), 2);
        assert_eq!(Arc::strong_count(&contents), base + 2);
        drop(measured_host);

        // The first insertion needs one arena slot before the two constructors.
        let mut initial_short = SyntaxBudget::with_limit(first - 3);
        initial_short.charge_units(17).unwrap();
        let (mut initial_host, contents, operation) = host(&mut initial_short);
        let base = Arc::strong_count(&contents);
        assert!(matches!(
            capture(&mut initial_host, operation, &mut Vec::new()),
            Err(RuntimeFailure::Report(report))
                if report.primary.reason == "internal.resource.syntax-work"
        ));
        assert!(initial_host.patterns.is_empty());
        assert_eq!(Arc::strong_count(&contents), base);
        assert_eq!(
            initial_host.syntax_work.as_deref().unwrap().consumed(),
            first - 3
        );
        drop(initial_host);

        // An already allocated two-slot arena omits the initial 1 and the
        // later 2+1 growth charge, while still copying both captures.
        let mut spare = SyntaxBudget::default();
        spare.charge_units(17).unwrap();
        let (mut spare_host, contents, operation) = host(&mut spare);
        spare_host.patterns.reserve_exact(2);
        let base = Arc::strong_count(&contents);
        let mut heap = Vec::new();
        capture(&mut spare_host, operation, &mut heap).unwrap();
        capture(&mut spare_host, operation, &mut heap).unwrap();
        assert_eq!(spare_host.patterns.len(), 2);
        assert_eq!(Arc::strong_count(&contents), base + 2);
        assert_eq!(
            spare_host.syntax_work.as_deref().unwrap().consumed() + 4,
            total
        );
        drop(spare_host);

        // The second push requests two slots and moves one live entry. Two
        // later constructor charges occur after that reservation and clone.
        let growth_limit = total - 3;
        assert!(growth_limit > first);
        let mut short = SyntaxBudget::with_limit(growth_limit);
        short.charge_units(17).unwrap();
        let (mut short_host, contents, operation) = host(&mut short);
        let base = Arc::strong_count(&contents);
        let mut heap = Vec::new();
        capture(&mut short_host, operation, &mut heap).unwrap();
        assert!(matches!(
            capture(&mut short_host, operation, &mut heap),
            Err(RuntimeFailure::Report(report))
                if report.primary.reason == "internal.resource.syntax-work"
        ));
        assert_eq!(short_host.patterns.len(), 1);
        assert_eq!(Arc::strong_count(&contents), base + 1);
        assert_eq!(
            short_host.syntax_work.as_deref().unwrap().consumed(),
            total - 5
        );
        drop(short_host);

        for _ in 0..2 {
            let mut exact = SyntaxBudget::with_limit(total);
            exact.charge_units(17).unwrap();
            let (mut exact_host, _, operation) = host(&mut exact);
            let mut heap = Vec::new();
            capture(&mut exact_host, operation, &mut heap).unwrap();
            capture(&mut exact_host, operation, &mut heap).unwrap();
            assert_eq!(exact_host.patterns.len(), 2);
            assert_eq!(exact_host.syntax_work.as_deref().unwrap().consumed(), total);
        }
    }

    #[test]
    fn pattern_parse_success_and_failure_arenas_pay_before_growth() {
        use super::{
            HeapCell, RuntimeFailure, SyntaxHost, Value, allocate_heap, constructor_fields,
        };
        use crate::{
            module::ModuleId,
            syntax::MacroOutputNode,
            syntax_resource::SyntaxBudget,
            types::{ConstructorId, NominalTypeId, OperationId, TypeWorkBudget},
        };

        fn host(budget: &mut SyntaxBudget) -> (SyntaxHost<'_>, OperationId) {
            let mut host = scalar_host(budget);
            let operation = OperationId::new(host.ops, 0);
            host.operations.insert(operation, "parse_pattern".into());
            let owner = NominalTypeId::new(ModuleId::new(0), 0);
            for (index, name) in (0u32..).zip([
                "Syntax",
                "NoNodes",
                "MoreNodes",
                "GroupNode",
                "TypeNode",
                "PatternNode",
                "ExpressionNode",
                "IdentifierNode",
                "TokenNode",
                "ParsedPattern",
                "ParseRejected",
            ]) {
                host.constructors
                    .insert(name.into(), ConstructorId::new(owner, index));
            }
            (host, operation)
        }

        fn input_syntax(host: &mut SyntaxHost<'_>, heap: &mut Vec<HeapCell>, valid: bool) -> Value {
            let nodes = if valid {
                vec![MacroOutputNode::Token(
                    crate::lexer::TokenKind::Wildcard,
                    "_".into(),
                    host.frame.invocation.into(),
                )]
            } else {
                Vec::new()
            };
            host.syntax_value(&nodes, heap, 0).unwrap()
        }

        fn parse_pattern(
            host: &mut SyntaxHost<'_>,
            operation: OperationId,
            syntax: &Value,
            heap: &mut Vec<HeapCell>,
        ) -> Result<Value, RuntimeFailure> {
            let fields = vec![host.input(), syntax.clone()].into_boxed_slice();
            let argument = Value::Location(allocate_heap(heap, HeapCell::Tuple(fields)).unwrap());
            host.request(operation, argument, heap, &mut TypeWorkBudget::unbounded())
        }

        // Synthetic constructors exercise the real parser and arenas. The
        // separate imported test checks the validated public host graph.
        for valid in [true, false] {
            let mut measured = SyntaxBudget::default();
            measured.charge_units(17).unwrap();
            let (mut measured_host, operation) = host(&mut measured);
            let mut heap = Vec::new();
            let syntax = input_syntax(&mut measured_host, &mut heap, valid);
            let mut first = 0;
            for expected_len in 1..=2 {
                let result =
                    parse_pattern(&mut measured_host, operation, &syntax, &mut heap).unwrap();
                let (tag, _) = constructor_fields(&result, &heap).unwrap();
                assert_eq!(
                    tag,
                    measured_host
                        .constructor(if valid {
                            "ParsedPattern"
                        } else {
                            "ParseRejected"
                        })
                        .unwrap()
                );
                assert_eq!(
                    if valid {
                        measured_host.patterns.len()
                    } else {
                        measured_host.parse_failures.len()
                    },
                    expected_len
                );
                if expected_len == 1 {
                    first = measured_host.syntax_work.as_deref().unwrap().consumed();
                }
            }
            let total = measured_host.syntax_work.as_deref().unwrap().consumed();
            drop(measured_host);

            let mut initial_short = SyntaxBudget::with_limit(first - 2);
            initial_short.charge_units(17).unwrap();
            let (mut initial_host, operation) = host(&mut initial_short);
            let mut heap = Vec::new();
            let syntax = input_syntax(&mut initial_host, &mut heap, valid);
            assert!(matches!(
                parse_pattern(&mut initial_host, operation, &syntax, &mut heap),
                Err(RuntimeFailure::Report(report))
                    if report.primary.reason == "internal.resource.syntax-work"
            ));
            assert!(initial_host.patterns.is_empty());
            assert!(initial_host.parse_failures.is_empty());
            assert_eq!(
                initial_host.syntax_work.as_deref().unwrap().consumed(),
                first - 2
            );
            drop(initial_host);

            let mut spare = SyntaxBudget::default();
            spare.charge_units(17).unwrap();
            let (mut spare_host, operation) = host(&mut spare);
            if valid {
                spare_host.patterns.reserve_exact(2);
            } else {
                spare_host.parse_failures.reserve_exact(2);
            }
            let mut heap = Vec::new();
            let syntax = input_syntax(&mut spare_host, &mut heap, valid);
            parse_pattern(&mut spare_host, operation, &syntax, &mut heap).unwrap();
            parse_pattern(&mut spare_host, operation, &syntax, &mut heap).unwrap();
            assert_eq!(
                spare_host.syntax_work.as_deref().unwrap().consumed() + 4,
                total
            );
            drop(spare_host);

            // The second push reserves two requested slots plus one live
            // move; constructing ParsedPattern/ParseRejected costs one more.
            let mut short = SyntaxBudget::with_limit(total - 2);
            short.charge_units(17).unwrap();
            let (mut short_host, operation) = host(&mut short);
            let mut heap = Vec::new();
            let syntax = input_syntax(&mut short_host, &mut heap, valid);
            parse_pattern(&mut short_host, operation, &syntax, &mut heap).unwrap();
            assert!(matches!(
                parse_pattern(&mut short_host, operation, &syntax, &mut heap),
                Err(RuntimeFailure::Report(report))
                    if report.primary.reason == "internal.resource.syntax-work"
            ));
            assert_eq!(
                if valid {
                    short_host.patterns.len()
                } else {
                    short_host.parse_failures.len()
                },
                1
            );
            assert_eq!(
                short_host.syntax_work.as_deref().unwrap().consumed(),
                total - 4
            );
            drop(short_host);

            for _ in 0..2 {
                let mut exact = SyntaxBudget::with_limit(total);
                exact.charge_units(17).unwrap();
                let (mut exact_host, operation) = host(&mut exact);
                let mut heap = Vec::new();
                let syntax = input_syntax(&mut exact_host, &mut heap, valid);
                parse_pattern(&mut exact_host, operation, &syntax, &mut heap).unwrap();
                parse_pattern(&mut exact_host, operation, &syntax, &mut heap).unwrap();
                assert_eq!(exact_host.syntax_work.as_deref().unwrap().consumed(), total);
            }
        }
    }

    #[test]
    fn pattern_syntax_issuance_arena_refuses_before_copy_and_retries() {
        use super::{HeapCell, RuntimeFailure, SyntaxHost};
        use crate::{
            module::ModuleId,
            surface::{SurfacePattern, SurfacePatternCapture, SurfacePatternKind},
            syntax::MacroOutputNode,
            syntax_resource::SyntaxBudget,
            types::{ConstructorId, NominalTypeId},
        };
        use std::sync::Arc;

        fn host(budget: &mut SyntaxBudget) -> SyntaxHost<'_> {
            let mut host = scalar_host(budget);
            let owner = NominalTypeId::new(ModuleId::new(0), 0);
            for (index, name) in (0u32..).zip(["NoNodes", "Syntax", "PatternNode", "MoreNodes"]) {
                host.constructors
                    .insert(name.into(), ConstructorId::new(owner, index));
            }
            host
        }

        fn capture_nodes(host: &SyntaxHost<'_>) -> (Vec<MacroOutputNode>, Arc<[MacroOutputNode]>) {
            let span = host.frame.invocation;
            let contents: Arc<[MacroOutputNode]> = Arc::from([]);
            (
                vec![MacroOutputNode::ForwardedPattern(
                    SurfacePatternCapture {
                        pattern: SurfacePattern {
                            kind: SurfacePatternKind::Wildcard,
                            span,
                            diagnostic: None,
                        },
                        contents: Arc::clone(&contents),
                    },
                    span.into(),
                )],
                contents,
            )
        }

        let mut measured = SyntaxBudget::default();
        measured.charge_units(17).unwrap();
        let mut measured_host = host(&mut measured);
        let (nodes, contents) = capture_nodes(&measured_host);
        let base = Arc::strong_count(&contents);
        let mut heap: Vec<HeapCell> = Vec::new();
        measured_host.syntax_value(&nodes, &mut heap, 0).unwrap();
        let first = measured_host.syntax_work.as_deref().unwrap().consumed();
        assert_eq!(measured_host.patterns.len(), 1);
        assert_eq!(Arc::strong_count(&contents), base + 1);
        measured_host.syntax_value(&nodes, &mut heap, 0).unwrap();
        assert_eq!(measured_host.patterns.len(), 2);
        assert_eq!(Arc::strong_count(&contents), base + 2);
        let total = measured_host.syntax_work.as_deref().unwrap().consumed();
        drop(measured_host);

        let mut initial_short = SyntaxBudget::with_limit(first - 11);
        initial_short.charge_units(17).unwrap();
        let mut initial_host = host(&mut initial_short);
        let (nodes, contents) = capture_nodes(&initial_host);
        let base = Arc::strong_count(&contents);
        assert!(matches!(
            initial_host.syntax_value(&nodes, &mut Vec::new(), 0),
            Err(RuntimeFailure::Report(report))
                if report.primary.reason == "internal.resource.syntax-work"
        ));
        assert!(initial_host.patterns.is_empty());
        assert_eq!(Arc::strong_count(&contents), base);
        assert_eq!(
            initial_host.syntax_work.as_deref().unwrap().consumed(),
            first - 11
        );
        drop(initial_host);

        let mut spare = SyntaxBudget::default();
        spare.charge_units(17).unwrap();
        let mut spare_host = host(&mut spare);
        spare_host.patterns.reserve_exact(2);
        let (nodes, contents) = capture_nodes(&spare_host);
        let base = Arc::strong_count(&contents);
        let mut heap = Vec::new();
        spare_host.syntax_value(&nodes, &mut heap, 0).unwrap();
        spare_host.syntax_value(&nodes, &mut heap, 0).unwrap();
        assert_eq!(Arc::strong_count(&contents), base + 2);
        assert_eq!(
            spare_host.syntax_work.as_deref().unwrap().consumed() + 4,
            total
        );
        drop(spare_host);

        // Two requested slots plus one live move are paid before the second
        // capture clone; ten later units build the returned Syntax value.
        let mut short = SyntaxBudget::with_limit(total - 11);
        short.charge_units(17).unwrap();
        let mut short_host = host(&mut short);
        let (nodes, contents) = capture_nodes(&short_host);
        let base = Arc::strong_count(&contents);
        let mut heap = Vec::new();
        short_host.syntax_value(&nodes, &mut heap, 0).unwrap();
        assert!(matches!(
            short_host.syntax_value(&nodes, &mut heap, 0),
            Err(RuntimeFailure::Report(report))
                if report.primary.reason == "internal.resource.syntax-work"
        ));
        assert_eq!(short_host.patterns.len(), 1);
        assert_eq!(Arc::strong_count(&contents), base + 1);
        assert_eq!(
            short_host.syntax_work.as_deref().unwrap().consumed(),
            total - 13
        );
        drop(short_host);

        for _ in 0..2 {
            let mut exact = SyntaxBudget::with_limit(total);
            exact.charge_units(17).unwrap();
            let mut exact_host = host(&mut exact);
            let (nodes, _) = capture_nodes(&exact_host);
            let mut heap = Vec::new();
            exact_host.syntax_value(&nodes, &mut heap, 0).unwrap();
            exact_host.syntax_value(&nodes, &mut heap, 0).unwrap();
            assert_eq!(exact_host.patterns.len(), 2);
            assert_eq!(exact_host.syntax_work.as_deref().unwrap().consumed(), total);
        }
    }

    #[test]
    fn type_host_deep_packet_roundtrip_on_a_512k_stack() {
        const CHILD: &str = "ASH_TYPE_HOST_512K_CHILD";
        if std::env::var_os(CHILD).is_none() {
            let output = std::process::Command::new(std::env::current_exe().unwrap())
                .args([
                    "--exact",
                    "eval::machine::syntax::tests::type_host_deep_packet_roundtrip_on_a_512k_stack",
                    "--nocapture",
                    "--test-threads=1",
                ])
                .env(CHILD, "1")
                .output()
                .unwrap();
            let stdout = String::from_utf8_lossy(&output.stdout);
            let stderr = String::from_utf8_lossy(&output.stderr);
            print!("{stdout}");
            eprint!("{stderr}");
            assert!(
                output.status.success(),
                "512 KiB child failed: {}",
                output.status
            );
            for marker in [
                "type host stack: issued, unwrapped and transferred composed-128 packet",
                "type host stack: dropped final accepted alias",
                "type host stack: refused composed-129 and dropped final alias",
                "type host stack: paid partial shortage and dropped final alias",
            ] {
                assert!(stderr.contains(marker), "missing marker {marker}");
            }
            return;
        }

        std::thread::Builder::new()
            .stack_size(512 * 1024)
            .spawn(|| {
                use super::{
                    HeapCell, RuntimeFailure, SyntaxHost, Value, constructor_fields, pair,
                };
                use crate::{
                    module::ModuleId,
                    source::Span,
                    surface::{SurfaceType, SurfaceTypeCapture, SurfaceTypeKind},
                    syntax::{MacroDelimiter, MacroOutputNode},
                    syntax_resource::SyntaxBudget,
                    types::{ConstructorId, NominalTypeId, OperationId, TypeWorkBudget},
                };
                use std::sync::Arc;

                fn make_host(budget: &mut SyntaxBudget) -> (SyntaxHost<'_>, OperationId) {
                    let mut host = scalar_host(budget);
                    let operation = OperationId::new(host.ops, 0);
                    host.operations.insert(operation, "type_syntax".into());
                    let owner = NominalTypeId::new(ModuleId::new(0), 0);
                    for (index, name) in (0u32..).zip([
                        "Syntax",
                        "NoNodes",
                        "MoreNodes",
                        "GroupNode",
                        "TypeNode",
                        "ExpressionNode",
                        "IdentifierNode",
                        "TokenNode",
                        "Parentheses",
                        "Braces",
                    ]) {
                        host.constructors
                            .insert(name.into(), ConstructorId::new(owner, index));
                    }
                    (host, operation)
                }

                fn packet(
                    depth: usize,
                    span: Span,
                ) -> (Vec<MacroOutputNode>, Arc<[MacroOutputNode]>) {
                    let mut node = MacroOutputNode::Token(
                        crate::lexer::TokenKind::IntType,
                        "Int".into(),
                        span.into(),
                    );
                    for _ in 0..depth {
                        node = MacroOutputNode::Group(
                            MacroDelimiter::Parentheses,
                            vec![node],
                            span.into(),
                        );
                    }
                    let contents: Arc<[MacroOutputNode]> = Arc::from([node]);
                    let nodes = vec![MacroOutputNode::ForwardedType(
                        SurfaceTypeCapture {
                            ty: SurfaceType {
                                kind: SurfaceTypeKind::Int,
                                span,
                                diagnostic: None,
                            },
                            contents: Arc::clone(&contents),
                        },
                        span.into(),
                    )];
                    (nodes, contents)
                }

                let mut budget = SyntaxBudget::default();
                let (mut host, operation) = make_host(&mut budget);
                let (nodes, alias) = packet(126, host.frame.invocation);
                let weak = Arc::downgrade(&alias);
                assert_eq!(2 + 126, crate::parser::STRUCTURAL_DEPTH_LIMIT);
                eprintln!("type host stack phase: issue composed-128 packet");
                let mut heap: Vec<HeapCell> = Vec::new();
                let issued = host.syntax_value(&nodes, &mut heap, 0).unwrap();
                assert_eq!(host.types.len(), 1);
                let (_, Some(children)) = constructor_fields(&issued, &heap).unwrap() else {
                    panic!("expected Syntax");
                };
                let (_, Some(fields)) = constructor_fields(children, &heap).unwrap() else {
                    panic!("expected MoreNodes");
                };
                let (node, _) = pair(fields, &heap).unwrap();
                let (_, Some(fields)) = constructor_fields(node, &heap).unwrap() else {
                    panic!("expected TypeNode");
                };
                let (handle, _) = pair(fields, &heap).unwrap();
                let handle: Value = handle.clone();
                eprintln!("type host stack phase: unwrap composed-128 packet");
                let unwrapped = host
                    .request(
                        operation,
                        handle,
                        &mut heap,
                        &mut TypeWorkBudget::unbounded(),
                    )
                    .unwrap();
                eprintln!("type host stack phase: transfer unwrapped packet");
                let transferred = host.transfer_syntax(&unwrapped, &heap, 0).unwrap();
                let mut level = transferred.as_slice();
                for _ in 0..126 {
                    let [MacroOutputNode::Group(MacroDelimiter::Parentheses, children, _)] = level
                    else {
                        panic!("expected a retained group");
                    };
                    level = children;
                }
                assert!(matches!(
                    level,
                    [MacroOutputNode::Token(
                        crate::lexer::TokenKind::IntType,
                        _,
                        _
                    )]
                ));
                assert!(Arc::ptr_eq(&host.types[0].contents, &alias));
                drop(transferred);
                eprintln!("type host stack: issued, unwrapped and transferred composed-128 packet");
                drop(heap);
                drop(host);
                drop(nodes);
                assert_eq!(Arc::strong_count(&alias), 1);
                eprintln!("type host stack phase: drop final accepted alias");
                drop(alias);
                assert!(weak.upgrade().is_none());
                eprintln!("type host stack: dropped final accepted alias");

                let mut budget = SyntaxBudget::default();
                let (mut host, _) = make_host(&mut budget);
                let (nodes, alias) = packet(127, host.frame.invocation);
                let weak = Arc::downgrade(&alias);
                assert_eq!(2 + 127, crate::parser::STRUCTURAL_DEPTH_LIMIT + 1);
                eprintln!("type host stack phase: refuse composed-129 packet");
                assert!(matches!(
                    host.syntax_value(&nodes, &mut Vec::new(), 0),
                    Err(RuntimeFailure::Report(report))
                        if report.primary.reason == "internal.resource.structural-depth"
                ));
                assert!(host.types.is_empty());
                drop(host);
                drop(nodes);
                assert_eq!(Arc::strong_count(&alias), 1);
                drop(alias);
                assert!(weak.upgrade().is_none());
                eprintln!("type host stack: refused composed-129 and dropped final alias");

                let mut budget = SyntaxBudget::with_limit(100);
                let (mut host, _) = make_host(&mut budget);
                let (nodes, alias) = packet(126, host.frame.invocation);
                let weak = Arc::downgrade(&alias);
                eprintln!("type host stack phase: refuse paid partial packet");
                assert!(matches!(
                    host.syntax_value(&nodes, &mut Vec::new(), 0),
                    Err(RuntimeFailure::Report(report))
                        if report.primary.reason == "internal.resource.syntax-work"
                ));
                assert!(host.syntax_work.as_deref().unwrap().consumed() > 1);
                assert!(host.types.is_empty());
                drop(host);
                drop(nodes);
                assert_eq!(Arc::strong_count(&alias), 1);
                drop(alias);
                assert!(weak.upgrade().is_none());
                eprintln!("type host stack: paid partial shortage and dropped final alias");
            })
            .unwrap()
            .join()
            .unwrap();
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
                eprintln!("actual host transfer completed with raw-output depth-127 metadata");
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

    fn issued_declaration(
        fixture: &DeclarationHostFixture,
        host: &mut super::SyntaxHost<'_>,
        heap: &mut Vec<super::HeapCell>,
    ) -> super::Value {
        use super::{HeapCell, Value, allocate_heap, constructor_fields};
        use crate::{integer::Integer, types::TypeWorkBudget};

        let input = Value::Location(
            allocate_heap(
                heap,
                HeapCell::Tuple(vec![host.input(), Value::integer(Integer::from_i64(0))].into()),
            )
            .unwrap(),
        );
        let captured = host
            .request(
                fixture.capture,
                input,
                heap,
                &mut TypeWorkBudget::unbounded(),
            )
            .unwrap();
        let (_, capture) = constructor_fields(&captured, heap).unwrap();
        let (_, declaration) = constructor_fields(capture.unwrap(), heap).unwrap();
        declaration.unwrap().clone()
    }

    fn declaration_node_result(
        host: &mut super::SyntaxHost<'_>,
        heap: &mut Vec<super::HeapCell>,
        declaration: super::Value,
        origin: super::Value,
        group_origin: super::Value,
        groups: usize,
    ) -> (super::Value, super::Value) {
        use super::{HeapCell, SyntaxHost, Value, allocate_heap};

        fn tuple(heap: &mut Vec<HeapCell>, fields: Vec<Value>) -> Value {
            Value::Location(allocate_heap(heap, HeapCell::Tuple(fields.into())).unwrap())
        }
        fn syntax(host: &mut SyntaxHost<'_>, heap: &mut Vec<HeapCell>, node: Value) -> Value {
            let end = host.construct(heap, "NoNodes", None).unwrap();
            let pair = tuple(heap, vec![node, end]);
            let nodes = host.construct(heap, "MoreNodes", Some(pair)).unwrap();
            host.construct(heap, "Syntax", Some(nodes)).unwrap()
        }
        let pair = tuple(heap, vec![declaration, origin]);
        let node = host.construct(heap, "DeclarationNode", Some(pair)).unwrap();
        let mut value = syntax(host, heap, node);
        for _ in 0..groups {
            let delimiter = host.construct(heap, "Parentheses", None).unwrap();
            let fields = tuple(heap, vec![delimiter, value, group_origin.clone()]);
            let group = host.construct(heap, "GroupNode", Some(fields)).unwrap();
            value = syntax(host, heap, group);
        }
        let expanded = host
            .construct(heap, "Expanded", Some(value.clone()))
            .unwrap();
        (value, expanded)
    }

    #[test]
    fn declaration_node_transfer_authenticates_handles_before_packet_work() {
        use super::{RuntimeFailure, Value};
        use crate::{
            eval::value::CompilerSyntaxHandleKind,
            lexer::TokenKind,
            surface::{SurfaceDeclarationCapture, SurfaceSyntaxCapture},
            syntax::MacroOutputNode,
            syntax_resource::SyntaxBudget,
            types::TypeWorkBudget,
        };
        use std::sync::Arc;

        let fixture = DeclarationHostFixture::new();
        let packet: Arc<[MacroOutputNode]> = Arc::from([MacroOutputNode::Token(
            TokenKind::Type,
            Arc::from("type"),
            fixture.caller.span.into(),
        )]);
        let captures = [SurfaceSyntaxCapture::Declaration(
            SurfaceDeclarationCapture {
                contents: Arc::clone(&packet),
            },
        )];
        let mut budget = SyntaxBudget::default();
        let mut host = fixture.host(&captures, &mut budget).unwrap();
        assert!(!host.type_accounting);
        let mut heap = Vec::new();
        let declaration = issued_declaration(&fixture, &mut host, &mut heap);
        let origin = host.issue_origin(fixture.caller.span.into()).unwrap();
        let mut foreign_budget = SyntaxBudget::default();
        let mut foreign = fixture.host(&captures, &mut foreign_budget).unwrap();
        let foreign_origin = foreign.issue_origin(fixture.caller.span.into()).unwrap();
        let foreign_declaration = issued_declaration(&fixture, &mut foreign, &mut Vec::new());
        let (stale_origin, stale_declaration) = {
            let mut stale_budget = SyntaxBudget::default();
            let mut stale = fixture.host(&captures, &mut stale_budget).unwrap();
            let origin = stale.issue_origin(fixture.caller.span.into()).unwrap();
            let declaration = issued_declaration(&fixture, &mut stale, &mut Vec::new());
            (origin, declaration)
        };
        let retained = Arc::strong_count(&packet);
        let invalid_origins = [
            foreign_origin,
            stale_origin,
            host.input(),
            host.handle(CompilerSyntaxHandleKind::Origin(999)),
            Value::Unit,
        ];
        for invalid in invalid_origins {
            *host.syntax_work.as_deref_mut().unwrap() = SyntaxBudget::default();
            let (_, result) = declaration_node_result(
                &mut host,
                &mut heap,
                declaration.clone(),
                invalid,
                origin.clone(),
                0,
            );
            // Exactly the list traversal and leaf setup fit. Packet inspection
            // would exhaust the remaining budget before authentication.
            *host.syntax_work.as_deref_mut().unwrap() = SyntaxBudget::with_limit(17 + 5);
            host.syntax_work
                .as_deref_mut()
                .unwrap()
                .charge_units(17)
                .unwrap();
            assert!(matches!(
                host.transfer(&result, &heap, &mut TypeWorkBudget::unbounded()),
                Err(RuntimeFailure::InvalidControlState)
            ));
            assert_eq!(host.syntax_work.as_deref().unwrap().consumed(), 22);
            assert_eq!(Arc::strong_count(&packet), retained);
        }
        for invalid in [
            foreign_declaration,
            stale_declaration,
            origin.clone(),
            host.handle(CompilerSyntaxHandleKind::Declaration(999)),
        ] {
            *host.syntax_work.as_deref_mut().unwrap() = SyntaxBudget::default();
            let (_, result) = declaration_node_result(
                &mut host,
                &mut heap,
                invalid,
                origin.clone(),
                origin.clone(),
                0,
            );
            *host.syntax_work.as_deref_mut().unwrap() = SyntaxBudget::with_limit(17 + 5);
            host.syntax_work
                .as_deref_mut()
                .unwrap()
                .charge_units(17)
                .unwrap();
            assert!(matches!(
                host.transfer(&result, &heap, &mut TypeWorkBudget::unbounded()),
                Err(RuntimeFailure::InvalidControlState)
            ));
            assert_eq!(host.syntax_work.as_deref().unwrap().consumed(), 22);
            assert_eq!(Arc::strong_count(&packet), retained);
        }
        eprintln!(
            "DeclarationNode rejects foreign, stale, wrong-kind and out-of-range declaration and Origin handles before packet work"
        );
    }

    #[test]
    fn declaration_only_group_transfer_pays_growth_and_composed_depth() {
        use super::RuntimeFailure;
        use crate::{
            lexer::TokenKind,
            surface::{SurfaceDeclarationCapture, SurfaceSyntaxCapture},
            syntax::{MacroDelimiter, MacroOutputNode, TransformerOutput},
            syntax_resource::SyntaxBudget,
            types::TypeWorkBudget,
        };
        use std::sync::Arc;

        fn run(
            fixture: &DeclarationHostFixture,
            packet: &Arc<[MacroOutputNode]>,
            groups: usize,
            limit: usize,
            public: bool,
        ) -> (Result<Vec<MacroOutputNode>, RuntimeFailure>, usize) {
            let captures = [SurfaceSyntaxCapture::Declaration(
                SurfaceDeclarationCapture {
                    contents: Arc::clone(packet),
                },
            )];
            let mut budget = SyntaxBudget::default();
            let mut host = fixture.host(&captures, &mut budget).unwrap();
            assert!(!host.type_accounting);
            let mut heap = Vec::new();
            let declaration = issued_declaration(fixture, &mut host, &mut heap);
            let origin = host.issue_origin(fixture.caller.span.into()).unwrap();
            let (syntax, result) = declaration_node_result(
                &mut host,
                &mut heap,
                declaration,
                origin.clone(),
                origin,
                groups,
            );
            *host.syntax_work.as_deref_mut().unwrap() = SyntaxBudget::with_limit(17 + limit);
            host.syntax_work
                .as_deref_mut()
                .unwrap()
                .charge_units(17)
                .unwrap();
            let result = if public {
                host.transfer(&result, &heap, &mut TypeWorkBudget::unbounded())
                    .map(|output| match output {
                        TransformerOutput::Expanded(nodes) => nodes,
                        _ => panic!("expected expanded declaration"),
                    })
            } else {
                host.transfer_syntax_inner(&syntax, &heap, 0, false)
            };
            let consumed = host.syntax_work.as_deref().unwrap().consumed();
            drop(host);
            drop(heap);
            (result, consumed)
        }

        let fixture = DeclarationHostFixture::new();
        let packet: Arc<[MacroOutputNode]> = Arc::from([MacroOutputNode::Token(
            TokenKind::Type,
            Arc::from("type"),
            fixture.caller.span.into(),
        )]);
        let retained = Arc::strong_count(&packet);
        let (measured, total) = run(&fixture, &packet, 2, 10_000, true);
        let measured = measured.unwrap();
        let (legacy, legacy_total) = run(&fixture, &packet, 2, 10_000, false);
        assert_eq!(legacy.unwrap(), measured);
        // Group continuation stack 1+3 and two parent-output slots 1+1.
        assert_eq!(total - legacy_total, 6);
        drop(measured);
        assert_eq!(Arc::strong_count(&packet), retained);
        let cost = total - 17;
        let (short, paid) = run(&fixture, &packet, 2, cost - 1, true);
        assert!(matches!(short, Err(RuntimeFailure::Report(report))
            if report.primary.reason_code() == "internal.resource.syntax-work"));
        assert!(paid <= 17 + cost - 1);
        assert_eq!(Arc::strong_count(&packet), retained);
        for _ in 0..2 {
            let (exact, paid) = run(&fixture, &packet, 2, cost, true);
            assert_eq!(paid, total);
            let output = exact.unwrap();
            let [MacroOutputNode::Group(_, first, _)] = output.as_slice() else {
                panic!("outer group survived host teardown")
            };
            let [MacroOutputNode::Group(_, second, _)] = first.as_slice() else {
                panic!("inner group survived host teardown")
            };
            let [MacroOutputNode::ForwardedDeclaration(capture, origin)] = second.as_slice() else {
                panic!("declaration survived host teardown")
            };
            assert!(Arc::ptr_eq(&capture.contents, &packet));
            assert_eq!(origin.primary(), fixture.caller.span);
            drop(output);
            assert_eq!(Arc::strong_count(&packet), retained);
        }

        for (inside, success) in [(125, true), (126, false)] {
            let mut node = MacroOutputNode::Token(
                TokenKind::Type,
                Arc::from("type"),
                fixture.caller.span.into(),
            );
            for _ in 0..inside {
                node = MacroOutputNode::Group(
                    MacroDelimiter::Parentheses,
                    vec![node],
                    fixture.caller.span.into(),
                );
            }
            let packet: Arc<[MacroOutputNode]> = Arc::from([node]);
            let retained = Arc::strong_count(&packet);
            let (result, _) = run(&fixture, &packet, 2, 10_000, true);
            if success {
                drop(result.unwrap());
            } else {
                assert!(matches!(result, Err(RuntimeFailure::Report(report))
                    if report.primary.reason_code() == "internal.resource.structural-depth"));
            }
            assert_eq!(Arc::strong_count(&packet), retained);
        }
        eprintln!(
            "declaration-only transfer pays group and parent growth: pre-spent 17, short/exact/retry, depth 128 accepted and 129 refused"
        );
    }

    #[test]
    fn declaration_host_source_snapshot_reserves_path_text_and_line_index() {
        use crate::{eval::RuntimeFailure, syntax_resource::SyntaxBudget};
        use std::sync::Arc;

        fn constructor_work(fixture: &DeclarationHostFixture) -> usize {
            let mut budget = SyntaxBudget::default();
            let host = fixture.host(&[], &mut budget).unwrap();
            drop(host);
            budget.consumed()
        }

        let original = "type Item = Item\n";
        let larger_text = format!("{original}{}\n{}\n", "a".repeat(128), "b".repeat(128));
        let base = DeclarationHostFixture::new();
        let path =
            DeclarationHostFixture::with_source("a-longer-component-source-path.ash", original);
        let text = DeclarationHostFixture::with_source("component.ash", &larger_text);
        let base_work = constructor_work(&base);
        let base_snapshot = base.source.snapshot_work().unwrap();
        for fixture in [&path, &text] {
            let snapshot = fixture.source.snapshot_work().unwrap();
            assert!(snapshot > base_snapshot);
            assert_eq!(
                constructor_work(fixture) - base_work,
                snapshot - base_snapshot
            );
        }

        let mut name_work = SyntaxBudget::default();
        crate::syntax::charge_type_name_copy(&text.caller, 0, &mut name_work).unwrap();
        let snapshot = text.source.snapshot_work().unwrap();
        let prefix = constructor_work(&text) - snapshot - name_work.consumed();
        let mut short = SyntaxBudget::with_limit(prefix + snapshot - 1);
        let frames = Arc::strong_count(&text.frame);
        let contexts = Arc::strong_count(&text.contexts);
        assert!(
            matches!(text.host(&[], &mut short), Err(RuntimeFailure::Report(report))
            if report.primary.reason_code() == "internal.resource.syntax-work"
                && report.primary.resource().is_none())
        );
        assert_eq!(
            short.consumed(),
            prefix,
            "the snapshot reservation is atomic"
        );
        assert_eq!(Arc::strong_count(&text.frame), frames);
        assert_eq!(Arc::strong_count(&text.contexts), contexts);
        assert_eq!(text.source.text(), larger_text);
        eprintln!(
            "source snapshot path, text and line-index growth; one-short refusal before source clone, paid prefix {prefix}"
        );
    }

    #[test]
    fn declaration_host_refuses_foreign_handles_and_protected_bridges_before_copy() {
        use super::{HeapCell, RuntimeFailure, Value, allocate_heap, constructor_fields};
        use crate::{
            eval::value::CompilerSyntaxHandleKind,
            integer::Integer,
            parser::{ExpectedForm, FoundToken, ParseReason},
            surface::{
                SurfaceDeclarationCapture, SurfaceExpr, SurfaceExprKind, SurfaceExpressionCapture,
                SurfacePattern, SurfacePatternCapture, SurfacePatternKind, SurfaceSyntaxCapture,
            },
            syntax::{MacroOrigin, MacroOutputNode},
            syntax_resource::SyntaxBudget,
            types::{ConstructorId, TypeWorkBudget},
        };
        use std::sync::Arc;

        let fixture = DeclarationHostFixture::new();
        let span = fixture.caller.span;
        let nested: Arc<[MacroOutputNode]> = Arc::from([]);
        let expression = SurfaceExpressionCapture {
            contains_protected_type: false,
            quote_sites: Default::default(),
            expression: SurfaceExpr {
                kind: SurfaceExprKind::Unit,
                span,
                diagnostic: None,
            },
            contents: Arc::clone(&nested),
        };
        let flat_expression = SurfaceSyntaxCapture::Expression(expression.clone());
        let pattern = SurfaceSyntaxCapture::Pattern(SurfacePatternCapture {
            pattern: SurfacePattern {
                kind: SurfacePatternKind::Wildcard,
                span,
                diagnostic: None,
            },
            contents: Arc::clone(&nested),
        });
        let before = Arc::strong_count(&nested);
        let mut expression_budget = SyntaxBudget::default();
        let expression_host = fixture
            .host(
                std::slice::from_ref(&flat_expression),
                &mut expression_budget,
            )
            .expect("the Some host admits a flat Expression capture");
        assert_eq!(Arc::strong_count(&nested), before + 1);
        drop(expression_host);
        assert_eq!(Arc::strong_count(&nested), before);
        let mut pattern_budget = SyntaxBudget::default();
        let pattern_host = fixture
            .host(std::slice::from_ref(&pattern), &mut pattern_budget)
            .expect("the Some host admits a flat Pattern capture");
        assert_eq!(Arc::strong_count(&nested), before + 1);
        drop(pattern_host);
        assert_eq!(Arc::strong_count(&nested), before);
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
        let rejected = ConstructorId::new(fixture.constructors["Expanded"].owner(), 100);
        host.constructors.insert("ParseRejected".into(), rejected);
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
        let expressions_before = host.expressions.len();
        let failures_before = host.parse_failures.len();
        let result = host
            .request(
                fixture.parse_expression,
                bridge,
                &mut heap,
                &mut TypeWorkBudget::unbounded(),
            )
            .unwrap();
        let (tag, Some(failure)) = constructor_fields(&result, &heap).unwrap() else {
            panic!("expected a parse rejection")
        };
        assert_eq!(tag, rejected);
        assert_eq!(host.expressions.len(), expressions_before);
        assert_eq!(host.parse_failures.len(), failures_before + 1);
        let CompilerSyntaxHandleKind::ParseFailure(index) = host.admitted_handle(failure).unwrap()
        else {
            panic!("expected a parse failure handle")
        };
        assert_eq!(index, failures_before);
        let (diagnostics, resource) = &host.parse_failures[index];
        assert!(resource.is_none());
        assert_eq!(diagnostics[0].reason, ParseReason::ExpectedOperand);
        assert_eq!(diagnostics[0].expected_form(), Some(ExpectedForm::Operand));
        assert_eq!(diagnostics[0].found_token(), Some(FoundToken::EndOfFile));

        // This indexed expression is seeded to check repeated unwrapping
        // independently of the parser.
        host.expressions.push(SurfaceExpressionCapture {
            contains_protected_type: false,
            quote_sites: Default::default(),
            expression: SurfaceExpr {
                kind: SurfaceExprKind::Unit,
                span,
                diagnostic: None,
            },
            contents: Arc::clone(&nested),
        });
        let mut foreign_expression_budget = SyntaxBudget::default();
        let mut foreign_expression = fixture
            .host(&captures, &mut foreign_expression_budget)
            .unwrap();
        foreign_expression
            .expressions
            .push(host.expressions[0].clone());
        let foreign_expression_handle =
            foreign_expression.handle(CompilerSyntaxHandleKind::Expression(0));
        let stale_expression_handle = {
            let mut stale_budget = SyntaxBudget::default();
            let mut stale = fixture.host(&captures, &mut stale_budget).unwrap();
            stale.expressions.push(host.expressions[0].clone());
            stale.handle(CompilerSyntaxHandleKind::Expression(0))
        };
        let nested_retained = Arc::strong_count(&nested);
        let heap_before = heap.len();
        for invalid in [
            foreign_expression_handle,
            stale_expression_handle,
            host.input(),
            host.handle(CompilerSyntaxHandleKind::Type(0)),
            host.handle(CompilerSyntaxHandleKind::Expression(999)),
            Value::Unit,
        ] {
            assert!(matches!(
                host.request(
                    fixture.expression_syntax,
                    invalid,
                    &mut heap,
                    &mut TypeWorkBudget::unbounded(),
                ),
                Err(RuntimeFailure::InvalidControlState)
            ));
            assert_eq!(host.expressions.len(), 1);
            assert_eq!(heap.len(), heap_before);
            assert_eq!(Arc::strong_count(&nested), nested_retained);
        }
        for _ in 0..2 {
            let syntax = host
                .request(
                    fixture.expression_syntax,
                    host.handle(CompilerSyntaxHandleKind::Expression(0)),
                    &mut heap,
                    &mut TypeWorkBudget::unbounded(),
                )
                .unwrap();
            assert_eq!(
                constructor_fields(&syntax, &heap).unwrap().0,
                fixture.constructors["Syntax"]
            );
            assert_eq!(Arc::strong_count(&nested), nested_retained);
        }

        let combined =
            MacroOrigin::combined(vec![span.into()], Arc::clone(&fixture.frame)).unwrap();
        let MacroOrigin::Combined { inputs, .. } = &combined else {
            unreachable!()
        };
        let origin = host.issue_origin(combined.clone()).unwrap();
        let retained = Arc::strong_count(inputs);
        for protected in ["ExpressionNode", "PatternNode", "DeclarationNode"] {
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
            "flat Expression and Pattern captures admitted; foreign handles and nested bridges refused; empty expression rejected; valid handle remains reusable"
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
                SurfaceName, SurfaceRepeatedCapture, SurfaceSyntaxCapture,
            },
            syntax::{ExpansionFrame, MacroOutputNode, SyntaxContexts},
            syntax_resource::SyntaxBudget,
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
                    quote_sites: Arc::from([]),
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
                    contains_protected_type: false,
                    quote_sites: Default::default(),
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

                let repeated = Arc::new(SurfaceRepeatedCapture { values: Vec::new() });
                let repeated_capture = [SurfaceSyntaxCapture::Repeated(Arc::clone(&repeated))];
                let repeated_references = Arc::strong_count(&repeated);
                assert!(matches!(
                    SyntaxHost::new(
                        &entry,
                        &repeated_capture,
                        &source,
                        &name,
                        0,
                        Arc::clone(&contexts),
                        Arc::clone(&frame),
                        None,
                    ),
                    Err(RuntimeFailure::InvalidControlState)
                ));
                let mut constructor_budget = SyntaxBudget::with_limit(100);
                constructor_budget.charge_units(17).unwrap();
                assert!(matches!(
                    SyntaxHost::new(
                        &entry,
                        &repeated_capture,
                        &source,
                        &name,
                        0,
                        Arc::clone(&contexts),
                        Arc::clone(&frame),
                        Some(&mut constructor_budget),
                    ),
                    Err(RuntimeFailure::InvalidControlState)
                ));
                assert_eq!(constructor_budget.consumed(), 19);
                assert_eq!(Arc::strong_count(&repeated), repeated_references);

                // Constructor admission makes this state unreachable in the ordinary host.
                let captures = vec![captures.into_iter().last().unwrap()];
                let mut request_budget = SyntaxBudget::with_limit(100);
                request_budget.charge_units(17).unwrap();
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
                    contexts: Some(contexts),
                    syntax_work: None,
                    quote_sites: Arc::from([]),
                    staged_owners: None,
                    type_accounting: false,
                    fresh_count: 0,
                    captures,
                    expressions: Vec::new(),
                    declarations: Vec::new(),
                    types: Vec::new(),
                    patterns: Vec::new(),
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
                        argument.clone(),
                        &mut heap,
                        &mut TypeWorkBudget::unbounded()
                    ),
                    Err(RuntimeFailure::InvalidControlState)
                ));
                // The repeated state is injected only to reach the request guard;
                // the real constructor above refuses it first.
                host.captures = vec![SurfaceSyntaxCapture::Repeated(Arc::clone(&repeated))];
                let repeated_references = Arc::strong_count(&repeated);
                let heap_len = heap.len();
                assert!(matches!(
                    host.request(
                        operation,
                        argument.clone(),
                        &mut heap,
                        &mut TypeWorkBudget::unbounded()
                    ),
                    Err(RuntimeFailure::InvalidControlState)
                ));
                assert_eq!(heap.len(), heap_len);
                assert_eq!(Arc::strong_count(&repeated), repeated_references);
                host.syntax_work = Some(&mut request_budget);
                assert!(matches!(
                    host.request(
                        operation,
                        argument,
                        &mut heap,
                        &mut TypeWorkBudget::unbounded()
                    ),
                    Err(RuntimeFailure::InvalidControlState)
                ));
                assert_eq!(heap.len(), heap_len);
                assert_eq!(Arc::strong_count(&repeated), repeated_references);
                drop(host);
                assert_eq!(request_budget.consumed(), 17 + 1 + "capture".len());
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
            contexts: Some(Arc::new(SyntaxContexts::new(&[], &[], &[]))),
            syntax_work: None,
            quote_sites: Arc::from([]),
            staged_owners: None,
            type_accounting: false,
            fresh_count: 0,
            captures: vec![SurfaceSyntaxCapture::Identifier(SurfaceIdentifierCapture {
                name: name.clone(),
                origin: span.into(),
            })],
            expressions: Vec::new(),
            declarations: Vec::new(),
            types: Vec::new(),
            patterns: Vec::new(),
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
            contains_protected_type: false,
            quote_sites: Default::default(),
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
            host.contexts.as_deref().unwrap(),
            &host.frame,
        )
        .expect("the mixed captured syntax is an expression");
        let original = SurfaceExpressionCapture {
            contains_protected_type: false,
            quote_sites: Default::default(),
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
