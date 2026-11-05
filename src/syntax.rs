//! Expansion of checked expression templates before ordinary resolution.

use std::{collections::HashMap, sync::Arc};

use crate::{
    module::ModuleId,
    resolved::{CheckedGlobalScheme, CheckedModule, ExportedConstructor, ExportedGlobal},
    source::Span,
    surface::{
        SurfaceBinder, SurfaceBlock, SurfaceDefinitionKind, SurfaceExpr, SurfaceExprKind,
        SurfaceExpressionCapture, SurfaceLocalDeclaration, SurfaceModule, SurfaceName,
        SurfacePattern, SurfacePatternKind, SurfaceReference, SurfaceSyntaxCapture,
        SurfaceSyntaxCaptureKind, SurfaceSyntaxDeclaration, SurfaceSyntaxImplementation,
        SurfaceSyntaxMatcherPart, SurfaceType, SurfaceTypeKind,
    },
    types::TypeWorkBudget,
};

/// Structured output transferred from one completed transformer invocation.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum MacroOutputNode {
    Expression(SurfaceExpressionCapture, MacroOrigin),
    Identifier(SurfaceName, MacroOrigin),
    Token(crate::lexer::TokenKind, Arc<str>, MacroOrigin),
    Group(MacroDelimiter, Vec<MacroOutputNode>, MacroOrigin),
    Splice(SurfaceName),
}

pub(crate) const MAX_ORIGIN_SPANS: usize = 65_536;

/// Ordered causal inputs retained by the invocation-owned syntax interface.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum MacroOrigin {
    Source(Span),
    Combined {
        inputs: Arc<[MacroOrigin]>,
        invocation: Span,
        definition: Span,
        span_count: usize,
        depth: usize,
    },
}

impl MacroOrigin {
    pub(crate) fn combined(inputs: Vec<Self>, invocation: Span, definition: Span) -> Option<Self> {
        let mut span_count = 2usize;
        let mut depth = 0usize;
        for input in &inputs {
            span_count = span_count.checked_add(input.span_count())?;
            depth = depth.max(input.depth().checked_add(1)?);
        }
        if inputs.is_empty()
            || span_count > MAX_ORIGIN_SPANS
            || depth > crate::parser::STRUCTURAL_DEPTH_LIMIT
        {
            return None;
        }
        Some(Self::Combined {
            inputs: inputs.into(),
            invocation,
            definition,
            span_count,
            depth,
        })
    }

    pub(crate) fn span_count(&self) -> usize {
        match self {
            Self::Source(_) => 1,
            Self::Combined { span_count, .. } => *span_count,
        }
    }

    fn depth(&self) -> usize {
        match self {
            Self::Source(_) => 0,
            Self::Combined { depth, .. } => *depth,
        }
    }

    pub(crate) fn primary(&self) -> Span {
        let mut origin = self;
        loop {
            match origin {
                Self::Source(span) => return *span,
                Self::Combined { inputs, .. } => origin = &inputs[0],
            }
        }
    }

    pub(crate) fn spans(&self) -> Vec<Span> {
        enum Pending<'a> {
            Origin(&'a MacroOrigin),
            Span(Span),
        }
        let mut spans = Vec::new();
        let mut pending = vec![Pending::Origin(self)];
        while let Some(item) = pending.pop() {
            match item {
                Pending::Span(span) => spans.push(span),
                Pending::Origin(MacroOrigin::Source(span)) => spans.push(*span),
                Pending::Origin(MacroOrigin::Combined {
                    inputs,
                    invocation,
                    definition,
                    ..
                }) => {
                    pending.push(Pending::Span(*definition));
                    pending.push(Pending::Span(*invocation));
                    pending.extend(inputs.iter().rev().map(Pending::Origin));
                }
            }
        }
        spans
    }
}

pub(crate) enum TransformerOutput {
    Expanded(Vec<MacroOutputNode>),
    Rejected(crate::driver::SyntaxExpansionFailure),
    SyntaxRejected(crate::driver::SyntaxParseFailure),
}

impl From<Span> for MacroOrigin {
    fn from(span: Span) -> Self {
        Self::Source(span)
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum MacroDelimiter {
    Parentheses,
    Braces,
}

#[derive(Clone, Debug)]
pub(crate) struct SelectedSyntax {
    pub(crate) name: String,
    pub(crate) declaration: SurfaceSyntaxDeclaration,
    pub(crate) owner: usize,
    pub(crate) import_span: Span,
}

/// The existing syntax imports visible from each issued introduction.
#[derive(Clone, Debug)]
pub(crate) struct SyntaxContexts {
    caller: Vec<SelectedSyntax>,
    owner_imports: Vec<Vec<SelectedSyntax>>,
    owners: Vec<Option<usize>>,
}

impl SyntaxContexts {
    pub(crate) fn new(
        caller: &[SelectedSyntax],
        owner_imports: &[Vec<SelectedSyntax>],
        owners: &[Option<usize>],
    ) -> Self {
        Self {
            caller: caller.to_vec(),
            owner_imports: owner_imports.to_vec(),
            owners: owners.to_vec(),
        }
    }

    pub(crate) fn select(&self, name: &SurfaceName) -> Option<&SelectedSyntax> {
        let imports = if name.introduction == 0 {
            &self.caller
        } else {
            let owner = self.owners.get(name.introduction - 1)?.as_ref()?;
            self.owner_imports.get(*owner)?
        };
        imports.iter().find(|syntax| syntax.name == name.text)
    }
}

/// A literal name and the checked syntax selection that introduced it.
pub(crate) struct SyntaxNameUse {
    pub(crate) name: SurfaceName,
    pub(crate) owner: usize,
    pub(crate) declaration: Span,
    pub(crate) import_span: Span,
}

/// Local checked term facts available only to an owner's selected syntax.
pub(crate) struct SyntaxOwnerBindings {
    pub(crate) module: ModuleId,
    terms: HashMap<String, ExportedGlobal>,
    constructors: HashMap<String, ExportedConstructor>,
}

impl SyntaxOwnerBindings {
    pub(crate) fn new(owner: &CheckedModule, work: &mut TypeWorkBudget) -> Result<Self, ()> {
        let mut terms = HashMap::new();
        for checked in owner.schemes() {
            let existing = owner
                .exports()
                .terms()
                .find(|(_, exported)| exported.binder == checked.binder)
                .and_then(|(_, exported)| exported.publication.as_ref());
            let publication = if let Some(existing) = existing {
                Arc::clone(existing)
            } else {
                Arc::new(CheckedGlobalScheme {
                    binder: checked.binder,
                    spelling: checked.spelling.clone(),
                    scheme: checked.scheme.clone_with_budget(work)?,
                    capture: checked.capture.clone_with_budget(work)?,
                    origin: checked.origin.clone(),
                })
            };
            let fact = ExportedGlobal {
                publication: Some(publication),
                binder: checked.binder,
                scheme: checked.scheme.clone_with_budget(work)?,
                capture: checked.capture.clone_with_budget(work)?,
                origin: checked.origin.clone(),
            };
            if terms.insert(checked.spelling.clone(), fact).is_some() {
                return Err(());
            }
        }
        let mut constructors = HashMap::new();
        for fact in owner.syntax_constructor_facts(work)? {
            if constructors.insert(fact.spelling.clone(), fact).is_some() {
                return Err(());
            }
        }
        Ok(Self {
            module: owner.module(),
            terms,
            constructors,
        })
    }

    pub(crate) fn empty(module: ModuleId) -> Self {
        Self {
            module,
            terms: HashMap::new(),
            constructors: HashMap::new(),
        }
    }

    pub(crate) fn get(&self, spelling: &str) -> Option<&ExportedGlobal> {
        self.terms.get(spelling)
    }

    pub(crate) fn constructor(&self, spelling: &str) -> Option<&ExportedConstructor> {
        self.constructors.get(spelling)
    }

    pub(crate) fn constructor_by_id(
        &self,
        id: crate::types::ConstructorId,
    ) -> Option<&ExportedConstructor> {
        self.constructors
            .values()
            .find(|constructor| constructor.id == id)
    }
}

impl Drop for SyntaxOwnerBindings {
    fn drop(&mut self) {
        for (_, fact) in self.terms.drain() {
            drop(fact.scheme);
            crate::source::discard_origin_iteratively(fact.origin);
        }
        for (_, fact) in self.constructors.drain() {
            fact.discard_iteratively();
        }
    }
}

/// Admit each procedural target from the completed defining module without
/// linking or executing the transformer.
pub(crate) fn validate_transformers(
    owner: &CheckedModule,
    checked: &[Arc<CheckedModule>],
    declarations: &[SurfaceSyntaxDeclaration],
) -> Result<(), Span> {
    for declaration in declarations {
        let SurfaceSyntaxImplementation::Transformer(name) = &declaration.implementation else {
            continue;
        };
        let scheme = owner
            .schemes()
            .iter()
            .find(|scheme| scheme.spelling == name.text)
            .ok_or(name.span)?;
        let syntax = checked
            .iter()
            .find(|module| module.module().is_builtin_compiler_syntax())
            .ok_or(name.span)?;
        let registry = syntax.registry();
        let input = registry
            .nominals()
            .iter()
            .find(|nominal| nominal.id.module() == syntax.module() && nominal.spelling == "Input")
            .ok_or(name.span)?
            .id;
        let output = registry
            .nominals()
            .iter()
            .find(|nominal| {
                nominal.id.module() == syntax.module() && nominal.spelling == "MacroResult"
            })
            .ok_or(name.span)?
            .id;
        let ops = registry
            .effects()
            .iter()
            .find(|effect| effect.id.module() == syntax.module() && effect.spelling == "Ops")
            .ok_or(name.span)?
            .id;
        if scheme.binder.module() != Some(owner.module())
            || !scheme.scheme.type_parameters.is_empty()
            || !scheme.scheme.requirements.is_empty()
        {
            return Err(name.span);
        }
        let (domain, result, row) = match &scheme.scheme.value_type {
            crate::types::Type::Function(domain, result) => {
                (domain.as_ref(), result.as_ref(), None)
            }
            crate::types::Type::EffectfulFunction(domain, result) => {
                (domain.as_ref(), result.value(), Some(result.effects()))
            }
            _ => return Err(name.span),
        };
        if domain != &crate::types::Type::Nominal(input)
            || result != &crate::types::Type::Nominal(output)
            || row.is_some_and(|row| {
                row.tail().is_some()
                    || row.known().iter().any(|instance| {
                        !instance.arguments().is_empty()
                            || (instance.effect() != ops
                                && !crate::resolved::RegionApi::for_module(
                                    instance.effect().module(),
                                )
                                .is_some_and(|api| api.default_alloc() == instance.effect()))
                    })
            })
        {
            return Err(name.span);
        }
    }
    Ok(())
}

/// Reject forms that still need definition-site binding and authority.
pub(crate) fn validate_template(declaration: &SurfaceSyntaxDeclaration) -> Result<(), Span> {
    fn check_annotation(annotation: &SurfaceType) -> Result<(), Span> {
        match &annotation.kind {
            SurfaceTypeKind::Int
            | SurfaceTypeKind::Bytes
            | SurfaceTypeKind::String
            | SurfaceTypeKind::Bool
            | SurfaceTypeKind::Unit => Ok(()),
            SurfaceTypeKind::Tuple(elements) => {
                for element in elements {
                    check_annotation(element)?;
                }
                Ok(())
            }
            SurfaceTypeKind::Function(function) if function.effects.is_none() => {
                check_annotation(&function.domain)?;
                check_annotation(&function.codomain)
            }
            _ => Err(annotation.span),
        }
    }

    fn check_pattern(
        pattern: &SurfacePattern,
        matcher: &[SurfaceSyntaxMatcherPart],
    ) -> Result<(), Span> {
        match &pattern.kind {
            SurfacePatternKind::TemplateSplice(name) => {
                if matcher.iter().any(|part| {
                    matches!(part, SurfaceSyntaxMatcherPart::Capture {
                    name: capture, kind: SurfaceSyntaxCaptureKind::Identifier,
                } if capture.text == name.text)
                }) {
                    Ok(())
                } else {
                    Err(name.span)
                }
            }
            SurfacePatternKind::Binder(_)
            | SurfacePatternKind::Boolean(_)
            | SurfacePatternKind::Wildcard
            | SurfacePatternKind::Unit => Ok(()),
            SurfacePatternKind::Tuple(elements) => {
                for element in elements {
                    check_pattern(element, matcher)?;
                }
                Ok(())
            }
            SurfacePatternKind::Constructor {
                name: SurfaceReference::Unqualified(_),
                payload,
            } => {
                if let Some(payload) = payload {
                    check_pattern(payload, matcher)?;
                }
                Ok(())
            }
            _ => Err(pattern.span),
        }
    }
    fn check_block(block: &SurfaceBlock, matcher: &[SurfaceSyntaxMatcherPart]) -> Result<(), Span> {
        for declaration in &block.declarations {
            let SurfaceLocalDeclaration::Binding(binding) = declaration else {
                return Err(block.span);
            };
            check_pattern(&binding.pattern, matcher)?;
            if let Some(annotation) = &binding.annotation {
                check_annotation(annotation)?;
            }
            check(&binding.initializer, matcher)?;
        }
        check(&block.result, matcher)
    }
    fn check(expression: &SurfaceExpr, matcher: &[SurfaceSyntaxMatcherPart]) -> Result<(), Span> {
        match &expression.kind {
            SurfaceExprKind::SyntaxInvocation { captures, .. } => {
                for capture in captures {
                    if let SurfaceSyntaxCapture::Expression(expression) = capture {
                        check(&expression.expression, matcher)?;
                    }
                }
                Ok(())
            }
            SurfaceExprKind::TemplateSplice(name)
                if matcher.iter().any(|part| matches!(part, SurfaceSyntaxMatcherPart::Capture { name: capture, .. } if capture.text == name.text)) => Ok(()),
            SurfaceExprKind::Integer(_)
            | SurfaceExprKind::String(_)
            | SurfaceExprKind::Boolean(_)
            | SurfaceExprKind::Name(SurfaceReference::Unqualified(_))
            | SurfaceExprKind::Unit => Ok(()),
            SurfaceExprKind::Tuple(elements) => {
                for element in elements { check(element, matcher)?; }
                Ok(())
            }
            SurfaceExprKind::Apply(application) => {
                check(&application.function, matcher)?;
                check(&application.argument, matcher)
            }
            SurfaceExprKind::Multiply(binary)
            | SurfaceExprKind::Add(binary)
            | SurfaceExprKind::Equal(binary) => {
                check(&binary.left, matcher)?;
                check(&binary.right, matcher)
            }
            SurfaceExprKind::Block(block) => check_block(block, matcher),
            SurfaceExprKind::Function(function) => {
                check_pattern(&function.parameter, matcher)?;
                check_block(&function.body, matcher)
            }
            SurfaceExprKind::Match(matching) => {
                check(&matching.scrutinee, matcher)?;
                for arm in &matching.arms {
                    check_pattern(&arm.pattern, matcher)?;
                    check(&arm.body, matcher)?;
                }
                Ok(())
            }
            _ => Err(expression.span),
        }
    }
    match &declaration.implementation {
        SurfaceSyntaxImplementation::Template(template) => check(template, &declaration.matcher),
        SurfaceSyntaxImplementation::Transformer(_) => Ok(()),
    }
}

fn capture_by_name<'a>(
    name: &SurfaceName,
    matcher: &[SurfaceSyntaxMatcherPart],
    captures: &'a [SurfaceSyntaxCapture],
) -> Result<&'a SurfaceSyntaxCapture, Span> {
    let index = matcher
        .iter()
        .filter_map(|part| match part {
            SurfaceSyntaxMatcherPart::Capture { name, .. } => Some(name),
            SurfaceSyntaxMatcherPart::Literal { .. } => None,
        })
        .position(|capture| capture.text == name.text)
        .ok_or(name.span)?;
    captures.get(index).ok_or(name.span)
}

fn substitute_pattern(
    pattern: &mut SurfacePattern,
    matcher: &[SurfaceSyntaxMatcherPart],
    captures: &[SurfaceSyntaxCapture],
    introduction: usize,
    invocation: Span,
) -> Result<(), Span> {
    match &mut pattern.kind {
        SurfacePatternKind::TemplateSplice(name) => {
            let SurfaceSyntaxCapture::Identifier(capture) =
                capture_by_name(name, matcher, captures)?
            else {
                return Err(name.span);
            };
            if !capture
                .text
                .as_bytes()
                .first()
                .is_some_and(|byte| byte.is_ascii_lowercase() || *byte == b'_')
            {
                return Err(capture.span);
            }
            *pattern = SurfacePattern {
                kind: SurfacePatternKind::Binder(SurfaceBinder {
                    name: capture.clone(),
                    span: capture.span,
                }),
                span: capture.span,
            };
        }
        SurfacePatternKind::Binder(binder) => {
            binder.name.introduction = introduction;
            binder.name.introduced_at = Some(invocation);
        }
        SurfacePatternKind::Tuple(elements) => {
            for element in elements {
                substitute_pattern(element, matcher, captures, introduction, invocation)?;
            }
        }
        SurfacePatternKind::Constructor {
            name: SurfaceReference::Unqualified(name),
            payload,
        } => {
            name.introduction = introduction;
            name.introduced_at = Some(invocation);
            if let Some(payload) = payload {
                substitute_pattern(payload, matcher, captures, introduction, invocation)?;
            }
        }
        SurfacePatternKind::Boolean(_)
        | SurfacePatternKind::Wildcard
        | SurfacePatternKind::Unit => {}
        _ => return Err(pattern.span),
    }
    Ok(())
}

fn collect_pattern_names(pattern: &SurfacePattern, names: &mut Vec<SurfaceName>) {
    match &pattern.kind {
        SurfacePatternKind::Tuple(elements) => {
            for element in elements {
                collect_pattern_names(element, names);
            }
        }
        SurfacePatternKind::Constructor { name, payload } => {
            if name.member().introduction != 0 {
                names.push(name.member().clone());
            }
            if let Some(payload) = payload {
                collect_pattern_names(payload, names);
            }
        }
        _ => {}
    }
}

pub(crate) fn admit_transformer_output(
    source: &crate::source::SourceFile,
    invocation: Span,
    output: Vec<MacroOutputNode>,
    contexts: &SyntaxContexts,
) -> Result<SurfaceExpr, crate::parser::MacroParseFailure> {
    let (mut expression, matcher, captures) =
        crate::parser::parse_macro_expression(source, invocation, output, contexts)?;
    substitute(&mut expression, &matcher, &captures, 0, invocation)
        .map_err(|_| crate::parser::MacroParseFailure::Invalid)?;
    expression.span = invocation;
    Ok(expression)
}

fn substitute_capture(
    capture: &mut SurfaceExpressionCapture,
    matcher: &[SurfaceSyntaxMatcherPart],
    captures: &[SurfaceSyntaxCapture],
    introduction: usize,
    invocation: Span,
) -> Result<(), Span> {
    if let SurfaceExprKind::TemplateSplice(name) = &capture.expression.kind
        && matches!(capture.contents.as_ref(), [MacroOutputNode::Splice(splice)] if splice.text == name.text)
        && let SurfaceSyntaxCapture::Expression(original) =
            capture_by_name(name, matcher, captures)?
    {
        *capture = original.clone();
        return Ok(());
    }
    substitute(
        &mut capture.expression,
        matcher,
        captures,
        introduction,
        invocation,
    )?;
    let mut contents = capture.contents.to_vec();
    substitute_contents(&mut contents, matcher, captures, introduction, invocation)?;
    capture.contents = contents.into();
    Ok(())
}

fn substitute_contents(
    contents: &mut Vec<MacroOutputNode>,
    matcher: &[SurfaceSyntaxMatcherPart],
    captures: &[SurfaceSyntaxCapture],
    introduction: usize,
    invocation: Span,
) -> Result<(), Span> {
    for node in contents {
        match node {
            MacroOutputNode::Splice(name) => {
                *node = match capture_by_name(name, matcher, captures)? {
                    SurfaceSyntaxCapture::Expression(capture) => {
                        MacroOutputNode::Expression(capture.clone(), invocation.into())
                    }
                    SurfaceSyntaxCapture::Identifier(name) => {
                        MacroOutputNode::Identifier(name.clone(), name.span.into())
                    }
                };
            }
            MacroOutputNode::Identifier(name, _) => {
                if introduction != 0 {
                    name.introduction = introduction;
                    name.introduced_at = Some(invocation);
                }
            }
            MacroOutputNode::Group(_, children, _) => {
                substitute_contents(children, matcher, captures, introduction, invocation)?;
            }
            MacroOutputNode::Token(_, _, _) | MacroOutputNode::Expression(_, _) => {}
        }
    }
    Ok(())
}

fn substitute_block(
    block: &mut SurfaceBlock,
    matcher: &[SurfaceSyntaxMatcherPart],
    captures: &[SurfaceSyntaxCapture],
    introduction: usize,
    invocation: Span,
) -> Result<(), Span> {
    for declaration in &mut block.declarations {
        let SurfaceLocalDeclaration::Binding(binding) = declaration else {
            return Err(block.span);
        };
        binding.expansion = Some(invocation);
        substitute_pattern(
            &mut binding.pattern,
            matcher,
            captures,
            introduction,
            invocation,
        )?;
        substitute(
            &mut binding.initializer,
            matcher,
            captures,
            introduction,
            invocation,
        )?;
    }
    substitute(
        &mut block.result,
        matcher,
        captures,
        introduction,
        invocation,
    )
}

fn substitute(
    expression: &mut SurfaceExpr,
    matcher: &[SurfaceSyntaxMatcherPart],
    captures: &[SurfaceSyntaxCapture],
    introduction: usize,
    invocation: Span,
) -> Result<(), Span> {
    match &mut expression.kind {
        SurfaceExprKind::SyntaxInvocation {
            name,
            captures: nested,
        } => {
            if introduction != 0 {
                name.introduction = introduction;
                name.introduced_at = Some(invocation);
            }
            for capture in nested {
                if let SurfaceSyntaxCapture::Expression(expression) = capture {
                    substitute_capture(expression, matcher, captures, introduction, invocation)?;
                }
            }
        }
        SurfaceExprKind::TemplateSplice(name) => {
            *expression = match capture_by_name(name, matcher, captures)? {
                SurfaceSyntaxCapture::Expression(capture) => capture.expression.clone(),
                SurfaceSyntaxCapture::Identifier(capture) => SurfaceExpr {
                    kind: SurfaceExprKind::Name(SurfaceReference::Unqualified(capture.clone())),
                    span: capture.span,
                },
            };
        }
        SurfaceExprKind::Tuple(elements) => {
            for element in elements {
                substitute(element, matcher, captures, introduction, invocation)?;
            }
        }
        SurfaceExprKind::Apply(application) => {
            application.expansion = Some(invocation);
            substitute(
                &mut application.function,
                matcher,
                captures,
                introduction,
                invocation,
            )?;
            substitute(
                &mut application.argument,
                matcher,
                captures,
                introduction,
                invocation,
            )?;
        }
        SurfaceExprKind::Multiply(binary)
        | SurfaceExprKind::Add(binary)
        | SurfaceExprKind::Equal(binary) => {
            substitute(
                &mut binary.left,
                matcher,
                captures,
                introduction,
                invocation,
            )?;
            substitute(
                &mut binary.right,
                matcher,
                captures,
                introduction,
                invocation,
            )?;
        }
        SurfaceExprKind::Block(block) => {
            substitute_block(block, matcher, captures, introduction, invocation)?;
        }
        SurfaceExprKind::Function(function) => {
            if introduction != 0 {
                function.expansion = Some(invocation);
            }
            substitute_pattern(
                &mut function.parameter,
                matcher,
                captures,
                introduction,
                invocation,
            )?;
            substitute_block(
                &mut function.body,
                matcher,
                captures,
                introduction,
                invocation,
            )?;
        }
        SurfaceExprKind::Match(matching) => {
            substitute(
                &mut matching.scrutinee,
                matcher,
                captures,
                introduction,
                invocation,
            )?;
            for arm in &mut matching.arms {
                substitute_pattern(
                    &mut arm.pattern,
                    matcher,
                    captures,
                    introduction,
                    invocation,
                )?;
                substitute(&mut arm.body, matcher, captures, introduction, invocation)?;
            }
        }
        SurfaceExprKind::Name(SurfaceReference::Unqualified(name)) => {
            if introduction != 0 {
                name.introduction = introduction;
                name.introduced_at = Some(invocation);
            }
        }
        SurfaceExprKind::Name(SurfaceReference::Qualified(name))
            if introduction == 0
                && name.qualifier.introduction == 0
                && name.member.introduction == 0 => {}
        SurfaceExprKind::Integer(_)
        | SurfaceExprKind::String(_)
        | SurfaceExprKind::Boolean(_)
        | SurfaceExprKind::Unit => {}
        _ => return Err(expression.span),
    }
    Ok(())
}

pub(crate) fn expand_module(
    module: &mut SurfaceModule,
    selected: &[SelectedSyntax],
    owner_imports: &[Vec<SelectedSyntax>],
    transformer: &mut dyn FnMut(
        &SelectedSyntax,
        &[SurfaceSyntaxCapture],
        Span,
        &SurfaceName,
        usize,
        &[Option<usize>],
    ) -> Result<(SurfaceExpr, usize), Span>,
) -> Result<Vec<SyntaxNameUse>, Span> {
    let mut next_introduction = ExpansionContexts {
        owner_imports,
        transformer,
        owners: Vec::new(),
        names: Vec::new(),
    };
    for definition in &mut module.definitions {
        match &mut definition.kind {
            SurfaceDefinitionKind::Equational(global) => {
                for equation in &mut global.equations {
                    expand_expression(&mut equation.body, selected, &mut next_introduction)?;
                }
            }
            SurfaceDefinitionKind::InlineOperational(global) => {
                expand_block(&mut global.body, selected, &mut next_introduction)?;
            }
        }
    }
    for implementation in &mut module.implementations {
        for equation in &mut implementation.equations {
            expand_expression(&mut equation.body, selected, &mut next_introduction)?;
        }
    }
    for resource in &mut module.resources {
        expand_expression(&mut resource.acquire, selected, &mut next_introduction)?;
        expand_expression(&mut resource.finish, selected, &mut next_introduction)?;
        for clause in &mut resource.handlers {
            expand_expression(&mut clause.body, selected, &mut next_introduction)?;
        }
        if let Some(family) = &mut resource.family {
            for clause in &mut family.handlers {
                expand_expression(&mut clause.body, selected, &mut next_introduction)?;
            }
        }
    }
    let mut uses = Vec::new();
    for name in next_introduction.names {
        let owner = next_introduction
            .owners
            .get(name.introduction - 1)
            .ok_or(name.span)?;
        if let Some(owner_index) = owner.owner {
            uses.push(SyntaxNameUse {
                name,
                owner: owner_index,
                declaration: owner.declaration,
                import_span: owner.import_span,
            });
        }
    }
    Ok(uses)
}

struct ExpansionContexts<'a> {
    owner_imports: &'a [Vec<SelectedSyntax>],
    transformer: &'a mut dyn FnMut(
        &SelectedSyntax,
        &[SurfaceSyntaxCapture],
        Span,
        &SurfaceName,
        usize,
        &[Option<usize>],
    ) -> Result<(SurfaceExpr, usize), Span>,
    owners: Vec<SyntaxOwner>,
    names: Vec<SurfaceName>,
}

struct SyntaxOwner {
    owner: Option<usize>,
    declaration: Span,
    import_span: Span,
}

fn expand_block(
    block: &mut SurfaceBlock,
    selected: &[SelectedSyntax],
    next_introduction: &mut ExpansionContexts<'_>,
) -> Result<(), Span> {
    for declaration in &mut block.declarations {
        match declaration {
            SurfaceLocalDeclaration::Evidence(evidence) => {
                for equation in &mut evidence.equations {
                    expand_expression(&mut equation.body, selected, next_introduction)?;
                }
            }
            SurfaceLocalDeclaration::Binding(binding) => {
                collect_pattern_names(&binding.pattern, &mut next_introduction.names);
                expand_expression(&mut binding.initializer, selected, next_introduction)?;
            }
            SurfaceLocalDeclaration::Recursive(group) => {
                for member in &mut group.members {
                    expand_expression(&mut member.initializer, selected, next_introduction)?;
                }
            }
            SurfaceLocalDeclaration::Newtype(_) => {}
        }
    }
    expand_expression(&mut block.result, selected, next_introduction)
}

fn expand_expression(
    expression: &mut SurfaceExpr,
    selected: &[SelectedSyntax],
    next_introduction: &mut ExpansionContexts<'_>,
) -> Result<(), Span> {
    match &mut expression.kind {
        SurfaceExprKind::SyntaxInvocation { name, captures } => {
            let invocation = expression.span;
            let expansion_anchor = name.introduced_at.unwrap_or(invocation);
            let syntax = if name.introduction == 0 {
                selected
            } else {
                let owner = next_introduction
                    .owners
                    .get(name.introduction - 1)
                    .ok_or(invocation)?;
                next_introduction
                    .owner_imports
                    .get(owner.owner.ok_or(invocation)?)
                    .ok_or(invocation)?
            };
            let declaration = syntax
                .iter()
                .find(|syntax| syntax.name == name.text)
                .cloned()
                .ok_or(expression.span)?;
            let template = match &declaration.declaration.implementation {
                SurfaceSyntaxImplementation::Template(template) => template,
                SurfaceSyntaxImplementation::Transformer(_) => {
                    next_introduction.owners.push(SyntaxOwner {
                        owner: Some(declaration.owner),
                        declaration: declaration.declaration.span,
                        import_span: declaration.import_span,
                    });
                    let introduction = next_introduction.owners.len();
                    let owners = next_introduction
                        .owners
                        .iter()
                        .map(|owner| owner.owner)
                        .collect::<Vec<_>>();
                    let (replacement, fresh_count) = (next_introduction.transformer)(
                        &declaration,
                        captures,
                        expansion_anchor,
                        name,
                        introduction,
                        &owners,
                    )?;
                    for _ in 0..fresh_count {
                        next_introduction.owners.push(SyntaxOwner {
                            owner: None,
                            declaration: declaration.declaration.span,
                            import_span: declaration.import_span,
                        });
                    }
                    *expression = replacement;
                    return expand_expression(expression, selected, next_introduction);
                }
            };
            let mut replacement = template.clone();
            next_introduction.owners.push(SyntaxOwner {
                owner: Some(declaration.owner),
                declaration: declaration.declaration.span,
                import_span: declaration.import_span,
            });
            let introduction = next_introduction.owners.len();
            substitute(
                &mut replacement,
                &declaration.declaration.matcher,
                captures,
                introduction,
                expansion_anchor,
            )?;
            // The complete expansion occupies the invocation in the caller.
            // Its children keep their own capture and template source spans.
            replacement.span = invocation;
            if let SurfaceExprKind::Block(block) = &mut replacement.kind {
                block.span = invocation;
            }
            *expression = replacement;
            return expand_expression(expression, selected, next_introduction);
        }
        SurfaceExprKind::TemplateSplice(_) => return Err(expression.span),
        SurfaceExprKind::Integer(_)
        | SurfaceExprKind::String(_)
        | SurfaceExprKind::Boolean(_)
        | SurfaceExprKind::Unit
        | SurfaceExprKind::Discard
        | SurfaceExprKind::Retain => {}
        SurfaceExprKind::Name(SurfaceReference::Unqualified(name)) if name.introduction != 0 => {
            next_introduction.names.push(name.clone());
        }
        SurfaceExprKind::Name(_) => {}
        SurfaceExprKind::Tuple(elements) => {
            for element in elements {
                expand_expression(element, selected, next_introduction)?;
            }
        }
        SurfaceExprKind::Apply(application) => {
            expand_expression(&mut application.function, selected, next_introduction)?;
            expand_expression(&mut application.argument, selected, next_introduction)?;
        }
        SurfaceExprKind::Multiply(binary)
        | SurfaceExprKind::Add(binary)
        | SurfaceExprKind::Equal(binary) => {
            expand_expression(&mut binary.left, selected, next_introduction)?;
            expand_expression(&mut binary.right, selected, next_introduction)?;
        }
        SurfaceExprKind::Block(block) => expand_block(block, selected, next_introduction)?,
        SurfaceExprKind::Function(function) => {
            expand_block(&mut function.body, selected, next_introduction)?
        }
        SurfaceExprKind::Match(matching) => {
            expand_expression(&mut matching.scrutinee, selected, next_introduction)?;
            for arm in &mut matching.arms {
                collect_pattern_names(&arm.pattern, &mut next_introduction.names);
                expand_expression(&mut arm.body, selected, next_introduction)?;
            }
        }
        SurfaceExprKind::Perform(perform) => {
            expand_expression(&mut perform.operand, selected, next_introduction)?
        }
        SurfaceExprKind::Handle(handler) => {
            expand_expression(&mut handler.body, selected, next_introduction)?;
            if let Some(store) = &mut handler.store {
                expand_expression(store, selected, next_introduction)?;
            }
            for clause in &mut handler.clauses {
                expand_expression(&mut clause.body, selected, next_introduction)?;
            }
        }
        SurfaceExprKind::Resume(value) => expand_expression(value, selected, next_introduction)?,
        SurfaceExprKind::Resource(resource) => {
            expand_expression(&mut resource.initializer, selected, next_introduction)?;
            expand_block(&mut resource.body, selected, next_introduction)?;
        }
        SurfaceExprKind::Region(region) => {
            if let Some(provider) = &mut region.provider {
                expand_expression(provider, selected, next_introduction)?;
            }
            expand_block(&mut region.body, selected, next_introduction)?;
        }
        SurfaceExprKind::RegionSelection(selection) => {
            expand_expression(&mut selection.region, selected, next_introduction)?;
            expand_block(&mut selection.body, selected, next_introduction)?;
        }
        SurfaceExprKind::ProviderResource(resource) => {
            expand_expression(&mut resource.initializer, selected, next_introduction)?;
            expand_block(&mut resource.body, selected, next_introduction)?;
        }
        SurfaceExprKind::Hook(hook) => expand_block(&mut hook.body, selected, next_introduction)?,
        SurfaceExprKind::Registration(registration) => {
            expand_expression(&mut registration.transformer, selected, next_introduction)?;
            expand_block(&mut registration.body, selected, next_introduction)?;
        }
        SurfaceExprKind::Cleanup(cleanup) => {
            expand_expression(&mut cleanup.action, selected, next_introduction)?;
            expand_block(&mut cleanup.body, selected, next_introduction)?;
        }
    }
    Ok(())
}
