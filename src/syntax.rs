//! Structured syntax instantiation for the ordinary resolver.

use std::{collections::HashMap, sync::Arc};

use crate::{
    module::{LoadedModule, ModuleId},
    resolved::{
        CheckedGlobalScheme, CheckedModule, DirectDependencyRoute, ExportedConstructor,
        ExportedGlobal,
    },
    source::Span,
    surface::{
        SurfaceExpr, SurfaceExprKind, SurfaceExpressionCapture, SurfaceIdentifierCapture,
        SurfaceImportItem, SurfaceImportSelection, SurfaceName, SurfaceSyntaxCapture,
        SurfaceSyntaxCaptureKind, SurfaceSyntaxDeclaration, SurfaceSyntaxImplementation,
        SurfaceSyntaxMatcherPart,
    },
    types::TypeWorkBudget,
};

/// Structured output transferred from one completed transformer invocation.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum MacroOutputNode {
    Expression(SurfaceExpressionCapture, MacroOrigin),
    ForwardedExpression(SurfaceExpressionCapture, MacroOrigin),
    Identifier(SurfaceName, MacroOrigin),
    Token(crate::lexer::TokenKind, Arc<str>, MacroOrigin),
    Group(MacroDelimiter, Vec<MacroOutputNode>, MacroOrigin),
    Splice(SurfaceName),
}

pub(crate) const MAX_ORIGIN_SPANS: usize = 65_536;

/// One actual expansion, shared by its output occurrences.
#[derive(Debug, Eq, PartialEq)]
pub(crate) struct ExpansionFrame {
    pub(crate) invocation: Span,
    pub(crate) definition: Span,
}

/// Diagnostic causes and the enclosing expansion occurrences for one expression.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct DiagnosticLocation {
    pub(crate) primary: MacroOrigin,
    pub(crate) related: Vec<MacroOrigin>,
    pub(crate) frames: Vec<Arc<ExpansionFrame>>,
    pub(crate) token_cause: bool,
    pub(crate) captured_expression: bool,
}

impl DiagnosticLocation {
    pub(crate) fn new(primary: MacroOrigin) -> Self {
        Self {
            primary,
            related: Vec::new(),
            frames: Vec::new(),
            token_cause: false,
            captured_expression: false,
        }
    }

    pub(crate) fn add_frame(&mut self, frame: &Arc<ExpansionFrame>) {
        if !self
            .frames
            .iter()
            .any(|existing| Arc::ptr_eq(existing, frame))
        {
            self.frames.push(Arc::clone(frame));
        }
    }

    pub(crate) fn add_cause(&mut self, cause: &Self) {
        self.related.push(cause.primary.clone());
        self.related.extend(cause.related.iter().cloned());
        for frame in &cause.frames {
            self.add_frame(frame);
        }
    }
}

/// Ordered causal inputs retained by the invocation-owned syntax interface.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum MacroOrigin {
    Source(Span),
    Combined {
        inputs: Arc<[MacroOrigin]>,
        frame: Arc<ExpansionFrame>,
        span_count: usize,
        depth: usize,
    },
}

pub(crate) enum MacroOriginPart {
    Source(Span),
    Frame(Arc<ExpansionFrame>),
}

impl MacroOrigin {
    pub(crate) fn combined(inputs: Vec<Self>, frame: Arc<ExpansionFrame>) -> Option<Self> {
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
            frame,
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
        let mut spans = Vec::new();
        for part in self.parts() {
            match part {
                MacroOriginPart::Source(span) => spans.push(span),
                MacroOriginPart::Frame(frame) => {
                    spans.push(frame.invocation);
                    spans.push(frame.definition);
                }
            }
        }
        spans
    }

    pub(crate) fn parts(&self) -> Vec<MacroOriginPart> {
        enum Pending<'a> {
            Origin(&'a MacroOrigin),
            Frame(&'a Arc<ExpansionFrame>),
        }
        let mut parts = Vec::new();
        let mut pending = vec![Pending::Origin(self)];
        while let Some(item) = pending.pop() {
            match item {
                Pending::Frame(frame) => parts.push(MacroOriginPart::Frame(Arc::clone(frame))),
                Pending::Origin(MacroOrigin::Source(span)) => {
                    parts.push(MacroOriginPart::Source(*span))
                }
                Pending::Origin(MacroOrigin::Combined { inputs, frame, .. }) => {
                    pending.push(Pending::Frame(frame));
                    pending.extend(inputs.iter().rev().map(Pending::Origin));
                }
            }
        }
        parts
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

#[derive(Clone, Copy, Eq, PartialEq)]
pub(crate) enum SyntaxNameNamespace {
    Term,
    Type,
    Effect,
    Interface,
}

/// A literal name and the checked syntax selection that introduced it.
pub(crate) struct SyntaxNameUse {
    pub(crate) name: SurfaceName,
    pub(crate) qualifier: Option<SurfaceName>,
    pub(crate) namespace: SyntaxNameNamespace,
    pub(crate) owner: usize,
    pub(crate) declaration: Span,
    pub(crate) import_span: Span,
}

#[derive(Clone, Copy)]
pub(crate) struct SyntaxOwner {
    pub(crate) owner: Option<usize>,
    pub(crate) declaration: Span,
    pub(crate) import_span: Span,
}

type SyntaxTransformer<'a> = dyn FnMut(
        &SelectedSyntax,
        &[SurfaceSyntaxCapture],
        Span,
        &SurfaceName,
        usize,
        &[Option<usize>],
        &Arc<ExpansionFrame>,
        &mut crate::interface::InterfaceConstraintBudget,
    ) -> Result<(SurfaceExpr, usize), Span>
    + 'a;

/// Expands one invocation while the ordinary resolver owns its lexical scope.
pub(crate) struct SyntaxExpansion<'a> {
    source: &'a crate::source::SourceFile,
    selected: &'a [SelectedSyntax],
    owner_imports: &'a [Vec<SelectedSyntax>],
    owners: Vec<SyntaxOwner>,
    parse_failure: Option<crate::driver::SyntaxParseFailure>,
    transformer: &'a mut SyntaxTransformer<'a>,
}

impl<'a> SyntaxExpansion<'a> {
    pub(crate) fn new(
        source: &'a crate::source::SourceFile,
        selected: &'a [SelectedSyntax],
        owner_imports: &'a [Vec<SelectedSyntax>],
        transformer: &'a mut SyntaxTransformer<'a>,
    ) -> Self {
        Self {
            source,
            selected,
            owner_imports,
            owners: Vec::new(),
            parse_failure: None,
            transformer,
        }
    }

    pub(crate) fn take_parse_failure(&mut self) -> Option<crate::driver::SyntaxParseFailure> {
        self.parse_failure.take()
    }

    pub(crate) fn owner(&self, introduction: usize) -> Option<SyntaxOwner> {
        introduction
            .checked_sub(1)
            .and_then(|index| self.owners.get(index))
            .copied()
    }

    pub(crate) fn selected(&self, name: &SurfaceName) -> Option<&SelectedSyntax> {
        let imports = if name.introduction == 0 {
            self.selected
        } else {
            let owner = self.owner(name.introduction)?;
            self.owner_imports.get(owner.owner?)?
        };
        imports.iter().find(|syntax| syntax.name == name.text)
    }

    pub(crate) fn expand(
        &mut self,
        name: &SurfaceName,
        captures: &[SurfaceSyntaxCapture],
        invocation: Span,
        constraint_work: &mut crate::interface::InterfaceConstraintBudget,
    ) -> Result<SurfaceExpr, Span> {
        let anchor = name.introduced_at.unwrap_or(invocation);
        let selection = self.selected(name).cloned().ok_or(invocation)?;
        self.owners.push(SyntaxOwner {
            owner: Some(selection.owner),
            declaration: selection.declaration.span,
            import_span: selection.import_span,
        });
        let introduction = self.owners.len();
        let frame = Arc::new(ExpansionFrame {
            invocation: anchor,
            definition: selection.declaration.span,
        });
        let owners = self
            .owners
            .iter()
            .map(|owner| owner.owner)
            .collect::<Vec<_>>();
        let (mut expression, fresh_count) = match &selection.declaration.implementation {
            SurfaceSyntaxImplementation::Template => {
                let mut contents = selection
                    .declaration
                    .template_contents
                    .as_ref()
                    .ok_or(invocation)?
                    .to_vec();
                substitute_contents(
                    &mut contents,
                    &selection.declaration.matcher,
                    captures,
                    introduction,
                    anchor,
                )?;
                let contexts = SyntaxContexts::new(self.selected, self.owner_imports, &owners);
                let expression = match crate::parser::parse_macro_expression(
                    self.source,
                    anchor,
                    Some((selection.declaration.span, introduction)),
                    contents,
                    &contexts,
                    Some(&frame),
                ) {
                    Ok(expression) => expression,
                    Err(crate::parser::MacroParseFailure::Syntax {
                        diagnostics,
                        resource,
                    }) => {
                        self.parse_failure = Some(crate::driver::SyntaxParseFailure {
                            diagnostics,
                            resource,
                            invocation: anchor,
                            definition: selection.declaration.span,
                            teardown: None,
                        });
                        return Err(invocation);
                    }
                    Err(crate::parser::MacroParseFailure::Invalid) => return Err(invocation),
                };
                (expression, 0)
            }
            SurfaceSyntaxImplementation::Transformer(_) => (self.transformer)(
                &selection,
                captures,
                anchor,
                name,
                introduction,
                &owners,
                &frame,
                constraint_work,
            )?,
        };
        self.owners.extend((0..fresh_count).map(|_| SyntaxOwner {
            owner: None,
            declaration: selection.declaration.span,
            import_span: selection.import_span,
        }));
        expression.span = invocation;
        Ok(expression)
    }
}

/// Local checked term facts available only to an owner's selected syntax.
pub(crate) struct SyntaxOwnerBindings {
    pub(crate) module: ModuleId,
    terms: HashMap<String, ExportedGlobal>,
    constructors: HashMap<String, ExportedConstructor>,
    qualified: HashMap<String, DirectDependencyRoute>,
    targeted: HashMap<String, (DirectDependencyRoute, String, Span)>,
    targeted_nominals: HashMap<String, (DirectDependencyRoute, String, Span)>,
    targeted_interfaces: HashMap<String, (DirectDependencyRoute, String, Span)>,
    targeted_effects: HashMap<String, (DirectDependencyRoute, String, Span)>,
}

impl SyntaxOwnerBindings {
    pub(crate) fn new(
        owner: &CheckedModule,
        loaded: &LoadedModule,
        graph: &[Arc<CheckedModule>],
        work: &mut TypeWorkBudget,
    ) -> Result<Self, ()> {
        if owner.module() != loaded.id() || owner.span().source() != loaded.source().id() {
            return Err(());
        }
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
        let mut qualified = HashMap::new();
        let mut targeted = HashMap::new();
        let mut targeted_nominals = HashMap::new();
        let mut targeted_interfaces = HashMap::new();
        let mut targeted_effects = HashMap::new();
        for (import, edge) in loaded.surface().imports.iter().zip(
            loaded
                .dependencies()
                .iter()
                .filter(|edge| !edge.is_region_service()),
        ) {
            let route = DirectDependencyRoute::new(edge.target(), import.span);
            if edge.import_span() != import.span || !owner.direct_dependencies().contains(&route) {
                return Err(());
            }
            match &import.selection {
                SurfaceImportSelection::Qualified { alias } => {
                    if qualified.insert(alias.text.clone(), route).is_some() {
                        return Err(());
                    }
                }
                SurfaceImportSelection::Targeted(items) => {
                    let dependency = graph
                        .iter()
                        .find(|candidate| candidate.module() == route.target())
                        .ok_or(())?;
                    for item in items {
                        let SurfaceImportItem::Name { name, alias, span } = item else {
                            continue;
                        };
                        if dependency.exports().term(&name.text).is_some()
                            || dependency.exports().constructor(&name.text).is_some()
                            || dependency.exports().method(&name.text).is_some()
                        {
                            let local = alias.as_ref().unwrap_or(name);
                            if targeted
                                .insert(local.text.clone(), (route, name.text.clone(), *span))
                                .is_some()
                            {
                                return Err(());
                            }
                        }
                        if dependency.exports().nominal(&name.text).is_some() {
                            let local = alias.as_ref().unwrap_or(name);
                            if targeted_nominals
                                .insert(local.text.clone(), (route, name.text.clone(), *span))
                                .is_some()
                            {
                                return Err(());
                            }
                        }
                        if dependency.exports().interface(&name.text).is_some() {
                            let local = alias.as_ref().unwrap_or(name);
                            if targeted_interfaces
                                .insert(local.text.clone(), (route, name.text.clone(), *span))
                                .is_some()
                            {
                                return Err(());
                            }
                        }
                        if dependency.exports().effect(&name.text).is_some() {
                            let local = alias.as_ref().unwrap_or(name);
                            if targeted_effects
                                .insert(local.text.clone(), (route, name.text.clone(), *span))
                                .is_some()
                            {
                                return Err(());
                            }
                        }
                    }
                }
            }
        }
        Ok(Self {
            module: owner.module(),
            terms,
            constructors,
            qualified,
            targeted,
            targeted_nominals,
            targeted_interfaces,
            targeted_effects,
        })
    }

    pub(crate) fn empty(module: ModuleId) -> Self {
        Self {
            module,
            terms: HashMap::new(),
            constructors: HashMap::new(),
            qualified: HashMap::new(),
            targeted: HashMap::new(),
            targeted_nominals: HashMap::new(),
            targeted_interfaces: HashMap::new(),
            targeted_effects: HashMap::new(),
        }
    }

    pub(crate) fn get(&self, spelling: &str) -> Option<&ExportedGlobal> {
        self.terms.get(spelling)
    }

    pub(crate) fn constructor(&self, spelling: &str) -> Option<&ExportedConstructor> {
        self.constructors.get(spelling)
    }

    pub(crate) fn qualified(&self, spelling: &str) -> Option<DirectDependencyRoute> {
        self.qualified.get(spelling).copied()
    }

    pub(crate) fn targeted(&self, spelling: &str) -> Option<(DirectDependencyRoute, &str, Span)> {
        let (route, original, selector) = self.targeted.get(spelling)?;
        Some((*route, original, *selector))
    }

    pub(crate) fn targeted_nominal(
        &self,
        spelling: &str,
    ) -> Option<(DirectDependencyRoute, &str, Span)> {
        let (route, original, selector) = self.targeted_nominals.get(spelling)?;
        Some((*route, original, *selector))
    }

    pub(crate) fn targeted_interface(
        &self,
        spelling: &str,
    ) -> Option<(DirectDependencyRoute, &str, Span)> {
        let (route, original, selector) = self.targeted_interfaces.get(spelling)?;
        Some((*route, original, *selector))
    }

    pub(crate) fn targeted_effect(
        &self,
        spelling: &str,
    ) -> Option<(DirectDependencyRoute, &str, Span)> {
        let (route, original, selector) = self.targeted_effects.get(spelling)?;
        Some((*route, original, *selector))
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

/// Check template grammar with category-correct placeholders, without resolving names.
pub(crate) fn validate_template_syntax(
    declaration: &SurfaceSyntaxDeclaration,
    source: &crate::source::SourceFile,
    contexts: &SyntaxContexts,
) -> Result<(), crate::parser::MacroParseFailure> {
    // Declaration template admission and selection are not connected yet.
    if declaration.category == crate::surface::SurfaceSyntaxCategory::Declaration {
        return Err(crate::parser::MacroParseFailure::Invalid);
    }
    let SurfaceSyntaxImplementation::Template = &declaration.implementation else {
        return Ok(());
    };
    let mut captures = Vec::new();
    let mut identifiers = Vec::new();
    for part in &declaration.matcher {
        let SurfaceSyntaxMatcherPart::Capture { name, kind } = part else {
            continue;
        };
        let capture = match kind {
            SurfaceSyntaxCaptureKind::Expression => {
                SurfaceSyntaxCapture::Expression(SurfaceExpressionCapture {
                    expression: SurfaceExpr {
                        diagnostic: None,
                        kind: SurfaceExprKind::Unit,
                        span: name.span,
                    },
                    contents: Arc::from([]),
                })
            }
            SurfaceSyntaxCaptureKind::Identifier => {
                let placeholder = SurfaceName {
                    text: format!("__ash_template_capture_{}", captures.len()),
                    span: name.span,
                    introduction: usize::MAX - captures.len(),
                    introduced_at: Some(name.span),
                    written: false,
                    diagnostic: None,
                };
                identifiers.push(placeholder.clone());
                SurfaceSyntaxCapture::Identifier(SurfaceIdentifierCapture {
                    origin: placeholder.span.into(),
                    name: placeholder,
                })
            }
        };
        captures.push(capture);
    }
    let mut contents = declaration
        .template_contents
        .as_ref()
        .ok_or(crate::parser::MacroParseFailure::Invalid)?
        .to_vec();
    substitute_contents(
        &mut contents,
        &declaration.matcher,
        &captures,
        0,
        declaration.span,
    )
    .map_err(|_| crate::parser::MacroParseFailure::Invalid)?;
    crate::parser::parse_template_admission(
        source,
        declaration.span,
        contents,
        contexts,
        &identifiers,
    )?;
    Ok(())
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

pub(crate) fn admit_transformer_output(
    source: &crate::source::SourceFile,
    output: Vec<MacroOutputNode>,
    contexts: &SyntaxContexts,
    frame: &Arc<ExpansionFrame>,
) -> Result<SurfaceExpr, crate::parser::MacroParseFailure> {
    let invocation = frame.invocation;
    let mut expression = crate::parser::parse_macro_expression(
        source,
        invocation,
        None,
        output,
        contexts,
        Some(frame),
    )?;
    expression.span = invocation;
    Ok(expression)
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
                        MacroOutputNode::ForwardedExpression(capture.clone(), invocation.into())
                    }
                    SurfaceSyntaxCapture::Identifier(capture) => {
                        MacroOutputNode::Identifier(capture.name.clone(), capture.origin.clone())
                    }
                };
            }
            MacroOutputNode::Identifier(name, _) => {
                if introduction != 0 {
                    name.introduction = introduction;
                    name.introduced_at = Some(invocation);
                    name.written = false;
                }
            }
            MacroOutputNode::Group(_, children, _) => {
                substitute_contents(children, matcher, captures, introduction, invocation)?;
            }
            MacroOutputNode::Token(_, _, _)
            | MacroOutputNode::Expression(_, _)
            | MacroOutputNode::ForwardedExpression(_, _) => {}
        }
    }
    Ok(())
}
