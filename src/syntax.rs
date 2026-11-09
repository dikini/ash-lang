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
        SurfaceEffectRow, SurfaceExpr, SurfaceExprKind, SurfaceExpressionCapture,
        SurfaceIdentifierCapture, SurfaceImportItem, SurfaceImportSelection, SurfaceName,
        SurfacePattern, SurfacePatternCapture, SurfacePatternKind, SurfaceReference,
        SurfaceSyntaxCapture, SurfaceSyntaxCaptureKind, SurfaceSyntaxDeclaration,
        SurfaceSyntaxImplementation, SurfaceSyntaxMatcherPart, SurfaceType, SurfaceTypeCapture,
        SurfaceTypeKind,
    },
    syntax_resource::{ResourceFailure, SyntaxBudget},
    types::TypeWorkBudget,
};

/// Structured output transferred from one completed transformer invocation.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum MacroOutputNode {
    Expression(SurfaceExpressionCapture, MacroOrigin),
    ForwardedExpression(SurfaceExpressionCapture, MacroOrigin),
    ForwardedType(SurfaceTypeCapture, MacroOrigin),
    ForwardedPattern(SurfacePatternCapture, MacroOrigin),
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
        self.select_parts(&name.text, name.introduction)
    }

    pub(crate) fn select_parts(&self, text: &str, introduction: usize) -> Option<&SelectedSyntax> {
        self.imports_for(introduction)?
            .iter()
            .find(|syntax| syntax.name == text)
    }

    fn imports_for(&self, introduction: usize) -> Option<&[SelectedSyntax]> {
        if introduction == 0 {
            Some(&self.caller)
        } else {
            let owner = self.owners.get(introduction - 1)?.as_ref()?;
            Some(self.owner_imports.get(*owner)?)
        }
    }

    /// Reserve the comparisons for this scan and the immediately following lookup.
    pub(crate) fn charge_selection_search(
        &self,
        text: &str,
        introduction: usize,
        budget: &mut crate::syntax_resource::SyntaxBudget,
    ) -> Result<(), crate::syntax_resource::ResourceFailure> {
        budget.charge_units(2)?;
        if let Some(imports) = self.imports_for(introduction) {
            for selection in imports {
                // Compare once here and once in the following ordinary lookup.
                budget.charge_units(2)?;
                let bytes = text.len().min(selection.name.len());
                budget.charge_units(bytes)?;
                budget.charge_units(bytes)?;
                if selection.name == text {
                    break;
                }
            }
        }
        Ok(())
    }

    /// Copy the exact parse-time selection snapshot under the graph's ledger.
    pub(crate) fn new_budgeted(
        caller: &[SelectedSyntax],
        owner_imports: &[Vec<SelectedSyntax>],
        owners: &[SyntaxOwner],
        budget: &mut crate::syntax_resource::SyntaxBudget,
    ) -> Result<Self, crate::syntax_resource::ResourceFailure> {
        budget.charge_units(owners.len())?;
        budget.charge_units(owners.len())?;
        budget.charge_units(owner_imports.len())?;
        for selection in caller.iter().chain(owner_imports.iter().flatten()) {
            charge_selected(selection, budget)?;
        }
        let owners = owners.iter().map(|owner| owner.owner).collect::<Vec<_>>();
        Ok(Self::new(caller, owner_imports, &owners))
    }
}

pub(crate) fn charge_name(
    name: &SurfaceName,
    budget: &mut crate::syntax_resource::SyntaxBudget,
) -> Result<(), crate::syntax_resource::ResourceFailure> {
    budget.charge()?;
    budget.charge_units(name.text.len())?;
    if let Some(diagnostic) = &name.diagnostic {
        budget.charge()?;
        budget.charge_units(diagnostic.related.len())?;
        budget.charge_units(diagnostic.frames.len())?;
    }
    Ok(())
}

#[derive(Clone, Copy)]
enum TypeWork {
    Inspect,
    Copy { inherit_frame: bool },
}

pub(crate) fn type_depth(depth: usize, extra: usize) -> Result<usize, ResourceFailure> {
    let Some(depth) = depth.checked_add(extra) else {
        return Err(ResourceFailure::StructuralDepth {
            limit: crate::parser::STRUCTURAL_DEPTH_LIMIT,
        });
    };
    if depth > crate::parser::STRUCTURAL_DEPTH_LIMIT {
        return Err(ResourceFailure::StructuralDepth {
            limit: crate::parser::STRUCTURAL_DEPTH_LIMIT,
        });
    }
    Ok(depth)
}

pub(crate) fn charge_type_origin(
    origin: &MacroOrigin,
    depth: usize,
    budget: &mut SyntaxBudget,
) -> Result<(), ResourceFailure> {
    budget.charge()?;
    type_depth(depth, origin.depth())?;
    Ok(())
}

fn charge_type_location(
    location: Option<&DiagnosticLocation>,
    depth: usize,
    work: TypeWork,
    budget: &mut SyntaxBudget,
) -> Result<(), ResourceFailure> {
    if let Some(location) = location {
        let depth = type_depth(depth, 1)?;
        budget.charge()?;
        if matches!(work, TypeWork::Copy { .. }) {
            budget.charge()?;
            budget.charge_units(location.related.len())?;
            budget.charge_units(location.frames.len())?;
        }
        charge_type_origin(&location.primary, depth, budget)?;
        for origin in &location.related {
            charge_type_origin(origin, depth, budget)?;
        }
    }
    if matches!(
        work,
        TypeWork::Copy {
            inherit_frame: true
        }
    ) {
        type_depth(depth, 1)?;
        // A new location or frame entry, plus the real deduplication scan.
        budget.charge_units(2)?;
        budget.charge_units(location.map_or(0, |location| location.frames.len()))?;
        // Appending to the copied frame vector can move its existing entries.
        budget.charge_units(location.map_or(0, |location| location.frames.len()))?;
    }
    Ok(())
}

fn charge_type_name(
    name: &SurfaceName,
    depth: usize,
    work: TypeWork,
    budget: &mut SyntaxBudget,
) -> Result<(), ResourceFailure> {
    budget.charge()?;
    if matches!(work, TypeWork::Copy { .. }) {
        budget.charge()?;
        budget.charge_units(name.text.len())?;
    }
    charge_type_location(name.diagnostic.as_deref(), depth, work, budget)
}

fn charge_type_reference(
    reference: &SurfaceReference,
    depth: usize,
    work: TypeWork,
    budget: &mut SyntaxBudget,
) -> Result<(), ResourceFailure> {
    budget.charge()?;
    match reference {
        SurfaceReference::Unqualified(name) => charge_type_name(name, depth, work, budget),
        SurfaceReference::Qualified(name) => {
            charge_type_name(&name.qualifier, depth, work, budget)?;
            charge_type_name(&name.member, depth, work, budget)
        }
    }
}

/// Visit owned type and row edges before a copy or a retained-contents scan.
fn charge_type_value(
    ty: &SurfaceType,
    prefix: usize,
    work: TypeWork,
    budget: &mut SyntaxBudget,
) -> Result<(), ResourceFailure> {
    enum Pending<'a> {
        Type(&'a SurfaceType, usize),
        Row(&'a SurfaceEffectRow, usize),
    }

    type_depth(prefix, 0)?;
    budget.charge()?;
    let mut pending = vec![Pending::Type(ty, prefix)];
    while let Some(item) = pending.pop() {
        budget.charge()?;
        match item {
            Pending::Type(ty, depth) => {
                if let TypeWork::Copy { inherit_frame } = work {
                    budget.charge()?;
                    if inherit_frame {
                        // The frame walk visits and retains a worklist entry.
                        budget.charge_units(2)?;
                    }
                }
                charge_type_location(ty.diagnostic.as_deref(), depth, work, budget)?;
                match &ty.kind {
                    SurfaceTypeKind::Named(reference) => {
                        charge_type_reference(reference, depth, work, budget)?;
                    }
                    SurfaceTypeKind::Application {
                        constructor,
                        arguments,
                    } => {
                        charge_type_reference(constructor, depth, work, budget)?;
                        let child_depth = type_depth(depth, 1)?;
                        if matches!(work, TypeWork::Copy { .. }) {
                            budget.charge_units(arguments.len())?;
                        }
                        budget.charge_units(arguments.len())?;
                        pending.extend(
                            arguments
                                .iter()
                                .map(|argument| Pending::Type(argument, child_depth)),
                        );
                    }
                    SurfaceTypeKind::Tuple(elements) => {
                        let child_depth = type_depth(depth, 1)?;
                        if matches!(work, TypeWork::Copy { .. }) {
                            budget.charge_units(elements.len())?;
                        }
                        budget.charge_units(elements.len())?;
                        pending.extend(
                            elements
                                .iter()
                                .map(|element| Pending::Type(element, child_depth)),
                        );
                    }
                    SurfaceTypeKind::Function(function) => {
                        let child_depth = type_depth(depth, 1)?;
                        if matches!(work, TypeWork::Copy { .. }) {
                            budget.charge_units(2)?;
                        }
                        budget.charge_units(2)?;
                        pending.push(Pending::Type(&function.domain, child_depth));
                        pending.push(Pending::Type(&function.codomain, child_depth));
                        if let Some(row) = &function.effects {
                            budget.charge()?;
                            pending.push(Pending::Row(row, child_depth));
                        }
                    }
                    SurfaceTypeKind::RowArgument(row) => {
                        let child_depth = type_depth(depth, 1)?;
                        budget.charge()?;
                        pending.push(Pending::Row(row, child_depth));
                    }
                    SurfaceTypeKind::Int
                    | SurfaceTypeKind::Bytes
                    | SurfaceTypeKind::String
                    | SurfaceTypeKind::Bool
                    | SurfaceTypeKind::Unit => {}
                }
            }
            Pending::Row(row, depth) => {
                let child_depth = type_depth(depth, 1)?;
                if matches!(work, TypeWork::Copy { .. }) {
                    budget.charge_units(row.effects.len())?;
                }
                if let Some(tail) = &row.tail {
                    charge_type_name(tail, child_depth, work, budget)?;
                }
                for instance in &row.effects {
                    budget.charge()?;
                    charge_type_reference(&instance.effect, child_depth, work, budget)?;
                    if matches!(work, TypeWork::Copy { .. }) {
                        budget.charge_units(instance.arguments.len())?;
                    }
                    budget.charge_units(instance.arguments.len())?;
                    pending.extend(
                        instance
                            .arguments
                            .iter()
                            .map(|argument| Pending::Type(argument, child_depth)),
                    );
                }
            }
        }
    }
    Ok(())
}

pub(crate) fn charge_type_copy(
    ty: &SurfaceType,
    prefix: usize,
    inherit_frame: bool,
    budget: &mut SyntaxBudget,
) -> Result<(), ResourceFailure> {
    charge_type_value(ty, prefix, TypeWork::Copy { inherit_frame }, budget)
}

/// Borrowed entries used to reserve protected expression and pattern copies.
enum OwnedSyntax<'a> {
    Expression(&'a SurfaceExpr),
    Pattern(&'a SurfacePattern),
    Block(&'a crate::surface::SurfaceBlock),
    Local(&'a crate::surface::SurfaceLocalDeclaration),
    Equation(&'a crate::surface::SurfaceEquation),
    Kind(&'a crate::surface::SurfaceKind),
    Contents(&'a MacroOutputNode),
}

/// Reserve actual owned edges and inspect shared contents before copying.
/// The result reports an expression-syntax/host bridge found in the value;
/// callers decide whether that bridge is an execution boundary or admission.
fn charge_owned_syntax(
    root: OwnedSyntax<'_>,
    prefix: usize,
    work: TypeWork,
    budget: &mut SyntaxBudget,
) -> Result<bool, ResourceFailure> {
    use crate::surface::{SurfaceKindKind, SurfaceLocalDeclaration};

    type_depth(prefix, 0)?;
    budget.charge()?;
    let mut pending = vec![(root, prefix, work)];
    let mut bridge = false;
    macro_rules! push {
        ($item:expr, $depth:expr, $work:expr) => {{
            budget.charge()?;
            pending.push(($item, $depth, $work));
        }};
    }
    macro_rules! copy_entries {
        ($count:expr, $work:expr) => {
            if matches!($work, TypeWork::Copy { .. }) {
                budget.charge_units($count)?;
            }
        };
    }
    macro_rules! contents {
        ($contents:expr, $depth:expr) => {{
            let depth = type_depth($depth, 1)?;
            budget.charge()?; // retained Arc
            for node in $contents.iter() {
                push!(OwnedSyntax::Contents(node), depth, TypeWork::Inspect);
            }
        }};
    }
    macro_rules! effect {
        ($effect:expr, $depth:expr, $work:expr) => {{
            charge_type_reference(&$effect.effect, $depth, $work, budget)?;
            copy_entries!($effect.arguments.len(), $work);
            if !$effect.arguments.is_empty() {
                let child = type_depth($depth, 1)?;
                for argument in &$effect.arguments {
                    charge_type_value(argument, child, $work, budget)?;
                }
            }
        }};
    }

    while let Some((value, depth, work)) = pending.pop() {
        budget.charge()?;
        let inner_work = match work {
            TypeWork::Inspect => TypeWork::Inspect,
            TypeWork::Copy { .. } => TypeWork::Copy {
                inherit_frame: false,
            },
        };
        match value {
            OwnedSyntax::Expression(expression) => {
                copy_entries!(1, work);
                charge_type_location(expression.diagnostic.as_deref(), depth, work, budget)?;
                match &expression.kind {
                    SurfaceExprKind::TemplateSplice(name) => {
                        charge_type_name(name, depth, inner_work, budget)?;
                    }
                    SurfaceExprKind::Name(reference) => {
                        charge_type_reference(reference, depth, inner_work, budget)?;
                    }
                    SurfaceExprKind::Integer(value) => {
                        if matches!(work, TypeWork::Copy { .. }) {
                            budget.charge_units(
                                usize::try_from(value.magnitude_byte_length())
                                    .unwrap_or(usize::MAX),
                            )?;
                        }
                    }
                    SurfaceExprKind::String(value) => {
                        if matches!(work, TypeWork::Copy { .. }) {
                            budget.charge_units(value.len())?;
                        }
                    }
                    SurfaceExprKind::Boolean(_)
                    | SurfaceExprKind::Unit
                    | SurfaceExprKind::Discard
                    | SurfaceExprKind::Retain => {}
                    SurfaceExprKind::Tuple(elements) => {
                        copy_entries!(elements.len(), work);
                        if !elements.is_empty() {
                            let child = type_depth(depth, 1)?;
                            for element in elements {
                                push!(OwnedSyntax::Expression(element), child, inner_work);
                            }
                        }
                    }
                    SurfaceExprKind::Apply(application) => {
                        let child = type_depth(depth, 1)?;
                        copy_entries!(2, work);
                        push!(
                            OwnedSyntax::Expression(&application.function),
                            child,
                            inner_work
                        );
                        push!(
                            OwnedSyntax::Expression(&application.argument),
                            child,
                            inner_work
                        );
                    }
                    SurfaceExprKind::Multiply(binary)
                    | SurfaceExprKind::Add(binary)
                    | SurfaceExprKind::Equal(binary) => {
                        let child = type_depth(depth, 1)?;
                        copy_entries!(2, work);
                        push!(OwnedSyntax::Expression(&binary.left), child, inner_work);
                        push!(OwnedSyntax::Expression(&binary.right), child, inner_work);
                    }
                    SurfaceExprKind::Block(block) => {
                        push!(OwnedSyntax::Block(block), depth, inner_work);
                    }
                    SurfaceExprKind::Function(function) => {
                        push!(OwnedSyntax::Pattern(&function.parameter), depth, inner_work);
                        push!(OwnedSyntax::Block(&function.body), depth, inner_work);
                    }
                    SurfaceExprKind::Match(value) => {
                        let child = type_depth(depth, 1)?;
                        copy_entries!(1 + value.arms.len(), work);
                        push!(OwnedSyntax::Expression(&value.scrutinee), child, inner_work);
                        for arm in &value.arms {
                            push!(OwnedSyntax::Pattern(&arm.pattern), child, inner_work);
                            push!(OwnedSyntax::Expression(&arm.body), child, inner_work);
                        }
                    }
                    SurfaceExprKind::Perform(value) => {
                        charge_type_reference(&value.effect, depth, inner_work, budget)?;
                        charge_type_name(&value.operation, depth, inner_work, budget)?;
                        let child = type_depth(depth, 1)?;
                        copy_entries!(1 + value.arguments.len(), work);
                        push!(OwnedSyntax::Expression(&value.operand), child, inner_work);
                        for argument in &value.arguments {
                            charge_type_value(argument, child, inner_work, budget)?;
                        }
                    }
                    SurfaceExprKind::Handle(value) => {
                        effect!(value.effect, depth, inner_work);
                        let child = type_depth(depth, 1)?;
                        copy_entries!(
                            1 + usize::from(value.store.is_some()) + value.clauses.len(),
                            work
                        );
                        push!(OwnedSyntax::Expression(&value.body), child, inner_work);
                        if let Some(store) = &value.store {
                            push!(OwnedSyntax::Expression(store), child, inner_work);
                        }
                        for clause in &value.clauses {
                            charge_type_name(&clause.operation, child, inner_work, budget)?;
                            push!(OwnedSyntax::Pattern(&clause.pattern), child, inner_work);
                            push!(OwnedSyntax::Expression(&clause.body), child, inner_work);
                        }
                    }
                    SurfaceExprKind::Resume(value) => {
                        let child = type_depth(depth, 1)?;
                        copy_entries!(1, work);
                        push!(OwnedSyntax::Expression(value), child, inner_work);
                    }
                    SurfaceExprKind::Resource(value) => {
                        let child = type_depth(depth, 1)?;
                        copy_entries!(1, work);
                        charge_type_name(&value.identity, child, inner_work, budget)?;
                        charge_type_name(&value.handle, child, inner_work, budget)?;
                        push!(
                            OwnedSyntax::Expression(&value.initializer),
                            child,
                            inner_work
                        );
                        push!(OwnedSyntax::Block(&value.body), child, inner_work);
                    }
                    SurfaceExprKind::Region(value) => {
                        let child = type_depth(depth, 1)?;
                        copy_entries!(1, work);
                        charge_type_name(&value.identity, child, inner_work, budget)?;
                        charge_type_name(&value.handle, child, inner_work, budget)?;
                        if let Some(provider) = &value.provider {
                            push!(OwnedSyntax::Expression(provider), child, inner_work);
                        }
                        push!(OwnedSyntax::Block(&value.body), child, inner_work);
                    }
                    SurfaceExprKind::RegionSelection(value) => {
                        let child = type_depth(depth, 1)?;
                        copy_entries!(1, work);
                        push!(OwnedSyntax::Expression(&value.region), child, inner_work);
                        push!(OwnedSyntax::Block(&value.body), child, inner_work);
                    }
                    SurfaceExprKind::ProviderResource(value) => {
                        let child = type_depth(depth, 1)?;
                        copy_entries!(1 + value.arguments.len(), work);
                        charge_type_reference(&value.family, child, inner_work, budget)?;
                        charge_type_name(&value.handle, child, inner_work, budget)?;
                        if !value.arguments.is_empty() {
                            let argument_depth = type_depth(child, 1)?;
                            for argument in &value.arguments {
                                charge_type_value(argument, argument_depth, inner_work, budget)?;
                            }
                        }
                        push!(
                            OwnedSyntax::Expression(&value.initializer),
                            child,
                            inner_work
                        );
                        push!(OwnedSyntax::Block(&value.body), child, inner_work);
                    }
                    SurfaceExprKind::Hook(value) => {
                        let child = type_depth(depth, 1)?;
                        copy_entries!(1, work);
                        effect!(value.effect, child, inner_work);
                        push!(OwnedSyntax::Block(&value.body), child, inner_work);
                    }
                    SurfaceExprKind::Registration(value) => {
                        let child = type_depth(depth, 1)?;
                        copy_entries!(1, work);
                        effect!(value.effect, child, inner_work);
                        push!(
                            OwnedSyntax::Expression(&value.transformer),
                            child,
                            inner_work
                        );
                        push!(OwnedSyntax::Block(&value.body), child, inner_work);
                    }
                    SurfaceExprKind::Cleanup(value) => {
                        let child = type_depth(depth, 1)?;
                        copy_entries!(1, work);
                        push!(OwnedSyntax::Expression(&value.action), child, inner_work);
                        push!(OwnedSyntax::Block(&value.body), child, inner_work);
                    }
                    SurfaceExprKind::SyntaxInvocation { name, captures } => {
                        bridge = true;
                        charge_type_name(name, depth, inner_work, budget)?;
                        copy_entries!(captures.len(), work);
                        if !captures.is_empty() {
                            let child = type_depth(depth, 1)?;
                            for capture in captures {
                                match capture {
                                    SurfaceSyntaxCapture::Identifier(capture) => {
                                        charge_type_name(&capture.name, child, inner_work, budget)?;
                                        charge_type_origin(&capture.origin, child, budget)?;
                                    }
                                    SurfaceSyntaxCapture::Expression(capture) => {
                                        push!(
                                            OwnedSyntax::Expression(&capture.expression),
                                            child,
                                            inner_work
                                        );
                                        contents!(capture.contents, child);
                                    }
                                    SurfaceSyntaxCapture::Pattern(capture) => {
                                        push!(
                                            OwnedSyntax::Pattern(&capture.pattern),
                                            child,
                                            inner_work
                                        );
                                        contents!(capture.contents, child);
                                    }
                                    SurfaceSyntaxCapture::Type(capture) => {
                                        charge_type_value(&capture.ty, child, inner_work, budget)?;
                                        contents!(capture.contents, child);
                                    }
                                }
                            }
                        }
                    }
                }
            }
            OwnedSyntax::Pattern(pattern) => {
                copy_entries!(1, work);
                if matches!(
                    work,
                    TypeWork::Copy {
                        inherit_frame: true
                    }
                ) {
                    budget.charge_units(2)?;
                }
                charge_type_location(pattern.diagnostic.as_deref(), depth, work, budget)?;
                match &pattern.kind {
                    SurfacePatternKind::TemplateSplice(name) => {
                        charge_type_name(name, depth, work, budget)?;
                    }
                    SurfacePatternKind::Binder(binder) => {
                        charge_type_name(&binder.name, depth, work, budget)?;
                    }
                    SurfacePatternKind::Tuple(elements) => {
                        copy_entries!(elements.len(), work);
                        if !elements.is_empty() {
                            let child = type_depth(depth, 1)?;
                            for element in elements {
                                push!(OwnedSyntax::Pattern(element), child, work);
                            }
                        }
                    }
                    SurfacePatternKind::Constructor { name, payload } => {
                        charge_type_reference(name, depth, work, budget)?;
                        if let Some(payload) = payload {
                            let child = type_depth(depth, 1)?;
                            copy_entries!(1, work);
                            push!(OwnedSyntax::Pattern(payload), child, work);
                        }
                    }
                    SurfacePatternKind::Wildcard
                    | SurfacePatternKind::Boolean(_)
                    | SurfacePatternKind::Unit => {}
                }
            }
            OwnedSyntax::Block(block) => {
                let child = type_depth(depth, 1)?;
                copy_entries!(1 + block.declarations.len(), work);
                push!(OwnedSyntax::Expression(&block.result), child, work);
                for declaration in &block.declarations {
                    push!(OwnedSyntax::Local(declaration), child, work);
                }
            }
            OwnedSyntax::Local(local) => match local {
                SurfaceLocalDeclaration::Binding(binding) => {
                    let child = type_depth(depth, 1)?;
                    copy_entries!(1, work);
                    push!(OwnedSyntax::Pattern(&binding.pattern), child, work);
                    if let Some(annotation) = &binding.annotation {
                        charge_type_value(annotation, child, work, budget)?;
                    }
                    push!(OwnedSyntax::Expression(&binding.initializer), child, work);
                }
                SurfaceLocalDeclaration::Evidence(evidence) => {
                    let child = type_depth(depth, 1)?;
                    copy_entries!(1, work);
                    charge_type_reference(&evidence.application.interface, child, work, budget)?;
                    copy_entries!(
                        evidence.application.arguments.len() + evidence.equations.len(),
                        work
                    );
                    if !evidence.application.arguments.is_empty() || !evidence.equations.is_empty()
                    {
                        let item = type_depth(child, 1)?;
                        for argument in &evidence.application.arguments {
                            charge_type_value(argument, item, work, budget)?;
                        }
                        for equation in &evidence.equations {
                            push!(OwnedSyntax::Equation(equation), item, work);
                        }
                    }
                }
                SurfaceLocalDeclaration::Recursive(group) => {
                    copy_entries!(group.members.len(), work);
                    if !group.members.is_empty() {
                        let child = type_depth(depth, 1)?;
                        for member in &group.members {
                            charge_type_name(&member.binder.name, child, work, budget)?;
                            charge_type_value(&member.annotation, child, work, budget)?;
                            push!(OwnedSyntax::Expression(&member.initializer), child, work);
                        }
                    }
                }
                SurfaceLocalDeclaration::Newtype(declaration) => {
                    charge_type_name(&declaration.name, depth, work, budget)?;
                    copy_entries!(
                        declaration.parameters.len() + declaration.constructors.len(),
                        work
                    );
                    if !declaration.parameters.is_empty() || !declaration.constructors.is_empty() {
                        let child = type_depth(depth, 1)?;
                        for parameter in &declaration.parameters {
                            charge_type_name(&parameter.name, child, work, budget)?;
                            if let Some(kind) = &parameter.kind {
                                push!(OwnedSyntax::Kind(kind), child, work);
                            }
                        }
                        for constructor in &declaration.constructors {
                            charge_type_name(&constructor.name, child, work, budget)?;
                            copy_entries!(constructor.fields.len(), work);
                            if !constructor.fields.is_empty() {
                                let field = type_depth(child, 1)?;
                                for ty in &constructor.fields {
                                    charge_type_value(ty, field, work, budget)?;
                                }
                            }
                        }
                    }
                    if let Some(order) = &declaration.generated_parameters {
                        let child = type_depth(depth, 1)?;
                        budget.charge()?; // retained Arc
                        charge_type_name(order.name(), child, TypeWork::Inspect, budget)?;
                        if !order.parameters().is_empty() {
                            let item = type_depth(child, 1)?;
                            for occurrence in order.parameters() {
                                charge_type_name(
                                    occurrence.name(),
                                    item,
                                    TypeWork::Inspect,
                                    budget,
                                )?;
                            }
                        }
                    }
                }
            },
            OwnedSyntax::Equation(equation) => {
                charge_type_name(&equation.name, depth, work, budget)?;
                copy_entries!(equation.patterns.len(), work);
                if !equation.patterns.is_empty() {
                    let child = type_depth(depth, 1)?;
                    for pattern in &equation.patterns {
                        push!(OwnedSyntax::Pattern(pattern), child, work);
                    }
                }
                push!(OwnedSyntax::Expression(&equation.body), depth, work);
            }
            OwnedSyntax::Kind(kind) => match &kind.kind {
                SurfaceKindKind::Type | SurfaceKindKind::EffectRow => {}
                SurfaceKindKind::Function { domain, codomain } => {
                    let child = type_depth(depth, 1)?;
                    copy_entries!(2, work);
                    push!(OwnedSyntax::Kind(domain), child, work);
                    push!(OwnedSyntax::Kind(codomain), child, work);
                }
            },
            OwnedSyntax::Contents(node) => match node {
                MacroOutputNode::Expression(capture, origin)
                | MacroOutputNode::ForwardedExpression(capture, origin) => {
                    if matches!(node, MacroOutputNode::Expression(..)) {
                        bridge = true;
                    }
                    let child = type_depth(depth, 1)?;
                    charge_type_origin(origin, child, budget)?;
                    push!(
                        OwnedSyntax::Expression(&capture.expression),
                        child,
                        TypeWork::Inspect
                    );
                    contents!(capture.contents, child);
                }
                MacroOutputNode::ForwardedPattern(capture, origin) => {
                    let child = type_depth(depth, 1)?;
                    charge_type_origin(origin, child, budget)?;
                    push!(
                        OwnedSyntax::Pattern(&capture.pattern),
                        child,
                        TypeWork::Inspect
                    );
                    contents!(capture.contents, child);
                }
                MacroOutputNode::ForwardedType(capture, origin) => {
                    let child = type_depth(depth, 1)?;
                    charge_type_origin(origin, child, budget)?;
                    charge_type_value(&capture.ty, child, TypeWork::Inspect, budget)?;
                    contents!(capture.contents, child);
                }
                MacroOutputNode::Group(_, children, origin) => {
                    let child = type_depth(depth, 1)?;
                    charge_type_origin(origin, child, budget)?;
                    for node in children {
                        push!(OwnedSyntax::Contents(node), child, TypeWork::Inspect);
                    }
                }
                MacroOutputNode::Identifier(name, origin) => {
                    charge_type_name(name, depth, TypeWork::Inspect, budget)?;
                    charge_type_origin(origin, depth, budget)?;
                }
                MacroOutputNode::Token(_, _, origin) => {
                    charge_type_origin(origin, depth, budget)?;
                }
                MacroOutputNode::Splice(name) => {
                    bridge = true;
                    charge_type_name(name, depth, TypeWork::Inspect, budget)?;
                }
            },
        }
    }
    Ok(bridge)
}

pub(crate) fn charge_expression_copy(
    expression: &SurfaceExpr,
    prefix: usize,
    inherit_frame: bool,
    budget: &mut SyntaxBudget,
) -> Result<bool, ResourceFailure> {
    charge_owned_syntax(
        OwnedSyntax::Expression(expression),
        prefix,
        TypeWork::Copy { inherit_frame },
        budget,
    )
}

pub(crate) fn charge_pattern_copy(
    pattern: &SurfacePattern,
    prefix: usize,
    inherit_frame: bool,
    budget: &mut SyntaxBudget,
) -> Result<bool, ResourceFailure> {
    charge_owned_syntax(
        OwnedSyntax::Pattern(pattern),
        prefix,
        TypeWork::Copy { inherit_frame },
        budget,
    )
}

fn charge_owned_retention(
    root: OwnedSyntax<'_>,
    contents: &[MacroOutputNode],
    prefix: usize,
    budget: &mut SyntaxBudget,
) -> Result<bool, ResourceFailure> {
    let depth = type_depth(prefix, 1)?;
    let mut bridge = charge_owned_syntax(root, depth, TypeWork::Inspect, budget)?;
    let contents_depth = type_depth(depth, 1)?;
    budget.charge()?; // retained contents Arc
    for node in contents {
        bridge |= charge_owned_syntax(
            OwnedSyntax::Contents(node),
            contents_depth,
            TypeWork::Inspect,
            budget,
        )?;
    }
    Ok(bridge)
}

pub(crate) fn charge_expression_retention(
    capture: &SurfaceExpressionCapture,
    prefix: usize,
    budget: &mut SyntaxBudget,
) -> Result<bool, ResourceFailure> {
    charge_owned_retention(
        OwnedSyntax::Expression(&capture.expression),
        &capture.contents,
        prefix,
        budget,
    )
}

pub(crate) fn charge_pattern_retention(
    capture: &SurfacePatternCapture,
    prefix: usize,
    budget: &mut SyntaxBudget,
) -> Result<bool, ResourceFailure> {
    charge_owned_retention(
        OwnedSyntax::Pattern(&capture.pattern),
        &capture.contents,
        prefix,
        budget,
    )
}

/// Inspect the ownership path that remains behind a copied type capture.
pub(crate) fn charge_type_retention(
    capture: &SurfaceTypeCapture,
    prefix: usize,
    budget: &mut SyntaxBudget,
) -> Result<(), crate::parser::MacroParseFailure> {
    use crate::parser::MacroParseFailure;

    fn resource(error: ResourceFailure) -> MacroParseFailure {
        MacroParseFailure::Syntax {
            diagnostics: Vec::new(),
            resource: Some(error),
        }
    }

    let depth = type_depth(prefix, 1).map_err(resource)?;
    charge_type_value(&capture.ty, depth, TypeWork::Inspect, budget).map_err(resource)?;
    let contents_depth = type_depth(depth, 1).map_err(resource)?;
    // Cloning the capture retains one shared contents handle.
    budget.charge().map_err(resource)?;
    budget
        .charge_units(capture.contents.len())
        .map_err(resource)?;
    let mut pending = capture
        .contents
        .iter()
        .map(|node| (node, contents_depth))
        .collect::<Vec<_>>();
    while let Some((node, prefix)) = pending.pop() {
        budget.charge().map_err(resource)?;
        match node {
            MacroOutputNode::Group(_, children, origin) => {
                let depth = type_depth(prefix, 1).map_err(resource)?;
                charge_type_origin(origin, depth, budget).map_err(resource)?;
                budget.charge_units(children.len()).map_err(resource)?;
                pending.extend(children.iter().map(|child| (child, depth)));
            }
            MacroOutputNode::ForwardedType(capture, origin) => {
                let depth = type_depth(prefix, 1).map_err(resource)?;
                charge_type_origin(origin, depth, budget).map_err(resource)?;
                charge_type_value(&capture.ty, depth, TypeWork::Inspect, budget)
                    .map_err(resource)?;
                let contents_depth = type_depth(depth, 1).map_err(resource)?;
                budget
                    .charge_units(capture.contents.len())
                    .map_err(resource)?;
                pending.extend(capture.contents.iter().map(|child| (child, contents_depth)));
            }
            MacroOutputNode::Identifier(name, origin) => {
                charge_type_name(name, prefix, TypeWork::Inspect, budget).map_err(resource)?;
                charge_type_origin(origin, prefix, budget).map_err(resource)?;
            }
            MacroOutputNode::Token(_, _, origin) => {
                charge_type_origin(origin, prefix, budget).map_err(resource)?;
            }
            MacroOutputNode::Expression(_, _)
            | MacroOutputNode::ForwardedExpression(_, _)
            | MacroOutputNode::ForwardedPattern(_, _)
            | MacroOutputNode::Splice(_) => return Err(MacroParseFailure::Invalid),
        }
    }
    Ok(())
}

pub(crate) fn charge_type_token_copy(
    kind: &crate::lexer::TokenKind,
    budget: &mut SyntaxBudget,
) -> Result<(), ResourceFailure> {
    use crate::lexer::TokenKind;
    budget.charge()?;
    match kind {
        TokenKind::Identifier(text)
        | TokenKind::UpperIdentifier(text)
        | TokenKind::StringLiteral(text) => budget.charge_units(text.len()),
        TokenKind::Integer(value) => budget
            .charge_units(usize::try_from(value.magnitude_byte_length()).unwrap_or(usize::MAX)),
        _ => Ok(()),
    }
}

/// Reserve the actual clone made while reconstructing captured type contents.
pub(crate) fn charge_captured_type_original(
    node: &MacroOutputNode,
    prefix: usize,
    budget: &mut SyntaxBudget,
) -> Result<(), crate::parser::MacroParseFailure> {
    use crate::parser::MacroParseFailure;

    fn resource(error: ResourceFailure) -> MacroParseFailure {
        MacroParseFailure::Syntax {
            diagnostics: Vec::new(),
            resource: Some(error),
        }
    }

    match node {
        MacroOutputNode::ForwardedType(capture, origin) => {
            let depth = type_depth(prefix, 1).map_err(resource)?;
            charge_type_origin(origin, depth, budget).map_err(resource)?;
            charge_type_copy(&capture.ty, depth, false, budget).map_err(resource)?;
            charge_type_retention(capture, prefix, budget)?;
            // A singleton forward retains its contents once more after the
            // temporary capture is dropped.
            budget.charge().map_err(resource)?;
        }
        MacroOutputNode::Identifier(name, origin) => {
            charge_type_name(
                name,
                prefix,
                TypeWork::Copy {
                    inherit_frame: false,
                },
                budget,
            )
            .map_err(resource)?;
            charge_type_origin(origin, prefix, budget).map_err(resource)?;
        }
        MacroOutputNode::Token(kind, _, origin) => {
            charge_type_token_copy(kind, budget).map_err(resource)?;
            // The spelling Arc is shared by this clone.
            budget.charge().map_err(resource)?;
            charge_type_origin(origin, prefix, budget).map_err(resource)?;
        }
        // capture_contents rebuilds group children and clones only the origin.
        MacroOutputNode::Group(_, _, origin) => {
            charge_type_origin(origin, prefix, budget).map_err(resource)?;
        }
        MacroOutputNode::Expression(_, _)
        | MacroOutputNode::ForwardedExpression(_, _)
        | MacroOutputNode::ForwardedPattern(_, _)
        | MacroOutputNode::Splice(_) => return Err(MacroParseFailure::Invalid),
    }
    Ok(())
}

pub(crate) fn charge_selected(
    selection: &SelectedSyntax,
    budget: &mut crate::syntax_resource::SyntaxBudget,
) -> Result<(), crate::syntax_resource::ResourceFailure> {
    budget.charge()?;
    budget.charge_units(selection.name.len())?;
    charge_name(&selection.declaration.name, budget)?;
    budget.charge_units(selection.declaration.matcher.len())?;
    for part in &selection.declaration.matcher {
        match part {
            SurfaceSyntaxMatcherPart::Literal { spelling, .. } => {
                // The spelling also bounds the storage of a cloned literal token.
                budget.charge_units(spelling.len())?;
                budget.charge_units(spelling.len())?;
            }
            SurfaceSyntaxMatcherPart::Capture { name, .. } => charge_name(name, budget)?,
        }
    }
    if let SurfaceSyntaxImplementation::Transformer(name) = &selection.declaration.implementation {
        charge_name(name, budget)?;
    }
    Ok(())
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
        owners: Vec<SyntaxOwner>,
        transformer: &'a mut SyntaxTransformer<'a>,
    ) -> Self {
        Self {
            source,
            selected,
            owner_imports,
            owners,
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
    let SurfaceSyntaxImplementation::Template = &declaration.implementation else {
        return if declaration.category == crate::surface::SurfaceSyntaxCategory::Declaration {
            Err(crate::parser::MacroParseFailure::Invalid)
        } else {
            Ok(())
        };
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
            SurfaceSyntaxCaptureKind::Type => SurfaceSyntaxCapture::Type(SurfaceTypeCapture {
                ty: SurfaceType {
                    kind: SurfaceTypeKind::Unit,
                    span: name.span,
                    diagnostic: None,
                },
                contents: Arc::from([]),
            }),
            SurfaceSyntaxCaptureKind::Pattern => {
                SurfaceSyntaxCapture::Pattern(SurfacePatternCapture {
                    pattern: SurfacePattern {
                        kind: SurfacePatternKind::Wildcard,
                        span: name.span,
                        diagnostic: None,
                    },
                    contents: Arc::from([]),
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
    match declaration.category {
        crate::surface::SurfaceSyntaxCategory::Expression => {
            crate::parser::parse_template_admission(
                source,
                declaration.span,
                contents,
                contexts,
                &identifiers,
            )?;
        }
        crate::surface::SurfaceSyntaxCategory::Declaration => {
            crate::parser::parse_declaration_template_admission(
                source,
                declaration.span,
                contents,
                contexts,
                &identifiers,
            )?;
        }
    }
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

/// Reserve the copies performed by declaration-template substitution.
fn charge_declaration_template(
    template: &[MacroOutputNode],
    matcher: &[SurfaceSyntaxMatcherPart],
    captures: &[SurfaceSyntaxCapture],
    budget: &mut SyntaxBudget,
) -> Result<bool, crate::parser::MacroParseFailure> {
    use crate::parser::{MacroParseFailure, STRUCTURAL_DEPTH_LIMIT};
    use crate::syntax_resource::ResourceFailure;

    fn resource(error: ResourceFailure) -> MacroParseFailure {
        MacroParseFailure::Syntax {
            diagnostics: Vec::new(),
            resource: Some(error),
        }
    }

    let mut bridge = false;
    budget.charge_units(template.len()).map_err(resource)?;
    budget.charge_units(template.len()).map_err(resource)?;
    let mut pending = template
        .iter()
        .map(|node| (node, 0usize))
        .collect::<Vec<_>>();
    while let Some((node, depth)) = pending.pop() {
        budget.charge().map_err(resource)?;
        match node {
            MacroOutputNode::Identifier(name, _) => charge_name(name, budget).map_err(resource)?,
            MacroOutputNode::Token(_, spelling, _) => {
                budget.charge_units(spelling.len()).map_err(resource)?;
            }
            MacroOutputNode::Group(_, children, _) => {
                if depth >= STRUCTURAL_DEPTH_LIMIT {
                    return Err(resource(ResourceFailure::StructuralDepth {
                        limit: STRUCTURAL_DEPTH_LIMIT,
                    }));
                }
                budget.charge_units(children.len()).map_err(resource)?;
                budget.charge_units(children.len()).map_err(resource)?;
                pending.extend(children.iter().map(|child| (child, depth + 1)));
            }
            MacroOutputNode::Splice(name) => {
                charge_name(name, budget).map_err(resource)?;
                for part in matcher {
                    // This scan, the preflight lookup, and substitution lookup.
                    budget.charge_units(3).map_err(resource)?;
                    if let SurfaceSyntaxMatcherPart::Capture { name: capture, .. } = part {
                        let bytes = name.text.len().min(capture.text.len());
                        budget.charge_units(bytes).map_err(resource)?;
                        budget.charge_units(bytes).map_err(resource)?;
                        budget.charge_units(bytes).map_err(resource)?;
                        if name.text == capture.text {
                            break;
                        }
                    }
                }
                match capture_by_name(name, matcher, captures) {
                    Ok(SurfaceSyntaxCapture::Identifier(capture)) => {
                        charge_name(&capture.name, budget).map_err(resource)?;
                    }
                    Ok(SurfaceSyntaxCapture::Type(capture)) => {
                        let type_prefix = type_depth(depth, 1).map_err(resource)?;
                        charge_type_copy(&capture.ty, type_prefix, false, budget)
                            .map_err(resource)?;
                        charge_type_retention(capture, depth, budget)?;
                    }
                    Ok(SurfaceSyntaxCapture::Expression(capture)) => {
                        let prefix = type_depth(depth, 1).map_err(resource)?;
                        let mut capture_bridge =
                            charge_expression_copy(&capture.expression, prefix, false, budget)
                                .map_err(resource)?;
                        capture_bridge |= charge_expression_retention(capture, depth, budget)
                            .map_err(resource)?;
                        bridge |= capture_bridge;
                    }
                    Ok(SurfaceSyntaxCapture::Pattern(capture)) => {
                        let prefix = type_depth(depth, 1).map_err(resource)?;
                        let mut capture_bridge =
                            charge_pattern_copy(&capture.pattern, prefix, false, budget)
                                .map_err(resource)?;
                        capture_bridge |=
                            charge_pattern_retention(capture, depth, budget).map_err(resource)?;
                        bridge |= capture_bridge;
                    }
                    _ => return Err(MacroParseFailure::Invalid),
                }
            }
            MacroOutputNode::Expression(_, _)
            | MacroOutputNode::ForwardedExpression(_, _)
            | MacroOutputNode::ForwardedType(_, _)
            | MacroOutputNode::ForwardedPattern(_, _) => return Err(MacroParseFailure::Invalid),
        }
    }
    Ok(bridge)
}

/// Instantiate supported captures before the existing declaration parser.
pub(crate) fn instantiate_declaration_template(
    selection: &SelectedSyntax,
    captures: &[SurfaceSyntaxCapture],
    introduction: usize,
    invocation: Span,
    budget: &mut SyntaxBudget,
) -> Result<Vec<MacroOutputNode>, crate::parser::MacroParseFailure> {
    use crate::parser::MacroParseFailure;

    let template = selection
        .declaration
        .template_contents
        .as_deref()
        .ok_or(MacroParseFailure::Invalid)?;
    if charge_declaration_template(template, &selection.declaration.matcher, captures, budget)? {
        return Err(MacroParseFailure::Invalid);
    }
    let mut output = template.to_vec();
    substitute_contents(
        &mut output,
        &selection.declaration.matcher,
        captures,
        introduction,
        invocation,
    )
    .map_err(|_| MacroParseFailure::Invalid)?;
    Ok(output)
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

pub(crate) fn substitute_contents(
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
                    SurfaceSyntaxCapture::Type(capture) => MacroOutputNode::ForwardedType(
                        capture.clone(),
                        capture.ty.diagnostic.as_ref().map_or_else(
                            || capture.ty.span.into(),
                            |location| location.primary.clone(),
                        ),
                    ),
                    SurfaceSyntaxCapture::Pattern(capture) => MacroOutputNode::ForwardedPattern(
                        capture.clone(),
                        capture.pattern.diagnostic.as_ref().map_or_else(
                            || capture.pattern.span.into(),
                            |location| location.primary.clone(),
                        ),
                    ),
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
            | MacroOutputNode::ForwardedExpression(_, _)
            | MacroOutputNode::ForwardedType(_, _)
            | MacroOutputNode::ForwardedPattern(_, _) => {}
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        source::{ByteRange, SourceFile},
        surface::{
            SurfacePattern, SurfacePatternCapture, SurfacePatternKind, SurfaceType,
            SurfaceTypeCapture, SurfaceTypeKind,
        },
    };

    fn nested_template(
        text: &str,
        transformer: bool,
    ) -> Result<(), crate::parser::MacroParseFailure> {
        let inner_source = SourceFile::new(
            "inner_forms.ash",
            include_str!("../docs/design/macros/fixtures/nested/inner_forms.ash"),
        )
        .unwrap();
        let inner_tree = crate::parser::parse(crate::lexer::lex(&inner_source).unwrap());
        let mut inner =
            crate::parser::project_module_retaining_templates(&inner_source, &inner_tree)
                .unwrap()
                .syntax_declarations
                .remove(0);
        if transformer {
            inner.implementation = SurfaceSyntaxImplementation::Transformer(inner.name.clone());
            inner.template_contents = None;
        }
        let selected = [SelectedSyntax {
            name: inner.name.text.clone(),
            owner: 0,
            import_span: inner.span,
            declaration: inner,
        }];
        let contexts = SyntaxContexts::new(&selected, &[], &[]);
        let source = SourceFile::new("outer_forms.ash", text).unwrap();
        let tree = crate::parser::parse(crate::lexer::lex(&source).unwrap());
        let module = crate::parser::project_module_retaining_templates(&source, &tree).unwrap();
        validate_template_syntax(&module.syntax_declarations[0], &source, &contexts)
    }

    #[test]
    fn nested_declaration_template_admits_fixed_invocation_without_executing_it() {
        let outer = include_str!("../docs/design/macros/fixtures/nested/outer_forms.ash");
        for transformer in [false, true] {
            nested_template(outer, transformer)
                .expect("admission must validate the fixed nested invocation without executing it");
            nested_template(
                "pub syntax declaration: (outer) $name:ident => {\n    inner $name\n    middle : Unit -> Int\n    middle () = 42\n    inner $name\n}\n",
                transformer,
            )
            .expect("each nested invocation and ordinary sibling is admitted");
        }
    }

    #[test]
    fn nested_declaration_template_rejects_malformed_siblings_and_matchers() {
        for body in [
            "bad : Int ->\n    inner $name",
            "inner $name\n    bad : Int ->",
            "inner",
            "inner 42",
            "inner $name unexpected",
            "inner $name\n    inner 42",
            "import other\n    inner $name",
            "inner $name\n    pub syntax declaration: (new) => {}",
            "inner $name\n    ;",
        ] {
            let source =
                format!("pub syntax declaration: (outer) $name:ident => {{\n    {body}\n}}\n");
            assert!(
                nested_template(&source, false).is_err(),
                "accepted {body:?}"
            );
        }
    }

    #[test]
    fn nested_declaration_template_rejects_protected_wrong_category_holes() {
        for body in [
            "inner $body",
            "$body : Unit -> Int\n    $body () = 42\n    inner $name",
            "inner $name\n    $body : Unit -> Int\n    $body () = 42",
        ] {
            let source = format!(
                "pub syntax declaration: (outer) $body:expr then $name:ident => {{\n    {body}\n}}\n"
            );
            assert!(
                matches!(
                    nested_template(&source, false),
                    Err(crate::parser::MacroParseFailure::Invalid)
                ),
                "the protected expression must fail projection in {body:?}"
            );
        }
        for (capture, body) in [
            ("T:type", "inner $T"),
            ("p:pattern", "inner $p"),
            (
                "p:pattern",
                "inner $name\n    bad : $p -> Int\n    bad _ = 42",
            ),
        ] {
            let source = format!(
                "pub syntax declaration: (outer) ${capture} then $name:ident => {{\n    {body}\n}}\n"
            );
            assert!(
                matches!(
                    nested_template(&source, false),
                    Err(crate::parser::MacroParseFailure::Syntax { .. })
                ),
                "the wrong category must fail ordinary parsing in {body:?}"
            );
        }
    }

    #[test]
    fn declaration_templates_admit_fixed_type_and_pattern_captures() {
        let declarations = include_str!("../docs/design/macros/fixtures/declarations/forms.ash");
        let types = &declarations[declarations
            .find("pub syntax declaration: (make_identity)")
            .unwrap()..];
        let forms = include_str!("../docs/design/macros/fixtures/captures/forms.ash");
        let start = forms.find("pub syntax declaration: (predicate)").unwrap();
        let end = forms
            .find("pub syntax declaration: (pass_declaration)")
            .unwrap();
        for text in [
            types,
            &forms[start..end],
            include_str!("../docs/design/macros/fixtures/captures/binder_forms.ash"),
        ] {
            let source = SourceFile::new("forms.ash", text).unwrap();
            let tree = crate::parser::parse(crate::lexer::lex(&source).unwrap());
            let module = crate::parser::project_module_retaining_templates(&source, &tree).unwrap();
            let contexts = SyntaxContexts::new(&[], &[], &[]);
            for declaration in &module.syntax_declarations {
                validate_template_syntax(declaration, &source, &contexts)
                    .expect("fixed type and pattern templates should be admitted");
            }
        }
    }

    #[test]
    fn declaration_templates_reject_wrong_capture_categories_at_definition() {
        for (text, expected) in [
            (
                "pub syntax declaration: (bad) $T:type => {\n    value : Unit -> Int\n    value $T = 42\n}\n",
                crate::parser::ExpectedForm::Pattern,
            ),
            (
                "pub syntax declaration: (bad) $p:pattern => {\n    value : $p -> Int\n    value _ = 42\n}\n",
                crate::parser::ExpectedForm::Type,
            ),
        ] {
            let source = SourceFile::new("bad.ash", text).unwrap();
            let tree = crate::parser::parse(crate::lexer::lex(&source).unwrap());
            let module = crate::parser::project_module_retaining_templates(&source, &tree).unwrap();
            let contexts = SyntaxContexts::new(&[], &[], &[]);
            let Err(crate::parser::MacroParseFailure::Syntax { diagnostics, .. }) =
                validate_template_syntax(&module.syntax_declarations[0], &source, &contexts)
            else {
                panic!("wrong-category template must fail at definition admission");
            };
            assert!(
                diagnostics
                    .iter()
                    .any(|diagnostic| diagnostic.expected_form() == Some(expected))
            );
        }
    }

    #[test]
    fn declarative_substitution_preserves_protected_type_and_pattern_captures() {
        let source = SourceFile::new("splice.ash", "capture").unwrap();
        let span = source.span(ByteRange::new(0, 7).unwrap()).unwrap();
        let name = SurfaceName {
            text: "capture".into(),
            span,
            introduction: 0,
            introduced_at: None,
            written: true,
            diagnostic: None,
        };
        let captures = [
            (
                SurfaceSyntaxCaptureKind::Type,
                SurfaceSyntaxCapture::Type(SurfaceTypeCapture {
                    ty: SurfaceType {
                        kind: SurfaceTypeKind::Int,
                        span,
                        diagnostic: None,
                    },
                    contents: Arc::from([MacroOutputNode::Token(
                        crate::lexer::TokenKind::IntType,
                        Arc::from("Int"),
                        span.into(),
                    )]),
                }),
            ),
            (
                SurfaceSyntaxCaptureKind::Pattern,
                SurfaceSyntaxCapture::Pattern(SurfacePatternCapture {
                    pattern: SurfacePattern {
                        kind: SurfacePatternKind::Wildcard,
                        span,
                        diagnostic: None,
                    },
                    contents: Arc::from([MacroOutputNode::Token(
                        crate::lexer::TokenKind::Wildcard,
                        Arc::from("_"),
                        span.into(),
                    )]),
                }),
            ),
        ];
        for (kind, capture) in captures {
            let matcher = [SurfaceSyntaxMatcherPart::Capture {
                name: name.clone(),
                kind,
            }];
            let mut output = vec![MacroOutputNode::Splice(name.clone())];
            substitute_contents(
                &mut output,
                &matcher,
                std::slice::from_ref(&capture),
                0,
                span,
            )
            .unwrap();
            match (&capture, output.as_slice()) {
                (
                    SurfaceSyntaxCapture::Type(original),
                    [MacroOutputNode::ForwardedType(actual, origin)],
                ) => {
                    assert!(Arc::ptr_eq(&original.contents, &actual.contents));
                    assert_eq!(origin.primary(), span);
                }
                (
                    SurfaceSyntaxCapture::Pattern(original),
                    [MacroOutputNode::ForwardedPattern(actual, origin)],
                ) => {
                    assert!(Arc::ptr_eq(&original.contents, &actual.contents));
                    assert_eq!(origin.primary(), span);
                }
                _ => panic!("the capture must remain a protected node of its own category"),
            }
        }
    }

    #[test]
    fn declaration_type_splices_reserve_each_owned_copy_before_substitution() {
        let source = SourceFile::new(
            "type_splices.ash",
            "pub syntax declaration: (emit) $T:type => {\n    value : $T -> $T\n    value input = input\n}\n",
        )
        .unwrap();
        let tree = crate::parser::parse(crate::lexer::lex(&source).unwrap());
        let declaration = crate::parser::project_module_retaining_templates(&source, &tree)
            .unwrap()
            .syntax_declarations
            .remove(0);
        let span = declaration.span;
        let selection = SelectedSyntax {
            name: declaration.name.text.clone(),
            import_span: span,
            declaration,
            owner: 0,
        };
        let leaf = SurfaceType {
            kind: SurfaceTypeKind::Int,
            span,
            diagnostic: None,
        };
        let small = SurfaceSyntaxCapture::Type(SurfaceTypeCapture {
            ty: leaf.clone(),
            contents: Arc::from([]),
        });
        let mut location = DiagnosticLocation::new(span.into());
        location.related.extend((0..8).map(|_| span.into()));
        location.frames.push(Arc::new(ExpansionFrame {
            invocation: span,
            definition: span,
        }));
        let large = SurfaceSyntaxCapture::Type(SurfaceTypeCapture {
            ty: SurfaceType {
                kind: SurfaceTypeKind::Tuple(vec![leaf.clone(), leaf]),
                span,
                diagnostic: Some(Box::new(location)),
            },
            contents: Arc::from([]),
        });
        let measure = |capture: &SurfaceSyntaxCapture| {
            let mut budget = crate::syntax_resource::SyntaxBudget::default();
            let output = instantiate_declaration_template(
                &selection,
                std::slice::from_ref(capture),
                1,
                span,
                &mut budget,
            )
            .expect("a protected type is permitted in the declaration template");
            assert_eq!(
                output
                    .iter()
                    .filter(|node| matches!(node, MacroOutputNode::ForwardedType(_, _)))
                    .count(),
                2
            );
            budget.consumed()
        };
        let small_cost = measure(&small);
        let large_cost = measure(&large);
        assert!(large_cost > small_cost);
        let mut short = crate::syntax_resource::SyntaxBudget::with_limit(large_cost - 1);
        assert!(matches!(
            instantiate_declaration_template(
                &selection,
                std::slice::from_ref(&large),
                1,
                span,
                &mut short,
            ),
            Err(crate::parser::MacroParseFailure::Syntax {
                resource: Some(crate::syntax_resource::ResourceFailure::SyntaxWork { .. }),
                ..
            })
        ));
        let mut exact = crate::syntax_resource::SyntaxBudget::with_limit(large_cost);
        instantiate_declaration_template(&selection, &[large], 1, span, &mut exact)
            .expect("the measured allowance covers both copies");
    }

    #[test]
    fn declaration_pattern_and_expression_splices_share_a_retryable_budget() {
        let source = SourceFile::new(
            "binder_forms.ash",
            include_str!("../docs/design/macros/fixtures/captures/binder_forms.ash"),
        )
        .unwrap();
        let tree = crate::parser::parse(crate::lexer::lex(&source).unwrap());
        let declaration = crate::parser::project_module_retaining_templates(&source, &tree)
            .unwrap()
            .syntax_declarations
            .remove(0);
        let span = declaration.span;
        let selection = SelectedSyntax {
            name: declaration.name.text.clone(),
            import_span: span,
            declaration,
            owner: 0,
        };
        let name = SurfaceName {
            text: "value".into(),
            span,
            introduction: 0,
            introduced_at: None,
            written: true,
            diagnostic: None,
        };
        let captures = [
            SurfaceSyntaxCapture::Identifier(SurfaceIdentifierCapture {
                name: name.clone(),
                origin: span.into(),
            }),
            SurfaceSyntaxCapture::Pattern(SurfacePatternCapture {
                pattern: SurfacePattern {
                    kind: SurfacePatternKind::Binder(crate::surface::SurfaceBinder {
                        name: name.clone(),
                        span,
                    }),
                    span,
                    diagnostic: None,
                },
                contents: Arc::from([]),
            }),
            SurfaceSyntaxCapture::Expression(SurfaceExpressionCapture {
                expression: SurfaceExpr {
                    kind: SurfaceExprKind::Name(SurfaceReference::Unqualified(name)),
                    span,
                    diagnostic: None,
                },
                contents: Arc::from([]),
            }),
        ];
        let mut measured = SyntaxBudget::default();
        let output =
            instantiate_declaration_template(&selection, &captures, 1, span, &mut measured)
                .expect("protected pattern and expression splices are admitted");
        assert!(
            output
                .iter()
                .any(|node| matches!(node, MacroOutputNode::ForwardedPattern(..)))
        );
        assert!(
            output
                .iter()
                .any(|node| matches!(node, MacroOutputNode::ForwardedExpression(..)))
        );
        let cost = measured.consumed();
        assert!(matches!(
            instantiate_declaration_template(
                &selection,
                &captures,
                1,
                span,
                &mut SyntaxBudget::with_limit(cost - 1),
            ),
            Err(crate::parser::MacroParseFailure::Syntax {
                resource: Some(ResourceFailure::SyntaxWork { .. }),
                ..
            })
        ));
        let retry = instantiate_declaration_template(
            &selection,
            &captures,
            1,
            span,
            &mut SyntaxBudget::with_limit(cost),
        )
        .expect("the measured allowance covers both copies on retry");
        assert_eq!(output, retry);
    }

    #[test]
    fn protected_type_work_counts_names_frames_and_each_shared_visit() {
        let source = SourceFile::new("protected.ash", "Type").unwrap();
        let span = source.span(ByteRange::new(0, 4).unwrap()).unwrap();
        let name = |text: &str, diagnostic| SurfaceName {
            text: text.into(),
            span,
            introduction: 0,
            introduced_at: None,
            written: true,
            diagnostic,
        };
        let named_type = |name| SurfaceType {
            kind: SurfaceTypeKind::Named(SurfaceReference::Unqualified(name)),
            span,
            diagnostic: None,
        };
        let mut location = DiagnosticLocation::new(span.into());
        location.related.extend((0..4).map(|_| span.into()));
        location.frames.extend((0..3).map(|_| {
            Arc::new(ExpansionFrame {
                invocation: span,
                definition: span,
            })
        }));
        let short_name = named_type(name("T", None));
        let long_name = named_type(name("LongCallerType", Some(Box::new(location))));
        let copy_cost = |ty: &SurfaceType| {
            let mut budget = SyntaxBudget::default();
            charge_type_copy(ty, 0, true, &mut budget).unwrap();
            budget.consumed()
        };
        let cost = copy_cost(&long_name);
        assert!(cost > copy_cost(&short_name));
        assert!(matches!(
            charge_type_copy(&long_name, 0, true, &mut SyntaxBudget::with_limit(cost - 1)),
            Err(ResourceFailure::SyntaxWork { .. })
        ));
        charge_type_copy(&long_name, 0, true, &mut SyntaxBudget::with_limit(cost)).unwrap();

        let inner = SurfaceTypeCapture {
            ty: short_name.clone(),
            contents: Arc::from([MacroOutputNode::Token(
                crate::lexer::TokenKind::IntType,
                Arc::from("Int"),
                span.into(),
            )]),
        };
        let outer = |copies: usize| SurfaceTypeCapture {
            ty: short_name.clone(),
            contents: (0..copies)
                .map(|_| MacroOutputNode::ForwardedType(inner.clone(), span.into()))
                .collect::<Vec<_>>()
                .into(),
        };
        let twice = outer(2);
        let [
            MacroOutputNode::ForwardedType(left, _),
            MacroOutputNode::ForwardedType(right, _),
        ] = twice.contents.as_ref()
        else {
            panic!("two forwarded captures must be retained");
        };
        assert!(Arc::ptr_eq(&left.contents, &right.contents));
        let retention_cost = |capture: &SurfaceTypeCapture| {
            let mut budget = SyntaxBudget::default();
            charge_type_retention(capture, 0, &mut budget).unwrap();
            budget.consumed()
        };
        let cost = retention_cost(&twice);
        assert!(cost > retention_cost(&outer(1)));
        assert!(matches!(
            charge_type_retention(&twice, 0, &mut SyntaxBudget::with_limit(cost - 1)),
            Err(crate::parser::MacroParseFailure::Syntax {
                resource: Some(ResourceFailure::SyntaxWork { .. }),
                ..
            })
        ));
        charge_type_retention(&twice, 0, &mut SyntaxBudget::with_limit(cost)).unwrap();
    }
}
