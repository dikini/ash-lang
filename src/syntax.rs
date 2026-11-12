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
        SurfaceDeclarationCapture, SurfaceEffectRow, SurfaceExpr, SurfaceExprKind,
        SurfaceExpressionCapture, SurfaceIdentifierCapture, SurfaceImportItem,
        SurfaceImportSelection, SurfaceMatcherContainerKind, SurfaceName, SurfacePattern,
        SurfacePatternCapture, SurfacePatternKind, SurfaceReference, SurfaceRepeatedCapture,
        SurfaceSyntaxCapture, SurfaceSyntaxCaptureKind, SurfaceSyntaxCategory,
        SurfaceSyntaxDeclaration, SurfaceSyntaxImplementation, SurfaceSyntaxMatcherPart,
        SurfaceType, SurfaceTypeCapture, SurfaceTypeKind,
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
    ForwardedDeclaration(SurfaceDeclarationCapture, MacroOrigin),
    Identifier(SurfaceName, MacroOrigin),
    Token(crate::lexer::TokenKind, Arc<str>, MacroOrigin),
    Group(MacroDelimiter, Vec<MacroOutputNode>, MacroOrigin),
    Splice(SurfaceName),
    /// A declaration-template directive, consumed before ordinary parsing.
    TemplateRepeat(Arc<TemplateRepeat>),
    /// An admitted outer escape and its checked, defining-module adapter.
    TemplateEscape(SurfaceName),
}

/// One immutable repetition in a declaration template.
#[derive(Debug, Eq, PartialEq)]
pub(crate) struct TemplateRepeat {
    pub(crate) body: Vec<MacroOutputNode>,
    pub(crate) generators: Option<Arc<[crate::surface::SurfaceTemplateGenerator]>>,
    pub(crate) separator: Option<(crate::lexer::TokenKind, Arc<str>, MacroOrigin)>,
    pub(crate) one_or_more: bool,
    pub(crate) origin: MacroOrigin,
}

/// A compiler-created call while its containing surface module is immutable.
/// The callee address is compared only while that module is borrowed; it is
/// never dereferenced or carried into a checked fragment.
#[derive(Debug, Eq, PartialEq)]
pub(crate) struct SurfaceQuoteSite {
    pub(crate) callee: usize,
    pub(crate) template: Arc<QuoteTemplate>,
}

/// Immutable compiler-owned data shared by the successive checked stages.
#[derive(Debug, Eq, PartialEq)]
pub(crate) struct QuoteTemplate {
    pub(crate) ordinal: usize,
    pub(crate) origin: Span,
    pub(crate) contents: Box<[MacroOutputNode]>,
    pub(crate) holes: usize,
}

#[derive(Debug, Eq, PartialEq)]
pub(crate) struct ResolvedQuoteSite {
    pub(crate) callee: usize,
    pub(crate) constructor: crate::types::ConstructorId,
    pub(crate) template: Arc<QuoteTemplate>,
}

/// Relocated quote IDs and the genuine checked helper/source owners.
#[derive(Debug)]
pub(crate) struct PreparedQuoteSite {
    pub(crate) nodes: crate::elaborate::CheckedQuoteSite,
    pub(crate) owner: usize,
    pub(crate) source: Arc<crate::source::SourceFile>,
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
    pub(crate) fn owner_count(&self) -> usize {
        self.owners.len()
    }

    pub(crate) fn owner_capacity(&self) -> usize {
        self.owners.capacity()
    }

    pub(crate) fn reserve_owner(&mut self) -> Result<(), ()> {
        self.owners.try_reserve_exact(1).map_err(|_| ())
    }

    pub(crate) fn push_owner(&mut self, owner: Option<usize>) {
        self.owners.push(owner);
    }
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

    pub(crate) fn new_budgeted_expression(
        caller: &[SelectedSyntax],
        owner_imports: &[Vec<SelectedSyntax>],
        owners: &[SyntaxOwner],
        budget: &mut SyntaxBudget,
    ) -> Result<Self, ResourceFailure> {
        // The mapped owner list and its copy in the contexts are separate.
        budget.charge_units(owners.len())?;
        budget.charge_units(owners.len())?;
        budget.charge_units(owner_imports.len())?;
        budget.charge_units(caller.len())?;
        for imports in owner_imports {
            budget.charge_units(imports.len())?;
        }
        for selection in caller.iter().chain(owner_imports.iter().flatten()) {
            charge_selected_expression(selection, budget)?;
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

pub(crate) fn charge_type_origin_copy(
    origin: &MacroOrigin,
    depth: usize,
    budget: &mut SyntaxBudget,
) -> Result<(), ResourceFailure> {
    charge_type_origin(origin, depth, budget)?;
    if matches!(origin, MacroOrigin::Combined { .. }) {
        // Cloning this origin retains its inputs and frame Arcs, without
        // recursively cloning the input origins.
        budget.charge_units(2)?;
    }
    Ok(())
}

fn charge_type_location(
    location: Option<&DiagnosticLocation>,
    depth: usize,
    work: TypeWork,
    budget: &mut SyntaxBudget,
) -> Result<(), ResourceFailure> {
    charge_type_location_inner(location, depth, work, false, budget)
}

fn charge_type_location_inner(
    location: Option<&DiagnosticLocation>,
    depth: usize,
    work: TypeWork,
    copy_origins: bool,
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
        if copy_origins {
            charge_type_origin_copy(&location.primary, depth, budget)?;
        } else {
            charge_type_origin(&location.primary, depth, budget)?;
        }
        for origin in &location.related {
            if copy_origins {
                charge_type_origin_copy(origin, depth, budget)?;
            } else {
                charge_type_origin(origin, depth, budget)?;
            }
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

pub(crate) fn charge_diagnostic_location_copy(
    location: &DiagnosticLocation,
    budget: &mut SyntaxBudget,
) -> Result<(), ResourceFailure> {
    charge_type_location_inner(
        Some(location),
        0,
        TypeWork::Copy {
            inherit_frame: false,
        },
        true,
        budget,
    )
}

fn charge_type_name(
    name: &SurfaceName,
    depth: usize,
    work: TypeWork,
    budget: &mut SyntaxBudget,
) -> Result<(), ResourceFailure> {
    charge_type_name_inner(name, depth, work, false, budget)
}

fn charge_type_name_inner(
    name: &SurfaceName,
    depth: usize,
    work: TypeWork,
    copy_origins: bool,
    budget: &mut SyntaxBudget,
) -> Result<(), ResourceFailure> {
    budget.charge()?;
    if matches!(work, TypeWork::Copy { .. }) {
        budget.charge()?;
        budget.charge_units(name.text.len())?;
    }
    charge_type_location_inner(
        name.diagnostic.as_deref(),
        depth,
        work,
        copy_origins,
        budget,
    )
}

pub(crate) fn charge_type_name_copy(
    name: &SurfaceName,
    depth: usize,
    budget: &mut SyntaxBudget,
) -> Result<(), ResourceFailure> {
    budget.charge_units(2)?;
    budget.charge_units(name.text.len())?;
    if let Some(location) = name.diagnostic.as_deref() {
        let depth = type_depth(depth, 1)?;
        budget.charge_units(2)?;
        budget.charge_units(location.related.len())?;
        budget.charge_units(location.frames.len())?;
        charge_type_origin_copy(&location.primary, depth, budget)?;
        for origin in &location.related {
            charge_type_origin_copy(origin, depth, budget)?;
        }
    }
    Ok(())
}

pub(crate) fn charge_type_name_inspection(
    name: &SurfaceName,
    depth: usize,
    budget: &mut SyntaxBudget,
) -> Result<(), ResourceFailure> {
    charge_type_name(name, depth, TypeWork::Inspect, budget)
}

fn charge_type_reference(
    reference: &SurfaceReference,
    depth: usize,
    work: TypeWork,
    budget: &mut SyntaxBudget,
) -> Result<(), ResourceFailure> {
    charge_type_reference_inner(reference, depth, work, false, budget)
}

fn charge_type_reference_inner(
    reference: &SurfaceReference,
    depth: usize,
    work: TypeWork,
    copy_origins: bool,
    budget: &mut SyntaxBudget,
) -> Result<(), ResourceFailure> {
    budget.charge()?;
    match reference {
        SurfaceReference::Unqualified(name) => {
            charge_type_name_inner(name, depth, work, copy_origins, budget)
        }
        SurfaceReference::Qualified(name) => {
            charge_type_name_inner(&name.qualifier, depth, work, copy_origins, budget)?;
            charge_type_name_inner(&name.member, depth, work, copy_origins, budget)
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
    charge_type_value_inner(ty, prefix, work, false, false, budget)
}

fn charge_type_value_inner(
    ty: &SurfaceType,
    prefix: usize,
    work: TypeWork,
    new_type: bool,
    later_metadata: bool,
    budget: &mut SyntaxBudget,
) -> Result<(), ResourceFailure> {
    enum Pending<'a> {
        Type(&'a SurfaceType, usize),
        Row(&'a SurfaceEffectRow, usize),
    }

    type_depth(prefix, 0)?;
    budget.charge()?;
    let mut pending = if new_type {
        budget.charge()?;
        vec![Pending::Type(ty, prefix)]
    } else {
        vec![Pending::Type(ty, prefix)]
    };
    macro_rules! reserve_pending {
        ($count:expr) => {{
            let count = $count;
            if new_type && count != 0 {
                let live = pending.len();
                let requested = live.checked_add(count).unwrap_or(usize::MAX);
                if requested > pending.capacity() {
                    budget.charge_units(requested.checked_add(live).unwrap_or(usize::MAX))?;
                    pending.reserve_exact(count);
                }
            }
        }};
    }
    let copy_origins = new_type && (later_metadata || matches!(work, TypeWork::Copy { .. }));
    while let Some(item) = pending.pop() {
        budget.charge()?;
        if later_metadata {
            // The later old Type walk and frame-inheritance walk each have a
            // 6N scratch bound on the pinned Vec growth implementation.
            budget.charge_units(12)?;
        } else if new_type
            && matches!(
                work,
                TypeWork::Copy {
                    inherit_frame: true
                }
            )
        {
            budget.charge_units(6)?;
        }
        match item {
            Pending::Type(ty, depth) => {
                if let TypeWork::Copy { inherit_frame } = work {
                    budget.charge()?;
                    if inherit_frame {
                        // The frame walk visits and retains a worklist entry.
                        budget.charge_units(2)?;
                    }
                }
                charge_type_location_inner(
                    ty.diagnostic.as_deref(),
                    depth,
                    work,
                    copy_origins,
                    budget,
                )?;
                match &ty.kind {
                    SurfaceTypeKind::Named(reference) => {
                        charge_type_reference_inner(reference, depth, work, copy_origins, budget)?;
                    }
                    SurfaceTypeKind::Application {
                        constructor,
                        arguments,
                    } => {
                        charge_type_reference_inner(
                            constructor,
                            depth,
                            work,
                            copy_origins,
                            budget,
                        )?;
                        let child_depth = type_depth(depth, 1)?;
                        if matches!(work, TypeWork::Copy { .. }) {
                            budget.charge_units(arguments.len())?;
                        }
                        budget.charge_units(arguments.len())?;
                        reserve_pending!(arguments.len());
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
                        reserve_pending!(elements.len());
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
                        reserve_pending!(1);
                        pending.push(Pending::Type(&function.domain, child_depth));
                        reserve_pending!(1);
                        pending.push(Pending::Type(&function.codomain, child_depth));
                        if let Some(row) = &function.effects {
                            budget.charge()?;
                            reserve_pending!(1);
                            pending.push(Pending::Row(row, child_depth));
                        }
                    }
                    SurfaceTypeKind::RowArgument(row) => {
                        let child_depth = type_depth(depth, 1)?;
                        budget.charge()?;
                        reserve_pending!(1);
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
                    charge_type_name_inner(tail, child_depth, work, copy_origins, budget)?;
                }
                for instance in &row.effects {
                    budget.charge()?;
                    charge_type_reference_inner(
                        &instance.effect,
                        child_depth,
                        work,
                        copy_origins,
                        budget,
                    )?;
                    if matches!(work, TypeWork::Copy { .. }) {
                        budget.charge_units(instance.arguments.len())?;
                    }
                    budget.charge_units(instance.arguments.len())?;
                    reserve_pending!(instance.arguments.len());
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

pub(crate) fn charge_new_type_copy(
    ty: &SurfaceType,
    prefix: usize,
    inherit_frame: bool,
    budget: &mut SyntaxBudget,
) -> Result<(), ResourceFailure> {
    charge_type_value_inner(
        ty,
        prefix,
        TypeWork::Copy { inherit_frame },
        true,
        false,
        budget,
    )
}

pub(crate) fn charge_transformer_type_metadata(
    ty: &SurfaceType,
    prefix: usize,
    budget: &mut SyntaxBudget,
) -> Result<(), ResourceFailure> {
    charge_type_value_inner(ty, prefix, TypeWork::Inspect, true, true, budget)
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

/// Reserve copying the location/frame produced by the first pattern projection.
fn charge_inherited_frame_copy(
    location: Option<&DiagnosticLocation>,
    depth: usize,
    frame: &Arc<ExpansionFrame>,
    budget: &mut SyntaxBudget,
) -> Result<(), ResourceFailure> {
    if let Some(location) = location {
        budget.charge_units(location.frames.len())?;
        if !location
            .frames
            .iter()
            .any(|existing| Arc::ptr_eq(existing, frame))
        {
            budget.charge()?;
        }
    } else {
        type_depth(depth, 1)?;
        // The first projection created a location, source origin and frame;
        // the scheduled clone copies all three.
        budget.charge_units(3)?;
    }
    Ok(())
}

fn charge_inherited_name_copy(
    name: &SurfaceName,
    depth: usize,
    frame: &Arc<ExpansionFrame>,
    budget: &mut SyntaxBudget,
) -> Result<(), ResourceFailure> {
    charge_inherited_frame_copy(name.diagnostic.as_deref(), depth, frame, budget)
}

fn charge_inherited_reference_copy(
    reference: &SurfaceReference,
    depth: usize,
    frame: &Arc<ExpansionFrame>,
    budget: &mut SyntaxBudget,
) -> Result<(), ResourceFailure> {
    match reference {
        SurfaceReference::Unqualified(name) => {
            charge_inherited_name_copy(name, depth, frame, budget)
        }
        SurfaceReference::Qualified(name) => {
            charge_inherited_name_copy(&name.qualifier, depth, frame, budget)?;
            charge_inherited_name_copy(&name.member, depth, frame, budget)
        }
    }
}

fn charge_pattern_frame_storage(
    location: Option<&DiagnosticLocation>,
    budget: &mut SyntaxBudget,
) -> Result<(), ResourceFailure> {
    let frames = location.map_or(0, |location| location.frames.len());
    budget.charge_units(frames.saturating_add(1).saturating_mul(6))
}

/// Reserve actual owned edges and inspect shared contents before copying.
/// The result reports an expression-syntax/host bridge found in the value;
/// callers decide whether that bridge is an execution boundary or admission.
fn charge_owned_syntax(
    root: OwnedSyntax<'_>,
    prefix: usize,
    work: TypeWork,
    copied_frame: Option<&Arc<ExpansionFrame>>,
    new_pattern: bool,
    new_expression: bool,
    budget: &mut SyntaxBudget,
) -> Result<Option<bool>, ResourceFailure> {
    use crate::surface::{SurfaceKindKind, SurfaceLocalDeclaration};

    type_depth(prefix, 0)?;
    budget.charge()?;
    let selected_owned = new_pattern || new_expression;
    let mut pending = if selected_owned {
        budget.charge()?;
        vec![(root, prefix, work)]
    } else {
        vec![(root, prefix, work)]
    };
    let mut bridge = false;
    macro_rules! push {
        ($item:expr, $depth:expr, $work:expr) => {{
            budget.charge()?;
            if selected_owned && pending.len() == pending.capacity() {
                let live = pending.len();
                let requested = live.checked_add(1).unwrap_or(usize::MAX);
                budget.charge_units(requested.checked_add(live).unwrap_or(usize::MAX))?;
                pending.reserve_exact(1);
            }
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
            selected_reference!(&$effect.effect, $depth, $work, budget)?;
            copy_entries!($effect.arguments.len(), $work);
            if !$effect.arguments.is_empty() {
                let child = type_depth($depth, 1)?;
                for argument in &$effect.arguments {
                    selected_type!(argument, child, $work, budget)?;
                }
            }
        }};
    }
    macro_rules! selected_name {
        ($name:expr, $depth:expr, $work:expr, $budget:expr $(,)?) => {{
            let work = $work;
            charge_type_name_inner(
                $name,
                $depth,
                work,
                new_expression && matches!(work, TypeWork::Copy { .. }),
                $budget,
            )
        }};
    }
    macro_rules! selected_reference {
        ($name:expr, $depth:expr, $work:expr, $budget:expr $(,)?) => {{
            let work = $work;
            if new_expression {
                charge_type_reference_inner(
                    $name,
                    $depth,
                    work,
                    matches!(work, TypeWork::Copy { .. }),
                    $budget,
                )
            } else {
                charge_type_reference($name, $depth, work, $budget)
            }
        }};
    }
    macro_rules! selected_location {
        ($location:expr, $depth:expr, $work:expr, $budget:expr $(,)?) => {{
            let work = $work;
            if new_expression {
                charge_type_location_inner(
                    $location,
                    $depth,
                    work,
                    matches!(work, TypeWork::Copy { .. }),
                    $budget,
                )
            } else {
                charge_type_location($location, $depth, work, $budget)
            }
        }};
    }
    macro_rules! selected_type {
        ($ty:expr, $depth:expr, $work:expr, $budget:expr $(,)?) => {
            charge_type_value_inner($ty, $depth, $work, new_expression, false, $budget)
        };
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
                selected_location!(expression.diagnostic.as_deref(), depth, work, budget)?;
                match &expression.kind {
                    SurfaceExprKind::TemplateSplice(name) => {
                        selected_name!(name, depth, inner_work, budget)?;
                    }
                    SurfaceExprKind::Name(reference) => {
                        selected_reference!(reference, depth, inner_work, budget)?;
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
                        selected_reference!(&value.effect, depth, inner_work, budget)?;
                        selected_name!(&value.operation, depth, inner_work, budget)?;
                        let child = type_depth(depth, 1)?;
                        copy_entries!(1 + value.arguments.len(), work);
                        push!(OwnedSyntax::Expression(&value.operand), child, inner_work);
                        for argument in &value.arguments {
                            selected_type!(argument, child, inner_work, budget)?;
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
                            selected_name!(&clause.operation, child, inner_work, budget)?;
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
                        selected_name!(&value.identity, child, inner_work, budget)?;
                        selected_name!(&value.handle, child, inner_work, budget)?;
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
                        selected_name!(&value.identity, child, inner_work, budget)?;
                        selected_name!(&value.handle, child, inner_work, budget)?;
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
                        selected_reference!(&value.family, child, inner_work, budget)?;
                        selected_name!(&value.handle, child, inner_work, budget)?;
                        if !value.arguments.is_empty() {
                            let argument_depth = type_depth(child, 1)?;
                            for argument in &value.arguments {
                                selected_type!(argument, argument_depth, inner_work, budget)?;
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
                        selected_name!(name, depth, inner_work, budget)?;
                        copy_entries!(captures.len(), work);
                        if !captures.is_empty() {
                            let child = type_depth(depth, 1)?;
                            for capture in captures {
                                match capture {
                                    SurfaceSyntaxCapture::Identifier(capture) => {
                                        selected_name!(&capture.name, child, inner_work, budget)?;
                                        if new_expression
                                            && matches!(inner_work, TypeWork::Copy { .. })
                                        {
                                            charge_type_origin_copy(
                                                &capture.origin,
                                                child,
                                                budget,
                                            )?;
                                        } else {
                                            charge_type_origin(&capture.origin, child, budget)?;
                                        }
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
                                        selected_type!(&capture.ty, child, inner_work, budget)?;
                                        contents!(capture.contents, child);
                                    }
                                    SurfaceSyntaxCapture::Declaration(_)
                                    | SurfaceSyntaxCapture::Repeated(_) => {
                                        budget.charge()?;
                                        return Ok(None);
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
                    if selected_owned {
                        // The separate mutable inheritance worklist grows at most 6N.
                        budget.charge_units(6)?;
                        charge_pattern_frame_storage(pattern.diagnostic.as_deref(), budget)?;
                    }
                }
                let copy_origins = selected_owned && matches!(work, TypeWork::Copy { .. });
                charge_type_location_inner(
                    pattern.diagnostic.as_deref(),
                    depth,
                    work,
                    copy_origins,
                    budget,
                )?;
                if let Some(frame) = copied_frame {
                    charge_inherited_frame_copy(
                        pattern.diagnostic.as_deref(),
                        depth,
                        frame,
                        budget,
                    )?;
                }
                match &pattern.kind {
                    SurfacePatternKind::TemplateSplice(name) => {
                        charge_type_name_inner(name, depth, work, copy_origins, budget)?;
                        if selected_owned
                            && matches!(
                                work,
                                TypeWork::Copy {
                                    inherit_frame: true
                                }
                            )
                        {
                            charge_pattern_frame_storage(name.diagnostic.as_deref(), budget)?;
                        }
                        if let Some(frame) = copied_frame {
                            charge_inherited_name_copy(name, depth, frame, budget)?;
                        }
                    }
                    SurfacePatternKind::Binder(binder) => {
                        charge_type_name_inner(&binder.name, depth, work, copy_origins, budget)?;
                        if selected_owned
                            && matches!(
                                work,
                                TypeWork::Copy {
                                    inherit_frame: true
                                }
                            )
                        {
                            charge_pattern_frame_storage(
                                binder.name.diagnostic.as_deref(),
                                budget,
                            )?;
                        }
                        if let Some(frame) = copied_frame {
                            charge_inherited_name_copy(&binder.name, depth, frame, budget)?;
                        }
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
                        charge_type_reference_inner(name, depth, work, copy_origins, budget)?;
                        if selected_owned
                            && matches!(
                                work,
                                TypeWork::Copy {
                                    inherit_frame: true
                                }
                            )
                        {
                            match name {
                                SurfaceReference::Unqualified(name) => {
                                    charge_pattern_frame_storage(
                                        name.diagnostic.as_deref(),
                                        budget,
                                    )?
                                }
                                SurfaceReference::Qualified(name) => {
                                    charge_pattern_frame_storage(
                                        name.qualifier.diagnostic.as_deref(),
                                        budget,
                                    )?;
                                    charge_pattern_frame_storage(
                                        name.member.diagnostic.as_deref(),
                                        budget,
                                    )?;
                                }
                            }
                        }
                        if let Some(frame) = copied_frame {
                            charge_inherited_reference_copy(name, depth, frame, budget)?;
                        }
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
                        selected_type!(annotation, child, work, budget)?;
                    }
                    push!(OwnedSyntax::Expression(&binding.initializer), child, work);
                }
                SurfaceLocalDeclaration::Evidence(evidence) => {
                    let child = type_depth(depth, 1)?;
                    copy_entries!(1, work);
                    selected_reference!(&evidence.application.interface, child, work, budget)?;
                    copy_entries!(
                        evidence.application.arguments.len() + evidence.equations.len(),
                        work
                    );
                    if !evidence.application.arguments.is_empty() || !evidence.equations.is_empty()
                    {
                        let item = type_depth(child, 1)?;
                        for argument in &evidence.application.arguments {
                            selected_type!(argument, item, work, budget)?;
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
                            selected_name!(&member.binder.name, child, work, budget)?;
                            selected_type!(&member.annotation, child, work, budget)?;
                            push!(OwnedSyntax::Expression(&member.initializer), child, work);
                        }
                    }
                }
                SurfaceLocalDeclaration::Newtype(declaration) => {
                    selected_name!(&declaration.name, depth, work, budget)?;
                    copy_entries!(
                        declaration.parameters.len() + declaration.constructors.len(),
                        work
                    );
                    if !declaration.parameters.is_empty() || !declaration.constructors.is_empty() {
                        let child = type_depth(depth, 1)?;
                        for parameter in &declaration.parameters {
                            selected_name!(&parameter.name, child, work, budget)?;
                            if let Some(kind) = &parameter.kind {
                                push!(OwnedSyntax::Kind(kind), child, work);
                            }
                        }
                        for constructor in &declaration.constructors {
                            selected_name!(&constructor.name, child, work, budget)?;
                            copy_entries!(constructor.fields.len(), work);
                            if !constructor.fields.is_empty() {
                                let field = type_depth(child, 1)?;
                                for ty in &constructor.fields {
                                    selected_type!(ty, field, work, budget)?;
                                }
                            }
                        }
                    }
                    if let Some(order) = &declaration.generated_parameters {
                        let child = type_depth(depth, 1)?;
                        budget.charge()?; // retained Arc
                        selected_name!(order.name(), child, TypeWork::Inspect, budget)?;
                        if !order.parameters().is_empty() {
                            let item = type_depth(child, 1)?;
                            for occurrence in order.parameters() {
                                selected_name!(occurrence.name(), item, TypeWork::Inspect, budget,)?;
                            }
                        }
                    }
                }
            },
            OwnedSyntax::Equation(equation) => {
                selected_name!(&equation.name, depth, work, budget)?;
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
                    if matches!(node, MacroOutputNode::Expression(..)) && !new_expression {
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
                    charge_type_value_inner(
                        &capture.ty,
                        child,
                        TypeWork::Inspect,
                        selected_owned,
                        false,
                        budget,
                    )?;
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
                MacroOutputNode::Splice(name) | MacroOutputNode::TemplateEscape(name) => {
                    bridge = true;
                    charge_type_name(name, depth, TypeWork::Inspect, budget)?;
                }
                MacroOutputNode::TemplateRepeat(_)
                | MacroOutputNode::ForwardedDeclaration(_, _) => return Ok(None),
            },
        }
    }
    Ok(Some(bridge))
}

pub(crate) fn charge_expression_copy(
    expression: &SurfaceExpr,
    prefix: usize,
    inherit_frame: bool,
    budget: &mut SyntaxBudget,
) -> Result<Option<bool>, ResourceFailure> {
    charge_owned_syntax(
        OwnedSyntax::Expression(expression),
        prefix,
        TypeWork::Copy { inherit_frame },
        None,
        false,
        false,
        budget,
    )
}

pub(crate) fn charge_pattern_copy(
    pattern: &SurfacePattern,
    prefix: usize,
    inherit_frame: bool,
    budget: &mut SyntaxBudget,
) -> Result<Option<bool>, ResourceFailure> {
    charge_owned_syntax(
        OwnedSyntax::Pattern(pattern),
        prefix,
        TypeWork::Copy { inherit_frame },
        None,
        false,
        false,
        budget,
    )
}

pub(crate) fn charge_scheduled_pattern_copy(
    pattern: &SurfacePattern,
    prefix: usize,
    frame: Option<&Arc<ExpansionFrame>>,
    budget: &mut SyntaxBudget,
) -> Result<Option<bool>, ResourceFailure> {
    charge_owned_syntax(
        OwnedSyntax::Pattern(pattern),
        prefix,
        TypeWork::Copy {
            inherit_frame: false,
        },
        frame,
        false,
        false,
        budget,
    )
}

fn charge_owned_retention(
    root: OwnedSyntax<'_>,
    contents: &[MacroOutputNode],
    prefix: usize,
    new_pattern: bool,
    new_expression: bool,
    budget: &mut SyntaxBudget,
) -> Result<Option<bool>, ResourceFailure> {
    let depth = type_depth(prefix, 1)?;
    let Some(mut bridge) = charge_owned_syntax(
        root,
        depth,
        TypeWork::Inspect,
        None,
        new_pattern,
        new_expression,
        budget,
    )?
    else {
        return Ok(None);
    };
    let contents_depth = type_depth(depth, 1)?;
    budget.charge()?; // retained contents Arc
    for node in contents {
        let Some(contents_bridge) = charge_owned_syntax(
            OwnedSyntax::Contents(node),
            contents_depth,
            TypeWork::Inspect,
            None,
            new_pattern,
            new_expression,
            budget,
        )?
        else {
            return Ok(None);
        };
        bridge |= contents_bridge;
    }
    Ok(Some(bridge))
}

pub(crate) fn charge_expression_retention(
    capture: &SurfaceExpressionCapture,
    prefix: usize,
    budget: &mut SyntaxBudget,
) -> Result<Option<bool>, ResourceFailure> {
    charge_owned_retention(
        OwnedSyntax::Expression(&capture.expression),
        &capture.contents,
        prefix,
        false,
        false,
        budget,
    )
}

pub(crate) fn charge_pattern_retention(
    capture: &SurfacePatternCapture,
    prefix: usize,
    budget: &mut SyntaxBudget,
) -> Result<Option<bool>, ResourceFailure> {
    charge_owned_retention(
        OwnedSyntax::Pattern(&capture.pattern),
        &capture.contents,
        prefix,
        false,
        false,
        budget,
    )
}

pub(crate) fn charge_new_pattern_copy(
    pattern: &SurfacePattern,
    prefix: usize,
    inherit_frame: bool,
    budget: &mut SyntaxBudget,
) -> Result<Option<bool>, ResourceFailure> {
    charge_owned_syntax(
        OwnedSyntax::Pattern(pattern),
        prefix,
        TypeWork::Copy { inherit_frame },
        None,
        true,
        false,
        budget,
    )
}

pub(crate) fn charge_new_scheduled_pattern_copy(
    pattern: &SurfacePattern,
    prefix: usize,
    frame: Option<&Arc<ExpansionFrame>>,
    budget: &mut SyntaxBudget,
) -> Result<Option<bool>, ResourceFailure> {
    charge_owned_syntax(
        OwnedSyntax::Pattern(pattern),
        prefix,
        TypeWork::Copy {
            inherit_frame: false,
        },
        frame,
        true,
        false,
        budget,
    )
}

pub(crate) fn charge_new_pattern_retention(
    capture: &SurfacePatternCapture,
    prefix: usize,
    budget: &mut SyntaxBudget,
) -> Result<Option<bool>, ResourceFailure> {
    charge_owned_retention(
        OwnedSyntax::Pattern(&capture.pattern),
        &capture.contents,
        prefix,
        true,
        false,
        budget,
    )
}

pub(crate) fn charge_new_expression_copy(
    expression: &SurfaceExpr,
    prefix: usize,
    inherit_frame: bool,
    budget: &mut SyntaxBudget,
) -> Result<Option<bool>, ResourceFailure> {
    charge_owned_syntax(
        OwnedSyntax::Expression(expression),
        prefix,
        TypeWork::Copy { inherit_frame },
        None,
        false,
        true,
        budget,
    )
}

pub(crate) fn charge_new_expression_retention(
    capture: &SurfaceExpressionCapture,
    prefix: usize,
    budget: &mut SyntaxBudget,
) -> Result<Option<bool>, ResourceFailure> {
    charge_owned_retention(
        OwnedSyntax::Expression(&capture.expression),
        &capture.contents,
        prefix,
        false,
        true,
        budget,
    )
}

/// Inspect the ownership path that remains behind a copied type capture.
pub(crate) fn charge_type_retention(
    capture: &SurfaceTypeCapture,
    prefix: usize,
    budget: &mut SyntaxBudget,
) -> Result<(), crate::parser::MacroParseFailure> {
    charge_type_retention_inner(capture, prefix, false, budget)
}

pub(crate) fn charge_new_type_retention(
    capture: &SurfaceTypeCapture,
    prefix: usize,
    budget: &mut SyntaxBudget,
) -> Result<(), crate::parser::MacroParseFailure> {
    charge_type_retention_inner(capture, prefix, true, budget)
}

fn charge_type_retention_inner(
    capture: &SurfaceTypeCapture,
    prefix: usize,
    new_type: bool,
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
    charge_type_value_inner(
        &capture.ty,
        depth,
        TypeWork::Inspect,
        new_type,
        false,
        budget,
    )
    .map_err(resource)?;
    let contents_depth = type_depth(depth, 1).map_err(resource)?;
    // Cloning the capture retains one shared contents handle.
    budget.charge().map_err(resource)?;
    budget
        .charge_units(capture.contents.len())
        .map_err(resource)?;
    if new_type && !capture.contents.is_empty() {
        budget
            .charge_units(capture.contents.len())
            .map_err(resource)?;
    }
    let mut pending = capture
        .contents
        .iter()
        .map(|node| (node, contents_depth))
        .collect::<Vec<_>>();
    macro_rules! reserve_pending {
        ($count:expr) => {{
            let count = $count;
            if new_type && count != 0 {
                let live = pending.len();
                let requested = live.checked_add(count).unwrap_or(usize::MAX);
                if requested > pending.capacity() {
                    budget
                        .charge_units(requested.checked_add(live).unwrap_or(usize::MAX))
                        .map_err(resource)?;
                    pending.reserve_exact(count);
                }
            }
        }};
    }
    while let Some((node, prefix)) = pending.pop() {
        budget.charge().map_err(resource)?;
        match node {
            MacroOutputNode::Group(_, children, origin) => {
                let depth = type_depth(prefix, 1).map_err(resource)?;
                charge_type_origin(origin, depth, budget).map_err(resource)?;
                budget.charge_units(children.len()).map_err(resource)?;
                reserve_pending!(children.len());
                pending.extend(children.iter().map(|child| (child, depth)));
            }
            MacroOutputNode::ForwardedType(capture, origin) => {
                let depth = type_depth(prefix, 1).map_err(resource)?;
                charge_type_origin(origin, depth, budget).map_err(resource)?;
                charge_type_value_inner(
                    &capture.ty,
                    depth,
                    TypeWork::Inspect,
                    new_type,
                    false,
                    budget,
                )
                .map_err(resource)?;
                let contents_depth = type_depth(depth, 1).map_err(resource)?;
                budget
                    .charge_units(capture.contents.len())
                    .map_err(resource)?;
                reserve_pending!(capture.contents.len());
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
            | MacroOutputNode::ForwardedDeclaration(_, _)
            | MacroOutputNode::Splice(_)
            | MacroOutputNode::TemplateRepeat(_)
            | MacroOutputNode::TemplateEscape(_) => return Err(MacroParseFailure::Invalid),
        }
    }
    Ok(())
}

/// Preflight and copy the owned contents made by a fragment parse service.
#[cfg(test)]
pub(crate) fn copy_fragment_output(
    output: &[MacroOutputNode],
    budget: &mut SyntaxBudget,
) -> Result<Vec<MacroOutputNode>, crate::parser::MacroParseFailure> {
    copy_fragment_output_with_type(output, budget).map(|(contents, _, _)| contents)
}

pub(crate) fn copy_fragment_output_with_type(
    output: &[MacroOutputNode],
    budget: &mut SyntaxBudget,
) -> Result<(Vec<MacroOutputNode>, bool, bool), crate::parser::MacroParseFailure> {
    use crate::parser::MacroParseFailure;

    fn resource(error: ResourceFailure) -> MacroParseFailure {
        MacroParseFailure::Syntax {
            diagnostics: Vec::new(),
            resource: Some(error),
        }
    }

    // The copied root Vec, this walk's entries, and its requested buffer.
    for _ in 0..3 {
        budget.charge_units(output.len()).map_err(resource)?;
    }
    // The returned capture owns both its AST and this contents Arc.
    let mut pending = output.iter().map(|node| (node, 2usize)).collect::<Vec<_>>();
    let mut group_count = 0usize;
    let mut group_depth = 0usize;
    let mut contains_protected_type = false;
    let mut contains_expression = false;
    while let Some((node, depth)) = pending.pop() {
        budget.charge().map_err(resource)?;
        match node {
            MacroOutputNode::Identifier(name, origin) => {
                charge_type_name_copy(name, depth, budget).map_err(resource)?;
                charge_type_origin_copy(origin, depth, budget).map_err(resource)?;
            }
            MacroOutputNode::Token(kind, _, origin) => {
                charge_type_token_copy(kind, budget).map_err(resource)?;
                budget.charge().map_err(resource)?; // spelling Arc
                charge_type_origin_copy(origin, depth, budget).map_err(resource)?;
            }
            MacroOutputNode::Group(_, children, origin) => {
                let child = type_depth(depth, 1).map_err(resource)?;
                charge_type_origin_copy(origin, child, budget).map_err(resource)?;
                group_count = group_count.saturating_add(1);
                // The copy stack holds only actual Groups, not owner layers.
                group_depth = group_depth.max(depth - 1);
                // The copied child Vec and this walk's child entries.
                budget.charge_units(children.len()).map_err(resource)?;
                budget.charge_units(children.len()).map_err(resource)?;
                let live = pending.len();
                let requested = live.saturating_add(children.len());
                if !children.is_empty() && requested > pending.capacity() {
                    budget
                        .charge_units(requested.saturating_add(live))
                        .map_err(resource)?;
                    pending.reserve_exact(children.len());
                }
                pending.extend(children.iter().map(|node| (node, child)));
            }
            MacroOutputNode::ForwardedType(capture, origin) => {
                contains_protected_type = true;
                let child = type_depth(depth, 1).map_err(resource)?;
                charge_type_origin_copy(origin, child, budget).map_err(resource)?;
                charge_new_type_copy(&capture.ty, child, false, budget).map_err(resource)?;
                charge_new_type_retention(capture, depth, budget)?;
            }
            MacroOutputNode::ForwardedPattern(capture, origin) => {
                let child = type_depth(depth, 1).map_err(resource)?;
                charge_type_origin_copy(origin, child, budget).map_err(resource)?;
                if charge_new_pattern_copy(&capture.pattern, child, false, budget)
                    .map_err(resource)?
                    != Some(false)
                    || charge_new_pattern_retention(capture, depth, budget).map_err(resource)?
                        != Some(false)
                {
                    return Err(MacroParseFailure::Invalid);
                }
            }
            MacroOutputNode::Expression(capture, origin)
            | MacroOutputNode::ForwardedExpression(capture, origin) => {
                contains_expression = true;
                contains_protected_type |= capture.contains_protected_type;
                let child = type_depth(depth, 1).map_err(resource)?;
                charge_type_origin_copy(origin, child, budget).map_err(resource)?;
                if charge_new_expression_copy(&capture.expression, child, false, budget)
                    .map_err(resource)?
                    != Some(false)
                    || charge_new_expression_retention(capture, depth, budget).map_err(resource)?
                        != Some(false)
                {
                    return Err(MacroParseFailure::Invalid);
                }
            }
            MacroOutputNode::Splice(_)
            | MacroOutputNode::ForwardedDeclaration(_, _)
            | MacroOutputNode::TemplateRepeat(_)
            | MacroOutputNode::TemplateEscape(_) => {
                return Err(MacroParseFailure::Invalid);
            }
        }
    }

    // The copied root/child Vecs were reserved above. This separate buffer
    // holds the live group continuations; pay it and their visits before any
    // owned copy so the copy has no later budget-refusal point.
    budget.charge_units(group_depth).map_err(resource)?;
    budget.charge_units(group_count).map_err(resource)?;
    struct GroupFrame<'a> {
        nodes: std::slice::Iter<'a, MacroOutputNode>,
        output: Vec<MacroOutputNode>,
        delimiter: MacroDelimiter,
        origin: &'a MacroOrigin,
    }
    let mut groups = Vec::with_capacity(group_depth);
    let mut nodes = output.iter();
    let mut copied = Vec::with_capacity(output.len());
    loop {
        match nodes.next() {
            Some(MacroOutputNode::Group(delimiter, children, origin)) => {
                let delimiter = delimiter.clone();
                let child_output = Vec::with_capacity(children.len());
                groups.push(GroupFrame {
                    nodes,
                    output: copied,
                    delimiter,
                    origin,
                });
                nodes = children.iter();
                copied = child_output;
            }
            Some(node) => copied.push(node.clone()),
            None => {
                let Some(group) = groups.pop() else {
                    return Ok((copied, contains_protected_type, contains_expression));
                };
                let node = MacroOutputNode::Group(group.delimiter, copied, group.origin.clone());
                nodes = group.nodes;
                copied = group.output;
                copied.push(node);
            }
        }
    }
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
        | MacroOutputNode::ForwardedDeclaration(_, _)
        | MacroOutputNode::Splice(_)
        | MacroOutputNode::TemplateRepeat(_)
        | MacroOutputNode::TemplateEscape(_) => return Err(MacroParseFailure::Invalid),
    }
    Ok(())
}

/// Reserve one original cloned while rebuilding expression or pattern contents.
/// Return whether its retained graph crosses an expression-syntax/host bridge.
#[cfg(test)]
pub(crate) fn charge_captured_ep_original(
    node: &MacroOutputNode,
    prefix: usize,
    budget: &mut SyntaxBudget,
) -> Result<bool, crate::parser::MacroParseFailure> {
    charge_captured_ep_original_selected(node, prefix, false, budget)
}

pub(crate) fn charge_captured_ep_original_selected(
    node: &MacroOutputNode,
    prefix: usize,
    new_expression: bool,
    budget: &mut SyntaxBudget,
) -> Result<bool, crate::parser::MacroParseFailure> {
    use crate::parser::MacroParseFailure;

    fn resource(error: ResourceFailure) -> MacroParseFailure {
        MacroParseFailure::Syntax {
            diagnostics: Vec::new(),
            resource: Some(error),
        }
    }

    let mut bridge = false;
    match node {
        MacroOutputNode::ForwardedExpression(capture, origin) => {
            let depth = type_depth(prefix, 1).map_err(resource)?;
            if new_expression {
                charge_type_origin_copy(origin, depth, budget).map_err(resource)?;
            } else {
                charge_type_origin(origin, depth, budget).map_err(resource)?;
            }
            bridge |= if new_expression {
                charge_new_expression_copy(&capture.expression, depth, false, budget)
            } else {
                charge_expression_copy(&capture.expression, depth, false, budget)
            }
            .map_err(resource)?
            .ok_or(MacroParseFailure::Invalid)?;
            bridge |= if new_expression {
                charge_new_expression_retention(capture, prefix, budget)
            } else {
                charge_expression_retention(capture, prefix, budget)
            }
            .map_err(resource)?
            .ok_or(MacroParseFailure::Invalid)?;
        }
        MacroOutputNode::ForwardedPattern(capture, origin) => {
            let depth = type_depth(prefix, 1).map_err(resource)?;
            charge_type_origin(origin, depth, budget).map_err(resource)?;
            bridge |= charge_pattern_copy(&capture.pattern, depth, false, budget)
                .map_err(resource)?
                .ok_or(MacroParseFailure::Invalid)?;
            bridge |= charge_pattern_retention(capture, prefix, budget)
                .map_err(resource)?
                .ok_or(MacroParseFailure::Invalid)?;
        }
        MacroOutputNode::ForwardedType(capture, origin) => {
            let depth = type_depth(prefix, 1).map_err(resource)?;
            if new_expression {
                charge_type_origin_copy(origin, depth, budget).map_err(resource)?;
                charge_new_type_copy(&capture.ty, depth, false, budget).map_err(resource)?;
                charge_new_type_retention(capture, prefix, budget)?;
            } else {
                charge_type_origin(origin, depth, budget).map_err(resource)?;
                charge_type_copy(&capture.ty, depth, false, budget).map_err(resource)?;
                charge_type_retention(capture, prefix, budget)?;
            }
        }
        MacroOutputNode::Identifier(name, origin) => {
            if new_expression {
                charge_type_name_copy(name, prefix, budget).map_err(resource)?;
                charge_type_origin_copy(origin, prefix, budget).map_err(resource)?;
            } else {
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
        }
        MacroOutputNode::Token(kind, _, origin) => {
            charge_type_token_copy(kind, budget).map_err(resource)?;
            budget.charge().map_err(resource)?; // retained spelling Arc
            if new_expression {
                charge_type_origin_copy(origin, prefix, budget).map_err(resource)?;
            } else {
                charge_type_origin(origin, prefix, budget).map_err(resource)?;
            }
        }
        MacroOutputNode::Group(_, _, origin) => {
            if new_expression {
                charge_type_origin_copy(origin, prefix, budget).map_err(resource)?;
            } else {
                charge_type_origin(origin, prefix, budget).map_err(resource)?;
            }
        }
        MacroOutputNode::Expression(_, _)
        | MacroOutputNode::ForwardedDeclaration(_, _)
        | MacroOutputNode::Splice(_)
        | MacroOutputNode::TemplateRepeat(_)
        | MacroOutputNode::TemplateEscape(_) => {
            return Err(MacroParseFailure::Invalid);
        }
    }
    Ok(bridge)
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
            SurfaceSyntaxMatcherPart::Container(_) => budget.charge()?,
            SurfaceSyntaxMatcherPart::LineEnd => {}
        }
    }
    if let SurfaceSyntaxImplementation::Transformer(name) = &selection.declaration.implementation {
        charge_name(name, budget)?;
    }
    if selection.declaration.template_escapes.is_some() {
        budget.charge()?;
    }
    Ok(())
}

pub(crate) fn charge_selected_expression(
    selection: &SelectedSyntax,
    budget: &mut SyntaxBudget,
) -> Result<(), ResourceFailure> {
    budget.charge()?;
    budget.charge_units(selection.name.len())?;
    charge_type_name_copy(&selection.declaration.name, 0, budget)?;
    budget.charge_units(selection.declaration.matcher.len())?;
    for part in &selection.declaration.matcher {
        match part {
            SurfaceSyntaxMatcherPart::Literal { kind, spelling } => {
                charge_type_token_copy(kind, budget)?;
                budget.charge_units(spelling.len())?;
            }
            SurfaceSyntaxMatcherPart::Capture { name, .. } => {
                charge_type_name_copy(name, 0, budget)?;
            }
            SurfaceSyntaxMatcherPart::Container(_) => budget.charge()?,
            SurfaceSyntaxMatcherPart::LineEnd => {}
        }
    }
    if selection.declaration.template_contents.is_some() {
        budget.charge()?;
    }
    if selection.declaration.template_escapes.is_some() {
        budget.charge()?;
    }
    if let SurfaceSyntaxImplementation::Transformer(name) = &selection.declaration.implementation {
        charge_type_name_copy(name, 0, budget)?;
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

#[derive(Clone, Copy, Debug)]
pub(crate) struct SyntaxOwner {
    pub(crate) owner: Option<usize>,
    pub(crate) declaration: Span,
    pub(crate) import_span: Span,
}

/// Work performed by one checked invocation adapter. State stays in Ash
/// locals; this list retains only the source binding and syntax positions.
pub(crate) enum GeneratorAction {
    Enter {
        generators: Arc<[crate::surface::SurfaceTemplateGenerator]>,
        binding: usize,
        state: usize,
        indices: Vec<usize>,
    },
    Advance {
        generators: Arc<[crate::surface::SurfaceTemplateGenerator]>,
        binding: usize,
        state: usize,
        next: usize,
        result: usize,
    },
    Escape {
        escapes: Arc<[crate::surface::SurfaceTemplateEscape]>,
        descriptor: usize,
        operands: Vec<EscapeOperand>,
        result: usize,
    },
}

pub(crate) enum EscapeOperand {
    Capture {
        slot: usize,
        kind: SurfaceSyntaxCaptureKind,
    },
    Generator {
        result: usize,
    },
}

pub(crate) struct GeneratorPlan {
    /// Every lexical clause needs a checked step shape, including when its
    /// owning repetition produces no runtime instances.
    pub(crate) shapes: Vec<(Arc<[crate::surface::SurfaceTemplateGenerator]>, usize)>,
    pub(crate) actions: Vec<GeneratorAction>,
    pub(crate) results: usize,
    /// Reached, selected leaves only; the host never opens a repeated capture.
    pub(crate) captures: Vec<SurfaceSyntaxCapture>,
}

struct ActiveGenerator {
    generators: Arc<[crate::surface::SurfaceTemplateGenerator]>,
    binding: usize,
    state: usize,
    cached: Option<usize>,
}

struct GeneratorPlanner {
    plan: GeneratorPlan,
    active: Vec<ActiveGenerator>,
    next_state: usize,
}

impl GeneratorPlanner {
    fn pay_push<T>(
        items: &mut Vec<T>,
        budget: &mut SyntaxBudget,
        span: Span,
    ) -> Result<(), TemplateSubstitutionFailure> {
        let live = items.len();
        let work = if live == items.capacity() {
            live.saturating_mul(2).saturating_add(1)
        } else {
            1
        };
        budget
            .charge_units(work)
            .map_err(|error| generator_resource(error, span))?;
        if live == items.capacity() {
            items.reserve_exact(1);
        }
        Ok(())
    }

    fn enter(
        &mut self,
        generators: &Arc<[crate::surface::SurfaceTemplateGenerator]>,
        indices: &[usize],
        budget: &mut SyntaxBudget,
    ) -> Result<(), TemplateSubstitutionFailure> {
        for (binding, item) in generators.iter().enumerate() {
            let state = self.next_state;
            self.next_state = self
                .next_state
                .checked_add(1)
                .ok_or(TemplateSubstitutionFailure::Invalid(item.span))?;
            budget
                .charge_units(indices.len().saturating_add(2))
                .map_err(|error| generator_resource(error, item.span))?;
            Self::pay_push(&mut self.plan.actions, budget, item.span)?;
            Self::pay_push(&mut self.active, budget, item.span)?;
            self.plan.actions.push(GeneratorAction::Enter {
                generators: Arc::clone(generators),
                binding,
                state,
                indices: indices.to_vec(),
            });
            self.active.push(ActiveGenerator {
                generators: Arc::clone(generators),
                binding,
                state,
                cached: None,
            });
        }
        Ok(())
    }

    fn enter_iteration(
        &mut self,
        bindings: Option<&Arc<[crate::surface::SurfaceTemplateGenerator]>>,
        indices: &[usize],
        budget: &mut SyntaxBudget,
    ) -> Result<Vec<Option<usize>>, TemplateSubstitutionFailure> {
        let span = bindings.and_then(|items| items.first()).map_or_else(
            || {
                self.active
                    .first()
                    .map(|item| item.generators[item.binding].span)
            },
            |item| Some(item.span),
        );
        if let Some(span) = span {
            budget
                .charge_units(self.active.len().saturating_mul(2))
                .map_err(|error| generator_resource(error, span))?;
        }
        let saved = self
            .active
            .iter_mut()
            .map(|item| item.cached.take())
            .collect();
        if let Some(bindings) = bindings {
            self.enter(bindings, indices, budget)?;
        }
        Ok(saved)
    }

    fn leave_iteration(&mut self, saved: Vec<Option<usize>>) {
        self.active.truncate(saved.len());
        for (item, cached) in self.active.iter_mut().zip(saved) {
            item.cached = cached;
        }
    }

    fn read_result(
        &mut self,
        name: &SurfaceName,
        budget: &mut SyntaxBudget,
    ) -> Result<Option<usize>, TemplateSubstitutionFailure> {
        let mut found = None;
        for (index, active) in self.active.iter().enumerate().rev() {
            let candidate = &active.generators[active.binding].name;
            budget
                .charge_units(name.text.len().min(candidate.text.len()).saturating_add(1))
                .map_err(|error| generator_resource(error, name.span))?;
            if name.text == candidate.text {
                found = Some(index);
                break;
            }
        }
        let Some(index) = found else {
            return Ok(None);
        };
        let result = if let Some(cached) = self.active[index].cached {
            cached
        } else {
            let next = self.next_state;
            self.next_state = self
                .next_state
                .checked_add(1)
                .ok_or(TemplateSubstitutionFailure::Invalid(name.span))?;
            let result = self.plan.results;
            self.plan.results = result
                .checked_add(1)
                .ok_or(TemplateSubstitutionFailure::Invalid(name.span))?;
            budget
                .charge()
                .map_err(|error| generator_resource(error, name.span))?;
            Self::pay_push(&mut self.plan.actions, budget, name.span)?;
            let item = &mut self.active[index];
            self.plan.actions.push(GeneratorAction::Advance {
                generators: Arc::clone(&item.generators),
                binding: item.binding,
                state: item.state,
                next,
                result,
            });
            item.state = next;
            item.cached = Some(result);
            result
        };
        Ok(Some(result))
    }

    fn marker(
        result: usize,
        name: &SurfaceName,
        budget: &mut SyntaxBudget,
    ) -> Result<MacroOutputNode, TemplateSubstitutionFailure> {
        let digits = result
            .checked_ilog10()
            .map_or(1, |value| value as usize + 1);
        budget
            .charge_units(
                "\0ash_generator_result_"
                    .len()
                    .saturating_add(digits)
                    .saturating_add(1),
            )
            .map_err(|error| generator_resource(error, name.span))?;
        let marker = SurfaceName {
            text: format!("\0ash_generator_result_{result}"),
            span: name.span,
            introduction: usize::MAX,
            introduced_at: None,
            written: false,
            diagnostic: None,
        };
        Ok(MacroOutputNode::Identifier(marker, name.span.into()))
    }

    fn read(
        &mut self,
        name: &SurfaceName,
        budget: &mut SyntaxBudget,
    ) -> Result<Option<MacroOutputNode>, TemplateSubstitutionFailure> {
        self.read_result(name, budget)?
            .map(|result| Self::marker(result, name, budget))
            .transpose()
    }

    fn escape(
        &mut self,
        name: &SurfaceName,
        escapes: &Arc<[crate::surface::SurfaceTemplateEscape]>,
        matcher: &[SurfaceSyntaxMatcherPart],
        captures: &[SurfaceSyntaxCapture],
        indices: &[usize],
        budget: &mut SyntaxBudget,
    ) -> Result<MacroOutputNode, TemplateSubstitutionFailure> {
        let fail = |error| generator_resource(error, name.span);
        let mut descriptor = None;
        for (index, escape) in escapes.iter().enumerate() {
            budget
                .charge_units(
                    name.text
                        .len()
                        .min(escape.adapter.text.len())
                        .saturating_add(1),
                )
                .map_err(fail)?;
            if name.text == escape.adapter.text {
                descriptor = Some(index);
                break;
            }
        }
        let descriptor = descriptor.ok_or(TemplateSubstitutionFailure::Invalid(name.span))?;
        let reads = &escapes[descriptor].reads;
        budget.charge_units(reads.len()).map_err(fail)?;
        let mut operands = Vec::with_capacity(reads.len());
        for read in reads.iter() {
            charge_matcher_lookup(matcher, read, 0, budget).map_err(fail)?;
            if let Some(schema) = matcher_capture_schema(matcher, read) {
                budget
                    .charge_units(indices.len().saturating_mul(3))
                    .map_err(fail)?;
                let capture = capture_by_name_at(read, matcher, captures, indices)
                    .map_err(|_| TemplateSubstitutionFailure::Invalid(read.span))?;
                match capture {
                    SurfaceSyntaxCapture::Identifier(value) => {
                        charge_type_name_copy(&value.name, 0, budget).map_err(fail)?;
                        charge_type_origin_copy(&value.origin, 0, budget).map_err(fail)?;
                    }
                    SurfaceSyntaxCapture::Expression(value) => {
                        if !matches!(value.quote_sites, crate::surface::CapturedQuoteSites::Empty)
                            || charge_new_expression_copy(&value.expression, 1, false, budget)
                                .map_err(fail)?
                                != Some(false)
                            || charge_new_expression_retention(value, 0, budget).map_err(fail)?
                                != Some(false)
                        {
                            return Err(TemplateSubstitutionFailure::Invalid(read.span));
                        }
                    }
                    SurfaceSyntaxCapture::Type(value) => {
                        charge_new_type_copy(&value.ty, 1, false, budget).map_err(fail)?;
                        charge_new_type_retention(value, 0, budget).map_err(|error| {
                            TemplateSubstitutionFailure::Syntax(read.span, error)
                        })?;
                    }
                    SurfaceSyntaxCapture::Pattern(value) => {
                        if charge_new_pattern_copy(&value.pattern, 1, false, budget)
                            .map_err(fail)?
                            != Some(false)
                            || charge_new_pattern_retention(value, 0, budget).map_err(fail)?
                                != Some(false)
                        {
                            return Err(TemplateSubstitutionFailure::Invalid(read.span));
                        }
                    }
                    SurfaceSyntaxCapture::Declaration(_) => budget.charge().map_err(fail)?,
                    SurfaceSyntaxCapture::Repeated(_) => {
                        return Err(TemplateSubstitutionFailure::Invalid(read.span));
                    }
                }
                Self::pay_push(&mut self.plan.captures, budget, read.span)?;
                let slot = self.plan.captures.len();
                self.plan.captures.push(capture.clone());
                operands.push(EscapeOperand::Capture {
                    slot,
                    kind: schema.kind,
                });
            } else {
                let result = self
                    .read_result(read, budget)?
                    .ok_or(TemplateSubstitutionFailure::Invalid(read.span))?;
                operands.push(EscapeOperand::Generator { result });
            }
        }
        let result = self.plan.results;
        self.plan.results = result
            .checked_add(1)
            .ok_or(TemplateSubstitutionFailure::Invalid(name.span))?;
        budget.charge().map_err(fail)?; // retained descriptor Arc
        Self::pay_push(&mut self.plan.actions, budget, name.span)?;
        self.plan.actions.push(GeneratorAction::Escape {
            escapes: Arc::clone(escapes),
            descriptor,
            operands,
            result,
        });
        Self::marker(result, name, budget)
    }
}

fn generator_resource(error: ResourceFailure, span: Span) -> TemplateSubstitutionFailure {
    TemplateSubstitutionFailure::Syntax(
        span,
        crate::parser::MacroParseFailure::Syntax {
            diagnostics: Vec::new(),
            resource: Some(error),
        },
    )
}

/// Construct the ordinary private entry consumed by the staged caller view.
#[allow(clippy::too_many_arguments)]
pub(crate) fn generator_adapter_definition(
    plan: &GeneratorPlan,
    escape_categories: &[Option<EscapeResultCategory>],
    matcher: &[SurfaceSyntaxMatcherPart],
    captures: &[SurfaceSyntaxCapture],
    definition_introduction: usize,
    builtin_introduction: usize,
    owners: &[SyntaxOwner],
    span: Span,
    budget: &mut SyntaxBudget,
) -> Result<(crate::surface::SurfaceDefinition, Vec<SyntaxNameUse>), crate::parser::MacroParseFailure>
{
    use crate::parser::MacroParseFailure;
    use crate::surface::*;
    let resource = |error| MacroParseFailure::Syntax {
        diagnostics: Vec::new(),
        resource: Some(error),
    };
    // Pay the generated tree, name text and its local list storage before any
    // construction; copied user syntax is charged separately below.
    budget
        .charge_units(
            plan.actions
                .len()
                .saturating_mul(512)
                .saturating_add(plan.captures.len().saturating_mul(512))
                .saturating_add(plan.shapes.len().saturating_mul(512))
                .saturating_add(plan.results.saturating_mul(256))
                .saturating_add(1024),
        )
        .map_err(resource)?;
    fn name(text: String, span: Span, introduction: usize) -> SurfaceName {
        SurfaceName {
            text,
            span,
            introduction,
            introduced_at: (introduction != 0).then_some(span),
            written: false,
            diagnostic: None,
        }
    }
    fn expr(kind: SurfaceExprKind, span: Span) -> SurfaceExpr {
        SurfaceExpr {
            kind,
            span,
            diagnostic: None,
        }
    }
    fn reference(text: String, span: Span, introduction: usize) -> SurfaceExpr {
        expr(
            SurfaceExprKind::Name(SurfaceReference::Unqualified(name(
                text,
                span,
                introduction,
            ))),
            span,
        )
    }
    fn call(function: SurfaceExpr, argument: SurfaceExpr, span: Span) -> SurfaceExpr {
        expr(
            SurfaceExprKind::Apply(ApplicationExpr {
                function: Box::new(function),
                argument: Box::new(argument),
            }),
            span,
        )
    }
    fn invoke(text: &str, introduction: usize, argument: SurfaceExpr, span: Span) -> SurfaceExpr {
        call(
            reference(text.to_owned(), span, introduction),
            argument,
            span,
        )
    }
    fn pair(first: SurfaceExpr, second: SurfaceExpr, span: Span) -> SurfaceExpr {
        expr(SurfaceExprKind::Tuple(vec![first, second]), span)
    }
    fn binder(text: String, span: Span) -> SurfacePattern {
        SurfacePattern {
            kind: SurfacePatternKind::Binder(SurfaceBinder {
                name: name(text, span, 0),
                span,
            }),
            span,
            diagnostic: None,
        }
    }
    fn local(
        pattern: SurfacePattern,
        initializer: SurfaceExpr,
        span: Span,
    ) -> SurfaceLocalDeclaration {
        SurfaceLocalDeclaration::Binding(Box::new(SurfaceBinding {
            pattern,
            annotation: None,
            initializer,
            span,
        }))
    }
    fn state(index: usize) -> String {
        format!("\0ash_generator_state_{index}")
    }
    fn value(index: usize) -> String {
        format!("\0ash_generator_value_{index}")
    }
    fn node(index: usize) -> String {
        format!("\0ash_generator_node_{index}")
    }
    fn step_reference(
        generator: &SurfaceTemplateGenerator,
        introduction: usize,
        span: Span,
        budget: &mut SyntaxBudget,
    ) -> Result<SurfaceExpr, MacroParseFailure> {
        let resource = |error| MacroParseFailure::Syntax {
            diagnostics: Vec::new(),
            resource: Some(error),
        };
        match &generator.step {
            SurfaceReference::Unqualified(name) => {
                charge_type_name_copy(name, 0, budget).map_err(resource)?;
                if let Some(location) = name.diagnostic.as_deref() {
                    budget
                        .charge_units(location.frames.len())
                        .map_err(resource)?;
                }
            }
            SurfaceReference::Qualified(qualified) => {
                charge_type_name_copy(&qualified.qualifier, 0, budget).map_err(resource)?;
                charge_type_name_copy(&qualified.member, 0, budget).map_err(resource)?;
                for name in [&qualified.qualifier, &qualified.member] {
                    if let Some(location) = name.diagnostic.as_deref() {
                        budget
                            .charge_units(location.frames.len())
                            .map_err(resource)?;
                    }
                }
            }
        }
        let mut step = generator.step.clone();
        match &mut step {
            SurfaceReference::Unqualified(name) => {
                name.introduction = introduction;
                name.introduced_at = Some(span);
                name.written = false;
            }
            SurfaceReference::Qualified(qualified) => {
                for name in [&mut qualified.qualifier, &mut qualified.member] {
                    name.introduction = introduction;
                    name.introduced_at = Some(span);
                    name.written = false;
                }
            }
        }
        // This expression is a compiler-created occurrence at the invocation;
        // the referenced names retain their defining spans and introduction.
        Ok(expr(SurfaceExprKind::Name(step), span))
    }
    fn step_shape(
        generator: &SurfaceTemplateGenerator,
        definition_introduction: usize,
        builtin_introduction: usize,
        label: &str,
        index: usize,
        seed: Option<SurfaceExpr>,
        span: Span,
        budget: &mut SyntaxBudget,
    ) -> Result<SurfaceExpr, MacroParseFailure> {
        let probe = format!("\0ash_generator_{label}_probe_{index}");
        let checked_next = format!("\0ash_generator_{label}_state_{index}");
        let checked_fragment = format!("\0ash_generator_{label}_fragment_{index}");
        let application = call(
            step_reference(generator, definition_introduction, span, budget)?,
            reference(probe.clone(), span, 0),
            span,
        );
        let checked_pattern = SurfacePattern {
            kind: SurfacePatternKind::Tuple(vec![
                binder(checked_next.clone(), span),
                binder(checked_fragment.clone(), span),
            ]),
            span,
            diagnostic: None,
        };
        let origin = invoke(
            "invocation_origin",
            builtin_introduction,
            reference("\0ash_generator_input".into(), span, 0),
            span,
        );
        let checked_node = invoke(
            "ExpressionNode",
            builtin_introduction,
            pair(reference(checked_fragment, span, 0), origin, span),
            span,
        );
        let wildcard = SurfacePattern {
            kind: SurfacePatternKind::Wildcard,
            span,
            diagnostic: None,
        };
        let checked_result = if let Some(seed) = seed {
            // The seed is checked in a never-called function and a
            // never-selected arm; its actual expression remains unchanged.
            let seed = expr(
                SurfaceExprKind::Block(SurfaceBlock {
                    declarations: Vec::new(),
                    result: Box::new(seed),
                    span,
                }),
                span,
            );
            let pattern = |value| SurfacePattern {
                kind: SurfacePatternKind::Boolean(value),
                span,
                diagnostic: None,
            };
            expr(
                SurfaceExprKind::Match(SurfaceMatchExpr {
                    scrutinee: Box::new(expr(SurfaceExprKind::Boolean(true), span)),
                    arms: vec![
                        SurfaceMatchArm {
                            pattern: pattern(true),
                            body: reference(checked_next, span, 0),
                            span,
                        },
                        SurfaceMatchArm {
                            pattern: pattern(false),
                            body: seed,
                            span,
                        },
                    ],
                }),
                span,
            )
        } else {
            reference(checked_next, span, 0)
        };
        let false_body = expr(
            SurfaceExprKind::Block(SurfaceBlock {
                declarations: vec![
                    local(checked_pattern, application, span),
                    local(wildcard, checked_node, span),
                ],
                result: Box::new(checked_result),
                span,
            }),
            span,
        );
        let boolean_pattern = |value| SurfacePattern {
            kind: SurfacePatternKind::Boolean(value),
            span,
            diagnostic: None,
        };
        let choice = expr(
            SurfaceExprKind::Match(SurfaceMatchExpr {
                scrutinee: Box::new(expr(SurfaceExprKind::Boolean(true), span)),
                arms: vec![
                    SurfaceMatchArm {
                        pattern: boolean_pattern(true),
                        body: reference(probe.clone(), span, 0),
                        span,
                    },
                    SurfaceMatchArm {
                        pattern: boolean_pattern(false),
                        body: false_body,
                        span,
                    },
                ],
            }),
            span,
        );
        Ok(expr(
            SurfaceExprKind::Function(FunctionExpr {
                parameter: binder(probe, span),
                body: SurfaceBlock {
                    declarations: Vec::new(),
                    result: Box::new(choice),
                    span,
                },
            }),
            span,
        ))
    }
    let mut declarations = Vec::with_capacity(
        plan.actions
            .len()
            .saturating_mul(2)
            .saturating_add(plan.shapes.len())
            .saturating_add(plan.results),
    );
    for (index, (generators, binding)) in plan.shapes.iter().enumerate() {
        // Checking this local function establishes the ordinary step shape.
        // Its body is never applied, including for a zero-count repetition.
        let generator = &generators[*binding];
        let candidate = match &generator.seed.kind {
            SurfaceExprKind::TemplateSplice(name) => {
                charge_matcher_lookup(matcher, name, 0, budget).map_err(resource)?;
                match capture_by_name_with_depth(name, matcher, captures, &[]) {
                    Ok((SurfaceSyntaxCapture::Expression(capture), 0))
                        if matches!(capture.quote_sites, CapturedQuoteSites::Empty) =>
                    {
                        Some(&capture.expression)
                    }
                    Ok((SurfaceSyntaxCapture::Expression(_), 0)) => None,
                    Ok((SurfaceSyntaxCapture::Repeated(_), depth)) if depth > 0 => None,
                    _ => return Err(MacroParseFailure::Invalid),
                }
            }
            SurfaceExprKind::Integer(_) | SurfaceExprKind::Boolean(_) | SurfaceExprKind::Unit => {
                Some(&generator.seed)
            }
            _ => None,
        };
        let seed = if let Some(candidate) = candidate {
            if charge_new_expression_copy(candidate, 0, false, budget)
                .map_err(resource)?
                .is_some()
            {
                // The block, match, arms and their boxed children are new.
                budget.charge_units(12).map_err(resource)?;
                Some(candidate.clone())
            } else {
                None
            }
        } else {
            None
        };
        let witness = step_shape(
            generator,
            definition_introduction,
            builtin_introduction,
            "shape",
            index,
            seed,
            span,
            budget,
        )?;
        declarations.push(local(
            binder(format!("\0ash_generator_shape_{index}"), span),
            witness,
            span,
        ));
    }
    if escape_categories.len() != plan.actions.len() {
        return Err(MacroParseFailure::Invalid);
    }
    for (action, category) in plan.actions.iter().zip(escape_categories) {
        match action {
            GeneratorAction::Enter {
                generators,
                binding,
                state: target,
                indices,
            } => {
                let generator = &generators[*binding];
                let seed = match &generator.seed.kind {
                    SurfaceExprKind::TemplateSplice(name) => {
                        charge_matcher_lookup(matcher, name, 0, budget).map_err(resource)?;
                        budget
                            .charge_units(indices.len().saturating_mul(3))
                            .map_err(resource)?;
                        let SurfaceSyntaxCapture::Expression(capture) =
                            capture_by_name_at(name, matcher, captures, indices)
                                .map_err(|_| MacroParseFailure::Invalid)?
                        else {
                            return Err(MacroParseFailure::Invalid);
                        };
                        if !matches!(capture.quote_sites, CapturedQuoteSites::Empty) {
                            return Err(MacroParseFailure::Invalid);
                        }
                        if charge_new_expression_copy(&capture.expression, 0, false, budget)
                            .map_err(resource)?
                            .is_none()
                        {
                            return Err(MacroParseFailure::Invalid);
                        }
                        capture.expression.clone()
                    }
                    SurfaceExprKind::Integer(_)
                    | SurfaceExprKind::Boolean(_)
                    | SurfaceExprKind::Unit => {
                        if charge_new_expression_copy(&generator.seed, 0, false, budget)
                            .map_err(resource)?
                            .is_none()
                        {
                            return Err(MacroParseFailure::Invalid);
                        }
                        generator.seed.clone()
                    }
                    _ => return Err(MacroParseFailure::Invalid),
                };
                // The shell is created at the invocation; the seed itself
                // keeps its original source, context and diagnostic packet.
                budget.charge_units(3).map_err(resource)?;
                let seed = expr(
                    SurfaceExprKind::Block(SurfaceBlock {
                        declarations: Vec::new(),
                        result: Box::new(seed),
                        span,
                    }),
                    span,
                );
                // Apply a separate witness to this real seed, preserving the
                // ordinary seed/input/next-state relation for each instance.
                let witness = step_shape(
                    generator,
                    definition_introduction,
                    builtin_introduction,
                    "entry",
                    *target,
                    None,
                    span,
                    budget,
                )?;
                let witness_name = format!("\0ash_generator_witness_{target}");
                declarations.push(local(binder(witness_name.clone(), span), witness, span));
                declarations.push(local(
                    binder(state(*target), span),
                    call(reference(witness_name, span, 0), seed, span),
                    span,
                ));
            }
            GeneratorAction::Advance {
                generators,
                binding,
                state: old,
                next,
                result,
            } => {
                let generator = &generators[*binding];
                let application = call(
                    step_reference(generator, definition_introduction, span, budget)?,
                    reference(state(*old), span, 0),
                    span,
                );
                let pattern = SurfacePattern {
                    kind: SurfacePatternKind::Tuple(vec![
                        binder(state(*next), span),
                        binder(value(*result), span),
                    ]),
                    span,
                    diagnostic: None,
                };
                declarations.push(local(pattern, application, span));
                let origin = invoke(
                    "invocation_origin",
                    builtin_introduction,
                    reference("\0ash_generator_input".into(), span, 0),
                    span,
                );
                let expression = invoke(
                    "ExpressionNode",
                    builtin_introduction,
                    pair(reference(value(*result), span, 0), origin, span),
                    span,
                );
                declarations.push(local(binder(node(*result), span), expression, span));
            }
            GeneratorAction::Escape {
                escapes,
                descriptor,
                operands,
                result,
            } => {
                let escape = escapes.get(*descriptor).ok_or(MacroParseFailure::Invalid)?;
                let mut arguments = Vec::with_capacity(operands.len());
                for operand in operands {
                    arguments.push(match operand {
                        EscapeOperand::Capture {
                            slot,
                            kind: SurfaceSyntaxCaptureKind::Identifier,
                        } => pair(
                            reference(format!("\0ash_capture_{slot}"), span, 0),
                            reference(format!("\0ash_capture_origin_{slot}"), span, 0),
                            span,
                        ),
                        EscapeOperand::Capture { slot, .. } => {
                            reference(format!("\0ash_capture_{slot}"), span, 0)
                        }
                        EscapeOperand::Generator { result } => reference(value(*result), span, 0),
                    });
                }
                let argument = match arguments.len() {
                    0 => expr(SurfaceExprKind::Unit, span),
                    1 => arguments.pop().ok_or(MacroParseFailure::Invalid)?,
                    _ => expr(SurfaceExprKind::Tuple(arguments), span),
                };
                let application = invoke(
                    &escape.adapter.text,
                    definition_introduction,
                    argument,
                    span,
                );
                declarations.push(local(binder(value(*result), span), application, span));
                let category = category.ok_or(MacroParseFailure::Invalid)?;
                let (constructor, fields) = if category == EscapeResultCategory::Identifier {
                    ("IdentifierNode", reference(value(*result), span, 0))
                } else {
                    let origin = invoke(
                        "invocation_origin",
                        builtin_introduction,
                        reference("\0ash_generator_input".into(), span, 0),
                        span,
                    );
                    (
                        match category {
                            EscapeResultCategory::Expression => "ExpressionNode",
                            EscapeResultCategory::Type => "TypeNode",
                            EscapeResultCategory::Pattern => "PatternNode",
                            EscapeResultCategory::Declaration => "DeclarationNode",
                            EscapeResultCategory::Identifier => unreachable!(),
                        },
                        pair(reference(value(*result), span, 0), origin, span),
                    )
                };
                let wrapped = invoke(constructor, builtin_introduction, fields, span);
                declarations.push(local(binder(node(*result), span), wrapped, span));
            }
        }
    }
    let mut nodes = reference("NoNodes".into(), span, builtin_introduction);
    for index in (0..plan.results).rev() {
        nodes = invoke(
            "MoreNodes",
            builtin_introduction,
            pair(reference(node(index), span, 0), nodes, span),
            span,
        );
    }
    let result = invoke(
        "Expanded",
        builtin_introduction,
        invoke("Syntax", builtin_introduction, nodes, span),
        span,
    );
    let mut body = expr(
        SurfaceExprKind::Block(SurfaceBlock {
            declarations,
            result: Box::new(result),
            span,
        }),
        span,
    );
    if !plan.captures.is_empty() {
        fn constructor_pattern(
            text: &str,
            payload: SurfacePattern,
            span: Span,
            introduction: usize,
        ) -> SurfacePattern {
            SurfacePattern {
                kind: SurfacePatternKind::Constructor {
                    name: SurfaceReference::Unqualified(name(text.to_owned(), span, introduction)),
                    payload: Some(Box::new(payload)),
                },
                span,
                diagnostic: None,
            }
        }
        let mut requested = Vec::with_capacity(plan.captures.len());
        let mut patterns = Vec::with_capacity(plan.captures.len());
        for (slot, capture) in plan.captures.iter().enumerate() {
            requested.push(invoke(
                "capture",
                builtin_introduction,
                pair(
                    reference("\0ash_generator_input".into(), span, 0),
                    expr(
                        SurfaceExprKind::Integer(crate::integer::Integer::from_usize(slot)),
                        span,
                    ),
                    span,
                ),
                span,
            ));
            let (constructor, payload) = match capture {
                SurfaceSyntaxCapture::Expression(_) => (
                    "ExpressionCapture",
                    binder(format!("\0ash_capture_{slot}"), span),
                ),
                SurfaceSyntaxCapture::Identifier(_) => (
                    "IdentifierCapture",
                    SurfacePattern {
                        kind: SurfacePatternKind::Tuple(vec![
                            binder(format!("\0ash_capture_{slot}"), span),
                            binder(format!("\0ash_capture_origin_{slot}"), span),
                        ]),
                        span,
                        diagnostic: None,
                    },
                ),
                SurfaceSyntaxCapture::Type(_) => {
                    ("TypeCapture", binder(format!("\0ash_capture_{slot}"), span))
                }
                SurfaceSyntaxCapture::Pattern(_) => (
                    "PatternCapture",
                    binder(format!("\0ash_capture_{slot}"), span),
                ),
                SurfaceSyntaxCapture::Declaration(_) => (
                    "DeclarationCapture",
                    binder(format!("\0ash_capture_{slot}"), span),
                ),
                SurfaceSyntaxCapture::Repeated(_) => return Err(MacroParseFailure::Invalid),
            };
            patterns.push(constructor_pattern(
                "Captured",
                constructor_pattern(constructor, payload, span, builtin_introduction),
                span,
                builtin_introduction,
            ));
        }
        let (scrutinee, pattern) = if requested.len() == 1 {
            (
                requested.pop().ok_or(MacroParseFailure::Invalid)?,
                patterns.pop().ok_or(MacroParseFailure::Invalid)?,
            )
        } else {
            (
                expr(SurfaceExprKind::Tuple(requested), span),
                SurfacePattern {
                    kind: SurfacePatternKind::Tuple(patterns),
                    span,
                    diagnostic: None,
                },
            )
        };
        let diagnostic = invoke(
            "MacroDiagnostic",
            builtin_introduction,
            expr(
                SurfaceExprKind::Tuple(vec![
                    expr(SurfaceExprKind::String("invalid capture".to_owned()), span),
                    invoke(
                        "invocation_origin",
                        builtin_introduction,
                        reference("\0ash_generator_input".into(), span, 0),
                        span,
                    ),
                    reference("NoOrigins".into(), span, builtin_introduction),
                ]),
                span,
            ),
            span,
        );
        let rejected = invoke("Rejected", builtin_introduction, diagnostic, span);
        body = expr(
            SurfaceExprKind::Match(SurfaceMatchExpr {
                scrutinee: Box::new(scrutinee),
                arms: vec![
                    SurfaceMatchArm {
                        pattern,
                        body,
                        span,
                    },
                    SurfaceMatchArm {
                        pattern: SurfacePattern {
                            kind: SurfacePatternKind::Wildcard,
                            span,
                            diagnostic: None,
                        },
                        body: rejected,
                        span,
                    },
                ],
            }),
            span,
        );
    }
    let named_type = |text: &str| SurfaceType {
        kind: SurfaceTypeKind::Named(SurfaceReference::Unqualified(name(
            text.into(),
            span,
            builtin_introduction,
        ))),
        span,
        diagnostic: None,
    };
    let annotation = SurfaceType {
        kind: SurfaceTypeKind::Function(FunctionType {
            domain: Box::new(named_type("Input")),
            codomain: Box::new(named_type("MacroResult")),
            effects: Some(SurfaceEffectRow {
                effects: vec![SurfaceEffectInstance {
                    effect: SurfaceReference::Unqualified(name(
                        "Ops".into(),
                        span,
                        builtin_introduction,
                    )),
                    arguments: Vec::new(),
                    span,
                }],
                tail: None,
                span,
            }),
        }),
        span,
        diagnostic: None,
    };
    let adapter = name("\0ash_generator_adapter".into(), span, 0);
    let definition = SurfaceDefinition {
        public: false,
        span,
        kind: SurfaceDefinitionKind::Equational(EquationalGlobal {
            interface: SurfaceExternalInterface {
                name: adapter.clone(),
                type_parameters: Some(Vec::new()),
                annotation,
                requirements: Vec::new(),
                span,
            },
            equations: vec![SurfaceEquation {
                name: adapter,
                patterns: vec![binder("\0ash_generator_input".into(), span)],
                body,
                span,
            }],
        }),
    };

    // The normal resolver already admits a slice of contextual uses together.
    // For escape-only adapters all these references are compiler-created and
    // authenticated. Generator adapters leave their user-written seeds and
    // steps in the ordinary lazy order.
    let mut uses = Vec::new();
    if plan.shapes.is_empty()
        && plan
            .actions
            .iter()
            .all(|action| matches!(action, GeneratorAction::Escape { .. }))
    {
        let mut record = |text: &str, introduction: usize| -> Result<(), MacroParseFailure> {
            let owner = introduction
                .checked_sub(1)
                .and_then(|index| owners.get(index))
                .ok_or(MacroParseFailure::Invalid)?;
            let owner_index = owner.owner.ok_or(MacroParseFailure::Invalid)?;
            let live = uses.len();
            budget
                .charge_units(text.len().saturating_add(if live == uses.capacity() {
                    live.saturating_mul(2).saturating_add(2)
                } else {
                    2
                }))
                .map_err(resource)?;
            if live == uses.capacity() {
                uses.reserve_exact(1);
            }
            uses.push(SyntaxNameUse {
                name: name(text.to_owned(), span, introduction),
                qualifier: None,
                namespace: SyntaxNameNamespace::Term,
                owner: owner_index,
                declaration: owner.declaration,
                import_span: owner.import_span,
            });
            Ok(())
        };
        for _ in &plan.captures {
            record("capture", builtin_introduction)?;
        }
        for (action, category) in plan.actions.iter().zip(escape_categories) {
            let GeneratorAction::Escape {
                escapes,
                descriptor,
                ..
            } = action
            else {
                return Err(MacroParseFailure::Invalid);
            };
            let escape = escapes.get(*descriptor).ok_or(MacroParseFailure::Invalid)?;
            record(&escape.adapter.text, definition_introduction)?;
            if *category != Some(EscapeResultCategory::Identifier) {
                record("invocation_origin", builtin_introduction)?;
            }
        }
        if !plan.captures.is_empty() {
            record("invocation_origin", builtin_introduction)?;
        }
    }
    Ok((definition, uses))
}

pub(crate) enum DeclarationAdapter<'a> {
    Transformer,
    Escape(&'a SurfaceName),
    Generators(&'a GeneratorPlan),
}

pub(crate) type DeclarationTransformer<'a> = dyn for<'call> FnMut(
        &'call SelectedSyntax,
        DeclarationAdapter<'call>,
        &'call [SurfaceSyntaxCapture],
        &'call crate::source::SourceFile,
        &'call SurfaceName,
        usize,
        Arc<SyntaxContexts>,
        Arc<ExpansionFrame>,
        &'call mut Vec<SyntaxOwner>,
        &'call mut crate::syntax_resource::SyntaxBudget,
    ) -> Result<(Vec<MacroOutputNode>, usize), Span>
    + 'a;

pub(crate) struct ExpandedExpression {
    pub(crate) expression: SurfaceExpr,
    pub(crate) quote_sites: Vec<SurfaceQuoteSite>,
}

pub(crate) struct QuoteExpansionLoan<'a> {
    pub(crate) budget: &'a mut SyntaxBudget,
    pub(crate) owners: &'a mut Vec<SyntaxOwner>,
    pub(crate) next_quote_ordinal: &'a mut usize,
    pub(crate) quote_introduction: usize,
}

pub(crate) fn has_quoted_capture(captures: &[SurfaceSyntaxCapture]) -> bool {
    captures.iter().any(|capture| {
        matches!(capture, SurfaceSyntaxCapture::Expression(value)
            if !matches!(value.quote_sites, crate::surface::CapturedQuoteSites::Empty))
    })
}

type SyntaxTransformer<'a> = dyn for<'call> FnMut(
        &SelectedSyntax,
        &[SurfaceSyntaxCapture],
        Span,
        &SurfaceName,
        usize,
        &[Option<usize>],
        &Arc<ExpansionFrame>,
        &mut crate::interface::InterfaceConstraintBudget,
        Option<QuoteExpansionLoan<'call>>,
    ) -> Result<(ExpandedExpression, usize), Span>
    + 'a;

/// Expands one invocation while the ordinary resolver owns its lexical scope.
pub(crate) struct SyntaxExpansion<'a> {
    source: &'a crate::source::SourceFile,
    selected: &'a [SelectedSyntax],
    owner_imports: &'a [Vec<SelectedSyntax>],
    owners: Vec<SyntaxOwner>,
    parse_failure: Option<crate::driver::SyntaxParseFailure>,
    syntax_budget: Option<&'a mut SyntaxBudget>,
    next_quote_ordinal: Option<&'a mut usize>,
    quote_introduction: Option<usize>,
    transformer: &'a mut SyntaxTransformer<'a>,
}

impl<'a> SyntaxExpansion<'a> {
    pub(crate) fn new(
        source: &'a crate::source::SourceFile,
        selected: &'a [SelectedSyntax],
        owner_imports: &'a [Vec<SelectedSyntax>],
        owners: Vec<SyntaxOwner>,
        syntax_budget: Option<&'a mut SyntaxBudget>,
        quote_source: Option<(&'a mut usize, usize)>,
        transformer: &'a mut SyntaxTransformer<'a>,
    ) -> Self {
        let (next_quote_ordinal, quote_introduction) = match quote_source {
            Some((ordinal, introduction)) => (Some(ordinal), Some(introduction)),
            None => (None, None),
        };
        Self {
            source,
            selected,
            owner_imports,
            owners,
            parse_failure: None,
            syntax_budget,
            next_quote_ordinal,
            quote_introduction,
            transformer,
        }
    }

    pub(crate) fn take_parse_failure(&mut self) -> Option<crate::driver::SyntaxParseFailure> {
        self.parse_failure.take()
    }

    pub(crate) fn charge_quote_work(&mut self, units: usize, span: Span) -> Result<(), ()> {
        let budget = self.syntax_budget.as_deref_mut().ok_or(())?;
        if let Err(resource) = budget.charge_units(units) {
            self.parse_failure = Some(crate::driver::SyntaxParseFailure {
                diagnostics: Vec::new(),
                resource: Some(resource),
                invocation: span,
                definition: span,
                teardown: None,
            });
            return Err(());
        }
        Ok(())
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

    fn quote_selection_index(
        &mut self,
        name: &SurfaceName,
        captures: &[SurfaceSyntaxCapture],
        invocation: Span,
    ) -> Result<Option<(Option<usize>, usize)>, ()> {
        // Protected-Type projection already reserved this future lookup.
        let prepaid = captures.iter().any(|capture| {
            matches!(capture, SurfaceSyntaxCapture::Expression(value) if value.contains_protected_type)
        });
        if !prepaid {
            self.charge_quote_work(2, invocation)?;
        }
        let owner = if name.introduction == 0 {
            None
        } else {
            let Some(owner) = self.owner(name.introduction).and_then(|owner| owner.owner) else {
                return Ok(None);
            };
            Some(owner)
        };
        let count = match owner {
            None => self.selected.len(),
            Some(owner) => match self.owner_imports.get(owner) {
                Some(imports) => imports.len(),
                None => return Ok(None),
            },
        };
        for index in 0..count {
            let candidate = match owner {
                None => &self.selected[index],
                Some(owner) => &self.owner_imports[owner][index],
            };
            let work = candidate.name.len().min(name.text.len()).saturating_add(1);
            if !prepaid {
                self.charge_quote_work(work, invocation)?;
            }
            let candidate = match owner {
                None => &self.selected[index],
                Some(owner) => &self.owner_imports[owner][index],
            };
            if candidate.name == name.text {
                return Ok(Some((owner, index)));
            }
        }
        Ok(None)
    }

    pub(crate) fn quoted_selection_span(
        &mut self,
        name: &SurfaceName,
        captures: &[SurfaceSyntaxCapture],
        invocation: Span,
    ) -> Result<Option<Span>, ()> {
        let Some((owner, index)) = self.quote_selection_index(name, captures, invocation)? else {
            return Ok(None);
        };
        Ok(Some(match owner {
            None => self.selected[index].declaration.span,
            Some(owner) => self.owner_imports[owner][index].declaration.span,
        }))
    }

    pub(crate) fn expand(
        &mut self,
        name: &SurfaceName,
        captures: &[SurfaceSyntaxCapture],
        invocation: Span,
        constraint_work: &mut crate::interface::InterfaceConstraintBudget,
    ) -> Result<ExpandedExpression, Span> {
        if has_quoted_capture(captures) {
            return self.expand_quote_expression(name, captures, invocation, constraint_work);
        }
        if captures.iter().any(|capture| {
            matches!(capture, SurfaceSyntaxCapture::Expression(value) if value.contains_protected_type)
        }) {
            return self.expand_type_expression(name, captures, invocation).map(|expression| {
                ExpandedExpression { expression, quote_sites: Vec::new() }
            });
        }
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
                if let Err(failure) = substitute_contents(
                    &mut contents,
                    &selection.declaration.matcher,
                    captures,
                    introduction,
                    anchor,
                    None,
                ) {
                    let span = failure.span();
                    if let crate::parser::MacroParseFailure::Syntax {
                        diagnostics,
                        resource,
                    } = failure.into_macro_failure()
                    {
                        self.parse_failure = Some(crate::driver::SyntaxParseFailure {
                            diagnostics,
                            resource,
                            invocation: anchor,
                            definition: selection.declaration.span,
                            teardown: None,
                        });
                    }
                    return Err(span);
                }
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
                (
                    ExpandedExpression {
                        expression,
                        quote_sites: Vec::new(),
                    },
                    0,
                )
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
                None,
            )?,
        };
        self.owners.extend((0..fresh_count).map(|_| SyntaxOwner {
            owner: None,
            declaration: selection.declaration.span,
            import_span: selection.import_span,
        }));
        expression.expression.span = invocation;
        Ok(expression)
    }

    fn expand_quote_expression(
        &mut self,
        name: &SurfaceName,
        captures: &[SurfaceSyntaxCapture],
        invocation: Span,
        constraint_work: &mut crate::interface::InterfaceConstraintBudget,
    ) -> Result<ExpandedExpression, Span> {
        let (owner, index) = self
            .quote_selection_index(name, captures, invocation)
            .map_err(|()| invocation)?
            .ok_or(invocation)?;
        let selection = match owner {
            None => &self.selected[index],
            Some(owner) => &self.owner_imports[owner][index],
        };
        if !matches!(
            selection.declaration.implementation,
            SurfaceSyntaxImplementation::Transformer(_)
        ) {
            return Err(invocation);
        }
        let anchor = name.introduced_at.unwrap_or(invocation);
        let definition = selection.declaration.span;
        let Some(budget) = self.syntax_budget.as_deref_mut() else {
            return Err(invocation);
        };
        let Some(next_quote_ordinal) = self.next_quote_ordinal.as_deref_mut() else {
            return Err(invocation);
        };
        let Some(quote_introduction) = self.quote_introduction else {
            return Err(invocation);
        };
        let owner_checkpoint = self.owners.len();
        let result = (|| {
            let charged = || crate::driver::SyntaxParseFailure {
                diagnostics: Vec::new(),
                resource: None,
                invocation: anchor,
                definition,
                teardown: None,
            };
            let pay = |resource| crate::driver::SyntaxParseFailure {
                resource: Some(resource),
                ..charged()
            };
            budget.charge_units(captures.len()).map_err(pay)?;
            charge_selected_expression(selection, budget).map_err(pay)?;
            let selection = selection.clone();
            budget.charge().map_err(pay)?;
            if self.owners.len() == self.owners.capacity() {
                let live = self.owners.len();
                budget
                    .charge_units(live.saturating_mul(2).saturating_add(1))
                    .map_err(pay)?;
                self.owners.reserve_exact(1);
            }
            self.owners.push(SyntaxOwner {
                owner: Some(selection.owner),
                declaration: definition,
                import_span: selection.import_span,
            });
            let introduction = self.owners.len();
            budget.charge().map_err(pay)?;
            let frame = Arc::new(ExpansionFrame {
                invocation: anchor,
                definition,
            });
            budget.charge_units(self.owners.len()).map_err(pay)?;
            let owners = self
                .owners
                .iter()
                .map(|owner| owner.owner)
                .collect::<Vec<_>>();
            let (mut expression, fresh_count) = (self.transformer)(
                &selection,
                captures,
                anchor,
                name,
                introduction,
                &owners,
                &frame,
                constraint_work,
                Some(QuoteExpansionLoan {
                    budget,
                    owners: &mut self.owners,
                    next_quote_ordinal,
                    quote_introduction,
                }),
            )
            .map_err(|_| charged())?;
            if fresh_count != 0 {
                return Err(charged());
            }
            expression.expression.span = invocation;
            Ok(expression)
        })();
        match result {
            Ok(expression) => Ok(expression),
            Err(failure) => {
                self.owners.truncate(owner_checkpoint);
                if failure.resource.is_some() {
                    self.parse_failure = Some(failure);
                }
                Err(invocation)
            }
        }
    }

    fn expand_type_expression(
        &mut self,
        name: &SurfaceName,
        captures: &[SurfaceSyntaxCapture],
        invocation: Span,
    ) -> Result<SurfaceExpr, Span> {
        use crate::parser::MacroParseFailure;

        // This lookup was reserved when the marked invocation was projected.
        let imports = if name.introduction == 0 {
            self.selected
        } else {
            let owner = self
                .owners
                .get(name.introduction.checked_sub(1).ok_or(invocation)?)
                .and_then(|owner| owner.owner)
                .ok_or(invocation)?;
            self.owner_imports.get(owner).ok_or(invocation)?
        };
        let selection = imports
            .iter()
            .find(|selection| selection.name == name.text)
            .ok_or(invocation)?;
        if selection.declaration.category != SurfaceSyntaxCategory::Expression
            || !matches!(
                selection.declaration.implementation,
                SurfaceSyntaxImplementation::Template
            )
        {
            return Err(invocation);
        }
        let definition = selection.declaration.span;
        let anchor = name.introduced_at.unwrap_or(invocation);
        let Some(budget) = self.syntax_budget.as_deref_mut() else {
            return Err(invocation);
        };
        let resource = |resource| MacroParseFailure::Syntax {
            diagnostics: Vec::new(),
            resource: Some(resource),
        };
        let result = (|| -> Result<SurfaceExpr, MacroParseFailure> {
            charge_selected_expression(selection, budget).map_err(resource)?;
            let selection = selection.clone();
            budget.charge().map_err(resource)?;
            if self.owners.len() == self.owners.capacity() {
                let live = self.owners.len();
                let requested = live.saturating_add(1);
                budget
                    .charge_units(requested.saturating_add(live))
                    .map_err(resource)?;
                self.owners.reserve_exact(1);
            }
            self.owners.push(SyntaxOwner {
                owner: Some(selection.owner),
                declaration: definition,
                import_span: selection.import_span,
            });
            let introduction = self.owners.len();
            budget.charge().map_err(resource)?;
            let frame = Arc::new(ExpansionFrame {
                invocation: anchor,
                definition,
            });
            let template = selection
                .declaration
                .template_contents
                .as_deref()
                .ok_or(MacroParseFailure::Invalid)?;
            if charge_template_inner(
                template,
                &selection.declaration.matcher,
                captures,
                true,
                None,
                &[],
                None,
                budget,
            )? {
                return Err(MacroParseFailure::Invalid);
            }
            let mut contents = template.to_vec();
            substitute_contents(
                &mut contents,
                &selection.declaration.matcher,
                captures,
                introduction,
                anchor,
                Some(&mut *budget),
            )
            .map_err(TemplateSubstitutionFailure::into_macro_failure)?;
            let contexts = SyntaxContexts::new_budgeted_expression(
                self.selected,
                self.owner_imports,
                &self.owners,
                budget,
            )
            .map_err(resource)?;
            let mut expression = crate::parser::parse_macro_expression_budgeted(
                self.source,
                anchor,
                Some((definition, introduction)),
                contents,
                &contexts,
                Some(&frame),
                budget,
            )?;
            expression.span = invocation;
            Ok(expression)
        })();
        match result {
            Ok(expression) => Ok(expression),
            Err(MacroParseFailure::Syntax {
                diagnostics,
                resource,
            }) => {
                self.parse_failure = Some(crate::driver::SyntaxParseFailure {
                    diagnostics,
                    resource,
                    invocation: anchor,
                    definition,
                    teardown: None,
                });
                Err(invocation)
            }
            Err(MacroParseFailure::Invalid) => Err(invocation),
        }
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
                .filter(|edge| !edge.is_compiler_private()),
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
    let mut admission_budget = (declaration.category
        != crate::surface::SurfaceSyntaxCategory::Expression)
        .then(SyntaxBudget::default);
    validate_template_syntax_inner(declaration, source, contexts, admission_budget.as_mut())
}

/// Use the graph ledger for newly admitted quotation work, preserving the
/// previous admission allowance for templates without quotes or escapes.
pub(crate) fn validate_quote_template_syntax(
    declaration: &SurfaceSyntaxDeclaration,
    source: &crate::source::SourceFile,
    contexts: &SyntaxContexts,
    budget: &mut SyntaxBudget,
) -> Result<(), crate::parser::MacroParseFailure> {
    validate_template_syntax_inner(declaration, source, contexts, Some(budget))
}

// Admission uses identifier placeholders solely to check the surrounding
// declaration grammar. Generator values themselves are produced later by
// the checked invocation adapter, and never drive a repetition.
fn generator_admission_matcher(
    declaration: &SurfaceSyntaxDeclaration,
    template: &[MacroOutputNode],
    captures: &mut Vec<SurfaceSyntaxCapture>,
    identifiers: &mut Vec<SurfaceName>,
    budget: &mut SyntaxBudget,
) -> Result<Vec<SurfaceSyntaxMatcherPart>, crate::parser::MacroParseFailure> {
    use crate::parser::MacroParseFailure;
    use crate::surface::SurfaceTemplateGenerator;

    fn resource(error: ResourceFailure) -> MacroParseFailure {
        MacroParseFailure::Syntax {
            diagnostics: Vec::new(),
            resource: Some(error),
        }
    }

    fn charge_name_copy(
        name: &SurfaceName,
        budget: &mut SyntaxBudget,
    ) -> Result<(), ResourceFailure> {
        charge_type_name_copy(name, 0, budget)?;
        if let Some(location) = name.diagnostic.as_deref() {
            budget.charge_units(location.frames.len())?;
        }
        Ok(())
    }

    fn charge_duplicate(
        name: &SurfaceName,
        budget: &mut SyntaxBudget,
    ) -> Result<(), MacroParseFailure> {
        budget
            .charge_units(crate::parser::duplicate_template_binding_work(name))
            .map_err(resource)?;
        if let Some(location) = name.diagnostic.as_deref() {
            charge_diagnostic_location_copy(location, budget).map_err(resource)?;
            budget
                .charge_units(location.frames.len())
                .map_err(resource)?;
        }
        Ok(())
    }

    fn append<'a>(
        bindings: &'a [SurfaceTemplateGenerator],
        matcher: &[SurfaceSyntaxMatcherPart],
        all: &mut Vec<&'a SurfaceTemplateGenerator>,
        budget: &mut SyntaxBudget,
    ) -> Result<(), MacroParseFailure> {
        for binding in bindings {
            charge_matcher_lookup(matcher, &binding.name, 0, budget).map_err(resource)?;
            if !matches!(
                capture_by_name_at(&binding.name, matcher, &[], &[]),
                Err(CaptureLookupFailure::Unknown(_))
            ) {
                charge_duplicate(&binding.name, budget)?;
                return Err(crate::parser::duplicate_template_binding(&binding.name));
            }
            for prior in all.iter() {
                budget
                    .charge_units(
                        binding
                            .name
                            .text
                            .len()
                            .min(prior.name.text.len())
                            .saturating_add(1),
                    )
                    .map_err(resource)?;
                if prior.name.text == binding.name.text {
                    charge_duplicate(&binding.name, budget)?;
                    return Err(crate::parser::duplicate_template_binding(&binding.name));
                }
            }
            if all.len() == all.capacity() {
                budget
                    .charge_units(all.len().saturating_mul(2).saturating_add(1))
                    .map_err(resource)?;
                all.reserve_exact(1);
            } else {
                budget.charge().map_err(resource)?;
            }
            all.push(binding);
        }
        Ok(())
    }

    fn collect<'a>(
        nodes: &'a [MacroOutputNode],
        matcher: &[SurfaceSyntaxMatcherPart],
        all: &mut Vec<&'a SurfaceTemplateGenerator>,
        depth: usize,
        budget: &mut SyntaxBudget,
    ) -> Result<(), MacroParseFailure> {
        for node in nodes {
            budget.charge().map_err(resource)?;
            match node {
                MacroOutputNode::Group(_, children, _) => {
                    collect(
                        children,
                        matcher,
                        all,
                        type_depth(depth, 1).map_err(resource)?,
                        budget,
                    )?;
                }
                MacroOutputNode::TemplateRepeat(repeat) => {
                    if let Some(bindings) = &repeat.generators {
                        append(bindings, matcher, all, budget)?;
                    }
                    collect(
                        &repeat.body,
                        matcher,
                        all,
                        type_depth(depth, 1).map_err(resource)?,
                        budget,
                    )?;
                }
                _ => {}
            }
        }
        Ok(())
    }

    fn scopes<'a>(
        nodes: &'a [MacroOutputNode],
        all: &[&SurfaceTemplateGenerator],
        active: &mut Vec<&'a SurfaceTemplateGenerator>,
        depth: usize,
        budget: &mut SyntaxBudget,
    ) -> Result<(), MacroParseFailure> {
        for node in nodes {
            budget.charge().map_err(resource)?;
            match node {
                MacroOutputNode::Splice(name) => {
                    let mut generator = false;
                    for candidate in all {
                        budget
                            .charge_units(
                                name.text
                                    .len()
                                    .min(candidate.name.text.len())
                                    .saturating_add(1),
                            )
                            .map_err(resource)?;
                        if name.text == candidate.name.text {
                            generator = true;
                            break;
                        }
                    }
                    if generator {
                        let mut visible = false;
                        for candidate in active.iter() {
                            budget
                                .charge_units(
                                    name.text
                                        .len()
                                        .min(candidate.name.text.len())
                                        .saturating_add(1),
                                )
                                .map_err(resource)?;
                            if name.text == candidate.name.text {
                                visible = true;
                                break;
                            }
                        }
                        if !visible {
                            return Err(unknown_capture_failure(name, Some(budget)));
                        }
                    }
                }
                MacroOutputNode::Group(_, children, _) => {
                    scopes(
                        children,
                        all,
                        active,
                        type_depth(depth, 1).map_err(resource)?,
                        budget,
                    )?;
                }
                MacroOutputNode::TemplateRepeat(repeat) => {
                    let original = active.len();
                    if let Some(bindings) = &repeat.generators {
                        let requested = original.saturating_add(bindings.len());
                        budget.charge_units(bindings.len()).map_err(resource)?;
                        if requested > active.capacity() {
                            budget
                                .charge_units(requested.saturating_add(original))
                                .map_err(resource)?;
                            active.reserve_exact(bindings.len());
                        }
                        active.extend(bindings.iter());
                    }
                    scopes(
                        &repeat.body,
                        all,
                        active,
                        type_depth(depth, 1).map_err(resource)?,
                        budget,
                    )?;
                    active.truncate(original);
                }
                _ => {}
            }
        }
        Ok(())
    }

    let mut all = Vec::new();
    if let Some(bindings) = &declaration.generators {
        append(bindings, &declaration.matcher, &mut all, budget)?;
    }
    collect(template, &declaration.matcher, &mut all, 0, budget)?;
    let initial = declaration.generators.as_deref().unwrap_or(&[]);
    budget
        .charge_units(initial.len().saturating_mul(2))
        .map_err(resource)?;
    let mut active = initial.iter().collect::<Vec<_>>();
    scopes(template, &all, &mut active, 0, budget)?;

    // Copy the matcher only for a generator-bearing template. The appended
    // placeholders use the existing capture/substitution admission path.
    let capacity = declaration.matcher.len().saturating_add(all.len());
    budget.charge_units(capacity).map_err(resource)?;
    for part in &declaration.matcher {
        match part {
            SurfaceSyntaxMatcherPart::Literal { kind, spelling } => {
                charge_type_token_copy(kind, budget).map_err(resource)?;
                budget.charge_units(spelling.len()).map_err(resource)?;
            }
            SurfaceSyntaxMatcherPart::Capture { name, .. } => {
                charge_name_copy(name, budget).map_err(resource)?
            }
            SurfaceSyntaxMatcherPart::Container(_) => budget.charge().map_err(resource)?,
            SurfaceSyntaxMatcherPart::LineEnd => {}
        }
    }
    let mut matcher = Vec::with_capacity(capacity);
    matcher.extend_from_slice(&declaration.matcher);
    for binding in all {
        charge_name_copy(&binding.name, budget).map_err(resource)?;
        let index = identifiers.len();
        let digits = index.checked_ilog10().map_or(1, |n| n as usize + 1);
        let bytes = "__ash_generator_admission_".len().saturating_add(digits);
        budget
            .charge_units(bytes.saturating_mul(2).saturating_add(3))
            .map_err(resource)?;
        for (len, capacity) in [
            (captures.len(), captures.capacity()),
            (identifiers.len(), identifiers.capacity()),
        ] {
            if len == capacity {
                budget
                    .charge_units(len.saturating_mul(2).saturating_add(1))
                    .map_err(resource)?;
            } else {
                budget.charge().map_err(resource)?;
            }
        }
        captures.reserve_exact(1);
        identifiers.reserve_exact(1);
        let placeholder = SurfaceName {
            text: format!("__ash_generator_admission_{index}"),
            span: binding.name.span,
            introduction: usize::MAX
                .checked_sub(index)
                .ok_or(MacroParseFailure::Invalid)?,
            introduced_at: Some(binding.name.span),
            written: false,
            diagnostic: None,
        };
        matcher.push(SurfaceSyntaxMatcherPart::Capture {
            name: binding.name.clone(),
            kind: SurfaceSyntaxCaptureKind::Identifier,
        });
        identifiers.push(placeholder.clone());
        captures.push(SurfaceSyntaxCapture::Identifier(SurfaceIdentifierCapture {
            origin: placeholder.span.into(),
            name: placeholder,
        }));
    }
    Ok(matcher)
}

fn validate_template_syntax_inner(
    declaration: &SurfaceSyntaxDeclaration,
    source: &crate::source::SourceFile,
    contexts: &SyntaxContexts,
    mut admission_budget: Option<&mut SyntaxBudget>,
) -> Result<(), crate::parser::MacroParseFailure> {
    use crate::parser::MacroParseFailure;

    fn resource(error: ResourceFailure) -> MacroParseFailure {
        MacroParseFailure::Syntax {
            diagnostics: Vec::new(),
            resource: Some(error),
        }
    }

    let SurfaceSyntaxImplementation::Template = &declaration.implementation else {
        return Ok(());
    };
    fn placeholders(
        matcher: &[SurfaceSyntaxMatcherPart],
        depth: usize,
        repetitions: usize,
        declaration_output: bool,
        captures: &mut Vec<SurfaceSyntaxCapture>,
        identifiers: &mut Vec<SurfaceName>,
        budget: &mut Option<&mut SyntaxBudget>,
    ) -> Result<(), MacroParseFailure> {
        // A matcher alternates repeat and group containers, so recursion here
        // consumes two Rust frames for each user-visible repetition level.
        // Keep the walk in matcher order while charging its owned stack before
        // each allocation and entry.
        if let Some(budget) = budget.as_deref_mut() {
            budget.charge_units(2).map_err(resource)?;
        }
        let mut pending = Vec::with_capacity(1);
        pending.push((matcher.iter(), depth, repetitions));
        while let Some((parts, depth, repetitions)) = pending.last_mut() {
            let Some(part) = parts.next() else {
                pending.pop();
                continue;
            };
            let (depth, repetitions) = (*depth, *repetitions);
            if let Some(budget) = budget.as_deref_mut() {
                budget.charge().map_err(resource)?;
            }
            let (name, kind) = match part {
                SurfaceSyntaxMatcherPart::Capture { name, kind } => {
                    if !declaration_output && *kind == SurfaceSyntaxCaptureKind::Declaration {
                        return Err(MacroParseFailure::Invalid);
                    }
                    (name, kind)
                }
                SurfaceSyntaxMatcherPart::Container(container) => {
                    if !declaration_output {
                        return Err(MacroParseFailure::Invalid);
                    }
                    let next = type_depth(depth, 1).map_err(resource)?;
                    if let Some(budget) = budget.as_deref_mut() {
                        // Pay the entry's eventual inspection/pop and, when
                        // necessary, the new slot and all moved live entries.
                        budget.charge().map_err(resource)?;
                        if pending.len() == pending.capacity() {
                            budget
                                .charge_units(pending.len().saturating_mul(2).saturating_add(1))
                                .map_err(resource)?;
                            pending.reserve_exact(1);
                        }
                    }
                    pending.push((
                        container.body.iter(),
                        next,
                        repetitions
                            + usize::from(matches!(
                                &container.kind,
                                SurfaceMatcherContainerKind::Repeat { .. }
                            )),
                    ));
                    continue;
                }
                SurfaceSyntaxMatcherPart::Literal { .. } | SurfaceSyntaxMatcherPart::LineEnd => {
                    continue;
                }
            };
            if let Some(budget) = budget.as_deref_mut() {
                let slots = captures.len().saturating_add(1);
                if captures.len() == captures.capacity() {
                    budget
                        .charge_units(slots.saturating_add(captures.len()))
                        .map_err(resource)?;
                    captures.reserve_exact(1);
                }
                budget
                    .charge_units(2usize.saturating_add(repetitions.saturating_mul(3)))
                    .map_err(resource)?;
                if *kind == SurfaceSyntaxCaptureKind::Identifier {
                    let digits = captures
                        .len()
                        .checked_ilog10()
                        .map_or(1, |n| n as usize + 1);
                    let bytes = "__ash_template_capture_".len().saturating_add(digits);
                    budget
                        .charge_units(bytes.saturating_mul(2))
                        .map_err(resource)?;
                    if identifiers.len() == identifiers.capacity() {
                        budget
                            .charge_units(identifiers.len().saturating_mul(2).saturating_add(1))
                            .map_err(resource)?;
                        identifiers.reserve_exact(1);
                    }
                }
            }
            let mut capture = match kind {
                SurfaceSyntaxCaptureKind::Expression => {
                    SurfaceSyntaxCapture::Expression(SurfaceExpressionCapture {
                        contains_protected_type: false,
                        quote_sites: Default::default(),
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
                SurfaceSyntaxCaptureKind::Declaration => {
                    SurfaceSyntaxCapture::Declaration(SurfaceDeclarationCapture {
                        contents: Arc::from([]),
                    })
                }
            };
            for _ in 0..repetitions {
                capture = SurfaceSyntaxCapture::Repeated(Arc::new(SurfaceRepeatedCapture {
                    values: vec![capture],
                }));
            }
            captures.push(capture);
        }
        Ok(())
    }
    let mut captures = Vec::new();
    let mut identifiers = Vec::new();
    placeholders(
        &declaration.matcher,
        0,
        0,
        declaration.category != crate::surface::SurfaceSyntaxCategory::Expression,
        &mut captures,
        &mut identifiers,
        &mut admission_budget,
    )?;
    let template = declaration
        .template_contents
        .as_deref()
        .ok_or(MacroParseFailure::Invalid)?;
    let generator_matcher = if declaration.contains_generators {
        let budget = admission_budget
            .as_deref_mut()
            .ok_or(MacroParseFailure::Invalid)?;
        Some(generator_admission_matcher(
            declaration,
            template,
            &mut captures,
            &mut identifiers,
            budget,
        )?)
    } else {
        None
    };
    if declaration.template_escapes.is_some() {
        let budget = admission_budget
            .as_deref_mut()
            .ok_or(MacroParseFailure::Invalid)?;
        // The template is complete here, including repetition-owned generator
        // clauses. Validate reads even when there are no generators.
        resolve_template_escape_reads(declaration, budget)?;
    }
    let matcher = generator_matcher.as_deref().unwrap_or(&declaration.matcher);
    if let Some(budget) = &mut admission_budget {
        // Admission validates structure without executing protected captures.
        charge_template_inner(
            template,
            matcher,
            &captures,
            false,
            None,
            &[],
            declaration.template_escapes.as_deref(),
            budget,
        )?;
    }
    let mut contents = template.to_vec();
    let mut loan = admission_budget.as_deref_mut();
    let placeholders = loan.as_ref().map(|_| &mut identifiers);
    let mut escape_placeholders = Vec::new();
    substitute_contents_at(
        &mut contents,
        matcher,
        &captures,
        0,
        declaration.span,
        &mut Vec::new(),
        &mut loan,
        &[],
        None,
        declaration.template_escapes.as_ref(),
        placeholders,
        Some(&mut escape_placeholders),
    )
    .map_err(TemplateSubstitutionFailure::into_macro_failure)?;
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
        crate::surface::SurfaceSyntaxCategory::Declaration
        | crate::surface::SurfaceSyntaxCategory::Derive => {
            let budget = admission_budget
                .as_mut()
                .expect("declaration admission owns its budget");
            // A complete-line escape can produce a declaration. Its result
            // category is known only after ordinary checking, so use an
            // admission-only declaration placeholder at this position. The
            // actual returned fragment is still parsed at invocation.
            for index in 0..contents.len() {
                budget.charge().map_err(resource)?;
                let line_start = index == 0
                    || matches!(
                        contents.get(index - 1),
                        Some(MacroOutputNode::Token(
                            crate::lexer::TokenKind::LineEnd,
                            _,
                            _
                        ))
                    );
                let line_end = index + 1 == contents.len()
                    || matches!(
                        contents.get(index + 1),
                        Some(MacroOutputNode::Token(
                            crate::lexer::TokenKind::LineEnd,
                            _,
                            _
                        ))
                    );
                if !line_start || !line_end {
                    continue;
                }
                let Some(MacroOutputNode::Identifier(name, _)) = contents.get(index) else {
                    continue;
                };
                let mut admitted = false;
                for placeholder in &escape_placeholders {
                    budget
                        .charge_units(
                            name.text
                                .len()
                                .min(placeholder.text.len())
                                .saturating_add(1),
                        )
                        .map_err(resource)?;
                    if name == placeholder {
                        admitted = true;
                        break;
                    }
                }
                if admitted {
                    let span = name.span;
                    budget.charge_units(2).map_err(resource)?;
                    contents[index] = MacroOutputNode::ForwardedDeclaration(
                        crate::surface::SurfaceDeclarationCapture {
                            contents: Arc::from([]),
                        },
                        span.into(),
                    );
                }
            }
            normalize_declaration_line_ends(&mut contents, budget).map_err(resource)?;
            if declaration.contains_quote_or_escape {
                crate::parser::parse_quote_declaration_template_admission(
                    source,
                    declaration.span,
                    contents,
                    contexts,
                    &identifiers,
                    budget,
                )?;
            } else {
                crate::parser::parse_declaration_template_admission(
                    source,
                    declaration.span,
                    contents,
                    contexts,
                    &identifiers,
                    budget,
                )?;
            }
        }
    }
    Ok(())
}

#[derive(Clone, Copy, Debug)]
enum CaptureLookupFailure<'a> {
    Unknown(&'a SurfaceName),
    Invalid(Span),
}

fn unknown_capture_failure(
    name: &SurfaceName,
    budget: Option<&mut SyntaxBudget>,
) -> crate::parser::MacroParseFailure {
    use crate::parser::{MacroParseFailure, UNKNOWN_TEMPLATE_CAPTURE_LABEL};

    if let Some(budget) = budget {
        let mut charge = || {
            // The diagnostic owns its label, capture spelling, vector and location.
            budget.charge_units(
                name.text
                    .len()
                    .saturating_add(1)
                    .saturating_mul(2)
                    .saturating_add(UNKNOWN_TEMPLATE_CAPTURE_LABEL.len())
                    .saturating_add(3),
            )?;
            if let Some(location) = name.diagnostic.as_deref() {
                charge_diagnostic_location_copy(location, budget)?;
                // The copied frame vector also retains each existing Arc.
                budget.charge_units(location.frames.len())?;
            }
            Ok(())
        };
        if let Err(resource) = charge() {
            return MacroParseFailure::Syntax {
                diagnostics: Vec::new(),
                resource: Some(resource),
            };
        }
    }
    crate::parser::unknown_template_capture(name)
}

fn capture_by_name_at<'a, 'name>(
    name: &'name SurfaceName,
    matcher: &[SurfaceSyntaxMatcherPart],
    captures: &'a [SurfaceSyntaxCapture],
    indices: &[usize],
) -> Result<&'a SurfaceSyntaxCapture, CaptureLookupFailure<'name>> {
    capture_by_name_with_depth(name, matcher, captures, indices).map(|(capture, _)| capture)
}

fn capture_by_name_with_depth<'a, 'name>(
    name: &'name SurfaceName,
    matcher: &[SurfaceSyntaxMatcherPart],
    captures: &'a [SurfaceSyntaxCapture],
    indices: &[usize],
) -> Result<(&'a SurfaceSyntaxCapture, usize), CaptureLookupFailure<'name>> {
    let schema =
        matcher_capture_schema(matcher, name).ok_or(CaptureLookupFailure::Unknown(name))?;
    let (index, repetitions) = (schema.index, schema.repetitions);
    let mut capture = captures
        .get(index)
        .ok_or(CaptureLookupFailure::Invalid(name.span))?;
    for index in indices.iter().take(repetitions) {
        let SurfaceSyntaxCapture::Repeated(values) = capture else {
            return Err(CaptureLookupFailure::Invalid(name.span));
        };
        capture = values
            .values
            .get(*index)
            .ok_or(CaptureLookupFailure::Invalid(name.span))?;
    }
    Ok((capture, repetitions))
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct MatcherCaptureSchema {
    index: usize,
    kind: SurfaceSyntaxCaptureKind,
    repetitions: usize,
}

// Use the same matcher preorder for definition admission and invocation leaf
// selection. Group containers do not add an invocation repetition index.
fn matcher_capture_schema(
    matcher: &[SurfaceSyntaxMatcherPart],
    name: &SurfaceName,
) -> Option<MatcherCaptureSchema> {
    fn find(
        parts: &[SurfaceSyntaxMatcherPart],
        name: &SurfaceName,
        offset: &mut usize,
        repetitions: usize,
    ) -> Option<MatcherCaptureSchema> {
        for part in parts {
            match part {
                SurfaceSyntaxMatcherPart::Capture {
                    name: capture,
                    kind,
                } => {
                    if capture.text == name.text {
                        return Some(MatcherCaptureSchema {
                            index: *offset,
                            kind: *kind,
                            repetitions,
                        });
                    }
                    *offset += 1;
                }
                SurfaceSyntaxMatcherPart::Container(container) => {
                    let nested = repetitions
                        + usize::from(matches!(
                            &container.kind,
                            SurfaceMatcherContainerKind::Repeat { .. }
                        ));
                    if let Some(found) = find(&container.body, name, offset, nested) {
                        return Some(found);
                    }
                }
                SurfaceSyntaxMatcherPart::Literal { .. } | SurfaceSyntaxMatcherPart::LineEnd => {}
            }
        }
        None
    }
    find(matcher, name, &mut 0, 0)
}

#[derive(Clone, Copy)]
enum RepetitionFailure<'a> {
    Unknown(&'a SurfaceName),
    Missing(Span),
    Mismatch(Span),
    Empty(Span),
    Invalid(Span),
    Resource(ResourceFailure, Span),
}

impl RepetitionFailure<'_> {
    fn span(self) -> Span {
        match self {
            Self::Unknown(name) => name.span,
            Self::Missing(span)
            | Self::Mismatch(span)
            | Self::Empty(span)
            | Self::Invalid(span)
            | Self::Resource(_, span) => span,
        }
    }

    fn diagnostic(
        self,
        invocation: Option<Span>,
        budget: Option<&mut SyntaxBudget>,
    ) -> crate::parser::MacroParseFailure {
        use crate::parser::{MacroParseFailure, ParseReason, repetition_failure};
        match self {
            Self::Unknown(name) => unknown_capture_failure(name, budget),
            Self::Missing(span) => repetition_failure(ParseReason::RepetitionMissingDriver, span),
            Self::Mismatch(span) => repetition_failure(
                ParseReason::RepetitionLengthMismatch,
                invocation.unwrap_or(span),
            ),
            Self::Empty(span) => {
                repetition_failure(ParseReason::RepetitionEmpty, invocation.unwrap_or(span))
            }
            Self::Invalid(_) => MacroParseFailure::Invalid,
            Self::Resource(resource, _) => MacroParseFailure::Syntax {
                diagnostics: Vec::new(),
                resource: Some(resource),
            },
        }
    }
}

fn charge_matcher_lookup(
    matcher: &[SurfaceSyntaxMatcherPart],
    name: &SurfaceName,
    depth: usize,
    budget: &mut SyntaxBudget,
) -> Result<(), ResourceFailure> {
    for part in matcher {
        budget.charge_units(3)?;
        match part {
            SurfaceSyntaxMatcherPart::Capture {
                name: candidate, ..
            } => {
                budget.charge_units(name.text.len().min(candidate.text.len()).saturating_mul(3))?;
            }
            SurfaceSyntaxMatcherPart::Container(container) => {
                charge_matcher_lookup(&container.body, name, type_depth(depth, 1)?, budget)?;
            }
            SurfaceSyntaxMatcherPart::Literal { .. } | SurfaceSyntaxMatcherPart::LineEnd => {}
        }
    }
    Ok(())
}

/// The known input type and source of one defining escape's lexical read.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum EscapeReadSource {
    Matcher {
        index: usize,
        kind: SurfaceSyntaxCaptureKind,
        repetitions: usize,
    },
    Generator,
}

/// Operand sources for one actual escape occurrence in a completed template.
#[derive(Debug, Eq, PartialEq)]
pub(crate) struct EscapeReadSchema {
    pub(crate) descriptor: usize,
    pub(crate) reads: Vec<EscapeReadSource>,
}

/// Resolve lexical reads only after the complete template and its generator
/// clauses are available. Structural depth counts groups and repetitions;
/// matcher selection uses only the separate repetition depth.
pub(crate) fn resolve_template_escape_reads(
    declaration: &SurfaceSyntaxDeclaration,
    budget: &mut SyntaxBudget,
) -> Result<Vec<EscapeReadSchema>, crate::parser::MacroParseFailure> {
    use crate::parser::MacroParseFailure;
    use crate::surface::SurfaceTemplateGenerator;

    fn resource(error: ResourceFailure) -> MacroParseFailure {
        MacroParseFailure::Syntax {
            diagnostics: Vec::new(),
            resource: Some(error),
        }
    }

    fn walk<'a>(
        nodes: &'a [MacroOutputNode],
        declaration: &'a SurfaceSyntaxDeclaration,
        active: &mut Vec<&'a SurfaceTemplateGenerator>,
        depth: usize,
        repetitions: usize,
        resolved: &mut Vec<EscapeReadSchema>,
        budget: &mut SyntaxBudget,
    ) -> Result<(), MacroParseFailure> {
        for node in nodes {
            budget.charge().map_err(resource)?;
            match node {
                MacroOutputNode::TemplateEscape(adapter) => {
                    let descriptors = declaration
                        .template_escapes
                        .as_deref()
                        .ok_or(MacroParseFailure::Invalid)?;
                    let mut selected = None;
                    for (index, descriptor) in descriptors.iter().enumerate() {
                        budget
                            .charge_units(
                                adapter
                                    .text
                                    .len()
                                    .min(descriptor.adapter.text.len())
                                    .saturating_add(1),
                            )
                            .map_err(resource)?;
                        if descriptor.adapter.text == adapter.text {
                            selected = Some((index, descriptor));
                            break;
                        }
                    }
                    let (descriptor, escape) = selected.ok_or(MacroParseFailure::Invalid)?;
                    budget.charge_units(escape.reads.len()).map_err(resource)?;
                    let mut reads = Vec::with_capacity(escape.reads.len());
                    for name in escape.reads.iter() {
                        charge_matcher_lookup(&declaration.matcher, name, 0, budget)
                            .map_err(resource)?;
                        if let Some(schema) = matcher_capture_schema(&declaration.matcher, name) {
                            if schema.repetitions > repetitions {
                                return Err(unknown_capture_failure(name, Some(budget)));
                            }
                            reads.push(EscapeReadSource::Matcher {
                                index: schema.index,
                                kind: schema.kind,
                                repetitions: schema.repetitions,
                            });
                        } else {
                            let mut found = false;
                            for generator in active.iter() {
                                budget
                                    .charge_units(
                                        name.text
                                            .len()
                                            .min(generator.name.text.len())
                                            .saturating_add(1),
                                    )
                                    .map_err(resource)?;
                                if generator.name.text == name.text {
                                    found = true;
                                    break;
                                }
                            }
                            if !found {
                                return Err(unknown_capture_failure(name, Some(budget)));
                            }
                            reads.push(EscapeReadSource::Generator);
                        }
                    }
                    if resolved.len() == resolved.capacity() {
                        budget
                            .charge_units(resolved.len().saturating_mul(2).saturating_add(1))
                            .map_err(resource)?;
                        resolved.reserve_exact(1);
                    } else {
                        budget.charge().map_err(resource)?;
                    }
                    resolved.push(EscapeReadSchema { descriptor, reads });
                }
                MacroOutputNode::Group(_, children, _) => walk(
                    children,
                    declaration,
                    active,
                    type_depth(depth, 1).map_err(resource)?,
                    repetitions,
                    resolved,
                    budget,
                )?,
                MacroOutputNode::TemplateRepeat(repeat) => {
                    let original = active.len();
                    if let Some(bindings) = &repeat.generators {
                        let requested = original.saturating_add(bindings.len());
                        budget.charge_units(bindings.len()).map_err(resource)?;
                        if requested > active.capacity() {
                            budget
                                .charge_units(requested.saturating_add(original))
                                .map_err(resource)?;
                            active.reserve_exact(bindings.len());
                        }
                        active.extend(bindings.iter());
                    }
                    walk(
                        &repeat.body,
                        declaration,
                        active,
                        type_depth(depth, 1).map_err(resource)?,
                        repetitions.saturating_add(1),
                        resolved,
                        budget,
                    )?;
                    active.truncate(original);
                }
                _ => {}
            }
        }
        Ok(())
    }

    let Some(template) = declaration.template_contents.as_deref() else {
        return Err(MacroParseFailure::Invalid);
    };
    let initial = declaration.generators.as_deref().unwrap_or(&[]);
    budget.charge_units(initial.len()).map_err(resource)?;
    let mut active = Vec::with_capacity(initial.len());
    active.extend(initial.iter());
    let mut resolved = Vec::new();
    walk(
        template,
        declaration,
        &mut active,
        0,
        0,
        &mut resolved,
        budget,
    )?;
    Ok(resolved)
}

/// Fill only compiler-created escape probe inputs after the complete template
/// has established their lexical operands. The returned definition indices
/// identify the probes whose local results must be observed by normal checking.
pub(crate) fn prepare_escape_probes(
    module: &mut crate::surface::SurfaceModule,
    introduction: Option<usize>,
    budget: &mut SyntaxBudget,
) -> Result<Vec<usize>, crate::parser::MacroParseFailure> {
    use crate::parser::MacroParseFailure;
    use crate::surface::{
        SurfaceBinder, SurfaceDefinitionKind, SurfacePattern, SurfacePatternKind, SurfaceType,
        SurfaceTypeKind,
    };

    fn resource(error: ResourceFailure) -> MacroParseFailure {
        MacroParseFailure::Syntax {
            diagnostics: Vec::new(),
            resource: Some(error),
        }
    }
    fn name(text: String, span: Span, introduction: usize) -> SurfaceName {
        SurfaceName {
            text,
            span,
            introduction,
            introduced_at: (introduction != 0).then_some(span),
            written: false,
            diagnostic: None,
        }
    }
    fn named_type(text: &str, span: Span, introduction: usize) -> SurfaceType {
        SurfaceType {
            kind: SurfaceTypeKind::Named(SurfaceReference::Unqualified(name(
                text.to_owned(),
                span,
                introduction,
            ))),
            span,
            diagnostic: None,
        }
    }

    let mut pending = Vec::new();
    for declaration in &module.syntax_declarations {
        budget.charge().map_err(resource)?;
        let Some(escapes) = declaration.template_escapes.as_deref() else {
            continue;
        };
        for schema in resolve_template_escape_reads(declaration, budget)? {
            let escape = escapes
                .get(schema.descriptor)
                .ok_or(MacroParseFailure::Invalid)?;
            let mut definition = None;
            for (index, candidate) in module.definitions.iter().enumerate() {
                budget.charge().map_err(resource)?;
                let SurfaceDefinitionKind::Equational(global) = &candidate.kind else {
                    continue;
                };
                budget
                    .charge_units(
                        escape
                            .adapter
                            .text
                            .len()
                            .min(global.interface.name.text.len())
                            .saturating_add(1),
                    )
                    .map_err(resource)?;
                if escape.adapter.text == global.interface.name.text {
                    definition = Some(index);
                    break;
                }
            }
            if pending.len() == pending.capacity() {
                budget
                    .charge_units(pending.len().saturating_mul(2).saturating_add(1))
                    .map_err(resource)?;
                pending.reserve_exact(1);
            } else {
                budget.charge().map_err(resource)?;
            }
            pending.push((definition.ok_or(MacroParseFailure::Invalid)?, schema.reads));
        }
    }
    if pending.is_empty() {
        return Ok(Vec::new());
    }
    let introduction = introduction.ok_or(MacroParseFailure::Invalid)?;
    budget.charge_units(pending.len()).map_err(resource)?;
    let mut definitions = Vec::with_capacity(pending.len());
    for (definition, reads) in pending {
        let global = module
            .definitions
            .get_mut(definition)
            .ok_or(MacroParseFailure::Invalid)?;
        let SurfaceDefinitionKind::Equational(global) = &mut global.kind else {
            return Err(MacroParseFailure::Invalid);
        };
        let SurfaceTypeKind::Function(function) = &mut global.interface.annotation.kind else {
            return Err(MacroParseFailure::Invalid);
        };
        let [equation] = global.equations.as_mut_slice() else {
            return Err(MacroParseFailure::Invalid);
        };
        if equation.patterns.len() != 1 {
            return Err(MacroParseFailure::Invalid);
        }
        let span = global.interface.name.span;
        budget
            .charge_units(reads.len().saturating_mul(2).saturating_add(2))
            .map_err(resource)?;
        let mut types = Vec::with_capacity(reads.len());
        let mut patterns = Vec::with_capacity(reads.len());
        for (index, read) in reads.iter().enumerate() {
            let kind = match read {
                EscapeReadSource::Matcher { kind, .. } => *kind,
                EscapeReadSource::Generator => SurfaceSyntaxCaptureKind::Expression,
            };
            let spelling = match kind {
                SurfaceSyntaxCaptureKind::Expression => "ExpressionFragment",
                SurfaceSyntaxCaptureKind::Identifier => "Identifier",
                SurfaceSyntaxCaptureKind::Type => "TypeFragment",
                SurfaceSyntaxCaptureKind::Pattern => "PatternFragment",
                SurfaceSyntaxCaptureKind::Declaration => "DeclarationFragment",
            };
            let digits = index.checked_ilog10().map_or(1, |n| n as usize + 1);
            let operand_bytes = "\0ash_escape_operand_".len().saturating_add(digits);
            let extra = if kind == SurfaceSyntaxCaptureKind::Identifier {
                "Origin".len().saturating_add(4)
            } else {
                0
            };
            budget
                .charge_units(
                    operand_bytes
                        .saturating_add(spelling.len())
                        .saturating_add(extra)
                        .saturating_add(5),
                )
                .map_err(resource)?;
            let ty = named_type(spelling, span, introduction);
            types.push(if kind == SurfaceSyntaxCaptureKind::Identifier {
                SurfaceType {
                    kind: SurfaceTypeKind::Tuple(vec![
                        ty,
                        named_type("Origin", span, introduction),
                    ]),
                    span,
                    diagnostic: None,
                }
            } else {
                ty
            });
            patterns.push(SurfacePattern {
                kind: SurfacePatternKind::Binder(SurfaceBinder {
                    name: name(format!("\0ash_escape_operand_{index}"), span, 0),
                    span,
                }),
                span,
                diagnostic: None,
            });
        }
        let domain = match types.len() {
            0 => SurfaceType {
                kind: SurfaceTypeKind::Unit,
                span,
                diagnostic: None,
            },
            1 => types.pop().ok_or(MacroParseFailure::Invalid)?,
            _ => SurfaceType {
                kind: SurfaceTypeKind::Tuple(types),
                span,
                diagnostic: None,
            },
        };
        let pattern = match patterns.len() {
            0 => SurfacePattern {
                kind: SurfacePatternKind::Unit,
                span,
                diagnostic: None,
            },
            1 => patterns.pop().ok_or(MacroParseFailure::Invalid)?,
            _ => SurfacePattern {
                kind: SurfacePatternKind::Tuple(patterns),
                span,
                diagnostic: None,
            },
        };
        function.domain = Box::new(domain);
        equation.patterns[0] = pattern;
        definitions.push(definition);
    }
    Ok(definitions)
}

/// Find the actual resolved local binder in each compiler-owned probe.
pub(crate) fn escape_probe_binders(
    module: &crate::surface::SurfaceModule,
    resolved: &crate::resolved::ResolvedModule,
    probes: &[usize],
    work: &mut TypeWorkBudget,
) -> Result<Vec<crate::resolved::BinderId>, ()> {
    use crate::resolved::{
        ResolvedDefinitionKind, ResolvedExprKind, ResolvedLocalDeclaration, ResolvedPatternKind,
    };
    use crate::surface::SurfaceDefinitionKind;

    work.charge(probes.len())?;
    let mut binders = Vec::new();
    binders.try_reserve_exact(probes.len()).map_err(|_| ())?;
    for index in probes {
        let SurfaceDefinitionKind::Equational(probe) =
            &module.definitions.get(*index).ok_or(())?.kind
        else {
            return Err(());
        };
        let mut selected = None;
        for candidate in resolved.definitions() {
            work.charge(1)?;
            let ResolvedDefinitionKind::Equational(global) = &candidate.kind else {
                continue;
            };
            work.charge(
                global
                    .interface
                    .name
                    .spelling
                    .len()
                    .min(probe.interface.name.text.len())
                    .saturating_add(1),
            )?;
            if global.interface.name.spelling == probe.interface.name.text {
                selected = Some(global);
                break;
            }
        }
        let global = selected.ok_or(())?;
        let [equation] = global.equations.as_slice() else {
            return Err(());
        };
        let ResolvedExprKind::Block(block) = &equation.body.kind else {
            return Err(());
        };
        let [ResolvedLocalDeclaration::Binding(binding)] = block.declarations.as_slice() else {
            return Err(());
        };
        let ResolvedPatternKind::Binder(binder) = &binding.pattern.kind else {
            return Err(());
        };
        work.charge(binder.spelling.len().saturating_add(4))?;
        if binder.spelling.strip_suffix("\0result") != Some(probe.interface.name.text.as_str()) {
            return Err(());
        }
        binders.push(binder.id);
    }
    Ok(binders)
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum EscapeResultCategory {
    Expression,
    Identifier,
    Type,
    Pattern,
    Declaration,
}

/// Classify only identities from the actual admitted compiler syntax module.
pub(crate) fn escape_result_category(
    ty: &crate::types::Type,
    builtin: &CheckedModule,
    work: &mut TypeWorkBudget,
) -> Result<Option<EscapeResultCategory>, ()> {
    use crate::types::Type;
    fn nominal<'a>(
        ty: &Type,
        builtin: &'a CheckedModule,
        work: &mut TypeWorkBudget,
    ) -> Result<Option<&'a str>, ()> {
        work.charge(1)?;
        let Type::Nominal(id) = ty else {
            return Ok(None);
        };
        if id.module() != builtin.module() || !builtin.module().is_builtin_compiler_syntax() {
            return Ok(None);
        }
        work.charge(1)?;
        let Some(fact) = builtin.registry().nominal(*id) else {
            return Ok(None);
        };
        work.charge(fact.spelling.len())?;
        Ok(Some(&fact.spelling))
    }

    if let Type::Tuple(elements) = ty
        && let [identifier, origin] = elements.as_ref()
    {
        return Ok((nominal(identifier, builtin, work)? == Some("Identifier")
            && nominal(origin, builtin, work)? == Some("Origin"))
        .then_some(EscapeResultCategory::Identifier));
    }
    Ok(match nominal(ty, builtin, work)? {
        Some("ExpressionFragment") => Some(EscapeResultCategory::Expression),
        Some("TypeFragment") => Some(EscapeResultCategory::Type),
        Some("PatternFragment") => Some(EscapeResultCategory::Pattern),
        Some("DeclarationFragment") => Some(EscapeResultCategory::Declaration),
        _ => None,
    })
}

/// Finish only the signatures and results of the registered compiler probes.
/// Their original initializer bodies and quote-site allocations are untouched.
pub(crate) fn finish_escape_probes(
    module: &mut crate::surface::SurfaceModule,
    introduction: Option<usize>,
    probes: &[usize],
    categories: &[(EscapeResultCategory, bool, bool)],
    budget: &mut SyntaxBudget,
) -> Result<(), crate::parser::MacroParseFailure> {
    use crate::parser::MacroParseFailure;
    use crate::surface::{
        ApplicationExpr, FunctionExpr, FunctionType, SurfaceBinder, SurfaceBinding, SurfaceBlock,
        SurfaceDefinitionKind, SurfaceExpr, SurfaceExprKind, SurfaceLocalDeclaration,
        SurfacePattern, SurfacePatternKind, SurfaceTypeKind,
    };
    let resource = |error| MacroParseFailure::Syntax {
        diagnostics: Vec::new(),
        resource: Some(error),
    };
    if probes.len() != categories.len() {
        return Err(MacroParseFailure::Invalid);
    }
    let introduction = introduction.ok_or(MacroParseFailure::Invalid)?;
    for (definition, &(category, pure, disjoint_atom)) in probes.iter().zip(categories) {
        let definition = module
            .definitions
            .get_mut(*definition)
            .ok_or(MacroParseFailure::Invalid)?;
        let SurfaceDefinitionKind::Equational(global) = &mut definition.kind else {
            return Err(MacroParseFailure::Invalid);
        };
        let SurfaceTypeKind::Function(function) = &mut global.interface.annotation.kind else {
            return Err(MacroParseFailure::Invalid);
        };
        let [equation] = global.equations.as_mut_slice() else {
            return Err(MacroParseFailure::Invalid);
        };
        let SurfaceExprKind::Block(block) = &mut equation.body.kind else {
            return Err(MacroParseFailure::Invalid);
        };
        let span = global.interface.name.span;
        let spelling = match category {
            EscapeResultCategory::Expression => "ExpressionFragment",
            EscapeResultCategory::Identifier => "Identifier",
            EscapeResultCategory::Type => "TypeFragment",
            EscapeResultCategory::Pattern => "PatternFragment",
            EscapeResultCategory::Declaration => "DeclarationFragment",
        };
        let extra = if category == EscapeResultCategory::Identifier {
            "Origin".len().saturating_add(4)
        } else {
            0
        };
        budget
            .charge_units(
                global
                    .interface
                    .name
                    .text
                    .len()
                    .saturating_add("\0result".len())
                    .saturating_add(spelling.len())
                    .saturating_add(extra)
                    .saturating_add(6),
            )
            .map_err(resource)?;
        let name = |text: String, introduction| SurfaceName {
            text,
            span,
            introduction,
            introduced_at: (introduction != 0).then_some(span),
            written: false,
            diagnostic: None,
        };
        let named = |text: &str| SurfaceType {
            kind: SurfaceTypeKind::Named(SurfaceReference::Unqualified(name(
                text.to_owned(),
                introduction,
            ))),
            span,
            diagnostic: None,
        };
        let ty = named(spelling);
        let ty = if category == EscapeResultCategory::Identifier {
            SurfaceType {
                kind: SurfaceTypeKind::Tuple(vec![ty, named("Origin")]),
                span,
                diagnostic: None,
            }
        } else {
            ty
        };
        let mut returned = SurfaceExpr {
            kind: SurfaceExprKind::Name(SurfaceReference::Unqualified(name(
                format!("{}\0result", global.interface.name.text),
                0,
            ))),
            span,
            diagnostic: None,
        };
        if disjoint_atom {
            if category != EscapeResultCategory::Expression {
                return Err(MacroParseFailure::Invalid);
            }
            let [SurfaceLocalDeclaration::Binding(initializer)] = block.declarations.as_slice()
            else {
                return Err(MacroParseFailure::Invalid);
            };
            let initializer_span = initializer.initializer.span;
            const IDENTITY: &str = "\0ash_escape_identity";
            const VALUE: &str = "\0ash_escape_identity_value";
            let live = block.declarations.len();
            let growth = if live == block.declarations.capacity() {
                live.saturating_mul(2).saturating_add(1)
            } else {
                1
            };
            budget
                .charge_units(
                    IDENTITY
                        .len()
                        .saturating_mul(2)
                        .saturating_add(VALUE.len().saturating_mul(2))
                        .saturating_add("ExpressionFragment".len().saturating_mul(2))
                        .saturating_add(growth)
                        .saturating_add(24),
                )
                .map_err(resource)?;
            if live == block.declarations.capacity() {
                block.declarations.reserve_exact(1);
            }
            let pattern = |text: &str| SurfacePattern {
                kind: SurfacePatternKind::Binder(SurfaceBinder {
                    name: name(text.to_owned(), 0),
                    span,
                }),
                span,
                diagnostic: None,
            };
            let reference = |text: &str| SurfaceExpr {
                kind: SurfaceExprKind::Name(SurfaceReference::Unqualified(name(
                    text.to_owned(),
                    0,
                ))),
                span,
                diagnostic: None,
            };
            let annotation = SurfaceType {
                kind: SurfaceTypeKind::Function(FunctionType {
                    domain: Box::new(named("ExpressionFragment")),
                    codomain: Box::new(named("ExpressionFragment")),
                    effects: None,
                }),
                span,
                diagnostic: None,
            };
            let identity = SurfaceExpr {
                kind: SurfaceExprKind::Function(FunctionExpr {
                    parameter: pattern(VALUE),
                    body: SurfaceBlock {
                        declarations: Vec::new(),
                        result: Box::new(reference(VALUE)),
                        span,
                    },
                }),
                span,
                diagnostic: None,
            };
            block
                .declarations
                .push(SurfaceLocalDeclaration::Binding(Box::new(SurfaceBinding {
                    pattern: pattern(IDENTITY),
                    annotation: Some(annotation),
                    initializer: identity,
                    span,
                })));
            returned.span = initializer_span;
            if let SurfaceExprKind::Name(SurfaceReference::Unqualified(name)) = &mut returned.kind {
                name.span = initializer_span;
            }
            returned = SurfaceExpr {
                kind: SurfaceExprKind::Apply(ApplicationExpr {
                    function: Box::new(reference(IDENTITY)),
                    argument: Box::new(returned),
                }),
                span: initializer_span,
                diagnostic: None,
            };
        }
        function.codomain = Box::new(ty);
        if pure {
            // The ordinary probe finalized this initializer as effect-free;
            // the complete final module check verifies the narrower shell.
            function.effects = None;
        }
        block.result = Box::new(returned);
    }
    Ok(())
}

/// Inspect all splice uses, including those nested in another repetition.
fn repetition_length<'a>(
    repeat: &'a TemplateRepeat,
    matcher: &[SurfaceSyntaxMatcherPart],
    captures: &[SurfaceSyntaxCapture],
    indices: &[usize],
    prefix: usize,
    generators: &[&SurfaceName],
    escapes: Option<&'a [crate::surface::SurfaceTemplateEscape]>,
    mut budget: Option<&mut SyntaxBudget>,
) -> Result<usize, RepetitionFailure<'a>> {
    #[allow(clippy::too_many_arguments)]
    fn inspect<'a>(
        name: &'a SurfaceName,
        matcher: &[SurfaceSyntaxMatcherPart],
        captures: &[SurfaceSyntaxCapture],
        indices: &[usize],
        generators: &[&SurfaceName],
        length: &mut Option<usize>,
        span: Span,
        budget: &mut Option<&mut SyntaxBudget>,
    ) -> Result<(), RepetitionFailure<'a>> {
        if let Some(budget) = budget.as_deref_mut() {
            // Pay this lookup and the corresponding substitution lookup.
            charge_matcher_lookup(matcher, name, 0, budget)
                .map_err(|error| RepetitionFailure::Resource(error, span))?;
            charge_matcher_lookup(matcher, name, 0, budget)
                .map_err(|error| RepetitionFailure::Resource(error, span))?;
            budget
                .charge_units(indices.len().saturating_mul(6))
                .map_err(|error| RepetitionFailure::Resource(error, span))?;
        }
        let capture = capture_by_name_at(name, matcher, captures, indices);
        if matches!(capture, Err(CaptureLookupFailure::Unknown(_))) {
            let mut found = false;
            for generator in generators {
                if let Some(budget) = budget.as_deref_mut() {
                    budget
                        .charge_units(
                            name.text
                                .len()
                                .min(generator.text.len())
                                .saturating_add(1)
                                .saturating_mul(2),
                        )
                        .map_err(|error| RepetitionFailure::Resource(error, span))?;
                }
                if generator.text == name.text {
                    found = true;
                    break;
                }
            }
            if found {
                return Ok(());
            }
        }
        if let SurfaceSyntaxCapture::Repeated(values) =
            capture.map_err(|failure| match failure {
                CaptureLookupFailure::Unknown(name) => RepetitionFailure::Unknown(name),
                CaptureLookupFailure::Invalid(span) => RepetitionFailure::Invalid(span),
            })?
        {
            if length.is_some_and(|prior| prior != values.values.len()) {
                return Err(RepetitionFailure::Mismatch(span));
            }
            *length = Some(values.values.len());
        }
        Ok(())
    }

    let span = repeat.origin.primary();
    if let Some(budget) = budget.as_deref_mut() {
        budget
            .charge_units(repeat.body.len().saturating_mul(2))
            .map_err(|error| RepetitionFailure::Resource(error, span))?;
    }
    let mut pending = repeat
        .body
        .iter()
        .map(|node| (node, prefix))
        .collect::<Vec<_>>();
    let mut length = None;
    while let Some((node, depth)) = pending.pop() {
        if let Some(budget) = budget.as_deref_mut() {
            // The same traversal runs during substitution after preflight.
            budget
                .charge_units(4)
                .map_err(|error| RepetitionFailure::Resource(error, span))?;
        }
        match node {
            MacroOutputNode::Splice(name) => {
                inspect(
                    name,
                    matcher,
                    captures,
                    indices,
                    generators,
                    &mut length,
                    span,
                    &mut budget,
                )?;
            }
            MacroOutputNode::Group(_, children, _) => {
                let next = type_depth(depth, 1)
                    .map_err(|error| RepetitionFailure::Resource(error, span))?;
                if let Some(budget) = budget.as_deref_mut() {
                    budget
                        .charge_units(children.len().saturating_mul(3))
                        .map_err(|error| RepetitionFailure::Resource(error, span))?;
                    if pending.len().saturating_add(children.len()) > pending.capacity() {
                        budget
                            .charge_units(
                                pending
                                    .len()
                                    .saturating_mul(2)
                                    .saturating_add(children.len())
                                    .saturating_mul(2),
                            )
                            .map_err(|error| RepetitionFailure::Resource(error, span))?;
                    }
                }
                pending.reserve_exact(children.len());
                pending.extend(children.iter().map(|node| (node, next)));
            }
            MacroOutputNode::TemplateRepeat(inner) => {
                let next = type_depth(depth, 1)
                    .map_err(|error| RepetitionFailure::Resource(error, span))?;
                if let Some(budget) = budget.as_deref_mut() {
                    budget
                        .charge_units(inner.body.len().saturating_mul(3))
                        .map_err(|error| RepetitionFailure::Resource(error, span))?;
                    if pending.len().saturating_add(inner.body.len()) > pending.capacity() {
                        budget
                            .charge_units(
                                pending
                                    .len()
                                    .saturating_mul(2)
                                    .saturating_add(inner.body.len())
                                    .saturating_mul(2),
                            )
                            .map_err(|error| RepetitionFailure::Resource(error, span))?;
                    }
                }
                pending.reserve_exact(inner.body.len());
                pending.extend(inner.body.iter().map(|node| (node, next)));
            }
            MacroOutputNode::TemplateEscape(adapter) => {
                let mut selected = None;
                for escape in escapes.into_iter().flatten() {
                    if let Some(budget) = budget.as_deref_mut() {
                        budget
                            .charge_units(
                                adapter
                                    .text
                                    .len()
                                    .min(escape.adapter.text.len())
                                    .saturating_add(1)
                                    .saturating_mul(2),
                            )
                            .map_err(|error| RepetitionFailure::Resource(error, span))?;
                    }
                    if escape.adapter.text == adapter.text {
                        selected = Some(escape);
                        break;
                    }
                }
                let escape = selected.ok_or(RepetitionFailure::Invalid(adapter.span))?;
                for name in escape.reads.iter() {
                    inspect(
                        name,
                        matcher,
                        captures,
                        indices,
                        generators,
                        &mut length,
                        span,
                        &mut budget,
                    )?;
                }
            }
            _ => {}
        }
    }
    let length = length.ok_or(RepetitionFailure::Missing(span))?;
    if repeat.one_or_more && length == 0 {
        return Err(RepetitionFailure::Empty(span));
    }
    Ok(length)
}

/// Reserve the copies performed by declaration-template substitution.
#[cfg(test)]
fn charge_declaration_template(
    template: &[MacroOutputNode],
    matcher: &[SurfaceSyntaxMatcherPart],
    captures: &[SurfaceSyntaxCapture],
    budget: &mut SyntaxBudget,
) -> Result<bool, crate::parser::MacroParseFailure> {
    charge_template_inner(template, matcher, captures, false, None, &[], None, budget)
}

fn charge_template_inner(
    template: &[MacroOutputNode],
    matcher: &[SurfaceSyntaxMatcherPart],
    captures: &[SurfaceSyntaxCapture],
    new_expression: bool,
    invocation: Option<Span>,
    generators: &[&SurfaceName],
    escapes: Option<&[crate::surface::SurfaceTemplateEscape]>,
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
    let mut expanded_nodes = 0usize;
    let mut repeat_visits = 0usize;
    budget.charge_units(template.len()).map_err(resource)?;
    budget.charge_units(template.len()).map_err(resource)?;
    if new_expression && !template.is_empty() {
        // The borrowed preflight and the eventual root clone own separate buffers.
        budget.charge_units(template.len()).map_err(resource)?;
        budget.charge_units(template.len()).map_err(resource)?;
    }
    let mut pending = template
        .iter()
        .map(|node| (node, 0usize, Vec::<usize>::new()))
        .collect::<Vec<_>>();
    while let Some((node, depth, indices)) = pending.pop() {
        expanded_nodes = expanded_nodes.saturating_add(1);
        budget.charge().map_err(resource)?;
        match node {
            MacroOutputNode::Identifier(name, origin) => {
                charge_type_name_copy(name, depth, budget).map_err(resource)?;
                charge_type_origin_copy(origin, depth, budget).map_err(resource)?;
            }
            MacroOutputNode::Token(kind, spelling, origin) => {
                budget.charge_units(spelling.len()).map_err(resource)?;
                charge_type_token_copy(kind, budget).map_err(resource)?;
                budget.charge().map_err(resource)?; // retained spelling Arc
                charge_type_origin_copy(origin, depth, budget).map_err(resource)?;
            }
            MacroOutputNode::Group(_, children, origin) => {
                if depth >= STRUCTURAL_DEPTH_LIMIT {
                    return Err(resource(ResourceFailure::StructuralDepth {
                        limit: STRUCTURAL_DEPTH_LIMIT,
                    }));
                }
                budget.charge_units(children.len()).map_err(resource)?;
                budget.charge_units(children.len()).map_err(resource)?;
                charge_type_origin_copy(origin, depth + 1, budget).map_err(resource)?;
                if new_expression && !children.is_empty() {
                    // Vec::clone requests the child buffer before substitution.
                    budget.charge_units(children.len()).map_err(resource)?;
                }
                let live = pending.len();
                let requested = live.saturating_add(children.len());
                if requested > pending.capacity() {
                    budget
                        .charge_units(requested.saturating_add(live))
                        .map_err(resource)?;
                    pending.reserve_exact(children.len());
                }
                budget
                    .charge_units(children.len().saturating_mul(indices.len()))
                    .map_err(resource)?;
                pending.extend(
                    children
                        .iter()
                        .map(|child| (child, depth + 1, indices.clone())),
                );
            }
            MacroOutputNode::Splice(name) => {
                charge_type_name_copy(name, depth, budget).map_err(resource)?;
                charge_matcher_lookup(matcher, name, 0, budget).map_err(resource)?;
                budget
                    .charge_units(indices.len().saturating_mul(3))
                    .map_err(resource)?;
                match capture_by_name_at(name, matcher, captures, &indices) {
                    Ok(SurfaceSyntaxCapture::Identifier(capture)) => {
                        charge_type_name_copy(&capture.name, depth, budget).map_err(resource)?;
                        charge_type_origin_copy(&capture.origin, depth, budget)
                            .map_err(resource)?;
                    }
                    Ok(SurfaceSyntaxCapture::Type(capture)) => {
                        let type_prefix = type_depth(depth, 1).map_err(resource)?;
                        charge_type_copy(&capture.ty, type_prefix, false, budget)
                            .map_err(resource)?;
                        charge_type_retention(capture, depth, budget)?;
                    }
                    Ok(SurfaceSyntaxCapture::Expression(capture)) => {
                        let prefix = type_depth(depth, 1).map_err(resource)?;
                        let mut capture_bridge = if new_expression {
                            charge_new_expression_copy(&capture.expression, prefix, false, budget)
                        } else {
                            charge_expression_copy(&capture.expression, prefix, false, budget)
                        }
                        .map_err(resource)?
                        .ok_or(MacroParseFailure::Invalid)?;
                        capture_bridge |= if new_expression {
                            charge_new_expression_retention(capture, depth, budget)
                        } else {
                            charge_expression_retention(capture, depth, budget)
                        }
                        .map_err(resource)?
                        .ok_or(MacroParseFailure::Invalid)?;
                        bridge |= capture_bridge;
                    }
                    Ok(SurfaceSyntaxCapture::Pattern(capture)) => {
                        let prefix = type_depth(depth, 1).map_err(resource)?;
                        let mut capture_bridge =
                            charge_pattern_copy(&capture.pattern, prefix, false, budget)
                                .map_err(resource)?
                                .ok_or(MacroParseFailure::Invalid)?;
                        capture_bridge |= charge_pattern_retention(capture, depth, budget)
                            .map_err(resource)?
                            .ok_or(MacroParseFailure::Invalid)?;
                        bridge |= capture_bridge;
                    }
                    Ok(SurfaceSyntaxCapture::Declaration(capture)) => {
                        type_depth(depth, 1).map_err(resource)?;
                        budget.charge().map_err(resource)?;
                        if let Some(origin) = declaration_capture_origin(capture) {
                            charge_type_origin_copy(origin, depth, budget).map_err(resource)?;
                        }
                    }
                    Err(CaptureLookupFailure::Unknown(name)) => {
                        let mut found = false;
                        for generator in generators {
                            budget
                                .charge_units(
                                    name.text.len().min(generator.text.len()).saturating_add(1),
                                )
                                .map_err(resource)?;
                            if generator.text == name.text {
                                found = true;
                                break;
                            }
                        }
                        if !found {
                            return Err(unknown_capture_failure(name, Some(budget)));
                        }
                    }
                    Ok(SurfaceSyntaxCapture::Repeated(_))
                    | Err(CaptureLookupFailure::Invalid(_)) => {
                        return Err(MacroParseFailure::Invalid);
                    }
                }
            }
            MacroOutputNode::TemplateEscape(name) => {
                charge_type_name_copy(name, depth, budget).map_err(resource)?;
            }
            MacroOutputNode::TemplateRepeat(repeat) => {
                budget.charge().map_err(resource)?; // retained repeat Arc
                repeat_visits = repeat_visits.saturating_add(1);
                let child_depth = type_depth(depth, 1).map_err(resource)?;
                let count = match repetition_length(
                    repeat,
                    matcher,
                    captures,
                    &indices,
                    child_depth,
                    generators,
                    escapes,
                    Some(&mut *budget),
                ) {
                    Ok(count) => count,
                    Err(failure) => return Err(failure.diagnostic(invocation, Some(budget))),
                };
                if repeat.separator.is_some() {
                    expanded_nodes = expanded_nodes.saturating_add(count.saturating_sub(1));
                }
                let entries = repeat.body.len().saturating_mul(count);
                // Body clones, result buffers, insertion moves and preflight entries.
                budget
                    .charge_units(entries.saturating_mul(6))
                    .map_err(resource)?;
                budget
                    .charge_units(count.saturating_mul(3).saturating_add(2))
                    .map_err(resource)?;
                budget
                    .charge_units(entries.saturating_mul(indices.len().saturating_add(1)))
                    .map_err(resource)?;
                // Each iteration also owns a separate temporary index buffer.
                budget
                    .charge_units(count.saturating_mul(indices.len().saturating_add(1)))
                    .map_err(resource)?;
                // Substitution grows its own shared index buffer and moves its
                // existing entries independently of those preflight buffers.
                budget
                    .charge_units(
                        count.saturating_mul(indices.len().saturating_mul(2).saturating_add(1)),
                    )
                    .map_err(resource)?;
                if let Some((kind, _, origin)) = &repeat.separator {
                    for _ in 1..count {
                        charge_type_token_copy(kind, budget).map_err(resource)?;
                        charge_type_origin_copy(origin, child_depth, budget).map_err(resource)?;
                        budget.charge_units(3).map_err(resource)?;
                    }
                }
                let live = pending.len();
                let requested = live.saturating_add(entries);
                if requested > pending.capacity() {
                    budget
                        .charge_units(requested.saturating_add(live))
                        .map_err(resource)?;
                    pending.reserve_exact(entries);
                }
                for iteration in (0..count).rev() {
                    let mut selected = Vec::with_capacity(indices.len().saturating_add(1));
                    selected.extend_from_slice(&indices);
                    selected.push(iteration);
                    pending.extend(
                        repeat
                            .body
                            .iter()
                            .rev()
                            .map(|node| (node, child_depth, selected.clone())),
                    );
                }
            }
            MacroOutputNode::Expression(_, _)
            | MacroOutputNode::ForwardedExpression(_, _)
            | MacroOutputNode::ForwardedType(_, _)
            | MacroOutputNode::ForwardedDeclaration(_, _)
            | MacroOutputNode::ForwardedPattern(_, _) => return Err(MacroParseFailure::Invalid),
        }
    }
    if repeat_visits != 0 {
        // Each splice can move at most the complete expanded sequence once;
        // piece and final buffers are filled at their exact capacity.
        budget
            .charge_units(
                expanded_nodes.saturating_mul(repeat_visits.saturating_mul(2).saturating_add(3)),
            )
            .map_err(resource)?;
    }
    Ok(bridge)
}

/// Instantiate supported captures before the existing declaration parser.
#[cfg(test)]
pub(crate) fn instantiate_declaration_template(
    selection: &SelectedSyntax,
    captures: &[SurfaceSyntaxCapture],
    introduction: usize,
    invocation: Span,
    budget: &mut SyntaxBudget,
) -> Result<Vec<MacroOutputNode>, crate::parser::MacroParseFailure> {
    let mut output = prepare_declaration_template(selection, captures, invocation, budget)?;
    substitute_contents(
        &mut output,
        &selection.declaration.matcher,
        captures,
        introduction,
        invocation,
        Some(budget),
    )
    .map_err(TemplateSubstitutionFailure::into_macro_failure)?;
    Ok(output)
}

pub(crate) fn prepare_declaration_template(
    selection: &SelectedSyntax,
    captures: &[SurfaceSyntaxCapture],
    invocation: Span,
    budget: &mut SyntaxBudget,
) -> Result<Vec<MacroOutputNode>, crate::parser::MacroParseFailure> {
    use crate::parser::MacroParseFailure;

    let template = selection
        .declaration
        .template_contents
        .as_deref()
        .ok_or(MacroParseFailure::Invalid)?;
    if charge_template_inner(
        template,
        &selection.declaration.matcher,
        captures,
        false,
        Some(invocation),
        &[],
        selection.declaration.template_escapes.as_deref(),
        budget,
    )? {
        return Err(MacroParseFailure::Invalid);
    }
    Ok(template.to_vec())
}

/// Expand the actual capture-driven repetitions and record the ordered
/// generator operations for this invocation. Generator reads never drive a
/// repetition; the admitted names only identify scalar consumers here.
pub(crate) fn prepare_generator_template(
    selection: &SelectedSyntax,
    captures: &[SurfaceSyntaxCapture],
    introduction: usize,
    invocation: Span,
    budget: &mut SyntaxBudget,
) -> Result<(Vec<MacroOutputNode>, GeneratorPlan), crate::parser::MacroParseFailure> {
    use crate::parser::MacroParseFailure;
    fn record<'a>(
        bindings: &'a Arc<[crate::surface::SurfaceTemplateGenerator]>,
        names: &mut Vec<&'a SurfaceName>,
        shapes: &mut Vec<(Arc<[crate::surface::SurfaceTemplateGenerator]>, usize)>,
        budget: &mut SyntaxBudget,
    ) -> Result<(), MacroParseFailure> {
        let resource = |error| MacroParseFailure::Syntax {
            diagnostics: Vec::new(),
            resource: Some(error),
        };
        for (index, binding) in bindings.iter().enumerate() {
            let names_live = names.len();
            let shapes_live = shapes.len();
            let names_work = if names_live == names.capacity() {
                names_live.saturating_mul(2).saturating_add(1)
            } else {
                1
            };
            let shapes_work = if shapes_live == shapes.capacity() {
                shapes_live.saturating_mul(2).saturating_add(1)
            } else {
                1
            };
            // Retain the Arc as well as the two list entries and any moves.
            budget
                .charge_units(names_work.saturating_add(shapes_work).saturating_add(1))
                .map_err(resource)?;
            if names_live == names.capacity() {
                names.reserve_exact(1);
            }
            if shapes_live == shapes.capacity() {
                shapes.reserve_exact(1);
            }
            names.push(&binding.name);
            shapes.push((Arc::clone(bindings), index));
        }
        Ok(())
    }
    fn collect<'a>(
        nodes: &'a [MacroOutputNode],
        names: &mut Vec<&'a SurfaceName>,
        shapes: &mut Vec<(Arc<[crate::surface::SurfaceTemplateGenerator]>, usize)>,
        depth: usize,
        budget: &mut SyntaxBudget,
    ) -> Result<(), MacroParseFailure> {
        let resource = |error| MacroParseFailure::Syntax {
            diagnostics: Vec::new(),
            resource: Some(error),
        };
        for node in nodes {
            budget.charge().map_err(resource)?;
            match node {
                MacroOutputNode::Group(_, children, _) => collect(
                    children,
                    names,
                    shapes,
                    type_depth(depth, 1).map_err(resource)?,
                    budget,
                )?,
                MacroOutputNode::TemplateRepeat(repeat) => {
                    if let Some(bindings) = &repeat.generators {
                        record(bindings, names, shapes, budget)?;
                    }
                    collect(
                        &repeat.body,
                        names,
                        shapes,
                        type_depth(depth, 1).map_err(resource)?,
                        budget,
                    )?;
                }
                _ => {}
            }
        }
        Ok(())
    }
    let template = selection
        .declaration
        .template_contents
        .as_deref()
        .ok_or(MacroParseFailure::Invalid)?;
    let mut names = Vec::new();
    let mut shapes = Vec::new();
    if let Some(bindings) = &selection.declaration.generators {
        record(bindings, &mut names, &mut shapes, budget)?;
    }
    collect(template, &mut names, &mut shapes, 0, budget)?;
    if charge_template_inner(
        template,
        &selection.declaration.matcher,
        captures,
        false,
        Some(invocation),
        &names,
        selection.declaration.template_escapes.as_deref(),
        budget,
    )? {
        return Err(MacroParseFailure::Invalid);
    }
    let mut output = template.to_vec();
    let mut planner = GeneratorPlanner {
        plan: GeneratorPlan {
            shapes,
            actions: Vec::new(),
            results: 0,
            captures: Vec::new(),
        },
        active: Vec::new(),
        next_state: 0,
    };
    if let Some(bindings) = &selection.declaration.generators {
        planner
            .enter(bindings, &[], budget)
            .map_err(TemplateSubstitutionFailure::into_macro_failure)?;
    }
    let mut loan = Some(budget);
    substitute_contents_at(
        &mut output,
        &selection.declaration.matcher,
        captures,
        introduction,
        invocation,
        &mut Vec::new(),
        &mut loan,
        &names,
        Some(&mut planner),
        selection.declaration.template_escapes.as_ref(),
        None,
        None,
    )
    .map_err(TemplateSubstitutionFailure::into_macro_failure)?;
    Ok((output, planner.plan))
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

#[derive(Debug)]
pub(crate) enum TemplateSubstitutionFailure {
    Invalid(Span),
    Syntax(Span, crate::parser::MacroParseFailure),
}

impl TemplateSubstitutionFailure {
    fn span(&self) -> Span {
        match self {
            Self::Invalid(span) | Self::Syntax(span, _) => *span,
        }
    }

    pub(crate) fn into_macro_failure(self) -> crate::parser::MacroParseFailure {
        match self {
            Self::Invalid(_) => crate::parser::MacroParseFailure::Invalid,
            Self::Syntax(_, failure) => failure,
        }
    }
}

pub(crate) fn substitute_contents(
    contents: &mut Vec<MacroOutputNode>,
    matcher: &[SurfaceSyntaxMatcherPart],
    captures: &[SurfaceSyntaxCapture],
    introduction: usize,
    invocation: Span,
    mut budget: Option<&mut SyntaxBudget>,
) -> Result<(), TemplateSubstitutionFailure> {
    substitute_contents_at(
        contents,
        matcher,
        captures,
        introduction,
        invocation,
        &mut Vec::new(),
        &mut budget,
        &[],
        None,
        None,
        None,
        None,
    )
}

/// Repetitions can leave a line boundary at the start or adjacent to another
/// boundary. Only the declaration output root is normalized: inner groups,
/// quoted fragments and forwarded declarations keep their original tokens.
pub(crate) fn normalize_declaration_line_ends(
    contents: &mut Vec<MacroOutputNode>,
    budget: &mut SyntaxBudget,
) -> Result<(), ResourceFailure> {
    budget.charge_units(contents.len())?;
    let mut previous_line_end = true;
    contents.retain(|node| {
        let is_line_end = matches!(
            node,
            MacroOutputNode::Token(crate::lexer::TokenKind::LineEnd, _, _)
        );
        let keep = !is_line_end || !previous_line_end;
        previous_line_end = is_line_end;
        keep
    });
    Ok(())
}

fn substitute_contents_at(
    contents: &mut Vec<MacroOutputNode>,
    matcher: &[SurfaceSyntaxMatcherPart],
    captures: &[SurfaceSyntaxCapture],
    introduction: usize,
    invocation: Span,
    indices: &mut Vec<usize>,
    budget: &mut Option<&mut SyntaxBudget>,
    generator_names: &[&SurfaceName],
    mut generator: Option<&mut GeneratorPlanner>,
    escapes: Option<&Arc<[crate::surface::SurfaceTemplateEscape]>>,
    mut admission_identifiers: Option<&mut Vec<SurfaceName>>,
    mut escape_placeholders: Option<&mut Vec<SurfaceName>>,
) -> Result<(), TemplateSubstitutionFailure> {
    let mut position = 0;
    while position < contents.len() {
        if let MacroOutputNode::TemplateRepeat(repeat) = &contents[position] {
            let repeat = Arc::clone(repeat);
            let count = match repetition_length(
                &repeat,
                matcher,
                captures,
                indices,
                indices.len(),
                generator_names,
                escapes.map(Arc::as_ref),
                None,
            ) {
                Ok(count) => count,
                Err(RepetitionFailure::Unknown(name)) => {
                    return Err(TemplateSubstitutionFailure::Syntax(
                        name.span,
                        unknown_capture_failure(name, budget.as_deref_mut()),
                    ));
                }
                Err(failure) => {
                    return Err(TemplateSubstitutionFailure::Invalid(failure.span()));
                }
            };
            let mut pieces = Vec::with_capacity(count);
            let mut output_len = if repeat.separator.is_some() {
                count.saturating_sub(1)
            } else {
                0
            };
            for iteration in 0..count {
                let mut body = repeat.body.clone();
                if indices.len() == indices.capacity() {
                    indices.reserve_exact(1);
                }
                indices.push(iteration);
                let saved = if let Some(generator) = generator.as_deref_mut() {
                    Some(
                        generator.enter_iteration(
                            repeat.generators.as_ref(),
                            indices,
                            budget
                                .as_deref_mut()
                                .expect("generator substitution has a budget"),
                        )?,
                    )
                } else {
                    None
                };
                substitute_contents_at(
                    &mut body,
                    matcher,
                    captures,
                    introduction,
                    invocation,
                    indices,
                    budget,
                    generator_names,
                    generator.as_deref_mut(),
                    escapes,
                    admission_identifiers.as_deref_mut(),
                    escape_placeholders.as_deref_mut(),
                )?;
                if let Some(saved) = saved {
                    generator
                        .as_deref_mut()
                        .expect("generator scope")
                        .leave_iteration(saved);
                }
                indices.pop();
                output_len = output_len.saturating_add(body.len());
                pieces.push(body);
            }
            let mut replacement = Vec::with_capacity(output_len);
            for (iteration, body) in pieces.into_iter().enumerate() {
                if iteration != 0
                    && let Some((kind, spelling, origin)) = &repeat.separator
                {
                    replacement.push(MacroOutputNode::Token(
                        kind.clone(),
                        Arc::clone(spelling),
                        origin.clone(),
                    ));
                }
                replacement.extend(body);
            }
            let emitted = replacement.len();
            if emitted > 1 {
                contents.reserve_exact(emitted - 1);
            }
            contents.splice(position..=position, replacement);
            position += emitted;
            continue;
        }
        let node = &mut contents[position];
        match node {
            MacroOutputNode::Splice(name) => {
                if let Some(generator) = generator.as_deref_mut()
                    && let Some(replacement) = generator.read(
                        name,
                        budget
                            .as_deref_mut()
                            .expect("generator substitution has a budget"),
                    )?
                {
                    *node = replacement;
                    position += 1;
                    continue;
                }
                let capture = match capture_by_name_at(name, matcher, captures, indices) {
                    Ok(capture) => capture,
                    Err(CaptureLookupFailure::Unknown(name)) => {
                        return Err(TemplateSubstitutionFailure::Syntax(
                            name.span,
                            unknown_capture_failure(name, budget.as_deref_mut()),
                        ));
                    }
                    Err(CaptureLookupFailure::Invalid(span)) => {
                        return Err(TemplateSubstitutionFailure::Invalid(span));
                    }
                };
                *node = match capture {
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
                    SurfaceSyntaxCapture::Declaration(capture) => {
                        MacroOutputNode::ForwardedDeclaration(
                            capture.clone(),
                            declaration_capture_origin(capture)
                                .cloned()
                                .unwrap_or_else(|| invocation.into()),
                        )
                    }
                    SurfaceSyntaxCapture::Repeated(_) => {
                        return Err(TemplateSubstitutionFailure::Invalid(name.span));
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
                substitute_contents_at(
                    children,
                    matcher,
                    captures,
                    introduction,
                    invocation,
                    indices,
                    budget,
                    generator_names,
                    generator.as_deref_mut(),
                    escapes,
                    admission_identifiers.as_deref_mut(),
                    escape_placeholders.as_deref_mut(),
                )?;
            }
            MacroOutputNode::TemplateEscape(name) => {
                if let Some(planner) = generator.as_deref_mut() {
                    let Some(escapes) = escapes else {
                        return Err(TemplateSubstitutionFailure::Invalid(name.span));
                    };
                    let Some(budget) = budget.as_deref_mut() else {
                        return Err(TemplateSubstitutionFailure::Invalid(name.span));
                    };
                    *node = planner.escape(name, escapes, matcher, captures, indices, budget)?;
                    position += 1;
                    continue;
                }
                let Some(identifiers) = admission_identifiers.as_deref_mut() else {
                    return Err(TemplateSubstitutionFailure::Invalid(name.span));
                };
                let Some(budget) = budget.as_deref_mut() else {
                    return Err(TemplateSubstitutionFailure::Invalid(name.span));
                };
                let resource = |error| {
                    TemplateSubstitutionFailure::Syntax(
                        name.span,
                        crate::parser::MacroParseFailure::Syntax {
                            diagnostics: Vec::new(),
                            resource: Some(error),
                        },
                    )
                };
                let span = name.span;
                let index = identifiers.len();
                let digits = index.checked_ilog10().map_or(1, |n| n as usize + 1);
                let bytes = "__ash_escape_admission_".len().saturating_add(digits);
                // The temporary name and its list copy both own text.
                budget
                    .charge_units(bytes.saturating_mul(2).saturating_add(2))
                    .map_err(resource)?;
                if identifiers.len() == identifiers.capacity() {
                    let live = identifiers.len();
                    budget
                        .charge_units(live.saturating_mul(2).saturating_add(1))
                        .map_err(resource)?;
                    identifiers.reserve_exact(1);
                } else {
                    budget.charge().map_err(resource)?;
                }
                let placeholder = SurfaceName {
                    text: format!("__ash_escape_admission_{index}"),
                    span,
                    introduction: usize::MAX - index,
                    introduced_at: Some(span),
                    written: false,
                    diagnostic: None,
                };
                identifiers.push(placeholder.clone());
                if let Some(escapes) = escape_placeholders.as_deref_mut() {
                    charge_type_name_copy(&placeholder, 0, budget).map_err(resource)?;
                    if escapes.len() == escapes.capacity() {
                        budget
                            .charge_units(escapes.len().saturating_mul(2).saturating_add(1))
                            .map_err(resource)?;
                        escapes.reserve_exact(1);
                    } else {
                        budget.charge().map_err(resource)?;
                    }
                    escapes.push(placeholder.clone());
                }
                *node = MacroOutputNode::Identifier(placeholder, span.into());
            }
            MacroOutputNode::TemplateRepeat(repeat) => {
                return Err(TemplateSubstitutionFailure::Invalid(
                    repeat.origin.primary(),
                ));
            }
            MacroOutputNode::Token(_, _, _)
            | MacroOutputNode::Expression(_, _)
            | MacroOutputNode::ForwardedExpression(_, _)
            | MacroOutputNode::ForwardedType(_, _)
            | MacroOutputNode::ForwardedDeclaration(_, _)
            | MacroOutputNode::ForwardedPattern(_, _) => {}
        }
        position += 1;
    }
    Ok(())
}

fn declaration_capture_origin(capture: &SurfaceDeclarationCapture) -> Option<&MacroOrigin> {
    match capture.contents.first()? {
        MacroOutputNode::Expression(_, origin)
        | MacroOutputNode::ForwardedExpression(_, origin)
        | MacroOutputNode::ForwardedType(_, origin)
        | MacroOutputNode::ForwardedPattern(_, origin)
        | MacroOutputNode::ForwardedDeclaration(_, origin)
        | MacroOutputNode::Identifier(_, origin)
        | MacroOutputNode::Token(_, _, origin)
        | MacroOutputNode::Group(_, _, origin) => Some(origin),
        MacroOutputNode::Splice(_)
        | MacroOutputNode::TemplateRepeat(_)
        | MacroOutputNode::TemplateEscape(_) => None,
    }
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

    #[test]
    fn unknown_capture_is_distinct_from_malformed_capture_storage() {
        use crate::surface::SurfaceMatcherContainer;

        let source = SourceFile::new("capture.ash", "known missing").unwrap();
        let known_span = source.span(ByteRange::new(0, 5).unwrap()).unwrap();
        let missing_span = source.span(ByteRange::new(6, 13).unwrap()).unwrap();
        let known = SurfaceName {
            text: "known".into(),
            span: known_span,
            introduction: 0,
            introduced_at: None,
            written: true,
            diagnostic: None,
        };
        let missing = SurfaceName {
            text: "missing".into(),
            span: missing_span,
            ..known.clone()
        };
        let matcher = [SurfaceSyntaxMatcherPart::Capture {
            name: known.clone(),
            kind: SurfaceSyntaxCaptureKind::Identifier,
        }];
        assert!(matches!(
            capture_by_name_at(&missing, &matcher, &[], &[]),
            Err(CaptureLookupFailure::Unknown(_))
        ));
        assert!(matches!(
            capture_by_name_at(&known, &matcher, &[], &[]),
            Err(CaptureLookupFailure::Invalid(span)) if span == known_span
        ));
        let repeated_matcher = [SurfaceSyntaxMatcherPart::Container(Arc::new(
            SurfaceMatcherContainer {
                kind: SurfaceMatcherContainerKind::Repeat {
                    one_or_more: true,
                    separator: None,
                },
                body: matcher.to_vec(),
            },
        ))];
        let flat = [SurfaceSyntaxCapture::Identifier(SurfaceIdentifierCapture {
            name: known.clone(),
            origin: known_span.into(),
        })];
        assert!(matches!(
            capture_by_name_at(&known, &repeated_matcher, &flat, &[0]),
            Err(CaptureLookupFailure::Invalid(span)) if span == known_span
        ));
        let empty = [SurfaceSyntaxCapture::Repeated(Arc::new(
            SurfaceRepeatedCapture { values: Vec::new() },
        ))];
        assert!(matches!(
            capture_by_name_at(&known, &repeated_matcher, &empty, &[0]),
            Err(CaptureLookupFailure::Invalid(span)) if span == known_span
        ));
        let mut invalid = vec![MacroOutputNode::Splice(known)];
        assert!(matches!(
            substitute_contents(&mut invalid, &matcher, &[], 0, known_span, None),
            Err(TemplateSubstitutionFailure::Invalid(span)) if span == known_span
        ));
        let mut unknown = vec![MacroOutputNode::Splice(missing)];
        assert!(matches!(
            substitute_contents(&mut unknown, &matcher, &[], 0, known_span, None),
            Err(TemplateSubstitutionFailure::Syntax(
                _,
                crate::parser::MacroParseFailure::Syntax { resource: None, .. }
            ))
        ));
    }

    #[test]
    fn unknown_capture_diagnostic_prepays_its_name_and_retained_location() {
        let source = SourceFile::new("capture.ash", "missing caller definition").unwrap();
        let span = source.span(ByteRange::new(0, 7).unwrap()).unwrap();
        let frame = Arc::new(ExpansionFrame {
            invocation: source.span(ByteRange::new(8, 14).unwrap()).unwrap(),
            definition: source.span(ByteRange::new(15, 25).unwrap()).unwrap(),
        });
        let mut location = DiagnosticLocation::new(span.into());
        location.add_frame(&frame);
        let name = SurfaceName {
            text: "missing".into(),
            span,
            introduction: 0,
            introduced_at: None,
            written: true,
            diagnostic: Some(Box::new(location)),
        };
        let mut measured = SyntaxBudget::default();
        let failure = unknown_capture_failure(&name, Some(&mut measured));
        let cost = measured.consumed();
        let crate::parser::MacroParseFailure::Syntax {
            diagnostics,
            resource: None,
        } = failure
        else {
            panic!("expected an unknown capture diagnostic");
        };
        assert_eq!(diagnostics[0].found.as_deref(), Some("$missing"));
        assert_eq!(diagnostics[0].primary.span(), span);
        let retained = diagnostics[0].primary.diagnostic_location().unwrap();
        assert!(Arc::ptr_eq(&retained.frames[0], &frame));
        let view = crate::presentation::compile_parse_diagnostic(&diagnostics[0], &[&source])
            .expect("the retained source frame is presentable");
        let mut json = Vec::new();
        crate::presentation::write_json(&mut json, &view).unwrap();
        let json: serde_json::Value = serde_json::from_slice(&json).unwrap();
        let labels = json["labels"].as_array().unwrap();
        for (relationship, start, end) in [
            ("unknown_template_capture", 0, 7),
            ("syntax_invocation", 8, 14),
            ("syntax_definition", 15, 25),
        ] {
            assert!(
                labels.iter().any(|label| {
                    label["relationship"] == relationship
                        && label["byte_start"] == start
                        && label["byte_end"] == end
                }),
                "{json}"
            );
        }
        assert!(matches!(
            unknown_capture_failure(&name, Some(&mut SyntaxBudget::with_limit(cost - 1))),
            crate::parser::MacroParseFailure::Syntax {
                diagnostics,
                resource: Some(ResourceFailure::SyntaxWork { .. }),
            } if diagnostics.is_empty()
        ));
        let mut exact = SyntaxBudget::with_limit(cost);
        assert!(matches!(
            unknown_capture_failure(&name, Some(&mut exact)),
            crate::parser::MacroParseFailure::Syntax { resource: None, .. }
        ));
        assert_eq!(exact.consumed(), cost);
    }

    #[test]
    fn selected_type_expression_expansion_uses_one_retryable_loan() {
        use crate::{
            interface::InterfaceConstraintBudget, surface::SurfaceDefinitionKind,
            syntax_resource::ResourceFailure,
        };
        use std::cell::Cell;

        let source = SourceFile::new(
            "expression-templates.ash",
            "pub syntax keep $body:expr => {\n $body\n}\n\
             pub syntax twice $body:expr => {\n $body + $body\n}\n\
             value : Unit -> Int\nvalue () = {\n let copy : Int = 21\n copy\n}\n",
        )
        .unwrap();
        let tree = crate::parser::parse(crate::lexer::lex(&source).unwrap());
        let module = crate::parser::project_module_retaining_templates(&source, &tree).unwrap();
        let SurfaceDefinitionKind::Equational(value) = &module.definitions[0].kind else {
            panic!("expected an equation")
        };
        let expression = value.equations[0].body.clone();
        let selection = |name: &str| {
            let declaration = module
                .syntax_declarations
                .iter()
                .find(|declaration| declaration.name.text == name)
                .unwrap()
                .clone();
            SelectedSyntax {
                name: name.into(),
                import_span: declaration.span,
                declaration,
                owner: 0,
            }
        };
        let keep = selection("keep");
        let twice = selection("twice");
        let span = keep.declaration.span;
        let contents: Arc<[MacroOutputNode]> = Arc::from([MacroOutputNode::ForwardedType(
            SurfaceTypeCapture {
                ty: SurfaceType {
                    kind: SurfaceTypeKind::Int,
                    span,
                    diagnostic: None,
                },
                contents: Arc::from([]),
            },
            span.into(),
        )]);
        let capture = SurfaceSyntaxCapture::Expression(SurfaceExpressionCapture {
            expression: expression.clone(),
            contents: Arc::clone(&contents),
            contains_protected_type: true,
            quote_sites: Default::default(),
        });
        let ordinary = SurfaceSyntaxCapture::Expression(SurfaceExpressionCapture {
            expression,
            contents: Arc::from([]),
            contains_protected_type: false,
            quote_sites: Default::default(),
        });
        let run = |selected: &[SelectedSyntax],
                   capture: &SurfaceSyntaxCapture,
                   loan: Option<&mut SyntaxBudget>| {
            let called = Cell::new(false);
            let mut transformer = |_: &SelectedSyntax,
                                   _: &[SurfaceSyntaxCapture],
                                   _: Span,
                                   _: &SurfaceName,
                                   _: usize,
                                   _: &[Option<usize>],
                                   _: &Arc<ExpansionFrame>,
                                   _: &mut InterfaceConstraintBudget,
                                   _: Option<QuoteExpansionLoan<'_>>|
             -> Result<(ExpandedExpression, usize), Span> {
                called.set(true);
                Err(span)
            };
            let mut expansion = SyntaxExpansion::new(
                &source,
                selected,
                &[],
                Vec::new(),
                loan,
                None,
                &mut transformer,
            );
            let result = expansion.expand(
                &selected[0].declaration.name,
                std::slice::from_ref(capture),
                span,
                &mut InterfaceConstraintBudget::default(),
            );
            let failure = expansion.take_parse_failure();
            let owners = expansion.owners.len();
            drop(expansion);
            (result, failure, owners, called.get())
        };

        let baseline = Arc::strong_count(&contents);
        let mut costs = Vec::new();
        for selected in [keep.clone(), twice.clone()] {
            let mut measured = SyntaxBudget::default();
            measured.charge_units(17).unwrap();
            let (output, failure, owners, called) = run(
                std::slice::from_ref(&selected),
                &capture,
                Some(&mut measured),
            );
            let output = output.expect("the selected Template expands");
            assert!(failure.is_none() && !called);
            assert_eq!(owners, 1);
            let SurfaceExprKind::Block(template) = &output.expression.kind else {
                panic!("the template returns its expression in a block")
            };
            assert!(template.declarations.is_empty());
            if selected.name == "keep" {
                assert!(matches!(template.result.kind, SurfaceExprKind::Block(_)));
            } else {
                let SurfaceExprKind::Add(binary) = &template.result.kind else {
                    panic!("twice must return both captured expressions")
                };
                assert!(matches!(binary.left.kind, SurfaceExprKind::Block(_)));
                assert!(matches!(binary.right.kind, SurfaceExprKind::Block(_)));
            }
            drop(output);
            assert_eq!(Arc::strong_count(&contents), baseline);
            let total = measured.consumed();
            costs.push(total);

            let mut short = SyntaxBudget::with_limit(total - 1);
            short.charge_units(17).unwrap();
            let (output, failure, _, called) =
                run(std::slice::from_ref(&selected), &capture, Some(&mut short));
            assert!(output.is_err() && !called);
            let failure = failure.expect("the shared loan reports its resource failure");
            assert!(matches!(
                failure.resource,
                Some(ResourceFailure::SyntaxWork { .. })
            ));
            assert_eq!(failure.invocation, span);
            assert_eq!(failure.definition, selected.declaration.span);
            assert_eq!(Arc::strong_count(&contents), baseline);
            for _ in 0..2 {
                let mut exact = SyntaxBudget::with_limit(total);
                exact.charge_units(17).unwrap();
                let (output, failure, _, called) =
                    run(std::slice::from_ref(&selected), &capture, Some(&mut exact));
                drop(output.expect("the exact loan succeeds"));
                assert!(failure.is_none() && !called);
                assert_eq!(exact.consumed(), total);
                assert_eq!(Arc::strong_count(&contents), baseline);
            }
        }
        assert!(costs[1] > costs[0]);

        let (output, failure, owners, called) = run(std::slice::from_ref(&keep), &capture, None);
        assert!(output.is_err() && failure.is_none() && !called);
        assert_eq!(owners, 0);
        let mut zero = SyntaxBudget::with_limit(0);
        let (output, failure, _, called) =
            run(std::slice::from_ref(&keep), &ordinary, Some(&mut zero));
        drop(output.expect("an unmarked expression keeps the legacy path"));
        assert!(failure.is_none() && !called);
        assert_eq!(zero.consumed(), 0);

        for wrong_category in [false, true] {
            let mut rejected = keep.clone();
            if wrong_category {
                rejected.declaration.category = SurfaceSyntaxCategory::Declaration;
            } else {
                rejected.declaration.implementation =
                    SurfaceSyntaxImplementation::Transformer(rejected.declaration.name.clone());
            }
            let mut budget = SyntaxBudget::default();
            let (output, failure, owners, called) =
                run(std::slice::from_ref(&rejected), &capture, Some(&mut budget));
            assert!(output.is_err() && failure.is_none() && !called);
            assert_eq!(owners, 0);
            assert_eq!(budget.consumed(), 0);
        }

        // The same paid lookup serves an actual quote invocation and its
        // structural-depth refusal. Exercise a later matching name so the
        // preceding comparison is charged as well.
        let mut quoted = ordinary.clone();
        let SurfaceSyntaxCapture::Expression(quoted_expression) = &mut quoted else {
            unreachable!()
        };
        quoted_expression.quote_sites = crate::surface::CapturedQuoteSites::Owned(Vec::new());
        let selected = [keep, twice.clone()];
        let lookup = |budget: &mut SyntaxBudget| {
            let mut transformer =
                |_: &SelectedSyntax,
                 _: &[SurfaceSyntaxCapture],
                 _: Span,
                 _: &SurfaceName,
                 _: usize,
                 _: &[Option<usize>],
                 _: &Arc<ExpansionFrame>,
                 _: &mut InterfaceConstraintBudget,
                 _: Option<QuoteExpansionLoan<'_>>|
                 -> Result<(ExpandedExpression, usize), Span> { Err(span) };
            let mut expansion = SyntaxExpansion::new(
                &source,
                &selected,
                &[],
                Vec::new(),
                Some(budget),
                None,
                &mut transformer,
            );
            let result = expansion.quoted_selection_span(
                &twice.declaration.name,
                std::slice::from_ref(&quoted),
                span,
            );
            (result, expansion.take_parse_failure())
        };
        let mut measured = SyntaxBudget::default();
        measured.charge_units(17).unwrap();
        let (result, failure) = lookup(&mut measured);
        assert_eq!(result.unwrap(), Some(twice.declaration.span));
        assert!(failure.is_none());
        let total = measured.consumed();
        assert!(total > 17);
        let mut short = SyntaxBudget::with_limit(total - 1);
        short.charge_units(17).unwrap();
        let (result, failure) = lookup(&mut short);
        assert!(result.is_err());
        assert!(matches!(
            failure.unwrap().resource,
            Some(ResourceFailure::SyntaxWork { .. })
        ));
        for _ in 0..2 {
            let mut exact = SyntaxBudget::with_limit(total);
            exact.charge_units(17).unwrap();
            let (result, failure) = lookup(&mut exact);
            assert_eq!(result.unwrap(), Some(twice.declaration.span));
            assert!(failure.is_none());
            assert_eq!(exact.consumed(), total);
        }
    }

    #[test]
    fn type_output_group_copy_preserves_order_origins_and_prepaid_boundaries() {
        use crate::lexer::TokenKind;
        use crate::parser::MacroParseFailure;

        let source = SourceFile::new("type-copy.ash", "Int").unwrap();
        let span = source.span(ByteRange::new(0, 3).unwrap()).unwrap();
        let frame = Arc::new(ExpansionFrame {
            invocation: span,
            definition: span,
        });
        let origin = MacroOrigin::combined(vec![span.into()], Arc::clone(&frame)).unwrap();
        let contents: Arc<[MacroOutputNode]> = Arc::from([]);
        let packet = vec![
            MacroOutputNode::Group(
                MacroDelimiter::Parentheses,
                vec![
                    MacroOutputNode::Token(TokenKind::IntType, "Int".into(), origin.clone()),
                    MacroOutputNode::Group(MacroDelimiter::Braces, Vec::new(), origin.clone()),
                    MacroOutputNode::ForwardedType(
                        SurfaceTypeCapture {
                            ty: SurfaceType {
                                kind: SurfaceTypeKind::Int,
                                span,
                                diagnostic: None,
                            },
                            contents: Arc::clone(&contents),
                        },
                        origin.clone(),
                    ),
                ],
                origin.clone(),
            ),
            MacroOutputNode::Token(TokenKind::IntType, "Int".into(), origin.clone()),
        ];
        let expected = packet.clone();
        let base_contents = Arc::strong_count(&contents);
        let base_frame = Arc::strong_count(&frame);
        let mut measured = SyntaxBudget::default();
        measured.charge_units(17).unwrap();
        let actual = copy_fragment_output(&packet, &mut measured).unwrap();
        let total = measured.consumed();
        assert_eq!(actual, expected);
        let [
            MacroOutputNode::Group(
                _,
                children,
                MacroOrigin::Combined {
                    frame: copied_frame,
                    ..
                },
            ),
            _,
        ] = actual.as_slice()
        else {
            panic!("expected the copied group and following token");
        };
        assert!(Arc::ptr_eq(copied_frame, &frame));
        let MacroOutputNode::ForwardedType(capture, _) = &children[2] else {
            panic!("expected the copied Type fragment");
        };
        assert!(Arc::ptr_eq(&capture.contents, &contents));
        drop(actual);
        assert_eq!(Arc::strong_count(&contents), base_contents);
        assert_eq!(Arc::strong_count(&frame), base_frame);

        let mut short = SyntaxBudget::with_limit(total - 1);
        short.charge_units(17).unwrap();
        assert!(matches!(
            copy_fragment_output(&packet, &mut short),
            Err(MacroParseFailure::Syntax {
                resource: Some(ResourceFailure::SyntaxWork { limit }), ..
            }) if limit == total - 1
        ));
        // Both actual Groups require frame-entry work. The final two-unit
        // reservation refuses as a chunk before any owned copy is made.
        assert_eq!(short.consumed(), total - 2);
        assert_eq!(Arc::strong_count(&contents), base_contents);
        assert_eq!(Arc::strong_count(&frame), base_frame);
        for _ in 0..2 {
            let mut exact = SyntaxBudget::with_limit(total);
            exact.charge_units(17).unwrap();
            assert_eq!(copy_fragment_output(&packet, &mut exact).unwrap(), expected);
            assert_eq!(exact.consumed(), total);
            assert_eq!(Arc::strong_count(&contents), base_contents);
            assert_eq!(Arc::strong_count(&frame), base_frame);
        }
        let mut empty = SyntaxBudget::with_limit(0);
        assert!(copy_fragment_output(&[], &mut empty).unwrap().is_empty());
        assert_eq!(empty.consumed(), 0);
    }

    #[test]
    fn declaration_host_copy_charges_shallow_origin_and_name_retentions() {
        let source = SourceFile::new("origin.ash", "item").unwrap();
        let span = source.span(ByteRange::new(0, 4).unwrap()).unwrap();
        let frame = Arc::new(ExpansionFrame {
            invocation: span,
            definition: span,
        });
        let combined = MacroOrigin::combined(vec![span.into()], Arc::clone(&frame)).unwrap();
        let MacroOrigin::Combined { inputs, .. } = &combined else {
            panic!("combined origin");
        };
        let inputs_before = Arc::strong_count(inputs);
        let frame_before = Arc::strong_count(&frame);
        let mut inspection = SyntaxBudget::with_limit(1);
        charge_type_origin(&combined, 0, &mut inspection).unwrap();
        assert_eq!(inspection.consumed(), 1);
        let mut short = SyntaxBudget::with_limit(2);
        assert!(matches!(
            charge_type_origin_copy(&combined, 0, &mut short),
            Err(ResourceFailure::SyntaxWork { .. })
        ));
        assert_eq!(Arc::strong_count(inputs), inputs_before);
        assert_eq!(Arc::strong_count(&frame), frame_before);
        let mut exact = SyntaxBudget::with_limit(3);
        charge_type_origin_copy(&combined, 0, &mut exact).unwrap();
        let copied = combined.clone();
        assert_eq!(exact.consumed(), 3);
        assert_eq!(Arc::strong_count(inputs), inputs_before + 1);
        assert_eq!(Arc::strong_count(&frame), frame_before + 1);
        drop(copied);

        let name = SurfaceName {
            text: "item".into(),
            span,
            introduction: 0,
            introduced_at: None,
            written: true,
            diagnostic: Some(Box::new(DiagnosticLocation {
                primary: combined.clone(),
                related: vec![combined.clone(), span.into()],
                frames: vec![Arc::clone(&frame)],
                token_cause: false,
                captured_expression: false,
            })),
        };
        let inputs_before = Arc::strong_count(inputs);
        let frame_before = Arc::strong_count(&frame);
        let mut short = SyntaxBudget::with_limit(17);
        assert!(matches!(
            charge_type_name_copy(&name, 0, &mut short),
            Err(ResourceFailure::SyntaxWork { .. })
        ));
        assert_eq!(Arc::strong_count(inputs), inputs_before);
        assert_eq!(Arc::strong_count(&frame), frame_before);
        let mut exact = SyntaxBudget::with_limit(18);
        charge_type_name_copy(&name, 0, &mut exact).unwrap();
        let copied = name.clone();
        assert_eq!(exact.consumed(), 18);
        assert_eq!(Arc::strong_count(inputs), inputs_before + 2);
        assert_eq!(Arc::strong_count(&frame), frame_before + 3);
        drop(copied);
        eprintln!(
            "borrowed origin 1; shallow Combined copy 3; name metadata exact 18 and one-short refusal"
        );
    }

    #[test]
    fn protected_retention_finds_nested_syntax_and_host_bridges() {
        let source = SourceFile::new("bridge.ash", "keep").unwrap();
        let span = source.span(ByteRange::new(0, 4).unwrap()).unwrap();
        let name = SurfaceName {
            text: "keep".into(),
            span,
            introduction: 0,
            introduced_at: None,
            written: true,
            diagnostic: None,
        };
        let ordinary = SurfaceExpr {
            kind: SurfaceExprKind::Unit,
            span,
            diagnostic: None,
        };
        let nested = SurfaceExpressionCapture {
            contains_protected_type: false,
            quote_sites: Default::default(),
            expression: SurfaceExpr {
                kind: SurfaceExprKind::SyntaxInvocation {
                    name,
                    captures: Vec::new(),
                },
                span,
                diagnostic: None,
            },
            contents: Arc::from([]),
        };
        assert!(
            charge_expression_copy(&nested.expression, 0, false, &mut SyntaxBudget::default(),)
                .unwrap()
                .unwrap()
        );
        let retained = Arc::from([MacroOutputNode::Group(
            MacroDelimiter::Parentheses,
            vec![MacroOutputNode::ForwardedExpression(nested, span.into())],
            span.into(),
        )]);
        let expression = SurfaceExpressionCapture {
            contains_protected_type: false,
            quote_sites: Default::default(),
            expression: ordinary.clone(),
            contents: Arc::clone(&retained),
        };
        let pattern = SurfacePatternCapture {
            pattern: SurfacePattern {
                kind: SurfacePatternKind::Wildcard,
                span,
                diagnostic: None,
            },
            contents: Arc::clone(&retained),
        };
        assert!(
            charge_expression_retention(&expression, 0, &mut SyntaxBudget::default())
                .unwrap()
                .unwrap()
        );
        assert!(
            charge_pattern_retention(&pattern, 0, &mut SyntaxBudget::default())
                .unwrap()
                .unwrap()
        );
        for original in [
            MacroOutputNode::ForwardedExpression(expression, span.into()),
            MacroOutputNode::ForwardedPattern(pattern, span.into()),
        ] {
            assert!(
                charge_captured_ep_original(&original, 0, &mut SyntaxBudget::default()).unwrap()
            );
        }
        let host = SurfaceExpressionCapture {
            contains_protected_type: false,
            quote_sites: Default::default(),
            expression: ordinary,
            contents: Arc::from([]),
        };
        let host_original = MacroOutputNode::Expression(host.clone(), span.into());
        assert!(matches!(
            charge_captured_ep_original(&host_original, 0, &mut SyntaxBudget::default()),
            Err(crate::parser::MacroParseFailure::Invalid)
        ));
        let protected = SurfaceExpressionCapture {
            contains_protected_type: false,
            quote_sites: Default::default(),
            expression: host.expression,
            contents: Arc::from([MacroOutputNode::Group(
                MacroDelimiter::Parentheses,
                vec![host_original],
                span.into(),
            )]),
        };
        assert!(
            charge_expression_retention(&protected, 0, &mut SyntaxBudget::default())
                .unwrap()
                .unwrap()
        );
    }

    #[test]
    fn generator_invocation_plans_first_reads_in_capture_iteration_order() {
        let source = SourceFile::new(
            "generator-plan.ash",
            "pub syntax declaration: (make) $( $name:ident ),+ => {\n$( $name : Unit -> Int\n$name () = $first + $number + $number )+\n} with {\n$number from 0 step next_number\n$first from 0 step is_first\n}\n",
        ).unwrap();
        let tree = crate::parser::parse(crate::lexer::lex(&source).unwrap());
        assert!(tree.parse_diagnostics().is_empty());
        let mut initial = SyntaxBudget::default();
        let mut module = crate::parser::project_declaration_expansions(
            &source,
            &tree,
            &[],
            &[],
            &mut Vec::new(),
            &mut initial,
            None,
        )
        .unwrap();
        let declaration = module.syntax_declarations.remove(0);
        let span = declaration.span;
        let selection = SelectedSyntax {
            name: "make".into(),
            declaration,
            owner: 0,
            import_span: span,
        };
        let identifiers = ["one", "two", "three"]
            .into_iter()
            .map(|text| {
                let name = SurfaceName {
                    text: text.into(),
                    span,
                    introduction: 0,
                    introduced_at: None,
                    written: true,
                    diagnostic: None,
                };
                SurfaceSyntaxCapture::Identifier(SurfaceIdentifierCapture {
                    origin: span.into(),
                    name,
                })
            })
            .collect();
        let captures = [SurfaceSyntaxCapture::Repeated(Arc::new(
            SurfaceRepeatedCapture {
                values: identifiers,
            },
        ))];

        fn run(
            selection: &SelectedSyntax,
            captures: &[SurfaceSyntaxCapture],
            budget: &mut SyntaxBudget,
        ) -> Result<(Vec<MacroOutputNode>, GeneratorPlan), crate::parser::MacroParseFailure>
        {
            prepare_generator_template(selection, captures, 1, selection.declaration.span, budget)
        }
        let mut measured = SyntaxBudget::default();
        measured.charge_units(17).unwrap();
        let (output, plan) = run(&selection, &captures, &mut measured).unwrap();
        let used = measured.consumed();
        assert_eq!(plan.results, 6);
        let actions = plan
            .actions
            .iter()
            .map(|action| match action {
                GeneratorAction::Enter {
                    generators,
                    binding,
                    ..
                } => ("enter", generators[*binding].name.text.as_str()),
                GeneratorAction::Advance {
                    generators,
                    binding,
                    ..
                } => ("step", generators[*binding].name.text.as_str()),
                GeneratorAction::Escape {
                    escapes,
                    descriptor,
                    ..
                } => ("escape", escapes[*descriptor].adapter.text.as_str()),
            })
            .collect::<Vec<_>>();
        assert_eq!(
            actions,
            [
                ("enter", "number"),
                ("enter", "first"),
                ("step", "first"),
                ("step", "number"),
                ("step", "first"),
                ("step", "number"),
                ("step", "first"),
                ("step", "number")
            ]
        );
        fn markers(nodes: &[MacroOutputNode], found: &mut Vec<usize>) {
            for node in nodes {
                match node {
                    MacroOutputNode::Group(_, children, _) => markers(children, found),
                    MacroOutputNode::Identifier(name, _)
                        if name.introduction == usize::MAX
                            && name.text.starts_with("\0ash_generator_result_") =>
                    {
                        found.push(
                            name.text["\0ash_generator_result_".len()..]
                                .parse()
                                .unwrap(),
                        )
                    }
                    _ => {}
                }
            }
        }
        let mut found = Vec::new();
        markers(&output, &mut found);
        assert_eq!(found, [0, 1, 1, 2, 3, 3, 4, 5, 5]);
        let mut short = SyntaxBudget::with_limit(used - 1);
        short.charge_units(17).unwrap();
        assert!(run(&selection, &captures, &mut short).is_err());
        for _ in 0..2 {
            let mut exact = SyntaxBudget::with_limit(used);
            exact.charge_units(17).unwrap();
            let (_, retry) = run(&selection, &captures, &mut exact).unwrap();
            assert_eq!(retry.results, 6);
            assert_eq!(exact.consumed(), used);
        }
    }

    #[test]
    fn original_escape_reads_keep_quote_holes_as_ordinary_names() {
        let source = SourceFile::new(
            "early_categories_forms.ash",
            include_str!("../docs/design/macros/fixtures/escapes/early_categories_forms.ash"),
        )
        .unwrap();
        let tree = crate::parser::parse(crate::lexer::lex(&source).unwrap());
        assert!(tree.parse_diagnostics().is_empty());
        let sites = std::cell::RefCell::new(crate::parser::QuoteProjection {
            introduction: 1,
            next_ordinal: 0,
            sites: Vec::new(),
        });
        let mut budget = SyntaxBudget::default();
        let module = crate::parser::project_declaration_expansions_with_quotes(
            &source,
            &tree,
            &[],
            &[],
            &mut Vec::new(),
            &mut budget,
            None,
            Some(&sites),
        )
        .expect("the original escape bodies are projected once");
        let observations = module
            .syntax_declarations
            .iter()
            .map(|declaration| {
                let reads = declaration
                    .template_escapes
                    .as_deref()
                    .unwrap_or(&[])
                    .iter()
                    .map(|escape| {
                        escape
                            .reads
                            .iter()
                            .map(|name| name.text.as_str())
                            .collect::<Vec<_>>()
                    })
                    .collect::<Vec<_>>();
                (declaration.name.text.as_str(), reads)
            })
            .collect::<Vec<_>>();
        assert_eq!(
            observations,
            [
                ("make_expr", vec![vec!["value"]]),
                ("local_capture", vec![vec!["value"]]),
                ("make_ident", vec![vec!["name"], vec!["name"]]),
                ("make_type", vec![vec!["T"], vec!["T"]]),
                ("make_pattern", vec![vec!["pattern"]]),
                ("pass_declaration", vec![vec!["item"]]),
            ]
        );
        let sites = sites.borrow();
        assert!(!sites.sites.is_empty());
        assert!(sites.sites.iter().all(|site| site.callee != 0));
    }

    #[test]
    fn escape_reads_use_completed_matcher_and_repetition_scopes() {
        fn project(text: &str) -> (SourceFile, crate::surface::SurfaceModule) {
            let source = SourceFile::new("escape-scope.ash", text).unwrap();
            let tree = crate::parser::parse(crate::lexer::lex(&source).unwrap());
            assert!(tree.parse_diagnostics().is_empty());
            let sites = std::cell::RefCell::new(crate::parser::QuoteProjection {
                introduction: 1,
                next_ordinal: 0,
                sites: Vec::new(),
            });
            let mut budget = SyntaxBudget::default();
            let module = crate::parser::project_declaration_expansions_with_quotes(
                &source,
                &tree,
                &[],
                &[],
                &mut Vec::new(),
                &mut budget,
                None,
                Some(&sites),
            )
            .unwrap();
            (source, module)
        }

        let (source, module) = project(include_str!(
            "../docs/design/macros/fixtures/escapes/forms.ash"
        ));
        let schema = |name: &str| {
            let declaration = module
                .syntax_declarations
                .iter()
                .find(|declaration| declaration.name.text == name)
                .unwrap();
            resolve_template_escape_reads(declaration, &mut SyntaxBudget::default()).unwrap()
        };
        assert_eq!(
            schema("zip_values")[0].reads,
            [EscapeReadSource::Matcher {
                index: 1,
                kind: SurfaceSyntaxCaptureKind::Expression,
                repetitions: 1,
            }]
        );
        assert_eq!(schema("cached")[0].reads, [EscapeReadSource::Generator]);
        assert_eq!(
            schema("nested_values")[0].reads,
            [
                EscapeReadSource::Matcher {
                    index: 2,
                    kind: SurfaceSyntaxCaptureKind::Expression,
                    repetitions: 2,
                },
                EscapeReadSource::Generator,
            ]
        );

        for name in ["zip_values", "cached", "nested_values"] {
            let declaration = module
                .syntax_declarations
                .iter()
                .find(|declaration| declaration.name.text == name)
                .unwrap();
            validate_quote_template_syntax(
                declaration,
                &source,
                &SyntaxContexts::new(&[], &[], &[]),
                &mut SyntaxBudget::default(),
            )
            .expect("the existing repetition is admitted with its escape reads");
        }

        let zip = module
            .syntax_declarations
            .iter()
            .find(|declaration| declaration.name.text == "zip_values")
            .unwrap();
        let repeat = zip
            .template_contents
            .as_deref()
            .unwrap()
            .iter()
            .find_map(|node| match node {
                MacroOutputNode::TemplateRepeat(repeat) => Some(repeat.as_ref()),
                _ => None,
            })
            .unwrap();
        let span = zip.name.span;
        let identifier = SurfaceSyntaxCapture::Identifier(SurfaceIdentifierCapture {
            name: zip.name.clone(),
            origin: span.into(),
        });
        let expression = SurfaceSyntaxCapture::Expression(SurfaceExpressionCapture {
            expression: SurfaceExpr {
                kind: SurfaceExprKind::Unit,
                span,
                diagnostic: None,
            },
            contains_protected_type: false,
            quote_sites: Default::default(),
            contents: Arc::from([]),
        });
        let repeated = |value: &SurfaceSyntaxCapture, count| {
            SurfaceSyntaxCapture::Repeated(Arc::new(SurfaceRepeatedCapture {
                values: vec![value.clone(); count],
            }))
        };
        let captures = [repeated(&identifier, 2), repeated(&expression, 2)];
        let mismatched = [repeated(&identifier, 2), repeated(&expression, 3)];
        let escapes = zip.template_escapes.as_deref();
        let run = |captures: &[SurfaceSyntaxCapture], budget: &mut SyntaxBudget| {
            repetition_length(
                repeat,
                &zip.matcher,
                captures,
                &[],
                0,
                &[],
                escapes,
                Some(budget),
            )
        };
        let mut measured = SyntaxBudget::default();
        measured.charge_units(17).unwrap();
        assert!(matches!(run(&captures, &mut measured), Ok(2)));
        let total = measured.consumed();
        let mut unequal = SyntaxBudget::default();
        assert!(matches!(
            run(&mismatched, &mut unequal),
            Err(RepetitionFailure::Mismatch(_))
        ));
        let mut short = SyntaxBudget::with_limit(total - 1);
        short.charge_units(17).unwrap();
        assert!(matches!(
            run(&captures, &mut short),
            Err(RepetitionFailure::Resource(_, _))
        ));
        for _ in 0..2 {
            let mut exact = SyntaxBudget::with_limit(total);
            exact.charge_units(17).unwrap();
            assert!(matches!(run(&captures, &mut exact), Ok(2)));
            assert_eq!(exact.consumed(), total);
        }

        let (_, mut invalid) = project(include_str!(
            "../docs/design/macros/fixtures/escapes/out_of_scope_forms.ash"
        ));
        let Err(crate::parser::MacroParseFailure::Syntax { diagnostics, .. }) =
            resolve_template_escape_reads(
                &invalid.syntax_declarations[0],
                &mut SyntaxBudget::default(),
            )
        else {
            panic!("a repeated read outside its repetition must fail at admission");
        };
        assert_eq!(
            diagnostics[0].reason,
            crate::parser::ParseReason::UnknownTemplateCapture
        );

        let declaration = &mut invalid.syntax_declarations[0];
        let descriptors = Arc::get_mut(declaration.template_escapes.as_mut().unwrap()).unwrap();
        let reads = Arc::get_mut(&mut descriptors[0].reads).unwrap();
        let name = &mut reads[0];
        let frame = Arc::new(ExpansionFrame {
            invocation: name.span,
            definition: declaration.span,
        });
        let mut location = DiagnosticLocation::new(name.span.into());
        location.frames.push(Arc::clone(&frame));
        name.diagnostic = Some(Box::new(location));
        let retained = Arc::strong_count(&frame);
        let mut measured = SyntaxBudget::default();
        measured.charge_units(17).unwrap();
        let failure = resolve_template_escape_reads(declaration, &mut measured).unwrap_err();
        assert!(matches!(
            &failure,
            crate::parser::MacroParseFailure::Syntax { resource: None, .. }
        ));
        assert_eq!(Arc::strong_count(&frame), retained + 1);
        drop(failure);
        assert_eq!(Arc::strong_count(&frame), retained);
        let total = measured.consumed();
        let mut short = SyntaxBudget::with_limit(total - 1);
        short.charge_units(17).unwrap();
        assert!(matches!(
            resolve_template_escape_reads(declaration, &mut short),
            Err(crate::parser::MacroParseFailure::Syntax {
                resource: Some(ResourceFailure::SyntaxWork { .. }),
                ..
            })
        ));
        assert_eq!(Arc::strong_count(&frame), retained);
        for _ in 0..2 {
            let mut exact = SyntaxBudget::with_limit(total);
            exact.charge_units(17).unwrap();
            let failure = resolve_template_escape_reads(declaration, &mut exact).unwrap_err();
            assert!(matches!(
                &failure,
                crate::parser::MacroParseFailure::Syntax { resource: None, .. }
            ));
            assert_eq!(exact.consumed(), total);
            drop(failure);
            assert_eq!(Arc::strong_count(&frame), retained);
        }
    }

    #[test]
    fn generator_admission_tracks_owned_scope_and_refuses_duplicate_names() {
        fn check(text: &str) -> Result<(), crate::parser::MacroParseFailure> {
            let source = SourceFile::new("generator-admission.ash", text).unwrap();
            let tree = crate::parser::parse(crate::lexer::lex(&source).unwrap());
            assert!(
                tree.parse_diagnostics().is_empty(),
                "{:?}",
                tree.parse_diagnostics()
            );
            let mut budget = SyntaxBudget::default();
            let module = crate::parser::project_declaration_expansions(
                &source,
                &tree,
                &[],
                &[],
                &mut Vec::new(),
                &mut budget,
                None,
            )
            .unwrap();
            validate_template_syntax_inner(
                &module.syntax_declarations[0],
                &source,
                &SyntaxContexts::new(&[], &[], &[]),
                Some(&mut budget),
            )
        }

        let good = "pub syntax declaration: (make) $( $name:ident ),+ => {\n$( pub $name : Unit -> Int\n$name () = $number )+\n} with { $number from 0 step next }\n";
        check(good).expect("a template generator is visible within its repetition");
        let duplicate = "pub syntax declaration: (make) $( $name:ident ),+ => {\n$( pub $name : Unit -> Int\n$name () = $number )+\n} with {\n$number from 0 step next\n$number from 0 step next\n}\n";
        let Err(crate::parser::MacroParseFailure::Syntax { diagnostics, .. }) = check(duplicate)
        else {
            panic!("a duplicate generator must produce an ordinary parse diagnostic");
        };
        assert_eq!(
            diagnostics[0].expected_form(),
            Some(crate::parser::ExpectedForm::Identifier)
        );
        assert!(diagnostics[0].message().is_some());
        let scope = "pub syntax declaration: (make) $( $name:ident ),+ => {\n$( pub $name : Unit -> Int\n$name () = $number )+ with { $number from 0 step next }\nother : Unit -> Int\nother () = $number\n}\n";
        let Err(crate::parser::MacroParseFailure::Syntax { diagnostics, .. }) = check(scope) else {
            panic!("a repetition-owned generator is unavailable outside its repetition");
        };
        assert_eq!(
            diagnostics[0].reason,
            crate::parser::ParseReason::UnknownTemplateCapture
        );
        let no_driver = "pub syntax declaration: (make) => {\n$( value : Unit -> Int\nvalue () = $number )+\n} with { $number from 0 step next }\n";
        let Err(crate::parser::MacroParseFailure::Syntax { diagnostics, .. }) = check(no_driver)
        else {
            panic!("a generator must not become a repetition driver");
        };
        assert_eq!(
            diagnostics[0].reason,
            crate::parser::ParseReason::RepetitionMissingDriver
        );
    }

    #[test]
    fn generator_admission_uses_the_graph_budget_and_retries() {
        use crate::parser::MacroParseFailure;

        let source = SourceFile::new(
            "generator-admission.ash",
            "pub syntax declaration: (make) $( $name:ident ),+ => {\n$( pub $name : Unit -> Int\n$name () = $number )+\n} with { $number from 0 step next }\n",
        ).unwrap();
        let tree = crate::parser::parse(crate::lexer::lex(&source).unwrap());
        let mut projection_work = SyntaxBudget::default();
        let module = crate::parser::project_declaration_expansions(
            &source,
            &tree,
            &[],
            &[],
            &mut Vec::new(),
            &mut projection_work,
            None,
        )
        .unwrap();
        let declaration = &module.syntax_declarations[0];
        let contexts = SyntaxContexts::new(&[], &[], &[]);
        let mut measured = SyntaxBudget::default();
        validate_quote_template_syntax(declaration, &source, &contexts, &mut measured).unwrap();
        let used = measured.consumed();
        let mut short = SyntaxBudget::with_limit(used - 1);
        assert!(matches!(
            validate_quote_template_syntax(declaration, &source, &contexts, &mut short),
            Err(MacroParseFailure::Syntax {
                resource: Some(ResourceFailure::SyntaxWork { .. }),
                ..
            })
        ));
        let mut spent = SyntaxBudget::with_limit(used);
        spent.charge().unwrap();
        assert!(matches!(
            validate_quote_template_syntax(declaration, &source, &contexts, &mut spent),
            Err(MacroParseFailure::Syntax {
                resource: Some(ResourceFailure::SyntaxWork { .. }),
                ..
            })
        ));
        let mut exact = SyntaxBudget::with_limit(used);
        validate_quote_template_syntax(declaration, &source, &contexts, &mut exact).unwrap();
        assert_eq!(exact.consumed(), used);
    }

    #[test]
    fn duplicate_generator_diagnostics_prepay_real_copies_and_retry() {
        use crate::parser::{ExpectedForm, MacroParseFailure, ParseReason};

        let cases = [
            "pub syntax declaration: (make) $( $name:ident ),+ => {\n$( pub $name : Unit -> Int\n$name () = 42 )+\n} with { $name from 0 step next }\n",
            "pub syntax declaration: (make) $( $name:ident ),+ => {\n$( pub $name : Unit -> Int\n$name () = $number )+\n} with {\n$number from 0 step next\n$number from 0 step next\n}\n",
        ];
        for text in cases {
            let source = SourceFile::new("duplicate-generator.ash", text).unwrap();
            let tree = crate::parser::parse(crate::lexer::lex(&source).unwrap());
            assert!(tree.parse_diagnostics().is_empty());
            let module = crate::parser::project_declaration_expansions(
                &source,
                &tree,
                &[],
                &[],
                &mut Vec::new(),
                &mut SyntaxBudget::default(),
                None,
            )
            .unwrap();
            let declaration = &module.syntax_declarations[0];
            let binding = &declaration
                .generators
                .as_ref()
                .unwrap()
                .last()
                .unwrap()
                .name;
            assert!(binding.diagnostic.is_none());
            let contexts = SyntaxContexts::new(&[], &[], &[]);
            let mut measured = SyntaxBudget::default();
            let Err(MacroParseFailure::Syntax {
                diagnostics,
                resource: None,
            }) = validate_quote_template_syntax(declaration, &source, &contexts, &mut measured)
            else {
                panic!("the duplicate must reach its ordinary diagnostic")
            };
            assert_eq!(diagnostics.len(), 1);
            assert_eq!(diagnostics[0].reason, ParseReason::ExpectedForm);
            assert_eq!(
                diagnostics[0].expected_form(),
                Some(ExpectedForm::Identifier)
            );
            assert_eq!(diagnostics[0].primary.span(), binding.span);
            assert_eq!(diagnostics[0].found.as_deref(), Some(binding.text.as_str()));
            let actual_copy_work = diagnostics[0]
                .primary
                .message()
                .len()
                .saturating_add(diagnostics[0].expected.as_ref().unwrap().len())
                .saturating_add(binding.text.len())
                .saturating_add(1);
            assert_eq!(actual_copy_work, binding.text.len() + 26 + 13 + 1);
            assert_eq!(
                crate::parser::duplicate_template_binding_work(binding),
                actual_copy_work,
            );
            let work = measured.consumed();
            for prefix in [0, 7] {
                let mut short = SyntaxBudget::with_limit(prefix + work - 1);
                short.charge_units(prefix).unwrap();
                assert!(matches!(
                    validate_quote_template_syntax(declaration, &source, &contexts, &mut short),
                    Err(MacroParseFailure::Syntax {
                        diagnostics,
                        resource: Some(ResourceFailure::SyntaxWork { .. }),
                    }) if diagnostics.is_empty()
                ));
                assert_eq!(short.consumed(), prefix + work - actual_copy_work);
                for _ in 0..2 {
                    let mut exact = SyntaxBudget::with_limit(prefix + work);
                    exact.charge_units(prefix).unwrap();
                    let Err(MacroParseFailure::Syntax {
                        diagnostics: actual,
                        resource: None,
                    }) =
                        validate_quote_template_syntax(declaration, &source, &contexts, &mut exact)
                    else {
                        panic!("the exact retry must preserve the original diagnostic")
                    };
                    assert_eq!(actual, diagnostics);
                    assert_eq!(exact.consumed(), prefix + work);
                }
            }
        }
    }

    #[test]
    fn declaration_escape_admission_uses_the_borrowed_budget_at_its_boundary() {
        use crate::parser::MacroParseFailure;

        let source = SourceFile::new(
            "wrong_category_forms.ash",
            include_str!("../docs/design/macros/fixtures/escapes/wrong_category_forms.ash"),
        )
        .unwrap();
        let tree = crate::parser::parse(crate::lexer::lex(&source).unwrap());
        let sites = std::cell::RefCell::new(crate::parser::QuoteProjection {
            introduction: 1,
            next_ordinal: 0,
            sites: Vec::new(),
        });
        let mut staging_budget = SyntaxBudget::default();
        let module = crate::parser::project_declaration_expansions_with_quotes(
            &source,
            &tree,
            &[],
            &[],
            &mut Vec::new(),
            &mut staging_budget,
            None,
            Some(&sites),
        )
        .expect("the actual declaration and escape adapter project");
        let declaration = &module.syntax_declarations[0];
        assert!(declaration.contains_quote_or_escape);
        let contexts = SyntaxContexts::new(&[], &[], &[]);

        let mut measured = SyntaxBudget::default();
        validate_quote_template_syntax(declaration, &source, &contexts, &mut measured)
            .expect("syntax-only admission accepts the escape placeholder");
        let used = measured.consumed();
        assert!(used > 1);

        let mut short = SyntaxBudget::with_limit(used - 1);
        assert!(matches!(
            validate_quote_template_syntax(declaration, &source, &contexts, &mut short),
            Err(MacroParseFailure::Syntax {
                resource: Some(ResourceFailure::SyntaxWork { .. }),
                ..
            })
        ));
        let mut spent = SyntaxBudget::with_limit(used);
        spent.charge().unwrap();
        assert!(matches!(
            validate_quote_template_syntax(declaration, &source, &contexts, &mut spent),
            Err(MacroParseFailure::Syntax {
                resource: Some(ResourceFailure::SyntaxWork { .. }),
                ..
            })
        ));
        let mut exact = SyntaxBudget::with_limit(used);
        validate_quote_template_syntax(declaration, &source, &contexts, &mut exact)
            .expect("the exact remaining graph allowance admits the template");
        assert_eq!(exact.consumed(), used);
    }

    #[test]
    fn declaration_admission_charges_every_literal_matcher_visit() {
        use crate::lexer::TokenKind;
        use crate::parser::MacroParseFailure;

        let source =
            SourceFile::new("empty.ash", "pub syntax declaration: (empty) => {}\n").unwrap();
        let tree = crate::parser::parse(crate::lexer::lex(&source).unwrap());
        let baseline = crate::parser::project_module_retaining_templates(&source, &tree)
            .unwrap()
            .syntax_declarations
            .remove(0);
        assert!(baseline.matcher.is_empty());
        assert!(baseline.template_contents.as_ref().unwrap().is_empty());
        let count = 128;
        let mut literal_heavy = baseline.clone();
        literal_heavy.matcher = (0..count)
            .map(|_| SurfaceSyntaxMatcherPart::Literal {
                kind: TokenKind::Identifier("tag".into()),
                spelling: "tag".into(),
            })
            .collect();
        assert_eq!(literal_heavy.matcher.len(), count);
        assert!(
            literal_heavy
                .matcher
                .iter()
                .all(|part| matches!(part, SurfaceSyntaxMatcherPart::Literal { .. }))
        );
        let contexts = SyntaxContexts::new(&[], &[], &[]);
        let measure = |declaration: &SurfaceSyntaxDeclaration| {
            let mut budget = SyntaxBudget::default();
            validate_template_syntax_inner(declaration, &source, &contexts, Some(&mut budget))
                .expect("the unused empty declaration template is admitted");
            budget.consumed()
        };
        let baseline_cost = measure(&baseline);
        let used = measure(&literal_heavy);
        // The single ordered placeholder walk visits each literal once; the
        // empty output leaves all later work unchanged.
        assert_eq!(used - baseline_cost, count);
        let mut short = SyntaxBudget::with_limit(used - 1);
        assert!(matches!(
            validate_template_syntax_inner(&literal_heavy, &source, &contexts, Some(&mut short)),
            Err(MacroParseFailure::Syntax {
                resource: Some(ResourceFailure::SyntaxWork { .. }),
                ..
            })
        ));
        let mut spent = SyntaxBudget::with_limit(used);
        spent.charge().unwrap();
        assert!(matches!(
            validate_template_syntax_inner(&literal_heavy, &source, &contexts, Some(&mut spent)),
            Err(MacroParseFailure::Syntax {
                resource: Some(ResourceFailure::SyntaxWork { .. }),
                ..
            })
        ));
        let mut fresh = SyntaxBudget::with_limit(used);
        validate_template_syntax_inner(&literal_heavy, &source, &contexts, Some(&mut fresh))
            .expect("the exact fresh admission ledger covers the walk and validation");
        assert_eq!(fresh.consumed(), used);
    }

    #[test]
    fn declaration_admission_refuses_before_placeholder_and_template_copy() {
        use crate::parser::MacroParseFailure;

        let source = SourceFile::new(
            "template.ash",
            "pub syntax declaration: (emit) gate $value:expr => {\nanswer : Unit -> Int\nanswer () = $value\n}\n",
        )
        .unwrap();
        let tree = crate::parser::parse(crate::lexer::lex(&source).unwrap());
        let declaration = crate::parser::project_module_retaining_templates(&source, &tree)
            .unwrap()
            .syntax_declarations
            .remove(0);
        assert!(declaration.matcher.len() > 1);
        let template = Arc::clone(declaration.template_contents.as_ref().unwrap());
        assert!(!template.is_empty());
        let references = Arc::strong_count(&template);
        let contexts = SyntaxContexts::new(&[], &[], &[]);
        let mut short = SyntaxBudget::with_limit(declaration.matcher.len() - 1);
        assert!(matches!(
            validate_template_syntax_inner(&declaration, &source, &contexts, Some(&mut short)),
            Err(MacroParseFailure::Syntax {
                resource: Some(ResourceFailure::SyntaxWork { .. }),
                ..
            })
        ));
        assert_eq!(short.consumed(), 0);
        assert!(Arc::ptr_eq(
            &template,
            declaration.template_contents.as_ref().unwrap()
        ));
        assert_eq!(Arc::strong_count(&template), references);
    }

    #[test]
    fn protected_template_splice_names_use_the_owned_walkers() {
        let source = SourceFile::new("splice.ash", "value").unwrap();
        let span = source.span(ByteRange::new(0, 5).unwrap()).unwrap();
        let name = SurfaceName {
            text: "value".repeat(32),
            span,
            introduction: 0,
            introduced_at: None,
            written: true,
            diagnostic: None,
        };
        let expression = SurfaceExpr {
            kind: SurfaceExprKind::TemplateSplice(name.clone()),
            span,
            diagnostic: None,
        };
        let pattern = SurfacePattern {
            kind: SurfacePatternKind::TemplateSplice(name),
            span,
            diagnostic: None,
        };
        let mut expression_budget = SyntaxBudget::default();
        assert!(
            !charge_expression_copy(&expression, 0, false, &mut expression_budget)
                .unwrap()
                .unwrap()
        );
        let expression_cost = expression_budget.consumed();
        assert!(matches!(
            charge_expression_copy(
                &expression,
                0,
                false,
                &mut SyntaxBudget::with_limit(expression_cost - 1)
            ),
            Err(ResourceFailure::SyntaxWork { .. })
        ));
        charge_expression_copy(
            &expression,
            0,
            false,
            &mut SyntaxBudget::with_limit(expression_cost),
        )
        .unwrap()
        .unwrap();
        let mut pattern_budget = SyntaxBudget::default();
        assert!(
            !charge_pattern_copy(&pattern, 0, false, &mut pattern_budget)
                .unwrap()
                .unwrap()
        );
        let pattern_cost = pattern_budget.consumed();
        assert!(matches!(
            charge_pattern_copy(
                &pattern,
                0,
                false,
                &mut SyntaxBudget::with_limit(pattern_cost - 1)
            ),
            Err(ResourceFailure::SyntaxWork { .. })
        ));
        charge_pattern_copy(
            &pattern,
            0,
            false,
            &mut SyntaxBudget::with_limit(pattern_cost),
        )
        .unwrap()
        .unwrap();
    }

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
    fn nested_declaration_admission_keeps_pattern_and_expression_placeholders() {
        let inner_source = SourceFile::new(
            "inner.ash",
            "pub syntax declaration: (inner) $pattern:pattern yields $body:expr => {}\n",
        )
        .unwrap();
        let inner_tree = crate::parser::parse(crate::lexer::lex(&inner_source).unwrap());
        let original =
            crate::parser::project_module_retaining_templates(&inner_source, &inner_tree)
                .unwrap()
                .syntax_declarations
                .remove(0);
        let outer_source = SourceFile::new(
            "outer.ash",
            "pub syntax declaration: (outer) $pattern:pattern yields $body:expr => {\n    inner $pattern yields $body\n}\n",
        )
        .unwrap();
        let outer_tree = crate::parser::parse(crate::lexer::lex(&outer_source).unwrap());
        let outer = crate::parser::project_module_retaining_templates(&outer_source, &outer_tree)
            .unwrap()
            .syntax_declarations
            .remove(0);
        for transformer in [false, true] {
            let mut declaration = original.clone();
            if transformer {
                declaration.implementation =
                    SurfaceSyntaxImplementation::Transformer(declaration.name.clone());
                declaration.template_contents = None;
            }
            let selected = [SelectedSyntax {
                name: declaration.name.text.clone(),
                owner: 0,
                import_span: declaration.span,
                declaration,
            }];
            let contexts = SyntaxContexts::new(&selected, &[], &[]);
            validate_template_syntax(&outer, &outer_source, &contexts)
                .expect("shape admission does not execute a nested selection");
        }
    }

    #[test]
    fn nested_ep_admission_uses_the_same_exact_retryable_ledger() {
        use crate::parser::MacroParseFailure;

        let inner_source = SourceFile::new(
            "inner.ash",
            "pub syntax declaration: (inner) $pattern:pattern yields $body:expr => {}\n",
        )
        .unwrap();
        let inner_tree = crate::parser::parse(crate::lexer::lex(&inner_source).unwrap());
        let inner = crate::parser::project_module_retaining_templates(&inner_source, &inner_tree)
            .unwrap()
            .syntax_declarations
            .remove(0);
        let selected = [SelectedSyntax {
            name: inner.name.text.clone(),
            owner: 0,
            import_span: inner.span,
            declaration: inner,
        }];
        let contexts = SyntaxContexts::new(&selected, &[], &[]);
        let outer_source = SourceFile::new(
            "outer.ash",
            format!(
                "pub syntax declaration: (outer) $pattern:pattern yields $body:expr => {{\nprior : Unit -> Int\nprior () = 42\ninner $pattern yields {}$body{}\n}}\n",
                "(".repeat(125),
                ")".repeat(125),
            ),
        )
        .unwrap();
        let tree = crate::parser::parse(crate::lexer::lex(&outer_source).unwrap());
        let outer = crate::parser::project_module_retaining_templates(&outer_source, &tree)
            .unwrap()
            .syntax_declarations
            .remove(0);
        let mut measured = SyntaxBudget::default();
        validate_template_syntax_inner(&outer, &outer_source, &contexts, Some(&mut measured))
            .expect("the prior declaration and grouped nested captures are admitted");
        let cost = measured.consumed();
        let mut short = SyntaxBudget::with_limit(cost - 1);
        assert!(matches!(
            validate_template_syntax_inner(&outer, &outer_source, &contexts, Some(&mut short)),
            Err(MacroParseFailure::Syntax {
                resource: Some(ResourceFailure::SyntaxWork { .. }),
                ..
            })
        ));
        let mut exact = SyntaxBudget::with_limit(cost);
        validate_template_syntax_inner(&outer, &outer_source, &contexts, Some(&mut exact))
            .expect("a fresh exact ledger retries the same nested admission");
        assert_eq!(exact.consumed(), cost);
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
                None,
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
                contains_protected_type: false,
                quote_sites: Default::default(),
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

    #[test]
    fn d5_admission_requires_a_retained_template_and_category() {
        let source = SourceFile::new(
            "forms.ash",
            include_str!("../tests/fixtures/surface-macros/declaration-capture/forms.ash"),
        )
        .unwrap();
        let tree = crate::parser::parse(crate::lexer::lex(&source).unwrap());
        let mut declaration = crate::parser::project_module_retaining_templates(&source, &tree)
            .unwrap()
            .syntax_declarations
            .remove(0);
        let contexts = SyntaxContexts::new(&[], &[], &[]);
        validate_template_syntax(&declaration, &source, &contexts).unwrap();
        let span = declaration.span;
        declaration.template_contents = None;
        assert!(matches!(
            validate_template_syntax(&declaration, &source, &contexts),
            Err(crate::parser::MacroParseFailure::Invalid)
        ));
        declaration.template_contents = Some(Arc::from([MacroOutputNode::Token(
            crate::lexer::TokenKind::LineEnd,
            Arc::from("\n"),
            span.into(),
        )]));
        validate_template_syntax(&declaration, &source, &contexts)
            .expect("a line boundary is a valid empty declaration output");
        declaration.template_contents = None;
        declaration.implementation =
            SurfaceSyntaxImplementation::Transformer(declaration.name.clone());
        validate_template_syntax(&declaration, &source, &contexts)
            .expect("a transformer has no template to validate");
        declaration.implementation = SurfaceSyntaxImplementation::Template;
        declaration.template_contents = Some(Arc::from([]));
        declaration.category = crate::surface::SurfaceSyntaxCategory::Expression;
        assert!(matches!(
            validate_template_syntax(&declaration, &source, &contexts),
            Err(crate::parser::MacroParseFailure::Invalid)
        ));
        declaration.matcher.insert(
            0,
            SurfaceSyntaxMatcherPart::Capture {
                name: declaration.name.clone(),
                kind: SurfaceSyntaxCaptureKind::Identifier,
            },
        );
        assert!(matches!(
            validate_template_syntax(&declaration, &source, &contexts),
            Err(crate::parser::MacroParseFailure::Invalid)
        ));
    }

    #[test]
    fn d5_empty_admission_fold_and_parser_share_exact_retryable_budget() {
        use crate::parser::MacroParseFailure;

        let source = SourceFile::new(
            "forms.ash",
            include_str!("../tests/fixtures/surface-macros/declaration-capture/forms.ash"),
        )
        .unwrap();
        let tree = crate::parser::parse(crate::lexer::lex(&source).unwrap());
        let declaration = crate::parser::project_module_retaining_templates(&source, &tree)
            .unwrap()
            .syntax_declarations
            .remove(0);
        let contexts = SyntaxContexts::new(&[], &[], &[]);
        let mut measured = SyntaxBudget::default();
        validate_template_syntax_inner(&declaration, &source, &contexts, Some(&mut measured))
            .unwrap();
        let cost = measured.consumed();
        assert!(cost > declaration.matcher.len());
        let mut short = SyntaxBudget::with_limit(cost - 1);
        assert!(matches!(
            validate_template_syntax_inner(&declaration, &source, &contexts, Some(&mut short)),
            Err(MacroParseFailure::Syntax {
                resource: Some(ResourceFailure::SyntaxWork { .. }),
                ..
            })
        ));
        for _ in 0..2 {
            let mut exact = SyntaxBudget::with_limit(cost);
            validate_template_syntax_inner(&declaration, &source, &contexts, Some(&mut exact))
                .unwrap();
            assert_eq!(exact.consumed(), cost);
        }
    }

    #[test]
    fn d5_expression_header_rejects_declaration_capture_at_its_category() {
        use crate::parser::{ExpectedForm, FoundToken, ParseReason};

        let text = "pub syntax bad $item:declaration => { $item }\n";
        let source = SourceFile::new("invalid-expression-header.ash", text).unwrap();
        let tree = crate::parser::parse(crate::lexer::lex(&source).unwrap());
        let offset = text.find("declaration").unwrap() as u32;
        assert!(
            tree.parse_diagnostics().iter().any(|diagnostic| {
                diagnostic.reason == ParseReason::ExpectedForm
                    && diagnostic.expected_form() == Some(ExpectedForm::Identifier)
                    && diagnostic.found_token() == Some(FoundToken::Identifier)
                    && diagnostic.primary.span().range().start() == offset
            }),
            "{:?}",
            tree.parse_diagnostics()
        );
    }

    #[test]
    fn d5_nested_declaration_in_owned_expression_or_contents_is_invalid_before_copy() {
        use crate::parser::MacroParseFailure;
        use crate::surface::SurfaceDeclarationCapture;

        let source = SourceFile::new("nested.ash", "item").unwrap();
        let span = source.span(ByteRange::new(0, 4).unwrap()).unwrap();
        let name = SurfaceName {
            text: "item".into(),
            span,
            introduction: 0,
            introduced_at: None,
            written: true,
            diagnostic: None,
        };
        let packet: Arc<[MacroOutputNode]> = Arc::from([]);
        let nested = SurfaceExpressionCapture {
            contains_protected_type: false,
            quote_sites: Default::default(),
            expression: SurfaceExpr {
                kind: SurfaceExprKind::SyntaxInvocation {
                    name: name.clone(),
                    captures: vec![SurfaceSyntaxCapture::Declaration(
                        SurfaceDeclarationCapture {
                            contents: Arc::clone(&packet),
                        },
                    )],
                },
                span,
                diagnostic: None,
            },
            contents: Arc::from([]),
        };
        let retained = Arc::strong_count(&packet);
        let mut measured = SyntaxBudget::default();
        assert_eq!(
            charge_expression_copy(&nested.expression, 0, false, &mut measured).unwrap(),
            None
        );
        let cost = measured.consumed();
        assert!(matches!(
            charge_expression_copy(
                &nested.expression,
                0,
                false,
                &mut SyntaxBudget::with_limit(cost - 1)
            ),
            Err(ResourceFailure::SyntaxWork { .. })
        ));
        for _ in 0..2 {
            let mut exact = SyntaxBudget::with_limit(cost);
            assert_eq!(
                charge_expression_copy(&nested.expression, 0, false, &mut exact).unwrap(),
                None
            );
            assert_eq!(exact.consumed(), cost);
        }
        let pattern = SurfacePatternCapture {
            pattern: SurfacePattern {
                kind: SurfacePatternKind::Wildcard,
                span,
                diagnostic: None,
            },
            contents: Arc::from([MacroOutputNode::ForwardedExpression(
                nested.clone(),
                span.into(),
            )]),
        };
        let after_pattern = Arc::strong_count(&packet);
        let mut measured = SyntaxBudget::default();
        assert_eq!(
            charge_pattern_retention(&pattern, 0, &mut measured).unwrap(),
            None
        );
        let cost = measured.consumed();
        assert!(matches!(
            charge_pattern_retention(&pattern, 0, &mut SyntaxBudget::with_limit(cost - 1)),
            Err(ResourceFailure::SyntaxWork { .. })
        ));
        let mut exact = SyntaxBudget::with_limit(cost);
        assert_eq!(
            charge_pattern_retention(&pattern, 0, &mut exact).unwrap(),
            None
        );
        assert_eq!(exact.consumed(), cost);
        let matcher = [SurfaceSyntaxMatcherPart::Capture {
            name: name.clone(),
            kind: SurfaceSyntaxCaptureKind::Expression,
        }];
        let captures = [SurfaceSyntaxCapture::Expression(nested.clone())];
        assert!(matches!(
            charge_declaration_template(
                &[MacroOutputNode::Splice(name)],
                &matcher,
                &captures,
                &mut SyntaxBudget::default()
            ),
            Err(MacroParseFailure::Invalid)
        ));
        let contexts = SyntaxContexts::new(&[], &[], &[]);
        assert!(matches!(
            crate::parser::parse_declaration_template_admission(
                &source,
                span,
                vec![MacroOutputNode::ForwardedExpression(nested, span.into())],
                &contexts,
                &[],
                &mut SyntaxBudget::default(),
            ),
            Err(MacroParseFailure::Invalid)
        ));
        assert_eq!(Arc::strong_count(&packet), after_pattern);
        drop(captures);
        drop(pattern);
        assert_eq!(Arc::strong_count(&packet), retained - 1);
    }

    #[test]
    fn d5_nested_admission_preserves_the_existing_expression_bridge() {
        let inner_source = SourceFile::new(
            "inner.ash",
            "pub syntax declaration: (inner) $body:expr => {}\n",
        )
        .unwrap();
        let inner_tree = crate::parser::parse(crate::lexer::lex(&inner_source).unwrap());
        let inner = crate::parser::project_module_retaining_templates(&inner_source, &inner_tree)
            .unwrap()
            .syntax_declarations
            .remove(0);
        let selected = [SelectedSyntax {
            name: inner.name.text.clone(),
            owner: 0,
            import_span: inner.span,
            declaration: inner,
        }];
        let contexts = SyntaxContexts::new(&selected, &[], &[]);
        let source = SourceFile::new(
            "outer.ash",
            "pub syntax declaration: (outer) $body:expr => {\n    inner $body\n}\n",
        )
        .unwrap();
        let tree = crate::parser::parse(crate::lexer::lex(&source).unwrap());
        let outer = crate::parser::project_module_retaining_templates(&source, &tree)
            .unwrap()
            .syntax_declarations
            .remove(0);
        let capture = SurfaceExpressionCapture {
            contains_protected_type: false,
            quote_sites: Default::default(),
            expression: SurfaceExpr {
                kind: SurfaceExprKind::SyntaxInvocation {
                    name: outer.name.clone(),
                    captures: Vec::new(),
                },
                span: outer.span,
                diagnostic: None,
            },
            contents: Arc::from([]),
        };
        assert_eq!(
            charge_expression_retention(&capture, 0, &mut SyntaxBudget::default()).unwrap(),
            Some(true)
        );
        let mut output = outer.template_contents.as_ref().unwrap().to_vec();
        substitute_contents(
            &mut output,
            &outer.matcher,
            &[SurfaceSyntaxCapture::Expression(capture)],
            0,
            outer.span,
            None,
        )
        .unwrap();
        crate::parser::parse_declaration_template_admission(
            &source,
            outer.span,
            output,
            &contexts,
            &[],
            &mut SyntaxBudget::default(),
        )
        .expect("D6 admits the protected bridge without executing it");
    }

    #[test]
    fn d5_declaration_splice_precharges_and_forwards_the_same_packet() {
        let source = SourceFile::new("capture.ash", "item").unwrap();
        let span = source.span(ByteRange::new(0, 4).unwrap()).unwrap();
        let name = SurfaceName {
            text: "item".into(),
            span,
            introduction: 0,
            introduced_at: None,
            written: true,
            diagnostic: None,
        };
        let matcher = [SurfaceSyntaxMatcherPart::Capture {
            name: name.clone(),
            kind: SurfaceSyntaxCaptureKind::Declaration,
        }];
        let captures = [SurfaceSyntaxCapture::Declaration(
            crate::surface::SurfaceDeclarationCapture {
                contents: Arc::from([MacroOutputNode::Token(
                    crate::lexer::TokenKind::IntType,
                    Arc::from("Int"),
                    span.into(),
                )]),
            },
        )];
        let mut output = vec![MacroOutputNode::Splice(name)];
        let [SurfaceSyntaxCapture::Declaration(packet)] = &captures else {
            unreachable!()
        };
        let retained = Arc::strong_count(&packet.contents);
        let mut measured = SyntaxBudget::default();
        charge_declaration_template(&output, &matcher, &captures, &mut measured).unwrap();
        let cost = measured.consumed();
        assert!(matches!(
            charge_declaration_template(
                &output,
                &matcher,
                &captures,
                &mut SyntaxBudget::with_limit(cost - 1),
            ),
            Err(crate::parser::MacroParseFailure::Syntax {
                resource: Some(ResourceFailure::SyntaxWork { .. }),
                ..
            })
        ));
        assert_eq!(Arc::strong_count(&packet.contents), retained);
        assert!(matches!(output.as_slice(), [MacroOutputNode::Splice(_)]));
        let mut exact = SyntaxBudget::with_limit(cost);
        charge_declaration_template(&output, &matcher, &captures, &mut exact).unwrap();
        assert_eq!(exact.consumed(), cost);
        substitute_contents(&mut output, &matcher, &captures, 0, span, None).unwrap();
        let [MacroOutputNode::ForwardedDeclaration(forwarded, origin)] = output.as_slice() else {
            panic!("declaration splice must remain a typed packet");
        };
        assert!(Arc::ptr_eq(&packet.contents, &forwarded.contents));
        assert_eq!(origin.primary(), span);
        assert_eq!(Arc::strong_count(&packet.contents), retained + 1);
        drop(output);
        assert_eq!(Arc::strong_count(&packet.contents), retained);
    }
}
