//! Original declaration coordinates reconstructed from resident source text.
//!
//! This syntax-only check grants no semantic or executable authority. In
//! particular, a retained nominal/effect ID cannot choose its defining slot.

mod coordinate_loan;

pub(crate) use coordinate_loan::DeclarationCoordinateLoan;

use std::collections::{HashMap, HashSet};

use super::{ValidationError, ValidationReason};
use crate::{
    lexer::{Token, TokenKind, lex_with_budget},
    module::ModuleId,
    parser::{
        ConcreteElement, ConcreteNode, ConcreteTree, NodeKind, STRUCTURAL_DEPTH_LIMIT,
        parse_with_budget, source_structural_weight,
    },
    resolved::{ResolvedNominalDeclarationKind, ResolvedRegistry},
    source::{Origin, SourceFile, SourceId, Span},
    syntax_resource::SyntaxBudget,
    types::{ConstructorId, EffectId, Kind, NominalTypeId, TypeVariableId, TypeWorkBudget},
};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct LibraryCoordinate {
    span: Span,
    name: Span,
    ordinal: u32,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum NominalRole {
    Data { newtype: bool, constructors: usize },
    Resource { source: bool, ordinal: u32 },
}

#[derive(Clone, Copy, Debug)]
struct NominalCoordinate {
    origin: Span,
    name: Span,
    role: NominalRole,
}

#[derive(Clone, Copy, Debug)]
struct ConstructorCoordinate {
    owner: u32,
    ordinal: u32,
    origin: Span,
}

#[derive(Clone, Copy, Debug)]
struct SymbolCoordinate {
    library: LibraryCoordinate,
    member: usize,
    symbol: usize,
}

#[derive(Clone, Copy, Debug)]
struct EffectCoordinate {
    origin: Span,
    span: Span,
    name: Span,
    foreign: Option<SymbolCoordinate>,
}

#[derive(Default)]
/// Readonly declaration provenance reconstructed from resident source syntax.
/// These coordinates contain no inferred callable requirements or executable code.
pub(crate) struct DeclarationCoordinates {
    nominals: Vec<NominalCoordinate>,
    nominal_origins: HashMap<Span, usize>,
    constructors: Vec<ConstructorCoordinate>,
    constructor_origins: HashMap<Span, usize>,
    effects: Vec<EffectCoordinate>,
    effect_origins: HashMap<Span, usize>,
    resource_binders: ResourceBinderCoordinates,
}

fn registry() -> ValidationError {
    ValidationError::new(ValidationReason::Registry, None)
}

fn resource() -> ValidationError {
    ValidationError::new(ValidationReason::Resource, None)
}

fn charge(work: &mut TypeWorkBudget, amount: usize) -> Result<(), ValidationError> {
    work.charge(amount).map_err(|()| resource())
}

fn push<T>(rows: &mut Vec<T>, value: T, work: &mut TypeWorkBudget) -> Result<(), ValidationError> {
    charge(work, 1)?;
    rows.try_reserve(1).map_err(|_| resource())?;
    rows.push(value);
    Ok(())
}

fn ordinal(value: usize) -> Result<u32, ValidationError> {
    u32::try_from(value).map_err(|_| registry())
}

fn syntax(source: &SourceFile, work: &mut TypeWorkBudget) -> Result<ConcreteTree, ValidationError> {
    // The byte scan and the retained syntax share the caller's cumulative
    // allowance. Return spent syntax before examining any result or tree.
    charge(work, source.text().len())?;
    let mut loan = SyntaxBudget::loan(work.remaining());
    let parsed =
        lex_with_budget(source, &mut loan).map(|lexed| parse_with_budget(lexed, &mut loan));
    charge(work, loan.consumed())?;
    let tree = parsed.map_err(|_| registry())?;
    if tree.resource_failure().is_some() {
        return Err(resource());
    }
    if tree.malformed.is_some()
        || !tree.lexical_diagnostics().is_empty()
        || !tree.parse_diagnostics().is_empty()
    {
        return Err(registry());
    }
    validate_tree(source, &tree, work)?;
    Ok(tree)
}

fn validate_tree(
    source: &SourceFile,
    tree: &ConcreteTree,
    work: &mut TypeWorkBudget,
) -> Result<(), ValidationError> {
    let root = tree.root().ok_or_else(registry)?;
    if root.kind != NodeKind::Module {
        return Err(registry());
    }
    let mut pending = Vec::new();
    push(&mut pending, (root, 0usize), work)?;
    let mut next_token = 0;
    while let Some((node, depth)) = pending.pop() {
        // structural_weight inspects only direct children. Charge those visits
        // as well as the following complete traversal before either begins.
        charge(
            work,
            node.children.len().checked_mul(2).ok_or_else(resource)?,
        )?;
        let depth = depth
            .checked_add(source_structural_weight(node))
            .ok_or_else(resource)?;
        if depth > STRUCTURAL_DEPTH_LIMIT {
            return Err(resource());
        }
        // Parser construction authenticates token coverage/order. This paid
        // walk independently preserves the projection's weighted depth check.
        for child in node.children.iter().rev() {
            match child {
                ConcreteElement::Node(child) => push(&mut pending, (child, depth), work)?,
                ConcreteElement::Missing { .. } | ConcreteElement::Error(_) => {
                    return Err(registry());
                }
                ConcreteElement::Token(_) => {}
            }
        }
    }
    // Parser construction checks token coverage/order. This fresh canonical
    // tree cannot be supplied by a caller; still validate every source range.
    for token in tree.tokens() {
        charge(work, 1)?;
        if token.span.source() != source.id()
            || source.span(token.span.range()).is_err()
            || token.span.range().start() < next_token
        {
            return Err(registry());
        }
        next_token = token.span.range().end();
    }
    if !matches!(tree.tokens().last(), Some(Token { kind: TokenKind::EndOfFile, span })
        if span.range().start() as usize == source.text().len()
            && span.range().end() as usize == source.text().len())
    {
        return Err(registry());
    }
    Ok(())
}

fn edge(
    mut node: &ConcreteNode,
    tokens: &[Token],
    back: bool,
    work: &mut TypeWorkBudget,
) -> Result<Span, ValidationError> {
    loop {
        charge(work, 1)?;
        let child = if back {
            node.children.last()
        } else {
            node.children.first()
        }
        .ok_or_else(registry)?;
        match child {
            ConcreteElement::Node(child) => node = child,
            ConcreteElement::Token(index) => {
                return tokens
                    .get(*index)
                    .map(|token| token.span)
                    .ok_or_else(registry);
            }
            ConcreteElement::Missing { .. } | ConcreteElement::Error(_) => return Err(registry()),
        }
    }
}

fn span(
    node: &ConcreteNode,
    tokens: &[Token],
    work: &mut TypeWorkBudget,
) -> Result<Span, ValidationError> {
    edge(node, tokens, false, work)?
        .cover(edge(node, tokens, true, work)?)
        .ok_or_else(registry)
}

fn name(
    node: &ConcreteNode,
    tokens: &[Token],
    work: &mut TypeWorkBudget,
) -> Result<Span, ValidationError> {
    for child in &node.children {
        charge(work, 1)?;
        if let ConcreteElement::Token(index) = child {
            let token = tokens.get(*index).ok_or_else(registry)?;
            if matches!(token.kind, TokenKind::UpperIdentifier(_)) {
                return Ok(token.span);
            }
        }
    }
    Err(registry())
}

fn text(source: &SourceFile, span: Span) -> Result<&str, ValidationError> {
    if span.source() != source.id() {
        return Err(registry());
    }
    source
        .text()
        .get(span.range().start() as usize..span.range().end() as usize)
        .ok_or_else(registry)
}

fn same_name(
    source: &SourceFile,
    coordinate: Span,
    spelling: &str,
    work: &mut TypeWorkBudget,
) -> Result<bool, ValidationError> {
    charge(work, spelling.len())?;
    Ok(text(source, coordinate)? == spelling)
}

fn original_span(mut origin: &Origin, work: &mut TypeWorkBudget) -> Result<Span, ValidationError> {
    loop {
        charge(work, 1)?;
        match origin {
            Origin::Source(span) => return Ok(*span),
            Origin::Generated { cause, .. } => origin = cause,
            Origin::Related { primary, .. } => origin = primary,
        }
    }
}

// These coordinates classify only the written generative binding site. They
// grant no executable scope, native, capture or ownership authority. Canonical
// source-origin binder records remain exact; this is no generated-Core renaming
// permission and prescribes no new global allocator replay.
#[derive(Clone, Copy)]
struct ResourceBinderCoordinate {
    scope: Span,
    family: Option<Span>,
    argument: Span,
    position: usize,
    arguments: usize,
}

#[derive(Default)]
struct ResourceBinderCoordinates {
    bindings: Vec<ResourceBinderCoordinate>,
}

impl ResourceBinderCoordinates {
    fn from_tree(
        root: &ConcreteNode,
        tokens: &[Token],
        work: &mut TypeWorkBudget,
    ) -> Result<Self, ValidationError> {
        let mut result = Self::default();
        let mut pending = Vec::new();
        push(&mut pending, root, work)?;
        while let Some(node) = pending.pop() {
            charge(work, node.children.len())?;
            for child in &node.children {
                if let ConcreteElement::Node(child) = child {
                    push(&mut pending, child, work)?;
                }
            }
            if node.kind == NodeKind::ResourceExpression {
                charge(work, node.children.len())?;
                let mut identity = None;
                for child in &node.children {
                    if let ConcreteElement::Token(index) = child {
                        let token = tokens.get(*index).ok_or_else(registry)?;
                        if matches!(token.kind, TokenKind::UpperIdentifier(_))
                            && identity.replace(token.span).is_some()
                        {
                            return Err(registry());
                        }
                    }
                }
                push(
                    &mut result.bindings,
                    ResourceBinderCoordinate {
                        scope: span(node, tokens, work)?,
                        family: None,
                        argument: identity.ok_or_else(registry)?,
                        position: 0,
                        arguments: 1,
                    },
                    work,
                )?;
            }
        }
        Ok(result)
    }

    fn authenticate(
        &self,
        registry: &ResolvedRegistry,
        module: ModuleId,
        source: &SourceFile,
        work: &mut TypeWorkBudget,
        admitted: &mut HashSet<TypeVariableId>,
    ) -> Result<(), ValidationError> {
        let mut binding_spans = HashMap::new();
        for binder in &self.bindings {
            charge(work, 1)?;
            let selected = Some((0, 1));
            let Some((owned, count)) = selected else {
                continue;
            };
            if owned != binder.position {
                continue;
            }
            if count != binder.arguments
                || binder.argument.source() != source.id()
                || binder.scope.source() != source.id()
                || binder.argument.range().start() < binder.scope.range().start()
                || binder.argument.range().end() > binder.scope.range().end()
                || !super::valid_upper_spelling(text(source, binder.argument)?)
            {
                return Err(registry_error());
            }
            charge(work, 1)?;
            binding_spans.try_reserve(1).map_err(|_| resource())?;
            if binding_spans
                .insert(binder.argument, binder.scope)
                .is_some()
            {
                return Err(registry_error());
            }
        }
        if binding_spans.is_empty() {
            return Ok(());
        }
        let mut found = HashSet::new();
        charge(work, registry.type_variable_count())?;
        for parameter in registry.type_variables() {
            if parameter.id.module() != Some(module) {
                continue;
            }
            let origin = parameter.origin.primary_span();
            charge(work, 1)?;
            if binding_spans.contains_key(&origin) {
                if !matches!(&parameter.origin, Origin::Source(span) if *span == origin)
                    || parameter.kind != Kind::Type
                    || !same_name(source, origin, &parameter.spelling, work)?
                    || registry
                        .type_variable(parameter.id)
                        .is_none_or(|canonical| !std::ptr::eq(canonical, parameter))
                {
                    return Err(registry_error());
                }
                charge(work, 2)?;
                admitted.try_reserve(1).map_err(|_| resource())?;
                found.try_reserve(1).map_err(|_| resource())?;
                if !admitted.insert(parameter.id) || !found.insert(origin) {
                    return Err(registry_error());
                }
            }
        }
        // An importing original can retain a resource declaration without the
        // dependency's unrelated bodies or their fresh binders. Authenticate
        // every retained matching record; the source file is not a census of
        // the projected registry. Ordinary scope/type checks still require the
        // canonical record for every identity actually used by the forest.
        Ok(())
    }

    fn unused_candidates(
        &self,
        registry: &ResolvedRegistry,
        module: ModuleId,
        source: &SourceFile,
        work: &mut TypeWorkBudget,
        candidates: &mut HashSet<TypeVariableId>,
    ) -> Result<(), ValidationError> {
        let mut coordinates = HashSet::new();
        for binder in &self.bindings {
            charge(work, 1)?;
            if !super::valid_upper_spelling(text(source, binder.argument)?) {
                continue;
            }
            if binder.scope.source() != source.id()
                || !super::span_contains(binder.scope, binder.argument)
            {
                return Err(registry_error());
            }
            coordinates.try_reserve(1).map_err(|_| resource())?;
            if !coordinates.insert(binder.argument) {
                return Err(registry_error());
            }
        }
        let mut found = HashSet::new();
        charge(work, registry.type_variable_count())?;
        for parameter in registry.type_variables() {
            if parameter.id.module() != Some(module) {
                continue;
            }
            let origin = parameter.origin.primary_span();
            charge(work, 1)?;
            if !coordinates.contains(&origin) {
                continue;
            }
            if parameter.kind != Kind::Type
                || !matches!(&parameter.origin, Origin::Source(span) if *span == origin)
                || !same_name(source, origin, &parameter.spelling, work)?
                || registry
                    .type_variable(parameter.id)
                    .is_none_or(|canonical| !std::ptr::eq(canonical, parameter))
            {
                return Err(registry_error());
            }
            charge(work, 2)?;
            found.try_reserve(1).map_err(|_| resource())?;
            candidates.try_reserve(1).map_err(|_| resource())?;
            if !found.insert(origin) || !candidates.insert(parameter.id) {
                return Err(registry_error());
            }
        }
        // This is only a coordinate candidate. Complete current-forest non-use
        // and formal disjointness must hold before written-order classification.
        Ok(())
    }
}

impl DeclarationCoordinates {
    /// Reconstructs syntax coordinates for an exact defining module/source pair.
    /// The compiler-owned Foreign text has compile-time syntax coordinates;
    /// every consuming registry still proves its semantic correspondence.
    fn from_module_source(
        module: ModuleId,
        source: &SourceFile,
        work: &mut TypeWorkBudget,
    ) -> Result<Self, ValidationError> {
        if module.is_builtin_foreign() {
            charge(work, source.text().len())?;
            if source.text() != crate::module::foreign_builtin_source_text() {
                return Err(registry());
            }
        }
        Self::from_source(source, work)
    }

    pub(crate) fn from_source(
        source: &SourceFile,
        work: &mut TypeWorkBudget,
    ) -> Result<Self, ValidationError> {
        let tree = syntax(source, work)?;
        let root = tree.root().ok_or_else(registry)?;
        let tokens = tree.tokens();
        let mut result = Self {
            resource_binders: ResourceBinderCoordinates::from_tree(root, tokens, work)?,
            ..Self::default()
        };
        let mut ordinary_resources = Vec::new();
        let mut next_library = 0usize;
        for element in &root.children {
            charge(work, 1)?;
            let ConcreteElement::Node(node) = element else {
                continue;
            };
            match node.kind {
                NodeKind::TypeDeclaration | NodeKind::NewtypeDeclaration => {
                    let owner = ordinal(result.nominals.len())?;
                    let mut constructors = 0usize;
                    for child in &node.children {
                        charge(work, 1)?;
                        if let ConcreteElement::Node(child) = child
                            && child.kind == NodeKind::ConstructorDeclaration
                        {
                            let coordinate = ConstructorCoordinate {
                                owner,
                                ordinal: ordinal(constructors)?,
                                origin: span(child, tokens, work)?,
                            };
                            push(&mut result.constructors, coordinate, work)?;
                            constructors = constructors.checked_add(1).ok_or_else(resource)?;
                        }
                    }
                    let coordinate = NominalCoordinate {
                        origin: span(node, tokens, work)?,
                        name: name(node, tokens, work)?,
                        role: NominalRole::Data {
                            newtype: node.kind == NodeKind::NewtypeDeclaration,
                            constructors,
                        },
                    };
                    push(&mut result.nominals, coordinate, work)?;
                }
                NodeKind::ResourceDefinition => {
                    let name = name(node, tokens, work)?;
                    push(
                        &mut ordinary_resources,
                        NominalCoordinate {
                            origin: name,
                            name,
                            role: NominalRole::Resource {
                                source: false,
                                ordinal: 0,
                            },
                        },
                        work,
                    )?;
                }
                NodeKind::EffectDeclaration => {
                    let name = name(node, tokens, work)?;
                    let coordinate = EffectCoordinate {
                        origin: name,
                        span: span(node, tokens, work)?,
                        name,
                        foreign: None,
                    };
                    push(&mut result.effects, coordinate, work)?;
                }
                NodeKind::ForeignLibrary => {
                    result.library(node, tokens, ordinal(next_library)?, work)?;
                    next_library = next_library.checked_add(1).ok_or_else(resource)?;
                }
                _ => {}
            }
        }
        for (index, mut coordinate) in ordinary_resources.into_iter().enumerate() {
            charge(work, 1)?;
            let NominalRole::Resource { source, .. } = coordinate.role else {
                return Err(registry());
            };
            coordinate.role = NominalRole::Resource {
                source,
                ordinal: ordinal(index)?,
            };
            push(&mut result.nominals, coordinate, work)?;
        }

        for (index, coordinate) in result.nominals.iter().enumerate() {
            charge(work, 1)?;
            result
                .nominal_origins
                .try_reserve(1)
                .map_err(|_| resource())?;
            if result
                .nominal_origins
                .insert(coordinate.origin, index)
                .is_some()
            {
                return Err(registry());
            }
        }
        for (index, coordinate) in result.effects.iter().enumerate() {
            charge(work, 1)?;
            result
                .effect_origins
                .try_reserve(1)
                .map_err(|_| resource())?;
            if result
                .effect_origins
                .insert(coordinate.origin, index)
                .is_some()
            {
                return Err(registry());
            }
        }
        for (index, coordinate) in result.constructors.iter().enumerate() {
            charge(work, 1)?;
            result
                .constructor_origins
                .try_reserve(1)
                .map_err(|_| resource())?;
            if result
                .constructor_origins
                .insert(coordinate.origin, index)
                .is_some()
            {
                return Err(registry());
            }
        }
        Ok(result)
    }

    fn library(
        &mut self,
        node: &ConcreteNode,
        tokens: &[Token],
        ordinal: u32,
        work: &mut TypeWorkBudget,
    ) -> Result<(), ValidationError> {
        let library = LibraryCoordinate {
            span: span(node, tokens, work)?,
            name: name(node, tokens, work)?,
            ordinal,
        };
        let (mut member, mut symbol) = (0usize, 0usize);
        for element in &node.children {
            charge(work, 1)?;
            let ConcreteElement::Node(child) = element else {
                continue;
            };
            if child.kind != NodeKind::ForeignMember {
                return Err(registry());
            }
            charge(work, 1)?;
            let Some(ConcreteElement::Token(first)) = child.children.first() else {
                return Err(registry());
            };
            let Some(Token {
                kind: TokenKind::Identifier(word),
                ..
            }) = tokens.get(*first)
            else {
                return Err(registry());
            };
            match word.as_str() {
                "symbol" => {
                    let origin = span(child, tokens, work)?;
                    let coordinate = EffectCoordinate {
                        origin,
                        span: origin,
                        name: name(child, tokens, work)?,
                        foreign: Some(SymbolCoordinate {
                            library,
                            member,
                            symbol,
                        }),
                    };
                    push(&mut self.effects, coordinate, work)?;
                    symbol = symbol.checked_add(1).ok_or_else(resource)?;
                }
                _ => {}
            }
            member = member.checked_add(1).ok_or_else(resource)?;
        }
        Ok(())
    }

    pub(crate) fn authenticate_effect(
        &self,
        module: ModuleId,
        source: &SourceFile,
        effect: &crate::resolved::ResolvedEffectDeclaration,
        work: &mut TypeWorkBudget,
    ) -> Result<(), ValidationError> {
        charge(work, 1)?;
        let origin = original_span(&effect.origin, work)?;
        let expected = *self
            .effect_origins
            .get(&origin)
            .ok_or_else(registry_error)?;
        let coordinate = &self.effects[expected];
        if effect.id != EffectId::new(module, ordinal(expected)?)
            || effect.span != coordinate.span
            || effect.native_contract.is_some() != coordinate.foreign.is_some()
            || !same_name(source, coordinate.name, &effect.spelling, work)?
        {
            return Err(registry_error());
        }
        if let Some(written) = coordinate.foreign {
            let symbol = effect.native_contract.as_ref().ok_or_else(registry_error)?;
            let prepared = symbol.prepared();
            charge(work, 1)?;
            let declaration = prepared
                .symbols()
                .get(written.symbol)
                .ok_or_else(registry_error)?;
            if prepared.module() != module
                || symbol.symbol_index() != written.symbol
                || symbol.library()
                    != crate::foreign::checked_source::NativeLibraryId::new(
                        module,
                        written.library.ordinal,
                    )
                || original_span(prepared.origin(), work)? != written.library.span
                || declaration.member_index() != written.member
                || original_span(declaration.origin(), work)? != coordinate.origin
                || !same_name(source, written.library.name, prepared.name(), work)?
                || !same_name(source, coordinate.name, declaration.name(), work)?
            {
                return Err(registry_error());
            }
        }
        Ok(())
    }

    fn nominal(
        &self,
        origin: Span,
        work: &mut TypeWorkBudget,
    ) -> Result<(u32, &NominalCoordinate), ValidationError> {
        charge(work, 1)?;
        let index = *self.nominal_origins.get(&origin).ok_or_else(registry)?;
        Ok((ordinal(index)?, &self.nominals[index]))
    }
}

/// Successful defining-source correspondence for this one immutable registry.
/// These positions account for declaration slots omitted by an import view;
/// they do not supply a declaration, type, scope, or executable permission.
#[derive(Debug, Default)]
pub(super) struct OriginalDeclarationProvenance {
    pub(super) generatives: HashSet<TypeVariableId>,
    // Coordinates alone grant nothing: the validator separately proves
    // complete semantic non-use and formal disjointness for the current forest.
    pub(super) ordering_candidates: HashSet<TypeVariableId>,
    pub(super) nominal_positions: HashMap<NominalTypeId, (u32, Span)>,
}

pub(super) fn authenticate(
    registry: &ResolvedRegistry,
    sources: &HashMap<SourceId, &SourceFile>,
    modules: &HashMap<ModuleId, SourceId>,
    work: &mut TypeWorkBudget,
) -> Result<OriginalDeclarationProvenance, ValidationError> {
    authenticate_with_coordinates(registry, sources, modules, work, None)
}

#[cfg(test)]
pub(super) fn authenticate_with_coordinate_loan(
    registry: &ResolvedRegistry,
    sources: &HashMap<SourceId, &SourceFile>,
    modules: &HashMap<ModuleId, SourceId>,
    work: &mut TypeWorkBudget,
    loan: &DeclarationCoordinateLoan<'_>,
) -> Result<OriginalDeclarationProvenance, ValidationError> {
    authenticate_with_coordinates(registry, sources, modules, work, Some(loan))
}

// Keep borrowed authority/context inputs and the mutable meter explicit here.

fn authenticate_with_coordinates(
    registry: &ResolvedRegistry,
    sources: &HashMap<SourceId, &SourceFile>,
    modules: &HashMap<ModuleId, SourceId>,
    work: &mut TypeWorkBudget,
    loan: Option<&DeclarationCoordinateLoan<'_>>,
) -> Result<OriginalDeclarationProvenance, ValidationError> {
    let mut original = OriginalDeclarationProvenance::default();
    for (module, source) in modules {
        charge(work, 1)?;
        let source = *sources.get(source).ok_or_else(registry_error)?;
        let shared = loan
            .map(|loan| loan.get(*module, source, work))
            .transpose()?;
        let fresh = if shared.is_none() {
            Some(DeclarationCoordinates::from_module_source(
                *module, source, work,
            )?)
        } else {
            None
        };
        let coordinates = shared
            .as_deref()
            .or(fresh.as_ref())
            .expect("one coordinate owner");
        // Only syntax is shared. Each immutable registry/context still proves
        // all declarations, retained resource binders and unused candidates.
        authenticate_module(registry, *module, source, coordinates, work, &mut original)?;
        coordinates.resource_binders.authenticate(
            registry,
            *module,
            source,
            work,
            &mut original.generatives,
        )?;
        coordinates.resource_binders.unused_candidates(
            registry,
            *module,
            source,
            work,
            &mut original.ordering_candidates,
        )?;
    }
    charge(work, original.ordering_candidates.len())?;
    original
        .ordering_candidates
        .retain(|id| !original.generatives.contains(id));
    Ok(original)
}

fn registry_error() -> ValidationError {
    registry()
}

fn authenticate_module(
    registry: &ResolvedRegistry,
    module: ModuleId,
    source: &SourceFile,
    coordinates: &DeclarationCoordinates,
    work: &mut TypeWorkBudget,
    original: &mut OriginalDeclarationProvenance,
) -> Result<(), ValidationError> {
    for nominal in registry.nominals() {
        charge(work, 1)?;
        if nominal.id.module() != module {
            continue;
        }
        let origin = original_span(&nominal.origin, work)?;
        let (expected, coordinate) = coordinates.nominal(origin, work)?;
        if nominal.id != NominalTypeId::new(module, expected) {
            return Err(registry_error());
        }
        match coordinate.role {
            NominalRole::Data {
                newtype,
                constructors,
            } => {
                if newtype != (nominal.declaration_kind == ResolvedNominalDeclarationKind::Newtype)
                    || constructors != nominal.constructors.len()
                {
                    return Err(registry_error());
                }
                // Imported aliases are display routes, not defining names.
            }
            _ => return Err(registry_error()),
        }
        charge(work, 1)?;
        original
            .nominal_positions
            .try_reserve(1)
            .map_err(|_| resource())?;
        if original
            .nominal_positions
            .insert(nominal.id, (expected, origin))
            .is_some()
        {
            return Err(registry_error());
        }
    }

    for (id, _, origin) in registry.abstract_nominal_kind_entries() {
        charge(work, 1)?;
        if id.module() != module {
            continue;
        }
        let (expected, _) = coordinates.nominal(origin, work)?;
        if id != NominalTypeId::new(module, expected) {
            return Err(registry_error());
        }
    }
    for constructor in registry.constructors() {
        charge(work, 1)?;
        if constructor.owner.module() != module {
            continue;
        }
        // Derive the owner from its independently authenticated original span.
        let owner = registry
            .nominal(constructor.owner)
            .ok_or_else(registry_error)?;
        let owner_origin = original_span(&owner.origin, work)?;
        let (expected, coordinate) = coordinates.nominal(owner_origin, work)?;
        let constructor_origin = original_span(&constructor.origin, work)?;
        if !matches!(coordinate.role, NominalRole::Data { .. }) {
            return Err(registry_error());
        }
        charge(work, 1)?;
        let original = &coordinates.constructors[*coordinates
            .constructor_origins
            .get(&constructor_origin)
            .ok_or_else(registry_error)?];
        if original.owner != expected
            || constructor.owner != NominalTypeId::new(module, expected)
            || constructor.id != ConstructorId::new(constructor.owner, original.ordinal)
        {
            return Err(registry_error());
        }
    }
    for effect in registry.effects() {
        charge(work, 1)?;
        if effect.id.module() != module {
            continue;
        }

        coordinates.authenticate_effect(module, source, effect, work)?;
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        core::EffectCoreBuilder,
        resolved::{
            ResolvedEffectDeclaration, ResolvedEffectOperation, ResolvedNominalType, ResolvedType,
            ResolvedTypeProvenance, ResolvedTypeProvenanceNode, ResolvedTypeVariable,
        },
        surface::{SurfaceModule, SurfaceTypeKind},
        types::{Kind, OperationId, Type, TypeVariableId},
    };
    use std::sync::Arc;

    fn surface(source: &SourceFile) -> SurfaceModule {
        let tree = crate::parser::parse(crate::lexer::lex(source).unwrap());
        crate::parser::project_module(source, &tree).unwrap()
    }

    fn original_registry_phase(
        source: &SourceFile,
        registry: ResolvedRegistry,
    ) -> Result<(), ValidationError> {
        original_registry_phase_modules(
            &[source],
            &[(ModuleId::from(source.id()), source.id())],
            registry,
        )
    }

    fn original_registry_phase_modules(
        sources: &[&SourceFile],
        modules: &[(ModuleId, SourceId)],
        registry: ResolvedRegistry,
    ) -> Result<(), ValidationError> {
        let source = sources[0];
        let mut builder = EffectCoreBuilder::with_effect_registry(Arc::new(registry));
        let root = builder
            .unit(
                Type::Unit,
                Origin::Source(
                    source
                        .span(crate::source::ByteRange::new(0, 1).unwrap())
                        .unwrap(),
                ),
            )
            .unwrap();
        let program = builder.finish(root).unwrap();
        let validator = super::super::Validator::new_modules(&program, sources, modules).unwrap();
        // Exercise the production original registry-admission phase, including
        // the independent source proof before any registry ordering. This does
        // not stand in for a complete resource forest or native execution.
        let provenance = authenticate(
            &program.registry,
            &sources
                .iter()
                .map(|source| (source.id(), *source))
                .collect(),
            &modules.iter().copied().collect(),
            &mut TypeWorkBudget::default(),
        )?;
        validator
            .validate_registry_with_original_provenance(Some(&provenance))
            .map(|_| ())
    }

    #[test]
    fn original_coordinate_authentication_preserves_work_and_rejects_missing_or_donor_sources() {
        let source = SourceFile::new(
            "ordinary.ash",
            "effect First { one : Unit -> Unit }\neffect Second { two : Unit -> Unit }\n",
        )
        .unwrap();
        let registry = effect_registry(&source, [0, 1]);
        let module = ModuleId::from(source.id());
        let sources = HashMap::from([(source.id(), &source)]);
        let modules = HashMap::from([(module, source.id())]);
        let mut measured = TypeWorkBudget::default();
        authenticate(&registry, &sources, &modules, &mut measured).unwrap();
        let total = measured.used();
        for prefix in [0usize, 41] {
            let mut short = TypeWorkBudget::with_limit(prefix + total - 1);
            short.charge(prefix).unwrap();
            assert_eq!(
                authenticate(&registry, &sources, &modules, &mut short)
                    .unwrap_err()
                    .reason(),
                ValidationReason::Resource
            );
            for _ in 0..2 {
                let mut exact = TypeWorkBudget::with_limit(prefix + total);
                exact.charge(prefix).unwrap();
                authenticate(&registry, &sources, &modules, &mut exact).unwrap();
                assert_eq!(exact.used(), prefix + total);
            }
        }
        assert_eq!(
            authenticate(
                &registry,
                &HashMap::new(),
                &modules,
                &mut TypeWorkBudget::default()
            )
            .unwrap_err()
            .reason(),
            ValidationReason::Registry
        );
        let donor = SourceFile::new("same-shape-donor.ash", source.text()).unwrap();
        assert_eq!(
            authenticate(
                &registry,
                &HashMap::from([(donor.id(), &donor)]),
                &HashMap::from([(module, donor.id())]),
                &mut TypeWorkBudget::default()
            )
            .unwrap_err()
            .reason(),
            ValidationReason::Registry
        );
    }

    #[test]
    fn coordinate_loan_never_reuses_registry_or_original_binder_authority() {
        let source_arena = [SourceFile::new(
            "ordinary.ash",
            "effect First { one : Unit -> Unit }\neffect Second { two : Unit -> Unit }\n",
        )
        .unwrap()];
        let source = &source_arena[0];
        let module = ModuleId::from(source.id());
        let module_arena = [module];
        let registry = effect_registry(source, [0, 1]);
        let permuted = effect_registry(source, [1, 0]);
        let sources = HashMap::from([(source.id(), source)]);
        let modules = HashMap::from([(module, source.id())]);
        let mut work = TypeWorkBudget::default();
        let loan = DeclarationCoordinateLoan::new(&source_arena, &module_arena, &mut work).unwrap();
        let cold = authenticate(&registry, &sources, &modules, &mut work).unwrap();
        let original =
            authenticate_with_coordinate_loan(&registry, &sources, &modules, &mut work, &loan)
                .unwrap();
        assert_eq!(original.nominal_positions, cold.nominal_positions);
        // The same source syntax can authenticate another valid projection,
        // but that view must receive its own empty provenance, not the earlier
        // complete view's retained positions or ordering/binder facts.
        let projected = authenticate_with_coordinate_loan(
            &ResolvedRegistry::default(),
            &sources,
            &modules,
            &mut work,
            &loan,
        )
        .unwrap();
        assert!(original.nominal_positions.is_empty());
        assert!(projected.nominal_positions.is_empty());
        assert!(projected.generatives.is_empty());
        assert!(projected.ordering_candidates.is_empty());
        let retained = loan.get(module, source, &mut work).unwrap();
        assert_eq!(
            authenticate_with_coordinate_loan(&permuted, &sources, &modules, &mut work, &loan,)
                .unwrap_err()
                .reason(),
            ValidationReason::Registry
        );
        assert!(Arc::ptr_eq(
            &retained,
            &loan.get(module, source, &mut work).unwrap()
        ));
        let again =
            authenticate_with_coordinate_loan(&registry, &sources, &modules, &mut work, &loan)
                .unwrap();
        assert_eq!(again.nominal_positions, original.nominal_positions);

        // A clone has identical bytes and SourceId, and passes the cold proof.
        // It is still another source object and cannot use this operation loan.
        let clone = source.clone();
        let cloned_sources = HashMap::from([(clone.id(), &clone)]);
        authenticate(&registry, &cloned_sources, &modules, &mut work).unwrap();
        assert_eq!(
            authenticate_with_coordinate_loan(
                &registry,
                &cloned_sources,
                &modules,
                &mut work,
                &loan,
            )
            .unwrap_err()
            .reason(),
            ValidationReason::Registry
        );
    }

    #[test]
    fn coordinate_loan_whole_original_admission_keeps_cumulative_work() {
        let source_arena = [SourceFile::new(
            "ordinary.ash",
            "effect First { one : Unit -> Unit }\neffect Second { two : Unit -> Unit }\n",
        )
        .unwrap()];
        let source = &source_arena[0];
        let module = ModuleId::from(source.id());
        let module_arena = [module];
        let registry = effect_registry(source, [0, 1]);
        let sources = HashMap::from([(source.id(), source)]);
        let modules = HashMap::from([(module, source.id())]);
        let operation = |work: &mut TypeWorkBudget| -> Result<(), ValidationError> {
            let loan = DeclarationCoordinateLoan::new(&source_arena, &module_arena, work)?;
            let first =
                authenticate_with_coordinate_loan(&registry, &sources, &modules, work, &loan)?;
            let second =
                authenticate_with_coordinate_loan(&registry, &sources, &modules, work, &loan)?;
            assert_eq!(first.nominal_positions, second.nominal_positions);
            Ok(())
        };
        let mut measured = TypeWorkBudget::default();
        operation(&mut measured).unwrap();
        let cost = measured.used();
        for prefix in [0, 17] {
            let mut short = TypeWorkBudget::with_limit(prefix + cost - 1);
            short.charge(prefix).unwrap();
            assert_eq!(
                operation(&mut short).unwrap_err().reason(),
                ValidationReason::Resource
            );
            assert!(short.used() <= short.limit());
            for _ in 0..2 {
                let mut exact = TypeWorkBudget::with_limit(prefix + cost);
                exact.charge(prefix).unwrap();
                operation(&mut exact).unwrap();
                assert_eq!(exact.used(), prefix + cost);
                assert_eq!(
                    operation(&mut exact).unwrap_err().reason(),
                    ValidationReason::Resource
                );
            }
        }
    }

    fn effect_registry(source: &SourceFile, permutation: [u32; 2]) -> ResolvedRegistry {
        let module = ModuleId::from(source.id());
        let declarations = surface(source);
        let effects = declarations
            .effects
            .iter()
            .zip(permutation)
            .map(|(effect, ordinal)| {
                let id = EffectId::new(module, ordinal);
                let operation = &effect.operations[0];
                let SurfaceTypeKind::Function(function) = &operation.annotation.kind else {
                    panic!("function fixture")
                };
                let annotation = operation.annotation.span;
                let provenance = ResolvedTypeProvenance::new(
                    vec![
                        ResolvedTypeProvenanceNode::Fact(function.domain.span),
                        ResolvedTypeProvenanceNode::Fact(function.codomain.span),
                        ResolvedTypeProvenanceNode::Function {
                            span: annotation,
                            domain: 0,
                            codomain: 1,
                            effect_arguments: Box::new([]),
                        },
                    ],
                    2,
                );
                ResolvedEffectDeclaration {
                    native_contract: None,
                    id,
                    public: effect.public,
                    spelling: effect.name.text.clone(),
                    parameters: Box::new([]),
                    operations: Box::new([ResolvedEffectOperation {
                        id: OperationId::new(id, 0),
                        spelling: operation.name.text.clone(),
                        annotation: ResolvedType {
                            ty: Type::Function(Box::new(Type::Unit), Box::new(Type::Unit)),
                            provenance,
                            origin: Origin::Source(annotation),
                            span: annotation,
                        },
                        origin: Origin::Source(operation.span),
                        span: operation.span,
                    }]),
                    origin: Origin::Source(effect.name.span),
                    span: effect.span,
                }
            })
            .collect();
        // Rebuild positions, owner definitions/signatures and operation IDs
        // together, so incoming table consistency cannot authenticate a slot.
        ResolvedRegistry::default().with_effects(effects)
    }

    #[test]
    fn original_admission_rejects_coherent_effect_id_and_operation_permutation() {
        let source = SourceFile::new(
            "effects.ash",
            "effect Earlier {\nfirst : Unit -> Unit\n}\neffect Later {\nsecond : Unit -> Unit\n}\n",
        )
        .unwrap();
        for (permutation, expected) in [([0, 1], None), ([1, 0], Some(ValidationReason::Registry))]
        {
            let registry = effect_registry(&source, permutation);
            registry
                .authenticate_owner_definitions(&mut TypeWorkBudget::default())
                .unwrap();
            for effect in registry.effects() {
                assert_eq!(registry.effect(effect.id), Some(effect));
                assert_eq!(effect.operations[0].id.owner(), effect.id);
            }
            assert_eq!(
                original_registry_phase(&source, registry)
                    .err()
                    .map(|error| error.reason()),
                expected
            );
        }
    }

    // This checks the body-free provenance mechanism against genuine resolver
    // records. The surrounding test separately requires whole checked Source
    // admission, pending publication and independent Core; this helper grants
    // no native or executable authority.

    #[test]
    fn declaration_coordinate_work_is_exact_cumulative_and_retryable() {
        let source = SourceFile::new("coordinates.ash", "type First = One\n| Two(Int)\neffect Before {\ncall : Unit -> Unit\n}\nnewtype Last = Last(Int)\n").unwrap();
        let mut measured = TypeWorkBudget::default();
        let coordinates = DeclarationCoordinates::from_source(&source, &mut measured).unwrap();
        assert_eq!(coordinates.nominals.len(), 2);
        assert_eq!(coordinates.constructors.len(), 3);
        assert_eq!(coordinates.constructors[2].owner, 1);
        let total = measured.used();
        for prefix in [0usize, 37] {
            let mut short = TypeWorkBudget::with_limit(prefix + total - 1);
            short.charge(prefix).unwrap();
            assert_eq!(
                DeclarationCoordinates::from_source(&source, &mut short)
                    .err()
                    .unwrap()
                    .reason(),
                ValidationReason::Resource
            );
            for _ in 0..2 {
                let mut exact = TypeWorkBudget::with_limit(prefix + total);
                exact.charge(prefix).unwrap();
                let retry = DeclarationCoordinates::from_source(&source, &mut exact).unwrap();
                assert_eq!(retry.nominals.len(), 2);
                assert_eq!(exact.used(), prefix + total);
            }
        }
    }

    #[test]
    fn syntax_loan_returns_lexer_parser_and_recovery_consumption_on_refusal() {
        let source = SourceFile::new("short.ash", "type Value = Make\n").unwrap();
        for extra in [1usize, 10] {
            let mut work = TypeWorkBudget::with_limit(source.text().len() + extra);
            assert_eq!(
                DeclarationCoordinates::from_source(&source, &mut work)
                    .err()
                    .unwrap()
                    .reason(),
                ValidationReason::Resource
            );
            assert_eq!(work.used(), source.text().len() + extra);
        }
        let malformed = SourceFile::new("malformed.ash", "type Value =\n").unwrap();
        let mut work = TypeWorkBudget::default();
        assert_eq!(
            DeclarationCoordinates::from_source(&malformed, &mut work)
                .err()
                .unwrap()
                .reason(),
            ValidationReason::Registry
        );
        assert!(work.used() > malformed.text().len());
    }
}
