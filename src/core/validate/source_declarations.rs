//! Original declaration coordinates reconstructed from resident source text.
//!
//! This syntax-only check grants no semantic or executable authority. In
//! particular, a retained nominal/effect ID cannot choose its defining slot.

use std::collections::{HashMap, HashSet};

use super::{ValidationError, ValidationReason};
use crate::{
    foreign::source_contract::PreparedForeignNominalRole,
    lexer::{Token, TokenKind, lex_with_budget},
    module::ModuleId,
    parser::{
        ConcreteElement, ConcreteNode, ConcreteTree, NodeKind, STRUCTURAL_DEPTH_LIMIT,
        parse_with_budget, source_structural_weight,
    },
    resolved::{ResolvedNominalDeclarationKind, ResolvedRegistry},
    source::{Origin, SourceFile, SourceId, Span},
    syntax_resource::SyntaxBudget,
    types::{
        ConstructorId, EffectId, Kind, NominalTypeId, ResourceDefinitionId, TypeVariableId,
        TypeWorkBudget,
    },
};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct LibraryCoordinate {
    span: Span,
    name: Span,
    ordinal: u32,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum NominalRole {
    Data {
        newtype: bool,
        constructors: usize,
    },
    Resource {
        source: bool,
        ordinal: u32,
    },
    Foreign {
        library: LibraryCoordinate,
        member: usize,
        role: PreparedForeignNominalRole,
    },
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
            } else if node.kind == NodeKind::ProviderResourceExpression {
                charge(work, node.children.len())?;
                let instance = node
                    .children
                    .iter()
                    .find_map(|child| match child {
                        ConcreteElement::Node(child) if child.kind == NodeKind::EffectInstance => {
                            Some(child)
                        }
                        _ => None,
                    })
                    .ok_or_else(registry)?;
                charge(work, instance.children.len())?;
                let qualified = instance.children.iter().find_map(|child| match child {
                    ConcreteElement::Node(child) if child.kind == NodeKind::QualifiedName => {
                        Some(child)
                    }
                    _ => None,
                });
                // A qualified spelling is not resolved here. It may identify a
                // raw argument coordinate, never a local family-owned slot.
                let family = match qualified {
                    Some(qualified) => span(qualified, tokens, work)?,
                    None => name(instance, tokens, work)?,
                };
                let mut arguments = Vec::new();
                charge(work, instance.children.len())?;
                for child in &instance.children {
                    if let ConcreteElement::Node(child) = child
                        && matches!(child.kind, NodeKind::Type | NodeKind::EffectRow)
                    {
                        push(&mut arguments, span(child, tokens, work)?, work)?;
                    }
                }
                for (position, argument) in arguments.iter().copied().enumerate() {
                    push(
                        &mut result.bindings,
                        ResourceBinderCoordinate {
                            scope: span(node, tokens, work)?,
                            family: Some(family),
                            argument,
                            position,
                            arguments: arguments.len(),
                        },
                        work,
                    )?;
                }
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
            let selected = if let Some(family) = binder.family {
                let family_name = text(source, family)?;
                let mut selected = None;
                for fact in registry.source_resource_facts() {
                    charge(work, 1 + fact.spelling.len())?;
                    if fact.id.module() == module
                        && fact.spelling == family_name
                        && selected
                            .replace((fact.owned_position, fact.parameters.len()))
                            .is_some()
                    {
                        return Err(registry_error());
                    }
                }
                charge(work, registry.provider_contract_count())?;
                for (_, certificate) in registry.provider_contracts() {
                    charge(work, certificate.resource_count())?;
                    for (spelling, _, fact) in certificate.resource_contracts() {
                        charge(work, spelling.len())?;
                        if fact.id.module() == module
                            && spelling == family_name
                            && selected.replace((0, fact.parameters.len())).is_some()
                        {
                            return Err(registry_error());
                        }
                    }
                }
                selected
            } else {
                Some((0, 1))
            };
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
    pub(crate) fn from_source(
        source: &SourceFile,
        work: &mut TypeWorkBudget,
    ) -> Result<Self, ValidationError> {
        #[cfg(test)]
        let measurement_before = work.used();
        #[cfg(test)]
        super::startup_measurement::count("core.coordinates.enter");
        let result = (|| {
            #[cfg(test)]
            let parse_before = work.used();
            let tree = syntax(source, work);
            #[cfg(test)]
            super::startup_measurement::record(
                if tree.is_ok() {
                    "core.coordinates.syntax.ok"
                } else {
                    "core.coordinates.syntax.err"
                },
                parse_before,
                work.used(),
            );
            let tree = tree?;
            let root = tree.root().ok_or_else(registry)?;
            let tokens = tree.tokens();
            let mut result = Self {
                resource_binders: ResourceBinderCoordinates::from_tree(root, tokens, work)?,
                ..Self::default()
            };
            let mut ordinary_resources = Vec::new();
            let mut source_resources = Vec::new();
            let mut foreign_nominals = Vec::new();
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
                        let mut is_source = false;
                        for child in &node.children {
                            charge(work, 1)?;
                            is_source |= matches!(child, ConcreteElement::Node(child) if child.kind == NodeKind::SourceResourceField);
                        }
                        let name = name(node, tokens, work)?;
                        let coordinate = NominalCoordinate {
                            origin: name,
                            name,
                            role: NominalRole::Resource {
                                source: is_source,
                                ordinal: 0,
                            },
                        };
                        push(
                            if is_source {
                                &mut source_resources
                            } else {
                                &mut ordinary_resources
                            },
                            coordinate,
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
                        result.library(
                            node,
                            tokens,
                            ordinal(next_library)?,
                            &mut foreign_nominals,
                            work,
                        )?;
                        next_library = next_library.checked_add(1).ok_or_else(resource)?;
                    }
                    _ => {}
                }
            }
            for (index, mut coordinate) in ordinary_resources
                .into_iter()
                .chain(source_resources)
                .enumerate()
            {
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
            for coordinate in foreign_nominals {
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
        })();
        #[cfg(test)]
        super::startup_measurement::record(
            if result.is_ok() {
                "core.coordinates.ok"
            } else {
                "core.coordinates.err"
            },
            measurement_before,
            work.used(),
        );
        result
    }

    fn library(
        &mut self,
        node: &ConcreteNode,
        tokens: &[Token],
        ordinal: u32,
        nominals: &mut Vec<NominalCoordinate>,
        work: &mut TypeWorkBudget,
    ) -> Result<(), ValidationError> {
        let library = LibraryCoordinate {
            span: span(node, tokens, work)?,
            name: name(node, tokens, work)?,
            ordinal,
        };
        let (mut member, mut owner, mut access, mut symbol) = (0usize, 0usize, 0usize, 0usize);
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
                "owner" | "access" => {
                    let role = if word == "owner" {
                        let role = PreparedForeignNominalRole::Owner(owner);
                        owner = owner.checked_add(1).ok_or_else(resource)?;
                        role
                    } else {
                        let role = PreparedForeignNominalRole::Access(access);
                        access = access.checked_add(1).ok_or_else(resource)?;
                        role
                    };
                    let coordinate = NominalCoordinate {
                        origin: span(child, tokens, work)?,
                        name: name(child, tokens, work)?,
                        role: NominalRole::Foreign {
                            library,
                            member,
                            role,
                        },
                    };
                    push(nominals, coordinate, work)?;
                }
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
    // Absent legacy Foreign formals are original ordering slots, not retained
    // types or scope authority. Only exact authenticated builtin slots qualify.
    pub(super) omitted_builtin_formals: HashSet<TypeVariableId>,
}

pub(super) fn authenticate(
    registry: &ResolvedRegistry,
    sources: &HashMap<SourceId, &SourceFile>,
    modules: &HashMap<ModuleId, SourceId>,
    work: &mut TypeWorkBudget,
) -> Result<OriginalDeclarationProvenance, ValidationError> {
    let mut original = OriginalDeclarationProvenance::default();
    for (module, source) in modules {
        charge(work, 1)?;
        let source = *sources.get(source).ok_or_else(registry_error)?;
        let coordinates = DeclarationCoordinates::from_source(source, work)?;
        authenticate_module(
            registry,
            *module,
            source,
            &coordinates,
            work,
            &mut original.nominal_positions,
        )?;
        if module.is_builtin_foreign() {
            charge(work, 1)?;
            if let Some(host) = registry.effect(EffectId::new(
                *module,
                crate::module::FOREIGN_NATIVE_HOST_LOCAL,
            )) {
                charge(work, source.text().len().saturating_add(10))?;
                if source.text() != crate::module::foreign_builtin_source_text()
                    || !crate::foreign::checked_builtins::is_canonical_native_host(
                        host, registry, work,
                    )
                    .map_err(|error| {
                        if error.is_resource_exhaustion() {
                            resource()
                        } else {
                            registry_error()
                        }
                    })?
                {
                    return Err(registry_error());
                }
                original
                    .omitted_builtin_formals
                    .try_reserve(10)
                    .map_err(|_| resource())?;
                for local in 4..14 {
                    let id = TypeVariableId::resolved(*module, local);
                    if registry.type_variable(id).is_none() {
                        original.omitted_builtin_formals.insert(id);
                    }
                }
            }
        }
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
    nominal_positions: &mut HashMap<NominalTypeId, (u32, Span)>,
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
            NominalRole::Foreign { .. } if nominal.constructors.is_empty() => {}
            _ => return Err(registry_error()),
        }
        charge(work, 1)?;
        nominal_positions.try_reserve(1).map_err(|_| resource())?;
        if nominal_positions
            .insert(nominal.id, (expected, origin))
            .is_some()
        {
            return Err(registry_error());
        }
    }
    for (prepared, role, id, _) in registry.source_foreign_nominal_candidates() {
        charge(work, 1)?;
        if id.module() != module {
            continue;
        }
        let (name, _, origin) = role.declaration(prepared).ok_or_else(registry_error)?;
        let origin = original_span(origin, work)?;
        let (expected, coordinate) = coordinates.nominal(origin, work)?;
        let member = match role {
            PreparedForeignNominalRole::Owner(index) => prepared
                .owners()
                .get(index)
                .map(|value| value.member_index()),
            PreparedForeignNominalRole::Access(index) => prepared
                .accesses()
                .get(index)
                .map(|value| value.member_index()),
        }
        .ok_or_else(registry_error)?;
        let NominalRole::Foreign {
            library,
            member: written_member,
            role: written_role,
        } = coordinate.role
        else {
            return Err(registry_error());
        };
        if id != NominalTypeId::new(module, expected)
            || prepared.module() != module
            || library.span != original_span(prepared.origin(), work)?
            || written_member != member
            || written_role != role
            || !same_name(source, library.name, prepared.name(), work)?
            || !same_name(source, coordinate.name, name, work)?
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
        if module.is_builtin_foreign() {
            // NativeHost is compiler metadata, not a parsed effect declaration.
            // Its exception requires the actual immutable defining source and
            // independently reconstructed complete builtin inventory.
            charge(work, source.text().len())?;
            if source.text() != crate::module::foreign_builtin_source_text()
                || !crate::foreign::checked_builtins::is_canonical_native_host(
                    effect, registry, work,
                )
                .map_err(|error| {
                    if error.is_resource_exhaustion() {
                        resource()
                    } else {
                        registry_error()
                    }
                })?
            {
                return Err(registry_error());
            }
            continue;
        }
        coordinates.authenticate_effect(module, source, effect, work)?;
    }
    for fact in registry.source_resource_facts() {
        charge(work, 1)?;
        if fact.id.module() != module {
            continue;
        }
        let origin = original_span(&fact.origin, work)?;
        let (expected, coordinate) = coordinates.nominal(origin, work)?;
        let NominalRole::Resource {
            source: true,
            ordinal,
        } = coordinate.role
        else {
            return Err(registry_error());
        };
        if fact.family != NominalTypeId::new(module, expected)
            || fact.id != ResourceDefinitionId::new(module, ordinal)
            || !same_name(source, coordinate.name, &fact.spelling, work)?
        {
            return Err(registry_error());
        }
    }
    for (_, certificate) in registry.provider_contracts() {
        charge(work, 1)?;
        for (_, _, fact) in certificate.resource_contracts() {
            charge(work, 1)?;
            if fact.id.module() != module {
                continue;
            }
            let origin = original_span(&fact.origin, work)?;
            let (expected, coordinate) = coordinates.nominal(origin, work)?;
            let NominalRole::Resource {
                source: false,
                ordinal,
            } = coordinate.role
            else {
                return Err(registry_error());
            };
            if fact.family != NominalTypeId::new(module, expected)
                || fact.id != ResourceDefinitionId::new(module, ordinal)
            {
                return Err(registry_error());
            }
        }
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
        let module = modules[0].0;
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
        let mut validator =
            super::super::Validator::new_modules(&program, sources, modules).unwrap();
        validator.source_resource_context =
            super::super::SourceResourceValidationContext::OriginalTemplate {
                resource: ResourceDefinitionId::new(module, 0),
                answer: false,
            };
        // Exercise the production original registry-admission phase, including
        // the independent source proof before any registry ordering. This does
        // not stand in for a complete resource forest or native execution.
        validator.authenticate_effect_registry_phase().map(|_| ())
    }

    fn owner_access_source() -> SourceFile {
        let base = include_str!("../../../tests/fixtures/source-owner/owner.ash")
            .split("pub type Acquire")
            .next()
            .unwrap();
        SourceFile::new(
            "owner-access.ash",
            base.replace(
                "    symbol Allocate",
                r#"    access View<W, R> {
        window W
        owner State<R>
        extent nul
        preserves Read
    }
    symbol Read<R> : State<R> -> Foreign.Call<Int> {
        name "ash_owner_read"
        abi (pointer(Address)) -> Size
        operand 0 from 0 current
        output result as scalar
        outcome otherwise { readable result }
    }
    symbol Allocate"#,
            ),
        )
        .unwrap()
    }

    #[test]
    fn source_control_original_nominal_projection_keeps_defining_positions() {
        let source = SourceFile::new(
            "nominal-projection.ash",
            "type UnusedFirst = First\ntype UnusedSecond = Second\ntype Needed = Kept\n",
        )
        .unwrap();
        let module = ModuleId::from(source.id());
        let coordinates =
            DeclarationCoordinates::from_source(&source, &mut TypeWorkBudget::default()).unwrap();
        let registry = |position, origin, constructor_position| {
            let family = NominalTypeId::new(module, position);
            let constructor = ConstructorId::new(family, constructor_position);
            ResolvedRegistry::new(
                vec![ResolvedNominalType {
                    id: family,
                    declaration_kind: ResolvedNominalDeclarationKind::Data,
                    spelling: "Needed".to_owned(),
                    constructors: Box::new([constructor]),
                    representation: None,
                    representation_provenance: None,
                    origin: Origin::Source(origin),
                }],
                vec![crate::resolved::ResolvedConstructor {
                    id: constructor,
                    owner: family,
                    spelling: "Kept".to_owned(),
                    payload: None,
                    origin: Origin::Source(coordinates.constructors[2].origin),
                }],
            )
            .with_type_parameters_with_budget(
                vec![(family, Vec::new())],
                &mut TypeWorkBudget::default(),
            )
            .unwrap()
        };
        let original = coordinates.nominals[2].origin;
        let projected = registry(2, original, 0);
        original_registry_phase(&source, projected.clone()).unwrap();
        for (position, origin, constructor_position) in [
            (0, original, 0),
            (2, coordinates.nominals[0].origin, 0),
            (2, original, 1),
        ] {
            assert_eq!(
                original_registry_phase(&source, registry(position, origin, constructor_position),)
                    .unwrap_err()
                    .reason(),
                ValidationReason::Registry,
                "a projected view cannot renumber the original, borrow another declaration, or change constructor position"
            );
        }

        // The exception comes from the successful defining-coordinate proof,
        // not a relaxed rule for ordinary whole-registry admission.
        let mut builder = EffectCoreBuilder::with_effect_registry(Arc::new(projected));
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
        let mut ordinary =
            super::super::Validator::new_modules(&program, &[&source], &[(module, source.id())])
                .unwrap();
        assert_eq!(
            ordinary.run_effect().unwrap_err().reason(),
            ValidationReason::Registry
        );
    }

    fn owner_access_registry(source: &SourceFile, permutation: [u32; 2]) -> ResolvedRegistry {
        owner_access_registry_order(source, permutation, false)
    }

    fn owner_access_registry_order(
        source: &SourceFile,
        permutation: [u32; 2],
        reverse: bool,
    ) -> ResolvedRegistry {
        let module = ModuleId::from(source.id());
        let surface = surface(source);
        let prepared = Arc::new(
            crate::foreign::source_contract::prepare_foreign_library(
                module,
                &surface.foreign_libraries[0],
            )
            .unwrap(),
        );
        let mut next_parameter = 0u32;
        let mut candidates = Vec::new();
        for (role, id) in [
            PreparedForeignNominalRole::Owner(0),
            PreparedForeignNominalRole::Access(0),
        ]
        .into_iter()
        .zip(permutation)
        {
            let (name, original, origin) = role.declaration(&prepared).unwrap();
            let parameters = original
                .iter()
                .map(|parameter| {
                    let id = TypeVariableId::resolved(module, next_parameter);
                    next_parameter += 1;
                    assert_eq!(parameter.kind(), &Kind::Type);
                    ResolvedTypeVariable {
                        id,
                        spelling: parameter.name().to_owned(),
                        kind: Kind::Type,
                        origin: parameter.origin().clone(),
                    }
                })
                .collect();
            let nominal = ResolvedNominalType {
                id: NominalTypeId::new(module, id),
                declaration_kind: ResolvedNominalDeclarationKind::Data,
                spelling: name.to_owned(),
                constructors: Box::new([]),
                representation: None,
                representation_provenance: None,
                origin: origin.clone(),
            };
            candidates.push((Arc::clone(&prepared), role, nominal, parameters));
        }
        // The production constructor installs all nominal lookup positions,
        // parameter/kind rows and original role candidates from the same IDs.
        // The negative is a coherent permutation, not a stale lookup table.
        if reverse {
            candidates.reverse();
        }
        ResolvedRegistry::default()
            .with_source_foreign_nominal_candidates(candidates, &mut TypeWorkBudget::default())
            .unwrap()
    }

    #[test]
    fn original_admission_rejects_coherent_owner_access_id_permutation() {
        let source = owner_access_source();
        for (permutation, expected) in [([0, 1], None), ([1, 0], Some(ValidationReason::Registry))]
        {
            let registry = owner_access_registry(&source, permutation);
            // Passive role/category authentication alone does not recover
            // the defining allocation ordinal. Both fixtures satisfy it.
            registry
                .authenticate_provider_contracts(&mut TypeWorkBudget::default())
                .unwrap();
            for (_, _, id, parameters) in registry.source_foreign_nominal_candidates() {
                assert_eq!(registry.nominal_parameters(id).unwrap(), parameters);
                assert!(registry.nominal(id).is_some());
            }
            assert_eq!(
                original_registry_phase(&source, registry)
                    .err()
                    .map(|error| error.reason()),
                expected
            );
        }
        original_registry_phase(&source, owner_access_registry_order(&source, [0, 1], true))
            .unwrap();
    }

    #[test]
    fn original_coordinate_authentication_preserves_work_and_rejects_missing_or_donor_sources() {
        let source = owner_access_source();
        let registry = owner_access_registry(&source, [0, 1]);
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

    #[test]
    fn original_admission_rejects_consistently_rebound_foreign_symbol_id_permutation() {
        use crate::{
            foreign::checked_source::{ForeignBindingContext, bind_foreign_symbol},
            module::{ModuleRoots, load_module_graph},
            resolve::{DependencyExports, resolve_module},
            resolved::{CheckedModule, clone_resolved_effect_with_budget},
        };
        use std::sync::atomic::{AtomicU64, Ordering};
        static IDS: AtomicU64 = AtomicU64::new(0);
        struct Directory(std::path::PathBuf);
        impl Drop for Directory {
            fn drop(&mut self) {
                let _ = std::fs::remove_dir_all(&self.0);
            }
        }
        let directory = Directory(std::env::temp_dir().join(format!(
            "ash-original-symbol-coordinates-{}-{}",
            std::process::id(),
            IDS.fetch_add(1, Ordering::Relaxed)
        )));
        std::fs::create_dir(&directory.0).unwrap();
        let entry = directory.0.join("entry.ash");
        std::fs::write(
            &entry,
            r#"import @builtin.foreign as Foreign
effect Before {
    before : Unit -> Unit
}
foreign library Native {
    profile "x86_64-unknown-linux-gnu"
    symbol First : Unit -> Foreign.Call<Unit> {
        name "ash_first"
        abi () -> void
        outcome otherwise {}
    }
    symbol Second : Unit -> Foreign.Call<Unit> {
        name "ash_second"
        abi () -> void
        outcome otherwise {}
    }
}
effect After {
    after : Unit -> Unit
}
main : Unit -> Int
main () = 42
"#,
        )
        .unwrap();
        let graph = load_module_graph(&entry, &ModuleRoots::empty()).unwrap();
        let mut checked: Vec<CheckedModule> = Vec::new();
        for loaded in graph.modules() {
            let dependencies = loaded
                .dependencies()
                .iter()
                .map(|edge| {
                    let dependency = checked
                        .iter()
                        .find(|checked| checked.module() == edge.target())
                        .unwrap();
                    DependencyExports::new(edge, dependency.exports()).unwrap()
                })
                .collect::<Vec<_>>();
            let resolved = resolve_module(loaded, &dependencies).unwrap();
            checked.push(crate::elaborate::check_module(resolved).unwrap());
        }
        let original = ResolvedRegistry::combine_checked(
            &checked,
            &mut TypeWorkBudget::default(),
            &mut crate::interface::InterfaceConstraintBudget::default(),
        )
        .unwrap();
        let sources = graph
            .modules()
            .iter()
            .map(|loaded| loaded.source())
            .collect::<Vec<_>>();
        let modules = graph
            .modules()
            .iter()
            .map(|loaded| (loaded.id(), loaded.source().id()))
            .collect::<Vec<_>>();
        std::fs::remove_file(entry).unwrap();
        original_registry_phase_modules(&sources, &modules, original.clone()).unwrap();

        let remap = |id: EffectId| {
            if id.module() == graph.entry() {
                match id.declaration() {
                    1 => EffectId::new(id.module(), 2),
                    2 => EffectId::new(id.module(), 1),
                    _ => id,
                }
            } else {
                id
            }
        };
        let mut setup = TypeWorkBudget::unbounded();
        let effects = original
            .effects()
            .iter()
            .map(|effect| {
                let mut effect = clone_resolved_effect_with_budget(effect, &mut setup).unwrap();
                effect.id = remap(effect.id);
                for operation in &mut effect.operations {
                    operation.id = OperationId::new(effect.id, operation.id.operation());
                }
                effect.native_contract = None;
                effect
            })
            .collect();
        let mut forged = original
            .clone()
            .rebuild_effect_identity_tables_for_core_test(effects);
        let mut rebound = Vec::new();
        let codec = original
            .effects()
            .iter()
            .find_map(|effect| effect.native_contract.as_ref())
            .unwrap()
            .call_codec();
        let context = ForeignBindingContext::new(
            &forged,
            codec.module(),
            codec.source(),
            codec.ids(),
            &mut setup,
        )
        .unwrap();
        for effect in original.effects() {
            let Some(symbol) = effect.native_contract.as_ref() else {
                continue;
            };
            rebound.push(Arc::new(
                bind_foreign_symbol(
                    symbol.library(),
                    Arc::clone(symbol.prepared()),
                    symbol.symbol_index(),
                    forged.effect(remap(effect.id)).unwrap(),
                    &context,
                    &mut setup,
                )
                .unwrap(),
            ));
        }
        for symbol in rebound {
            forged.retain_native_symbol(symbol, &mut setup).unwrap();
        }
        forged.authenticate_owner_definitions(&mut setup).unwrap();
        for effect in forged.effects() {
            assert_eq!(forged.effect(effect.id), Some(effect));
            for operation in &effect.operations {
                assert_eq!(operation.id.owner(), effect.id);
            }
            if let Some(symbol) = effect.native_contract.as_ref() {
                assert!(Arc::ptr_eq(
                    forged.native_symbol(symbol.operation()).unwrap(),
                    symbol
                ));
                assert_eq!(symbol.effect(), effect.id);
            }
        }
        assert_eq!(
            original_registry_phase_modules(&sources, &modules, forged)
                .err()
                .unwrap()
                .reason(),
            ValidationReason::Registry
        );
    }

    #[test]
    fn defining_categories_allocate_after_data_despite_an_early_foreign_library() {
        let source = SourceFile::new(
            "owner.ash",
            include_str!("../../../tests/fixtures/source-owner/owner.ash"),
        )
        .unwrap();
        let mut work = TypeWorkBudget::default();
        let coordinates = DeclarationCoordinates::from_source(&source, &mut work).unwrap();
        let names = coordinates
            .nominals
            .iter()
            .map(|entry| text(&source, entry.name).unwrap())
            .collect::<Vec<_>>();
        assert_eq!(
            names,
            ["Acquire", "Finish", "Completion", "Scope", "Probe", "State"]
        );
        let state = coordinates.nominals.last().unwrap();
        assert!(state.origin.range().start() < coordinates.nominals[0].origin.range().start());
        assert!(matches!(
            state.role,
            NominalRole::Foreign {
                role: PreparedForeignNominalRole::Owner(0),
                member: 3,
                ..
            }
        ));
        assert_eq!(coordinates.nominal(state.origin, &mut work).unwrap().0, 5);
        assert_eq!(
            coordinates
                .effects
                .iter()
                .map(|entry| text(&source, entry.name).unwrap())
                .collect::<Vec<_>>(),
            ["Allocate", "Free", "ProbeOps"]
        );
        assert!(matches!(
            coordinates.nominals[4].role,
            NominalRole::Resource {
                source: true,
                ordinal: 0
            }
        ));
    }

    // This checks the body-free provenance mechanism against genuine resolver
    // records. The surrounding test separately requires whole checked Source
    // admission, pending publication and independent Core; this helper grants
    // no native or executable authority.
    fn source_control_generative_provenance_inputs(
        resolved: &crate::resolved::ResolvedModule,
        source: &SourceFile,
    ) {
        let module = resolved.module();
        let mut view = resolved
            .registry()
            .source_original_checker_view(resolved.imported_facts(), &mut TypeWorkBudget::default())
            .unwrap();
        let headers = resolved
            .source_resources()
            .iter()
            .filter(|resource| view.source_resource_fact(resource.header.id).is_none())
            .map(|resource| Arc::clone(&resource.header))
            .collect::<Vec<_>>();
        view = view
            .with_image_source_resource_facts(headers, &mut TypeWorkBudget::default())
            .unwrap();
        let check = |registry: &ResolvedRegistry, work: &mut TypeWorkBudget| {
            let coordinates = DeclarationCoordinates::from_source(source, work)?;
            let mut admitted = HashSet::new();
            coordinates.resource_binders.authenticate(
                registry,
                module,
                source,
                work,
                &mut admitted,
            )?;
            Ok::<_, ValidationError>(admitted)
        };
        let mut measured = TypeWorkBudget::default();
        let admitted = check(&view, &mut measured).unwrap();
        assert_eq!(admitted.len(), 1);
        let identity = *admitted.iter().next().unwrap();
        let original = view.type_variable(identity).unwrap();
        assert_eq!(original.spelling, "Fresh");
        assert_eq!(
            text(source, original.origin.primary_span()).unwrap(),
            "Fresh"
        );
        let cost = measured.used();
        for prefix in [0, 13] {
            for _ in 0..2 {
                let mut exact = TypeWorkBudget::with_limit(prefix + cost);
                exact.charge(prefix).unwrap();
                assert_eq!(check(&view, &mut exact).unwrap(), admitted);
                assert_eq!(exact.used(), prefix + cost);
                let mut short = TypeWorkBudget::with_limit(prefix + cost - 1);
                short.charge(prefix).unwrap();
                assert_eq!(
                    check(&view, &mut short).unwrap_err().reason(),
                    ValidationReason::Resource
                );
                assert_eq!(
                    check(&view, &mut TypeWorkBudget::default()).unwrap(),
                    admitted
                );
            }
        }
        let mut projected = view.clone();
        assert!(projected.corrupt_global_parameter_rows_for_core_test(
            crate::resolved::CoreGlobalParameterRowMutationForTest::RemoveCanonicalParameter(
                identity,
            ),
        ));
        assert!(
            check(&projected, &mut TypeWorkBudget::default())
                .unwrap()
                .is_empty(),
            "source-only coordinates do not require an unrelated projected binder"
        );
        let donor = SourceFile::new("unrelated-binder.ash", "Fresh").unwrap();
        for mutation in 0..7 {
            let mut changed = crate::resolved::clone_resolved_type_variable_with_budget(
                original,
                &mut TypeWorkBudget::default(),
            )
            .unwrap();
            match mutation {
                0 => changed.kind = Kind::EffectRow,
                1 => {
                    changed.origin = resolved.source_resources()[0].header.parameters[0]
                        .origin
                        .clone()
                }
                2 => {
                    changed.origin = Origin::Source(
                        donor
                            .span(crate::source::ByteRange::new(0, 5).unwrap())
                            .unwrap(),
                    )
                }
                3 => changed.id = resolved.source_resources()[0].header.parameters[0].id,
                4 => changed.spelling = "Different".to_owned(),
                5 => {
                    changed.origin = Origin::Generated {
                        cause: Box::new(changed.origin),
                        reason: crate::source::GeneratedReason::TypeChecking,
                    }
                }
                6 => {
                    let span = changed.origin.primary_span();
                    changed.origin = Origin::Source(
                        source
                            .span(
                                crate::source::ByteRange::new(
                                    span.range().start() + 1,
                                    span.range().end(),
                                )
                                .unwrap(),
                            )
                            .unwrap(),
                    );
                }
                _ => unreachable!(),
            }
            let forged = view.clone().with_additional_type_variables([changed]);
            let result = check(&forged, &mut TypeWorkBudget::default());
            if matches!(mutation, 1 | 2 | 6) {
                assert!(
                    result.unwrap().is_empty(),
                    "a retained record outside the exact binding coordinate gets no ordering authority: mutation {mutation}"
                );
            } else {
                assert_eq!(
                    result.unwrap_err().reason(),
                    ValidationReason::Registry,
                    "generative provenance mutation {mutation}"
                );
            }
        }
    }

    fn source_control_native_formal_metadata_inputs(
        resolved: &crate::resolved::ResolvedModule,
        view: &ResolvedRegistry,
        cost: usize,
    ) {
        let native = view
            .foreign_modules()
            .find(|native| {
                native.data_types.contains_key("Acquire")
                    && native.data_types.contains_key("Result")
            })
            .unwrap();
        let module = native.admission.module_id;
        let canonical = native.canonical_registry();
        for parameter in canonical
            .type_variables()
            .filter(|parameter| parameter.id.module() == Some(module))
        {
            assert_eq!(view.type_variable(parameter.id), Some(parameter));
        }
        let statement = native
            .states
            .iter()
            .find(|state| canonical.nominal(state.id).unwrap().spelling == "StatementState")
            .unwrap();
        assert!(view.nominal(statement.id).is_none());
        assert!(view.nominal(native.data_types["Result"]).is_none());
        let donor = SourceFile::new("unrelated-native-formal.ash", "T").unwrap();
        for (local, spelling) in [(1, "S"), (2, "C"), (3, "T")] {
            let parameter = canonical
                .type_variable(TypeVariableId::resolved(module, local))
                .unwrap();
            assert_eq!(parameter.spelling, spelling);
            assert_eq!(view.type_variable(parameter.id), Some(parameter));
            let matching = crate::resolved::clone_resolved_type_variable_with_budget(
                parameter,
                &mut TypeWorkBudget::default(),
            )
            .unwrap();
            let matching_view = resolved
                .registry()
                .as_ref()
                .clone()
                .with_additional_type_variables([matching])
                .source_original_checker_view(
                    resolved.imported_facts(),
                    &mut TypeWorkBudget::default(),
                )
                .unwrap();
            assert_eq!(matching_view.type_variable(parameter.id), Some(parameter));
            for mutation in 0..5 {
                let mut changed = crate::resolved::clone_resolved_type_variable_with_budget(
                    parameter,
                    &mut TypeWorkBudget::default(),
                )
                .unwrap();
                match mutation {
                    0 => changed.id = TypeVariableId::resolved(module, local % 3 + 1),
                    1 => changed.kind = Kind::EffectRow,
                    2 => {
                        changed.origin = canonical
                            .type_variable(TypeVariableId::resolved(module, 4))
                            .unwrap()
                            .origin
                            .clone()
                    }
                    3 => {
                        changed.origin = Origin::Source(
                            donor
                                .span(crate::source::ByteRange::new(0, 1).unwrap())
                                .unwrap(),
                        )
                    }
                    4 => changed.spelling = "Different".to_owned(),
                    _ => unreachable!(),
                }
                assert!(
                    matches!(
                        resolved
                            .registry()
                            .as_ref()
                            .clone()
                            .with_additional_type_variables([changed])
                            .source_original_checker_view(
                                resolved.imported_facts(),
                                &mut TypeWorkBudget::default()
                            ),
                        Err(crate::resolved::ResolvedBuildFailure::InvalidState)
                    ),
                    "native canonical formal {local}, mirror mutation {mutation}"
                );
            }
        }
        let mut exact = TypeWorkBudget::with_limit(13 + cost);
        exact.charge(13).unwrap();
        resolved
            .registry()
            .source_original_checker_view(resolved.imported_facts(), &mut exact)
            .unwrap();
        assert_eq!(exact.used(), 13 + cost);
        let mut short = TypeWorkBudget::with_limit(13 + cost - 1);
        short.charge(13).unwrap();
        assert!(matches!(
            resolved
                .registry()
                .source_original_checker_view(resolved.imported_facts(), &mut short),
            Err(crate::resolved::ResolvedBuildFailure::TypeResource)
        ));
    }

    #[test]
    fn source_control_unused_ordering_checks_the_current_cached_forest() {
        use crate::{
            core::{
                dialect::{
                    MethodEvidenceCatalog, MethodEvidenceMethod, StoredNode, UnvalidatedCoreProgram,
                },
                effect::{
                    EffectExprKind, EffectOperation, NativeInterpretNode, NativeInterpretation,
                    UnvalidatedEffectProgram,
                },
                source_resource::SourceResourceGlobals,
                validate::{SourceResourceStructureSession, Validator},
            },
            interface::{InterfaceId, MethodId},
            module::{ModuleRoots, load_module_graph},
            resolve::{DependencyExports, resolve_module},
            resolved::CheckedModule,
            types::{
                ComputationType, EffectInstance, EffectRow, EffectRowVariable, IterativeTypeOwner,
            },
        };
        use std::sync::atomic::{AtomicU64, Ordering};
        static IDS: AtomicU64 = AtomicU64::new(0);
        struct Directory(std::path::PathBuf);
        impl Drop for Directory {
            fn drop(&mut self) {
                let _ = std::fs::remove_dir_all(&self.0);
            }
        }
        let directory = Directory(std::env::temp_dir().join(format!(
            "ash-unused-ordering-{}-{}",
            std::process::id(),
            IDS.fetch_add(1, Ordering::Relaxed)
        )));
        std::fs::create_dir(&directory.0).unwrap();
        let owner = include_str!("../../../tests/fixtures/source-owner/owner.ash");
        std::fs::write(directory.0.join("owner.ash"), owner).unwrap();
        // The exact qualified-family/later-formal contrast from integration851.
        let entry = format!(
            "import owner as Donor\n{owner}\nmain : Unit -> Donor.Scope<Unit, Unit, Int>\nmain () = resource Donor.Probe<{{}}, ImportedFresh, {{}}> owner = 42 {{\n    42\n}}\ninterface KeepConfig<A> {{\n    keepConfig : A -> A\n}}\n"
        );
        std::fs::write(directory.0.join("entry.ash"), entry).unwrap();
        let graph =
            load_module_graph(&directory.0.join("entry.ash"), &ModuleRoots::empty()).unwrap();
        let mut checked: Vec<CheckedModule> = Vec::new();
        let mut provider_codes = crate::elaborate::ProviderCodeAvailability::default();
        let (mut checking_work, _) = crate::compiler_work::source_work(&graph).unwrap();
        let mut coverage_work = crate::pattern::UsefulnessBudget::default();
        let mut constraint_work = crate::interface::InterfaceConstraintBudget::default();
        for loaded in graph.modules() {
            let dependencies = loaded
                .dependencies()
                .iter()
                .map(|edge| {
                    DependencyExports::new(
                        edge,
                        checked
                            .iter()
                            .find(|module| module.module() == edge.target())
                            .unwrap()
                            .exports(),
                    )
                    .unwrap()
                })
                .collect::<Vec<_>>();
            let compiled = crate::elaborate::check_module_with_budget_and_provider_codes(
                resolve_module(loaded, &dependencies).unwrap(),
                &provider_codes,
                &mut checking_work,
                &mut coverage_work,
                &mut constraint_work,
            )
            .unwrap();
            if let Some(code) = compiled.provider_code() {
                provider_codes
                    .retain(loaded.id(), code, &mut checking_work)
                    .unwrap();
            }
            if let Some(code) = compiled.source_resource_code() {
                provider_codes
                    .retain_source(loaded.id(), code, &mut checking_work)
                    .unwrap();
            }
            checked.push(compiled);
        }
        let original = checked
            .iter()
            .find(|module| module.module() == graph.entry())
            .unwrap()
            .source_resource_code()
            .unwrap()
            .resource(0)
            .unwrap();
        let original = original.original_acquire();
        let header = Arc::clone(
            original
                .registry
                .source_resource_facts()
                .find(|fact| fact.id.module() == graph.entry())
                .unwrap(),
        );
        let identity = original
            .registry
            .type_variables()
            .find(|parameter| {
                parameter.id.module() == Some(graph.entry())
                    && parameter.spelling == "ImportedFresh"
            })
            .unwrap()
            .id;
        let sources = graph
            .modules()
            .iter()
            .map(|loaded| loaded.source())
            .collect::<Vec<_>>();
        let modules = graph
            .modules()
            .iter()
            .map(|loaded| (loaded.id(), loaded.source().id()))
            .collect::<Vec<_>>();
        let globals = Arc::new(SourceResourceGlobals::new());
        let check = |session: &mut SourceResourceStructureSession<'_>,
                     program: &UnvalidatedEffectProgram,
                     globals: &Arc<SourceResourceGlobals>,
                     work: &mut TypeWorkBudget| {
            session.check_with_globals(program, &header, false, &sources, &modules, globals, work)
        };
        let mut session = SourceResourceStructureSession::default();
        let mut measured = TypeWorkBudget::default();
        check(&mut session, original, &globals, &mut measured).unwrap();
        let first = measured.used();
        assert!(
            session
                .admitted
                .as_ref()
                .unwrap()
                .unused_ordering
                .contains(&identity)
        );
        check(&mut session, original, &globals, &mut measured).unwrap();
        let reused = measured.used() - first;
        assert!(
            reused < first,
            "unchanged current forest must take the real completed-admission reuse path"
        );
        assert!(
            session
                .admitted
                .as_ref()
                .unwrap()
                .unused_ordering
                .contains(&identity)
        );
        for prefix in [0, 13] {
            let mut work = TypeWorkBudget::with_limit(prefix + first);
            work.charge(prefix).unwrap();
            check(
                &mut SourceResourceStructureSession::default(),
                original,
                &globals,
                &mut work,
            )
            .unwrap();
            assert_eq!(work.used(), prefix + first);
            let mut short = TypeWorkBudget::with_limit(prefix + first - 1);
            short.charge(prefix).unwrap();
            assert_eq!(
                check(
                    &mut SourceResourceStructureSession::default(),
                    original,
                    &globals,
                    &mut short
                )
                .unwrap_err()
                .reason(),
                ValidationReason::Resource
            );
            check(
                &mut SourceResourceStructureSession::default(),
                original,
                &globals,
                &mut TypeWorkBudget::default(),
            )
            .unwrap();
        }
        fn copy(program: &UnvalidatedEffectProgram) -> UnvalidatedEffectProgram {
            UnvalidatedCoreProgram {
                registry: Arc::clone(&program.registry),
                method_evidence: Arc::clone(&program.method_evidence),
                arena: program.arena,
                root: program.root,
                method_evidence_anchors: program
                    .method_evidence_anchors
                    .iter()
                    .map(|anchor| crate::core::dialect::MethodEvidenceAnchor {
                        node: anchor.node,
                        owner: anchor.owner,
                        requirement: anchor.requirement,
                        method: anchor.method,
                        application: anchor.application.clone(),
                        role: anchor.role,
                        occurrence: anchor.occurrence,
                        expectation: anchor.expectation,
                    })
                    .collect(),
                nodes: program
                    .nodes
                    .iter()
                    .map(|node| StoredNode {
                        dialect: node.dialect,
                        ty: node.ty.clone(),
                        effects: node.effects.clone(),
                        origin: node.origin.clone(),
                        kind: node.kind.clone(),
                    })
                    .collect(),
            }
        }
        for mutation in 0..6 {
            let mut changed = copy(original);
            match mutation {
                0 => changed.nodes[changed.root.index().unwrap()].ty = Type::Variable(identity),
                1 | 2 | 3 | 5 => {
                    let value_type = match mutation {
                        1 => Type::Forall(
                            Box::new([(identity, Kind::Type)]),
                            Box::new(Type::Variable(identity)),
                        ),
                        5 => Type::Forall(Box::new([(identity, Kind::Type)]), Box::new(Type::Unit)),
                        2 => Type::EffectfulFunction(
                            Box::new(Type::Unit),
                            Box::new(ComputationType::new(
                                Type::Unit,
                                EffectRow::open(EffectRowVariable::rigid(identity), Box::new([])),
                            )),
                        ),
                        _ => Type::Unit,
                    };
                    let method = MethodEvidenceMethod {
                        id: MethodId::new(InterfaceId::new(graph.entry(), 0), 0),
                        spelling: "metadata_only".into(),
                        interface_parameters: Box::new([]),
                        inherited_parameters: Box::new([]),
                        parameters: if mutation == 3 {
                            Box::new([(identity, Kind::Type)])
                        } else {
                            Box::new([])
                        },
                        value_type,
                    };
                    changed.method_evidence = Arc::new(MethodEvidenceCatalog::new(
                        vec![method],
                        Vec::new(),
                        Vec::new(),
                        Vec::new(),
                        Vec::new(),
                        Vec::new(),
                        Vec::new(),
                    ));
                }
                4 => {
                    let symbol = Arc::clone(
                        changed
                            .registry
                            .effects()
                            .iter()
                            .find_map(|effect| effect.native_contract.as_ref())
                            .unwrap(),
                    );
                    let effect =
                        EffectInstance::new(symbol.effect(), Box::new([Type::Variable(identity)]));
                    changed.nodes[changed.root.index().unwrap()].kind = EffectExprKind::Operation(
                        EffectOperation::NativeInterpret(NativeInterpretNode::new(
                            changed.root,
                            Box::new([NativeInterpretation::new(effect, symbol)]),
                        )),
                    );
                }
                _ => unreachable!(),
            }
            assert!(Arc::ptr_eq(&changed.registry, &original.registry));
            let validator = Validator::new_modules(&changed, &sources, &modules).unwrap();
            assert!(
                validator
                    .unused_ordering_candidates(&HashSet::from([identity]))
                    .unwrap()
                    .is_empty(),
                "semantic carrier mutation {mutation}"
            );
            let mut session = SourceResourceStructureSession::default();
            check(
                &mut session,
                original,
                &globals,
                &mut TypeWorkBudget::default(),
            )
            .unwrap();
            let failure = check(
                &mut session,
                &changed,
                &globals,
                &mut TypeWorkBudget::default(),
            )
            .unwrap_err();
            assert_eq!(
                failure.reason(),
                ValidationReason::Registry,
                "mutation {mutation}"
            );
            assert_eq!(
                failure.node(),
                None,
                "written-order guard mutation {mutation}"
            );
            assert!(
                session.admitted.is_none(),
                "the actual same-registry/source/modules/globals reuse branch must invalidate the prior unused proof before fresh refusal: {mutation}"
            );
            check(
                &mut session,
                original,
                &globals,
                &mut TypeWorkBudget::default(),
            )
            .unwrap();
            changed.discard_iteratively();
        }
        // A changed globals Arc deliberately tests fresh context, separately
        // from the SAME-Arc cache cases above.
        let mut used_globals = SourceResourceGlobals::new();
        used_globals.insert(
            crate::resolved::BinderId::new(987654),
            IterativeTypeOwner::new(Type::Variable(identity)),
        );
        let mut fresh = SourceResourceStructureSession::default();
        assert_eq!(
            check(
                &mut fresh,
                original,
                &Arc::new(used_globals),
                &mut TypeWorkBudget::default()
            )
            .unwrap_err()
            .reason(),
            ValidationReason::Registry
        );
        println!(
            "unused ordering: exact={first}, reused={reused}; six actual cache-hit carrier changes refused before reuse; globals-only use, exact/one-short prefix and retries"
        );
    }

    #[test]
    fn source_control_original_registry_retains_distinct_resource_categories() {
        use crate::{
            foreign::{ForeignRegistrations, provider_manifest, sqlite_manifest},
            module::{ForeignRegistrationId, ModuleRoots, load_module_graph},
            resolve::{DependencyExports, resolve_module},
            resolved::CheckedModule,
        };
        use std::sync::atomic::{AtomicU64, Ordering};
        static IDS: AtomicU64 = AtomicU64::new(0);
        struct File(std::path::PathBuf);
        impl Drop for File {
            fn drop(&mut self) {
                let _ = std::fs::remove_file(&self.0);
            }
        }
        let path = File(std::env::temp_dir().join(format!(
            "ash-resource-coordinates-{}-{}.ash",
            std::process::id(),
            IDS.fetch_add(1, Ordering::Relaxed)
        )));
        // Reuse the genuine current source-owner definition. The ordinary
        // experimental declaration needs its own normally checked provider
        // certificate; legacy registrations here establish registry categories,
        // not generated-host or current source-resource execution evidence.
        let source = format!(
            "import @foreign.sqlite as Legacy\n{}\n{}",
            include_str!("../../../tests/fixtures/source-owner/owner.ash"),
            r#"
        interface OrdinaryProvider<R> {
            diagnostic : Ordinary<R> -> Legacy.Error ! {OrdinaryOps<R>}
        }
        effect OrdinaryOps<R> {
            diagnostic : Ordinary<R> -> Legacy.Error
        }
        resource Ordinary<R> {
            input Legacy.OpenConfig
            state Legacy.ConnectionState<R>
            result Scope<Legacy.OpenError, Legacy.CloseError, Answer> for <Answer>
            provider OrdinaryProvider<R>
            effect OrdinaryOps<R>
            interpret Legacy.Connection<R>
            acquire config => perform Legacy.Connection<R>.open config
            finish state => perform Legacy.Connection<R>.close state
            handlers state {
                diagnostic access => resume (perform Legacy.Connection<R>.diagnostic state)
            }
        }
        main : Unit -> Scope<Unit, Unit, Int>
        main () = resource Probe<{}, Fresh, {}> owner = 42 {
            42
        }
        "#
        );
        std::fs::write(&path.0, &source).unwrap();
        let roots = ModuleRoots::empty().with_foreign_registrations(
            ForeignRegistrations::new([
                sqlite_manifest(ForeignRegistrationId::new(991)).unwrap(),
                provider_manifest(ForeignRegistrationId::new(992)).unwrap(),
            ])
            .unwrap(),
        );
        let graph = load_module_graph(&path.0, &roots).unwrap();
        let mut checked: Vec<CheckedModule> = Vec::new();
        let mut tested_categories = false;
        for loaded in graph.modules() {
            let dependencies = loaded
                .dependencies()
                .iter()
                .map(|edge| {
                    DependencyExports::new(
                        edge,
                        checked
                            .iter()
                            .find(|module| module.module() == edge.target())
                            .unwrap()
                            .exports(),
                    )
                    .unwrap()
                })
                .collect::<Vec<_>>();
            let resolved = resolve_module(loaded, &dependencies).unwrap();
            if loaded.id() == graph.entry() {
                let ordinary = &resolved.resources()[0];
                let current = &resolved.source_resources()[0];
                assert!(current.span.range().start() < ordinary.span.range().start());
                let coordinates = DeclarationCoordinates::from_source(
                    loaded.source(),
                    &mut TypeWorkBudget::default(),
                )
                .unwrap();
                let module = loaded.id();
                assert_eq!(ordinary.id, ResourceDefinitionId::new(module, 0));
                assert_eq!(current.id, ResourceDefinitionId::new(module, 1));
                assert_eq!(ordinary.family, NominalTypeId::new(module, 4));
                assert_eq!(current.family, NominalTypeId::new(module, 5));
                for (origin, family, is_source, slot) in [
                    (ordinary.origin.primary_span(), ordinary.family, false, 0),
                    (current.origin.primary_span(), current.family, true, 1),
                ] {
                    let (expected, coordinate) = coordinates
                        .nominal(origin, &mut TypeWorkBudget::default())
                        .unwrap();
                    assert_eq!(family, NominalTypeId::new(module, expected));
                    assert!(
                        matches!(coordinate.role, NominalRole::Resource { source, ordinal } if source == is_source && ordinal == slot)
                    );
                }
                tested_categories = true;
            }
            let compiled = crate::elaborate::check_module(resolved).unwrap();
            if loaded.id() == graph.entry() {
                let original = compiled
                    .source_resource_code()
                    .unwrap()
                    .resource(0)
                    .unwrap();
                let group = compiled.provider_code().unwrap();
                for forest in [
                    original.original_acquire(),
                    original.original_finish(),
                    original.original_handler(),
                ] {
                    let certificate = forest
                        .registry
                        .provider_contracts()
                        .find(|(module, _)| **module == loaded.id())
                        .unwrap()
                        .1;
                    assert!(
                        Arc::ptr_eq(certificate, group.contracts()),
                        "Source originals and final module must consume the same once-checked ordinary group"
                    );
                }
            }
            checked.push(compiled);
        }
        assert!(tested_categories);
        let mut registry = ResolvedRegistry::combine_checked(
            &checked,
            &mut TypeWorkBudget::default(),
            &mut crate::interface::InterfaceConstraintBudget::default(),
        )
        .unwrap();
        let sources = graph
            .modules()
            .iter()
            .map(|loaded| loaded.source())
            .collect::<Vec<_>>();
        let modules = graph
            .modules()
            .iter()
            .map(|loaded| (loaded.id(), loaded.source().id()))
            .collect::<Vec<_>>();
        let current = registry
            .source_resource_facts()
            .find(|fact| fact.id.module() == graph.entry())
            .unwrap();
        assert_eq!(current.id, ResourceDefinitionId::new(graph.entry(), 1));
        assert_eq!(current.family, NominalTypeId::new(graph.entry(), 5));
        let ordinary = registry
            .provider_contracts()
            .find(|(module, _)| **module == graph.entry())
            .unwrap()
            .1
            .resource_contracts()
            .find(|(_, _, fact)| fact.id == ResourceDefinitionId::new(graph.entry(), 0))
            .unwrap()
            .2;
        assert_eq!(ordinary.family, NominalTypeId::new(graph.entry(), 4));
        assert!(
            current.origin.primary_span().range().start()
                < ordinary.origin.primary_span().range().start()
        );
        let source_id = current.id;
        registry
            .authenticate_provider_contracts(&mut TypeWorkBudget::default())
            .unwrap();
        registry
            .authenticate_owner_definitions(&mut TypeWorkBudget::default())
            .unwrap();
        let original = registry
            .source_control_take_original_resource_fact(source_id)
            .unwrap();
        assert_eq!(
            registry.authenticate_owner_definitions(&mut TypeWorkBudget::default()),
            Err(crate::resolved::ResolvedBuildFailure::InvalidState),
            "a same-module ordinary certificate cannot replace the missing Source owner declaration"
        );
        registry = registry
            .with_image_source_resource_facts(vec![original], &mut TypeWorkBudget::default())
            .unwrap();
        registry
            .authenticate_owner_definitions(&mut TypeWorkBudget::default())
            .unwrap();
        original_registry_phase_modules(&sources, &modules, registry).unwrap();

        // A pure local prerequisite is checked in the same body transaction,
        // then its actual closed facts authenticate the ordinary group. Both
        // this helper and the Source scope must survive final Core admission.
        let dependent = source.replace(
            "acquire config => perform Legacy.Connection<R>.open config",
            "acquire config => perform Legacy.Connection<R>.open (needed config)",
        ) + "\nneeded : Legacy.OpenConfig -> Legacy.OpenConfig\nneeded config = neededIdentity config\nneededIdentity : Legacy.OpenConfig -> Legacy.OpenConfig\nneededIdentity config = config\n";
        let source_start = dependent.find("pub resource Probe").unwrap();
        let ordinary_start = dependent
            .find("        interface OrdinaryProvider")
            .unwrap();
        let ordinary_only = format!(
            "{}{}",
            &dependent[..source_start],
            &dependent[ordinary_start..]
        )
        .replace(
            "main : Unit -> Scope<Unit, Unit, Int>\n        main () = resource Probe<{}, Fresh, {}> owner = 42 {\n            42\n        }",
            "main : Unit -> Int\n        main () = 42",
        );
        // This prerequisite actually needs the Source original that is still
        // awaiting the ordinary certificate. It cannot be marked checked or
        // offered as a capture fact merely because its signature is available.
        let unavailable = dependent.replace(
            "needed config = neededIdentity config",
            "needed config = {\n    let scoped = resource Probe<{}, Prerequisite, {}> owner = 42 {\n        0\n    }\n    config\n}",
        );
        let selected = dependent.replace(
            "needed config = neededIdentity config",
            "needed config = keepConfig (neededIdentity config)",
        ) + "\ninterface KeepConfig<A> {\nkeepConfig : A -> A\n}\nimpl KeepConfig<Legacy.OpenConfig> {\nkeepConfig config = config\n}\n";
        let late_failure = selected.replace(
            "owner = 42 {\n            42",
            "owner = 42 {\n            true",
        );
        assert_ne!(late_failure, selected);
        for (text, waits_for_source, independent_core, selected_slot, late_refusal) in [
            (&dependent, false, true, false, false),
            (&ordinary_only, false, false, false, false),
            (&unavailable, true, false, false, false),
            (&selected, false, true, true, false),
            (&late_failure, false, false, true, true),
        ] {
            std::fs::write(&path.0, text).unwrap();
            let graph = load_module_graph(&path.0, &roots).unwrap();
            let mut checked: Vec<CheckedModule> = Vec::new();
            for loaded in graph.modules() {
                let dependencies = loaded
                    .dependencies()
                    .iter()
                    .map(|edge| {
                        DependencyExports::new(
                            edge,
                            checked
                                .iter()
                                .find(|module| module.module() == edge.target())
                                .unwrap()
                                .exports(),
                        )
                        .unwrap()
                    })
                    .collect::<Vec<_>>();
                let resolved = resolve_module(loaded, &dependencies).unwrap();
                if loaded.id() == graph.entry()
                    && (waits_for_source || independent_core || selected_slot)
                {
                    let prerequisites =
                        crate::elaborate::source_original_prerequisites_for_test(&resolved)
                            .unwrap();
                    if waits_for_source {
                        assert!(
                            prerequisites.is_empty(),
                            "the unchecked Source-code dependency is withheld from early preparation"
                        );
                        // This asserts the internal staging boundary only. It
                        // deliberately makes no whole-module rejection claim.
                        continue;
                    }
                    assert_eq!(prerequisites.len(), if selected_slot { 3 } else { 2 });
                    for (index, definition) in resolved.definitions().iter().enumerate() {
                        let name = match &definition.kind {
                            crate::resolved::ResolvedDefinitionKind::Equational(global)
                            | crate::resolved::ResolvedDefinitionKind::ForeignConstant(global) => {
                                global.interface.name.spelling.as_str()
                            }
                            crate::resolved::ResolvedDefinitionKind::InlineOperational(global) => {
                                global.header.name.spelling.as_str()
                            }
                        };
                        if matches!(name, "needed" | "neededIdentity") {
                            assert!(prerequisites.contains(
                                &crate::resolved::ResolvedDeclarationIndex::Global(index)
                            ));
                        }
                    }
                }
                if selected_slot && !late_refusal && loaded.id() == graph.entry() {
                    source_control_generative_provenance_inputs(&resolved, loaded.source());
                }
                let pending = if selected_slot && loaded.id() == graph.entry() {
                    let definition = resolved
                        .definitions()
                        .iter()
                        .find(|definition| {
                            matches!(&definition.kind,
                            crate::resolved::ResolvedDefinitionKind::Equational(global)
                                if global.interface.name.spelling == "needed")
                        })
                        .unwrap();
                    let crate::resolved::ResolvedDefinitionKind::Equational(global) =
                        &definition.kind
                    else {
                        unreachable!()
                    };
                    let crate::resolved::ResolvedExprKind::Apply(application) =
                        &global.equations[0].body.kind
                    else {
                        panic!("selected helper application")
                    };
                    let crate::resolved::ResolvedExprKind::Occurrence(occurrence) =
                        &application.function.kind
                    else {
                        panic!("selected helper method")
                    };
                    let [slot] = occurrence.evidence.as_ref() else {
                        panic!("one real selected evidence slot")
                    };
                    let handle = slot.handle();
                    assert!(handle.selection().is_none());
                    Some(handle)
                } else {
                    None
                };
                let result = crate::elaborate::check_module(resolved);
                if late_refusal && loaded.id() == graph.entry() {
                    assert!(matches!(
                        result,
                        Err(crate::elaborate::TypeError::Source(_))
                            | Err(crate::elaborate::TypeError::Mismatch(_))
                    ));
                    assert!(
                        pending.unwrap().selection().is_none(),
                        "a later body failure cannot publish the earlier selected helper"
                    );
                } else {
                    checked.push(result.unwrap());
                    if let Some(handle) = pending {
                        assert!(handle.selection().is_some());
                    }
                }
            }
            if independent_core {
                crate::driver::compile_path(crate::driver::RunConfiguration {
                    entry: path.0.clone(),
                    roots: roots.clone(),
                })
                .expect("same-module Source scope and checked pure prerequisite reach independent whole Core admission");
            }
        }

        // Select one renamed public resource from a group that also contains a
        // private resource. The original checker retains the complete group,
        // not just the selected public spelling or its one family.
        let provider_name = format!(
            "ash_source_provider_{}_{}",
            std::process::id(),
            IDS.fetch_add(1, Ordering::Relaxed)
        );
        let provider_path = File(path.0.with_file_name(format!("{provider_name}.ash")));
        let ordinary_start = source.find("        interface OrdinaryProvider").unwrap();
        let main_start = source.find("        main :").unwrap();
        let private = source[ordinary_start..main_start]
            .replace("Ordinary", "PrivateOrdinary")
            .replace("diagnostic :", "privateDiagnostic :")
            .replace("diagnostic access =>", "privateDiagnostic access =>");
        let donor = source.replacen(
            "        resource Ordinary<R>",
            "        pub resource Ordinary<R>",
            1,
        ) + &private;
        std::fs::write(&provider_path.0, donor).unwrap();
        let imported_entry = format!(
            "import {provider_name} (Ordinary as Renamed)\n{}\nmain : Unit -> Scope<Unit, Unit, Int>\nmain () = resource Probe<{{}}, Fresh, {{}}> owner = 42 {{\n42\n}}\n",
            include_str!("../../../tests/fixtures/source-owner/owner.ash")
        );
        std::fs::write(&path.0, imported_entry).unwrap();
        let graph = load_module_graph(&path.0, &roots).unwrap();
        let mut checked: Vec<CheckedModule> = Vec::new();
        for loaded in graph.modules() {
            let dependencies = loaded
                .dependencies()
                .iter()
                .map(|edge| {
                    DependencyExports::new(
                        edge,
                        checked
                            .iter()
                            .find(|module| module.module() == edge.target())
                            .unwrap()
                            .exports(),
                    )
                    .unwrap()
                })
                .collect::<Vec<_>>();
            let resolved = resolve_module(loaded, &dependencies).unwrap();
            if loaded.id() == graph.entry() {
                let (alias, fact) = resolved
                    .imported_facts()
                    .resource_facts()
                    .find(|(name, _)| *name == "Renamed")
                    .unwrap();
                assert_eq!(alias, "Renamed");
                let certificate = resolved
                    .imported_facts()
                    .provider_contract(fact.id.module())
                    .unwrap();
                assert_eq!(certificate.resource_count(), 2);
                let mut view_work = TypeWorkBudget::default();
                let view = resolved
                    .registry()
                    .source_original_checker_view(resolved.imported_facts(), &mut view_work)
                    .unwrap();
                source_control_native_formal_metadata_inputs(&resolved, &view, view_work.used());
                let donor_source = graph
                    .modules()
                    .iter()
                    .find(|module| module.id() == fact.id.module())
                    .unwrap()
                    .source();
                assert!(donor_source.text().contains("Fresh"));
                assert!(
                    !view.type_variables().any(|parameter| {
                        parameter.id.module() == Some(fact.id.module())
                            && parameter.spelling == "Fresh"
                    }),
                    "the importing original retains the whole ordinary group but projects out its dependency's unrelated main binder"
                );
                let unrelated = SourceFile::new("unrelated-provider-formal.ash", "R").unwrap();
                let mut private_effect_rows = 0;
                for (_, _, original) in certificate.resource_contracts() {
                    let mut measured = TypeWorkBudget::default();
                    let rows = certificate
                        .provider_declaration_formals(original.id, &mut measured)
                        .unwrap();
                    for (owner, parameters) in rows {
                        assert_eq!(parameters.len(), 1);
                        assert_eq!(
                            text(donor_source, parameters[0].origin.primary_span()).unwrap(),
                            "R"
                        );
                        if matches!(owner, crate::resolved::OwnerId::Effect(effect) if view.effect(effect).is_none())
                        {
                            assert!(view.defining_owner_parameters(owner).is_none());
                            private_effect_rows += 1;
                        } else {
                            assert!(
                                crate::resolved::same_resolved_type_variables_with_budget(
                                    view.defining_owner_parameters(owner).unwrap(),
                                    parameters,
                                    &mut TypeWorkBudget::default(),
                                )
                                .unwrap()
                            )
                        }
                        let parameter = &parameters[0];
                        assert_eq!(view.type_variable(parameter.id), Some(parameter));
                        let already_supplied = resolved.imported_facts().effects().any(|effect| {
                            effect
                                .parameters
                                .iter()
                                .any(|other| other.id == parameter.id)
                        });
                        if !already_supplied {
                            let matching =
                                crate::resolved::clone_resolved_type_variable_with_budget(
                                    parameter,
                                    &mut TypeWorkBudget::default(),
                                )
                                .unwrap();
                            let matching_view = resolved
                                .registry()
                                .as_ref()
                                .clone()
                                .with_additional_type_variables([matching])
                                .source_original_checker_view(
                                    resolved.imported_facts(),
                                    &mut TypeWorkBudget::default(),
                                )
                                .unwrap();
                            assert_eq!(matching_view.type_variable(parameter.id), Some(parameter));
                        }
                        if let crate::resolved::OwnerId::Interface(interface) = owner {
                            assert!(
                                !resolved
                                    .imported_facts()
                                    .interface_imports()
                                    .any(|imported| imported.fact.id == interface),
                                "private provider formals do not expose an interface import"
                            );
                        } else {
                            assert_eq!(
                                owner,
                                crate::resolved::OwnerId::Effect(
                                    original.provided.instance.effect()
                                ),
                            );
                        }
                        let cost = measured.used();
                        let mut exact = TypeWorkBudget::with_limit(13 + cost);
                        exact.charge(13).unwrap();
                        certificate
                            .provider_declaration_formals(original.id, &mut exact)
                            .unwrap();
                        assert_eq!(exact.used(), 13 + cost);
                        let mut short = TypeWorkBudget::with_limit(13 + cost - 1);
                        short.charge(13).unwrap();
                        assert_eq!(
                            certificate
                                .provider_declaration_formals(original.id, &mut short)
                                .unwrap_err(),
                            crate::resolved::ResolvedBuildFailure::TypeResource
                        );
                        if already_supplied {
                            continue;
                        }
                        for mutation in 0..5 {
                            let mut changed =
                                crate::resolved::clone_resolved_type_variable_with_budget(
                                    parameter,
                                    &mut TypeWorkBudget::default(),
                                )
                                .unwrap();
                            match mutation {
                                0 => {
                                    let (_, _, other) = certificate
                                        .resource_contracts()
                                        .find(|(_, _, other)| other.id != original.id)
                                        .unwrap();
                                    let (_, other_parameters) = certificate
                                        .provider_declaration_formals(
                                            other.id,
                                            &mut TypeWorkBudget::default(),
                                        )
                                        .unwrap()
                                        .into_iter()
                                        .find(|(other_owner, _)| {
                                            std::mem::discriminant(other_owner)
                                                == std::mem::discriminant(&owner)
                                        })
                                        .unwrap();
                                    changed.id = other_parameters[0].id;
                                }
                                1 => changed.origin = original.origin.clone(),
                                2 => changed.kind = Kind::EffectRow,
                                3 => {
                                    changed.origin = Origin::Source(
                                        unrelated
                                            .span(crate::source::ByteRange::new(0, 1).unwrap())
                                            .unwrap(),
                                    );
                                }
                                4 => changed.spelling = "Different".to_owned(),
                                _ => unreachable!(),
                            }
                            let result = resolved
                                .registry()
                                .as_ref()
                                .clone()
                                .with_additional_type_variables([changed])
                                .source_original_checker_view(
                                    resolved.imported_facts(),
                                    &mut TypeWorkBudget::default(),
                                );
                            assert!(
                                matches!(
                                    result,
                                    Err(crate::resolved::ResolvedBuildFailure::InvalidState)
                                ),
                                "private provider formal mirror mutation {mutation}"
                            );
                        }
                    }
                }
                assert_eq!(private_effect_rows, 1);
                view.authenticate_provider_contracts(&mut TypeWorkBudget::default())
                    .unwrap();
                for (_, _, original) in certificate.resource_contracts() {
                    assert!(view.resource_signature_family(original.id).is_some());
                    assert!(view.type_variable(original.answer.id).is_some());
                }
            }
            checked.push(crate::elaborate::check_module(resolved).unwrap());
        }
        let compiled = crate::driver::compile_path(crate::driver::RunConfiguration {
            entry: path.0.clone(),
            roots,
        })
        .expect("renamed imported complete ordinary group and local Source scope reach final Core");
        let (program, provenance) = compiled.effect_build_input().unwrap();
        let mut forged = crate::core::transform::identity_effect_traversal(program).unwrap();
        let identity = forged
            .nodes
            .iter()
            .find_map(|node| match &node.kind {
                crate::core::EffectExprKind::Operation(
                    crate::core::EffectOperation::SourceResourceScope(scope),
                ) => Some(scope.identity()),
                _ => None,
            })
            .unwrap();
        assert!(
            Arc::make_mut(&mut forged.registry).corrupt_global_parameter_rows_for_core_test(
                crate::resolved::CoreGlobalParameterRowMutationForTest::RemoveCanonicalParameter(
                    identity,
                ),
            )
        );
        let sources = provenance
            .iter()
            .map(|(_, source)| source.as_ref())
            .collect::<Vec<_>>();
        let modules = provenance
            .iter()
            .map(|(module, source)| (*module, source.id()))
            .collect::<Vec<_>>();
        let error = super::super::validate_effect_modules_with_work(
            forged,
            &sources,
            &modules,
            &mut TypeWorkBudget::default(),
        )
        .unwrap_err();
        assert_eq!(error.reason(), ValidationReason::Registry);
    }

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

    #[test]
    fn checked_builtin_original_declarations_require_exact_source_and_host_role() {
        let directory =
            std::env::temp_dir().join(format!("ash-original-host-{}", std::process::id()));
        std::fs::create_dir(&directory).unwrap();
        let entry = directory.join("entry.ash");
        std::fs::write(
            &entry,
            "import @builtin.foreign as Foreign\nmain : Unit -> Int\nmain () = 42\n",
        )
        .unwrap();
        let graph =
            crate::module::load_module_graph(&entry, &crate::module::ModuleRoots::empty()).unwrap();
        std::fs::remove_dir_all(directory).unwrap();
        let loaded = graph
            .modules()
            .iter()
            .find(|module| module.id().is_builtin_foreign())
            .unwrap();
        let resolved = crate::resolve::resolve_module(loaded, &[]).unwrap();
        let original_registry = Arc::clone(resolved.registry());
        let original = &original_registry;
        let check = |registry: &ResolvedRegistry, source: &SourceFile| {
            authenticate(
                registry,
                &HashMap::from([(source.id(), source)]),
                &HashMap::from([(loaded.id(), source.id())]),
                &mut TypeWorkBudget::unbounded(),
            )
            .map(|_| ())
        };
        assert!(check(original, loaded.source()).is_ok());
        let mut effects = original.effects().to_vec();
        effects[0].public = false;
        let changed = original.as_ref().clone().with_effects(effects);
        assert_eq!(
            check(&changed, loaded.source()).unwrap_err().reason(),
            ValidationReason::Registry
        );
        let rewritten = SourceFile::new(
            "rewritten.ash",
            loaded
                .source()
                .text()
                .replace("ConversionError", "ConversionWrong"),
        )
        .unwrap();
        assert_eq!(rewritten.text().len(), loaded.source().text().len());
        // Keep original coordinates/registry here. Without the resident-byte
        // comparison this module phase would accept the equal-length rewrite:
        // no nominal or constructor display spelling grants a defining role.
        let coordinates =
            DeclarationCoordinates::from_source(loaded.source(), &mut TypeWorkBudget::unbounded())
                .unwrap();
        assert!(
            authenticate_module(
                original,
                loaded.id(),
                loaded.source(),
                &coordinates,
                &mut TypeWorkBudget::unbounded(),
                &mut HashMap::new()
            )
            .is_ok()
        );
        assert_eq!(
            authenticate_module(
                original,
                loaded.id(),
                &rewritten,
                &coordinates,
                &mut TypeWorkBudget::unbounded(),
                &mut HashMap::new()
            )
            .unwrap_err()
            .reason(),
            ValidationReason::Registry
        );

        let builtin = crate::elaborate::check_module(resolved).unwrap();
        let entry = graph
            .modules()
            .iter()
            .find(|module| !module.id().is_builtin_foreign())
            .unwrap();
        let dependencies = entry
            .dependencies()
            .iter()
            .map(|edge| crate::resolve::DependencyExports::new(edge, builtin.exports()).unwrap())
            .collect::<Vec<_>>();
        let entry_resolved = crate::resolve::resolve_module(entry, &dependencies).unwrap();
        let view = entry_resolved
            .registry()
            .source_original_checker_view(
                entry_resolved.imported_facts(),
                &mut TypeWorkBudget::unbounded(),
            )
            .unwrap();
        let sources = graph
            .modules()
            .iter()
            .map(|module| module.source())
            .collect::<Vec<_>>();
        let modules = graph
            .modules()
            .iter()
            .map(|module| (module.id(), module.source().id()))
            .collect::<Vec<_>>();
        let source_map = sources
            .iter()
            .map(|source| (source.id(), *source))
            .collect::<HashMap<_, _>>();
        let module_map = modules.iter().copied().collect::<HashMap<_, _>>();
        let mut measured = TypeWorkBudget::unbounded();
        let proof = authenticate(&view, &source_map, &module_map, &mut measured).unwrap();
        assert_eq!(
            proof.omitted_builtin_formals,
            (4..14)
                .map(|local| TypeVariableId::resolved(loaded.id(), local))
                .collect()
        );
        assert!(
            !proof
                .omitted_builtin_formals
                .contains(&TypeVariableId::resolved(loaded.id(), 3))
        );
        assert!(
            !proof
                .omitted_builtin_formals
                .contains(&TypeVariableId::resolved(loaded.id(), 14))
        );
        assert!(
            !proof
                .omitted_builtin_formals
                .contains(&TypeVariableId::resolved(entry.id(), 4))
        );
        let required = measured.used();
        assert!(
            authenticate(
                &view,
                &source_map,
                &module_map,
                &mut TypeWorkBudget::with_limit(required)
            )
            .is_ok()
        );
        assert_eq!(
            authenticate(
                &view,
                &source_map,
                &module_map,
                &mut TypeWorkBudget::with_limit(required - 1)
            )
            .unwrap_err()
            .reason(),
            ValidationReason::Resource
        );
        assert!(
            authenticate(
                &view,
                &source_map,
                &module_map,
                &mut TypeWorkBudget::with_limit(required)
            )
            .is_ok()
        );
        assert!(original_registry_phase_modules(&sources, &modules, view.clone()).is_ok());
        let census_budget = |registry: ResolvedRegistry,
                             proof: &OriginalDeclarationProvenance,
                             allowance,
                             prefix| {
            let mut builder = EffectCoreBuilder::with_effect_registry(Arc::new(registry));
            let root = builder
                .unit(
                    Type::Unit,
                    Origin::Source(
                        loaded
                            .source()
                            .span(crate::source::ByteRange::new(0, 1).unwrap())
                            .unwrap(),
                    ),
                )
                .unwrap();
            let program = builder.finish(root).unwrap();
            let mut validator =
                super::super::Validator::new_modules(&program, &sources, &modules).unwrap();
            validator.source_resource_context =
                super::super::SourceResourceValidationContext::OriginalTemplate {
                    resource: ResourceDefinitionId::new(loaded.id(), 0),
                    answer: false,
                };
            validator.type_work_limit = allowance;
            validator.type_work.set(prefix);
            let result = validator
                .validate_registry_with_original_provenance(Some(proof))
                .map(|_| ());
            (result, validator.type_work.get())
        };
        let census = |registry, proof| census_budget(registry, proof, usize::MAX, 0).0;
        assert!(census(view.clone(), &proof).is_ok());
        let prefix = 7;
        let (positive, required) = census_budget(view.clone(), &proof, usize::MAX, prefix);
        assert!(positive.is_ok());
        assert!(required > prefix + 10);
        assert!(
            census_budget(view.clone(), &proof, required, prefix)
                .0
                .is_ok()
        );
        assert_eq!(
            census_budget(view.clone(), &proof, required - 1, prefix)
                .0
                .unwrap_err()
                .reason(),
            ValidationReason::Resource
        );
        assert!(
            census_budget(view.clone(), &proof, required, prefix)
                .0
                .is_ok()
        );
        let missing_later = view
            .clone()
            .remove_type_variable_for_core_test(TypeVariableId::resolved(loaded.id(), 14));
        assert_eq!(
            census(missing_later, &proof).unwrap_err().reason(),
            ValidationReason::Registry
        );
        let no_host = view
            .clone()
            .rebuild_effect_identity_tables_for_core_test(Vec::new());
        let absent_proof = authenticate(
            &no_host,
            &source_map,
            &module_map,
            &mut TypeWorkBudget::unbounded(),
        )
        .unwrap();
        assert!(absent_proof.omitted_builtin_formals.is_empty());
        assert_eq!(
            census(no_host, &absent_proof).unwrap_err().reason(),
            ValidationReason::Registry
        );
        let mut wrong_namespace = authenticate(
            &view,
            &source_map,
            &module_map,
            &mut TypeWorkBudget::unbounded(),
        )
        .unwrap();
        wrong_namespace.omitted_builtin_formals = (4..14)
            .map(|local| TypeVariableId::resolved(entry.id(), local))
            .collect();
        assert_eq!(
            census(view.clone(), &wrong_namespace).unwrap_err().reason(),
            ValidationReason::Registry
        );
        let mut stale = authenticate(
            original,
            &source_map,
            &module_map,
            &mut TypeWorkBudget::unbounded(),
        )
        .unwrap();
        assert!(stale.omitted_builtin_formals.is_empty());
        stale.omitted_builtin_formals = proof.omitted_builtin_formals.clone();
        assert_eq!(
            census(original.as_ref().clone(), &stale)
                .unwrap_err()
                .reason(),
            ValidationReason::Registry
        );
        let mut effects = view.effects().to_vec();
        effects[0].public = false;
        let forged = view.with_effects(effects);
        assert_eq!(
            original_registry_phase_modules(&sources, &modules, forged)
                .unwrap_err()
                .reason(),
            ValidationReason::Registry
        );
    }

    #[test]
    fn checked_builtin_original_selective_legacy_view_has_no_host_or_omission_proof() {
        let directory =
            std::env::temp_dir().join(format!("ash-selective-host-{}", std::process::id()));
        std::fs::create_dir(&directory).unwrap();
        let path = directory.join("entry.ash");
        std::fs::write(
            &path,
            "import @builtin.foreign (checked_i64 as signed)\nmain : Unit -> Int\nmain () = 42\n",
        )
        .unwrap();
        let graph =
            crate::module::load_module_graph(&path, &crate::module::ModuleRoots::empty()).unwrap();
        std::fs::remove_dir_all(directory).unwrap();
        let loaded = graph
            .modules()
            .iter()
            .find(|module| module.id().is_builtin_foreign())
            .unwrap();
        let builtin =
            crate::elaborate::check_module(crate::resolve::resolve_module(loaded, &[]).unwrap())
                .unwrap();
        let entry = graph
            .modules()
            .iter()
            .find(|module| !module.id().is_builtin_foreign())
            .unwrap();
        let dependencies = entry
            .dependencies()
            .iter()
            .map(|edge| crate::resolve::DependencyExports::new(edge, builtin.exports()).unwrap())
            .collect::<Vec<_>>();
        let resolved = crate::resolve::resolve_module(entry, &dependencies).unwrap();
        let view = resolved
            .registry()
            .source_original_checker_view(
                resolved.imported_facts(),
                &mut TypeWorkBudget::unbounded(),
            )
            .unwrap();
        assert!(
            view.effect(EffectId::new(
                loaded.id(),
                crate::module::FOREIGN_NATIVE_HOST_LOCAL
            ))
            .is_none()
        );
        let sources = graph
            .modules()
            .iter()
            .map(|module| module.source())
            .collect::<Vec<_>>();
        let modules = graph
            .modules()
            .iter()
            .map(|module| (module.id(), module.source().id()))
            .collect::<Vec<_>>();
        let proof = authenticate(
            &view,
            &sources
                .iter()
                .map(|source| (source.id(), *source))
                .collect(),
            &modules.iter().copied().collect(),
            &mut TypeWorkBudget::unbounded(),
        )
        .unwrap();
        assert!(proof.omitted_builtin_formals.is_empty());
        assert!(original_registry_phase_modules(&sources, &modules, view).is_ok());
    }
}
