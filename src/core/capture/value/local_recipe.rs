//! Once-per-Graph source recipe preparation, not source/frame admission.
//!
//! Own one Compiler in the normal Analysis for its immutable Graph loan. New
//! family roots reuse accepted AND declined expression cells. Construction
//! borrows Analysis's original evidence_keys/evidence_ports only temporarily;
//! the resulting object borrows Graph, never Analysis or its index storage.
//! No Type/Row, Expr, capture vector or dictionary tuple is cloned here.

use std::collections::HashSet;

use super::{Analysis, Expr, Failure, Graph, ProducerWitness, TypeWorkBudget, charge};
use super::deferred_frame::ProjectionClass;
use crate::types::{Kind, KindedArgument};

const ASSIGNED: u16 = 1;
const RESOURCE: u16 = 2;
const DICTIONARY: u16 = 4;
const GLOBAL: u16 = 8;
const AMBIGUOUS_GLOBAL: u16 = 16;
const OPAQUE_PROVIDER: u16 = 32;
const LEXICAL: u16 = 64;
const AMBIGUOUS_LEXICAL: u16 = 128;
const CAPTURED: u16 = 256;

#[derive(Clone, Copy)]
struct Ownership {
    flags: u16,
    global: usize,
    dictionary_start: usize,
    dictionary_len: usize,
    body_owner: usize,
    body_owners: usize,
    handler_capture: bool,
}

// These coordinates retain an ORIGINAL ordered source occurrence. They do not
// collapse repeated methods, repeated keys, repeated arguments or shared ports.
#[derive(Clone, Copy, Debug)]
pub(super) struct DictionarySource {
    pub(super) evidence_expression: usize,
    pub(super) binding_ordinal: usize,
    pub(super) evidence_ordinal: usize,
}

// One original Bind initializer occurrence. This is code-shape
// provenance only: an unentered binding can stay empty and capture transport
// can supply the same code with a different creation. Always retain Head(b,c).
#[derive(Clone, Copy, Debug)]
pub(super) struct LexicalSource {
    pub(super) owner: usize,
    pub(super) initializer: usize,
}

#[derive(Clone, Copy, Debug)]
pub(super) enum SlotRole {
    Unbound,
    Metadata,
    Resource,
    Global { source: usize },
    Lexical { source: usize },
    Dictionary { start: usize, len: usize },
}

// Fixed local value shape, deliberately weaker than a complete occurrence's
// ProjectionClass. Function shape does not inspect captures; Evidence shape
// does not inspect dictionary bindings or residual validity. Those dependencies
// remain live in the owner-held transport. There is no conversion to a complete
// class and no admission authority in this type.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum LocalShape {
    Empty,
    Metadata,
    Callable(usize),
}

#[derive(Clone, Copy, Debug)]
pub(super) enum RecipeTag {
    Scalar,
    Slot(SlotRole),
    Alias,
    Merge,
    Function,
    TypedCall { factory: usize, body: usize },
    Evidence,
}

// Static original producer coordinates, not an occurrence/admission token.
// q and literal G have no indexed direct writer/capture roles. Transparent
// Evidence topology can still install q, and can write G at Call contexts.
// The consuming owner needs context separation, complete capture classes,
// actual inputs and the immutable source-family/consumer publication policy.
#[derive(Clone, Copy, Debug)]
pub(super) struct DirectPayload {
    pub(super) payload: usize,
    pub(super) factory: usize,
    pub(super) body: usize,
}

#[derive(Clone, Copy, Debug)]
pub(super) enum Decline {
    Unsupported,
    ConflictingOwnership,
    UnsealedTypedCall,
    MixedProjection,
    Cyclic,
    Dependency,
}

#[derive(Clone, Copy)]
struct Prepared {
    tag: RecipeTag,
    shape: LocalShape,
    // Separate from local shape. Some(true) requires the complete static
    // all-writer closure proof below; Some(false) is a permanent decline.
    writer_class: Option<bool>,
}

#[derive(Clone, Copy)]
enum Cell {
    Unseen,
    Visiting,
    Accepted(Prepared),
    Declined,
}

// Borrowed original operands and their weaker fixed shape. Dictionary Slot
// shape includes every indexed source binding input; Function/Evidence shape
// deliberately stops before capture/binding validity and live dependencies.
// The owner-held source visit must still authenticate occurrence writers,
// complete classes, lexical Type/Row scope, creation/root feeds, phases and
// frozen boundaries. Shape preparation alone cannot admit a source visit.
pub(super) struct PreparedSource<'g> {
    pub(super) tag: RecipeTag,
    pub(super) shape: LocalShape,
    pub(super) source: &'g Expr,
}

#[derive(Clone, Copy)]
struct Work {
    expression: usize,
    tag: RecipeTag,
    next: usize,
}

pub(super) struct Compiler<'g> {
    graph: &'g Graph,
    ownership: Vec<Ownership>,
    // CSR groups actual source binding matches by original target port. This
    // is derived provenance, not a duplicate evidence-key/port lookup map.
    dictionary: Vec<DictionarySource>,
    lexical: Vec<LexicalSource>,
    cells: Vec<Cell>,
}

fn flag(ownership: &mut [Ownership], port: usize, bits: u16,
    budget: &mut TypeWorkBudget) -> Result<(), Failure>
{
    charge(budget, 1)?;
    ownership.get_mut(port).ok_or(Failure::Invalid)?.flags |= bits;
    Ok(())
}

fn lexical_source(
    ownership: &mut [Ownership], sources: &mut Vec<LexicalSource>,
    binder: usize, source: LexicalSource, budget: &mut TypeWorkBudget,
) -> Result<(), Failure> {
    charge(budget, 3)?; // role lookup, uniqueness test and role publication
    let role = ownership.get_mut(binder).ok_or(Failure::Invalid)?;
    if role.flags & LEXICAL != 0 {
        role.flags |= AMBIGUOUS_LEXICAL;
        return Ok(());
    }
    charge(budget, 2)?; // reserve and append the original occurrence record
    sources.try_reserve(1).map_err(|_| Failure::Resource)?;
    // GLOBAL and LEXICAL are mutually exclusive in every accepted role. Reuse
    // this scalar index; conflicting roles decline before either interpretation.
    role.global = sources.len();
    role.flags |= LEXICAL;
    sources.push(source);
    Ok(())
}

fn same_kind(left: &Kind, right: &Kind, budget: &mut TypeWorkBudget) -> Result<bool, Failure> {
    charge(budget, 1)?;
    let mut pending = Vec::new();
    pending.try_reserve(1).map_err(|_| Failure::Resource)?;
    pending.push((left, right));
    while let Some((left, right)) = pending.pop() {
        charge(budget, 1)?;
        match (left, right) {
            (Kind::Type, Kind::Type) | (Kind::EffectRow, Kind::EffectRow) => {}
            (Kind::Arrow(ld, lc), Kind::Arrow(rd, rc)) => {
                charge(budget, 2)?;
                pending.try_reserve(2).map_err(|_| Failure::Resource)?;
                pending.push((lc.as_ref(), rc.as_ref()));
                pending.push((ld.as_ref(), rd.as_ref()));
            }
            _ => return Ok(false),
        }
    }
    Ok(true)
}

fn combine(left: LocalShape, right: LocalShape) -> Option<LocalShape> {
    match (left, right) {
        (LocalShape::Empty, other) | (other, LocalShape::Empty) => Some(other),
        (left, right) if left == right => Some(left),
        _ => None,
    }
}

impl<'g> Compiler<'g> {
    // Analysis::new built both exact indices from THIS Graph's complete
    // ordered evidence vector. Borrow them during construction; do not rebuild
    // ports_by_key or retain a self-reference to Analysis in this compiler.
    pub(super) fn new(analysis: &Analysis<'g>, budget: &mut TypeWorkBudget) -> Result<Self, Failure> {
        let graph = analysis.graph;
        let count = graph.expressions.len();
        charge(budget, count.checked_mul(2).ok_or(Failure::Resource)?)?;
        let mut ownership = Vec::new();
        ownership.try_reserve_exact(count).map_err(|_| Failure::Resource)?;
        ownership.resize(count, Ownership { flags: 0, global: 0,
            dictionary_start: 0, dictionary_len: 0, body_owner: 0,
            body_owners: 0, handler_capture: false });
        let mut cells = Vec::new();
        cells.try_reserve_exact(count).map_err(|_| Failure::Resource)?;
        cells.resize(count, Cell::Unseen);
        for &(port, source) in &graph.globals {
            charge(budget, 1)?;
            if graph.expressions.get(source).is_none() { return Err(Failure::Invalid); }
            let role = ownership.get_mut(port).ok_or(Failure::Invalid)?;
            if role.flags & GLOBAL != 0 { role.flags |= AMBIGUOUS_GLOBAL; }
            else { role.global = source; }
            role.flags |= GLOBAL;
        }
        let mut lexical = Vec::new();
        for (owner, expression) in graph.expressions.iter().enumerate() {
            charge(budget, 1)?;
            match expression {
                Expr::Bind { binder, initializer, .. } => lexical_source(
                    &mut ownership, &mut lexical, *binder,
                    LexicalSource { owner, initializer: *initializer }, budget)?,
                Expr::Recursive { bindings, .. } => {
                    for (binder, _) in bindings {
                        flag(&mut ownership, *binder, ASSIGNED, budget)?;
                    }
                }
                Expr::Match { arms, .. } => {
                    for (bindings, _) in arms {
                        charge(budget, 1)?;
                        for (binder, _) in bindings { flag(&mut ownership, *binder, ASSIGNED, budget)?; }
                    }
                }
                Expr::Handler { clauses, .. } => {
                    for clause in clauses {
                        for capture in &clause.captures {
                            flag(&mut ownership, *capture, CAPTURED, budget)?;
                            charge(budget, 1)?;
                            ownership.get_mut(*capture).ok_or(Failure::Invalid)?.handler_capture = true;
                        }
                        flag(&mut ownership, clause.input, ASSIGNED, budget)?;
                        for (binder, _) in &clause.bindings { flag(&mut ownership, *binder, ASSIGNED, budget)?; }
                    }
                }
                Expr::Function { parameters, captures, body } => {
                    charge(budget, 2)?;
                    let role = ownership.get_mut(*body).ok_or(Failure::Invalid)?;
                    if role.body_owners == 0 { role.body_owner = owner; }
                    role.body_owners = role.body_owners.checked_add(1).ok_or(Failure::Resource)?;
                    for capture in captures {
                        flag(&mut ownership, *capture, CAPTURED, budget)?;
                    }
                    for parameter in parameters {
                        charge(budget, 1)?;
                        if !graph.metadata.contains_key(parameter) {
                            flag(&mut ownership, *parameter, ASSIGNED, budget)?;
                        }
                    }
                }
                Expr::Resource { handle, identity, .. } => {
                    flag(&mut ownership, *handle, RESOURCE, budget)?;
                    flag(&mut ownership, *identity, RESOURCE, budget)?;
                }
                _ => {}
            }
        }
        for provider in &graph.provider {
            charge(budget, 1)?;
            for (port, _) in &provider.lexical { flag(&mut ownership, *port, ASSIGNED, budget)?; }
            for port in &provider.parameters { flag(&mut ownership, *port, ASSIGNED, budget)?; }
            for port in &provider.capture_ports { flag(&mut ownership, *port, OPAQUE_PROVIDER, budget)?; }
        }
        // Use the existing original port index to mark exact dictionary roles.
        for (&port, positions) in &analysis.evidence_ports {
            flag(&mut ownership, port, DICTIONARY, budget)?;
            for &position in positions {
                charge(budget, 1)?;
                if graph.evidence.get(position).is_none_or(|(_, actual)| *actual != port) {
                    return Err(Failure::Invalid);
                }
            }
        }
        // Count exact binding/key matches, retaining each original evidence
        // ordinal, including duplicate keys mapping to the same target port.
        for expression in &graph.expressions {
            charge(budget, 1)?;
            if let Expr::Evidence { bindings, .. } = expression {
                for &(requirement, method, argument) in bindings {
                    charge(budget, 1)?;
                    if graph.expressions.get(argument).is_none() { return Err(Failure::Invalid); }
                    let key = (requirement, method);
                    if let Some(positions) = analysis.evidence_keys.get(&key) {
                        for &position in positions {
                            charge(budget, 1)?;
                            let &(actual_key, port) = graph.evidence.get(position).ok_or(Failure::Invalid)?;
                            if actual_key != key { return Err(Failure::Invalid); }
                            let role = ownership.get_mut(port).ok_or(Failure::Invalid)?;
                            role.dictionary_len = role.dictionary_len.checked_add(1).ok_or(Failure::Resource)?;
                        }
                    }
                }
            }
        }
        let mut total = 0usize;
        charge(budget, count)?;
        for role in &mut ownership {
            role.dictionary_start = total;
            total = total.checked_add(role.dictionary_len).ok_or(Failure::Resource)?;
        }
        charge(budget, total.checked_add(count).ok_or(Failure::Resource)?)?;
        let mut dictionary = Vec::new();
        dictionary.try_reserve_exact(total).map_err(|_| Failure::Resource)?;
        dictionary.resize(total, DictionarySource { evidence_expression: 0,
            binding_ordinal: 0, evidence_ordinal: 0 });
        let mut cursors = Vec::new();
        cursors.try_reserve_exact(count).map_err(|_| Failure::Resource)?;
        cursors.resize(count, 0usize);
        for (expression, source) in graph.expressions.iter().enumerate() {
            charge(budget, 1)?;
            if let Expr::Evidence { bindings, .. } = source {
                for (binding_ordinal, &(requirement, method, _)) in bindings.iter().enumerate() {
                    charge(budget, 1)?;
                    if let Some(positions) = analysis.evidence_keys.get(&(requirement, method)) {
                        for &evidence_ordinal in positions {
                            charge(budget, 1)?;
                            let port = graph.evidence.get(evidence_ordinal).ok_or(Failure::Invalid)?.1;
                            let role = ownership.get(port).ok_or(Failure::Invalid)?;
                            let cursor = cursors.get_mut(port).ok_or(Failure::Invalid)?;
                            if *cursor >= role.dictionary_len { return Err(Failure::Invalid); }
                            let destination = role.dictionary_start.checked_add(*cursor).ok_or(Failure::Resource)?;
                            *dictionary.get_mut(destination).ok_or(Failure::Invalid)? = DictionarySource {
                                evidence_expression: expression, binding_ordinal, evidence_ordinal };
                            *cursor += 1;
                        }
                    }
                }
            }
        }
        charge(budget, count)?;
        if ownership.iter().zip(cursors).any(|(role, cursor)| role.dictionary_len != cursor) {
            return Err(Failure::Invalid);
        }
        Ok(Self { graph, ownership, dictionary, lexical, cells })
    }

    fn witness(&self, expression: usize) -> Option<&'g ProducerWitness> {
        match self.graph.producers.as_slice() { [table] => table.entries.get(&expression), _ => None }
    }

    // This repeats no all-global scan. Indexed source ownership plus the exact
    // two original typed witnesses supplies the factory/use input relation.
    // It does not authenticate a live callee stream or dynamic source visit.
    fn typed_factory(&self, call: usize, budget: &mut TypeWorkBudget)
        -> Result<Option<(usize, usize)>, Failure>
    {
        let Some(Expr::Call { function, arguments, type_application: true, .. }) = self.graph.expressions.get(call)
            else { return Ok(None); };
        let Some(ProducerWitness::Application { function: original, binders: use_header,
            arguments: actuals }) = self.witness(call) else { return Ok(None); };
        charge(budget, arguments.len())?;
        if function != original || arguments.len() != actuals.len()
            || arguments.iter().zip(actuals).any(|(port, actual)| *port != actual.port)
        { return Ok(None); }
        let Some(Expr::Alias(global)) = self.graph.expressions.get(*function) else { return Ok(None); };
        if self.ownership.get(*function).ok_or(Failure::Invalid)?.flags & OPAQUE_PROVIDER != 0 {
            return Ok(None);
        }
        let role = self.ownership.get(*global).ok_or(Failure::Invalid)?;
        if role.flags & (GLOBAL | ASSIGNED | AMBIGUOUS_GLOBAL | OPAQUE_PROVIDER | DICTIONARY | RESOURCE | LEXICAL | AMBIGUOUS_LEXICAL) != GLOBAL
            || !matches!(self.graph.expressions.get(*global), Some(Expr::Slot))
            || self.graph.metadata.contains_key(global)
        { return Ok(None); }
        let factory = role.global;
        let Some(ProducerWitness::Abstraction { binders: definition, formals }) = self.witness(factory)
            else { return Ok(None); };
        let Some(Expr::Function { parameters, body, .. }) = self.graph.expressions.get(factory)
            else { return Ok(None); };
        charge(budget, formals.len())?;
        if formals.is_empty() || parameters != formals || formals.len() != definition.len()
            || definition.len() != use_header.len() || actuals.len() != formals.len()
        { return Ok(None); }
        let Some(Expr::Function { parameters: inner, captures, .. }) = self.graph.expressions.get(*body)
            else { return Ok(None); };
        if inner.len() != 1 || captures.is_empty() || self.graph.metadata.contains_key(&inner[0])
            || !self.graph.targets.contains_key(body)
        { return Ok(None); }
        charge(budget, formals.len().checked_mul(3).ok_or(Failure::Resource)?)?;
        let mut definitions = HashSet::new();
        let mut uses = HashSet::new();
        let mut slots = HashSet::new();
        definitions.try_reserve(formals.len()).map_err(|_| Failure::Resource)?;
        uses.try_reserve(formals.len()).map_err(|_| Failure::Resource)?;
        slots.try_reserve(formals.len()).map_err(|_| Failure::Resource)?;
        for (((def, dk), (use_binder, uk)), (formal, argument)) in definition.iter()
            .zip(use_header).zip(formals.iter().zip(actuals))
        {
            charge(budget, 1)?;
            if !definitions.insert(*def) || !uses.insert(*use_binder) || !slots.insert(*formal)
                || self.graph.metadata.get(formal) != Some(def)
                || !matches!(self.graph.expressions.get(*formal), Some(Expr::Slot))
                || self.ownership.get(*formal).ok_or(Failure::Invalid)?.flags & !CAPTURED != 0
                || !same_kind(dk, uk, budget)?
            { return Ok(None); }
            match (dk, argument.value.as_ref()) {
                (Kind::EffectRow, KindedArgument::RowArg(_)) => {}
                (Kind::Type | Kind::Arrow(_, _), KindedArgument::TypeArg(_)) => {}
                _ => return Ok(None),
            }
            let Some(Expr::Merge(inputs)) = self.graph.expressions.get(argument.port) else { return Ok(None); };
            charge(budget, inputs.len())?;
            if inputs.iter().any(|port| !self.graph.metadata.contains_key(port)
                || !matches!(self.graph.expressions.get(*port), Some(Expr::Slot)))
            { return Ok(None); }
        }
        Ok(Some((factory, *body)))
    }

    fn tag(&self, expression: usize, budget: &mut TypeWorkBudget)
        -> Result<Result<RecipeTag, Decline>, Failure>
    {
        charge(budget, 1)?;
        let source = self.graph.expressions.get(expression).ok_or(Failure::Invalid)?;
        let role = self.ownership.get(expression).ok_or(Failure::Invalid)?;
        if role.flags & OPAQUE_PROVIDER != 0 { return Ok(Err(Decline::ConflictingOwnership)); }
        Ok(Ok(match source {
            Expr::Scalar => RecipeTag::Scalar,
            Expr::Slot => {
                if role.flags & (ASSIGNED | AMBIGUOUS_GLOBAL | AMBIGUOUS_LEXICAL) != 0 { return Ok(Err(Decline::ConflictingOwnership)); }
                let metadata = self.graph.metadata.contains_key(&expression);
                // Resource identity is also typed metadata. Both writer kinds
                // produce the same metadata projection; this is one category.
                let categories = usize::from(metadata || role.flags & RESOURCE != 0)
                    + usize::from(role.flags & GLOBAL != 0) + usize::from(role.flags & DICTIONARY != 0)
                    + usize::from(role.flags & LEXICAL != 0);
                if categories > 1 { return Ok(Err(Decline::ConflictingOwnership)); }
                RecipeTag::Slot(if role.flags & RESOURCE != 0 { SlotRole::Resource }
                    else if metadata { SlotRole::Metadata }
                    else if role.flags & GLOBAL != 0 { SlotRole::Global { source: role.global } }
                    else if role.flags & LEXICAL != 0 {
                        charge(budget, 3)?; // occurrence record, owning Bind, literal Function
                        let source = self.lexical.get(role.global).ok_or(Failure::Invalid)?;
                        let actual = match self.graph.expressions.get(source.owner) {
                            Some(Expr::Bind { binder, initializer, .. }) => Some((*binder, *initializer)),
                            _ => None,
                        };
                        if actual != Some((expression, source.initializer)) { return Err(Failure::Invalid); }
                        if !matches!(self.graph.expressions.get(source.initializer), Some(Expr::Function { .. })) {
                            return Ok(Err(Decline::Unsupported));
                        }
                        SlotRole::Lexical { source: source.initializer }
                    }
                    else if role.flags & DICTIONARY != 0 { SlotRole::Dictionary {
                        start: role.dictionary_start, len: role.dictionary_len } }
                    else { SlotRole::Unbound })
            }
            Expr::Alias(_) => RecipeTag::Alias,
            Expr::Merge(_) => RecipeTag::Merge,
            Expr::Function { .. } => RecipeTag::Function,
            Expr::Call { type_application: true, .. } => {
                let Some((factory, body)) = self.typed_factory(expression, budget)?
                    else { return Ok(Err(Decline::UnsealedTypedCall)); };
                RecipeTag::TypedCall { factory, body }
            }
            // The weaker code shape depends only on value. Original ordered
            // bindings, residuals and late Unknown are owner-transport work.
            Expr::Evidence { .. } => RecipeTag::Evidence,
            _ => return Ok(Err(Decline::Unsupported)),
        }))
    }

    fn child_count(&self, expression: usize, tag: RecipeTag) -> Result<usize, Failure> {
        Ok(match (tag, self.graph.expressions.get(expression).ok_or(Failure::Invalid)?) {
            (RecipeTag::Slot(SlotRole::Global { .. } | SlotRole::Lexical { .. }) | RecipeTag::Alias, _) => 1,
            (RecipeTag::Slot(SlotRole::Dictionary { len, .. }), _) => len,
            (RecipeTag::Merge, Expr::Merge(values)) => values.len(),
            (RecipeTag::Function, Expr::Function { .. }) => 0,
            (RecipeTag::TypedCall { .. }, Expr::Call { arguments, .. }) => arguments.len().checked_add(2).ok_or(Failure::Resource)?,
            (RecipeTag::Evidence, Expr::Evidence { .. }) => 1,
            (RecipeTag::Scalar | RecipeTag::Slot(_), _) => 0,
            _ => return Err(Failure::Invalid),
        })
    }

    fn child(&self, expression: usize, tag: RecipeTag, position: usize) -> Result<usize, Failure> {
        let source = self.graph.expressions.get(expression).ok_or(Failure::Invalid)?;
        Ok(match (tag, source) {
            (RecipeTag::Slot(SlotRole::Global { source } | SlotRole::Lexical { source }), _) if position == 0 => source,
            (RecipeTag::Slot(SlotRole::Dictionary { start, len }), _) if position < len => {
                let original = self.dictionary.get(start.checked_add(position).ok_or(Failure::Resource)?).ok_or(Failure::Invalid)?;
                let binding = self.dictionary_binding(*original).ok_or(Failure::Invalid)?;
                let entry = self.graph.evidence.get(original.evidence_ordinal).ok_or(Failure::Invalid)?;
                if entry.1 != expression || entry.0 != (binding.0, binding.1) { return Err(Failure::Invalid); }
                binding.2
            }
            (RecipeTag::Alias, Expr::Alias(value)) if position == 0 => *value,
            (RecipeTag::Merge, Expr::Merge(values)) => *values.get(position).ok_or(Failure::Invalid)?,
            (RecipeTag::TypedCall { factory, body }, Expr::Call { arguments, .. }) => {
                if position < arguments.len() { arguments[position] }
                else if position == arguments.len() { factory }
                else if position == arguments.len() + 1 { body }
                else { return Err(Failure::Invalid); }
            }
            (RecipeTag::Evidence, Expr::Evidence { value, .. }) if position == 0 => *value,
            _ => return Err(Failure::Invalid),
        })
    }

    fn finish(&self, expression: usize, tag: RecipeTag, budget: &mut TypeWorkBudget)
        -> Result<Result<LocalShape, Decline>, Failure>
    {
        let mut union = LocalShape::Empty;
        let count = self.child_count(expression, tag)?;
        charge(budget, count)?;
        for position in 0..count {
            let child = self.child(expression, tag, position)?;
            let Some(Cell::Accepted(prepared)) = self.cells.get(child) else { return Ok(Err(Decline::Dependency)); };
            match tag {
                RecipeTag::Slot(SlotRole::Dictionary { .. }) => {
                    let Some(next) = combine(union, prepared.shape) else { return Ok(Err(Decline::MixedProjection)); };
                    union = next;
                }
                RecipeTag::Merge => {
                    if !matches!(prepared.shape, LocalShape::Empty | LocalShape::Metadata) {
                        return Ok(Err(Decline::MixedProjection));
                    }
                }
                RecipeTag::TypedCall { factory, body } => {
                    let arguments = count - 2;
                    let valid = if position < arguments {
                        matches!(prepared.shape, LocalShape::Empty | LocalShape::Metadata)
                    } else if position == arguments { prepared.shape == LocalShape::Callable(factory) }
                    else { prepared.shape == LocalShape::Callable(body) };
                    if !valid { return Ok(Err(Decline::MixedProjection)); }
                }
                RecipeTag::Evidence if position == 0 => {
                    if !matches!(prepared.shape, LocalShape::Callable(_)) { return Ok(Err(Decline::MixedProjection)); }
                    union = prepared.shape;
                }
                RecipeTag::Alias | RecipeTag::Slot(SlotRole::Global { .. } | SlotRole::Lexical { .. }) => union = prepared.shape,
                _ => {}
            }
        }
        Ok(Ok(match tag {
            RecipeTag::Scalar | RecipeTag::Merge | RecipeTag::Slot(SlotRole::Metadata | SlotRole::Resource) => LocalShape::Metadata,
            RecipeTag::Function => LocalShape::Callable(expression),
            RecipeTag::TypedCall { body, .. } => LocalShape::Callable(body),
            RecipeTag::Slot(SlotRole::Unbound) => LocalShape::Empty,
            RecipeTag::Slot(_) | RecipeTag::Alias | RecipeTag::Evidence => union,
        }))
    }

    fn enter(&mut self, expression: usize, pending: &mut Vec<Work>, budget: &mut TypeWorkBudget)
        -> Result<(), Failure>
    {
        // Reserve before Visiting is published. These two units also cover
        // resetting this temporary cell if later resource refusal unwinds.
        charge(budget, 2)?;
        pending.try_reserve(1).map_err(|_| Failure::Resource)?;
        match self.tag(expression, budget)? {
            Ok(tag) => {
                *self.cells.get_mut(expression).ok_or(Failure::Invalid)? = Cell::Visiting;
                pending.push(Work { expression, tag, next: 0 });
            }
            Err(_) => *self.cells.get_mut(expression).ok_or(Failure::Invalid)? = Cell::Declined,
        }
        Ok(())
    }

    fn compile_one(&mut self, root: usize, budget: &mut TypeWorkBudget) -> Result<bool, Failure> {
        charge(budget, 1)?;
        match self.cells.get(root).copied().ok_or(Failure::Invalid)? {
            Cell::Accepted(_) => return Ok(true),
            Cell::Declined => return Ok(false),
            Cell::Visiting => return Err(Failure::Invalid),
            Cell::Unseen => {}
        }
        let mut pending = Vec::new();
        let result = (|| {
            self.enter(root, &mut pending, budget)?;
            while let Some(work) = pending.last().copied() {
                charge(budget, 1)?;
                if matches!(self.cells[work.expression], Cell::Declined) { pending.pop(); continue; }
                let count = self.child_count(work.expression, work.tag)?;
                if work.next < count {
                    let child = self.child(work.expression, work.tag, work.next)?;
                    pending.last_mut().ok_or(Failure::Invalid)?.next += 1;
                    match self.cells.get(child).copied().ok_or(Failure::Invalid)? {
                        Cell::Accepted(_) => {}
                        Cell::Declined => self.cells[work.expression] = Cell::Declined,
                        Cell::Visiting => {
                            self.cells[child] = Cell::Declined;
                            self.cells[work.expression] = Cell::Declined;
                        }
                        Cell::Unseen => self.enter(child, &mut pending, budget)?,
                    }
                    continue;
                }
                self.cells[work.expression] = match self.finish(work.expression, work.tag, budget)? {
                    Ok(shape) => Cell::Accepted(Prepared { tag: work.tag, shape, writer_class: None }),
                    Err(_) => Cell::Declined,
                };
                pending.pop();
            }
            Ok(matches!(self.cells[root], Cell::Accepted(_)))
        })();
        if result.is_err() {
            // Flat iterative cleanup; completed accepted/declined cells remain
            // reusable. A work refusal never becomes a semantic decline.
            for work in pending {
                if matches!(self.cells[work.expression], Cell::Visiting) {
                    self.cells[work.expression] = Cell::Unseen;
                }
            }
        }
        result
    }

    pub(super) fn compile_set(&mut self, roots: &[usize], budget: &mut TypeWorkBudget) -> Result<bool, Failure> {
        charge(budget, roots.len())?;
        for root in roots { if !self.compile_one(*root, budget)? { return Ok(false); } }
        Ok(true)
    }

    pub(super) fn prepared(&self, expression: usize) -> Option<PreparedSource<'g>> {
        let Cell::Accepted(prepared) = *self.cells.get(expression)? else { return None; };
        Some(PreparedSource { tag: prepared.tag, shape: prepared.shape,
            source: self.graph.expressions.get(expression)? })
    }


    // Indexed source ownership only, independent of the shape cache. A
    // dictionary Slot whose inputs decline/cycle still has its original role.
    // This neither proves absence of occurrence writers nor grants admission;
    // the owner must use the role with the original definition-context laws.
    pub(super) fn source_slot_role(&self, expression: usize, budget: &mut TypeWorkBudget)
        -> Result<Option<SlotRole>, Failure>
    {
        charge(budget, 1)?;
        if !matches!(self.graph.expressions.get(expression).ok_or(Failure::Invalid)?, Expr::Slot) {
            return Ok(None);
        }
        Ok(match self.tag(expression, budget)? {
            Ok(RecipeTag::Slot(role)) => Some(role),
            Ok(_) => return Err(Failure::Invalid),
            Err(_) => None,
        })
    }

    // Indexed over ALL present Graph functions, including relocated imports.
    // None includes both a missing owner and a shared/overwritten root body.
    pub(super) fn unique_body_owner(&self, body: usize, budget: &mut TypeWorkBudget)
        -> Result<Option<usize>, Failure>
    {
        charge(budget, 1)?;
        let role = self.ownership.get(body).ok_or(Failure::Invalid)?;
        Ok((role.body_owners == 1).then_some(role.body_owner))
    }

    // Complete zero-writer exclusion, separate from a slot's value shape.
    // Graph.start seeds only indexed globals at zero. Bind/assignment/resource
    // and opaque provider writers are excluded here. Remaining dictionary
    // writes target Call contexts; formal/capture/handler transport targets
    // nonzero Root/Invoke/Dispatch contexts. Context interning can fold only to
    // an existing Step, never to the zero path. Thus these original Slots have
    // no writer at zero for the lifetime of this immutable Graph.
    pub(super) fn prove_zero_empty_slot(&self, expression: usize,
        budget: &mut TypeWorkBudget) -> Result<bool, Failure>
    {
        charge(budget, 1)?;
        if !matches!(self.graph.expressions.get(expression), Some(Expr::Slot)) {
            return Ok(false);
        }
        let ownership = self.ownership.get(expression).ok_or(Failure::Invalid)?;
        if ownership.handler_capture || ownership.flags & !(CAPTURED | DICTIONARY) != 0 {
            return Ok(false);
        }
        Ok(matches!(self.source_slot_role(expression, budget)?,
            Some(SlotRole::Metadata | SlotRole::Dictionary { .. } | SlotRole::Unbound)))
    }

    // No assignment, provider, handler, resource, lexical or keyed dictionary
    // writer may target this non-Slot local recipe. Ordinary same-expression
    // capture/root transport is allowed and must remain a separate live feed.
    pub(super) fn raw_local_recipe(&self, expression: usize, budget: &mut TypeWorkBudget)
        -> Result<bool, Failure>
    {
        charge(budget, 1)?;
        let role = self.ownership.get(expression).ok_or(Failure::Invalid)?;
        Ok(!matches!(self.graph.expressions.get(expression), Some(Expr::Slot))
            && !self.graph.metadata.contains_key(&expression)
            && !role.handler_capture && role.flags & !CAPTURED == 0)
    }

    // Direct Function capture/writer exclusion. Transparent Evidence can
    // still visit this body at a Call context; actual fresh-Invoke separation
    // is an additional owner check, not a consequence of this role lookup.
    pub(super) fn raw_returned_body(&self, expression: usize, budget: &mut TypeWorkBudget)
        -> Result<bool, Failure>
    {
        charge(budget, 1)?;
        let role = self.ownership.get(expression).ok_or(Failure::Invalid)?;
        Ok(matches!(self.graph.expressions.get(expression), Some(Expr::Function { .. }))
            && !self.graph.metadata.contains_key(&expression)
            && !role.handler_capture && role.flags == 0)
    }

    // This is a coordinate/role certificate for a FRESH nonzero raw Invoke.
    // It is not a complete class and does not certify context freshness.
    // Global initialization occurs only at zero; a noncaptured global Slot at
    // the fresh Invoke has no copied global source. Dictionary writes occur
    // at Call destinations. Neither may be silently redirected to zero.
    pub(super) fn fresh_raw_slot_role(&self, expression: usize, budget: &mut TypeWorkBudget)
        -> Result<Option<SlotRole>, Failure>
    {
        charge(budget, 1)?;
        let role = self.ownership.get(expression).ok_or(Failure::Invalid)?;
        if role.handler_capture
            || role.flags & (ASSIGNED | RESOURCE | OPAQUE_PROVIDER | LEXICAL
                | AMBIGUOUS_LEXICAL | AMBIGUOUS_GLOBAL) != 0
        { return Ok(None); }
        Ok(match self.source_slot_role(expression, budget)? {
            Some(role @ (SlotRole::Unbound | SlotRole::Metadata | SlotRole::Global { .. }
                | SlotRole::Dictionary { .. })) => Some(role),
            Some(SlotRole::Resource | SlotRole::Lexical { .. }) | None => None,
        })
    }

    fn class_writers_allowed(&self, expression: usize, prepared: Prepared,
        budget: &mut TypeWorkBudget) -> Result<bool, Failure>
    {
        charge(budget, 1)?;
        let role = self.ownership.get(expression).ok_or(Failure::Invalid)?;
        if role.handler_capture { return Ok(false); }
        let allowed = match prepared.tag {
            RecipeTag::Slot(SlotRole::Metadata | SlotRole::Unbound) => CAPTURED,
            // Exact owner-bearing actual metadata may remain an opaque seed.
            // This class proof never admits it as a normalized support Slot;
            // fresh_raw_slot_role separately rejects RESOURCE.
            RecipeTag::Slot(SlotRole::Resource) => CAPTURED | RESOURCE,
            RecipeTag::Slot(SlotRole::Global { .. }) => CAPTURED | GLOBAL,
            RecipeTag::Slot(SlotRole::Dictionary { .. }) => CAPTURED | DICTIONARY,
            // tag() authenticated one Bind with a literal Function initializer.
            // Its full initializer dependency is still checked below. An
            // unentered binder may be empty, and same-expression capture/root
            // feeds may change creation, but neither introduces another code.
            // This opaque source class grants no raw-Invoke Slot baseline or
            // capture/frame validity; those boundaries still reject LEXICAL.
            RecipeTag::Slot(SlotRole::Lexical { .. }) => CAPTURED | LEXICAL,
            RecipeTag::Scalar | RecipeTag::Alias | RecipeTag::Merge | RecipeTag::Function
                | RecipeTag::TypedCall { .. } | RecipeTag::Evidence => CAPTURED,
        };
        Ok(role.flags & !allowed == 0)
    }

    // Prove a homogeneous upper class of ALL normal-analysis writers. This
    // does not prove readiness/nonemptiness or authorize a frame. LocalShape
    // alone is insufficient: each output dependency must also have only the
    // enumerated local writer and same-expression capture/root transport.
    // Metadata parameters produce metadata; global Slots have one indexed
    // source; unique lexical Function initializers retain their full source
    // dependency; dictionary Slots include EVERY ordered original binding input.
    // The accepted value-dependency graph is finite; Function capture/frame
    // dependencies deliberately require the separate whole-family qualifier.
    pub(super) fn prove_source_class(&mut self, expression: usize, budget: &mut TypeWorkBudget)
        -> Result<Option<ProjectionClass>, Failure>
    {
        if !self.compile_one(expression, budget)? { return Ok(None); }
        let mut pending = Vec::new();
        charge(budget, 1)?;
        pending.try_reserve(1).map_err(|_| Failure::Resource)?;
        pending.push((expression, false));
        while let Some((current, finish)) = pending.pop() {
            charge(budget, 1)?;
            let Cell::Accepted(prepared) = *self.cells.get(current).ok_or(Failure::Invalid)?
                else { return Err(Failure::Invalid); };
            if prepared.writer_class.is_some() { continue; }
            let count = self.child_count(current, prepared.tag)?;
            let proved = if !self.class_writers_allowed(current, prepared, budget)? {
                false
            } else if !finish {
                let storage = count.checked_add(1).ok_or(Failure::Resource)?;
                charge(budget, storage)?;
                pending.try_reserve(storage).map_err(|_| Failure::Resource)?;
                pending.push((current, true));
                for position in (0..count).rev() {
                    pending.push((self.child(current, prepared.tag, position)?, false));
                }
                continue;
            } else {
                charge(budget, count)?;
                let mut proved = true;
                for position in 0..count {
                    let child = self.child(current, prepared.tag, position)?;
                    let Cell::Accepted(child) = *self.cells.get(child).ok_or(Failure::Invalid)?
                        else { return Err(Failure::Invalid); };
                    proved &= child.writer_class == Some(true);
                }
                proved
            };
            charge(budget, 1)?;
            self.cells[current] = Cell::Accepted(Prepared { writer_class: Some(proved), ..prepared });
        }
        let Cell::Accepted(prepared) = self.cells[expression] else { return Err(Failure::Invalid); };
        Ok((prepared.writer_class == Some(true)).then_some(match prepared.shape {
            LocalShape::Empty => ProjectionClass::Empty,
            LocalShape::Metadata => ProjectionClass::Metadata,
            LocalShape::Callable(code) => ProjectionClass::Callable(code),
        }))
    }

    // The immutable final Graph includes imported producers and every source
    // writer/capture role. The payload permits same-expression capture feeds;
    // the complete owner must retain them independently from its LOCAL recipe.
    // Assignment, handler/provider, dictionary and other direct writers decline.
    // This does not exclude indirect topology installation or G writes at Call
    // contexts, and supplies no no-materialization/admission certificate.
    // Evidence topology descends through a typed Call with lexical=false; any
    // dictionary replacement of q would be indexed as DICTIONARY and decline.
    // Literal G remains uncaptured; the complete family qualifier separately
    // proves its unique body association.
    pub(super) fn direct_evidence_payload(
        &mut self, evidence: usize, budget: &mut TypeWorkBudget,
    ) -> Result<Option<DirectPayload>, Failure> {
        charge(budget, 1)?;
        let Some(Expr::Evidence { value: payload, .. }) = self.graph.expressions.get(evidence)
            else { return Ok(None); };
        let payload = *payload;
        if !self.compile_one(payload, budget)? { return Ok(None); }
        let prepared = self.prepared(payload).ok_or(Failure::Invalid)?;
        let RecipeTag::TypedCall { factory, body } = prepared.tag else { return Ok(None); };
        if !self.raw_local_recipe(payload, budget)? || !self.raw_returned_body(body, budget)? {
            return Ok(None);
        }
        Ok(Some(DirectPayload { payload, factory, body }))
    }

    pub(super) fn dictionary_binding(&self, source: DictionarySource)
        -> Option<&'g (crate::interface::RequirementId, crate::interface::MethodId, usize)>
    {
        let Expr::Evidence { bindings, .. } = self.graph.expressions.get(source.evidence_expression)? else { return None; };
        bindings.get(source.binding_ordinal)
    }
}
