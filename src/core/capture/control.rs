//! Finite control positions and continuation occurrences for capture checking.
//!
//! An address contains a static frame site, an active/capture/completion region,
//! a finite allocation context, and a recent/older distinction. It never contains a residual, stack,
//! or request-history identity. Older occurrences join edges; the recent address
//! denotes one occurrence and permits consumption to move that occurrence.
//! Live and consumed clauses have separate sites. Ordinary frames save control
//! positions and type contexts, never a saved copy of an owner's usage state.
//!
//! Selection copies only paths through the nearest matching handler and cuts
//! their boundary at End. Restoration replaces End with the remaining clause
//! continuation. Capture edges retain that cut when older snapshots join.
//! Type contexts map formal variables to original type subtrees or an unproved
//! replacement; unproved arguments widen matching only within one effect ID.
//! These finite domains bound the possible edges and state graphs. The visited
//! set computes closure without a depth cutoff; exhausted work never succeeds.

use std::{
    collections::{HashMap, HashSet, VecDeque},
    hash::{DefaultHasher, Hasher},
    sync::Arc,
};

use super::{
    CompletionOwner, Failure, Request, SummaryGraph, TypeArguments, UnsafeDiscard, Value, charge,
    same_effect,
};
use crate::{
    source::Span,
    types::{
        EffectInstance, EffectRow, EffectRowVariable, KindedArgument, Type, TypeVariableId,
        TypeWorkBudget, clone_effect_row_with_budget, clone_type_with_budget,
        hash_type_with_budget, rebuild_effect_row_with_budget, same_type_with_budget,
        substitute_type_and_row_variables_borrowed_with,
    },
};

/// Potential coincidence differs from equality: a rigid row formal may be
/// instantiated at a call site. Closed rows preserve their defining families;
/// ordinary exact equality is checked before this conservative relation.
fn extend_possible_owner_pairs<'a>(
    left: &'a [KindedArgument],
    right: &'a [KindedArgument],
    pending_types: &mut Vec<(&'a Type, &'a Type)>,
    budget: &mut TypeWorkBudget,
) -> Result<bool, Failure> {
    charge(budget, left.len() + right.len())?;
    if left.len() != right.len() {
        return Ok(false);
    }
    let mut pending = Vec::new();
    pending
        .try_reserve(left.len())
        .map_err(|_| Failure::Resource)?;
    pending.extend(left.iter().zip(right));
    while let Some((left, right)) = pending.pop() {
        charge(budget, 1)?;
        match (left, right) {
            (KindedArgument::TypeArg(left), KindedArgument::TypeArg(right)) => {
                pending_types
                    .try_reserve(1)
                    .map_err(|_| Failure::Resource)?;
                pending_types.push((left, right));
            }
            (KindedArgument::RowArg(left), KindedArgument::RowArg(right)) => {
                // Neither an open prefix nor its lacks facts establish
                // inequality before complete callable substitution is known.
                if left.tail().is_some() || right.tail().is_some() {
                    continue;
                }
                // Closed-row defining effect IDs are stable under substitution.
                // Multiple instances of one family may coincide after type/row
                // substitution, so only a unique pair determines argument pairs.
                charge(budget, left.known().len() + right.known().len())?;
                for member in left.known() {
                    charge(budget, left.known().len() + right.known().len())?;
                    let left_count = left
                        .known()
                        .iter()
                        .filter(|candidate| candidate.effect() == member.effect())
                        .count();
                    let mut matches = right
                        .known()
                        .iter()
                        .filter(|candidate| candidate.effect() == member.effect());
                    let Some(other) = matches.next() else {
                        return Ok(false);
                    };
                    if left_count == 1 && matches.next().is_none() {
                        if member.arguments().len() != other.arguments().len() {
                            return Ok(false);
                        }
                        charge(budget, member.arguments().len())?;
                        pending
                            .try_reserve(member.arguments().len())
                            .map_err(|_| Failure::Resource)?;
                        pending.extend(member.arguments().iter().zip(other.arguments()));
                    }
                }
                for member in right.known() {
                    charge(budget, left.known().len())?;
                    if !left
                        .known()
                        .iter()
                        .any(|candidate| candidate.effect() == member.effect())
                    {
                        return Ok(false);
                    }
                }
            }
            _ => return Ok(false),
        }
    }
    Ok(true)
}

/// Retain explicit owner RowArg equations alongside ordinary type equations.
/// A closed actual prefix can identify a known member; an open actual row
/// cannot select one instance on the basis of its prefix alone.
fn extend_owner_context_pairs<'a>(
    formal: &'a [KindedArgument],
    actual: &'a [KindedArgument],
    pending_types: &mut Vec<(&'a Type, &'a Type)>,
    row_equations: &mut Vec<(&'a EffectRow, Option<&'a EffectRow>)>,
    budget: &mut TypeWorkBudget,
) -> Result<(), Failure> {
    charge(budget, formal.len() + actual.len())?;
    if formal.len() != actual.len() {
        return Ok(());
    }
    let mut pending = Vec::new();
    pending
        .try_reserve(formal.len())
        .map_err(|_| Failure::Resource)?;
    pending.extend(formal.iter().zip(actual));
    while let Some((formal, actual)) = pending.pop() {
        charge(budget, 1)?;
        match (formal, actual) {
            (KindedArgument::TypeArg(formal), KindedArgument::TypeArg(actual)) => {
                pending_types
                    .try_reserve(1)
                    .map_err(|_| Failure::Resource)?;
                pending_types.push((formal, actual));
            }
            (KindedArgument::RowArg(formal), KindedArgument::RowArg(actual)) => {
                if matches!(
                    formal.tail().map(|tail| tail.variable()),
                    Some(EffectRowVariable::Rigid(_))
                ) {
                    row_equations
                        .try_reserve(1)
                        .map_err(|_| Failure::Resource)?;
                    row_equations.push((formal, Some(actual)));
                }
                if actual.tail().is_some() {
                    continue;
                }
                charge(budget, formal.known().len())?;
                for effect in formal.known() {
                    charge(budget, actual.known().len())?;
                    let mut matches = actual
                        .known()
                        .iter()
                        .filter(|member| member.effect() == effect.effect());
                    if let Some(candidate) = matches.next()
                        && matches.next().is_none()
                        && effect.arguments().len() == candidate.arguments().len()
                    {
                        charge(budget, effect.arguments().len())?;
                        pending
                            .try_reserve(effect.arguments().len())
                            .map_err(|_| Failure::Resource)?;
                        pending.extend(effect.arguments().iter().zip(candidate.arguments()));
                    }
                }
            }
            _ => {}
        }
    }
    Ok(())
}

fn retain_owner_row_universe<'a>(
    arguments: &'a [KindedArgument],
    rows: &mut Vec<&'a EffectRow>,
    budget: &mut TypeWorkBudget,
) -> Result<(), Failure> {
    let mut pending = Vec::new();
    charge(budget, arguments.len())?;
    pending
        .try_reserve(arguments.len())
        .map_err(|_| Failure::Resource)?;
    pending.extend(arguments);
    while let Some(argument) = pending.pop() {
        charge(budget, 1)?;
        if let KindedArgument::RowArg(row) = argument {
            rows.try_reserve(1).map_err(|_| Failure::Resource)?;
            rows.push(row);
            charge(
                budget,
                row.known().len() + row.tail().map_or(0, |tail| tail.lacks().len()),
            )?;
            for member in row
                .known()
                .iter()
                .chain(row.tail().into_iter().flat_map(|tail| tail.lacks()))
            {
                charge(budget, member.arguments().len())?;
                pending
                    .try_reserve(member.arguments().len())
                    .map_err(|_| Failure::Resource)?;
                pending.extend(member.arguments());
            }
        }
    }
    Ok(())
}

#[derive(Debug)]
pub(super) enum Control {
    NativeInterpret {
        body: usize,
        effects: Vec<Request>,
    },
    Cleanup {
        body: usize,
        action: usize,
        row_type: usize,
        source: Span,
    },
    Registration {
        body: usize,
        source: Span,
    },
    Return,
    /// Forbidden control retained only in a private provider query graph.
    /// It remains a refusal whenever the actual selected callable reaches it.
    Unavailable,
    Sequence(Vec<usize>),
    Choice(Vec<usize>),
    Call {
        value: Value,
        ty: usize,
        source: Span,
        prefix: Option<Request>,
    },
    Request(Request),
    Handler {
        body: usize,
        effect: Request,
        clauses: Vec<Clause>,
    },
    Resource {
        body: usize,
        effect: Request,
    },
    /// The Store operand has already been evaluated before this boundary.
    RetainedRoot {
        body: usize,
        store: usize,
    },
    Retain {
        owner: usize,
    },
    /// Both operands have already been evaluated; adapter branches are delayed.
    Continue {
        store: usize,
        key: usize,
        some: usize,
        none: usize,
    },
    Resume {
        owner: usize,
        value: usize,
    },
    Discard {
        owner: usize,
        node: usize,
        local: bool,
        row_type: usize,
        source: Span,
    },
}

#[derive(Clone, Copy, Debug)]
pub(super) struct Clause {
    pub(super) operation: Option<crate::types::OperationId>,
    pub(super) body: usize,
    pub(super) owner: usize,
    pub(super) source: Span,
}

impl Control {
    pub(super) fn requests(&self) -> impl Iterator<Item = &Request> {
        let single = match self {
            Self::Call {
                prefix: Some(request),
                ..
            }
            | Self::Request(request)
            | Self::Handler {
                effect: request, ..
            }
            | Self::Resource {
                effect: request, ..
            } => Some(request),
            _ => None,
        };
        let multiple: &[Request] = match self {
            Self::NativeInterpret { effects, .. } => effects,
            _ => &[],
        };
        single.into_iter().chain(multiple.iter())
    }

    fn children(
        &self,
        graph: &SummaryGraph,
        pending: &mut Vec<usize>,
        budget: &mut TypeWorkBudget,
    ) -> Result<(), Failure> {
        match self {
            Self::Cleanup { body, action, .. } => {
                charge(budget, 2)?;
                pending.try_reserve(2).map_err(|_| Failure::Resource)?;
                pending.extend([*body, *action]);
            }
            Self::Continue {
                store,
                key,
                some,
                none,
            } => {
                charge(budget, 4)?;
                pending.try_reserve(4).map_err(|_| Failure::Resource)?;
                pending.extend([*store, *key, *some, *none]);
            }
            Self::Sequence(children) | Self::Choice(children) => {
                charge(budget, children.len())?;
                pending
                    .try_reserve(children.len())
                    .map_err(|_| Failure::Resource)?;
                pending.extend(children);
            }
            Self::Call { value, .. } => {
                charge(budget, value.targets.len())?;
                pending
                    .try_reserve(value.targets.len())
                    .map_err(|_| Failure::Resource)?;
                for target in &value.targets {
                    pending.push(graph.callables.get(*target, budget)?.body);
                }
            }
            Self::Handler { body, clauses, .. } => {
                charge(budget, clauses.len() + 1)?;
                pending
                    .try_reserve(clauses.len() + 1)
                    .map_err(|_| Failure::Resource)?;
                pending.push(*body);
                pending.extend(clauses.iter().map(|clause| clause.body));
            }
            Self::NativeInterpret { body: value, .. }
            | Self::Resume { value, .. }
            | Self::Resource { body: value, .. }
            | Self::RetainedRoot { body: value, .. }
            | Self::Registration { body: value, .. } => {
                pending.try_reserve(1).map_err(|_| Failure::Resource)?;
                pending.push(*value);
            }
            _ => {}
        }
        Ok(())
    }
    pub(super) fn copy(
        &self,
        code_offset: usize,
        target_offset: usize,
        type_offset: usize,
        budget: &mut TypeWorkBudget,
    ) -> Result<Self, Failure> {
        charge(budget, 1)?;
        Ok(match self {
            Self::Cleanup {
                body,
                action,
                row_type,
                source,
            } => Self::Cleanup {
                body: body + code_offset,
                action: action + code_offset,
                row_type: row_type + type_offset,
                source: *source,
            },
            Self::Registration { body, source } => Self::Registration {
                body: body + code_offset,
                source: *source,
            },
            Self::NativeInterpret { body, effects } => {
                charge(budget, effects.len())?;
                let mut copied = Vec::new();
                copied
                    .try_reserve_exact(effects.len())
                    .map_err(|_| Failure::Resource)?;
                for effect in effects {
                    copied.push(effect.copy(budget)?);
                }
                Self::NativeInterpret {
                    body: body + code_offset,
                    effects: copied,
                }
            }
            Self::Return => Self::Return,
            Self::Unavailable => Self::Unavailable,
            Self::Sequence(children) | Self::Choice(children) => {
                let mut copy = copy_slice(children, budget)?;
                for child in &mut copy {
                    *child += code_offset;
                }
                if matches!(self, Self::Sequence(_)) {
                    Self::Sequence(copy)
                } else {
                    Self::Choice(copy)
                }
            }
            Self::Call {
                value,
                ty,
                source,
                prefix,
            } => {
                let mut value = value.copy(budget)?;
                value.relocate(target_offset, budget)?;
                Self::Call {
                    value,
                    ty: ty + type_offset,
                    source: *source,
                    prefix: prefix
                        .as_ref()
                        .map(|request| request.copy(budget))
                        .transpose()?,
                }
            }
            Self::Request(request) => Self::Request(request.copy(budget)?),
            Self::Resource { body, effect } => Self::Resource {
                body: body + code_offset,
                effect: effect.copy(budget)?,
            },
            Self::RetainedRoot { body, store } => Self::RetainedRoot {
                body: body + code_offset,
                store: store + code_offset,
            },
            Self::Retain { owner } => Self::Retain {
                owner: owner + code_offset,
            },
            Self::Continue {
                store,
                key,
                some,
                none,
            } => Self::Continue {
                store: store + code_offset,
                key: key + code_offset,
                some: some + code_offset,
                none: none + code_offset,
            },
            Self::Handler {
                body,
                effect,
                clauses,
            } => {
                let mut clauses = copy_slice(clauses, budget)?;
                for clause in &mut clauses {
                    clause.body += code_offset;
                    clause.owner += code_offset;
                }
                Self::Handler {
                    body: body + code_offset,
                    effect: effect.copy(budget)?,
                    clauses,
                }
            }
            Self::Resume { owner, value } => Self::Resume {
                owner: owner + code_offset,
                value: value + code_offset,
            },
            Self::Discard {
                owner,
                node,
                source,
                row_type,
                ..
            } => Self::Discard {
                owner: owner + code_offset,
                node: *node,
                local: false,
                row_type: row_type + type_offset,
                source: *source,
            },
        })
    }
}

pub(super) fn query_required(
    graph: &SummaryGraph,
    root: usize,
    budget: &mut TypeWorkBudget,
) -> Result<bool, Failure> {
    let mut pending = Vec::new();
    let mut seen = HashSet::new();
    pending.try_reserve(1).map_err(|_| Failure::Resource)?;
    pending.push(root);
    while let Some(code) = pending.pop() {
        charge(budget, 1)?;
        if seen.contains(&code) {
            continue;
        }
        seen.try_reserve(1).map_err(|_| Failure::Resource)?;
        seen.insert(code);
        if matches!(
            graph.code[code],
            Control::Discard { .. }
                | Control::Resource { .. }
                | Control::RetainedRoot { .. }
                | Control::Retain { .. }
                | Control::Continue { .. }
                | Control::Registration { .. }
                | Control::Cleanup { .. }
        ) {
            return Ok(true);
        }
        // A saved allocation context can feed a published global callable even
        // when the initializer contains no local resource boundary.
        if let Control::Request(request) = &graph.code[code]
            && let Some(operation) = request.operation
            && let Some(api) = crate::resolved::RegionApi::for_module(operation.owner().module())
            && operation == crate::types::OperationId::new(api.default_alloc(), 1)
            && request.opaque_row.is_none()
            && request.effect.as_ref().is_some_and(|effect| {
                effect.effect() == api.default_alloc() && effect.arguments().is_empty()
            })
        {
            return Ok(true);
        }
        graph.code[code].children(graph, &mut pending, budget)?;
    }
    Ok(false)
}

pub(super) fn copy_slice<T: Copy>(
    source: &[T],
    budget: &mut TypeWorkBudget,
) -> Result<Vec<T>, Failure> {
    charge(budget, source.len() + 1)?;
    let mut result = Vec::new();
    result
        .try_reserve_exact(source.len())
        .map_err(|_| Failure::Resource)?;
    result.extend_from_slice(source);
    Ok(result)
}

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct Position {
    code: usize,
    next: usize,
}

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum Site {
    Closing(usize, bool),
    RemovedHandler(usize),
    Cleanup(usize, bool),
    Registration(usize),
    NativeInterpret(usize),
    Next(Position),
    Handler(usize),
    Resource(usize),
    RetainedRoot(usize),
    Clause(usize, bool),
}

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum Region {
    Active,
    Capture(usize, usize),
    Completion(usize, usize),
    Closing(usize, usize),
}

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum Address {
    Empty,
    End,
    Slot {
        region: Region,
        site: Site,
        // Saved execution contexts can change on restoration. Allocation
        // provenance cannot: copying preserves this existing finite value ID.
        allocation_context: usize,
        old: bool,
    },
}

impl Address {
    fn older(self) -> Self {
        match self {
            Self::Slot {
                region,
                site,
                allocation_context,
                ..
            } => Self::Slot {
                region,
                site,
                allocation_context,
                old: true,
            },
            _ => self,
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct Event {
    code: usize,
    label: usize,
    unknown: bool,
    port: Option<usize>,
}

/// The owner occurrence uses the existing finite value-context domain.
/// An equal native effect never substitutes for this exact enclosing frame.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct ProviderResourceOccurrence {
    code: usize,
    value_context: usize,
}

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum Frame {
    NativeInterpret {
        code: usize,
        context: usize,
        value_context: usize,
    },
    Closing {
        code: usize,
        site: Site,
        context: usize,
        value_context: usize,
        capture: Option<Address>,
        event: Event,
    },
    RemovedHandler {
        code: usize,
        context: usize,
        value_context: usize,
    },
    Cleanup {
        code: usize,
        context: usize,
        value_context: usize,
        running: bool,
        closing: Option<usize>,
    },
    Registration {
        code: usize,
        context: usize,
        value_context: usize,
    },
    Next {
        position: Position,
        context: usize,
        value_context: usize,
    },
    Handler {
        code: usize,
        context: usize,
        value_context: usize,
        capture_context: usize,
    },
    Resource {
        code: usize,
        context: usize,
        value_context: usize,
        focused: bool,
    },
    RetainedRoot {
        code: usize,
        context: usize,
        value_context: usize,
        store: Address,
        baseline: Address,
    },
    Clause {
        handler: usize,
        ordinal: usize,
        owner: usize,
        context: usize,
        value_context: usize,
        capture: Address,
        capture_context: usize,
        clause_context: usize,
        event: Event,
        consumed: bool,
    },
}

impl Frame {
    fn allocation_context(self) -> usize {
        match self {
            Self::Next { value_context, .. }
            | Self::Closing { value_context, .. }
            | Self::RemovedHandler { value_context, .. }
            | Self::Cleanup { value_context, .. }
            | Self::NativeInterpret { value_context, .. }
            | Self::Registration { value_context, .. }
            | Self::Handler { value_context, .. }
            | Self::Resource { value_context, .. }
            | Self::RetainedRoot { value_context, .. } => value_context,
            Self::Clause { clause_context, .. } => clause_context,
        }
    }

    fn site(self) -> Site {
        match self {
            Self::Closing { site, .. } => site,
            Self::RemovedHandler { code, .. } => Site::RemovedHandler(code),
            Self::Cleanup { code, running, .. } => Site::Cleanup(code, running),
            Self::Next { position, .. } => Site::Next(position),
            Self::Registration { code, .. } => Site::Registration(code),
            Self::NativeInterpret { code, .. } => Site::NativeInterpret(code),
            Self::Handler { code, .. } => Site::Handler(code),
            Self::Resource { code, .. } => Site::Resource(code),
            Self::RetainedRoot { code, .. } => Site::RetainedRoot(code),
            Self::Clause {
                owner, consumed, ..
            } => Site::Clause(owner, consumed),
        }
    }
    fn remap(&mut self, map: &HashMap<Address, Address>) {
        if let Self::Clause { capture, .. } = self {
            *capture = map.get(capture).copied().unwrap_or(*capture);
        }
        if let Self::Closing {
            capture: Some(capture),
            ..
        } = self
        {
            *capture = map.get(capture).copied().unwrap_or(*capture);
        }
        if let Self::RetainedRoot {
            store, baseline, ..
        } = self
        {
            *store = map.get(store).copied().unwrap_or(*store);
            *baseline = map.get(baseline).copied().unwrap_or(*baseline);
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct Edge {
    address: Address,
    frame: Frame,
    next: Address,
}

/// A Store owns this capture; the locator and interpreter baseline do not.
/// A spent entry preserves the bounded allocation coordinate for stale keys.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct RetainedCapture {
    store: Address,
    key: (usize, usize),
    capture: Option<Address>,
    baseline: Address,
    root: usize,
    root_context: usize,
    root_value_context: usize,
    handler: usize,
    handler_context: usize,
    event: Event,
}

// A Store in an owned cut also owns every live capture in its slots. Locator
// values and spent entries do not themselves add continuation edges.
fn push_store_captures(
    state: &State,
    store: Address,
    pending: &mut Vec<Address>,
    budget: &mut TypeWorkBudget,
) -> Result<(), Failure> {
    for retained in &state.retained {
        charge(budget, 1)?;
        if retained.store == store
            && let Some(capture) = retained.capture
        {
            charge(budget, 1)?;
            pending.try_reserve(1).map_err(|_| Failure::Resource)?;
            pending.push(capture);
        }
    }
    Ok(())
}

/// Current roots are immutable value ports. A later replacement changes only
/// this control state's root; earlier read ports keep their original edge.
#[derive(Debug, Eq, Hash, PartialEq)]
struct CellContents {
    occurrence: ProviderResourceOccurrence,
    owner: (usize, usize),
    roots: Vec<usize>,
    enclosing: Arc<[(usize, usize)]>,
    predecessors: Arc<[usize]>,
    shared: bool,
}

impl CellContents {
    fn copy(&self, budget: &mut TypeWorkBudget) -> Result<Self, Failure> {
        charge(budget, 2)?;
        Ok(Self {
            occurrence: self.occurrence,
            owner: self.owner,
            roots: copy_slice(&self.roots, budget)?,
            enclosing: Arc::clone(&self.enclosing),
            predecessors: Arc::clone(&self.predecessors),
            shared: self.shared,
        })
    }
    fn intersect_birth(
        &mut self,
        enclosing: &[(usize, usize)],
        predecessors: &[usize],
        budget: &mut TypeWorkBudget,
    ) -> Result<(), Failure> {
        charge(
            budget,
            self.enclosing
                .len()
                .checked_mul(enclosing.len())
                .ok_or(Failure::Resource)?,
        )?;
        charge(
            budget,
            self.predecessors
                .len()
                .checked_mul(predecessors.len())
                .ok_or(Failure::Resource)?,
        )?;
        let same_enclosing = self.enclosing.iter().all(|owner| enclosing.contains(owner));
        let same_predecessors = self
            .predecessors
            .iter()
            .all(|port| predecessors.contains(port));
        if same_enclosing && same_predecessors {
            return Ok(());
        }
        // Construct both immutable replacements before changing this state.
        // Other copied states retain their original acquisition relation.
        charge(budget, 2)?;
        let enclosing = if same_enclosing {
            Arc::clone(&self.enclosing)
        } else {
            let mut retained = copy_slice(&self.enclosing, budget)?;
            charge(
                budget,
                retained
                    .len()
                    .checked_mul(enclosing.len())
                    .ok_or(Failure::Resource)?,
            )?;
            retained.retain(|owner| enclosing.contains(owner));
            share_cell_birth_slice(retained, budget)?
        };
        let predecessors = if same_predecessors {
            Arc::clone(&self.predecessors)
        } else {
            let mut retained = copy_slice(&self.predecessors, budget)?;
            charge(
                budget,
                retained
                    .len()
                    .checked_mul(predecessors.len())
                    .ok_or(Failure::Resource)?,
            )?;
            retained.retain(|port| predecessors.contains(port));
            share_cell_birth_slice(retained, budget)?
        };
        self.enclosing = enclosing;
        self.predecessors = predecessors;
        Ok(())
    }

    fn insert_root(&mut self, root: usize, budget: &mut TypeWorkBudget) -> Result<(), Failure> {
        charge(budget, self.roots.len() + 1)?;
        if let Err(position) = self.roots.binary_search(&root) {
            self.roots.try_reserve(1).map_err(|_| Failure::Resource)?;
            self.roots.insert(position, root);
        }
        Ok(())
    }
}

/// Birth metadata contains only flat Copy coordinates. Converting the owned
/// vector into shared immutable storage pays its allocation/copy before use.
fn share_cell_birth_slice<T: Copy>(
    values: Vec<T>,
    budget: &mut TypeWorkBudget,
) -> Result<Arc<[T]>, Failure> {
    charge(
        budget,
        values.len().checked_add(1).ok_or(Failure::Resource)?,
    )?;
    Ok(Arc::from(values))
}

#[derive(Debug, Eq, Hash, PartialEq)]
struct State {
    position: Position,
    context: usize,
    value_context: usize,
    stack: Address,
    heap: Vec<Edge>,
    retained: Vec<RetainedCapture>,
    cells: Vec<CellContents>,
    abandoned: Option<(usize, Event)>,
}

impl State {
    fn charge_cells(&self, budget: &mut TypeWorkBudget) -> Result<(), Failure> {
        charge(budget, self.cells.len())?;
        for cell in &self.cells {
            let units = cell
                .enclosing
                .len()
                .checked_mul(2)
                .and_then(|units| units.checked_add(cell.roots.len()))
                .and_then(|units| units.checked_add(cell.predecessors.len()))
                .and_then(|units| units.checked_add(4))
                .ok_or(Failure::Resource)?;
            charge(budget, units)?;
        }
        Ok(())
    }

    /// Every State-keyed lookup/insertion visits the complete structural key,
    /// including hits which perform no copying or new state retention.
    fn charge_key(&self, budget: &mut TypeWorkBudget) -> Result<(), Failure> {
        charge(
            budget,
            self.heap.len().checked_add(1).ok_or(Failure::Resource)?,
        )?;
        charge(budget, self.retained.len())?;
        self.charge_cells(budget)
    }

    fn edges(&self, address: Address, budget: &mut TypeWorkBudget) -> Result<&[Edge], Failure> {
        charge(budget, self.heap.len().max(1).ilog2() as usize + 1)?;
        let start = self.heap.partition_point(|edge| edge.address < address);
        let mut count = 0;
        for edge in &self.heap[start..] {
            charge(budget, 1)?;
            if edge.address != address {
                break;
            }
            count += 1;
        }
        charge(budget, count)?;
        Ok(&self.heap[start..start + count])
    }
    fn copy(&self, budget: &mut TypeWorkBudget) -> Result<Self, Failure> {
        charge(budget, self.cells.len())?;
        let mut cells = Vec::new();
        cells
            .try_reserve(self.cells.len())
            .map_err(|_| Failure::Resource)?;
        for cell in &self.cells {
            cells.push(cell.copy(budget)?);
        }
        Ok(Self {
            position: self.position,
            context: self.context,
            value_context: self.value_context,
            stack: self.stack,
            heap: copy_slice(&self.heap, budget)?,
            retained: copy_slice(&self.retained, budget)?,
            cells,
            abandoned: self.abandoned,
        })
    }

    fn rename(
        &mut self,
        map: &HashMap<Address, Address>,
        budget: &mut TypeWorkBudget,
    ) -> Result<(), Failure> {
        charge(budget, self.heap.len() + self.retained.len() + 1)?;
        self.stack = map.get(&self.stack).copied().unwrap_or(self.stack);
        for edge in &mut self.heap {
            edge.address = map.get(&edge.address).copied().unwrap_or(edge.address);
            edge.next = map.get(&edge.next).copied().unwrap_or(edge.next);
            edge.frame.remap(map);
        }
        for retained in &mut self.retained {
            retained.store = map.get(&retained.store).copied().unwrap_or(retained.store);
            retained.baseline = map
                .get(&retained.baseline)
                .copied()
                .unwrap_or(retained.baseline);
            if let Some(capture) = &mut retained.capture {
                *capture = map.get(capture).copied().unwrap_or(*capture);
            }
        }
        Ok(())
    }

    fn push(&mut self, mut frame: Frame, budget: &mut TypeWorkBudget) -> Result<(), Failure> {
        let address = Address::Slot {
            region: Region::Active,
            site: frame.site(),
            allocation_context: frame.allocation_context(),
            old: false,
        };
        let mut renaming = HashMap::new();
        renaming.try_reserve(1).map_err(|_| Failure::Resource)?;
        renaming.insert(address, address.older());
        self.rename(&renaming, budget)?;
        frame.remap(&renaming);
        self.heap.try_reserve(1).map_err(|_| Failure::Resource)?;
        self.heap.push(Edge {
            address,
            frame,
            next: self.stack,
        });
        self.stack = address;
        Ok(())
    }

    // Copy a selected stack graph, including its boundary. The boundary tail
    // is replaced atomically; no captured graph edge points past that port.
    fn copy_segment(
        &mut self,
        root: Address,
        edges: &[Edge],
        boundary: Option<Edge>,
        tail: Address,
        region: Region,
        budget: &mut TypeWorkBudget,
    ) -> Result<Address, Failure> {
        charge(budget, edges.len())?;
        let mut destinations = HashMap::new();
        let mut renaming = HashMap::new();
        let mut origins = HashMap::new();
        origins
            .try_reserve(edges.len())
            .map_err(|_| Failure::Resource)?;
        destinations
            .try_reserve(edges.len())
            .map_err(|_| Failure::Resource)?;
        renaming
            .try_reserve(edges.len())
            .map_err(|_| Failure::Resource)?;
        for edge in edges {
            let Address::Slot {
                old,
                allocation_context,
                ..
            } = edge.address
            else {
                return Err(Failure::Invalid);
            };
            let address = Address::Slot {
                region,
                site: edge.frame.site(),
                allocation_context,
                old,
            };
            destinations.insert(edge.address, address);
            if !old {
                charge(budget, 1)?;
                let source = origins.entry(address).or_insert(Some(edge.address));
                if *source != Some(edge.address) {
                    *source = None;
                }
                renaming.insert(address, address.older());
            }
        }
        // Distinct source regions can collapse to the same copy region. Such
        // a destination summarizes occurrences; it cannot authorize a recent
        // singleton's strong completion update.
        for address in destinations.values_mut() {
            charge(budget, 1)?;
            if origins.get(address) == Some(&None) {
                *address = address.older();
            }
        }
        // Moving an enclosing Store also moves its slot table. Record exact
        // copied owners before destination aging; references to owners outside
        // this segment remain non-owning and are handled by ordinary renaming.
        let mut moved_stores = Vec::new();
        charge(budget, self.retained.len())?;
        for (index, retained) in self.retained.iter().enumerate() {
            let Some(&store) = destinations.get(&retained.store) else {
                continue;
            };
            if !matches!(retained.store, Address::Slot { old: false, .. })
                || !matches!(store, Address::Slot { old: false, .. })
            {
                return Err(Failure::Invalid);
            }
            moved_stores.try_reserve(1).map_err(|_| Failure::Resource)?;
            moved_stores.push((index, store, destinations.get(&retained.baseline).copied()));
        }
        self.rename(&renaming, budget)?;
        for (index, store, baseline) in moved_stores {
            self.retained[index].store = store;
            if let Some(baseline) = baseline {
                self.retained[index].baseline = baseline;
            }
        }
        let tail = renaming.get(&tail).copied().unwrap_or(tail);
        self.heap
            .try_reserve(edges.len())
            .map_err(|_| Failure::Resource)?;
        charge(budget, edges.len())?;
        for edge in edges {
            let mut frame = edge.frame;
            frame.remap(&renaming);
            if let (
                Frame::RetainedRoot {
                    store: original_store,
                    baseline: original_baseline,
                    ..
                },
                Frame::RetainedRoot {
                    store, baseline, ..
                },
            ) = (edge.frame, &mut frame)
            {
                if let Some(&copied) = destinations.get(&original_store) {
                    *store = copied;
                }
                if let Some(&copied) = destinations.get(&original_baseline) {
                    *baseline = copied;
                }
            }
            let next = if boundary == Some(*edge) || edge.next == Address::End {
                tail
            } else {
                *destinations.get(&edge.next).ok_or(Failure::Invalid)?
            };
            self.heap.push(Edge {
                address: destinations[&edge.address],
                frame,
                next,
            });
        }
        if root == Address::End {
            Ok(tail)
        } else {
            destinations.get(&root).copied().ok_or(Failure::Invalid)
        }
    }

    fn normalize(&mut self, budget: &mut TypeWorkBudget) -> Result<(), Failure> {
        charge(
            budget,
            self.heap
                .len()
                .saturating_mul(self.heap.len().max(1).ilog2() as usize + 1),
        )?;
        self.heap.sort_unstable();
        self.heap.dedup();
        charge(
            budget,
            self.retained
                .len()
                .saturating_mul(self.retained.len().max(1).ilog2() as usize + 1),
        )?;
        self.retained.sort_unstable();
        self.retained.dedup();
        self.prune_sorted_heap(budget)
    }

    fn prune_sorted_heap(&mut self, budget: &mut TypeWorkBudget) -> Result<(), Failure> {
        charge(budget, self.heap.len())?;
        let mut ranges: HashMap<Address, (usize, usize)> = HashMap::new();
        ranges
            .try_reserve(self.heap.len())
            .map_err(|_| Failure::Resource)?;
        for (index, edge) in self.heap.iter().enumerate() {
            ranges.entry(edge.address).or_insert((index, index)).1 = index + 1;
        }
        let mut reachable = HashSet::new();
        let mut pending = Vec::new();
        charge(budget, self.retained.len())?;
        pending
            .try_reserve(self.retained.len() + 1)
            .map_err(|_| Failure::Resource)?;
        pending.push(self.stack);
        pending.extend(self.retained.iter().filter_map(|entry| entry.capture));
        while let Some(address) = pending.pop() {
            charge(budget, 1)?;
            if matches!(address, Address::Empty | Address::End) || reachable.contains(&address) {
                continue;
            }
            reachable.try_reserve(1).map_err(|_| Failure::Resource)?;
            reachable.insert(address);
            charge(budget, 1)?;
            let (start, end) = ranges.get(&address).copied().unwrap_or((0, 0));
            charge(budget, end - start)?;
            for edge in &self.heap[start..end] {
                pending.try_reserve(2).map_err(|_| Failure::Resource)?;
                pending.push(edge.next);
                if let Frame::Clause {
                    capture,
                    consumed: false,
                    ..
                }
                | Frame::Closing {
                    capture: Some(capture),
                    ..
                } = edge.frame
                {
                    pending.push(capture);
                }
            }
        }
        charge(budget, self.heap.len())?;
        self.heap.retain(|edge| reachable.contains(&edge.address));
        Ok(())
    }

    fn prune_after_pop(
        &mut self,
        root: Address,
        budget: &mut TypeWorkBudget,
    ) -> Result<(), Failure> {
        if !self.retained.is_empty() {
            return self.prune_sorted_heap(budget);
        }
        let edges = self.edges(root, budget)?;
        if edges.len() != 1
            || edges[0].next != self.stack
            || matches!(
                edges[0].frame,
                Frame::Clause {
                    consumed: false,
                    ..
                } | Frame::Closing {
                    capture: Some(_),
                    ..
                }
            )
        {
            return self.prune_sorted_heap(budget);
        }
        // In a normalized graph this sole outgoing edge reached every other
        // vertex through its tail. Only the popped root can become unreachable.
        for edge in &self.heap {
            charge(budget, 1)?;
            if edge.next == root
                || matches!(edge.frame, Frame::Clause { capture, consumed: false, .. } if capture == root)
                || matches!(edge.frame, Frame::Closing { capture: Some(capture), .. } if capture == root)
            {
                return Ok(());
            }
        }
        charge(budget, self.heap.len())?;
        self.heap.retain(|edge| edge.address != root);
        Ok(())
    }
}

struct Selection {
    boundary: Edge,
    prefix: Vec<Edge>,
}

#[derive(Clone, Copy)]
enum Completion {
    Resume,
    Discard,
    Retain,
}

enum StoreBoundary {
    Found(Edge),
    Pending,
    Symbolic,
}

// `select` returns (can_select, can_cross). Preserve the forward boundary
// order separately from the backward prefix reconstruction used by captures.
fn selection_boundaries(
    state: &State,
    root: Address,
    mut select: impl FnMut(Frame) -> Result<(bool, bool), Failure>,
    budget: &mut TypeWorkBudget,
) -> Result<(Vec<Edge>, Vec<Edge>, bool), Failure> {
    let mut pending = Vec::new();
    pending.try_reserve(1).map_err(|_| Failure::Resource)?;
    pending.push(root);
    let mut visited = HashSet::new();
    let mut prefixes = Vec::new();
    let mut boundaries = Vec::new();
    let mut escaped = false;
    while let Some(address) = pending.pop() {
        charge(budget, 1)?;
        if matches!(address, Address::Empty | Address::End) {
            escaped = true;
            continue;
        }
        if visited.contains(&address) {
            continue;
        }
        visited.try_reserve(1).map_err(|_| Failure::Resource)?;
        visited.insert(address);
        for edge in state.edges(address, budget)? {
            let (selected, crossed) = select(edge.frame)?;
            if selected {
                boundaries.try_reserve(1).map_err(|_| Failure::Resource)?;
                boundaries.push(*edge);
            }
            if crossed {
                prefixes.try_reserve(1).map_err(|_| Failure::Resource)?;
                prefixes.push(*edge);
                pending.try_reserve(1).map_err(|_| Failure::Resource)?;
                pending.push(edge.next);
            }
        }
    }
    Ok((boundaries, prefixes, escaped))
}

fn selections(
    state: &State,
    root: Address,
    select: impl FnMut(Frame) -> Result<(bool, bool), Failure>,
    budget: &mut TypeWorkBudget,
) -> Result<(Vec<Selection>, bool), Failure> {
    let (boundaries, prefixes, escaped) = selection_boundaries(state, root, select, budget)?;
    let mut result = Vec::new();
    for boundary in boundaries {
        let mut reaches = HashSet::new();
        reaches.try_reserve(1).map_err(|_| Failure::Resource)?;
        reaches.insert(boundary.address);
        loop {
            let mut changed = false;
            for edge in &prefixes {
                charge(budget, 1)?;
                if reaches.contains(&edge.next) && !reaches.contains(&edge.address) {
                    reaches.try_reserve(1).map_err(|_| Failure::Resource)?;
                    reaches.insert(edge.address);
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }
        let mut prefix = Vec::new();
        charge(budget, prefixes.len() + 1)?;
        prefix
            .try_reserve(prefixes.len() + 1)
            .map_err(|_| Failure::Resource)?;
        for edge in &prefixes {
            if reaches.contains(&edge.next) {
                prefix.push(*edge);
            }
        }
        prefix.push(boundary);
        result.try_reserve(1).map_err(|_| Failure::Resource)?;
        result.push(Selection { boundary, prefix });
    }
    Ok((result, escaped))
}

#[derive(Debug, Eq, Hash, PartialEq)]
struct Context {
    // Each replacement names an original type subtree; MAX is unproved.
    // There are no recursively extended substitution-context identities.
    bindings: Vec<(TypeVariableId, usize)>,
    // Exact row keys stay distinct even when their callbacks share a caller.
    rows: Vec<RowBinding>,
}

// Consumed only after the original formal-prefix removal has completed.
// Unproved deliberately lends no residual row to the membership consumer.
enum RowEquation<'r> {
    Unproved,
    Residual(&'r EffectRow),
}

#[derive(Debug, Eq, Hash, PartialEq)]
struct RowBinding {
    variable: TypeVariableId,
    // Labels use only arguments in the same original type-subtree universe.
    known: Vec<usize>,
    tail: Option<EffectRowVariable>,
    lacks: Vec<usize>,
    // Conflicting equations never establish an empty or exact replacement.
    unproved: bool,
}

// Call observations outlive one dispatch, but their construction frame does not.
struct ObservedCall {
    state: State,
    delivered: Option<super::value::DeliveredCallPrefix>,
}

#[derive(Clone, Copy)]
struct CellRetentionSite {
    target: (usize, usize),
    request: Option<usize>,
    root: usize,
    source: Span,
    acquisition: Span,
}

struct CellRetention {
    target: (usize, usize),
    request: Option<usize>,
    root: usize,
    enclosing: Vec<(usize, usize)>,
    predecessors: Vec<usize>,
    source: Span,
    acquisition: Span,
}

struct RetainedSupport {
    target: (usize, usize),
    store_owner: bool,
    inputs: super::value::SavedInputs,
    source: Span,
    acquisition: Span,
}

pub(super) struct Analysis<'a> {
    graph: &'a SummaryGraph,
    has_retained_root: bool,
    types: PreparedTypeUniverse<'a>,
    owner_rows: Vec<&'a EffectRow>,
    contexts: Vec<Context>,
    labels: Vec<Request>,
    label_cache: HashMap<(usize, usize), usize>,
    call_cache: HashMap<(usize, usize, usize), usize>,
    data: Option<super::value::Analysis<'a>>,
    entries: Vec<State>,
    candidates: HashSet<(usize, usize)>,
    focusing: bool,
    payloads: Vec<(usize, usize, usize)>,
    cell_retentions: Vec<CellRetention>,
    retained_support: Vec<RetainedSupport>,
    pub(super) infer_cleanup_rows: bool,
    pub(super) collect_cleanup_rows: bool,
    pub(super) authenticate_actual_captures: bool,
    pub(super) actual_captures: Vec<super::ActualDiscardCapture>,
    pub(super) cleanup_rows: Vec<super::CleanupRequirement>,
}

/// Resource restore cuts relocate an existing exact occurrence. A same-code
/// sibling cannot replace it, and conflicting relocations grant no authority.
fn relocate_provider_resource_occurrence(
    owner: ProviderResourceOccurrence,
    restored_owners: &[(ProviderResourceOccurrence, ProviderResourceOccurrence)],
    budget: &mut TypeWorkBudget,
) -> Result<ProviderResourceOccurrence, Failure> {
    let mut restored = None;
    for (original, actual) in restored_owners {
        charge(budget, 1)?;
        if *original == owner {
            if restored.is_some_and(|previous| previous != *actual) {
                return Err(Failure::Invalid);
            }
            restored = Some(*actual);
        }
    }
    Ok(restored.unwrap_or(owner))
}

// Buckets restrict candidate comparisons; only full equality admits a duplicate.
// The constructor owns this index, and the borrowed first-occurrence vector stays authoritative.
fn retain_type_universe_entry<'a>(
    types: &mut Vec<&'a Type>,
    buckets: &mut HashMap<u64, Vec<usize>>,
    ty: &'a Type,
    hash: u64,
    budget: &mut TypeWorkBudget,
) -> Result<bool, Failure> {
    charge(budget, 1)?;
    if let Some(ordinals) = buckets.get_mut(&hash) {
        for ordinal in ordinals.iter() {
            charge(budget, 1)?;
            let previous = types.get(*ordinal).ok_or(Failure::Invalid)?;
            if same_type_with_budget(previous, ty, budget).map_err(|_| Failure::Resource)? {
                return Ok(false);
            }
        }
        charge(budget, 2)?;
        types.try_reserve(1).map_err(|_| Failure::Resource)?;
        ordinals.try_reserve(1).map_err(|_| Failure::Resource)?;
        let ordinal = types.len();
        types.push(ty);
        ordinals.push(ordinal);
    } else {
        charge(budget, 3)?;
        let mut ordinals = Vec::new();
        ordinals.try_reserve(1).map_err(|_| Failure::Resource)?;
        buckets.try_reserve(1).map_err(|_| Failure::Resource)?;
        types.try_reserve(1).map_err(|_| Failure::Resource)?;
        ordinals.push(types.len());
        types.push(ty);
        buckets.insert(hash, ordinals);
    }
    Ok(true)
}

// This constructor-local owner exposes no mutable universe or phase view.
// Entries only append, and consuming it ends the Unit admission proof.
// Consuming the original builder preserves its paid selector and authoritative order.
struct PreparedTypeUniverse<'a> {
    ordered: Vec<&'a Type>,
    buckets: HashMap<u64, Vec<usize>>,
}

impl<'a> PreparedTypeUniverse<'a> {
    fn lookup(&self, actual: &Type, budget: &mut TypeWorkBudget) -> Result<Option<usize>, ()> {
        let mut hasher = DefaultHasher::new();
        hash_type_with_budget(actual, &mut hasher, budget)?;
        budget.charge(1)?;
        let Some(ordinals) = self.buckets.get(&hasher.finish()) else {
            return Ok(None);
        };
        for ordinal in ordinals {
            budget.charge(1)?;
            let original = self.ordered.get(*ordinal).ok_or(())?;
            if same_type_with_budget(original, actual, budget)? {
                return Ok(Some(*ordinal));
            }
        }
        Ok(None)
    }

    #[cfg(test)]
    fn iter(&self) -> std::slice::Iter<'_, &'a Type> {
        self.ordered.iter()
    }

    #[cfg(test)]
    fn len(&self) -> usize {
        self.ordered.len()
    }

    #[cfg(test)]
    fn swap_ordinals(&mut self, left: usize, right: usize) {
        self.ordered.swap(left, right);
        for ordinals in self.buckets.values_mut() {
            for ordinal in ordinals.iter_mut() {
                if *ordinal == left {
                    *ordinal = right;
                } else if *ordinal == right {
                    *ordinal = left;
                }
            }
            ordinals.sort_unstable();
        }
    }
}

impl<'a> std::ops::Index<usize> for PreparedTypeUniverse<'a> {
    type Output = &'a Type;
    fn index(&self, index: usize) -> &Self::Output {
        &self.ordered[index]
    }
}

struct TypeUniverseBuilder<'a> {
    ordered: Vec<&'a Type>,
    buckets: HashMap<u64, Vec<usize>>,
    unit: UnitPhase,
}

enum UnitPhase {
    Unseen,
    Admitted,
}

// Constructed only by the actual Unit match; cold admission uses this borrow.
struct UnitOccurrence<'a> {
    original: &'a Type,
}

impl<'a> TypeUniverseBuilder<'a> {
    fn new() -> Self {
        Self {
            ordered: Vec::new(),
            buckets: HashMap::new(),
            unit: UnitPhase::Unseen,
        }
    }

    fn admit(&mut self, original: &'a Type, budget: &mut TypeWorkBudget) -> Result<bool, Failure> {
        // Pay the new kind classification, including on the full non-Unit path.
        charge(budget, 1)?;
        match original {
            Type::Unit => self.admit_unit(UnitOccurrence { original }, budget),
            _ => self.retain_original(original, budget),
        }
    }

    fn admit_unit(
        &mut self,
        unit: UnitOccurrence<'a>,
        budget: &mut TypeWorkBudget,
    ) -> Result<bool, Failure> {
        charge(budget, 1)?;
        match self.unit {
            UnitPhase::Admitted => Ok(false),
            UnitPhase::Unseen => {
                // Admit the scalar phase entry before original fallible work.
                // Full successful equality or retention establishes Unit here.
                charge(budget, 1)?;
                let retained = self.retain_original(unit.original, budget)?;
                self.unit = UnitPhase::Admitted;
                Ok(retained)
            }
        }
    }

    fn retain_original(
        &mut self,
        original: &'a Type,
        budget: &mut TypeWorkBudget,
    ) -> Result<bool, Failure> {
        let mut hasher = DefaultHasher::new();
        hash_type_with_budget(original, &mut hasher, budget).map_err(|_| Failure::Resource)?;
        retain_type_universe_entry(
            &mut self.ordered,
            &mut self.buckets,
            original,
            hasher.finish(),
            budget,
        )
    }

    fn into_prepared(
        self,
        budget: &mut TypeWorkBudget,
    ) -> Result<PreparedTypeUniverse<'a>, Failure> {
        charge(budget, 1)?;
        Ok(PreparedTypeUniverse {
            ordered: self.ordered,
            buckets: self.buckets,
        })
    }

    #[cfg(test)]
    fn into_ordered(self) -> Vec<&'a Type> {
        self.ordered
    }
}

/// Complete original-code inputs, consumed before any query state is created.
/// The borrowed graph fixes the identity of both the flag and ordered row inventory.
struct ControlCodeInventory<'a> {
    graph: &'a SummaryGraph,
    has_resource: bool,
    has_retained_root: bool,
    owner_rows: Vec<&'a EffectRow>,
}

/// Unused traversal payment from this root call's short-circuit control gate.
/// This is neither an owner-row inventory nor a semantic admission result.
/// Keep it lexical: the caller only filters queries on the same unmoved meter
/// before consuming it. No meter replacement, reset or submeter is permitted.
pub(super) struct PrepaidControlCodeScan<'a> {
    graph: &'a SummaryGraph,
    prefix: usize,
    unused: usize,
    meter: *const TypeWorkBudget,
    used: usize,
}

impl<'a> PrepaidControlCodeScan<'a> {
    pub(super) fn for_roots(
        graph: &'a SummaryGraph,
        budget: &mut TypeWorkBudget,
    ) -> Result<Option<Self>, Failure> {
        let count = graph.code.len();
        // Preserve the old no-control path: full structural payment, but no
        // owner-row traversal, allocation or validation at all.
        charge(budget, count)?;
        let Some(first) = graph.code.iter().position(|code| {
            matches!(
                code,
                Control::Discard { .. }
                    | Control::Resource { .. }
                    | Control::RetainedRoot { .. }
                    | Control::Retain { .. }
                    | Control::Continue { .. }
                    | Control::Registration { .. }
                    | Control::Cleanup { .. }
            )
        }) else {
            return Ok(None);
        };
        let prefix = first.checked_add(1).ok_or(Failure::Resource)?;
        let unused = count.checked_sub(prefix).ok_or(Failure::Invalid)?;
        charge(budget, 1)?;
        Ok(Some(Self {
            graph,
            prefix,
            unused,
            meter: std::ptr::from_ref(budget),
            used: budget.used(),
        }))
    }

    fn into_inventory(
        self,
        budget: &mut TypeWorkBudget,
    ) -> Result<ControlCodeInventory<'a>, Failure> {
        charge(budget, 1)?;
        if !std::ptr::eq(self.meter, std::ptr::from_ref(budget))
            || budget.used() < self.used
            || self.prefix.checked_add(self.unused) != Some(self.graph.code.len())
        {
            return Err(Failure::Invalid);
        }
        // The first gate spent prefix visits; only unused visits remain paid.
        // Pay the repeated prefix so the complete fresh scan below is covered.
        charge(budget, self.prefix)?;
        ControlCodeInventory::from_paid_scan(self.graph, budget)
    }
}

impl<'a> ControlCodeInventory<'a> {
    fn prepare(graph: &'a SummaryGraph, budget: &mut TypeWorkBudget) -> Result<Self, Failure> {
        charge(budget, graph.code.len())?;
        Self::from_paid_scan(graph, budget)
    }

    // Enter only after full payment above or consumption of one lexical gate
    // receipt. Every original row is visited in unchanged code/member order.
    fn from_paid_scan(
        graph: &'a SummaryGraph,
        budget: &mut TypeWorkBudget,
    ) -> Result<Self, Failure> {
        let mut has_resource = false;
        let mut has_retained_root = false;
        let mut owner_rows = Vec::new();
        for code in &graph.code {
            has_retained_root |= matches!(code, Control::RetainedRoot { .. });
            if let Control::NativeInterpret { effects, .. } = code {
                charge(budget, effects.len())?;
                for request in effects {
                    if let Some(effect) = &request.effect {
                        retain_owner_row_universe(effect.arguments(), &mut owner_rows, budget)?;
                    }
                }
            }
            match code {
                Control::Resource { effect, .. } => {
                    has_resource = true;
                    if let Some(effect) = &effect.effect {
                        retain_owner_row_universe(effect.arguments(), &mut owner_rows, budget)?;
                    }
                }
                Control::Request(request)
                | Control::Handler {
                    effect: request, ..
                } => {
                    if let Some(effect) = &request.effect {
                        retain_owner_row_universe(effect.arguments(), &mut owner_rows, budget)?;
                    }
                }
                Control::Registration { .. }
                | Control::Cleanup { .. }
                | Control::RetainedRoot { .. }
                | Control::Retain { .. }
                | Control::Continue { .. } => {
                    has_resource = true;
                }
                _ => {}
            }
        }
        Ok(Self {
            graph,
            has_resource,
            has_retained_root,
            owner_rows,
        })
    }
}

impl<'a> Analysis<'a> {
    pub(super) fn new(
        graph: &'a SummaryGraph,
        seed: Option<&'a Type>,
        budget: &mut TypeWorkBudget,
    ) -> Result<Self, Failure> {
        Self::from_code_inventory(ControlCodeInventory::prepare(graph, budget)?, seed, budget)
    }

    pub(super) fn from_prepaid_control_scan(
        scan: PrepaidControlCodeScan<'a>,
        seed: Option<&'a Type>,
        budget: &mut TypeWorkBudget,
    ) -> Result<Self, Failure> {
        Self::from_code_inventory(scan.into_inventory(budget)?, seed, budget)
    }

    fn from_code_inventory(
        inventory: ControlCodeInventory<'a>,
        seed: Option<&'a Type>,
        budget: &mut TypeWorkBudget,
    ) -> Result<Self, Failure> {
        let ControlCodeInventory {
            graph,
            has_resource,
            has_retained_root,
            mut owner_rows,
        } = inventory;
        let mut universe = TypeUniverseBuilder::new();
        let mut pending = Vec::new();
        pending
            .try_reserve(graph.types.0.len() + graph.callables.len())
            .map_err(|_| Failure::Resource)?;
        pending.extend(graph.types.0.iter());
        graph.callables.extend_types(&mut pending, budget)?;
        if let Some(seed) = seed {
            charge(budget, 1)?;
            pending.try_reserve(1).map_err(|_| Failure::Resource)?;
            pending.push(seed);
        }
        while let Some(ty) = pending.pop() {
            charge(budget, 1)?;
            if !universe.admit(ty, budget)? {
                continue;
            }
            match ty {
                Type::Application(a, b) | Type::Function(a, b) => {
                    pending.try_reserve(2).map_err(|_| Failure::Resource)?;
                    pending.push(a);
                    pending.push(b);
                }
                Type::Tuple(items) => {
                    pending
                        .try_reserve(items.len())
                        .map_err(|_| Failure::Resource)?;
                    pending.extend(items);
                }
                Type::Forall(_, body) => {
                    pending.try_reserve(1).map_err(|_| Failure::Resource)?;
                    pending.push(body);
                }
                Type::EffectfulFunction(domain, result) => {
                    pending.try_reserve(2).map_err(|_| Failure::Resource)?;
                    pending.push(domain);
                    pending.push(result.value());
                    charge(
                        budget,
                        result.effects().known().len()
                            + result.effects().tail().map_or(0, |tail| tail.lacks().len()),
                    )?;
                    for effect in result.effects().known().iter().chain(
                        result
                            .effects()
                            .tail()
                            .into_iter()
                            .flat_map(|tail| tail.lacks()),
                    ) {
                        charge(budget, effect.arguments().len())?;
                        pending
                            .try_reserve(effect.arguments().len())
                            .map_err(|_| Failure::Resource)?;
                        retain_owner_row_universe(effect.arguments(), &mut owner_rows, budget)?;
                        crate::types::extend_owner_type_children_with_charge(
                            effect.arguments(),
                            &mut pending,
                            budget,
                        )
                        .map_err(|_| Failure::Resource)?;
                    }
                }
                Type::ResourceApply(_, arguments) => {
                    retain_owner_row_universe(arguments, &mut owner_rows, budget)?;
                    crate::types::extend_owner_type_children_with_charge(
                        arguments.iter(),
                        &mut pending,
                        budget,
                    )
                    .map_err(|_| Failure::Resource)?;
                }
                _ => {}
            }
        }
        let types = universe.into_prepared(budget)?;
        let mut contexts = Vec::new();
        contexts.try_reserve(1).map_err(|_| Failure::Resource)?;
        contexts.push(Context {
            bindings: Vec::new(),
            rows: Vec::new(),
        });
        Ok(Self {
            graph,
            has_retained_root,
            types,
            owner_rows,
            contexts,
            labels: Vec::new(),
            label_cache: HashMap::new(),
            call_cache: HashMap::new(),
            data: if has_resource {
                Some(graph.data.as_ref().ok_or(Failure::Invalid)?.start(budget)?)
            } else {
                None
            },
            entries: Vec::new(),
            candidates: HashSet::new(),
            focusing: false,
            payloads: Vec::new(),
            cell_retentions: Vec::new(),
            retained_support: Vec::new(),
            infer_cleanup_rows: false,
            collect_cleanup_rows: false,
            authenticate_actual_captures: false,
            actual_captures: Vec::new(),
            cleanup_rows: Vec::new(),
        })
    }

    // The prepared universe already borrows immutable original source Types.
    // Return that source lifetime, so label interning may mutate this Analysis
    // while the completed replacement input remains borrowed and unchanged.
    fn type_replacements(
        &self,
        bindings: &[(TypeVariableId, usize)],
        budget: &mut TypeWorkBudget,
    ) -> Result<HashMap<TypeVariableId, &'a Type>, Failure> {
        let mut substitutions = HashMap::new();
        for (variable, target) in bindings {
            charge(budget, 1)?;
            if *target == usize::MAX {
                continue;
            }
            substitutions
                .try_reserve(1)
                .map_err(|_| Failure::Resource)?;
            substitutions.insert(*variable, self.types[*target]);
        }
        Ok(substitutions)
    }

    fn substitute(
        &self,
        ty: &Type,
        context: usize,
        budget: &mut TypeWorkBudget,
    ) -> Result<Type, Failure> {
        let substitutions = self.type_replacements(&self.contexts[context].bindings, budget)?;
        let mut rows = HashMap::new();
        for binding in &self.contexts[context].rows {
            charge(budget, 1)?;
            if binding.unproved || binding.tail == Some(EffectRowVariable::rigid(binding.variable))
            {
                continue;
            }
            let effect = |id: &usize| {
                self.labels[*id]
                    .effect
                    .as_deref()
                    .expect("exact row labels have instances")
            };
            let row = rebuild_effect_row_with_budget(
                binding.known.iter().map(effect),
                binding.tail,
                binding.lacks.iter().map(effect),
                clone_type_with_budget,
                budget,
            )
            .map_err(|_| Failure::Resource)?;
            rows.try_reserve(1).map_err(|_| Failure::Resource)?;
            rows.insert(binding.variable, row);
        }
        substitute_type_and_row_variables_borrowed_with(
            ty,
            &substitutions,
            &rows,
            |count| charge(budget, count),
            || Failure::Resource,
        )?
        .map_err(|_| Failure::Invalid)
    }

    fn intern_label(
        &mut self,
        label: Request,
        budget: &mut TypeWorkBudget,
    ) -> Result<usize, Failure> {
        for (id, previous) in self.labels.iter().enumerate() {
            charge(budget, 1)?;
            if previous.ambiguous_instance == label.ambiguous_instance
                && previous.region_service == label.region_service
                && same_effect(previous.effect.as_deref(), label.effect.as_deref(), budget)?
                && match (&previous.opaque_row, &label.opaque_row) {
                    (None, None) => true,
                    (Some(left), Some(right)) => {
                        crate::types::same_effect_rows_with_budget(left, right, budget)
                            .map_err(|_| Failure::Resource)?
                    }
                    _ => false,
                }
            {
                return Ok(id);
            }
        }
        self.labels.try_reserve(1).map_err(|_| Failure::Resource)?;
        let id = self.labels.len();
        self.labels.push(label);
        Ok(id)
    }

    fn specialize_label(
        &mut self,
        request: &Request,
        context: usize,
        budget: &mut TypeWorkBudget,
    ) -> Result<usize, Failure> {
        let mut label = request.copy(budget)?;
        if let Some(effect) = &request.effect {
            let mut arguments = super::KindedArguments(Vec::new());
            charge(budget, effect.arguments().len())?;
            arguments
                .0
                .try_reserve(effect.arguments().len())
                .map_err(|_| Failure::Resource)?;
            let substitutions = self.type_replacements(&self.contexts[context].bindings, budget)?;
            let mut rows = HashMap::new();
            rows.try_reserve(self.contexts[context].rows.len())
                .map_err(|_| Failure::Resource)?;
            for binding in &self.contexts[context].rows {
                charge(budget, 1)?;
                if binding.unproved
                    || binding.tail == Some(EffectRowVariable::rigid(binding.variable))
                {
                    continue;
                }
                let effect = |id: &usize| {
                    self.labels[*id]
                        .effect
                        .as_deref()
                        .expect("exact row labels have instances")
                };
                let row = rebuild_effect_row_with_budget(
                    binding.known.iter().map(effect),
                    binding.tail,
                    binding.lacks.iter().map(effect),
                    clone_type_with_budget,
                    budget,
                )
                .map_err(|_| Failure::Resource)?;
                rows.insert(binding.variable, row);
            }
            for argument in effect.arguments() {
                arguments.0.push(
                    crate::types::substitute_kinded_argument_borrowed_with(
                        argument,
                        &substitutions,
                        &rows,
                        |units| budget.charge(units),
                    )
                    .map_err(|_| Failure::Resource)?
                    .map_err(|_| Failure::Invalid)?,
                );
            }
            label.effect = Some(Arc::new(EffectInstance::new_kinded(
                effect.effect(),
                arguments.into_boxed_slice(),
            )));
            // Widening applies to the effect identity, never unrelated effects.
            charge(
                budget,
                self.contexts[context].bindings.len() + self.contexts[context].rows.len(),
            )?;
            label.ambiguous_instance |= self.contexts[context]
                .bindings
                .iter()
                .any(|(_, ty)| *ty == usize::MAX)
                || self.contexts[context]
                    .rows
                    .iter()
                    .any(|binding| binding.unproved);
        }
        self.intern_label(label, budget)
    }

    fn label(
        &mut self,
        code: usize,
        context: usize,
        budget: &mut TypeWorkBudget,
    ) -> Result<usize, Failure> {
        if let Some(label) = self.label_cache.get(&(code, context)) {
            return Ok(*label);
        }
        let request = match &self.graph.code[code] {
            Control::Request(request)
            | Control::Handler {
                effect: request, ..
            }
            | Control::Resource {
                effect: request, ..
            } => request,
            _ => return Err(Failure::Invalid),
        };
        let label = self.specialize_label(request, context, budget)?;
        self.label_cache
            .try_reserve(1)
            .map_err(|_| Failure::Resource)?;
        self.label_cache.insert((code, context), label);
        Ok(label)
    }

    fn match_labels(
        &self,
        request: usize,
        handler: usize,
        budget: &mut TypeWorkBudget,
    ) -> Result<(bool, bool), Failure> {
        let a = &self.labels[request];
        let b = &self.labels[handler];
        if let (Some(row), Some(effect)) = (&a.opaque_row, &b.effect)
            && !a.ambiguous_instance
            && !b.ambiguous_instance
            && let Some(tail) = row.tail()
        {
            for excluded in tail.lacks() {
                if same_effect(Some(excluded), Some(effect), budget)? {
                    return Ok((false, true));
                }
            }
        }
        let (Some(ae), Some(be)) = (&a.effect, &b.effect) else {
            return Ok((true, true));
        };
        if ae.effect() != be.effect() {
            return Ok((false, true));
        }
        if !a.ambiguous_instance
            && !b.ambiguous_instance
            && same_effect(Some(ae), Some(be), budget)?
        {
            return Ok((true, false));
        }
        if a.ambiguous_instance || b.ambiguous_instance {
            return Ok((true, true));
        }
        let mut pending = Vec::new();
        pending
            .try_reserve(ae.arguments().len())
            .map_err(|_| Failure::Resource)?;
        if !extend_possible_owner_pairs(ae.arguments(), be.arguments(), &mut pending, budget)? {
            return Ok((false, true));
        }
        while let Some((a, b)) = pending.pop() {
            charge(budget, 1)?;
            match (a, b) {
                (Type::Variable(_) | Type::Inference(_), _)
                | (_, Type::Variable(_) | Type::Inference(_)) => {}
                (Type::Application(a, b), Type::Application(c, d))
                | (Type::Function(a, b), Type::Function(c, d)) => {
                    pending.try_reserve(2).map_err(|_| Failure::Resource)?;
                    pending.push((a, c));
                    pending.push((b, d));
                }
                (Type::EffectfulFunction(a, b), Type::EffectfulFunction(c, d)) => {
                    pending.try_reserve(2).map_err(|_| Failure::Resource)?;
                    pending.push((a, c));
                    pending.push((b.value(), d.value()));
                }
                (Type::Forall(_, a), Type::Forall(_, b)) => {
                    pending.try_reserve(1).map_err(|_| Failure::Resource)?;
                    pending.push((a, b));
                }
                (Type::ResourceApply(a, left), Type::ResourceApply(b, right)) if a == b => {
                    if !extend_possible_owner_pairs(left, right, &mut pending, budget)? {
                        return Ok((false, true));
                    }
                }
                (Type::Tuple(a), Type::Tuple(b)) if a.len() == b.len() => {
                    pending
                        .try_reserve(a.len())
                        .map_err(|_| Failure::Resource)?;
                    pending.extend(a.iter().zip(b));
                }
                _ if same_type_with_budget(a, b, budget).map_err(|_| Failure::Resource)? => {}
                _ => return Ok((false, true)),
            }
        }
        Ok((true, true))
    }

    fn call_context(
        &mut self,
        code: usize,
        target: usize,
        context: usize,
        budget: &mut TypeWorkBudget,
    ) -> Result<usize, Failure> {
        if let Some(id) = self.call_cache.get(&(code, target, context)) {
            return Ok(*id);
        }
        let Control::Call { ty, source, .. } = &self.graph.code[code] else {
            return Err(Failure::Invalid);
        };
        let mut actual = TypeArguments(Vec::new());
        actual.0.try_reserve(1).map_err(|_| Failure::Resource)?;
        actual
            .0
            .push(self.substitute(&self.graph.types.0[*ty], context, budget)?);
        let result = self.context_for_actual(target, &actual.0[0], *source, budget)?;
        self.call_cache
            .try_reserve(1)
            .map_err(|_| Failure::Resource)?;
        self.call_cache.insert((code, target, context), result);
        Ok(result)
    }

    fn context_for_actual(
        &mut self,
        target: usize,
        actual: &Type,
        source: Span,
        budget: &mut TypeWorkBudget,
    ) -> Result<usize, Failure> {
        let mut pending = Vec::new();
        pending.try_reserve(1).map_err(|_| Failure::Resource)?;
        pending.push((&self.graph.callables.get(target, budget)?.ty, actual));
        let mut bindings = Vec::new();
        let mut row_equations = Vec::new();
        while let Some((formal, actual)) = pending.pop() {
            charge(budget, 1)?;
            if let Type::Variable(variable) = formal {
                let replacement = self
                    .types
                    .lookup(actual, budget)
                    .map_err(|_| Failure::Resource)?
                    .unwrap_or(usize::MAX);
                charge(budget, bindings.len())?;
                if let Some((_, previous)) = bindings.iter_mut().find(|(id, _)| id == variable) {
                    if *previous != replacement {
                        *previous = usize::MAX;
                    }
                } else {
                    bindings.try_reserve(1).map_err(|_| Failure::Resource)?;
                    bindings.push((*variable, replacement));
                }
            } else if let (Some(formal), Some(actual)) =
                (formal.function_view(), actual.function_view())
            {
                pending.try_reserve(2).map_err(|_| Failure::Resource)?;
                pending.push((formal.domain(), actual.domain()));
                pending.push((formal.value(), actual.value()));
                if let Some(formal) = formal.effects() {
                    let actual = actual.effects();
                    if matches!(
                        formal.tail().map(|tail| tail.variable()),
                        Some(EffectRowVariable::Rigid(_))
                    ) {
                        charge(budget, 1)?;
                        row_equations
                            .try_reserve(1)
                            .map_err(|_| Failure::Resource)?;
                        row_equations.push((formal, actual));
                    }
                    charge(budget, formal.known().len())?;
                    for effect in formal.known() {
                        let Some(actual) = actual else {
                            continue;
                        };
                        // An unresolved tail may contain another instance of this API.
                        // Its known prefix alone cannot determine the target's identity.
                        if actual.tail().is_some() {
                            continue;
                        }
                        charge(budget, actual.known().len())?;
                        let mut matches = actual
                            .known()
                            .iter()
                            .filter(|candidate| candidate.effect() == effect.effect());
                        if let Some(candidate) = matches.next()
                            && matches.next().is_none()
                        {
                            pending
                                .try_reserve(effect.arguments().len())
                                .map_err(|_| Failure::Resource)?;
                            extend_owner_context_pairs(
                                effect.arguments(),
                                candidate.arguments(),
                                &mut pending,
                                &mut row_equations,
                                budget,
                            )?;
                        }
                    }
                }
            } else {
                match (formal, actual) {
                    (Type::ResourceApply(a, left), Type::ResourceApply(b, right)) if a == b => {
                        extend_owner_context_pairs(
                            left,
                            right,
                            &mut pending,
                            &mut row_equations,
                            budget,
                        )?;
                    }
                    (Type::Application(a, b), Type::Application(c, d)) => {
                        pending.try_reserve(2).map_err(|_| Failure::Resource)?;
                        pending.push((a, c));
                        pending.push((b, d));
                    }
                    (Type::Tuple(a), Type::Tuple(b)) => {
                        pending
                            .try_reserve(a.len())
                            .map_err(|_| Failure::Resource)?;
                        pending.extend(a.iter().zip(b));
                    }
                    (Type::Forall(_, a), Type::Forall(_, b)) => {
                        pending.try_reserve(1).map_err(|_| Failure::Resource)?;
                        pending.push((a, b));
                    }
                    _ => {}
                }
            }
        }
        let mut rows: Vec<RowBinding> = Vec::new();
        if !row_equations.is_empty() {
            let substitutions = self.type_replacements(&bindings, budget)?;
            for (formal, actual) in row_equations {
                let Some(EffectRowVariable::Rigid(variable)) =
                    formal.tail().map(|tail| tail.variable())
                else {
                    return Err(Failure::Invalid);
                };
                let formal = formal
                    .substitute_type_variables_borrowed_with_budget(&substitutions, budget)
                    .map_err(|_| Failure::Resource)?;
                let mut remainder = if let Some(actual) = actual {
                    clone_effect_row_with_budget(actual, budget).map_err(|_| Failure::Resource)?
                } else {
                    EffectRow::empty()
                };
                // The original exact-removal result directly produces the
                // equation phase; no second caller-side classification is needed.
                let equation = 'known_prefix: {
                    for instance in formal.known() {
                        match remainder
                            .remove_exact_with_budget(instance, budget)
                            .map_err(|_| Failure::Resource)?
                        {
                            Ok(rest) => remainder = rest,
                            Err(_) => break 'known_prefix RowEquation::Unproved,
                        }
                    }
                    RowEquation::Residual(&remainder)
                };
                let incoming = self.row_binding(variable, equation, source, budget)?;
                charge(budget, rows.len())?;
                if let Some(previous) = rows.iter_mut().find(|binding| binding.variable == variable)
                {
                    charge(
                        budget,
                        previous.known.len()
                            + previous.lacks.len()
                            + incoming.known.len()
                            + incoming.lacks.len()
                            + 1,
                    )?;
                    if *previous != incoming {
                        previous.known.clear();
                        previous.lacks.clear();
                        previous.tail = None;
                        previous.unproved = true;
                    }
                } else {
                    charge(budget, 1)?;
                    rows.try_reserve(1).map_err(|_| Failure::Resource)?;
                    rows.push(incoming);
                }
            }
        }
        // Binding traversal is determined by the retained formal type.
        let incoming = Context { bindings, rows };
        let mut result = None;
        for (id, previous) in self.contexts.iter().enumerate() {
            charge(budget, previous.bindings.len() + previous.rows.len() + 1)?;
            for row in &previous.rows {
                charge(budget, row.known.len() + row.lacks.len())?;
            }
            if previous == &incoming {
                result = Some(id);
                break;
            }
        }
        let result = match result {
            Some(id) => id,
            None => {
                self.contexts
                    .try_reserve(1)
                    .map_err(|_| Failure::Resource)?;
                let id = self.contexts.len();
                self.contexts.push(incoming);
                id
            }
        };
        Ok(result)
    }

    fn row_binding(
        &mut self,
        variable: TypeVariableId,
        equation: RowEquation<'_>,
        source: Span,
        budget: &mut TypeWorkBudget,
    ) -> Result<RowBinding, Failure> {
        let mut known = Vec::new();
        let mut lacks = Vec::new();
        // One paid consuming dispatch. A completed prefix mismatch carries no
        // row; membership work cannot recover precision from this result.
        charge(budget, 1)?;
        let row = match equation {
            RowEquation::Unproved => {
                return Ok(RowBinding {
                    variable,
                    known,
                    tail: None,
                    lacks,
                    unproved: true,
                });
            }
            RowEquation::Residual(row) => row,
        };
        let mut unproved = false;
        // Row substitutions must not recursively grow a new argument universe.
        // As for ordinary bindings, exact arguments name original type subtrees.
        charge(
            budget,
            row.known().len() + row.tail().map_or(0, |tail| tail.lacks().len()),
        )?;
        for instance in row
            .known()
            .iter()
            .chain(row.tail().into_iter().flat_map(|tail| tail.lacks()))
        {
            charge(budget, instance.arguments().len())?;
            crate::types::visit_owner_type_children_with_charge(
                instance.arguments(),
                budget,
                |argument, budget| {
                    let found = self.types.lookup(argument, budget)?.is_some();
                    unproved |= !found;
                    Ok(())
                },
            )
            .map_err(|_| Failure::Resource)?;
        }
        let mut actual_owner_rows = Vec::new();
        for instance in row
            .known()
            .iter()
            .chain(row.tail().into_iter().flat_map(|tail| tail.lacks()))
        {
            retain_owner_row_universe(instance.arguments(), &mut actual_owner_rows, budget)?;
        }
        for row_argument in actual_owner_rows {
            let mut found = false;
            for original in &self.owner_rows {
                if crate::types::same_effect_rows_with_budget(row_argument, original, budget)
                    .map_err(|_| Failure::Resource)?
                {
                    found = true;
                    break;
                }
            }
            unproved |= !found;
        }
        if !unproved {
            for (destination, instances) in [
                (&mut known, row.known()),
                (&mut lacks, row.tail().map_or(&[][..], |tail| tail.lacks())),
            ] {
                charge(budget, instances.len())?;
                destination
                    .try_reserve(instances.len())
                    .map_err(|_| Failure::Resource)?;
                for instance in instances {
                    let label = Request::effect(instance, source, budget)?;
                    destination.push(self.intern_label(label, budget)?);
                }
                charge(
                    budget,
                    destination
                        .len()
                        .saturating_mul(destination.len().max(1).ilog2() as usize + 1),
                )?;
                destination.sort_unstable();
                destination.dedup();
            }
        }
        Ok(RowBinding {
            variable,
            known,
            tail: if unproved {
                None
            } else {
                row.tail().map(|tail| tail.variable())
            },
            lacks,
            unproved,
        })
    }

    fn source(&self, event: Event) -> Span {
        match &self.graph.code[event.code] {
            Control::Request(request) => request.source,
            Control::Call { source, .. } => *source,
            _ => unreachable!("events have request or call sites"),
        }
    }

    fn unsafe_discard(&self, code: usize, event: Event, owner: Option<CompletionOwner>) -> Failure {
        let Control::Discard { node, source, .. } = self.graph.code[code] else {
            return Failure::Invalid;
        };
        Failure::Unsafe(UnsafeDiscard {
            node,
            discard: source,
            request: self.source(event),
            owner,
        })
    }

    fn enqueue(
        state: State,
        pending: &mut VecDeque<State>,
        visited: &mut HashSet<State>,
        budget: &mut TypeWorkBudget,
    ) -> Result<(), Failure> {
        let mut state = state;
        state.normalize(budget)?;
        Self::enqueue_normalized(state, pending, visited, budget)
    }

    // Scalar control-position/context changes, or the proven pop helper below,
    // may reuse normalized reachability. Other stack/frame changes and new
    // roots use enqueue.
    fn enqueue_normalized(
        state: State,
        pending: &mut VecDeque<State>,
        visited: &mut HashSet<State>,
        budget: &mut TypeWorkBudget,
    ) -> Result<(), Failure> {
        let mut state = state;
        if state.abandoned.is_some() {
            // Discard provenance supplies diagnostics for unfinished clauses and
            // handlers removed during cleanup. Once none remain reachable, it
            // cannot affect later control. Keeping it would distinguish every
            // completed discard history in all subsequent computations.
            charge(budget, state.heap.len())?;
            if !state.heap.iter().any(|edge| {
                matches!(
                    edge.frame,
                    Frame::Clause {
                        consumed: false,
                        ..
                    } | Frame::RemovedHandler { .. }
                )
            }) {
                state.abandoned = None;
            }
        }
        state.charge_key(budget)?;
        if visited.contains(&state) {
            return Ok(());
        }
        let saved = state.copy(budget)?;
        state.charge_key(budget)?;
        visited.try_reserve(1).map_err(|_| Failure::Resource)?;
        visited.insert(saved);
        pending.try_reserve(1).map_err(|_| Failure::Resource)?;
        pending.push_back(state);
        Ok(())
    }

    fn enqueue_after_pop(
        mut state: State,
        root: Address,
        pending: &mut VecDeque<State>,
        visited: &mut HashSet<State>,
        budget: &mut TypeWorkBudget,
    ) -> Result<(), Failure> {
        state.prune_after_pop(root, budget)?;
        Self::enqueue_normalized(state, pending, visited, budget)
    }

    pub(super) fn check(
        &mut self,
        roots: &[usize],
        budget: &mut TypeWorkBudget,
    ) -> Result<(), Failure> {
        self.entries.clear();
        self.candidates.clear();
        self.payloads.clear();
        self.discover(roots, None, budget)?;
        // Passive row records describe the whole original discovery. Focused
        // safety queries remain strict and do not invent additional row sites.
        self.collect_cleanup_rows = false;
        if self.infer_cleanup_rows {
            return Ok(());
        }
        self.check_payloads(budget)?;
        self.check_cell_retentions(budget)?;
        if let Some(data) = &mut self.data {
            data.close(budget)?;
            for candidate in data.resource_candidates(budget)? {
                charge(budget, 1)?;
                self.candidates
                    .try_reserve(1)
                    .map_err(|_| Failure::Resource)?;
                self.candidates.insert(candidate);
            }
        }
        self.check_focused_entries(budget)
    }

    fn discover(
        &mut self,
        roots: &[usize],
        seed: Option<&State>,
        budget: &mut TypeWorkBudget,
    ) -> Result<(), Failure> {
        let mut pending = VecDeque::new();
        let mut visited = HashSet::new();
        let mut calls: Vec<ObservedCall> = Vec::new();
        let mut value_requests = HashSet::new();
        let mut unresolved_retained = HashSet::new();
        let mut observed_calls = HashMap::new();
        let mut revision = self
            .data
            .as_ref()
            .map_or(0, super::value::Analysis::revision);
        if let Some(seed) = seed {
            Self::enqueue(seed.copy(budget)?, &mut pending, &mut visited, budget)?;
        }
        for root in roots {
            let value_context = if let Some(data) = &mut self.data {
                let context = data.root_context(*root, budget)?;
                // Linked Core retains globals as ordinary outer bindings. Demand
                // the actual root so its lexical initializers feed callable ports.
                data.port(*root, context, budget)?;
                context
            } else {
                0
            };
            Self::enqueue(
                State {
                    position: Position {
                        code: *root,
                        next: 0,
                    },
                    context: 0,
                    value_context,
                    stack: Address::Empty,
                    heap: Vec::new(),
                    retained: Vec::new(),
                    cells: Vec::new(),
                    abandoned: None,
                },
                &mut pending,
                &mut visited,
                budget,
            )?;
        }
        loop {
            while let Some(state) = pending.pop_front() {
                charge(budget, 1)?;
                let code = state.position.code;
                match &self.graph.code[code] {
                    Control::Return => self.returned(state, &mut pending, &mut visited, budget)?,
                    Control::Unavailable => return Err(Failure::Invalid),
                    Control::Sequence(children) => {
                        self.discover_sequence(
                            state,
                            children,
                            &mut pending,
                            &mut visited,
                            budget,
                        )?;
                    }
                    Control::Choice(children) => {
                        for child in children {
                            let mut next = state.copy(budget)?;
                            next.position = Position {
                                code: *child,
                                next: 0,
                            };
                            Self::enqueue_normalized(next, &mut pending, &mut visited, budget)?;
                        }
                    }
                    Control::Handler { body, .. }
                    | Control::Cleanup { body, .. }
                    | Control::Resource { body, .. }
                    | Control::Registration { body, .. }
                    | Control::NativeInterpret { body, .. } => {
                        self.discover_boundary(state, *body, &mut pending, &mut visited, budget)?;
                    }
                    Control::RetainedRoot { body, store } => {
                        let (body, store) = (*body, *store);
                        state.charge_key(budget)?;
                        if !value_requests.contains(&state) {
                            value_requests
                                .try_reserve(1)
                                .map_err(|_| Failure::Resource)?;
                            value_requests.insert(state.copy(budget)?);
                        }
                        self.discover_retained_root(
                            state,
                            body,
                            store,
                            &mut unresolved_retained,
                            &mut pending,
                            &mut visited,
                            budget,
                        )?;
                    }
                    Control::Continue {
                        store,
                        key,
                        some,
                        none,
                    } => {
                        let (store, key, some, none) = (*store, *key, *some, *none);
                        state.charge_key(budget)?;
                        if !value_requests.contains(&state) {
                            value_requests
                                .try_reserve(1)
                                .map_err(|_| Failure::Resource)?;
                            value_requests.insert(state.copy(budget)?);
                        }
                        self.discover_continue(
                            state,
                            store,
                            key,
                            some,
                            none,
                            &mut unresolved_retained,
                            &mut pending,
                            &mut visited,
                            budget,
                        )?;
                    }
                    Control::Request(request) => {
                        if request.region_service
                            || request.effect.as_ref().is_some_and(|effect| {
                                effect.effect().module().is_builtin_resource()
                            })
                        {
                            state.charge_key(budget)?;
                            if !value_requests.contains(&state) {
                                value_requests
                                    .try_reserve(1)
                                    .map_err(|_| Failure::Resource)?;
                                let saved = state.copy(budget)?;
                                state.charge_key(budget)?;
                                value_requests.insert(saved);
                            }
                        }
                        let label = self.label(code, state.context, budget)?;
                        let port = self
                            .data
                            .as_mut()
                            .map(|data| data.port(code, state.value_context, budget))
                            .transpose()?;
                        self.requested(
                            &state,
                            Event {
                                code,
                                label,
                                unknown: false,
                                port,
                            },
                            &mut pending,
                            &mut visited,
                            budget,
                        )?;
                    }
                    Control::Call { .. } => {
                        self.discover_call(
                            state,
                            &mut calls,
                            &mut observed_calls,
                            &mut pending,
                            &mut visited,
                            budget,
                        )?;
                    }
                    Control::Resume { owner, value } => {
                        if state.position.next == 0 {
                            let value = *value;
                            let mut next = state;
                            next.push(
                                Frame::Next {
                                    position: Position { code, next: 1 },
                                    context: next.context,
                                    value_context: next.value_context,
                                },
                                budget,
                            )?;
                            next.position = Position {
                                code: value,
                                next: 0,
                            };
                            Self::enqueue(next, &mut pending, &mut visited, budget)?;
                        } else {
                            self.completed(
                                state,
                                *owner,
                                Completion::Resume,
                                &mut pending,
                                &mut visited,
                                budget,
                            )?;
                        }
                    }
                    Control::Discard { owner, .. } => self.completed(
                        state,
                        *owner,
                        Completion::Discard,
                        &mut pending,
                        &mut visited,
                        budget,
                    )?,
                    Control::Retain { owner } => self.completed(
                        state,
                        *owner,
                        Completion::Retain,
                        &mut pending,
                        &mut visited,
                        budget,
                    )?,
                }
            }
            let Some(data) = &mut self.data else {
                break;
            };
            data.close(budget)?;
            if data.revision() == revision {
                // Native transfers remain live during value growth. Missing
                // operands reject only after both discovery queues stabilize.
                break;
            }
            revision = data.revision();
            // Calls and explicit-owner requests choose successors from growing
            // value facts. Replay directly; enqueue would suppress visited states.
            charge(budget, calls.len())?;
            pending
                .try_reserve(calls.len())
                .map_err(|_| Failure::Resource)?;
            for call in &calls {
                pending.push_back(call.state.copy(budget)?);
            }
            charge(budget, value_requests.len())?;
            pending
                .try_reserve(value_requests.len())
                .map_err(|_| Failure::Resource)?;
            for request in &value_requests {
                pending.push_back(request.copy(budget)?);
            }
        }
        if !unresolved_retained.is_empty() {
            return Err(Failure::Invalid);
        }
        Ok(())
    }

    // Dispatch-specific owned temporaries must not remain live while a different
    // control branch copies continuation graphs on a bounded thread stack.
    #[inline(never)]
    fn discover_sequence(
        &mut self,
        state: State,
        children: &[usize],
        pending: &mut VecDeque<State>,
        visited: &mut HashSet<State>,
        budget: &mut TypeWorkBudget,
    ) -> Result<(), Failure> {
        let code = state.position.code;
        let mut ordinal = state.position.next;
        while children
            .get(ordinal)
            .is_some_and(|child| matches!(self.graph.code[*child], Control::Return))
        {
            charge(budget, 1)?;
            ordinal += 1;
        }
        if let Some(child) = children.get(ordinal).copied() {
            let mut next = state;
            // Pure trailing work has no continuation control. Keeping a
            // Next frame here multiplies recursive capture states.
            let mut following = ordinal + 1;
            while children
                .get(following)
                .is_some_and(|child| matches!(self.graph.code[*child], Control::Return))
            {
                charge(budget, 1)?;
                following += 1;
            }
            let position = Position {
                code,
                next: following,
            };
            if following < children.len() {
                next.push(
                    Frame::Next {
                        position,
                        context: next.context,
                        value_context: next.value_context,
                    },
                    budget,
                )?;
            }
            next.position = Position {
                code: child,
                next: 0,
            };
            if following < children.len() {
                Self::enqueue(next, pending, visited, budget)?;
            } else {
                Self::enqueue_normalized(next, pending, visited, budget)?;
            }
        } else {
            self.returned(state, pending, visited, budget)?;
        }
        Ok(())
    }

    fn is_store(&self, frame: Frame) -> bool {
        let Frame::Resource { code, .. } = frame else {
            return false;
        };
        matches!(&self.graph.code[code], Control::Resource { effect, .. }
            if effect.effect.as_ref().is_some_and(|instance|
                crate::resolved::StoreApi::for_module(instance.effect().module())
                    .is_some_and(|api| instance.effect() == api.probe())))
    }

    fn store_boundary(
        &mut self,
        state: &State,
        operand: usize,
        budget: &mut TypeWorkBudget,
    ) -> Result<StoreBoundary, Failure> {
        let (stores, _) = selections(
            state,
            state.stack,
            |frame| Ok((self.is_store(frame), true)),
            budget,
        )?;
        let data = self.data.as_mut().ok_or(Failure::Invalid)?;
        let (targets, unknown) = data.store_targets(operand, state.value_context, budget)?;
        if targets.is_empty() && stores.is_empty() {
            // A generic callable is checked before its actual caller supplies
            // a Store. Its graph is retained for that later invocation.
            return Ok(StoreBoundary::Symbolic);
        }
        if targets.is_empty() && !unknown {
            return Ok(StoreBoundary::Pending);
        }
        if unknown || targets.len() != 1 {
            return Err(Failure::Invalid);
        }
        let target = targets[0];
        let mut matches = Vec::new();
        let mut pending_owner = false;
        for selected in stores {
            charge(budget, 1)?;
            let Frame::Resource {
                code,
                value_context,
                ..
            } = selected.boundary.frame
            else {
                return Err(Failure::Invalid);
            };
            // A focused replay gives the frame a new occurrence context, but
            // its handle still names the original resource creation. Match
            // the actual handle's owner, as for other resource providers.
            let owners = data.cell_owner(code, value_context, budget)?;
            if owners.is_empty() {
                pending_owner = true;
                continue;
            }
            let [owner] = owners.as_slice() else {
                return Err(Failure::Invalid);
            };
            if *owner == target {
                matches.try_reserve(1).map_err(|_| Failure::Resource)?;
                matches.push(selected.boundary);
            }
        }
        if pending_owner {
            return Ok(StoreBoundary::Pending);
        }
        let [store] = matches.as_slice() else {
            return Err(Failure::Invalid);
        };
        if !matches!(store.address, Address::Slot { old: false, .. }) {
            return Err(Failure::Invalid);
        }
        Ok(StoreBoundary::Found(*store))
    }

    fn require_driver(
        &self,
        state: &State,
        store: Address,
        budget: &mut TypeWorkBudget,
    ) -> Result<(), Failure> {
        let mut pending = copy_slice(&[state.stack], budget)?;
        let mut visited = HashSet::new();
        while let Some(address) = pending.pop() {
            charge(budget, 1)?;
            if matches!(address, Address::Empty | Address::End) || visited.contains(&address) {
                continue;
            }
            visited.try_reserve(1).map_err(|_| Failure::Resource)?;
            visited.insert(address);
            for edge in state.edges(address, budget)? {
                if matches!(edge.frame, Frame::RetainedRoot { store: owner, .. } if owner == store)
                {
                    return Err(Failure::Invalid);
                }
                pending.try_reserve(2).map_err(|_| Failure::Resource)?;
                pending.push(edge.next);
                if let Frame::Clause {
                    capture,
                    consumed: false,
                    ..
                }
                | Frame::Closing {
                    capture: Some(capture),
                    ..
                } = edge.frame
                {
                    pending.push(capture);
                }
            }
        }
        Ok(())
    }

    #[allow(clippy::too_many_arguments)]
    fn discover_retained_root(
        &mut self,
        state: State,
        body: usize,
        store: usize,
        unresolved: &mut HashSet<State>,
        pending: &mut VecDeque<State>,
        visited: &mut HashSet<State>,
        budget: &mut TypeWorkBudget,
    ) -> Result<(), Failure> {
        let selected = match self.store_boundary(&state, store, budget)? {
            StoreBoundary::Symbolic => return Ok(()),
            StoreBoundary::Pending => {
                state.charge_key(budget)?;
                unresolved.try_reserve(1).map_err(|_| Failure::Resource)?;
                unresolved.insert(state);
                return Ok(());
            }
            StoreBoundary::Found(selected) => selected,
        };
        state.charge_key(budget)?;
        unresolved.remove(&state);
        self.require_driver(&state, selected.address, budget)?;
        let mut next = state;
        next.push(
            Frame::RetainedRoot {
                code: next.position.code,
                context: next.context,
                value_context: next.value_context,
                store: selected.address,
                baseline: selected.next,
            },
            budget,
        )?;
        next.position = Position {
            code: body,
            next: 0,
        };
        Self::enqueue(next, pending, visited, budget)
    }

    fn check_retained_capture(
        &self,
        state: &State,
        capture: Address,
        store: Address,
        budget: &mut TypeWorkBudget,
    ) -> Result<(), Failure> {
        let mut pending = copy_slice(&[capture], budget)?;
        let mut seen = HashSet::new();
        while let Some(address) = pending.pop() {
            charge(budget, 1)?;
            if matches!(address, Address::End | Address::Empty) || seen.contains(&address) {
                continue;
            }
            if address == store {
                return Err(Failure::Invalid);
            }
            seen.try_reserve(1).map_err(|_| Failure::Resource)?;
            seen.insert(address);
            let edges = state.edges(address, budget)?;
            if edges.is_empty() {
                return Err(Failure::Invalid);
            }
            for edge in edges {
                if self.is_store(edge.frame) {
                    push_store_captures(state, edge.address, &mut pending, budget)?;
                }
                pending.try_reserve(2).map_err(|_| Failure::Resource)?;
                pending.push(edge.next);
                if let Frame::Clause {
                    capture,
                    consumed: false,
                    ..
                }
                | Frame::Closing {
                    capture: Some(capture),
                    ..
                } = edge.frame
                {
                    pending.push(capture);
                }
            }
        }
        Ok(())
    }

    fn record_retained_support(
        &mut self,
        state: &State,
        capture: Address,
        store: Address,
        baseline: Address,
        code: usize,
        budget: &mut TypeWorkBudget,
    ) -> Result<(), Failure> {
        let Some(target) = self
            .data
            .as_ref()
            .and_then(super::value::Analysis::cell_focus)
        else {
            return Ok(());
        };
        let store_edges = state.edges(store, budget)?;
        let [store_edge] = store_edges else {
            return Err(Failure::Invalid);
        };
        // N's type and locator dependencies do not own its Store. Actual
        // Store handles still need to be absent from this captured cut.
        let store_owner = matches!(store_edge.frame, Frame::Resource { focused: true, .. });
        let select_focus = |frame| {
            let found = matches!(frame, Frame::Resource { focused: true, .. });
            Ok((found, !found))
        };
        if !store_owner {
            for root in [capture, baseline] {
                let (selected, escaped) = selections(state, root, select_focus, budget)?;
                if !selected.is_empty() {
                    if !escaped
                        && selected.len() == 1
                        && matches!(
                            selected[0].boundary.address,
                            Address::Slot { old: false, .. }
                        )
                    {
                        // The owner either moves with this cut or encloses N.
                        return Ok(());
                    }
                    return Err(Failure::Invalid);
                }
                if !escaped {
                    return Err(Failure::Invalid);
                }
            }
        }

        let data = self.data.as_ref().ok_or(Failure::Invalid)?;
        let (source, acquisition) = data.retained_support_site(code, budget)?;
        let mut inputs = super::value::SavedInputs::default();
        let mut pending = copy_slice(&[capture], budget)?;
        let mut seen = HashSet::new();
        while let Some(address) = pending.pop() {
            charge(budget, 1)?;
            if matches!(address, Address::Empty | Address::End) || seen.contains(&address) {
                continue;
            }
            seen.try_reserve(1).map_err(|_| Failure::Resource)?;
            seen.insert(address);
            let edges = state.edges(address, budget)?;
            if edges.is_empty() {
                return Err(Failure::Invalid);
            }
            for edge in edges {
                if self.is_store(edge.frame) {
                    push_store_captures(state, edge.address, &mut pending, budget)?;
                }
                match edge.frame {
                    Frame::Next {
                        position,
                        value_context,
                        ..
                    } => match &self.graph.code[position.code] {
                        Control::Sequence(children) => {
                            let current = position.next.checked_sub(1).ok_or(Failure::Invalid)?;
                            if current >= children.len() {
                                return Err(Failure::Invalid);
                            }
                            for child in &children[..current] {
                                data.saved_value(*child, value_context, &mut inputs, budget)?;
                            }
                            for child in &children[current..] {
                                if matches!(self.graph.code[*child], Control::Choice(_)) {
                                    data.saved_choice_inputs(
                                        position.code,
                                        *child,
                                        value_context,
                                        &mut inputs,
                                        budget,
                                    )?;
                                } else {
                                    data.saved_inputs(*child, value_context, &mut inputs, budget)?;
                                }
                            }
                        }
                        Control::Resume { value, .. } if position.next == 1 => {
                            data.saved_inputs(*value, value_context, &mut inputs, budget)?;
                        }
                        Control::Continue { .. } if position.next == 1 => {
                            data.saved_continue_inputs(
                                position.code,
                                value_context,
                                &mut inputs,
                                budget,
                            )?;
                        }
                        _ => return Err(Failure::Invalid),
                    },
                    Frame::Handler {
                        code,
                        capture_context,
                        ..
                    } => {
                        data.saved_handler_inputs(code, capture_context, &mut inputs, budget)?;
                    }
                    Frame::RemovedHandler {
                        code,
                        value_context,
                        ..
                    } => {
                        data.saved_handler_inputs(code, value_context, &mut inputs, budget)?;
                    }
                    Frame::Cleanup {
                        code,
                        value_context,
                        running,
                        ..
                    } => {
                        let Control::Cleanup { body, action, .. } = self.graph.code[code] else {
                            return Err(Failure::Invalid);
                        };
                        data.saved_inputs(action, value_context, &mut inputs, budget)?;
                        if running {
                            data.saved_value(body, value_context, &mut inputs, budget)?;
                        }
                    }
                    Frame::Clause {
                        handler,
                        ordinal,
                        clause_context,
                        capture_context,
                        ..
                    } => {
                        data.saved_clause_inputs(
                            handler,
                            ordinal,
                            clause_context,
                            &mut inputs,
                            budget,
                        )?;
                        data.saved_handler_inputs(handler, capture_context, &mut inputs, budget)?;
                    }
                    Frame::Resource { focused: true, .. } => {
                        // A nested owned occurrence needs a path-specific proof.
                        return Err(Failure::Invalid);
                    }
                    Frame::Resource {
                        code,
                        value_context,
                        ..
                    } => {
                        data.saved_inputs(code, value_context, &mut inputs, budget)?;
                        let occurrence = ProviderResourceOccurrence {
                            code,
                            value_context,
                        };
                        for cell in &state.cells {
                            charge(budget, 1)?;
                            if cell.occurrence == occurrence {
                                inputs.extend_ports(&cell.roots, budget)?;
                            }
                        }
                    }
                    Frame::Closing {
                        code,
                        value_context,
                        ..
                    }
                    | Frame::RetainedRoot {
                        code,
                        value_context,
                        ..
                    }
                    | Frame::Registration {
                        code,
                        value_context,
                        ..
                    }
                    | Frame::NativeInterpret {
                        code,
                        value_context,
                        ..
                    } => {
                        data.saved_inputs(code, value_context, &mut inputs, budget)?;
                    }
                }
                pending.try_reserve(2).map_err(|_| Failure::Resource)?;
                pending.push(edge.next);
                if let Frame::Clause {
                    capture,
                    consumed: false,
                    ..
                }
                | Frame::Closing {
                    capture: Some(capture),
                    ..
                } = edge.frame
                {
                    pending.push(capture);
                }
            }
        }
        charge(budget, 1)?;
        self.retained_support
            .try_reserve(1)
            .map_err(|_| Failure::Resource)?;
        self.retained_support.push(RetainedSupport {
            target,
            store_owner,
            inputs,
            source,
            acquisition,
        });
        Ok(())
    }

    fn check_retained_support(&mut self, budget: &mut TypeWorkBudget) -> Result<(), Failure> {
        let data = self.data.as_mut().ok_or(Failure::Invalid)?;
        data.close(budget)?;
        for support in &self.retained_support {
            charge(budget, 1)?;
            data.check_retained_support(
                support.target,
                support.store_owner,
                &support.inputs,
                support.source,
                support.acquisition,
                budget,
            )?;
        }
        Ok(())
    }

    #[allow(clippy::too_many_arguments)]
    fn discover_continue(
        &mut self,
        state: State,
        store: usize,
        key: usize,
        some: usize,
        none: usize,
        unresolved: &mut HashSet<State>,
        pending: &mut VecDeque<State>,
        visited: &mut HashSet<State>,
        budget: &mut TypeWorkBudget,
    ) -> Result<(), Failure> {
        if state.position.next == 1 {
            let mut next = state;
            next.position = Position {
                code: some,
                next: 0,
            };
            return Self::enqueue_normalized(next, pending, visited, budget);
        }
        let store = match self.store_boundary(&state, store, budget)? {
            StoreBoundary::Symbolic => return Ok(()),
            StoreBoundary::Pending => {
                state.charge_key(budget)?;
                unresolved.try_reserve(1).map_err(|_| Failure::Resource)?;
                unresolved.insert(state);
                return Ok(());
            }
            StoreBoundary::Found(store) => store,
        };
        self.require_driver(&state, store.address, budget)?;
        let (keys, unknown) = self.data.as_mut().ok_or(Failure::Invalid)?.retained_keys(
            key,
            state.value_context,
            budget,
        )?;
        if unknown {
            return Err(Failure::Invalid);
        }
        if keys.is_empty() {
            state.charge_key(budget)?;
            unresolved.try_reserve(1).map_err(|_| Failure::Resource)?;
            unresolved.insert(state);
            return Ok(());
        }
        state.charge_key(budget)?;
        unresolved.remove(&state);

        // A finite site/context key may summarize a stale generation. Keep
        // the miss path unless the value domain can prove a particular live
        // generation; a miss never consumes or executes a stored capture.
        let mut missed = state.copy(budget)?;
        missed.position = Position {
            code: none,
            next: 0,
        };
        Self::enqueue_normalized(missed, pending, visited, budget)?;

        for (ordinal, retained) in state.retained.iter().copied().enumerate() {
            charge(budget, 1)?;
            let Some(capture) = retained.capture else {
                continue;
            };
            if retained.store != store.address || !keys.contains(&retained.key) {
                continue;
            }
            let request = retained.event.port.ok_or(Failure::Invalid)?;
            let mut next = state.copy(budget)?;
            // Older addresses summarize multiple occurrences. Restoring one
            // cannot prove that all represented slots have been spent.
            if matches!(capture, Address::Slot { old: false, .. }) {
                next.retained[ordinal].capture = None;
            }
            self.data
                .as_mut()
                .ok_or(Failure::Invalid)?
                .continue_capture(
                    state.position.code,
                    state.value_context,
                    request,
                    retained.handler,
                    retained.handler_context,
                    budget,
                )?;
            next.push(
                Frame::Next {
                    position: Position {
                        code: state.position.code,
                        next: 1,
                    },
                    context: state.context,
                    value_context: state.value_context,
                },
                budget,
            )?;
            next.push(
                Frame::RetainedRoot {
                    code: retained.root,
                    context: retained.root_context,
                    value_context: retained.root_value_context,
                    store: retained.store,
                    baseline: retained.baseline,
                },
                budget,
            )?;
            let mut captured = Vec::new();
            let mut todo = copy_slice(&[capture], budget)?;
            let mut seen = HashSet::new();
            while let Some(address) = todo.pop() {
                charge(budget, 1)?;
                if address == Address::End || seen.contains(&address) {
                    continue;
                }
                seen.try_reserve(1).map_err(|_| Failure::Resource)?;
                seen.insert(address);
                for edge in state.edges(address, budget)? {
                    captured.try_reserve(1).map_err(|_| Failure::Resource)?;
                    captured.push(*edge);
                    todo.try_reserve(1).map_err(|_| Failure::Resource)?;
                    todo.push(edge.next);
                }
            }
            next.stack =
                next.copy_segment(capture, &captured, None, next.stack, Region::Active, budget)?;
            next.position = Position { code: 0, next: 0 };
            Self::enqueue(next, pending, visited, budget)?;
        }
        Ok(())
    }

    #[inline(never)]
    fn discover_boundary(
        &mut self,
        state: State,
        body: usize,
        pending: &mut VecDeque<State>,
        visited: &mut HashSet<State>,
        budget: &mut TypeWorkBudget,
    ) -> Result<(), Failure> {
        let code = state.position.code;
        let mut next = state;
        let frame = if matches!(self.graph.code[code], Control::Cleanup { .. }) {
            Frame::Cleanup {
                code,
                context: next.context,
                value_context: next.value_context,
                running: false,
                closing: None,
            }
        } else if matches!(self.graph.code[code], Control::Resource { .. }) {
            self.initialize_cell(&mut next, code, budget)?;
            if !self.focusing {
                let frame = Frame::Resource {
                    code,
                    context: next.context,
                    value_context: next.value_context,
                    focused: false,
                };
                let region = matches!(&self.graph.code[code], Control::Resource { effect, .. }
                    if effect.effect.as_ref().is_some_and(|instance|
                        crate::resolved::RegionApi::for_module(instance.effect().module())
                            .is_some_and(|api| instance.effect() == api.default_alloc())));
                if self.is_store(frame) || (self.has_retained_root && region) {
                    // A retained cut can depend on an owner without the
                    // final body result carrying it. Check these Store and
                    // region occurrences actually entered by control.
                    let owner = self.data.as_ref().ok_or(Failure::Invalid)?.resource_key(
                        code,
                        next.value_context,
                        budget,
                    )?;
                    charge(budget, 1)?;
                    self.candidates
                        .try_reserve(1)
                        .map_err(|_| Failure::Resource)?;
                    self.candidates.insert(owner);
                }
                charge(budget, 1)?;
                self.entries.try_reserve(1).map_err(|_| Failure::Resource)?;
                self.entries.push(next.copy(budget)?);
            }
            Frame::Resource {
                code,
                context: next.context,
                value_context: next.value_context,
                focused: false,
            }
        } else if matches!(self.graph.code[code], Control::NativeInterpret { .. }) {
            Frame::NativeInterpret {
                code,
                context: next.context,
                value_context: next.value_context,
            }
        } else if matches!(self.graph.code[code], Control::Registration { .. }) {
            Frame::Registration {
                code,
                context: next.context,
                value_context: next.value_context,
            }
        } else {
            Frame::Handler {
                code,
                context: next.context,
                value_context: next.value_context,
                capture_context: next.value_context,
            }
        };
        next.push(frame, budget)?;
        next.position = Position {
            code: body,
            next: 0,
        };
        Self::enqueue(next, pending, visited, budget)?;
        Ok(())
    }

    #[inline(never)]
    fn discover_call(
        &mut self,
        state: State,
        calls: &mut Vec<ObservedCall>,
        observed_calls: &mut HashMap<State, usize>,
        pending: &mut VecDeque<State>,
        visited: &mut HashSet<State>,
        budget: &mut TypeWorkBudget,
    ) -> Result<(), Failure> {
        let code = state.position.code;
        let Control::Call {
            value,
            ty,
            source,
            prefix,
        } = &self.graph.code[code]
        else {
            return Err(Failure::Invalid);
        };
        let (successors, publication) = if let Some(data) = &mut self.data {
            state.charge_key(budget)?;
            let (index, new_record) = if let Some(index) = observed_calls.get(&state) {
                (*index, false)
            } else {
                // One ordinal in the existing exact-State map and
                // one completed-phase field in its existing record.
                charge(budget, 2)?;
                observed_calls
                    .try_reserve(1)
                    .map_err(|_| Failure::Resource)?;
                let index = calls.len();
                let saved = state.copy(budget)?;
                state.charge_key(budget)?;
                observed_calls.insert(saved, index);
                calls.try_reserve(1).map_err(|_| Failure::Resource)?;
                (index, true)
            };
            let (successors, publication) = data.calls_after(
                code,
                state.value_context,
                if new_record {
                    None
                } else {
                    calls[index].delivered.as_ref()
                },
                budget,
            )?;
            (successors, Some((index, new_record, publication)))
        } else {
            charge(budget, value.targets.len())?;
            let mut targets = Vec::new();
            targets
                .try_reserve(value.targets.len())
                .map_err(|_| Failure::Resource)?;
            targets.extend(value.targets.iter().map(|target| (*target, 0)));
            (
                super::value::CallSuccessors {
                    targets,
                    unknown: value.unknown || value.targets.is_empty(),
                    returns: false,
                },
                None,
            )
        };
        let super::value::CallSuccessors {
            targets,
            unknown,
            returns,
        } = successors;
        let prefix = prefix
            .as_ref()
            .map(|request| request.copy(budget))
            .transpose()?;
        let ty = *ty;
        let source = *source;
        for (target, value_context) in targets {
            let context = self.call_context(code, target, state.context, budget)?;
            let mut next = state.copy(budget)?;
            next.context = context;
            next.value_context = value_context;
            next.position = Position {
                code: self.graph.callables.get(target, budget)?.body,
                next: 0,
            };
            Self::enqueue_normalized(next, pending, visited, budget)?;
        }
        if returns || unknown {
            // The opaque call may return now or request again. No
            // uncertainty marker survives its normal return.
            self.returned(state.copy(budget)?, pending, visited, budget)?;
        }
        if unknown {
            if let Some(prefix) = prefix {
                let label = self.intern_label(prefix, budget)?;
                let port = self
                    .data
                    .as_mut()
                    .map(|data| data.port(code, state.value_context, budget))
                    .transpose()?;
                self.requested(
                    &state,
                    Event {
                        code,
                        label,
                        unknown: true,
                        port,
                    },
                    pending,
                    visited,
                    budget,
                )?;
            }
            let mut ty_owner = TypeArguments(Vec::new());
            ty_owner.0.try_reserve(1).map_err(|_| Failure::Resource)?;
            ty_owner
                .0
                .push(self.substitute(&self.graph.types.0[ty], state.context, budget)?);
            if let Some(effects) = ty_owner.0[0]
                .function_view()
                .and_then(|function| function.effects())
            {
                let mut labels = Vec::new();
                for effect in effects.known() {
                    let request = Request::effect(effect, source, budget)?;
                    let label = self.intern_label(request, budget)?;
                    labels.try_reserve(1).map_err(|_| Failure::Resource)?;
                    labels.push(label);
                }
                if effects.tail().is_some() {
                    // Exact row bindings were expanded by substitute. Any
                    // remaining tail is unknown, not the enclosing call's row.
                    let mut request = Request::unknown(source);
                    charge(
                        budget,
                        self.contexts[state.context].bindings.len()
                            + self.contexts[state.context].rows.len(),
                    )?;
                    request.ambiguous_instance = self.contexts[state.context]
                        .bindings
                        .iter()
                        .any(|(_, ty)| *ty == usize::MAX)
                        || self.contexts[state.context]
                            .rows
                            .iter()
                            .any(|row| row.unproved);
                    request.opaque_row = Some(Arc::new(
                        clone_effect_row_with_budget(effects, budget)
                            .map_err(|_| Failure::Resource)?,
                    ));
                    let label = self.intern_label(request, budget)?;
                    charge(budget, 1)?;
                    labels.try_reserve(1).map_err(|_| Failure::Resource)?;
                    labels.push(label);
                }
                for label in labels {
                    let port = self
                        .data
                        .as_mut()
                        .map(|data| data.port(code, state.value_context, budget))
                        .transpose()?;
                    self.requested(
                        &state,
                        Event {
                            code,
                            label,
                            unknown: true,
                            port,
                        },
                        pending,
                        visited,
                        budget,
                    )?;
                }
            }
        }
        if let Some((index, new_record, publication)) = publication {
            let delivered = Some(publication.publish(budget)?);
            if new_record {
                // The exact key and record capacity are already paid. Retain
                // this owned state only after all successor/publication work
                // succeeds, rather than copying it and dropping the original.
                calls.push(ObservedCall { state, delivered });
            } else {
                calls[index].delivered = delivered;
            }
        }
        Ok(())
    }

    fn check_focused_entries(&mut self, budget: &mut TypeWorkBudget) -> Result<(), Failure> {
        if self.candidates.is_empty() {
            return Ok(());
        }
        let normal = self.data.take().ok_or(Failure::Invalid)?;
        let entries = std::mem::take(&mut self.entries);
        let mut covered = HashSet::new();
        self.focusing = true;
        let result = (|| {
            for entry in &entries {
                let key = normal.resource_key(entry.position.code, entry.value_context, budget)?;
                charge(budget, 1)?;
                if !self.candidates.contains(&key) {
                    continue;
                }
                covered.try_reserve(1).map_err(|_| Failure::Resource)?;
                covered.insert(key);
                let (query, context) =
                    normal.focused(entry.position.code, entry.value_context, budget)?;
                self.data = Some(query);
                self.cell_retentions.clear();
                self.retained_support.clear();
                let seed = self.restore_entry(entry, context, budget)?;
                self.payloads.clear();
                self.discover(&[], Some(&seed), budget)?;
                self.check_cell_retentions(budget)?;
                self.check_payloads(budget)?;
                self.check_retained_support(budget)?;
                let data = self.data.as_mut().ok_or(Failure::Invalid)?;
                data.close(budget)?;
                if let Err(failure) = data.check_resources(budget) {
                    if matches!(&self.graph.code[entry.position.code], Control::Resource { effect, .. }
                        if effect.effect.as_ref().is_some_and(|instance| instance.effect().module().is_builtin_resource()))
                    {
                        return Err(data.cell_escape_failure(
                            failure,
                            None,
                            entry.position.code,
                            context,
                            budget,
                        )?);
                    }
                    return Err(failure);
                }
            }
            charge(budget, self.candidates.len())?;
            if self
                .candidates
                .iter()
                .any(|candidate| !covered.contains(candidate))
            {
                return Err(Failure::Invalid);
            }
            Ok(())
        })();
        self.data = Some(normal);
        self.focusing = false;
        result
    }

    fn restore_entry(
        &mut self,
        entry: &State,
        context: usize,
        budget: &mut TypeWorkBudget,
    ) -> Result<State, Failure> {
        let mut seed = entry.copy(budget)?;
        let data = self.data.as_mut().ok_or(Failure::Invalid)?;
        let mut cuts = Vec::new();
        charge(budget, seed.heap.len())?;
        cuts.try_reserve(seed.heap.len())
            .map_err(|_| Failure::Resource)?;
        let mut restored_owners = Vec::new();
        charge(budget, seed.heap.len())?;
        restored_owners
            .try_reserve_exact(seed.heap.len())
            .map_err(|_| Failure::Resource)?;
        for edge in &mut seed.heap {
            let original_owner = match edge.frame {
                Frame::Resource {
                    code,
                    value_context,
                    ..
                } => Some(ProviderResourceOccurrence {
                    code,
                    value_context,
                }),
                _ => None,
            };
            let cut = match &mut edge.frame {
                Frame::Closing {
                    code,
                    value_context,
                    ..
                } => {
                    let cut = data.restore_cut(
                        *value_context,
                        *code,
                        usize::MAX - 5,
                        *code,
                        &[],
                        true,
                        budget,
                    )?;
                    *value_context = cut.context;
                    cut
                }
                Frame::Next {
                    position,
                    value_context,
                    ..
                } => {
                    let (pending, completed) = match &self.graph.code[position.code] {
                        Control::Sequence(children) => {
                            let pending = position.next.checked_sub(1).ok_or(Failure::Invalid)?;
                            (
                                *children.get(pending).ok_or(Failure::Invalid)?,
                                &children[..pending],
                            )
                        }
                        Control::Resume { value, .. } if position.next == 1 => (*value, &[][..]),
                        _ => return Err(Failure::Invalid),
                    };
                    let cut = data.restore_cut(
                        *value_context,
                        position.code,
                        position.next,
                        pending,
                        completed,
                        false,
                        budget,
                    )?;
                    *value_context = cut.context;
                    cut
                }
                Frame::Cleanup {
                    code,
                    value_context,
                    running,
                    ..
                } => {
                    let Control::Cleanup { body, action, .. } = self.graph.code[*code] else {
                        return Err(Failure::Invalid);
                    };
                    let completed = if *running {
                        std::slice::from_ref(&body)
                    } else {
                        &[]
                    };
                    let cut = data.restore_cut(
                        *value_context,
                        *code,
                        usize::MAX - 2 - usize::from(*running),
                        if *running { action } else { body },
                        completed,
                        false,
                        budget,
                    )?;
                    *value_context = cut.context;
                    cut
                }
                Frame::Handler {
                    code,
                    value_context,
                    ..
                }
                | Frame::RemovedHandler {
                    code,
                    value_context,
                    ..
                }
                | Frame::Resource {
                    code,
                    value_context,
                    ..
                }
                | Frame::RetainedRoot {
                    code,
                    value_context,
                    ..
                }
                | Frame::NativeInterpret {
                    code,
                    value_context,
                    ..
                }
                | Frame::Registration {
                    code,
                    value_context,
                    ..
                } => {
                    let body = match &self.graph.code[*code] {
                        Control::Handler { body, .. }
                        | Control::Resource { body, .. }
                        | Control::RetainedRoot { body, .. }
                        | Control::Registration { body, .. }
                        | Control::NativeInterpret { body, .. } => *body,
                        _ => return Err(Failure::Invalid),
                    };
                    let cut = data.restore_cut(
                        *value_context,
                        *code,
                        usize::MAX - 1,
                        body,
                        &[],
                        true,
                        budget,
                    )?;
                    *value_context = cut.context;
                    cut
                }
                Frame::Clause {
                    handler,
                    ordinal,
                    value_context,
                    clause_context,
                    event,
                    ..
                } => {
                    let Control::Handler { body, clauses, .. } = &self.graph.code[*handler] else {
                        return Err(Failure::Invalid);
                    };
                    let clause = clauses.get(*ordinal).ok_or(Failure::Invalid)?;
                    let cut = data.restore_cut(
                        *clause_context,
                        clause.body,
                        usize::MAX - 2,
                        clause.body,
                        &[],
                        true,
                        budget,
                    )?;
                    let handler_cut = data.restore_cut(
                        *value_context,
                        *handler,
                        usize::MAX - 1,
                        *body,
                        &[],
                        true,
                        budget,
                    )?;
                    data.join_ports(handler_cut.result, cut.result, budget)?;
                    *value_context = handler_cut.context;
                    *clause_context = cut.context;
                    if let Some(port) = event.port {
                        event.port = Some(data.restore_event(port, budget)?);
                    }
                    super::value::Cut {
                        result: handler_cut.result,
                        ..cut
                    }
                }
            };
            if let Some(original) = original_owner {
                let Frame::Resource {
                    code,
                    value_context,
                    ..
                } = edge.frame
                else {
                    return Err(Failure::Invalid);
                };
                restored_owners.push((
                    original,
                    ProviderResourceOccurrence {
                        code,
                        value_context,
                    },
                ));
            }
            cuts.push(cut);
        }
        for cell in &mut seed.cells {
            cell.occurrence =
                relocate_provider_resource_occurrence(cell.occurrence, &restored_owners, budget)?;
        }
        // A live Store slot is part of the same saved control graph as its
        // frames. Rebuild its non-owning root/handler contexts and request
        // port with the same cut identities; a spent locator has no capture.
        for retained in &mut seed.retained {
            charge(budget, 1)?;
            if retained.capture.is_none() {
                continue;
            }
            let Control::RetainedRoot { body, .. } = self.graph.code[retained.root] else {
                return Err(Failure::Invalid);
            };
            retained.root_value_context = data
                .restore_cut(
                    retained.root_value_context,
                    retained.root,
                    usize::MAX - 1,
                    body,
                    &[],
                    true,
                    budget,
                )?
                .context;
            let Control::Handler { body, .. } = self.graph.code[retained.handler] else {
                return Err(Failure::Invalid);
            };
            retained.handler_context = data
                .restore_cut(
                    retained.handler_context,
                    retained.handler,
                    usize::MAX - 1,
                    body,
                    &[],
                    true,
                    budget,
                )?
                .context;
            let port = retained.event.port.ok_or(Failure::Invalid)?;
            retained.event.port = Some(data.restore_event(port, budget)?);
        }
        // Connect the saved continuation graph by result ports. Reusing old
        // value-context equality would replay completed calls and acquisitions.
        for (index, edge) in seed.heap.iter().enumerate() {
            for (outer, destination) in seed.heap.iter().enumerate() {
                charge(budget, 1)?;
                if edge.next == destination.address {
                    data.join_ports(cuts[outer].input, cuts[index].result, budget)?;
                }
            }
            if let Frame::Clause {
                capture,
                event: Event {
                    port: Some(port), ..
                },
                ..
            } = edge.frame
            {
                for (captured, destination) in seed.heap.iter().enumerate() {
                    charge(budget, 1)?;
                    if capture == destination.address {
                        data.join_ports(cuts[captured].input, port, budget)?;
                    }
                }
            }
        }
        for retained in &seed.retained {
            charge(budget, 1)?;
            let Some(capture) = retained.capture else {
                continue;
            };
            let port = retained.event.port.ok_or(Failure::Invalid)?;
            let mut connected = false;
            for (index, edge) in seed.heap.iter().enumerate() {
                charge(budget, 1)?;
                if capture == edge.address {
                    data.join_ports(cuts[index].input, port, budget)?;
                    connected = true;
                }
            }
            if !connected {
                return Err(Failure::Invalid);
            }
        }
        let result = data.port(entry.position.code, context, budget)?;
        for (index, edge) in seed.heap.iter().enumerate() {
            charge(budget, 1)?;
            if seed.stack == edge.address {
                data.join_ports(cuts[index].input, result, budget)?;
            }
        }
        let Control::Resource { body, .. } = self.graph.code[entry.position.code] else {
            return Err(Failure::Invalid);
        };
        let fresh_cell = if matches!(&self.graph.code[entry.position.code], Control::Resource { effect, .. } if effect.effect.as_ref().is_some_and(|instance| instance.effect().module().is_builtin_resource()))
        {
            let owner = data.resource_key(entry.position.code, context, budget)?;
            let (_, root) =
                data.cell_initializer(entry.position.code, entry.value_context, budget)?;
            let predecessors =
                data.cell_predecessors(entry.position.code, entry.value_context, budget)?;
            Some((owner, root, predecessors))
        } else {
            None
        };
        data.close(budget)?;
        seed.value_context = context;
        if let Some((owner, root, predecessors)) = fresh_cell {
            let Control::Resource { effect, .. } = &self.graph.code[entry.position.code] else {
                return Err(Failure::Invalid);
            };
            let source = effect.source;
            let enclosing = self.cell_enclosing(&seed, seed.stack, budget)?;
            let initializer_source = self
                .data
                .as_ref()
                .ok_or(Failure::Invalid)?
                .cell_initializer_source(entry.position.code, budget)?;
            self.record_cell_retention(
                CellRetentionSite {
                    target: owner,
                    request: None,
                    root,
                    source: initializer_source,
                    acquisition: source,
                },
                &enclosing,
                &predecessors,
                budget,
            )?;
            // Keep an enclosing same-site occurrence, but replace the marker
            // belonging solely to this not-yet-entered acquisition.
            charge(budget, seed.cells.len().saturating_mul(seed.heap.len()))?;
            seed.cells.retain(|cell| seed.heap.iter().any(|edge| matches!(edge.frame,
                Frame::Resource { code, value_context, .. } if cell.occurrence == ProviderResourceOccurrence { code, value_context })));
            charge(budget, 1)?;
            seed.cells.try_reserve(1).map_err(|_| Failure::Resource)?;
            seed.cells.push(CellContents {
                occurrence: ProviderResourceOccurrence {
                    code: entry.position.code,
                    value_context: context,
                },
                owner,
                roots: copy_slice(&[root], budget)?,
                enclosing: share_cell_birth_slice(enclosing, budget)?,
                predecessors: share_cell_birth_slice(predecessors, budget)?,
                shared: false,
            });
        }
        seed.push(
            Frame::Resource {
                code: entry.position.code,
                context: entry.context,
                value_context: context,
                focused: true,
            },
            budget,
        )?;
        seed.position = Position {
            code: body,
            next: 0,
        };
        Ok(seed)
    }

    fn returned(
        &mut self,
        state: State,
        pending: &mut VecDeque<State>,
        visited: &mut HashSet<State>,
        budget: &mut TypeWorkBudget,
    ) -> Result<(), Failure> {
        if state.stack == Address::Empty {
            return Ok(());
        }
        for edge in state.edges(state.stack, budget)? {
            if self.focusing && matches!(edge.frame, Frame::Resource { focused: true, .. }) {
                // This query ends with its designated activation. The final
                // converged body-result check owns the exit obligation; later
                // caller execution cannot acquire this fresh marker again.
                continue;
            }
            let mut next = state.copy(budget)?;
            next.stack = edge.next;
            if let Frame::Resource {
                code,
                value_context,
                ..
            } = edge.frame
            {
                charge(budget, next.cells.len())?;
                next.cells.retain(|cell| {
                    cell.shared
                        || cell.occurrence
                            != ProviderResourceOccurrence {
                                code,
                                value_context,
                            }
                });
            }
            match edge.frame {
                Frame::Closing {
                    code,
                    context,
                    value_context,
                    capture,
                    event,
                    ..
                } => {
                    next.context = context;
                    next.value_context = value_context;
                    next.position = Position { code: 0, next: 0 };
                    if let Some(capture) = capture {
                        self.close_segment(&state, &mut next, capture, code, event, budget)?;
                    }
                }
                Frame::Cleanup {
                    code,
                    context,
                    value_context,
                    running,
                    closing,
                } => {
                    next.context = context;
                    next.value_context = value_context;
                    next.position = if running {
                        Position { code: 0, next: 0 }
                    } else {
                        if let Some(discard) = closing {
                            self.record_cleanup_row(
                                &state, edge.next, code, context, discard, budget,
                            )?;
                        }
                        let Control::Cleanup { action, .. } = self.graph.code[code] else {
                            return Err(Failure::Invalid);
                        };
                        next.push(
                            Frame::Cleanup {
                                code,
                                context,
                                value_context,
                                running: true,
                                closing,
                            },
                            budget,
                        )?;
                        Position {
                            code: action,
                            next: 0,
                        }
                    };
                }
                Frame::Next {
                    position,
                    context,
                    value_context,
                } => {
                    next.position = position;
                    next.context = context;
                    next.value_context = value_context;
                }
                Frame::Handler {
                    context,
                    value_context,
                    ..
                }
                | Frame::RemovedHandler {
                    context,
                    value_context,
                    ..
                }
                | Frame::Resource {
                    context,
                    value_context,
                    ..
                }
                | Frame::RetainedRoot {
                    context,
                    value_context,
                    ..
                }
                | Frame::NativeInterpret {
                    context,
                    value_context,
                    ..
                }
                | Frame::Registration {
                    context,
                    value_context,
                    ..
                } => {
                    next.position = Position { code: 0, next: 0 };
                    next.context = context;
                    next.value_context = value_context;
                }
                Frame::Clause {
                    handler,
                    ordinal,
                    context,
                    value_context,
                    consumed,
                    ..
                } => {
                    if !consumed && (!self.infer_cleanup_rows || self.authenticate_actual_captures)
                    {
                        let Control::Handler { clauses, .. } = &self.graph.code[handler] else {
                            return Err(Failure::Invalid);
                        };
                        return Err(match state.abandoned {
                            Some((discard, event)) => self.unsafe_discard(
                                discard,
                                event,
                                Some(CompletionOwner::Clause(clauses[ordinal].source)),
                            ),
                            None => Failure::Invalid,
                        });
                    }
                    next.position = Position { code: 0, next: 0 };
                    next.context = context;
                    next.value_context = value_context;
                }
            }
            if matches!(
                edge.frame,
                Frame::Cleanup { running: false, .. }
                    | Frame::Closing {
                        capture: Some(_),
                        ..
                    }
            ) {
                // Starting the action adds a new completion frame, so this is
                // not the pop-only transition whose heap is already sorted.
                Self::enqueue(next, pending, visited, budget)?;
            } else {
                // Popping changes reachability, not the order or contents of edges.
                Self::enqueue_after_pop(next, state.stack, pending, visited, budget)?;
            }
        }
        Ok(())
    }

    fn is_cell_handler(&self, frame: Frame) -> bool {
        let code = match frame {
            Frame::Handler { code, .. } | Frame::RemovedHandler { code, .. } => code,
            _ => return false,
        };
        matches!(&self.graph.code[code], Control::Handler { effect, .. } if effect.effect.as_ref().is_some_and(|effect| effect.effect().module().is_builtin_resource()))
    }

    fn boundary_match_key(&self, frame: Frame) -> (usize, usize, Option<Frame>) {
        let (code, context) = match frame {
            Frame::Handler { code, context, .. }
            | Frame::RemovedHandler { code, context, .. }
            | Frame::Resource { code, context, .. }
            | Frame::NativeInterpret { code, context, .. } => (code, context),
            _ => unreachable!("only interpreter boundaries have match keys"),
        };
        // Generic cells depend on the exact live occurrence as well as code/context.
        (
            code,
            context,
            (self.is_cell(frame) || self.is_cell_handler(frame)
                || matches!(&self.graph.code[code], Control::Handler { effect, .. } if effect.region_service)).then_some(frame),
        )
    }

    fn requested(
        &mut self,
        state: &State,
        event: Event,
        pending: &mut VecDeque<State>,
        visited: &mut HashSet<State>,
        budget: &mut TypeWorkBudget,
    ) -> Result<(), Failure> {
        if self.has_retained_root {
            self.check_probe_driver(state, event, budget)?;
        }
        // Finish boundary specialization before reserving the continuation
        // frame, which contains copied states and capture construction locals.
        let boundaries = self.requested_boundaries(state, event, state.stack, budget)?;
        if self.has_retained_root {
            self.check_retained_interpretation(state, event, &boundaries, budget)?;
        }
        self.requested_continuations(state, event, boundaries, pending, visited, budget)
    }

    fn check_probe_driver(
        &mut self,
        state: &State,
        event: Event,
        budget: &mut TypeWorkBudget,
    ) -> Result<(), Failure> {
        let mut pending = copy_slice(&[state.stack], budget)?;
        let mut seen = HashSet::new();
        while let Some(address) = pending.pop() {
            charge(budget, 1)?;
            if matches!(address, Address::Empty | Address::End) || seen.contains(&address) {
                continue;
            }
            seen.try_reserve(1).map_err(|_| Failure::Resource)?;
            seen.insert(address);
            for edge in state.edges(address, budget)? {
                if let Frame::RetainedRoot { store, .. } = edge.frame {
                    let owners = state.edges(store, budget)?;
                    let [owner] = owners else {
                        return Err(Failure::Invalid);
                    };
                    let Frame::Resource { code, context, .. } = owner.frame else {
                        return Err(Failure::Invalid);
                    };
                    let target = self.label(code, context, budget)?;
                    if self.match_labels(event.label, target, budget)?.0 {
                        return Err(Failure::Invalid);
                    }
                }
                pending.try_reserve(2).map_err(|_| Failure::Resource)?;
                pending.push(edge.next);
                if let Frame::Clause {
                    capture,
                    consumed: false,
                    ..
                }
                | Frame::Closing {
                    capture: Some(capture),
                    ..
                } = edge.frame
                {
                    pending.push(capture);
                }
            }
        }
        Ok(())
    }

    fn check_retained_interpretation(
        &mut self,
        state: &State,
        event: Event,
        boundaries: &(Vec<Selection>, bool),
        budget: &mut TypeWorkBudget,
    ) -> Result<(), Failure> {
        let mut checks = Vec::new();
        for selected in &boundaries.0 {
            for edge in &selected.prefix {
                charge(budget, 1)?;
                if let Frame::RetainedRoot { baseline, .. } = edge.frame {
                    checks.try_reserve(1).map_err(|_| Failure::Resource)?;
                    checks.push((baseline, Some(selected.boundary)));
                }
            }
        }
        if boundaries.1 {
            // A summarized stack may contain several possible escaped paths.
            // Checking every active root is conservative for those paths.
            let (roots, _) = selections(
                state,
                state.stack,
                |frame| Ok((matches!(frame, Frame::RetainedRoot { .. }), true)),
                budget,
            )?;
            for root in roots {
                let Frame::RetainedRoot { baseline, .. } = root.boundary.frame else {
                    return Err(Failure::Invalid);
                };
                checks.try_reserve(1).map_err(|_| Failure::Resource)?;
                checks.push((baseline, None));
            }
        }
        for (baseline, actual) in checks {
            if !matches!(baseline, Address::Empty | Address::End)
                && state.edges(baseline, budget)?.is_empty()
            {
                return Err(Failure::RetainedInterpretation {
                    source: self.source(event),
                });
            }
            let (expected, escaped) = self.requested_boundaries(state, event, baseline, budget)?;
            let same = match actual {
                Some(actual) => matches!(expected.as_slice(), [expected]
                    if !escaped && matches!(actual.address, Address::Slot { old: false, .. })
                        && expected.boundary.address == actual.address
                        && expected.boundary.frame == actual.frame),
                None => escaped && expected.is_empty(),
            };
            if !same {
                return Err(Failure::RetainedInterpretation {
                    source: self.source(event),
                });
            }
        }
        Ok(())
    }

    fn requested_boundaries(
        &mut self,
        state: &State,
        event: Event,
        root: Address,
        budget: &mut TypeWorkBudget,
    ) -> Result<(Vec<Selection>, bool), Failure> {
        // Resolve labels first so selection's callback does not borrow the
        // shared structural work counter a second time.
        let mut matching = HashMap::new();
        let mut cell_operands = None;
        let mut region_targets = None;
        let explicit_region = matches!(&self.graph.code[event.code], Control::Request(request) if request.region_service);
        charge(budget, state.heap.len())?;
        for edge in &state.heap {
            if let Frame::Handler { code, context, .. }
            | Frame::Resource { code, context, .. }
            | Frame::RemovedHandler { code, context, .. }
            | Frame::NativeInterpret { code, context, .. } = edge.frame
                && !matching.contains_key(&self.boundary_match_key(edge.frame))
            {
                if let (Frame::NativeInterpret { .. }, Control::NativeInterpret { effects, .. }) =
                    (&edge.frame, &self.graph.code[code])
                {
                    charge(budget, effects.len())?;
                    let mut possible = false;
                    let mut outward = true;
                    for request in effects {
                        let target = self.specialize_label(request, context, budget)?;
                        let relation = self.match_labels(event.label, target, budget)?;
                        possible |= relation.0;
                        outward &= relation.1;
                    }
                    matching.try_reserve(1).map_err(|_| Failure::Resource)?;
                    matching.insert(self.boundary_match_key(edge.frame), (possible, outward));
                    continue;
                }
                let region_handler = matches!(&self.graph.code[code], Control::Handler { effect, .. } if effect.region_service);
                if explicit_region || region_handler {
                    let mut relation = (false, true);
                    if explicit_region && region_handler {
                        if region_targets.is_none() {
                            region_targets = Some(
                                self.data
                                    .as_mut()
                                    .ok_or(Failure::Invalid)?
                                    .region_targets(event.port.ok_or(Failure::Invalid)?, budget)?,
                            );
                        }
                        let (Frame::Handler { value_context, .. }
                        | Frame::RemovedHandler { value_context, .. }) = edge.frame
                        else {
                            return Err(Failure::Invalid);
                        };
                        let owners = self
                            .data
                            .as_mut()
                            .ok_or(Failure::Invalid)?
                            .handler_cell_owners(code, value_context, budget)?;
                        let (targets, unknown, host) =
                            region_targets.as_ref().ok_or(Failure::Invalid)?;
                        if let Some(owners) = owners {
                            relation = (*unknown, *unknown || *host || targets.is_empty());
                            for target in targets {
                                charge(budget, owners.len() + 1)?;
                                let matches = owners.contains(target);
                                relation.0 |= matches;
                                relation.1 |= !matches;
                            }
                        } else {
                            // Unresolved symbolic views retain every candidate
                            // and outward obligation; they never select nearest.
                            relation = (true, true);
                        }
                    }
                    matching.try_reserve(1).map_err(|_| Failure::Resource)?;
                    matching.insert(self.boundary_match_key(edge.frame), relation);
                    continue;
                }
                let target = self.label(code, context, budget)?;
                let relation = self.match_labels(event.label, target, budget)?;
                let relation = if self.is_cell(edge.frame)
                    && let Control::Request(request) = &self.graph.code[event.code]
                    && let Some(operation) = request.operation
                    && operation.owner().module().is_builtin_resource()
                {
                    let port = event.port.ok_or(Failure::Invalid)?;
                    if cell_operands.is_none() {
                        cell_operands =
                            Some(self.data.as_mut().ok_or(Failure::Invalid)?.cell_operands(
                                port,
                                operation == crate::types::OperationId::new(operation.owner(), 1),
                                budget,
                            )?);
                    }
                    let operands = cell_operands.as_ref().ok_or(Failure::Invalid)?;
                    let Frame::Resource {
                        code,
                        value_context,
                        ..
                    } = edge.frame
                    else {
                        return Err(Failure::Invalid);
                    };
                    let occurrence = ProviderResourceOccurrence {
                        code,
                        value_context,
                    };
                    let mut possible = false;
                    let mut outward = false;
                    for (targets, _) in operands {
                        for target in targets {
                            charge(budget, state.cells.len() + 1)?;
                            let matches = state
                                .cells
                                .iter()
                                .any(|cell| cell.occurrence == occurrence && cell.owner == *target);
                            possible |= matches;
                            outward |= !matches;
                        }
                    }
                    // Label matching may conservatively equate distinct rigid
                    // owner variables. Actual access targets select the live
                    // builtin occurrence; every other possible target continues
                    // outward. Empty operands await the value-queue replay.
                    (relation.0 && possible, relation.1 || outward)
                } else if self.is_cell_handler(edge.frame)
                    && let Control::Request(request) = &self.graph.code[event.code]
                    && let Some(operation) = request.operation
                    && operation.owner().module().is_builtin_resource()
                {
                    let (Frame::Handler { value_context, .. }
                    | Frame::RemovedHandler { value_context, .. }) = edge.frame
                    else {
                        return Err(Failure::Invalid);
                    };
                    let data = self.data.as_mut().ok_or(Failure::Invalid)?;
                    if let Some(owners) = data.handler_cell_owners(code, value_context, budget)? {
                        if cell_operands.is_none() {
                            cell_operands = Some(data.cell_operands(
                                event.port.ok_or(Failure::Invalid)?,
                                operation == crate::types::OperationId::new(operation.owner(), 1),
                                budget,
                            )?);
                        }
                        let mut possible = false;
                        let mut outward = false;
                        for (targets, _) in cell_operands.as_ref().ok_or(Failure::Invalid)? {
                            for target in targets {
                                charge(budget, owners.len() + 1)?;
                                let matches = owners.contains(target);
                                possible |= matches;
                                outward |= !matches;
                            }
                        }
                        (relation.0 && possible, relation.1 || outward)
                    } else {
                        relation
                    }
                } else {
                    relation
                };
                matching.try_reserve(1).map_err(|_| Failure::Resource)?;
                matching.insert(self.boundary_match_key(edge.frame), relation);
            }
        }
        selections(
            state,
            root,
            |frame| {
                Ok(match frame {
                    Frame::Handler { .. }
                    | Frame::Resource { .. }
                    | Frame::RemovedHandler { .. }
                    | Frame::NativeInterpret { .. } => matching[&self.boundary_match_key(frame)],
                    _ => (false, true),
                })
            },
            budget,
        )
    }

    fn requested_continuations(
        &mut self,
        state: &State,
        event: Event,
        boundaries: (Vec<Selection>, bool),
        pending: &mut VecDeque<State>,
        visited: &mut HashSet<State>,
        budget: &mut TypeWorkBudget,
    ) -> Result<(), Failure> {
        let (selected, escaped) = boundaries;
        if escaped {
            self.requested_escape(state, event, pending, visited, budget)?;
        }
        for selected in selected {
            if matches!(selected.boundary.frame, Frame::NativeInterpret { .. }) {
                self.check_payload(state, event, &selected.prefix, budget)?;
                if let (Some(data), Some(port)) = (&mut self.data, event.port) {
                    data.external_result(port, budget)?;
                }
                self.returned(state.copy(budget)?, pending, visited, budget)?;
                continue;
            }
            if let Frame::RemovedHandler { code, .. } = selected.boundary.frame {
                if self.infer_cleanup_rows && !self.authenticate_actual_captures {
                    self.returned(state.copy(budget)?, pending, visited, budget)?;
                    continue;
                }
                let Control::Handler { effect, .. } = &self.graph.code[code] else {
                    return Err(Failure::Invalid);
                };
                let Some((discard, _)) = state.abandoned else {
                    return Err(Failure::Invalid);
                };
                let Control::Discard { source, .. } = self.graph.code[discard] else {
                    return Err(Failure::Invalid);
                };
                let action = selected
                    .prefix
                    .iter()
                    .find_map(|edge| match edge.frame {
                        Frame::Cleanup {
                            code,
                            running: true,
                            ..
                        } => match self.graph.code[code] {
                            Control::Cleanup { source, .. } => Some(source),
                            _ => None,
                        },
                        _ => None,
                    })
                    .unwrap_or(self.source(event));
                return Err(Failure::CleanupContext {
                    discard: source,
                    action,
                    handler: effect.source,
                });
            }
            if matches!(selected.boundary.frame, Frame::Resource { .. }) {
                self.requested_native(state, event, &selected, pending, visited, budget)?;
                continue;
            }
            self.check_payload(state, event, &selected.prefix, budget)?;
            let Frame::Handler { code: handler, .. } = selected.boundary.frame else {
                return Err(Failure::Invalid);
            };
            let Control::Handler { clauses, .. } = &self.graph.code[handler] else {
                return Err(Failure::Invalid);
            };
            for (ordinal, clause) in clauses.iter().enumerate() {
                charge(budget, 1)?;
                if let Control::Request(request) = &self.graph.code[event.code]
                    && request.operation.is_some()
                    && clause.operation.is_some()
                    && request.operation != clause.operation
                {
                    continue;
                }
                self.requested_clause(
                    state,
                    event,
                    (&selected, ordinal),
                    pending,
                    visited,
                    budget,
                )?;
            }
        }
        Ok(())
    }

    #[inline(never)]
    fn requested_escape(
        &mut self,
        state: &State,
        event: Event,
        pending: &mut VecDeque<State>,
        visited: &mut HashSet<State>,
        budget: &mut TypeWorkBudget,
    ) -> Result<(), Failure> {
        if let (Some(data), Some(port)) = (&mut self.data, event.port) {
            data.external_result(port, budget)?;
        }
        // Escaping payload checks consume every owner boundary, but no captured
        // prefix. Keep the identical charged forward walk without reconstructing
        // unused per-owner backward paths.
        let (owners, _, _) = selection_boundaries(
            state,
            state.stack,
            |frame| Ok((matches!(frame, Frame::Resource { .. }), true)),
            budget,
        )?;
        for owner in owners {
            self.check_payload(state, event, &[owner], budget)?;
        }
        if event.unknown {
            Self::enqueue(state.copy(budget)?, pending, visited, budget)?;
        } else {
            self.returned(state.copy(budget)?, pending, visited, budget)?;
        }
        Ok(())
    }

    fn is_cell(&self, frame: Frame) -> bool {
        matches!(frame, Frame::Resource { code, .. }
            if matches!(&self.graph.code[code], Control::Resource { effect, .. }
                if effect.effect.as_ref().is_some_and(|instance| instance.effect().module().is_builtin_resource())))
    }

    fn cell_enclosing(
        &mut self,
        state: &State,
        stack: Address,
        budget: &mut TypeWorkBudget,
    ) -> Result<Vec<(usize, usize)>, Failure> {
        let mut enclosing = Vec::new();
        for edge in &state.heap {
            charge(budget, 1)?;
            let Frame::Resource {
                code,
                value_context,
                ..
            } = edge.frame
            else {
                continue;
            };
            let (_, absent) = selections(
                state,
                stack,
                |frame| {
                    let selected = matches!(frame, Frame::Resource { code: other, value_context: context, .. }
                    if code == other && value_context == context);
                    Ok((selected, !selected))
                },
                budget,
            )?;
            if !absent && let Some(data) = &mut self.data {
                let occurrence = ProviderResourceOccurrence {
                    code,
                    value_context,
                };
                charge(budget, state.cells.len())?;
                let owners = if let Some(cell) = state
                    .cells
                    .iter()
                    .find(|cell| cell.occurrence == occurrence)
                {
                    copy_slice(&[cell.owner], budget)?
                } else {
                    data.cell_owner(code, value_context, budget)?
                };
                charge(budget, owners.len())?;
                enclosing
                    .try_reserve(owners.len())
                    .map_err(|_| Failure::Resource)?;
                enclosing.extend(owners);
            }
        }
        Ok(enclosing)
    }

    fn record_cell_retention(
        &mut self,
        site: CellRetentionSite,
        enclosing: &[(usize, usize)],
        predecessors: &[usize],
        budget: &mut TypeWorkBudget,
    ) -> Result<(), Failure> {
        let CellRetentionSite {
            target,
            request,
            root,
            source,
            acquisition,
        } = site;
        // Normal discovery supplies candidate entries and current contents,
        // never an ownership proof. Each designated query checks its target;
        // obligations for other targets belong to their own focused queries.
        if self
            .data
            .as_ref()
            .and_then(super::value::Analysis::cell_focus)
            != Some(target)
        {
            return Ok(());
        }
        let enclosing = copy_slice(enclosing, budget)?;
        let predecessors = copy_slice(predecessors, budget)?;
        charge(budget, 1)?;
        self.cell_retentions
            .try_reserve(1)
            .map_err(|_| Failure::Resource)?;
        self.cell_retentions.push(CellRetention {
            target,
            request,
            root,
            enclosing,
            predecessors,
            source,
            acquisition,
        });
        Ok(())
    }

    fn initialize_cell(
        &mut self,
        state: &mut State,
        code: usize,
        budget: &mut TypeWorkBudget,
    ) -> Result<(), Failure> {
        let occurrence = ProviderResourceOccurrence {
            code,
            value_context: state.value_context,
        };
        let frame = Frame::Resource {
            code,
            value_context: state.value_context,
            context: state.context,
            focused: false,
        };
        if !self.is_cell(frame) {
            return Ok(());
        }
        let Control::Resource { effect, .. } = &self.graph.code[code] else {
            return Err(Failure::Invalid);
        };
        let source = effect.source;
        let (owner, root) = self
            .data
            .as_mut()
            .ok_or(Failure::Invalid)?
            .cell_initializer(code, state.value_context, budget)?;
        let enclosing = self.cell_enclosing(state, state.stack, budget)?;
        let predecessors = self
            .data
            .as_ref()
            .ok_or(Failure::Invalid)?
            .cell_predecessors(code, state.value_context, budget)?;
        let initializer_source = self
            .data
            .as_ref()
            .ok_or(Failure::Invalid)?
            .cell_initializer_source(code, budget)?;
        self.record_cell_retention(
            CellRetentionSite {
                target: owner,
                request: None,
                root,
                source: initializer_source,
                acquisition: source,
            },
            &enclosing,
            &predecessors,
            budget,
        )?;
        charge(budget, state.cells.len() + 1)?;
        if let Some(cell) = state
            .cells
            .iter_mut()
            .find(|cell| cell.occurrence == occurrence)
        {
            cell.intersect_birth(&enclosing, &predecessors, budget)?;
            cell.shared = true;
            cell.insert_root(root, budget)?;
        } else {
            state.cells.try_reserve(1).map_err(|_| Failure::Resource)?;
            state.cells.push(CellContents {
                occurrence,
                owner,
                roots: copy_slice(&[root], budget)?,
                enclosing: share_cell_birth_slice(enclosing, budget)?,
                predecessors: share_cell_birth_slice(predecessors, budget)?,
                shared: false,
            });
        }
        if !self.focusing {
            charge(budget, 1)?;
            self.candidates
                .try_reserve(1)
                .map_err(|_| Failure::Resource)?;
            self.candidates.insert(owner);
        }
        Ok(())
    }

    fn requested_cell(
        &mut self,
        state: &State,
        event: Event,
        selected: &Selection,
        pending: &mut VecDeque<State>,
        visited: &mut HashSet<State>,
        budget: &mut TypeWorkBudget,
    ) -> Result<(), Failure> {
        let Frame::Resource {
            code,
            value_context,
            ..
        } = selected.boundary.frame
        else {
            return Err(Failure::Invalid);
        };
        let occurrence = ProviderResourceOccurrence {
            code,
            value_context,
        };
        let Control::Resource { effect, .. } = &self.graph.code[code] else {
            return Err(Failure::Invalid);
        };
        let acquisition = effect.source;
        // Labels intern exact effect instances and intentionally erase operation
        // identity. Only the original request selects read versus write.
        let Control::Request(request) = &self.graph.code[event.code] else {
            return Err(Failure::Invalid);
        };
        let operation = request.operation.ok_or(Failure::Invalid)?;
        let source = request.source;
        let api = crate::resolved::ResourceApi::for_module(operation.owner().module())
            .ok_or(Failure::Invalid)?;
        let write = operation == crate::types::OperationId::new(api.ops(), 1);
        if !write && operation != crate::types::OperationId::new(api.ops(), 0) {
            return Err(Failure::Invalid);
        }
        let request = event.port.ok_or(Failure::Invalid)?;
        let operands = self
            .data
            .as_mut()
            .ok_or(Failure::Invalid)?
            .cell_operands(request, write, budget)?;
        for (targets, replacement) in operands {
            for owner in targets {
                charge(budget, state.cells.len() + 1)?;
                let Some(index) = state
                    .cells
                    .iter()
                    .position(|cell| cell.occurrence == occurrence && cell.owner == owner)
                else {
                    // This alternative belongs to another builtin occurrence;
                    // boundary selection retained its independent outward path.
                    continue;
                };
                let mut next = state.copy(budget)?;
                if let Some(root) = replacement {
                    self.record_cell_retention(
                        CellRetentionSite {
                            target: owner,
                            request: Some(request),
                            root,
                            source,
                            acquisition,
                        },
                        &state.cells[index].enclosing,
                        &state.cells[index].predecessors,
                        budget,
                    )?;
                    if !next.cells[index].shared {
                        next.cells[index].roots.clear();
                    }
                    next.cells[index].insert_root(root, budget)?;
                    self.data
                        .as_mut()
                        .ok_or(Failure::Invalid)?
                        .external_result(request, budget)?;
                } else {
                    for root in &state.cells[index].roots {
                        charge(budget, 1)?;
                        self.data
                            .as_mut()
                            .ok_or(Failure::Invalid)?
                            .cell_read(request, *root, budget)?;
                    }
                }
                self.returned(next, pending, visited, budget)?;
            }
        }
        Ok(())
    }

    fn check_cell_retentions(&mut self, budget: &mut TypeWorkBudget) -> Result<(), Failure> {
        let Some(data) = &mut self.data else {
            return Ok(());
        };
        // Symbolic recurring occurrences cannot prove strict ownership. Every
        // actual acquisition entry is checked with its fresh designated marker.
        let Some(focus) = data.cell_focus() else {
            return Ok(());
        };
        for retention in &self.cell_retentions {
            charge(budget, 1)?;
            if retention.target != focus {
                continue;
            }
            if let Err(mut failure) = data.cell_retention(
                retention.root,
                &retention.enclosing,
                &retention.predecessors,
                (retention.source, retention.acquisition),
                budget,
            ) {
                if let Failure::Dependency { source, causes, .. } = &mut failure
                    && let Some(request) = retention.request
                {
                    (*source, causes[1]) =
                        data.cell_request_site(request, *source, retention.acquisition, budget)?;
                }
                return Err(failure);
            }
        }
        Ok(())
    }

    #[inline(never)]
    fn requested_native(
        &mut self,
        state: &State,
        event: Event,
        selected: &Selection,
        pending: &mut VecDeque<State>,
        visited: &mut HashSet<State>,
        budget: &mut TypeWorkBudget,
    ) -> Result<(), Failure> {
        if self.is_cell(selected.boundary.frame) {
            return self.requested_cell(state, event, selected, pending, visited, budget);
        }
        if let (Some(data), Some(port)) = (&mut self.data, event.port) {
            data.external_result(port, budget)?;
        }
        // The trusted interpreter completes this operation without
        // transferring its operand outside the owning scope.
        self.returned(state.copy(budget)?, pending, visited, budget)?;
        Ok(())
    }

    #[inline(never)]
    fn requested_clause(
        &mut self,
        state: &State,
        event: Event,
        clause: (&Selection, usize),
        pending: &mut VecDeque<State>,
        visited: &mut HashSet<State>,
        budget: &mut TypeWorkBudget,
    ) -> Result<(), Failure> {
        let (selected, ordinal) = clause;
        let Frame::Handler {
            code: handler,
            context,
            value_context,
            capture_context,
            ..
        } = selected.boundary.frame
        else {
            return Err(Failure::Invalid);
        };
        let Control::Handler { clauses, .. } = &self.graph.code[handler] else {
            return Err(Failure::Invalid);
        };
        let clause = clauses.get(ordinal).ok_or(Failure::Invalid)?;
        let clause_context = if let (Some(data), Some(port)) = (&mut self.data, event.port) {
            data.dispatch(
                port,
                handler,
                ordinal,
                capture_context,
                value_context,
                budget,
            )?
        } else {
            value_context
        };
        let mut next = state.copy(budget)?;
        next.stack = selected.boundary.next;
        let mut prefix = copy_slice(&selected.prefix, budget)?;
        // An opaque request resumes at the same call position.
        let root = if event.unknown {
            let position = Position {
                code: event.code,
                next: 0,
            };
            let address = Address::Slot {
                region: Region::Active,
                site: Site::Next(position),
                allocation_context: state.value_context,
                old: false,
            };
            prefix.try_reserve(1).map_err(|_| Failure::Resource)?;
            prefix.push(Edge {
                address,
                frame: Frame::Next {
                    position,
                    context: state.context,
                    value_context: state.value_context,
                },
                next: state.stack,
            });
            address
        } else {
            state.stack
        };
        let capture = next.copy_segment(
            root,
            &prefix,
            Some(selected.boundary),
            Address::End,
            Region::Capture(handler, event.code),
            budget,
        )?;
        next.push(
            Frame::Clause {
                handler,
                ordinal,
                owner: clause.owner,
                context,
                value_context,
                capture,
                capture_context,
                clause_context,
                event,
                consumed: false,
            },
            budget,
        )?;
        next.context = context;
        next.value_context = clause_context;
        next.position = Position {
            code: clause.body,
            next: 0,
        };
        Self::enqueue(next, pending, visited, budget)?;
        Ok(())
    }

    fn record_cleanup_row(
        &mut self,
        state: &State,
        outer: Address,
        code: usize,
        context: usize,
        discard: usize,
        budget: &mut TypeWorkBudget,
    ) -> Result<(), Failure> {
        if !self.infer_cleanup_rows && !self.collect_cleanup_rows {
            return Ok(());
        }
        let Control::Cleanup { row_type, .. } = self.graph.code[code] else {
            return Err(Failure::Invalid);
        };
        let Control::Discard {
            node,
            local,
            source,
            row_type: discard_row_type,
            ..
        } = self.graph.code[discard]
        else {
            return Err(Failure::Invalid);
        };
        let mut holder = TypeArguments(Vec::new());
        holder.0.try_reserve(1).map_err(|_| Failure::Resource)?;
        holder
            .0
            .push(self.substitute(&self.graph.types.0[row_type], context, budget)?);
        let row = match holder.0[0]
            .function_view()
            .and_then(|function| function.effects())
        {
            Some(row) => {
                clone_effect_row_with_budget(row, budget).map_err(|_| Failure::Resource)?
            }
            None => EffectRow::empty(),
        };
        let (resources, _) = selections(
            state,
            outer,
            |frame| {
                Ok((
                    matches!(frame, Frame::Resource { .. }),
                    !matches!(
                        frame,
                        Frame::Closing {
                            site: Site::Closing(_, _),
                            ..
                        }
                    ),
                ))
            },
            budget,
        )?;
        let mut retained = Vec::new();
        let mut discard_context = None;
        let mut requests = Vec::new();
        let (drivers, _) = selections(
            state,
            outer,
            |frame| {
                let selected = matches!(frame, Frame::Closing { site: Site::Closing(owner, false), .. } if owner == discard);
                Ok((selected, !selected))
            },
            budget,
        )?;
        for driver in drivers {
            let Frame::Closing {
                context,
                value_context,
                event,
                ..
            } = driver.boundary.frame
            else {
                return Err(Failure::Invalid);
            };
            if discard_context.is_some_and(|previous| previous != context) {
                return Err(Failure::Invalid);
            }
            discard_context = Some(context);
            let request = super::ActualRequestContext {
                code: event.code,
                label: event.label,
                port: event.port,
                value_context,
            };
            charge(
                budget,
                requests.len().checked_add(1).ok_or(Failure::Resource)?,
            )?;
            if !requests.contains(&request) {
                requests.try_reserve(1).map_err(|_| Failure::Resource)?;
                requests.push(request);
            }
        }
        let discard_context = discard_context.ok_or(Failure::Invalid)?;
        charge(budget, 1)?;
        holder.0.try_reserve(1).map_err(|_| Failure::Resource)?;
        holder.0.push(self.substitute(
            &self.graph.types.0[discard_row_type],
            discard_context,
            budget,
        )?);
        let expected = match holder.0[1]
            .function_view()
            .and_then(|function| function.effects())
        {
            Some(row) => {
                clone_effect_row_with_budget(row, budget).map_err(|_| Failure::Resource)?
            }
            None => EffectRow::empty(),
        };
        let count = resources.len();
        charge(budget, count.checked_add(1).ok_or(Failure::Resource)?)?;
        retained.try_reserve(count).map_err(|_| Failure::Resource)?;
        for resource in resources {
            let Frame::Resource { code, context, .. } = resource.boundary.frame else {
                return Err(Failure::Invalid);
            };
            let label = self.label(code, context, budget)?;
            if let Some(effect) = &self.labels[label].effect {
                retained.push(
                    crate::core::effect::clone_effect_instance_with_budget(effect, budget)
                        .map_err(|_| Failure::Resource)?,
                );
            }
        }
        charge(budget, requests.len())?;
        self.cleanup_rows
            .try_reserve(requests.len())
            .map_err(|_| Failure::Resource)?;
        for _request in requests {
            let mut retained_copy = Vec::new();
            charge(budget, retained.len())?;
            retained_copy
                .try_reserve_exact(retained.len())
                .map_err(|_| Failure::Resource)?;
            for effect in &retained {
                retained_copy.push(
                    crate::core::effect::clone_effect_instance_with_budget(effect, budget)
                        .map_err(|_| Failure::Resource)?,
                );
            }
            self.cleanup_rows.push(super::CleanupRequirement {
                discard: node,
                local,
                code: discard,
                source,
                context: discard_context,
                #[cfg(test)]
                request: _request,
                expected: clone_effect_row_with_budget(&expected, budget)
                    .map_err(|_| Failure::Resource)?,
                row: clone_effect_row_with_budget(&row, budget).map_err(|_| Failure::Resource)?,
                retained: retained_copy,
            });
        }
        Ok(())
    }

    fn close_segment(
        &self,
        source: &State,
        target: &mut State,
        root: Address,
        discard: usize,
        event: Event,
        budget: &mut TypeWorkBudget,
    ) -> Result<(), Failure> {
        let mut pending = Vec::new();
        let mut seen = HashSet::new();
        let mut edges = Vec::new();
        pending.try_reserve(1).map_err(|_| Failure::Resource)?;
        pending.push(root);
        while let Some(address) = pending.pop() {
            charge(budget, 1)?;
            if matches!(address, Address::End | Address::Empty) || seen.contains(&address) {
                continue;
            }
            seen.try_reserve(1).map_err(|_| Failure::Resource)?;
            seen.insert(address);
            for edge in source.edges(address, budget)? {
                let mut edge = *edge;
                let site = edge.frame.site();
                edge.frame = match edge.frame {
                    Frame::RetainedRoot { .. }
                        if !self.infer_cleanup_rows || self.authenticate_actual_captures =>
                    {
                        // Source discard cannot retire unfinished private work.
                        return Err(self.unsafe_discard(discard, event, None));
                    }
                    Frame::Cleanup {
                        code,
                        running: true,
                        ..
                    } if !self.infer_cleanup_rows || self.authenticate_actual_captures => {
                        let Control::Cleanup { source, .. } = self.graph.code[code] else {
                            return Err(Failure::Invalid);
                        };
                        return Err(self.unsafe_discard(
                            discard,
                            event,
                            Some(CompletionOwner::Cleanup(source)),
                        ));
                    }
                    Frame::Closing { .. }
                        if !self.infer_cleanup_rows || self.authenticate_actual_captures =>
                    {
                        return Err(self.unsafe_discard(discard, event, None));
                    }
                    Frame::Cleanup {
                        code,
                        context,
                        value_context,
                        running: false,
                        ..
                    } => Frame::Cleanup {
                        code,
                        context,
                        value_context,
                        running: false,
                        closing: Some(discard),
                    },
                    frame @ Frame::Handler { code, .. } if matches!(&self.graph.code[code], Control::Handler { effect, .. } if effect.region_service) => {
                        frame
                    }
                    Frame::Handler {
                        code,
                        context,
                        value_context,
                        ..
                    } => Frame::RemovedHandler {
                        code,
                        context,
                        value_context,
                    },
                    Frame::Next {
                        context,
                        value_context,
                        ..
                    }
                    | Frame::Clause {
                        context,
                        value_context,
                        consumed: true,
                        ..
                    } => Frame::Closing {
                        code: discard,
                        site,
                        context,
                        value_context,
                        capture: None,
                        event,
                    },
                    Frame::Clause {
                        context,
                        value_context,
                        capture,
                        ..
                    } => Frame::Closing {
                        code: discard,
                        site,
                        context,
                        value_context,
                        capture: Some(capture),
                        event,
                    },
                    frame => frame,
                };
                edges.try_reserve(1).map_err(|_| Failure::Resource)?;
                edges.push(edge);
                pending.try_reserve(1).map_err(|_| Failure::Resource)?;
                pending.push(edge.next);
            }
        }
        target.stack = target.copy_segment(
            root,
            &edges,
            None,
            target.stack,
            Region::Closing(discard, event.code),
            budget,
        )?;
        Ok(())
    }

    fn completed(
        &mut self,
        state: State,
        owner: usize,
        completion: Completion,
        pending: &mut VecDeque<State>,
        visited: &mut HashSet<State>,
        budget: &mut TypeWorkBudget,
    ) -> Result<(), Failure> {
        let resume = matches!(completion, Completion::Resume);
        let discard = matches!(completion, Completion::Discard);
        let retain = matches!(completion, Completion::Retain);
        let (selected, escaped) = selections(
            &state,
            state.stack,
            |frame| {
                Ok(match frame {
                    Frame::Clause {
                        owner: candidate, ..
                    } if candidate == owner => (true, false),
                    Frame::Clause { .. } if retain => (false, false),
                    _ => (false, true),
                })
            },
            budget,
        )?;
        if escaped || (retain && selected.is_empty()) {
            return Err(Failure::Invalid);
        }
        for mut selected in selected {
            let Frame::Clause {
                capture,
                event,
                consumed,
                handler,
                value_context,
                ..
            } = selected.boundary.frame
            else {
                return Err(Failure::Invalid);
            };
            if consumed {
                return Err(Failure::Invalid);
            }
            if resume && let (Some(data), Some(port)) = (&mut self.data, event.port) {
                data.resume(
                    port,
                    state.position.code,
                    state.value_context,
                    handler,
                    value_context,
                    budget,
                )?;
            }
            if discard
                && event.unknown
                && (!self.infer_cleanup_rows || self.authenticate_actual_captures)
            {
                return Err(self.unsafe_discard(state.position.code, event, None));
            }
            if discard && self.authenticate_actual_captures {
                let label = self.labels.get(event.label).ok_or(Failure::Invalid)?;
                if event.unknown
                    || label.ambiguous_instance
                    || label.effect.is_none()
                    || event.port.is_none()
                {
                    return Err(self.unsafe_discard(state.position.code, event, None));
                }
                let occurrence = super::ActualDiscardCapture {
                    code: state.position.code,
                    context: state.context,
                    request: super::ActualRequestContext {
                        code: event.code,
                        label: event.label,
                        port: event.port,
                        value_context: state.value_context,
                    },
                };
                charge(
                    budget,
                    self.actual_captures
                        .len()
                        .checked_add(1)
                        .ok_or(Failure::Resource)?,
                )?;
                if !self.actual_captures.contains(&occurrence) {
                    self.actual_captures
                        .try_reserve(1)
                        .map_err(|_| Failure::Resource)?;
                    self.actual_captures.push(occurrence);
                }
            }
            let retained_root = if retain {
                if !matches!(selected.boundary.address, Address::Slot { old: false, .. }) {
                    return Err(Failure::Invalid);
                }
                let (roots, escaped) = selections(
                    &state,
                    selected.boundary.next,
                    |frame| {
                        Ok(match frame {
                            Frame::RetainedRoot { .. } => (true, false),
                            _ => (false, true),
                        })
                    },
                    budget,
                )?;
                let [root] = roots.as_slice() else {
                    return Err(Failure::Invalid);
                };
                if escaped {
                    return Err(Failure::Invalid);
                }
                let Frame::RetainedRoot {
                    code,
                    context,
                    value_context,
                    store,
                    baseline,
                } = root.boundary.frame
                else {
                    return Err(Failure::Invalid);
                };
                if !matches!(self.graph.code[code], Control::RetainedRoot { body, .. } if body == handler)
                {
                    return Err(Failure::Invalid);
                }
                self.check_retained_capture(&state, capture, store, budget)?;
                self.record_retained_support(
                    &state,
                    capture,
                    store,
                    baseline,
                    state.position.code,
                    budget,
                )?;
                Some((store, baseline, code, context, value_context))
            } else {
                None
            };
            let mut next = state.copy(budget)?;
            // Replacing this occurrence does not mutate an older activation
            // sharing the static owner identity.
            if let Frame::Clause {
                consumed, capture, ..
            } = &mut selected.boundary.frame
            {
                *consumed = true;
                *capture = Address::End;
            }
            let last = selected.prefix.last_mut().ok_or(Failure::Invalid)?;
            *last = selected.boundary;
            let continuation = if resume && selected.prefix.len() == 1 {
                // Tail resume has no remaining clause computation. Its
                // consumed owner is an empty return step, not an outside
                // completion obligation. Keep the captured owners intact.
                selected.boundary.next
            } else if matches!(selected.boundary.address, Address::Slot { old: false, .. }) {
                // A recent address denotes one occurrence. Consuming it is
                // a move, not a fresh allocation of all its ordinary frames.
                let address = Address::Slot {
                    region: Region::Active,
                    site: selected.boundary.frame.site(),
                    allocation_context: match selected.boundary.address {
                        Address::Slot {
                            allocation_context, ..
                        } => allocation_context,
                        _ => return Err(Failure::Invalid),
                    },
                    old: false,
                };
                let mut rename = HashMap::new();
                rename.try_reserve(1).map_err(|_| Failure::Resource)?;
                rename.insert(address, address.older());
                next.rename(&rename, budget)?;
                let mut rename_owner = HashMap::new();
                rename_owner.try_reserve(1).map_err(|_| Failure::Resource)?;
                rename_owner.insert(selected.boundary.address, address);
                charge(budget, next.heap.len())?;
                for edge in &mut next.heap {
                    if edge.address == selected.boundary.address {
                        edge.frame = selected.boundary.frame;
                    }
                }
                next.rename(&rename_owner, budget)?;
                next.stack
            } else {
                next.copy_segment(
                    state.stack,
                    &selected.prefix,
                    Some(selected.boundary),
                    selected.boundary.next,
                    // The rebound older prefix must not retain the live
                    // original prefix's tail. Repeated completions at this
                    // fixed site still join conservatively within a region.
                    Region::Completion(state.position.code, owner),
                    budget,
                )?
            };
            next.stack = continuation;
            if resume {
                // The capture reference may have been aged by copying the
                // active prefix; the copied clause's old capture is immutable.
                let mut captured = Vec::new();
                let mut todo = Vec::new();
                let mut seen = HashSet::new();
                todo.try_reserve(1).map_err(|_| Failure::Resource)?;
                todo.push(capture);
                while let Some(address) = todo.pop() {
                    if address == Address::End || seen.contains(&address) {
                        continue;
                    }
                    seen.try_reserve(1).map_err(|_| Failure::Resource)?;
                    seen.insert(address);
                    for edge in state.edges(address, budget)? {
                        captured.try_reserve(1).map_err(|_| Failure::Resource)?;
                        captured.push(*edge);
                        todo.try_reserve(1).map_err(|_| Failure::Resource)?;
                        todo.push(edge.next);
                    }
                }
                next.stack = next.copy_segment(
                    capture,
                    &captured,
                    None,
                    continuation,
                    Region::Active,
                    budget,
                )?;
            } else if discard {
                next.abandoned = Some((state.position.code, event));
                next.push(
                    Frame::Closing {
                        code: state.position.code,
                        site: Site::Closing(state.position.code, false),
                        context: state.context,
                        value_context: state.value_context,
                        capture: None,
                        event,
                    },
                    budget,
                )?;
                self.close_segment(
                    &state,
                    &mut next,
                    capture,
                    state.position.code,
                    event,
                    budget,
                )?;
            } else {
                let (store, baseline, root, root_context, root_value_context) =
                    retained_root.ok_or(Failure::Invalid)?;
                charge(budget, 1)?;
                next.retained
                    .try_reserve(1)
                    .map_err(|_| Failure::Resource)?;
                let key = self.data.as_mut().ok_or(Failure::Invalid)?.retained_key(
                    state.position.code,
                    state.value_context,
                    budget,
                )?;
                next.retained.push(RetainedCapture {
                    store,
                    key,
                    capture: Some(capture),
                    baseline,
                    root,
                    root_context,
                    root_value_context,
                    handler,
                    handler_context: value_context,
                    event,
                });
            }
            next.position = Position { code: 0, next: 0 };
            Self::enqueue(next, pending, visited, budget)?;
        }
        Ok(())
    }

    fn check_payload(
        &mut self,
        _state: &State,
        event: Event,
        crossed: &[Edge],
        budget: &mut TypeWorkBudget,
    ) -> Result<(), Failure> {
        if let (Some(_), Some(port)) = (&mut self.data, event.port) {
            for edge in crossed {
                charge(budget, 1)?;
                if let Frame::Resource {
                    code,
                    value_context,
                    focused,
                    ..
                } = edge.frame
                {
                    if self.focusing && !focused {
                        continue;
                    }
                    let payload = (port, code, value_context);
                    charge(budget, self.payloads.len() + 1)?;
                    if !self.payloads.contains(&payload) {
                        self.payloads
                            .try_reserve(1)
                            .map_err(|_| Failure::Resource)?;
                        self.payloads.push(payload);
                    }
                }
            }
            return Ok(());
        }
        for edge in crossed {
            charge(budget, 1)?;
            if matches!(edge.frame, Frame::Resource { .. }) {
                return Err(Failure::Invalid);
            }
        }
        Ok(())
    }

    fn check_payloads(&mut self, budget: &mut TypeWorkBudget) -> Result<(), Failure> {
        let Some(data) = &mut self.data else {
            return Ok(());
        };
        for &(port, code, context) in &self.payloads {
            charge(budget, 1)?;
            if let Err(failure) = data.check_payload(port, code, context, budget) {
                if !self.focusing && matches!(failure, Failure::Escape { .. }) {
                    let candidate = data.resource_key(code, context, budget)?;
                    charge(budget, 1)?;
                    self.candidates
                        .try_reserve(1)
                        .map_err(|_| Failure::Resource)?;
                    self.candidates.insert(candidate);
                } else {
                    if self.focusing
                        && matches!(&self.graph.code[code], Control::Resource { effect, .. }
                        if effect.effect.as_ref().is_some_and(|instance| instance.effect().module().is_builtin_resource()))
                    {
                        return Err(data.cell_escape_failure(
                            failure,
                            Some(port),
                            code,
                            context,
                            budget,
                        )?);
                    }
                    return Err(failure);
                }
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn retained_existing_slot_replays_its_request_and_handler_in_the_focused_context() {
        use super::super::tests::{RetainedContextFixture, retained_context_core};
        use crate::core::effect::{EffectExprKind, EffectOperationFamily};
        fn operation(kind: &EffectExprKind) -> Option<&crate::core::effect::EffectOperation> {
            match kind {
                EffectExprKind::Operation(operation) => Some(operation),
                _ => None,
            }
        }
        let core = retained_context_core(RetainedContextFixture::PreexistingSlot).unwrap();
        let mut work = TypeWorkBudget::with_limit(3 * crate::types::TYPE_WORK_LIMIT);
        let built = super::super::build_capture_graph::<EffectOperationFamily>(
            &core.nodes,
            &[],
            &[],
            operation,
            &[],
            &[],
            None,
            &mut work,
        )
        .unwrap()
        .unwrap();
        let mut analysis = Analysis::new(&built.graph, None, &mut work).unwrap();
        analysis.discover(&built.roots, None, &mut work).unwrap();
        let entry = analysis.entries.iter().find(|entry| {
            entry.retained.iter().any(|slot| slot.capture.is_some())
                && matches!(&built.graph.code[entry.position.code], Control::Resource { effect, .. }
                    if effect.effect.as_ref().is_some_and(|effect| effect.effect().module().is_builtin_resource()))
        }).expect("the Cell starts while the Store owns a live slot").copy(&mut work).unwrap();
        let normal = analysis.data.take().unwrap();
        let (query, context) = normal
            .focused(entry.position.code, entry.value_context, &mut work)
            .unwrap();
        analysis.data = Some(query);
        let restored = analysis.restore_entry(&entry, context, &mut work).unwrap();
        let (old, slot) = entry
            .retained
            .iter()
            .zip(&restored.retained)
            .find(|(old, _)| old.capture.is_some())
            .unwrap();
        assert_ne!(
            slot.event.port, old.event.port,
            "the request result must be restored"
        );
        assert_ne!(
            slot.root_value_context, old.root_value_context,
            "the root must use its restored context"
        );
        let (handlers, escaped) = selections(
            &restored,
            slot.capture.unwrap(),
            |frame| {
                let found = matches!(frame, Frame::Handler { code, value_context, .. }
                    if code == slot.handler && value_context == slot.handler_context);
                Ok((found, !found))
            },
            &mut work,
        )
        .unwrap();
        assert!(
            !escaped && handlers.len() == 1,
            "the slot must use its actual captured handler's restored value context"
        );
        let [head] = entry.edges(old.capture.unwrap(), &mut work).unwrap() else {
            panic!("the source fixture has one captured entry")
        };
        let Frame::Next {
            position,
            value_context,
            ..
        } = head.frame
        else {
            panic!("the checkpoint is inside the fixture's saved sequence")
        };
        let data = analysis.data.as_ref().unwrap();
        let input = data
            .restored_cut_input_for_test(value_context, position.code, position.next)
            .expect("the captured entry was rebuilt");
        assert!(
            data.has_edge_for_test(input, slot.event.port.unwrap()),
            "the restored checkpoint result must feed the restored captured entry"
        );
    }

    #[test]
    fn retained_store_cut_follows_only_its_live_slot_captures() {
        let address = |site| Address::Slot {
            region: Region::Active,
            site: Site::Resource(site),
            allocation_context: 0,
            old: false,
        };
        let owner = address(1);
        let other = address(2);
        let capture = address(3);
        let event = Event {
            code: 0,
            label: 0,
            unknown: false,
            port: None,
        };
        let retained = |store, capture| RetainedCapture {
            store,
            key: (0, 0),
            capture,
            baseline: Address::End,
            root: 0,
            root_context: 0,
            root_value_context: 0,
            handler: 0,
            handler_context: 0,
            event,
        };
        let state = State {
            position: Position { code: 0, next: 0 },
            context: 0,
            value_context: 0,
            stack: Address::Empty,
            heap: Vec::new(),
            cells: Vec::new(),
            abandoned: None,
            retained: vec![
                retained(owner, Some(capture)),
                retained(owner, None),
                retained(other, Some(address(4))),
            ],
        };
        let mut pending = Vec::new();
        push_store_captures(
            &state,
            owner,
            &mut pending,
            &mut TypeWorkBudget::unbounded(),
        )
        .unwrap();
        assert_eq!(pending, vec![capture]);
    }

    #[test]
    fn generic_cell_copied_birth_intersection_is_atomic_and_keeps_snapshot_roots() {
        let original = State {
            position: Position { code: 0, next: 0 },
            context: 0,
            value_context: 0,
            stack: Address::Empty,
            heap: Vec::new(),
            abandoned: None,
            retained: Vec::new(),
            cells: vec![CellContents {
                occurrence: ProviderResourceOccurrence {
                    code: 1,
                    value_context: 2,
                },
                owner: (3, 4),
                roots: vec![7],
                enclosing: vec![(1, 1), (2, 2)].into(),
                predecessors: vec![11, 13].into(),
                shared: true,
            }],
        };
        let run = |work: &mut TypeWorkBudget| {
            let mut copied = original.copy(&mut TypeWorkBudget::default()).unwrap();
            assert!(Arc::ptr_eq(
                &copied.cells[0].enclosing,
                &original.cells[0].enclosing
            ));
            assert!(Arc::ptr_eq(
                &copied.cells[0].predecessors,
                &original.cells[0].predecessors
            ));
            let result = copied.cells[0].intersect_birth(&[(1, 1)], &[13], work);
            (result, copied)
        };
        let mut measured = TypeWorkBudget::default();
        let (result, mut copied) = run(&mut measured);
        result.unwrap();
        assert_eq!(&*copied.cells[0].enclosing, &[(1, 1)]);
        assert_eq!(&*copied.cells[0].predecessors, &[13]);
        copied.cells[0]
            .insert_root(9, &mut TypeWorkBudget::default())
            .unwrap();
        assert_eq!(copied.cells[0].roots, [7, 9]);
        assert_eq!(original.cells[0].roots, [7]);
        assert_eq!(&*original.cells[0].enclosing, &[(1, 1), (2, 2)]);
        assert_eq!(&*original.cells[0].predecessors, &[11, 13]);
        let (result, refused) = run(&mut TypeWorkBudget::with_limit(measured.used() - 1));
        assert!(matches!(result, Err(Failure::Resource)));
        assert_eq!(
            refused, original,
            "intersection refusal publishes neither replacement slice"
        );
        for _ in 0..2 {
            let mut exact = TypeWorkBudget::with_limit(measured.used());
            let (result, copied) = run(&mut exact);
            result.unwrap();
            assert_eq!(&*copied.cells[0].enclosing, &[(1, 1)]);
            assert_eq!(&*copied.cells[0].predecessors, &[13]);
            assert_eq!(exact.used(), measured.used());
        }
    }

    #[test]
    fn generic_cell_wide_state_replay_hits_pay_complete_keys_and_retry() {
        for width in [0, 1, 64] {
            let make = || State {
                position: Position { code: 0, next: 0 },
                context: 0,
                value_context: 0,
                stack: Address::Empty,
                abandoned: None,
                heap: (0..width)
                    .map(|code| Edge {
                        address: Address::Slot {
                            region: Region::Active,
                            site: Site::Resource(code),
                            allocation_context: code,
                            old: false,
                        },
                        frame: Frame::Resource {
                            code,
                            context: 0,
                            value_context: code,
                            focused: false,
                        },
                        next: Address::Empty,
                    })
                    .collect(),
                retained: Vec::new(),
                cells: vec![CellContents {
                    occurrence: ProviderResourceOccurrence {
                        code: 1,
                        value_context: 2,
                    },
                    owner: (3, 4),
                    roots: (0..width).collect(),
                    enclosing: (0..width)
                        .map(|code| (code, code))
                        .collect::<Vec<_>>()
                        .into(),
                    predecessors: (0..width).collect::<Vec<_>>().into(),
                    shared: true,
                }],
            };
            let state = make();
            let set = HashSet::from([make()]);
            let map = HashMap::from([(make(), 7)]);
            let hit = |work: &mut TypeWorkBudget| -> Result<(), Failure> {
                state.charge_key(work)?;
                assert!(set.contains(&state));
                state.charge_key(work)?;
                assert_eq!(map.get(&state), Some(&7));
                Ok(())
            };
            let mut measured = TypeWorkBudget::default();
            hit(&mut measured).unwrap();
            assert!(measured.used() >= 2 * (5 * width + 5));
            assert!(matches!(
                hit(&mut TypeWorkBudget::with_limit(measured.used() - 1)),
                Err(Failure::Resource)
            ));
            assert_eq!((set.len(), map.len()), (1, 1));
            for _ in 0..2 {
                let mut exact = TypeWorkBudget::with_limit(measured.used());
                hit(&mut exact).unwrap();
                assert_eq!(exact.used(), measured.used());
            }
        }
    }

    #[test]
    fn generic_cell_state_insertion_pays_nested_roots_before_publication() {
        let make = || State {
            position: Position { code: 0, next: 0 },
            context: 0,
            value_context: 0,
            stack: Address::Empty,
            heap: Vec::new(),
            abandoned: None,
            retained: Vec::new(),
            cells: vec![CellContents {
                occurrence: ProviderResourceOccurrence {
                    code: 1,
                    value_context: 2,
                },
                owner: (3, 4),
                roots: (0..64).collect(),
                enclosing: vec![(1, 2)].into(),
                predecessors: (64..96).collect::<Vec<_>>().into(),
                shared: true,
            }],
        };
        let run = |work: &mut TypeWorkBudget| {
            let mut pending = VecDeque::new();
            let mut visited = HashSet::new();
            let result = Analysis::enqueue(make(), &mut pending, &mut visited, work);
            (result, pending.len(), visited.len())
        };
        let mut measured = TypeWorkBudget::default();
        let (result, pending, visited) = run(&mut measured);
        result.unwrap();
        assert_eq!((pending, visited), (1, 1));
        let (result, pending, visited) = run(&mut TypeWorkBudget::with_limit(measured.used() - 1));
        assert!(matches!(result, Err(Failure::Resource)));
        assert_eq!((pending, visited), (0, 0));
        for _ in 0..2 {
            let mut exact = TypeWorkBudget::with_limit(measured.used());
            let (result, pending, visited) = run(&mut exact);
            result.unwrap();
            assert_eq!((pending, visited, exact.used()), (1, 1, measured.used()));
        }
    }

    #[test]
    fn generic_cell_root_join_refusal_preserves_current_roots_and_retries() {
        let make = || super::CellContents {
            occurrence: super::ProviderResourceOccurrence {
                code: 1,
                value_context: 2,
            },
            owner: (3, 4),
            roots: vec![7, 11],
            enclosing: vec![(1, 2)].into(),
            predecessors: vec![5].into(),
            shared: true,
        };
        let mut measured = crate::types::TypeWorkBudget::default();
        let mut joined = make();
        joined.insert_root(9, &mut measured).unwrap();
        assert_eq!(joined.roots, [7, 9, 11]);
        let mut refused = make();
        assert!(
            refused
                .insert_root(
                    9,
                    &mut crate::types::TypeWorkBudget::with_limit(measured.used() - 1)
                )
                .is_err()
        );
        assert_eq!(refused.roots, [7, 11]);
        for _ in 0..2 {
            let mut fresh = make();
            let mut exact = crate::types::TypeWorkBudget::with_limit(measured.used());
            fresh.insert_root(9, &mut exact).unwrap();
            assert_eq!(fresh.roots, joined.roots);
            assert_eq!(exact.used(), measured.used());
        }
    }

    use super::super::CallableSlots;
    use super::*;
    use crate::core::capture::Callable;
    use crate::{
        module::ModuleId,
        source::{ByteRange, SourceFile},
        types::{ComputationType, EffectId, EffectRow},
    };

    #[test]
    fn actual_capture_mode_refuses_unknown_missing_ports_and_nearest_removed_handler() {
        let source = SourceFile::new("actual-c-negative", "x").unwrap();
        let span = source.span(ByteRange::new(0, 1).unwrap()).unwrap();
        let effect = EffectInstance::new(EffectId::new(ModuleId::new(0), 0), Box::new([]));
        let graph = SummaryGraph {
            effects: true,
            data: None,
            callables: CallableSlots::default(),
            types: TypeArguments(vec![Type::function_computation(
                Type::Unit,
                crate::types::ComputationType::new(Type::Unit, EffectRow::empty()),
            )]),
            code: vec![
                Control::Return,
                Control::Handler {
                    body: 0,
                    effect: Request::effect(&effect, span, &mut TypeWorkBudget::unbounded())
                        .unwrap(),
                    clauses: vec![],
                },
                Control::Request(
                    Request::effect(&effect, span, &mut TypeWorkBudget::unbounded()).unwrap(),
                ),
                Control::Discard {
                    owner: 7,
                    node: 3,
                    local: true,
                    row_type: 0,
                    source: span,
                },
            ],
        };
        for (unknown, port) in [(true, Some(0)), (false, None)] {
            let mut budget = TypeWorkBudget::unbounded();
            let mut analysis = Analysis::new(&graph, None, &mut budget).unwrap();
            analysis.infer_cleanup_rows = true;
            analysis.authenticate_actual_captures = true;
            let label = analysis.label(2, 0, &mut budget).unwrap();
            let event = Event {
                code: 2,
                label,
                unknown,
                port,
            };
            let clause = Frame::Clause {
                handler: 1,
                ordinal: 0,
                owner: 7,
                context: 0,
                value_context: 0,
                capture: Address::End,
                capture_context: 0,
                clause_context: 0,
                event,
                consumed: false,
            };
            let address = Address::Slot {
                region: Region::Active,
                site: clause.site(),
                allocation_context: 0,
                old: false,
            };
            let mut state = State {
                position: Position { code: 3, next: 0 },
                context: 0,
                value_context: 0,
                stack: address,
                retained: Vec::new(),
                cells: Vec::new(),
                heap: vec![Edge {
                    address,
                    frame: clause,
                    next: Address::Empty,
                }],
                abandoned: None,
            };
            state.normalize(&mut budget).unwrap();
            assert!(matches!(
                analysis.completed(
                    state,
                    7,
                    Completion::Discard,
                    &mut VecDeque::new(),
                    &mut HashSet::new(),
                    &mut budget
                ),
                Err(Failure::Unsafe(_))
            ));
            assert!(
                analysis.actual_captures.is_empty(),
                "unproved request never contributes an empty c"
            );
        }
        let mut budget = TypeWorkBudget::unbounded();
        let mut analysis = Analysis::new(&graph, None, &mut budget).unwrap();
        analysis.infer_cleanup_rows = true;
        analysis.authenticate_actual_captures = true;
        let label = analysis.label(2, 0, &mut budget).unwrap();
        let event = Event {
            code: 2,
            label,
            unknown: false,
            port: Some(0),
        };
        let removed = Frame::RemovedHandler {
            code: 1,
            context: 0,
            value_context: 0,
        };
        let live = Frame::Handler {
            code: 1,
            context: 0,
            value_context: 0,
            capture_context: 0,
        };
        let address = |frame: Frame| Address::Slot {
            region: Region::Closing(3, 2),
            site: frame.site(),
            allocation_context: 0,
            old: false,
        };
        let mut state = State {
            position: Position { code: 2, next: 0 },
            context: 0,
            value_context: 0,
            stack: address(removed),
            retained: Vec::new(),
            cells: Vec::new(),
            heap: vec![
                Edge {
                    address: address(removed),
                    frame: removed,
                    next: address(live),
                },
                Edge {
                    address: address(live),
                    frame: live,
                    next: Address::Empty,
                },
            ],
            abandoned: Some((3, event)),
        };
        state.normalize(&mut budget).unwrap();
        assert!(
            matches!(
                analysis.requested(
                    &state,
                    event,
                    &mut VecDeque::new(),
                    &mut HashSet::new(),
                    &mut budget
                ),
                Err(Failure::CleanupContext { .. })
            ),
            "an outer same-label live handler cannot replace the nearest removed source handler during actual c inference"
        );
    }

    #[test]
    fn provider_restore_relocates_the_original_owner_cut_and_refuses_conflicts() {
        let original = ProviderResourceOccurrence {
            code: 3,
            value_context: 7,
        };
        let restored = ProviderResourceOccurrence {
            value_context: 10,
            ..original
        };
        let sibling = ProviderResourceOccurrence {
            value_context: 8,
            ..original
        };
        let mapping = [
            (
                sibling,
                ProviderResourceOccurrence {
                    value_context: 99,
                    ..sibling
                },
            ),
            (original, restored),
        ];
        let mut measured = TypeWorkBudget::unbounded();
        assert_eq!(
            relocate_provider_resource_occurrence(original, &mapping, &mut measured).unwrap(),
            restored
        );
        let exact = measured.used();
        assert!(matches!(
            relocate_provider_resource_occurrence(
                original,
                &mapping,
                &mut TypeWorkBudget::with_limit(exact - 1)
            ),
            Err(Failure::Resource)
        ));
        assert_eq!(
            relocate_provider_resource_occurrence(
                original,
                &mapping,
                &mut TypeWorkBudget::with_limit(exact)
            )
            .unwrap(),
            restored
        );
        let conflict = [
            (original, restored),
            (
                original,
                ProviderResourceOccurrence {
                    value_context: 11,
                    ..original
                },
            ),
        ];
        assert!(matches!(
            relocate_provider_resource_occurrence(
                original,
                &conflict,
                &mut TypeWorkBudget::unbounded()
            ),
            Err(Failure::Invalid)
        ));
    }

    #[test]
    fn wide_resource_free_call_targets_preflight_and_retry_exactly() {
        const WIDTH: usize = 128;
        let source = SourceFile::new("wide-targets", "x").unwrap();
        let span = source.span(ByteRange::new(0, 1).unwrap()).unwrap();
        let ty = || Type::Function(Box::new(Type::Unit), Box::new(Type::Unit));
        let mut graph = SummaryGraph {
            effects: true,
            data: None,
            callables: vec![Callable {
                body: 0,
                ty: ty(),
                result: Value::default(),
            }]
            .into(),
            types: TypeArguments(vec![ty()]),
            code: vec![
                Control::Return,
                Control::Call {
                    prefix: None,
                    value: Value {
                        targets: vec![0; WIDTH],
                        unknown: false,
                        ..Value::default()
                    },
                    ty: 0,
                    source: span,
                },
            ],
        };
        let run = |early: bool, budget: &mut TypeWorkBudget| {
            let mut analysis =
                Analysis::new(&graph, None, &mut TypeWorkBudget::unbounded()).unwrap();
            let outcome = analysis.discover(&[1], None, budget);
            if early {
                assert!(
                    analysis.call_cache.is_empty(),
                    "target staging must fail before target expansion"
                );
            }
            outcome
        };
        for limit in [0, WIDTH - 1] {
            assert!(matches!(
                run(true, &mut TypeWorkBudget::with_limit(limit)),
                Err(Failure::Resource)
            ));
        }
        let mut measured = TypeWorkBudget::unbounded();
        run(false, &mut measured).unwrap();
        assert!(matches!(
            run(false, &mut TypeWorkBudget::with_limit(measured.used() - 1)),
            Err(Failure::Resource)
        ));
        for _ in 0..2 {
            run(false, &mut TypeWorkBudget::with_limit(measured.used())).unwrap();
        }
        graph.callables.positions.push(None);
        for target in [1, 2] {
            let Control::Call { value, .. } = &mut graph.code[1] else {
                unreachable!()
            };
            value.targets = vec![target];
            let mut analysis =
                Analysis::new(&graph, None, &mut TypeWorkBudget::unbounded()).unwrap();
            assert!(matches!(
                analysis.discover(&[1], None, &mut TypeWorkBudget::unbounded()),
                Err(Failure::Invalid)
            ));
        }
    }

    fn observed_call_graph() -> SummaryGraph {
        let source = SourceFile::new("observed-control-call", "x").unwrap();
        let span = source.span(ByteRange::new(0, 1).unwrap()).unwrap();
        let ty = || Type::function(Type::Unit, Type::Unit);
        SummaryGraph {
            effects: true,
            data: Some(Arc::new(
                super::super::value::observed_control_call_graph_for_test(),
            )),
            callables: vec![
                Callable {
                    body: 0,
                    ty: ty(),
                    result: Value::default(),
                },
                Callable {
                    body: 2,
                    ty: ty(),
                    result: Value::default(),
                },
            ]
            .into(),
            types: TypeArguments(vec![ty()]),
            code: vec![
                Control::Return,
                Control::Call {
                    prefix: None,
                    value: Value::default(),
                    ty: 0,
                    source: span,
                },
                Control::Return,
            ],
        }
    }

    fn observed_call_analysis(graph: &SummaryGraph) -> Analysis<'_> {
        let mut setup = TypeWorkBudget::default();
        let mut analysis = Analysis::new(graph, None, &mut setup).unwrap();
        analysis.data = Some(graph.data.as_ref().unwrap().start(&mut setup).unwrap());
        analysis
    }

    fn observed_call_state(context: usize) -> State {
        State {
            position: Position { code: 1, next: 0 },
            context,
            value_context: 0,
            stack: Address::Empty,
            heap: Vec::new(),
            abandoned: None,
            retained: Vec::new(),
            cells: vec![CellContents {
                occurrence: ProviderResourceOccurrence {
                    code: 0,
                    value_context: 0,
                },
                owner: (0, 0),
                roots: vec![0, 1, 2],
                enclosing: vec![(0, 0)].into(),
                predecessors: vec![1, 2].into(),
                shared: true,
            }],
        }
    }

    #[derive(Default)]
    struct ObservedCallStage {
        calls: Vec<ObservedCall>,
        indices: HashMap<State, usize>,
        pending: VecDeque<State>,
        visited: HashSet<State>,
    }

    impl ObservedCallStage {
        fn dispatch(
            &mut self,
            analysis: &mut Analysis<'_>,
            state: State,
            work: &mut TypeWorkBudget,
        ) -> Result<(), Failure> {
            analysis.discover_call(
                state,
                &mut self.calls,
                &mut self.indices,
                &mut self.pending,
                &mut self.visited,
                work,
            )
        }
    }

    #[test]
    fn observed_call_owned_state_preserves_exact_records_and_late_prefixes() {
        let graph = observed_call_graph();
        let mut analysis = observed_call_analysis(&graph);
        let mut stage = ObservedCallStage::default();
        let expected = observed_call_state(0);
        let mut work = TypeWorkBudget::default();
        stage
            .dispatch(&mut analysis, observed_call_state(0), &mut work)
            .unwrap();
        assert_eq!(stage.calls.len(), 1);
        assert_eq!(stage.calls[0].state, expected);
        assert_eq!(stage.indices.get(&expected), Some(&0));
        assert!(stage.calls[0].delivered.is_some());
        assert_eq!(stage.pending.len(), 1);

        stage.pending.clear();
        stage
            .dispatch(&mut analysis, observed_call_state(0), &mut work)
            .unwrap();
        assert_eq!(stage.calls.len(), 1);
        assert!(
            stage.pending.is_empty(),
            "the completed callee prefix is not replayed"
        );
        analysis
            .data
            .as_mut()
            .unwrap()
            .add_observed_control_call_target_for_test(&mut work)
            .unwrap();
        stage
            .dispatch(&mut analysis, observed_call_state(0), &mut work)
            .unwrap();
        assert_eq!(stage.calls.len(), 1);
        assert_eq!(stage.pending.len(), 1, "a new actual callee remains live");
        assert_eq!(stage.pending[0].position.code, 2);

        // An equal call port is not an equal control State. A separate valid
        // type context must receive its own first observation and ordered record.
        let distinct_context = analysis.contexts.len();
        analysis.contexts.push(Context {
            bindings: Vec::new(),
            rows: Vec::new(),
        });
        stage.pending.clear();
        stage
            .dispatch(
                &mut analysis,
                observed_call_state(distinct_context),
                &mut work,
            )
            .unwrap();
        assert_eq!(stage.calls.len(), 2);
        assert_eq!(
            stage.indices.get(&observed_call_state(distinct_context)),
            Some(&1)
        );
        assert_eq!(stage.calls[0].state, expected);
        assert_eq!(stage.calls[1].state, observed_call_state(distinct_context));
    }

    #[test]
    fn observed_call_first_publication_is_bounded_and_freshly_retryable() {
        let graph = observed_call_graph();
        let run = |work: &mut TypeWorkBudget| {
            let mut analysis = observed_call_analysis(&graph);
            let mut stage = ObservedCallStage::default();
            let result = stage.dispatch(&mut analysis, observed_call_state(0), work);
            if result.is_ok() {
                assert_eq!(stage.calls.len(), 1);
                assert_eq!(stage.indices.get(&stage.calls[0].state), Some(&0));
                assert!(stage.calls[0].delivered.is_some());
            } else {
                assert!(
                    stage.calls.is_empty(),
                    "no completed record before publication"
                );
            }
            result
        };
        let mut measured = TypeWorkBudget::default();
        run(&mut measured).unwrap();
        let cost = measured.used();
        for prefix in [0, 7] {
            for available in 0..cost {
                let mut short = TypeWorkBudget::with_limit(prefix + available);
                short.charge(prefix).unwrap();
                assert!(matches!(run(&mut short), Err(Failure::Resource)));
            }
            let mut exact = TypeWorkBudget::with_limit(prefix + cost);
            exact.charge(prefix).unwrap();
            run(&mut exact).unwrap();
            assert_eq!(exact.used(), prefix + cost);
            assert!(matches!(run(&mut exact), Err(Failure::Resource)));
            for _ in 0..2 {
                let mut fresh = TypeWorkBudget::with_limit(prefix + cost);
                fresh.charge(prefix).unwrap();
                run(&mut fresh).unwrap();
                assert_eq!(fresh.used(), prefix + cost);
            }
        }
    }

    #[test]
    fn observed_call_late_publication_failure_does_not_advance_record() {
        let graph = observed_call_graph();
        let run = |work: &mut TypeWorkBudget| {
            let mut analysis = observed_call_analysis(&graph);
            let mut stage = ObservedCallStage::default();
            let mut setup = TypeWorkBudget::default();
            stage
                .dispatch(&mut analysis, observed_call_state(0), &mut setup)
                .unwrap();
            stage.pending.clear();
            analysis
                .data
                .as_mut()
                .unwrap()
                .add_observed_control_call_target_for_test(&mut setup)
                .unwrap();
            let result = stage.dispatch(&mut analysis, observed_call_state(0), work);
            assert_eq!(stage.calls.len(), 1);
            assert_eq!(stage.calls[0].state, observed_call_state(0));
            let (remaining, _) = analysis
                .data
                .as_mut()
                .unwrap()
                .calls_after(1, 0, stage.calls[0].delivered.as_ref(), &mut setup)
                .unwrap();
            assert_eq!(remaining.targets.len(), usize::from(result.is_err()));
            result
        };
        let mut measured = TypeWorkBudget::default();
        run(&mut measured).unwrap();
        assert!(matches!(
            run(&mut TypeWorkBudget::with_limit(measured.used() - 1)),
            Err(Failure::Resource)
        ));
        for _ in 0..2 {
            let mut exact = TypeWorkBudget::with_limit(measured.used());
            run(&mut exact).unwrap();
            assert_eq!(exact.used(), measured.used());
        }
    }

    #[test]
    fn tail_resume_preserves_captured_resource_and_outside_live_clause() {
        let graph = SummaryGraph {
            effects: true,
            data: None,
            callables: CallableSlots::default(),
            types: TypeArguments(vec![]),
            code: vec![Control::Return],
        };
        for old in [false, true] {
            let run = |budget: &mut TypeWorkBudget| {
                let address = |site, region| Address::Slot {
                    region,
                    site,
                    allocation_context: 0,
                    old,
                };
                let inner = address(Site::Clause(3, false), Region::Active);
                let outer = address(Site::Clause(9, false), Region::Active);
                let captured = address(Site::Resource(7), Region::Capture(0, 0));
                let event = Event {
                    code: 0,
                    label: 0,
                    unknown: false,
                    port: None,
                };
                let clause = |owner, capture| Frame::Clause {
                    handler: 0,
                    ordinal: 0,
                    owner,
                    context: 0,
                    value_context: 0,
                    capture,
                    capture_context: 0,
                    clause_context: 0,
                    event,
                    consumed: false,
                };
                let mut state = State {
                    position: Position { code: 0, next: 0 },
                    context: 0,
                    value_context: 0,
                    stack: inner,
                    abandoned: None,
                    retained: Vec::new(),
                    cells: Vec::new(),
                    heap: vec![
                        Edge {
                            address: inner,
                            frame: clause(3, captured),
                            next: outer,
                        },
                        Edge {
                            address: outer,
                            frame: clause(9, Address::End),
                            next: Address::Empty,
                        },
                        Edge {
                            address: captured,
                            frame: Frame::Resource {
                                code: 7,
                                context: 0,
                                value_context: 0,
                                focused: true,
                            },
                            next: Address::End,
                        },
                    ],
                };
                state.normalize(budget)?;
                let mut pending = VecDeque::new();
                Analysis::new(&graph, None, budget)?.completed(
                    state,
                    3,
                    Completion::Resume,
                    &mut pending,
                    &mut HashSet::new(),
                    budget,
                )?;
                let resumed = pending.pop_front().unwrap();
                assert_eq!(resumed.heap.len(), 2);
                let (resources, _) = selections(
                    &resumed,
                    resumed.stack,
                    |frame| Ok((matches!(frame, Frame::Resource { code: 7, .. }), true)),
                    budget,
                )?;
                assert_eq!(resources.len(), 1);
                let (owners, escaped) = selections(
                    &resumed,
                    resumed.stack,
                    |frame| {
                        Ok((
                            matches!(
                                frame,
                                Frame::Clause {
                                    owner: 9,
                                    consumed: false,
                                    ..
                                }
                            ),
                            true,
                        ))
                    },
                    budget,
                )?;
                assert_eq!(owners.len(), 1);
                assert!(escaped);
                Ok::<(), Failure>(())
            };
            let mut measured = TypeWorkBudget::unbounded();
            run(&mut measured).unwrap();
            assert!(matches!(
                run(&mut TypeWorkBudget::with_limit(measured.used() - 1)),
                Err(Failure::Resource)
            ));
            for _ in 0..2 {
                run(&mut TypeWorkBudget::with_limit(measured.used())).unwrap();
            }
        }
    }

    #[test]
    fn consuming_an_older_clause_keeps_rebound_and_original_prefixes_separate() {
        let graph = SummaryGraph {
            effects: true,
            data: None,
            callables: CallableSlots::default(),
            types: TypeArguments(vec![]),
            code: vec![Control::Return],
        };
        let run = |budget: &mut TypeWorkBudget| {
            let resource = Frame::Resource {
                code: 7,
                context: 0,
                value_context: 0,
                focused: true,
            };
            let address = |site| Address::Slot {
                region: Region::Active,
                site,
                allocation_context: 0,
                old: true,
            };
            let root = address(resource.site());
            let owner = address(Site::Clause(3, false));
            let retained = address(Site::Clause(9, false));
            let event = Event {
                code: 0,
                label: 0,
                unknown: false,
                port: None,
            };
            let clause = |id, capture| Frame::Clause {
                handler: 0,
                ordinal: 0,
                owner: id,
                context: 0,
                value_context: 0,
                capture,
                capture_context: 0,
                clause_context: 0,
                event,
                consumed: false,
            };
            let mut state = State {
                position: Position { code: 0, next: 0 },
                context: 0,
                value_context: 0,
                stack: root,
                abandoned: None,
                retained: Vec::new(),
                cells: Vec::new(),
                heap: vec![
                    Edge {
                        address: root,
                        frame: resource,
                        next: owner,
                    },
                    Edge {
                        address: owner,
                        frame: clause(3, Address::End),
                        next: retained,
                    },
                    Edge {
                        address: retained,
                        frame: clause(9, root),
                        next: Address::Empty,
                    },
                ],
            };
            state.normalize(budget)?;
            let mut pending = VecDeque::new();
            Analysis::new(&graph, None, budget)?.completed(
                state,
                3,
                Completion::Resume,
                &mut pending,
                &mut HashSet::new(),
                budget,
            )?;
            let rebound = pending.pop_front().unwrap();
            let (selected, _) = selections(
                &rebound,
                rebound.stack,
                |frame| Ok((matches!(frame, Frame::Clause { owner: 3, .. }), true)),
                budget,
            )?;
            assert!(selected.iter().all(|selection| matches!(
                selection.boundary.frame,
                Frame::Clause { consumed: true, .. }
            )));
            assert!(
                rebound
                    .edges(root, budget)?
                    .iter()
                    .any(|edge| edge.next == owner)
            );
            assert!(rebound.edges(owner, budget)?.iter().any(|edge| matches!(
                edge.frame,
                Frame::Clause {
                    consumed: false,
                    ..
                }
            )));
            Ok::<(), Failure>(())
        };
        let mut measured = TypeWorkBudget::unbounded();
        run(&mut measured).unwrap();
        run(&mut TypeWorkBudget::with_limit(measured.used())).unwrap();
        assert!(matches!(
            run(&mut TypeWorkBudget::with_limit(measured.used() - 1)),
            Err(Failure::Resource)
        ));
        run(&mut TypeWorkBudget::with_limit(measured.used())).unwrap();
    }

    #[test]
    fn discard_provenance_retains_live_owners_and_precharges_wide_scans() {
        let event = Event {
            code: 8,
            label: 9,
            unknown: false,
            port: Some(10),
        };
        for old in [false, true] {
            for frame in [
                Frame::Clause {
                    handler: 1,
                    ordinal: 0,
                    owner: 2,
                    context: 3,
                    value_context: 4,
                    capture: Address::End,
                    capture_context: 5,
                    clause_context: 6,
                    event,
                    consumed: false,
                },
                Frame::RemovedHandler {
                    code: 1,
                    context: 3,
                    value_context: 4,
                },
            ] {
                let address = Address::Slot {
                    region: Region::Active,
                    site: frame.site(),
                    allocation_context: frame.allocation_context(),
                    old,
                };
                let mut pending = VecDeque::new();
                let mut visited = HashSet::new();
                for port in [10, 20] {
                    Analysis::enqueue_normalized(
                        State {
                            position: Position { code: 3, next: 0 },
                            context: 3,
                            value_context: 4,
                            stack: address,
                            retained: Vec::new(),
                            cells: Vec::new(),
                            heap: vec![Edge {
                                address,
                                frame,
                                next: Address::Empty,
                            }],
                            abandoned: Some((
                                7,
                                Event {
                                    port: Some(port),
                                    ..event
                                },
                            )),
                        },
                        &mut pending,
                        &mut visited,
                        &mut TypeWorkBudget::default(),
                    )
                    .unwrap();
                }
                assert_eq!(pending.len(), 2);
                assert!(pending.iter().all(|state| state.abandoned.is_some()));
            }
        }
        for width in [1, 4096] {
            let mut heap = Vec::new();
            for code in 0..width {
                let frame = Frame::Registration {
                    code,
                    context: 0,
                    value_context: 0,
                };
                heap.push(Edge {
                    address: Address::Slot {
                        region: Region::Active,
                        site: frame.site(),
                        allocation_context: 0,
                        old: false,
                    },
                    frame,
                    next: if code + 1 == width {
                        Address::Empty
                    } else {
                        Address::Slot {
                            region: Region::Active,
                            site: Site::Registration(code + 1),
                            allocation_context: 0,
                            old: false,
                        }
                    },
                });
            }
            let state = State {
                position: Position { code: 3, next: 0 },
                context: 0,
                value_context: 0,
                stack: heap[0].address,
                heap,
                retained: Vec::new(),
                cells: Vec::new(),
                abandoned: Some((7, event)),
            };
            let run = |budget: &mut TypeWorkBudget| {
                let input = state.copy(&mut TypeWorkBudget::unbounded()).unwrap();
                let mut pending = VecDeque::new();
                let mut visited = HashSet::new();
                Analysis::enqueue_normalized(input, &mut pending, &mut visited, budget)?;
                Ok::<_, Failure>((pending, visited))
            };
            let mut measured = TypeWorkBudget::unbounded();
            let expected = run(&mut measured).unwrap();
            assert_eq!(expected.0[0].abandoned, None);
            assert_eq!(expected.0[0].heap, state.heap);
            assert_eq!(
                run(&mut TypeWorkBudget::with_limit(measured.used())).unwrap(),
                expected
            );
            assert!(matches!(
                run(&mut TypeWorkBudget::with_limit(measured.used() - 1)),
                Err(Failure::Resource)
            ));
            assert_eq!(
                run(&mut TypeWorkBudget::with_limit(measured.used())).unwrap(),
                expected
            );
            let mut pending = VecDeque::new();
            let mut visited = HashSet::new();
            let mut short = TypeWorkBudget::with_limit(width - 1);
            assert!(matches!(
                Analysis::enqueue_normalized(state, &mut pending, &mut visited, &mut short),
                Err(Failure::Resource)
            ));
            assert_eq!(short.used(), 0);
            assert!(pending.is_empty() && visited.is_empty());
        }
    }

    #[test]
    fn captured_discard_diagnostic_owner_survives_history_normalization() {
        let event = Event {
            code: 8,
            label: 9,
            unknown: false,
            port: Some(10),
        };
        let owner = Frame::RemovedHandler {
            code: 1,
            context: 2,
            value_context: 3,
        };
        let capture = Address::Slot {
            region: Region::Closing(7, 8),
            site: owner.site(),
            allocation_context: 3,
            old: true,
        };
        let closing = Frame::Closing {
            code: 7,
            site: Site::Closing(7, false),
            context: 2,
            value_context: 3,
            capture: Some(capture),
            event,
        };
        let stack = Address::Slot {
            region: Region::Active,
            site: closing.site(),
            allocation_context: 3,
            old: false,
        };
        let mut pending = VecDeque::new();
        let mut visited = HashSet::new();
        Analysis::enqueue(
            State {
                position: Position { code: 0, next: 0 },
                context: 2,
                value_context: 3,
                stack,
                retained: Vec::new(),
                cells: Vec::new(),
                heap: vec![
                    Edge {
                        address: stack,
                        frame: closing,
                        next: Address::Empty,
                    },
                    Edge {
                        address: capture,
                        frame: owner,
                        next: Address::End,
                    },
                ],
                abandoned: Some((7, event)),
            },
            &mut pending,
            &mut visited,
            &mut TypeWorkBudget::default(),
        )
        .unwrap();
        assert_eq!(pending[0].heap.len(), 2);
        assert_eq!(pending[0].abandoned, Some((7, event)));
    }

    #[test]
    fn completed_discard_histories_join_before_later_computations() {
        let run = |budget: &mut TypeWorkBudget| {
            let mut pending = VecDeque::new();
            let mut visited = HashSet::new();
            for port in [None, Some(10), Some(20)] {
                Analysis::enqueue_normalized(
                    State {
                        position: Position { code: 3, next: 0 },
                        context: 4,
                        value_context: 5,
                        stack: Address::Empty,
                        heap: Vec::new(),
                        retained: Vec::new(),
                        cells: Vec::new(),
                        abandoned: port.map(|port| {
                            (
                                7,
                                Event {
                                    code: 8,
                                    label: 9,
                                    unknown: false,
                                    port: Some(port),
                                },
                            )
                        }),
                    },
                    &mut pending,
                    &mut visited,
                    budget,
                )?;
            }
            Ok::<_, Failure>((pending, visited))
        };
        let mut measured = TypeWorkBudget::unbounded();
        let expected = run(&mut measured).unwrap();
        assert_eq!(expected.0.len(), 1);
        assert_eq!(expected.1.len(), 1);
        assert_eq!(expected.0[0].abandoned, None);
        assert_eq!(
            run(&mut TypeWorkBudget::with_limit(measured.used())).unwrap(),
            expected
        );
        assert!(matches!(
            run(&mut TypeWorkBudget::with_limit(measured.used() - 1)),
            Err(Failure::Resource)
        ));
        assert_eq!(
            run(&mut TypeWorkBudget::with_limit(measured.used())).unwrap(),
            expected
        );
    }

    #[test]
    fn scalar_successor_reuses_normalized_heap_with_exact_fresh_retry() {
        let frame = Frame::Resource {
            code: 7,
            context: 0,
            value_context: 0,
            focused: false,
        };
        let root = Address::Slot {
            region: Region::Active,
            site: frame.site(),
            allocation_context: 0,
            old: false,
        };
        let run = |normalize, budget: &mut TypeWorkBudget| {
            let state = State {
                position: Position { code: 3, next: 2 },
                context: 4,
                value_context: 5,
                stack: root,
                retained: Vec::new(),
                cells: Vec::new(),
                heap: vec![Edge {
                    address: root,
                    frame,
                    next: Address::Empty,
                }],
                abandoned: None,
            };
            let mut pending = VecDeque::new();
            let mut visited = HashSet::new();
            if normalize {
                Analysis::enqueue(state, &mut pending, &mut visited, budget)?;
            } else {
                Analysis::enqueue_normalized(state, &mut pending, &mut visited, budget)?;
            }
            Ok::<_, Failure>((pending, visited))
        };
        let mut full = TypeWorkBudget::unbounded();
        let expected = run(true, &mut full).unwrap();
        let mut measured = TypeWorkBudget::unbounded();
        assert_eq!(run(false, &mut measured).unwrap(), expected);
        assert!(measured.used() < full.used());
        assert_eq!(
            run(false, &mut TypeWorkBudget::with_limit(measured.used())).unwrap(),
            expected
        );
        assert!(matches!(
            run(false, &mut TypeWorkBudget::with_limit(measured.used() - 1)),
            Err(Failure::Resource)
        ));
        assert_eq!(
            run(false, &mut TypeWorkBudget::with_limit(measured.used())).unwrap(),
            expected
        );
    }

    #[test]
    fn allocation_context_survives_restoration_copy_and_aging() {
        let run = |budget: &mut TypeWorkBudget| {
            let frame = |value_context| Frame::Resource {
                code: 7,
                context: 0,
                value_context,
                focused: false,
            };
            let mut state = State {
                position: Position { code: 0, next: 0 },
                context: 0,
                value_context: 0,
                stack: Address::Empty,
                heap: Vec::new(),
                retained: Vec::new(),
                cells: Vec::new(),
                abandoned: None,
            };
            state.push(frame(3), budget)?;
            let first = state.stack;
            state.push(frame(4), budget)?;
            assert_ne!(state.stack, first);
            assert_eq!(
                state.heap[0].address, first,
                "another allocation context must not age the first"
            );
            state.push(frame(3), budget)?;
            assert_eq!(state.stack, first);
            assert!(state.heap.iter().any(|edge| edge.address == first.older()));
            let mut edge = *state.heap.last().unwrap();
            if let Frame::Resource { value_context, .. } = &mut edge.frame {
                *value_context = 99;
            }
            let copied = state.copy_segment(
                first,
                &[edge],
                Some(edge),
                Address::End,
                Region::Capture(2, 5),
                budget,
            )?;
            assert!(matches!(
                copied,
                Address::Slot {
                    allocation_context: 3,
                    old: false,
                    ..
                }
            ));
            state.normalize(budget)?;
            Ok::<(), Failure>(())
        };
        let mut measured = TypeWorkBudget::unbounded();
        run(&mut measured).unwrap();
        run(&mut TypeWorkBudget::with_limit(measured.used())).unwrap();
        assert!(matches!(
            run(&mut TypeWorkBudget::with_limit(measured.used() - 1)),
            Err(Failure::Resource)
        ));
        run(&mut TypeWorkBudget::with_limit(measured.used())).unwrap();
    }

    #[test]
    fn stack_pop_prunes_sorted_heap_with_exact_fresh_retry() {
        let run = |sort, budget: &mut TypeWorkBudget| {
            let frame = Frame::Resource {
                code: 7,
                context: 0,
                value_context: 0,
                focused: false,
            };
            let root = Address::Slot {
                region: Region::Active,
                site: frame.site(),
                allocation_context: 0,
                old: false,
            };
            let unreachable = Address::Slot {
                region: Region::Active,
                site: Site::Resource(8),
                allocation_context: 0,
                old: false,
            };
            let state = State {
                position: Position { code: 0, next: 0 },
                context: 0,
                value_context: 0,
                stack: root,
                retained: Vec::new(),
                cells: Vec::new(),
                heap: vec![
                    Edge {
                        address: root,
                        frame,
                        next: Address::Empty,
                    },
                    Edge {
                        address: unreachable,
                        frame,
                        next: root,
                    },
                ],
                abandoned: None,
            };
            let mut pending = VecDeque::new();
            let mut visited = HashSet::new();
            if sort {
                Analysis::enqueue(state, &mut pending, &mut visited, budget)?;
            } else {
                Analysis::enqueue_after_pop(
                    state,
                    unreachable,
                    &mut pending,
                    &mut visited,
                    budget,
                )?;
            }
            assert_eq!(pending[0].heap.len(), 1);
            Ok::<_, Failure>((pending, visited))
        };
        let mut full = TypeWorkBudget::unbounded();
        let expected = run(true, &mut full).unwrap();
        let mut measured = TypeWorkBudget::unbounded();
        assert_eq!(run(false, &mut measured).unwrap(), expected);
        assert!(measured.used() < full.used());
        assert_eq!(
            run(false, &mut TypeWorkBudget::with_limit(measured.used())).unwrap(),
            expected
        );
        assert!(matches!(
            run(false, &mut TypeWorkBudget::with_limit(measured.used() - 1)),
            Err(Failure::Resource)
        ));
        assert_eq!(
            run(false, &mut TypeWorkBudget::with_limit(measured.used())).unwrap(),
            expected
        );
    }

    #[test]
    fn copying_distinct_recent_regions_never_claims_a_singleton() {
        let run = |budget: &mut TypeWorkBudget| {
            let frame = Frame::Resource {
                code: 7,
                context: 0,
                value_context: 3,
                focused: false,
            };
            let address = |region| Address::Slot {
                region,
                site: frame.site(),
                allocation_context: 3,
                old: false,
            };
            let first = address(Region::Active);
            let second = address(Region::Completion(2, 5));
            let edges = [
                Edge {
                    address: first,
                    frame,
                    next: second,
                },
                Edge {
                    address: second,
                    frame,
                    next: Address::End,
                },
            ];
            let mut state = State {
                position: Position { code: 0, next: 0 },
                context: 0,
                value_context: 0,
                stack: Address::Empty,
                heap: Vec::new(),
                retained: Vec::new(),
                cells: Vec::new(),
                abandoned: None,
            };
            state.stack = state.copy_segment(
                first,
                &edges,
                Some(edges[1]),
                Address::End,
                Region::Capture(1, 4),
                budget,
            )?;
            assert!(matches!(state.stack, Address::Slot { old: true, .. }));
            state.normalize(budget)?;
            let copied = state.edges(state.stack, budget)?;
            assert_eq!(copied.len(), 2);
            assert!(copied.iter().any(|edge| edge.next == state.stack));
            assert!(copied.iter().any(|edge| edge.next == Address::End));
            // A second copy joins the existing older destination without
            // erasing either tail; repeated edges from one source stay recent.
            state.stack = state.copy_segment(
                first,
                &edges,
                Some(edges[1]),
                Address::Empty,
                Region::Capture(1, 4),
                budget,
            )?;
            state.normalize(budget)?;
            assert_eq!(state.edges(state.stack, budget)?.len(), 3);
            let recent = state.copy_segment(
                second,
                &[edges[1], edges[1]],
                Some(edges[1]),
                Address::End,
                Region::Capture(1, 4),
                budget,
            )?;
            assert!(matches!(recent, Address::Slot { old: false, .. }));
            state.stack = recent;
            let merged = state.copy_segment(
                first,
                &edges,
                Some(edges[1]),
                Address::Empty,
                Region::Capture(1, 4),
                budget,
            )?;
            assert_eq!(
                state.stack,
                recent.older(),
                "retained recent references must age even when new copies demote"
            );
            assert_eq!(merged, state.stack);
            state.normalize(budget)?;
            assert_eq!(state.edges(merged, budget)?.len(), 3);
            Ok::<(), Failure>(())
        };
        let mut measured = TypeWorkBudget::unbounded();
        run(&mut measured).unwrap();
        run(&mut TypeWorkBudget::with_limit(measured.used())).unwrap();
        assert!(matches!(
            run(&mut TypeWorkBudget::with_limit(measured.used() - 1)),
            Err(Failure::Resource)
        ));
        run(&mut TypeWorkBudget::with_limit(measured.used())).unwrap();
    }

    #[test]
    fn resource_proof_requires_contextual_graph_and_payload_ports() {
        let source = SourceFile::new("missing-resource-data", "x").unwrap();
        let span = source.span(ByteRange::new(0, 1).unwrap()).unwrap();
        let effect = EffectInstance::new(EffectId::new(ModuleId::new(0), 0), Box::new([]));
        let mut budget = TypeWorkBudget::unbounded();
        let mut graph = SummaryGraph {
            effects: true,
            data: None,
            callables: CallableSlots::default(),
            types: TypeArguments(vec![]),
            code: vec![
                Control::Return,
                Control::Resource {
                    body: 0,
                    effect: Request::effect(&effect, span, &mut budget).unwrap(),
                },
            ],
        };
        assert!(matches!(
            Analysis::new(&graph, None, &mut budget),
            Err(Failure::Invalid)
        ));
        graph.code.pop();
        let mut analysis = Analysis::new(&graph, None, &mut budget).unwrap();
        let state = State {
            position: Position { code: 0, next: 0 },
            context: 0,
            value_context: 0,
            stack: Address::Empty,
            heap: Vec::new(),
            retained: Vec::new(),
            cells: Vec::new(),
            abandoned: None,
        };
        let crossed = [Edge {
            address: Address::Empty,
            frame: Frame::Resource {
                code: 1,
                context: 0,
                value_context: 0,
                focused: false,
            },
            next: Address::Empty,
        }];
        for port in [None, Some(0)] {
            assert!(matches!(
                analysis.check_payload(
                    &state,
                    Event {
                        code: 0,
                        label: 0,
                        unknown: false,
                        port
                    },
                    &crossed,
                    &mut budget
                ),
                Err(Failure::Invalid)
            ));
        }
        let imports = super::super::ImportedCallables::new(&[], 0, &mut budget).unwrap();
        let data = super::super::value::Graph::build::<crate::core::effect::EffectOperationFamily>(
            &[],
            &[],
            &[],
            &imports,
            |_| None,
            &[],
            &[],
            &mut budget,
        )
        .unwrap();
        graph.data = Some(Arc::new(data));
        graph.code.push(Control::Resource {
            body: 0,
            effect: Request::effect(&effect, span, &mut budget).unwrap(),
        });
        let mut analysis = Analysis::new(&graph, None, &mut budget).unwrap();
        assert!(analysis.data.is_some());
        assert!(matches!(
            analysis.check_payload(
                &state,
                Event {
                    code: 0,
                    label: 0,
                    unknown: false,
                    port: None
                },
                &crossed,
                &mut budget
            ),
            Err(Failure::Invalid)
        ));
    }

    #[test]
    fn wide_copy_preflights_staging_and_has_an_exact_fresh_boundary() {
        const WIDTH: usize = 96;
        let frame = Frame::Resource {
            code: 7,
            context: 0,
            value_context: 3,
            focused: false,
        };
        let address = |site| Address::Slot {
            region: Region::Completion(site, 5),
            site: frame.site(),
            allocation_context: 3,
            old: false,
        };
        let edges: Vec<_> = (0..WIDTH)
            .map(|index| Edge {
                address: address(index),
                frame,
                next: if index + 1 == WIDTH {
                    Address::End
                } else {
                    address(index + 1)
                },
            })
            .collect();
        let run = |budget: &mut TypeWorkBudget| {
            let mut state = State {
                position: Position { code: 0, next: 0 },
                context: 0,
                value_context: 0,
                stack: Address::Empty,
                heap: Vec::new(),
                retained: Vec::new(),
                cells: Vec::new(),
                abandoned: None,
            };
            let result = state.copy_segment(
                address(0),
                &edges,
                Some(edges[WIDTH - 1]),
                Address::End,
                Region::Capture(1, 4),
                budget,
            );
            if budget.used() == 0 {
                assert!(state.heap.is_empty());
            }
            assert!(matches!(result?, Address::Slot { old: true, .. }));
            Ok::<(), Failure>(())
        };
        for limit in [0, WIDTH - 1] {
            let mut budget = TypeWorkBudget::with_limit(limit);
            assert!(matches!(run(&mut budget), Err(Failure::Resource)));
            assert_eq!(budget.used(), 0);
        }
        let mut measured = TypeWorkBudget::unbounded();
        run(&mut measured).unwrap();
        run(&mut TypeWorkBudget::with_limit(measured.used())).unwrap();
        assert!(matches!(
            run(&mut TypeWorkBudget::with_limit(measured.used() - 1)),
            Err(Failure::Resource)
        ));
        run(&mut TypeWorkBudget::with_limit(measured.used())).unwrap();
    }

    #[test]
    fn singleton_pop_matches_full_pruning_for_cycles_captures_and_summary_roots() {
        let event = Event {
            code: 0,
            label: 0,
            unknown: false,
            port: None,
        };
        let resource = |code| Frame::Resource {
            code,
            context: 0,
            value_context: 0,
            focused: false,
        };
        let address = |frame: Frame| Address::Slot {
            region: Region::Active,
            site: frame.site(),
            allocation_context: 0,
            old: false,
        };
        let clause = |owner, capture, consumed| Frame::Clause {
            handler: 0,
            ordinal: 0,
            owner,
            context: 0,
            value_context: 0,
            capture,
            capture_context: 0,
            clause_context: 0,
            event,
            consumed,
        };
        for case in 0..8 {
            let branch = address(resource(9));
            let root_frame = if case == 6 {
                clause(7, branch, false)
            } else {
                resource(7)
            };
            let root = address(root_frame);
            let tail_frame = if case == 3 || case == 4 {
                clause(8, root, case == 4)
            } else {
                resource(8)
            };
            let tail = address(tail_frame);
            let mut heap = vec![Edge {
                address: root,
                frame: root_frame,
                next: if case == 1 { root } else { tail },
            }];
            if case != 1 {
                heap.push(Edge {
                    address: tail,
                    frame: tail_frame,
                    next: if case == 2 { root } else { Address::Empty },
                });
            }
            if case == 5 {
                heap.push(Edge {
                    address: root,
                    frame: root_frame,
                    next: branch,
                });
            }
            if case == 5 || case == 6 {
                heap.push(Edge {
                    address: branch,
                    frame: resource(9),
                    next: Address::Empty,
                });
            }
            if case == 7 {
                heap[1].next = address(resource(9));
                for code in 9..41 {
                    heap.push(Edge {
                        address: address(resource(code)),
                        frame: resource(code),
                        next: if code == 40 {
                            Address::Empty
                        } else {
                            address(resource(code + 1))
                        },
                    });
                }
            }
            let mut state = State {
                position: Position { code: 0, next: 0 },
                context: 0,
                value_context: 0,
                stack: root,
                heap,
                retained: Vec::new(),
                cells: Vec::new(),
                abandoned: None,
            };
            state.normalize(&mut TypeWorkBudget::unbounded()).unwrap();
            state.stack = if case == 1 { root } else { tail };
            let mut expected = state.copy(&mut TypeWorkBudget::unbounded()).unwrap();
            let mut full = TypeWorkBudget::unbounded();
            expected.prune_sorted_heap(&mut full).unwrap();
            let run = |budget: &mut TypeWorkBudget| {
                let mut next = state.copy(&mut TypeWorkBudget::unbounded())?;
                next.prune_after_pop(root, budget)?;
                assert_eq!(next, expected, "case {case}");
                Ok::<(), Failure>(())
            };
            let mut measured = TypeWorkBudget::unbounded();
            run(&mut measured).unwrap();
            if case == 7 {
                assert!(
                    measured.used() < full.used(),
                    "wide chain did not use the singleton fast path"
                );
            }
            run(&mut TypeWorkBudget::with_limit(measured.used())).unwrap();
            assert!(matches!(
                run(&mut TypeWorkBudget::with_limit(measured.used() - 1)),
                Err(Failure::Resource)
            ));
            run(&mut TypeWorkBudget::with_limit(measured.used())).unwrap();
        }
    }

    #[test]
    fn address_ranges_match_two_bounds_with_exact_wide_retry() {
        let address = |code| Address::Slot {
            region: Region::Active,
            site: Site::Resource(code),
            allocation_context: 0,
            old: false,
        };
        for (length, group) in [(0, 1), (1, 1), (8, 2), (96, 1), (192, 96)] {
            let heap = (0..length)
                .map(|index| {
                    let code = (index / group) * 2 + 2;
                    Edge {
                        address: address(code),
                        frame: Frame::Resource {
                            code,
                            context: 0,
                            value_context: index,
                            focused: false,
                        },
                        next: Address::Empty,
                    }
                })
                .collect();
            let state = State {
                position: Position { code: 0, next: 0 },
                context: 0,
                value_context: 0,
                stack: Address::Empty,
                heap,
                retained: Vec::new(),
                cells: Vec::new(),
                abandoned: None,
            };
            for target in [
                Address::Empty,
                Address::End,
                address(0),
                address(2),
                address(3),
                address(4),
                address(length * 2 + 4),
            ] {
                let start = state.heap.partition_point(|edge| edge.address < target);
                let count = state.heap[start..].partition_point(|edge| edge.address == target);
                let expected = &state.heap[start..start + count];
                let old_work = state.heap.len().max(1).ilog2() as usize * 2 + 1 + count;
                let run = |budget: &mut TypeWorkBudget| {
                    assert_eq!(state.edges(target, budget)?, expected);
                    Ok::<(), Failure>(())
                };
                let mut measured = TypeWorkBudget::unbounded();
                run(&mut measured).unwrap();
                if group == 1 && length == 96 && count == 1 {
                    assert!(measured.used() < old_work);
                }
                run(&mut TypeWorkBudget::with_limit(measured.used())).unwrap();
                assert!(matches!(
                    run(&mut TypeWorkBudget::with_limit(measured.used() - 1)),
                    Err(Failure::Resource)
                ));
                run(&mut TypeWorkBudget::with_limit(measured.used())).unwrap();
            }
        }
    }

    #[test]
    fn indexed_pruning_matches_range_walk_for_every_root_and_retries_atomically() {
        fn reference(state: &mut State, budget: &mut TypeWorkBudget) -> Result<(), Failure> {
            let mut reachable = HashSet::new();
            let mut pending = vec![state.stack];
            while let Some(address) = pending.pop() {
                charge(budget, 1)?;
                if matches!(address, Address::Empty | Address::End) || reachable.contains(&address)
                {
                    continue;
                }
                reachable.try_reserve(1).map_err(|_| Failure::Resource)?;
                reachable.insert(address);
                for edge in state.edges(address, budget)? {
                    pending.try_reserve(2).map_err(|_| Failure::Resource)?;
                    pending.push(edge.next);
                    if let Frame::Clause {
                        capture,
                        consumed: false,
                        ..
                    } = edge.frame
                    {
                        pending.push(capture);
                    }
                }
            }
            charge(budget, state.heap.len())?;
            state.heap.retain(|edge| reachable.contains(&edge.address));
            Ok(())
        }
        let address = |code| Address::Slot {
            region: Region::Active,
            site: match code {
                50 => Site::Clause(50, false),
                70 => Site::Clause(70, true),
                _ => Site::Resource(code),
            },
            allocation_context: 0,
            old: code % 2 == 0,
        };
        let event = Event {
            code: 0,
            label: 0,
            unknown: false,
            port: None,
        };
        let frame = |code| {
            if code == 50 || code == 70 {
                Frame::Clause {
                    handler: 0,
                    ordinal: 0,
                    owner: code,
                    context: 0,
                    value_context: 0,
                    capture: address(if code == 50 { 200 } else { 201 }),
                    capture_context: 0,
                    clause_context: 0,
                    event,
                    consumed: code == 70,
                }
            } else {
                Frame::Resource {
                    code,
                    context: 0,
                    value_context: 0,
                    focused: false,
                }
            }
        };
        let mut heap: Vec<_> = (0..128)
            .map(|code| Edge {
                address: address(code),
                frame: frame(code),
                next: if code == 127 {
                    Address::End
                } else {
                    address(code + 1)
                },
            })
            .collect();
        heap.extend([
            Edge {
                address: address(6),
                frame: frame(6),
                next: address(3),
            },
            Edge {
                address: address(200),
                frame: frame(200),
                next: address(200),
            },
            Edge {
                address: address(201),
                frame: frame(201),
                next: Address::End,
            },
        ]);
        heap.sort_unstable();
        for root in (0..128)
            .chain(200..203)
            .map(address)
            .chain([Address::Empty, Address::End])
        {
            let state = State {
                position: Position { code: 0, next: 0 },
                context: 0,
                value_context: 0,
                stack: root,
                heap: heap.clone(),
                retained: Vec::new(),
                cells: Vec::new(),
                abandoned: None,
            };
            let mut expected = state.copy(&mut TypeWorkBudget::unbounded()).unwrap();
            let mut old_work = TypeWorkBudget::unbounded();
            reference(&mut expected, &mut old_work).unwrap();
            let run = |budget: &mut TypeWorkBudget| {
                let mut next = state.copy(&mut TypeWorkBudget::unbounded())?;
                let result = next.prune_sorted_heap(budget);
                if result.is_err() {
                    assert_eq!(next.heap, state.heap);
                }
                result?;
                assert_eq!(next, expected);
                Ok::<(), Failure>(())
            };
            let mut measured = TypeWorkBudget::unbounded();
            run(&mut measured).unwrap();
            if root == address(0) {
                assert!(measured.used() < old_work.used());
            }
            run(&mut TypeWorkBudget::with_limit(measured.used())).unwrap();
            assert!(matches!(
                run(&mut TypeWorkBudget::with_limit(measured.used() - 1)),
                Err(Failure::Resource)
            ));
            run(&mut TypeWorkBudget::with_limit(measured.used())).unwrap();
        }
    }

    #[test]
    fn wide_call_context_charges_binding_membership_exactly_and_retries() {
        const WIDTH: usize = 96;
        let source = SourceFile::new("wide-context", "x").unwrap();
        let span = source.span(ByteRange::new(0, 1).unwrap()).unwrap();
        let formal = Type::Function(
            Box::new(Type::Tuple(
                (0..WIDTH)
                    .map(|id| Type::Variable(TypeVariableId::new(id as u32)))
                    .collect(),
            )),
            Box::new(Type::Unit),
        );
        let actual = Type::Function(
            Box::new(Type::Tuple((0..WIDTH).map(|_| Type::Int).collect())),
            Box::new(Type::Unit),
        );
        let graph = SummaryGraph {
            effects: true,
            data: None,
            callables: vec![Callable {
                body: 0,
                ty: formal,
                result: Value::default(),
            }]
            .into(),
            types: TypeArguments(vec![actual]),
            code: vec![Control::Call {
                prefix: None,
                value: Value {
                    targets: vec![0],
                    unknown: false,
                    ..Value::default()
                },
                ty: 0,
                source: span,
            }],
        };
        let run = |budget: &mut TypeWorkBudget| {
            let mut analysis =
                Analysis::new(&graph, None, &mut TypeWorkBudget::unbounded()).unwrap();
            // Keep replacement lookup constant-cost so it cannot conceal the
            // independent scan over already bound formal variables.
            let integer = analysis
                .types
                .iter()
                .position(|ty| matches!(ty, Type::Int))
                .unwrap();
            analysis.types.swap_ordinals(0, integer);
            let context = analysis.call_context(0, 0, 0, budget)?;
            assert_eq!(analysis.contexts[context].bindings.len(), WIDTH);
            Ok::<(), Failure>(())
        };
        let mut measured = TypeWorkBudget::unbounded();
        run(&mut measured).unwrap();
        assert!(
            measured.used() >= WIDTH * (WIDTH - 1) / 2,
            "{} units omitted the accumulated-binding scans",
            measured.used()
        );
        let mut exact = TypeWorkBudget::with_limit(measured.used());
        run(&mut exact).unwrap();
        assert_eq!(exact.used(), measured.used());
        assert!(matches!(
            run(&mut TypeWorkBudget::with_limit(measured.used() - 1)),
            Err(Failure::Resource)
        ));
        let mut retry = TypeWorkBudget::with_limit(measured.used());
        run(&mut retry).unwrap();
        assert_eq!(retry.used(), measured.used());
    }

    #[test]
    fn deep_abandonment_query_is_stack_safe_exact_and_retryable() {
        std::thread::Builder::new()
            .stack_size(64 * 1024)
            .spawn(|| {
                let source = SourceFile::new("deep-query", "x").unwrap();
                let span = source.span(ByteRange::new(0, 1).unwrap()).unwrap();
                let effect = EffectInstance::new(EffectId::new(ModuleId::new(0), 0), Box::new([]));
                let mut preparation = TypeWorkBudget::unbounded();
                let mut graph = SummaryGraph {
                    effects: true,
                    data: None,
                    callables: CallableSlots::default(),
                    types: TypeArguments(Vec::new()),
                    code: vec![
                        Control::Return,
                        Control::Request(Request::effect(&effect, span, &mut preparation).unwrap()),
                        Control::Discard {
                            owner: 2,
                            node: 2,
                            local: true,
                            row_type: 0,
                            source: span,
                        },
                    ],
                };
                let mut body = 1;
                for _ in 0..384 {
                    let next = graph.code.len();
                    graph.code.push(Control::Sequence(vec![body, 0]));
                    body = next;
                }
                let root = graph.code.len();
                graph.code.push(Control::Handler {
                    body,
                    effect: Request::effect(&effect, span, &mut preparation).unwrap(),
                    clauses: vec![Clause {
                        operation: None,
                        body: 2,
                        owner: 2,
                        source: span,
                    }],
                });
                let run = |budget: &mut TypeWorkBudget| {
                    Analysis::new(&graph, None, budget)?.check(&[root], budget)
                };
                let mut measured = TypeWorkBudget::unbounded();
                run(&mut measured).unwrap();
                let mut exact = TypeWorkBudget::with_limit(measured.used());
                run(&mut exact).unwrap();
                assert_eq!(exact.used(), measured.used());
                assert!(matches!(
                    run(&mut TypeWorkBudget::with_limit(measured.used() - 1)),
                    Err(Failure::Resource)
                ));
                let mut retry = TypeWorkBudget::with_limit(measured.used());
                run(&mut retry).unwrap();
                assert_eq!(retry.used(), measured.used());
                eprintln!(
                    "deep abandonment query: {} control positions, {} charged work units",
                    graph.code.len(),
                    measured.used()
                );
            })
            .unwrap()
            .join()
            .unwrap();
    }

    #[test]
    fn row_tail_contexts_bind_callback_identity_without_conflating_local_rows() {
        use crate::types::EffectRowVariable;
        let source = SourceFile::new("row-context", "x").unwrap();
        let span = source.span(ByteRange::new(0, 1).unwrap()).unwrap();
        let effect = EffectId::new(ModuleId::new(0), 0);
        let row_e = TypeVariableId::new(0);
        let row_f = TypeVariableId::new(1);
        let identity = TypeVariableId::new(2);
        let owner_a = TypeVariableId::new(3);
        let owner_b = TypeVariableId::new(4);
        let instance = |variable| EffectInstance::new(effect, Box::new([Type::Variable(variable)]));
        let open = |variable| EffectRow::open(EffectRowVariable::rigid(variable), Box::new([]));
        let closed = |variable| EffectRow::singleton(instance(variable));
        let callback =
            |row| Type::function_computation(Type::Unit, ComputationType::new(Type::Int, row));
        let relay = |left, right, output| {
            Type::function_computation(
                Type::Tuple(vec![callback(left), callback(right)].into_boxed_slice()),
                ComputationType::new(Type::Int, output),
            )
        };
        let mut preparation = TypeWorkBudget::unbounded();
        let graph = SummaryGraph {
            effects: true,
            data: None,
            callables: vec![
                Callable {
                    body: 0,
                    ty: relay(open(row_e), open(row_f), open(row_e)),
                    result: Value::default(),
                },
                Callable {
                    body: 0,
                    ty: callback(closed(identity)),
                    result: Value::default(),
                },
            ]
            .into(),
            types: TypeArguments(vec![
                relay(closed(owner_a), closed(owner_b), closed(owner_a)),
                callback(open(row_e)),
                callback(open(row_f)),
            ]),
            code: vec![
                Control::Return,
                Control::Call {
                    prefix: None,
                    value: Value::default(),
                    ty: 0,
                    source: span,
                },
                Control::Call {
                    prefix: None,
                    value: Value::default(),
                    ty: 1,
                    source: span,
                },
                Control::Call {
                    prefix: None,
                    value: Value::default(),
                    ty: 2,
                    source: span,
                },
                Control::Request(
                    Request::effect(&instance(identity), span, &mut preparation).unwrap(),
                ),
                Control::Request(
                    Request::effect(&instance(owner_a), span, &mut preparation).unwrap(),
                ),
                Control::Request(
                    Request::effect(&instance(owner_b), span, &mut preparation).unwrap(),
                ),
            ],
        };
        let run = |budget: &mut TypeWorkBudget| {
            let mut analysis = Analysis::new(&graph, None, budget)?;
            let relay = analysis.call_context(1, 0, 0, budget)?;
            for (call, expected, unrelated) in [(2, 5, 6), (3, 6, 5)] {
                let context = analysis.call_context(call, 1, relay, budget)?;
                let request = analysis.label(4, context, budget)?;
                let expected = analysis.label(expected, 0, budget)?;
                let unrelated = analysis.label(unrelated, 0, budget)?;
                assert_eq!(
                    analysis.match_labels(request, expected, budget)?,
                    (true, false),
                    "the referenced row must supply the exact identity"
                );
                assert_ne!(
                    analysis.match_labels(request, unrelated, budget)?,
                    (true, false),
                    "a locally handled F must not borrow enclosing E"
                );
            }
            Ok::<(), Failure>(())
        };
        let mut measured = TypeWorkBudget::unbounded();
        run(&mut measured).unwrap();
        assert!(matches!(
            run(&mut TypeWorkBudget::with_limit(measured.used() - 1)),
            Err(Failure::Resource)
        ));
        for _ in 0..2 {
            run(&mut TypeWorkBudget::with_limit(measured.used())).unwrap();
        }
    }

    #[test]
    fn formal_known_scan_preflights_pure_and_open_actual_rows_with_exact_retries() {
        let source = SourceFile::new("formal-known-scan", "x").unwrap();
        let span = source.span(ByteRange::new(0, 1).unwrap()).unwrap();
        for open in [false, true] {
            let mut costs = Vec::new();
            for width in [1, 4096] {
                let actual = if open {
                    Type::function_computation(
                        Type::Unit,
                        ComputationType::new(
                            Type::Int,
                            EffectRow::open(
                                EffectRowVariable::rigid(TypeVariableId::new(0)),
                                Box::new([]),
                            ),
                        ),
                    )
                } else {
                    Type::Function(Box::new(Type::Unit), Box::new(Type::Int))
                };
                let formal = Type::function_computation(
                    Type::Unit,
                    ComputationType::new(
                        Type::Int,
                        EffectRow::closed(
                            (0..width)
                                .map(|ordinal| {
                                    EffectInstance::new(
                                        EffectId::new(ModuleId::new(0), ordinal),
                                        Box::new([]),
                                    )
                                })
                                .collect(),
                        ),
                    ),
                );
                let graph = SummaryGraph {
                    effects: true,
                    data: None,
                    callables: vec![Callable {
                        body: 0,
                        ty: formal,
                        result: Value::default(),
                    }]
                    .into(),
                    types: TypeArguments(vec![actual]),
                    code: vec![Control::Call {
                        prefix: None,
                        value: Value::default(),
                        ty: 0,
                        source: span,
                    }],
                };
                let run = |budget: &mut TypeWorkBudget| {
                    let mut analysis =
                        Analysis::new(&graph, None, &mut TypeWorkBudget::unbounded()).unwrap();
                    let outcome = analysis.call_context(0, 0, 0, budget);
                    if outcome.is_err() {
                        assert!(
                            analysis.call_cache.is_empty(),
                            "failed work must not cache a call context"
                        );
                        assert_eq!(
                            analysis.contexts.len(),
                            1,
                            "failed work must not publish a context"
                        );
                    }
                    assert_eq!(
                        outcome?, 0,
                        "pure and unresolved actual rows yield no identity binding"
                    );
                    Ok::<(), Failure>(())
                };
                let mut measured = TypeWorkBudget::unbounded();
                run(&mut measured).unwrap();
                assert!(
                    measured.used() >= width as usize,
                    "formal width {width}, open={open}: only {} work units charged",
                    measured.used()
                );
                costs.push(measured.used());
                for limit in [0, width as usize - 1, measured.used() - 1] {
                    assert!(matches!(
                        run(&mut TypeWorkBudget::with_limit(limit)),
                        Err(Failure::Resource)
                    ));
                }
                for _ in 0..2 {
                    let mut exact = TypeWorkBudget::with_limit(measured.used());
                    run(&mut exact).unwrap();
                    assert_eq!(exact.used(), measured.used());
                }
            }
            assert_eq!(
                costs[1] - costs[0],
                4095,
                "each formal label must have one admitted visit"
            );
        }
    }

    #[test]
    fn row_context_records_empty_effects_from_erased_pure_function_types() {
        use crate::types::EffectRowVariable;
        let source = SourceFile::new("empty-row-context", "x").unwrap();
        let span = source.span(ByteRange::new(0, 1).unwrap()).unwrap();
        let row = TypeVariableId::new(0);
        let callback = || {
            Type::function_computation(
                Type::Unit,
                ComputationType::new(
                    Type::Int,
                    EffectRow::open(EffectRowVariable::rigid(row), Box::new([])),
                ),
            )
        };
        let pure = || Type::Function(Box::new(Type::Unit), Box::new(Type::Int));
        let graph = SummaryGraph {
            effects: true,
            data: None,
            callables: vec![Callable {
                body: 0,
                ty: Type::function_computation(
                    callback(),
                    ComputationType::new(
                        Type::Int,
                        EffectRow::open(EffectRowVariable::rigid(row), Box::new([])),
                    ),
                ),
                result: Value::default(),
            }]
            .into(),
            types: TypeArguments(vec![Type::Function(Box::new(pure()), Box::new(Type::Int))]),
            code: vec![Control::Call {
                prefix: None,
                value: Value::default(),
                ty: 0,
                source: span,
            }],
        };
        let run = |budget: &mut TypeWorkBudget| {
            let mut analysis = Analysis::new(&graph, None, budget)?;
            let context = analysis.call_context(0, 0, 0, budget)?;
            let actual = TypeArguments(vec![analysis.substitute(&callback(), context, budget)?]);
            assert_eq!(actual.0[0], pure());
            Ok::<(), Failure>(())
        };
        let mut measured = TypeWorkBudget::unbounded();
        run(&mut measured).unwrap();
        assert!(matches!(
            run(&mut TypeWorkBudget::with_limit(measured.used() - 1)),
            Err(Failure::Resource)
        ));
        for _ in 0..2 {
            run(&mut TypeWorkBudget::with_limit(measured.used())).unwrap();
        }
    }

    #[test]
    fn opaque_row_exclusions_are_exact_interned_and_charged() {
        let source = SourceFile::new("opaque-exclusions", "x").unwrap();
        let span = source.span(ByteRange::new(0, 1).unwrap()).unwrap();
        let effect = EffectId::new(ModuleId::new(0), 0);
        let instance = |ty| EffectInstance::new(effect, Box::new([ty]));
        let graph = SummaryGraph {
            effects: true,
            data: None,
            callables: CallableSlots::default(),
            types: TypeArguments(Vec::new()),
            code: Vec::new(),
        };
        let run = |budget: &mut TypeWorkBudget| {
            for reverse in [false, true] {
                for (excluded, handled, widened, matches) in [
                    (
                        Type::Variable(TypeVariableId::new(0)),
                        Type::Variable(TypeVariableId::new(0)),
                        false,
                        false,
                    ),
                    (
                        Type::Variable(TypeVariableId::new(0)),
                        Type::Variable(TypeVariableId::new(1)),
                        false,
                        true,
                    ),
                    (Type::Int, Type::Int, false, false),
                    (Type::Int, Type::Int, true, true),
                ] {
                    let mut analysis = Analysis::new(&graph, None, budget)?;
                    let row = EffectRow::open(
                        EffectRowVariable::rigid(TypeVariableId::new(2)),
                        Box::new([instance(excluded)]),
                    );
                    let mut refined = Request::unknown(span);
                    refined.opaque_row = Some(Arc::new(
                        clone_effect_row_with_budget(&row, budget)
                            .map_err(|_| Failure::Resource)?,
                    ));
                    refined.ambiguous_instance = widened;
                    let bare = Request::unknown(span);
                    let (bare, refined) = if reverse {
                        let refined = analysis.intern_label(refined, budget)?;
                        (analysis.intern_label(bare, budget)?, refined)
                    } else {
                        let bare = analysis.intern_label(bare, budget)?;
                        (bare, analysis.intern_label(refined, budget)?)
                    };
                    assert_ne!(bare, refined);
                    let handler = Request::effect(&instance(handled), span, budget)?;
                    let handler = analysis.intern_label(handler, budget)?;
                    assert!(analysis.match_labels(bare, handler, budget)?.0);
                    assert_eq!(analysis.match_labels(refined, handler, budget)?.0, matches);
                }
            }
            Ok::<(), Failure>(())
        };
        let mut measured = TypeWorkBudget::unbounded();
        run(&mut measured).unwrap();
        assert!(matches!(
            run(&mut TypeWorkBudget::with_limit(measured.used() - 1)),
            Err(Failure::Resource)
        ));
        for _ in 0..2 {
            run(&mut TypeWorkBudget::with_limit(measured.used())).unwrap();
        }
    }

    #[test]
    fn type_universe_collision_keeps_complete_owner_rows_and_first_ordinals() {
        use crate::types::{Kind, ResourceDefinitionId};
        let module = ModuleId::new(0);
        let owner = ResourceDefinitionId::new(module, 0);
        let effect = EffectId::new(module, 0);
        let excluded = EffectId::new(module, 1);
        let row = |tail, payload| {
            EffectRow::with_tail(
                Box::new([EffectInstance::new(effect, Box::new([Type::Int]))]),
                EffectRowVariable::rigid(TypeVariableId::new(tail)),
                Box::new([EffectInstance::new(excluded, Box::new([payload]))]),
            )
        };
        let owned =
            |family, row| Type::ResourceApply(family, Box::new([KindedArgument::RowArg(row)]));
        let originals = vec![
            owned(owner, row(0, Type::Int)),
            owned(owner, row(1, Type::Int)),
            owned(
                owner,
                EffectRow::with_tail(
                    Box::new([EffectInstance::new(effect, Box::new([Type::Bool]))]),
                    EffectRowVariable::rigid(TypeVariableId::new(0)),
                    Box::new([EffectInstance::new(excluded, Box::new([Type::Int]))]),
                ),
            ),
            owned(owner, row(0, Type::Bool)),
            owned(ResourceDefinitionId::new(module, 1), row(0, Type::Int)),
            Type::ResourceApply(owner, Box::new([KindedArgument::TypeArg(Type::Int)])),
            Type::Forall(
                Box::new([(TypeVariableId::new(2), Kind::Type)]),
                Box::new(Type::Variable(TypeVariableId::new(2))),
            ),
            Type::Forall(
                Box::new([(TypeVariableId::new(2), Kind::EffectRow)]),
                Box::new(Type::Variable(TypeVariableId::new(2))),
            ),
            Type::Forall(
                Box::new([(TypeVariableId::new(3), Kind::Type)]),
                Box::new(Type::Variable(TypeVariableId::new(3))),
            ),
            Type::function(Type::Unit, Type::Int),
            Type::EffectfulFunction(
                Box::new(Type::Unit),
                Box::new(ComputationType::new(Type::Int, EffectRow::empty())),
            ),
            owned(owner, row(0, Type::Int)),
        ];
        let mut types = Vec::new();
        let mut buckets = HashMap::new();
        for (ordinal, ty) in originals.iter().enumerate() {
            let retained = retain_type_universe_entry(
                &mut types,
                &mut buckets,
                ty,
                0,
                &mut TypeWorkBudget::unbounded(),
            )
            .unwrap();
            assert_eq!(retained, ordinal < 10);
        }
        assert_eq!(types.len(), 10);
        assert_eq!(buckets.get(&0).unwrap(), &(0..10).collect::<Vec<_>>());
        for (retained, original) in types.iter().zip(&originals) {
            assert!(std::ptr::eq(*retained, original));
        }
        // A forced collision must run exact equality and refuse a corrupt index.
        buckets.get_mut(&0).unwrap().push(usize::MAX);
        let fresh = Type::Bytes;
        assert!(matches!(
            retain_type_universe_entry(
                &mut types,
                &mut buckets,
                &fresh,
                0,
                &mut TypeWorkBudget::unbounded(),
            ),
            Err(Failure::Invalid)
        ));
        assert_eq!(types.len(), 10);

        // Every refusal before a new colliding entry commits preserves the prior universe.
        let first = Type::Int;
        let next = &originals[0];
        for prefix in [0, 9] {
            let seed = || {
                let mut types = Vec::new();
                let mut buckets = HashMap::new();
                retain_type_universe_entry(
                    &mut types,
                    &mut buckets,
                    &first,
                    0,
                    &mut TypeWorkBudget::unbounded(),
                )
                .unwrap();
                (types, buckets)
            };
            let (mut measured_types, mut measured_buckets) = seed();
            let mut measured = TypeWorkBudget::unbounded();
            measured.charge(prefix).unwrap();
            retain_type_universe_entry(
                &mut measured_types,
                &mut measured_buckets,
                next,
                0,
                &mut measured,
            )
            .unwrap();
            let cost = measured.used() - prefix;
            for available in 0..cost {
                let (mut types, mut buckets) = seed();
                let mut short = TypeWorkBudget::with_limit(prefix + available);
                short.charge(prefix).unwrap();
                assert!(matches!(
                    retain_type_universe_entry(&mut types, &mut buckets, next, 0, &mut short,),
                    Err(Failure::Resource)
                ));
                assert_eq!(types.len(), 1);
                assert!(std::ptr::eq(types[0], &first));
                assert_eq!(buckets.get(&0).unwrap(), &[0]);
                let mut retry = TypeWorkBudget::with_limit(prefix + cost);
                retry.charge(prefix).unwrap();
                assert!(
                    retain_type_universe_entry(&mut types, &mut buckets, next, 0, &mut retry,)
                        .unwrap()
                );
                assert_eq!(retry.used(), prefix + cost);
                assert_eq!(buckets.get(&0).unwrap(), &[0, 1]);
            }
        }
    }

    #[test]
    fn prepaid_control_scan_keeps_no_control_rows_and_queries_unobserved() {
        let source = SourceFile::new("no-control-scan", "x").unwrap();
        let span = source.span(ByteRange::new(0, 1).unwrap()).unwrap();
        let instance = EffectInstance::new_kinded(
            EffectId::new(ModuleId::new(0), 0),
            Box::new([KindedArgument::RowArg(EffectRow::open(
                EffectRowVariable::rigid(TypeVariableId::new(0)),
                Box::new([]),
            ))]),
        );
        let request = Request::effect(&instance, span, &mut TypeWorkBudget::unbounded()).unwrap();
        let graph = SummaryGraph {
            effects: true,
            data: None,
            callables: CallableSlots::default(),
            types: TypeArguments(Vec::new()),
            code: vec![
                Control::NativeInterpret {
                    body: usize::MAX,
                    effects: vec![request.clone()],
                },
                Control::Handler {
                    body: usize::MAX,
                    effect: request,
                    clauses: Vec::new(),
                },
            ],
        };
        // These rows need more work if prepared, and their unreachable bodies
        // are not valid query roots. The historical no-control path reads neither.
        assert!(matches!(
            ControlCodeInventory::prepare(
                &graph,
                &mut TypeWorkBudget::with_limit(graph.code.len())
            ),
            Err(Failure::Resource)
        ));
        for prefix in [0, 7] {
            let mut short = TypeWorkBudget::with_limit(prefix + graph.code.len() - 1);
            short.charge(prefix).unwrap();
            assert!(matches!(
                super::super::check_control_roots_with_rows(
                    &graph,
                    vec![usize::MAX],
                    true,
                    &mut short
                ),
                Err(Failure::Resource)
            ));
            for _ in 0..2 {
                let mut exact = TypeWorkBudget::with_limit(prefix + graph.code.len());
                exact.charge(prefix).unwrap();
                assert!(
                    super::super::check_control_roots_with_rows(
                        &graph,
                        vec![usize::MAX],
                        true,
                        &mut exact
                    )
                    .unwrap()
                    .is_empty()
                );
                assert_eq!(exact.used(), prefix + graph.code.len());
                assert!(matches!(
                    PrepaidControlCodeScan::for_roots(&graph, &mut exact),
                    Err(Failure::Resource)
                ));
            }
        }
    }

    #[test]
    fn prepaid_control_scan_keeps_discard_gate_distinct_and_literal_meters_bound() {
        let source = SourceFile::new("discard-control-scan", "x").unwrap();
        let span = source.span(ByteRange::new(0, 1).unwrap()).unwrap();
        let graph = SummaryGraph {
            effects: true,
            data: None,
            callables: CallableSlots::default(),
            types: TypeArguments(Vec::new()),
            code: vec![
                Control::Return,
                Control::Discard {
                    owner: 0,
                    node: 0,
                    local: true,
                    row_type: 0,
                    source: span,
                },
            ],
        };
        let donor = SummaryGraph {
            effects: false,
            data: None,
            callables: CallableSlots::default(),
            types: TypeArguments(Vec::new()),
            code: vec![Control::Return],
        };
        let mut work = TypeWorkBudget::unbounded();
        let scan = PrepaidControlCodeScan::for_roots(&graph, &mut work)
            .unwrap()
            .unwrap();
        let inventory = scan.into_inventory(&mut work).unwrap();
        assert!(std::ptr::eq(inventory.graph, &graph));
        assert!(!std::ptr::eq(inventory.graph, &donor));
        assert!(
            !inventory.has_resource,
            "Discard alone must not require a Value graph"
        );
        Analysis::from_code_inventory(inventory, None, &mut work).unwrap();
        Analysis::new(&graph, None, &mut TypeWorkBudget::unbounded()).unwrap();

        let mut original = TypeWorkBudget::unbounded();
        let scan = PrepaidControlCodeScan::for_roots(&graph, &mut original)
            .unwrap()
            .unwrap();
        let original_used = original.used();
        let mut other = TypeWorkBudget::unbounded();
        assert!(matches!(
            scan.into_inventory(&mut other),
            Err(Failure::Invalid)
        ));
        assert_eq!(
            original.used(),
            original_used,
            "a refusal does not refund gate work"
        );
        assert_eq!(other.used(), 1, "the rejected consume is itself paid");
        let scan = PrepaidControlCodeScan::for_roots(&graph, &mut original)
            .unwrap()
            .unwrap();
        Analysis::from_prepaid_control_scan(scan, None, &mut original).unwrap();
    }

    #[test]
    fn prepaid_control_scan_preserves_native_prefix_rows_and_pruned_root_checks() {
        let source = SourceFile::new("native-prefix-control-scan", "x").unwrap();
        let span = source.span(ByteRange::new(0, 1).unwrap()).unwrap();
        let instance = EffectInstance::new_kinded(
            EffectId::new(ModuleId::new(0), 0),
            Box::new([KindedArgument::RowArg(EffectRow::open(
                EffectRowVariable::rigid(TypeVariableId::new(0)),
                Box::new([]),
            ))]),
        );
        let request = Request::effect(&instance, span, &mut TypeWorkBudget::unbounded()).unwrap();
        let graph = SummaryGraph {
            effects: true,
            data: None,
            callables: CallableSlots::default(),
            types: TypeArguments(Vec::new()),
            code: vec![
                Control::Return,
                Control::NativeInterpret {
                    body: 0,
                    effects: vec![request],
                },
                Control::Discard {
                    owner: 0,
                    node: 0,
                    local: true,
                    row_type: 0,
                    source: span,
                },
            ],
        };
        let mut work = TypeWorkBudget::unbounded();
        let standalone = ControlCodeInventory::prepare(&graph, &mut work).unwrap();
        assert_eq!(standalone.owner_rows.len(), 1);
        let scan = PrepaidControlCodeScan::for_roots(&graph, &mut work)
            .unwrap()
            .unwrap();
        let prepaid = scan.into_inventory(&mut work).unwrap();
        assert_eq!(prepaid.owner_rows.len(), standalone.owner_rows.len());
        assert!(std::ptr::eq(
            prepaid.owner_rows[0],
            standalone.owner_rows[0]
        ));

        let graph = SummaryGraph {
            effects: true,
            data: None,
            callables: CallableSlots::default(),
            types: TypeArguments(Vec::new()),
            code: vec![
                Control::Return,
                Control::Resource {
                    body: 0,
                    effect: Request::unknown(span),
                },
            ],
        };
        // Return is pruned, but an empty query list still constructs Analysis.
        // The missing required Value graph must therefore remain a refusal.
        assert!(matches!(
            super::super::check_control_roots_with_rows(
                &graph,
                vec![0],
                false,
                &mut TypeWorkBudget::unbounded()
            ),
            Err(Failure::Invalid)
        ));
    }

    #[test]
    fn complete_code_inventory_preserves_nested_owner_rows_and_hidden_resource_gates() {
        let module = ModuleId::new(0);
        let source = SourceFile::new("code-inventory", "x").unwrap();
        let span = source.span(ByteRange::new(0, 1).unwrap()).unwrap();
        let nested = EffectRow::open(
            EffectRowVariable::rigid(TypeVariableId::new(0)),
            Box::new([]),
        );
        let excluded_nested = EffectRow::open(
            EffectRowVariable::rigid(TypeVariableId::new(2)),
            Box::new([]),
        );
        let outer = EffectRow::with_tail(
            Box::new([EffectInstance::new_kinded(
                EffectId::new(module, 1),
                Box::new([KindedArgument::RowArg(nested)]),
            )]),
            EffectRowVariable::rigid(TypeVariableId::new(1)),
            Box::new([EffectInstance::new_kinded(
                EffectId::new(module, 2),
                Box::new([KindedArgument::RowArg(excluded_nested)]),
            )]),
        );
        let instance = EffectInstance::new_kinded(
            EffectId::new(module, 0),
            Box::new([KindedArgument::RowArg(outer)]),
        );
        let request = Request::effect(&instance, span, &mut TypeWorkBudget::unbounded()).unwrap();
        let graph = SummaryGraph {
            effects: true,
            data: None,
            callables: CallableSlots::default(),
            types: TypeArguments(Vec::new()),
            code: vec![
                Control::Return,
                Control::Request(request.clone()),
                Control::Handler {
                    body: 0,
                    effect: request.clone(),
                    clauses: Vec::new(),
                },
                Control::Resource {
                    body: 0,
                    effect: request.clone(),
                },
                Control::Registration {
                    body: 0,
                    source: span,
                },
                Control::Cleanup {
                    body: 0,
                    action: 0,
                    row_type: 0,
                    source: span,
                },
                Control::Request(request.clone()),
                Control::Request(Request::unknown(span)),
            ],
        };
        let mut expected_rows = Vec::new();
        for ordinal in [1, 2, 3, 6] {
            let request = match &graph.code[ordinal] {
                Control::Request(request)
                | Control::Handler {
                    effect: request, ..
                }
                | Control::Resource {
                    effect: request, ..
                } => request,
                _ => unreachable!(),
            };
            let effect = request.effect.as_ref().unwrap();
            let KindedArgument::RowArg(outer) = &effect.arguments()[0] else {
                unreachable!()
            };
            let KindedArgument::RowArg(nested) = &outer.known()[0].arguments()[0] else {
                unreachable!()
            };
            // Canonical formation copies every known member into the tail's
            // lacks set. The copied member owns a distinct nested row which
            // must also be retained; the two equal rows are not one pointer.
            let lacks = outer.tail().unwrap().lacks();
            assert_eq!(lacks.len(), 2);
            assert_eq!(lacks[0].effect(), EffectId::new(module, 1));
            assert_eq!(lacks[1].effect(), EffectId::new(module, 2));
            let KindedArgument::RowArg(known_lacks_nested) = &lacks[0].arguments()[0] else {
                unreachable!()
            };
            let KindedArgument::RowArg(excluded_nested) = &lacks[1].arguments()[0] else {
                unreachable!()
            };
            assert!(!std::ptr::eq(nested, known_lacks_nested));
            // Explicit expected LIFO order: outer, last lacks argument,
            // canonical known-member lacks argument, known argument.
            expected_rows.extend([outer, excluded_nested, known_lacks_nested, nested]);
        }
        let run = |budget: &mut TypeWorkBudget| {
            let inventory = ControlCodeInventory::prepare(&graph, budget)?;
            assert!(std::ptr::eq(inventory.graph, &graph));
            assert!(inventory.has_resource);
            assert_eq!(inventory.owner_rows.len(), 16);
            for (actual, expected) in inventory.owner_rows.iter().zip(&expected_rows) {
                assert!(std::ptr::eq(*actual, *expected));
            }
            Ok::<(), Failure>(())
        };
        let mut measured = TypeWorkBudget::unbounded();
        run(&mut measured).unwrap();
        let prepaid_run = |budget: &mut TypeWorkBudget| {
            let scan = PrepaidControlCodeScan::for_roots(&graph, budget)?.unwrap();
            assert_eq!(scan.prefix, 4);
            assert_eq!(scan.unused, graph.code.len() - 4);
            let inventory = scan.into_inventory(budget)?;
            assert!(std::ptr::eq(inventory.graph, &graph));
            assert!(inventory.has_resource);
            assert_eq!(inventory.owner_rows.len(), expected_rows.len());
            for (actual, expected) in inventory.owner_rows.iter().zip(&expected_rows) {
                assert!(std::ptr::eq(*actual, *expected));
            }
            Ok::<(), Failure>(())
        };
        let mut prepaid_measured = TypeWorkBudget::unbounded();
        prepaid_run(&mut prepaid_measured).unwrap();
        // The standalone inventory already pays E. The gate adds P repeated
        // visits and its two receipt operations, rather than a second full E.
        assert_eq!(prepaid_measured.used(), measured.used() + 4 + 2);
        for prefix in [0, 7] {
            let cost = prepaid_measured.used();
            let mut short = TypeWorkBudget::with_limit(prefix + cost - 1);
            short.charge(prefix).unwrap();
            assert!(matches!(prepaid_run(&mut short), Err(Failure::Resource)));
            for _ in 0..2 {
                let mut exact = TypeWorkBudget::with_limit(prefix + cost);
                exact.charge(prefix).unwrap();
                prepaid_run(&mut exact).unwrap();
                assert_eq!(exact.used(), prefix + cost);
                assert!(matches!(prepaid_run(&mut exact), Err(Failure::Resource)));
            }
        }
        for prefix in [0, 9] {
            for available in 0..measured.used() {
                let mut short = TypeWorkBudget::with_limit(prefix + available);
                short.charge(prefix).unwrap();
                assert!(matches!(run(&mut short), Err(Failure::Resource)));
                let mut retry = TypeWorkBudget::with_limit(prefix + measured.used());
                retry.charge(prefix).unwrap();
                run(&mut retry).unwrap();
                assert_eq!(retry.used(), prefix + measured.used());
            }
        }
        // Each hidden resource-bearing variant independently requires the Value graph.
        // A Request/Handler alone retains owner rows without granting that flag.
        for code in [
            Control::Resource {
                body: 0,
                effect: request.clone(),
            },
            Control::Registration {
                body: 0,
                source: span,
            },
            Control::Cleanup {
                body: 0,
                action: 0,
                row_type: 0,
                source: span,
            },
        ] {
            let graph = SummaryGraph {
                effects: true,
                data: None,
                callables: CallableSlots::default(),
                types: TypeArguments(Vec::new()),
                code: vec![code],
            };
            let inventory =
                ControlCodeInventory::prepare(&graph, &mut TypeWorkBudget::unbounded()).unwrap();
            assert!(inventory.has_resource);
            assert!(matches!(
                Analysis::from_code_inventory(inventory, None, &mut TypeWorkBudget::unbounded()),
                Err(Failure::Invalid)
            ));
        }
        let graph = SummaryGraph {
            effects: true,
            data: None,
            callables: CallableSlots::default(),
            types: TypeArguments(Vec::new()),
            code: vec![
                Control::Request(request.clone()),
                Control::Handler {
                    body: 0,
                    effect: request,
                    clauses: Vec::new(),
                },
            ],
        };
        let inventory =
            ControlCodeInventory::prepare(&graph, &mut TypeWorkBudget::unbounded()).unwrap();
        assert!(!inventory.has_resource);
        assert_eq!(inventory.owner_rows.len(), 8);
        Analysis::from_code_inventory(inventory, None, &mut TypeWorkBudget::unbounded()).unwrap();
    }

    #[test]
    fn type_universe_hash_preserves_constructor_order_and_owner_row_domain() {
        use crate::types::ResourceDefinitionId;
        let owner = ResourceDefinitionId::new(ModuleId::new(0), 0);
        let row = EffectRow::open(
            EffectRowVariable::rigid(TypeVariableId::new(0)),
            Box::new([]),
        );
        let mut graph = SummaryGraph {
            effects: true,
            data: None,
            callables: CallableSlots {
                positions: vec![
                    None,
                    Some(Callable {
                        body: 0,
                        ty: Type::Unit,
                        result: Value::default(),
                    }),
                    None,
                ],
                absent_unit: Type::Unit,
            },
            types: TypeArguments(vec![
                Type::ResourceApply(owner, Box::new([KindedArgument::RowArg(row)])),
                Type::function(Type::Unit, Type::Int),
                Type::function(Type::Unit, Type::Int),
                Type::Unit,
                Type::Unit,
            ]),
            code: Vec::new(),
        };
        let seed = Type::Unit;
        let run = |budget: &mut TypeWorkBudget| {
            let analysis = Analysis::new(&graph, Some(&seed), budget)?;
            assert_eq!(analysis.types.len(), 4);
            // Seed is popped first; later Unit roots and the function child
            // retain that exact borrowed representative, never a canonical copy.
            assert!(std::ptr::eq(analysis.types[0], &seed));
            assert!(std::ptr::eq(analysis.types[1], &graph.types.0[2]));
            assert_eq!(analysis.types[2], &Type::Int);
            assert!(std::ptr::eq(analysis.types[3], &graph.types.0[0]));
            let Type::ResourceApply(_, arguments) = &graph.types.0[0] else {
                unreachable!()
            };
            let KindedArgument::RowArg(row) = &arguments[0] else {
                unreachable!()
            };
            assert_eq!(analysis.owner_rows.len(), 1);
            assert!(std::ptr::eq(analysis.owner_rows[0], row));
            Ok::<(), Failure>(())
        };
        let mut measured = TypeWorkBudget::unbounded();
        run(&mut measured).unwrap();
        for prefix in [0, 9] {
            let mut short = TypeWorkBudget::with_limit(prefix + measured.used() - 1);
            short.charge(prefix).unwrap();
            assert!(matches!(run(&mut short), Err(Failure::Resource)));
            for _ in 0..2 {
                let mut exact = TypeWorkBudget::with_limit(prefix + measured.used());
                exact.charge(prefix).unwrap();
                run(&mut exact).unwrap();
                assert_eq!(exact.used(), prefix + measured.used());
            }
        }
        let later = Type::Unit;
        let mut measured_owner = TypeUniverseBuilder::new();
        let mut cold = TypeWorkBudget::unbounded();
        assert!(measured_owner.admit(&seed, &mut cold).unwrap());
        assert_eq!(cold.used(), 8); // pop is owned by the constructor, not this API
        let mut warm = TypeWorkBudget::unbounded();
        assert!(!measured_owner.admit(&later, &mut warm).unwrap());
        assert_eq!(warm.used(), 2);
        assert!(std::ptr::eq(measured_owner.into_ordered()[0], &seed));
        for prefix in [0, 9] {
            for available in 0..cold.used() {
                let mut refused = TypeUniverseBuilder::new();
                let mut short = TypeWorkBudget::with_limit(prefix + available);
                short.charge(prefix).unwrap();
                assert!(matches!(
                    refused.admit(&seed, &mut short),
                    Err(Failure::Resource)
                ));
                assert!(matches!(refused.unit, UnitPhase::Unseen));
                assert!(refused.ordered.is_empty());
                assert!(refused.buckets.is_empty());
            }
            let mut retry = TypeUniverseBuilder::new();
            let mut exact = TypeWorkBudget::with_limit(prefix + cold.used());
            exact.charge(prefix).unwrap();
            assert!(retry.admit(&seed, &mut exact).unwrap());
            assert_eq!(exact.used(), prefix + cold.used());
            assert!(matches!(retry.unit, UnitPhase::Admitted));
            for available in 0..warm.used() {
                let mut short = TypeWorkBudget::with_limit(prefix + available);
                short.charge(prefix).unwrap();
                assert!(matches!(
                    retry.admit(&later, &mut short),
                    Err(Failure::Resource)
                ));
                assert!(matches!(retry.unit, UnitPhase::Admitted));
                assert_eq!(retry.ordered.len(), 1);
                assert!(std::ptr::eq(retry.ordered[0], &seed));
            }
            let mut duplicate = TypeWorkBudget::with_limit(prefix + warm.used());
            duplicate.charge(prefix).unwrap();
            assert!(!retry.admit(&later, &mut duplicate).unwrap());
            assert_eq!(duplicate.used(), prefix + warm.used());
            assert!(std::ptr::eq(retry.into_ordered()[0], &seed));
        }
        let unseeded = Analysis::new(&graph, None, &mut TypeWorkBudget::unbounded()).unwrap();
        assert!(std::ptr::eq(
            unseeded.types[0],
            &graph.callables.absent_unit
        ));
        drop(unseeded);
        graph.callables.positions.swap(1, 2);
        let genuine = Analysis::new(&graph, None, &mut TypeWorkBudget::unbounded()).unwrap();
        assert!(std::ptr::eq(
            genuine.types[0],
            &graph.callables.positions[2].as_ref().unwrap().ty
        ));
    }

    #[test]
    fn row_type_universe_preflights_nullary_known_and_lacks_visits() {
        const WIDTH: usize = 96;
        let instance =
            |ordinal| EffectInstance::new(EffectId::new(ModuleId::new(0), ordinal), Box::new([]));
        let row = EffectRow::with_tail(
            (0..WIDTH as u32).map(instance).collect(),
            EffectRowVariable::rigid(TypeVariableId::new(0)),
            (WIDTH as u32..2 * WIDTH as u32).map(instance).collect(),
        );
        let instances = row.known().len() + row.tail().unwrap().lacks().len();
        let graph = SummaryGraph {
            effects: true,
            data: None,
            callables: CallableSlots::default(),
            types: TypeArguments(vec![Type::function_computation(
                Type::Unit,
                ComputationType::new(Type::Int, row),
            )]),
            code: Vec::new(),
        };
        for limit in [0, instances] {
            let mut budget = TypeWorkBudget::with_limit(limit);
            assert!(matches!(
                Analysis::new(&graph, None, &mut budget),
                Err(Failure::Resource)
            ));
            // The complete hash now admits each nullary row member before universe publication.
            assert_eq!(budget.used(), limit);
        }
        let mut measured = TypeWorkBudget::unbounded();
        Analysis::new(&graph, None, &mut measured).unwrap();
        assert!(matches!(
            Analysis::new(
                &graph,
                None,
                &mut TypeWorkBudget::with_limit(measured.used() - 1)
            ),
            Err(Failure::Resource)
        ));
        for _ in 0..2 {
            Analysis::new(
                &graph,
                None,
                &mut TypeWorkBudget::with_limit(measured.used()),
            )
            .unwrap();
        }
    }

    #[test]
    fn row_fact_universe_scan_preflights_nullary_and_empty_pool_work() {
        const WIDTH: usize = 96;
        let source = SourceFile::new("wide-row-facts", "x").unwrap();
        let span = source.span(ByteRange::new(0, 1).unwrap()).unwrap();
        let module = ModuleId::new(0);
        let nullary = |ordinal| EffectInstance::new(EffectId::new(module, ordinal), Box::new([]));
        let variable = TypeVariableId::new(0);
        let graph = SummaryGraph {
            effects: true,
            data: None,
            callables: CallableSlots::default(),
            types: TypeArguments(Vec::new()),
            code: Vec::new(),
        };
        for (arguments, already_unproved) in [(false, true), (false, false), (true, false)] {
            let row = if arguments {
                EffectRow::singleton(EffectInstance::new(
                    EffectId::new(module, 0),
                    vec![Type::Int; WIDTH].into_boxed_slice(),
                ))
            } else {
                EffectRow::with_tail(
                    (0..WIDTH as u32).map(nullary).collect(),
                    EffectRowVariable::rigid(TypeVariableId::new(1)),
                    (WIDTH as u32..2 * WIDTH as u32).map(nullary).collect(),
                )
            };
            let run = |early: bool, budget: &mut TypeWorkBudget| {
                let mut analysis =
                    Analysis::new(&graph, None, &mut TypeWorkBudget::unbounded()).unwrap();
                let equation = if already_unproved {
                    RowEquation::Unproved
                } else {
                    RowEquation::Residual(&row)
                };
                let outcome = analysis.row_binding(variable, equation, span, budget);
                if early {
                    assert!(
                        analysis.labels.is_empty(),
                        "the universe scan must be admitted before label publication"
                    );
                }
                let binding = outcome?;
                assert_eq!(binding.unproved, arguments || already_unproved);
                if already_unproved {
                    assert!(binding.known.is_empty());
                    assert!(binding.lacks.is_empty());
                    assert_eq!(binding.tail, None);
                }
                Ok::<(), Failure>(())
            };
            let width = row.known().len() + row.tail().map_or(0, |tail| tail.lacks().len());
            if already_unproved {
                let mut short = TypeWorkBudget::with_limit(0);
                assert!(matches!(run(true, &mut short), Err(Failure::Resource)));
                assert_eq!(short.used(), 0);
                for _ in 0..2 {
                    let mut exact = TypeWorkBudget::with_limit(1);
                    run(true, &mut exact).unwrap();
                    assert_eq!(exact.used(), 1);
                }
                continue;
            }
            // Retain both original scan cuts after the one-unit phase dispatch,
            // and separately exercise refusal of that added dispatch itself.
            for limit in [0, 1, 1 + if arguments { WIDTH } else { width - 1 }] {
                let mut budget = TypeWorkBudget::with_limit(limit);
                assert!(matches!(run(true, &mut budget), Err(Failure::Resource)));
                assert_eq!(
                    budget.used(),
                    if limit == 0 {
                        0
                    } else if arguments && limit > 1 {
                        2
                    } else {
                        1
                    }
                );
            }
            let mut measured = TypeWorkBudget::unbounded();
            run(false, &mut measured).unwrap();
            assert!(matches!(
                run(false, &mut TypeWorkBudget::with_limit(measured.used() - 1)),
                Err(Failure::Resource)
            ));
            for _ in 0..2 {
                run(false, &mut TypeWorkBudget::with_limit(measured.used())).unwrap();
            }
        }
    }

    #[test]
    fn keyed_row_facts_preserve_lacks_and_bound_the_argument_universe() {
        const WIDTH: usize = 96;
        let source = SourceFile::new("row-facts", "x").unwrap();
        let span = source.span(ByteRange::new(0, 1).unwrap()).unwrap();
        let effect = EffectId::new(ModuleId::new(0), 0);
        let instance = |ty| EffectInstance::new(effect, Box::new([ty]));
        let graph = SummaryGraph {
            effects: true,
            data: None,
            callables: CallableSlots::default(),
            types: TypeArguments(vec![Type::Int, Type::Bool]),
            code: Vec::new(),
        };
        let run = |budget: &mut TypeWorkBudget| {
            let mut analysis = Analysis::new(&graph, None, budget)?;
            let row = EffectRow::singleton(instance(Type::Int));
            let mut rows = Vec::new();
            for index in 0..WIDTH {
                rows.push(analysis.row_binding(
                    TypeVariableId::new(index as u32),
                    RowEquation::Residual(&row),
                    span,
                    budget,
                )?);
            }
            analysis.contexts.push(Context {
                bindings: Vec::new(),
                rows,
            });
            let open = |lacks| {
                Type::function_computation(
                    Type::Unit,
                    ComputationType::new(
                        Type::Int,
                        EffectRow::open(
                            EffectRowVariable::rigid(TypeVariableId::new(0)),
                            Box::new([instance(lacks)]),
                        ),
                    ),
                )
            };
            let expanded =
                TypeArguments(vec![analysis.substitute(&open(Type::Bool), 1, budget)?]);
            assert!(
                expanded.0[0]
                    .function_view()
                    .unwrap()
                    .effects()
                    .unwrap()
                    .tail()
                    .is_none()
            );
            match analysis.substitute(&open(Type::Int), 1, budget) {
                Err(Failure::Invalid) => {}
                Err(error) => return Err(error),
                Ok(ty) => {
                    let _owner = TypeArguments(vec![ty]);
                    panic!("exact lacks must not be erased");
                }
            }
            let novel = EffectRow::singleton(instance(Type::Tuple(Box::new([Type::Int]))));
            let binding = analysis.row_binding(
                TypeVariableId::new(WIDTH as u32),
                RowEquation::Residual(&novel),
                span,
                budget,
            )?;
            assert!(
                binding.unproved && binding.known.is_empty(),
                "new nested arguments cannot enlarge the finite type universe"
            );
            let alias = EffectRow::open(
                EffectRowVariable::rigid(TypeVariableId::new(WIDTH as u32 + 1)),
                Box::new([instance(Type::Bool)]),
            );
            let binding = analysis.row_binding(
                TypeVariableId::new(WIDTH as u32),
                RowEquation::Residual(&alias),
                span,
                budget,
            )?;
            assert!(
                !binding.unproved
                    && binding.tail == alias.tail().map(|tail| tail.variable())
                    && binding.lacks.len() == 1
            );
            Ok::<(), Failure>(())
        };
        let mut measured = TypeWorkBudget::unbounded();
        run(&mut measured).unwrap();
        assert!(matches!(
            run(&mut TypeWorkBudget::with_limit(measured.used() - 1)),
            Err(Failure::Resource)
        ));
        for _ in 0..2 {
            run(&mut TypeWorkBudget::with_limit(measured.used())).unwrap();
        }
    }

    #[test]
    fn keyed_rows_keep_conflicting_and_multiple_instance_matches_unproved() {
        let source = SourceFile::new("ambiguous-row", "x").unwrap();
        let span = source.span(ByteRange::new(0, 1).unwrap()).unwrap();
        let effect = EffectId::new(ModuleId::new(0), 0);
        let row = TypeVariableId::new(0);
        let identity = TypeVariableId::new(1);
        let instance = |ty| EffectInstance::new(effect, Box::new([ty]));
        let callback = |effects| {
            Type::function_computation(Type::Unit, ComputationType::new(Type::Int, effects))
        };
        let open = || EffectRow::open(EffectRowVariable::rigid(row), Box::new([]));
        for conflict in [false, true] {
            let actual = if conflict {
                EffectRow::singleton(instance(Type::Int))
            } else {
                EffectRow::closed(
                    vec![instance(Type::Int), instance(Type::Bool)].into_boxed_slice(),
                )
            };
            let mut preparation = TypeWorkBudget::unbounded();
            let graph = SummaryGraph {
                effects: true,
                data: None,
                callables: vec![
                    Callable {
                        body: 0,
                        ty: Type::function_computation(
                            callback(open()),
                            ComputationType::new(Type::Int, open()),
                        ),
                        result: Value::default(),
                    },
                    Callable {
                        body: 0,
                        ty: callback(EffectRow::singleton(instance(Type::Variable(identity)))),
                        result: Value::default(),
                    },
                ]
                .into(),
                types: TypeArguments(vec![
                    Type::function_computation(
                        callback(actual.clone()),
                        ComputationType::new(
                            Type::Int,
                            if conflict {
                                EffectRow::singleton(instance(Type::Bool))
                            } else {
                                actual
                            },
                        ),
                    ),
                    callback(open()),
                ]),
                code: vec![
                    Control::Call {
                        prefix: None,
                        value: Value::default(),
                        ty: 0,
                        source: span,
                    },
                    Control::Call {
                        prefix: None,
                        value: Value::default(),
                        ty: 1,
                        source: span,
                    },
                    Control::Request(
                        Request::effect(
                            &instance(Type::Variable(identity)),
                            span,
                            &mut preparation,
                        )
                        .unwrap(),
                    ),
                    Control::Request(
                        Request::effect(&instance(Type::Int), span, &mut preparation).unwrap(),
                    ),
                    Control::Request(
                        Request::effect(&instance(Type::Bool), span, &mut preparation).unwrap(),
                    ),
                ],
            };
            let run = |budget: &mut TypeWorkBudget| {
                let mut analysis = Analysis::new(&graph, None, budget)?;
                let relay = analysis.call_context(0, 0, 0, budget)?;
                if conflict {
                    assert!(analysis.contexts[relay].rows.iter().any(|row| row.unproved));
                }
                let context = analysis.call_context(1, 1, relay, budget)?;
                let request = analysis.label(2, context, budget)?;
                for concrete in [3, 4] {
                    let handler = analysis.label(concrete, 0, budget)?;
                    assert_eq!(
                        analysis.match_labels(request, handler, budget)?,
                        (true, true)
                    );
                }
                Ok::<(), Failure>(())
            };
            let mut measured = TypeWorkBudget::unbounded();
            run(&mut measured).unwrap();
            assert!(matches!(
                run(&mut TypeWorkBudget::with_limit(measured.used() - 1)),
                Err(Failure::Resource)
            ));
            for _ in 0..2 {
                run(&mut TypeWorkBudget::with_limit(measured.used())).unwrap();
            }
        }
    }

    #[test]
    fn row_only_parameter_with_multiple_instances_never_loses_a_hazard() {
        let source = SourceFile::new("capture", "x").unwrap();
        let span = source.span(ByteRange::new(0, 1).unwrap()).unwrap();
        let effect = EffectId::new(ModuleId::new(0), 0);
        let variable = TypeVariableId::new(0);
        let instance = |ty| EffectInstance::new(effect, vec![ty].into_boxed_slice());
        let function = |argument| {
            Type::function_computation(
                Type::Unit,
                ComputationType::new(
                    Type::Unit,
                    EffectRow::closed(
                        vec![instance(argument), instance(Type::Int)].into_boxed_slice(),
                    ),
                ),
            )
        };
        let mut budget = TypeWorkBudget::default();
        let graph = SummaryGraph {
            effects: true,
            data: None,
            callables: vec![Callable {
                body: 0,
                ty: function(Type::Variable(variable)),
                result: Value::default(),
            }]
            .into(),
            types: TypeArguments(vec![function(Type::Bool)]),
            code: vec![
                Control::Return,
                Control::Call {
                    prefix: None,
                    value: Value {
                        targets: vec![0],
                        unknown: false,
                        ..Value::default()
                    },
                    ty: 0,
                    source: span,
                },
                Control::Request(
                    Request::effect(&instance(Type::Variable(variable)), span, &mut budget)
                        .unwrap(),
                ),
                Control::Request(
                    Request::effect(&instance(Type::Bool), span, &mut budget).unwrap(),
                ),
                Control::Request(
                    Request::effect(
                        &EffectInstance::new(EffectId::new(ModuleId::new(0), 1), Box::new([])),
                        span,
                        &mut budget,
                    )
                    .unwrap(),
                ),
            ],
        };
        let mut analysis = Analysis::new(&graph, None, &mut budget).unwrap();
        let context = analysis.call_context(1, 0, 0, &mut budget).unwrap();
        let request = analysis.label(2, context, &mut budget).unwrap();
        let matching = analysis.label(3, 0, &mut budget).unwrap();
        let unrelated = analysis.label(4, 0, &mut budget).unwrap();
        assert!(
            analysis
                .match_labels(request, matching, &mut budget)
                .unwrap()
                .0
        );
        assert!(
            !analysis
                .match_labels(request, unrelated, &mut budget)
                .unwrap()
                .0
        );
    }

    #[test]
    fn generic_effect_arguments_may_coincide_inside_effectful_function_types() {
        let source = SourceFile::new("capture", "x").unwrap();
        let span = source.span(ByteRange::new(0, 1).unwrap()).unwrap();
        let effect = EffectId::new(ModuleId::new(0), 0);
        let latent = EffectId::new(ModuleId::new(0), 1);
        let argument = |result| {
            Type::function_computation(
                Type::Unit,
                ComputationType::new(
                    result,
                    EffectRow::closed(
                        vec![EffectInstance::new(latent, Box::new([]))].into_boxed_slice(),
                    ),
                ),
            )
        };
        let instance =
            |result| EffectInstance::new(effect, vec![argument(result)].into_boxed_slice());
        let mut budget = TypeWorkBudget::default();
        let graph = SummaryGraph {
            effects: true,
            data: None,
            callables: CallableSlots::default(),
            types: TypeArguments(Vec::new()),
            code: Vec::new(),
        };
        let mut analysis = Analysis::new(&graph, None, &mut budget).unwrap();
        let generic = analysis
            .intern_label(
                Request::effect(
                    &instance(Type::Variable(TypeVariableId::new(0))),
                    span,
                    &mut budget,
                )
                .unwrap(),
                &mut budget,
            )
            .unwrap();
        let integer = analysis
            .intern_label(
                Request::effect(&instance(Type::Int), span, &mut budget).unwrap(),
                &mut budget,
            )
            .unwrap();
        let boolean = analysis
            .intern_label(
                Request::effect(&instance(Type::Bool), span, &mut budget).unwrap(),
                &mut budget,
            )
            .unwrap();
        assert!(
            analysis
                .match_labels(generic, integer, &mut budget)
                .unwrap()
                .0
        );
        assert!(
            !analysis
                .match_labels(integer, boolean, &mut budget)
                .unwrap()
                .0
        );
    }
    #[test]
    fn completed_type_universe_lookup_keeps_first_original_and_checks_collisions() {
        let originals = [
            Type::function(Type::Unit, Type::Int),
            Type::Unit,
            Type::Bool,
            Type::Int,
            Type::EffectfulFunction(
                Box::new(Type::Unit),
                Box::new(ComputationType::new(Type::Int, EffectRow::empty())),
            ),
        ];
        let mut builder = TypeUniverseBuilder::new();
        for ty in &originals {
            builder.admit(ty, &mut TypeWorkBudget::unbounded()).unwrap();
        }
        let mut prepared = builder
            .into_prepared(&mut TypeWorkBudget::unbounded())
            .unwrap();
        assert_eq!(prepared.len(), 4);
        assert!(std::ptr::eq(prepared[0], &originals[0]));
        assert_eq!(
            prepared
                .lookup(&originals[4], &mut TypeWorkBudget::unbounded())
                .unwrap(),
            Some(0)
        );
        // Force selector collision; full equality still determines the first ID.
        let mut hasher = DefaultHasher::new();
        hash_type_with_budget(&Type::Int, &mut hasher, &mut TypeWorkBudget::unbounded()).unwrap();
        prepared.buckets.insert(hasher.finish(), vec![0, 1, 2, 3]);
        assert_eq!(
            prepared
                .lookup(&Type::Int, &mut TypeWorkBudget::unbounded())
                .unwrap(),
            Some(3)
        );
        assert_eq!(
            prepared
                .lookup(&Type::String, &mut TypeWorkBudget::unbounded())
                .unwrap(),
            None
        );
        let mut measured = TypeWorkBudget::unbounded();
        assert_eq!(prepared.lookup(&Type::Int, &mut measured).unwrap(), Some(3));
        for cut in 0..measured.used() {
            assert_eq!(
                prepared.lookup(&Type::Int, &mut TypeWorkBudget::with_limit(cut)),
                Err(())
            );
            assert!(std::ptr::eq(prepared[0], &originals[0]));
        }
        assert_eq!(
            prepared
                .lookup(&Type::Int, &mut TypeWorkBudget::with_limit(measured.used()))
                .unwrap(),
            Some(3)
        );
    }
}
