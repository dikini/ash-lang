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
    sync::Arc,
};

use super::{
    CompletionOwner, Failure, Request, Substitutions, SummaryGraph, TypeArguments, UnsafeDiscard,
    Value, charge, same_effect,
};
use crate::{
    source::Span,
    types::{
        EffectInstance, EffectRow, EffectRowVariable, KindedArgument, Type, TypeVariableId,
        TypeWorkBudget, clone_effect_row_with_budget, clone_type_with_budget,
        rebuild_effect_row_with_budget, same_type_with_budget,
        substitute_type_and_row_variables_with,
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
                pending.extend(
                    value
                        .targets
                        .iter()
                        .map(|target| graph.callables[*target].body),
                );
            }
            Self::Handler { body, clauses, .. } => {
                charge(budget, clauses.len() + 1)?;
                pending
                    .try_reserve(clauses.len() + 1)
                    .map_err(|_| Failure::Resource)?;
                pending.push(*body);
                pending.extend(clauses.iter().map(|clause| clause.body));
            }
            Self::Resume { value, .. }
            | Self::Resource { body: value, .. }
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
            Self::Call { value, ty, source } => {
                let mut value = value.copy(budget)?;
                value.relocate(target_offset, budget)?;
                Self::Call {
                    value,
                    ty: ty + type_offset,
                    source: *source,
                }
            }
            Self::Request(request) => Self::Request(request.copy(budget)?),
            Self::Resource { body, effect } => Self::Resource {
                body: body + code_offset,
                effect: effect.copy(budget)?,
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
                | Control::Registration { .. }
                | Control::Cleanup { .. }
        ) {
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
    Next(Position),
    Handler(usize),
    Resource(usize),
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

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum Frame {
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
            | Self::Registration { value_context, .. }
            | Self::Handler { value_context, .. }
            | Self::Resource { value_context, .. } => value_context,
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
            Self::Handler { code, .. } => Site::Handler(code),
            Self::Resource { code, .. } => Site::Resource(code),
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
    }
}

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct Edge {
    address: Address,
    frame: Frame,
    next: Address,
}

#[derive(Debug, Eq, Hash, PartialEq)]
struct State {
    position: Position,
    context: usize,
    value_context: usize,
    stack: Address,
    heap: Vec<Edge>,
    abandoned: Option<(usize, Event)>,
}

impl State {
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
        Ok(Self {
            position: self.position,
            context: self.context,
            value_context: self.value_context,
            stack: self.stack,
            heap: copy_slice(&self.heap, budget)?,
            abandoned: self.abandoned,
        })
    }

    fn rename(
        &mut self,
        map: &HashMap<Address, Address>,
        budget: &mut TypeWorkBudget,
    ) -> Result<(), Failure> {
        charge(budget, self.heap.len() + 1)?;
        self.stack = map.get(&self.stack).copied().unwrap_or(self.stack);
        for edge in &mut self.heap {
            edge.address = map.get(&edge.address).copied().unwrap_or(edge.address);
            edge.next = map.get(&edge.next).copied().unwrap_or(edge.next);
            edge.frame.remap(map);
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
        self.rename(&renaming, budget)?;
        let tail = renaming.get(&tail).copied().unwrap_or(tail);
        self.heap
            .try_reserve(edges.len())
            .map_err(|_| Failure::Resource)?;
        charge(budget, edges.len())?;
        for edge in edges {
            let mut frame = edge.frame;
            frame.remap(&renaming);
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
        pending.try_reserve(1).map_err(|_| Failure::Resource)?;
        pending.push(self.stack);
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

// `select` returns (can_select, can_cross). The graph is walked iteratively;
// backward reachability retains only prefixes leading to this boundary.
fn selections(
    state: &State,
    root: Address,
    mut select: impl FnMut(Frame) -> Result<(bool, bool), Failure>,
    budget: &mut TypeWorkBudget,
) -> Result<(Vec<Selection>, bool), Failure> {
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

pub(super) struct Analysis<'a> {
    graph: &'a SummaryGraph,
    types: Vec<&'a Type>,
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
    pub(super) infer_cleanup_rows: bool,
    pub(super) cleanup_rows: Vec<super::CleanupRequirement>,
}

impl<'a> Analysis<'a> {
    pub(super) fn new(
        graph: &'a SummaryGraph,
        seed: Option<&'a Type>,
        budget: &mut TypeWorkBudget,
    ) -> Result<Self, Failure> {
        charge(budget, graph.code.len())?;
        let has_resource = graph.code.iter().any(|code| {
            matches!(
                code,
                Control::Resource { .. } | Control::Registration { .. } | Control::Cleanup { .. }
            )
        });
        let mut types: Vec<&Type> = Vec::new();
        let mut owner_rows = Vec::new();
        charge(budget, graph.code.len())?;
        for code in &graph.code {
            if let Control::Request(request)
            | Control::Handler {
                effect: request, ..
            }
            | Control::Resource {
                effect: request, ..
            } = code
                && let Some(effect) = &request.effect
            {
                retain_owner_row_universe(effect.arguments(), &mut owner_rows, budget)?;
            }
        }
        let mut pending = Vec::new();
        pending
            .try_reserve(graph.types.0.len() + graph.callables.len())
            .map_err(|_| Failure::Resource)?;
        pending.extend(graph.types.0.iter());
        pending.extend(graph.callables.iter().map(|callable| &callable.ty));
        if let Some(seed) = seed {
            charge(budget, 1)?;
            pending.try_reserve(1).map_err(|_| Failure::Resource)?;
            pending.push(seed);
        }
        while let Some(ty) = pending.pop() {
            charge(budget, 1)?;
            let mut found = false;
            for previous in &types {
                if same_type_with_budget(previous, ty, budget).map_err(|_| Failure::Resource)? {
                    found = true;
                    break;
                }
            }
            if found {
                continue;
            }
            types.try_reserve(1).map_err(|_| Failure::Resource)?;
            types.push(ty);
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
        let mut contexts = Vec::new();
        contexts.try_reserve(1).map_err(|_| Failure::Resource)?;
        contexts.push(Context {
            bindings: Vec::new(),
            rows: Vec::new(),
        });
        Ok(Self {
            graph,
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
            infer_cleanup_rows: false,
            cleanup_rows: Vec::new(),
        })
    }

    fn type_replacements(
        &self,
        bindings: &[(TypeVariableId, usize)],
        budget: &mut TypeWorkBudget,
    ) -> Result<Substitutions, Failure> {
        let mut substitutions = Substitutions::default();
        for (variable, target) in bindings {
            charge(budget, 1)?;
            if *target == usize::MAX {
                continue;
            }
            substitutions
                .0
                .try_reserve(1)
                .map_err(|_| Failure::Resource)?;
            substitutions.insert(
                *variable,
                clone_type_with_budget(self.types[*target], budget)
                    .map_err(|_| Failure::Resource)?,
            );
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
        substitute_type_and_row_variables_with(
            ty,
            &substitutions.0,
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
                    crate::types::substitute_kinded_argument_with(
                        argument,
                        &substitutions.0,
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
        pending.push((&self.graph.callables[target].ty, actual));
        let mut bindings = Vec::new();
        let mut row_equations = Vec::new();
        while let Some((formal, actual)) = pending.pop() {
            charge(budget, 1)?;
            if let Type::Variable(variable) = formal {
                let mut replacement = usize::MAX;
                for (id, ty) in self.types.iter().enumerate() {
                    if same_type_with_budget(ty, actual, budget).map_err(|_| Failure::Resource)? {
                        replacement = id;
                        break;
                    }
                }
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
                    .substitute_type_variables_with_budget(&substitutions.0, budget)
                    .map_err(|_| Failure::Resource)?;
                let mut remainder = if let Some(actual) = actual {
                    clone_effect_row_with_budget(actual, budget).map_err(|_| Failure::Resource)?
                } else {
                    EffectRow::empty()
                };
                let mut unproved = false;
                for instance in formal.known() {
                    match remainder
                        .remove_exact_with_budget(instance, budget)
                        .map_err(|_| Failure::Resource)?
                    {
                        Ok(rest) => remainder = rest,
                        Err(_) => {
                            unproved = true;
                            break;
                        }
                    }
                }
                let incoming = self.row_binding(variable, &remainder, unproved, source, budget)?;
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
        row: &EffectRow,
        mut unproved: bool,
        source: Span,
        budget: &mut TypeWorkBudget,
    ) -> Result<RowBinding, Failure> {
        let mut known = Vec::new();
        let mut lacks = Vec::new();
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
                    let mut found = false;
                    for original in &self.types {
                        if same_type_with_budget(argument, original, budget)? {
                            found = true;
                            break;
                        }
                    }
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
        charge(budget, state.heap.len() + 1)?;
        if visited.contains(&state) {
            return Ok(());
        }
        let saved = state.copy(budget)?;
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

    /// The private bridge executes only selected pure source calls. Dictionary
    /// staging is already represented by exact value-graph evidence bindings.
    pub(super) fn provider_independent_call(
        graph: &'a SummaryGraph,
        targets: &[usize],
        actual: &'a Type,
        authenticated_wrapper: bool,
        budget: &mut TypeWorkBudget,
    ) -> Result<(), Failure> {
        let mut analysis = Self::new(graph, Some(actual), budget)?;
        let mut data = graph
            .data
            .as_ref()
            .ok_or(Failure::Invalid)?
            .start_provider(budget)?;
        let mut pending = Vec::new();
        let mut visited = HashSet::new();
        for target in targets {
            let callable = graph.callables.get(*target).ok_or(Failure::Invalid)?;
            let source = graph
                .data
                .as_ref()
                .ok_or(Failure::Invalid)?
                .provider_source(*target, budget)?;
            let context = analysis.context_for_actual(*target, actual, source, budget)?;
            let value_context = data.provider_invoke(*target, budget)?;
            if !authenticated_wrapper {
                data.provider_captures(*target, value_context, budget)?;
            }
            charge(budget, 1)?;
            pending.try_reserve(1).map_err(|_| Failure::Resource)?;
            pending.push((callable.body, context, value_context));
            data.provider_result(callable.body, value_context, budget)?;
        }
        while let Some((code, context, value_context)) = pending.pop() {
            charge(budget, 1)?;
            visited.try_reserve(1).map_err(|_| Failure::Resource)?;
            if !visited.insert((code, context, value_context)) {
                continue;
            }
            match graph.code.get(code).ok_or(Failure::Invalid)? {
                Control::Return => {}
                Control::Sequence(children) | Control::Choice(children) => {
                    charge(budget, children.len())?;
                    pending
                        .try_reserve(children.len())
                        .map_err(|_| Failure::Resource)?;
                    pending.extend(
                        children
                            .iter()
                            .map(|child| (*child, context, value_context)),
                    );
                }
                Control::Call { .. } => {
                    let successors = data.calls(code, value_context, budget)?;
                    if successors.unknown || successors.targets.is_empty() && !successors.returns {
                        return Err(Failure::Invalid);
                    }
                    for (target, invoked) in successors.targets {
                        let substituted = analysis.call_context(code, target, context, budget)?;
                        data.provider_captures(target, invoked, budget)?;
                        charge(budget, 1)?;
                        pending.try_reserve(1).map_err(|_| Failure::Resource)?;
                        pending.push((
                            graph.callables.get(target).ok_or(Failure::Invalid)?.body,
                            substituted,
                            invoked,
                        ));
                    }
                }
                _ => return Err(Failure::Invalid),
            }
        }
        Ok(())
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
        if self.infer_cleanup_rows {
            return Ok(());
        }
        self.check_payloads(budget)?;
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
        let mut calls = Vec::new();
        let mut observed_calls = HashSet::new();
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
                            while children.get(following).is_some_and(|child| {
                                matches!(self.graph.code[*child], Control::Return)
                            }) {
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
                                Self::enqueue(next, &mut pending, &mut visited, budget)?;
                            } else {
                                Self::enqueue_normalized(next, &mut pending, &mut visited, budget)?;
                            }
                        } else {
                            self.returned(state, &mut pending, &mut visited, budget)?;
                        }
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
                    | Control::Registration { body, .. } => {
                        let body = *body;
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
                            if !self.focusing {
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
                        Self::enqueue(next, &mut pending, &mut visited, budget)?;
                    }
                    Control::Request(_) => {
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
                    Control::Call { value, ty, source } => {
                        if self.data.is_some() {
                            charge(budget, state.heap.len() + 1)?;
                            if !observed_calls.contains(&state) {
                                observed_calls
                                    .try_reserve(1)
                                    .map_err(|_| Failure::Resource)?;
                                observed_calls.insert(state.copy(budget)?);
                                calls.try_reserve(1).map_err(|_| Failure::Resource)?;
                                calls.push(state.copy(budget)?);
                            }
                        }
                        let super::value::CallSuccessors {
                            targets,
                            unknown,
                            returns,
                        } = if let Some(data) = &mut self.data {
                            data.calls(code, state.value_context, budget)?
                        } else {
                            charge(budget, value.targets.len())?;
                            let mut targets = Vec::new();
                            targets
                                .try_reserve(value.targets.len())
                                .map_err(|_| Failure::Resource)?;
                            targets.extend(value.targets.iter().map(|target| (*target, 0)));
                            super::value::CallSuccessors {
                                targets,
                                unknown: value.unknown || value.targets.is_empty(),
                                returns: false,
                            }
                        };
                        let ty = *ty;
                        let source = *source;
                        for (target, value_context) in targets {
                            let context = self.call_context(code, target, state.context, budget)?;
                            let mut next = state.copy(budget)?;
                            next.context = context;
                            next.value_context = value_context;
                            next.position = Position {
                                code: self.graph.callables[target].body,
                                next: 0,
                            };
                            Self::enqueue_normalized(next, &mut pending, &mut visited, budget)?;
                        }
                        if returns || unknown {
                            // The opaque call may return now or request again. No
                            // uncertainty marker survives its normal return.
                            self.returned(state.copy(budget)?, &mut pending, &mut visited, budget)?;
                        }
                        if unknown {
                            let mut ty_owner = TypeArguments(Vec::new());
                            ty_owner.0.try_reserve(1).map_err(|_| Failure::Resource)?;
                            ty_owner.0.push(self.substitute(
                                &self.graph.types.0[ty],
                                state.context,
                                budget,
                            )?);
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
                                        &mut pending,
                                        &mut visited,
                                        budget,
                                    )?;
                                }
                            }
                        }
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
                                true,
                                &mut pending,
                                &mut visited,
                                budget,
                            )?;
                        }
                    }
                    Control::Discard { owner, .. } => {
                        self.completed(state, *owner, false, &mut pending, &mut visited, budget)?
                    }
                }
            }
            let Some(data) = &mut self.data else {
                break;
            };
            data.close(budget)?;
            if data.revision() == revision {
                break;
            }
            revision = data.revision();
            // Only calls choose control successors from growing value facts.
            // Replay them directly; ordinary enqueue would suppress visited states.
            charge(budget, calls.len())?;
            pending
                .try_reserve(calls.len())
                .map_err(|_| Failure::Resource)?;
            for call in &calls {
                pending.push_back(call.copy(budget)?);
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
                let seed = self.restore_entry(entry, context, budget)?;
                self.payloads.clear();
                self.discover(&[], Some(&seed), budget)?;
                self.check_payloads(budget)?;
                let data = self.data.as_mut().ok_or(Failure::Invalid)?;
                data.close(budget)?;
                data.check_resources(budget)?;
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
        for edge in &mut seed.heap {
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
                | Frame::Registration {
                    code,
                    value_context,
                    ..
                } => {
                    let body = match &self.graph.code[*code] {
                        Control::Handler { body, .. }
                        | Control::Resource { body, .. }
                        | Control::Registration { body, .. } => *body,
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
            cuts.push(cut);
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
        seed.value_context = context;
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
        data.close(budget)?;
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
                    if !consumed && !self.infer_cleanup_rows {
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

    fn requested(
        &mut self,
        state: &State,
        event: Event,
        pending: &mut VecDeque<State>,
        visited: &mut HashSet<State>,
        budget: &mut TypeWorkBudget,
    ) -> Result<(), Failure> {
        // Resolve labels first so selection's callback does not borrow the
        // shared structural work counter a second time.
        let mut matching = HashMap::new();
        charge(budget, state.heap.len())?;
        for edge in &state.heap {
            if let Frame::Handler { code, context, .. }
            | Frame::Resource { code, context, .. }
            | Frame::RemovedHandler { code, context, .. } = edge.frame
                && !matching.contains_key(&(code, context))
            {
                let label = self.label(code, context, budget)?;
                let relation = self.match_labels(event.label, label, budget)?;
                matching.try_reserve(1).map_err(|_| Failure::Resource)?;
                matching.insert((code, context), relation);
            }
        }
        let (selected, escaped) = selections(
            state,
            state.stack,
            |frame| {
                Ok(match frame {
                    Frame::Handler { code, context, .. }
                    | Frame::Resource { code, context, .. }
                    | Frame::RemovedHandler { code, context, .. } => matching[&(code, context)],
                    _ => (false, true),
                })
            },
            budget,
        )?;
        if escaped {
            if let (Some(data), Some(port)) = (&mut self.data, event.port) {
                data.external_result(port, budget)?;
            }
            let (owners, _) = selections(
                state,
                state.stack,
                |frame| Ok((matches!(frame, Frame::Resource { .. }), true)),
                budget,
            )?;
            for owner in owners {
                self.check_payload(state, event, &[owner.boundary], budget)?;
            }
            if event.unknown {
                Self::enqueue(state.copy(budget)?, pending, visited, budget)?;
            } else {
                self.returned(state.copy(budget)?, pending, visited, budget)?;
            }
        }
        for selected in selected {
            if let Frame::RemovedHandler { code, .. } = selected.boundary.frame {
                if self.infer_cleanup_rows {
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
                if let (Some(data), Some(port)) = (&mut self.data, event.port) {
                    data.external_result(port, budget)?;
                }
                // The trusted interpreter completes this operation without
                // transferring its operand outside the owning scope.
                self.returned(state.copy(budget)?, pending, visited, budget)?;
                continue;
            }
            self.check_payload(state, event, &selected.prefix, budget)?;
            let Frame::Handler {
                code: handler,
                context,
                value_context,
                capture_context,
            } = selected.boundary.frame
            else {
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
                let clause_context = if let (Some(data), Some(port)) = (&mut self.data, event.port)
                {
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
            }
        }
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
        if !self.infer_cleanup_rows {
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
            let Frame::Closing { context, .. } = driver.boundary.frame else {
                return Err(Failure::Invalid);
            };
            if discard_context.is_some_and(|previous| previous != context) {
                return Err(Failure::Invalid);
            }
            discard_context = Some(context);
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
        charge(budget, resources.len() + 1)?;
        retained
            .try_reserve(resources.len())
            .map_err(|_| Failure::Resource)?;
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
        self.cleanup_rows
            .try_reserve(1)
            .map_err(|_| Failure::Resource)?;
        self.cleanup_rows.push(super::CleanupRequirement {
            discard: node,
            local,
            code: discard,
            source,
            context: discard_context,
            expected,
            row,
            retained,
        });
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
                    Frame::Cleanup {
                        code,
                        running: true,
                        ..
                    } if !self.infer_cleanup_rows => {
                        let Control::Cleanup { source, .. } = self.graph.code[code] else {
                            return Err(Failure::Invalid);
                        };
                        return Err(self.unsafe_discard(
                            discard,
                            event,
                            Some(CompletionOwner::Cleanup(source)),
                        ));
                    }
                    Frame::Closing { .. } if !self.infer_cleanup_rows => {
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
        resume: bool,
        pending: &mut VecDeque<State>,
        visited: &mut HashSet<State>,
        budget: &mut TypeWorkBudget,
    ) -> Result<(), Failure> {
        let (selected, escaped) = selections(
            &state,
            state.stack,
            |frame| {
                Ok(match frame {
                    Frame::Clause {
                        owner: candidate, ..
                    } if candidate == owner => (true, false),
                    _ => (false, true),
                })
            },
            budget,
        )?;
        if escaped {
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
            if !resume && event.unknown && !self.infer_cleanup_rows {
                return Err(self.unsafe_discard(state.position.code, event, None));
            }
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
            } else {
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
                    return Err(failure);
                }
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::core::capture::Callable;
    use crate::{
        module::ModuleId,
        source::{ByteRange, SourceFile},
        types::{ComputationType, EffectId, EffectRow},
    };

    #[test]
    fn wide_resource_free_call_targets_preflight_and_retry_exactly() {
        const WIDTH: usize = 128;
        let source = SourceFile::new("wide-targets", "x").unwrap();
        let span = source.span(ByteRange::new(0, 1).unwrap()).unwrap();
        let ty = || Type::Function(Box::new(Type::Unit), Box::new(Type::Unit));
        let graph = SummaryGraph {
            effects: true,
            data: None,
            callables: vec![Callable {
                body: 0,
                ty: ty(),
                result: Value::default(),
            }],
            types: TypeArguments(vec![ty()]),
            code: vec![
                Control::Return,
                Control::Call {
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
    }

    #[test]
    fn tail_resume_preserves_captured_resource_and_outside_live_clause() {
        let graph = SummaryGraph {
            effects: true,
            data: None,
            callables: vec![],
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
                    true,
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
            callables: vec![],
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
                true,
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
            callables: vec![],
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
            }],
            types: TypeArguments(vec![actual]),
            code: vec![Control::Call {
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
            analysis.types.swap(0, integer);
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
                    callables: Vec::new(),
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
            ],
            types: TypeArguments(vec![
                relay(closed(owner_a), closed(owner_b), closed(owner_a)),
                callback(open(row_e)),
                callback(open(row_f)),
            ]),
            code: vec![
                Control::Return,
                Control::Call {
                    value: Value::default(),
                    ty: 0,
                    source: span,
                },
                Control::Call {
                    value: Value::default(),
                    ty: 1,
                    source: span,
                },
                Control::Call {
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
                    }],
                    types: TypeArguments(vec![actual]),
                    code: vec![Control::Call {
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
            }],
            types: TypeArguments(vec![Type::Function(Box::new(pure()), Box::new(Type::Int))]),
            code: vec![Control::Call {
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
            callables: Vec::new(),
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
            callables: Vec::new(),
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
            assert_eq!(budget.used(), usize::from(limit != 0));
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
            callables: Vec::new(),
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
                let outcome = analysis.row_binding(variable, &row, already_unproved, span, budget);
                if early {
                    assert!(
                        analysis.labels.is_empty(),
                        "the universe scan must be admitted before label publication"
                    );
                }
                let binding = outcome?;
                assert_eq!(binding.unproved, arguments || already_unproved);
                Ok::<(), Failure>(())
            };
            let width = row.known().len() + row.tail().map_or(0, |tail| tail.lacks().len());
            for limit in [0, if arguments { WIDTH } else { width - 1 }] {
                let mut budget = TypeWorkBudget::with_limit(limit);
                assert!(matches!(run(true, &mut budget), Err(Failure::Resource)));
                assert_eq!(budget.used(), if arguments && limit != 0 { 1 } else { 0 });
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
            callables: Vec::new(),
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
                    &row,
                    false,
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
                &novel,
                false,
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
                &alias,
                false,
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
                ],
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
                        value: Value::default(),
                        ty: 0,
                        source: span,
                    },
                    Control::Call {
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
            }],
            types: TypeArguments(vec![function(Type::Bool)]),
            code: vec![
                Control::Return,
                Control::Call {
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
            callables: Vec::new(),
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
}
