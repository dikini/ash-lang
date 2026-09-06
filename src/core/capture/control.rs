//! Finite control positions and continuation occurrences for capture checking.
//!
//! An address contains a static frame site, an active or handler/request capture
//! region, and a recent/older distinction. It never contains a residual, stack,
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
    Failure, Request, Substitutions, SummaryGraph, TypeArguments, UnsafeDiscard, Value, charge,
    same_effect,
};
use crate::{
    source::Span,
    types::{
        EffectInstance, Type, TypeVariableId, TypeWorkBudget, clone_type_with_budget,
        same_type_with_budget, substitute_type_variables_with,
    },
};

#[derive(Debug)]
pub(super) enum Control {
    Return,
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
    Resume {
        owner: usize,
        value: usize,
    },
    Discard {
        owner: usize,
        node: usize,
        source: Span,
    },
}

#[derive(Clone, Copy, Debug)]
pub(super) struct Clause {
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
            Self::Resume { value, .. } => {
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
            Self::Return => Self::Return,
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
                for target in &mut value.targets {
                    *target += target_offset;
                }
                Self::Call {
                    value,
                    ty: ty + type_offset,
                    source: *source,
                }
            }
            Self::Request(request) => Self::Request(request.copy(budget)?),
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
            } => Self::Discard {
                owner: owner + code_offset,
                node: *node,
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
        if matches!(graph.code[code], Control::Discard { .. }) {
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
    Next(Position),
    Handler(usize),
    Clause(usize, bool),
}

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum Region {
    Active,
    Capture(usize, usize),
}

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum Address {
    Empty,
    End,
    Slot {
        region: Region,
        site: Site,
        old: bool,
    },
}

impl Address {
    fn older(self) -> Self {
        match self {
            Self::Slot { region, site, .. } => Self::Slot {
                region,
                site,
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
}

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum Frame {
    Next {
        position: Position,
        context: usize,
    },
    Handler {
        code: usize,
        context: usize,
    },
    Clause {
        handler: usize,
        ordinal: usize,
        owner: usize,
        context: usize,
        capture: Address,
        event: Event,
        consumed: bool,
    },
}

impl Frame {
    fn site(self) -> Site {
        match self {
            Self::Next { position, .. } => Site::Next(position),
            Self::Handler { code, .. } => Site::Handler(code),
            Self::Clause {
                owner, consumed, ..
            } => Site::Clause(owner, consumed),
        }
    }
    fn remap(&mut self, map: &HashMap<Address, Address>) {
        if let Self::Clause { capture, .. } = self {
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
    stack: Address,
    heap: Vec<Edge>,
    abandoned: Option<(usize, Event)>,
}

impl State {
    fn edges(&self, address: Address, budget: &mut TypeWorkBudget) -> Result<&[Edge], Failure> {
        charge(budget, self.heap.len().max(1).ilog2() as usize * 2 + 1)?;
        let start = self.heap.partition_point(|edge| edge.address < address);
        let count = self.heap[start..].partition_point(|edge| edge.address == address);
        charge(budget, count)?;
        Ok(&self.heap[start..start + count])
    }
    fn copy(&self, budget: &mut TypeWorkBudget) -> Result<Self, Failure> {
        Ok(Self {
            position: self.position,
            context: self.context,
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
        let mut destinations = HashMap::new();
        let mut renaming = HashMap::new();
        destinations
            .try_reserve(edges.len())
            .map_err(|_| Failure::Resource)?;
        renaming
            .try_reserve(edges.len())
            .map_err(|_| Failure::Resource)?;
        for edge in edges {
            charge(budget, 1)?;
            let old = matches!(edge.address, Address::Slot { old: true, .. });
            let address = Address::Slot {
                region,
                site: edge.frame.site(),
                old,
            };
            destinations.insert(edge.address, address);
            if !old {
                renaming.insert(address, address.older());
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
            for edge in self.edges(address, budget)? {
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
        charge(budget, self.heap.len())?;
        self.heap.retain(|edge| reachable.contains(&edge.address));
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
    row: Vec<usize>,
    open: bool,
}

pub(super) struct Analysis<'a> {
    graph: &'a SummaryGraph,
    types: Vec<&'a Type>,
    contexts: Vec<Context>,
    labels: Vec<Request>,
    label_cache: HashMap<(usize, usize), usize>,
    call_cache: HashMap<(usize, usize, usize), usize>,
}

impl<'a> Analysis<'a> {
    pub(super) fn new(
        graph: &'a SummaryGraph,
        budget: &mut TypeWorkBudget,
    ) -> Result<Self, Failure> {
        let mut types: Vec<&Type> = Vec::new();
        let mut pending = Vec::new();
        pending
            .try_reserve(graph.types.0.len() + graph.callables.len())
            .map_err(|_| Failure::Resource)?;
        pending.extend(graph.types.0.iter());
        pending.extend(graph.callables.iter().map(|callable| &callable.ty));
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
                    for effect in result.effects().known() {
                        pending
                            .try_reserve(effect.arguments().len())
                            .map_err(|_| Failure::Resource)?;
                        pending.extend(effect.arguments());
                    }
                }
                _ => {}
            }
        }
        let mut contexts = Vec::new();
        contexts.try_reserve(1).map_err(|_| Failure::Resource)?;
        contexts.push(Context {
            bindings: Vec::new(),
            row: Vec::new(),
            open: true,
        });
        Ok(Self {
            graph,
            types,
            contexts,
            labels: Vec::new(),
            label_cache: HashMap::new(),
            call_cache: HashMap::new(),
        })
    }

    fn substitute(
        &self,
        ty: &Type,
        context: usize,
        budget: &mut TypeWorkBudget,
    ) -> Result<Type, Failure> {
        let mut substitutions = Substitutions::default();
        for (variable, target) in &self.contexts[context].bindings {
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
        substitute_type_variables_with(
            ty,
            &substitutions.0,
            |count| charge(budget, count),
            || Failure::Resource,
        )
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
            let mut arguments = TypeArguments(Vec::new());
            arguments
                .0
                .try_reserve(effect.arguments().len())
                .map_err(|_| Failure::Resource)?;
            for argument in effect.arguments() {
                arguments
                    .0
                    .push(self.substitute(argument, context, budget)?);
            }
            label.effect = Some(Arc::new(EffectInstance::new(
                effect.effect(),
                arguments.into_boxed_slice(),
            )));
            // Widening applies to the effect identity, never unrelated effects.
            label.ambiguous_instance |= self.contexts[context]
                .bindings
                .iter()
                .any(|(_, ty)| *ty == usize::MAX);
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
        pending.extend(ae.arguments().iter().zip(be.arguments()));
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
        let actual = &actual.0[0];
        let mut pending = Vec::new();
        pending.try_reserve(1).map_err(|_| Failure::Resource)?;
        pending.push((&self.graph.callables[target].ty, actual));
        let mut bindings = Vec::new();
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
                if let (Some(formal), Some(actual)) = (formal.effects(), actual.effects()) {
                    for effect in formal.known() {
                        charge(budget, actual.known().len() + 1)?;
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
                            pending.extend(effect.arguments().iter().zip(candidate.arguments()));
                        }
                    }
                }
            } else {
                match (formal, actual) {
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
        let mut row = Vec::new();
        let mut open = false;
        if let Some(effects) = actual
            .function_view()
            .and_then(|function| function.effects())
        {
            open = effects.tail().is_some() && self.contexts[context].open;
            for effect in effects.known() {
                let request = Request::effect(effect, *source, budget)?;
                let label = self.intern_label(request, budget)?;
                row.try_reserve(1).map_err(|_| Failure::Resource)?;
                row.push(label);
            }
            if effects.tail().is_some() {
                charge(budget, self.contexts[context].row.len())?;
                for label in &self.contexts[context].row {
                    row.try_reserve(1).map_err(|_| Failure::Resource)?;
                    row.push(*label);
                }
            }
        }
        charge(
            budget,
            row.len()
                .saturating_mul(row.len().max(1).ilog2() as usize + 1),
        )?;
        row.sort_unstable();
        row.dedup();
        // Binding traversal is determined by the retained formal type.
        let incoming = Context {
            bindings,
            row,
            open,
        };
        let mut result = None;
        for (id, previous) in self.contexts.iter().enumerate() {
            charge(budget, previous.bindings.len() + previous.row.len() + 1)?;
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
        self.call_cache
            .try_reserve(1)
            .map_err(|_| Failure::Resource)?;
        self.call_cache.insert((code, target, context), result);
        Ok(result)
    }

    fn source(&self, event: Event) -> Span {
        match &self.graph.code[event.code] {
            Control::Request(request) => request.source,
            Control::Call { source, .. } => *source,
            _ => unreachable!("events have request or call sites"),
        }
    }

    fn unsafe_discard(&self, code: usize, event: Event, owner: Option<Span>) -> Failure {
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

    pub(super) fn check(
        &mut self,
        roots: &[usize],
        budget: &mut TypeWorkBudget,
    ) -> Result<(), Failure> {
        let mut pending = VecDeque::new();
        let mut visited = HashSet::new();
        for root in roots {
            Self::enqueue(
                State {
                    position: Position {
                        code: *root,
                        next: 0,
                    },
                    context: 0,
                    stack: Address::Empty,
                    heap: Vec::new(),
                    abandoned: None,
                },
                &mut pending,
                &mut visited,
                budget,
            )?;
        }
        while let Some(state) = pending.pop_front() {
            charge(budget, 1)?;
            let code = state.position.code;
            match &self.graph.code[code] {
                Control::Return => self.returned(state, &mut pending, &mut visited, budget)?,
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
                        let position = Position {
                            code,
                            next: ordinal + 1,
                        };
                        if ordinal + 1 < children.len() {
                            next.push(
                                Frame::Next {
                                    position,
                                    context: next.context,
                                },
                                budget,
                            )?;
                        }
                        next.position = Position {
                            code: child,
                            next: 0,
                        };
                        Self::enqueue(next, &mut pending, &mut visited, budget)?;
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
                        Self::enqueue(next, &mut pending, &mut visited, budget)?;
                    }
                }
                Control::Handler { body, .. } => {
                    let body = *body;
                    let mut next = state;
                    next.push(
                        Frame::Handler {
                            code,
                            context: next.context,
                        },
                        budget,
                    )?;
                    next.position = Position {
                        code: body,
                        next: 0,
                    };
                    Self::enqueue(next, &mut pending, &mut visited, budget)?;
                }
                Control::Request(_) => {
                    let label = self.label(code, state.context, budget)?;
                    self.requested(
                        &state,
                        Event {
                            code,
                            label,
                            unknown: false,
                        },
                        &mut pending,
                        &mut visited,
                        budget,
                    )?;
                }
                Control::Call { value, ty, source } => {
                    let targets = copy_slice(&value.targets, budget)?;
                    let unknown = value.unknown || targets.is_empty();
                    let ty = *ty;
                    let source = *source;
                    for target in targets {
                        let context = self.call_context(code, target, state.context, budget)?;
                        let mut next = state.copy(budget)?;
                        next.context = context;
                        next.position = Position {
                            code: self.graph.callables[target].body,
                            next: 0,
                        };
                        Self::enqueue(next, &mut pending, &mut visited, budget)?;
                    }
                    if unknown {
                        // The opaque call may return now or request again. No
                        // uncertainty marker survives its normal return.
                        self.returned(state.copy(budget)?, &mut pending, &mut visited, budget)?;
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
                                labels
                                    .try_reserve(self.contexts[state.context].row.len() + 1)
                                    .map_err(|_| Failure::Resource)?;
                                labels.extend(&self.contexts[state.context].row);
                                if self.contexts[state.context].open {
                                    let label =
                                        self.intern_label(Request::unknown(source), budget)?;
                                    labels.push(label);
                                }
                            }
                            for label in labels {
                                self.requested(
                                    &state,
                                    Event {
                                        code,
                                        label,
                                        unknown: true,
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
                            },
                            budget,
                        )?;
                        next.position = Position {
                            code: value,
                            next: 0,
                        };
                        Self::enqueue(next, &mut pending, &mut visited, budget)?;
                    } else {
                        self.completed(state, *owner, true, &mut pending, &mut visited, budget)?;
                    }
                }
                Control::Discard { owner, .. } => {
                    self.completed(state, *owner, false, &mut pending, &mut visited, budget)?
                }
            }
        }
        Ok(())
    }

    fn returned(
        &self,
        state: State,
        pending: &mut VecDeque<State>,
        visited: &mut HashSet<State>,
        budget: &mut TypeWorkBudget,
    ) -> Result<(), Failure> {
        if state.stack == Address::Empty {
            return Ok(());
        }
        for edge in state.edges(state.stack, budget)? {
            let mut next = state.copy(budget)?;
            next.stack = edge.next;
            match edge.frame {
                Frame::Next { position, context } => {
                    next.position = position;
                    next.context = context;
                }
                Frame::Handler { context, .. } => {
                    next.position = Position { code: 0, next: 0 };
                    next.context = context;
                }
                Frame::Clause {
                    handler,
                    ordinal,
                    context,
                    consumed,
                    ..
                } => {
                    if !consumed {
                        let Control::Handler { clauses, .. } = &self.graph.code[handler] else {
                            return Err(Failure::Invalid);
                        };
                        return Err(match state.abandoned {
                            Some((discard, event)) => {
                                self.unsafe_discard(discard, event, Some(clauses[ordinal].source))
                            }
                            None => Failure::Invalid,
                        });
                    }
                    next.position = Position { code: 0, next: 0 };
                    next.context = context;
                }
            }
            Self::enqueue(next, pending, visited, budget)?;
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
            if let Frame::Handler { code, context } = edge.frame
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
                    Frame::Handler { code, context } => matching[&(code, context)],
                    _ => (false, true),
                })
            },
            budget,
        )?;
        if escaped {
            if event.unknown {
                Self::enqueue(state.copy(budget)?, pending, visited, budget)?;
            } else {
                self.returned(state.copy(budget)?, pending, visited, budget)?;
            }
        }
        for selected in selected {
            let Frame::Handler {
                code: handler,
                context,
            } = selected.boundary.frame
            else {
                return Err(Failure::Invalid);
            };
            let Control::Handler { clauses, .. } = &self.graph.code[handler] else {
                return Err(Failure::Invalid);
            };
            for (ordinal, clause) in clauses.iter().enumerate() {
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
                        old: false,
                    };
                    prefix.try_reserve(1).map_err(|_| Failure::Resource)?;
                    prefix.push(Edge {
                        address,
                        frame: Frame::Next {
                            position,
                            context: state.context,
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
                        capture,
                        event,
                        consumed: false,
                    },
                    budget,
                )?;
                next.context = context;
                next.position = Position {
                    code: clause.body,
                    next: 0,
                };
                Self::enqueue(next, pending, visited, budget)?;
            }
        }
        Ok(())
    }

    fn completed(
        &self,
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
                ..
            } = selected.boundary.frame
            else {
                return Err(Failure::Invalid);
            };
            if consumed {
                return Err(Failure::Invalid);
            }
            if !resume {
                if event.unknown {
                    return Err(self.unsafe_discard(state.position.code, event, None));
                }
                let (live, _) = selections(
                    &state,
                    capture,
                    |frame| {
                        Ok((
                            matches!(
                                frame,
                                Frame::Clause {
                                    consumed: false,
                                    ..
                                }
                            ),
                            true,
                        ))
                    },
                    budget,
                )?;
                if let Some(live) = live.first() {
                    let Frame::Clause {
                        handler, ordinal, ..
                    } = live.boundary.frame
                    else {
                        return Err(Failure::Invalid);
                    };
                    let Control::Handler { clauses, .. } = &self.graph.code[handler] else {
                        return Err(Failure::Invalid);
                    };
                    return Err(self.unsafe_discard(
                        state.position.code,
                        event,
                        Some(clauses[ordinal].source),
                    ));
                }
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
            let continuation =
                if matches!(selected.boundary.address, Address::Slot { old: false, .. }) {
                    // A recent address denotes one occurrence. Consuming it is
                    // a move, not a fresh allocation of all its ordinary frames.
                    let address = Address::Slot {
                        region: Region::Active,
                        site: selected.boundary.frame.site(),
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
                        Region::Active,
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
            }
            next.position = Position { code: 0, next: 0 };
            Self::enqueue(next, pending, visited, budget)?;
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
                },
                ty: 0,
                source: span,
            }],
        };
        let run = |budget: &mut TypeWorkBudget| {
            let mut analysis = Analysis::new(&graph, &mut TypeWorkBudget::unbounded()).unwrap();
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
                    callables: Vec::new(),
                    types: TypeArguments(Vec::new()),
                    code: vec![
                        Control::Return,
                        Control::Request(Request::effect(&effect, span, &mut preparation).unwrap()),
                        Control::Discard {
                            owner: 2,
                            node: 2,
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
                        body: 2,
                        owner: 2,
                        source: span,
                    }],
                });
                let run = |budget: &mut TypeWorkBudget| {
                    Analysis::new(&graph, budget)?.check(&[root], budget)
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
        let mut analysis = Analysis::new(&graph, &mut budget).unwrap();
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
            callables: Vec::new(),
            types: TypeArguments(Vec::new()),
            code: Vec::new(),
        };
        let mut analysis = Analysis::new(&graph, &mut budget).unwrap();
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
