//! Private bounded capture projection, intended as a child of capture::value.
//! This file is not installed or compiled. Frame admission belongs to the
//! original typed Call/Evidence producer, not to this projection algebra.

use std::collections::{HashMap, HashSet};
use std::hash::{DefaultHasher, Hash, Hasher};

use super::{Atom, Failure, TypeWorkBudget, charge, copy_slice};
use super::typed_environment::TypeOrigin;

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(super) struct OriginalPort {
    pub(super) expression: usize,
    pub(super) context: usize,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(super) struct RouteId(usize);

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(super) struct FrameId(usize);

pub(super) struct PendingFrame(FrameId);

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(super) struct CompletedFrame(FrameId);

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(super) enum ProjectedAtom {
    Original(Atom),
    // This is a separate namespace; FrameId is never a ContextId.
    Closure { function: usize, frame: CompletedFrame },
}

// Absent is not an empty result. Existing consumers decide their own absent
// behavior. A present empty capture must remain invalid for provider queries.
pub(super) enum Observation {
    Absent,
    Present(Vec<ProjectedAtom>),
}

pub(super) trait Leaves {
    // Snapshot implementations may read ONLY the query's terminal original
    // slots. This interface cannot create slots, close equations or acquire.
    fn atoms(&self, original: OriginalPort) -> Option<&[Atom]>;
    fn function_captures(&self, function: usize) -> Option<&[usize]>;
    fn capture_class(&self, function: usize, creation: usize, capture: usize) -> Option<ProjectionClass>;
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(super) enum ProjectionClass {
    Empty,
    Metadata,
    Callable(usize),
}

#[derive(Debug)]
enum Route {
    Original(OriginalPort),
    // Current occurrence head in live analysis; the copied head in a snapshot.
    // Distinct from a concrete leaf, and never creates a material slot.
    Head(OriginalPort),
    Empty,
    Free,
    // The producer has authenticated an inert original Function constructor.
    // Resolving it does not traverse or evaluate the frame's captures.
    Construct { function: usize, frame: CompletedFrame },
    Ready { inputs: Vec<RouteId>, value: RouteId },
    // Generic route union is deliberately unavailable. The first admissible
    // families have an independently established observation projection:
    // metadata membership or one callable target code, preserving environments.
    Join { class: ProjectionClass, sources: Vec<RouteId> },
}

#[derive(Debug)]
enum Environment {
    // Full original capture vector, never the union of all call inputs.
    Bindings(Vec<(usize, RouteId)>),
    // Alternatives remain separate for provider validity. A required capture
    // PORT that is empty cannot borrow values from another alternative.
    // A function with zero declared captures remains valid vacuously.
    Choice(Vec<CompletedFrame>),
}

#[derive(Debug)]
struct Frame {
    function: usize,
    environment: Environment,
    original_creation: Option<usize>,
    classes: Vec<ProjectionClass>,
    type_origin: Option<TypeOrigin>,
}

pub(super) struct Arena {
    routes: Vec<Route>,
    frames: Vec<Frame>,
    heads: HashMap<OriginalPort, RouteId>,
    capture_routes: HashMap<(CompletedFrame, usize, ProjectionClass), RouteId>,
    choices: HashMap<(usize, u64, usize), Vec<CompletedFrame>>,
    originals: HashMap<(usize, usize), CompletedFrame>,
    frozen_contexts: usize,
}

impl Arena {
    pub(super) fn new() -> Self {
        Self {
            routes: Vec::new(), frames: Vec::new(), heads: HashMap::new(),
            capture_routes: HashMap::new(),
            choices: HashMap::new(),
            originals: HashMap::new(),
            frozen_contexts: 0,
        }
    }

    fn route(&mut self, route: Route, budget: &mut TypeWorkBudget) -> Result<RouteId, Failure> {
        charge(budget, 1)?;
        self.routes.try_reserve(1).map_err(|_| Failure::Resource)?;
        let result = RouteId(self.routes.len());
        self.routes.push(route);
        Ok(result)
    }

    pub(super) fn original(&mut self, port: OriginalPort, budget: &mut TypeWorkBudget) -> Result<RouteId, Failure> {
        self.route(Route::Original(port), budget)
    }

    pub(super) fn head(&mut self, port: OriginalPort, budget: &mut TypeWorkBudget) -> Result<RouteId, Failure> {
        self.route(Route::Head(port), budget)
    }

    pub(super) fn empty(&mut self, budget: &mut TypeWorkBudget) -> Result<RouteId, Failure> {
        self.route(Route::Empty, budget)
    }

    pub(super) fn free(&mut self, budget: &mut TypeWorkBudget) -> Result<RouteId, Failure> {
        self.route(Route::Free, budget)
    }

    fn check_route(&self, route: RouteId) -> Result<(), Failure> {
        self.routes.get(route.0).map(|_| ()).ok_or(Failure::Invalid)
    }

    pub(super) fn bindings(
        &mut self, function: usize, original_captures: &[usize],
        captures: &[(usize, RouteId)], classes: &[ProjectionClass], type_origin: TypeOrigin, budget: &mut TypeWorkBudget,
    ) -> Result<PendingFrame, Failure> {
        charge(budget, original_captures.len() + captures.len())?;
        if original_captures.len() != captures.len() || classes.len() != captures.len() { return Err(Failure::Invalid); }
        for (&original, &(capture, route)) in original_captures.iter().zip(captures) {
            if original != capture { return Err(Failure::Invalid); }
            self.check_route(route)?;
        }
        let captures = copy_slice(captures, budget)?;
        let classes = copy_slice(classes, budget)?;
        charge(budget, 1)?;
        self.frames.try_reserve(1).map_err(|_| Failure::Resource)?;
        let result = FrameId(self.frames.len());
        self.frames.push(Frame { function, environment: Environment::Bindings(captures), original_creation: None, classes, type_origin: Some(type_origin) });
        Ok(PendingFrame(result))
    }

    // The caller is the exclusive matched source Function visit. It has proved
    // complete capture classes and installed the original live capture/root
    // equations. Preserve exact Closure(G,C) identity and full original context
    // provenance; a typed-body visit does not normalize Type/Row inputs here.
    pub(super) fn original_constructor_frame(
        &mut self, function: usize, creation: usize, captures: &[usize],
        bindings: &[(usize, RouteId)], classes: &[ProjectionClass],
        admitted: &super::AdmittedFrame, budget: &mut TypeWorkBudget,
    ) -> Result<CompletedFrame, Failure> {
        charge(budget, 1)?;
        if let Some(frame) = self.originals.get(&(function, creation)) { return Ok(*frame); }
        // Reserve the cache before constructing or completing the new record.
        charge(budget, 1)?;
        self.originals.try_reserve(1).map_err(|_| Failure::Resource)?;
        let pending = self.bindings(function, captures, bindings, classes,
            TypeOrigin::OriginalContext(creation), budget)?;
        self.frames[pending.0.0].original_creation = Some(creation);
        charge(budget, 2)?; // completion lookup and cache publication
        let completed = self.complete_under(pending, admitted)?;
        self.originals.insert((function, creation), completed);
        Ok(completed)
    }

    pub(super) fn original_creation(&self, frame: CompletedFrame, budget: &mut TypeWorkBudget) -> Result<Option<usize>, Failure> {
        charge(budget, 1)?;
        self.frames.get(frame.0.0).map(|record| record.original_creation).ok_or(Failure::Invalid)
    }

    // Private completion: the connected definition producer calls this only
    // under its exclusively owned Installed visit. New Call/Evidence families
    // still require their authenticated matched visit after exact kinds, actuals, ordered dictionary
    // tuple, whole-family one-code result and all required routes are admitted.
    // Installing operand records or route coordinates cannot call this API.
    fn complete(&self, pending: PendingFrame) -> CompletedFrame {
        CompletedFrame(pending.0)
    }

    pub(super) fn complete_under(&self, pending: PendingFrame,
        admitted: &super::AdmittedFrame) -> Result<CompletedFrame, Failure>
    {
        let frame = self.frames.get(pending.0.0).ok_or(Failure::Invalid)?;
        if frame.function != admitted.function { return Err(Failure::Invalid); }
        Ok(self.complete(pending))
    }

    fn choice(
        &mut self, function: usize, frames: &[CompletedFrame], budget: &mut TypeWorkBudget,
    ) -> Result<CompletedFrame, Failure> {
        if frames.is_empty() { return Err(Failure::Invalid); }
        charge(budget, frames.len())?;
        for frame in frames {
            if self.frames.get(frame.0.0).is_none_or(|frame| frame.function != function) {
                return Err(Failure::Invalid);
            }
        }
        if let [frame] = frames { return Ok(*frame); }
        let key = Self::choice_hash(function, frames, budget)?;
        charge(budget, 1)?;
        if let Some(candidates) = self.choices.get(&key) {
            charge(budget, candidates.len())?;
            for candidate in candidates {
                let Environment::Choice(original) = &self.frames[candidate.0.0].environment else { return Err(Failure::Invalid); };
                charge(budget, original.len() + 1)?;
                if original.as_slice() == frames { return Ok(*candidate); }
            }
        }
        let frames = copy_slice(frames, budget)?;
        charge(budget, 1)?;
        self.frames.try_reserve(1).map_err(|_| Failure::Resource)?;
        self.choices.try_reserve(1).map_err(|_| Failure::Resource)?;
        let candidates = self.choices.entry(key).or_default();
        candidates.try_reserve(1).map_err(|_| Failure::Resource)?;
        let result = CompletedFrame(FrameId(self.frames.len()));
        self.frames.push(Frame { function, environment: Environment::Choice(frames), original_creation: None, classes: Vec::new(), type_origin: None });
        candidates.push(result);
        Ok(result)
    }

    fn choice_hash(function: usize, frames: &[CompletedFrame], budget: &mut TypeWorkBudget) -> Result<(usize, u64, usize), Failure> {
        // Only the scalar digest/length tuple enters HashMap. Every full-key
        // hash/equality walk is separately paid, including collisions.
        charge(budget, frames.len() + 2)?;
        let mut hasher = DefaultHasher::new();
        function.hash(&mut hasher);
        frames.len().hash(&mut hasher);
        for frame in frames { frame.hash(&mut hasher); }
        Ok((function, hasher.finish(), frames.len()))
    }

    fn wrap_original(
        &mut self, function: usize, creation: usize, leaves: &impl Leaves,
        budget: &mut TypeWorkBudget,
    ) -> Result<CompletedFrame, Failure> {
        charge(budget, 1)?;
        if let Some(&frame) = self.originals.get(&(function, creation)) { return Ok(frame); }
        // This adapter consumes an actually observed original Closure atom,
        // preserving exactly its declared capture ports and creation context.
        // It does not qualify a new constructor or substitute a static Type.
        let captures = leaves.function_captures(function).ok_or(Failure::Invalid)?;
        charge(budget, captures.len())?;
        let mut routes = Vec::new();
        let mut classes = Vec::new();
        routes.try_reserve_exact(captures.len()).map_err(|_| Failure::Resource)?;
        classes.try_reserve_exact(captures.len()).map_err(|_| Failure::Resource)?;
        for capture in captures {
            let original = OriginalPort { expression: *capture, context: creation };
            charge(budget, 1)?;
            if !self.heads.contains_key(&original) && leaves.atoms(original).is_none() { return Err(Failure::Invalid); }
            let route = self.head(original, budget)?;
            routes.push((*capture, route));
            // Supplied only by the complete admitted family. Current empty
            // atoms are not a certificate of permanent Empty output.
            classes.push(leaves.capture_class(function, creation, *capture).ok_or(Failure::Invalid)?);
        }
        let pending = self.bindings(function, captures, &routes, &classes, TypeOrigin::OriginalContext(creation), budget)?;
        self.frames[pending.0.0].original_creation = Some(creation);
        charge(budget, 1)?;
        self.originals.try_reserve(1).map_err(|_| Failure::Resource)?;
        let frame = self.complete(pending);
        self.originals.insert((function, creation), frame);
        Ok(frame)
    }

    pub(super) fn construct(
        &mut self, function: usize, frame: CompletedFrame, budget: &mut TypeWorkBudget,
    ) -> Result<RouteId, Failure> {
        charge(budget, 1)?;
        if self.frames.get(frame.0.0).is_none_or(|frame| frame.function != function) {
            return Err(Failure::Invalid);
        }
        self.route(Route::Construct { function, frame }, budget)
    }

    pub(super) fn function(&self, frame: CompletedFrame) -> Result<usize, Failure> {
        self.frames.get(frame.0.0).map(|frame| frame.function).ok_or(Failure::Invalid)
    }

    pub(super) fn ready(
        &mut self, inputs: &[RouteId], value: RouteId, budget: &mut TypeWorkBudget,
    ) -> Result<RouteId, Failure> {
        charge(budget, inputs.len() + 1)?;
        self.check_route(value)?;
        for input in inputs { self.check_route(*input)?; }
        let inputs = copy_slice(inputs, budget)?;
        self.route(Route::Ready { inputs, value }, budget)
    }

    pub(super) fn join(
        &mut self, class: ProjectionClass, sources: &[RouteId], budget: &mut TypeWorkBudget,
    ) -> Result<RouteId, Failure> {
        charge(budget, sources.len())?;
        for source in sources { self.check_route(*source)?; }
        let sources = copy_slice(sources, budget)?;
        self.route(Route::Join { class, sources }, budget)
    }

    pub(super) fn publish_head(
        &mut self, original: OriginalPort, complete: RouteId, budget: &mut TypeWorkBudget,
    ) -> Result<bool, Failure> {
        self.check_route(complete)?;
        charge(budget, 1)?;
        if original.context < self.frozen_contexts { return Err(Failure::Invalid); }
        if self.heads.get(&original) == Some(&complete) { return Ok(false); }
        self.heads.try_reserve(1).map_err(|_| Failure::Resource)?;
        // Only the complete local-plus-all-feeds route is accepted here.
        // The Analysis producer MUST reserve notification storage before this
        // call, then increment revision and notify all existing virtual readers
        // on true. A same-code head change can introduce a new owner or an
        // invalid required capture even though the target projection is stable.
        self.heads.insert(original, complete);
        Ok(true)
    }

    pub(super) fn lookup_head(&self, original: OriginalPort, budget: &mut TypeWorkBudget) -> Result<Option<RouteId>, Failure> {
        charge(budget, 1)?;
        Ok(self.heads.get(&original).copied())
    }

    pub(super) fn transfer_union(
        &mut self, frame: CompletedFrame, capture: usize, class: ProjectionClass,
        budget: &mut TypeWorkBudget,
    ) -> Result<RouteId, Failure> {
        let key = (frame, capture, class);
        charge(budget, 1)?;
        if let Some(&route) = self.capture_routes.get(&key) { return Ok(route); }
        // Child FrameIds precede parents, so an explicit postorder has no
        // recursive Rust ownership or stack traversal. Memoization is structural.
        let mut pending = Vec::new();
        pending.try_reserve(1).map_err(|_| Failure::Resource)?;
        pending.push((frame, false));
        while let Some((frame, finish)) = pending.pop() {
            charge(budget, 1)?;
            let key = (frame, capture, class);
            if self.capture_routes.contains_key(&key) { continue; }
            let original = self.frames.get(frame.0.0).ok_or(Failure::Invalid)?;
            let route = match &original.environment {
                Environment::Bindings(bindings) => {
                    charge(budget, bindings.len())?;
                    bindings.iter().find(|(id, _)| *id == capture)
                        .map(|(_, route)| *route).ok_or(Failure::Invalid)?
                }
                Environment::Choice(frames) if !finish => {
                    charge(budget, frames.len() + 1)?;
                    pending.try_reserve(frames.len() + 1).map_err(|_| Failure::Resource)?;
                    pending.push((frame, true));
                    pending.extend(frames.iter().rev().map(|child| (*child, false)));
                    continue;
                }
                Environment::Choice(frames) => {
                    charge(budget, frames.len())?;
                    let mut sources = Vec::new();
                    sources.try_reserve_exact(frames.len()).map_err(|_| Failure::Resource)?;
                    for child in frames {
                        sources.push(*self.capture_routes.get(&(*child, capture, class)).ok_or(Failure::Invalid)?);
                    }
                    self.join(class, &sources, budget)?
                }
            };
            charge(budget, 1)?;
            self.capture_routes.try_reserve(1).map_err(|_| Failure::Resource)?;
            self.capture_routes.insert(key, route);
        }
        self.capture_routes.get(&(frame, capture, class)).copied().ok_or(Failure::Invalid)
    }

    pub(super) fn capture_class(
        &self, frame: CompletedFrame, capture: usize, budget: &mut TypeWorkBudget,
    ) -> Result<ProjectionClass, Failure> {
        let mut pending = copy_slice(&[frame], budget)?;
        let mut visited = HashSet::new();
        let mut result = ProjectionClass::Empty;
        while let Some(frame) = pending.pop() {
            charge(budget, 1)?;
            if visited.contains(&frame) { continue; }
            visited.try_reserve(1).map_err(|_| Failure::Resource)?;
            visited.insert(frame);
            let original = self.frames.get(frame.0.0).ok_or(Failure::Invalid)?;
            match &original.environment {
                Environment::Bindings(captures) => {
                    charge(budget, captures.len())?;
                    let position = captures.iter().position(|(id, _)| *id == capture).ok_or(Failure::Invalid)?;
                    let class = *original.classes.get(position).ok_or(Failure::Invalid)?;
                    result = match (result, class) {
                        (ProjectionClass::Empty, class) | (class, ProjectionClass::Empty) => class,
                        (old, new) if old == new => old,
                        _ => return Err(Failure::Invalid),
                    };
                }
                Environment::Choice(children) => {
                    charge(budget, children.len())?;
                    pending.try_reserve(children.len()).map_err(|_| Failure::Resource)?;
                    pending.extend(children.iter().rev().copied());
                }
            }
        }
        Ok(result)
    }

    // Focus receives independent route/frame/head storage. It may append its
    // own immutable projections, but can never follow a later normal head.
    pub(super) fn snapshot(&self, frozen_contexts: usize, budget: &mut TypeWorkBudget) -> Result<Self, Failure> {
        charge(budget, self.routes.len() + self.frames.len() + self.heads.len())?;
        let mut result = Self::new();
        result.frozen_contexts = frozen_contexts;
        result.routes.try_reserve_exact(self.routes.len()).map_err(|_| Failure::Resource)?;
        result.frames.try_reserve_exact(self.frames.len()).map_err(|_| Failure::Resource)?;
        result.heads.try_reserve(self.heads.len()).map_err(|_| Failure::Resource)?;
        for route in &self.routes {
            result.routes.push(match route {
                Route::Original(port) => Route::Original(*port),
                Route::Head(port) => Route::Head(*port),
                Route::Empty => Route::Empty,
                Route::Free => Route::Free,
                Route::Construct { function, frame } => Route::Construct { function: *function, frame: *frame },
                Route::Ready { inputs, value } => Route::Ready { inputs: copy_slice(inputs, budget)?, value: *value },
                Route::Join { class, sources } => Route::Join { class: *class, sources: copy_slice(sources, budget)? },
            });
        }
        for (id, frame) in self.frames.iter().enumerate() {
            let environment = match &frame.environment {
                Environment::Bindings(bindings) => Environment::Bindings(copy_slice(bindings, budget)?),
                Environment::Choice(frames) => {
                    let key = Self::choice_hash(frame.function, frames, budget)?;
                    charge(budget, 1)?;
                    result.choices.try_reserve(1).map_err(|_| Failure::Resource)?;
                    let candidates = result.choices.entry(key).or_default();
                    candidates.try_reserve(1).map_err(|_| Failure::Resource)?;
                    candidates.push(CompletedFrame(FrameId(id)));
                    Environment::Choice(copy_slice(frames, budget)?)
                }
            };
            if let Some(creation) = frame.original_creation {
                charge(budget, 1)?;
                result.originals.try_reserve(1).map_err(|_| Failure::Resource)?;
                result.originals.insert((frame.function, creation), CompletedFrame(FrameId(id)));
            }
            let classes = copy_slice(&frame.classes, budget)?;
            result.frames.push(Frame { function: frame.function, environment, original_creation: frame.original_creation, classes, type_origin: frame.type_origin });
        }
        result.heads.extend(self.heads.iter().map(|(key, value)| (*key, *value)));
        // Rebuild this optional structural index only on demand in the query.
        Ok(result)
    }

    pub(super) fn freeze_virtual(
        &mut self, original: OriginalPort, leaves: &impl Leaves,
        budget: &mut TypeWorkBudget,
    ) -> Result<Observation, Failure> {
        charge(budget, 1)?;
        let Some(&head) = self.heads.get(&original) else { return Ok(Observation::Absent); };
        self.resolve(head, leaves, budget).map(Observation::Present)
    }

    pub(super) fn alternatives(
        &self, frame: CompletedFrame, budget: &mut TypeWorkBudget,
    ) -> Result<Vec<CaptureAlternative>, Failure> {
        let mut pending = copy_slice(&[frame], budget)?;
        let mut visited = HashSet::new();
        let mut result = Vec::new();
        while let Some(frame) = pending.pop() {
            charge(budget, 1)?;
            if visited.contains(&frame) { continue; }
            visited.try_reserve(1).map_err(|_| Failure::Resource)?;
            visited.insert(frame);
            let original = self.frames.get(frame.0.0).ok_or(Failure::Invalid)?;
            match &original.environment {
                Environment::Bindings(captures) => {
                    let captures = copy_slice(captures, budget)?;
                    charge(budget, 1)?;
                    result.try_reserve(1).map_err(|_| Failure::Resource)?;
                    result.push(CaptureAlternative { function: original.function, captures, type_origin: original.type_origin.ok_or(Failure::Invalid)? });
                }
                Environment::Choice(children) => {
                    charge(budget, children.len())?;
                    pending.try_reserve(children.len()).map_err(|_| Failure::Resource)?;
                    pending.extend(children.iter().rev().copied());
                }
            }
        }
        Ok(result)
    }

    pub(super) fn target(
        atoms: &[ProjectedAtom], expected: usize, budget: &mut TypeWorkBudget,
    ) -> Result<Option<usize>, Failure> {
        charge(budget, atoms.len())?;
        for atom in atoms {
            match atom {
                ProjectedAtom::Closure { function, .. }
                | ProjectedAtom::Original(Atom::Closure(function, _)) if *function == expected => {}
                _ => return Err(Failure::Invalid),
            }
        }
        Ok((!atoms.is_empty()).then_some(expected))
    }

    fn append_unique(
        result: &mut Vec<ProjectedAtom>, seen: &mut HashSet<ProjectedAtom>,
        atom: ProjectedAtom, budget: &mut TypeWorkBudget,
    ) -> Result<(), Failure> {
        charge(budget, 1)?;
        if seen.contains(&atom) { return Ok(()); }
        charge(budget, 2)?;
        result.try_reserve(1).map_err(|_| Failure::Resource)?;
        seen.try_reserve(1).map_err(|_| Failure::Resource)?;
        seen.insert(atom);
        result.push(atom);
        Ok(())
    }

    fn project_original(atom: Atom) -> ProjectedAtom {
        match atom {
            Atom::FramedClosure(function, frame) => ProjectedAtom::Closure { function, frame },
            original => ProjectedAtom::Original(original),
        }
    }

    pub(super) fn resolve(
        &mut self, head: RouteId, leaves: &impl Leaves,
        budget: &mut TypeWorkBudget,
    ) -> Result<Vec<ProjectedAtom>, Failure> {
        self.resolve_observed(head, leaves, budget).map(|result| result.atoms)
    }

    pub(super) fn resolve_observed(
        &mut self, head: RouteId, leaves: &impl Leaves,
        budget: &mut TypeWorkBudget,
    ) -> Result<Resolved, Failure> {
        self.check_route(head)?;
        // Answers belong only to this observation. In live Analysis a later
        // original leaf can grow; no returned value is a completion token.
        let mut values: HashMap<RouteId, Vec<ProjectedAtom>> = HashMap::new();
        let mut active = HashSet::new();
        let mut observed_leaves = ObservedPorts::new();
        let mut observed_heads = ObservedPorts::new();
        let mut pending = Vec::new();
        pending.try_reserve(1).map_err(|_| Failure::Resource)?;
        pending.push((head, false));
        while let Some((route, finish)) = pending.pop() {
            charge(budget, 1)?;
            if values.contains_key(&route) { continue; }
            let original = self.routes.get(route.0).ok_or(Failure::Invalid)?;
            if !finish {
                charge(budget, 1)?;
                active.try_reserve(1).map_err(|_| Failure::Resource)?;
                // Qualified recipe families are acyclic. This is defensive;
                // a cycle cannot trigger a late fallback after publication.
                if !active.insert(route) { return Err(Failure::Invalid); }
                let children: &[RouteId] = match original {
                    Route::Ready { inputs, .. } => inputs,
                    Route::Join { sources, .. } => sources,
                    _ => &[],
                };
                charge(budget, children.len() + 2)?;
                pending.try_reserve(children.len() + 2).map_err(|_| Failure::Resource)?;
                pending.push((route, true));
                if let Route::Head(port) = original {
                    observed_heads.observe(*port, budget)?;
                    if let Some(&head) = self.heads.get(port) { pending.push((head, false)); }
                }
                pending.extend(children.iter().rev().map(|child| (*child, false)));
                continue;
            }
            if let Route::Ready { inputs, value } = original {
                charge(budget, inputs.len())?;
                let ready = inputs.iter().all(|input| values.get(input).is_some_and(|atoms| !atoms.is_empty()));
                if ready && !values.contains_key(value) {
                    pending.try_reserve(2).map_err(|_| Failure::Resource)?;
                    pending.push((route, true));
                    pending.push((*value, false));
                    continue;
                }
            }
            let mut result = Vec::new();
            let mut seen = HashSet::new();
            match original {
                Route::Original(port) => {
                    // Missing original leaves are never silently empty.
                    let atoms = leaves.atoms(*port).ok_or(Failure::Invalid)?;
                    observed_leaves.observe(*port, budget)?;
                    charge(budget, atoms.len())?;
                    for atom in atoms { Self::append_unique(&mut result, &mut seen, Self::project_original(*atom), budget)?; }
                }
                Route::Head(port) => {
                    if let Some(head) = self.heads.get(port) {
                        result = copy_slice(values.get(head).ok_or(Failure::Invalid)?, budget)?;
                    } else {
                        let atoms = leaves.atoms(*port).ok_or(Failure::Invalid)?;
                        charge(budget, atoms.len() + 1)?;
                        observed_leaves.observe(*port, budget)?;
                        for atom in atoms { Self::append_unique(&mut result, &mut seen, Self::project_original(*atom), budget)?; }
                    }
                }
                Route::Empty => {}
                Route::Free => Self::append_unique(&mut result, &mut seen, ProjectedAtom::Original(Atom::Free), budget)?,
                Route::Construct { function, frame } => Self::append_unique(&mut result, &mut seen,
                    ProjectedAtom::Closure { function: *function, frame: *frame }, budget)?,
                Route::Ready { inputs, value } => {
                    let mut ready = true;
                    charge(budget, inputs.len())?;
                    for input in inputs { ready &= !values.get(input).ok_or(Failure::Invalid)?.is_empty(); }
                    if ready {
                        result = copy_slice(values.get(value).ok_or(Failure::Invalid)?, budget)?;
                    }
                }
                Route::Join { class, sources } => {
                    let class = *class;
                    // Copy route coordinates before appending a Choice frame.
                    let sources = copy_slice(sources, budget)?;
                    let mut alternatives = Vec::new();
                    let mut alternative_set = HashSet::new();
                    for source in sources {
                        let atoms = values.get(&source).ok_or(Failure::Invalid)?;
                        charge(budget, atoms.len())?;
                        for atom in atoms {
                            match (class, *atom) {
                                (ProjectionClass::Metadata, ProjectedAtom::Original(Atom::Free | Atom::Unknown | Atom::Resource(..))) => {
                                    Self::append_unique(&mut result, &mut seen, *atom, budget)?;
                                }
                                (ProjectionClass::Callable(target), ProjectedAtom::Closure { function, frame }) if target == function => {
                                    charge(budget, 1)?;
                                    if !alternative_set.contains(&frame) {
                                        charge(budget, 2)?;
                                        alternatives.try_reserve(1).map_err(|_| Failure::Resource)?;
                                        alternative_set.try_reserve(1).map_err(|_| Failure::Resource)?;
                                        alternative_set.insert(frame);
                                        alternatives.push(frame);
                                    }
                                }
                                (ProjectionClass::Callable(target), ProjectedAtom::Original(Atom::Closure(function, creation))) if target == function => {
                                    let frame = self.wrap_original(function, creation, leaves, budget)?;
                                    charge(budget, 1)?;
                                    if !alternative_set.contains(&frame) {
                                        charge(budget, 2)?;
                                        alternatives.try_reserve(1).map_err(|_| Failure::Resource)?;
                                        alternative_set.try_reserve(1).map_err(|_| Failure::Resource)?;
                                        alternative_set.insert(frame);
                                        alternatives.push(frame);
                                    }
                                }
                                _ => return Err(Failure::Invalid),
                            }
                        }
                    }
                    if let ProjectionClass::Callable(function) = class {
                        if !alternatives.is_empty() {
                            let frame = self.choice(function, &alternatives, budget)?;
                            Self::append_unique(&mut result, &mut seen, ProjectedAtom::Closure { function, frame }, budget)?;
                        }
                    }
                }
            }
            charge(budget, 1)?;
            values.try_reserve(1).map_err(|_| Failure::Resource)?;
            values.insert(route, result);
            active.remove(&route);
        }
        Ok(Resolved {
            atoms: values.remove(&head).ok_or(Failure::Invalid)?,
            leaves: observed_leaves.ordered,
            heads: observed_heads.ordered,
        })
    }
}

pub(super) struct Resolved {
    pub(super) atoms: Vec<ProjectedAtom>,
    // The actual live consumer installs original leaf and virtual-head watches
    // before publishing dependent answers. Frozen consumers need no watches.
    pub(super) leaves: Vec<OriginalPort>,
    pub(super) heads: Vec<OriginalPort>,
}

pub(super) struct CaptureAlternative {
    pub(super) function: usize,
    pub(super) captures: Vec<(usize, RouteId)>,
    pub(super) type_origin: TypeOrigin,
}

struct ObservedPorts {
    ordered: Vec<OriginalPort>,
    members: HashSet<OriginalPort>,
}

impl ObservedPorts {
    fn new() -> Self { Self { ordered: Vec::new(), members: HashSet::new() } }

    fn observe(&mut self, port: OriginalPort, budget: &mut TypeWorkBudget) -> Result<(), Failure> {
        charge(budget, 1)?;
        if self.members.contains(&port) { return Ok(()); }
        charge(budget, 2)?;
        self.ordered.try_reserve(1).map_err(|_| Failure::Resource)?;
        self.members.try_reserve(1).map_err(|_| Failure::Resource)?;
        self.members.insert(port);
        self.ordered.push(port);
        Ok(())
    }
}
